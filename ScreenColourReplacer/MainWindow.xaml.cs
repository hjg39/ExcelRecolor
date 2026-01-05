using System.Diagnostics;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading;
using System.Windows;
using System.Windows.Interop;
using System.Windows.Media.Imaging;
using System.Windows.Threading;
using System.Buffers.Binary;
using System.IO.Hashing;
using System.Runtime.CompilerServices;
using System.IO;
using System.Windows.Media;



namespace ScreenColourReplacer
{
    readonly struct CacheKey : IEquatable<CacheKey>
    {
        public CacheKey(IntPtr hwnd, int w, int h) { Hwnd = hwnd; W = w; H = h; }
        public readonly IntPtr Hwnd;
        public readonly int W;
        public readonly int H;

        public bool Equals(CacheKey other) => Hwnd == other.Hwnd && W == other.W && H == other.H;
        public override bool Equals(object? obj) => obj is CacheKey other && Equals(other);
        public override int GetHashCode() => HashCode.Combine(Hwnd, W, H);
    }


    public partial class MainWindow : Window
    {
        // ---------- Perf knobs ----------
        private const int TIMER_MS = 20; // 20 FPS-ish. Try 33 for 30 FPS, 100 for 10 FPS.
        private const int LUT_BITS = 5;  // 5 => 32 levels/channel (32^3 = 32768)
        private const int LUT_SIZE = 1 << LUT_BITS;
        private const int LUT_MASK = LUT_SIZE - 1;

        // ---------- Overlay / desktop ----------
        private WriteableBitmap? _overlay;
        private int _vsLeft, _vsTop, _vsW, _vsH;

        private readonly DispatcherTimer _timer = new DispatcherTimer(DispatcherPriority.Background)
        {
            Interval = TimeSpan.FromMilliseconds(TIMER_MS)
        };


        // Cache per Excel window (buffer reuse)
        private readonly Dictionary<CacheKey, CaptureCache> _cache = new();


        // Last seen windows for "clear stale regions"
        private List<ExcelWin> _lastWins = new();

        private readonly uint[] _lut32 = new uint[LUT_SIZE * LUT_SIZE * LUT_SIZE]; // packed BGRA in little-endian

        private readonly Dictionary<uint, bool> _pidIsIgnoredOccluder = new();
        private int _pidCacheSweepCounter = 0;

        // --- Tick re-entrancy guard ---
        private int _inTick;

        // --- Cached handles ---
        private IntPtr _overlayHwnd;
        private IntPtr _screenDc;

        // --- Per-tick Z-order cache ---
        private readonly List<(IntPtr Hwnd, RECT Rect)> _zOrder = new(256);
        private readonly Dictionary<IntPtr, int> _zIndex = new(256);

        // --- Per-tick stale rects (screen-space, clipped) ---
        private readonly List<RECT> _staleRects = new(64);
        private readonly Dictionary<IntPtr, RECT> _tmpNewByHwnd = new(16);

        // --- Draw jobs (capture/hash phase -> draw phase) ---
        private readonly List<DrawJob> _jobs = new(8);

        private struct DrawJob
        {
            public CaptureCache Cc;
            public RECT ExcelRect;
            public List<RECT> Visibles;   // screen-space, clipped
            public bool VisChanged;
        }

        // --- Cleanup reuse (avoid per-tick allocations) ---
        private readonly HashSet<IntPtr> _aliveHwnds = new();
        private readonly List<CacheKey> _toDeleteKeys = new();

        // --- Excel HWND caching ---
        private const int EXCEL_ENUM_REFRESH_EVERY_N_TICKS = 10;
        private int _excelEnumCountdown = 0;

        private readonly List<IntPtr> _excelHwnds = new(8);
        private readonly HashSet<IntPtr> _excelFound = new(16);
        private readonly List<IntPtr> _excelHwndsToRemove = new(8);

        private readonly List<ExcelWin> _wins = new(4);
        private readonly StringBuilder _classSb = new(16);

        // --- Fast per-byte quantization ---
        private static readonly byte[] _q = BuildQuantTable();

        private static byte[] BuildQuantTable()
        {
            var t = new byte[256];
            int shift = 8 - LUT_BITS; // e.g. 3 when LUT_BITS=5
            for (int i = 0; i < 256; i++)
                t[i] = (byte)(i >> shift);
            return t;
        }


        public MainWindow()
        {
            InitializeComponent();
            LoadHueFromConfig();
            BuildLut();
            _timer.Tick += (_, __) => Tick();
        }

        private void Window_Loaded(object sender, RoutedEventArgs e)
        {
            // Virtual desktop in *physical pixels*
            int vsLeftPx = GetSystemMetrics(SM_XVIRTUALSCREEN);
            int vsTopPx = GetSystemMetrics(SM_YVIRTUALSCREEN);
            int vsWPx = GetSystemMetrics(SM_CXVIRTUALSCREEN);
            int vsHPx = GetSystemMetrics(SM_CYVIRTUALSCREEN);

            // Store as pixel coords (used for your dstX/dstY math)
            _vsLeft = vsLeftPx;
            _vsTop = vsTopPx;
            _vsW = vsWPx;
            _vsH = vsHPx;

            // Convert pixels -> DIPs for *WPF window placement*
            var dpi = VisualTreeHelper.GetDpi(this);
            double sx = dpi.DpiScaleX;
            double sy = dpi.DpiScaleY;

            Left = vsLeftPx / sx;
            Top = vsTopPx / sy;
            Width = vsWPx / sx;
            Height = vsHPx / sy;

            // Create bitmap in *pixel dimensions*, but set DPI to match monitor scale
            _overlay = new WriteableBitmap(vsWPx, vsHPx, dpi.PixelsPerInchX, dpi.PixelsPerInchY,
                                           System.Windows.Media.PixelFormats.Bgra32, null);

            OverlayImage.Source = _overlay;
            _screenDc = GetDC(IntPtr.Zero);

            try
            {
                var p = Process.GetCurrentProcess();
                p.PriorityClass = ProcessPriorityClass.BelowNormal;
                p.PriorityBoostEnabled = false;
            }
            catch { }

            try { Thread.CurrentThread.Priority = ThreadPriority.BelowNormal; }
            catch { }


            _timer.Start();
        }


        private unsafe ulong ComputeSignatureFull(IntPtr bits, int stride, int w, int h)
        {
            int rowBytes = w * 4;
            var hasher = new XxHash3();

            if (stride == rowBytes)
            {
                var all = new ReadOnlySpan<byte>(bits.ToPointer(), h * stride);
                hasher.Append(all);
            }
            else
            {
                byte* p = (byte*)bits.ToPointer();
                for (int y = 0; y < h; y++)
                {
                    var row = new ReadOnlySpan<byte>(p + y * stride, rowBytes);
                    hasher.Append(row);
                }
            }

            Span<byte> out8 = stackalloc byte[8];
            hasher.GetCurrentHash(out8);
            return BinaryPrimitives.ReadUInt64LittleEndian(out8);
        }



        // ---- Click-through / no-activate / don't-capture-self ----
        protected override void OnSourceInitialized(EventArgs e)
        {
            base.OnSourceInitialized(e);

            var hwnd = new WindowInteropHelper(this).Handle;
            _overlayHwnd = hwnd;

            var exStyle = GetWindowLongPtr(hwnd, GWL_EXSTYLE);
            exStyle = new IntPtr(exStyle.ToInt64() | WS_EX_TRANSPARENT | WS_EX_LAYERED | WS_EX_NOACTIVATE | WS_EX_TOOLWINDOW);
            SetWindowLongPtr(hwnd, GWL_EXSTYLE, exStyle);

            // DO NOT block capture
            // SetWindowDisplayAffinity(hwnd, WDA_EXCLUDEFROMCAPTURE);
        }


        protected override void OnClosed(EventArgs e)
        {
            if (_screenDc != IntPtr.Zero)
            {
                ReleaseDC(IntPtr.Zero, _screenDc);
                _screenDc = IntPtr.Zero;
            }
            base.OnClosed(e);
        }

        private void Tick()
        {
            if (Interlocked.Exchange(ref _inTick, 1) == 1)
                return;

            try
            {
                TickCore();
            }
            finally
            {
                Volatile.Write(ref _inTick, 0);
            }
        }

        private void TickCore()
        {
            if (_overlay == null) return;

            EnsureExcelHwndsUpToDate();
            var wins = GetExcelWindows_FromKnownHwnds();

            // 1) compute stale regions (no overlay lock)
            CollectStaleRegions(_lastWins, wins, _staleRects);
            CoalesceRectsInPlace(_staleRects);

            // snapshot lastWins (important: don't keep references to reused lists)
            _lastWins.Clear();
            _lastWins.AddRange(wins);

            // If no Excel, just clear stale and exit
            if (wins.Count == 0)
            {
                if (_staleRects.Count == 0) return;

                _overlay.Lock();
                try
                {
                    IntPtr dstBackBuffer = _overlay.BackBuffer;
                    int dstStride = _overlay.BackBufferStride;

                    RECT dirty = default;
                    bool hasDirty = false;

                    for (int i = 0; i < _staleRects.Count; i++)
                    {
                        var r = _staleRects[i];
                        ClearBackBufferRect_ScreenSpace(dstBackBuffer, dstStride, r);
                        UnionInto(ref dirty, ref hasDirty, r);
                    }

                    if (hasDirty)
                    {
                        int x = dirty.Left - _vsLeft;
                        int y = dirty.Top - _vsTop;
                        _overlay.AddDirtyRect(new Int32Rect(x, y, dirty.Width, dirty.Height));
                    }
                }
                finally
                {
                    _overlay.Unlock();
                }

                CleanupCacheForClosedWindows(wins);
                return;
            }

            // 2) build Z-order cache ONCE per tick (no overlay lock)
            var interest = UnionAll(wins);
            BuildZOrderCache(interest);

            // 3) Phase A: capture/hash outside overlay lock
            _jobs.Clear();

            IntPtr screenDc = _screenDc;
            if (screenDc == IntPtr.Zero) return;

            for (int wi = 0; wi < wins.Count; wi++)
            {
                var w = wins[wi];

                if (!ClipToVirtualScreen(w.Rect, out var fullCap)) continue;

                int fullW = w.Rect.Width;
                int fullH = w.Rect.Height;
                if (fullW <= 0 || fullH <= 0) continue;

                var key = new CacheKey(w.Hwnd, fullW, fullH);
                if (!_cache.TryGetValue(key, out var cc))
                {
                    cc = new CaptureCache(fullW, fullH);
                    RemoveOtherSizesForHwnd(w.Hwnd, fullW, fullH);
                    _cache[key] = cc;
                }

                if (!_zIndex.TryGetValue(w.Hwnd, out int excelZi))
                    excelZi = _zOrder.Count;

                // Visible rects from cached Z-order
                List<RECT> visiblesRaw;
                if (excelZi == 0)
                {
                    cc.TmpVisA.Clear();
                    cc.TmpVisA.Add(w.Rect);
                    visiblesRaw = cc.TmpVisA;
                }
                else
                {
                    visiblesRaw = GetVisibleExcelRects_FromZ(w.Rect, excelZi, cc.TmpVisA, cc.TmpVisB);
                }

                // Clip to virtual screen into reused list
                var visibles = cc.TmpClipped;
                visibles.Clear();
                for (int i = 0; i < visiblesRaw.Count; i++)
                    if (ClipToVirtualScreen(visiblesRaw[i], out var cap))
                        visibles.Add(cap);

                CoalesceRectsInPlace(visibles);

                ulong visSig = ComputeRectsSignature_NoSort(visibles);
                bool visChanged = !cc.HasLastVisSig || visSig != cc.LastVisSig;

                // If fully hidden, only need to clear prior drawn pixels if visibility changed
                if (visibles.Count == 0)
                {
                    if (!visChanged)
                        continue;

                    cc.LastVisSig = visSig;
                    cc.HasLastVisSig = true;

                    _jobs.Add(new DrawJob { Cc = cc, ExcelRect = w.Rect, Visibles = visibles, VisChanged = true });
                    continue;
                }

                // Capture once (keep your PrintWindow-or-fallback behaviour)
                cc.CaptureExcelClientOrFallback(w.Hwnd, screenDc, w.Rect.Left, w.Rect.Top);

                ulong sig = ComputeSignatureFull(cc.BitsPtr, cc.SrcStride, fullW, fullH);
                bool contentChanged = !cc.HasLastSig || sig != cc.LastSig;

                if (!contentChanged && !visChanged)
                    continue;

                cc.LastSig = sig;
                cc.HasLastSig = true;

                cc.LastVisSig = visSig;
                cc.HasLastVisSig = true;

                _jobs.Add(new DrawJob { Cc = cc, ExcelRect = w.Rect, Visibles = visibles, VisChanged = visChanged });
            }

            if (_jobs.Count == 0 && _staleRects.Count == 0)
            {
                CleanupCacheForClosedWindows(wins);
                return;
            }

            // 4) Phase B: backbuffer writes inside overlay lock
            _overlay.Lock();
            try
            {
                IntPtr dstBackBuffer = _overlay.BackBuffer;
                int dstStride = _overlay.BackBufferStride;

                RECT dirty = default;
                bool hasDirty = false;

                // Clear stale
                for (int i = 0; i < _staleRects.Count; i++)
                {
                    var r = _staleRects[i];
                    ClearBackBufferRect_ScreenSpace(dstBackBuffer, dstStride, r);
                    UnionInto(ref dirty, ref hasDirty, r);
                }

                // Draw jobs
                for (int j = 0; j < _jobs.Count; j++)
                {
                    var job = _jobs[j];
                    var cc = job.Cc;
                    var excelRect = job.ExcelRect;
                    var visibles = job.Visibles;

                    // If visibility changed, clear last drawn for this hwnd
                    if (job.VisChanged)
                    {
                        for (int i = 0; i < cc.LastVisibleRects.Count; i++)
                        {
                            var r = cc.LastVisibleRects[i];
                            ClearBackBufferRect_ScreenSpace(dstBackBuffer, dstStride, r);
                            UnionInto(ref dirty, ref hasDirty, r);
                        }

                        cc.LastVisibleRects.Clear();
                        cc.LastVisibleRects.AddRange(visibles);
                    }

                    // Draw current visible rects
                    for (int i = 0; i < visibles.Count; i++)
                    {
                        var cap = visibles[i];

                        int capW = cap.Width;
                        int capH = cap.Height;

                        int srcX = cap.Left - excelRect.Left;
                        int srcY = cap.Top - excelRect.Top;

                        int dstX = cap.Left - _vsLeft;
                        int dstY = cap.Top - _vsTop;

                        ApplyLutToBackBuffer_WithSrcOffset(
                            cc.BitsPtr, cc.SrcStride,
                            dstBackBuffer, dstStride,
                            srcX, srcY,
                            dstX, dstY,
                            capW, capH);

                        UnionInto(ref dirty, ref hasDirty, cap);
                    }
                }

                if (hasDirty)
                {
                    int x = dirty.Left - _vsLeft;
                    int y = dirty.Top - _vsTop;
                    _overlay.AddDirtyRect(new Int32Rect(x, y, dirty.Width, dirty.Height));
                }
            }
            finally
            {
                _overlay.Unlock();
            }

            CleanupCacheForClosedWindows(wins);
        }


        private bool IsIgnoredOccluderWindow(IntPtr hwnd)
        {
            uint pid;
            GetWindowThreadProcessId(hwnd, out pid);
            if (pid == 0) return false;

            // Very cheap periodic cache reset (every ~2000 occluder checks)
            if (++_pidCacheSweepCounter > 2000)
            {
                _pidCacheSweepCounter = 0;
                _pidIsIgnoredOccluder.Clear();
            }

            if (_pidIsIgnoredOccluder.TryGetValue(pid, out bool cached))
                return cached;

            bool ignored = false;

            IntPtr hProc = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, false, pid);
            if (hProc != IntPtr.Zero)
            {
                try
                {
                    var sb = new StringBuilder(1024);
                    int size = sb.Capacity;
                    if (QueryFullProcessImageName(hProc, 0, sb, ref size))
                    {
                        string exe = Path.GetFileName(sb.ToString());

                        // Snipping Tool / clipping overlay (most common)
                        if (exe.Equals("ScreenClippingHost.exe", StringComparison.OrdinalIgnoreCase) ||
                            exe.Equals("SnippingTool.exe", StringComparison.OrdinalIgnoreCase))
                        {
                            ignored = true;
                        }
                    }
                }
                finally
                {
                    CloseHandle(hProc);
                }
            }

            _pidIsIgnoredOccluder[pid] = ignored;
            return ignored;
        }


        private unsafe void ClearBackBufferRect(
            IntPtr dstBackBuffer, int dstStride,
            int dstX, int dstY,
            int w, int h)
        {
            if (w <= 0 || h <= 0) return;

            byte* basePtr = (byte*)dstBackBuffer.ToPointer();

            for (int y = 0; y < h; y++)
            {
                byte* row = basePtr + (dstY + y) * dstStride + dstX * 4;
                Unsafe.InitBlockUnaligned(row, 0, (uint)(w * 4)); // set BGRA bytes to 0 => transparent
            }
        }

        // ---------- Region clipping ----------
        private bool ClipToVirtualScreen(RECT r, out RECT cap)
        {
            int left = Math.Max(r.Left, _vsLeft);
            int top = Math.Max(r.Top, _vsTop);
            int right = Math.Min(r.Right, _vsLeft + _vsW);
            int bottom = Math.Min(r.Bottom, _vsTop + _vsH);

            cap = new RECT { Left = left, Top = top, Right = right, Bottom = bottom };
            return cap.Width > 0 && cap.Height > 0;
        }

        private static bool RectsEqual(RECT a, RECT b) =>
            a.Left == b.Left && a.Top == b.Top && a.Right == b.Right && a.Bottom == b.Bottom;

        private void CleanupCacheForClosedWindows(List<ExcelWin> wins)
        {
            _aliveHwnds.Clear();
            for (int i = 0; i < wins.Count; i++)
                _aliveHwnds.Add(wins[i].Hwnd);

            _toDeleteKeys.Clear();

            foreach (var kv in _cache)
                if (!_aliveHwnds.Contains(kv.Key.Hwnd))
                    _toDeleteKeys.Add(kv.Key);

            for (int i = 0; i < _toDeleteKeys.Count; i++)
            {
                var key = _toDeleteKeys[i];
                _cache[key].Dispose();
                _cache.Remove(key);
            }
        }



        // ---------- LUT application ----------
        [MethodImpl(MethodImplOptions.AggressiveOptimization)]
        private unsafe void ApplyLutToBackBuffer_WithSrcOffset(
            IntPtr srcBits, int srcStride,
            IntPtr dstBackBuffer, int dstStride,
            int srcX, int srcY,
            int dstX, int dstY,
            int w, int h)
        {
            byte* srcBase = (byte*)srcBits.ToPointer();
            byte* dstBase = (byte*)dstBackBuffer.ToPointer();

            byte[] q = _q;
            uint[] lut = _lut32;

            for (int y = 0; y < h; y++)
            {
                uint* s = (uint*)(srcBase + (srcY + y) * srcStride) + srcX;
                uint* d = (uint*)(dstBase + (dstY + y) * dstStride) + dstX;

                for (int x = 0; x < w; x++)
                {
                    uint src = s[x];

                    int bQ = q[(byte)(src)];
                    int gQ = q[(byte)(src >> 8)];
                    int rQ = q[(byte)(src >> 16)];

                    int idx = (rQ << (2 * LUT_BITS)) | (gQ << LUT_BITS) | bQ;

                    // Keep original behaviour: non-match => transparent (0)
                    d[x] = lut[idx];
                }
            }
        }

        private void CollectStaleRegions(List<ExcelWin> oldWins, List<ExcelWin> newWins, List<RECT> outRects)
        {
            outRects.Clear();

            _tmpNewByHwnd.Clear();
            for (int i = 0; i < newWins.Count; i++)
                _tmpNewByHwnd[newWins[i].Hwnd] = newWins[i].Rect;

            for (int i = 0; i < oldWins.Count; i++)
            {
                var ow = oldWins[i];
                if (!_tmpNewByHwnd.TryGetValue(ow.Hwnd, out var nr) || !RectsEqual(ow.Rect, nr))
                {
                    if (ClipToVirtualScreen(ow.Rect, out var capOld))
                        outRects.Add(capOld);
                }
            }
        }

        private void ClearBackBufferRect_ScreenSpace(IntPtr dstBackBuffer, int dstStride, RECT cap)
        {
            int w = cap.Width, h = cap.Height;
            if (w <= 0 || h <= 0) return;

            int dstX = cap.Left - _vsLeft;
            int dstY = cap.Top - _vsTop;

            ClearBackBufferRect(dstBackBuffer, dstStride, dstX, dstY, w, h);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void UnionInto(ref RECT u, ref bool has, in RECT r)
        {
            if (r.Width <= 0 || r.Height <= 0) return;

            if (!has)
            {
                u = r;
                has = true;
                return;
            }

            u.Left = Math.Min(u.Left, r.Left);
            u.Top = Math.Min(u.Top, r.Top);
            u.Right = Math.Max(u.Right, r.Right);
            u.Bottom = Math.Max(u.Bottom, r.Bottom);
        }

        private static RECT UnionAll(IReadOnlyList<ExcelWin> wins)
        {
            int l = int.MaxValue, t = int.MaxValue, r = int.MinValue, b = int.MinValue;
            for (int i = 0; i < wins.Count; i++)
            {
                var w = wins[i].Rect;
                l = Math.Min(l, w.Left); t = Math.Min(t, w.Top);
                r = Math.Max(r, w.Right); b = Math.Max(b, w.Bottom);
            }
            return new RECT { Left = l, Top = t, Right = r, Bottom = b };
        }

        private void BuildZOrderCache(RECT interest)
        {
            _zOrder.Clear();
            _zIndex.Clear();

            for (IntPtr h = GetTopWindow(IntPtr.Zero); h != IntPtr.Zero; h = GetWindow(h, GW_HWNDNEXT))
            {
                if (!IsWindowVisible(h) || IsIconic(h)) continue;
                if (h == _overlayHwnd) continue;

                if (!GetWindowRect(h, out var wr)) continue;
                if (!Intersect(wr, interest, out _)) continue; // prune first

                if (IsIgnoredOccluderWindow(h)) continue;      // expensive last

                _zIndex[h] = _zOrder.Count;
                _zOrder.Add((h, wr));
            }
        }

        private List<RECT> GetVisibleExcelRects_FromZ(
            RECT excelRect,
            int excelZIndex,
            List<RECT> a,
            List<RECT> b)
        {
            a.Clear();
            a.Add(excelRect);

            var cur = a;
            var next = b;

            for (int zi = 0; zi < excelZIndex && cur.Count != 0; zi++)
            {
                var oc = _zOrder[zi].Rect;

                if (!Intersect(oc, excelRect, out var cut)) continue;

                next.Clear();
                for (int i = 0; i < cur.Count; i++)
                    SubtractRectInto(cur[i], cut, next);

                var tmp = cur;
                cur = next;
                next = tmp;
            }

            return cur;
        }

        private static void SubtractRectInto(in RECT src, in RECT cut, List<RECT> dst)
        {
            if (!Intersect(src, cut, out var i))
            {
                dst.Add(src);
                return;
            }

            if (src.Top < i.Top)
                dst.Add(new RECT { Left = src.Left, Top = src.Top, Right = src.Right, Bottom = i.Top });

            if (i.Bottom < src.Bottom)
                dst.Add(new RECT { Left = src.Left, Top = i.Bottom, Right = src.Right, Bottom = src.Bottom });

            if (src.Left < i.Left)
                dst.Add(new RECT { Left = src.Left, Top = i.Top, Right = i.Left, Bottom = i.Bottom });

            if (i.Right < src.Right)
                dst.Add(new RECT { Left = i.Right, Top = i.Top, Right = src.Right, Bottom = i.Bottom });
        }


        private void BuildLut()
        {
            // Precompute mapping for each quantized RGB.
            // For each bin, we pick the bin center value to compute HSV + match targets.
            for (int rQ = 0; rQ < LUT_SIZE; rQ++)
            {
                byte r = (byte)((rQ * 255 + (LUT_SIZE - 1) / 2) / (LUT_SIZE - 1));
                for (int gQ = 0; gQ < LUT_SIZE; gQ++)
                {
                    byte g = (byte)((gQ * 255 + (LUT_SIZE - 1) / 2) / (LUT_SIZE - 1));
                    for (int bQ = 0; bQ < LUT_SIZE; bQ++)
                    {
                        byte b = (byte)((bQ * 255 + (LUT_SIZE - 1) / 2) / (LUT_SIZE - 1));

                        RgbToHsv(r, g, b, out float h, out float s, out float v);
                        bool match = MatchesAnyTarget(h, s, v);

                        int idx = ((rQ * LUT_SIZE + gQ) * LUT_SIZE + bQ);

                        if (match)
                        {
                            HsvToRgb(_targetHueDeg, s, v, out byte rr, out byte gg, out byte bb);

                            // WriteableBitmap is BGRA in memory.
                            // Pack as 0xAARRGGBB so little-endian bytes are BB GG RR AA.
                            _lut32[idx] = (uint)(bb | (gg << 8) | (rr << 16) | (255u << 24));
                        }
                        else
                        {
                            _lut32[idx] = 0u; // transparent
                        }

                    }
                }
            }
        }

        // ---------- Hue matching config (your targets) ----------
        private const int DEFAULT_TARGET_HUE_DEG = 285;
        private int _targetHueDeg = DEFAULT_TARGET_HUE_DEG;

        private static readonly string HueConfigPath =
            Path.Combine(AppContext.BaseDirectory, "ScreenColourReplacer.config");


        private const float MIN_V = 0.08f;

        // (HueDeg, TolDeg, MinS)
        private static readonly (float HueDeg, float TolDeg, float MinS)[] TARGETS =
        {
            (141.94f, 12f, 0.18f), // #60BD82-ish
            (147.00f, 12f, 0.10f), // #9FC7B1-ish
            (148.42f, 12f, 0.04f), // #CFE2D8-ish
            (124.86f, 12f, 0.18f), // #1E6824-ish
            (76.47f, 12f, 0.18f),  // #BEDA74-ish
            (110.77f, 12f, 0.18f), // #72D560-ish
            (147.22f, 12f, 0.18f), // #0F703B / #107C41-ish
        };

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool CanMergeH(in RECT a, in RECT b) =>
    a.Top == b.Top && a.Bottom == b.Bottom && a.Right == b.Left;

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool CanMergeV(in RECT a, in RECT b) =>
            a.Left == b.Left && a.Right == b.Right && a.Bottom == b.Top;

        private static void CoalesceRectsInPlace(List<RECT> rects)
        {
            if (rects.Count < 2) return;

            rects.Sort(static (a, b) =>
            {
                int c = a.Top.CompareTo(b.Top);
                if (c != 0) return c;
                c = a.Left.CompareTo(b.Left);
                if (c != 0) return c;
                c = a.Bottom.CompareTo(b.Bottom);
                if (c != 0) return c;
                return a.Right.CompareTo(b.Right);
            });

            int write = 0;
            RECT cur = rects[0];
            for (int i = 1; i < rects.Count; i++)
            {
                var r = rects[i];
                if (CanMergeH(cur, r))
                {
                    cur.Right = r.Right;
                }
                else
                {
                    rects[write++] = cur;
                    cur = r;
                }
            }
            rects[write++] = cur;
            if (write < rects.Count) rects.RemoveRange(write, rects.Count - write);

            if (rects.Count < 2) return;

            write = 0;
            cur = rects[0];
            for (int i = 1; i < rects.Count; i++)
            {
                var r = rects[i];
                if (CanMergeV(cur, r))
                {
                    cur.Bottom = r.Bottom;
                }
                else
                {
                    rects[write++] = cur;
                    cur = r;
                }
            }
            rects[write++] = cur;
            if (write < rects.Count) rects.RemoveRange(write, rects.Count - write);
        }

        private static ulong ComputeRectsSignature_NoSort(List<RECT> rects)
        {
            const ulong OFFSET = 1469598103934665603UL;
            const ulong PRIME = 1099511628211UL;

            ulong x = OFFSET;
            ulong s = 0;

            x ^= (ulong)(uint)rects.Count; x *= PRIME;

            for (int i = 0; i < rects.Count; i++)
            {
                var r = rects[i];

                ulong h = OFFSET;
                h ^= (ulong)(uint)r.Left; h *= PRIME;
                h ^= (ulong)(uint)r.Top; h *= PRIME;
                h ^= (ulong)(uint)r.Right; h *= PRIME;
                h ^= (ulong)(uint)r.Bottom; h *= PRIME;

                x ^= h;
                s += h * PRIME;
            }

            x ^= s + 0x9E3779B97F4A7C15UL;
            x *= PRIME;
            return x;
        }


        private static ulong ComputeRectsSignature(List<RECT> rects)
        {
            // Order-independent signature: sort a copy-like by sorting in-place on the list we already built.
            rects.Sort((a, b) =>
            {
                int c = a.Top.CompareTo(b.Top);
                if (c != 0) return c;
                c = a.Left.CompareTo(b.Left);
                if (c != 0) return c;
                c = a.Bottom.CompareTo(b.Bottom);
                if (c != 0) return c;
                return a.Right.CompareTo(b.Right);
            });

            const ulong OFFSET = 1469598103934665603UL;
            const ulong PRIME = 1099511628211UL;

            ulong h = OFFSET;
            h ^= (ulong)(uint)rects.Count; h *= PRIME;

            foreach (var r in rects)
            {
                h ^= (ulong)(uint)r.Left; h *= PRIME;
                h ^= (ulong)(uint)r.Top; h *= PRIME;
                h ^= (ulong)(uint)r.Right; h *= PRIME;
                h ^= (ulong)(uint)r.Bottom; h *= PRIME;
            }
            return h;
        }

        private void LoadHueFromConfig()
        {
            _targetHueDeg = DEFAULT_TARGET_HUE_DEG;

            try
            {
                if (!File.Exists(HueConfigPath))
                    return;

                foreach (var raw in File.ReadAllLines(HueConfigPath))
                {
                    var line = raw.Trim();
                    if (line.Length == 0) continue;
                    if (line.StartsWith("//") || line.StartsWith(";")) continue;

                    const string key = "HUE=";
                    if (!line.StartsWith(key, StringComparison.OrdinalIgnoreCase))
                        continue;

                    var value = line.Substring(key.Length).Trim();

                    if (int.TryParse(value, out int hue))
                    {
                        // clamp into [0, 359] but also allow negative or 360+ by wrapping
                        hue %= 360;
                        if (hue < 0) hue += 360;

                        _targetHueDeg = hue;
                    }

                    return; // only one HUE line expected
                }
            }
            catch
            {
                _targetHueDeg = DEFAULT_TARGET_HUE_DEG;
            }
        }


        private static bool MatchesAnyTarget(float hDeg, float s, float v)
        {
            if (v < MIN_V) return false;

            for (int i = 0; i < TARGETS.Length; i++)
            {
                var t = TARGETS[i];
                if (s >= t.MinS && HueDistanceDeg(hDeg, t.HueDeg) <= t.TolDeg)
                    return true;
            }
            return false;
        }

        private static float HueDistanceDeg(float a, float b)
        {
            float d = MathF.Abs(a - b);
            return MathF.Min(d, 360f - d);
        }

        private static void RgbToHsv(byte r8, byte g8, byte b8, out float hDeg, out float s, out float v)
        {
            float r = r8 / 255f, g = g8 / 255f, b = b8 / 255f;
            float max = MathF.Max(r, MathF.Max(g, b));
            float min = MathF.Min(r, MathF.Min(g, b));
            float delta = max - min;

            v = max;
            s = (max <= 0f) ? 0f : (delta / max);

            if (delta <= 0f)
            {
                hDeg = 0f;
                return;
            }

            float h;
            if (max == r) h = (g - b) / delta;
            else if (max == g) h = 2f + (b - r) / delta;
            else h = 4f + (r - g) / delta;

            h *= 60f;
            if (h < 0f) h += 360f;
            hDeg = h;
        }

        private static void HsvToRgb(float hDeg, float s, float v, out byte r8, out byte g8, out byte b8)
        {
            if (s <= 0f)
            {
                byte vv = (byte)Math.Clamp((int)MathF.Round(v * 255f), 0, 255);
                r8 = g8 = b8 = vv;
                return;
            }

            float h = (hDeg % 360f) / 60f;
            int i = (int)MathF.Floor(h);
            float f = h - i;

            float p = v * (1f - s);
            float q = v * (1f - s * f);
            float t = v * (1f - s * (1f - f));

            float r, g, b;
            switch (i)
            {
                case 0: r = v; g = t; b = p; break;
                case 1: r = q; g = v; b = p; break;
                case 2: r = p; g = v; b = t; break;
                case 3: r = p; g = q; b = v; break;
                case 4: r = t; g = p; b = v; break;
                default: r = v; g = p; b = q; break;
            }

            r8 = (byte)Math.Clamp((int)MathF.Round(r * 255f), 0, 255);
            g8 = (byte)Math.Clamp((int)MathF.Round(g * 255f), 0, 255);
            b8 = (byte)Math.Clamp((int)MathF.Round(b * 255f), 0, 255);
        }

        // ---------- Excel window enumeration ----------
        private const string EXCEL_CLASS = "XLMAIN";

        public readonly struct ExcelWin
        {
            public ExcelWin(IntPtr hwnd, RECT rect) { Hwnd = hwnd; Rect = rect; }
            public IntPtr Hwnd { get; }
            public RECT Rect { get; }
        }

        [StructLayout(LayoutKind.Sequential)]
        public struct RECT
        {
            public int Left, Top, Right, Bottom;
            public int Width => Right - Left;
            public int Height => Bottom - Top;
        }

        [StructLayout(LayoutKind.Sequential)]
        public struct POINT { public int X, Y; }

        private delegate bool EnumWindowsProc(IntPtr hWnd, IntPtr lParam);

        [DllImport("user32.dll")] private static extern bool EnumWindows(EnumWindowsProc lpEnumFunc, IntPtr lParam);
        [DllImport("user32.dll", CharSet = CharSet.Unicode)] private static extern int GetClassName(IntPtr hWnd, StringBuilder lpClassName, int nMaxCount);
        [DllImport("user32.dll")] private static extern bool IsWindowVisible(IntPtr hWnd);
        [DllImport("user32.dll")] private static extern bool IsIconic(IntPtr hWnd);

        [DllImport("user32.dll")] private static extern bool GetClientRect(IntPtr hWnd, out RECT lpRect);
        [DllImport("user32.dll")] private static extern bool ClientToScreen(IntPtr hWnd, ref POINT lpPoint);

        [DllImport("user32.dll")] private static extern bool IsWindow(IntPtr hWnd);

        private void EnsureExcelHwndsUpToDate()
        {
            if (_excelHwnds.Count == 0 || _excelEnumCountdown-- <= 0)
            {
                EnumerateExcelHwnds();
                _excelEnumCountdown = EXCEL_ENUM_REFRESH_EVERY_N_TICKS;
            }
        }

        private void EnumerateExcelHwnds()
        {
            _excelFound.Clear();

            EnumWindows((hWnd, _) =>
            {
                if (!IsWindowVisible(hWnd) || IsIconic(hWnd)) return true;

                _classSb.Clear();
                GetClassName(hWnd, _classSb, _classSb.Capacity);

                if (!IsExcelClass(_classSb)) return true;

                _excelFound.Add(hWnd);
                return true;
            }, IntPtr.Zero);

            _excelHwndsToRemove.Clear();
            for (int i = 0; i < _excelHwnds.Count; i++)
                if (!_excelFound.Contains(_excelHwnds[i]))
                    _excelHwndsToRemove.Add(_excelHwnds[i]);

            for (int i = 0; i < _excelHwndsToRemove.Count; i++)
                _excelHwnds.Remove(_excelHwndsToRemove[i]);

            foreach (var h in _excelFound)
                if (!_excelHwnds.Contains(h))
                    _excelHwnds.Add(h);
        }

        private List<ExcelWin> GetExcelWindows_FromKnownHwnds()
        {
            _wins.Clear();
            _excelHwndsToRemove.Clear();

            for (int i = 0; i < _excelHwnds.Count; i++)
            {
                var hWnd = _excelHwnds[i];

                if (!IsWindow(hWnd) || !IsWindowVisible(hWnd) || IsIconic(hWnd))
                {
                    if (!IsWindow(hWnd)) _excelHwndsToRemove.Add(hWnd);
                    continue;
                }

                if (!GetClientRect(hWnd, out var rcClient)) continue;
                if (rcClient.Width <= 0 || rcClient.Height <= 0) continue;

                var tl = new POINT { X = 0, Y = 0 };
                ClientToScreen(hWnd, ref tl);

                int right = tl.X + rcClient.Right;
                int bottom = tl.Y + rcClient.Bottom;

                _wins.Add(new ExcelWin(hWnd, new RECT { Left = tl.X, Top = tl.Y, Right = right, Bottom = bottom }));
            }

            for (int i = 0; i < _excelHwndsToRemove.Count; i++)
                _excelHwnds.Remove(_excelHwndsToRemove[i]);

            return _wins;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool IsExcelClass(StringBuilder sb)
        {
            // "XLMAIN"
            return sb.Length == 6 &&
                   sb[0] == 'X' && sb[1] == 'L' && sb[2] == 'M' &&
                   sb[3] == 'A' && sb[4] == 'I' && sb[5] == 'N';
        }


        private static List<ExcelWin> GetExcelWindows()
        {
            var wins = new List<ExcelWin>(4);

            EnumWindows((hWnd, _) =>
            {
                if (!IsWindowVisible(hWnd) || IsIconic(hWnd)) return true;

                var sb = new StringBuilder(256);
                GetClassName(hWnd, sb, sb.Capacity);
                if (!string.Equals(sb.ToString(), EXCEL_CLASS, StringComparison.Ordinal))
                    return true;

                if (!GetClientRect(hWnd, out var rcClient)) return true;
                if (rcClient.Width <= 0 || rcClient.Height <= 0) return true;

                var tl = new POINT { X = rcClient.Left, Y = rcClient.Top };
                var br = new POINT { X = rcClient.Right, Y = rcClient.Bottom };
                ClientToScreen(hWnd, ref tl);
                ClientToScreen(hWnd, ref br);

                var screenRect = new RECT { Left = tl.X, Top = tl.Y, Right = br.X, Bottom = br.Y };
                wins.Add(new ExcelWin(hWnd, screenRect));
                return true;
            }, IntPtr.Zero);

            return wins;
        }

        private void RemoveOtherSizesForHwnd(IntPtr hwnd, int keepW, int keepH)
        {
            List<CacheKey>? kill = null;

            foreach (var kv in _cache)
            {
                if (kv.Key.Hwnd == hwnd && (kv.Key.W != keepW || kv.Key.H != keepH))
                {
                    kill ??= new List<CacheKey>();
                    kill.Add(kv.Key);
                }
            }

            if (kill == null) return;

            foreach (var k in kill)
            {
                _cache[k].Dispose();
                _cache.Remove(k);
            }
        }


        // ---------- High-performance capture cache (BitBlt -> DIB section) ----------
        private sealed class CaptureCache : IDisposable
        {
            public int Width { get; }
            public int Height { get; }
            public int SrcStride { get; } // w * 4

            public IntPtr BitsPtr => _bitsPtr;

            public ulong LastSig;
            public bool HasLastSig;

            private readonly IntPtr _memDc;
            private readonly IntPtr _hBmp;
            private readonly IntPtr _oldObj;
            private readonly IntPtr _bitsPtr;

            public ulong LastVisSig;
            public bool HasLastVisSig;
            public readonly List<RECT> LastVisibleRects = new(); // screen-space, already clipped to virtual screen

            public readonly List<RECT> TmpVisA = new(32);
            public readonly List<RECT> TmpVisB = new(64);
            public readonly List<RECT> TmpClipped = new(32);


            public CaptureCache(int w, int h)
            {
                Width = w;
                Height = h;
                SrcStride = w * 4;

                _memDc = CreateCompatibleDC(IntPtr.Zero);

                BITMAPINFO bmi = new BITMAPINFO
                {
                    biSize = (uint)Marshal.SizeOf<BITMAPINFO>(),
                    biWidth = w,
                    biHeight = -h,
                    biPlanes = 1,
                    biBitCount = 32,
                    biCompression = BI_RGB
                };

                _hBmp = CreateDIBSection(_memDc, ref bmi, DIB_RGB_COLORS, out _bitsPtr, IntPtr.Zero, 0);
                if (_hBmp == IntPtr.Zero) throw new Exception("CreateDIBSection failed.");

                _oldObj = SelectObject(_memDc, _hBmp);
            }

            public bool CaptureExcelClient(IntPtr hwnd)
            {
                // Capture the client area (Excel grid) into our DIB.
                // Note: PW_RENDERFULLCONTENT helps for some windows, Excel may ignore it.
                return PrintWindow(hwnd, _memDc, PW_CLIENTONLY | PW_RENDERFULLCONTENT);
            }

            public void CaptureScreenRegion(IntPtr screenDc, int screenX, int screenY)
            {
                BitBlt(_memDc, 0, 0, Width, Height, screenDc, screenX, screenY, SRCCOPY);
            }

            public void CaptureExcelClientOrFallback(IntPtr hwnd, IntPtr screenDc, int screenX, int screenY)
            {
                if (!CaptureExcelClient(hwnd))
                {
                    // Fallback: copy from screen (client rect position).
                    CaptureScreenRegion(screenDc, screenX, screenY);
                }
            }

            public void Dispose()
            {
                if (_oldObj != IntPtr.Zero) SelectObject(_memDc, _oldObj);
                if (_hBmp != IntPtr.Zero) DeleteObject(_hBmp);
                if (_memDc != IntPtr.Zero) DeleteDC(_memDc);
            }
        }



        // ---------- P/Invokes for capture ----------
        private const int SRCCOPY = 0x00CC0020;
        private const uint BI_RGB = 0;
        private const uint DIB_RGB_COLORS = 0;

        [StructLayout(LayoutKind.Sequential)]
        private struct BITMAPINFO
        {
            public uint biSize;
            public int biWidth;
            public int biHeight;
            public ushort biPlanes;
            public ushort biBitCount;
            public uint biCompression;
            public uint biSizeImage;
            public int biXPelsPerMeter;
            public int biYPelsPerMeter;
            public uint biClrUsed;
            public uint biClrImportant;
        }

        [DllImport("gdi32.dll", SetLastError = true)]
        private static extern IntPtr CreateCompatibleDC(IntPtr hdc);

        [DllImport("gdi32.dll", SetLastError = true)]
        private static extern bool DeleteDC(IntPtr hdc);

        [DllImport("gdi32.dll", SetLastError = true)]
        private static extern IntPtr SelectObject(IntPtr hdc, IntPtr h);

        [DllImport("gdi32.dll", SetLastError = true)]
        private static extern bool DeleteObject(IntPtr hObject);

        [DllImport("gdi32.dll", SetLastError = true)]
        private static extern bool BitBlt(IntPtr hdcDest, int xDest, int yDest, int wDest, int hDest,
                                         IntPtr hdcSrc, int xSrc, int ySrc, int rop);

        [DllImport("gdi32.dll", SetLastError = true)]
        private static extern IntPtr CreateDIBSection(
            IntPtr hdc,
            [In] ref BITMAPINFO pbmi,
            uint iUsage,
            out IntPtr ppvBits,
            IntPtr hSection,
            uint dwOffset);

        [DllImport("user32.dll")]
        private static extern IntPtr GetDC(IntPtr hWnd);

        [DllImport("user32.dll")]
        private static extern int ReleaseDC(IntPtr hWnd, IntPtr hDC);

        // ---------- P/Invokes for window styles / capture affinity ----------
        private const int GWL_EXSTYLE = -20;
        private const long WS_EX_TRANSPARENT = 0x20;
        private const long WS_EX_LAYERED = 0x80000;
        private const long WS_EX_NOACTIVATE = 0x08000000;
        private const long WS_EX_TOOLWINDOW = 0x00000080;

        [DllImport("user32.dll", EntryPoint = "GetWindowLongPtr", SetLastError = true)]
        private static extern IntPtr GetWindowLongPtr(IntPtr hWnd, int nIndex);

        [DllImport("user32.dll", EntryPoint = "SetWindowLongPtr", SetLastError = true)]
        private static extern IntPtr SetWindowLongPtr(IntPtr hWnd, int nIndex, IntPtr dwNewLong);

        [DllImport("user32.dll", SetLastError = true)]
        private static extern bool SetWindowDisplayAffinity(IntPtr hWnd, uint dwAffinity);

        private const uint WDA_EXCLUDEFROMCAPTURE = 0x11;

        private const uint GW_HWNDFIRST = 0;
        private const uint GW_HWNDNEXT = 2;

        [DllImport("user32.dll")] private static extern IntPtr GetTopWindow(IntPtr hWnd);
        [DllImport("user32.dll")] private static extern IntPtr GetWindow(IntPtr hWnd, uint uCmd);
        [DllImport("user32.dll")] private static extern bool GetWindowRect(IntPtr hWnd, out RECT lpRect);
        [DllImport("user32.dll")] private static extern int GetWindowTextLength(IntPtr hWnd);

        [DllImport("user32.dll", SetLastError = true)]
        private static extern bool PrintWindow(IntPtr hwnd, IntPtr hdcBlt, uint nFlags);

        private const uint PW_CLIENTONLY = 0x00000001;
        private const uint PW_RENDERFULLCONTENT = 0x00000002; // harmless if ignored

        [DllImport("user32.dll")]
        private static extern uint GetWindowThreadProcessId(IntPtr hWnd, out uint lpdwProcessId);

        [DllImport("kernel32.dll", SetLastError = true)]
        private static extern IntPtr OpenProcess(uint dwDesiredAccess, bool bInheritHandle, uint dwProcessId);

        [DllImport("kernel32.dll", SetLastError = true)]
        private static extern bool CloseHandle(IntPtr hObject);

        [DllImport("kernel32.dll", SetLastError = true, CharSet = CharSet.Unicode)]
        private static extern bool QueryFullProcessImageName(IntPtr hProcess, int dwFlags, StringBuilder lpExeName, ref int lpdwSize);

        private const uint PROCESS_QUERY_LIMITED_INFORMATION = 0x1000;

        [DllImport("user32.dll")]
        private static extern int GetSystemMetrics(int nIndex);

        private const int SM_XVIRTUALSCREEN = 76;
        private const int SM_YVIRTUALSCREEN = 77;
        private const int SM_CXVIRTUALSCREEN = 78;
        private const int SM_CYVIRTUALSCREEN = 79;

        private static bool Intersect(in RECT a, in RECT b, out RECT r)
        {
            int l = Math.Max(a.Left, b.Left);
            int t = Math.Max(a.Top, b.Top);
            int rr = Math.Min(a.Right, b.Right);
            int bb = Math.Min(a.Bottom, b.Bottom);
            r = new RECT { Left = l, Top = t, Right = rr, Bottom = bb };
            return r.Width > 0 && r.Height > 0;
        }

        private static List<RECT> SubtractRect(RECT src, RECT cut)
        {
            // Returns up to 4 rectangles (src minus cut)
            var res = new List<RECT>(4);

            if (!Intersect(src, cut, out var i))
            {
                res.Add(src);
                return res;
            }

            // Top band
            if (src.Top < i.Top)
                res.Add(new RECT { Left = src.Left, Top = src.Top, Right = src.Right, Bottom = i.Top });

            // Bottom band
            if (i.Bottom < src.Bottom)
                res.Add(new RECT { Left = src.Left, Top = i.Bottom, Right = src.Right, Bottom = src.Bottom });

            // Left band
            if (src.Left < i.Left)
                res.Add(new RECT { Left = src.Left, Top = i.Top, Right = i.Left, Bottom = i.Bottom });

            // Right band
            if (i.Right < src.Right)
                res.Add(new RECT { Left = i.Right, Top = i.Top, Right = src.Right, Bottom = i.Bottom });

            return res;
        }

        private List<RECT> GetVisibleExcelRects(IntPtr excelHwnd, RECT excelRect)
        {
            // Start with the full Excel rect, subtract occluders above it.
            var visible = new List<RECT> { excelRect };

            for (IntPtr h = GetTopWindow(IntPtr.Zero); h != IntPtr.Zero && h != excelHwnd; h = GetWindow(h, GW_HWNDNEXT))
            {
                if (!IsWindowVisible(h) || IsIconic(h)) continue;
                if (IsIgnoredOccluderWindow(h)) continue;

                // Skip our own overlay window if it ever appears in enumeration
                if (h == new WindowInteropHelper(this).Handle) continue;

                // Optional: skip “empty” windows (tooltips etc.)
                if (GetWindowTextLength(h) == 0) { /* you may want to keep these; leave as-is */ }

                if (!GetWindowRect(h, out var wr)) continue;

                // Only care if it overlaps Excel
                if (!Intersect(wr, excelRect, out var overlap)) continue;

                // Subtract this overlap from all current visible rects
                var next = new List<RECT>(visible.Count * 2);
                foreach (var v in visible)
                    next.AddRange(SubtractRect(v, overlap));

                visible = next;
                if (visible.Count == 0) break;
            }

            return visible;
        }

    }
}
