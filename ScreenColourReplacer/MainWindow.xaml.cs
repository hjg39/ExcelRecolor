using System.Buffers.Binary;
using System.IO;
using System.IO.Hashing;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Text;
using System.Windows;
using System.Windows.Interop;
using System.Windows.Media;
using System.Windows.Media.Imaging;
using System.Windows.Threading;



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
        private const int TIMER_MS = 16; // Try 33 for 30 FPS, 100 for 10 FPS.
        private const int LUT_BITS = 5;  // 5 => 32 levels/channel (32^3 = 32768)
        private const int LUT_SIZE = 1 << LUT_BITS;
        private const int LUT_MASK = LUT_SIZE - 1;

        private readonly HashSet<IntPtr> _aliveHwnds = new();
        private readonly List<CacheKey> _toDeleteKeys = new();

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

        // --- Cached handles ---
        private IntPtr _overlayHwnd;
        private IntPtr _screenDc;

        // --- Per-tick Z-order cache (built once per Tick) ---
        private readonly List<(IntPtr Hwnd, RECT Rect)> _zOrder = new(256);
        private readonly Dictionary<IntPtr, int> _zIndex = new(256);

        // --- Per-tick stale clears (screen-space rects, clipped) ---
        private readonly List<RECT> _staleRects = new(64);
        private readonly Dictionary<IntPtr, RECT> _tmpNewByHwnd = new(16);

        private int _inTick;

        private readonly List<ExcelWin> _wins = new(4);
        private readonly StringBuilder _classSb = new(16);

        private readonly List<DrawJob> _jobs = new(8);

        private int _zOrderCountdown = 0;
        private IntPtr _lastForeground = IntPtr.Zero;
        private const int ZORDER_REFRESH_EVERY_N_TICKS = 3; // ~90ms at 30ms tick

        // How often to re-scan the whole desktop for new Excel windows.
        // 10 ticks @ 30ms = ~300ms
        private const int EXCEL_ENUM_REFRESH_EVERY_N_TICKS = 10;

        private int _excelEnumCountdown = 0;

        // Known Excel top-level HWNDs (discovered by EnumWindows occasionally)
        private readonly List<IntPtr> _excelHwnds = new(8);
        private readonly List<IntPtr> _excelHwndsToRemove = new(8);
        private readonly HashSet<IntPtr> _excelFound = new(16);



        private struct DrawJob
        {
            public CaptureCache Cc;
            public RECT ExcelRect;         // screen rect of the Excel client
            public List<RECT> Visibles;    // screen-space rects (already clipped), owned by that CaptureCache
            public bool VisChanged;
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

            _timer.Start();
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



        private unsafe ulong ComputeSignatureFull(IntPtr bits, int stride, int w, int h)
        {
            int rowBytes = w * 4;

            var hasher = new XxHash3();

            // Your DIB uses SrcStride = w*4, so it's contiguous. If that ever changes, fallback row-wise.
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


        private unsafe ulong ComputeSignatureVisibleRects(
            IntPtr bits,
            int stride,
            in RECT excelRect,          // full Excel rect (screen coords)
            List<RECT> visibles)        // screen coords, clipped
        {

            byte* p = (byte*)bits.ToPointer();
            var hasher = new XxHash3();

            // include rect metadata so different placements don’t collide
            Span<byte> tmp = stackalloc byte[16];

            for (int i = 0; i < visibles.Count; i++)
            {
                var r = visibles[i];

                int srcX = r.Left - excelRect.Left;
                int srcY = r.Top - excelRect.Top;
                int w = r.Width;
                int h = r.Height;

                // Rect header
                BinaryPrimitives.WriteInt32LittleEndian(tmp.Slice(0, 4), srcX);
                BinaryPrimitives.WriteInt32LittleEndian(tmp.Slice(4, 4), srcY);
                BinaryPrimitives.WriteInt32LittleEndian(tmp.Slice(8, 4), w);
                BinaryPrimitives.WriteInt32LittleEndian(tmp.Slice(12, 4), h);
                hasher.Append(tmp);

                int rowBytes = w * 4;
                for (int y = 0; y < h; y++)
                {
                    var row = new ReadOnlySpan<byte>(p + (srcY + y) * stride + srcX * 4, rowBytes);
                    hasher.Append(row);
                }
            }

            Span<byte> out8 = stackalloc byte[8];
            hasher.GetCurrentHash(out8);
            return BinaryPrimitives.ReadUInt64LittleEndian(out8);
        }


        protected override void OnSourceInitialized(EventArgs e)
        {
            base.OnSourceInitialized(e);

            var hwnd = new WindowInteropHelper(this).Handle;
            _overlayHwnd = hwnd;

            var exStyle = GetWindowLongPtr(hwnd, GWL_EXSTYLE);
            exStyle = new IntPtr(exStyle.ToInt64() | WS_EX_TRANSPARENT | WS_EX_LAYERED | WS_EX_NOACTIVATE | WS_EX_TOOLWINDOW);
            SetWindowLongPtr(hwnd, GWL_EXSTYLE, exStyle);

            SetWindowDisplayAffinity(hwnd, WDA_EXCLUDEFROMCAPTURE);
        }

        private void TickCore()
        {
            if (_overlay == null) return;

            EnsureExcelHwndsUpToDate();
            var wins = GetExcelWindows_FromKnownHwnds();


            // 1) Compute stale regions from previous snapshot -> current (no lock)
            CollectStaleRegions(_lastWins, wins, _staleRects);
            CoalesceRectsInPlace(_staleRects);


            // IMPORTANT: _wins is reused, so we must snapshot into _lastWins (not assign reference!)
            _lastWins.Clear();
            _lastWins.AddRange(wins);

            // If no Excel windows, only clear stale (lock only for blit)
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

            // 2) Build occluder Z-order ONCE per tick (no lock)
            var interest = UnionAll(wins);

            IntPtr fg = GetForegroundWindow();
            bool fgChanged = fg != _lastForeground;
            _lastForeground = fg;

            // If Excel moved/appeared/disappeared this tick, stale rects will be non-empty.
            bool excelChanged = _staleRects.Count != 0;

            if (excelChanged || fgChanged || _zOrderCountdown <= 0)
            {
                BuildZOrderCache(interest);
                _zOrderCountdown = ZORDER_REFRESH_EVERY_N_TICKS;
            }
            else
            {
                _zOrderCountdown--;
            }


            // 3) Phase A: determine what needs drawing + capture/hash OUTSIDE overlay lock
            _jobs.Clear();

            IntPtr screenDc = _screenDc;
            if (screenDc == IntPtr.Zero) return;

            for (int wi = 0; wi < wins.Count; wi++)
            {
                var w = wins[wi];

                if (!ClipToVirtualScreen(w.Rect, out var fullCap)) continue; // fullCap = Excel clipped to virtual screen

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
                var visiblesRaw = GetVisibleExcelRects_FromZ(w.Rect, excelZi, cc.TmpVisA, cc.TmpVisB);

                // Clip to virtual screen into reused list
                var visibles = cc.TmpClipped;
                visibles.Clear();
                for (int i = 0; i < visiblesRaw.Count; i++)
                    if (ClipToVirtualScreen(visiblesRaw[i], out var cap))
                        visibles.Add(cap);

                CoalesceRectsInPlace(visibles);

                // Visibility signature
                ulong visSig = ComputeRectsSignature_NoSort(visibles);
                bool visChanged = !cc.HasLastVisSig || visSig != cc.LastVisSig;

                // If fully hidden, don't capture/hash; just clear last drawn if visibility changed
                if (visibles.Count == 0)
                {
                    if (!visChanged)
                        continue;

                    cc.LastVisSig = visSig;
                    cc.HasLastVisSig = true;

                    _jobs.Add(new DrawJob { Cc = cc, ExcelRect = w.Rect, Visibles = visibles, VisChanged = visChanged });
                    continue;
                }

                // Fully visible if the only visible rect == fullCap
                bool fullyVisible = (visibles.Count == 1 && RectsEqual(visibles[0], fullCap));

                ulong sig;

                // Capture + hash (outside lock)
                if (fullyVisible)
                {
                    // Full capture + full hash
                    cc.CaptureScreenRegion(screenDc, w.Rect.Left, w.Rect.Top); // same as your current fallback
                    sig = ComputeSignatureFull(cc.BitsPtr, cc.SrcStride, fullW, fullH);
                }
                else
                {
                    // Only capture visible pieces + hash only those pieces
                    cc.CaptureVisibleRects(screenDc, w.Rect, visibles);
                    sig = ComputeSignatureVisibleRects(cc.BitsPtr, cc.SrcStride, w.Rect, visibles);
                }

                bool contentChanged = !cc.HasLastSig || sig != cc.LastSig;

                if (!contentChanged && !visChanged)
                    continue;

                // Update sig cache (we computed sig in both branches above)
                cc.LastSig = sig;
                cc.HasLastSig = true;

                // Update visibility cache
                cc.LastVisSig = visSig;
                cc.HasLastVisSig = true;

                _jobs.Add(new DrawJob { Cc = cc, ExcelRect = w.Rect, Visibles = visibles, VisChanged = visChanged });

            }

            // If nothing to draw and no stale to clear, we can skip lock entirely
            if (_jobs.Count == 0 && _staleRects.Count == 0)
            {
                CleanupCacheForClosedWindows(wins);
                return;
            }

            // 4) Phase B: do all backbuffer writes inside overlay lock
            _overlay.Lock();
            try
            {
                IntPtr dstBackBuffer = _overlay.BackBuffer;
                int dstStride = _overlay.BackBufferStride;

                RECT dirty = default;
                bool hasDirty = false;

                // Clear stale rects
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

                // ONE dirty rect for everything touched this tick
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
                if (!Intersect(wr, interest, out _)) continue; // <<< prune FIRST

                if (IsIgnoredOccluderWindow(h)) continue;      // <<< expensive check LAST

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

            // Occluders are windows above Excel => indices [0 .. excelZIndex-1]
            for (int zi = 0; zi < excelZIndex && cur.Count != 0; zi++)
            {
                var oc = _zOrder[zi].Rect;

                // Quick reject: if it doesn't overlap the full Excel rect, skip
                if (!Intersect(oc, excelRect, out var cut)) continue;

                next.Clear();
                for (int i = 0; i < cur.Count; i++)
                    SubtractRectInto(cur[i], cut, next);

                // swap
                var tmp = cur;
                cur = next;
                next = tmp;
            }

            return cur; // either a or b
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool CanMergeH(in RECT a, in RECT b) =>
    a.Top == b.Top && a.Bottom == b.Bottom && a.Right == b.Left;

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool CanMergeV(in RECT a, in RECT b) =>
            a.Left == b.Left && a.Right == b.Right && a.Bottom == b.Top;

        private static void CoalesceRectsInPlace(List<RECT> rects)
        {
            if (rects.Count < 2) return;

            // Sort once here so:
            //  - coalescing is effective
            //  - rect order becomes stable, letting you remove sorts elsewhere if desired
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

            // 1) Horizontal merge pass
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

            // 2) Vertical merge pass (same sort order still works)
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
                        // Snipping Tool / clipping overlay (most common)
                        if (EndsWithExe(sb, "ScreenClippingHost.exe") || EndsWithExe(sb, "SnippingTool.exe"))
                            ignored = true;
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

            const int shift = 8 - LUT_BITS;

            for (int y = 0; y < h; y++)
            {
                uint* s = (uint*)(srcBase + (srcY + y) * srcStride) + srcX;
                uint* d = (uint*)(dstBase + (dstY + y) * dstStride) + dstX;

                for (int x = 0; x < w; x++)
                {
                    uint src = s[x] | 0xFF000000u; // force opaque alpha

                    // BGRA in memory: B 0..7, G 8..15, R 16..23
                    int bQ = (int)((src >> shift) & LUT_MASK);
                    int gQ = (int)((src >> (8 + shift)) & LUT_MASK);
                    int rQ = (int)((src >> (16 + shift)) & LUT_MASK);

                    int idx = (rQ << (2 * LUT_BITS)) | (gQ << LUT_BITS) | bQ;

                    uint mapped = _lut32[idx];
                    d[x] = (mapped != 0) ? mapped : src;
                }
            }
        }

        private void BuildLut()
        {
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
                            _lut32[idx] = (uint)(bb | (gg << 8) | (rr << 16) | (255u << 24));
                        }
                        else
                        {
                            // put a sentinel with A=0 to mean "not a match"
                            _lut32[idx] = 0u;
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
            (161.94f, 12f, 0.18f), // #6ED5B6-ish
        };

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

            // mix
            x ^= s + 0x9E3779B97F4A7C15UL;
            x *= PRIME;
            return x;
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

        private void EnsureExcelHwndsUpToDate()
        {
            // If we currently have none, scan immediately (keeps startup responsive)
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

            // Remove anything no longer present
            _excelHwndsToRemove.Clear();
            for (int i = 0; i < _excelHwnds.Count; i++)
                if (!_excelFound.Contains(_excelHwnds[i]))
                    _excelHwndsToRemove.Add(_excelHwnds[i]);

            for (int i = 0; i < _excelHwndsToRemove.Count; i++)
                _excelHwnds.Remove(_excelHwndsToRemove[i]);

            // Add newly found
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

                // If hwnd got destroyed OR reused by a non-Excel window, drop it.
                if (!IsWindow(hWnd) || !IsWindowVisible(hWnd) || IsIconic(hWnd))
                {
                    // Keep minimized/hidden Excel? If you prefer keeping them, change this:
                    // - If IsWindow(hWnd) is true but it's minimized, DON'T remove, just continue.
                    // I’d suggest keeping minimized ones:
                    if (!IsWindow(hWnd)) _excelHwndsToRemove.Add(hWnd);
                    continue;
                }

                if (!GetClientRect(hWnd, out var rcClient)) continue;
                if (rcClient.Width <= 0 || rcClient.Height <= 0) continue;

                // Client origin (0,0) -> screen
                var tl = new POINT { X = 0, Y = 0 };
                ClientToScreen(hWnd, ref tl);

                int right = tl.X + rcClient.Right;   // width
                int bottom = tl.Y + rcClient.Bottom; // height

                _wins.Add(new ExcelWin(hWnd, new RECT { Left = tl.X, Top = tl.Y, Right = right, Bottom = bottom }));
            }

            // Apply removals
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

        private void RemoveOtherSizesForHwnd(IntPtr hwnd, int keepW, int keepH)
        {
            _toDeleteKeys.Clear();

            foreach (var kv in _cache)
                if (kv.Key.Hwnd == hwnd && (kv.Key.W != keepW || kv.Key.H != keepH))
                    _toDeleteKeys.Add(kv.Key);

            for (int i = 0; i < _toDeleteKeys.Count; i++)
            {
                var k = _toDeleteKeys[i];
                _cache[k].Dispose();
                _cache.Remove(k);
            }
        }

        static bool EndsWithExe(StringBuilder sb, string exe)
        {
            // compare trailing filename case-insensitive
            int len = sb.Length;
            int slash = -1;
            for (int i = len - 1; i >= 0; i--)
            {
                char c = sb[i];
                if (c == '\\' || c == '/') { slash = i; break; }
            }
            int start = slash + 1;
            int fnLen = len - start;
            if (fnLen != exe.Length) return false;

            for (int i = 0; i < fnLen; i++)
            {
                char a = char.ToLowerInvariant(sb[start + i]);
                char b = char.ToLowerInvariant(exe[i]);
                if (a != b) return false;
            }
            return true;
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

            // in CaptureCache
            public void CaptureVisibleRects(IntPtr screenDc, in RECT excelRect, List<RECT> visibles)
            {
                for (int i = 0; i < visibles.Count; i++)
                {
                    var cap = visibles[i];

                    int w = cap.Width, h = cap.Height;
                    if (w <= 0 || h <= 0) continue;

                    // Destination in the DIB (Excel-local coords)
                    int dstX = cap.Left - excelRect.Left;
                    int dstY = cap.Top - excelRect.Top;

                    // Source on screen (screen coords)
                    BitBlt(_memDc, dstX, dstY, w, h, screenDc, cap.Left, cap.Top, SRCCOPY);
                }
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
                CaptureScreenRegion(screenDc, screenX, screenY);
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

        [DllImport("user32.dll")]
        private static extern IntPtr GetForegroundWindow();

        [DllImport("user32.dll")] private static extern bool IsWindow(IntPtr hWnd);


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

        private static void SubtractRectInto(in RECT src, in RECT cut, List<RECT> dst)
        {
            if (!Intersect(src, cut, out var i))
            {
                dst.Add(src);
                return;
            }

            // Top band
            if (src.Top < i.Top)
                dst.Add(new RECT { Left = src.Left, Top = src.Top, Right = src.Right, Bottom = i.Top });

            // Bottom band
            if (i.Bottom < src.Bottom)
                dst.Add(new RECT { Left = src.Left, Top = i.Bottom, Right = src.Right, Bottom = src.Bottom });

            // Left band
            if (src.Left < i.Left)
                dst.Add(new RECT { Left = src.Left, Top = i.Top, Right = i.Left, Bottom = i.Bottom });

            // Right band
            if (i.Right < src.Right)
                dst.Add(new RECT { Left = i.Right, Top = i.Top, Right = src.Right, Bottom = i.Bottom });
        }


        private List<RECT> GetVisibleExcelRects_NoAlloc(
            IntPtr excelHwnd,
            RECT excelRect,
            List<RECT> a,
            List<RECT> b,
            IntPtr overlayHwnd)
        {
            a.Clear();
            a.Add(excelRect);

            var cur = a;
            var next = b;

            for (IntPtr h = GetTopWindow(IntPtr.Zero);
                 h != IntPtr.Zero && h != excelHwnd;
                 h = GetWindow(h, GW_HWNDNEXT))
            {
                if (!IsWindowVisible(h) || IsIconic(h)) continue;
                if (IsIgnoredOccluderWindow(h)) continue;
                if (h == overlayHwnd) continue;

                if (!GetWindowRect(h, out var wr)) continue;
                if (!Intersect(wr, excelRect, out var overlap)) continue;

                next.Clear();

                for (int i = 0; i < cur.Count; i++)
                    SubtractRectInto(cur[i], overlap, next);

                // swap buffers
                var tmp = cur;
                cur = next;
                next = tmp;

                if (cur.Count == 0) break;
            }

            return cur; // IMPORTANT: this is either 'a' or 'b'
        }



    }
}
