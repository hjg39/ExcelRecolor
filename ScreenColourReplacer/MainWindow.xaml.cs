using System.Runtime.InteropServices;
using System.Text;
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
        private const int TIMER_MS = 30; // 20 FPS-ish. Try 33 for 30 FPS, 100 for 10 FPS.
        private const int LUT_BITS = 5;  // 5 => 32 levels/channel (32^3 = 32768)
        private const int LUT_SIZE = 1 << LUT_BITS;
        private const int LUT_MASK = LUT_SIZE - 1;

        // ---------- Overlay / desktop ----------
        private WriteableBitmap? _overlay;
        private int _vsLeft, _vsTop, _vsW, _vsH;

        private readonly DispatcherTimer _timer = new DispatcherTimer
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

            _timer.Start();
        }


        private unsafe ulong ComputeSignatureFull(IntPtr bits, int stride, int w, int h)
        {
            int rowBytes = w * 4;
            byte* p = (byte*)bits.ToPointer();

            var hasher = new XxHash3();
            for (int y = 0; y < h; y++)
            {
                var row = new ReadOnlySpan<byte>(p + y * stride, rowBytes);
                hasher.Append(row);
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
            var exStyle = GetWindowLongPtr(hwnd, GWL_EXSTYLE);
            exStyle = new IntPtr(exStyle.ToInt64() | WS_EX_TRANSPARENT | WS_EX_LAYERED | WS_EX_NOACTIVATE | WS_EX_TOOLWINDOW);
            SetWindowLongPtr(hwnd, GWL_EXSTYLE, exStyle);

            // Prevent overlay being included in the capture (stops feedback flicker)
            SetWindowDisplayAffinity(hwnd, WDA_EXCLUDEFROMCAPTURE);
        }

        private void Tick()
        {
            if (_overlay == null) return;

            var wins = GetExcelWindows();

            if (wins.Count == 0)
            {
                if (_lastWins.Count != 0)
                {
                    ClearStaleRegions(_lastWins);
                    _lastWins.Clear();
                }
                return;
            }

            // Keep your existing stale-clear logic BEFORE Lock() (because it uses WritePixels)
            ClearChangedOrClosedRegions(_lastWins, wins);
            _lastWins = wins;

            // ---- Lock overlay once ----
            _overlay.Lock();
            try
            {
                IntPtr dstBackBuffer = _overlay.BackBuffer;
                int dstStride = _overlay.BackBufferStride;

                IntPtr screenDc = GetDC(IntPtr.Zero);
                try
                {
                    foreach (var w in wins)
                    {
                        // Clip to virtual screen just to avoid pointless work
                        if (!ClipToVirtualScreen(w.Rect, out var capWin)) continue;

                        int fullW = w.Rect.Width;
                        int fullH = w.Rect.Height;
                        if (fullW <= 0 || fullH <= 0) continue;

                        // Cache is for the FULL client size (not clipped)
                        var key = new CacheKey(w.Hwnd, fullW, fullH);
                        if (!_cache.TryGetValue(key, out var cc))
                        {
                            cc = new CaptureCache(fullW, fullH);
                            RemoveOtherSizesForHwnd(w.Hwnd, fullW, fullH);

                            _cache[key] = cc;
                        }

                        // Capture ONCE for the whole Excel client
                        //cc.CaptureExcelClientOrFallback(w.Hwnd, screenDc, w.Rect.Left, w.Rect.Top);

                        // Compute visible rects first (screen-space) and clip to virtual screen.
                        // We'll use this list BOTH for clearing and drawing.
                        var visiblesRaw = GetVisibleExcelRects(w.Hwnd, w.Rect);

                        var visibles = new List<RECT>(visiblesRaw.Count);
                        foreach (var vr in visiblesRaw)
                        {
                            if (ClipToVirtualScreen(vr, out var cap))
                                visibles.Add(cap);
                        }

                        // Visibility signature (changes when Excel goes behind something / uncovered)
                        ulong visSig = ComputeRectsSignature(visibles);

                        // Capture ONCE for the whole Excel client
                        cc.CaptureExcelClientOrFallback(w.Hwnd, screenDc, w.Rect.Left, w.Rect.Top);

                        // Pixel signature (content changes)
                        ulong sig = ComputeSignatureFull(cc.BitsPtr, cc.SrcStride, fullW, fullH);

                        // Decide if we must update: content OR visibility changed
                        bool contentChanged = !cc.HasLastSig || sig != cc.LastSig;
                        bool visChanged = !cc.HasLastVisSig || visSig != cc.LastVisSig;

                        if (!contentChanged && !visChanged)
                            continue;

                        // ---- IMPORTANT: clear what we drew last time for this hwnd ----
                        foreach (var old in cc.LastVisibleRects)
                        {
                            // old is already clipped to virtual screen
                            int oldDstX = old.Left - _vsLeft;
                            int oldDstY = old.Top - _vsTop;
                            ClearBackBufferRect(dstBackBuffer, dstStride, oldDstX, oldDstY, old.Width, old.Height);

                            _overlay.AddDirtyRect(new Int32Rect(oldDstX, oldDstY, old.Width, old.Height));
                        }

                        // Update stored signatures + rects
                        cc.LastSig = sig;
                        cc.HasLastSig = true;

                        cc.LastVisSig = visSig;
                        cc.HasLastVisSig = true;

                        cc.LastVisibleRects.Clear();
                        cc.LastVisibleRects.AddRange(visibles);

                        // ---- Draw current visible rects ----
                        foreach (var cap in visibles) // cap already clipped
                        {
                            int capW = cap.Width;
                            int capH = cap.Height;

                            int srcX = cap.Left - w.Rect.Left;
                            int srcY = cap.Top - w.Rect.Top;

                            int dstX = cap.Left - _vsLeft;
                            int dstY = cap.Top - _vsTop;

                            ApplyLutToBackBuffer_WithSrcOffset(
                                cc.BitsPtr, cc.SrcStride,
                                dstBackBuffer, dstStride,
                                srcX, srcY,
                                dstX, dstY,
                                capW, capH);

                            _overlay.AddDirtyRect(new Int32Rect(dstX, dstY, capW, capH));
                        }

                    }
                }
                finally
                {
                    ReleaseDC(IntPtr.Zero, screenDc);
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

        // ---------- Clear only stale areas ----------
        private void ClearChangedOrClosedRegions(List<ExcelWin> oldWins, List<ExcelWin> newWins)
        {
            if (_overlay == null) return;

            // Build a lookup of new rects by hwnd
            var newByHwnd = new Dictionary<IntPtr, RECT>(newWins.Count);
            foreach (var nw in newWins) newByHwnd[nw.Hwnd] = nw.Rect;

            foreach (var ow in oldWins)
            {
                if (!newByHwnd.TryGetValue(ow.Hwnd, out var nr) || !RectsEqual(ow.Rect, nr))
                {
                    // window closed or moved/resized => clear old region
                    if (ClipToVirtualScreen(ow.Rect, out var capOld))
                        WriteTransparentRect(capOld);
                }
            }
        }

        private void ClearStaleRegions(List<ExcelWin> oldWins)
        {
            foreach (var ow in oldWins)
            {
                if (ClipToVirtualScreen(ow.Rect, out var capOld))
                    WriteTransparentRect(capOld);
            }
        }

        private void WriteTransparentRect(RECT cap)
        {
            if (_overlay == null) return;
            int w = cap.Width;
            int h = cap.Height;
            if (w <= 0 || h <= 0) return;

            // reuse a small clear buffer keyed by size (simple local static cache)
            var key = (w, h);
            if (!ClearBufferCache.TryGetValue(key, out var buf))
            {
                buf = new byte[w * h * 4]; // zero = transparent
                ClearBufferCache[key] = buf;
            }
            // buf is already all zeros; no need to clear each time

            int destX = cap.Left - _vsLeft;
            int destY = cap.Top - _vsTop;
            _overlay.WritePixels(new Int32Rect(destX, destY, w, h), buf, w * 4, 0);
        }

        private static readonly Dictionary<(int W, int H), byte[]> ClearBufferCache = new();

        private static bool RectsEqual(RECT a, RECT b) =>
            a.Left == b.Left && a.Top == b.Top && a.Right == b.Right && a.Bottom == b.Bottom;

        private void CleanupCacheForClosedWindows(List<ExcelWin> wins)
        {
            // Alive Excel hwnds
            var alive = new HashSet<IntPtr>();
            foreach (var w in wins) alive.Add(w.Hwnd);

            // Collect keys to delete (cache is keyed by CacheKey now)
            List<CacheKey>? toDelete = null;

            foreach (var kv in _cache)
            {
                if (!alive.Contains(kv.Key.Hwnd))
                {
                    toDelete ??= new List<CacheKey>();
                    toDelete.Add(kv.Key);
                }
            }

            if (toDelete == null) return;

            foreach (var key in toDelete)
            {
                _cache[key].Dispose();
                _cache.Remove(key);
            }
        }


        // ---------- LUT application ----------
        private unsafe void ApplyLutToBackBuffer_WithSrcOffset(
            IntPtr srcBits, int srcStride,
            IntPtr dstBackBuffer, int dstStride,
            int srcX, int srcY,
            int dstX, int dstY,
            int w, int h)
        {
            byte* srcBase = (byte*)srcBits.ToPointer();
            byte* dstBase = (byte*)dstBackBuffer.ToPointer();

            for (int y = 0; y < h; y++)
            {
                byte* sRow = srcBase + (srcY + y) * srcStride + srcX * 4;
                uint* dRow = (uint*)(dstBase + (dstY + y) * dstStride + dstX * 4);

                for (int x = 0; x < w; x++)
                {
                    int si = x * 4;

                    // Read source as a packed pixel (BGRA in memory)
                    uint src = *(uint*)(sRow + si) | 0xFF000000u;

                    byte b = (byte)(src & 0xFF);
                    byte g = (byte)((src >> 8) & 0xFF);
                    byte r = (byte)((src >> 16) & 0xFF);

                    int rQ = r >> (8 - LUT_BITS);
                    int gQ = g >> (8 - LUT_BITS);
                    int bQ = b >> (8 - LUT_BITS);

                    int idx = ((rQ * LUT_SIZE + gQ) * LUT_SIZE + bQ);
                    uint mapped = _lut32[idx];

                    if (mapped != 0)
                    {
                        // Match: write shifted color (opaque)
                        dRow[x] = mapped;
                    }
                    else
                    {
                        dRow[x] = src;
                    }
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
