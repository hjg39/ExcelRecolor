using System;
using System.Collections.Generic;
using System.Drawing;
using System.Runtime.InteropServices;
using System.Text;
using System.Windows;
using System.Windows.Interop;
using System.Windows.Media.Imaging;
using System.Windows.Threading;
using System.Buffers.Binary;
using System.IO.Hashing;


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
        private const int TIMER_MS = 50; // 20 FPS-ish. Try 33 for 30 FPS, 100 for 10 FPS.
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

        public MainWindow()
        {
            InitializeComponent();
            BuildLut();
            _timer.Tick += (_, __) => Tick();
        }

        private void Window_Loaded(object sender, RoutedEventArgs e)
        {
            // Full virtual desktop (all monitors)
            _vsLeft = (int)SystemParameters.VirtualScreenLeft;
            _vsTop = (int)SystemParameters.VirtualScreenTop;
            _vsW = (int)SystemParameters.VirtualScreenWidth;
            _vsH = (int)SystemParameters.VirtualScreenHeight;

            Left = _vsLeft;
            Top = _vsTop;
            Width = _vsW;
            Height = _vsH;

            _overlay = new WriteableBitmap(_vsW, _vsH, 96, 96, System.Windows.Media.PixelFormats.Bgra32, null);
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
                        cc.CaptureExcelClientOrFallback(w.Hwnd, screenDc, w.Rect.Left, w.Rect.Top);

                        // Dirty-check ONCE for the whole captured client
                        ulong sig = ComputeSignatureFull(cc.BitsPtr, cc.SrcStride, fullW, fullH);
                        if (cc.HasLastSig && sig == cc.LastSig)
                            continue;

                        cc.LastSig = sig;
                        cc.HasLastSig = true;

                        // Now compute visible rects (to avoid painting over occluders)
                        var visibles = GetVisibleExcelRects(w.Hwnd, w.Rect);

                        foreach (var vr in visibles)
                        {
                            if (!ClipToVirtualScreen(vr, out var cap)) continue;

                            int capW = cap.Width;
                            int capH = cap.Height;

                            // Source offsets inside the captured Excel client buffer
                            int srcX = cap.Left - w.Rect.Left;
                            int srcY = cap.Top - w.Rect.Top;

                            // Destination offsets inside the overlay
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

                byte* dRowBytes = dstBase + (dstY + y) * dstStride + dstX * 4;
                uint* dRow = (uint*)dRowBytes;

                for (int x = 0; x < w; x++)
                {
                    int si = x * 4;
                    byte b = sRow[si + 0];
                    byte g = sRow[si + 1];
                    byte r = sRow[si + 2];

                    int rQ = r >> (8 - LUT_BITS);
                    int gQ = g >> (8 - LUT_BITS);
                    int bQ = b >> (8 - LUT_BITS);

                    int idx = ((rQ * LUT_SIZE + gQ) * LUT_SIZE + bQ);
                    dRow[x] = _lut32[idx];
                }
            }
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
                            HsvToRgb(PURPLE_HUE_DEG, s, v, out byte rr, out byte gg, out byte bb);

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
        private const float PURPLE_HUE_DEG = 285f;
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
