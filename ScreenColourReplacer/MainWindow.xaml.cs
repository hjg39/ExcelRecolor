using System;
using System.Collections.Generic;
using System.Drawing;
using System.Runtime.InteropServices;
using System.Text;
using System.Windows;
using System.Windows.Interop;
using System.Windows.Media.Imaging;
using System.Windows.Threading;

namespace ScreenColourReplacer
{
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
        private readonly Dictionary<IntPtr, CaptureCache> _cache = new();

        // Last seen windows for "clear stale regions"
        private List<ExcelWin> _lastWins = new();

        // Precomputed quantized RGB -> BGRA output (alpha=0 means transparent)
        // Stored as 4 bytes per entry (BGRA) for fast writes
        private readonly byte[] _lutBGRA = new byte[LUT_SIZE * LUT_SIZE * LUT_SIZE * 4];

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

            // No Excel => clear any previously drawn regions and stop doing work.
            if (wins.Count == 0)
            {
                if (_lastWins.Count != 0)
                {
                    ClearStaleRegions(_lastWins);
                    _lastWins.Clear();
                }
                return;
            }

            // Clear regions from windows that moved/closed (only those regions, not full screen)
            ClearChangedOrClosedRegions(_lastWins, wins);
            _lastWins = wins;

            // Capture + process each Excel window region
            foreach (var w in wins)
            {
                // Clip to virtual screen
                if (!ClipToVirtualScreen(w.Rect, out var cap)) continue;

                int capW = cap.Width;
                int capH = cap.Height;

                // Get/reuse cache for this hwnd and size
                if (!_cache.TryGetValue(w.Hwnd, out var cc) || cc.Width != capW || cc.Height != capH)
                {
                    cc?.Dispose();
                    cc = new CaptureCache(capW, capH);
                    _cache[w.Hwnd] = cc;
                }

                // Capture cap region into cc.SrcBytes (BGRA32)
                cc.CaptureScreenRegion(cap.Left, cap.Top);

                // Build mask in cc.MaskBytes using LUT (BGRA32)
                ApplyLut(cc.SrcBytes, cc.SrcStride, cc.MaskBytes, cc.MaskStride, capW, capH);

                // Write to overlay at correct offset
                int destX = cap.Left - _vsLeft;
                int destY = cap.Top - _vsTop;
                _overlay.WritePixels(new Int32Rect(destX, destY, capW, capH), cc.MaskBytes, cc.MaskStride, 0);
            }

            // Optional: clean caches for Excel windows that closed
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
            // Remove caches for hwnds not present anymore
            var alive = new HashSet<IntPtr>();
            foreach (var w in wins) alive.Add(w.Hwnd);

            // Collect to delete (avoid modifying dictionary while iterating)
            List<IntPtr>? toDelete = null;
            foreach (var kv in _cache)
            {
                if (!alive.Contains(kv.Key))
                {
                    toDelete ??= new List<IntPtr>();
                    toDelete.Add(kv.Key);
                }
            }
            if (toDelete == null) return;

            foreach (var h in toDelete)
            {
                _cache[h].Dispose();
                _cache.Remove(h);
            }
        }

        // ---------- LUT application ----------
        private void ApplyLut(byte[] srcBGRA, int srcStride, byte[] dstBGRA, int dstStride, int w, int h)
        {
            // Fast rejects: if your targets are mostly green-ish, early reject lots of pixels cheaply:
            // (kept simple here; LUT already cheap)
            for (int y = 0; y < h; y++)
            {
                int sRow = y * srcStride;
                int dRow = y * dstStride;

                for (int x = 0; x < w; x++)
                {
                    int si = sRow + x * 4;
                    byte b = srcBGRA[si + 0];
                    byte g = srcBGRA[si + 1];
                    byte r = srcBGRA[si + 2];

                    // Quantize to 5-bit bins
                    int rQ = r >> (8 - LUT_BITS);
                    int gQ = g >> (8 - LUT_BITS);
                    int bQ = b >> (8 - LUT_BITS);

                    int idx = (((rQ & LUT_MASK) * LUT_SIZE + (gQ & LUT_MASK)) * LUT_SIZE + (bQ & LUT_MASK)) * 4;

                    int di = dRow + x * 4;
                    dstBGRA[di + 0] = _lutBGRA[idx + 0];
                    dstBGRA[di + 1] = _lutBGRA[idx + 1];
                    dstBGRA[di + 2] = _lutBGRA[idx + 2];
                    dstBGRA[di + 3] = _lutBGRA[idx + 3];
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

                        int idx = (((rQ * LUT_SIZE + gQ) * LUT_SIZE + bQ) * 4);

                        if (match)
                        {
                            HsvToRgb(PURPLE_HUE_DEG, s, v, out byte rr, out byte gg, out byte bb);
                            _lutBGRA[idx + 0] = bb;
                            _lutBGRA[idx + 1] = gg;
                            _lutBGRA[idx + 2] = rr;
                            _lutBGRA[idx + 3] = 255;
                        }
                        else
                        {
                            _lutBGRA[idx + 0] = 0;
                            _lutBGRA[idx + 1] = 0;
                            _lutBGRA[idx + 2] = 0;
                            _lutBGRA[idx + 3] = 0; // transparent
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

        // ---------- High-performance capture cache (BitBlt -> DIB section) ----------
        private sealed class CaptureCache : IDisposable
        {
            public int Width { get; }
            public int Height { get; }
            public int SrcStride { get; }
            public int MaskStride { get; }

            public byte[] SrcBytes { get; }
            public byte[] MaskBytes { get; }

            private readonly IntPtr _memDc;
            private readonly IntPtr _hBmp;
            private readonly IntPtr _oldObj;
            private readonly IntPtr _bitsPtr;

            public CaptureCache(int w, int h)
            {
                Width = w;
                Height = h;
                SrcStride = w * 4;
                MaskStride = w * 4;

                SrcBytes = new byte[SrcStride * h];
                MaskBytes = new byte[MaskStride * h];

                _memDc = CreateCompatibleDC(IntPtr.Zero);

                // Create top-down 32bpp DIB section
                BITMAPINFO bmi = new BITMAPINFO
                {
                    biSize = (uint)Marshal.SizeOf<BITMAPINFO>(),
                    biWidth = w,
                    biHeight = -h, // negative => top-down
                    biPlanes = 1,
                    biBitCount = 32,
                    biCompression = BI_RGB
                };

                _hBmp = CreateDIBSection(_memDc, ref bmi, DIB_RGB_COLORS, out _bitsPtr, IntPtr.Zero, 0);
                if (_hBmp == IntPtr.Zero) throw new Exception("CreateDIBSection failed.");

                _oldObj = SelectObject(_memDc, _hBmp);
            }

            public void CaptureScreenRegion(int screenX, int screenY)
            {
                IntPtr screenDc = GetDC(IntPtr.Zero);
                try
                {
                    // Copy screen into our DIB section
                    BitBlt(_memDc, 0, 0, Width, Height, screenDc, screenX, screenY, SRCCOPY);
                }
                finally
                {
                    ReleaseDC(IntPtr.Zero, screenDc);
                }

                // Copy DIB pixels into managed SrcBytes (single Marshal.Copy; no LockBits/Bitmap)
                Marshal.Copy(_bitsPtr, SrcBytes, 0, SrcBytes.Length);
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
    }
}
