using System;
using System.Drawing;
using System.Drawing.Imaging;
using System.Runtime.InteropServices;
using System.Windows;
using System.Windows.Interop;
using System.Windows.Media.Imaging;
using System.Windows.Threading;

namespace ScreenColourReplacer
{
    public partial class MainWindow : Window
    {
        private System.Collections.Generic.List<RECT> _lastExcelRects = new();

        private readonly DispatcherTimer _timer = new DispatcherTimer
        {
            Interval = TimeSpan.FromMilliseconds(100) // ~10 FPS
        };

        private WriteableBitmap? _overlay;
        private byte[]? _mask; // BGRA buffer (WPF PixelFormats.Bgra32)
        private int _w, _h, _stride;
        private int _left, _top;

        public MainWindow()
        {
            InitializeComponent();
            _timer.Tick += (_, __) => Tick();
        }

        private void Window_Loaded(object sender, RoutedEventArgs e)
        {
            // Full virtual desktop (all monitors)
            _left = (int)SystemParameters.VirtualScreenLeft;
            _top = (int)SystemParameters.VirtualScreenTop;
            _w = (int)SystemParameters.VirtualScreenWidth;
            _h = (int)SystemParameters.VirtualScreenHeight;

            Left = _left;
            Top = _top;
            Width = _w;
            Height = _h;

            _stride = _w * 4; // BGRA32
            _mask = new byte[_stride * _h];

            _overlay = new WriteableBitmap(_w, _h, 96, 96, System.Windows.Media.PixelFormats.Bgra32, null);
            OverlayImage.Source = _overlay;

            _timer.Start();
        }

        private void Tick()
        {
            if (_overlay == null) return;

            var excelRects = GetExcelClientRects();

            // If Excel isn't present, clear once and bail.
            if (excelRects.Count == 0)
            {
                if (_lastExcelRects.Count != 0)
                {
                    ClearOverlay();
                    _lastExcelRects.Clear();
                }
                return;
            }

            // If the Excel window moved/resized, clear the old painted areas (simple + correct).
            if (!SameRects(_lastExcelRects, excelRects))
            {
                ClearOverlay();
                _lastExcelRects = excelRects;
            }

            foreach (var rc in excelRects)
            {
                // Clip to virtual screen
                int capLeft = Math.Max(rc.Left, _left);
                int capTop = Math.Max(rc.Top, _top);
                int capRight = Math.Min(rc.Right, _left + _w);
                int capBottom = Math.Min(rc.Bottom, _top + _h);

                int capW = capRight - capLeft;
                int capH = capBottom - capTop;
                if (capW <= 0 || capH <= 0) continue;

                // Capture only this Excel client region
                using var bmp = new Bitmap(capW, capH, PixelFormat.Format32bppArgb);
                using (var g = Graphics.FromImage(bmp))
                {
                    g.CopyFromScreen(capLeft, capTop, 0, 0, new System.Drawing.Size(capW, capH), CopyPixelOperation.SourceCopy);
                }

                // Read pixels
                var data = bmp.LockBits(new System.Drawing.Rectangle(0, 0, capW, capH),
                                        ImageLockMode.ReadOnly, PixelFormat.Format32bppArgb);

                byte[] src;
                int srcStride;
                try
                {
                    srcStride = data.Stride;
                    src = new byte[srcStride * capH];
                    Marshal.Copy(data.Scan0, src, 0, src.Length);
                }
                finally
                {
                    bmp.UnlockBits(data);
                }

                // Build mask for this region only
                int localStride = capW * 4;
                byte[] localMask = new byte[localStride * capH];

                for (int y = 0; y < capH; y++)
                {
                    int srcRow = y * srcStride;
                    int dstRow = y * localStride;

                    for (int x = 0; x < capW; x++)
                    {
                        int si = srcRow + x * 4;
                        byte b = src[si + 0];
                        byte g2 = src[si + 1];
                        byte r = src[si + 2];

                        RgbToHsv(r, g2, b, out float h, out float s, out float v);
                        bool match = MatchesAnyTarget(h, s, v);

                        int di = dstRow + x * 4;

                        if (match)
                        {
                            HsvToRgb(PURPLE_HUE_DEG, s, v, out byte rr, out byte gg, out byte bb);
                            localMask[di + 0] = bb;
                            localMask[di + 1] = gg;
                            localMask[di + 2] = rr;
                            localMask[di + 3] = 255;
                        }
                        else
                        {
                            localMask[di + 3] = 0; // transparent
                        }
                    }
                }

                // Write this rect into the full-screen overlay at the correct offset
                int destX = capLeft - _left;
                int destY = capTop - _top;

                _overlay.WritePixels(new Int32Rect(destX, destY, capW, capH), localMask, localStride, 0);
            }
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

        // ---- Hue matching config ----
        // Replace these two green-ish hue families with a purple hue.
        // #60BD82 hue ≈ 141.94°, #9FC7B1 hue ≈ 147.00°
        private const float PURPLE_HUE_DEG = 285f; // 270–300 looks "purple"

        private const float MIN_V = 0.08f; // ignore near-black pixels (optional)

        private static readonly (float HueDeg, float TolDeg, float MinS)[] TARGETS =
        {
            (141.94f, 12f, 0.18f), // #60BD82-ish (more saturated)
            (147.00f, 12f, 0.10f), // #9FC7B1-ish (pastel / lower saturation)
            (148.42f, 12f, 0.04f),
            (124.86f, 12f, 0.18f),
            (76.47f, 12f, 0.18f),
            (110.77f, 12f, 0.18f),
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

            float h = (hDeg % 360f) / 60f; // 0..6
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
                default: r = v; g = p; b = q; break; // case 5
            }

            r8 = (byte)Math.Clamp((int)MathF.Round(r * 255f), 0, 255);
            g8 = (byte)Math.Clamp((int)MathF.Round(g * 255f), 0, 255);
            b8 = (byte)Math.Clamp((int)MathF.Round(b * 255f), 0, 255);
        }

        private const string EXCEL_CLASS = "XLMAIN";

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
        [DllImport("user32.dll", CharSet = CharSet.Unicode)] private static extern int GetClassName(IntPtr hWnd, System.Text.StringBuilder lpClassName, int nMaxCount);
        [DllImport("user32.dll")] private static extern bool IsWindowVisible(IntPtr hWnd);
        [DllImport("user32.dll")] private static extern bool IsIconic(IntPtr hWnd);

        [DllImport("user32.dll")] private static extern bool GetClientRect(IntPtr hWnd, out RECT lpRect);
        [DllImport("user32.dll")] private static extern bool ClientToScreen(IntPtr hWnd, ref POINT lpPoint);

        private static System.Collections.Generic.List<RECT> GetExcelClientRects()
        {
            var rects = new System.Collections.Generic.List<RECT>();

            EnumWindows((hWnd, _) =>
            {
                if (!IsWindowVisible(hWnd) || IsIconic(hWnd)) return true;

                var sb = new System.Text.StringBuilder(256);
                GetClassName(hWnd, sb, sb.Capacity);
                if (!string.Equals(sb.ToString(), EXCEL_CLASS, StringComparison.Ordinal))
                    return true;

                // client rect -> screen coords
                if (!GetClientRect(hWnd, out var rcClient)) return true;
                if (rcClient.Width <= 0 || rcClient.Height <= 0) return true;

                var tl = new POINT { X = rcClient.Left, Y = rcClient.Top };
                var br = new POINT { X = rcClient.Right, Y = rcClient.Bottom };
                ClientToScreen(hWnd, ref tl);
                ClientToScreen(hWnd, ref br);

                rects.Add(new RECT { Left = tl.X, Top = tl.Y, Right = br.X, Bottom = br.Y });
                return true;
            }, IntPtr.Zero);

            return rects;
        }

        private static bool SameRects(System.Collections.Generic.List<RECT> a, System.Collections.Generic.List<RECT> b)
        {
            if (a.Count != b.Count) return false;
            for (int i = 0; i < a.Count; i++)
            {
                if (a[i].Left != b[i].Left || a[i].Top != b[i].Top || a[i].Right != b[i].Right || a[i].Bottom != b[i].Bottom)
                    return false;
            }
            return true;
        }

        private void ClearOverlay()
        {
            if (_overlay == null || _mask == null) return;
            Array.Clear(_mask, 0, _mask.Length);
            _overlay.WritePixels(new Int32Rect(0, 0, _w, _h), _mask, _stride, 0);
        }

    }
}
