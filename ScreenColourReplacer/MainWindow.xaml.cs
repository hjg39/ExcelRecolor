using System;
using System.Drawing;
using System.Drawing.Imaging;
using System.Runtime.InteropServices;
using System.Windows;
using System.Windows.Interop;
using System.Windows.Media;
using System.Windows.Media.Imaging;
using System.Windows.Threading;

namespace ScreenColourReplacer
{
    public partial class MainWindow : Window
    {
        private readonly DispatcherTimer _timer = new DispatcherTimer
        {
            Interval = TimeSpan.FromMilliseconds(100) // start at 10 FPS; adjust later
        };

        private WriteableBitmap? _overlay;
        private byte[]? _mask; // BGRA buffer
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
            if (_overlay == null || _mask == null) return;

            // 1) Capture screen into a 32bpp bitmap
            using var bmp = new Bitmap(_w, _h, System.Drawing.Imaging.PixelFormat.Format32bppArgb);
            using (var g = Graphics.FromImage(bmp))
            {
                g.CopyFromScreen(_left, _top, 0, 0, new System.Drawing.Size(_w, _h), CopyPixelOperation.SourceCopy);
            }

            // 2) Read pixels and build the overlay mask (green where black else transparent)
            var rect = new System.Drawing.Rectangle(0, 0, _w, _h);
            var data = bmp.LockBits(rect, ImageLockMode.ReadOnly, System.Drawing.Imaging.PixelFormat.Format32bppArgb);

            try
            {
                int srcStride = data.Stride;
                int srcBytes = srcStride * _h;
                byte[] src = new byte[srcBytes];
                Marshal.Copy(data.Scan0, src, 0, srcBytes);

                // Build mask in BGRA32 (WPF expects BGRA for PixelFormats.Bgra32)
                // Source is 32bpp ARGB in memory as BGRA on little-endian Windows (same byte order),
                // but we don't assume stride matches; we remap per pixel.
                for (int y = 0; y < _h; y++)
                {
                    int srcRow = y * srcStride;
                    int dstRow = y * _stride;

                    for (int x = 0; x < _w; x++)
                    {
                        int si = srcRow + x * 4;
                        byte b = src[si + 0];
                        byte g2 = src[si + 1];
                        byte r = src[si + 2];
                        // byte a = src[si + 3]; // not needed for test

                        int di = dstRow + x * 4;

                        // EXACT black:
                        if (r == 0 && g2 == 0 && b == 0)
                        {
                            _mask[di + 0] = 0;   // B
                            _mask[di + 1] = 255; // G
                            _mask[di + 2] = 0;   // R
                            _mask[di + 3] = 255; // A (opaque)
                        }
                        else
                        {
                            _mask[di + 0] = 0;
                            _mask[di + 1] = 0;
                            _mask[di + 2] = 0;
                            _mask[di + 3] = 0;   // fully transparent
                        }
                    }
                }
            }
            finally
            {
                bmp.UnlockBits(data);
            }

            // 3) Push mask to the overlay
            _overlay.WritePixels(new Int32Rect(0, 0, _w, _h), _mask, _stride, 0);
        }

        // ---- Click-through / no-activate ----
        protected override void OnSourceInitialized(EventArgs e)
        {
            base.OnSourceInitialized(e);

            var hwnd = new WindowInteropHelper(this).Handle;
            var exStyle = GetWindowLongPtr(hwnd, GWL_EXSTYLE);

            exStyle = new IntPtr(exStyle.ToInt64() | WS_EX_TRANSPARENT | WS_EX_LAYERED | WS_EX_NOACTIVATE | WS_EX_TOOLWINDOW);
            SetWindowLongPtr(hwnd, GWL_EXSTYLE, exStyle);
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
    }
}
