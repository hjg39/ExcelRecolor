using System.Runtime.InteropServices;
using System.Windows;

namespace ScreenColourReplacer
{
    /// <summary>
    /// Interaction logic for App.xaml
    /// </summary>
    public partial class App : Application
    {
        [DllImport("user32.dll")]
        private static extern bool SetProcessDpiAwarenessContext(IntPtr value);

        // Per-monitor v2
        private static readonly IntPtr DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2 = new IntPtr(-4);

        protected override void OnStartup(StartupEventArgs e)
        {
            // Must be called before creating any windows
            SetProcessDpiAwarenessContext(DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2);

            base.OnStartup(e);
        }
    }

}
