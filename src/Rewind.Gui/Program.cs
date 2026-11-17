using Rewind.Gui.Services;
using Velopack;

namespace Rewind.Gui;

internal static class Program
{
    [STAThread]
    private static int Main()
    {
        // Velopack's installer, updater and uninstaller start this program with arguments of their own and expect it
        // to do what they ask and exit, so this comes before anything else. The install puts the folder holding
        // rewind.exe on the user's PATH, so the command-line tool works in any terminal; uninstalling takes it off.
        VelopackApp.Build()
            .OnAfterInstallFastCallback(_ => CommandLinePath.TryAdd())
            .OnBeforeUninstallFastCallback(_ => CommandLinePath.TryRemove())
            .Run();

        var app = new App();
        app.InitializeComponent();
        return app.Run();
    }
}
