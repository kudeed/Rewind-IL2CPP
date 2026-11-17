using System.IO;
using System.Windows;
using System.Windows.Threading;
using Microsoft.Win32;
using Rewind.Gui.Services;
using Rewind.Gui.ViewModels;

namespace Rewind.Gui;

public partial class App : Application
{
    private GuiSettings _settings = new();

    protected override void OnStartup(StartupEventArgs e)
    {
        base.OnStartup(e);
        DispatcherUnhandledException += OnUnhandled;

        _settings = SettingsStore.Load();
        ThemeService.Apply(_settings);
        // "System" follows Windows' light or dark setting, also when it changes while the app is open.
        SystemEvents.UserPreferenceChanged += (_, args) =>
        {
            if (args.Category == UserPreferenceCategory.General && _settings.Theme == AppTheme.System)
                Dispatcher.BeginInvoke(() => ThemeService.Apply(_settings));
        };

        var model = new MainViewModel(_settings);
        var window = new MainWindow { DataContext = model };
        MainWindow = window;
        window.Show();
        model.Started();
    }

    protected override void OnExit(ExitEventArgs e)
    {
        SettingsStore.Save(_settings);
        base.OnExit(e);
    }

    private void OnUnhandled(object sender, DispatcherUnhandledExceptionEventArgs e)
    {
        string log = SettingsStore.Folder;
        try
        {
            Directory.CreateDirectory(log);
            log = Path.Combine(log, "gui-errors.log");
            File.AppendAllText(log, $"{DateTime.Now:u} {e.Exception}{Environment.NewLine}{Environment.NewLine}");
        }
        catch (Exception ex) when (ex is IOException or UnauthorizedAccessException)
        {
            log = "(the log could not be written)";
        }
        MessageBox.Show(MainWindow, $"Something went wrong in the Rewind window:\n\n{e.Exception.Message}\n\nDetails were written to {log}.",
            "Rewind", MessageBoxButton.OK, MessageBoxImage.Error);
        e.Handled = true;
    }
}
