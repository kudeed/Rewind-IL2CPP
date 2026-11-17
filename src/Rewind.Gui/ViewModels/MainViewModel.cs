using CommunityToolkit.Mvvm.ComponentModel;
using MaterialDesignThemes.Wpf;
using Rewind.Gui.Services;

namespace Rewind.Gui.ViewModels;

public sealed partial class MainViewModel : ObservableObject
{
    public const int DecompilePage = 0;
    public const int SettingsPage = 1;

    public MainViewModel(GuiSettings settings)
    {
        Decompile = new DecompileViewModel(settings, Messages);
        Settings = new SettingsViewModel(settings, Messages, this);
    }

    public SnackbarMessageQueue Messages { get; } = new(TimeSpan.FromSeconds(8));

    public IReadOnlyList<NavItem> NavItems { get; } =
    [
        new("Decompile", PackIconKind.RewindOutline, PackIconKind.Rewind, -360),
        new("Settings", PackIconKind.CogOutline, PackIconKind.Cog, 180),
        new("About", PackIconKind.InformationOutline, PackIconKind.Information),
    ];

    public DecompileViewModel Decompile { get; }

    public SettingsViewModel Settings { get; }

    [ObservableProperty]
    private int _selectedPage;

    /// <summary>After the window is shown: the update check, when updates are automatic.</summary>
    public void Started() => Settings.Started();

    public void ShowSettings() => SelectedPage = SettingsPage;
}
