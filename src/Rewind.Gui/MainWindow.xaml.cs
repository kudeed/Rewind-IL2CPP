using System.ComponentModel;
using System.IO;
using System.Windows;
using System.Windows.Interop;
using System.Windows.Media;
using System.Windows.Media.Animation;
using Rewind.Gui.Services;
using Rewind.Gui.ViewModels;

namespace Rewind.Gui;

public partial class MainWindow : Window
{
    public MainWindow()
    {
        InitializeComponent();
        SourceInitialized += (_, _) => StyleTitleBar();
        ThemeService.Changed += StyleTitleBar;
        Closed += (_, _) => ThemeService.Changed -= StyleTitleBar;
        foreach (FrameworkElement page in new FrameworkElement[] { DecompilePage, SettingsPage, AboutPage })
            page.IsVisibleChanged += (_, e) => { if (e.NewValue is true) Enter(page); };
    }

    private MainViewModel? Model => DataContext as MainViewModel;

    /// <summary>A page comes in on a spring: it rises into place, overshooting a little, as it fades in.</summary>
    private static void Enter(FrameworkElement page)
    {
        var move = new TranslateTransform(0, 48);
        page.RenderTransform = move;
        page.BeginAnimation(OpacityProperty, new DoubleAnimation(0, 1, TimeSpan.FromMilliseconds(200)));
        move.BeginAnimation(TranslateTransform.YProperty,
            new DoubleAnimation(48, 0, TimeSpan.FromMilliseconds(650)) { EasingFunction = new Expressive.Spring { Damping = 0.62 } });
    }

    private void OnDragOver(object sender, DragEventArgs e)
    {
        e.Effects = e.Data.GetDataPresent(DataFormats.FileDrop) ? DragDropEffects.Copy : DragDropEffects.None;
        e.Handled = true;
    }

    /// <summary>A game folder or file dropped anywhere on the window becomes the input.</summary>
    private void OnDrop(object sender, DragEventArgs e)
    {
        if (Model == null || e.Data.GetData(DataFormats.FileDrop) is not string[] { Length: > 0 } paths) return;
        string path = paths[0];
        if (!File.Exists(path) && !Directory.Exists(path)) return;
        Model.Decompile.Input = path;
        Model.SelectedPage = MainViewModel.DecompilePage;
        e.Handled = true;
    }

    protected override void OnClosing(CancelEventArgs e)
    {
        if (Model is { Decompile.IsRunning: true } model)
        {
            MessageBoxResult answer = MessageBox.Show(this, "Rewind is still running. Stop it and close the window?", "Rewind",
                MessageBoxButton.YesNo, MessageBoxImage.Question, MessageBoxResult.No);
            if (answer != MessageBoxResult.Yes)
            {
                e.Cancel = true;
                return;
            }
            model.Decompile.StopCommand.Execute(null);
        }
        base.OnClosing(e);
    }

    private void StyleTitleBar() => ThemeService.StyleTitleBar(new WindowInteropHelper(this).Handle);
}
