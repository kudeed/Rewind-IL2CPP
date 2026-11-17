using System.Windows;
using System.Windows.Controls;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Threading;
using Rewind.Gui.Services;
using Rewind.Gui.ViewModels;

namespace Rewind.Gui.Views;

public partial class DecompileView : UserControl
{
    private DecompileViewModel? _model;
    private ScrollViewer? _scroller;
    // Follows the newest output line until it is scrolled away from the end, and again once back at the end.
    private bool _follow = true;

    public DecompileView()
    {
        InitializeComponent();
        DataContextChanged += (_, _) =>
        {
            if (_model != null) _model.LineAdded -= KeepNewestInSight;
            _model = DataContext as DecompileViewModel;
            if (_model != null) _model.LineAdded += KeepNewestInSight;
        };
        Log.Loaded += (_, _) =>
        {
            _scroller ??= FindScroller(Log);
            if (_scroller != null) _scroller.ScrollChanged += OnScrolled;
        };
        // Ctrl+C on the output copies the selected lines.
        Log.CommandBindings.Add(new CommandBinding(ApplicationCommands.Copy, (_, e) =>
        {
            var lines = Log.SelectedItems.OfType<LogLine>().OrderBy(l => Log.Items.IndexOf(l)).Select(l => l.Text);
            Shell.CopyText(string.Join(Environment.NewLine, lines));
            e.Handled = true;
        }));
    }

    private void OnScrolled(object sender, ScrollChangedEventArgs e)
    {
        // Moves caused by new lines or a resize do not change whether the end is followed; the user's own do.
        if (e.ExtentHeightChange == 0 && e.ViewportHeightChange == 0 && _scroller != null)
            _follow = _scroller.VerticalOffset >= _scroller.ScrollableHeight - 1;
    }

    private void KeepNewestInSight()
    {
        if (_model?.Lines.Count <= 1) _follow = true;
        if (!_follow) return;
        Dispatcher.BeginInvoke(DispatcherPriority.Background, () => _scroller?.ScrollToEnd());
    }

    private static ScrollViewer? FindScroller(DependencyObject parent)
    {
        for (int i = 0; i < VisualTreeHelper.GetChildrenCount(parent); i++)
        {
            DependencyObject child = VisualTreeHelper.GetChild(parent, i);
            if (child is ScrollViewer scroller) return scroller;
            if (FindScroller(child) is { } found) return found;
        }
        return null;
    }
}
