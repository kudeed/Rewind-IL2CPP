using System.Globalization;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Data;
using MaterialDesignThemes.Wpf;

namespace Rewind.Gui;

/// <summary>
/// Stacks list rows the way Android 16's settings do: a small gap between rows, large rounded corners on the
/// outside of the group and small ones between rows. Rows that are collapsed do not count, so the group keeps its
/// shape when some are hidden. A Border child gets the corners as its CornerRadius, any other control as
/// ButtonAssist.CornerRadius, which the row templates use.
/// </summary>
public sealed class ListGroup : Panel
{
    public double Gap { get; set; } = 2;
    public double OuterRadius { get; set; } = 24;
    public double InnerRadius { get; set; } = 4;

    protected override Size MeasureOverride(Size available)
    {
        var visible = InternalChildren.Cast<UIElement>().Where(c => c.Visibility != Visibility.Collapsed).ToList();
        double width = 0, height = 0;
        for (int i = 0; i < visible.Count; i++)
        {
            double top = i == 0 ? OuterRadius : InnerRadius;
            double bottom = i == visible.Count - 1 ? OuterRadius : InnerRadius;
            Shape(visible[i], new CornerRadius(top, top, bottom, bottom));
            visible[i].Measure(new Size(available.Width, double.PositiveInfinity));
            width = Math.Max(width, visible[i].DesiredSize.Width);
            height += visible[i].DesiredSize.Height + (i > 0 ? Gap : 0);
        }
        return new Size(double.IsInfinity(available.Width) ? width : available.Width, height);
    }

    protected override Size ArrangeOverride(Size final)
    {
        double y = 0;
        bool first = true;
        foreach (UIElement child in InternalChildren)
        {
            if (child.Visibility == Visibility.Collapsed) continue;
            if (!first) y += Gap;
            first = false;
            child.Arrange(new Rect(0, y, final.Width, child.DesiredSize.Height));
            y += child.DesiredSize.Height;
        }
        return final;
    }

    private static void Shape(UIElement child, CornerRadius corners)
    {
        if (child is Border border)
        {
            if (border.CornerRadius != corners) border.CornerRadius = corners;
        }
        else if (!ButtonAssist.GetCornerRadius(child).Equals(corners))
        {
            ButtonAssist.SetCornerRadius(child, corners);
        }
    }
}

/// <summary>Shows a page while the selected page index equals the converter parameter.</summary>
public sealed class PageVisibility : IValueConverter
{
    public object Convert(object value, Type targetType, object parameter, CultureInfo culture) =>
        value is int index && parameter is string p && int.TryParse(p, out int page) && index == page
            ? Visibility.Visible
            : Visibility.Collapsed;

    public object ConvertBack(object value, Type targetType, object parameter, CultureInfo culture) =>
        throw new NotSupportedException();
}

/// <summary>An entry of the navigation rail.</summary>
/// <remarks>Spin: how far the icon turns, in degrees, when its page is chosen.</remarks>
public sealed record NavItem(string Label, PackIconKind Icon, PackIconKind SelectedIcon, double Spin = 0);
