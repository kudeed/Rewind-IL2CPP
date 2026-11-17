using System.ComponentModel;
using System.Globalization;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Media;
using System.Windows.Media.Animation;
using MaterialDesignThemes.Wpf;

namespace Rewind.Gui.Expressive;

/// <summary>
/// A spring, as Material 3 Expressive moves things: it overshoots and settles instead of easing in a curve.
/// Damping 1 settles without overshoot; lower values bounce (0.5 is lively, 0.8 a little).
/// </summary>
public sealed class Spring : EasingFunctionBase
{
    public static readonly DependencyProperty DampingProperty =
        DependencyProperty.Register(nameof(Damping), typeof(double), typeof(Spring), new PropertyMetadata(0.7));

    public Spring() => EasingMode = EasingMode.EaseIn;

    public double Damping
    {
        get => (double)GetValue(DampingProperty);
        set => SetValue(DampingProperty, value);
    }

    protected override double EaseInCore(double t)
    {
        double z = Math.Clamp(Damping, 0.05, 1.0);
        if (z >= 0.999)
        {
            const double w = 8;
            return 1 - Math.Exp(-w * t) * (1 + w * t);
        }
        // The envelope has decayed to a fraction of a percent when the animation ends.
        const double decay = 6.5;
        double omega = decay / z;
        double damped = omega * Math.Sqrt(1 - z * z);
        return 1 - Math.Exp(-decay * t) * (Math.Cos(damped * t) + decay / damped * Math.Sin(damped * t));
    }

    protected override Freezable CreateInstanceCore() => new Spring();
}

/// <summary>The motion of the expressive controls, as attached properties any element can use.</summary>
public static class Motion
{
    public static DoubleAnimation SpringTo(double to, double milliseconds, double damping) =>
        new(to, TimeSpan.FromMilliseconds(milliseconds)) { EasingFunction = new Spring { Damping = damping } };

    /// <summary>A scale and a rotation about the element's center, made once and reused.</summary>
    public static (ScaleTransform Scale, RotateTransform Rotate) Transforms(UIElement element)
    {
        element.RenderTransformOrigin = new Point(0.5, 0.5);
        if (element.RenderTransform is TransformGroup { Children.Count: 2 } g && g.Children[0] is ScaleTransform s && g.Children[1] is RotateTransform r)
            return (s, r);
        var scale = new ScaleTransform(1, 1);
        var rotate = new RotateTransform(0);
        element.RenderTransform = new TransformGroup { Children = { scale, rotate } };
        return (scale, rotate);
    }

    // ---- Pop: an icon that changes springs into its new form

    public static readonly DependencyProperty PopProperty =
        DependencyProperty.RegisterAttached("Pop", typeof(bool), typeof(Motion), new PropertyMetadata(false, OnPopChanged));

    public static bool GetPop(DependencyObject d) => (bool)d.GetValue(PopProperty);
    public static void SetPop(DependencyObject d, bool value) => d.SetValue(PopProperty, value);

    private static readonly DependencyPropertyDescriptor KindDescriptor =
        DependencyPropertyDescriptor.FromProperty(PackIcon.KindProperty, typeof(PackIcon));

    private static void OnPopChanged(DependencyObject d, DependencyPropertyChangedEventArgs e)
    {
        if (d is not PackIcon icon || e.NewValue is not true) return;
        KindDescriptor.AddValueChanged(icon, (_, _) => PopNow(icon));
    }

    public static void PopNow(UIElement element)
    {
        if (!element.IsVisible) return;
        var (scale, rotate) = Transforms(element);
        scale.BeginAnimation(ScaleTransform.ScaleXProperty, new DoubleAnimation(0.4, 1, TimeSpan.FromMilliseconds(520)) { EasingFunction = new Spring { Damping = 0.45 } });
        scale.BeginAnimation(ScaleTransform.ScaleYProperty, new DoubleAnimation(0.4, 1, TimeSpan.FromMilliseconds(520)) { EasingFunction = new Spring { Damping = 0.45 } });
        rotate.BeginAnimation(RotateTransform.AngleProperty, new DoubleAnimation(-45, 0, TimeSpan.FromMilliseconds(520)) { EasingFunction = new Spring { Damping = 0.55 } });
    }

    // ---- Spinning: turns while true, then springs to rest on a whole turn

    public static readonly DependencyProperty SpinningProperty =
        DependencyProperty.RegisterAttached("Spinning", typeof(bool), typeof(Motion), new PropertyMetadata(false, OnSpinningChanged));

    public static bool GetSpinning(DependencyObject d) => (bool)d.GetValue(SpinningProperty);
    public static void SetSpinning(DependencyObject d, bool value) => d.SetValue(SpinningProperty, value);

    private static void OnSpinningChanged(DependencyObject d, DependencyPropertyChangedEventArgs e)
    {
        if (d is not UIElement element) return;
        var (_, rotate) = Transforms(element);
        double now = rotate.Angle % 360;
        if (e.NewValue is true)
        {
            rotate.BeginAnimation(RotateTransform.AngleProperty,
                new DoubleAnimation(now, now + 360, TimeSpan.FromMilliseconds(900)) { RepeatBehavior = RepeatBehavior.Forever });
        }
        else
        {
            double current = rotate.Angle;
            rotate.BeginAnimation(RotateTransform.AngleProperty, null);
            rotate.Angle = current % 360;
            rotate.BeginAnimation(RotateTransform.AngleProperty, SpringTo(360, 700, 0.5));
        }
    }

    // ---- Rotation: springs to the angle it is given (chevrons that open and close)

    public static readonly DependencyProperty RotationProperty =
        DependencyProperty.RegisterAttached("Rotation", typeof(double), typeof(Motion), new PropertyMetadata(0.0, OnRotationChanged));

    public static double GetRotation(DependencyObject d) => (double)d.GetValue(RotationProperty);
    public static void SetRotation(DependencyObject d, double value) => d.SetValue(RotationProperty, value);

    private static void OnRotationChanged(DependencyObject d, DependencyPropertyChangedEventArgs e)
    {
        if (d is not UIElement element) return;
        var (_, rotate) = Transforms(element);
        rotate.BeginAnimation(RotateTransform.AngleProperty, SpringTo((double)e.NewValue, 600, 0.5));
    }

    // ---- SpringIn: an element that appears grows into place

    public static readonly DependencyProperty SpringInProperty =
        DependencyProperty.RegisterAttached("SpringIn", typeof(bool), typeof(Motion), new PropertyMetadata(false, OnSpringInChanged));

    public static bool GetSpringIn(DependencyObject d) => (bool)d.GetValue(SpringInProperty);
    public static void SetSpringIn(DependencyObject d, bool value) => d.SetValue(SpringInProperty, value);

    private static void OnSpringInChanged(DependencyObject d, DependencyPropertyChangedEventArgs e)
    {
        if (d is not UIElement element || e.NewValue is not true) return;
        element.IsVisibleChanged += (_, args) =>
        {
            if (args.NewValue is not true) return;
            var (scale, _) = Transforms(element);
            scale.BeginAnimation(ScaleTransform.ScaleXProperty, new DoubleAnimation(0.88, 1, TimeSpan.FromMilliseconds(600)) { EasingFunction = new Spring { Damping = 0.55 } });
            scale.BeginAnimation(ScaleTransform.ScaleYProperty, new DoubleAnimation(0.88, 1, TimeSpan.FromMilliseconds(600)) { EasingFunction = new Spring { Damping = 0.55 } });
            element.BeginAnimation(UIElement.OpacityProperty, new DoubleAnimation(0, 1, TimeSpan.FromMilliseconds(200)));
        };
    }

    // ---- Count: a number that counts up to its value when it changes

    public static readonly DependencyProperty CountProperty =
        DependencyProperty.RegisterAttached("Count", typeof(double), typeof(Motion), new PropertyMetadata(double.NaN, OnCountChanged));

    public static double GetCount(DependencyObject d) => (double)d.GetValue(CountProperty);
    public static void SetCount(DependencyObject d, double value) => d.SetValue(CountProperty, value);

    public static readonly DependencyProperty CountFormatProperty =
        DependencyProperty.RegisterAttached("CountFormat", typeof(string), typeof(Motion), new PropertyMetadata("{0:N0}"));

    public static string GetCountFormat(DependencyObject d) => (string)d.GetValue(CountFormatProperty);
    public static void SetCountFormat(DependencyObject d, string value) => d.SetValue(CountFormatProperty, value);

    private static readonly DependencyProperty ShownProperty =
        DependencyProperty.RegisterAttached("Shown", typeof(double), typeof(Motion), new PropertyMetadata(0.0, OnShownChanged));

    private static void OnCountChanged(DependencyObject d, DependencyPropertyChangedEventArgs e)
    {
        if (d is not TextBlock text || e.NewValue is not double target || double.IsNaN(target)) return;
        text.BeginAnimation(ShownProperty, new DoubleAnimation(0, target, TimeSpan.FromMilliseconds(1100))
        {
            EasingFunction = new CubicEase { EasingMode = EasingMode.EaseOut },
        });
    }

    private static void OnShownChanged(DependencyObject d, DependencyPropertyChangedEventArgs e)
    {
        if (d is TextBlock text) text.Text = string.Format(CultureInfo.CurrentCulture, GetCountFormat(text), (double)e.NewValue);
    }

    // ---- Navigation rail items: the pill springs open, the icon spins or pops

    public static readonly DependencyProperty NavItemProperty =
        DependencyProperty.RegisterAttached("NavItem", typeof(bool), typeof(Motion), new PropertyMetadata(false, OnNavItemChanged));

    public static bool GetNavItem(DependencyObject d) => (bool)d.GetValue(NavItemProperty);
    public static void SetNavItem(DependencyObject d, bool value) => d.SetValue(NavItemProperty, value);

    private static void OnNavItemChanged(DependencyObject d, DependencyPropertyChangedEventArgs e)
    {
        if (d is not ListBoxItem item || e.NewValue is not true) return;
        item.Loaded += (_, _) => NavState(item, animate: false);
        item.Selected += (_, _) => NavState(item, animate: true);
        item.Unselected += (_, _) => NavState(item, animate: true);
    }

    private static void NavState(ListBoxItem item, bool animate)
    {
        if (item.Template?.FindName("Pill", item) is not FrameworkElement pill ||
            item.Template.FindName("Icon", item) is not FrameworkElement icon) return;
        var (scale, _) = Transforms(pill);
        if (!animate)
        {
            pill.Opacity = item.IsSelected ? 1 : 0;
            scale.ScaleX = 1;
            return;
        }
        if (item.IsSelected)
        {
            pill.BeginAnimation(UIElement.OpacityProperty, new DoubleAnimation(1, TimeSpan.FromMilliseconds(120)));
            scale.BeginAnimation(ScaleTransform.ScaleXProperty, new DoubleAnimation(0.3, 1, TimeSpan.FromMilliseconds(650)) { EasingFunction = new Spring { Damping = 0.5 } });
            double spin = item.DataContext is NavItem { Spin: var s } ? s : 0;
            var (iconScale, rotate) = Transforms(icon);
            if (spin != 0)
                rotate.BeginAnimation(RotateTransform.AngleProperty, new DoubleAnimation(0, spin, TimeSpan.FromMilliseconds(800)) { EasingFunction = new Spring { Damping = 0.6 } });
            iconScale.BeginAnimation(ScaleTransform.ScaleXProperty, new DoubleAnimation(0.7, 1, TimeSpan.FromMilliseconds(600)) { EasingFunction = new Spring { Damping = 0.45 } });
            iconScale.BeginAnimation(ScaleTransform.ScaleYProperty, new DoubleAnimation(0.7, 1, TimeSpan.FromMilliseconds(600)) { EasingFunction = new Spring { Damping = 0.45 } });
        }
        else
        {
            pill.BeginAnimation(UIElement.OpacityProperty, new DoubleAnimation(0, TimeSpan.FromMilliseconds(160)));
            scale.BeginAnimation(ScaleTransform.ScaleXProperty, new DoubleAnimation(0.5, TimeSpan.FromMilliseconds(200)));
        }
    }
}

/// <summary>Turns a bool into an angle (the converter parameter) or 0.</summary>
public sealed class BoolToAngle : System.Windows.Data.IValueConverter
{
    public object Convert(object value, Type targetType, object parameter, CultureInfo culture) =>
        value is true && double.TryParse(parameter as string, NumberStyles.Float, CultureInfo.InvariantCulture, out double angle) ? angle : 0.0;

    public object ConvertBack(object value, Type targetType, object parameter, CultureInfo culture) =>
        throw new NotSupportedException();
}
