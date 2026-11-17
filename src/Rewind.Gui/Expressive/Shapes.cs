using System.Windows;
using System.Windows.Controls;
using System.Windows.Media;
using System.Windows.Media.Animation;

namespace Rewind.Gui.Expressive;

/// <summary>
/// The shapes of Material 3 Expressive (cookies, suns, bursts, clovers, ovals), as a radius around a center:
/// r(θ) = 1 + a·cos(nθ). Two shapes sampled at the same angles morph into each other point by point.
/// </summary>
public readonly record struct PolarShape(int Lobes, double Depth)
{
    public static readonly PolarShape Circle = new(0, 0);
    public static readonly PolarShape Cookie4 = new(4, 0.13);
    public static readonly PolarShape Cookie6 = new(6, 0.09);
    public static readonly PolarShape Cookie7 = new(7, 0.08);
    public static readonly PolarShape Cookie9 = new(9, 0.065);
    public static readonly PolarShape Cookie12 = new(12, 0.045);
    public static readonly PolarShape Sunny = new(8, 0.055);
    public static readonly PolarShape SoftBurst = new(10, 0.1);
    public static readonly PolarShape Pentagon = new(5, 0.11);
    public static readonly PolarShape Clover = new(4, 0.24);
    public static readonly PolarShape Oval = new(2, 0.12);

    public double Radius(double theta) => 1 + Depth * Math.Cos(Lobes * theta);

    /// <summary>Largest radius, to fit the shape in a box.</summary>
    public double Max => 1 + Math.Abs(Depth);

    public const int Samples = 144;

    public static Geometry Build(Func<double, double> radius, Point center, double scale, double rotationDegrees)
    {
        var geometry = new StreamGeometry();
        using (StreamGeometryContext g = geometry.Open())
        {
            double turn = rotationDegrees * Math.PI / 180;
            for (int i = 0; i < Samples; i++)
            {
                double theta = 2 * Math.PI * i / Samples;
                double r = radius(theta) * scale;
                var p = new Point(center.X + r * Math.Cos(theta + turn - Math.PI / 2), center.Y + r * Math.Sin(theta + turn - Math.PI / 2));
                if (i == 0) g.BeginFigure(p, true, true);
                else g.LineTo(p, true, true);
            }
        }
        geometry.Freeze();
        return geometry;
    }
}

/// <summary>
/// A filled expressive shape (a cookie behind an icon, a sun behind the logo), which can turn slowly.
/// </summary>
public sealed class ShapeView : FrameworkElement
{
    public static readonly DependencyProperty FillProperty = DependencyProperty.Register(nameof(Fill), typeof(Brush), typeof(ShapeView),
        new FrameworkPropertyMetadata(Brushes.Gray, FrameworkPropertyMetadataOptions.AffectsRender));
    public static readonly DependencyProperty LobesProperty = DependencyProperty.Register(nameof(Lobes), typeof(int), typeof(ShapeView),
        new FrameworkPropertyMetadata(9, FrameworkPropertyMetadataOptions.AffectsRender));
    public static readonly DependencyProperty DepthProperty = DependencyProperty.Register(nameof(Depth), typeof(double), typeof(ShapeView),
        new FrameworkPropertyMetadata(0.065, FrameworkPropertyMetadataOptions.AffectsRender));
    /// <summary>Seconds for a whole turn; 0 keeps it still.</summary>
    public static readonly DependencyProperty TurnSecondsProperty = DependencyProperty.Register(nameof(TurnSeconds), typeof(double), typeof(ShapeView),
        new PropertyMetadata(0.0, (d, _) => ((ShapeView)d).Turn()));

    public Brush Fill { get => (Brush)GetValue(FillProperty); set => SetValue(FillProperty, value); }
    public int Lobes { get => (int)GetValue(LobesProperty); set => SetValue(LobesProperty, value); }
    public double Depth { get => (double)GetValue(DepthProperty); set => SetValue(DepthProperty, value); }
    public double TurnSeconds { get => (double)GetValue(TurnSecondsProperty); set => SetValue(TurnSecondsProperty, value); }

    public ShapeView()
    {
        IsVisibleChanged += (_, _) => Turn();
    }

    private void Turn()
    {
        var (_, rotate) = Motion.Transforms(this);
        if (TurnSeconds <= 0 || !IsVisible)
        {
            rotate.BeginAnimation(RotateTransform.AngleProperty, null);
            return;
        }
        var spin = new DoubleAnimation(0, 360, TimeSpan.FromSeconds(TurnSeconds)) { RepeatBehavior = RepeatBehavior.Forever };
        Timeline.SetDesiredFrameRate(spin, 30);
        rotate.BeginAnimation(RotateTransform.AngleProperty, spin);
    }

    protected override void OnRender(DrawingContext dc)
    {
        var shape = new PolarShape(Lobes, Depth);
        double size = Math.Min(ActualWidth, ActualHeight);
        if (size <= 0) return;
        dc.DrawGeometry(Fill, null, PolarShape.Build(shape.Radius, new Point(ActualWidth / 2, ActualHeight / 2), size / 2 / shape.Max, 0));
    }
}

/// <summary>
/// The Material 3 Expressive loading indicator: a shape that keeps morphing into the next one while it spins,
/// on a round container.
/// </summary>
public sealed class LoadingIndicator : FrameworkElement
{
    private static readonly PolarShape[] Sequence =
    [
        PolarShape.SoftBurst, PolarShape.Cookie9, PolarShape.Pentagon, PolarShape.Oval,
        PolarShape.Sunny, PolarShape.Cookie4, PolarShape.Clover,
    ];

    private const double StepMilliseconds = 650;
    private const double MorphMilliseconds = 450;
    private static readonly Spring Morph = new() { Damping = 0.55 };

    public static readonly DependencyProperty FillProperty = DependencyProperty.Register(nameof(Fill), typeof(Brush), typeof(LoadingIndicator),
        new FrameworkPropertyMetadata(Brushes.Gray, FrameworkPropertyMetadataOptions.AffectsRender));
    public static readonly DependencyProperty ContainerProperty = DependencyProperty.Register(nameof(Container), typeof(Brush), typeof(LoadingIndicator),
        new FrameworkPropertyMetadata(null, FrameworkPropertyMetadataOptions.AffectsRender));

    public Brush Fill { get => (Brush)GetValue(FillProperty); set => SetValue(FillProperty, value); }
    public Brush? Container { get => (Brush?)GetValue(ContainerProperty); set => SetValue(ContainerProperty, value); }

    private readonly System.Diagnostics.Stopwatch _clock = new();
    private bool _hooked;

    public LoadingIndicator()
    {
        IsVisibleChanged += (_, _) => Hook(IsVisible);
        Unloaded += (_, _) => Hook(false);
        Loaded += (_, _) => Hook(IsVisible);
    }

    private void Hook(bool on)
    {
        if (on == _hooked) return;
        _hooked = on;
        if (on)
        {
            _clock.Restart();
            CompositionTarget.Rendering += OnFrame;
        }
        else
        {
            CompositionTarget.Rendering -= OnFrame;
            _clock.Stop();
        }
    }

    private void OnFrame(object? sender, EventArgs e) => InvalidateVisual();

    protected override void OnRender(DrawingContext dc)
    {
        double size = Math.Min(ActualWidth, ActualHeight);
        if (size <= 0) return;
        var center = new Point(ActualWidth / 2, ActualHeight / 2);
        if (Container != null) dc.DrawEllipse(Container, null, center, size / 2, size / 2);

        double ms = _clock.Elapsed.TotalMilliseconds;
        int step = (int)(ms / StepMilliseconds);
        double within = ms - step * StepMilliseconds;
        double t = Math.Clamp(within / MorphMilliseconds, 0, 1);
        double eased = Morph.Ease(t);
        PolarShape from = Sequence[step % Sequence.Length];
        PolarShape to = Sequence[(step + 1) % Sequence.Length];
        // A steady turn, plus a springy quarter turn with every change of shape.
        double rotation = ms / 1500.0 * 360 + (step + eased) * 90;
        double max = Math.Max(from.Max, to.Max);
        double scale = size * (Container != null ? 0.38 : 0.5) / max;
        dc.DrawGeometry(Fill, null, PolarShape.Build(theta => from.Radius(theta) + (to.Radius(theta) - from.Radius(theta)) * eased, center, scale, rotation));
    }
}

/// <summary>
/// The Material 3 Expressive linear progress indicator: the done part is a moving wave, the rest a flat track
/// ending in a dot. Without a value it runs a wavy stretch across the track again and again.
/// </summary>
public sealed class WavyProgress : FrameworkElement
{
    public static readonly DependencyProperty ValueProperty = DependencyProperty.Register(nameof(Value), typeof(double), typeof(WavyProgress),
        new FrameworkPropertyMetadata(0.0, FrameworkPropertyMetadataOptions.AffectsRender));
    public static readonly DependencyProperty MaximumProperty = DependencyProperty.Register(nameof(Maximum), typeof(double), typeof(WavyProgress),
        new FrameworkPropertyMetadata(100.0, FrameworkPropertyMetadataOptions.AffectsRender));
    public static readonly DependencyProperty IsIndeterminateProperty = DependencyProperty.Register(nameof(IsIndeterminate), typeof(bool), typeof(WavyProgress),
        new FrameworkPropertyMetadata(false, FrameworkPropertyMetadataOptions.AffectsRender));
    public static readonly DependencyProperty ActiveProperty = DependencyProperty.Register(nameof(Active), typeof(Brush), typeof(WavyProgress),
        new FrameworkPropertyMetadata(Brushes.Gray, FrameworkPropertyMetadataOptions.AffectsRender));
    public static readonly DependencyProperty TrackProperty = DependencyProperty.Register(nameof(Track), typeof(Brush), typeof(WavyProgress),
        new FrameworkPropertyMetadata(Brushes.LightGray, FrameworkPropertyMetadataOptions.AffectsRender));

    public double Value { get => (double)GetValue(ValueProperty); set => SetValue(ValueProperty, value); }
    public double Maximum { get => (double)GetValue(MaximumProperty); set => SetValue(MaximumProperty, value); }
    public bool IsIndeterminate { get => (bool)GetValue(IsIndeterminateProperty); set => SetValue(IsIndeterminateProperty, value); }
    public Brush Active { get => (Brush)GetValue(ActiveProperty); set => SetValue(ActiveProperty, value); }
    public Brush Track { get => (Brush)GetValue(TrackProperty); set => SetValue(TrackProperty, value); }

    private const double Thickness = 4;
    private const double Amplitude = 3;
    private const double Wavelength = 22;
    private const double Gap = 6;

    private readonly System.Diagnostics.Stopwatch _clock = new();
    private bool _hooked;

    public WavyProgress()
    {
        Height = 14;
        IsVisibleChanged += (_, _) => Hook(IsVisible);
        Unloaded += (_, _) => Hook(false);
        Loaded += (_, _) => Hook(IsVisible);
    }

    private void Hook(bool on)
    {
        if (on == _hooked) return;
        _hooked = on;
        if (on)
        {
            _clock.Restart();
            CompositionTarget.Rendering += OnFrame;
        }
        else
        {
            CompositionTarget.Rendering -= OnFrame;
            _clock.Stop();
        }
    }

    private void OnFrame(object? sender, EventArgs e) => InvalidateVisual();

    protected override void OnRender(DrawingContext dc)
    {
        double w = ActualWidth, mid = ActualHeight / 2;
        if (w <= Thickness * 2) return;
        double s = _clock.Elapsed.TotalSeconds;
        double phase = s * 2 * Math.PI * 1.2;
        var activePen = new Pen(Active, Thickness) { StartLineCap = PenLineCap.Round, EndLineCap = PenLineCap.Round, LineJoin = PenLineJoin.Round };
        var trackPen = new Pen(Track, Thickness) { StartLineCap = PenLineCap.Round, EndLineCap = PenLineCap.Round };
        double left = Thickness / 2, right = w - Thickness / 2;

        if (IsIndeterminate)
        {
            // A stretch that grows from the left and runs off to the right, about every 1.8 s.
            double cycle = s / 1.8 % 1.0;
            double head = Ease(Math.Clamp(cycle / 0.75, 0, 1));
            double tail = Ease(Math.Clamp((cycle - 0.25) / 0.75, 0, 1));
            double a = left + (right - left) * tail, b = left + (right - left) * head;
            if (a > left + Gap) dc.DrawLine(trackPen, new Point(left, mid), new Point(a - Gap, mid));
            if (b - a > 1) DrawWave(dc, activePen, a, b, mid, phase);
            if (b < right - Gap) dc.DrawLine(trackPen, new Point(b + Gap, mid), new Point(right, mid));
            return;
        }

        double fraction = Maximum > 0 ? Math.Clamp(Value / Maximum, 0, 1) : 0;
        double end = left + (right - left) * fraction;
        if (end > left + 0.5) DrawWave(dc, activePen, left, end, mid, phase);
        double trackStart = fraction > 0 ? end + Gap : left;
        if (trackStart < right) dc.DrawLine(trackPen, new Point(trackStart, mid), new Point(right, mid));
        // The stop dot at the end of the track.
        if (fraction < 1) dc.DrawEllipse(Active, null, new Point(right, mid), Thickness / 2, Thickness / 2);
    }

    private static double Ease(double t) => t < 0.5 ? 4 * t * t * t : 1 - Math.Pow(-2 * t + 2, 3) / 2;

    private static void DrawWave(DrawingContext dc, Pen pen, double from, double to, double mid, double phase)
    {
        var geometry = new StreamGeometry();
        using (StreamGeometryContext g = geometry.Open())
        {
            bool first = true;
            for (double x = from; ; x += 2)
            {
                double px = Math.Min(x, to);
                // The wave flattens near the ends, so the stretch starts and stops on the line.
                double edge = Math.Min(1, Math.Min(px - from, to - px) / 8);
                var p = new Point(px, mid + Amplitude * edge * Math.Sin(px / Wavelength * 2 * Math.PI - phase));
                if (first) g.BeginFigure(p, false, false);
                else g.LineTo(p, true, true);
                first = false;
                if (px >= to) break;
            }
        }
        geometry.Freeze();
        dc.DrawGeometry(null, pen, geometry);
    }
}

/// <summary>
/// The surface of an expressive control: a filled, outlined shape with a state layer, whose corners morph.
/// Squeeze (0..1) moves every corner toward PressedRadius (a pressed button turns from a pill to a rounded
/// square); Round (0..1) moves every corner to a full half-height (a chosen segment turns into a pill).
/// Both are meant to be animated with a Spring.
/// </summary>
public sealed class Surface : Decorator
{
    private static FrameworkPropertyMetadata Render(object value) => new(value, FrameworkPropertyMetadataOptions.AffectsRender);

    public static readonly DependencyProperty FillProperty = DependencyProperty.Register(nameof(Fill), typeof(Brush), typeof(Surface), Render(null!));
    public static readonly DependencyProperty StrokeProperty = DependencyProperty.Register(nameof(Stroke), typeof(Brush), typeof(Surface), Render(null!));
    public static readonly DependencyProperty StrokeThicknessProperty = DependencyProperty.Register(nameof(StrokeThickness), typeof(Thickness), typeof(Surface), Render(new Thickness(0)));
    public static readonly DependencyProperty OverlayProperty = DependencyProperty.Register(nameof(Overlay), typeof(Brush), typeof(Surface), Render(null!));
    public static readonly DependencyProperty OverlayOpacityProperty = DependencyProperty.Register(nameof(OverlayOpacity), typeof(double), typeof(Surface), Render(0.0));
    public static readonly DependencyProperty FocusRingProperty = DependencyProperty.Register(nameof(FocusRing), typeof(Brush), typeof(Surface), Render(null!));
    public static readonly DependencyProperty FocusOpacityProperty = DependencyProperty.Register(nameof(FocusOpacity), typeof(double), typeof(Surface), Render(0.0));
    public static readonly DependencyProperty CornerRadiusProperty = DependencyProperty.Register(nameof(CornerRadius), typeof(CornerRadius), typeof(Surface), Render(new CornerRadius(20)));
    public static readonly DependencyProperty PressedRadiusProperty = DependencyProperty.Register(nameof(PressedRadius), typeof(double), typeof(Surface), Render(8.0));
    public static readonly DependencyProperty SqueezeProperty = DependencyProperty.Register(nameof(Squeeze), typeof(double), typeof(Surface), Render(0.0));
    public static readonly DependencyProperty RoundProperty = DependencyProperty.Register(nameof(Round), typeof(double), typeof(Surface), Render(0.0));

    public Brush? Fill { get => (Brush?)GetValue(FillProperty); set => SetValue(FillProperty, value); }
    public Brush? Stroke { get => (Brush?)GetValue(StrokeProperty); set => SetValue(StrokeProperty, value); }
    public Thickness StrokeThickness { get => (Thickness)GetValue(StrokeThicknessProperty); set => SetValue(StrokeThicknessProperty, value); }
    public Brush? Overlay { get => (Brush?)GetValue(OverlayProperty); set => SetValue(OverlayProperty, value); }
    public double OverlayOpacity { get => (double)GetValue(OverlayOpacityProperty); set => SetValue(OverlayOpacityProperty, value); }
    public Brush? FocusRing { get => (Brush?)GetValue(FocusRingProperty); set => SetValue(FocusRingProperty, value); }
    public double FocusOpacity { get => (double)GetValue(FocusOpacityProperty); set => SetValue(FocusOpacityProperty, value); }
    public CornerRadius CornerRadius { get => (CornerRadius)GetValue(CornerRadiusProperty); set => SetValue(CornerRadiusProperty, value); }
    public double PressedRadius { get => (double)GetValue(PressedRadiusProperty); set => SetValue(PressedRadiusProperty, value); }
    public double Squeeze { get => (double)GetValue(SqueezeProperty); set => SetValue(SqueezeProperty, value); }
    public double Round { get => (double)GetValue(RoundProperty); set => SetValue(RoundProperty, value); }

    protected override void OnRender(DrawingContext dc)
    {
        var box = new Rect(0, 0, ActualWidth, ActualHeight);
        if (box.Width <= 0 || box.Height <= 0) return;
        double full = Math.Min(box.Width, box.Height) / 2;
        double Corner(double radius)
        {
            double r = radius + (PressedRadius - radius) * Squeeze;
            r += (full - r) * Round;
            return Math.Clamp(r, 0, full);
        }
        CornerRadius c = CornerRadius;
        var corners = new CornerRadius(Corner(c.TopLeft), Corner(c.TopRight), Corner(c.BottomRight), Corner(c.BottomLeft));

        if (FocusRing != null && FocusOpacity > 0)
        {
            dc.PushOpacity(FocusOpacity);
            var ring = Rect.Inflate(box, 3.5, 3.5);
            dc.DrawGeometry(null, new Pen(FocusRing, 3), Shape(ring, Grow(corners, 3.5)));
            dc.Pop();
        }
        Geometry shape = Shape(box, corners);
        if (Fill != null) dc.DrawGeometry(Fill, null, shape);
        // Pressing deepens the state layer along with the squeeze.
        double overlay = OverlayOpacity + 0.06 * Math.Clamp(Squeeze, 0, 1);
        if (Overlay != null && overlay > 0)
        {
            dc.PushOpacity(overlay);
            dc.DrawGeometry(Overlay, null, shape);
            dc.Pop();
        }
        double stroke = StrokeThickness.Left;
        if (Stroke != null && stroke > 0)
        {
            var inner = Rect.Inflate(box, -stroke / 2, -stroke / 2);
            dc.DrawGeometry(null, new Pen(Stroke, stroke), Shape(inner, Grow(corners, -stroke / 2)));
        }
    }

    private static CornerRadius Grow(CornerRadius c, double by) =>
        new(Math.Max(0, c.TopLeft + by), Math.Max(0, c.TopRight + by), Math.Max(0, c.BottomRight + by), Math.Max(0, c.BottomLeft + by));

    /// <summary>A rectangle with its own radius at each corner.</summary>
    public static Geometry Shape(Rect r, CornerRadius c)
    {
        var g = new StreamGeometry();
        using (StreamGeometryContext s = g.Open())
        {
            s.BeginFigure(new Point(r.Left + c.TopLeft, r.Top), true, true);
            s.LineTo(new Point(r.Right - c.TopRight, r.Top), true, true);
            if (c.TopRight > 0) s.ArcTo(new Point(r.Right, r.Top + c.TopRight), new Size(c.TopRight, c.TopRight), 0, false, SweepDirection.Clockwise, true, true);
            s.LineTo(new Point(r.Right, r.Bottom - c.BottomRight), true, true);
            if (c.BottomRight > 0) s.ArcTo(new Point(r.Right - c.BottomRight, r.Bottom), new Size(c.BottomRight, c.BottomRight), 0, false, SweepDirection.Clockwise, true, true);
            s.LineTo(new Point(r.Left + c.BottomLeft, r.Bottom), true, true);
            if (c.BottomLeft > 0) s.ArcTo(new Point(r.Left, r.Bottom - c.BottomLeft), new Size(c.BottomLeft, c.BottomLeft), 0, false, SweepDirection.Clockwise, true, true);
            s.LineTo(new Point(r.Left, r.Top + c.TopLeft), true, true);
            if (c.TopLeft > 0) s.ArcTo(new Point(r.Left + c.TopLeft, r.Top), new Size(c.TopLeft, c.TopLeft), 0, false, SweepDirection.Clockwise, true, true);
        }
        g.Freeze();
        return g;
    }
}
