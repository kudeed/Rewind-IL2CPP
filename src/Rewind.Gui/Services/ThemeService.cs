using System.Runtime.InteropServices;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Imaging;
using MaterialColorUtilities.Palettes;
using MaterialDesignColors;
using MaterialDesignThemes.Wpf;

namespace Rewind.Gui.Services;

/// <summary>
/// A Material 3 color scheme: every color role of the current spec (surface containers included), made from one seed
/// color with Google's HCT "tonal spot" palettes, as Android makes a Pixel's colors from its wallpaper.
/// </summary>
public sealed class M3Scheme
{
    public required Color Primary, OnPrimary, PrimaryContainer, OnPrimaryContainer;
    public required Color Secondary, OnSecondary, SecondaryContainer, OnSecondaryContainer;
    public required Color Tertiary, OnTertiary, TertiaryContainer, OnTertiaryContainer;
    public required Color Error, OnError, ErrorContainer, OnErrorContainer;
    public required Color Surface, OnSurface, OnSurfaceVariant, Outline, OutlineVariant;
    public required Color SurfaceDim, SurfaceBright;
    public required Color SurfaceContainerLowest, SurfaceContainerLow, SurfaceContainer, SurfaceContainerHigh, SurfaceContainerHighest;
    public required Color InverseSurface, InverseOnSurface, InversePrimary;
    public required bool Dark;

    public static M3Scheme From(Color seed, bool dark)
    {
        CorePalette p = CorePalette.Of(Argb(seed), MaterialColorUtilities.Palettes.Style.TonalSpot);
        Color P(uint t) => FromArgb(p.Primary[t]);
        Color S(uint t) => FromArgb(p.Secondary[t]);
        Color T(uint t) => FromArgb(p.Tertiary[t]);
        Color E(uint t) => FromArgb(p.Error[t]);
        Color N(uint t) => FromArgb(p.Neutral[t]);
        Color NV(uint t) => FromArgb(p.NeutralVariant[t]);

        return dark
            ? new M3Scheme
            {
                Dark = true,
                Primary = P(80), OnPrimary = P(20), PrimaryContainer = P(30), OnPrimaryContainer = P(90),
                Secondary = S(80), OnSecondary = S(20), SecondaryContainer = S(30), OnSecondaryContainer = S(90),
                Tertiary = T(80), OnTertiary = T(20), TertiaryContainer = T(30), OnTertiaryContainer = T(90),
                Error = E(80), OnError = E(20), ErrorContainer = E(30), OnErrorContainer = E(90),
                Surface = N(6), OnSurface = N(90), OnSurfaceVariant = NV(80), Outline = NV(60), OutlineVariant = NV(30),
                SurfaceDim = N(6), SurfaceBright = N(24),
                SurfaceContainerLowest = N(4), SurfaceContainerLow = N(10), SurfaceContainer = N(12),
                SurfaceContainerHigh = N(17), SurfaceContainerHighest = N(22),
                InverseSurface = N(90), InverseOnSurface = N(20), InversePrimary = P(40),
            }
            : new M3Scheme
            {
                Dark = false,
                Primary = P(40), OnPrimary = P(100), PrimaryContainer = P(90), OnPrimaryContainer = P(30),
                Secondary = S(40), OnSecondary = S(100), SecondaryContainer = S(90), OnSecondaryContainer = S(30),
                Tertiary = T(40), OnTertiary = T(100), TertiaryContainer = T(90), OnTertiaryContainer = T(30),
                Error = E(40), OnError = E(100), ErrorContainer = E(90), OnErrorContainer = E(30),
                Surface = N(98), OnSurface = N(10), OnSurfaceVariant = NV(30), Outline = NV(50), OutlineVariant = NV(80),
                SurfaceDim = N(87), SurfaceBright = N(98),
                SurfaceContainerLowest = N(100), SurfaceContainerLow = N(96), SurfaceContainer = N(94),
                SurfaceContainerHigh = N(92), SurfaceContainerHighest = N(90),
                InverseSurface = N(20), InverseOnSurface = N(95), InversePrimary = P(80),
            };
    }

    /// <summary>The three colors a Pixel shows for a color choice: primary over secondary and tertiary.</summary>
    public static (Color Top, Color Left, Color Right) Swatch(Color seed)
    {
        CorePalette p = CorePalette.Of(Argb(seed), MaterialColorUtilities.Palettes.Style.TonalSpot);
        return (FromArgb(p.Primary[70]), FromArgb(p.Secondary[85]), FromArgb(p.Tertiary[75]));
    }

    private static uint Argb(Color c) => 0xFF000000u | ((uint)c.R << 16) | ((uint)c.G << 8) | c.B;

    private static Color FromArgb(uint argb) => Color.FromRgb((byte)(argb >> 16), (byte)(argb >> 8), (byte)argb);
}

/// <summary>A color choice: the seed its scheme is made from.</summary>
public sealed class Accent
{
    public const string WindowsName = "Windows";

    private Accent(string name, string label, Color seed)
    {
        Name = name;
        Label = label;
        Seed = seed;
        (Color top, Color left, Color right) = M3Scheme.Swatch(seed);
        Top = Frozen(top);
        Left = Frozen(left);
        Right = Frozen(right);
    }

    public string Name { get; }
    public string Label { get; }
    public Color Seed { get; }
    public SolidColorBrush Top { get; }
    public SolidColorBrush Left { get; }
    public SolidColorBrush Right { get; }

    private static IReadOnlyList<Accent>? _all;

    /// <summary>Windows' accent color first (when there is one), then fixed seeds.</summary>
    public static IReadOnlyList<Accent> All => _all ??= Make();

    private static IReadOnlyList<Accent> Make()
    {
        var list = new List<Accent>();
        if (Theme.GetSystemAccentColor() is { } windows) list.Add(new Accent(WindowsName, "Windows accent color", windows));
        foreach ((string name, string seed) in new[]
                 {
                     ("Purple", "#6750A4"), ("Blue", "#0B57D0"), ("Teal", "#00696D"), ("Green", "#386A20"),
                     ("Yellow", "#7A5900"), ("Orange", "#9C4400"), ("Red", "#B3261E"), ("Pink", "#984061"),
                 })
            list.Add(new Accent(name, name, (Color)ColorConverter.ConvertFromString(seed)));
        return list;
    }

    public static Accent Named(string? name) =>
        All.FirstOrDefault(a => a.Name == name) ?? All.First(a => a.Name == "Purple");

    internal static SolidColorBrush Frozen(Color color)
    {
        var brush = new SolidColorBrush(color);
        brush.Freeze();
        return brush;
    }
}

public static class ThemeService
{
    public static bool IsDark { get; private set; }

    public static M3Scheme? Scheme { get; private set; }

    public static event Action? Changed;

    public static void Apply(GuiSettings settings)
    {
        bool dark = settings.Theme switch
        {
            AppTheme.Light => false,
            AppTheme.Dark => true,
            _ => Theme.GetSystemTheme() == BaseTheme.Dark,
        };
        M3Scheme s = M3Scheme.From(Accent.Named(settings.Accent).Seed, dark);
        Scheme = s;
        IsDark = dark;

        ResourceDictionary r = Application.Current.Resources;
        void Set(string key, Color color) => r["M3." + key] = Accent.Frozen(color);
        Set("Primary", s.Primary); Set("OnPrimary", s.OnPrimary);
        Set("PrimaryContainer", s.PrimaryContainer); Set("OnPrimaryContainer", s.OnPrimaryContainer);
        Set("Secondary", s.Secondary); Set("OnSecondary", s.OnSecondary);
        Set("SecondaryContainer", s.SecondaryContainer); Set("OnSecondaryContainer", s.OnSecondaryContainer);
        Set("Tertiary", s.Tertiary); Set("OnTertiary", s.OnTertiary);
        Set("TertiaryContainer", s.TertiaryContainer); Set("OnTertiaryContainer", s.OnTertiaryContainer);
        Set("Error", s.Error); Set("OnError", s.OnError);
        Set("ErrorContainer", s.ErrorContainer); Set("OnErrorContainer", s.OnErrorContainer);
        Set("Surface", s.Surface); Set("OnSurface", s.OnSurface); Set("OnSurfaceVariant", s.OnSurfaceVariant);
        Set("Outline", s.Outline); Set("OutlineVariant", s.OutlineVariant);
        Set("SurfaceContainerLowest", s.SurfaceContainerLowest); Set("SurfaceContainerLow", s.SurfaceContainerLow);
        Set("SurfaceContainer", s.SurfaceContainer); Set("SurfaceContainerHigh", s.SurfaceContainerHigh);
        Set("SurfaceContainerHighest", s.SurfaceContainerHighest);
        Set("InverseSurface", s.InverseSurface); Set("InverseOnSurface", s.InverseOnSurface); Set("InversePrimary", s.InversePrimary);
        // Android 16's settings: list groups on a tinted background, lighter in a light theme, raised in a dark one.
        Set("PageBrush", dark ? s.Surface : s.SurfaceContainer);
        Set("RowBrush", dark ? s.SurfaceContainer : s.SurfaceBright);
        Set("CodeBrush", dark ? s.SurfaceContainerLowest : s.SurfaceContainerHigh);

        var logo = new BitmapImage();
        logo.BeginInit();
        logo.UriSource = new Uri(dark ? "pack://application:,,,/Assets/rewind-logo-dark.png" : "pack://application:,,,/Assets/rewind-logo.png");
        logo.DecodePixelWidth = 256;
        logo.EndInit();
        logo.Freeze();
        r["Rewind.Logo"] = logo;

        // The toolkit's own controls (text fields, menus, scroll bars, the snackbar) take the same scheme.
        var palette = new PaletteHelper();
        Theme theme = palette.GetTheme();
        theme.SetBaseTheme(dark ? BaseTheme.Dark : BaseTheme.Light);
        theme.PrimaryLight = new ColorPair(s.PrimaryContainer, s.OnPrimaryContainer);
        theme.PrimaryMid = new ColorPair(s.Primary, s.OnPrimary);
        theme.PrimaryDark = new ColorPair(s.Primary, s.OnPrimary);
        theme.SecondaryLight = new ColorPair(s.SecondaryContainer, s.OnSecondaryContainer);
        theme.SecondaryMid = new ColorPair(s.Primary, s.OnPrimary);
        theme.SecondaryDark = new ColorPair(s.Primary, s.OnPrimary);
        Color page = dark ? s.Surface : s.SurfaceContainer;
        Color row = dark ? s.SurfaceContainer : s.SurfaceBright;
        theme.Background = page;
        theme.Foreground = s.OnSurface;
        theme.ForegroundLight = s.OnSurfaceVariant;
        theme.ValidationError = s.Error;
        theme.Cards.Background = row;
        theme.TextBoxes.OutlineBorder = s.Primary;
        theme.TextBoxes.OutlineInactiveBorder = s.Outline;
        theme.TextBoxes.HoverBorder = s.OnSurface;
        theme.TextBoxes.Border = s.Outline;
        theme.ComboBoxes.OutlineBorder = s.Primary;
        theme.ComboBoxes.OutlineInactiveBorder = s.Outline;
        theme.ComboBoxes.HoverBorder = s.OnSurface;
        theme.ComboBoxes.Border = s.Outline;
        theme.ComboBoxes.Popups.LightBackground = s.SurfaceContainer;
        theme.ComboBoxes.Popups.DarkBackground = s.SurfaceContainer;
        theme.ComboBoxes.Popups.LightForeground = s.OnSurface;
        theme.ComboBoxes.Popups.DarkForeground = s.OnSurface;
        theme.ComboBoxes.DropDowns.Background = s.SurfaceContainer;
        theme.SnackBars.Background = s.InverseSurface;
        theme.ToolTips.Background = s.InverseSurface;
        theme.Separators.Background = s.OutlineVariant;
        palette.SetTheme(theme);

        Changed?.Invoke();
    }

    /// <summary>
    /// The title bar in the page's color (Windows 11), or at least dark with the dark theme (Windows 10).
    /// </summary>
    public static void StyleTitleBar(IntPtr window)
    {
        if (window == IntPtr.Zero || Scheme is not { } s) return;
        int dark = IsDark ? 1 : 0;
        _ = DwmSetWindowAttribute(window, 20, ref dark, sizeof(int));
        Color page = s.Dark ? s.Surface : s.SurfaceContainer;
        int caption = page.R | (page.G << 8) | (page.B << 16);
        int text = s.OnSurface.R | (s.OnSurface.G << 8) | (s.OnSurface.B << 16);
        _ = DwmSetWindowAttribute(window, 35, ref caption, sizeof(int));
        _ = DwmSetWindowAttribute(window, 36, ref text, sizeof(int));
    }

    [DllImport("dwmapi.dll")]
    private static extern int DwmSetWindowAttribute(IntPtr window, int attribute, ref int value, int size);
}
