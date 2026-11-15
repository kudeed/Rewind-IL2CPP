using System.Text.RegularExpressions;

namespace Rewind.Metadata;

/// <summary>A Unity editor/player version such as 6000.3.12f1 or 2022.3.33f1.</summary>
public readonly partial record struct UnityVersion(int Major, int Minor, int Build, char Type, int Revision)
    : IComparable<UnityVersion>
{
    [GeneratedRegex(@"(\d{1,4})\.(\d{1,2})\.(\d{1,3})(?:([abfpx])(\d{1,3}))?")]
    private static partial Regex Pattern();

    public static bool TryParse(string? text, out UnityVersion version)
    {
        version = default;
        if (string.IsNullOrEmpty(text)) return false;
        Match m = Pattern().Match(text);
        if (!m.Success) return false;
        int major = int.Parse(m.Groups[1].Value);
        if (major is not ((>= 3 and <= 5) or (>= 2017 and <= 2023) or >= 6000)) return false;
        char type = m.Groups[4].Success ? m.Groups[4].Value[0] : 'f';
        int revision = m.Groups[5].Success ? int.Parse(m.Groups[5].Value) : 1;
        version = new UnityVersion(major, int.Parse(m.Groups[2].Value), int.Parse(m.Groups[3].Value), type, revision);
        return true;
    }

    // alpha < beta < final (f) < patch (p); 'x' (experimental) sorts with final.
    private int TypeRank => Type switch { 'a' => 0, 'b' => 1, 'p' => 3, _ => 2 };

    public int CompareTo(UnityVersion other)
    {
        int c = Major.CompareTo(other.Major);
        if (c != 0) return c;
        c = Minor.CompareTo(other.Minor);
        if (c != 0) return c;
        c = Build.CompareTo(other.Build);
        if (c != 0) return c;
        c = TypeRank.CompareTo(other.TypeRank);
        return c != 0 ? c : Revision.CompareTo(other.Revision);
    }

    public bool AtLeast(int major, int minor = 0, int build = 0, char type = 'a', int revision = 0) =>
        CompareTo(new UnityVersion(major, minor, build, type, revision)) >= 0;

    public override string ToString() => $"{Major}.{Minor}.{Build}{Type}{Revision}";
}

/// <summary>
/// IL2CPP metadata format versions. Unity changed layouts several times without bumping the number stored in
/// the file, so each distinct layout gets its own value here: major * 100 + sub-version (24.15 is 2415).
/// </summary>
public static class MetaVersion
{
    public const int V24_0 = 2400, V24_1 = 2410, V24_15 = 2415, V24_2 = 2420, V24_3 = 2430, V24_4 = 2440, V24_5 = 2450;
    public const int V27_0 = 2700, V27_1 = 2710, V27_2 = 2720;
    public const int V29_0 = 2900, V29_1 = 2910;
    public const int V31_0 = 3100, V31_1 = 3110;
    public const int V35 = 3500, V38 = 3800, V39 = 3900;

    public const int MinSupportedMajor = 24, MaxSupportedMajor = 39;

    public static string Describe(int v) => v % 100 == 0 ? (v / 100).ToString() : $"{v / 100}.{(v % 10 == 0 ? v % 100 / 10 : v % 100)}";

    /// <summary>All known layouts that store <paramref name="major"/> in the file header, newest first.</summary>
    public static int[] Candidates(int major) => major switch
    {
        24 => [V24_5, V24_4, V24_3, V24_2, V24_15, V24_1, V24_0],
        27 => [V27_2, V27_1, V27_0],
        29 => [V29_1, V29_0],
        31 => [V31_1, V31_0],
        35 => [V35],
        38 => [V38],
        39 => [V39],
        _ => major is > 24 and < 39 ? [major * 100] : [],
    };

    /// <summary>Picks the exact layout from the Unity version, when the Unity version is known.</summary>
    public static int? FromUnity(int major, UnityVersion u)
    {
        switch (major)
        {
            case 24:
                if (u.AtLeast(2020, 1, 11)) return V24_4;
                if (u.AtLeast(2020)) return V24_3;
                if (u.AtLeast(2019, 4, 21)) return V24_5;
                if (u.AtLeast(2019, 4, 15)) return V24_4;
                if (u.AtLeast(2019, 3, 7)) return V24_3;
                if (u.AtLeast(2019)) return V24_2;
                if (u.AtLeast(2018, 4, 34)) return V24_15;
                if (u.AtLeast(2018, 3)) return V24_1;
                return V24_0;
            case 27:
                if (u.AtLeast(2021, 1)) return V27_2;
                if (u.AtLeast(2020, 2, 4)) return V27_1;
                return V27_0;
            case 29:
                return u.AtLeast(2022, 1, 0, 'b', 7) ? V29_1 : V29_0;
            case 31:
                return u.AtLeast(2022, 3, 33) ? V31_1 : V31_0;
            default:
                return null;
        }
    }
}
