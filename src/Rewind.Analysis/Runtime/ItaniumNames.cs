using System.Text;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// Reads the qualified name out of an Itanium-mangled symbol (what clang writes for Android and iOS), in the
/// order MSVC decorated names have it: innermost first, joined by '@' ("Raise@Exception@vm@il2cpp"), template
/// arguments left out. That way one set of name rules serves both kinds of symbol file.
/// </summary>
public static class ItaniumNames
{
    public static string? Core(string mangled)
    {
        if (!mangled.StartsWith("_Z", StringComparison.Ordinal)) return null;
        int p = 2;
        if (p < mangled.Length && mangled[p] == 'L') p++; // internal linkage
        var parts = new List<string>();
        if (p >= mangled.Length) return null;
        if (mangled[p] == 'N')
        {
            p++;
            while (p < mangled.Length && mangled[p] is 'r' or 'V' or 'K') p++;
            if (p < mangled.Length && mangled[p] is 'R' or 'O') p++;
            while (p < mangled.Length && mangled[p] != 'E')
            {
                char c = mangled[p];
                if (char.IsDigit(c))
                {
                    if (ReadSource(mangled, ref p) is not { } name) return null;
                    parts.Add(name);
                }
                else if (c == 'I')
                {
                    if (!SkipTemplateArgs(mangled, ref p)) return null;
                }
                else if (c == 'S')
                {
                    if (!SkipSubstitution(mangled, ref p, out bool std)) return null;
                    parts.Add(std ? "std" : "?");
                }
                else if (c == 'C' && p + 1 < mangled.Length && char.IsDigit(mangled[p + 1]))
                {
                    parts.Add(parts.Count > 0 ? parts[^1] : "ctor");
                    p += 2;
                }
                else if (c == 'D' && p + 1 < mangled.Length && mangled[p + 1] is '0' or '1' or '2')
                {
                    parts.Add("~" + (parts.Count > 0 ? parts[^1] : ""));
                    p += 2;
                }
                else if (c == 'L') p++;
                else return null; // operator names and other special forms
            }
        }
        else if (char.IsDigit(mangled[p]))
        {
            if (ReadSource(mangled, ref p) is not { } name) return null;
            parts.Add(name);
        }
        else return null;
        if (parts.Count == 0) return null;
        parts.Reverse();
        return string.Join("@", parts);
    }

    private static string? ReadSource(string s, ref int p)
    {
        int length = 0;
        while (p < s.Length && char.IsDigit(s[p])) length = length * 10 + (s[p++] - '0');
        if (length == 0 || p + length > s.Length) return null;
        string name = s.Substring(p, length);
        p += length;
        return name;
    }

    private static bool SkipSubstitution(string s, ref int p, out bool std)
    {
        std = false;
        if (p + 1 >= s.Length) return false;
        char next = s[p + 1];
        if (char.IsLower(next))
        {
            std = true;
            p += 2;
            return true;
        }
        int q = p + 1;
        while (q < s.Length && s[q] != '_') q++;
        if (q >= s.Length) return false;
        p = q + 1;
        return true;
    }

    /// <summary>Skips "I ... E" (template arguments), with what nests inside.</summary>
    private static bool SkipTemplateArgs(string s, ref int p)
    {
        int depth = 0;
        while (p < s.Length)
        {
            char c = s[p];
            if (char.IsDigit(c))
            {
                if (ReadSource(s, ref p) == null) return false;
                continue;
            }
            switch (c)
            {
                case 'I' or 'N' or 'X' or 'F' or 'Z':
                    depth++;
                    p++;
                    break;
                case 'L':
                {
                    // literal: L <type> <value> E, or L _Z <encoding> E
                    p++;
                    if (p < s.Length && char.IsDigit(s[p]))
                    {
                        if (ReadSource(s, ref p) == null) return false;
                    }
                    else if (p < s.Length) p += s[p] == 'D' ? 2 : 1;
                    while (p < s.Length && s[p] != 'E') p++;
                    p++;
                    break;
                }
                case 'S':
                    if (!SkipSubstitution(s, ref p, out _)) return false;
                    break;
                case 'T':
                {
                    while (p < s.Length && s[p] != '_') p++;
                    p++;
                    break;
                }
                case 'E':
                    depth--;
                    p++;
                    if (depth == 0) return true;
                    break;
                default:
                    p++;
                    break;
            }
        }
        return false;
    }
}
