using System.Text.RegularExpressions;

namespace Rewind.Output;

public static partial class Decompiler
{
    /// <summary>
    /// Turns the compiler-generated names the C# decompiler leaves in the source ("&lt;Method&gt;d__0",
    /// "&lt;&gt;c__DisplayClass", "CS$&lt;&gt;8__locals1", "&lt;Property&gt;k__BackingField", ...) into valid identifiers,
    /// so the written source can be compiled again. A recovered body names these types and members directly; only
    /// the characters are illegal, not the shapes.
    /// </summary>
    private static void SanitizeIdentifiers(ref string text)
    {
        // Metadata identifiers are code. Text, comments, and recovery evidence are not.
        var protectedText = SourceTextProtection.Mask(text, static expression =>
        {
            SanitizeIdentifiers(ref expression);
            return expression;
        });
        text = protectedText.Text;
        text = protectedText.RewriteIdentifiers(text, @"(?<![\w@])<([^<>]+)>d__(\d+)", m => IdentName(m.Groups[1].Value) + "_d__" + m.Groups[2].Value);
        text = protectedText.RewriteIdentifiers(text, @"(?<![\w@])<([^<>]+)>(\d+)__(\d+)", m => IdentName(m.Groups[1].Value) + "_" + m.Groups[2].Value + "__" + m.Groups[3].Value);
        text = protectedText.RewriteIdentifiers(text, @"(?<![\w@])<([^<>]+)>g__(\w+)\|(\d+)(?:_(\d+))?", m => IdentName(m.Groups[1].Value) + "_g__" + m.Groups[2].Value + "_" + m.Groups[3].Value + (m.Groups[4].Success ? "_" + m.Groups[4].Value : ""));
        text = protectedText.RewriteIdentifiers(text, @"(?<![\w@])<([^<>]+)>b__(\d+)(?:_(\d+))?", m => IdentName(m.Groups[1].Value) + "_b__" + m.Groups[2].Value + (m.Groups[3].Success ? "_" + m.Groups[3].Value : ""));
        text = Regex.Replace(text, @"<>([A-Za-z0-9_]+)", m => "_" + m.Groups[1].Value);
        text = text.Replace("CS$<>", "CS__");
        text = Regex.Replace(text, @"(?<![A-Za-z0-9_])\$([A-Za-z_])", m => "_" + m.Groups[1].Value);
        text = Regex.Replace(text, @"([A-Za-z0-9_])\$([A-Za-z0-9_])", m => m.Groups[1].Value + "_" + m.Groups[2].Value);
        // "<PrivateImplementationDetails>." is a type the C# compiler emitted; named validly here, the helper the
        // decompiler writes alongside the source defines it.
        text = Regex.Replace(text, @"(?<![A-Za-z0-9_])<([A-Za-z_][A-Za-z0-9_]*)>(?=\.)", m => "_" + m.Groups[1].Value + "_");
        // A write through an auto-property's backing field on a struct ("x.<P>k__BackingField.M = v") cannot
        // become "x.P.M = v" (the getter's value is not a variable): read the property, write the member, set it back.
        text = Regex.Replace(text, @"(\w+)\.<(\w+)>k__BackingField\.(\w+)\s*=\s*([^;]+);",
            m => "{ var __b = " + m.Groups[1].Value + "." + m.Groups[2].Value + "; __b." + m.Groups[3].Value + " = " + m.Groups[4].Value + "; " + m.Groups[1].Value + "." + m.Groups[2].Value + " = __b; }");
        text = Regex.Replace(text, @"\.<(\w+)>k__BackingField", m => "." + m.Groups[1].Value);
        // Collection and object initializers written with the "in" argument modifier ("{ in item }") are not C#.
        text = Regex.Replace(text, @"\{(\s*)in[ \t]+", m => "{" + m.Groups[1].Value);
        text = Regex.Replace(text, @"(?m)^([ \t]*)in[ \t]+", m => m.Groups[1].Value);

        // IL2CPP may retain an explicit interface accessor method without its Property row.
        // C# requires an explicit interface PROPERTY implementation, not get_X()/set_X() methods.
        RewriteExplicitInterfaceAccessors(ref text);

        // A partial auto-property may retain a bare backing field declaration and uses.
        // Keep those fields rather than inventing an accessor or dropping the stored value.
        text = Regex.Replace(text, @"(?<![\w@])<([A-Za-z_]\w*)>(k__BackingField|P|d)\b",
            m => "_rewind_cg_" + m.Groups[1].Value + "_" + m.Groups[2].Value);
        text = Regex.Replace(text, @"(?<=_PrivateImplementationDetails_\.)([0-9A-F]{64})\b",
            m => "_" + m.Groups[1].Value);
        text = protectedText.Restore(text);
    }

    private static void RewriteExplicitInterfaceAccessors(ref string text)
    {
        var getters = Regex.Matches(text,
            @"(?m)^(?<indent>[ \t]*)(?<type>[A-Za-z_][\w.<>,\[\]?]*)\s+(?<iface>[A-Za-z_][\w.]*)\.get_(?<property>[A-Za-z_]\w*)\s*\(\s*\)\s*$");
        for (int i = getters.Count - 1; i >= 0; i--)
        {
            Match m = getters[i];
            int open = NextNonWhitespace(text, m.Index + m.Length);
            if (open < 0 || text[open] != '{') continue;
            int close = MatchingBraceForAccessor(text, open);
            if (close < 0) continue;
            string indent = m.Groups["indent"].Value;
            string body = IndentBody(text[(open + 1)..close], "\t");
            string replacement = indent + m.Groups["type"].Value + " " + m.Groups["iface"].Value + "." + m.Groups["property"].Value
                + "\n" + indent + "{\n" + indent + "\tget\n" + indent + "\t{\n" + body
                + indent + "\t}\n" + indent + "}";
            text = text[..m.Index] + replacement + text[(close + 1)..];
        }

        var setters = Regex.Matches(text,
            @"(?m)^(?<indent>[ \t]*)void\s+(?<iface>[A-Za-z_][\w.]*)\.set_(?<property>[A-Za-z_]\w*)\s*\(\s*(?<type>[A-Za-z_][\w.<>,\[\]?]*)\s+(?<parameter>[A-Za-z_]\w*)\s*\)\s*$");
        for (int i = setters.Count - 1; i >= 0; i--)
        {
            Match m = setters[i];
            int open = NextNonWhitespace(text, m.Index + m.Length);
            if (open < 0 || text[open] != '{') continue;
            int close = MatchingBraceForAccessor(text, open);
            if (close < 0) continue;
            string indent = m.Groups["indent"].Value;
            string body = IndentBody(text[(open + 1)..close], "\t");
            string replacement = indent + m.Groups["type"].Value + " " + m.Groups["iface"].Value + "." + m.Groups["property"].Value
                + "\n" + indent + "{\n" + indent + "\tset\n" + indent + "\t{\n" + body
                + indent + "\t}\n" + indent + "}";
            text = text[..m.Index] + replacement + text[(close + 1)..];
        }
    }

    private static int NextNonWhitespace(string text, int index)
    {
        while (index < text.Length && char.IsWhiteSpace(text[index])) index++;
        return index < text.Length ? index : -1;
    }

    private static int MatchingBraceForAccessor(string text, int open)
    {
        int depth = 0;
        for (int i = open; i < text.Length; i++)
        {
            char c = text[i];
            if (c == '/' && i + 1 < text.Length && text[i + 1] == '/')
            {
                i += 2;
                while (i < text.Length && text[i] != '\n') i++;
                continue;
            }
            if (c == '/' && i + 1 < text.Length && text[i + 1] == '*')
            {
                i += 2;
                while (i + 1 < text.Length && !(text[i] == '*' && text[i + 1] == '/')) i++;
                i++;
                continue;
            }
            if (c == '@' && i + 1 < text.Length && text[i + 1] == '"')
            {
                i += 2;
                while (i < text.Length)
                {
                    if (text[i] == '"')
                    {
                        if (i + 1 < text.Length && text[i + 1] == '"') { i += 2; continue; }
                        break;
                    }
                    i++;
                }
                continue;
            }
            if (c == '"' || c == '\'')
            {
                char quote = c;
                for (i++; i < text.Length; i++)
                {
                    if (text[i] == '\\') { i++; continue; }
                    if (text[i] == quote) break;
                }
                continue;
            }
            if (c == '{') depth++;
            else if (c == '}' && --depth == 0) return i;
        }
        return -1;
    }

    private static string IndentBody(string body, string extra)
    {
        string[] lines = body.Replace("\r\n", "\n").Split('\n');
        int first = 0, last = lines.Length;
        while (first < last && string.IsNullOrWhiteSpace(lines[first])) first++;
        while (last > first && string.IsNullOrWhiteSpace(lines[last - 1])) last--;
        return string.Concat(lines.Skip(first).Take(last - first).Select(line => extra + line + "\n"));
    }

    private static string IdentName(string s) => Regex.Replace(s, "[^A-Za-z0-9_]", "_");
}
