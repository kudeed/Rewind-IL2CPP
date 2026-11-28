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
        text = Regex.Replace(text, @"<([^<>]+)>d__(\d+)", m => IdentName(m.Groups[1].Value) + "_d__" + m.Groups[2].Value);
        text = Regex.Replace(text, @"<([^<>]+)>(\d+)__(\d+)", m => IdentName(m.Groups[1].Value) + "_" + m.Groups[2].Value + "__" + m.Groups[3].Value);
        text = Regex.Replace(text, @"<([^<>]+)>g__(\w+)\|(\d+)(?:_(\d+))?", m => IdentName(m.Groups[1].Value) + "_g__" + m.Groups[2].Value + "_" + m.Groups[3].Value + (m.Groups[4].Success ? "_" + m.Groups[4].Value : ""));
        text = Regex.Replace(text, @"<([^<>]+)>b__(\d+)(?:_(\d+))?", m => IdentName(m.Groups[1].Value) + "_b__" + m.Groups[2].Value + (m.Groups[3].Success ? "_" + m.Groups[3].Value : ""));
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
        // The same field named without a receiver: its declaration ("double? <P>k__BackingField;") and the
        // reads and writes inside the property itself. A bare "<...>" is not a C# identifier.
        text = Regex.Replace(text, @"<(\w+)>k__BackingField", m => m.Groups[1].Value + "BackingField");
        // Collection and object initializers written with the "in" argument modifier ("{ in item }") are not C#.
        text = Regex.Replace(text, @"\{(\s*)in[ \t]+", m => "{" + m.Groups[1].Value);
        text = Regex.Replace(text, @"(?m)^([ \t]*)in[ \t]+", m => m.Groups[1].Value);
    }

    private static string IdentName(string s) => Regex.Replace(s, "[^A-Za-z0-9_]", "_");
}
