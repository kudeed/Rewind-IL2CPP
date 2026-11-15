using Rewind.Analysis;
using Rewind.Analysis.Runtime;
using Rewind.Model;

namespace Rewind.Lab;

/// <summary>Checks the identification of private copies of managed methods against symbol names.</summary>
internal static class InlineLab
{
    private static string Sanitize(string name)
    {
        var sb = new System.Text.StringBuilder(name.Length);
        foreach (char c in name)
        {
            if (char.IsAsciiLetterOrDigit(c) || c == '_') sb.Append(c);
            else if (c is '.' or '`' or '/') sb.Append('_');
            else sb.Append('U').Append(((int)c).ToString(c < 0x100 ? "X2" : "X4"));
        }
        return sb.ToString();
    }

    /// <summary>inline-check &lt;input&gt; &lt;symbols.tsv&gt;</summary>
    public static int Check(Il2CppModel model, string symbolsPath)
    {
        Dictionary<ulong, List<string>> symbols = CallStats.LoadSymbols(model.Image, symbolsPath);
        ProgramAnalysis program = LiftLab.MakeProgram(model, symbolsPath);
        int agree = 0, disagree = 0, unnamed = 0;
        foreach (var (address, copy) in program.InlineCopies)
        {
            if (!symbols.TryGetValue(address, out List<string>? names)) { unnamed++; continue; }
            string expected = Sanitize(copy.Method.DeclaringType.Name) + "_" + Sanitize(copy.Method.Name) + "_m";
            if (names.Any(n => n.Contains(expected, StringComparison.Ordinal))) agree++;
            else
            {
                disagree++;
                if (disagree <= 12) Console.WriteLine($"  DISAGREE 0x{address:X}: identified {copy.Method.FullName} ({copy.Sites} sites); symbol {names[0][..Math.Min(100, names[0].Length)]}");
            }
        }
        int inlineSymbols = symbols.Count(kv => kv.Value.Any(n => n.Contains("_inline@@", StringComparison.Ordinal)) && !model.MethodsByAddress.ContainsKey(kv.Key) && !model.InstsByAddress.ContainsKey(kv.Key));
        Console.WriteLine($"private copies identified: {program.InlineCopies.Count}; symbol agrees {agree}, disagrees {disagree}, no symbol {unnamed}");
        Console.WriteLine($"unlisted functions the symbols call '_inline': {inlineSymbols}");
        return disagree == 0 ? 0 : 1;
    }
}
