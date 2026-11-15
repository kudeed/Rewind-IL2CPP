using System.Diagnostics;
using System.Text;
using System.Text.RegularExpressions;
using Rewind.Analysis;
using Rewind.Analysis.Runtime;
using Rewind.Model;

namespace Rewind.Lab;

/// <summary>
/// Writes a build's functions as training data for the identification model: every function's token stream,
/// with the names it is known by. Managed methods are named by the game's own metadata (so any standard build
/// is labeled data for them); runtime functions and private copies of methods are named only when a symbol
/// file is given, which is the case for builds of ours.
/// </summary>
internal static class ExportLab
{
    private static string Sanitize(string name)
    {
        var sb = new StringBuilder(name.Length);
        foreach (char c in name)
        {
            if (char.IsAsciiLetterOrDigit(c) || c == '_') sb.Append(c);
            else if (c is '.' or '`' or '/') sb.Append('_');
            else sb.Append('U').Append(((int)c).ToString(c < 0x100 ? "X2" : "X4"));
        }
        return sb.ToString();
    }

    private static readonly Regex MethodHash = new("_m[0-9A-F]{40}", RegexOptions.Compiled);

    /// <summary>
    /// The plain identifier of a C++ function name: "?Name@@..." (MSVC) and "_Z[L]<length>Name..." (Itanium,
    /// used on Android) both become "Name". Anything else is returned as it is.
    /// </summary>
    internal static string PlainName(string symbol)
    {
        if (symbol.StartsWith("?", StringComparison.Ordinal))
        {
            int at = symbol.IndexOf("@@", StringComparison.Ordinal);
            return at > 0 ? symbol[1..at] : symbol[1..];
        }
        if (!symbol.StartsWith("_Z", StringComparison.Ordinal)) return symbol;
        int i = 2;
        if (i < symbol.Length && symbol[i] == 'L') i++;
        int digits = i;
        while (i < symbol.Length && char.IsAsciiDigit(symbol[i])) i++;
        if (i == digits || !int.TryParse(symbol.AsSpan(digits, i - digits), out int length) || i + length > symbol.Length) return symbol;
        return symbol.Substring(i, length);
    }

    /// <summary>The "Type_Method" part of a generated function name such as ?List_1_Add_m0771...5F_inline@@YAX...</summary>
    private static string? MangledPrefix(string symbol)
    {
        string core = PlainName(symbol);
        if (core.StartsWith('?'))
        {
            int at = core.IndexOf("@@", StringComparison.Ordinal);
            core = at > 0 ? core[1..at] : core[1..];
        }
        Match hash = MethodHash.Match(core);
        if (!hash.Success) return null;
        string prefix = core[..hash.Index];
        int generic = prefix.IndexOf("_Tis", StringComparison.Ordinal);
        if (generic > 0) prefix = prefix[..generic];
        return prefix;
    }

    /// <summary>
    /// A method definition's full signature. Overloads differ in it (Math.Max(int, int) and Math.Max(float, float)
    /// are different functions and must not share a label), instantiations of one generic definition do not.
    /// </summary>
    private static string FullKey(MethodDef m) =>
        m.DeclaringType.ReflectionName + "::" + m.Name + "(" + string.Join(",", m.Parameters.Select(p => p.Type.DisplayName)) + "):" + m.ReturnType.DisplayName;

    /// <summary>export-functions &lt;input&gt; &lt;out directory&gt; [symbols.tsv]</summary>
    public static int Export(Il2CppModel model, string outDirectory, string? symbolsPath, string? sourcePath = null)
    {
        var sw = Stopwatch.StartNew();
        var context = new ModelCodeContext(model);
        context.DiscoverCallTargets();
        var tokenizer = new FunctionTokenizer(model, context);
        Dictionary<ulong, List<string>>? symbols = symbolsPath != null ? CallStats.LoadSymbols(model.Image, symbolsPath) : null;

        var byMangled = new Dictionary<string, HashSet<string>>(StringComparer.Ordinal);
        foreach (MethodDef m in model.Methods)
        {
            string prefix = Sanitize(m.DeclaringType.Name) + "_" + Sanitize(m.Name);
            if (!byMangled.TryGetValue(prefix, out HashSet<string>? set)) byMangled[prefix] = set = [];
            set.Add(FullKey(m));
        }

        // Generated function names carry a hash of the method they implement ("..._m<40 hex digits>"). A
        // private copy has the same hash as the method's own function, which the tables do list - so the
        // hash says exactly which method (which overload) a copy is a copy of.
        var listedByHash = new Dictionary<string, ulong>(StringComparer.Ordinal);
        if (symbols != null)
        {
            foreach (var (address, names) in symbols)
            {
                if (!model.MethodsByAddress.ContainsKey(address) && !model.InstsByAddress.ContainsKey(address)) continue;
                foreach (string name in names)
                {
                    if (PlainName(name).EndsWith("_inline", StringComparison.Ordinal)) continue;
                    Match hash = MethodHash.Match(name);
                    if (hash.Success) listedByHash.TryAdd(hash.Value, address);
                }
            }
        }
        var exportsAt = new Dictionary<ulong, List<string>>();
        foreach (var (name, address) in model.Image.Exports)
        {
            if (!exportsAt.TryGetValue(address, out List<string>? list)) exportsAt[address] = list = [];
            list.Add(name);
        }

        Directory.CreateDirectory(outDirectory);
        const ushort AggressiveInlining = 0x100;
        int written = 0, managed = 0, inline = 0, named = 0, unnamed = 0, failed = 0, exactCopies = 0;
        long offset = 0, instructionTotal = 0;
        using (var tokenFile = new BinaryWriter(File.Create(Path.Combine(outDirectory, "tokens.u16"))))
        using (var index = new StreamWriter(Path.Combine(outDirectory, "index.tsv"), false, new UTF8Encoding(false)))
        {
            foreach (ulong start in context.FunctionStarts)
            {
                if (!model.Image.IsCodeAddress(start)) continue;
                ushort[]? tokens;
                int instructions;
                try
                {
                    tokens = tokenizer.Tokenize(start, out instructions);
                }
                catch (Exception e)
                {
                    tokens = null;
                    instructions = 0;
                    if (failed < 3 && Environment.GetEnvironmentVariable("REWIND_EXPORT_DEBUG") != null)
                        Console.WriteLine($"  exception at 0x{start:X}: {e}");
                }
                if (tokens == null || tokens.Length < 2)
                {
                    failed++;
                    if (failed <= 8 && Environment.GetEnvironmentVariable("REWIND_EXPORT_DEBUG") != null)
                        Console.WriteLine($"  not decodable: 0x{start:X} next 0x{context.NextFunctionStart(start):X} section {model.Image.SectionAt(start)?.Name} tokens {tokens?.Length.ToString() ?? "null"}: {tokenizer.LastFailure}");
                    continue;
                }

                var labels = new SortedSet<string>(StringComparer.Ordinal);
                var flags = new StringBuilder();
                char kind;
                model.MethodsByAddress.TryGetValue(start, out List<MethodDef>? methods);
                model.InstsByAddress.TryGetValue(start, out List<MethodInst>? insts);
                if (methods != null || insts != null)
                {
                    kind = 'M';
                    managed++;
                    var exact = new SortedSet<string>(StringComparer.Ordinal);
                    bool aggressive = false;
                    foreach (MethodDef m in methods ?? [])
                    {
                        exact.Add("M:" + FullKey(m));
                        labels.Add("D:" + FullKey(m));
                        aggressive |= (m.ImplFlags & AggressiveInlining) != 0;
                    }
                    foreach (MethodInst inst in insts ?? [])
                    {
                        exact.Add("M:" + inst + ":" + inst.Method.ReturnType.DisplayName + "/" + inst.Method.Parameters.Length);
                        labels.Add("D:" + FullKey(inst.Method));
                        aggressive |= (inst.Method.ImplFlags & AggressiveInlining) != 0;
                    }
                    // Many unrelated methods folded into one body say nothing about what the body is.
                    if (exact.Count > 12 || labels.Count > 12) flags.Append('X');
                    if (aggressive) flags.Append('A');
                    foreach (string e in exact.Take(12)) labels.Add(e);
                }
                else
                {
                    List<string>? names = null;
                    symbols?.TryGetValue(start, out names);
                    string? inlineName = names?.FirstOrDefault(n => PlainName(n).EndsWith("_inline", StringComparison.Ordinal));
                    if (inlineName != null && MangledPrefix(inlineName) is { } prefix && byMangled.TryGetValue(prefix, out HashSet<string>? definitions))
                    {
                        kind = 'I';
                        inline++;
                        // The exact method when its own function is known by the same hash; otherwise every
                        // method of that type with that name (the best a name alone can say).
                        var precise = new List<string>();
                        if (MethodHash.Match(inlineName) is { Success: true } copyHash && listedByHash.TryGetValue(copyHash.Value, out ulong original))
                        {
                            if (model.MethodsByAddress.TryGetValue(original, out List<MethodDef>? originals))
                                foreach (MethodDef m in originals)
                                    if (definitions.Contains(FullKey(m)))
                                        precise.Add(FullKey(m));
                            if (model.InstsByAddress.TryGetValue(original, out List<MethodInst>? originalInsts))
                                foreach (MethodInst inst in originalInsts)
                                    if (definitions.Contains(FullKey(inst.Method)) && !precise.Contains(FullKey(inst.Method)))
                                        precise.Add(FullKey(inst.Method));
                        }
                        if (precise.Count != 0)
                        {
                            exactCopies++;
                            foreach (string d in precise.Take(8)) labels.Add("D:" + d);
                        }
                        else
                            foreach (string d in definitions) labels.Add("D:" + d);
                    }
                    else if (names is { Count: > 0 })
                    {
                        kind = 'R';
                        named++;
                        foreach (string n in names.Take(3)) labels.Add("S:" + n);
                    }
                    else
                    {
                        kind = 'U';
                        unnamed++;
                    }
                    if (exportsAt.TryGetValue(start, out List<string>? exports))
                        foreach (string e in exports) labels.Add("E:" + e);
                }

                foreach (ushort t in tokens) tokenFile.Write(t);
                index.Write(offset);
                index.Write('\t');
                index.Write(tokens.Length);
                index.Write('\t');
                index.Write(start.ToString("X"));
                index.Write('\t');
                index.Write(instructions);
                index.Write('\t');
                index.Write(kind);
                index.Write('\t');
                index.Write(flags.Length == 0 ? "-" : flags.ToString());
                index.Write('\t');
                index.Write(string.Join(";;", labels.Take(40)).Replace('\t', ' ').Replace('\n', ' '));
                index.Write('\n');
                offset += tokens.Length;
                instructionTotal += instructions;
                written++;
            }
        }
        File.WriteAllText(Path.Combine(outDirectory, "meta.txt"),
            $"unity\t{model.UnityVersion?.ToString() ?? "unknown"}\nformat\t{model.Image.Format}/{model.Image.Arch}/{model.Image.Os}\n" +
            $"functions\t{written}\ntokens\t{offset}\ninstructions\t{instructionTotal}\nvocabulary\t{TokenVocabulary.Size}\n" +
            $"symbols\t{(symbols != null ? "yes" : "no")}\narch\t{model.Image.Arch}\n" +
            $"source\t{(sourcePath != null ? Path.GetFullPath(sourcePath) : "-")}\nsymbol-file\t{(symbolsPath != null ? Path.GetFullPath(symbolsPath) : "-")}\n");
        Console.WriteLine($"exported {written} functions ({managed} managed, {inline} private copies of which {exactCopies} tied to the exact method, {named} named runtime, {unnamed} unnamed; {failed} not decodable): " +
                          $"{offset:N0} tokens for {instructionTotal:N0} instructions ({(double)offset / Math.Max(1, instructionTotal):F2} per instruction), vocabulary {TokenVocabulary.Size} ({sw.ElapsedMilliseconds} ms)");
        return 0;
    }
}
