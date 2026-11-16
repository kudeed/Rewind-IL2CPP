using System.Diagnostics;
using Rewind.Analysis;
using Rewind.Analysis.Runtime;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Lab;

/// <summary>Research commands for recognizing runtime support functions in binaries that have no symbols.</summary>
internal static class SigLab
{
    private static (ModelCodeContext Context, CodeIndex Index) Open(Il2CppModel model)
    {
        var sw = Stopwatch.StartNew();
        var context = new ModelCodeContext(model);
        int added = context.DiscoverCallTargets();
        Console.WriteLine($"  {context.FunctionStarts.Count} function starts ({added} found as call targets, {sw.ElapsedMilliseconds} ms)");
        return (context, new CodeIndex(context));
    }

    /// <summary>
    /// How close each library signature comes to the functions at the given addresses: the near-identical-code
    /// stage's score (CodeIndex.Similarity of the sketches) and whether the instruction counts are close enough for
    /// that stage to compare them at all. For finding out why a helper was not identified.
    /// </summary>
    public static int Near(string libraryPath, Il2CppModel target, string[] addresses)
    {
        HelperLibrary library = HelperLibrary.Load(libraryPath);
        var (_, index) = Open(target);
        foreach (string text in addresses)
        {
            ulong address = Convert.ToUInt64(text.StartsWith("0x", StringComparison.OrdinalIgnoreCase) ? text[2..] : text, 16);
            if (index.Get(address) is not { } code) { Console.WriteLine($"=== 0x{address:X}: no code"); continue; }
            Console.WriteLine($"=== 0x{address:X}: {code.Instructions} instructions{(code.IsThunk ? $", thunk to 0x{index.ThunkTarget(address):X}" : "")}");
            foreach (var (entry, score) in library.Entries
                         .Where(e => !e.IsThunk)
                         .Select(e => (e, CodeIndex.Similarity(e.Sketch, code.Sketch)))
                         .OrderByDescending(x => x.Item2).Take(8))
            {
                bool window = code.Instructions >= entry.Instructions * 3 / 4 && code.Instructions <= entry.Instructions * 4 / 3 + 1;
                Console.WriteLine($"  {score:F3}  {entry.Info.Kind,-24} {entry.Instructions,5} ins {(window ? "" : "(outside the size window) ")}{entry.Info.Name}");
            }
        }
        return 0;
    }

    private static RuntimeHelpers FromSymbols(Il2CppModel model, string symbolsPath)
    {
        Dictionary<ulong, List<string>> symbols = CallStats.LoadSymbols(model.Image, symbolsPath);
        // Only code can be a helper; data symbols with similar names are not.
        var named = RuntimeHelpers.FromSymbols(symbols, a => model.MethodsByAddress.ContainsKey(a) || model.InstsByAddress.ContainsKey(a));
        var code = new RuntimeHelpers();
        foreach (var (address, info) in named.ByAddress)
            if (model.Image.IsCodeAddress(address))
                code.Add(address, info);
        return code;
    }

    /// <summary>
    /// sig-build &lt;out.sig&gt; (&lt;reference input&gt; &lt;symbols.tsv&gt;)+: writes the signature library of one or more builds
    /// that have symbols (several build configurations of one Unity version go into one library).
    /// </summary>
    public static int Build(string outPath, string[] pairs)
    {
        HelperLibrary? merged = null;
        for (int i = 0; i + 1 < pairs.Length; i += 2)
        {
            Il2CppModel reference = Program.LoadModel(pairs[i]);
            RuntimeHelpers named = FromSymbols(reference, pairs[i + 1]);
            var (context, index) = Open(reference);
            HelperLibrary library = HelperLibrary.Build(named, index, reference.Image, context.IsManaged,
                reference.UnityVersion?.ToString() ?? "unknown", reference.Image.Os.ToString(), reference.Image.Arch.ToString());
            Console.WriteLine($"  {named.ByAddress.Count} named helpers -> {library.Entries.Count} signatures");
            if (merged == null) merged = library;
            else merged.Merge(library);
        }
        if (merged == null) return 2;
        Directory.CreateDirectory(Path.GetDirectoryName(Path.GetFullPath(outPath))!);
        merged.Save(outPath);
        Console.WriteLine($"{merged.Entries.Count} signatures written to {outPath}");
        return 0;
    }

    /// <summary>
    /// sig-apply &lt;library.sig&gt; &lt;target input&gt; [symbols.tsv]: finds the library's functions in the target. With a
    /// symbol file for the target, every identification is checked against the name the symbols give that address.
    /// </summary>
    public static int Apply(string libraryPath, Il2CppModel target, string? symbolsPath)
    {
        HelperLibrary library = HelperLibrary.Load(libraryPath);
        Console.WriteLine($"library: {library.Entries.Count} signatures from Unity {library.Unity} {library.Platform}/{library.Arch}");
        var (context, index) = Open(target);
        var sw = Stopwatch.StartNew();
        RuntimeHelpers matched = library.Match(index, target.Image, context.FunctionStarts.Where(a => !context.IsManaged(a)), out HelperMatchReport report,
            context.FunctionStarts.Where(context.IsManaged));
        Console.WriteLine($"{report} ({sw.ElapsedMilliseconds} ms)");
        // What matters is whether each kind of helper was found at all; a library holds several variants of each.
        var identifiedKinds = matched.ByAddress.Values.GroupBy(i => i.Kind).ToDictionary(g => g.Key, g => g.Count());
        var libraryKinds = library.Entries.Select(e => e.Info.Kind).Distinct().ToList();
        Console.WriteLine($"helper kinds: {identifiedKinds.Count} of {libraryKinds.Count} identified");
        Console.WriteLine("  identified: " + string.Join(", ", identifiedKinds.OrderByDescending(kv => kv.Value).Select(kv => $"{kv.Key} x{kv.Value}")));
        Console.WriteLine("  NOT identified: " + string.Join(", ", libraryKinds.Where(k => !identifiedKinds.ContainsKey(k))));

        if (Environment.GetEnvironmentVariable("REWIND_SIG_LIST") is { Length: > 0 } filter)
            foreach (var (address, info) in matched.ByAddress.OrderBy(kv => kv.Value.Kind).ThenBy(kv => kv.Key))
                if (filter == "*" || info.Kind.ToString().Contains(filter, StringComparison.OrdinalIgnoreCase))
                {
                    FunctionCode? code = index.Get(address);
                    Console.WriteLine($"  {info.Kind,-24} 0x{address:X} {report.Stage[address],-7} {code?.Instructions,4} ins -> 0x{index.ThunkTarget(address):X}  {Short(info.Name)}");
                }

        if (symbolsPath == null) return 0;
        RuntimeHelpers truth = FromSymbols(target, symbolsPath);
        var agree = new Dictionary<MatchStage, int>();
        var unnamed = new Dictionary<MatchStage, int>();
        int wrong = 0;
        foreach (var (address, info) in matched.ByAddress)
        {
            MatchStage stage = report.Stage[address];
            HelperKind expected = truth.KindAt(address);
            if (expected == info.Kind) agree[stage] = agree.GetValueOrDefault(stage) + 1;
            else if (expected == HelperKind.None) unnamed[stage] = unnamed.GetValueOrDefault(stage) + 1;
            else
            {
                wrong++;
                Console.WriteLine($"  WRONG ({stage}) at 0x{address:X}: identified as {info.Kind}, symbols say {expected} ({Short(truth.At(address)!.Name)})");
            }
        }
        var missedKinds = new Dictionary<HelperKind, int>();
        int missed = 0;
        foreach (var (address, info) in truth.ByAddress)
            if (matched.At(address) == null)
            {
                missed++;
                missedKinds[info.Kind] = missedKinds.GetValueOrDefault(info.Kind) + 1;
            }
        string Show(Dictionary<MatchStage, int> d) => d.Count == 0 ? "0" : string.Join(", ", d.OrderBy(kv => kv.Key).Select(kv => $"{kv.Key} {kv.Value}"));
        Console.WriteLine($"against symbols: agree [{Show(agree)}]; WRONG {wrong}; identified but not a named helper [{Show(unnamed)}]; named helpers not identified {missed}");
        if (missed != 0)
            Console.WriteLine("  not identified: " + string.Join(", ", missedKinds.OrderByDescending(kv => kv.Value).Select(kv => $"{kv.Key} x{kv.Value}")));
        return wrong == 0 ? 0 : 1;
    }

    private static string Short(string name) => name.Length > 100 ? name[..100] : name;
}
