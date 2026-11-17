using System.Text.RegularExpressions;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;

namespace Rewind.Lab;

/// <summary>
/// Which kinds of gap, once closed, complete the most methods? Every method lists the kinds that block it;
/// a method becomes complete only when all of its kinds are closed. The greedy order printed here is the
/// work plan by yield.
/// </summary>
internal static class GapCover
{
    internal static string Kind(string problem)
    {
        string key = Regex.Replace(problem, "0x[0-9A-Fa-f]+", "N");
        key = Regex.Replace(key, "%[0-9]+", "%");
        key = Regex.Replace(key, @"\(.*$", "").Trim();
        key = Regex.Replace(key, " of [^ ]+.*$| into a .*$| on [^ ]+$| for .*$", "");
        key = Regex.Replace(key, "access of [0-9]+ bytes spans fields", "access spans fields");
        key = Regex.Replace(key, "could not rebuild .* from register bits", "could not rebuild struct from register bits");
        key = Regex.Replace(key, "array index scale [0-9]+ does not match element size [0-9]+", "array index scale mismatch");
        key = Regex.Replace(key, "the constructor .* was inlined.*", "inlined constructor not folded");
        key = Regex.Replace(key, "virtual slot [0-9]+ not found.*", "virtual slot not found");
        key = Regex.Replace(key, "^(load|store|address computation): ", "");
        return key;
    }

    private static string Digest(string text) =>
        Convert.ToHexString(System.Security.Cryptography.SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(text)), 0, 8);

    public static int Run(Il2CppModel model, string symbolsPath, string? assemblyFilter)
    {
        ProgramAnalysis program = LiftLab.MakeProgram(model, symbolsPath);
        var perMethod = new List<HashSet<string>>();
        int total = 0, clean = 0, crashed = 0;
        // REWIND_GAP_LIST=<file>: every method with what blocks it, to compare two rounds method by method.
        string? listPath = Environment.GetEnvironmentVariable("REWIND_GAP_LIST");
        List<string>? listed = listPath != null ? [] : null;
        // REWIND_GAP_DIGEST=<file>: every method with a digest of what it was recovered as. Two rounds that give
        // the same file gave the same code for every method.
        string? digestPath = Environment.GetEnvironmentVariable("REWIND_GAP_DIGEST");
        var methods = new List<MethodDef>();
        foreach (MethodDef method in model.Methods)
        {
            if (method.Address == 0) continue;
            if (assemblyFilter != null && method.DeclaringType.Assembly.Name != assemblyFilter) continue;
            if (method.DeclaringType.GenericParameters.Length != 0 || method.GenericParameters.Length != 0) continue;
            if (!Rewind.Output.AssemblyEmitter.HasIlBody(method)) continue;
            methods.Add(method);
        }
        // REWIND_GAP_ORDER=reverse, or a number to shuffle by: the order the methods are recovered in. What a
        // method is recovered as must not depend on it (the lists are written in the methods' own order).
        int[] order = Enumerable.Range(0, methods.Count).ToArray();
        string? orderName = Environment.GetEnvironmentVariable("REWIND_GAP_ORDER");
        if (orderName == "reverse") Array.Reverse(order);
        else if (int.TryParse(orderName, out int seed)) new Random(seed).Shuffle(order);
        var problems = new List<string>?[methods.Count];
        var crashes = new string?[methods.Count];
        var digests = new string?[methods.Count];
        var shown = new HashSet<ulong>();
        foreach (string address in (Environment.GetEnvironmentVariable("REWIND_GAP_SHOW") ?? "").Split(';', StringSplitOptions.RemoveEmptyEntries))
            shown.Add(Convert.ToUInt64(address.Trim(), 16));
        // (On REWIND_THREADS threads, one per processor when it is not set.)
        var watch = System.Diagnostics.Stopwatch.StartNew();
        bool progress = Environment.GetEnvironmentVariable("REWIND_GAP_PROGRESS") != null;
        // (With REWIND_GAP_PROGRESS also: the methods that have been under way for a long time, now and then.)
        var underWay = new System.Collections.Concurrent.ConcurrentDictionary<int, (int Method, long Started)>();
        using var slow = progress
            ? new Timer(_ =>
            {
                foreach (var (thread, (method, started)) in underWay)
                {
                    double seconds = System.Diagnostics.Stopwatch.GetElapsedTime(started).TotalSeconds;
                    if (seconds >= 15) Console.Error.WriteLine($"  under way for {seconds:F0} s on thread {thread}: 0x{methods[method].Address:X} {methods[method].FullName}");
                }
            }, null, 20000, 20000)
            : null;
        RecoveryThreads.Run(program, methods.Count, 0,
            (pipeline, k) =>
            {
                if (progress) underWay[Environment.CurrentManagedThreadId] = (order[k], System.Diagnostics.Stopwatch.GetTimestamp());
                try
                {
                    HMethod h = pipeline.Recover(methods[order[k]]);
                    string? text = digestPath != null ? HirPrinter.Print(h) + "\n" + string.Join("\n", h.Problems) : null;
                    // REWIND_GAP_SHOW=<address>;<address>: what those methods were recovered as, next to the digests.
                    if (text != null && shown.Contains(methods[order[k]].Address)) File.WriteAllText($"{digestPath}.0x{methods[order[k]].Address:X}.txt", text);
                    return (Problems: h.Problems.Distinct().ToList(), Digest: text != null ? Digest(text) : null, Crash: (string?)null);
                }
                catch (Exception e)
                {
                    return (Problems: (List<string>?)null, Digest: (string?)null, Crash: e.GetType().Name);
                }
                finally
                {
                    if (progress) underWay.TryRemove(Environment.CurrentManagedThreadId, out _);
                }
            },
            (k, r) =>
            {
                (problems[order[k]], digests[order[k]], crashes[order[k]]) = (r.Problems, r.Digest, r.Crash);
                // REWIND_GAP_PROGRESS: how far it is, every few thousand methods.
                if (progress && (k + 1) % 5000 == 0) Console.Error.WriteLine($"{k + 1} of {methods.Count} methods after {watch.Elapsed.TotalSeconds:F0} s");
            });
        Console.Error.WriteLine($"recovered on {Math.Min(RecoveryThreads.Default, Math.Max(1, methods.Count))} threads in {watch.Elapsed.TotalSeconds:F0} s; " +
                                $"peak memory {System.Diagnostics.Process.GetCurrentProcess().PeakWorkingSet64 >> 20} MB");
        if (RecoveryStats.On) Console.Error.WriteLine(RecoveryStats.Report() + $"; threads stood still for {RecoveryThreads.Waited:F0} s; garbage collections {GC.CollectionCount(0)}/{GC.CollectionCount(1)}/{GC.CollectionCount(2)}, {GC.GetTotalPauseDuration().TotalSeconds:F0} s paused");
        if (Environment.GetEnvironmentVariable("REWIND_CHECK_KEPT") != null)
        {
            var (kept, changed) = program.CheckKept();
            Console.Error.WriteLine($"kept bodies: {kept}; changed after they were kept: {changed.Count}");
            foreach (string name in changed.Take(40)) Console.Error.WriteLine("  changed: " + name);
        }
        var digestLines = digestPath != null ? new List<string>() : null;
        for (int i = 0; i < methods.Count; i++)
        {
            MethodDef method = methods[i];
            total++;
            digestLines?.Add($"0x{method.Address:X}\t{method.FullName}\t{digests[i] ?? "crash " + crashes[i]}");
            if (problems[i] is { } found)
            {
                listed?.Add($"0x{method.Address:X}\t{method.FullName}\t{(found.Count == 0 ? "complete" : string.Join(" | ", found.Take(4)))}");
                if (found.Count == 0) { clean++; continue; }
                perMethod.Add(found.Select(Kind).ToHashSet());
            }
            else
            {
                listed?.Add($"0x{method.Address:X}\t{method.FullName}\tcrash {crashes[i]}");
                crashed++;
                perMethod.Add(["crash"]);
            }
        }
        if (listPath != null) File.WriteAllLines(listPath, listed!);
        if (digestPath != null) File.WriteAllLines(digestPath, digestLines!);
        Console.WriteLine($"{total} methods: {clean} complete ({100.0 * clean / Math.Max(1, total):F1}%), {perMethod.Count} blocked, {crashed} crashed");

        var fixedKinds = new HashSet<string>();
        int done = clean;
        Console.WriteLine("greedy order (kind -> methods completed by closing it after the ones above; cumulative share):");
        for (int step = 0; step < 40 && perMethod.Count != 0; step++)
        {
            // Value of a kind: methods it alone still blocks, plus a share of methods it blocks together with others.
            var solo = new Dictionary<string, double>();
            foreach (HashSet<string> kinds in perMethod)
            {
                var open = kinds.Where(k => !fixedKinds.Contains(k)).ToList();
                if (open.Count == 0) continue;
                foreach (string k in open) solo[k] = solo.GetValueOrDefault(k) + 1.0 / (open.Count * open.Count);
            }
            if (solo.Count == 0) break;
            string best = solo.OrderByDescending(kv => kv.Value).First().Key;
            fixedKinds.Add(best);
            int before = perMethod.Count;
            int touching = perMethod.Count(k => k.Contains(best));
            perMethod.RemoveAll(kinds => kinds.All(fixedKinds.Contains));
            done += before - perMethod.Count;
            Console.WriteLine($"  {before - perMethod.Count,6} (+{touching,6} touched)  {100.0 * done / total,5:F1}%  {best}");
        }
        return 0;
    }
}
