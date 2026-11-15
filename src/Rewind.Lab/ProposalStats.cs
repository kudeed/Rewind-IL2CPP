using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Lab;

/// <summary>
/// proposal-stats &lt;input&gt; &lt;symbols|sig&gt; [count]: for a sample of the model's proposals (REWIND_IDENTIFICATIONS, best
/// score first), why checking the best candidate succeeds or fails: the candidate or the copy is not recovered
/// completely, or the two recover to different code (and then how different).
/// </summary>
internal static class ProposalStats
{
    public static int Run(Il2CppModel model, string symbolsPath, int count)
    {
        ProgramAnalysis program = LiftLab.MakeProgram(model, symbolsPath);
        if (program.Identified == null || program.Identified.Proposals.Count == 0)
        {
            Console.WriteLine("no proposals loaded (REWIND_IDENTIFICATIONS)");
            return 1;
        }
        program.CopyVerifier = (_, _) => false; // look at each proposal on its own; no nested checks
        var pipeline = new Rewind.Analysis.Recover.MethodPipeline(program);
        var outcome = new Dictionary<string, int>();
        var ownProblems = new Dictionary<string, int>();
        var copyProblems = new Dictionary<string, int>();
        var examples = new Dictionary<string, List<string>>();
        void Count(Dictionary<string, int> d, string key) => d[key] = d.GetValueOrDefault(key) + 1;
        string Kind(string p)
        {
            string key = System.Text.RegularExpressions.Regex.Replace(p, "0x[0-9A-Fa-f]+", "N");
            key = System.Text.RegularExpressions.Regex.Replace(key, "%[0-9]+", "%");
            return key.Length > 60 ? key[..60] : key;
        }
        int done = 0;
        foreach (var (address, candidates) in program.Identified.Proposals.OrderByDescending(kv => kv.Value[0].Score).Take(count))
        {
            done++;
            string result = "no candidate recovers to the same code";
            string? detail = null;
            bool anyOwnComplete = false, anyCopyComplete = false;
            foreach (var (score, group) in candidates)
            {
                var (method, own, copy, error) = pipeline.RecoverBoth(address, group[0]);
                if (method == null || own == null || copy == null) continue;
                if (own.Problems.Count != 0) { foreach (string p in own.Problems.Select(Kind).Distinct()) Count(ownProblems, p); continue; }
                anyOwnComplete = true;
                if (copy.Problems.Count != 0) { foreach (string p in copy.Problems.Select(Kind).Distinct()) Count(copyProblems, p); continue; }
                anyCopyComplete = true;
                string a = HirPrinter.Canonical(own), b = HirPrinter.Canonical(copy);
                if (a == b) { result = "same code"; detail = $"0x{address:X} = {method.FullName} ({score:F3})"; break; }
                detail ??= $"0x{address:X} vs {method.FullName} ({score:F3}): {a.Split('\n').Length} / {b.Split('\n').Length} lines";
            }
            if (result != "same code")
                result = !anyOwnComplete ? "no candidate method is itself recovered completely"
                    : !anyCopyComplete ? "the function, read as a candidate, is not recovered completely" : result;
            Count(outcome, result);
            if (detail != null)
            {
                if (!examples.TryGetValue(result, out List<string>? list)) examples[result] = list = [];
                if (list.Count < 6) list.Add(detail);
            }
        }
        Console.WriteLine($"{done} proposals looked at (best score first):");
        foreach (var (key, n) in outcome.OrderByDescending(kv => kv.Value))
        {
            Console.WriteLine($"  {n,5}  {key}");
            if (examples.TryGetValue(key, out List<string>? list))
                foreach (string e in list) Console.WriteLine("           " + e);
        }
        Console.WriteLine("what keeps candidate methods from complete recovery:");
        foreach (var (key, n) in ownProblems.OrderByDescending(kv => kv.Value).Take(8)) Console.WriteLine($"  {n,5}  {key}");
        Console.WriteLine("what keeps the function, read as a candidate, from complete recovery:");
        foreach (var (key, n) in copyProblems.OrderByDescending(kv => kv.Value).Take(8)) Console.WriteLine($"  {n,5}  {key}");
        return 0;
    }
}
