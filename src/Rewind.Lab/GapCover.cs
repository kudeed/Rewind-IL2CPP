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

    public static int Run(Il2CppModel model, string symbolsPath, string? assemblyFilter)
    {
        ProgramAnalysis program = LiftLab.MakeProgram(model, symbolsPath);
        var pipeline = new MethodPipeline(program);
        var perMethod = new List<HashSet<string>>();
        int total = 0, clean = 0, crashed = 0;
        foreach (MethodDef method in model.Methods)
        {
            if (method.Address == 0) continue;
            if (assemblyFilter != null && method.DeclaringType.Assembly.Name != assemblyFilter) continue;
            if (method.DeclaringType.GenericParameters.Length != 0 || method.GenericParameters.Length != 0) continue;
            if (!Rewind.Output.AssemblyEmitter.HasIlBody(method)) continue;
            total++;
            try
            {
                HMethod h = pipeline.Recover(method);
                if (h.Problems.Count == 0) { clean++; continue; }
                perMethod.Add(h.Problems.Select(Kind).ToHashSet());
            }
            catch (Exception)
            {
                crashed++;
                perMethod.Add(["crash"]);
            }
        }
        Console.WriteLine($"{total} methods: {clean} complete ({100.0 * clean / Math.Max(1, total):F1}%), {perMethod.Count} blocked, {crashed} crashed");
        if (program.ProposalsChecked != 0) Console.WriteLine($"model proposals: {program.ProposalsChecked} checked, {program.ProposalsConfirmed} confirmed by equal recovered code");

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
