using Mono.Cecil;

namespace Rewind.Lab;

/// <summary>pinvoke-check &lt;recovered dir&gt; &lt;original Managed dir&gt;: compares the DllImport of every P/Invoke declaration.</summary>
internal static class PInvokeCheck
{
    public static int Run(string recoveredDir, string originalDir)
    {
        int total = 0, same = 0, missing = 0;
        var differences = new Dictionary<string, int>();
        foreach (string originalPath in Directory.GetFiles(originalDir, "*.dll"))
        {
            string recoveredPath = Path.Combine(recoveredDir, Path.GetFileName(originalPath));
            if (!File.Exists(recoveredPath)) continue;
            using var original = AssemblyDefinition.ReadAssembly(originalPath);
            using var recovered = AssemblyDefinition.ReadAssembly(recoveredPath);
            var recoveredMethods = recovered.MainModule.GetTypes().SelectMany(t => t.Methods).Where(m => m.IsPInvokeImpl)
                .GroupBy(m => m.FullName).ToDictionary(g => g.Key, g => g.First());
            foreach (MethodDefinition m in original.MainModule.GetTypes().SelectMany(t => t.Methods).Where(m => m.IsPInvokeImpl && m.PInvokeInfo != null))
            {
                total++;
                if (!recoveredMethods.TryGetValue(m.FullName, out MethodDefinition? r) || r.PInvokeInfo == null) { missing++; continue; }
                var problems = new List<string>();
                if (!string.Equals(m.PInvokeInfo.Module.Name, r.PInvokeInfo.Module.Name, StringComparison.OrdinalIgnoreCase)) problems.Add("module");
                if (m.PInvokeInfo.EntryPoint != r.PInvokeInfo.EntryPoint) problems.Add("entry point");
                if (m.PInvokeInfo.Attributes != r.PInvokeInfo.Attributes) problems.Add($"attributes {m.PInvokeInfo.Attributes} vs {r.PInvokeInfo.Attributes}");
                if (problems.Count == 0) { same++; continue; }
                string key = string.Join(", ", problems);
                if (differences.TryAdd(key, 1)) Console.WriteLine($"  {m.FullName}: {key} (original {m.PInvokeInfo.Module.Name}!{m.PInvokeInfo.EntryPoint}, recovered {r.PInvokeInfo.Module.Name}!{r.PInvokeInfo.EntryPoint})");
                else differences[key]++;
            }
        }
        Console.WriteLine($"{total} P/Invoke declarations: {same} identical, {missing} missing, {total - same - missing} different");
        foreach (var (key, count) in differences.OrderByDescending(kv => kv.Value)) Console.WriteLine($"  {count,5}  {key}");
        return 0;
    }
}
