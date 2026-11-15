using System.IO.Compression;
using System.Text.Json;
using Rewind.Analysis;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Lab;

/// <summary>
/// Ground truth for stack typing from the compiler's own records (tools/pdblocals.py output), in managed terms.
///
/// The PDB names C++ types (List_1_t5CAE...*); which managed type each stands for is learned from the functions
/// themselves: every function is a known method, so its parameters pair C++ types with the managed parameter
/// types from the metadata. A C++ type that always pairs with one managed type means that type.
///
/// pdb-labels &lt;input&gt; &lt;symbols&gt; &lt;locals.jsonl.gz&gt; &lt;out.tsv&gt; [oracle]
///   writes, per function, the managed type of every program-level stack local (offset from the entry stack
///   pointer, size, type, the code ranges it holds that value). With "oracle", also recovers every method with
///   those types given to the decompiler up front, and reports how many more methods come out complete: the most a
///   perfect stack-type predictor could add.
/// </summary>
internal static class PdbLabels
{
    private sealed record Local(string Name, string Type, int Size, bool Param, bool Inlined, List<(string Kind, long A, long B, long Start, long Length)> Loc);
    private sealed record Function(ulong Rva, string Name, int FrameSize, int Saved, string? Base, List<Local> Locals);

    private static List<Function> Read(string path)
    {
        var result = new List<Function>();
        using var stream = new GZipStream(File.OpenRead(path), CompressionMode.Decompress);
        using var reader = new StreamReader(stream);
        string? line;
        while ((line = reader.ReadLine()) != null)
        {
            using JsonDocument doc = JsonDocument.Parse(line);
            JsonElement f = doc.RootElement;
            var locals = new List<Local>();
            foreach (JsonElement l in f.GetProperty("locals").EnumerateArray())
            {
                var loc = new List<(string, long, long, long, long)>();
                foreach (JsonElement x in l.GetProperty("loc").EnumerateArray())
                {
                    var a = x.EnumerateArray().ToArray();
                    string kind = a[0].GetString()!;
                    loc.Add(kind switch
                    {
                        "frame" or "reg" => (kind, a[1].GetInt64(), 0, a[2].GetInt64(), a[3].GetInt64()),
                        _ => (kind, a[1].GetInt64(), a[2].GetInt64(), a[3].GetInt64(), a[4].GetInt64()),
                    });
                }
                locals.Add(new Local(l.GetProperty("name").GetString()!, l.GetProperty("type").GetString()!, l.GetProperty("size").GetInt32(),
                    l.GetProperty("param").GetBoolean(), l.TryGetProperty("inlined", out _), loc));
            }
            JsonElement frame = f.GetProperty("frame");
            bool hasFrame = frame.ValueKind == JsonValueKind.Object;
            result.Add(new Function(f.GetProperty("rva").GetUInt64(), f.GetProperty("name").GetString()!,
                hasFrame ? frame.GetProperty("size").GetInt32() : 0, hasFrame ? frame.GetProperty("saved").GetInt32() : 0,
                hasFrame ? frame.GetProperty("base").GetString() : null, locals));
        }
        return result;
    }

    private static string Kind(string p)
    {
        string key = System.Text.RegularExpressions.Regex.Replace(p, "0x[0-9A-Fa-f]+", "N");
        key = System.Text.RegularExpressions.Regex.Replace(key, "%[0-9]+", "%");
        key = System.Text.RegularExpressions.Regex.Replace(key, @"\(.*\)", "(..)");
        return System.Text.RegularExpressions.Regex.Replace(key, " of [^ ]+$| into a .*$|on [^ ]+$", "");
    }

    private static bool IsPlumbing(Local l) =>
        l.Type.Contains("::", StringComparison.Ordinal) || l.Type.Contains("lambda", StringComparison.Ordinal) ||
        l.Type.StartsWith("PInvokeArguments", StringComparison.Ordinal) || l.Type.StartsWith("Il2Cpp", StringComparison.Ordinal) ||
        l.Type.StartsWith("il2cpp", StringComparison.Ordinal) || l.Name is "method" or "pinvokeArgs" or "__finallyBlock" or "__active_exceptions";

    private static readonly Dictionary<string, Il2CppTypeEnum> Primitives = new()
    {
        ["int32_t"] = Il2CppTypeEnum.I4, ["uint32_t"] = Il2CppTypeEnum.U4, ["int64_t"] = Il2CppTypeEnum.I8, ["uint64_t"] = Il2CppTypeEnum.U8,
        ["int16_t"] = Il2CppTypeEnum.I2, ["uint16_t"] = Il2CppTypeEnum.U2, ["int8_t"] = Il2CppTypeEnum.I1, ["uint8_t"] = Il2CppTypeEnum.U1,
        ["float"] = Il2CppTypeEnum.R4, ["double"] = Il2CppTypeEnum.R8, ["bool"] = Il2CppTypeEnum.Boolean, ["wchar_t"] = Il2CppTypeEnum.Char,
        ["char16_t"] = Il2CppTypeEnum.Char, ["RuntimeObject*"] = Il2CppTypeEnum.Object, ["String_t*"] = Il2CppTypeEnum.String,
    };

    public static int Run(Il2CppModel model, string symbolsPath, string localsPath, string outPath, bool oracle)
    {
        ProgramAnalysis program = LiftLab.MakeProgram(model, symbolsPath);
        List<Function> functions = Read(localsPath);
        ulong imageBase = model.Image.ImageBase;

        // 1. C++ type -> managed type, from parameters.
        var votes = new Dictionary<string, Dictionary<string, (TypeSig Type, int Count)>>();
        void Vote(string cpp, TypeSig managed)
        {
            if (managed.ContainsGenericParameter) return;
            if (!votes.TryGetValue(cpp, out var byName)) votes[cpp] = byName = [];
            string key = managed.DisplayName;
            byName[key] = byName.TryGetValue(key, out var v) ? (v.Type, v.Count + 1) : (managed, 1);
        }
        void Pair(string cpp, TypeSig managed)
        {
            if (managed is ByRefSig byRef)
            {
                if (cpp.EndsWith('*') || cpp.EndsWith('&')) Vote(cpp[..^1], byRef.ElementType);
                return;
            }
            if (managed.IsValueType) Vote(cpp, managed);
            else if (cpp.EndsWith('*')) Vote(cpp, managed);
        }
        var methodAt = new Dictionary<ulong, (MethodDef Method, TypeSig[] ClassArgs, TypeSig[] MethodArgs)?>();
        (MethodDef, TypeSig[], TypeSig[])? MethodAt(ulong va)
        {
            if (methodAt.TryGetValue(va, out var known)) return known;
            (MethodDef, TypeSig[], TypeSig[])? found = null;
            int count = 0;
            if (model.MethodsByAddress.TryGetValue(va, out List<MethodDef>? defs))
                foreach (MethodDef m in defs) { found = (m, [], []); count++; }
            if (model.InstsByAddress.TryGetValue(va, out List<MethodInst>? insts))
                foreach (MethodInst i in insts) { found = (i.Method, i.ClassArguments, i.MethodArguments); count++; }
            return methodAt[va] = count == 1 ? found : null;
        }
        TypeSig Concrete(TypeSig t, TypeSig[] classArgs, TypeSig[] methodArgs) =>
            classArgs.Length == 0 && methodArgs.Length == 0 ? t : model.Sigs.Substitute(t, classArgs, methodArgs);
        foreach (Function f in functions)
        {
            if (MethodAt(imageBase + f.Rva) is not var (method, classArgs, methodArgs)) continue;
            foreach (Local l in f.Locals)
            {
                if (!l.Param) continue;
                if (l.Name == "__this")
                {
                    TypeSig self = classArgs.Length != 0 && method.DeclaringType.Sig is var open
                        ? model.Sigs.Substitute(open, classArgs, []) : method.DeclaringType.Sig;
                    if (l.Type.EndsWith('*')) Vote(self.IsValueType ? l.Type[..^1] : l.Type, self);
                    continue;
                }
                // ___<index>_<name>
                if (!l.Name.StartsWith("___", StringComparison.Ordinal)) continue;
                int underscore = l.Name.IndexOf('_', 3);
                if (underscore < 0 || !int.TryParse(l.Name[3..underscore], out int index) || index >= method.Parameters.Length) continue;
                Pair(l.Type, Concrete(method.Parameters[index].Type, classArgs, methodArgs));
            }
        }
        var map = new Dictionary<string, TypeSig>();
        int ambiguous = 0;
        foreach (var (cpp, byName) in votes)
        {
            var best = byName.Values.OrderByDescending(v => v.Count).First();
            int votesTotal = byName.Values.Sum(v => v.Count);
            if (best.Count * 20 >= votesTotal * 19) map[cpp] = best.Type;
            else ambiguous++;
        }
        TypeSig? Managed(string cpp)
        {
            if (Primitives.TryGetValue(cpp, out Il2CppTypeEnum e)) return model.Sigs.Primitive(e);
            if (map.TryGetValue(cpp, out TypeSig? t)) return t;
            return null;
        }
        Console.WriteLine($"C++ types paired with managed types: {map.Count} mapped, {ambiguous} ambiguous (shared generic code)");

        // 2. Labels: program-level stack locals with a known managed type.
        var hints = new Dictionary<ulong, Dictionary<int, TypeSig>>();
        int stackLocals = 0, labelled = 0, reused = 0;
        using (var writer = new StreamWriter(outPath))
        {
            writer.WriteLine("rva\toffset\tsize\ttype\tname\tranges");
            foreach (Function f in functions)
            {
                if (f.Base != "rsp" || MethodAt(imageBase + f.Rva) == null) continue;
                int shift = f.FrameSize + f.Saved;
                var perOffset = new Dictionary<int, HashSet<string>>();
                var rows = new List<(int Offset, int Size, TypeSig? Type, Local Local, string Ranges)>();
                foreach (Local l in f.Locals)
                {
                    if (IsPlumbing(l)) continue;
                    var frames = l.Loc.Where(x => x.Kind == "frame" && x.A - shift < 0).ToList();
                    foreach (var group in frames.GroupBy(x => (int)(x.A - shift)))
                    {
                        stackLocals++;
                        TypeSig? type = Managed(l.Type);
                        if (!perOffset.TryGetValue(group.Key, out var kinds)) perOffset[group.Key] = kinds = [];
                        kinds.Add(type?.DisplayName ?? l.Type);
                        string ranges = string.Join(",", group.Select(x => $"{x.Start:X}+{x.Length}"));
                        rows.Add((group.Key, l.Size, type, l, ranges));
                    }
                }
                foreach (var row in rows)
                {
                    if (row.Type == null) continue;
                    labelled++;
                    writer.WriteLine($"{f.Rva:X}\t{row.Offset}\t{row.Size}\t{row.Type.DisplayName}\t{row.Local.Name}\t{row.Ranges}");
                    if (perOffset[row.Offset].Count == 1)
                    {
                        if (!hints.TryGetValue(imageBase + f.Rva, out var h)) hints[imageBase + f.Rva] = h = [];
                        h[row.Offset] = row.Type;
                    }
                }
                reused += perOffset.Count(kv => kv.Value.Count > 1);
            }
        }
        Console.WriteLine($"stack locals: {stackLocals}, with a managed type: {labelled}; offsets holding several types: {reused}; functions with hints: {hints.Count}");
        if (!oracle) return 0;

        // 3. Oracle: recover with and without the true stack types.
        var pipeline = new Rewind.Analysis.Recover.MethodPipeline(program);
        int total = 0, before = 0, after = 0, gained = 0, lost = 0;
        var newProblems = new Dictionary<string, int>();
        var remaining = new Dictionary<string, int>();
        foreach (MethodDef method in model.Methods)
        {
            if (method.Address == 0 || !hints.ContainsKey(method.Address)) continue;
            total++;
            program.FrameHints = null;
            bool cleanBefore, cleanAfter;
            List<string> problemsAfter;
            try
            {
                cleanBefore = pipeline.Recover(method).Problems.Count == 0;
                program.FrameHints = address => hints.GetValueOrDefault(address);
                var h = pipeline.Recover(method);
                cleanAfter = h.Problems.Count == 0;
                problemsAfter = h.Problems;
            }
            catch { continue; }
            finally { program.FrameHints = null; }
            if (!cleanAfter)
                foreach (string p in problemsAfter.Select(Kind).Distinct()) remaining[p] = remaining.GetValueOrDefault(p) + 1;
            if (cleanBefore) before++;
            if (cleanAfter) after++;
            if (cleanAfter && !cleanBefore) gained++;
            if (cleanBefore && !cleanAfter)
            {
                lost++;
                foreach (string p in problemsAfter.Distinct()) newProblems[p] = newProblems.GetValueOrDefault(p) + 1;
            }
        }
        Console.WriteLine($"oracle over {total} methods with stack hints: complete {before} -> {after} (+{gained}, -{lost})");
        foreach (var (p, n) in newProblems.OrderByDescending(kv => kv.Value).Take(8)) Console.WriteLine($"  lost by: {n,5}  {p}");
        Console.WriteLine("what still blocks them (methods mentioning each):");
        foreach (var (p, n) in remaining.OrderByDescending(kv => kv.Value).Take(25)) Console.WriteLine($"  {n,6}  {p}");
        return 0;
    }
}
