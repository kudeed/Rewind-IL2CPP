using Iced.Intel;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Lab;

/// <summary>
/// Research tool: which non-managed functions does managed code call, and how often? With a symbol file this
/// names the runtime helpers the lifter must understand.
/// </summary>
internal static class CallStats
{
    public static Dictionary<ulong, List<string>> LoadSymbols(NativeImage image, string path)
    {
        var namesAt = new Dictionary<ulong, List<string>>();
        foreach (string line in File.ReadLines(path))
        {
            string[] parts = line.Split('\t', 3);
            if (parts.Length < 3) continue;
            ulong va = image.ImageBase + Convert.ToUInt64(parts[0], 16);
            if (!namesAt.TryGetValue(va, out List<string>? list)) namesAt[va] = list = [];
            list.Add(parts[2]);
        }
        return namesAt;
    }

    public static int Run(Il2CppModel model, string symbolsPath, int top)
    {
        NativeImage image = model.Image;
        if (image.Arch != CpuArch.X64)
        {
            Console.WriteLine("call-stats currently supports x64 only");
            return 1;
        }
        Dictionary<ulong, List<string>> symbols = LoadSymbols(image, symbolsPath);

        // Every address that starts a managed method body (definitions and generic instantiations).
        var managed = new HashSet<ulong>(model.MethodsByAddress.Keys);
        managed.UnionWith(model.InstsByAddress.Keys);

        var counts = new Dictionary<ulong, int>();
        var callers = new Dictionary<ulong, int>();
        long instructions = 0;
        int functions = 0;

        foreach (FunctionRange fn in image.FunctionTable)
        {
            if (!managed.Contains(fn.Start)) continue;
            functions++;
            int length = (int)(fn.End - fn.Start);
            if (!image.TrySpan(fn.Start, length, out ReadOnlySpan<byte> code)) continue;
            var reader = new ByteArrayCodeReader(code.ToArray());
            var decoder = Decoder.Create(64, reader, fn.Start);
            ulong end = fn.End;
            var seen = new HashSet<ulong>();
            while (decoder.IP < end)
            {
                decoder.Decode(out Instruction ins);
                if (ins.IsInvalid) break;
                instructions++;
                if (ins.Mnemonic is Mnemonic.Call or Mnemonic.Jmp && ins.Op0Kind == OpKind.NearBranch64)
                {
                    ulong target = ins.NearBranchTarget;
                    if (ins.Mnemonic == Mnemonic.Jmp && target >= fn.Start && target < fn.End) continue;
                    if (managed.Contains(target)) continue;
                    counts[target] = counts.GetValueOrDefault(target) + 1;
                    if (seen.Add(target)) callers[target] = callers.GetValueOrDefault(target) + 1;
                }
            }
        }

        Console.WriteLine($"scanned {functions} managed functions, {instructions:N0} instructions; {counts.Count} distinct non-managed call targets");
        foreach (var (target, count) in counts.OrderByDescending(kv => kv.Value).Take(top))
        {
            string name = symbols.TryGetValue(target, out List<string>? names)
                ? names[0] + (names.Count > 1 ? $" (+{names.Count - 1})" : "")
                : "?";
            string section = image.SectionAt(target)?.Name ?? "?";
            string export = image.Exports.FirstOrDefault(e => e.Value == target).Key ?? "";
            Console.WriteLine($"{count,8} calls {callers[target],7} fns  0x{target:X} [{section}] {name}{(export.Length != 0 ? "  <export " + export + ">" : "")}");
        }
        return 0;
    }
}
