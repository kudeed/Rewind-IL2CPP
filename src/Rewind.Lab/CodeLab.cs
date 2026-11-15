using Iced.Intel;
using Rewind.Analysis;
using Rewind.Model;
using Decoder = Iced.Intel.Decoder;

namespace Rewind.Lab;

/// <summary>code &lt;input&gt; &lt;symbols|sig&gt; &lt;address&gt;...: annotated disassembly of native functions, for study.</summary>
internal static class CodeLab
{
    private static string Describe(ProgramAnalysis program, ulong address)
    {
        CallTarget target = program.Resolve(address);
        if (target.Helper != null) return $"helper {target.Helper.Kind} ({target.Helper.Name})";
        if (target.Methods.Count != 0) return "method " + target.Methods[0].FullName + (target.Methods.Count > 1 ? $" (+{target.Methods.Count - 1})" : "");
        if (target.Insts.Count != 0) return "method " + target.Insts[0] + (target.Insts.Count > 1 ? $" (+{target.Insts.Count - 1})" : "");
        if (program.Model.ResolveUsageSlot(address) is { } usage) return usage.ToString() ?? "";
        if (program.Defaults.Slots.TryGetValue(address, out var slot)) return "default " + slot;
        Rewind.Binary.ImageSection? section = program.Model.Image.SectionAt(address);
        if (section is { IsExecutable: false } && program.Model.Image.TryCString(address, 80) is { Length: > 3 } text && text.All(c => c >= 32 && c < 127))
            return $"\"{text}\"";
        return section == null ? "" : $"[{section.Name}]";
    }

    /// <summary>nearest &lt;input&gt; &lt;symbols|sig&gt; &lt;address&gt;...: listed methods whose code is most like the function's.</summary>
    public static int Nearest(Il2CppModel model, string symbolsPath, string[] addresses)
    {
        ProgramAnalysis program = LiftLab.MakeProgram(model, symbolsPath);
        var listed = new List<(ulong Address, Rewind.Analysis.Runtime.FunctionCode Code)>();
        foreach (ulong start in program.Context.FunctionStarts)
            if (program.Context.IsManaged(start) && program.Code.Get(start) is { } code)
                listed.Add((start, code));
        foreach (string text in addresses)
        {
            ulong address = Convert.ToUInt64(text.StartsWith("0x", StringComparison.OrdinalIgnoreCase) ? text[2..] : text, 16);
            if (program.Code.Get(address) is not { } query) { Console.WriteLine($"=== 0x{address:X}: no code"); continue; }
            Console.WriteLine($"=== 0x{address:X} {query.Instructions} instructions, {query.Callees.Count} callees");
            foreach (var (a, code) in listed
                         .Where(l => l.Code.Instructions * 2 >= query.Instructions && l.Code.Instructions <= query.Instructions * 2)
                         .Select(l => (l.Address, Score: Rewind.Analysis.Runtime.CodeIndex.Similarity(query.Sketch, l.Code.Sketch), l.Code))
                         .OrderByDescending(l => l.Score).Take(5).Select(l => (l.Address, l.Code)))
                Console.WriteLine($"    {Rewind.Analysis.Runtime.CodeIndex.Similarity(query.Sketch, code.Sketch):F2}  0x{a:X}  {code.Instructions} instr  {Describe(program, a)}");
        }
        return 0;
    }

    public static int Run(Il2CppModel model, string symbolsPath, string[] addresses)
    {
        ProgramAnalysis program = LiftLab.MakeProgram(model, symbolsPath);
        var formatter = new IntelFormatter();
        formatter.Options.RipRelativeAddresses = false;
        formatter.Options.HexPrefix = "0x";
        formatter.Options.HexSuffix = "";
        formatter.Options.SpaceAfterOperandSeparator = true;
        foreach (string text in addresses)
        {
            ulong start = text.Contains("::", StringComparison.Ordinal)
                ? model.Methods.FirstOrDefault(m => m.Address != 0 && m.FullName.Contains(text, StringComparison.Ordinal))?.Address ?? 0
                : Convert.ToUInt64(text.StartsWith("0x", StringComparison.OrdinalIgnoreCase) ? text[2..] : text, 16);
            if (start == 0) { Console.WriteLine($"=== {text}: not found"); continue; }
            // The function runs to the next function start (unwind entries may cover only its first part).
            ulong end = 0;
            foreach (ulong next in program.Context.FunctionStarts)
                if (next > start && (end == 0 || next < end))
                    end = next;
            if (end - start > 4000) end = start + 4000;
            Console.WriteLine($"=== 0x{start:X} {Describe(program, start)}");
            ReadOnlySpan<byte> bytes = model.Image.SpanToSectionEnd(start);
            int length = (int)Math.Min((ulong)bytes.Length, end > start ? end - start : 400);
            var reader = new ByteArrayCodeReader(bytes[..length].ToArray());
            var decoder = Decoder.Create(64, reader, start);
            var output = new StringOutput();
            int count = 0;
            while (decoder.IP < start + (ulong)length && count++ < 400)
            {
                Instruction ins = decoder.Decode();
                if (ins.IsInvalid) break;
                formatter.Format(ins, output);
                string line = output.ToStringAndReset();
                string note = "";
                if (ins.FlowControl is FlowControl.Call or FlowControl.UnconditionalBranch && ins.Op0Kind == OpKind.NearBranch64)
                {
                    ulong t = ins.NearBranchTarget;
                    if (t < start || t >= start + (ulong)length) note = Describe(program, t);
                }
                else if (ins.IsIPRelativeMemoryOperand) note = Describe(program, ins.IPRelativeMemoryAddress);
                Console.WriteLine($"  {ins.IP:X}  {line,-52} {(note.Length != 0 ? "; " + note : "")}");
                if (end == 0 && ins.FlowControl is FlowControl.Return or FlowControl.Interrupt) break;
            }
        }
        return 0;
    }
}
