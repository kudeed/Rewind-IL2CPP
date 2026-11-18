using Rewind.Analysis.Arm64;
using Rewind.Analysis.Ir;
using Rewind.Binary;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// Functions no table lists that are a listed method compiled a second time, differently.
///
/// IL2CPP writes a second copy of small methods for inlining (the "_inline" functions); where clang does not
/// paste one in, it stays a function of its own. It is compiled from the same text as the method, but on its own:
/// registers are allocated differently, blocks laid out in another order, and the metadata it reads reached
/// through a computed address instead of the global offset table. The instructions differ, so the exact
/// comparison (<see cref="CopyMatcher"/>) does not see the copy; what it refers to does not: the same metadata
/// slots (classes, methods, strings), the same runtime functions.
///
/// A function is taken to be a method's copy when
/// <list type="bullet">
/// <item>the slots and runtime functions it refers to are, as a whole, exactly those of one listed method and of
/// no other, and enough of them to tell methods apart (two different slots, three references at least);</item>
/// <item>it is about as long (within a fifth);</item>
/// <item>it reads the same argument registers as the method. A copy the compiler made private may lose an
/// argument it never reads, which moves the ones after it to other registers; that shows here, and such a
/// function is left alone.</item>
/// </list>
/// AArch64 only: MSVC pastes these copies in or keeps them identical.
/// </summary>
public static class NearCopyFinder
{
    private sealed record Print(string Key, int Instructions, int Slots);

    public static Dictionary<ulong, List<ulong>> Find(ProgramAnalysis program)
    {
        var result = new Dictionary<ulong, List<ulong>>();
        NativeImage image = program.Model.Image;
        if (image.Arch != CpuArch.Arm64 || Environment.GetEnvironmentVariable("REWIND_NO_NEAR_COPIES") != null) return result;
        var model = program.Model;

        // The functions managed code calls that nothing names.
        var callees = new HashSet<ulong>();
        foreach (FunctionRange f in image.FunctionTable)
        {
            if (!model.MethodsByAddress.ContainsKey(f.Start) && !model.InstsByAddress.ContainsKey(f.Start)) continue;
            for (ulong at = f.Start; at + 4 <= f.End && image.IsMapped(at, 4); at += 4)
            {
                A64Instruction ins = A64Decoder.Decode(image.U32(at), at);
                // (A call, or a jump out of the function: a tail call.)
                bool call = ins.Op == A64Op.Bl || (ins.Op == A64Op.B && (ins.Target < f.Start || ins.Target >= f.End));
                if (!call || callees.Contains(ins.Target)) continue;
                if (model.MethodsByAddress.ContainsKey(ins.Target) || model.InstsByAddress.ContainsKey(ins.Target)) continue;
                CallTarget known = program.Resolve(ins.Target);
                if (known.IsManaged || known.Helper != null) continue;
                callees.Add(ins.Target);
            }
        }
        if (callees.Count == 0) return result;

        // The listed methods, by what they refer to.
        var listed = new Dictionary<string, List<(ulong Address, int Instructions)>>();
        foreach (ulong address in model.MethodsByAddress.Keys.Concat(model.InstsByAddress.Keys).Distinct())
        {
            if (Fingerprint(program, address) is not { } print) continue;
            if (!listed.TryGetValue(print.Key, out var list)) listed[print.Key] = list = [];
            list.Add((address, print.Instructions));
        }

        ulong traced = Environment.GetEnvironmentVariable("REWIND_NEAR_COPIES_TRACE") is { } t ? Convert.ToUInt64(t, 16) : 0;
        if (traced != 0)
        {
            Console.WriteLine($"near copies: 0x{traced:X} is {(callees.Contains(traced) ? "" : "not ")}a candidate; {Fingerprint(program, traced)?.Key ?? "(no fingerprint)"}");
            if (Environment.GetEnvironmentVariable("REWIND_NEAR_COPIES_OF") is { } of)
                Console.WriteLine($"near copies: method 0x{of}: {Fingerprint(program, Convert.ToUInt64(of, 16))?.Key ?? "(no fingerprint)"}");
        }
        var canonical = new Dictionary<ulong, string?>();
        string? dump = Environment.GetEnvironmentVariable("REWIND_NEAR_COPIES_DUMP");
        var rejected = dump is { Length: > 0 } ? new List<string>() : null;
        foreach (ulong callee in callees)
        {
            string? why = null;
            // (A function that refers to nothing of its own - "return Vector2.zero" - cannot be told apart from
            // every other function doing the same: Vector2.zero and RenderTexture.GetTexelOffset compile alike.)
            if (Fingerprint(program, callee) is not { } print) why = "few references";
            else if (!listed.TryGetValue(print.Key, out var same)) why = "no method refers to the same";
            else if (same.Select(s => s.Address).Distinct().Count() != 1)
            {
                // Several methods refer to the same: the ones whose lifted code is the copy's.
                if (SameCode(program, callee, same.Select(s => s.Address).Distinct().ToList(), canonical) is { Count: > 0 } equal) result[callee] = equal;
                else why = "several methods refer to the same";
            }
            else
            {
                var (method, instructions) = same[0];
                if (Math.Abs(instructions - print.Instructions) * 5 > Math.Max(instructions, print.Instructions)) why = "length differs";
                else if (!SameArguments(program, callee, method)) why = "arguments differ";
                else result[callee] = [method];
            }
            if (why != null) rejected?.Add($"{callee:X}\t-\t{why}");
        }
        // (For checking against a build's symbols: copy and method, one pair a line, then the functions left alone.)
        if (rejected != null)
            File.WriteAllLines(dump!, result.SelectMany(p => p.Value.Select(m => $"{p.Key:X}\t{m:X}")).Concat(rejected));
        return result;
    }

    /// <summary>
    /// The metadata slots and runtime functions a function refers to, sorted (block order and register choice
    /// do not matter), and how many instructions it has; null when that is too little to tell methods apart.
    /// </summary>
    private static Print? Fingerprint(ProgramAnalysis program, ulong address)
    {
        NativeImage image = program.Model.Image;
        A64Cfg cfg = A64Cfg.Build(program.Context, address);
        if (cfg.Blocks.Count == 0 || cfg.Blocks.Count > 400) return null;
        var references = new List<string>();
        var slots = new HashSet<ulong>();
        int count = 0;
        void Refer(ulong target)
        {
            ulong value = image.IsReadOnlyAfterLoad(target) ? image.U64(target) : target;
            foreach (ulong candidate in (ReadOnlySpan<ulong>)[value, target])
                if (program.Model.ResolveUsageSlot(candidate) != null || program.Defaults.Slots.ContainsKey(candidate))
                {
                    references.Add("s" + candidate.ToString("X"));
                    slots.Add(candidate);
                    return;
                }
        }
        foreach (A64Block block in cfg.Blocks)
        {
            var pages = new Dictionary<byte, ulong>();
            foreach (A64Instruction ins in block.Instructions)
            {
                if (ins.IsInvalid) return null;
                count++;
                switch (ins.Op)
                {
                    case A64Op.Adrp:
                        pages[ins.Rd] = ins.Target;
                        continue;
                    case A64Op.AddImm when !ins.SetFlags && ins.Rn < 31 && pages.TryGetValue(ins.Rn, out ulong page):
                        Refer(page + (ulong)ins.Imm);
                        break;
                    case A64Op.Ldr when !ins.Vector && ins.Mode == A64Mode.Offset && ins.Rn < 31 && pages.TryGetValue(ins.Rn, out ulong slotPage):
                        Refer(slotPage + (ulong)ins.Imm);
                        break;
                    case A64Op.LdrLit or A64Op.Adr:
                        Refer(ins.Target);
                        break;
                    case A64Op.Bl or A64Op.B when program.Helpers.At(ins.Target) is { } helper:
                        references.Add("h" + (int)helper.Kind);
                        break;
                }
                foreach (byte r in pages.Keys.ToList())
                    if (A64Cfg.Writes(ins, r)) pages.Remove(r);
            }
        }
        if (slots.Count < 2 || references.Count < 3) return null;
        references.Sort(StringComparer.Ordinal);
        return new Print(string.Join(",", references), count, slots.Count);
    }

    private const int MostAlike = 8;

    /// <summary>
    /// The listed methods among <paramref name="candidates"/> (a few at most) whose lifted code is the
    /// function's: the same values computed the same way, the same calls, the same flow.
    /// </summary>
    private static List<ulong>? SameCode(ProgramAnalysis program, ulong copy, List<ulong> candidates, Dictionary<ulong, string?> cache)
    {
        if (candidates.Count > MostAlike) return null;
        string? Of(ulong address)
        {
            if (!cache.TryGetValue(address, out string? text)) cache[address] = text = Canonical(program, address);
            return text;
        }
        if (Of(copy) is not { } mine) return null;
        var equal = new List<ulong>();
        foreach (ulong candidate in candidates)
            if (Of(candidate) == mine) equal.Add(candidate);
        return equal;
    }

    /// <summary>
    /// A function's lifted code written out the same way whatever registers and block order the compiler chose:
    /// blocks in reverse post order, values numbered as they are first met, constants by value, calls by what
    /// they call.
    /// </summary>
    private static string? Canonical(ProgramAnalysis program, ulong address)
    {
        Function fn;
        try
        {
            fn = program.NewLifter().Lift(address);
        }
        catch (Exception)
        {
            return null;
        }
        if (fn.Blocks.Count == 0 || fn.Blocks.Count > 64) return null;
        Passes.DeadCode.Run(fn);
        var cfg = new Cfg(fn);
        var blockNumber = new Dictionary<Block, int>();
        foreach (Block b in cfg.ReversePostOrder) blockNumber[b] = blockNumber.Count;
        var number = new Dictionary<Node, int>();
        var parameter = fn.Params.ToDictionary(p => p.Value, p => p.Key);
        foreach (Block b in cfg.ReversePostOrder)
        {
            foreach (Node n in b.Phis) number[n] = number.Count;
            foreach (Node n in b.Nodes) if (!n.Dead) number[n] = number.Count;
        }
        string Operand(Node n) =>
            number.TryGetValue(n, out int k) ? "n" + k
            : n.IsConst ? $"c{n.Type}:{n.Imm}"
            : parameter.TryGetValue(n, out int variable) ? "p" + variable
            : $"{n.Op}.{n.Type}.{n.Imm}";
        var sb = new System.Text.StringBuilder();
        foreach (Block b in cfg.ReversePostOrder)
        {
            sb.Append('B').Append(blockNumber[b]).Append(':');
            foreach (Node n in b.Phis) sb.Append("phi(").AppendJoin(',', n.In.Select(Operand)).Append(");");
            foreach (Node n in b.Nodes)
            {
                if (n.Dead) continue;
                sb.Append(n.Op).Append('.').Append(n.Type);
                if (n.Op is Op.Proj or Op.Idiom) sb.Append('.').Append(n.Imm);
                if (n.Aux is CallInfo call)
                {
                    if (call.Intrinsic != null) sb.Append('[').Append(call.Intrinsic).Append(']');
                    else if (!call.Indirect)
                    {
                        CallTarget target = program.Resolve(call.Target);
                        if (target.Helper is { } helper) sb.Append("[h").Append((int)helper.Kind).Append(']');
                        else if (target.Methods.Count != 0) sb.Append("[m").Append(target.Methods[0].Index).Append(']');
                        else if (target.Insts.Count != 0) sb.Append("[i").Append(target.Insts[0].Method.Index).Append(']');
                        else sb.Append("[?]"); // (an unknown function: its address says nothing)
                    }
                }
                sb.Append('(').AppendJoin(',', n.In.Select(Operand)).Append(");");
            }
            sb.Append("->").AppendJoin(',', b.Succs.Select(s => blockNumber.TryGetValue(s, out int k) ? k : -1)).Append('|');
        }
        return sb.ToString();
    }

    /// <summary>Whether the two functions read the same argument registers (integer and floating point) before writing them.</summary>
    private static bool SameArguments(ProgramAnalysis program, ulong a, ulong b)
    {
        if (ArgumentsRead(program, a) is not { } first || ArgumentsRead(program, b) is not { } second) return false;
        return first.SetEquals(second);
    }

    private static HashSet<int>? ArgumentsRead(ProgramAnalysis program, ulong address)
    {
        Function fn;
        try
        {
            fn = program.NewLifter().Lift(address);
        }
        catch (Exception)
        {
            return null;
        }
        if (fn.Blocks.Count == 0) return null;
        Passes.DeadCode.Run(fn);
        Dictionary<Node, List<Node>> uses = Passes.DeadCode.Uses(fn);
        RegisterModel regs = fn.Regs;
        var read = new HashSet<int>();
        foreach (int variable in regs.IntArgs)
            if (fn.Params.TryGetValue(variable, out Node? p) && uses.ContainsKey(p)) read.Add(variable);
        for (int v = 0; v < 8; v++)
            for (int lane = 0; lane < 2; lane++)
            {
                int variable = regs.FloatLane(v, lane);
                if (fn.Params.TryGetValue(variable, out Node? p) && uses.ContainsKey(p)) read.Add(variable);
            }
        return read;
    }
}
