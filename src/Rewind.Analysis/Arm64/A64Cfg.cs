using Rewind.Analysis.X64;
using Rewind.Binary;

namespace Rewind.Analysis.Arm64;

public sealed class A64Block
{
    public ulong Start;
    public List<A64Instruction> Instructions = [];
    public BlockEnd End;
    /// <summary>Successor addresses. For Branch: [taken, fall-through]. For Switch: one per table entry.</summary>
    public List<ulong> Successors = [];
    public ulong EndAddress => Instructions.Count == 0 ? Start : Instructions[^1].NextAddress;
}

/// <summary>Decodes one A64 function by following control flow and splits it into basic blocks.</summary>
public sealed class A64Cfg
{
    public ulong Start;
    public ulong Limit;
    public List<A64Block> Blocks = [];
    public List<string> Problems = [];

    private const int MaxInstructions = 200_000;

    public static A64Cfg Build(ICodeContext context, ulong start) => Build(context, start, null);

    /// <param name="extraRoots">Addresses reached other than by the code's own control flow (landing pads).</param>
    /// <param name="extraLeaders">Addresses where a block must start even without a jump there (call-site boundaries).</param>
    /// <param name="splitAfter">Call targets after whose calls a block ends (the end of a catch handler).</param>
    public static A64Cfg Build(ICodeContext context, ulong start, IEnumerable<ulong>? extraRoots, IEnumerable<ulong>? extraLeaders = null,
        Func<ulong, bool>? splitAfter = null)
    {
        NativeImage image = context.Image;
        var cfg = new A64Cfg { Start = start };
        ImageSection? section = image.SectionAt(start);
        if (section == null || !section.IsExecutable || (start & 3) != 0)
        {
            cfg.Problems.Add($"0x{start:X} is not in an executable section");
            return cfg;
        }
        ulong limit = context.NextFunctionStart(start);
        if (limit == 0 || limit > section.End) limit = section.End;
        cfg.Limit = limit;

        var instructions = new SortedDictionary<ulong, A64Instruction>();
        var leaders = new HashSet<ulong> { start };
        var branchIslands = new HashSet<ulong>();
        var ends = new Dictionary<ulong, (BlockEnd End, List<ulong> Successors)>();
        var work = new Stack<ulong>();
        if (extraRoots != null)
            foreach (ulong root in extraRoots)
                if (root > start && root < limit)
                {
                    leaders.Add(root);
                    work.Push(root);
                }
        work.Push(start);
        if (extraLeaders != null)
            foreach (ulong leader in extraLeaders)
                if (leader > start && leader < limit)
                    leaders.Add(leader);

        bool InFunction(ulong a) => a >= start && a < limit && (a == start || !context.IsFunctionStart(a));

        // Accept only a bounded, straight-line executable island whose final direct
        // branch demonstrably rejoins this function. Calls, returns, traps and indirect
        // or conditional transfers keep the existing external-tail-call classification.
        List<ulong>? ReturningBranchIsland(ulong target)
        {
            if ((target & 3) != 0) return null;
            ImageSection? islandSection = image.SectionAt(target);
            if (islandSection == null || !islandSection.IsExecutable) return null;
            ulong islandLimit = context.NextFunctionStart(target);
            if (islandLimit == 0 || islandLimit > islandSection.End) islandLimit = islandSection.End;
            var addresses = new List<ulong>();
            for (ulong address = target; addresses.Count < 4 && address + 4 <= islandLimit; address += 4)
            {
                if (InFunction(address) || !image.TrySpan(address, 4, out _)) return null;
                A64Instruction instruction = A64Decoder.Decode(image.U32(address), address);
                addresses.Add(address);
                if (instruction.Op == A64Op.B)
                    return InFunction(instruction.Target) ? addresses : null;
                if (instruction.Op is not (A64Op.Nop or A64Op.Adr or A64Op.Adrp or
                    A64Op.Ldr or A64Op.LdrLit or A64Op.Str or A64Op.AddImm or A64Op.SubImm)) return null;
            }
            return null;
        }

        while (work.Count > 0)
        {
            ulong ip = work.Pop();
            while (true)
            {
                if (instructions.ContainsKey(ip)) break;
                if ((ip < start || ip >= limit) && !branchIslands.Contains(ip))
                {
                    cfg.Problems.Add($"control flow runs outside the function at 0x{ip:X}");
                    break;
                }
                if (instructions.Count > MaxInstructions)
                {
                    cfg.Problems.Add("function too large");
                    work.Clear();
                    break;
                }
                A64Instruction ins = A64Decoder.Decode(image.U32(ip), ip);
                instructions[ip] = ins;
                ulong next = ip + 4;
                switch (ins.Op)
                {
                    case A64Op.Invalid:
                        cfg.Problems.Add($"invalid instruction 0x{ins.Word:X8} at 0x{ip:X}");
                        ends[ip] = (BlockEnd.Trap, []);
                        goto nextBlock;
                    case A64Op.BCond or A64Op.Cbz or A64Op.Cbnz or A64Op.Tbz or A64Op.Tbnz:
                    {
                        if (ins.Op == A64Op.BCond && ins.Cond >= 14)
                        {
                            // "always": a plain jump
                            goto case A64Op.B;
                        }
                        ulong target = ins.Target;
                        if (!InFunction(target)) cfg.Problems.Add($"conditional branch leaves the function at 0x{ip:X}");
                        else
                        {
                            leaders.Add(target);
                            work.Push(target);
                        }
                        ends[ip] = (BlockEnd.Branch, [target, next]);
                        leaders.Add(next);
                        work.Push(next);
                        goto nextBlock;
                    }
                    case A64Op.B:
                    {
                        ulong target = ins.Target;
                        if (!InFunction(target) && !branchIslands.Contains(target))
                        {
                            // Linker/outline islands can branch back into the caller. Keep their
                            // instructions and register effects: this is a jump, not a call/return.
                            List<ulong>? island = ReturningBranchIsland(target);
                            if (island != null)
                            {
                                foreach (ulong address in island) branchIslands.Add(address);
                                ends[ip] = (BlockEnd.Jump, [target]);
                                leaders.Add(target);
                                work.Push(target);
                                goto nextBlock;
                            }
                            ends[ip] = (BlockEnd.TailCall, []);
                            goto nextBlock;
                        }
                        ends[ip] = (BlockEnd.Jump, [target]);
                        leaders.Add(target);
                        work.Push(target);
                        goto nextBlock;
                    }
                    case A64Op.Br:
                    {
                        List<ulong>? table = TryReadJumpTable(image, instructions, ip, start, limit);
                        if (table == null) ends[ip] = (BlockEnd.IndirectTailCall, []);
                        else
                        {
                            ends[ip] = (BlockEnd.Switch, table);
                            foreach (ulong t in table)
                            {
                                leaders.Add(t);
                                work.Push(t);
                            }
                        }
                        goto nextBlock;
                    }
                    case A64Op.Ret:
                        ends[ip] = (BlockEnd.Return, []);
                        goto nextBlock;
                    case A64Op.Brk or A64Op.Udf or A64Op.Hlt:
                        ends[ip] = (BlockEnd.Trap, []);
                        goto nextBlock;
                    case A64Op.Bl or A64Op.Blr:
                    {
                        // A call that cannot return: known as such, followed by a trap, or the last thing before
                        // the next function (nothing to return to).
                        bool noReturn = (ins.Op == A64Op.Bl && context.IsNoReturn(ins.Target)) || next >= limit ||
                                        (next < limit && A64Decoder.Decode(image.U32(next), next).Op is A64Op.Brk or A64Op.Udf);
                        if (noReturn)
                        {
                            ends[ip] = (BlockEnd.NoReturnCall, []);
                            goto nextBlock;
                        }
                        if (ins.Op == A64Op.Bl && splitAfter != null && splitAfter(ins.Target)) leaders.Add(next);
                        break;
                    }
                }
                ip = next;
                continue;

            nextBlock:
                break;
            }
        }

        A64Block? current = null;
        ulong expected = 0;
        foreach (var (address, ins) in instructions)
        {
            if (current != null && (leaders.Contains(address) || address != expected))
            {
                if (address == expected)
                {
                    current.End = BlockEnd.FallThrough;
                    current.Successors = [address];
                }
                else current.End = BlockEnd.Trap; // (only after an error)
                cfg.Blocks.Add(current);
                current = null;
            }
            current ??= new A64Block { Start = address };
            current.Instructions.Add(ins);
            expected = address + 4;
            if (ends.TryGetValue(address, out var end))
            {
                current.End = end.End;
                current.Successors = end.Successors;
                cfg.Blocks.Add(current);
                current = null;
            }
        }
        if (current != null)
        {
            current.End = BlockEnd.Trap;
            cfg.Blocks.Add(current);
        }

        int entryIndex = cfg.Blocks.FindIndex(b => b.Start == start);
        if (entryIndex > 0)
        {
            A64Block entry = cfg.Blocks[entryIndex];
            cfg.Blocks.RemoveAt(entryIndex);
            cfg.Blocks.Insert(0, entry);
        }
        return cfg;
    }

    /// <summary>
    /// Recognizes the jump tables clang writes for AArch64 and returns their targets (null when the indirect
    /// branch is not one). Entries are bytes, halfwords or words; the target is a base address plus the entry,
    /// shifted left by 2 for the compressed forms:
    /// <code>
    ///   cmp  wI, #n ; b.hi default
    ///   adrp xT, table ; add xT, xT, :lo12:table
    ///   adr  xB, base                        (compressed tables)
    ///   ldrb wE, [xT, xI]  / ldrh wE, [xT, xI, lsl #1] / ldrsw xE, [xT, xI, lsl #2]
    ///   add  xD, xB, xE, lsl #2              (or: add xD, xT, xE)
    ///   br   xD
    /// </code>
    /// </summary>
    private static List<ulong>? TryReadJumpTable(NativeImage image, SortedDictionary<ulong, A64Instruction> decoded, ulong jumpAddress, ulong start, ulong limit)
    {
        // The straight-line code before the jump, nearest first.
        var before = new List<A64Instruction>();
        ulong expect = jumpAddress - 4;
        foreach (var (address, ins) in decoded.Reverse())
        {
            if (address >= jumpAddress) continue;
            if (address != expect) break;
            before.Add(ins);
            expect -= 4;
            if (before.Count == 32) break;
        }
        A64Instruction jump = decoded[jumpAddress];

        // The last write to a register before position 'from' in 'before' (index into it), or -1.
        int Def(byte reg, int from)
        {
            for (int k = from; k < before.Count; k++)
                if (Writes(before[k], reg)) return k;
            return -1;
        }
        ulong? ConstantOf(byte reg, int from)
        {
            int k = Def(reg, from);
            if (k < 0) return null;
            A64Instruction d = before[k];
            if (d.Op is A64Op.Adr or A64Op.Adrp) return d.Target;
            if (d.Op == A64Op.AddImm && !d.SetFlags && d.Rn == reg && Def(reg, k + 1) is int p and >= 0 && before[p].Op == A64Op.Adrp)
                return before[p].Target + (ulong)d.Imm;
            if (d.Op == A64Op.AddImm && !d.SetFlags && d.Rn != reg) return ConstantOf(d.Rn, k + 1) is ulong b ? b + (ulong)d.Imm : null;
            return null;
        }

        int addAt = Def(jump.Rn, 0);
        if (addAt < 0) return null;
        A64Instruction add = before[addAt];
        byte baseReg, entryReg;
        int shift;
        if (add.Op == A64Op.AddReg && !add.SetFlags && add.Shift == A64Shift.Lsl)
        {
            (baseReg, entryReg, shift) = (add.Rn, add.Rm, add.Amount);
        }
        else if (add.Op == A64Op.AddExt && !add.SetFlags && add.Extend is A64Extend.Sxtw or A64Extend.Uxtw or A64Extend.Uxtx or A64Extend.Sxtx)
        {
            (baseReg, entryReg, shift) = (add.Rn, add.Rm, add.Amount);
        }
        else return null;

        int loadAt = Def(entryReg, addAt + 1);
        if (loadAt < 0) return null;
        A64Instruction load = before[loadAt];
        if (load.Op != A64Op.Ldr || load.Vector || load.Mode != A64Mode.RegOffset || load.Size > 4) return null;
        if (load.Amount != 0 && 1 << load.Amount != load.Size) return null;
        ulong? table = ConstantOf(load.Rn, loadAt + 1);
        ulong? targetBase = ConstantOf(baseReg, addAt + 1);
        if (table == null || targetBase == null) return null;
        byte indexReg = load.Rm;

        // The bound: "cmp wI, #n" followed by a branch away when above.
        int bound = -1;
        for (int k = loadAt + 1; k < before.Count; k++)
        {
            A64Instruction c = before[k];
            if (c.Op == A64Op.SubImm && c.SetFlags && c.Rd == A64Instruction.Zr && c.Rn == indexReg)
            {
                bound = (int)c.Imm + 1;
                break;
            }
            // clang copies wI to a scratch index register after the checked bound.
            // A plain 32-bit MOV also proves the high half used for addressing is zero.
            if (Writes(c, indexReg) && c.Op == A64Op.Orr && !c.Is64 && !c.SetFlags &&
                c.Rn == A64Instruction.Zr && c.Rm < 31 && c.Shift == A64Shift.Lsl && c.Amount == 0)
            {
                indexReg = c.Rm;
                continue;
            }
            if (Writes(c, indexReg)) break;
        }
        if (bound <= 0 || bound > 4096) return null;

        var targets = new List<ulong>(bound);
        for (int k = 0; k < bound; k++)
        {
            ulong slot = table.Value + (ulong)(k * load.Size);
            if (!image.IsMapped(slot, load.Size)) return null;
            long entry = load.Size switch
            {
                1 => load.Signed ? (sbyte)image.U8(slot) : image.U8(slot),
                2 => load.Signed ? (short)image.U16(slot) : image.U16(slot),
                _ => load.Signed || load.Is64 ? (int)image.U32(slot) : image.U32(slot),
            };
            if (add.Op == A64Op.AddExt && add.Extend == A64Extend.Sxtw) entry = (int)entry;
            ulong target = (ulong)((long)targetBase.Value + (entry << shift));
            if (target < start || target >= limit || (target & 3) != 0) return null;
            targets.Add(target);
        }
        return targets;
    }

    /// <summary>True when the instruction writes general register <paramref name="reg"/> (as Rd, or as a base written back).</summary>
    internal static bool Writes(in A64Instruction i, byte reg)
    {
        if (reg >= 31) return false;
        switch (i.Op)
        {
            case A64Op.St1Lane:
                return i.Mode == A64Mode.PostIndex && i.Rn == reg;
            case A64Op.Ld1Lane or A64Op.Ld1R:
                return i.Mode == A64Mode.PostIndex && i.Rn == reg;
            case A64Op.Str or A64Op.Stp or A64Op.Stlr or A64Op.Prfm or A64Op.Nop or A64Op.Barrier or A64Op.B or A64Op.BCond or A64Op.Cbz or A64Op.Cbnz
                or A64Op.Tbz or A64Op.Tbnz or A64Op.Br or A64Op.Ret or A64Op.Brk or A64Op.Udf or A64Op.Hlt or A64Op.Clrex or A64Op.Msr:
                return (i.Op is A64Op.Str or A64Op.Stp && i.Mode is A64Mode.PreIndex or A64Mode.PostIndex && i.Rn == reg);
            case A64Op.Stxr or A64Op.Stlxr or A64Op.Stxp or A64Op.Stlxp:
                return i.Ra == reg;
            case A64Op.Bl or A64Op.Blr:
                return reg is <= 18 or 30;
            case A64Op.CcmpReg or A64Op.CcmpImm or A64Op.CcmnReg or A64Op.CcmnImm or A64Op.FCmp or A64Op.FCmpe or A64Op.FCcmp or A64Op.FCcmpe:
                return false;
        }
        if (IsFpDestination(i)) return false;
        if (i.Op is A64Op.Ldr or A64Op.Ldp && i.Mode is A64Mode.PreIndex or A64Mode.PostIndex && i.Rn == reg) return true;
        if (i.Op == A64Op.Ldp && !i.Vector && i.Ra == reg) return true;
        if (i.Vector && i.Op is A64Op.Ldr or A64Op.Ldp or A64Op.LdrLit) return false;
        return i.Rd == reg;
    }

    /// <summary>Instructions whose Rd is a SIMD/FP register.</summary>
    internal static bool IsFpDestination(in A64Instruction i) => i.Op is A64Op.FMov or A64Op.FMovImm or A64Op.FMovFromGp or A64Op.FMovFromGpHigh
        or A64Op.FAbs or A64Op.FNeg or A64Op.FSqrt or A64Op.FCvt or A64Op.FRint or A64Op.FAdd or A64Op.FSub or A64Op.FMul or A64Op.FDiv
        or A64Op.FMax or A64Op.FMin or A64Op.FMaxNm or A64Op.FMinNm or A64Op.FNMul or A64Op.FMAdd or A64Op.FMSub or A64Op.FNMAdd or A64Op.FNMSub
        or A64Op.FCsel or A64Op.Scvtf or A64Op.Ucvtf or A64Op.Movi or A64Op.VMov or A64Op.Dup or A64Op.DupScalar or A64Op.DupGp or A64Op.Ins
        or A64Op.InsGp or A64Op.VAnd or A64Op.VOrr or A64Op.VEor or A64Op.VBic or A64Op.VOrImm or A64Op.VBicImm or A64Op.VFAdd or A64Op.VFSub or A64Op.VFMul or A64Op.VFDiv or A64Op.Vector
        or A64Op.VecOp or A64Op.Ld1Lane or A64Op.Ld1R;
}
