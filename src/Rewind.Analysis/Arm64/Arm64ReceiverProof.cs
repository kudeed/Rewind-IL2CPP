using Rewind.Binary;

namespace Rewind.Analysis.Arm64;

/// <summary>
/// Proves that every entry path kills the incoming x0 before reading it,
/// calling another function, or leaving the body. Deliberately limited to
/// a small allowlist of ordinary prologue instructions and forward branches.
/// Unknown operations and cycles before the kill are rejected.
/// </summary>
public static class Arm64ReceiverProof
{
    public static bool IsUnused(NativeImage image, ulong start, ulong end)
    {
        if (image.Arch != CpuArch.Arm64 || start >= end || (start & 3) != 0 || (end & 3) != 0 ||
            image.SectionAt(start) is not { IsExecutable: true } section || end > section.End) return false;
        // Do not try to reason about exceptional entries for this narrow proof.
        if (image is ElfImage elf && elf.ExceptionTableOf(start) is { } table &&
            table.CallSites.Any(c => c.Catches)) return false;
        var pending = new Stack<ulong>();
        var seen = new HashSet<ulong>();
        pending.Push(start);
        while (pending.Count != 0)
        {
            ulong pc = pending.Pop();
            if (pc < start || pc >= end || (pc & 3) != 0 || !image.IsMapped(pc,4)) return false;
            if (!seen.Add(pc)) continue;
            if (seen.Count > 256) return false;
            A64Instruction i = A64Decoder.Decode(image.U32(pc),pc);
            bool kill = false;
            switch (i.Op)
            {
                case A64Op.Nop or A64Op.Barrier: break;
                case A64Op.Adr or A64Op.Adrp or A64Op.MovZ or A64Op.MovN:
                    kill = i.Rd == 0; break;
                case A64Op.MovK:
                    if (i.Rd == 0) return false;
                    break;
                case A64Op.AddImm or A64Op.SubImm or A64Op.AndImm or A64Op.OrrImm or A64Op.EorImm:
                    if (i.Rn == 0) return false;
                    kill = i.Rd == 0; break;
                case A64Op.AddReg or A64Op.SubReg or A64Op.AddExt or A64Op.SubExt or
                    A64Op.And or A64Op.Bic or A64Op.Orr or A64Op.Orn or A64Op.Eor or A64Op.Eon:
                    if (i.Rn == 0 || i.Rm == 0) return false;
                    kill = i.Rd == 0; break;
                case A64Op.Ldr or A64Op.Ldp or A64Op.Str or A64Op.Stp:
                    if (i.Rn == 0 || i.Mode == A64Mode.RegOffset && i.Rm == 0) return false;
                    if (!i.Vector)
                    {
                        bool touches = i.Rd == 0 || i.Op is A64Op.Ldp or A64Op.Stp && i.Ra == 0;
                        if (i.Op is A64Op.Str or A64Op.Stp && touches) return false;
                        kill = i.Op is A64Op.Ldr or A64Op.Ldp && touches;
                    }
                    break;
                case A64Op.LdrLit:
                    kill = !i.Vector && i.Rd == 0; break;
                case A64Op.B:
                    if (i.Target <= pc || i.Target >= end) return false;
                    pending.Push(i.Target);
                    continue;
                case A64Op.Cbz or A64Op.Cbnz or A64Op.Tbz or A64Op.Tbnz:
                    if (i.Rd == 0) return false;
                    goto case A64Op.BCond;
                case A64Op.BCond:
                    if (i.Target <= pc || i.Target >= end) return false;
                    pending.Push(i.Target);
                    break;
                // In particular, calls consume x0 and an unknown instruction
                // can read it. Neither is evidence of independence.
                default: return false;
            }
            if (!kill) pending.Push(pc+4);
        }
        return true;
    }
}
