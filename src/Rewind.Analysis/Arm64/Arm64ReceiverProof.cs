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
    // The IR call must still be backed by the exact direct ARM64
    // transfer. Never infer receiver independence for indirect calls,
    // thunk aliases, or a synthetic IR node at an unrelated address.
    public static bool ExactDirectTransfer(NativeImage image,ulong pc,ulong target,bool tail)
    {
        if(image.Arch!=CpuArch.Arm64||pc==0||target==0||(pc&3)!=0||(target&3)!=0||
            !image.IsMapped(pc,4)||!image.IsMapped(target,4)||
            image.SectionAt(pc) is not {IsExecutable:true}||
            image.SectionAt(target) is not {IsExecutable:true})return false;
        var ins=A64Decoder.Decode(image.U32(pc),pc);
        return ins.Op==(tail?A64Op.B:A64Op.Bl)&&ins.Target==target;
    }

    // Exact repeated direct call with a bit-zero test on its boolean return.
    // The second call's incoming x0 is the first call's result, not this.
    public static bool RepeatedBooleanCall(NativeImage image, ulong pc, ulong target)
    {
        if(image.Arch!=CpuArch.Arm64||pc<8||!image.IsMapped(pc-8,12)||
           image.SectionAt(pc-8) is not {IsExecutable:true} section||pc+4>section.End)return false;
        uint word=image.U32(pc-4);
        if((word&0xfff8001fu) is not (0x36000000u or 0x37000000u))return false;
        var first=A64Decoder.Decode(image.U32(pc-8),pc-8);
        var test=A64Decoder.Decode(word,pc-4);
        var second=A64Decoder.Decode(image.U32(pc),pc);
        return first.Op==A64Op.Bl&&first.Target==target&&second.Op==A64Op.Bl&&second.Target==target&&
            test.Op is A64Op.Tbz or A64Op.Tbnz&&test.Target>=pc+4&&test.Target<section.End;
    }

    // Exact epilogue with restored x20/x19, one x1 load from x8,
    // restored LR/x21 and a direct B. No write/read of stale x0.
    public static bool DirectRestoredTail(NativeImage image,ulong pc,ulong target)
    {
        if(image.Arch!=CpuArch.Arm64||pc<12||!image.IsMapped(pc-12,16)||
           image.SectionAt(pc-12) is not {IsExecutable:true} section||pc+4>section.End)return false;
        return image.U32(pc-12)==0xa9414ff4u&&
               image.U32(pc-8)==0xf9400101u&&
               image.U32(pc-4)==0xa8c257feu&&
               A64Decoder.Decode(image.U32(pc),pc) is {Op:A64Op.B,Target:var dest}&&dest==target;
    }

    // An entry null-checks the first managed reference argument before
    // copying it into x0. The only path that skips the overwrite must
    // reach an identified argumentless null-reference throw directly.
    public static bool GuardedFirstArgument(NativeImage image, ulong start, ulong end, Func<ulong,bool> arglessThrow)
    {
        if(image.Arch!=CpuArch.Arm64||start>=end||end-start<20||
           !image.IsMapped(start,16)||image.SectionAt(start) is not {IsExecutable:true} section||end>section.End)return false;
        if(image.U32(start)!=0xf81e0ffeu||image.U32(start+4)!=0xa9014ff4u||
           image.U32(start+12)!=0xaa0103e0u)return false;
        uint word=image.U32(start+8);
        if((word&0xff00001fu)!=0xb4000001u)return false;
        var guard=A64Decoder.Decode(word,start+8);
        if(guard.Op!=A64Op.Cbz||guard.Target<start+16||guard.Target+4>end||!image.IsMapped(guard.Target,4))return false;
        var fail=A64Decoder.Decode(image.U32(guard.Target),guard.Target);
        return fail.Op==A64Op.Bl&&arglessThrow(fail.Target)&&
            IsUnused(image,start,end,arglessThrow:arglessThrow);
    }

    /// <summary>
    /// Whether an AAPCS64 method uses x8 as its hidden aggregate result buffer.
    /// The compiler normally preserves that incoming pointer in x19-x28 or
    /// stores through x8 before its first call. Restricting the proof to the
    /// entry block avoids mistaking a later scratch use of x8 for an sret buffer.
    /// </summary>
    public static bool HasIndirectReturnBuffer(NativeImage image, ulong start, ulong end)
    {
        if (image.Arch != Rewind.Binary.CpuArch.Arm64 || end <= start ||
            !image.IsMapped(start, 4) || image.SectionAt(start) is not { IsExecutable: true }) return false;
        int count = (int)Math.Min(64UL, (end - start) / 4);
        for (int n = 0; n < count; n++)
        {
            ulong pc = start + (ulong)n * 4;
            if (!image.IsMapped(pc, 4)) return false;
            A64Instruction i = A64Decoder.Decode(image.U32(pc), pc);
            if (i.Op is A64Op.Bl or A64Op.Blr or A64Op.Ret) return false;
            if (i.Op == A64Op.Orr && i.Rm == 8 && i.Rd is >= 19 and <= 28) return true;
            if (i.Op is A64Op.Ldr or A64Op.Str or A64Op.Ldp or A64Op.Stp && i.Rn == 8) return true;
            if (i.Op == A64Op.AddImm && i.Rn == 8 && i.Rd is >= 19 and <= 28) return true;
        }
        return false;
    }

    public static bool IsUnused(NativeImage image, ulong start, ulong end, byte register = 0, Func<ulong,bool>? unaryMetadataCall = null, Func<ulong,bool>? arglessThrow = null, bool allowVoidReturn = false, bool allowIndirectStructReturn = false)
    {
        if (register > 7 || image.Arch != CpuArch.Arm64 || start >= end || (start & 3) != 0 || (end & 3) != 0 ||
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
                    kill = i.Rd == register; break;
                case A64Op.MovK:
                    if (i.Rd == register) return false;
                    break;
                case A64Op.AddImm or A64Op.SubImm or A64Op.AndImm or A64Op.OrrImm or A64Op.EorImm:
                    if (i.Rn == register) return false;
                    kill = i.Rd == register; break;
                case A64Op.AddReg or A64Op.SubReg or A64Op.AddExt or A64Op.SubExt or
                    A64Op.And or A64Op.Bic or A64Op.Orr or A64Op.Orn or A64Op.Eor or A64Op.Eon:
                    if (i.Rn == register || i.Rm == register) return false;
                    kill = i.Rd == register; break;
                case A64Op.Ldr or A64Op.Ldp or A64Op.Str or A64Op.Stp:
                    if (i.Rn == register || i.Mode == A64Mode.RegOffset && i.Rm == register) return false;
                    if (!i.Vector)
                    {
                        bool touches = i.Rd == register || i.Op is A64Op.Ldp or A64Op.Stp && i.Ra == register;
                        if (i.Op is A64Op.Str or A64Op.Stp && touches) return false;
                        kill = i.Op is A64Op.Ldr or A64Op.Ldp && touches;
                    }
                    break;
                case A64Op.LdrLit:
                    kill = !i.Vector && i.Rd == register; break;
                // These decoded scalar bitfields do not read the old Rd.
                case A64Op.Ubfm or A64Op.Sbfm:
                    if (i.Rn == register) return false;
                    kill = i.Rd == register; break;
                // GP -> SIMD copies/conversions read Rn, never GP Rd.
                // SIMD register numbers overlap GP numbers; treating a vector
                // destination as a GP write would falsely prove a kill.
                case A64Op.DupGp or A64Op.InsGp or A64Op.FMovFromGp or A64Op.FMovFromGpHigh or
                     A64Op.Scvtf or A64Op.Ucvtf:
                    if (i.Rn == register) return false;
                    break;
                // SIMD -> GP copies/conversions overwrite Rd; Rn is a SIMD register.
                case A64Op.Umov or A64Op.Smov or A64Op.FMovToGp or A64Op.FMovToGpHigh or A64Op.FCvtToInt:
                    kill = i.Rd == register; break;
                case A64Op.Ret:
                    // Void methods and AAPCS64 indirect aggregate returns do not
                    // return through x0. For the latter, the hidden result buffer
                    // is x8; x0 may remain stale provided no path reads it.
                    // Only ordinary RET x30 is a receiver-independent exit.
                    if (register==0 && (allowVoidReturn || allowIndirectStructReturn) && image.U32(pc)==0xd65f03c0u) continue;
                    return false;
                case A64Op.Bl:
                    // An exactly identified argumentless nonreturning throw
                    // consumes no incoming register and ends this path.
                    if(arglessThrow!=null&&arglessThrow(i.Target))continue;
                    // For a separately proven unary metadata service only, continue
                    // until the incoming argument register is explicitly overwritten.
                    // Do not rely on caller-saved registers being clobbered.
                    if (register < 2 || unaryMetadataCall == null || !unaryMetadataCall(i.Target)) return false;
                    break;
                case A64Op.B:
                    if (i.Target <= pc || i.Target >= end) return false;
                    pending.Push(i.Target);
                    continue;
                case A64Op.Cbz or A64Op.Cbnz or A64Op.Tbz or A64Op.Tbnz:
                    if (i.Rd == register) return false;
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
