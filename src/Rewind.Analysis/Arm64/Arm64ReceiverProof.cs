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

    public static bool IsUnused(NativeImage image, ulong start, ulong end, byte register = 0, Func<ulong,bool>? unaryMetadataCall = null, Func<ulong,bool>? arglessThrow = null, Func<ulong,bool>? independentCall = null)
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
                // Scalar S/D FMOV uses only the FP register file, even when its numeric
                // register indices equal the tracked general register. Preserve the move.
                // GP/FP transfers, half precision and all other SIMD operations remain unproved.
                case A64Op.FMov when i.FpSize is 4 or 8 && (i.Word & 0xff3ffc00u) == 0x1e204000u:
                    break;
                // These operations exclusively read/write scalar FP registers
                // (and possibly NZCV), never the incoming general register.
                case A64Op.Movi or A64Op.FMovImm or A64Op.FAbs or A64Op.FNeg or A64Op.FSqrt or A64Op.FCvt or A64Op.FRint or
                    A64Op.FAdd or A64Op.FSub or A64Op.FMul or A64Op.FDiv or A64Op.FMax or A64Op.FMin or
                    A64Op.FMaxNm or A64Op.FMinNm or A64Op.FNMul or A64Op.FMAdd or A64Op.FMSub or
                    A64Op.FNMAdd or A64Op.FNMSub or A64Op.FCmp or A64Op.FCmpe or A64Op.FCcmp or
                    A64Op.FCcmpe or A64Op.FCsel:
                    break;
                case A64Op.FMovFromGp or A64Op.FMovFromGpHigh or A64Op.Scvtf or A64Op.Ucvtf:
                    if (i.Rn == register) return false;
                    break;
                case A64Op.FMovToGp or A64Op.FMovToGpHigh or A64Op.FCvtToInt:
                    kill = i.Rd == register;
                    break;
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
                case A64Op.Bl:
                    // An exactly identified argumentless nonreturning throw
                    // consumes no incoming register and ends this path.
                    if(arglessThrow!=null&&arglessThrow(i.Target))continue;
                    // The callback proves this exact direct body kills its incoming x0
                    // before reading, forwarding or returning it. This is not an ABI clobber assumption.
                    if(register==0&&independentCall!=null&&independentCall(i.Target)){kill=true;break;}
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
