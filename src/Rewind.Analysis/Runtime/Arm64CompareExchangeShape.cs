using System.Buffers.Binary;
using Rewind.Binary;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// Recognize one complete ARM64 compare-exchange wrapper and the outlined
/// compiler atomic it calls. No address or game-specific signature is assumed.
/// Unknown variants are deliberately rejected.
/// </summary>
public static class Arm64CompareExchangeShape
{
    private static uint Word(ReadOnlySpan<byte> bytes, int index) =>
        BinaryPrimitives.ReadUInt32LittleEndian(bytes.Slice(index * 4, 4));

    /// <summary>Wrapper takes (location, value, comparand), returns old value.</summary>
    public static bool TryGetAtomicTarget(ReadOnlySpan<byte> body, ulong start, out ulong target)
    {
        target = 0;
        if (body.Length < 40) return false;
        // stp x30,x19,[sp,#-16]!; mov x19,x2; mov x2,x0; mov x0,x19
        // bl outlined_atomic; cmp x0,x19; dmb ish; csel x0,x19,x0,eq
        // ldp x30,x19,[sp],#16; ret
        if (Word(body,0)!=0xA9BF4FFEu || Word(body,1)!=0xAA0203F3u ||
            Word(body,2)!=0xAA0003E2u || Word(body,3)!=0xAA1303E0u ||
            Word(body,5)!=0xEB13001Fu || Word(body,6)!=0xD5033BBFu ||
            Word(body,7)!=0x9A800260u || Word(body,8)!=0xA8C14FFEu ||
            Word(body,9)!=0xD65F03C0u) return false;
        uint bl = Word(body,4);
        if ((bl & 0xFC000000u)!=0x94000000u) return false;
        // Sign extend imm26 and multiply by four; PC is the BL instruction.
        long disp = ((int)(bl << 6) >> 6) * 4L;
        target = unchecked((ulong)((long)start + 16 + disp));
        return target != start && (target & 3) == 0;
    }

    /// <summary>
    /// Complete compiler-rt outlined CAS8 acquire/release implementation.
    /// Feature flag address is the only variable part. Both control-flow paths
    /// must match, including the exclusive retry and mismatch branches.
    /// </summary>
    public static bool IsOutlinedAtomic(ReadOnlySpan<byte> body)
    {
        if (body.Length < 52) return false;
        return Word(body,0)==0xD503245Fu && // bti c
            (Word(body,1)&0x9F00001Fu)==0x90000010u && // adrp x16, feature page
            (Word(body,2)&0xFFC003FFu)==0x39400210u && // ldrb w16,[x16,#flag]
            Word(body,3)==0x34000070u && // cbz w16, exclusive path
            Word(body,4)==0xC8E0FC41u && // casal x0,x1,[x2]
            Word(body,5)==0xD65F03C0u &&
            Word(body,6)==0xAA0003F0u && // mov x16,x0 (expected)
            Word(body,7)==0xC85FFC40u && // ldaxr x0,[x2]
            Word(body,8)==0xEB10001Fu && // cmp x0,x16
            Word(body,9)==0x54000061u && // b.ne return
            Word(body,10)==0xC811FC41u && // stlxr w17,x1,[x2]
            Word(body,11)==0x35FFFF91u && // cbnz w17, retry
            Word(body,12)==0xD65F03C0u;
    }

    public static bool Matches(NativeImage image, ulong start)
    {
        if (image.Arch != CpuArch.Arm64 || image.SectionAt(start)?.IsExecutable != true ||
            !image.TrySpan(start,40,out var body) || !TryGetAtomicTarget(body,start,out ulong target) ||
            image.SectionAt(target)?.IsExecutable != true || !image.TrySpan(target,52,out var atomic)) return false;
        return IsOutlinedAtomic(atomic);
    }
}
