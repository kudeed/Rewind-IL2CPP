using Rewind.Analysis.Ir;
using Rewind.Binary;

namespace Rewind.Analysis.Recover;

/// <summary>Reads exact scalar bits from a wholly mapped immutable ARM64 ELF data section.</summary>
internal static class ImmutableImageLoad
{
    internal static bool TryRead(NativeImage image,Node load,out long bits)
    {
        bits=0;
        if(image.Arch!=CpuArch.Arm64||image.Format!=ImageFormat.Elf||image.PointerSize!=8||
           load.Op!=Op.Load||load.In.Length!=1||load.In[0].Type!=VT.I64||
           load.Type is not(VT.I8 or VT.I16 or VT.I32 or VT.I64 or VT.F32 or VT.F64)||
           !Normalizer.FlagConstant(load.In[0],out ulong address))return false;
        int bytes=load.Type.Bytes();
        if(address>ulong.MaxValue-(ulong)(bytes-1)||
           image.SectionAt(address) is not{IsWritable:false,IsExecutable:false} section||
           (section.Flags&SectionFlags.Read)==0||!section.Contains(address+(ulong)(bytes-1))||
           !image.IsMapped(address,bytes))return false;
        // Preserve the original bit pattern, including signed zero, infinities,
        // NaN payloads and packed scalar lanes. No host floating conversion.
        bits=bytes switch
        {
            1=>image.U8(address),
            2=>image.U16(address),
            4=>image.U32(address),
            8=>unchecked((long)image.U64(address)),
            _=>throw new InvalidDataException("Unsupported proven image literal width")
        };
        return true;
    }
}
