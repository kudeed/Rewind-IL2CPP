using Rewind.Binary;

namespace Rewind.Analysis.Recover;

/// <summary>Safety policy for folding a late ARM64 GOT read into a metadata-slot address.</summary>
public static class MetadataGotLoad
{
    public static bool TryResolve(NativeImage image, ulong address, Func<ulong, bool> isMetadataSlot, out ulong slot)
    {
        slot = 0;
        if (image.Arch != CpuArch.Arm64 || image.Format != ImageFormat.Elf || image.PointerSize != 8 ||
            (address & 7) != 0 || address > ulong.MaxValue - 7 ||
            image.SectionAt(address) is not { IsExecutable: false } section ||
            !section.Contains(address + 7) || !image.IsMapped(address, 8) ||
            !image.IsReadOnlyAfterLoad(address) || !image.IsReadOnlyAfterLoad(address + 7)) return false;
        ulong candidate = image.Ptr(address);
        if ((candidate & 7) != 0 || !isMetadataSlot(candidate)) return false;
        slot = candidate;
        return true;
    }
}
