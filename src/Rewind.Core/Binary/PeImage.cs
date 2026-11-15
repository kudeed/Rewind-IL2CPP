using Rewind.IO;

namespace Rewind.Binary;

/// <summary>Windows PE / PE32+ image (GameAssembly.dll).</summary>
public sealed class PeImage : NativeImage
{
    public override ImageFormat Format => ImageFormat.PE;

    /// <summary>Raw x64 RUNTIME_FUNCTION entries; <see cref="NativeImage.FunctionTable"/> mirrors them.</summary>
    public ulong ExceptionDirectoryVa { get; private set; }
    public int ExceptionDirectorySize { get; private set; }

    public PeImage(byte[] file, string path)
    {
        FilePath = path;
        Os = TargetOs.Windows;
        var f = new ByteBlock(file);

        int pe = f.I32(0x3C);
        if (!f.InRange(pe, 24) || f.U32(pe) != 0x00004550)
            throw new InvalidDataException("Missing PE signature");

        ushort machine = f.U16(pe + 4);
        int sectionCount = f.U16(pe + 6);
        int optSize = f.U16(pe + 20);
        int opt = pe + 24;
        ushort magic = f.U16(opt);
        bool plus = magic == 0x20B;
        if (!plus && magic != 0x10B) throw new InvalidDataException($"Unknown optional header magic 0x{magic:X}");

        Arch = machine switch
        {
            0x8664 => CpuArch.X64,
            0x014C => CpuArch.X86,
            0xAA64 => CpuArch.Arm64,
            0x01C0 or 0x01C2 or 0x01C4 => CpuArch.Arm32,
            _ => throw new NotSupportedException($"Unsupported PE machine 0x{machine:X4}"),
        };
        PointerSize = plus ? 8 : 4;
        ImageBase = plus ? f.U64(opt + 24) : f.U32(opt + 28);
        uint sizeOfImage = f.U32(opt + 56);
        uint sizeOfHeaders = f.U32(opt + 60);
        int dirCount = (int)f.U32(opt + (plus ? 108 : 92));
        int dirs = opt + (plus ? 112 : 96);

        MemoryBase = ImageBase;
        Memory = new byte[sizeOfImage];
        Array.Copy(file, 0, Memory, 0, Math.Min(Math.Min(sizeOfHeaders, sizeOfImage), (uint)file.Length));

        int sectionTable = opt + optSize;
        for (int i = 0; i < sectionCount; i++)
        {
            int s = sectionTable + i * 40;
            string name = f.FixedAscii(s, 8);
            uint virtualSize = f.U32(s + 8);
            uint rva = f.U32(s + 12);
            uint rawSize = f.U32(s + 16);
            uint rawPtr = f.U32(s + 20);
            uint characteristics = f.U32(s + 36);

            uint size = virtualSize != 0 ? virtualSize : rawSize;
            uint copy = Math.Min(rawSize, size);
            if (rawPtr != 0 && copy != 0 && rva < sizeOfImage)
            {
                copy = (uint)Math.Min(copy, Math.Min(sizeOfImage - rva, (uint)Math.Max(0, file.Length - rawPtr)));
                Array.Copy(file, rawPtr, Memory, rva, copy);
            }

            var flags = SectionFlags.None;
            if ((characteristics & 0x40000000) != 0) flags |= SectionFlags.Read;
            if ((characteristics & 0x80000000) != 0) flags |= SectionFlags.Write;
            if ((characteristics & 0x20000000) != 0) flags |= SectionFlags.Execute;
            if (rawSize == 0) flags |= SectionFlags.ZeroFill;
            Sections.Add(new ImageSection(name, ImageBase + rva, size, flags));
        }

        (uint Rva, uint Size) Dir(int index) =>
            index < dirCount ? (f.U32(dirs + index * 8), f.U32(dirs + index * 8 + 4)) : (0u, 0u);

        ReadExports(Dir(0));
        ReadImports(Dir(1), plus);
        ReadExceptionTable(Dir(3));
    }

    private void ReadExports((uint Rva, uint Size) dir)
    {
        if (dir.Rva == 0 || dir.Size < 40) return;
        ulong d = ImageBase + dir.Rva;
        if (!IsMapped(d, 40)) return;
        uint nameCount = U32(d + 24);
        ulong functions = ImageBase + U32(d + 28);
        ulong names = ImageBase + U32(d + 32);
        ulong ordinals = ImageBase + U32(d + 36);
        uint functionCount = U32(d + 20);
        for (uint i = 0; i < nameCount; i++)
        {
            if (!IsMapped(names + i * 4, 4) || !IsMapped(ordinals + i * 2, 2)) break;
            string? name = TryCString(ImageBase + U32(names + i * 4));
            ushort ordinal = U16(ordinals + i * 2);
            if (name == null || ordinal >= functionCount || !IsMapped(functions + (ulong)ordinal * 4, 4)) continue;
            uint rva = U32(functions + (ulong)ordinal * 4);
            // Forwarders point back inside the export directory and are not code.
            if (rva >= dir.Rva && rva < dir.Rva + dir.Size) continue;
            Exports[name] = ImageBase + rva;
        }
    }

    private void ReadImports((uint Rva, uint Size) dir, bool plus)
    {
        if (dir.Rva == 0) return;
        ulong d = ImageBase + dir.Rva;
        for (; IsMapped(d, 20); d += 20)
        {
            uint lookupRva = U32(d);
            uint nameRva = U32(d + 12);
            uint thunkRva = U32(d + 16);
            if (nameRva == 0 && thunkRva == 0) break;
            string dll = TryCString(ImageBase + nameRva) ?? "?";
            ulong lookup = ImageBase + (lookupRva != 0 ? lookupRva : thunkRva);
            ulong thunk = ImageBase + thunkRva;
            int step = plus ? 8 : 4;
            for (int i = 0; IsMapped(lookup + (ulong)(i * step), step); i++)
            {
                ulong entry = plus ? U64(lookup + (ulong)(i * step)) : U32(lookup + (ulong)(i * step));
                if (entry == 0) break;
                bool byOrdinal = plus ? (entry >> 63) != 0 : (entry >> 31) != 0;
                string symbol = byOrdinal
                    ? $"#{entry & 0xFFFF}"
                    : TryCString(ImageBase + (entry & 0x7FFFFFFF) + 2) ?? "?";
                ImportSlots[thunk + (ulong)(i * step)] = dll + "!" + symbol;
            }
        }
    }

    private void ReadExceptionTable((uint Rva, uint Size) dir)
    {
        if (dir.Rva == 0 || dir.Size == 0) return;
        ExceptionDirectoryVa = ImageBase + dir.Rva;
        ExceptionDirectorySize = (int)dir.Size;
        if (Arch != CpuArch.X64) return;
        int count = (int)(dir.Size / 12);
        FunctionTable.Capacity = count;
        for (int i = 0; i < count; i++)
        {
            ulong e = ExceptionDirectoryVa + (ulong)i * 12;
            if (!IsMapped(e, 12)) break;
            uint begin = U32(e);
            uint end = U32(e + 4);
            uint unwind = U32(e + 8);
            if (begin == 0 && end == 0) continue;
            // UNWIND_INFO starts with version (3 bits) and flags (5 bits); UNW_FLAG_CHAININFO (4) marks a range
            // that continues another function's unwind data.
            ulong unwindVa = ImageBase + unwind;
            bool chained = IsMapped(unwindVa) && ((U8(unwindVa) >> 3) & 4) != 0;
            FunctionTable.Add(new FunctionRange(ImageBase + begin, ImageBase + end, unwindVa, chained));
        }
        FunctionTable.Sort((a, b) => a.Start.CompareTo(b.Start));
    }
}
