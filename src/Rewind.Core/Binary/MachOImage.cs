using System.Buffers.Binary;
using Rewind.IO;

namespace Rewind.Binary;

/// <summary>
/// 64-bit Mach-O image (UnityFramework, GameAssembly.dylib), including the arm64/x86_64 slice of a fat binary.
/// Chained fixups (the iOS 15+ pointer encoding) are resolved so data pointers read as plain addresses.
/// NOTE: no Apple build target is installed on the development machine, so this loader is written from the
/// format documentation and has not been exercised against a real Unity build.
/// </summary>
public sealed class MachOImage : NativeImage
{
    public override ImageFormat Format => ImageFormat.MachO;

    private const uint LC_SEGMENT_64 = 0x19, LC_SYMTAB = 0x2, LC_BUILD_VERSION = 0x32, LC_VERSION_MIN_IPHONEOS = 0x25;
    private const uint LC_DYLD_CHAINED_FIXUPS = 0x80000034, LC_FUNCTION_STARTS = 0x26;

    public int FixupsApplied { get; private set; }

    public MachOImage(byte[] file, string path)
    {
        FilePath = path;
        int sliceOffset = 0, sliceSize = file.Length;
        uint magic = BinaryPrimitives.ReadUInt32LittleEndian(file);
        if (magic is 0xBEBAFECA or 0xBFBAFECA)
            (sliceOffset, sliceSize) = PickFatSlice(file, magic == 0xBFBAFECA);

        var f = new ByteBlock(file);
        int b = sliceOffset;
        if (f.U32(b) != 0xFEEDFACF) throw new NotSupportedException("Only 64-bit Mach-O images are supported");
        uint cpu = f.U32(b + 4);
        Arch = cpu switch
        {
            0x0100000C => CpuArch.Arm64,
            0x01000007 => CpuArch.X64,
            _ => throw new NotSupportedException($"Unsupported Mach-O cpu type 0x{cpu:X}"),
        };
        PointerSize = 8;
        Os = Arch == CpuArch.Arm64 ? TargetOs.IOS : TargetOs.MacOS;
        int ncmds = (int)f.U32(b + 16);

        var segments = new List<(string Name, ulong Vm, ulong VmSize, ulong FileOff, ulong FileSize, uint Prot, int Cmd)>();
        (int Off, int Size) chained = default, functionStarts = default;
        (int SymOff, int NSyms, int StrOff, int StrSize) symtab = default;

        int c = b + 32;
        for (int i = 0; i < ncmds && f.InRange(c, 8); i++)
        {
            uint cmd = f.U32(c);
            int size = (int)f.U32(c + 4);
            if (size < 8) break;
            switch (cmd)
            {
                case LC_SEGMENT_64:
                    segments.Add((f.FixedAscii(c + 8, 16), f.U64(c + 24), f.U64(c + 32), f.U64(c + 40), f.U64(c + 48),
                        f.U32(c + 60), c));
                    break;
                case LC_SYMTAB:
                    symtab = ((int)f.U32(c + 8), (int)f.U32(c + 12), (int)f.U32(c + 16), (int)f.U32(c + 20));
                    break;
                case LC_DYLD_CHAINED_FIXUPS:
                    chained = ((int)f.U32(c + 8), (int)f.U32(c + 12));
                    break;
                case LC_FUNCTION_STARTS:
                    functionStarts = ((int)f.U32(c + 8), (int)f.U32(c + 12));
                    break;
                case LC_BUILD_VERSION:
                    Os = f.U32(c + 8) == 1 ? TargetOs.MacOS : TargetOs.IOS;
                    break;
                case LC_VERSION_MIN_IPHONEOS:
                    Os = TargetOs.IOS;
                    break;
            }
            c += size;
        }

        ulong lo = ulong.MaxValue, hi = 0, textVm = 0;
        foreach (var s in segments)
        {
            if (s.Name == "__PAGEZERO" || s.VmSize == 0) continue;
            lo = Math.Min(lo, s.Vm);
            hi = Math.Max(hi, s.Vm + s.VmSize);
            if (s.Name == "__TEXT") textVm = s.Vm;
        }
        if (lo == ulong.MaxValue) throw new InvalidDataException("Mach-O has no segments");
        if (hi - lo > int.MaxValue) throw new NotSupportedException("Mach-O image larger than 2 GB");

        ImageBase = textVm;
        MemoryBase = lo;
        Memory = new byte[(int)(hi - lo)];
        foreach (var s in segments)
        {
            if (s.Name == "__PAGEZERO") continue;
            ulong n = Math.Min(s.FileSize, s.VmSize);
            long src = sliceOffset + (long)s.FileOff;
            if (n != 0 && src < file.Length)
                Array.Copy(file, src, Memory, (long)(s.Vm - lo), (long)Math.Min(n, (ulong)(file.Length - src)));

            int nsects = (int)f.U32(s.Cmd + 64);
            for (int k = 0; k < nsects; k++)
            {
                int sh = s.Cmd + 72 + k * 80;
                string sect = f.FixedAscii(sh, 16);
                ulong addr = f.U64(sh + 32), size = f.U64(sh + 40);
                uint type = f.U32(sh + 64) & 0xFF;
                if (size == 0) continue;
                var flags = SectionFlags.None;
                if ((s.Prot & 1) != 0) flags |= SectionFlags.Read;
                if ((s.Prot & 2) != 0) flags |= SectionFlags.Write;
                if ((s.Prot & 4) != 0 && s.Name == "__TEXT" && sect is "__text" or "il2cpp" or "__stubs")
                    flags |= SectionFlags.Execute;
                if (type is 1 or 12) flags |= SectionFlags.ZeroFill; // S_ZEROFILL, S_GB_ZEROFILL
                Sections.Add(new ImageSection(s.Name + "," + sect, addr, size, flags));
            }
        }

        if (chained.Size != 0) ApplyChainedFixups(f, sliceOffset + chained.Off, segments.Select(s => s.Vm).ToList());
        ReadSymbols(f, sliceOffset, symtab);
        ReadFunctionStarts(f, sliceOffset + functionStarts.Off, functionStarts.Size);
    }

    private static (int Offset, int Size) PickFatSlice(byte[] file, bool fat64)
    {
        int count = (int)BinaryPrimitives.ReadUInt32BigEndian(file.AsSpan(4));
        int entry = fat64 ? 32 : 20;
        (int, int) best = default;
        int bestRank = -1;
        for (int i = 0; i < count; i++)
        {
            ReadOnlySpan<byte> e = file.AsSpan(8 + i * entry, entry);
            uint cpu = BinaryPrimitives.ReadUInt32BigEndian(e);
            long off = fat64 ? (long)BinaryPrimitives.ReadUInt64BigEndian(e[8..]) : BinaryPrimitives.ReadUInt32BigEndian(e[8..]);
            long size = fat64 ? (long)BinaryPrimitives.ReadUInt64BigEndian(e[16..]) : BinaryPrimitives.ReadUInt32BigEndian(e[12..]);
            int rank = cpu == 0x0100000C ? 2 : cpu == 0x01000007 ? 1 : 0;
            if (rank > bestRank)
            {
                bestRank = rank;
                best = ((int)off, (int)size);
            }
        }
        if (bestRank <= 0) throw new NotSupportedException("Fat Mach-O has no 64-bit slice");
        return best;
    }

    private void ApplyChainedFixups(ByteBlock f, int header, List<ulong> segmentVms)
    {
        if (!f.InRange(header, 28)) return;
        int startsOffset = header + (int)f.U32(header + 4);
        int segCount = (int)f.U32(startsOffset);
        for (int s = 0; s < segCount; s++)
        {
            uint segInfoOffset = f.U32(startsOffset + 4 + s * 4);
            if (segInfoOffset == 0) continue;
            int seg = startsOffset + (int)segInfoOffset;
            ushort pageSize = f.U16(seg + 4);
            ushort pointerFormat = f.U16(seg + 6);
            ulong segmentOffset = f.U64(seg + 8);
            ushort pageCount = f.U16(seg + 20);
            // 2 = DYLD_CHAINED_PTR_64 (absolute target), 6 = DYLD_CHAINED_PTR_64_OFFSET (image-relative target)
            if (pointerFormat is not (2 or 6)) continue;
            for (int p = 0; p < pageCount; p++)
            {
                ushort start = f.U16(seg + 22 + p * 2);
                if (start == 0xFFFF) continue;
                ulong va = ImageBase + segmentOffset + (ulong)p * pageSize + start;
                while (IsMapped(va, 8))
                {
                    ulong raw = U64(va);
                    ulong next = (raw >> 51) & 0xFFF;
                    bool bind = (raw >> 63) != 0;
                    if (!bind)
                    {
                        ulong target = raw & 0xFFFFFFFFFUL;
                        ulong high8 = (raw >> 36) & 0xFF;
                        ulong value = (pointerFormat == 6 ? ImageBase + target : target) | (high8 << 56);
                        BinaryPrimitives.WriteUInt64LittleEndian(Memory.AsSpan((int)(va - MemoryBase), 8), value);
                        FixupsApplied++;
                    }
                    else
                    {
                        BinaryPrimitives.WriteUInt64LittleEndian(Memory.AsSpan((int)(va - MemoryBase), 8), 0);
                    }
                    if (next == 0) break;
                    va += next * 4;
                }
            }
        }
    }

    private void ReadSymbols(ByteBlock f, int slice, (int SymOff, int NSyms, int StrOff, int StrSize) t)
    {
        if (t.NSyms == 0) return;
        for (int i = 0; i < t.NSyms; i++)
        {
            long e = slice + t.SymOff + (long)i * 16;
            if (!f.InRange(e, 16)) break;
            uint strx = f.U32(e);
            byte type = f.U8(e + 4);
            ulong value = f.U64(e + 8);
            if ((type & 0xE0) != 0 || (type & 0x0E) != 0x0E || value == 0 || strx >= t.StrSize) continue; // N_SECT only
            string? name = f.Utf8Z(slice + t.StrOff + strx, 1024);
            if (string.IsNullOrEmpty(name)) continue;
            if (name[0] == '_') name = name[1..];
            Symbols.TryAdd(value, name);
            if ((type & 1) != 0) Exports[name] = value; // N_EXT
        }
    }

    private void ReadFunctionStarts(ByteBlock f, int offset, int size)
    {
        if (size == 0 || !f.InRange(offset, size)) return;
        ReadOnlySpan<byte> data = f.Span(offset, size);
        int pos = 0;
        ulong addr = ImageBase;
        var starts = new List<ulong>();
        while (pos < data.Length)
        {
            ulong delta = VarInt.ReadUleb128(data, ref pos);
            if (delta == 0) break;
            addr += delta;
            starts.Add(addr);
        }
        for (int i = 0; i < starts.Count; i++)
        {
            ulong end = i + 1 < starts.Count ? starts[i + 1] : starts[i];
            FunctionTable.Add(new FunctionRange(starts[i], end, 0));
        }
    }
}
