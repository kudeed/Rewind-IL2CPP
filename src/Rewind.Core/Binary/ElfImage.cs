using System.Buffers.Binary;
using Rewind.IO;

namespace Rewind.Binary;

/// <summary>
/// ELF shared object (libil2cpp.so, GameAssembly.so). The image is laid out by PT_LOAD segments and all
/// relative relocations (REL, RELA, RELR and Android packed APS2) are applied, because position independent
/// libraries keep most data pointers as relocation addends rather than as bytes in the file.
/// </summary>
public sealed class ElfImage : NativeImage
{
    public override ImageFormat Format => ImageFormat.Elf;

    private const int PT_LOAD = 1, PT_DYNAMIC = 2;
    private const int SHT_SYMTAB = 2, SHT_NOBITS = 8, SHT_DYNSYM = 11;

    private readonly ByteBlock _file;
    private readonly bool _is64;
    private ulong _symtab, _strtab, _strsz;
    private int _syment;
    private int _dynsymCount = -1;

    public int RelocationsApplied { get; private set; }

    private readonly record struct Segment(uint Type, uint Flags, ulong Offset, ulong Vaddr, ulong FileSize, ulong MemSize);

    public ElfImage(byte[] file, string path)
    {
        FilePath = path;
        _file = new ByteBlock(file);
        var f = _file;
        if (file.Length < 0x34) throw new InvalidDataException("Truncated ELF header");
        _is64 = f.U8(4) == 2;
        if (f.U8(5) != 1) throw new NotSupportedException("Big-endian ELF is not supported");
        PointerSize = _is64 ? 8 : 4;

        ushort machine = f.U16(18);
        Arch = machine switch
        {
            3 => CpuArch.X86,
            40 => CpuArch.Arm32,
            62 => CpuArch.X64,
            183 => CpuArch.Arm64,
            _ => throw new NotSupportedException($"Unsupported ELF machine {machine}"),
        };

        ulong phoff = _is64 ? f.U64(32) : f.U32(28);
        ulong shoff = _is64 ? f.U64(40) : f.U32(32);
        int phentsize = f.U16(_is64 ? 54 : 42);
        int phnum = f.U16(_is64 ? 56 : 44);
        int shentsize = f.U16(_is64 ? 58 : 46);
        int shnum = f.U16(_is64 ? 60 : 48);
        int shstrndx = f.U16(_is64 ? 62 : 50);

        var segments = new List<Segment>();
        for (int i = 0; i < phnum; i++)
        {
            long p = (long)phoff + (long)i * phentsize;
            if (!f.InRange(p, phentsize)) break;
            segments.Add(_is64
                ? new Segment(f.U32(p), f.U32(p + 4), f.U64(p + 8), f.U64(p + 16), f.U64(p + 32), f.U64(p + 40))
                : new Segment(f.U32(p), f.U32(p + 24), f.U32(p + 4), f.U32(p + 8), f.U32(p + 16), f.U32(p + 20)));
        }

        ulong lo = ulong.MaxValue, hi = 0;
        foreach (Segment s in segments)
        {
            if (s.Type != PT_LOAD || s.MemSize == 0) continue;
            lo = Math.Min(lo, s.Vaddr);
            hi = Math.Max(hi, s.Vaddr + s.MemSize);
        }
        if (lo == ulong.MaxValue) throw new InvalidDataException("ELF has no loadable segments");
        if (hi - lo > int.MaxValue) throw new NotSupportedException("ELF image larger than 2 GB");

        ImageBase = 0;
        MemoryBase = lo & ~0xFFFUL;
        Memory = new byte[(int)(hi - MemoryBase)];
        foreach (Segment s in segments)
        {
            if (s.Type != PT_LOAD) continue;
            ulong n = Math.Min(s.FileSize, s.MemSize);
            if (n == 0 || s.Offset >= (ulong)file.Length) continue;
            n = Math.Min(n, (ulong)file.Length - s.Offset);
            Array.Copy(file, (long)s.Offset, Memory, (long)(s.Vaddr - MemoryBase), (long)n);
        }

        bool haveSections = ReadSections(shoff, shentsize, shnum, shstrndx);
        if (!haveSections) SynthesizeSections(segments);

        foreach (Segment s in segments)
            if (s.Type == PT_DYNAMIC)
                ReadDynamic(s.Vaddr, s.MemSize);

        Os = DetectOs(haveSections);
        ReadFunctionSymbols(shoff, shentsize, shnum);
        // A stripped library has no symbol table, but its unwind tables still list every function.
        if (FunctionTable.Count == 0) ReadUnwindStarts(segments);
        FunctionTable.Sort((a, b) => a.Start.CompareTo(b.Start));
    }

    // ---- unwind tables -----------------------------------------------------------------------------------------

    /// <summary>Reads one DWARF pointer encoding (the subset linkers write into .eh_frame_hdr and FDEs).</summary>
    private bool TryReadEncoded(ref ulong p, byte encoding, ulong dataBase, out ulong value)
    {
        value = 0;
        if (encoding == 0xFF) return true; // DW_EH_PE_omit
        ulong at = p;
        long raw;
        switch (encoding & 0x0F)
        {
            case 0x00 or 0x04: // absptr / udata8
                if (!IsMapped(p, 8)) return false;
                raw = (long)U64(p);
                p += 8;
                break;
            case 0x03: // udata4
                if (!IsMapped(p, 4)) return false;
                raw = U32(p);
                p += 4;
                break;
            case 0x0B: // sdata4
                if (!IsMapped(p, 4)) return false;
                raw = (int)U32(p);
                p += 4;
                break;
            case 0x0C: // sdata8
                if (!IsMapped(p, 8)) return false;
                raw = (long)U64(p);
                p += 8;
                break;
            default:
                return false;
        }
        value = (encoding & 0x70) switch
        {
            0x00 => (ulong)raw,
            0x10 => (ulong)((long)at + raw),        // pcrel
            0x30 => (ulong)((long)dataBase + raw),  // datarel
            _ => (ulong)raw,
        };
        return (encoding & 0x70) is 0x00 or 0x10 or 0x30;
    }

    private void ReadUnwindStarts(List<Segment> segments)
    {
        ulong hdr = 0;
        foreach (ImageSection s in Sections)
            if (s.Name == ".eh_frame_hdr") hdr = s.Va;
        if (hdr == 0)
            foreach (Segment s in segments)
                if (s.Type == 0x6474e550) hdr = s.Vaddr; // PT_GNU_EH_FRAME
        if (hdr == 0 || !IsMapped(hdr, 4) || U8(hdr) != 1) return;
        byte framePointerEncoding = U8(hdr + 1), countEncoding = U8(hdr + 2), tableEncoding = U8(hdr + 3);
        ulong p = hdr + 4;
        if (!TryReadEncoded(ref p, framePointerEncoding, hdr, out _)) return;
        if (!TryReadEncoded(ref p, countEncoding, hdr, out ulong count) || count == 0 || count > 10_000_000) return;
        if (tableEncoding != 0x3B) return; // datarel | sdata4: what every linker writes for the search table

        var ranges = new List<FunctionRange>((int)count);
        for (ulong i = 0; i < count && IsMapped(p, 8); i++, p += 8)
        {
            ulong start = (ulong)((long)hdr + (int)U32(p));
            ulong fde = (ulong)((long)hdr + (int)U32(p + 4));
            // The FDE repeats the start (pc-relative, 4 bytes, in practice) and gives the length.
            ulong end = 0;
            if (IsMapped(fde, 16) && U32(fde) != 0xFFFFFFFF)
            {
                ulong begin = (ulong)((long)(fde + 8) + (int)U32(fde + 8));
                if (begin == start) end = start + U32(fde + 12);
            }
            ranges.Add(new FunctionRange(start, end > start ? end : start, 0));
        }
        ranges.Sort((a, b) => a.Start.CompareTo(b.Start));
        for (int i = 0; i < ranges.Count; i++)
        {
            FunctionRange r = ranges[i];
            if (i > 0 && ranges[i - 1].Start == r.Start) continue;
            // No length known: up to the next function.
            if (r.End == r.Start) r = r with { End = i + 1 < ranges.Count ? ranges[i + 1].Start : r.Start + 4 };
            FunctionTable.Add(r);
        }
    }

    private TargetOs DetectOs(bool haveSections)
    {
        foreach (ImageSection s in Sections)
            if (s.Name is ".note.android.ident")
                return TargetOs.Android;
        foreach (string import in ImportSlots.Values)
            if (import.StartsWith("__android_log", StringComparison.Ordinal))
                return TargetOs.Android;
        // Unity only ships 32/64-bit ARM ELF binaries for Android; x86/x64 ELF may be Linux or Android.
        if (Arch is CpuArch.Arm64 or CpuArch.Arm32) return TargetOs.Android;
        return TargetOs.Linux;
    }

    private bool ReadSections(ulong shoff, int shentsize, int shnum, int shstrndx)
    {
        var f = _file;
        if (shoff == 0 || shnum == 0 || shstrndx >= shnum) return false;
        if (!f.InRange((long)shoff, (long)shnum * shentsize)) return false;

        long strHdr = (long)shoff + (long)shstrndx * shentsize;
        ulong strOff = _is64 ? f.U64(strHdr + 24) : f.U32(strHdr + 16);
        ulong strSize = _is64 ? f.U64(strHdr + 32) : f.U32(strHdr + 20);
        if (!f.InRange((long)strOff, (long)strSize)) return false;

        int added = 0;
        for (int i = 0; i < shnum; i++)
        {
            long h = (long)shoff + (long)i * shentsize;
            uint nameOff = f.U32(h);
            uint type = f.U32(h + 4);
            ulong flags = _is64 ? f.U64(h + 8) : f.U32(h + 8);
            ulong addr = _is64 ? f.U64(h + 16) : f.U32(h + 12);
            ulong size = _is64 ? f.U64(h + 32) : f.U32(h + 20);
            ulong entsize = _is64 ? f.U64(h + 56) : f.U32(h + 36);
            if (type == SHT_DYNSYM && entsize != 0) _dynsymCount = (int)(size / entsize);
            if ((flags & 2) == 0 || addr == 0 || size == 0) continue; // SHF_ALLOC only
            string name = nameOff < strSize ? f.Utf8Z((long)strOff + nameOff, 256) ?? "" : "";
            var sf = SectionFlags.Read;
            if ((flags & 1) != 0) sf |= SectionFlags.Write;
            if ((flags & 4) != 0) sf |= SectionFlags.Execute;
            if (type == SHT_NOBITS) sf |= SectionFlags.ZeroFill;
            Sections.Add(new ImageSection(name, addr, size, sf));
            added++;
        }
        return added > 0;
    }

    private void SynthesizeSections(List<Segment> segments)
    {
        int index = 0;
        foreach (Segment s in segments)
        {
            if (s.Type != PT_LOAD || s.MemSize == 0) continue;
            var sf = SectionFlags.None;
            if ((s.Flags & 4) != 0) sf |= SectionFlags.Read;
            if ((s.Flags & 2) != 0) sf |= SectionFlags.Write;
            if ((s.Flags & 1) != 0) sf |= SectionFlags.Execute;
            if (s.FileSize != 0)
                Sections.Add(new ImageSection($"LOAD{index}", s.Vaddr, s.FileSize, sf));
            if (s.MemSize > s.FileSize)
                Sections.Add(new ImageSection($"LOAD{index}.bss", s.Vaddr + s.FileSize, s.MemSize - s.FileSize,
                    sf | SectionFlags.ZeroFill));
            index++;
        }
    }

    private void ReadDynamic(ulong va, ulong size)
    {
        int step = _is64 ? 16 : 8;
        var tags = new Dictionary<ulong, ulong>();
        for (ulong p = va; p + (ulong)step <= va + size && IsMapped(p, step); p += (ulong)step)
        {
            ulong tag = _is64 ? U64(p) : U32(p);
            ulong val = _is64 ? U64(p + 8) : U32(p + 4);
            if (tag == 0) break;
            tags.TryAdd(tag, val);
        }

        ulong Tag(ulong t) => tags.TryGetValue(t, out ulong v) ? v : 0;

        _symtab = Tag(6);
        _strtab = Tag(5);
        _strsz = Tag(10);
        _syment = (int)Tag(11);
        if (_syment == 0) _syment = _is64 ? 24 : 16;
        if (_dynsymCount < 0) _dynsymCount = CountDynamicSymbols(Tag(4), Tag(0x6ffffef5));

        ReadDynamicSymbols();

        // Order mirrors the Android linker: RELR first, then REL/RELA, then PLT.
        ApplyRelr(Tag(36), Tag(35));
        ApplyRelr(Tag(0x6fffe000), Tag(0x6fffe001));
        ApplyTable(Tag(7), Tag(8), rela: true);
        ApplyTable(Tag(17), Tag(18), rela: false);
        ApplyPacked(Tag(0x60000011), Tag(0x60000012), rela: true);
        ApplyPacked(Tag(0x6000000f), Tag(0x60000010), rela: false);
        ApplyTable(Tag(23), Tag(2), rela: Tag(20) == 7);
    }

    private int CountDynamicSymbols(ulong hash, ulong gnuHash)
    {
        if (hash != 0 && IsMapped(hash, 8)) return (int)U32(hash + 4); // nchain
        if (gnuHash != 0 && IsMapped(gnuHash, 16))
        {
            uint nbuckets = U32(gnuHash);
            uint symoffset = U32(gnuHash + 4);
            uint bloomSize = U32(gnuHash + 8);
            ulong buckets = gnuHash + 16 + (ulong)bloomSize * (ulong)PointerSize;
            ulong chains = buckets + (ulong)nbuckets * 4;
            uint max = 0;
            for (uint i = 0; i < nbuckets && IsMapped(buckets + i * 4UL, 4); i++)
                max = Math.Max(max, U32(buckets + i * 4UL));
            if (max < symoffset) return (int)symoffset;
            while (IsMapped(chains + (ulong)(max - symoffset) * 4, 4) &&
                   (U32(chains + (ulong)(max - symoffset) * 4) & 1) == 0)
                max++;
            return (int)max + 1;
        }
        // Last resort: the dynamic string table normally follows the symbol table directly.
        if (_symtab != 0 && _strtab > _symtab) return (int)((_strtab - _symtab) / (ulong)_syment);
        return 0;
    }

    private (string? Name, ulong Value, int Shndx, int Type) ReadSymbol(ulong table, int index)
    {
        ulong p = table + (ulong)index * (ulong)_syment;
        if (!IsMapped(p, _syment)) return (null, 0, 0, 0);
        uint nameOff = U32(p);
        ulong value;
        int shndx, info;
        if (_is64)
        {
            info = U8(p + 4);
            shndx = U16(p + 6);
            value = U64(p + 8);
        }
        else
        {
            value = U32(p + 4);
            info = U8(p + 12);
            shndx = U16(p + 14);
        }
        string? name = nameOff != 0 && (_strsz == 0 || nameOff < _strsz) ? TryCString(_strtab + nameOff) : null;
        return (name, value, shndx, info & 0xF);
    }

    private void ReadDynamicSymbols()
    {
        if (_symtab == 0 || _strtab == 0) return;
        for (int i = 1; i < _dynsymCount; i++)
        {
            var (name, value, shndx, _) = ReadSymbol(_symtab, i);
            if (name == null || shndx == 0 || value == 0) continue;
            Exports[name] = value;
        }
    }

    /// <summary>Reads .symtab from the file when the library was not stripped, giving names and sizes.</summary>
    private void ReadFunctionSymbols(ulong shoff, int shentsize, int shnum)
    {
        var f = _file;
        if (shoff == 0 || !f.InRange((long)shoff, (long)shnum * shentsize)) return;
        for (int i = 0; i < shnum; i++)
        {
            long h = (long)shoff + (long)i * shentsize;
            if (f.U32(h + 4) != SHT_SYMTAB) continue;
            ulong off = _is64 ? f.U64(h + 24) : f.U32(h + 16);
            ulong size = _is64 ? f.U64(h + 32) : f.U32(h + 20);
            uint link = f.U32(h + (_is64 ? 40 : 24));
            ulong entsize = _is64 ? f.U64(h + 56) : f.U32(h + 36);
            if (entsize == 0 || link >= shnum || !f.InRange((long)off, (long)size)) continue;
            long sh = (long)shoff + (long)link * shentsize;
            ulong strOff = _is64 ? f.U64(sh + 24) : f.U32(sh + 16);
            ulong strSize = _is64 ? f.U64(sh + 32) : f.U32(sh + 20);
            if (!f.InRange((long)strOff, (long)strSize)) continue;

            int count = (int)(size / entsize);
            for (int s = 1; s < count; s++)
            {
                long p = (long)off + (long)s * (long)entsize;
                uint nameOff = f.U32(p);
                ulong value, symSize;
                int info, shndx;
                if (_is64)
                {
                    info = f.U8(p + 4);
                    shndx = f.U16(p + 6);
                    value = f.U64(p + 8);
                    symSize = f.U64(p + 16);
                }
                else
                {
                    value = f.U32(p + 4);
                    symSize = f.U32(p + 8);
                    info = f.U8(p + 12);
                    shndx = f.U16(p + 14);
                }
                int type = info & 0xF;
                if (shndx == 0 || value == 0 || nameOff == 0 || nameOff >= strSize) continue;
                if (type != 1 && type != 2) continue; // STT_OBJECT, STT_FUNC
                string? name = f.Utf8Z((long)strOff + nameOff, 1024);
                if (string.IsNullOrEmpty(name) || name[0] == '$') continue; // skip ARM mapping symbols
                ulong addr = Arch == CpuArch.Arm32 && type == 2 ? value & ~1UL : value;
                Symbols.TryAdd(addr, name);
                if (type == 2 && symSize != 0) FunctionTable.Add(new FunctionRange(addr, addr + symSize, 0));
            }
        }
    }

    // ---- relocations -------------------------------------------------------------------------------------------

    private void WritePtr(ulong va, ulong value)
    {
        if (!IsMapped(va, PointerSize)) return;
        Span<byte> dst = Memory.AsSpan((int)(va - MemoryBase), PointerSize);
        if (_is64) BinaryPrimitives.WriteUInt64LittleEndian(dst, value);
        else BinaryPrimitives.WriteUInt32LittleEndian(dst, (uint)value);
        RelocationsApplied++;
    }

    private void ApplyOne(ulong offset, ulong info, long addend, bool hasAddend)
    {
        uint type = _is64 ? (uint)(info & 0xFFFFFFFF) : (uint)(info & 0xFF);
        int sym = _is64 ? (int)(info >> 32) : (int)(info >> 8);

        bool relative, absolute;
        switch (Arch)
        {
            case CpuArch.Arm64:
                relative = type == 1027;                         // R_AARCH64_RELATIVE
                absolute = type is 257 or 1025 or 1026;          // ABS64, GLOB_DAT, JUMP_SLOT
                break;
            case CpuArch.X64:
                relative = type == 8;                            // R_X86_64_RELATIVE
                absolute = type is 1 or 6 or 7;                  // 64, GLOB_DAT, JUMP_SLOT
                break;
            case CpuArch.Arm32:
                relative = type == 23;                           // R_ARM_RELATIVE
                absolute = type is 2 or 21 or 22;                // ABS32, GLOB_DAT, JUMP_SLOT
                break;
            default:
                relative = type == 8;                            // R_386_RELATIVE
                absolute = type is 1 or 6 or 7;                  // 32, GLOB_DAT, JMP_SLOT
                break;
        }

        if (!IsMapped(offset, PointerSize)) return;
        long implicitAddend = hasAddend ? addend : (long)Ptr(offset);

        if (relative)
        {
            WritePtr(offset, ImageBase + (ulong)implicitAddend);
            return;
        }
        if (!absolute || _symtab == 0) return;

        var (name, value, shndx, _) = ReadSymbol(_symtab, sym);
        if (shndx != 0 && value != 0)
        {
            // GLOB_DAT / JUMP_SLOT ignore the addend; ABS uses it.
            bool usesAddend = Arch switch
            {
                CpuArch.Arm64 => type == 257,
                CpuArch.X64 => type == 1,
                CpuArch.Arm32 => type == 2,
                _ => type == 1,
            };
            WritePtr(offset, value + (usesAddend ? (ulong)implicitAddend : 0));
        }
        else if (name != null)
        {
            ImportSlots[offset] = name;
        }
    }

    private void ApplyTable(ulong va, ulong size, bool rela)
    {
        if (va == 0 || size == 0) return;
        int ent = _is64 ? (rela ? 24 : 16) : (rela ? 12 : 8);
        ulong count = size / (ulong)ent;
        for (ulong i = 0; i < count; i++)
        {
            ulong p = va + i * (ulong)ent;
            if (!IsMapped(p, ent)) break;
            if (_is64)
                ApplyOne(U64(p), U64(p + 8), rela ? I64(p + 16) : 0, rela);
            else
                ApplyOne(U32(p), U32(p + 4), rela ? I32(p + 8) : 0, rela);
        }
    }

    private void ApplyRelr(ulong va, ulong size)
    {
        if (va == 0 || size == 0) return;
        ulong word = (ulong)PointerSize;
        ulong count = size / word;
        ulong where = 0;
        for (ulong i = 0; i < count; i++)
        {
            if (!IsMapped(va + i * word, PointerSize)) break;
            ulong entry = Ptr(va + i * word);
            if ((entry & 1) == 0)
            {
                Rebase(entry);
                where = entry + word;
            }
            else
            {
                ulong bitmap = entry >> 1;
                for (ulong bit = 0; bitmap != 0; bit++, bitmap >>= 1)
                    if ((bitmap & 1) != 0)
                        Rebase(where + bit * word);
                where += (word * 8 - 1) * word;
            }
        }

        void Rebase(ulong addr)
        {
            if (IsMapped(addr, PointerSize)) WritePtr(addr, Ptr(addr) + ImageBase);
        }
    }

    /// <summary>Android "APS2" packed relocations (bionic linker's packed_reloc_iterator).</summary>
    private void ApplyPacked(ulong va, ulong size, bool rela)
    {
        if (va == 0 || size < 4 || !TrySpan(va, (int)size, out ReadOnlySpan<byte> data)) return;
        if (data[0] != 'A' || data[1] != 'P' || data[2] != 'S' || data[3] != '2') return;

        const long GroupedByInfo = 1, GroupedByOffsetDelta = 2, GroupedByAddend = 4, HasAddend = 8;
        int pos = 4;
        long total = VarInt.ReadSleb128(data, ref pos);
        ulong offset = (ulong)VarInt.ReadSleb128(data, ref pos);
        long addend = 0;
        long done = 0;
        while (done < total && pos < data.Length)
        {
            long groupSize = VarInt.ReadSleb128(data, ref pos);
            long flags = VarInt.ReadSleb128(data, ref pos);
            long groupDelta = (flags & GroupedByOffsetDelta) != 0 ? VarInt.ReadSleb128(data, ref pos) : 0;
            ulong groupInfo = (flags & GroupedByInfo) != 0 ? (ulong)VarInt.ReadSleb128(data, ref pos) : 0;
            if ((flags & HasAddend) != 0 && (flags & GroupedByAddend) != 0)
                addend += VarInt.ReadSleb128(data, ref pos);
            else if ((flags & HasAddend) == 0)
                addend = 0;

            for (long i = 0; i < groupSize && pos <= data.Length; i++)
            {
                offset += (flags & GroupedByOffsetDelta) != 0
                    ? (ulong)groupDelta
                    : (ulong)VarInt.ReadSleb128(data, ref pos);
                ulong info = (flags & GroupedByInfo) != 0 ? groupInfo : (ulong)VarInt.ReadSleb128(data, ref pos);
                if ((flags & HasAddend) != 0 && (flags & GroupedByAddend) == 0)
                    addend += VarInt.ReadSleb128(data, ref pos);
                ApplyOne(offset, info, addend, rela);
            }
            done += groupSize;
        }
    }
}
