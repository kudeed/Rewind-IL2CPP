using System.Buffers.Binary;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Text;

namespace Rewind.Binary;

public enum CpuArch { X86, X64, Arm32, Arm64 }

public enum ImageFormat { PE, Elf, MachO }

public enum TargetOs { Windows, Linux, Android, MacOS, IOS, Unknown }

[Flags]
public enum SectionFlags { None = 0, Read = 1, Write = 2, Execute = 4, ZeroFill = 8 }

public sealed record ImageSection(string Name, ulong Va, ulong Size, SectionFlags Flags)
{
    public ulong End => Va + Size;
    public bool Contains(ulong va) => va >= Va && va < End;
    public bool IsExecutable => (Flags & SectionFlags.Execute) != 0;
    public bool IsWritable => (Flags & SectionFlags.Write) != 0;
}

/// <summary>
/// A function extent taken from unwind tables (PE .pdata, ELF .eh_frame) or symbols. A chained range is a
/// further region of a function that started elsewhere, not a function of its own.
/// </summary>
public readonly record struct FunctionRange(ulong Start, ulong End, ulong UnwindInfo, bool Chained = false);

/// <summary>
/// A native image laid out the way the loader would map it, so everything can be addressed by virtual address.
/// Relative relocations are already applied: reading a pointer slot yields the address it holds at run time
/// (assuming the image is loaded at <see cref="ImageBase"/>).
/// </summary>
public abstract class NativeImage
{
    protected byte[] Memory = [];
    protected ulong MemoryBase;

    public string FilePath { get; protected set; } = "";
    public abstract ImageFormat Format { get; }
    public CpuArch Arch { get; protected set; }
    public TargetOs Os { get; protected set; } = TargetOs.Unknown;
    public int PointerSize { get; protected set; }
    public ulong ImageBase { get; protected set; }

    public List<ImageSection> Sections { get; } = [];

    /// <summary>Exported symbol name to virtual address.</summary>
    public Dictionary<string, ulong> Exports { get; } = new(StringComparer.Ordinal);

    /// <summary>Import slot (IAT / GOT entry) virtual address to imported symbol name.</summary>
    public Dictionary<ulong, string> ImportSlots { get; } = [];

    /// <summary>Symbols from a non-stripped symbol table, when present.</summary>
    public Dictionary<ulong, string> Symbols { get; } = [];

    /// <summary>Function extents sorted by start address; empty when the format offers none.</summary>
    public List<FunctionRange> FunctionTable { get; } = [];

    public bool Is64Bit => PointerSize == 8;

    public ulong MemoryStart => MemoryBase;
    public ulong MemoryEnd => MemoryBase + (ulong)Memory.Length;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool IsMapped(ulong va, int size = 1)
    {
        ulong off = va - MemoryBase;
        return va >= MemoryBase && off <= (ulong)Memory.Length && (ulong)size <= (ulong)Memory.Length - off;
    }

    public ReadOnlySpan<byte> Span(ulong va, int length)
    {
        if (!IsMapped(va, length))
            throw new ArgumentOutOfRangeException(nameof(va), $"Address 0x{va:X} (+{length}) is outside the image");
        return Memory.AsSpan((int)(va - MemoryBase), length);
    }

    public bool TrySpan(ulong va, int length, out ReadOnlySpan<byte> span)
    {
        if (!IsMapped(va, length))
        {
            span = default;
            return false;
        }
        span = Memory.AsSpan((int)(va - MemoryBase), length);
        return true;
    }

    /// <summary>All mapped bytes from <paramref name="va"/> to the end of the section containing it.</summary>
    public ReadOnlySpan<byte> SpanToSectionEnd(ulong va)
    {
        ImageSection? s = SectionAt(va);
        if (s == null) return default;
        ulong len = Math.Min(s.End, MemoryEnd) - va;
        return Memory.AsSpan((int)(va - MemoryBase), (int)len);
    }

    public byte U8(ulong va) => Span(va, 1)[0];
    public ushort U16(ulong va) => BinaryPrimitives.ReadUInt16LittleEndian(Span(va, 2));
    public uint U32(ulong va) => BinaryPrimitives.ReadUInt32LittleEndian(Span(va, 4));
    public int I32(ulong va) => BinaryPrimitives.ReadInt32LittleEndian(Span(va, 4));
    public ulong U64(ulong va) => BinaryPrimitives.ReadUInt64LittleEndian(Span(va, 8));
    public long I64(ulong va) => BinaryPrimitives.ReadInt64LittleEndian(Span(va, 8));

    /// <summary>Reads a pointer-sized unsigned value.</summary>
    public ulong Ptr(ulong va) => PointerSize == 8 ? U64(va) : U32(va);

    /// <summary>Reads a pointer-sized signed value (used for count fields padded to pointer width).</summary>
    public long NInt(ulong va) => PointerSize == 8 ? I64(va) : I32(va);

    public bool TryPtr(ulong va, out ulong value)
    {
        if (!IsMapped(va, PointerSize))
        {
            value = 0;
            return false;
        }
        value = Ptr(va);
        return true;
    }

    /// <summary>Reads a NUL-terminated UTF-8 string, or null when the address is unmapped or not text.</summary>
    public string? TryCString(ulong va, int maxLength = 512)
    {
        if (!IsMapped(va)) return null;
        int start = (int)(va - MemoryBase);
        int limit = Math.Min(Memory.Length, start + maxLength);
        int end = Array.IndexOf(Memory, (byte)0, start, limit - start);
        if (end < 0) return null;
        return Encoding.UTF8.GetString(Memory, start, end - start);
    }

    public ImageSection? SectionAt(ulong va)
    {
        foreach (ImageSection s in Sections)
            if (s.Contains(va))
                return s;
        return null;
    }

    public bool IsCodeAddress(ulong va)
    {
        ImageSection? s = SectionAt(va);
        return s != null && s.IsExecutable;
    }

    public bool IsDataAddress(ulong va)
    {
        ImageSection? s = SectionAt(va);
        return s != null && !s.IsExecutable;
    }

    /// <summary>Finds every occurrence of a byte pattern inside mapped, file-backed memory.</summary>
    public IEnumerable<ulong> FindBytes(byte[] pattern, Func<ImageSection, bool>? filter = null)
    {
        foreach (ImageSection s in Sections)
        {
            if ((s.Flags & SectionFlags.ZeroFill) != 0) continue;
            if (filter != null && !filter(s)) continue;
            if (!IsMapped(s.Va)) continue;
            int start = (int)(s.Va - MemoryBase);
            int length = (int)Math.Min(s.Size, (ulong)(Memory.Length - start));
            int pos = 0;
            while (pos <= length - pattern.Length)
            {
                int hit = Memory.AsSpan(start + pos, length - pos).IndexOf(pattern);
                if (hit < 0) break;
                yield return s.Va + (ulong)(pos + hit);
                pos += hit + 1;
            }
        }
    }

    /// <summary>Finds pointer-aligned slots in non-executable sections that hold <paramref name="value"/>.</summary>
    public List<ulong> FindPointersTo(ulong value)
    {
        var hits = new List<ulong>();
        foreach (ImageSection s in Sections)
        {
            if (s.IsExecutable || (s.Flags & SectionFlags.ZeroFill) != 0) continue;
            if (!IsMapped(s.Va)) continue;
            ulong va = (s.Va + (ulong)(PointerSize - 1)) & ~(ulong)(PointerSize - 1);
            int start = (int)(va - MemoryBase);
            int length = (int)Math.Min(s.End - va, (ulong)(Memory.Length - start));
            if (PointerSize == 8)
            {
                ReadOnlySpan<ulong> words = MemoryMarshal.Cast<byte, ulong>(Memory.AsSpan(start, length & ~7));
                int pos = 0;
                while (pos < words.Length)
                {
                    int hit = words[pos..].IndexOf(value);
                    if (hit < 0) break;
                    hits.Add(va + (ulong)(pos + hit) * 8);
                    pos += hit + 1;
                }
            }
            else
            {
                ReadOnlySpan<uint> words = MemoryMarshal.Cast<byte, uint>(Memory.AsSpan(start, length & ~3));
                uint v = (uint)value;
                int pos = 0;
                while (pos < words.Length)
                {
                    int hit = words[pos..].IndexOf(v);
                    if (hit < 0) break;
                    hits.Add(va + (ulong)(pos + hit) * 4);
                    pos += hit + 1;
                }
            }
        }
        return hits;
    }

    /// <summary>Opens a PE, ELF or Mach-O image from raw file bytes.</summary>
    public static NativeImage Load(byte[] file, string path)
    {
        if (file.Length >= 4)
        {
            if (file[0] == 'M' && file[1] == 'Z') return new PeImage(file, path);
            if (file[0] == 0x7F && file[1] == 'E' && file[2] == 'L' && file[3] == 'F') return new ElfImage(file, path);
            uint magic = BinaryPrimitives.ReadUInt32LittleEndian(file);
            if (magic is 0xFEEDFACF or 0xFEEDFACE or 0xBEBAFECA or 0xBFBAFECA)
                return new MachOImage(file, path);
        }
        throw new InvalidDataException($"'{path}' is not a PE, ELF or Mach-O image");
    }
}
