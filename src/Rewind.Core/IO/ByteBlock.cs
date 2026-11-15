using System.Buffers.Binary;
using System.Runtime.CompilerServices;
using System.Text;

namespace Rewind.IO;

/// <summary>Little-endian reads over an in-memory byte array, addressed by file offset.</summary>
public sealed class ByteBlock
{
    public readonly byte[] Data;

    public ByteBlock(byte[] data) => Data = data;

    public int Length => Data.Length;

    public bool InRange(long offset, long length = 1) =>
        offset >= 0 && length >= 0 && offset + length <= Data.Length;

    public ReadOnlySpan<byte> Span(long offset, int length) => Data.AsSpan(checked((int)offset), length);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public byte U8(long o) => Data[o];

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public ushort U16(long o) => BinaryPrimitives.ReadUInt16LittleEndian(Data.AsSpan((int)o, 2));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public short I16(long o) => BinaryPrimitives.ReadInt16LittleEndian(Data.AsSpan((int)o, 2));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public uint U32(long o) => BinaryPrimitives.ReadUInt32LittleEndian(Data.AsSpan((int)o, 4));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public int I32(long o) => BinaryPrimitives.ReadInt32LittleEndian(Data.AsSpan((int)o, 4));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public ulong U64(long o) => BinaryPrimitives.ReadUInt64LittleEndian(Data.AsSpan((int)o, 8));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public long I64(long o) => BinaryPrimitives.ReadInt64LittleEndian(Data.AsSpan((int)o, 8));

    /// <summary>Reads a NUL-terminated UTF-8 string. Returns null when the offset is out of range.</summary>
    public string? Utf8Z(long offset, int maxLength = 1 << 20)
    {
        if (offset < 0 || offset >= Data.Length) return null;
        int start = (int)offset;
        int limit = (int)Math.Min(Data.Length, offset + maxLength);
        int end = Array.IndexOf(Data, (byte)0, start, limit - start);
        if (end < 0) end = limit;
        return Encoding.UTF8.GetString(Data, start, end - start);
    }

    /// <summary>Reads a NUL-terminated ASCII name from a fixed-size field.</summary>
    public string FixedAscii(long offset, int fieldSize)
    {
        ReadOnlySpan<byte> s = Span(offset, fieldSize);
        int n = s.IndexOf((byte)0);
        if (n < 0) n = fieldSize;
        return Encoding.ASCII.GetString(s[..n]);
    }
}

/// <summary>LEB128 and ECMA-335 compressed integer decoding.</summary>
public static class VarInt
{
    public static long ReadSleb128(ReadOnlySpan<byte> data, ref int pos)
    {
        long result = 0;
        int shift = 0;
        byte b;
        do
        {
            b = data[pos++];
            result |= (long)(b & 0x7F) << shift;
            shift += 7;
        } while ((b & 0x80) != 0 && shift < 70);
        if (shift < 64 && (b & 0x40) != 0) result |= -1L << shift;
        return result;
    }

    public static ulong ReadUleb128(ReadOnlySpan<byte> data, ref int pos)
    {
        ulong result = 0;
        int shift = 0;
        byte b;
        do
        {
            b = data[pos++];
            result |= (ulong)(b & 0x7F) << shift;
            shift += 7;
        } while ((b & 0x80) != 0 && shift < 70);
        return result;
    }

    /// <summary>
    /// IL2CPP's compressed uint32 (see libil2cpp utils/MemoryRead / ReadCompressedUInt32): 1, 2 or 4 byte forms
    /// like ECMA-335, plus the 0xF0 five-byte form and the 0xFE/0xFF sentinels.
    /// </summary>
    public static uint ReadCompressedUInt32(ReadOnlySpan<byte> data, ref int pos)
    {
        byte first = data[pos++];
        if ((first & 0x80) == 0) return first;
        if ((first & 0xC0) == 0x80)
        {
            uint v = (uint)(first & 0x3F) << 8 | data[pos];
            pos += 1;
            return v;
        }
        if ((first & 0xE0) == 0xC0)
        {
            uint v = (uint)(first & 0x1F) << 24 | (uint)data[pos] << 16 | (uint)data[pos + 1] << 8 | data[pos + 2];
            pos += 3;
            return v;
        }
        if (first == 0xF0)
        {
            uint v = BinaryPrimitives.ReadUInt32LittleEndian(data.Slice(pos, 4));
            pos += 4;
            return v;
        }
        if (first == 0xFE) return uint.MaxValue - 1;
        if (first == 0xFF) return uint.MaxValue;
        throw new InvalidDataException($"Invalid compressed integer lead byte 0x{first:X2}");
    }

    public static int ReadCompressedInt32(ReadOnlySpan<byte> data, ref int pos)
    {
        uint encoded = ReadCompressedUInt32(data, ref pos);
        if (encoded == uint.MaxValue) return int.MinValue;
        bool negative = (encoded & 1) != 0;
        encoded >>= 1;
        return negative ? -(int)(encoded + 1) : (int)encoded;
    }
}
