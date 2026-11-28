using System.Buffers.Binary;

namespace Rewind.Analysis.Runtime;

/// <summary>The complete ARM64 rank-two, eight-byte element getter, including both bounds failures.</summary>
internal static class Arm64MultiArrayAccessShape
{
    public static HelperInfo? Match(ReadOnlySpan<byte> body, ulong start, Func<ulong, bool> isIndexThrower)
    {
        if (body.Length != 56 || start > ulong.MaxValue - 56) return null;
        Span<uint> words = stackalloc uint[14];
        for (int i = 0; i < words.Length; i++) words[i] = BinaryPrimitives.ReadUInt32LittleEndian(body[(i * 4)..]);
        if (words[0] != 0xF81F0FFE || words[1] != 0xF9400808 || words[2] != 0xB9400109 ||
            words[3] != 0x6B09003F || words[5] != 0xF9400908 || words[6] != 0x6B08005F ||
            words[8] != 0x9B010908 || words[9] != 0x8B080C08 || words[10] != 0xF9401100 ||
            words[11] != 0xF84107FE || words[12] != 0xD65F03C0 ||
            (words[4] & 0xFF00001F) != 0x54000002 || (words[7] & 0xFF00001F) != 0x54000002 ||
            Branch19(words[4], start + 16) != start + 52 || Branch19(words[7], start + 28) != start + 52 ||
            (words[13] & 0xFC000000) != 0x94000000) return null;
        long displacement = (int)(words[13] << 6) >> 4;
        ulong failure = unchecked((ulong)((long)(start + 52) + displacement));
        if (!isIndexThrower(failure)) return null;
        return new HelperInfo(HelperKind.RectangularArrayGetAt, 3, false, true,
            "ARM64 rank-two reference getter (complete bounds/access/return shape)");
    }

    private static ulong Branch19(uint instruction, ulong address)
    {
        long displacement = (int)(instruction << 8) >> 11;
        return unchecked((ulong)((long)address + displacement));
    }
}
