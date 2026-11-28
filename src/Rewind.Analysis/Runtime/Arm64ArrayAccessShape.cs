using System.Buffers.Binary;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// A complete ARM64 object-array store wrapper: unsigned bounds check, one eight-byte
/// store and return, with its sole failing edge calling the proved index thrower.
/// The caller must separately prove an exact fresh object[] and a canonical index.
/// </summary>
internal static class Arm64ArrayAccessShape
{
    internal static HelperInfo? Match(ReadOnlySpan<byte> body, ulong start, Func<ulong, bool> isIndexThrower)
    {
        if (body.Length != 32 || (start & 3) != 0) return null;
        ReadOnlySpan<uint> fixedWords = [0xB9401808, 0x6B08003F, 0x54000082,
            0x8B010C08, 0xF9001102, 0xD65F03C0, 0xF81F0FFE];
        for (int i = 0; i < fixedWords.Length; i++)
            if (BinaryPrimitives.ReadUInt32LittleEndian(body[(i * 4)..]) != fixedWords[i]) return null;
        A64Instruction call = A64Decoder.Decode(BinaryPrimitives.ReadUInt32LittleEndian(body[28..]), start + 28);
        if (call.Op != A64Op.Bl || !isIndexThrower(call.Target)) return null;
        return new HelperInfo(HelperKind.ArraySetAt, 3, false, false,
            "ARM64 checked object-array store (complete native shape)") { ArrayAccessFreshObjectStore = true };
    }

    /// <summary>The guard consumes w1, but the address uses x1; their successful values must agree.</summary>
    internal static bool CanonicalIndex(Node index)
    {
        if (index.Dead) return false;
        if (index.Type == VT.I32) return true;
        if (index.Type != VT.I64) return false;
        if (index.Op is Op.ZExt or Op.SExt)
            return index.In is [{ Type: VT.I32, Dead: false }];
        return index.Op == Op.Const && index.In.Length == 0 && index.Aux == null &&
            (index.UImm <= uint.MaxValue || index.Imm >= int.MinValue && index.Imm < 0);
    }

    internal static bool FreshAllocation(Node value, Func<ulong, HelperKind> kindAt) =>
        value is { Dead: false, Op: Op.Proj, Imm: 0, Type: VT.I64,
            In: [{ Dead: false, Op: Op.Call, Aux: CallInfo { Indirect: false } call }] } &&
        kindAt(call.Target) == HelperKind.SzArrayNew;
}
