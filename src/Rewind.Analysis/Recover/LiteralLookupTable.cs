using Rewind.Analysis.Ir;
using Rewind.Binary;

namespace Rewind.Analysis.Recover;

/// <summary>Bounded, immutable metadata string-pointer tables on ELF ARM64.
/// This recognizes slot addresses, not initialized managed string objects.
/// The caller must separately prove the unsigned index bound.</summary>
public static class LiteralLookupTable
{
    public const int MaxEntries = 128;

    public static bool TryRead(NativeImage image, ulong address, int count,
        Func<ulong, bool> isStringSlot, out ulong[] entries)
    {
        entries = [];
        if (image.Arch != CpuArch.Arm64 || image.Format != ImageFormat.Elf ||
            image.PointerSize != 8 || (address & 7) != 0 ||
            count < 1 || count > MaxEntries ||
            address > ulong.MaxValue - (ulong)(count * 8 - 1) ||
            image.SectionAt(address) is not { IsExecutable: false } section ||
            !section.Contains(address + (ulong)(count * 8 - 1)) ||
            !image.IsMapped(address, count * 8)) return false;

        var found = new ulong[count];
        for (int i = 0; i < count; i++)
        {
            ulong va = address + (ulong)(i * 8);
            // Only RELRO pointer tables: import slots and partial ranges are
            // not stable constants. ResolveUsageSlot handles original tokens.
            if (!image.IsReadOnlyAfterLoad(va) || !image.IsReadOnlyAfterLoad(va + 7))
                return false;
            ulong slot = image.Ptr(va);
            if ((slot & 7) != 0 || !image.IsMapped(slot, 8) ||
                image.SectionAt(slot) is not { IsExecutable: false } target ||
                slot > ulong.MaxValue - 7 || !target.Contains(slot + 7) ||
                !isStringSlot(slot)) return false;
            found[i] = slot;
        }
        entries = found;
        return true;
    }

    /// <summary>Balanced unsigned index partition over proven domain [0,n).
    /// Unlike a linear select chain, this keeps metadata choices shallow.
    /// Emit children before parents, retaining original block and source site.</summary>
    public static Node BuildChoice(Function fn, Block block, ref int at,
        Node index, ulong[] entries, ulong source)
    {
        if (entries.Length < 1 || entries.Length > MaxEntries ||
            !index.Type.IsInt() || index.Type.Bits() < 8 ||
            index.Type.Bits() > 32) throw new ArgumentException("invalid literal table");
        int position = at;
        Node C(VT type, ulong value)
        {
            Node n = fn.NewNode(Op.Const, type, null);
            n.Imm = unchecked((long)value);
            return n;
        }
        Node Put(Op op, VT type, params Node[] inputs)
        {
            Node n = fn.NewNode(op, type, block, inputs);
            n.Addr = source;
            block.Nodes.Insert(position++, n);
            return n;
        }
        Node Tree(int lo, int hi)
        {
            ulong first = entries[lo];
            bool same = true;
            for (int i = lo + 1; i < hi; i++) same &= entries[i] == first;
            if (same) return C(VT.I64, first);
            int mid = lo + (hi - lo) / 2;
            Node test = Put(Op.CmpLtU, VT.I1, index, C(index.Type, (ulong)mid));
            Node left = Tree(lo, mid), right = Tree(mid, hi);
            return Put(Op.Select, VT.I64, test, left, right);
        }
        Node result = Tree(0, entries.Length);
        at = position;
        return result;
    }
}
