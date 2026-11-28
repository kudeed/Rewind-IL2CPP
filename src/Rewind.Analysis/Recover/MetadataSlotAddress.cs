using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Recover;

/// <summary>
/// A fixed metadata-table entry can remain expressed as base + offset after SSA construction.
/// Recognize only a full-width constant sum that names an already-proved metadata slot. This
/// does not dereference native memory or assign a type to an arbitrary writable global.
/// </summary>
internal static class MetadataSlotAddress
{
    internal static bool TryConstantAdd(Node address, Func<ulong, bool> isMetadataSlot, out ulong slot)
    {
        slot = 0;
        if (address.Dead || address.Op != Op.Add || address.Type != VT.I64 || address.Aux != null ||
            address.In is not [var left, var right] || left.Dead || right.Dead ||
            left.Op != Op.Const || right.Op != Op.Const || left.Type != VT.I64 || right.Type != VT.I64 ||
            left.In.Length != 0 || right.In.Length != 0 || left.Aux != null || right.Aux != null) return false;
        // Native pointer arithmetic wraps at the register width. Membership in the independently found
        // metadata table is still required for the resulting address, including a negative displacement.
        ulong value = unchecked(left.UImm + right.UImm);
        if (value == 0 || (value & 7) != 0 || !isMetadataSlot(value)) return false;
        slot = value;
        return true;
    }
}
