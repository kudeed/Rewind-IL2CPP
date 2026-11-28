using Rewind.Analysis.Ir;
using Rewind.Analysis.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Memory written by the scalar C math helpers. A floating argument consumes an argument position on Win64,
/// but does not consume a general register on AAPCS64. Each output pointer names exactly one float/double.
/// </summary>
internal static class ScalarMathWriteExtent
{
    internal static int Of(HelperInfo helper, ArgSlot slot, RegisterModel registers)
    {
        if (helper.NoReturn || helper.FloatArgs != 1 || slot.Kind != ArgSlotKind.IntReg ||
            helper.Kind is not (HelperKind.Modf or HelperKind.SinCos)) return -1;
        int first = registers.SharedPositions ? 1 : 0;
        int count = helper.Kind == HelperKind.SinCos ? 2 : 1;
        if (slot.Index < first || slot.Index >= first + count) return -1;
        return helper.IsDouble ? 8 : 4;
    }
}
