using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Recover;

public sealed partial class Normalizer
{
    internal static bool IsNativeClassCheck(Node condition, Func<ulong, bool> isClassSlot)
    {
        if (condition.Op is not (Op.CmpEq or Op.CmpNe) || condition.In.Length != 2) return false;
        bool Pair(Node actual, Node expected) =>
            actual is { Op: Op.Load, Type: VT.I64, In.Length: 1 } && actual.In[0].Type == VT.I64 &&
            expected is { Op: Op.SlotValue, Type: VT.I64 } && isClassSlot(expected.UImm);
        return Pair(condition.In[0], condition.In[1]) || Pair(condition.In[1], condition.In[0]);
    }
}
