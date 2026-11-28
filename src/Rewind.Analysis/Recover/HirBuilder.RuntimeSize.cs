using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

public sealed partial class HirBuilder
{
    private SRuntimeSize? RuntimeSize(Node node)
    {
        // The fields are unsigned 32-bit byte counts, kept in a pointer-sized register.
        while (node.Op == Op.ZExt && node.In.Length == 1 && node.In[0].Type == VT.I32 && node.Type == VT.I64)
            node = node.In[0];
        return Eval(node) as SRuntimeSize;
    }

    private bool TryEmitRuntimeSizedCopy(Node call)
    {
        if (!_abi.UsesFullySharedReturnBuffer || call.Aux is not CallInfo info || info.Indirect ||
            _p.Helpers.KindAt(info.Target) != Runtime.HelperKind.Memcpy ||
            IntAt(call, 0) is not { } destination || IntAt(call, 1) is not { } source ||
            IntAt(call, 2) is not { } bytes || RuntimeSize(bytes) is not { Array: null } size)
            return false;
        // Both addresses must independently identify a whole T; the runtime count is T's stack slot.
        // A partial, differently typed, unknown, or fixed-size copy is left to the existing paths.
        HExpr? to = LocationOf(destination, size.Type), from = LocationOf(source, size.Type);
        if (to?.Type?.Key != size.Type.Key || from?.Type?.Key != size.Type.Key) return false;
        Emit(new HAssign(to, from), call.Addr);
        return true;
    }
}
