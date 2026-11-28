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

    private readonly Dictionary<Node, SRuntimeBuffer> _runtimeBuffers = [];

    private SRuntimeAllocationExtent? RuntimeAllocationExtent(Node extent)
    {
        if (!_abi.UsesFullySharedRuntime || extent.Op != Op.And || extent.Type != VT.I64 ||
            !extent.In[1].IsConst || extent.In[1].UImm is not (0x1FFFFFFF0UL or 0xFFFFFFFFFFFFFFF0UL) ||
            extent.In[0] is not { Op: Op.Add, Type: VT.I64 } rounded || !rounded.In[1].IsConstValue(15) ||
            RuntimeSize(rounded.In[0]) is not { Array: null, Type: GenericParamSig } size) return null;
        return new SRuntimeAllocationExtent(size.Type);
    }

    private SRuntimeBuffer? RuntimeBufferAllocation(Node node, int depth = 0)
    {
        if (!_abi.UsesFullySharedRuntime || depth > 32 || node.Op != Op.Sub || node.Type != VT.I64) return null;
        if (_runtimeBuffers.TryGetValue(node, out var existing)) return existing;
        Node extent = node.In[1];
        if (extent.Op != Op.And || !extent.In[1].IsConst ||
            extent.In[1].UImm is not (0x1FFFFFFF0UL or 0xFFFFFFFFFFFFFFF0UL) ||
            extent.In[0] is not { Op: Op.Add, Type: VT.I64 } rounded || !rounded.In[1].IsConstValue(15) ||
            RuntimeSize(rounded.In[0]) is not { Array: null, Type: GenericParamSig } size) return null;
        // Allocations and their entry-frame origin are recognized syntactically. Do not evaluate
        // arbitrary data while a phi or canary proof is being planned before call results exist.
        int upperBound;
        if (IsFrameAddress(node.In[0], out int fixedAt)) upperBound = fixedAt;
        else if (RuntimeBufferAllocation(node.In[0], depth + 1) is { } prior) upperBound = prior.UpperBound;
        else return null;
        HVar value = _h.NewLocal(size.Type, "generic");
        var buffer = new SRuntimeBuffer(size.Type, value, upperBound);
        _runtimeBuffers.Add(node, buffer);
        return buffer;
    }

    private TypeSig? RuntimeBufferPhiType(Node phi)
    {
        if (!_abi.UsesFullySharedRuntime || phi.Type != VT.I64 || phi.In.Length == 0) return null;
        TypeSig? type = null;
        foreach (Node input in phi.In)
        {
            if (RuntimeBufferAllocation(input) is not { } buffer) return null;
            if (type != null && type.Key != buffer.Type.Key) return null;
            type = buffer.Type;
        }
        return type;
    }

    private bool TryEmitRuntimeSizedFill(Node call)
    {
        if (!_abi.UsesFullySharedRuntime || call.Aux is not CallInfo { Indirect: false } info ||
            _p.Helpers.KindAt(info.Target) != Runtime.HelperKind.Memset ||
            IntAt(call, 0) is not { } target || IntAt(call, 1) is not { } fill || !fill.IsConstValue(0) ||
            IntAt(call, 2) is not { } bytes || RuntimeSize(bytes) is not { Array: null } size ||
            Eval(target) is not SRuntimeBuffer buffer || buffer.Type.Key != size.Type.Key) return false;
        Emit(new HAssign(new HLocal(buffer.Variable) { Type = size.Type }, new HTypeExpr(HTypeOp.Default, size.Type, null) { Type = size.Type }), call.Addr);
        return true;
    }

    private bool TryEmitRuntimeSizedCopy(Node call)
    {
        if (!_abi.UsesFullySharedRuntime || call.Aux is not CallInfo info || info.Indirect ||
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
