using Rewind.Analysis.Ir;
using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;
using Rewind.Analysis.Runtime;

namespace Rewind.Analysis.Recover;

public sealed partial class HirBuilder
{
    private readonly HashSet<Block> _runtimeStackGuards = [];
    private HashSet<Block>? _runtimeReachable;

    private static bool SameRuntimeIndex32(Node left, Node right) =>
        left.Type == VT.I32 && right.Type == VT.I32 &&
        (ReferenceEquals(left, right) ||
         left.Op == Op.Trunc && right.Op == Op.Trunc && left.In[0].Type == VT.I64 &&
         ReferenceEquals(left.In[0], right.In[0]));

    private bool RuntimeArrayLength32(Node value, Node array)
    {
        if (value.Type != VT.I32) return false;
        if (value.Op == Op.Trunc && value.In[0].Type == VT.I64) value = value.In[0];
        return value.Op == Op.Load && value.Type is VT.I32 or VT.I64 &&
            value.In[0] is { Op: Op.Add } address && ReferenceEquals(address.In[0], array) &&
            address.In[1].IsConstValue(_header + _ptr);
    }

    private bool RuntimeArrayIndexInRange(Node call, Node array, Node index)
    {
        // Deliberately require the actual unsigned bounds guard immediately preceding this block.
        // Its false edge is the block's only entry; no join or unchecked alternate path is accepted.
        if (call.Block is not { Preds.Count: 1 } block) return false;
        Block guard = block.Preds[0];
        if (guard.Scope != block.Scope || guard.Succs.Count != 2 ||
            !ReferenceEquals(guard.Succs[1], block) || ReferenceEquals(guard.Succs[0], block) ||
            !_cfg.Dominates(guard, block) ||
            guard.Terminator is not { Op: Op.Branch } branch ||
            branch.In[0] is not { Op: Op.CmpLeU } compare) return false;
        Node length = compare.In[0], checkedIndex = compare.In[1];
        if (length.Type != checkedIndex.Type) return false;
        if (length is { Op: Op.ZExt, Type: VT.I64 } && length.In[0].Type == VT.I32)
            length = length.In[0];
        if (!RuntimeArrayLength32(length, array)) return false;

        if (ReferenceEquals(index, checkedIndex)) return true;
        // A 32-bit guard cannot bound an arbitrary 64-bit address index. Only the exact signed or
        // unsigned extension of those same 32 bits is accepted (array Length is a nonnegative int).
        if (index.Type != VT.I64 || index.Op is not (Op.SExt or Op.ZExt) ||
            index.In[0].Type != VT.I32) return false;
        if (checkedIndex.Type == VT.I64 && checkedIndex.Op is Op.SExt or Op.ZExt &&
            checkedIndex.In[0].Type == VT.I32) checkedIndex = checkedIndex.In[0];
        return SameRuntimeIndex32(index.In[0], checkedIndex);
    }

    // Inspect address syntax without evaluating its index. Planning happens before calls are emitted:
    // evaluating a projection here would incorrectly cache an as-yet unbound program value.
    private bool RuntimeArrayDestination(Node call, Node address, TypeSig element)
    {
        long offset = 0;
        var terms = new List<Node>();
        var pending = new Stack<Node>();
        pending.Push(address);
        int budget = 64;
        while (pending.TryPop(out Node? node))
        {
            if (--budget < 0) return false;
            if (node.IsConst) offset += IrBuilder.SImm(node);
            else if (node.Op == Op.Add && node.Type == VT.I64)
            {
                pending.Push(node.In[0]);
                pending.Push(node.In[1]);
            }
            else terms.Add(node);
        }
        if (offset != _header + 2 * _ptr || terms.Count != 2) return false;
        for (int side = 0; side < 2; side++)
        {
            Node array = terms[side], product = terms[1 - side];
            if (!_sem.TryGetValue(array, out Sem? bound) || bound is not SVal { Expr: HArg, Type: SzArraySig type } ||
                type.ElementType.Key != element.Key || product.Op != Op.Mul || product.Type != VT.I64)
                continue;
            for (int factor = 0; factor < 2; factor++)
            {
                Node stride = product.In[factor];
                if (stride.Op == Op.ZExt && stride.In[0].Type == VT.I32) stride = stride.In[0];
                if (stride is not { Op: Op.Load, Type: VT.I32 } ||
                    stride.In[0] is not { Op: Op.Add } field || !field.In[1].IsConstValue(_p.Klass.ElementSize) ||
                    field.In[0] is not { Op: Op.Load, Type: VT.I64 } klass ||
                    !ReferenceEquals(klass.In[0], array)) continue;
                if (RuntimeArrayIndexInRange(call, array, product.In[1 - factor])) return true;
            }
        }
        return false;
    }

    private bool RuntimeWriteOutside(Node call, int offset)
    {
        if (call.Aux is not CallInfo { Indirect: false } info ||
            _p.Helpers.KindAt(info.Target) is not (HelperKind.Memset or HelperKind.Memcpy) ||
            IntAt(call, 0) is not { } destination ||
            IntAt(call, 2) is not { } count || RuntimeSize(count) is not { Array: null } size)
            return false;
        // Only the allocation pattern is evaluated; an arbitrary computed address may contain
        // program data which is not bound until its producing call is emitted.
        if (RuntimeBufferAllocation(destination) is { } buffer && size.Type.Key == buffer.Type.Key)
            return buffer.UpperBound <= offset;
        // Only a whole T whose original bounds guard proves an in-range element is outside the stack.
        return RuntimeArrayDestination(call, destination, size.Type);
    }

    private bool ScalarManagedCall(Node call)
    {
        if (call.Aux is not CallInfo { Indirect: false } info) return false;
        CallTarget target = _p.Resolve(info.Target);
        if (target.Methods.Count != 1 || target.Insts.Count != 0) return false;
        MethodDef method = target.Methods[0];
        static bool Scalar(TypeSig type) => type is PrimitiveSig { Element:
            Il2CppTypeEnum.Boolean or Il2CppTypeEnum.Char or Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 or
            Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 or Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 or
            Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 or Il2CppTypeEnum.R4 or Il2CppTypeEnum.R8 };
        if (!method.IsStatic || !Scalar(method.ReturnType) || method.Parameters.Any(p => !Scalar(p.Type))) return false;
        // Numeric parameters may still contain an explicitly formed stack address: reject that case.
        return RuntimeNoStackAddress(call.In);
    }

    private bool RuntimeNoStackAddress(IEnumerable<Node> values)
    {
        var seen = new HashSet<Node>();
        var work = new Stack<Node>(values);
        while (work.TryPop(out Node? value))
        {
            if (!seen.Add(value)) continue;
            if (seen.Count > 2048 || value.Op == Op.Param && value.Imm == _fn.Regs.StackPointer) return false;
            foreach (Node input in value.In) work.Push(input);
        }
        return true;
    }

    private bool RuntimePrefixKeepsFramePrivate(int before)
    {
        // A later scalar call is safe only while no earlier instruction could have exported this
        // frame's address. The canary store does not erase an escape that happened before it.
        if (_fn.Entry.Preds.Count != 0) return false;
        for (int i = 0; i < before; i++)
        {
            Node node = _fn.Entry.Nodes[i];
            if (node.Dead) continue;
            if (node.Op == Op.Store)
            {
                int bytes = node.In[1].Type.Bytes();
                if (!IsFrameAddress(node.In[0], out int at) || at >= 0 || bytes <= 0 ||
                    (long)at + bytes > 0 || !RuntimeNoStackAddress([node.In[1]])) return false;
            }
            else if (node.IsEffect && node.Op != Op.Load) return false;
        }
        return true;
    }

    private bool RuntimeWordIsConstant(Block readAt, int before, int offset, long value)
    {
        // Require the exact initialization in the entry block. All paths (including loop backedges)
        // from it to this read are checked for writes, so a cycle cannot manufacture a value proof.
        Node? initial = _fn.Entry.Nodes.FirstOrDefault(node => !node.Dead && node.Op == Op.Store &&
            node.In[1].Type == VT.I64 && node.In[1].IsConstValue(value) &&
            IsFrameAddress(node.In[0], out int at) && at == offset);
        if (initial == null || !_cfg.Dominates(_fn.Entry, readAt)) return false;
        int initialAt = _fn.Entry.Nodes.IndexOf(initial);
        if (ReferenceEquals(readAt, _fn.Entry) && before <= initialAt ||
            !RuntimePrefixKeepsFramePrivate(initialAt)) return false;
        var ancestors = new HashSet<Block>();
        var work = new Stack<Block>();
        work.Push(readAt);
        while (work.TryPop(out Block? block))
        {
            if (!_cfg.IsReachable(block) || !ancestors.Add(block)) continue;
            if (block.Scope != readAt.Scope) return false;
            foreach (Block previous in block.Preds)
            {
                // If this read itself is in a cycle, instructions after it may affect a later read.
                // This exit-word proof does not model that case; keep the real failure branch.
                if (ReferenceEquals(previous, readAt)) return false;
                work.Push(previous);
            }
        }
        foreach (Block block in ancestors)
        {
            int start = ReferenceEquals(block, _fn.Entry) ? initialAt + 1 : 0;
            int end = ReferenceEquals(block, readAt) ? before : block.Nodes.Count;
            for (int i = start; i < end; i++)
            {
                Node node = block.Nodes[i];
                if (node.Dead) continue;
                if (node.Op == Op.Store)
                {
                    if (!IsFrameAddress(node.In[0], out int at)) return false;
                    int size = node.In[1].Type.Bytes();
                    if (size <= 0 || (long)at < (long)offset + 8 && (long)offset < (long)at + size) return false;
                }
                else if (node.Op is Op.Call or Op.TailCall)
                {
                    if (!RuntimeWriteOutside(node, offset) && !ScalarManagedCall(node)) return false;
                }
            }
        }
        return true;
    }

    private void PlanRuntimeStackGuards()
    {
        if (!_abi.UsesFullySharedRuntime || _fn.TryRegions.Count != 0) return;
        foreach (Block block in _cfg.ReversePostOrder)
        {
            if (block.Terminator is not { Op: Op.Branch } branch || block.Succs.Count != 2 ||
                branch.In[0] is not { Op: Op.CmpNe } compare) continue;
            Node constant = compare.In[0], load = compare.In[1];
            if (!constant.IsConst) (constant, load) = (load, constant);
            if (!constant.IsConstValue(0x5354414B47554152) ||
                load is not { Op: Op.Load, Type: VT.I64, Block: { } readAt } ||
                !IsFrameAddress(load.In[0], out int slot)) continue;
            Block failure = block.Succs[0];
            if (failure.Phis.Any(p => !p.Dead) || failure.Succs.Count != 0 ||
                failure.Nodes.Count(n => !n.Dead && n.Op == Op.Call) != 1 ||
                failure.Nodes.Any(n => !n.Dead && n.Op is not (Op.Call or Op.Unreachable)) ||
                failure.Nodes.First(n => !n.Dead && n.Op == Op.Call).Aux is not CallInfo { Indirect: false, NoReturn: true } call ||
                _p.Helpers.KindAt(call.Target) != HelperKind.StackCheckFail) continue;
            // Every predecessor path must still contain that exact stored word. Unknown writes/calls,
            // partial overwrites and exception regions all keep the real failure branch.
            if (!RuntimeWordIsConstant(readAt, readAt.Nodes.IndexOf(load), slot, constant.Imm)) continue;
            _runtimeStackGuards.Add(block);
            _h.Notes.Add($"constant stack protector proved at 0x{branch.Addr:X}");
        }
        if (_runtimeStackGuards.Count == 0 && _runtimeMarshalGuards.Count == 0) return;
        _runtimeReachable = [];
        var work = new Stack<Block>();
        work.Push(_fn.Entry);
        while (work.TryPop(out Block? block))
        {
            if (!_runtimeReachable.Add(block)) continue;
            if (_runtimeStackGuards.Contains(block)) work.Push(block.Succs[1]);
            else if (_runtimeMarshalGuards.Contains(block)) work.Push(block.Succs[0]);
            else foreach (Block successor in block.Succs) work.Push(successor);
        }
    }
}
