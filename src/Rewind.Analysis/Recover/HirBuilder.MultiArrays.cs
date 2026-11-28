using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

public sealed partial class HirBuilder
{
    private sealed class MdArrayBounds(Node array, ArraySig type) : Sem
    {
        public readonly Node Array = array;
        public readonly ArraySig Type = type;
    }

    private sealed record MdArrayRead(Node Array, ArraySig ArrayType, HVar Local,
        int Dimension, bool LowerBound, Node? Row, Node? Column);

    private readonly Dictionary<Node, MdArrayRead> _mdArrayReads = [];
    private Cfg? _mdArrayCfg;
    private MethodDef? _mdGetValue, _mdGetLength, _mdGetLongLength, _mdGetLowerBound;
    private bool _mdArrayApiLooked;
    private readonly Node _mdZero = new() { Id = -1, Op = Op.Const, Type = VT.I32 };

    // Type queries only: never evaluate a native call projection or a field's current value here.
    private TypeSig? MdKnownType(Node node, int depth = 0)
    {
        if (depth > 12) return null;
        if (_sem.TryGetValue(node, out Sem? known) && known is SVal { Type: { } type }) return type;
        if (_phiVar.TryGetValue(node, out HVar? phi)) return phi.Type;
        if (node.Op == Op.Load && node.Type == VT.I64 &&
            MdBaseOffset(node.In[0], out Node owner, out long offset) &&
            offset is >= int.MinValue and <= int.MaxValue && MdKnownType(owner, depth + 1) is { } ownerType &&
            _p.Layouts.FieldAt(Declared(ownerType), (int)offset) is { } field &&
            field.Offset == offset && field.Size == _ptr) return field.Type;
        return null;
    }

    private bool MdReferenceArray(Node array, out ArraySig type)
    {
        type = null!;
        if (_ptr != 8 || _header != 16 || _m.Image.Arch != Rewind.Binary.CpuArch.Arm64 ||
            MdKnownType(array) is not ArraySig { Rank: 2 } candidate ||
            candidate.ElementType.ContainsGenericParameter || !IsReference(candidate.ElementType)) return false;
        type = candidate;
        return true;
    }

    private static bool MdBaseOffset(Node address, out Node basis, out long offset)
    {
        basis = address; offset = 0;
        int depth = 0;
        while (basis is { Op: Op.Add, Type: VT.I64 } && ++depth <= 8)
        {
            if (basis.In[1].IsConst) { offset += IrBuilder.SImm(basis.In[1]); basis = basis.In[0]; }
            else if (basis.In[0].IsConst) { offset += IrBuilder.SImm(basis.In[0]); basis = basis.In[1]; }
            else break;
        }
        return depth <= 8;
    }

    private static bool MdRawDimension(Node read, Node bounds, out int dimension, out bool lower)
    {
        dimension = -1; lower = false;
        if (read.Op != Op.Load || read.Type is not (VT.I32 or VT.I64) ||
            !MdBaseOffset(read.In[0], out Node basis, out long offset) || !ReferenceEquals(basis, bounds) ||
            offset is < 0 or > 24) return false;
        dimension = (int)(offset / 16);
        lower = offset % 16 == 8;
        return offset % 16 == 0 || lower && read.Type == VT.I32;
    }

    private bool MdBounds(Node node, out Node array, out ArraySig type)
    {
        array = null!; type = null!;
        if (node is not { Op: Op.Load, Type: VT.I64, Block: { } block } ||
            !MdBaseOffset(node.In[0], out array, out long offset) || offset != _header ||
            !MdReferenceArray(array, out type)) return false;
        // Replacing the native bounds pointer by its typed dimensions must not delay a null failure
        // past another observable operation. Its first following effect must dereference these bounds.
        for (int i = block.Nodes.IndexOf(node) + 1; i < block.Nodes.Count; i++)
        {
            Node next = block.Nodes[i];
            if (next.Dead || !next.IsEffect) continue;
            return MdRawDimension(next, node, out _, out _);
        }
        return false;
    }

    private bool MdDimension(Node value, out Node array, out ArraySig type, out int dimension, out bool lower)
    {
        array = null!; type = null!; dimension = -1; lower = false;
        while (value.Op is Op.Trunc or Op.ZExt && value.In.Length == 1 &&
            value.Type is VT.I32 or VT.I64 && value.In[0].Type is VT.I32 or VT.I64) value = value.In[0];
        if (value.Op != Op.Load || !MdBaseOffset(value.In[0], out Node bounds, out _) ||
            !MdBounds(bounds, out array, out type)) return false;
        return MdRawDimension(value, bounds, out dimension, out lower);
    }

    private bool MdArrayApi()
    {
        if (!_mdArrayApiLooked)
        {
            _mdArrayApiLooked = true;
            MethodDef? Find(string name, TypeSig returned, int parameters) =>
                _m.FindType("System.Array")?.Methods.SingleOrDefault(m => m.DeclaringType.Assembly.Name == "mscorlib" &&
                    m.DeclaringType.Namespace == "System" && m.DeclaringType.Name == "Array" &&
                    m.Name == name && !m.IsStatic && m.GenericParameters.Length == 0 &&
                    m.ReturnType.Key == returned.Key && m.Parameters.Length == parameters &&
                    m.Parameters.All(p => p.Type.Key == _int.Key));
            _mdGetValue = Find("GetValue", _object, 2);
            _mdGetLength = Find("GetLength", _int, 1);
            _mdGetLongLength = Find("GetLongLength", _long, 1);
            _mdGetLowerBound = Find("GetLowerBound", _int, 1);
        }
        return _mdGetValue != null && _mdGetLength != null && _mdGetLongLength != null && _mdGetLowerBound != null;
    }

    private bool MdSameIndex(Node addressIndex, Node checkedIndex, Block guard, Block success)
    {
        if (ReferenceEquals(addressIndex, checkedIndex)) return true;
        if (addressIndex.IsConst && checkedIndex.IsConst)
            return IrBuilder.SImm(addressIndex) == IrBuilder.SImm(checkedIndex);
        if (checkedIndex is { Op: Op.Trunc, Type: VT.I32 } && ReferenceEquals(checkedIndex.In[0], addressIndex) &&
            (MdCanonicalIndex(addressIndex) || MdLoopIndexFits32(addressIndex, guard, success))) return true;
        if (addressIndex.Type != VT.I64 || addressIndex.Op is not (Op.SExt or Op.ZExt) ||
            addressIndex.In[0].Type != VT.I32) return false;
        if (checkedIndex.Type == VT.I64 && checkedIndex.Op is Op.SExt or Op.ZExt &&
            checkedIndex.In[0].Type == VT.I32) checkedIndex = checkedIndex.In[0];
        return SameRuntimeIndex32(addressIndex.In[0], checkedIndex);
    }

    private bool MdLoopIndexFits32(Node index, Block guard, Block success)
    {
        // A 64-bit loop counter is not generally bounded by checking its low word. This narrow
        // induction starts at zero and increments once, only after this unsigned array bound holds.
        // Given a 32-bit counter, success means counter < Length <= Int32.MaxValue; +1 still fits.
        if (index is not { Op: Op.Phi, Type: VT.I64, Block: { Preds.Count: 2 } header } || index.In.Length != 2)
            return false;
        Cfg cfg = _mdArrayCfg ??= new Cfg(_fn);
        for (int entry = 0; entry < 2; entry++)
        {
            Node increment = index.In[1 - entry];
            if (!index.In[entry].IsConstValue(0) || increment is not { Op: Op.Add, Type: VT.I64, Block: { } step } ||
                !ReferenceEquals(increment.In[0], index) || !increment.In[1].IsConstValue(1) ||
                !ReferenceEquals(header.Preds[1 - entry], step) || step.Succs.Count != 1 ||
                !ReferenceEquals(step.Succs[0], header) || !cfg.Dominates(header, guard) ||
                !cfg.Dominates(success, step)) continue;
            return true;
        }
        return false;
    }

    private bool MdIndexInRange(Node array, Node index, int dimension, Block use)
    {
        Cfg cfg = _mdArrayCfg ??= new Cfg(_fn);
        foreach (Block guard in cfg.ReversePostOrder)
        {
            if (guard.Scope != use.Scope || guard.Terminator is not { Op: Op.Branch } branch ||
                guard.Succs.Count != 2 || ReferenceEquals(guard.Succs[0], guard.Succs[1])) continue;
            Block success = guard.Succs[1];
            if (success.Preds.Count != 1 || !ReferenceEquals(success.Preds[0], guard) ||
                !cfg.Dominates(guard, use) || !cfg.Dominates(success, use)) continue;
            Node compare = branch.In[0];
            if (compare.Op is not (Op.CmpLeU or Op.CmpEq)) continue;
            Node length = compare.In[0], checkedIndex = compare.In[1];
            if (length.Type is not (VT.I32 or VT.I64) || checkedIndex.Type != length.Type) continue;
            if (compare.Op == Op.CmpEq && length.IsConstValue(0)) (length, checkedIndex) = (checkedIndex, length);
            if (compare.Op == Op.CmpEq && (!index.IsConstValue(0) || !checkedIndex.IsConstValue(0))) continue;
            if (!MdDimension(length, out Node owner, out _, out int dim, out bool lower) ||
                lower || dim != dimension || !ReferenceEquals(owner, array)) continue;
            if (compare.Op == Op.CmpEq || MdSameIndex(index, checkedIndex, guard, success)) return true;
        }
        return false;
    }

    private bool MdElement(Node read, out Node array, out ArraySig type, out Node row, out Node column)
    {
        array = null!; type = null!; row = column = _mdZero;
        if (read is not { Op: Op.Load, Type: VT.I64, Block: { } block }) return false;
        long offset = 0;
        var terms = new List<(Node Node, long Scale)>();
        var work = new Stack<(Node Node, long Scale)>(); work.Push((read.In[0], 1));
        int budget = 64;
        while (work.TryPop(out var item))
        {
            if (--budget < 0) return false;
            Node n = item.Node; long scale = item.Scale;
            if (n.IsConst) offset += scale * IrBuilder.SImm(n);
            else if (n is { Op: Op.Add, Type: VT.I64 }) { work.Push((n.In[0], scale)); work.Push((n.In[1], scale)); }
            else if (n is { Op: Op.Shl, Type: VT.I64 } && n.In[1].IsConstValue(3)) work.Push((n.In[0], scale * 8));
            else if (n is { Op: Op.Mul, Type: VT.I64 } && n.In[1].IsConstValue(8)) work.Push((n.In[0], scale * 8));
            else terms.Add(item);
        }
        if (offset != _header + 2 * _ptr) return false;
        int baseAt = terms.FindIndex(t => t.Scale == 1 && MdReferenceArray(t.Node, out _));
        if (baseAt < 0) return false;
        array = terms[baseAt].Node;
        if (!MdReferenceArray(array, out type)) return false;
        terms.RemoveAt(baseAt);
        if (terms.Count > 2 || terms.Any(t => t.Scale != _ptr)) return false;
        bool haveRow = false, haveColumn = false;
        foreach (var term in terms)
        {
            Node value = term.Node; Node? multipliedRow = null;
            if (value is { Op: Op.Mul, Type: VT.I64 })
                for (int side = 0; side < 2; side++)
                    if (value.In[side].Type == VT.I64 &&
                        MdDimension(value.In[side], out Node owner, out _, out int dimension, out bool lower) &&
                        !lower && dimension == 1 && ReferenceEquals(owner, array))
                        multipliedRow = value.In[1 - side];
            if (multipliedRow != null)
            {
                if (haveRow) return false; haveRow = true; row = multipliedRow;
            }
            else
            {
                if (haveColumn) return false; haveColumn = true; column = value;
            }
        }
        return MdIndexInRange(array, row, 0, block) && MdIndexInRange(array, column, 1, block);
    }

    private MdArrayRead? MdReadPlan(Node read)
    {
        if (_mdArrayReads.TryGetValue(read, out MdArrayRead? prior)) return prior;
        if (read.Op != Op.Load) return null;
        MdArrayRead? plan = null;
        if (MdDimension(read, out Node array, out ArraySig type, out int dimension, out bool lower))
        {
            if (!MdArrayApi()) return null;
            TypeSig result = read.Type == VT.I32 ? _int : _long;
            plan = new MdArrayRead(array, type, _h.NewLocal(result, "dimension"), dimension, lower, null, null);
        }
        else if (MdElement(read, out array, out type, out Node row, out Node column))
        {
            if (!MdArrayApi()) return null;
            plan = new MdArrayRead(array, type, _h.NewLocal(type.ElementType, "element"), -1, false, row, column);
        }
        if (plan != null) _mdArrayReads.Add(read, plan);
        return plan;
    }

    private Sem? MdArrayLoad(Node read)
    {
        if (MdBounds(read, out Node array, out ArraySig type)) return new MdArrayBounds(array, type);
        if (MdReadPlan(read) is not { } plan) return null;
        // The local is assigned by ProcessBlock at this exact native load, even if type planning
        // encounters it earlier. Neither array values nor future index call results are evaluated here.
        return new SVal(new HLocal(plan.Local) { Type = plan.Local.Type });
    }

    private HCall MdDimensionCall(HExpr array, MethodDef method, int dimension) =>
        new() { Method = method, This = array, Arguments = [new HConst(dimension, _int)], Type = method.ReturnType };

    private static bool MdCanonicalIndex(Node node)
    {
        if (node.Type == VT.I32) return true;
        if (node.Type != VT.I64) return false;
        if (node.Op is Op.SExt or Op.ZExt && node.In[0].Type == VT.I32) return true;
        if (node.Op == Op.ShrU && node.In[1].IsConst && node.In[1].UImm is >= 32 and < 64) return true;
        if (node.Op == Op.And && node.In[1].IsConst && node.In[1].UImm <= uint.MaxValue) return true;
        return node.IsConst && (node.UImm <= uint.MaxValue || IrBuilder.SImm(node) is >= int.MinValue and < 0);
    }

    private HExpr MdElementRead(HExpr array, ArraySig type, HExpr row, HExpr column, ulong address)
    {
        // Native arguments have already been produced before its first bounds/null dereference.
        // Capturing non-stable values here prevents receiver duplication and keeps a final index
        // producer ahead of the new GetLowerBound calls (including their possible null failure).
        HExpr Capture(HExpr value, string name)
        {
            if (value is HArg or HLocal or HConst) return value;
            HVar held = _h.NewLocal(value.Type ?? _int, name);
            var local = new HLocal(held) { Type = held.Type };
            Emit(new HAssign(local, value), address);
            return local;
        }
        array = Capture(array, "array");
        row = Capture(row, "row");
        column = Capture(column, "column");
        HExpr Adjust(HExpr index, int dimension)
        {
            HExpr logical = index.Type?.Key == _int.Key ? index : new HConv(HConvKind.I4, index) { Type = _int };
            return new HBinary(HBinaryOp.Add, logical, MdDimensionCall(array, _mdGetLowerBound!, dimension)) { Type = _int };
        }
        var value = new HCall { Method = _mdGetValue!, This = array,
            Arguments = [Adjust(row, 0), Adjust(column, 1)], Type = _object };
        return new HTypeExpr(HTypeOp.CastClass, type.ElementType, value) { Type = type.ElementType };
    }

    private bool TryEmitMdArrayRead(Node read)
    {
        if (MdReadPlan(read) is not { } plan) return false;
        HExpr array = Value(plan.Array);
        HExpr value = plan.Dimension >= 0
            ? MdDimensionCall(array, plan.LowerBound ? _mdGetLowerBound! : read.Type == VT.I32 ? _mdGetLength! : _mdGetLongLength!, plan.Dimension)
            : MdElementRead(array, plan.ArrayType, IntValue(plan.Row!), IntValue(plan.Column!), read.Addr);
        var local = new HLocal(plan.Local) { Type = plan.Local.Type };
        Emit(new HAssign(local, value), read.Addr);
        _sem[read] = new SVal(local);
        return true;
    }
}
