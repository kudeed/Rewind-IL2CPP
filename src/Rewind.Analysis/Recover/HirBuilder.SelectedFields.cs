using System.Runtime.CompilerServices;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Model;
using Rewind.Runtime;

[assembly: InternalsVisibleTo("SelectedObjectFieldSmoke")]

namespace Rewind.Analysis.Recover;

/// <summary>
/// A native conditional move can choose unrelated objects whose fields occupy the
/// same bytes. Keep each field attached to its own managed receiver; the selected
/// reference itself has no single class through which that access is valid.
/// </summary>
internal static class SelectedObjectFields
{
    internal static bool TryAddress(Node load, IReadOnlyDictionary<Node, List<Node>> uses,
        out Node choice, out int offset)
    {
        choice = null!;
        offset = 0;
        if (load.Op != Op.Load || load.In.Length != 1 || load.Block is not { Scope: -1 } block) return false;
        Node current = load.In[0], consumer = load;
        long displacement = 0;
        for (int depth = 0; depth < 8; depth++)
        {
            if (current.Dead || current.Type != VT.I64 || !ReferenceEquals(current.Block, block) ||
                !uses.TryGetValue(current, out List<Node>? readers) || readers.Count != 1 ||
                !ReferenceEquals(readers[0], consumer)) return false;
            if (current.Op == Op.Select)
            {
                if (current.In.Length != 3 || current.In[0].Type != VT.I1 ||
                    current.In[1].Type != VT.I64 || current.In[2].Type != VT.I64 ||
                    displacement is < 16 or > int.MaxValue) return false;
                int start = block.Nodes.IndexOf(current), end = block.Nodes.IndexOf(load);
                if (start < 0 || end <= start) return false;
                // Recreate the choice at its read only when no intervening operation
                // can observe state or change the operands' meaning.
                for (int i = start + 1; i < end; i++)
                    if (!block.Nodes[i].Dead && block.Nodes[i].IsEffect) return false;
                choice = current;
                offset = (int)displacement;
                return true;
            }
            Node next;
            long step;
            if (current.Op == Op.Add && current.In.Length == 2 && current.In[1].IsConst)
                (next, step) = (current.In[0], IrBuilder.SImm(current.In[1]));
            else if (current.Op == Op.Add && current.In.Length == 2 && current.In[0].IsConst)
                (next, step) = (current.In[1], IrBuilder.SImm(current.In[0]));
            else if (current.Op == Op.Sub && current.In.Length == 2 && current.In[1].IsConst)
            {
                if (IrBuilder.SImm(current.In[1]) == long.MinValue) return false;
                (next, step) = (current.In[0], -IrBuilder.SImm(current.In[1]));
            }
            else return false;
            try { displacement = checked(displacement + step); }
            catch (OverflowException) { return false; }
            consumer = current;
            current = next;
        }
        return false;
    }

    internal static bool StableReceiver(HExpr value) =>
        value is HArg || value is HLocal { Variable.AddressTaken: false } local &&
        local.Variable.Type.Key == local.Type?.Key;

    internal static HSelect? TryRead(HExpr condition, HExpr whenTrue, HExpr whenFalse,
        int offset, int size, Func<TypeSig, TypeLayout> layoutOf)
    {
        if (condition.Type is not PrimitiveSig { Element: Il2CppTypeEnum.Boolean } ||
            !StableReceiver(whenTrue) || !StableReceiver(whenFalse) ||
            whenTrue.Type is not TypeDefSig { Definition: { IsValueType: false, IsInterface: false, GenericParameters.Length: 0 } } firstType ||
            whenFalse.Type is not TypeDefSig { Definition: { IsValueType: false, IsInterface: false, GenericParameters.Length: 0 } } secondType ||
            firstType.Key == secondType.Key || size is not (1 or 2 or 4 or 8) || offset < 16) return null;

        HField? Field(HExpr receiver, TypeDefSig owner)
        {
            TypeLayout layout = layoutOf(owner);
            if (!layout.Known) return null;
            FieldSlot[] touching = layout.Fields.Where(f =>
                (long)f.Offset < (long)offset + size && (long)offset < (long)f.Offset + f.Size).ToArray();
            if (touching.Length != 1) return null;
            FieldSlot slot = touching[0];
            if (slot.Offset != offset || slot.Size != size || slot.Field.IsStatic ||
                slot.Field.Offset != offset || !ReferenceEquals(slot.Field.DeclaringType, owner.Definition) ||
                slot.Type.Key != slot.Field.Type.Key || slot.Type.ContainsGenericParameter) return null;
            // A single native load is a whole scalar or reference, never an
            // inferred struct, raw pointer, open generic, or overlapping union.
            bool wholeScalar = slot.Type is PrimitiveSig primitive &&
                primitive.Element is not (Il2CppTypeEnum.Void or Il2CppTypeEnum.TypedByRef) &&
                primitive.SizeOf(8) == size;
            bool wholeReference = slot.Type is TypeDefSig { Definition: { IsValueType: false, GenericParameters.Length: 0 } } && size == 8;
            if (!wholeScalar && !wholeReference) return null;
            return new HField { Object = receiver, Field = slot.Field, DeclaringType = owner, Type = slot.Type };
        }

        HField? first = Field(whenTrue, firstType), second = Field(whenFalse, secondType);
        if (first == null || second == null || first.Type!.Key != second.Type!.Key) return null;
        // HSelect evaluates only its selected arm. In particular, no speculative
        // read of a null receiver is introduced.
        return new HSelect(condition, first, second) { Type = first.Type };
    }
}

public sealed partial class HirBuilder
{
    private static readonly bool NoSelectedObjectFields =
        Environment.GetEnvironmentVariable("REWIND_NO_SELECTED_OBJECT_FIELDS") != null;

    private Place? SelectedObjectFieldLoad(Node load)
    {
        if (NoSelectedObjectFields || _m.Image.Arch != Rewind.Binary.CpuArch.Arm64 || _ptr != 8 ||
            !SelectedObjectFields.TryAddress(load, _uses, out Node choice, out int offset) ||
            _materialize.Contains(choice)) return null;
        // Do not move, duplicate, or conditionally suppress the evaluation of
        // either native operand. Only arguments or already captured SSA locals
        // may become the receiver of a conditional field read.
        if (Eval(choice.In[1]) is not SVal first || !SelectedObjectFields.StableReceiver(first.Expr) ||
            Eval(choice.In[2]) is not SVal second || !SelectedObjectFields.StableReceiver(second.Expr)) return null;
        HSelect? selected = SelectedObjectFields.TryRead(Condition(choice.In[0]), first.Expr, second.Expr,
            offset, load.Type.Bytes(), _p.Layouts.Of);
        return selected == null ? null : new PChosenValue(selected);
    }
}
