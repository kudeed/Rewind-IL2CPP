using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Evidence that the immediately preceding managed reference store already performs the GC barrier.
/// No expression is evaluated here. A raw pointer, struct copy or unknown store never supplies evidence.
/// </summary>
internal static class ManagedStoreBarrierProof
{
    internal sealed record Witness(Node Store, Node Address, Node StoredValue, HAssign Assignment, HExpr Target, HExpr Value);

    internal static Witness? Record(Node store, HAssign assignment) =>
        store is { Op: Op.Store, Dead: false, In.Length: 2 } && store.In[1].Type == VT.I64 &&
        ReferenceLocation(assignment.Target) ? new(store, store.In[0], store.In[1], assignment, assignment.Target, assignment.Value) : null;

    internal static bool CanElide(Witness? witness, Node call, Node? address, HBlock current,
        bool managedVoid, Func<Node, bool> used)
    {
        if (witness == null || address == null || call.Dead || call.Op is not (Op.Call or Op.TailCall) ||
            call.Aux is not CallInfo { Indirect: false, Intrinsic: null, NoReturn: false } info ||
            call.In.Length != 1 || info.Slots.Count != 1 || info.Slots[0] != new ArgSlot(ArgSlotKind.IntReg, 0) ||
            !ReferenceEquals(call.In[0], address) ||
            call.Op == Op.TailCall && !managedVoid || call.Block is not { } block ||
            witness.Store.Dead || !ReferenceEquals(witness.Store.Block, block) ||
            witness.Store.Op != Op.Store || witness.Store.In.Length != 2 ||
            !ReferenceEquals(witness.Store.In[0], witness.Address) || !ReferenceEquals(witness.Address, address) ||
            !ReferenceEquals(witness.Store.In[1], witness.StoredValue) || witness.StoredValue.Type != VT.I64 ||
            !ReferenceEquals(witness.Assignment.Target, witness.Target) ||
            !ReferenceEquals(witness.Assignment.Value, witness.Value) || !ReferenceLocation(witness.Target) ||
            current.Statements.Count == 0 || !ReferenceEquals(current.Statements[^1], witness.Assignment)) return false;
        int before = block.Nodes.IndexOf(witness.Store), after = block.Nodes.IndexOf(call);
        if (before < 0 || after <= before) return false;
        for (int i = before + 1; i < after; i++)
            if (!block.Nodes[i].Dead && block.Nodes[i].IsEffect) return false;
        // The native mark-only function leaves x0 intact, although its semantic signature is void.
        // A consumer of that physical register is unsupported here and must retain the opaque call.
        foreach (Node n in block.Nodes)
            if (n.Op == Op.Proj && n.In.Length == 1 && ReferenceEquals(n.In[0], call) && used(n)) return false;
        return true;
    }

    private static bool SameType(TypeSig? first, TypeSig? second) =>
        first != null && second != null && first.Key == second.Key;

    private static TypeSig? StableType(HExpr expression) => expression switch
    {
        HArg a => a.Type,
        HLocal l when SameType(l.Type, l.Variable.Type) => l.Variable.Type,
        _ => null,
    };

    private static bool ReferenceType(TypeSig? type) => type switch
    {
        PrimitiveSig p => p.Element is Il2CppTypeEnum.String or Il2CppTypeEnum.Object,
        SzArraySig or ArraySig => true,
        TypeDefSig or GenericInstSig => type.Definition != null && !type.IsValueType,
        _ => false,
    };

    private static bool ReferenceLocation(HExpr expression) => ReferenceType(expression.Type) && (expression switch
    {
        // An annotation alone does not turn an integer field into a GC slot. Generic owner fields
        // need an exact substitution proof; this narrow rule leaves them unconsumed for now.
        HField f when f.Field is { DeclaringType: { GenericParameters.Length: 0 } } &&
            f.DeclaringType is not GenericInstSig && ReferenceType(f.Field.Type) && SameType(f.Field.Type, f.Type) =>
            f.Field.IsStatic ? f.Object == null : f.Object != null && ReferenceType(StableType(f.Object)),
        HElement e => StableType(e.Array) is SzArraySig array && ReferenceType(array.ElementType) &&
            SameType(array.ElementType, e.Type) &&
            (StableType(e.Index) is PrimitiveSig { Element: Il2CppTypeEnum.I4 } ||
                e.Index is HConst { Value: int, Type: PrimitiveSig { Element: Il2CppTypeEnum.I4 } }),
        _ => false,
    });
}
