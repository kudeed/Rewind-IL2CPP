using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>Recover List.Clear's reference-free value-element fast path.
/// Unknown layouts, observable snapshots, callbacks and ambiguous receivers remain explicit.</summary>
internal static class ListValueClearFolding
{
    private static bool Number(HExpr e, int n) => e is HConst c &&
        (c.Value is int i && i == n || c.Value is long l && l == n);
    private static bool Int(TypeSig t) => t is PrimitiveSig { Element: Il2CppTypeEnum.I4 };
    private static bool Local(HExpr? e, HVar v) => e is HLocal l && l.Variable == v;

    private static bool ReferenceFree(TypeSig type, LayoutCalculator layouts, HashSet<string> visiting)
    {
        if (type.ContainsGenericParameter) return false;
        if (type is PrimitiveSig p) return p.Element is Il2CppTypeEnum.Boolean or Il2CppTypeEnum.Char or
            Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 or Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 or
            Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 or Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 or
            Il2CppTypeEnum.I or Il2CppTypeEnum.U or Il2CppTypeEnum.R4 or Il2CppTypeEnum.R8;
        if (!type.IsValueType || type is not (TypeDefSig or GenericInstSig) ||
            type.Definition == null || !visiting.Add(type.Key)) return false;
        try
        {
            if (type.Definition.IsEnum) return type.Definition.EnumUnderlyingType is { } underlying &&
                ReferenceFree(underlying, layouts, visiting);
            var layout = layouts.Of(type);
            return layout.Known && layout.Size > 0 &&
                layout.Fields.All(f => ReferenceFree(f.Type, layouts, visiting));
        }
        finally { visiting.Remove(type.Key); }
    }

    internal static bool TryFold(HMethod h, SigFactory sigs, LayoutCalculator layouts, HBlock block, int at)
    {
        if (h.Method == null || h.Method.IsStatic || h.Method.DeclaringType.IsValueType ||
            h.Method.GenericParameters.Length != 0 || h.TryRegions.Count != 0 ||
            h.Blocks.Count == 0 || h.Blocks.Any(b => b.Scope != -1) ||
            at < 0 || at + 2 >= block.Statements.Count ||
            block.Statements[at] is not HAssign { Target: HLocal snapshot, Value: HField { Object: HLocal list } prior } ||
            list.Variable.Type is not GenericInstSig g || g.Definition.FullName != "System.Collections.Generic.List" ||
            g.Definition.Assembly.Name is not ("mscorlib" or "System.Private.CoreLib") ||
            g.Arguments.Length != 1 || !g.Arguments[0].IsValueType ||
            !ReferenceFree(g.Arguments[0], layouts, []) ||
            list.Variable.AddressTaken || snapshot.Variable.AddressTaken ||
            !Int(snapshot.Variable.Type) || snapshot.Variable == list.Variable) return false;
        bool Field(HField f, string name) => f.Field.Name == name && !f.Field.IsStatic &&
            f.Field.DeclaringType == g.Definition && f.DeclaringType?.Key == g.Key && Local(f.Object, list.Variable);
        if (!Field(prior, "_version") || !Int(prior.Field.Type)) return false;
        int write = at + 1;
        if (block.Statements[write] is HAssign { Target: HLocal temp, Value: HField { Object: HArg { Index: -1 } } ownerRead })
        {
            // Only an independent, ordinary read from the same owner field already read at entry.
            // Entry's first statement proves this nonnull before every reachable candidate.
            if (temp.Variable == list.Variable || temp.Variable == snapshot.Variable ||
                ownerRead.Field.IsStatic || ownerRead.Field.DeclaringType != h.Method.DeclaringType ||
                h.Blocks[0].Statements.FirstOrDefault() is not HAssign
                    { Target: HLocal, Value: HField { Object: HArg { Index: -1 } } entryRead } ||
                entryRead.Field != ownerRead.Field) return false;
            write++;
        }
        if (write + 1 >= block.Statements.Count ||
            block.Statements[write] is not HAssign { Target: HField size, Value: var zero } ||
            block.Statements[write + 1] is not HAssign { Target: HField version, Value: HBinary
                { Op: HBinaryOp.Add, Left: HLocal saved, Right: var one } } ||
            !Field(size, "_size") || !Int(size.Field.Type) || !Number(zero, 0) ||
            !Field(version, "_version") || version.Field != prior.Field ||
            saved.Variable != snapshot.Variable || !Number(one, 1)) return false;
        foreach (var b in h.Blocks)
        foreach (var statement in b.Statements)
            if (!ReferenceEquals(statement, block.Statements[at]) &&
                !ReferenceEquals(statement, block.Statements[write + 1]) &&
                ConstructorFolding.Mentions(statement, snapshot.Variable)) return false;
        var methods = g.Definition.Methods.Where(m => m.Name == "Clear" && !m.IsStatic &&
            m.GenericParameters.Length == 0 && m.Parameters.Length == 0 && m.ReturnType.IsVoid &&
            (m.Flags & MethodDef.AccessMask) == 6).ToArray();
        if (methods.Length != 1) return false;
        var call = new HEval(new HCall { Method = methods[0], DeclaringType = g, This = list, Type = methods[0].ReturnType })
            { Address = block.Statements[at].Address };
        block.Statements.RemoveRange(write, 2);
        block.Statements[at] = call;
        h.Locals.Remove(snapshot.Variable);
        h.Notes.Add($"public List.Clear restored from reference-free value tail at 0x{call.Address:X}");
        return true;
    }

    internal static void Run(HMethod h, SigFactory sigs, LayoutCalculator layouts)
    {
        if (Environment.GetEnvironmentVariable("REWIND_NO_LIST_VALUE_CLEAR_FOLDING") != null) return;
        foreach (var block in h.Blocks)
            for (int at = 0; at < block.Statements.Count; at++) TryFold(h, sigs, layouts, block, at);
    }
}
