using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// The order in which an inlined wrapper first reads its parameters need not be their declaration order.
/// A scalar expression may cross another argument only when it cannot throw, observe mutable memory, or
/// change value over the folded region. Calls and other observable computations retain their relative order.
/// </summary>
internal static class InlineArgumentOrder
{
    internal static bool Preserves(IReadOnlyList<int> order, IReadOnlyList<HExpr?> arguments,
        HMethod method, IReadOnlyList<HStmt> site, int first, int last)
    {
        if (first < 0 || last < first || last >= site.Count) return false;
        var seen = new HashSet<int>();
        foreach (int index in order)
            if (index < 0 || index >= arguments.Count || !seen.Add(index)) return false;
        var movable = new Dictionary<int, bool>();
        bool CanMove(int index)
        {
            if (movable.TryGetValue(index, out bool known)) return known;
            var locals = new HashSet<HVar>();
            bool safe = Scalar(arguments[index], locals);
            if (safe && locals.Count != 0)
            {
                // In addition to AddressTaken, check actual address expressions. A preexisting alias may
                // otherwise let a call modify a scalar that looks like an independent value here.
                foreach (HBlock block in method.Blocks)
                    foreach (HStmt statement in block.Statements)
                        FinallyFolding.Visit(statement, expression =>
                        {
                            if (!safe || expression is not HAddressOf address) return;
                            foreach (HVar local in locals)
                                if (ConstructorFolding.Mentions(address.Target, local)) { safe = false; break; }
                        });
                for (int at = first; at <= last && safe; at++)
                    if (site[at] is HAssign assignment)
                        foreach (HVar local in locals)
                            if (ConstructorFolding.Mentions(assignment.Target, local)) { safe = false; break; }
            }
            movable[index] = safe;
            return safe;
        }
        // Considering every inversion also catches two calls separated by an inert argument.
        for (int a = 0; a < order.Count; a++)
            for (int b = a + 1; b < order.Count; b++)
                if (order[a] > order[b] && !CanMove(order[a]) && !CanMove(order[b])) return false;
        return true;
    }

    private static bool Primitive(TypeSig? type) => type is PrimitiveSig { Element:
        Il2CppTypeEnum.Boolean or Il2CppTypeEnum.Char or Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 or
        Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 or Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 or
        Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 or Il2CppTypeEnum.I or Il2CppTypeEnum.U or
        Il2CppTypeEnum.R4 or Il2CppTypeEnum.R8 };

    private static bool Scalar(HExpr? expression, HashSet<HVar> locals)
    {
        if (expression is HLocal local)
        {
            if (local.Variable.AddressTaken || !Primitive(local.Variable.Type) ||
                (local.Type != null && local.Type.Key != local.Variable.Type.Key)) return false;
            locals.Add(local.Variable);
            return true;
        }
        if (expression == null || !Primitive(expression.Type)) return false;
        return expression switch
        {
            HConst constant => constant.Value is bool or char or sbyte or byte or short or ushort or int or uint or long or ulong or float or double,
            HUnary unary => Scalar(unary.Operand, locals),
            HBinary binary => HirBuilder.IsPure(binary) && Scalar(binary.Left, locals) && Scalar(binary.Right, locals),
            HCompare comparison => Scalar(comparison.Left, locals) && Scalar(comparison.Right, locals),
            HConv conversion => HirBuilder.IsPure(conversion) && Scalar(conversion.Operand, locals),
            _ => false,
        };
    }
}
