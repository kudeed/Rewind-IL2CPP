using Rewind.Runtime;
using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>Removes scalar computations whose dependency cycles reach no observable use.</summary>
public static class HirDeadScalarCycles
{
    private static bool Scalar(TypeSig? type) => type is PrimitiveSig { Element:
        Il2CppTypeEnum.Boolean or Il2CppTypeEnum.Char or Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 or
        Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 or Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 or
        Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 or Il2CppTypeEnum.I or Il2CppTypeEnum.U or
        Il2CppTypeEnum.R4 or Il2CppTypeEnum.R8 };

    private static bool PureScalar(HExpr value)
    {
        var todo = new Stack<HExpr>(); var seen = new HashSet<HExpr>(); todo.Push(value);
        while (todo.TryPop(out HExpr? e))
        {
            if (!seen.Add(e)) continue;
            switch (e)
            {
                case HConst { Value: bool or char or sbyte or byte or short or ushort or int or uint or long or ulong or float or double }: break;
                case HLocal local when Scalar(local.Variable.Type): break;
                case HArg when Scalar(e.Type): break;
                case HUnary unary when unary.Op is HUnaryOp.Neg or HUnaryOp.Not or HUnaryOp.LogicalNot: todo.Push(unary.Operand); break;
                case HBinary binary when binary.Op is HBinaryOp.Add or HBinaryOp.Sub or HBinaryOp.Mul or HBinaryOp.And or
                    HBinaryOp.Or or HBinaryOp.Xor or HBinaryOp.Shl or HBinaryOp.Shr or HBinaryOp.ShrUn:
                    todo.Push(binary.Left); todo.Push(binary.Right); break;
                case HCompare compare: todo.Push(compare.Left); todo.Push(compare.Right); break;
                case HConv convert when convert.Kind >= HConvKind.I1 && convert.Kind < HConvKind.OvfI1: todo.Push(convert.Operand); break;
                case HSelect select: todo.Push(select.Condition); todo.Push(select.WhenTrue); todo.Push(select.WhenFalse); break;
                case HOpaque { Text: "undefined" } opaque:
                    foreach (HExpr input in opaque.Operands) todo.Push(input);
                    break;
                default: return false;
            }
        }
        return true;
    }

    private static bool Reads(HExpr? value, HashSet<HVar> locals)
    {
        if (value == null) return true;
        var todo = new Stack<HExpr>(); var seen = new HashSet<HExpr>(); todo.Push(value);
        void Push(HExpr? e) { if (e != null) todo.Push(e); }
        while (todo.TryPop(out HExpr? e))
        {
            if (!seen.Add(e)) continue;
            switch (e)
            {
                case HLocal local: locals.Add(local.Variable); break;
                case HConst or HArg or HMethodPointer or HMemberToken: break;
                case HField field: Push(field.Object); break;
                case HElement element: Push(element.Array); Push(element.Index); break;
                case HArrayLength length: Push(length.Array); break;
                case HAddressOf address: Push(address.Target); break;
                case HDeref dereference: Push(dereference.Pointer); break;
                case HUnary unary: Push(unary.Operand); break;
                case HBinary binary: Push(binary.Left); Push(binary.Right); break;
                case HCompare compare: Push(compare.Left); Push(compare.Right); break;
                case HConv convert: Push(convert.Operand); break;
                case HCall call:
                    Push(call.This); foreach (HExpr input in call.Arguments) Push(input);
                    break;
                case HNewObject creation: foreach (HExpr input in creation.Arguments) Push(input); break;
                case HNewArray array: Push(array.Length); break;
                case HTypeExpr type: Push(type.Operand); break;
                case HCachedDelegate cached: Push(cached.Cache); Push(cached.Creation); break;
                case HSelect select: Push(select.Condition); Push(select.WhenTrue); Push(select.WhenFalse); break;
                case HOpaque { Text: "undefined" } opaque:
                    foreach (HExpr input in opaque.Operands) Push(input);
                    break;
                // Unknown native expressions may conceal memory aliases. Keep the original method intact.
                default: return false;
            }
        }
        return true;
    }

    public static int Run(HMethod method)
    {
        if (method.UnidentifiedNativeCalls.Count != 0) return 0;
        var roots = new HashSet<HVar>();
        var dependencies = new Dictionary<HVar, HashSet<HVar>>();
        var candidates = new HashSet<HAssign>();
        foreach (HTryRegion region in method.TryRegions.Values)
            if (region.Exception is { } exception) roots.Add(exception);
        foreach (HStmt statement in method.Blocks.SelectMany(b => b.Statements))
        {
            var reads = new HashSet<HVar>();
            switch (statement)
            {
                case HAssign { Target: HLocal local } assign:
                    if (!Reads(assign.Value, reads)) return 0;
                    if (Scalar(local.Variable.Type) && PureScalar(assign.Value))
                    {
                        if (!dependencies.TryGetValue(local.Variable, out var inputs)) dependencies[local.Variable] = inputs = [];
                        inputs.UnionWith(reads); candidates.Add(assign);
                        continue;
                    }
                    break;
                case HAssign assign:
                    if (!Reads(assign.Target, reads) || !Reads(assign.Value, reads)) return 0;
                    break;
                case HEval eval: if (!Reads(eval.Expression, reads)) return 0; break;
                case HReturn result: if (!Reads(result.Value, reads)) return 0; break;
                case HThrow throwing: if (!Reads(throwing.Exception, reads)) return 0; break;
                case HBranch branch: if (!Reads(branch.Condition, reads)) return 0; break;
                case HSwitch choice: if (!Reads(choice.Value, reads)) return 0; break;
                case HJump or HEndFinally: break;
                default: return 0;
            }
            roots.UnionWith(reads);
        }
        var live = new HashSet<HVar>(roots); var work = new Stack<HVar>(roots);
        while (work.TryPop(out HVar? local))
            if (dependencies.TryGetValue(local, out var inputs))
                foreach (HVar input in inputs) if (live.Add(input)) work.Push(input);
        int removed = 0;
        // Frame locals carry AddressTaken even without an emitted address use. Every actual address expression
        // above is an observable root; neither flags nor an unrecognized native pointer substitute for that proof.
        foreach (HBlock block in method.Blocks)
            removed += block.Statements.RemoveAll(s => s is HAssign { Target: HLocal local } assign &&
                candidates.Contains(assign) && !live.Contains(local.Variable));
        if (removed != 0) method.Notes.Add($"unobserved pure scalar assignments removed after dependency-cycle proof: {removed}");
        return removed;
    }
}
