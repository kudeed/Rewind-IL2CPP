using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>Restore the subtype of an unchanged object argument only where a successful native type-test edge dominates the call.</summary>
public static class TypeTestReceiverCasts
{
    private static IEnumerable<HBlock> Successors(HBlock block) => block.Statements.LastOrDefault() switch
    {
        HBranch b => [b.WhenTrue, b.WhenFalse],
        HJump j => [j.Target],
        HSwitch s => s.Targets.Append(s.Default),
        _ => [],
    };

    public static int Run(HMethod method)
    {
        if (method.Blocks.Count == 0 || method.TryRegions.Count != 0 || method.Blocks.Any(b => b.Scope != -1)) return 0;
        var blocks = method.Blocks.ToHashSet();
        if (blocks.Count != method.Blocks.Count || blocks.Any(b => Successors(b).Any(s => !blocks.Contains(s)))) return 0;
        HashSet<HBlock> Reachable(HBlock? omitFrom = null, HBlock? omitTo = null)
        {
            var seen = new HashSet<HBlock>(); var work = new Stack<HBlock>(); work.Push(method.Blocks[0]);
            while (work.TryPop(out var b))
            {
                if (!seen.Add(b)) continue;
                foreach (var next in Successors(b)) if (b != omitFrom || next != omitTo) work.Push(next);
            }
            return seen;
        }
        var reachable = Reachable(); int changed = 0;
        foreach (var guard in method.Blocks)
        {
            if (!reachable.Contains(guard) || guard.Statements.LastOrDefault() is not HBranch branch || branch.WhenTrue == branch.WhenFalse ||
                branch.Condition is not HCompare { Op: HCompareOp.Eq or HCompareOp.Ne } compare) continue;
            HTypeExpr? test = compare.Left is HTypeExpr left && compare.Right is HConst { Value: null } ? left :
                compare.Right is HTypeExpr right && compare.Left is HConst { Value: null } ? right : null;
            if (test is not { Op: HTypeOp.IsInst, Operand: HArg argument, Target: TypeDefSig { Definition: { IsValueType: false, IsInterface: false, IsGenericDefinition: false } tested } }) continue;
            TypeSig? sourceType = argument.Index == -1 ? (method.Method.IsStatic ? null : method.Method.DeclaringType.Sig) :
                argument.Index >= 0 && argument.Index < method.Method.Parameters.Length ? method.Method.Parameters[argument.Index].Type : null;
            if (sourceType is not TypeDefSig { Definition: { IsValueType: false, IsInterface: false, IsGenericDefinition: false } source } ||
                !ReferenceEquals(argument.Type, sourceType) || !HirBuilder.IsNonGenericReceiverOwner(tested, source)) continue;
            bool mutable = false;
            foreach (var b in method.Blocks) foreach (var s in b.Statements)
            {
                if (s is HAssign { Target: HArg assigned } && assigned.Index == argument.Index) mutable = true;
                FinallyFolding.Visit(s, e => { if (e is HAddressOf { Target: HArg addressed } && addressed.Index == argument.Index) mutable = true; });
            }
            if (mutable) continue;
            var success = compare.Op == HCompareOp.Ne ? branch.WhenTrue : branch.WhenFalse;
            var withoutSuccess = Reachable(guard, success);
            foreach (var use in method.Blocks)
            {
                if (!reachable.Contains(use) || withoutSuccess.Contains(use)) continue;
                foreach (var statement in use.Statements) FinallyFolding.Visit(statement, e =>
                {
                    if (e is not HCall { This: HArg receiver, Method: { IsStatic: false, IsConstructor: false, DeclaringType: { IsValueType: false, IsInterface: false, IsGenericDefinition: false } owner }, DeclaringType: null, MethodArguments.Length: 0 } call ||
                        receiver.Index != argument.Index || !ReferenceEquals(receiver.Type, sourceType) ||
                        HirBuilder.IsNonGenericReceiverOwner(source, owner) || !HirBuilder.IsNonGenericReceiverOwner(tested, owner)) return;
                    call.This = new HTypeExpr(HTypeOp.CastClass, test.Target, receiver) { Type = test.Target };
                    changed++;
                });
            }
        }
        return changed;
    }
}
