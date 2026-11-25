using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>Small, fail-closed scheduling proof for a fresh object inside
/// an instance constructor. The caller's non-null this and the new object
/// are distinct; a field read from the former can pass plain stores to
/// the latter. Never move a read across calls or another local assignment.</summary>
internal static class ScheduledConstructorReads
{
    internal static bool TryGather(MethodDef caller, List<HStmt> site, int allocation, HVar created,
        int length, out List<int> picked)
    {
        picked = [];
        if (caller.Name != ".ctor" || caller.IsStatic || caller.DeclaringType.IsValueType ||
            created.AddressTaken || length is < 2 or > 32 ||
            allocation < 0 || allocation >= site.Count) return false;
        bool IsCreated(HExpr? e) => e is HLocal l && ReferenceEquals(l.Variable,created);
        bool PlainStore(HStmt s) => s is HAssign {Target: HField {Object: var owner,Field.IsStatic:false}, Value:var value}
            && IsCreated(owner) && value is HConst or HArg or HLocal &&
            (value is not HLocal l || !l.Variable.AddressTaken && !ReferenceEquals(l.Variable,created));
        bool afterBase = false;
        var moved = new HashSet<HVar>();
        for (int j = allocation + 1; j < site.Count && picked.Count < length && j - allocation <= length + 4; j++)
        {
            HStmt stmt = site[j];
            if (afterBase && stmt is HAssign {Target: HLocal dest,
                    Value: HField {Object: HArg {Index: -1}, Field: {IsStatic: false} field}} &&
                ReferenceEquals(field.DeclaringType,caller.DeclaringType) &&
                !dest.Variable.AddressTaken && !ReferenceEquals(dest.Variable,created) &&
                moved.Add(dest.Variable))
                continue;
            if (moved.Count != 0 && !PlainStore(stmt)) return false;
            if (stmt is not (HAssign or HEval)) return false;
            picked.Add(j);
            if (stmt is HEval {Expression:HCall {Method.Name:".ctor",This:var self}} && IsCreated(self))
                afterBase = true;
        }
        if (picked.Count != length || moved.Count == 0 ||
            picked.Any(i => moved.Any(v => ConstructorFolding.Mentions(site[i],v))))
            return false;
        return true;
    }
}
