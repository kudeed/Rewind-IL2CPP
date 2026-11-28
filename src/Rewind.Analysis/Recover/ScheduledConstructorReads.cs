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

    /// <summary>Only a non-virtual, zero-argument accessor whose complete recovered
    /// body is a read of the caller's own instance field can be scheduled. The call
    /// stays in place, including its null-receiver behavior.</summary>
    internal static bool IndependentCallerGetter(HCall call, TypeDef caller, Func<MethodDef, HMethod?> recover)
    {
        MethodDef method = call.Method;
        if (call.This is not HArg { Index: -1 } || method.IsStatic || method.IsVirtual ||
            method.Parameters.Length != 0 || call.Arguments.Length != 0 ||
            method.GenericParameters.Length != 0 || call.MethodArguments.Length != 0 ||
            call.DeclaringType != null || !ReferenceEquals(method.DeclaringType, caller)) return false;
        HMethod? body = recover(method);
        return body is { Problems.Count: 0, TryRegions.Count: 0,
            Blocks: [{ Statements: [HReturn { Value: HField { Object: HArg { Index: -1 }, Field: var field } }] }] } &&
            !field.IsStatic && ReferenceEquals(field.DeclaringType, caller);
    }

    /// <summary>Like the original constructor-only field-read proof, but for a fresh
    /// object in any reference-type instance method. Only an exactly identified empty
    /// System.Object constructor and plain private-object writes can be gathered; no
    /// operation can publish the object before the delayed read.</summary>
    internal static bool TryGatherGetters(MethodDef caller, List<HStmt> site, int allocation, HVar created,
        int length, TypeDef objectType, Func<MethodDef, HMethod?> recover, out List<int> picked)
    {
        picked = [];
        if (caller.IsStatic || caller.DeclaringType.IsValueType || created.AddressTaken ||
            length is < 2 or > 32 || allocation < 0 || allocation >= site.Count) return false;
        bool IsCreated(HExpr? e) => e is HLocal l && ReferenceEquals(l.Variable, created);
        bool PlainStore(HStmt s) => s is HAssign { Target: HField { Object: var owner, Field: var field }, Value: var value } &&
            !field.IsStatic && ReferenceEquals(field.DeclaringType, created.Type.Definition) &&
            IsCreated(owner) && value is HConst or HArg or HLocal &&
            (value is not HLocal l || !l.Variable.AddressTaken && !ReferenceEquals(l.Variable, created));
        bool EmptyBase(HStmt s) => s is HEval { Expression: HCall { Method: var m, This: var self, Arguments.Length: 0 } } &&
            IsCreated(self) && m.Name == ".ctor" && !m.IsStatic && m.Parameters.Length == 0 &&
            ReferenceEquals(m.DeclaringType, objectType);
        bool IndependentRead(HExpr value) => value switch
        {
            HField { Object: HArg { Index: -1 }, Field: var field } =>
                !field.IsStatic && ReferenceEquals(field.DeclaringType, caller.DeclaringType),
            HCall getter => IndependentCallerGetter(getter, caller.DeclaringType, recover),
            _ => false,
        };
        bool afterBase = false;
        var moved = new HashSet<HVar>();
        for (int j = allocation + 1; j < site.Count && picked.Count < length && j - allocation <= length + 4; j++)
        {
            HStmt stmt = site[j];
            if (afterBase && stmt is HAssign { Target: HLocal dest, Value: var read } &&
                IndependentRead(read) &&
                !dest.Variable.AddressTaken && !ReferenceEquals(dest.Variable, created) && moved.Add(dest.Variable))
                continue;
            if (EmptyBase(stmt))
            {
                if (afterBase) return false;
                afterBase = true;
            }
            else if (!PlainStore(stmt)) return false;
            picked.Add(j);
        }
        return afterBase && moved.Count != 0 && picked.Count == length &&
            !picked.Any(i => moved.Any(v => ConstructorFolding.Mentions(site[i], v)));
    }
}
