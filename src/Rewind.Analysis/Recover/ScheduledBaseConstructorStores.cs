using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>Recover a direct base constructor whose constant field initializers
/// were scheduled around independent derived-class initializers. The final
/// ancestor constructor call must be present and is consumed exactly once.</summary>
internal static class ScheduledBaseConstructorStores
{
    internal static bool TryGather(MethodDef caller, MethodDef constructor, List<HStmt> site,
        List<HStmt> template, Func<MethodDef, HMethod?> recover, out List<int> picked)
    {
        picked = [];
        TypeDef owner = caller.DeclaringType, parent = constructor.DeclaringType;
        if (caller.Name != ".ctor" || caller.IsStatic || owner.IsValueType ||
            constructor.Name != ".ctor" || constructor.IsStatic || constructor.Parameters.Length != 0 ||
            owner.GenericParameters.Length != 0 || parent.GenericParameters.Length != 0 ||
            !ReferenceEquals(owner.BaseType?.Definition, parent) || template.Count is < 2 or > 32 ||
            template[^1] is not HEval { Expression: HCall { Method: var ancestor, This: HArg { Index: -1 }, Arguments.Length: 0 } } ||
            ancestor.Name != ".ctor" || ancestor.IsStatic || ancestor.Parameters.Length != 0 ||
            !ReferenceEquals(parent.BaseType?.Definition, ancestor.DeclaringType)) return false;
        foreach (HStmt statement in template.Take(template.Count - 1))
            if (statement is not HAssign { Target: HField { Object: HArg { Index: -1 }, Field: var field }, Value: HConst } ||
                field.IsStatic || !ReferenceEquals(field.DeclaringType, parent)) return false;

        bool OwnStore(HStmt statement) => statement is HAssign
            { Target: HField { Object: HArg { Index: -1 }, Field: var field }, Value: var value } &&
            !field.IsStatic && ReferenceEquals(field.DeclaringType, owner) && IndependentValue(value, field.Type, recover);
        for (int start = 0; start + template.Count <= site.Count; start++)
        {
            if (!Same(template[0], site[start])) continue;
            var matches = new List<int>();
            int at = start, skipped = 0;
            bool valid = true;
            foreach (HStmt wanted in template)
            {
                while (matches.Count != 0 && at < site.Count && !Same(wanted, site[at]) && OwnStore(site[at]))
                {
                    skipped++;
                    at++;
                }
                if (at >= site.Count || !Same(wanted, site[at])) { valid = false; break; }
                matches.Add(at++);
            }
            if (valid && skipped != 0) { picked = matches; return true; }
        }
        return false;
    }

    private static bool Same(HStmt wanted, HStmt actual) => (wanted, actual) switch
    {
        (HAssign { Target: HField { Object: HArg { Index: -1 }, Field: var left }, Value: HConst a },
         HAssign { Target: HField { Object: HArg { Index: -1 }, Field: var right }, Value: HConst b }) =>
            ReferenceEquals(left, right) && ConstantEqual(a.Value, b.Value),
        (HEval { Expression: HCall { Method: var left, This: HArg { Index: -1 }, Arguments.Length: 0 } },
         HEval { Expression: HCall { Method: var right, This: HArg { Index: -1 }, Arguments.Length: 0 } }) =>
            ReferenceEquals(left, right),
        _ => false,
    };

    private static bool ConstantEqual(object? left, object? right) => (left, right) switch
    {
        (float x, float y) => BitConverter.SingleToInt32Bits(x) == BitConverter.SingleToInt32Bits(y),
        (double x, double y) => BitConverter.DoubleToInt64Bits(x) == BitConverter.DoubleToInt64Bits(y),
        _ => Equals(left, right),
    };

    private static bool IndependentValue(HExpr value, TypeSig target, Func<MethodDef, HMethod?> recover)
    {
        TypeSig? actual = value is HLocal local ? local.Variable.Type : value.Type;
        if (actual == null || actual.Key != target.Key) return false;
        if (value is HConst or HArg { Index: >= 0 } || value is HLocal { Variable.AddressTaken: false }) return true;
        if (value is not HNewObject { Constructor: var ctor, Arguments: var arguments } ||
            !ctor.DeclaringType.IsValueType || ctor.IsStatic || ctor.Name != ".ctor" ||
            ctor.DeclaringType.GenericParameters.Length != 0 || ctor.DeclaringType.Methods.Any(m => m.Name == ".cctor") ||
            ctor.Parameters.Length != arguments.Length ||
            arguments.Any(a => a is not HConst) || recover(ctor) is not
            { Problems.Count: 0, TryRegions.Count: 0, Blocks: [{ Statements: var statements }] } ||
            statements.Count < 2 || statements[^1] is not HReturn { Value: null }) return false;
        for (int i = 0; i < arguments.Length; i++)
            if (arguments[i].Type?.Key != ctor.Parameters[i].Type.Key) return false;
        foreach (HStmt statement in statements.Take(statements.Count - 1))
            if (statement is not HAssign { Target: HField { Object: HArg { Index: -1 }, Field: var field }, Value: var stored } ||
                field.IsStatic || !ReferenceEquals(field.DeclaringType, ctor.DeclaringType) ||
                stored is not (HConst or HArg { Index: >= 0 }) ||
                stored is HArg arg && (arg.Index >= ctor.Parameters.Length || ctor.Parameters[arg.Index].Type.Key != field.Type.Key) ||
                stored is HConst constant && constant.Type?.Key != field.Type.Key) return false;
        return true;
    }
}
