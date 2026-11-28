using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Restores a public setter whose native body calls another method and then stores its argument. Native
/// scheduling may put independent reads of the caller's own fields between those two statements. Keep the
/// call at its original position and move only the final store across those reads. The argument must already
/// be available, the caller must already have been dereferenced, and unrelated reference classes prove that
/// the skipped reads cannot observe the stored field.
/// </summary>
internal static class ScheduledSetterWrites
{
    internal static int Run(HMethod h, ProgramAnalysis program, MethodPipeline pipeline)
    {
        if (Environment.GetEnvironmentVariable("REWIND_NO_SCHEDULED_SETTER_WRITES") != null) return 0;
        var cache = new Dictionary<FieldDef, (MethodDef Setter, HCall Prelude)[]>();
        (MethodDef Setter, HCall Prelude)[] Templates(FieldDef field)
        {
            if (cache.TryGetValue(field, out var found)) return found;
            var candidates = new List<(MethodDef, HCall)>();
            foreach (var m in field.DeclaringType.Methods)
                if (m.Name.StartsWith("set_", StringComparison.Ordinal) && !m.IsStatic && !m.IsVirtual &&
                    !m.IsAbstract && !m.IsGenericDefinition && !m.DeclaringType.IsGenericDefinition &&
                    (m.Flags & MethodDef.AccessMask) == 6 && m.ReturnType.IsVoid && m.Parameters.Length == 1 &&
                    SameType(m.Parameters[0].Type, field.Type) && m.Address != 0 &&
                    program.Code.Get(m.Address) is { Instructions: <= 32 } &&
                    pipeline.CoreBody(m) is { Problems.Count: 0, TryRegions.Count: 0, Blocks:
                        [{ Scope: -1, Statements: [HEval { Expression: HCall { This: HArg { Index: -1 } } call },
                            HAssign { Target: HField { Object: HArg { Index: -1 } } target,
                                Value: HArg { Index: 0 } argument }, HReturn { Value: null }] }] } &&
                    target.Field == field && SameType(target.Type, field.Type) && SameType(argument.Type, field.Type) &&
                    call.Arguments.Length == 0 && call.Method.Parameters.Length == 0 && call.Method.ReturnType.IsVoid &&
                    !call.Method.IsStatic && !call.Method.IsConstructor && !call.Method.IsGenericDefinition &&
                    call.DeclaringType == null && call.Constrained == null && call.MethodArguments.Length == 0)
                    candidates.Add((m, call));
            return cache[field] = candidates.ToArray();
        }
        return Run(h, Templates);
    }

    internal static int Run(HMethod h, Func<FieldDef, (MethodDef Setter, HCall Prelude)[]> templates)
    {
        if (h.Problems.Count != 0 || h.TryRegions.Count != 0 || h.Method.IsStatic ||
            h.Method.DeclaringType.IsValueType || h.Blocks.Any(b => b.Scope != -1)) return 0;
        int changed = 0;
        foreach (HBlock block in h.Blocks)
        for (int store = 0; store < block.Statements.Count; store++)
        {
            if (block.Statements[store] is not HAssign
                    { Target: HField { Object: HLocal receiver } target, Value: var value } assignment ||
                target.Field.IsStatic || (target.Field.Attrs & FieldDef.InitOnly) != 0 ||
                (target.Field.Attrs & FieldDef.AccessMask) != 1 ||
                !SameOwner(target.DeclaringType, target.Field.DeclaringType) || !SameType(target.Type, target.Field.Type) ||
                !SameType(receiver.Type, receiver.Variable.Type) || receiver.Variable.AddressTaken ||
                !SameType(receiver.Type, target.Field.DeclaringType.Sig) ||
                !SameType(value.Type, target.Field.Type) || target.Field.DeclaringType.IsValueType ||
                !UnrelatedClasses(h.Method.DeclaringType, target.Field.DeclaringType)) continue;
            var models = templates(target.Field);
            for (int at = store - 1; at >= 0 && store - at <= 5; at--)
            {
                if (block.Statements[at] is not HEval { Expression: HCall before }) continue;
                var model = models.FirstOrDefault(t => SameCall(t.Prelude, before, receiver.Variable));
                if (model.Setter == null || !Ready(value, block, at, store, h.Method) ||
                    !Ready(receiver, block, at, store, h.Method) ||
                    !CallerAlreadyRead(block, at, h.Method.DeclaringType)) continue;
                bool safe = true;
                for (int i = at + 1; i < store; i++)
                {
                    if (block.Statements[i] is not HAssign { Target: HLocal local,
                            Value: HField { Object: HArg { Index: -1 } } read } ||
                        read.Field.IsStatic || read.Field.DeclaringType != h.Method.DeclaringType ||
                        !SameOwner(read.DeclaringType, read.Field.DeclaringType) || !SameType(read.Type, read.Field.Type) ||
                        !SameType(local.Type, local.Variable.Type) || !SameType(local.Type, read.Type) || local.Variable.AddressTaken ||
                        local.Variable == receiver.Variable || value is HLocal arg && local.Variable == arg.Variable ||
                        local.Type is ByRefSig or PointerSig or OpaqueSig)
                    { safe = false; break; }
                }
                if (!safe) continue;
                block.Statements[at] = new HEval(new HCall
                {
                    Method = model.Setter, This = new HLocal(receiver.Variable) { Type = receiver.Type },
                    Arguments = [value], Type = model.Setter.ReturnType
                }) { Address = block.Statements[at].Address };
                block.Statements.RemoveAt(store);
                h.Notes.Add($"restored scheduled public setter: {model.Setter.FullName}, {store - at - 1} independent caller field read(s)");
                changed++;
                store--;
                break;
            }
        }
        return changed;
    }

    private static bool SameOwner(TypeSig? type, TypeDef owner) => type == null ||
        type is TypeDefSig definition && definition.Definition == owner && SameType(type, owner.Sig);

    private static bool SameType(TypeSig? a, TypeSig? b) => a != null && b != null &&
        a.Key.Length != 0 && a.Key == b.Key;

    private static bool SameCall(HCall model, HCall site, HVar receiver) =>
        model.Method == site.Method && model.Virtual == site.Virtual &&
        site.This is HLocal local && local.Variable == receiver &&
        site.Arguments.Length == 0 && site.DeclaringType == null && site.Constrained == null &&
        site.MethodArguments.Length == 0;

    private static bool Ready(HExpr value, HBlock block, int call, int store, MethodDef method)
    {
        if (value.Type is ByRefSig or PointerSig or OpaqueSig) return false;
        if (value is HConst constant) return constant.Value != null || value.Type is { IsValueType: false };
        if (value is HArg { Index: >= 0 } argument)
            return argument.Index < method.Parameters.Length && SameType(argument.Type, method.Parameters[argument.Index].Type);
        if (value is not HLocal local || local.Variable.AddressTaken || !SameType(local.Type, local.Variable.Type)) return false;
        bool defined = block.Statements.Take(call).Any(s => s is HAssign { Target: HLocal l } &&
            l.Variable == local.Variable);
        return defined && !block.Statements.Skip(call + 1).Take(store - call - 1)
            .Any(s => s is HAssign { Target: HLocal l } && l.Variable == local.Variable);
    }

    private static bool CallerAlreadyRead(HBlock block, int at, TypeDef caller) =>
        block.Statements.Take(at).Any(s => s is HAssign
        {
            Value: HField { Object: HArg { Index: -1 }, Field: { IsStatic: false } f }
        } && f.DeclaringType == caller);

    private static bool UnrelatedClasses(TypeDef a, TypeDef b)
    {
        if (a.IsValueType || b.IsValueType || a.IsGenericDefinition || b.IsGenericDefinition) return false;
        bool Chain(TypeDef t, out HashSet<TypeDef> chain)
        {
            chain = [];
            while (true)
            {
                if (!chain.Add(t) || (t.Flags & TypeDef.LayoutMask) == TypeDef.ExplicitLayout) return false;
                if (t.BaseType == null) return true;
                if (t.BaseType.Definition is not { } parent) return false;
                t = parent;
            }
        }
        return Chain(a, out var aa) && Chain(b, out var bb) && !aa.Contains(b) && !bb.Contains(a);
    }
}
