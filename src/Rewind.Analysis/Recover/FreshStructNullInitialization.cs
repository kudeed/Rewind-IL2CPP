using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// A private reference field that is still null in a fresh struct needs no second null store. Prove the
/// dominating default assignment and inspect every path to the store. An address escape, unknown struct
/// mutator, overlapping layout, reassignment, exception region or cycle makes the proof fail.
/// </summary>
internal static class FreshStructNullInitialization
{
    internal static int Run(HMethod h, ProgramAnalysis program, MethodPipeline pipeline)
    {
        if (Environment.GetEnvironmentVariable("REWIND_NO_FRESH_STRUCT_NULL_INIT") != null) return 0;
        var layouts = new Dictionary<TypeDef, bool>();
        var setters = new Dictionary<MethodDef, FieldDef?>();
        bool Layout(HVar local, FieldDef field)
        {
            var owner = field.DeclaringType;
            if (layouts.TryGetValue(owner, out bool known)) return known;
            var layout = program.Layouts.Of(local.Type!);
            bool valid = !owner.IsGenericDefinition && (owner.Flags & TypeDef.LayoutMask) != TypeDef.ExplicitLayout &&
                layout.Known && layout.Size > 0 && layout.Fields.Length == owner.Fields.Count(f => !f.IsStatic);
            for (int i = 0; i < layout.Fields.Length && valid; i++)
            {
                var a = layout.Fields[i];
                if (a.Offset < 0 || a.Size <= 0 || a.Offset + a.Size > layout.Size) { valid = false; break; }
                for (int j = 0; j < i; j++)
                {
                    var b = layout.Fields[j];
                    if (a.Offset < b.Offset + b.Size && b.Offset < a.Offset + a.Size) { valid = false; break; }
                }
            }
            return layouts[owner] = valid;
        }
        FieldDef? Setter(HCall call)
        {
            MethodDef m = call.Method;
            if (call.Virtual || call.MethodArguments.Length != 0 || call.DeclaringType != null ||
                m.IsStatic || m.IsVirtual || m.IsAbstract || m.IsGenericDefinition || m.Address == 0 ||
                (m.Flags & MethodDef.AccessMask) != 6 || !m.DeclaringType.IsValueType ||
                m.DeclaringType.IsGenericDefinition || m.Parameters.Length != 1 ||
                !m.ReturnType.IsVoid || call.Arguments.Length != 1) return null;
            if (setters.TryGetValue(m, out var known)) return known;
            FieldDef? field = null;
            if (pipeline.CoreBody(m) is { Problems.Count: 0, TryRegions.Count: 0, Blocks:
                    [{ Statements: [HAssign { Target: HField { Object: HArg { Index: -1 } } target,
                        Value: HArg { Index: 0 } }, HReturn { Value: null }] }] } &&
                target.Field.DeclaringType == m.DeclaringType && !target.Field.IsStatic &&
                target.Field.Type.Key == m.Parameters[0].Type.Key)
                field = target.Field;
            setters[m] = field;
            return field;
        }
        return Run(h, Layout, Setter);
    }

    // The policy inputs are separate so the path proof can be exercised without loading a native image.
    internal static int Run(HMethod h, Func<HVar, FieldDef, bool> layout,
        Func<HCall, FieldDef?> setter)
    {
        if (h.Problems.Count != 0 || h.TryRegions.Count != 0 || h.Blocks.Count is < 1 or > 64 ||
            h.Blocks.Any(b => b.Scope != -1)) return 0;
        var predecessors = h.Blocks.ToDictionary(b => b, _ => new HashSet<HBlock>());
        foreach (var b in h.Blocks)
        {
            if (b.Statements.Count == 0) return 0;
            HBlock[] next;
            switch (b.Statements[^1])
            {
                case HJump j: next = [j.Target]; break;
                case HBranch c: next = [c.WhenTrue, c.WhenFalse]; break;
                case HSwitch s: next = [.. s.Targets, s.Default]; break;
                case HReturn or HThrow: next = []; break;
                default: return 0;
            }
            foreach (var target in next)
            {
                if (!predecessors.TryGetValue(target, out var incoming)) return 0;
                incoming.Add(b);
            }
        }
        if (predecessors[h.Blocks[0]].Count != 0) return 0;
        var remove = new HashSet<HStmt>();
        foreach (var block in h.Blocks)
        for (int at = 0; at < block.Statements.Count; at++)
        {
            if (block.Statements[at] is not HAssign { Target: HField { Object: HLocal local } target,
                    Value: HConst { Value: null } } assignment ||
                local.Variable.Type is not TypeDefSig { Definition: { IsValueType: true, IsEnum: false } owner } type ||
                target.Field.DeclaringType != owner || target.Field.IsStatic ||
                (target.Field.Attrs & FieldDef.AccessMask) != 1 ||
                (target.Field.Attrs & FieldDef.InitOnly) != 0 ||
                target.Field.Type is not TypeDefSig { Definition.IsValueType: false } ||
                local.Type?.Key != type.Key || !layout(local.Variable, target.Field)) continue;
            HVar variable = local.Variable;
            var entry = h.Blocks[0];
            int initial = entry.Statements.FindIndex(s => s is HAssign
                { Target: HLocal l, Value: HTypeExpr { Op: HTypeOp.Default } zero } &&
                l.Variable == variable && zero.Target.Key == type.Key);
            if (initial < 0 || block == entry && initial >= at ||
                entry.Statements.Take(initial).Any(s => Mentions(s, variable))) continue;

            var ancestors = new HashSet<HBlock>();
            var visiting = new HashSet<HBlock>();
            bool Ancestors(HBlock b)
            {
                if (visiting.Contains(b)) return false;
                if (ancestors.Contains(b)) return true;
                visiting.Add(b);
                foreach (var prior in predecessors[b])
                    if (!Ancestors(prior)) return false;
                visiting.Remove(b);
                ancestors.Add(b);
                return true;
            }
            if (!Ancestors(block) || !ancestors.Contains(entry)) continue;

            bool Safe(HExpr? e)
            {
                if (e == null || !Mentions(e, variable)) return true;
                switch (e)
                {
                    case HLocal: return true; // reading a struct value makes a copy
                    case HField f: return Safe(f.Object);
                    case HElement x: return Safe(x.Array) && Safe(x.Index);
                    case HArrayLength x: return Safe(x.Array);
                    case HUnary x: return Safe(x.Operand);
                    case HBinary x: return Safe(x.Left) && Safe(x.Right);
                    case HCompare x: return Safe(x.Left) && Safe(x.Right);
                    case HConv x: return x.Type is not (ByRefSig or PointerSig) && Safe(x.Operand);
                    case HTypeExpr x: return x.Type is not (ByRefSig or PointerSig) && Safe(x.Operand);
                    case HSelect x: return Safe(x.Condition) && Safe(x.WhenTrue) && Safe(x.WhenFalse);
                    case HCall call:
                        if (Mentions(call.This, variable) &&
                            (call.This is not HLocal l || l.Variable != variable ||
                             setter(call) is not { } written || written.DeclaringType != owner ||
                             written == target.Field)) return false;
                        if (call.Arguments.Length != call.Method.Parameters.Length) return false;
                        for (int i = 0; i < call.Arguments.Length; i++)
                            if (!Safe(call.Arguments[i]) ||
                                Mentions(call.Arguments[i], variable) &&
                                call.Method.Parameters[i].Type is ByRefSig or PointerSig) return false;
                        return call.This is HLocal || Safe(call.This);
                    case HNewObject creation:
                        if (creation.Arguments.Length != creation.Constructor.Parameters.Length) return false;
                        for (int i = 0; i < creation.Arguments.Length; i++)
                            if (!Safe(creation.Arguments[i]) ||
                                Mentions(creation.Arguments[i], variable) &&
                                creation.Constructor.Parameters[i].Type is ByRefSig or PointerSig) return false;
                        return true;
                    case HNewArray x: return Safe(x.Length);
                    // In particular: an address of the local or a field, pointer dereference, or opaque use.
                    default: return false;
                }
            }
            bool Unchanged(HStmt s)
            {
                switch (s)
                {
                    case HAssign a:
                        if (!Safe(a.Value)) return false;
                        if (a.Target is HLocal l && l.Variable == variable) return false;
                        if (a.Target.Type is ByRefSig or PointerSig && Mentions(a.Value, variable)) return false;
                        if (a.Target is HField { Object: HLocal on } f && on.Variable == variable)
                            return f.Field.DeclaringType == owner && !f.Field.IsStatic &&
                                (f.Field != target.Field || a.Value is HConst { Value: null });
                        return Safe(a.Target);
                    case HEval e: return Safe(e.Expression);
                    case HBranch b: return Safe(b.Condition);
                    case HSwitch sw: return Safe(sw.Value);
                    case HReturn r: return h.Method.ReturnType is not (ByRefSig or PointerSig) && Safe(r.Value);
                    case HThrow t: return Safe(t.Exception);
                    case HJump: return true;
                    default: return false;
                }
            }
            bool unchanged = true;
            foreach (var ancestor in ancestors)
            {
                int start = ancestor == entry ? initial + 1 : 0;
                int end = ancestor == block ? at : ancestor.Statements.Count;
                for (int i = start; i < end && unchanged; i++)
                    unchanged = Unchanged(ancestor.Statements[i]);
                if (!unchanged) break;
            }
            if (unchanged) remove.Add(assignment);
        }
        foreach (var block in h.Blocks) block.Statements.RemoveAll(remove.Contains);
        if (remove.Count != 0)
            h.Notes.Add($"restored fresh struct initialization: {remove.Count} reference field null store(s) already supplied by default");
        return remove.Count;
    }

    private static bool Mentions(HExpr? e, HVar variable)
    {
        bool found = false;
        FinallyFolding.Visit(e, x => found |= x is HLocal l && l.Variable == variable);
        return found;
    }

    private static bool Mentions(HStmt s, HVar variable)
    {
        bool found = false;
        FinallyFolding.Visit(s, x => found |= x is HLocal l && l.Variable == variable);
        return found;
    }
}
