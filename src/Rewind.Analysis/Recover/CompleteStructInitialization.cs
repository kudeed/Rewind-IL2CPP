using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// A complete struct initializer may survive as public property writes mixed with private zero stores.
/// When a contiguous run writes each field exactly once, a whole default value supplies the zero stores.
/// The other writes stay in their original order. No prior value, unknown call, or aliased field read may
/// participate, and an accessor is accepted only after its own native body proves one field assignment.
/// </summary>
internal static class CompleteStructInitialization
{
    internal static int Run(HMethod h, ProgramAnalysis program, MethodPipeline pipeline)
    {
        if (Environment.GetEnvironmentVariable("REWIND_NO_COMPLETE_STRUCT_INIT") != null) return 0;
        var layouts = new Dictionary<TypeSig, bool>();
        var setters = new Dictionary<MethodDef, FieldDef?>();
        bool Layout(TypeSig type)
        {
            if (layouts.TryGetValue(type, out bool cached)) return cached;
            var layout = program.Layouts.Of(type);
            var fields = type.Definition!.Fields.Where(f => !f.IsStatic).ToArray();
            bool valid = layout.Known && layout.Size > 0 && layout.Fields.Length == fields.Length &&
                layout.Fields.All(f => fields.Contains(f.Field) && f.Offset >= 0 && f.Size > 0 &&
                    f.Offset + f.Size <= layout.Size);
            for (int i = 0; i < layout.Fields.Length && valid; i++)
                for (int j = 0; j < i; j++)
                    if (layout.Fields[i].Offset < layout.Fields[j].Offset + layout.Fields[j].Size &&
                        layout.Fields[j].Offset < layout.Fields[i].Offset + layout.Fields[i].Size)
                        valid = false;
            return layouts[type] = valid;
        }
        FieldDef? Setter(HCall call)
        {
            MethodDef m = call.Method;
            if (setters.TryGetValue(m, out var cached)) return cached;
            FieldDef? field = null;
            if (m.Address != 0 && program.Code.Get(m.Address) is { Instructions: <= 16 } &&
                pipeline.CoreBody(m) is { Problems.Count: 0, TryRegions.Count: 0, Blocks:
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

    // Separate layout/native-body policy from the complete-write proof for focused, model-free tests.
    internal static int Run(HMethod h, Func<TypeSig, bool> layout, Func<HCall, FieldDef?> setter)
    {
        if (h.Problems.Count != 0 || h.TryRegions.Count != 0 || h.Blocks.Any(b => b.Scope != -1)) return 0;
        int changed = 0;
        foreach (HBlock block in h.Blocks)
        for (int at = 0; at < block.Statements.Count; at++)
        {
            if (!Write(block.Statements[at], out var place, out _, out _, out _) ||
                place.Type is not TypeDefSig { Definition: { IsValueType: true, IsEnum: false } owner } type ||
                owner.IsGenericDefinition || (owner.Flags & TypeDef.LayoutMask) == TypeDef.ExplicitLayout ||
                !Place(place, h.Method) || !layout(type)) continue;
            var fields = owner.Fields.Where(f => !f.IsStatic).ToArray();
            if (fields.Length is < 2 or > 64 || fields.Any(f => (f.Attrs & FieldDef.InitOnly) != 0 ||
                    f.Type is PointerSig or ByRefSig or OpaqueSig or GenericParamSig)) continue;
            var seen = new HashSet<FieldDef>();
            var keep = new List<HStmt>();
            bool valid = true, inaccessibleZero = false;
            for (int i = 0; i < fields.Length; i++)
            {
                if (at + i >= block.Statements.Count ||
                    !Write(block.Statements[at + i], out var on, out var field, out var value, out var call) ||
                    !SamePlace(place, on) || field.DeclaringType != owner || !fields.Contains(field) ||
                    !seen.Add(field) || !SameType(value.Type, field.Type) || !Plain(value, place))
                { valid = false; break; }
                bool zero = Default(value, field.Type);
                bool accessible = call == null ? AccessorFolding.IsAccessible(field, h.Method) :
                    (call.Method.Flags & MethodDef.AccessMask) == 6;
                if (zero) inaccessibleZero |= !accessible;
                else if (!accessible) { valid = false; break; }
                else keep.Add(block.Statements[at + i]);
            }
            if (!valid || !inaccessibleZero || keep.Count == fields.Length) continue;
            // These are complete, independent writes. No previous content or intermediate observer is used.
            var initial = new HAssign(CopyPlace(place), new HTypeExpr(HTypeOp.Default, type, null) { Type = type })
                { Address = block.Statements[at].Address };
            block.Statements.RemoveRange(at, fields.Length);
            block.Statements.InsertRange(at, new HStmt[] { initial }.Concat(keep));
            h.Notes.Add($"restored complete struct initialization: {type.DisplayName}, {fields.Length - keep.Count} default field write(s), {keep.Count} original write(s) kept");
            changed++;
            at += keep.Count;
        }
        return changed;

        bool Write(HStmt statement, out HExpr place, out FieldDef field, out HExpr value, out HCall? call)
        {
            place = null!; field = null!; value = null!; call = null;
            if (statement is HAssign { Target: HField { Object: { } on } f, Value: var v } &&
                !f.Field.IsStatic && SameType(f.Type, f.Field.Type))
            { place = on; field = f.Field; value = v; return true; }
            if (statement is not HEval { Expression: HCall { This: { } receiver } c } ||
                c.Virtual || c.Constrained != null || c.DeclaringType != null || c.MethodArguments.Length != 0 ||
                c.Method.IsStatic || c.Method.IsVirtual || c.Method.IsAbstract || c.Method.IsGenericDefinition ||
                c.Method.IsConstructor || !c.Method.ReturnType.IsVoid || c.Method.Parameters.Length != 1 ||
                c.Arguments.Length != 1 || c.Method.DeclaringType.IsGenericDefinition ||
                !c.Method.DeclaringType.IsValueType || c.Method.Parameters[0].Type is ByRefSig or PointerSig ||
                setter(c) is not { } written || written.IsStatic ||
                written.DeclaringType != c.Method.DeclaringType ||
                !SameType(written.Type, c.Method.Parameters[0].Type)) return false;
            place = receiver; field = written; value = c.Arguments[0]; call = c; return true;
        }
    }

    private static bool SameType(TypeSig? a, TypeSig? b) => a != null && b != null &&
        a.Key.Length != 0 && a.Key == b.Key;

    private static bool Place(HExpr e, MethodDef method) => e switch
    {
        HLocal l => SameType(l.Type, l.Variable.Type),
        HField { Object: HArg { Index: -1 }, Field: var f } when !method.IsStatic &&
            !method.DeclaringType.IsValueType && f.DeclaringType == method.DeclaringType &&
            !f.IsStatic && (f.Attrs & FieldDef.InitOnly) == 0 => SameType(e.Type, f.Type),
        _ => false
    };

    private static bool SamePlace(HExpr a, HExpr b) => SameType(a.Type, b.Type) && (a, b) switch
    {
        (HLocal x, HLocal y) => x.Variable == y.Variable,
        (HField { Object: HArg { Index: -1 } } x, HField { Object: HArg { Index: -1 } } y) => x.Field == y.Field,
        _ => false
    };

    private static HExpr CopyPlace(HExpr e) => e switch
    {
        HLocal l => new HLocal(l.Variable) { Type = l.Type },
        HField { Object: HArg a } f => new HField
        {
            Object = new HArg(a.Index) { Type = a.Type }, Field = f.Field,
            DeclaringType = f.DeclaringType, Type = f.Type
        },
        _ => throw new InvalidOperationException("Unproven struct destination")
    };

    private static bool Default(HExpr e, TypeSig type) =>
        e is HTypeExpr { Op: HTypeOp.Default, Operand: null } d && SameType(d.Target, type) ||
        e is HConst { Value: null } && !type.IsValueType && type is not (PointerSig or ByRefSig or GenericParamSig or OpaqueSig);

    private static bool Plain(HExpr e, HExpr destination) => e switch
    {
        HTypeExpr { Op: HTypeOp.Default, Operand: null } d => SameType(d.Type, d.Target),
        HConst => e.Type is not (PointerSig or ByRefSig or OpaqueSig),
        HLocal l => !SamePlace(l, destination) && SameType(l.Type, l.Variable.Type) &&
            l.Type is not (PointerSig or ByRefSig or OpaqueSig),
        HArg { Index: >= 0 } => e.Type is not (PointerSig or ByRefSig or OpaqueSig),
        _ => false
    };
}
