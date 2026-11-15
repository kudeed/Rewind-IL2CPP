using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// A struct that is one number and nothing else (the number of a player, the tick a timer ends at) is that
/// number to the machine: it is copied by copying the number, kept in a register like any other, and where
/// its own methods are pasted in, the number is all there is left to see. Written out as it stands, that is
/// code which reads and writes the struct's private field from the outside.
///
/// Two things are put right here, before the struct folds look at the method:
///
///   - A struct on the stack is given its type by the method that is called on it, and identical methods of
///     different structs share one body ("is this number above zero?" of a timer and of a mining result).
///     Where everything put into such a variable is read from another struct of the same shape, and that
///     struct has a method with the same body for each one called on the variable, the variable is that
///     other struct.
///
///   - A variable that only ever holds such a struct's number - everything put in it is read from the one
///     field of such a struct, or is zero - holds the struct: it is given the struct's type, what is put in
///     it is the struct, and where it is read, its field is read. Copies made from it are then copies of
///     the struct, and what is done with the number is recognized as the struct's own methods.
/// </summary>
internal static class WrapperFolding
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_WRAPPER_FOLD") != null;
    /// <summary>REWIND_WRAPPER_TRACE=text: says on the error stream what was made of the methods whose name contains the text.</summary>
    private static readonly string? Traced = Environment.GetEnvironmentVariable("REWIND_WRAPPER_TRACE");

    /// <summary>Structs on the stack typed by a method that another struct has too (see above); before the struct folds.</summary>
    public static void Retype(HMethod method, ProgramAnalysis program)
    {
        if (Disabled || method.Blocks.Count == 0) return;
        Receivers(method, program);
    }

    /// <summary>
    /// Variables that hold a struct's number (see above); true when there were any. After the methods pasted
    /// in were recognized: those are compared with their own code, in which such a variable holds the number.
    /// </summary>
    public static bool Lift(HMethod method, MethodPipeline pipeline)
    {
        if (Disabled || method.Blocks.Count == 0) return false;
        bool any = false;
        for (int round = 0; round < 4 && Variables(method); round++) any = true;
        any |= Wrapped(method, pipeline);
        return any;
    }

    // ---- a struct taken apart and put together again ----------------------------------------------------------------

    private static int Width(TypeSig? type) => type is PrimitiveSig p
        ? p.Element switch
        {
            Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 => 8,
            Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 => 16,
            Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 => 32,
            Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 => 64,
            _ => 0,
        }
        : 0;

    /// <summary>A method of a struct that does nothing but put the number it is given into a new one.</summary>
    private static bool OnlyWraps(MethodDef method, FieldDef field, MethodPipeline pipeline)
    {
        if (pipeline.CoreBody(method) is not { Blocks: [{ Statements: [.., HReturn { Value: HLocal back }] statements }] }) return false;
        bool stored = false;
        for (int k = 0; k < statements.Count - 1; k++)
        {
            switch (statements[k])
            {
                case HAssign { Target: HLocal made, Value: HTypeExpr { Op: HTypeOp.Default } } when ReferenceEquals(made.Variable, back.Variable) && !stored:
                    break;
                case HAssign { Target: HField { Object: HLocal made } set, Value: HArg { Index: 0 } }
                    when ReferenceEquals(made.Variable, back.Variable) && ReferenceEquals(set.Field, field) && !stored:
                    stored = true;
                    break;
                default:
                    return false;
            }
        }
        return stored;
    }

    /// <summary>"W.From(x.number)", where From only wraps the number it is given: that is x.</summary>
    private static bool Wrapped(HMethod method, MethodPipeline pipeline)
    {
        bool any = false;
        HExpr? Whole(HExpr e)
        {
            if (e is not HCall { This: null, Arguments: [var given] } call || !call.Method.IsStatic || call.Method.GenericParameters.Length != 0) return null;
            if (OnlyField(call.Type) is not { } field || !ReferenceEquals(call.Method.DeclaringType, field.DeclaringType)) return null;
            HExpr inner = given;
            while (inner is HConv { Operand: { } operand } conv && conv.Kind is HConvKind.I4 or HConvKind.U4 or HConvKind.I8 or HConvKind.U8 &&
                   (conv.Kind is HConvKind.I8 or HConvKind.U8 ? 64 : 32) >= Width(field.Type))
                inner = operand;
            if (inner is not HField { Object: { } whole } read || !ReferenceEquals(read.Field, field) || !ReferenceEquals(whole.Type, call.Type)) return null;
            if (!OnlyWraps(call.Method, field, pipeline)) return null;
            any = true;
            return whole;
        }
        foreach (HBlock b in method.Blocks)
            foreach (HStmt s in b.Statements)
                EnumeratorLoops.Rewrite(s, Whole);
        return any;
    }

    /// <summary>The one field a struct consists of, when that is a plain whole number.</summary>
    internal static FieldDef? OnlyField(TypeSig? type)
    {
        if (type is null or PrimitiveSig or ByRefSig or PointerSig or GenericParamSig) return null;
        if (type.Definition is not { IsValueType: true, IsEnum: false } definition) return null;
        FieldDef? only = null;
        foreach (FieldDef f in definition.Fields)
        {
            if (f.IsStatic) continue;
            if (only != null) return null;
            only = f;
        }
        return only is
        {
            Type: PrimitiveSig
            {
                Element: Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 or Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 or Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4
                or Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8
            }
        }
            ? only
            : null;
    }

    private static bool IsZero(HExpr? e) => e is HConst { Value: 0 or 0L };

    // ---- a variable that holds the number of a struct ------------------------------------------------------------

    private static bool Variables(HMethod method)
    {
        var defs = new Dictionary<HVar, List<HAssign>>();
        foreach (HBlock b in method.Blocks)
            foreach (HStmt s in b.Statements)
                if (s is HAssign { Target: HLocal t } a)
                {
                    if (!defs.TryGetValue(t.Variable, out List<HAssign>? list)) defs[t.Variable] = list = [];
                    list.Add(a);
                }
        var caught = new HashSet<HVar>();
        foreach (HTryRegion r in method.TryRegions.Values) caught.Add(r.Exception);

        var lifted = new Dictionary<HVar, (TypeSig Wrapper, FieldDef Field)>();
        foreach ((HVar v, List<HAssign> list) in defs)
        {
            if (v.AddressTaken || caught.Contains(v) || v.Type is not PrimitiveSig) continue;
            TypeSig? wrapper = null;
            FieldDef? field = null;
            bool fine = true;
            foreach (HAssign a in list)
            {
                if (IsZero(a.Value)) continue;
                if (a.Value is HField { Object: { } owner } read && OnlyField(owner.Type) is { } only && ReferenceEquals(only, read.Field) &&
                    (wrapper == null || ReferenceEquals(wrapper, owner.Type)))
                {
                    wrapper = owner.Type;
                    field = only;
                    continue;
                }
                fine = false;
                break;
            }
            if (!fine || wrapper == null || field == null || !ReferenceEquals(field.Type, v.Type)) continue;
            // Only where the field could not be named here: a struct whose field is open to this method may
            // well have been taken apart by the method itself.
            if (AccessorFolding.IsAccessible(field, method.Method)) continue;
            lifted[v] = (wrapper, field);
        }
        if (lifted.Count == 0) return false;

        HExpr? Read(HExpr e) => e is HLocal l && lifted.TryGetValue(l.Variable, out var to)
            ? new HField { Object = new HLocal(l.Variable) { Type = to.Wrapper }, Field = to.Field, DeclaringType = to.Wrapper, Type = to.Field.Type }
            : null;
        foreach (HBlock b in method.Blocks)
            foreach (HStmt s in b.Statements)
            {
                if (s is HAssign { Target: HLocal t } a)
                {
                    if (lifted.TryGetValue(t.Variable, out var to))
                    {
                        a.Value = IsZero(a.Value) ? new HTypeExpr(HTypeOp.Default, to.Wrapper, null) { Type = to.Wrapper } : ((HField)a.Value).Object!;
                        t.Type = to.Wrapper;
                    }
                    a.Value = EnumeratorLoops.Rewrite(a.Value, Read);
                }
                else EnumeratorLoops.Rewrite(s, Read);
            }
        foreach ((HVar v, (TypeSig Wrapper, FieldDef Field) to) in lifted) v.Type = to.Wrapper;
        return true;
    }

    // ---- a struct typed by a method that another struct has too ----------------------------------------------------

    private static void Receivers(HMethod method, ProgramAnalysis program)
    {
        foreach (HVar v in method.Locals)
        {
            // The struct it was taken for: any, of which only the number it starts with is used.
            if (v.Type is null or PrimitiveSig or ByRefSig or PointerSig or GenericParamSig || v.Type.Definition is not { IsValueType: true, IsEnum: false }) continue;
            TypeLayout layout = program.Layouts.Of(v.Type);
            if (!layout.Known || layout.Fields.Length == 0) continue;
            FieldSlot start = layout.Fields.FirstOrDefault(f => f.Offset == 0);
            if (start.Field is not { } own || !ReferenceEquals(start.Type, own.Type) || own.Type is not PrimitiveSig) continue;
            bool Is(HExpr? e) => e is HLocal l && ReferenceEquals(l.Variable, v);

            int total = 0, known = 0;
            TypeSig? other = null;
            FieldDef? theirs = null;
            bool fine = true;
            var calls = new List<HCall>();
            var stores = new List<HField>();
            var clears = new List<HAssign>();
            foreach (HBlock b in method.Blocks)
                foreach (HStmt s in b.Statements)
                {
                    FinallyFolding.Visit(s, e =>
                    {
                        if (Is(e)) total++;
                        if (e is HCall c && (Is(c.This) || (c.This is HAddressOf { Target: var held } && Is(held))))
                        {
                            calls.Add(c);
                            known++;
                        }
                    });
                    switch (s)
                    {
                        case HAssign { Target: var target, Value: HTypeExpr { Op: HTypeOp.Default } } clear when Is(target):
                            clears.Add(clear);
                            known++;
                            break;
                        case HAssign { Target: HField { Object: var into } set, Value: var value } when Is(into) && ReferenceEquals(set.Field, own):
                            if (IsZero(value)) { }
                            else if (value is HField { Object: { } from } read && OnlyField(from.Type) is { } only && ReferenceEquals(only, read.Field) &&
                                     !ReferenceEquals(only.DeclaringType, own.DeclaringType) && ReferenceEquals(only.Type, own.Type) &&
                                     (other == null || ReferenceEquals(other, from.Type)))
                            {
                                other = from.Type;
                                theirs = only;
                            }
                            else fine = false;
                            stores.Add(set);
                            known++;
                            break;
                    }
                }
            bool tracing = Traced != null && method.Method.FullName.Contains(Traced, StringComparison.Ordinal);
            if (tracing)
                Console.Error.WriteLine($"[wrapper] {method.Method.FullName}: {v.Name} ({v.Type.DisplayName}): {total} uses, {known} understood, " +
                                        $"{(fine ? "" : "a store of something else, ")}filled from {other?.DisplayName ?? "nothing else"}, {calls.Count} calls" +
                                        string.Concat(calls.Select(c => $"; {c.Method.Name} [{string.Join(", ", c.Alternatives.Select(m => m.DeclaringType.Name + "." + m.Name))}]")));
            // Everything the variable is used for must be one of these: a use that was not understood is a
            // reason to leave it alone.
            if (!fine || other == null || theirs == null || total != known || calls.Count == 0) continue;

            var replacements = new List<MethodDef>();
            foreach (HCall c in calls)
            {
                // The methods with the same body: all the program has at that address (the call itself keeps only
                // those that fitted the type the variable was taken for).
                IEnumerable<MethodDef> sharing = c.Method.Address != 0 ? c.Alternatives.Concat(program.Resolve(c.Method.Address).Methods) : c.Alternatives;
                MethodDef? same = !ReferenceEquals(c.Method.DeclaringType, own.DeclaringType) || c.Virtual || c.Constrained != null ? null : sharing.FirstOrDefault(m =>
                    ReferenceEquals(m.DeclaringType, other.Definition) && m.IsStatic == c.Method.IsStatic && ReferenceEquals(m.ReturnType, c.Method.ReturnType) &&
                    m.GenericParameters.Length == 0 && m.Parameters.Length == c.Method.Parameters.Length &&
                    m.Parameters.Zip(c.Method.Parameters, (x, y) => ReferenceEquals(x.Type, y.Type)).All(agree => agree));
                if (same == null)
                {
                    fine = false;
                    break;
                }
                replacements.Add(same);
            }
            if (!fine) continue;

            for (int i = 0; i < calls.Count; i++)
            {
                HCall c = calls[i];
                MethodDef was = c.Method;
                c.Alternatives.Remove(replacements[i]);
                c.Alternatives.Add(was);
                c.Method = replacements[i];
                c.DeclaringType = other is GenericInstSig ? other : null;
            }
            foreach (HField set in stores)
            {
                set.Field = theirs;
                set.DeclaringType = other;
                set.Type = theirs.Type;
            }
            foreach (HAssign clear in clears) clear.Value = new HTypeExpr(HTypeOp.Default, other, null) { Type = other };
            foreach (HBlock b in method.Blocks)
                foreach (HStmt s in b.Statements)
                    FinallyFolding.Visit(s, e =>
                    {
                        if (Is(e)) e.Type = other;
                        else if (e is HAddressOf { Target: var held } address && Is(held)) address.Type = program.Model.Sigs.ByRef(other);
                    });
            v.Type = other;
        }
    }
}
