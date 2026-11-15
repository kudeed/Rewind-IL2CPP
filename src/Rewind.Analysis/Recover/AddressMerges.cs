using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Removes variables that only ever hold the address of one local.
///
/// Where two paths meet, the machine code has "the address of the bounds" in a register on both - handed back
/// by the call that filled them on each path - and what follows reads through that register. Translated
/// literally that is a reference variable given the same address in two places: correct, but not something
/// C# lets one write (a reference to a local cannot be put into a variable declared before it), and not what
/// was written - the code after the two paths simply uses the local.
///
/// A variable whose every assignment gives it the address of the same place inside a local (the local itself,
/// or a field of a struct held in it) is replaced by that address wherever it is read. The address of a local
/// is the same wherever it is taken, so it does not matter which assignment a read follows.
/// </summary>
internal static class AddressMerges
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_ADDRESS_MERGES") != null;

    private static bool IsStruct(TypeSig? t) => t is { IsValueType: true } and not (PrimitiveSig or PointerSig or ByRefSig or OpaqueSig) && t.Definition is { IsEnum: false };

    /// <summary>The variable a place lies in: the place itself, or a chain of fields of structs held in it.</summary>
    private static HVar? RootOf(HExpr place)
    {
        HExpr e = place;
        while (e is HField { Object: { } owner } field && !field.Field.IsStatic && IsStruct(owner.Type)) e = owner;
        return e is HLocal l ? l.Variable : null;
    }

    private static HExpr Clone(HExpr place) => place switch
    {
        HLocal l => new HLocal(l.Variable) { Type = l.Type },
        HField f => new HField { Object = Clone(f.Object!), Field = f.Field, DeclaringType = f.DeclaringType, Type = f.Type },
        _ => place,
    };

    public static bool Run(HMethod method)
    {
        if (Disabled || method.Blocks.Count == 0) return false;
        // What each variable is given: the one place whose address it always is, or null for anything else.
        var places = new Dictionary<HVar, HExpr?>();
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
            {
                if (s is not HAssign { Target: HLocal { Variable: var variable } } assignment) continue;
                if (places.TryGetValue(variable, out HExpr? known) && known == null) continue;
                HExpr? place = assignment.Value is HAddressOf { Target: var target } && RootOf(target) is { } root && !ReferenceEquals(root, variable) ? target : null;
                places[variable] = place != null && (known == null || HirCleanup.Same(known, place)) ? known ?? place : null;
            }
        foreach (HTryRegion region in method.TryRegions.Values) places.Remove(region.Exception);
        var chosen = new Dictionary<HVar, HExpr>();
        foreach (var (variable, place) in places)
            if (place != null && !variable.AddressTaken && variable.Type is ByRefSig or PointerSig)
                chosen[variable] = place;
        if (chosen.Count == 0) return false;
        // A variable used in any other way than read (its own address taken, say) stays.
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
                FinallyFolding.Visit(s, e =>
                {
                    if (e is HAddressOf { Target: HLocal { Variable: var taken } }) chosen.Remove(taken);
                });
        if (chosen.Count == 0) return false;

        HExpr? Map(HExpr e)
        {
            switch (e)
            {
                case HDeref { Pointer: HLocal { Variable: var through } } when chosen.TryGetValue(through, out HExpr? place):
                    return Clone(place);
                case HField { Object: HLocal { Variable: var owner } } field when chosen.TryGetValue(owner, out HExpr? place):
                    return new HField { Object = Clone(place), Field = field.Field, DeclaringType = field.DeclaringType, Type = field.Type };
                case HLocal { Variable: var read } local when chosen.TryGetValue(read, out HExpr? place):
                    return new HAddressOf(Clone(place)) { Type = local.Type };
                default:
                    return null;
            }
        }

        foreach (HBlock block in method.Blocks)
        {
            block.Statements.RemoveAll(s => s is HAssign { Target: HLocal { Variable: var given } } && chosen.ContainsKey(given));
            foreach (HStmt s in block.Statements) EnumeratorLoops.Rewrite(s, Map);
        }
        return true;
    }
}
