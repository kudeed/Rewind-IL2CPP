using System.Runtime.CompilerServices;
using Rewind.Model;

namespace Rewind.Analysis;

/// <summary>
/// What the code of an assembly can refer to, by the assembly references its metadata lists.
///
/// IL names a type or a member through a reference to the assembly that defines it, and the compiler writes one
/// for every assembly it names anything of: a type that IL of this assembly names comes from the assembly itself
/// or from one it refers to directly (or through a facade that only forwards). Machine code is less strict - a
/// method pasted in from a library can call into that library's own libraries - so for which function is called,
/// the assemblies reached through references of references count too.
/// Where the metadata lists no references for an assembly at all, nothing is ruled out.
/// </summary>
public static class AssemblyScope
{
    public static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_REACHABLE_ASSEMBLIES") != null;
    private static readonly ConditionalWeakTable<AssemblyModel, HashSet<AssemblyModel>> DirectSets = new(), ClosureSets = new();

    /// <summary>Whether IL of <paramref name="from"/> can name a type or member of <paramref name="to"/>.</summary>
    public static bool Names(AssemblyModel from, AssemblyModel to)
    {
        if (Disabled || ReferenceEquals(from, to) || from.References.Count == 0) return true;
        return DirectSets.GetValue(from, Direct).Contains(to);
    }

    /// <summary>Whether code of <paramref name="from"/> can end up running code of <paramref name="to"/> directly.</summary>
    public static bool Reaches(AssemblyModel from, AssemblyModel to)
    {
        if (Disabled || ReferenceEquals(from, to) || from.References.Count == 0) return true;
        return ClosureSets.GetValue(from, Closure).Contains(to);
    }

    /// <summary>Whether IL of <paramref name="from"/> can name a type, its type arguments and what it is made of included.</summary>
    public static bool Names(AssemblyModel from, TypeSig? type, int depth = 0)
    {
        if (Disabled || type == null || depth > 16) return true;
        if (type.ElementType is { } element) return Names(from, element, depth + 1);
        if (type is GenericInstSig g && g.Arguments.Any(a => !Names(from, a, depth + 1))) return false;
        return type.Definition is not { } definition || Names(from, definition.Assembly);
    }

    private static HashSet<AssemblyModel> Direct(AssemblyModel from)
    {
        var set = new HashSet<AssemblyModel> { from };
        var pending = new Stack<AssemblyModel>();
        foreach (AssemblyModel reference in from.References)
            if (set.Add(reference))
                pending.Push(reference);
        // A facade (an assembly with no types of its own) only forwards to what it refers to.
        while (pending.Count > 0)
        {
            AssemblyModel facade = pending.Pop();
            if (facade.Types.Count != 0) continue;
            foreach (AssemblyModel reference in facade.References)
                if (set.Add(reference))
                    pending.Push(reference);
        }
        return set;
    }

    private static HashSet<AssemblyModel> Closure(AssemblyModel from)
    {
        var set = new HashSet<AssemblyModel> { from };
        var pending = new Stack<AssemblyModel>();
        pending.Push(from);
        while (pending.Count > 0)
            foreach (AssemblyModel reference in pending.Pop().References)
                if (set.Add(reference))
                    pending.Push(reference);
        return set;
    }
}
