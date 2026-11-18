using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Calls the native code makes straight to an implementation the calling assembly cannot name, put back as the
/// call of the interface method or base method it implements.
///
/// IL2CPP calls a virtual method directly where it knows which implementation the receiver has: "Logger.Log(...)"
/// on an ILogger whose only implementation is a private class of another assembly becomes a call of that class's
/// Log. Written as that call, the C# names the class, which it may not ("is inaccessible due to its protection
/// level"), and casts the receiver to it. The source cannot have named the class either: it called the method
/// through what it could name, the interface (or a base class), and that call reaches the same code on the same
/// object. Which method that is, the vtable says: the slot of the implementation lies in the range of one of the
/// class's interfaces, or is the slot of a method of a base class.
///
/// A variable of such a class that is only given values of one type the method can name, and is only called
/// through that type (or compared), takes that type.
/// </summary>
internal static class HiddenImplementations
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_HIDDEN_IMPLEMENTATIONS") != null;

    public static void Run(HMethod method, ProgramAnalysis program)
    {
        if (Disabled) return;
        AssemblyModel from = method.Method.DeclaringType.Assembly;
        SigFactory sigs = program.Model.Sigs;
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
                FinallyFolding.Visit(s, e =>
                {
                    if (e is not HCall { Virtual: false, This: not null, Constrained: null } call || call.Method.IsStatic ||
                        !call.Method.IsVirtual || !call.Method.HasSlot || Reachable(call.Method, from)) return;
                    if (Implemented(call.Method, call.DeclaringType, from, sigs) is not { } found) return;
                    var (target, declaring) = found;
                    call.Method = target;
                    call.DeclaringType = declaring;
                    call.Virtual = true;
                    call.Alternatives.Clear();
                });
        // (Also where the call was virtual already: a field of the class read in place, put back as the getter
        // that returns it as the interface, left the variable with the field's type.)
        Retype(method, from, sigs);
    }

    /// <summary>
    /// The interface or base-class method a virtual method implements that the assembly can name, with its
    /// declaring type as the receiver sees it (instantiated); null when there is none or more than one.
    /// </summary>
    private static (MethodDef Method, TypeSig? Declaring)? Implemented(MethodDef impl, TypeSig? declaringSig, AssemblyModel from, SigFactory sigs)
    {
        TypeDef owner = impl.DeclaringType;
        TypeSig[] classArgs = declaringSig is GenericInstSig g ? g.Arguments : [];
        int slot = impl.Slot;
        (MethodDef, TypeSig?)? found = null;
        foreach (var (iface, offset) in owner.InterfaceOffsets)
        {
            if (slot < offset || iface.Definition is not { } def) continue;
            MethodDef? m = def.Methods.FirstOrDefault(x => x.HasSlot && x.Slot == slot - offset && !x.IsStatic);
            if (m == null || !Reachable(m, from)) continue;
            if (found != null) return null;
            TypeSig instantiated = sigs.Substitute(iface, classArgs, []);
            found = (m, instantiated is GenericInstSig ? instantiated : null);
        }
        if (found != null) return found;
        // An override: the method of the nearest base class with the slot, that the assembly can name.
        for (TypeSig? baseSig = owner.BaseType; baseSig?.Definition is { } baseDef; baseSig = baseDef.BaseType)
        {
            MethodDef? m = baseDef.Methods.FirstOrDefault(x => x.HasSlot && x.Slot == slot && x.IsVirtual && !x.IsStatic && x.Name == impl.Name);
            if (m == null || !Reachable(m, from)) continue;
            TypeSig instantiated = sigs.Substitute(baseSig, classArgs, []);
            return (m, instantiated is GenericInstSig ? instantiated : null);
        }
        return null;
    }

    /// <summary>Code of the assembly can name the type: its own, or public all the way out.</summary>
    internal static bool Reachable(TypeDef type, AssemblyModel from)
    {
        if (type.Assembly == from) return true;
        for (TypeDef? t = type; t != null; t = t.DeclaringType)
        {
            uint visibility = t.Flags & TypeDef.VisibilityMask;
            if (t.DeclaringType == null ? visibility != 1 : visibility != 2) return false; // Public, NestedPublic
        }
        return true;
    }

    /// <summary>
    /// The method can be called by the assembly's code: a method of the assembly, or a public one, or a
    /// protected one (callable from derived classes: left as it is) of a type it can name.
    /// </summary>
    private static bool Reachable(MethodDef m, AssemblyModel from)
    {
        if (!Reachable(m.DeclaringType, from)) return false;
        if (m.DeclaringType.Assembly == from) return true;
        int access = m.Flags & MethodDef.AccessMask;
        return access is 6 or 4 or 5; // Public, Family, FamORAssem
    }

    /// <summary>A variable of a type the method cannot name, given one type it can and used only through that one.</summary>
    private static void Retype(HMethod method, AssemblyModel from, SigFactory sigs)
    {
        var candidates = method.Locals.Where(v => v.Type?.Definition is { } d && !Reachable(d, from) && !v.AddressTaken).ToHashSet();
        if (candidates.Count == 0) return;
        var given = new Dictionary<HVar, TypeSig?>();
        var allowed = new HashSet<HExpr>(ReferenceEqualityComparer.Instance);
        var spoiled = new HashSet<HVar>();
        var wanted = new Dictionary<HVar, List<TypeSig>>();
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
            {
                if (s is HAssign { Target: HLocal { Variable: var v } target, Value: var value } && candidates.Contains(v))
                {
                    allowed.Add(target);
                    // (What a call returns is what its method says it returns: the call may carry a narrower type,
                    // the field's that the getter returns.)
                    TypeSig? type = value switch
                    {
                        HConst { Value: null } => null,
                        HCall { Method.ReturnType: { ContainsGenericParameter: false } returned } => returned,
                        _ => value.Type,
                    };
                    if (type != null && (type.Definition is not { } d || !Reachable(d, from) || type.IsValueType)) spoiled.Add(v);
                    else if (type != null)
                    {
                        if (given.TryGetValue(v, out TypeSig? before) && before != null && before.Key != type.Key) spoiled.Add(v);
                        else given[v] = type;
                    }
                }
                FinallyFolding.Visit(s, e =>
                {
                    switch (e)
                    {
                        case HCall { This: HLocal { Variable: var v } receiver, Virtual: true } call when candidates.Contains(v):
                            allowed.Add(receiver);
                            if (!wanted.TryGetValue(v, out List<TypeSig>? list)) wanted[v] = list = [];
                            list.Add(call.DeclaringType ?? call.Method.DeclaringType.Sig);
                            break;
                        case HCompare { Left: var l, Right: var r }:
                            if (l is HLocal { Variable: var lv } && candidates.Contains(lv)) allowed.Add(l);
                            if (r is HLocal { Variable: var rv } && candidates.Contains(rv)) allowed.Add(r);
                            break;
                    }
                });
            }
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
                FinallyFolding.Visit(s, e =>
                {
                    if (e is HLocal { Variable: var v } && candidates.Contains(v) && !allowed.Contains(e)) spoiled.Add(v);
                });
        foreach (HVar v in candidates)
        {
            if (spoiled.Contains(v) || !given.TryGetValue(v, out TypeSig? type) || type == null) continue;
            if (wanted.TryGetValue(v, out List<TypeSig>? uses) && !uses.All(u => Converts(type, u, sigs))) continue;
            v.Type = type;
            foreach (HBlock block in method.Blocks)
                foreach (HStmt s in block.Statements)
                    FinallyFolding.Visit(s, e =>
                    {
                        if (e is HLocal { Variable: var same } local && ReferenceEquals(same, v)) local.Type = type;
                    });
        }
    }

    /// <summary>A value of <paramref name="from"/> is a <paramref name="to"/>: the same type, a base class or an interface of it.</summary>
    private static bool Converts(TypeSig from, TypeSig to, SigFactory sigs, int depth = 0)
    {
        if (from.Key == to.Key) return true;
        if (depth > 16 || from.Definition is not { } def) return false;
        TypeSig[] args = from is GenericInstSig g ? g.Arguments : [];
        if (def.BaseType is { } b && Converts(sigs.Substitute(b, args, []), to, sigs, depth + 1)) return true;
        foreach (TypeSig i in def.Interfaces)
            if (Converts(sigs.Substitute(i, args, []), to, sigs, depth + 1)) return true;
        return false;
    }
}
