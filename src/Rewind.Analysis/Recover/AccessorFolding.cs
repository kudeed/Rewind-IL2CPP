using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Finds, for a field, the method of its class that does nothing but read (or write) it. Such accessors are
/// what callers in other classes actually used; the compiler inlined them, leaving a bare field access that
/// the source could not have contained.
/// </summary>
public sealed class AccessorIndex(ProgramAnalysis program)
{
    private readonly Dictionary<FieldDef, MethodDef?> _getters = [], _setters = [];
    private MethodPipeline? _pipeline;
    private bool _busy;

    private HMethod? Body(MethodDef method, MethodInst? inst)
    {
        // Accessors are a handful of instructions (a static one first makes sure its class is initialized);
        // anything longer is not one.
        if (program.Code.Get(inst?.Address ?? method.Address) is not { Instructions: <= 32 }) return null;
        _pipeline ??= new MethodPipeline(program);
        try
        {
            HMethod h = inst != null ? _pipeline.Recover(inst) : _pipeline.Recover(method);
            return h.Problems.Count == 0 && h.Blocks.Count == 1 ? h : null;
        }
        catch (Exception)
        {
            return null;
        }
    }

    /// <summary>
    /// The recovered bodies to judge a method by. A method of a generic class has no body of its own, only per
    /// instantiation; an accessor does the same thing whatever the type arguments are, but not every
    /// instantiation shows it as plainly (a large struct is moved in pieces), so a few are looked at.
    /// </summary>
    private IEnumerable<HMethod> Bodies(MethodDef method)
    {
        if (method.Address != 0)
        {
            if (Body(method, null) is { } own) yield return own;
            yield break;
        }
        var seen = new HashSet<ulong>();
        foreach (MethodInst inst in program.InstsOf(method))
        {
            if (inst.Address == 0 || !seen.Add(inst.Address)) continue;
            if (Body(method, inst) is { } body) yield return body;
            if (seen.Count >= 6) yield break;
        }
    }

    private static readonly bool NoWiderGetters = Environment.GetEnvironmentVariable("REWIND_NO_WIDER_GETTERS") != null;

    /// <summary>
    /// Whether a getter's type may be a wider view of what a field holds: both are references (an object as
    /// one of its interfaces or base classes). That it is - that the getter returns the field's object as it
    /// is - is told by its code, which must be "return this.field" and nothing else.
    /// </summary>
    private static bool Wider(TypeSig returned, TypeSig held) =>
        !NoWiderGetters && !returned.IsVoid && !returned.IsValueType && !held.IsValueType &&
        returned is not (PointerSig or ByRefSig or GenericParamSig) && held is not (PointerSig or ByRefSig or GenericParamSig);

    private static bool IsFieldOfThis(HExpr e, FieldDef field) =>
        e is HField f && ReferenceEquals(f.Field, field) && (field.IsStatic ? f.Object == null : f.Object is HArg { Index: -1 });

    private MethodDef? Find(FieldDef field, bool setter)
    {
        if (_busy) return null; // asked while recovering an accessor: no answer rather than recursion
        _busy = true;
        try
        {
            MethodDef? found = null;
            foreach (MethodDef m in field.DeclaringType.Methods)
            {
                if (m.IsStatic != field.IsStatic || m.IsAbstract || m.GenericParameters.Length != 0 || m.IsConstructor) continue;
                if (setter ? m.Parameters.Length != 1 || !m.ReturnType.IsVoid || !ReferenceEquals(m.Parameters[0].Type, field.Type)
                           : m.Parameters.Length != 0 || !(ReferenceEquals(m.ReturnType, field.Type) || Wider(m.ReturnType, field.Type))) continue;
                bool matches = false;
                foreach (HMethod body in Bodies(m))
                {
                    List<HStmt> statements = body.Blocks[0].Statements;
                    matches = setter
                        ? statements.Count == 2 && statements[0] is HAssign a && IsFieldOfThis(a.Target, field) && a.Value is HArg { Index: 0 } && statements[1] is HReturn { Value: null }
                        : statements.Count == 1 && statements[0] is HReturn { Value: { } value } && IsFieldOfThis(value, field);
                    if (matches) break;
                }
                if (!matches) continue;
                // Prefer the property accessor when several methods happen to do the same.
                if (found == null || (m.Name.StartsWith(setter ? "set_" : "get_", StringComparison.Ordinal) && !found.Name.StartsWith(setter ? "set_" : "get_", StringComparison.Ordinal)))
                    found = m;
            }
            return found;
        }
        finally
        {
            _busy = false;
        }
    }

    /// <summary>The property's name when the field is the storage the compiler made for an automatic property.</summary>
    public static string? AutoPropertyName(FieldDef field)
    {
        const string tail = ">k__BackingField";
        string name = field.Name;
        return name.Length > tail.Length + 1 && name[0] == '<' && name.EndsWith(tail, StringComparison.Ordinal) ? name[1..^tail.Length] : null;
    }

    public static bool IsBackingField(FieldDef field) => AutoPropertyName(field) != null;

    /// <summary>
    /// The accessor of an automatic property, found by name: its storage is named after it, and there is no
    /// need to look at what the accessor does.
    /// </summary>
    private static MethodDef? AutoAccessor(FieldDef field, bool setter)
    {
        if (AutoPropertyName(field) is not { } property) return null;
        foreach (PropertyDef p in field.DeclaringType.Properties)
        {
            if (!string.Equals(p.Name, property, StringComparison.Ordinal)) continue;
            MethodDef? accessor = setter ? p.Setter : p.Getter;
            if (accessor != null && accessor.IsStatic == field.IsStatic && accessor.Parameters.Length == (setter ? 1 : 0)) return accessor;
        }
        return null;
    }

    public MethodDef? GetterOf(FieldDef field)
    {
        if (_getters.TryGetValue(field, out MethodDef? known)) return known;
        if (IsBackingField(field)) return _getters[field] = AutoAccessor(field, setter: false);
        if (_busy) return null;
        return _getters[field] = Find(field, setter: false);
    }

    public MethodDef? SetterOf(FieldDef field)
    {
        if (_setters.TryGetValue(field, out MethodDef? known)) return known;
        if (IsBackingField(field)) return _setters[field] = AutoAccessor(field, setter: true);
        if (_busy) return null;
        return _setters[field] = Find(field, setter: true);
    }
}

/// <summary>
/// Rewrites accesses to fields the current method could not legally name (private to another class) into the
/// accessor calls they were inlined from.
/// </summary>
public static class AccessorFolding
{
    private static bool Within(TypeDef inner, TypeDef outer)
    {
        for (TypeDef? t = inner; t != null; t = t.DeclaringType)
            if (ReferenceEquals(t, outer))
                return true;
        return false;
    }

    private static bool Derives(TypeDef type, TypeDef ancestor)
    {
        int guard = 0;
        for (TypeDef? t = type; t != null && guard++ < 64; t = t.BaseType?.Definition)
            if (ReferenceEquals(t, ancestor))
                return true;
        return false;
    }

    /// <summary>Whether a class between this one and the method's own (this one included) has its own version of a virtual method.</summary>
    private static bool Overridden(MethodDef method, TypeDef from)
    {
        if (!method.HasSlot) return false;
        int guard = 0;
        for (TypeDef? t = from; t != null && guard++ < 64 && !ReferenceEquals(t, method.DeclaringType); t = t.BaseType?.Definition)
            foreach (MethodDef m in t.Methods)
                if (m.IsVirtual && !m.IsStatic && m.HasSlot && m.Slot == method.Slot)
                    return true;
        return false;
    }

    public static bool IsAccessible(FieldDef field, MethodDef from)
    {
        TypeDef user = from.DeclaringType, owner = field.DeclaringType;
        bool sameAssembly = ReferenceEquals(user.Assembly, owner.Assembly);
        bool family = false;
        for (TypeDef? t = user; t != null && !family; t = t.DeclaringType) family = Derives(t, owner);
        return (field.Attrs & FieldDef.AccessMask) switch
        {
            6 => true,
            1 => Within(user, owner),
            3 => sameAssembly,
            4 => family || Within(user, owner),
            5 => family || sameAssembly,
            2 => family && sameAssembly,
            _ => Within(user, owner),
        };
    }

    public static void Run(HMethod method, ProgramAnalysis program)
    {
        AccessorIndex index = program.Accessors;
        MethodDef current = method.Method;
        var unfolded = new HashSet<FieldDef>();

        // The storage of an automatic property has no name in source. Outside the accessors, every use of it was
        // a use of the property - in the class itself too. Only a constructor of the class writes it directly:
        // an initializer, or the assignment of a property without a setter.
        bool Nameable(FieldDef field) => !AccessorIndex.IsBackingField(field) && IsAccessible(field, current);
        bool OwnConstructor(FieldDef field) => current.IsConstructor && ReferenceEquals(current.DeclaringType, field.DeclaringType);

        // The storage of a base class's property, used on "this" in a class that has its own version of the
        // accessor: the source said "base.X". (A virtual call there would come back to the class's own version -
        // in that version itself, without end.)
        bool ViaBase(MethodDef accessor, HExpr? on) =>
            accessor.IsVirtual && !accessor.IsStatic && !current.IsStatic && on is HArg { Index: -1 } &&
            !ReferenceEquals(current.DeclaringType, accessor.DeclaringType) && Derives(current.DeclaringType, accessor.DeclaringType) &&
            Overridden(accessor, current.DeclaringType);

        HCall? Getter(HField f)
        {
            if (index.GetterOf(f.Field) is not { } getter || ReferenceEquals(getter, current)) return null;
            return new HCall { Method = getter, DeclaringType = f.DeclaringType is GenericInstSig ? f.DeclaringType : null, This = f.Object, Arguments = [], Virtual = getter.IsVirtual && !ViaBase(getter, f.Object), Type = f.Type };
        }

        // What a field is reached through, when the field is written or its address is taken: a struct that
        // sits in a field or an array element stays that place (a copy of it would take the write); anything
        // else is a value that is read.
        static bool HoldsStruct(HExpr e) => e is HField or HElement && e.Type is { IsValueType: true } and not (PointerSig or PrimitiveSig or OpaqueSig);
        HExpr Owner(HExpr e) => HoldsStruct(e) ? Place(e) : Read(e);

        HExpr Place(HExpr e)
        {
            switch (e)
            {
                case HField f:
                    if (f.Object != null) f.Object = Owner(f.Object);
                    return f;
                case HElement el: el.Array = Read(el.Array); el.Index = Read(el.Index); return el;
                case HDeref d: d.Pointer = Read(d.Pointer); return d;
                default: return Read(e);
            }
        }

        // The storage of an automatic property where only its value is wanted (the receiver of a struct method,
        // an argument passed by "in" reference): the source had the property there, and the call got a copy.
        HExpr? ValueOfStorage(HExpr e)
        {
            if (e is not HField f || !AccessorIndex.IsBackingField(f.Field)) return null;
            if (f.Object != null) f.Object = Owner(f.Object);
            return Getter(f);
        }

        void Arguments(MethodDef callee, HExpr[] arguments)
        {
            for (int i = 0; i < arguments.Length; i++)
            {
                HExpr a = arguments[i];
                if (a == null) continue;
                ParamDef? parameter = i < callee.Parameters.Length ? callee.Parameters[i] : null;
                if (parameter is { Type: ByRefSig })
                {
                    // Passed by reference: a place, not a value. Only "in" can take the value of a property.
                    HExpr target = a is HAddressOf address ? address.Target : a;
                    if (target is HField && parameter.IsIn && ValueOfStorage(target) is { } copy)
                    {
                        if (a is HAddressOf wrapper) wrapper.Target = copy;
                        else arguments[i] = new HAddressOf(copy) { Type = parameter.Type };
                        continue;
                    }
                    if (a is HAddressOf at) { at.Target = Place(at.Target); continue; }
                    if (a is HField or HElement) { arguments[i] = Place(a); continue; }
                }
                arguments[i] = Read(a);
            }
        }

        HExpr Read(HExpr e)
        {
            switch (e)
            {
                case HField f:
                    if (f.Object != null) f.Object = Read(f.Object);
                    if (Nameable(f.Field)) return f;
                    if (Getter(f) is { } get) return get;
                    if (!IsAccessible(f.Field, current)) unfolded.Add(f.Field);
                    return f;
                case HElement el: el.Array = Read(el.Array); el.Index = Read(el.Index); return el;
                case HArrayLength len: len.Array = Read(len.Array); return len;
                case HAddressOf a:
                    // The address of a field cannot go through an accessor; only look inside.
                    a.Target = Place(a.Target);
                    return a;
                case HDeref d: d.Pointer = Read(d.Pointer); return d;
                case HUnary u: u.Operand = Read(u.Operand); return u;
                case HBinary b: b.Left = Read(b.Left); b.Right = Read(b.Right); return b;
                case HCompare c: c.Left = Read(c.Left); c.Right = Read(c.Right); return c;
                case HConv c: c.Operand = Read(c.Operand); return c;
                case HCall call:
                    if (call.This != null)
                    {
                        // A struct receiver is a location (its address is taken), not a value to read through a
                        // getter - unless it is the storage of a property, which the source could only call on.
                        if (!call.Method.DeclaringType.IsValueType || call.This is not (HField or HElement)) call.This = Read(call.This);
                        else if (!call.Method.IsConstructor && ValueOfStorage(call.This) is { } copy) call.This = copy;
                        else call.This = Place(call.This);
                    }
                    Arguments(call.Method, call.Arguments);
                    return call;
                case HNewObject n:
                    Arguments(n.Constructor, n.Arguments);
                    return n;
                case HNewArray na: na.Length = Read(na.Length); return na;
                case HTypeExpr t: if (t.Operand != null) t.Operand = Read(t.Operand); return t;
                case HSelect s: s.Condition = Read(s.Condition); s.WhenTrue = Read(s.WhenTrue); s.WhenFalse = Read(s.WhenFalse); return s;
                case HOpaque o:
                    for (int i = 0; i < o.Operands.Length; i++) o.Operands[i] = Read(o.Operands[i]);
                    return o;
                default: return e;
            }
        }

        foreach (HBlock block in method.Blocks)
        {
            for (int i = 0; i < block.Statements.Count; i++)
            {
                switch (block.Statements[i])
                {
                    case HAssign a:
                        a.Value = Read(a.Value);
                        if (a.Target is HField f)
                        {
                            if (f.Object != null) f.Object = Owner(f.Object);
                            if (Nameable(f.Field) || (AccessorIndex.IsBackingField(f.Field) && OwnConstructor(f.Field))) break;
                            if (index.SetterOf(f.Field) is { } setter && !ReferenceEquals(setter, current))
                            {
                                var call = new HCall { Method = setter, DeclaringType = f.DeclaringType is GenericInstSig ? f.DeclaringType : null, This = f.Object, Arguments = [a.Value], Virtual = setter.IsVirtual && !ViaBase(setter, f.Object), Type = setter.ReturnType };
                                block.Statements[i] = new HEval(call) { Address = a.Address };
                            }
                            else if (!IsAccessible(f.Field, current)) unfolded.Add(f.Field);
                        }
                        else if (a.Target is HElement el) { el.Array = Read(el.Array); el.Index = Read(el.Index); }
                        else if (a.Target is HDeref d) d.Pointer = Read(d.Pointer);
                        break;
                    case HEval e: e.Expression = Read(e.Expression); break;
                    case HReturn r: if (r.Value != null) r.Value = Read(r.Value); break;
                    case HThrow t: if (t.Exception != null) t.Exception = Read(t.Exception); break;
                    case HBranch b: b.Condition = Read(b.Condition); break;
                    case HSwitch sw: sw.Value = Read(sw.Value); break;
                }
            }
        }

        // What remains is code of another class that was inlined here and not folded back: correct in what it
        // does, but not something the source of this method contained.
        if (unfolded.Count != 0)
            method.Notes.Add("contains inlined code of " + string.Join(", ", unfolded.Select(f => f.DeclaringType.Name).Distinct().Take(4)) +
                             " (private members shown directly)");
    }
}
