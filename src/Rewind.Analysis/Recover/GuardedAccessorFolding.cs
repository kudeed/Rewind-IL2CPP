using System.Text.RegularExpressions;
using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Puts inlined accessors of networked properties back.
///
/// Photon Fusion rewrites every "[Networked] T Name { get; set; }" at build time: the accessors become
/// "if (Ptr == null) throw new InvalidOperationException("Error when accessing Class.Name. ..."); " followed by
/// a read or write of the object's replicated memory at the property's offset. The C++ compiler then pastes
/// those accessors into their callers. What the callers show is the check and the raw memory access; what they
/// were written as is the property - and only that compiles against the class as its source declares it.
///
/// Here the accessors of such properties are recovered from their own machine code, and wherever a method
/// contains what one of them computes (or stores), on whatever object, the property is used instead. The checks
/// that belonged to the pasted accessors go: the property makes them itself.
/// </summary>
internal sealed class GuardedAccessorFolding(MethodPipeline pipeline)
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_NETWORKED_FOLD") != null;
    /// <summary>REWIND_NETWORKED_TRACE=text: says on the error stream what was made of the accessors of "Class.property" names containing the text.</summary>
    private static readonly string? Traced = Environment.GetEnvironmentVariable("REWIND_NETWORKED_TRACE");
    private static readonly Regex Message = new(@"^Error when accessing .+\.([^. ]+)\. Networked properties can only be accessed when Spawned\(\) has been called\.$", RegexOptions.Compiled);

    private sealed class Accessor
    {
        public required PropertyDef Property;
        public MethodDef? Getter, Setter;
        /// <summary>What the getter returns, written in terms of its "this".</summary>
        public HExpr? Value;
        /// <summary>The setter's one statement, written in terms of its "this" and its argument.</summary>
        public HAssign? Store;
    }

    private readonly Dictionary<TypeDef, List<Accessor>> _own = [];
    private readonly Dictionary<TypeDef, List<Accessor>> _all = [];

    private static bool IsStorageField(FieldDef f) =>
        f.Name == "Ptr" && f.DeclaringType is { Name: "NetworkBehaviour", Namespace: "Fusion", DeclaringType: null };

    private static bool IsZero(HExpr e) => e is HConst { Value: null or 0 or 0L };

    /// <summary>"x.Ptr == null" (or "!= null"): the object, and whether the test is for null.</summary>
    private static bool IsStorageTest(HExpr condition, out HExpr? owner, out bool whenNull)
    {
        owner = null;
        whenNull = false;
        bool negated = false;
        while (condition is HUnary { Op: HUnaryOp.LogicalNot } not)
        {
            negated = !negated;
            condition = not.Operand;
        }
        if (condition is not HCompare { Op: HCompareOp.Eq or HCompareOp.Ne } c) return false;
        HExpr? field = IsZero(c.Right) ? c.Left : IsZero(c.Left) ? c.Right : null;
        if (field is not HField { Object: { } o } f || !IsStorageField(f.Field)) return false;
        owner = o;
        whenNull = (c.Op == HCompareOp.Eq) != negated;
        return true;
    }

    /// <summary>A block that does nothing but throw the "accessed before Spawned()" exception.</summary>
    private static bool IsRefusal(HBlock block) => RefusedProperty(block) != null;

    /// <summary>The property such a block names, or null when the block is something else.</summary>
    private static string? RefusedProperty(HBlock block)
    {
        HExpr? thrown = block.Statements switch
        {
            [HAssign { Target: HLocal made, Value: var value }, HThrow { Exception: HLocal t }] when ReferenceEquals(made.Variable, t.Variable) => value,
            [HThrow { Exception: { } direct }] => direct,
            _ => null,
        };
        if (thrown is not HNewObject { Constructor.DeclaringType.Name: "InvalidOperationException", Arguments: [HConst { Value: string text }] }) return null;
        System.Text.RegularExpressions.Match m = Message.Match(text);
        return m.Success ? m.Groups[1].Value : null;
    }

    /// <summary>The property whose pasted accessor a block's check belongs to, or null.</summary>
    private static string? GuardedProperty(HBlock block)
    {
        if (block.Statements is not [.., HBranch branch] || !IsStorageTest(branch.Condition, out _, out bool whenNull)) return null;
        return RefusedProperty(whenNull ? branch.WhenTrue : branch.WhenFalse);
    }

    /// <summary>The block an accessor's check leads to when the object has its memory, or null when the block is no such check.</summary>
    private static HBlock? Guarded(HBlock block)
    {
        if (block.Statements is not [.., HBranch branch] || !IsStorageTest(branch.Condition, out _, out bool whenNull)) return null;
        HBlock refusal = whenNull ? branch.WhenTrue : branch.WhenFalse, access = whenNull ? branch.WhenFalse : branch.WhenTrue;
        return IsRefusal(refusal) ? access : null;
    }

    private List<Accessor> OwnAccessors(TypeDef type)
    {
        if (_own.TryGetValue(type, out List<Accessor>? known)) return known;
        var list = new List<Accessor>();
        _own[type] = list;
        if (type.GenericParameters.Length != 0) return list;
        foreach (PropertyDef p in type.Properties)
        {
            var a = new Accessor { Property = p };
            if (p.Getter is { IsStatic: false, Parameters.Length: 0, Address: not 0 } getter && pipeline.CoreBody(getter) is { } get &&
                get.Blocks.Count != 0 && get.Blocks[0].Statements.Count == 1 && Guarded(get.Blocks[0]) is { } reading)
            {
                // The getter may itself keep the address it reads through in a variable.
                if (reading.Statements is not [HReturn] && pipeline.FreshCoreBody(getter) is { } own)
                {
                    Unhold(own);
                    if (own.Blocks.Count != 0 && Guarded(own.Blocks[0]) is { } again) reading = again;
                }
                if (reading.Statements is [HReturn { Value: { } value }])
                {
                    a.Getter = getter;
                    a.Value = value;
                }
            }
            if (p.Setter is { IsStatic: false, Parameters.Length: 1, Address: not 0 } setter && pipeline.CoreBody(setter) is { } set &&
                set.Blocks.Count != 0 && set.Blocks[0].Statements.Count == 1 && Guarded(set.Blocks[0]) is { } guarded)
            {
                // The setter may itself keep the address it stores through in a variable.
                if (guarded.Statements is not [HAssign, HReturn] && pipeline.FreshCoreBody(setter) is { } own)
                {
                    Unhold(own);
                    if (own.Blocks.Count != 0 && Guarded(own.Blocks[0]) is { } again) guarded = again;
                }
                if (guarded.Statements is [HAssign { Target: HDeref } store, HReturn { Value: null }])
                {
                    a.Setter = setter;
                    a.Store = store;
                }
            }
            if (a.Getter != null || a.Setter != null) list.Add(a);
            if (Traced != null && (type.Name + "." + p.Name).Contains(Traced, StringComparison.Ordinal))
            {
                Console.Error.WriteLine($"[networked] {type.Name}.{p.Name}: getter {(a.Getter != null ? "read as " + HirPrinter.Print(a.Value!, null!) : "not recognized")}, setter {(a.Setter != null ? "recognized" : "not recognized")}");
                if (a.Getter == null && p.Getter is { Address: not 0 } g && pipeline.CoreBody(g) is { } shown) Console.Error.WriteLine(HirPrinter.Print(shown));
                if (a.Setter == null && p.Setter is { Address: not 0 } s && pipeline.CoreBody(s) is { } shown2) Console.Error.WriteLine(HirPrinter.Print(shown2));
            }
        }
        return list;
    }

    /// <summary>The networked properties of a class, its base classes' included.</summary>
    private List<Accessor> Accessors(TypeDef type)
    {
        if (_all.TryGetValue(type, out List<Accessor>? known)) return known;
        var list = new List<Accessor>();
        int guard = 0;
        for (TypeDef? t = type; t != null && guard++ < 32; t = t.BaseType?.Definition) list.AddRange(OwnAccessors(t));
        return _all[type] = list;
    }

    private static bool SameConst(object? a, object? b) => (a, b) switch
    {
        (int x, long y) => x == y,
        (long x, int y) => x == y,
        (float x, float y) => BitConverter.SingleToInt32Bits(x) == BitConverter.SingleToInt32Bits(y),
        (double x, double y) => BitConverter.DoubleToInt64Bits(x) == BitConverter.DoubleToInt64Bits(y),
        _ => Equals(a, b),
    };

    /// <summary>
    /// Matches an accessor's expression against one found in a method: "this" stands for one object (found on the
    /// way), the setter's argument for any value.
    /// </summary>
    private sealed class Match
    {
        public HExpr? Self, Argument;

        public bool Unify(HExpr? pattern, HExpr? site)
        {
            if (pattern == null || site == null) return pattern == null && site == null;
            switch (pattern)
            {
                case HArg { Index: < 0 }:
                    if (Self != null) return HirCleanup.Same(Self, site);
                    if (!HirBuilder.IsPure(site)) return false;
                    Self = site;
                    return true;
                case HArg { Index: 0 }:
                    if (Argument != null) return HirCleanup.Same(Argument, site);
                    Argument = site;
                    return true;
                case HConst c: return site is HConst sc && SameConst(c.Value, sc.Value);
                // The one field of the struct the setter was given, where the place stores nothing: the
                // struct given was its default ("timer = TickTimer.None").
                case HField { Object: HArg { Index: 0, Type: { IsValueType: true, Definition: { } wrapper } whole } } only
                    when Argument == null && site is HConst { Value: int or long } zero && Convert.ToInt64(zero.Value) == 0 &&
                         wrapper.Fields.Count(x => !x.IsStatic) == 1 && ReferenceEquals(only.Field.DeclaringType, wrapper):
                    Argument = new HTypeExpr(HTypeOp.Default, whole, null) { Type = whole };
                    return true;
                case HField f: return site is HField sf && ReferenceEquals(f.Field, sf.Field) && Unify(f.Object, sf.Object);
                case HDeref d: return site is HDeref sd && Unify(d.Pointer, sd.Pointer);
                case HAddressOf a: return site is HAddressOf sa && Unify(a.Target, sa.Target);
                case HUnary u: return site is HUnary su && u.Op == su.Op && Unify(u.Operand, su.Operand);
                case HBinary b: return site is HBinary sb && b.Op == sb.Op && Unify(b.Left, sb.Left) && Unify(b.Right, sb.Right);
                case HCompare c: return site is HCompare sc2 && c.Op == sc2.Op && Unify(c.Left, sc2.Left) && Unify(c.Right, sc2.Right);
                case HConv c:
                    if (site is HConv sc3 && c.Kind == sc3.Kind) return Unify(c.Operand, sc3.Operand);
                    // "store = (byte)value": whatever is stored is what the setter was given.
                    return c.Operand is HArg { Index: 0 } && Unify(c.Operand, site);
                case HSelect s: return site is HSelect ss && Unify(s.Condition, ss.Condition) && Unify(s.WhenTrue, ss.WhenTrue) && Unify(s.WhenFalse, ss.WhenFalse);
                case HTypeExpr t:
                    return site is HTypeExpr st && t.Op == st.Op && t.Op != HTypeOp.Allocate && ReferenceEquals(t.Target, st.Target) && Unify(t.Operand, st.Operand);
                case HCall call:
                    return site is HCall sc4 && ReferenceEquals(call.Method, sc4.Method) && call.Virtual == sc4.Virtual && call.Arguments.Length == sc4.Arguments.Length &&
                           Unify(call.This, sc4.This) && All(call.Arguments, sc4.Arguments);
                case HNewObject n:
                    return site is HNewObject sn && ReferenceEquals(n.Constructor, sn.Constructor) && n.Arguments.Length == sn.Arguments.Length && All(n.Arguments, sn.Arguments);
                default: return false;
            }
        }

        private bool All(HExpr[] pattern, HExpr[] site)
        {
            for (int i = 0; i < pattern.Length; i++)
                if (!Unify(pattern[i], site[i]))
                    return false;
            return true;
        }
    }

    /// <summary>
    /// A whole number tested against zero, in any of the ways that can be written: what is tested, and whether
    /// the test holds when it is not zero.
    /// </summary>
    private static bool ZeroTest(HExpr? e, out HExpr? tested, out bool nonzero)
    {
        tested = null;
        nonzero = false;
        if (e is not HCompare c) return false;
        bool zeroRight = IsZero(c.Right), zeroLeft = IsZero(c.Left);
        if (zeroRight == zeroLeft) return false;
        tested = zeroRight ? c.Left : c.Right;
        if (tested.Type is PrimitiveSig { Element: Rewind.Runtime.Il2CppTypeEnum.R4 or Rewind.Runtime.Il2CppTypeEnum.R8 }) return false;
        switch (c.Op)
        {
            case HCompareOp.Ne: nonzero = true; return true;
            case HCompareOp.Eq: nonzero = false; return true;
            // Without a sign, "more than nothing" is "not nothing".
            case HCompareOp.GtUn when zeroRight: nonzero = true; return true;
            case HCompareOp.LtUn when zeroLeft: nonzero = true; return true;
            case HCompareOp.LeUn when zeroRight: nonzero = false; return true;
            case HCompareOp.GeUn when zeroLeft: nonzero = false; return true;
            default: return false;
        }
    }

    /// <summary>
    /// The compiler reads the address of the replicated memory once and keeps it while nothing can change it;
    /// the accessors it pasted each read it for themselves. A variable that holds nothing but that address,
    /// of one object, is put back as the read it stands for - which is what the accessors are recognized by.
    /// </summary>
    private static void Unhold(HMethod method)
    {
        var written = new Dictionary<HVar, int>();
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
                if (s is HAssign { Target: HLocal l })
                    written[l.Variable] = written.GetValueOrDefault(l.Variable) + 1;
        foreach (HTryRegion region in method.TryRegions.Values) written[region.Exception] = written.GetValueOrDefault(region.Exception) + 2;
        bool Fixed(HExpr owner) => owner is HArg { Index: < 0 } ||
                                   (owner is HLocal { Variable: var v } && !v.AddressTaken && written.GetValueOrDefault(v) == 1);
        var held = new Dictionary<HVar, HField>();
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
                if (s is HAssign { Target: HLocal l, Value: HField { Object: { } owner } f } && IsStorageField(f.Field) && !l.Variable.AddressTaken &&
                    written.GetValueOrDefault(l.Variable) == 1 && Fixed(owner))
                    held[l.Variable] = f;
        if (held.Count == 0) return;
        foreach (HBlock block in method.Blocks)
            block.Statements.RemoveAll(s => s is HAssign { Target: HLocal l } && held.ContainsKey(l.Variable));
        HExpr? Memory(HExpr e)
        {
            if (e is not HLocal l || !held.TryGetValue(l.Variable, out HField? f)) return null;
            HExpr owner = f.Object is HLocal o ? new HLocal(o.Variable) { Type = o.Type } : new HArg(((HArg)f.Object!).Index) { Type = f.Object!.Type };
            return new HField { Object = owner, Field = f.Field, DeclaringType = f.DeclaringType, Type = f.Type };
        }
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
                EnumeratorLoops.Rewrite(s, Memory);
        method.Locals.RemoveAll(held.ContainsKey);
    }

    /// <summary>The memory a field (of a field ...) of a struct read through a pointer is part of; null for any other place.</summary>
    private static HDeref? PartOfMemory(HExpr place)
    {
        HExpr? e = place;
        for (int depth = 0; depth < 8 && e is HField { Object: { } of } f && !f.Field.IsStatic; depth++)
        {
            if (of.Type is not { IsValueType: true }) return null;
            if (of is HDeref memory) return memory;
            e = of;
        }
        return null;
    }

    private static bool Derives(TypeDef? type, TypeDef ancestor)
    {
        int guard = 0;
        for (TypeDef? t = type; t != null && guard++ < 64; t = t.BaseType?.Definition)
            if (ReferenceEquals(t, ancestor))
                return true;
        return false;
    }

    /// <summary>Whether an expression reads the replicated memory of some object directly.</summary>
    private static bool TouchesStorage(HExpr? e)
    {
        bool found = false;
        Walk(e, x => { if (x is HField f && IsStorageField(f.Field)) found = true; });
        return found;
    }

    private static void Walk(HExpr? e, Action<HExpr> visit)
    {
        if (e == null) return;
        visit(e);
        switch (e)
        {
            case HField f: Walk(f.Object, visit); break;
            case HElement el: Walk(el.Array, visit); Walk(el.Index, visit); break;
            case HArrayLength len: Walk(len.Array, visit); break;
            case HAddressOf a: Walk(a.Target, visit); break;
            case HDeref d: Walk(d.Pointer, visit); break;
            case HUnary u: Walk(u.Operand, visit); break;
            case HBinary b: Walk(b.Left, visit); Walk(b.Right, visit); break;
            case HCompare c: Walk(c.Left, visit); Walk(c.Right, visit); break;
            case HConv c: Walk(c.Operand, visit); break;
            case HCall call: Walk(call.This, visit); foreach (HExpr a in call.Arguments) Walk(a, visit); break;
            case HNewObject n: foreach (HExpr a in n.Arguments) Walk(a, visit); break;
            case HNewArray na: Walk(na.Length, visit); break;
            case HTypeExpr t: Walk(t.Operand, visit); break;
            case HSelect s: Walk(s.Condition, visit); Walk(s.WhenTrue, visit); Walk(s.WhenFalse, visit); break;
            case HOpaque o: foreach (HExpr a in o.Operands) Walk(a, visit); break;
        }
    }

    public bool Run(HMethod method)
    {
        if (Disabled) return false;

        // The classes whose replicated memory this method touches.
        var classes = new HashSet<TypeDef>();
        TypeDef? ClassOf(HExpr e) => e.Type?.Definition ?? (e is HArg { Index: < 0 } ? method.Method.DeclaringType : null);
        void Note(HExpr? e) => Walk(e, x =>
        {
            if (x is HField { Object: { } owner } f && IsStorageField(f.Field) && ClassOf(owner) is { } type) classes.Add(type);
        });
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
                switch (s)
                {
                    case HAssign a: Note(a.Target); Note(a.Value); break;
                    case HEval e: Note(e.Expression); break;
                    case HReturn r: Note(r.Value); break;
                    case HThrow t: Note(t.Exception); break;
                    case HBranch b: Note(b.Condition); break;
                    case HSwitch sw: Note(sw.Value); break;
                }
        if (classes.Count == 0) return false;

        Unhold(method);

        var candidates = new List<Accessor>();
        foreach (TypeDef type in classes)
            foreach (Accessor a in Accessors(type))
                if (!candidates.Contains(a) && !ReferenceEquals(a.Getter, method.Method) && !ReferenceEquals(a.Setter, method.Method))
                    candidates.Add(a);
        // An accessor of a networked property is that code: its own check stays.
        string? own = method.Method.Name.StartsWith("get_", StringComparison.Ordinal) || method.Method.Name.StartsWith("set_", StringComparison.Ordinal)
            ? method.Method.Name[4..]
            : null;

        bool any = false;
        HExpr Read(HExpr e)
        {
            if (TouchesStorage(e))
            {
                foreach (Accessor a in candidates)
                {
                    if (a.Value == null) continue;
                    // The whole of what the getter returns, or the memory read inside a conversion of it.
                    HExpr pattern = a.Value.GetType() == e.GetType() ? a.Value : a.Value is HConv { Operand: HDeref inner } && e is HDeref ? inner : null!;
                    if (pattern == null) continue;
                    var match = new Match();
                    bool opposite = false;
                    if (!match.Unify(pattern, e))
                    {
                        // A yes or no kept as a number: "is it anything but zero", which the place may ask
                        // in another way - or the other way round.
                        if (!ZeroTest(pattern, out HExpr? kept, out bool yes) || !ZeroTest(e, out HExpr? read, out bool asked)) continue;
                        match = new Match();
                        if (!match.Unify(kept, read)) continue;
                        opposite = yes != asked;
                    }
                    if (match.Self == null || !Derives(ClassOf(match.Self), a.Property.DeclaringType)) continue;
                    any = true;
                    HExpr got = new HCall { Method = a.Getter!, This = Read(match.Self), Arguments = [], Virtual = a.Getter!.IsVirtual, Type = a.Getter.ReturnType };
                    return opposite ? new HUnary(HUnaryOp.LogicalNot, got) { Type = got.Type } : got;
                }
            }
            switch (e)
            {
                case HField f: if (f.Object != null) f.Object = Read(f.Object); break;
                case HElement el: el.Array = Read(el.Array); el.Index = Read(el.Index); break;
                case HArrayLength len: len.Array = Read(len.Array); break;
                case HAddressOf a: a.Target = Read(a.Target); break;
                case HDeref d: d.Pointer = Read(d.Pointer); break;
                case HUnary u: u.Operand = Read(u.Operand); break;
                case HBinary b: b.Left = Read(b.Left); b.Right = Read(b.Right); break;
                case HCompare c: c.Left = Read(c.Left); c.Right = Read(c.Right); break;
                case HConv c: c.Operand = Read(c.Operand); break;
                case HCall call:
                    if (call.This != null) call.This = Read(call.This);
                    for (int i = 0; i < call.Arguments.Length; i++)
                        if (call.Arguments[i] != null) call.Arguments[i] = Read(call.Arguments[i]);
                    break;
                case HNewObject n:
                    for (int i = 0; i < n.Arguments.Length; i++)
                        if (n.Arguments[i] != null) n.Arguments[i] = Read(n.Arguments[i]);
                    break;
                case HNewArray na: na.Length = Read(na.Length); break;
                case HTypeExpr t: if (t.Operand != null) t.Operand = Read(t.Operand); break;
                case HSelect s: s.Condition = Read(s.Condition); s.WhenTrue = Read(s.WhenTrue); s.WhenFalse = Read(s.WhenFalse); break;
                case HOpaque o:
                    for (int i = 0; i < o.Operands.Length; i++) o.Operands[i] = Read(o.Operands[i]);
                    break;
            }
            return e;
        }

        foreach (HBlock block in method.Blocks)
        {
            for (int i = 0; i < block.Statements.Count; i++)
            {
                switch (block.Statements[i])
                {
                    case HAssign a:
                    {
                        // A store into a part of what a property keeps ("grabbedInfo.rootRotation = r" cannot be
                        // written of a property, and the compiler has taken apart what was): the property read,
                        // changed and written back - a run of such stores as one, and without the reading when
                        // they fill every field.
                        if (a.Target is HField && PartOfMemory(a.Target) is { } root && TouchesStorage(root))
                        {
                            Accessor? kept = null;
                            Match? found = null;
                            foreach (Accessor candidate in candidates)
                            {
                                if (candidate.Getter == null || candidate.Setter == null || candidate.Value is not HDeref whole) continue;
                                var match = new Match();
                                if (!match.Unify(whole, root) || match.Self == null || !Derives(ClassOf(match.Self), candidate.Property.DeclaringType)) continue;
                                kept = candidate;
                                found = match;
                                break;
                            }
                            if (kept != null && found != null)
                            {
                                TypeSig type = kept.Getter!.ReturnType;
                                int end = i;
                                while (end + 1 < block.Statements.Count && block.Statements[end + 1] is HAssign { Target: HField next } &&
                                       PartOfMemory(next) is { } again && HirCleanup.Same(again, root)) end++;
                                var filled = new HashSet<FieldDef>();
                                for (int k = i; k <= end; k++)
                                    if (((HAssign)block.Statements[k]).Target is HField { Object: { } of } direct && HirCleanup.Same(of, root))
                                        filled.Add(direct.Field);
                                bool complete = type.Definition is { } definition && definition.Fields.Where(f => !f.IsStatic).All(filled.Contains);
                                HVar copy = method.NewLocal(type, "v");
                                HExpr Copy() => new HLocal(copy) { Type = type };
                                HExpr Self() => found.Self switch
                                {
                                    HArg self => new HArg(self.Index) { Type = self.Type },
                                    HLocal self => new HLocal(self.Variable) { Type = self.Type },
                                    var self => self!,
                                };
                                HExpr? InCopy(HExpr e) => e is HDeref && HirCleanup.Same(e, root) ? Copy() : null;
                                var rebuilt = new List<HStmt>
                                {
                                    new HAssign(Copy(), complete
                                        ? new HTypeExpr(HTypeOp.Default, type, null) { Type = type }
                                        : new HCall { Method = kept.Getter, This = Read(Self()), Arguments = [], Virtual = kept.Getter.IsVirtual, Type = type })
                                    { Address = a.Address },
                                };
                                for (int k = i; k <= end; k++)
                                {
                                    var store = (HAssign)block.Statements[k];
                                    EnumeratorLoops.Rewrite(store, InCopy);
                                    store.Value = Read(store.Value);
                                    rebuilt.Add(store);
                                }
                                rebuilt.Add(new HEval(new HCall
                                {
                                    Method = kept.Setter!, This = Read(Self()), Arguments = [Copy()], Virtual = kept.Setter!.IsVirtual, Type = kept.Setter.ReturnType,
                                })
                                { Address = block.Statements[end].Address });
                                block.Statements.RemoveRange(i, end - i + 1);
                                block.Statements.InsertRange(i, rebuilt);
                                i += rebuilt.Count - 1;
                                any = true;
                                break;
                            }
                        }
                        // A store into the memory of a property is its setter; the value may itself read others.
                        if (a.Target is HDeref && TouchesStorage(a.Target))
                        {
                            HStmt? call = null;
                            foreach (Accessor candidate in candidates)
                            {
                                if (candidate.Store == null) continue;
                                var match = new Match();
                                if (!match.Unify(candidate.Store.Target, a.Target) || !match.Unify(candidate.Store.Value, a.Value) || match.Self == null || match.Argument == null ||
                                    !Derives(ClassOf(match.Self), candidate.Property.DeclaringType)) continue;
                                call = new HEval(new HCall
                                {
                                    Method = candidate.Setter!, This = Read(match.Self), Arguments = [Read(match.Argument)], Virtual = candidate.Setter!.IsVirtual,
                                    Type = candidate.Setter.ReturnType,
                                })
                                { Address = a.Address };
                                break;
                            }
                            if (call != null)
                            {
                                block.Statements[i] = call;
                                any = true;
                                break;
                            }
                        }
                        a.Value = Read(a.Value);
                        if (a.Target is not HLocal) a.Target = Read(a.Target) is { } target && target is not HCall ? target : a.Target;
                        break;
                    }
                    case HEval e: e.Expression = Read(e.Expression); break;
                    case HReturn r: if (r.Value != null) r.Value = Read(r.Value); break;
                    case HThrow t: if (t.Exception != null) t.Exception = Read(t.Exception); break;
                    case HBranch b:
                        // The check itself is looked at below; do not turn it into anything else.
                        if (Guarded(block) == null) b.Condition = Read(b.Condition);
                        break;
                    case HSwitch sw: sw.Value = Read(sw.Value); break;
                }
            }
        }

        // The checks of the pasted accessors: the properties make them now.
        foreach (HBlock block in method.Blocks)
        {
            if (Guarded(block) is not { } access || (own != null && GuardedProperty(block) == own)) continue;
            HStmt branch = block.Statements[^1];
            block.Statements[^1] = new HJump(access) { Address = branch.Address };
            any = true;
        }
        if (!any) return false;
        HirCleanup.Run(method);

        bool left = false;
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
                left |= s switch
                {
                    HAssign a => TouchesStorage(a.Target) || TouchesStorage(a.Value),
                    HEval e => TouchesStorage(e.Expression),
                    HReturn r => TouchesStorage(r.Value),
                    HBranch b => TouchesStorage(b.Condition),
                    HSwitch sw => TouchesStorage(sw.Value),
                    _ => false,
                };
        if (left) method.Notes.Add("replicated memory of a networked object is accessed directly (an inlined accessor that was not recognized)");
        return true;
    }
}
