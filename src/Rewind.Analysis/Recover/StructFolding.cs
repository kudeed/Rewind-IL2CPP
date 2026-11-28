using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Puts whole-struct operations back.
///
/// A struct is copied, cleared or built by moving its bytes, and what the machine code shows is each field read
/// and written on its own: "a.x = b.x; a.y = b.y; a.z = b.z" where the source said "a = b", three stores where it
/// said "a = new Vector3(x, y, z)", a lone "n.hasValue = false" where it said "n = null". That is exact, but it is
/// not what was written, and often not something that could be written: the fields may be private or read-only,
/// and a field initializer taken apart like this no longer is one.
///
/// Here a run of statements that stores every field of one struct is replaced by a single assignment when the
/// stored values are the fields of another struct of the same type (a copy), all zero (default), or one of the
/// type's constructors applied to some values (compared with the constructor's own recovered body, as
/// ConstructorFolding does for classes). Anything else stays as it is: it does the same thing either way.
/// </summary>
internal static class StructFolding
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_FOLD") != null;

    public static void Run(HMethod method, ProgramAnalysis program, MethodPipeline pipeline)
    {
        if (Disabled) return;
        bool any = StructSnapshots.Run(method, program.Layouts);
        foreach (HBlock block in method.Blocks)
        {
            // Inner structs first: folding "a.p.x = ..; a.p.y = .." into "a.p = .." is what lets "a" fold next.
            for (int round = 0; round < 6 && FoldBlock(method, block, program, pipeline); round++) any = true;
            if (DropRepeatedClears(block)) any = true;
        }
        // (After the folding: a store that repeats one before may still be part of a whole made anew.)
        if (!NoRepeatedStores && DropRepeatedStores(method, program)) any = true;
        if (!NoUnionCopies && UnionCopies(method, program, pipeline)) any = true;
        if (!NoUnionCopies && !NoHeldCopies && HeldUnionCopies(method, program, pipeline)) any = true;
        if (ForwardWholeValues(method, pipeline)) any = true;
        if (any) HirCleanup.Run(method);
    }

    // ---- how variables are used --------------------------------------------------------------------------------

    private sealed class Usage
    {
        private readonly Dictionary<HVar, int> _defs = [], _reads = [];

        /// <summary>
        /// A variable written once and mentioned once: a value on its way from one place to another. (Whoever
        /// asks has that one mention in hand as a plain read, so nothing takes the variable's address.)
        /// </summary>
        public bool IsTemp(HVar v) => _defs.GetValueOrDefault(v) == 1 && _reads.GetValueOrDefault(v) == 1;

        public static Usage Of(HMethod method)
        {
            var u = new Usage();
            void Read(HExpr? e) => Walk(e, x => { if (x is HLocal l) u._reads[l.Variable] = u._reads.GetValueOrDefault(l.Variable) + 1; });
            foreach (HTryRegion r in method.TryRegions.Values) u._defs[r.Exception] = u._defs.GetValueOrDefault(r.Exception) + 2;
            foreach (HBlock block in method.Blocks)
                foreach (HStmt s in block.Statements)
                    switch (s)
                    {
                        case HAssign a:
                            if (a.Target is HLocal written) u._defs[written.Variable] = u._defs.GetValueOrDefault(written.Variable) + 1;
                            else Read(a.Target);
                            Read(a.Value);
                            break;
                        case HEval e: Read(e.Expression); break;
                        case HReturn r: Read(r.Value); break;
                        case HThrow t: Read(t.Exception); break;
                        case HBranch b: Read(b.Condition); break;
                        case HSwitch sw: Read(sw.Value); break;
                    }
            return u;
        }
    }

    /// <summary>Visits an expression and everything inside it.</summary>
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
            case HMethodPointer p: Walk(p.VirtualOn, visit); break;
        }
    }

    private static bool Mentions(HExpr? e, HVar variable)
    {
        bool found = false;
        Walk(e, x => { if (x is HLocal l && ReferenceEquals(l.Variable, variable)) found = true; });
        return found;
    }

    private static bool MentionsStatement(HStmt s, HVar variable)
    {
        bool found = false;
        FinallyFolding.Visit(s, x => found |= x is HLocal l && ReferenceEquals(l.Variable, variable));
        return found;
    }

    /// <summary>REWIND_NO_STRUCT_PARTS_ACROSS: a struct filled field by field is put together only where nothing else is done in between.</summary>
    private static readonly bool NoPartsAcross = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_PARTS_ACROSS") != null;
    private static readonly bool NoFreshObjects = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_PAST_NEW") != null;

    // ---- which memory two places can share -------------------------------------------------------------------------

    private static bool IsStruct(TypeSig? t) =>
        t is { IsValueType: true } and not (PrimitiveSig or PointerSig or ByRefSig or OpaqueSig or GenericParamSig) && t.Definition is { IsEnum: false };

    private static bool SameType(TypeSig? a, TypeSig? b) => a != null && b != null && (ReferenceEquals(a, b) || (a.Key.Length != 0 && a.Key == b.Key));

    /// <summary>True when a struct of type <paramref name="outer"/> has a part of type <paramref name="inner"/> (itself included).</summary>
    private static bool Holds(TypeSig? outer, TypeSig? inner, int depth = 0)
    {
        if (outer == null || inner == null) return true; // unknown: assume it can
        if (SameType(outer, inner)) return true;
        if (!IsStruct(outer)) return false;
        if (depth > 6) return true;
        foreach (FieldDef f in outer.Definition!.Fields)
        {
            if (f.IsStatic) continue;
            if (f.Type is GenericParamSig || Holds(f.Type, inner, depth + 1)) return true;
        }
        return false;
    }

    private enum RootKind { Variable, Object, Unknown }

    /// <summary>
    /// A place taken apart: where it starts and the fields that lead from there to it. A variable is its own
    /// memory; a field of an object (or a static field) is found from the field alone; anything else (an array
    /// element, something behind a pointer, the "this" of a struct method) could be anywhere its type allows.
    /// </summary>
    private readonly record struct PlacePath(RootKind Kind, HExpr Root, List<HField> Fields);

    private static PlacePath PathOf(HExpr place)
    {
        var fields = new List<HField>();
        HExpr e = place;
        while (e is HField { Object: { } owner } f && IsStruct(owner.Type) && owner is HField or HLocal or HArg or HElement or HDeref)
        {
            fields.Add(f);
            e = owner;
        }
        RootKind kind;
        if (e is HField top)
        {
            // A field of an object, or a static field: the first step of the path.
            fields.Add(top);
            kind = RootKind.Object;
        }
        else if (e is HLocal { Variable.AddressTaken: false }) kind = RootKind.Variable;
        else if (e is HArg { Index: >= 0 } a && a.Type is not (ByRefSig or PointerSig)) kind = RootKind.Variable; // a parameter passed by value
        else kind = RootKind.Unknown;
        fields.Reverse();
        return new PlacePath(kind, e, fields);
    }

    private static TypeSig? TypeOfField(HField f) => f.Type ?? f.Field.Type;

    /// <summary>False when the fields named along two paths, taken from the same start, part ways.</summary>
    private static bool SamePath(List<HField> a, int fromA, List<HField> b, int fromB)
    {
        for (int i = 0; fromA + i < a.Count && fromB + i < b.Count; i++)
            if (!ReferenceEquals(a[fromA + i].Field, b[fromB + i].Field))
                return false;
        return true;
    }

    /// <summary>Whether the paths can meet when the first one starts at a pointer that could point anywhere its type allows.</summary>
    private static bool CanStartInside(PlacePath pointer, PlacePath other)
    {
        TypeSig? pointee = pointer.Root.Type is ByRefSig or PointerSig ? pointer.Root.Type.ElementType : pointer.Root.Type;
        if (pointee == null) return true;
        // The pointer may be the other path's start, or any struct along it.
        for (int p = 0; p <= other.Fields.Count; p++)
        {
            TypeSig? here = p == 0 ? (other.Kind == RootKind.Object ? null : other.Root.Type) : TypeOfField(other.Fields[p - 1]);
            if (p == 0 && other.Kind == RootKind.Object) continue; // before its first field there is an object, not a struct
            if (here is ByRefSig or PointerSig) here = here.ElementType;
            if (here == null) return true;
            if (SameType(here, pointee) && SamePath(pointer.Fields, 0, other.Fields, p)) return true;
        }
        // Or it points into the place the other path ends at (a part of a struct that is read or written whole).
        TypeSig? last = other.Fields.Count != 0 ? TypeOfField(other.Fields[^1]) : other.Root.Type;
        if (last is ByRefSig or PointerSig) last = last.ElementType;
        return !SameType(last, pointee) && IsStruct(last) && Holds(last, pointee);
    }

    /// <summary>True unless two places are certain to be different memory.</summary>
    private static bool MayOverlap(HExpr a, HExpr b)
    {
        PlacePath x = PathOf(a), y = PathOf(b);
        // Variables of the method are separate memory, whatever points to them, and none of them is inside an
        // object: two places in variables meet only in the same variable, and a place in a variable never
        // meets a field of an object.
        static bool InLocal(PlacePath p) => p.Root is HLocal { Type: not (ByRefSig or PointerSig) };
        if (InLocal(x) && InLocal(y)) return HirCleanup.Same(x.Root, y.Root) && SamePath(x.Fields, 0, y.Fields, 0);
        if ((InLocal(x) && y.Kind == RootKind.Object) || (InLocal(y) && x.Kind == RootKind.Object)) return false;
        if (x.Kind == RootKind.Variable || y.Kind == RootKind.Variable)
        {
            // A variable nothing points to shares memory only with itself.
            if (x.Kind != y.Kind || !HirCleanup.Same(x.Root, y.Root)) return false;
            return SamePath(x.Fields, 0, y.Fields, 0);
        }
        if (x.Kind == RootKind.Object && y.Kind == RootKind.Object) return SamePath(x.Fields, 0, y.Fields, 0);
        if (x.Kind == RootKind.Unknown && CanStartInside(x, y)) return true;
        if (y.Kind == RootKind.Unknown && CanStartInside(y, x)) return true;
        return false;
    }

    /// <summary>The places an expression reads.</summary>
    private static List<HExpr> ReadsOf(HExpr? e)
    {
        var reads = new List<HExpr>();
        // What a field is reached through: a struct held in place is part of the same read (the field's path
        // covers it); an object reference, an array or a pointer is a read of its own.
        void VisitBase(HExpr? o)
        {
            while (o is HField through && IsStruct(through.Type))
            {
                if (through.Object == null) return;
                o = through.Object;
            }
            switch (o)
            {
                case null: return;
                case HLocal or HArg when IsStruct(o.Type): return;
                case HElement el when IsStruct(el.Type): Visit(el.Array); Visit(el.Index); return;
                case HDeref d when IsStruct(d.Type): Visit(d.Pointer); return;
                default: Visit(o); return;
            }
        }
        void Visit(HExpr? x)
        {
            switch (x)
            {
                case null: return;
                case HField f:
                    reads.Add(f);
                    VisitBase(f.Object);
                    return;
                case HLocal or HArg: if (IsStruct(x.Type)) reads.Add(x); return;
                case HElement el: reads.Add(el); Visit(el.Array); Visit(el.Index); return;
                case HDeref d: reads.Add(d); Visit(d.Pointer); return;
                case HArrayLength len: Visit(len.Array); return;
                case HAddressOf a: Visit(a.Target); return;
                case HUnary u: Visit(u.Operand); return;
                case HBinary b: Visit(b.Left); Visit(b.Right); return;
                case HCompare c: Visit(c.Left); Visit(c.Right); return;
                case HConv c: Visit(c.Operand); return;
                case HTypeExpr t: Visit(t.Operand); return;
                case HSelect s: Visit(s.Condition); Visit(s.WhenTrue); Visit(s.WhenFalse); return;
                case HCall call: Visit(call.This); foreach (HExpr arg in call.Arguments) Visit(arg); return;
                case HNewObject n: foreach (HExpr arg in n.Arguments) Visit(arg); return;
                case HNewArray na: Visit(na.Length); return;
                case HOpaque o: foreach (HExpr arg in o.Operands) Visit(arg); return;
            }
        }
        Visit(e);
        return reads;
    }

    /// <summary>
    /// Whether a value computed at <paramref name="from"/> is the same when computed at <paramref name="to"/>
    /// instead: nothing in between may change what it reads. (<paramref name="except"/>: a statement that goes away.)
    /// </summary>
    internal static bool Movable(HExpr value, List<HStmt> statements, int from, int to, HStmt? except)
    {
        if (!HirBuilder.IsPure(value)) return false;
        List<HExpr>? reads = null;
        bool? proof = null;
        for (int k = from + 1; k <= to && k < statements.Count; k++)
        {
            HStmt s = statements[k];
            if (ReferenceEquals(s, except)) continue;
            // A new object, and object's own constructor run on it, change nothing that was there before.
            if (!NoFreshObjects)
            {
                if (s is HAssign { Target: HLocal fresh, Value: HTypeExpr { Op: HTypeOp.Allocate } })
                {
                    if (Mentions(value, fresh.Variable)) return false;
                    continue;
                }
                if (s is HEval { Expression: HCall { Method: { Name: ".ctor", IsStatic: false, Parameters.Length: 0 } created, This: HLocal } } &&
                    created.DeclaringType.BaseType == null && !created.DeclaringType.IsValueType)
                    continue;
            }
            // A call made for what it does: only what no call can change is still what it was.
            if (s is HEval && !NoPartsAcross)
            {
                if (!(proof ??= CallProof(value))) return false;
                continue;
            }
            if (s is not HAssign a) return false;
            // Something that does work, put somewhere: only what no call can change is still what it was.
            if (!HirBuilder.IsPure(a.Value) && !(proof ??= CallProof(value))) return false;
            if (a.Target is HLocal l)
            {
                if (Mentions(value, l.Variable)) return false;
                continue;
            }
            if (a.Target is not (HField or HElement or HDeref or HArg)) return false;
            reads ??= ReadsOf(value);
            foreach (HExpr read in reads)
                if (MayOverlap(read, a.Target))
                    return false;
        }
        return true;
    }

    // ---- folding -----------------------------------------------------------------------------------------------

    /// <summary>A value no call can change: made of constants and of variables nothing points to.</summary>
    private static bool CallProof(HExpr? e) => e switch
    {
        HConst => true,
        HLocal l => !l.Variable.AddressTaken,
        HArg a => a.Index >= 0 && a.Type is not (ByRefSig or PointerSig),
        HField { Object: { } o } f => !f.Field.IsStatic && o.Type is { IsValueType: true } and not (ByRefSig or PointerSig) && CallProof(o),
        HUnary u => CallProof(u.Operand),
        HBinary b => HirBuilder.IsPure(b) && CallProof(b.Left) && CallProof(b.Right),
        HCompare c => CallProof(c.Left) && CallProof(c.Right),
        HConv c => HirBuilder.IsPure(c) && CallProof(c.Operand),
        HTypeExpr { Op: HTypeOp.Default } => true,
        _ => false,
    };

    private static bool IsZero(HExpr? e) => e switch
    {
        HConst { Value: null } => true,
        HConst { Value: int i } => i == 0,
        HConst { Value: long l } => l == 0,
        HConst { Value: bool b } => !b,
        HConst { Value: float f } => BitConverter.SingleToInt32Bits(f) == 0,
        HConst { Value: double d } => BitConverter.DoubleToInt64Bits(d) == 0,
        HTypeExpr { Op: HTypeOp.Default } => true,
        _ => false,
    };

    private static bool SameConst(object? a, object? b) => (a, b) switch
    {
        (float x, float y) => BitConverter.SingleToInt32Bits(x) == BitConverter.SingleToInt32Bits(y),
        (double x, double y) => BitConverter.DoubleToInt64Bits(x) == BitConverter.DoubleToInt64Bits(y),
        _ => Equals(a, b),
    };

    private sealed class Store
    {
        public required int Index;
        public required HAssign Statement;
        public required FieldDef Field;
        /// <summary>The stored value; when it came through a temporary, what the temporary was given.</summary>
        public required HExpr Value;
        /// <summary>Where the temporary was given its value (-1: the value is written in the store itself).</summary>
        public int TempAt = -1;
        /// <summary>The value is a variable that holds this field of a struct (see HeldPart): what it is a copy of.</summary>
        public HField? Held;
    }

    /// <summary>
    /// A struct that has just been set to its default has nothing left to clear: a store of zero into a part of
    /// it right after is the same clearing seen a second time ("n = null", and then the bytes of the value a
    /// Nullable holds - a field nobody outside can name).
    /// </summary>
    private static bool DropRepeatedClears(HBlock block)
    {
        List<HStmt> s = block.Statements;
        bool any = false;
        for (int i = 0; i < s.Count; i++)
        {
            if (s[i] is not HAssign { Target: var place, Value: HTypeExpr { Op: HTypeOp.Default } } || !IsStruct(place.Type) || !HirBuilder.IsPure(place)) continue;
            for (int k = i + 1; k < s.Count; k++)
            {
                if (s[k] is not HAssign a) break;
                if (a.Target is HField part && IsZero(a.Value) && PartOf(part, place))
                {
                    // Nothing between the two may have changed the struct or where it is.
                    if (!Movable(place, s, i, k - 1, null)) break;
                    s.RemoveAt(k--);
                    any = true;
                    continue;
                }
                if (!HirBuilder.IsPure(a.Value)) break;
            }
        }
        return any;
    }

    /// <summary>True when a field is (a part of a part of ...) the struct at a place.</summary>
    private static bool PartOf(HField part, HExpr place)
    {
        HExpr? e = part.Object;
        for (int depth = 0; e != null && depth < 8; depth++)
        {
            if (HirCleanup.Same(e, place)) return true;
            if (e is not HField { Object: var outer } through || !IsStruct(through.Type)) return false;
            e = outer;
        }
        return false;
    }

    /// <summary>True when two fields of a struct share memory, or where they are is not known.</summary>
    private static bool Overlaid(ProgramAnalysis program, TypeSig type)
    {
        TypeLayout layout = program.Layouts.Of(type);
        if (!layout.Known) return true;
        FieldSlot[] slots = layout.Fields;
        for (int i = 0; i < slots.Length; i++)
            for (int j = i + 1; j < slots.Length; j++)
                if (slots[i].Offset < slots[j].Offset + slots[j].Size && slots[j].Offset < slots[i].Offset + slots[i].Size)
                    return true;
        return false;
    }

    private static readonly bool NoUnionFold = Environment.GetEnvironmentVariable("REWIND_NO_UNION_FOLD") != null;

    /// <summary>Whether two fields of a struct have a byte in common (true as well when either's place is not known).</summary>
    private static bool SharesBytes(TypeLayout layout, FieldDef a, FieldDef b)
    {
        int i = Array.FindIndex(layout.Fields, x => ReferenceEquals(x.Field, a)), j = Array.FindIndex(layout.Fields, x => ReferenceEquals(x.Field, b));
        if (i < 0 || j < 0) return true;
        FieldSlot p = layout.Fields[i], q = layout.Fields[j];
        return p.Offset < q.Offset + q.Size && q.Offset < p.Offset + p.Size;
    }

    /// <summary>
    /// Whether the fields a run of stores fills make up the whole of a struct whose fields share memory: no two
    /// of them have a byte in common, and every field of the struct lies within them. Each byte that belongs to
    /// a field is then written once - "d.flags = ..; d.hi = ..; d.ulomidLE = .." fills a decimal as surely as
    /// stores into its four numbers would, and "c.rgba = .." a Color32.
    /// </summary>
    private static bool Tiles(TypeLayout layout, List<Store> stores)
    {
        if (!layout.Known || layout.Fields.Length == 0) return false;
        var filled = new List<(int From, int To)>();
        foreach (Store store in stores)
        {
            int at = Array.FindIndex(layout.Fields, x => ReferenceEquals(x.Field, store.Field));
            if (at < 0 || layout.Fields[at].Size <= 0) return false;
            (int from, int to) = (layout.Fields[at].Offset, layout.Fields[at].Offset + layout.Fields[at].Size);
            foreach ((int From, int To) other in filled)
                if (from < other.To && other.From < to)
                    return false;
            filled.Add((from, to));
        }
        filled.Sort();
        foreach (FieldSlot slot in layout.Fields)
        {
            // Filled from its first byte to its last, by stored fields that follow one another.
            int reached = slot.Offset;
            foreach ((int From, int To) part in filled)
                if (part.From <= reached && part.To > reached)
                    reached = part.To;
            if (reached < slot.Offset + slot.Size) return false;
        }
        return true;
    }

    private static int Width(TypeSig? type) => type is PrimitiveSig p
        ? p.Element switch
        {
            Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 => 1,
            Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 => 2,
            Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 => 4,
            Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 => 8,
            _ => 0,
        }
        : 0;

    /// <summary>
    /// A value without the conversions that change nothing of what the store keeps: those between whole
    /// numbers to something at least as wide as the field (the store drops the rest again).
    /// </summary>
    private static HExpr Unconverted(HExpr value, TypeSig field)
    {
        int width = Width(field);
        while (width != 0 && value is HConv c && Width(c.Operand.Type) >= width)
        {
            int to = c.Kind switch
            {
                HConvKind.I1 or HConvKind.U1 => 1,
                HConvKind.I2 or HConvKind.U2 => 2,
                HConvKind.I4 or HConvKind.U4 => 4,
                HConvKind.I8 or HConvKind.U8 => 8,
                _ => 0,
            };
            if (to < width) break;
            value = c.Operand;
        }
        return value;
    }

    private static readonly bool NoHeldParts = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_HELD_PARTS") != null;
    private static readonly bool NoRepeatedStores = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_REPEATED_STORES") != null;

    /// <summary>
    /// A store into a field of a struct variable that puts in what the field holds already: the same value,
    /// stored there before - on the one way here - with neither the struct nor what the value is made of set
    /// since. Code pasted in on two ways copies the struct field by field on each ("v.name = t" before a
    /// test, and again on one way after it); the second store does nothing.
    /// </summary>
    private static bool DropRepeatedStores(HMethod method, ProgramAnalysis program)
    {
        bool any = false;
        Dictionary<HBlock, List<HBlock>>? predecessors = null;
        foreach (HBlock block in method.Blocks)
        {
            List<HStmt> s = block.Statements;
            for (int i = s.Count - 1; i >= 0; i--)
            {
                if (s[i] is not HAssign { Target: HField { Object: HLocal { Variable: var v, Type: var vt } } target, Value: var value } || target.Field.IsStatic ||
                    !IsStruct(vt) || !CallProof(value) || (v.AddressTaken && AddressNamed(method, v)))
                    continue;
                bool union = Overlaid(program, vt!);
                // Walk back to the last statement that sets the variable or anything the value is made of.
                HStmt? last = null;
                HBlock current = block;
                int k = i - 1;
                var visited = new HashSet<HBlock> { block };
                bool done = false;
                for (int hops = 0; hops < 16 && !done; hops++)
                {
                    for (; k >= 0 && !done; k--)
                    {
                        if (current.Statements[k] is not HAssign { Target: var set } other) continue;
                        HExpr root = set;
                        HField? outer = null;
                        while (root is HField { Object: { } inside } f && !f.Field.IsStatic && IsStruct(inside.Type))
                        {
                            outer = f;
                            root = inside;
                        }
                        if (root is not HLocal { Variable: var written }) continue;
                        // (Another field of the struct leaves this one as it is - unless fields share memory.)
                        if (ReferenceEquals(written, v) && !Mentions(value, written) && outer != null && !ReferenceEquals(outer.Field, target.Field) && !union) continue;
                        if (ReferenceEquals(written, v) || Mentions(value, written))
                        {
                            last = other;
                            done = true;
                        }
                    }
                    if (done) break;
                    if (current == method.Blocks[0]) break;
                    predecessors ??= Predecessors(method);
                    if (!predecessors.TryGetValue(current, out List<HBlock>? into) || into.Count != 1 || into[0].Scope != current.Scope || !visited.Add(into[0])) break;
                    current = into[0];
                    k = current.Statements.Count - 2;
                }
                if (last is not HAssign { Target: HField { Object: HLocal { Variable: var again } } before } earlier || !ReferenceEquals(again, v) ||
                    !ReferenceEquals(before.Field, target.Field) || !HirCleanup.Same(earlier.Value, value))
                    continue;
                s.RemoveAt(i);
                any = true;
            }
        }
        return any;
    }

    private static Dictionary<HBlock, List<HBlock>> Predecessors(HMethod method)
    {
        var predecessors = new Dictionary<HBlock, List<HBlock>>();
        foreach (HBlock b in method.Blocks)
        {
            if (b.Statements.Count == 0) continue;
            IEnumerable<HBlock> next = b.Statements[^1] switch
            {
                HJump j => [j.Target],
                HBranch br => [br.WhenTrue, br.WhenFalse],
                HSwitch sw => [.. sw.Targets, sw.Default],
                _ => [],
            };
            foreach (HBlock to in next.Distinct())
            {
                if (!predecessors.TryGetValue(to, out List<HBlock>? list)) predecessors[to] = list = [];
                list.Add(b);
            }
        }
        return predecessors;
    }

    /// <summary>
    /// The field of a struct variable that a variable holds at a statement: its last value, found by going
    /// back through the block and the blocks that are the only way into it, is "t = x.f" - with x not set
    /// again since. Null when that is not so.
    /// </summary>
    private static HField? HeldPart(HMethod method, HBlock block, int at, HVar kept, Dictionary<HBlock, List<HBlock>> predecessors)
    {
        var passed = new List<HStmt>();
        HBlock current = block;
        int i = at - 1;
        var visited = new HashSet<HBlock> { block };
        for (int hops = 0; hops < 16; hops++)
        {
            for (; i >= 0; i--)
            {
                HStmt s = current.Statements[i];
                if (s is HAssign { Target: HLocal { Variable: var set }, Value: var value } && ReferenceEquals(set, kept))
                {
                    if (value is not HField { Object: HLocal { Variable: var whole, Type: var wholeType } } part || part.Field.IsStatic || !IsStruct(wholeType) ||
                        (whole.AddressTaken && AddressNamed(method, whole)) || ReferenceEquals(whole, kept))
                        return null;
                    // The struct must not have been changed on the way: no store into it, whole or in part.
                    foreach (HStmt later in passed)
                        if (later is HAssign { Target: var target } && Root(target) is HLocal { Variable: var changed } && ReferenceEquals(changed, whole))
                            return null;
                    return new HField { Object = new HLocal(whole) { Type = wholeType }, Field = part.Field, DeclaringType = part.DeclaringType, Type = part.Type };
                }
                if (s is HAssign { Target: var other } && Root(other) is HLocal { Variable: var partly } && ReferenceEquals(partly, kept)) return null;
                passed.Add(s);
            }
            // The one way into the block (in the same region): where the value came from is there.
            if (current == method.Blocks[0] || !predecessors.TryGetValue(current, out List<HBlock>? into) || into.Count != 1) return null;
            HBlock before = into[0];
            if (before.Scope != current.Scope || !visited.Add(before)) return null;
            current = before;
            i = current.Statements.Count - 2; // (the last statement is the jump or test that leads here)
        }
        return null;

        static HExpr Root(HExpr e)
        {
            while (e is HField { Object: { } inside } f && !f.Field.IsStatic && IsStruct(inside.Type)) e = inside;
            return e;
        }
    }

    /// <summary>
    /// Whether the method's statements take the address of a variable (or of a part of it) anywhere, or do
    /// something with memory that is not written out (then it may be anywhere). A variable whose address the
    /// machine code took (for a call that fills it, say) but whose statements never name its address any more
    /// is changed only where it is set.
    /// </summary>
    private static bool AddressNamed(HMethod method, HVar variable)
    {
        bool named = false;
        foreach (HBlock b in method.Blocks)
            foreach (HStmt s in b.Statements)
                FinallyFolding.Visit(s, e => named |= e is HOpaque || e is HAddressOf { Target: var t } && Mentions(t, variable));
        return named;
    }

    private static bool FoldBlock(HMethod method, HBlock block, ProgramAnalysis program, MethodPipeline pipeline)
    {
        List<HStmt> s = block.Statements;
        bool any = false;
        Usage usage = Usage.Of(method);
        Dictionary<HBlock, List<HBlock>>? predecessors = null;
        for (int i = 0; i < s.Count; i++)
        {
            if (s[i] is not HAssign { Target: HField { Object: { } place } first } || first.Field.IsStatic) continue;
            TypeDef owner = first.Field.DeclaringType;
            if (!owner.IsValueType || owner.IsEnum || !IsStruct(place.Type) || !ReferenceEquals(place.Type!.Definition, owner)) continue;
            // Fields laid over one another (a union) are not a list of separate values - unless the ones that
            // are stored lie beside one another and leave no field of the struct out (see Tiles). (An explicit
            // layout alone does not make a union: networked structs give each field its place and nothing more.)
            bool union = (owner.Flags & TypeDef.LayoutMask) == TypeDef.ExplicitLayout && Overlaid(program, place.Type!);
            if (union && NoUnionFold) continue;
            TypeLayout? shared = union ? program.Layouts.Of(place.Type!) : null;
            if (place is not (HLocal or HArg or HField or HElement or HDeref)) continue;
            HExpr root = place;
            while (root is HField { Object: { } inner } part && !part.Field.IsStatic && IsStruct(inner.Type)) root = inner;
            HVar? inLocal = !NoPartsAcross && root is HLocal { Variable: var variable, Type: not (ByRefSig or PointerSig) } ? variable : null;
            HVar? own = block.Scope < 0 ? inLocal : null;

            // The run: stores into fields of this one place, with nothing between them but values on their way.
            var stores = new List<Store>();
            var seen = new HashSet<FieldDef>();
            for (int j = i; j < s.Count && j - i < 96; j++)
            {
                if (s[j] is HAssign { Target: HField { Object: { } o } g } a && ReferenceEquals(g.Field.DeclaringType, owner) && HirCleanup.Same(o, place))
                {
                    if (!seen.Add(g.Field)) break;
                    // In a union, a store over bytes that were filled already starts something new.
                    if (shared != null && stores.Any(x => SharesBytes(shared, x.Field, g.Field))) break;
                    stores.Add(new Store { Index = j, Statement = a, Field = g.Field, Value = a.Value });
                    continue;
                }
                if (s[j] is HAssign { Target: HLocal t } load && usage.IsTemp(t.Variable) && HirBuilder.IsPure(load.Value)) continue;
                // Something else being filled at the same time (the compiler clears a struct in whatever
                // order suits it): it can stay where it is as long as it has nothing to do with this place.
                if (IsBystander(s[j], place, pipeline)) continue;
                // A struct in a variable of the method is memory nothing else reaches: what does not name the
                // variable - a call too - leaves it alone. The compiler fills such a struct field by field
                // between the other work ("v.x = 0; t = Random.Range(..); v.z = 0; v.y = t * k"), where the
                // source made it in one go ("new Vector3(0, t * k, 0)"), as the argument of a call it then
                // pasted in. Outside a try region, nothing can see it half filled when one of those calls
                // throws: the variable is gone then.
                if (own != null && s[j] is HAssign or HEval && !MentionsStatement(s[j], own)) continue;
                break;
            }
            if (shared != null && !Tiles(shared, stores)) continue;
            int end = stores[^1].Index;

            // Values that reached their store through a temporary of this block.
            foreach (Store store in stores)
            {
                if (store.Value is not HLocal temp || !usage.IsTemp(temp.Variable)) continue;
                for (int d = store.Index - 1; d >= 0; d--)
                {
                    if (s[d] is not HAssign { Target: HLocal t } def || !ReferenceEquals(t.Variable, temp.Variable)) continue;
                    if (Movable(def.Value, s, d, end, store.Statement))
                    {
                        store.Value = def.Value;
                        store.TempAt = d;
                    }
                    break;
                }
            }
            // ... and values kept in a variable that still holds a field of a struct: what a copy is made of when
            // the compiler read the field once for two copies ("t = item.name" before a test, then
            // "a.name = t" on one way and "b.name = t" on the other).
            if (!NoHeldParts)
                foreach (Store store in stores)
                    if (store.TempAt < 0 && Unconverted(store.Value, store.Field.Type) is HLocal { Variable: var kept } && !kept.AddressTaken)
                        store.Held = HeldPart(method, block, store.Index, kept, predecessors ??= Predecessors(method));

            HStmt? folded = Fold(method, place, owner, stores, s, end, program, pipeline, whole: shared != null, own: inLocal != null, guarded: block.Scope >= 0);
            if (folded == null) continue;

            folded.Address = stores[0].Statement.Address;
            var remove = new HashSet<int>();
            foreach (Store store in stores)
            {
                remove.Add(store.Index);
                if (store.TempAt >= 0) remove.Add(store.TempAt);
            }
            var rebuilt = new List<HStmt>(s.Count);
            for (int k = 0; k < s.Count; k++)
            {
                if (k == end) rebuilt.Add(folded);
                else if (!remove.Contains(k)) rebuilt.Add(s[k]);
            }
            s.Clear();
            s.AddRange(rebuilt);
            usage = Usage.Of(method);
            any = true;
            i = -1; // statements moved: look again from the start of the block
        }
        return any;
    }

    /// <summary>A store that neither reads nor writes any part of <paramref name="place"/>, nor decides where it is.</summary>
    private static bool IsBystander(HStmt statement, HExpr place, MethodPipeline? pipeline = null)
    {
        if (statement is not HAssign { Target: HField or HLocal or HArg } a || !HirBuilder.IsPure(a.Target)) return false;
        // What is stored: something that only computes - or a struct made of such things by a constructor that
        // only fills its fields (what a run of stores like the one looked at becomes).
        HExpr[] values = [a.Value];
        if (!HirBuilder.IsPure(a.Value))
        {
            if (pipeline == null || a.Value is not HNewObject made || !made.Arguments.All(HirBuilder.IsPure) || !OnlyStores(made.Constructor, made.Type, pipeline)) return false;
            values = made.Arguments;
        }
        if (a.Target is HLocal l && Mentions(place, l.Variable)) return false;
        if (MayOverlap(a.Target, place)) return false;
        foreach (HExpr read in ReadsOf(a.Target))
            if (MayOverlap(read, place))
                return false;
        foreach (HExpr value in values)
            foreach (HExpr read in ReadsOf(value))
                if (MayOverlap(read, place))
                    return false;
        return true;
    }

    /// <summary>
    /// A constructor of a struct that does nothing but put its parameters and constants into fields: making
    /// such a struct computes nothing and touches nothing.
    /// </summary>
    internal static bool OnlyStores(MethodDef constructor, TypeSig? made, MethodPipeline pipeline)
    {
        if (!constructor.DeclaringType.IsValueType) return false;
        TypeSig[] classArguments = made is GenericInstSig g ? g.Arguments : [];
        if (pipeline.ConstructorBody(constructor, classArguments) is not { } body) return false;
        List<HStmt> statements = body.Blocks[0].Statements;
        for (int k = 0; k < statements.Count - 1; k++)
            if (statements[k] is not HAssign { Target: HField { Object: HArg { Index: < 0 } }, Value: HArg { Index: >= 0 } or HConst })
                return false;
        return true;
    }

    /// <summary>A place inside a variable of the method: finding it computes nothing.</summary>
    private static bool InVariable(HExpr target)
    {
        HExpr e = target;
        while (e is HField { Object: { } o } && IsStruct(o.Type)) e = o;
        return e is HLocal or HArg { Index: >= 0 };
    }

    private static bool IsNullable(TypeDef type) => type.Name == "Nullable`1" && type.Namespace == "System" && type.DeclaringType == null;

    /// <summary>The single assignment a run of stores amounts to, or null when it is not one.</summary>
    private static HStmt? Fold(HMethod method, HExpr place, TypeDef owner, List<Store> stores, List<HStmt> statements, int end,
        ProgramAnalysis program, MethodPipeline pipeline, bool whole = false, bool own = false, bool guarded = false)
    {
        TypeSig type = place.Type!;
        var values = new Dictionary<FieldDef, Store>();
        foreach (Store store in stores) values[store.Field] = store;
        int instanceFields = owner.Fields.Count(f => !f.IsStatic);
        // (whole: a union, of which the stored fields are known to make up everything.)
        bool complete = whole || values.Count == instanceFields;

        // Every value is computed where the last store was; each must still be what it was where it stood.
        // (The last store's own value may do work - a call: it is computed where it always was. What the stores
        // before it put in must then be something no call can change, wherever it ends up being computed.)
        Store? closing = stores.FirstOrDefault(x => x.Index == end && x.TempAt < 0);
        bool works = closing != null && !HirBuilder.IsPure(closing.Value);
        // Stores one right after the other into a struct of a variable of the method (see FoldBlock), where
        // several values do work ("v.x = Random.Range(..) * k; v.y = Random.Range(..) * k"): made in one go,
        // they are worked out in the order of the constructor's parameters - the order they stand in here, which
        // is checked below. What the others put in must be something no call can change.
        // (In a try region, what is stored after the first store must be something that cannot fail: a handler
        // would see the struct half filled otherwise.)
        bool inOrder = own && !NoPartsAcross && stores.Count > 1 && stores.Any(x => x.TempAt < 0 && !HirBuilder.IsPure(x.Value));
        for (int k = 0; k < stores.Count && inOrder; k++)
            inOrder = stores[k].Index == stores[0].Index + k && (!HirBuilder.IsPure(stores[k].Value) ? stores[k].TempAt < 0 && (!guarded || k == 0) : CallProof(stores[k].Value));
        bool Settled(Store store) => store.TempAt >= 0 || store.Index == end || Movable(store.Value, statements, store.Index, end, null) ||
                                     (works && CallProof(store.Value) && Movable(store.Value, statements, store.Index, end - 1, null)) ||
                                     inOrder;
        bool Independent(HExpr value)
        {
            // What the new value is made of must not be the place that is being overwritten.
            foreach (HExpr read in ReadsOf(value))
                if (MayOverlap(read, place))
                    return false;
            return true;
        }

        // A copy: every field from the same field of one other struct.
        HStmt? Copy(bool viaHeld)
        {
            HExpr? source = null;
            foreach (Store store in stores)
            {
                // (A field kept in a variable is read from the struct where the copy is made.)
                bool held = viaHeld && store.Held != null && (store.Index == end || Movable(store.Held, statements, store.Index, end, null));
                if ((held ? store.Held : Unconverted(store.Value, store.Field.Type)) is not HField { Object: { } from } read || !ReferenceEquals(read.Field, store.Field) ||
                    !SameType(from.Type, type) || (source != null && !HirCleanup.Same(source, from)) || !(held || Settled(store)))
                    return null;
                source ??= from;
            }
            // The other struct is named once for each field, so naming it must do nothing - unless there is
            // one field only, read where it is stored: then it is named once here as well.
            if (source != null && !HirCleanup.Same(source, place) &&
                (HirBuilder.IsPure(source) || (stores.Count == 1 && stores[0].TempAt < 0)))
                return new HAssign(place, source);
            return null;
        }
        // Only where nothing else says what the stores make: fields kept in variables (see HeldPart).
        HStmt? CopyOfHeld() => complete && stores.Any(x => x.Held != null) ? Copy(true) : null;

        if (complete && Copy(false) is { } copied) return copied;

        // Building a struct in its own constructor is that constructor's body, not a use of it.
        bool ownConstruction = place is HArg { Index: < 0 } && method.Method.IsConstructor && ReferenceEquals(method.Method.DeclaringType, owner);
        if (ownConstruction) return null;
        if (!stores.All(Settled)) return CopyOfHeld();

        HExpr Default() => new HTypeExpr(HTypeOp.Default, type, null) { Type = type };

        if (IsNullable(owner))
        {
            // "no value": the flag is cleared; what the value field holds then is nobody's business, and the
            // compiler often does not bother to clear it.
            Store? flag = stores.FirstOrDefault(x => x.Field.Name == "hasValue"), held = stores.FirstOrDefault(x => x.Field.Name == "value");
            if (flag != null && flag.Value is HConst { Value: false or 0 } && (held == null || IsZero(held.Value)) && stores.Count == (held == null ? 1 : 2))
                return new HAssign(place, Default());
            if (flag != null && held != null && stores.Count == 2 && flag.Value is HConst { Value: true or 1 } && Independent(held.Value) &&
                owner.Methods.FirstOrDefault(m => m.Name == ".ctor" && !m.IsStatic && m.Parameters.Length == 1) is { } wrap)
                return new HAssign(place, new HNewObject { Constructor = wrap, DeclaringType = type is GenericInstSig ? type : null, Arguments = [held.Value], Type = type });
            // The flag worked out (a copy that went through registers): a value or none, by that flag. A Nullable
            // that holds no value holds the default in its value field - nothing else makes one - so the value
            // given with a cleared flag is that default, whatever it is written as here.
            if (!NoNullableFlags && flag != null && held != null && stores.Count == 2 && flag.Value is not HConst && HirBuilder.IsPure(flag.Value) &&
                HirBuilder.IsPure(held.Value) && Independent(flag.Value) && Independent(held.Value) &&
                owner.Methods.FirstOrDefault(m => m.Name == ".ctor" && !m.IsStatic && m.Parameters.Length == 1) is { } wrapped)
            {
                HExpr flagged = flag.Value is HCompare or HUnary { Op: HUnaryOp.LogicalNot } || flag.Value.Type is PrimitiveSig { Element: Il2CppTypeEnum.Boolean }
                    ? flag.Value
                    : new HCompare(HCompareOp.Ne, flag.Value, new HConst(0, flag.Value.Type)) { Type = program.Model.Sigs.Primitive(Il2CppTypeEnum.Boolean) };
                return new HAssign(place, new HSelect(flagged,
                    new HNewObject { Constructor = wrapped, DeclaringType = type is GenericInstSig ? type : null, Arguments = [held.Value], Type = type },
                    Default()) { Type = type });
            }
            return null;
        }
        if (!complete) return null;

        if (stores.All(x => IsZero(x.Value))) return new HAssign(place, Default());

        // One of the type's constructors, applied to some values.
        TypeSig[] classArguments = type is GenericInstSig g ? g.Arguments : [];
        MethodDef? best = null;
        HExpr?[]? bestArguments = null;
        foreach (MethodDef constructor in owner.Methods)
        {
            if (constructor.Name != ".ctor" || constructor.IsStatic || constructor.Parameters.Length == 0 || ReferenceEquals(constructor, method.Method)) continue;
            if (best != null && best.Parameters.Length <= constructor.Parameters.Length) continue;
            HMethod? body = pipeline.ConstructorBody(constructor, classArguments);
            if (body == null) continue;
            List<HStmt> formulas = body.Blocks[0].Statements;
            var arguments = new HExpr?[constructor.Parameters.Length];
            var assigned = new HashSet<FieldDef>();
            // (inOrder: the parameter each value that does work is given to, in the order of the stores.)
            var worked = new List<(int Store, int Parameter)>();
            bool matches = true;
            for (int k = 0; k < formulas.Count - 1 && matches; k++)
            {
                if (formulas[k] is not HAssign { Target: HField { Object: HArg { Index: < 0 } } target, Value: var formula } ||
                    !assigned.Add(target.Field) || !values.TryGetValue(target.Field, out Store? actual))
                {
                    matches = false;
                    break;
                }
                bool working = inOrder && !HirBuilder.IsPure(actual.Value);
                matches = Unify(formula, actual.Value, arguments, (actual.Index == end && actual.TempAt < 0) || working);
                if (matches && working)
                {
                    if (formula is HArg { Index: >= 0 } given) worked.Add((actual.Index, given.Index));
                    else matches = false;
                }
            }
            if (!matches) continue;
            if (inOrder)
            {
                worked.Sort((x, y) => x.Store.CompareTo(y.Store));
                for (int k = 1; k < worked.Count && matches; k++) matches = worked[k - 1].Parameter < worked[k].Parameter;
                if (!matches) continue;
            }
            // A field the constructor leaves alone is zero in a new struct.
            if (stores.Any(x => !assigned.Contains(x.Field) && !IsZero(x.Value))) continue;
            if (arguments.Any(a => a != null && !Independent(a))) continue;
            best = constructor;
            bestArguments = arguments;
        }
        if (best == null || bestArguments == null) return CopyOfHeld();

        var final = new HExpr[best.Parameters.Length];
        for (int k = 0; k < final.Length; k++)
        {
            TypeSig parameter = best.Parameters[k].Type;
            if (classArguments.Length != 0) parameter = program.Model.Sigs.Substitute(parameter, classArguments, []);
            // A parameter the constructor never looks at: any value does.
            final[k] = bestArguments[k] ?? (parameter.IsValueType || parameter is GenericParamSig
                ? new HTypeExpr(HTypeOp.Default, parameter, null) { Type = parameter }
                : new HConst(null, parameter));
        }
        return new HAssign(place, new HNewObject { Constructor = best, DeclaringType = type is GenericInstSig ? type : null, Arguments = final, Type = type });
    }

    /// <summary>
    /// The arguments another constructor of the same struct would be given to make the same value, where both
    /// constructors only put their parameters and constants into the fields ("new Vector3(a, b)" is
    /// "new Vector3(a, b, 0f)"). Null when that cannot be said.
    /// </summary>
    internal static HExpr[]? Reexpress(HNewObject made, MethodDef wanted, MethodPipeline pipeline)
    {
        TypeSig[] classArguments = made.Type is GenericInstSig g ? g.Arguments : [];
        if (pipeline.ConstructorBody(made.Constructor, classArguments) is not { } from || pipeline.ConstructorBody(wanted, classArguments) is not { } to) return null;

        // What each field holds.
        var fields = new Dictionary<FieldDef, HExpr>();
        var used = new int[made.Arguments.Length];
        List<HStmt> statements = from.Blocks[0].Statements;
        for (int k = 0; k < statements.Count - 1; k++)
        {
            if (statements[k] is not HAssign { Target: HField { Object: HArg { Index: < 0 } } target, Value: var formula }) return null;
            HExpr? value = null;
            if (formula is HArg { Index: >= 0 } given && given.Index < made.Arguments.Length)
            {
                value = made.Arguments[given.Index];
                // Something that does work is worked out once, wherever it goes.
                if (++used[given.Index] > 1 && !HirBuilder.IsPure(value)) return null;
            }
            else if (formula is HConst) value = formula;
            if (value == null || !fields.TryAdd(target.Field, value)) return null;
        }

        // ... and what the other constructor must be given for the fields to hold that.
        var arguments = new HExpr?[wanted.Parameters.Length];
        var covered = new HashSet<FieldDef>();
        statements = to.Blocks[0].Statements;
        for (int k = 0; k < statements.Count - 1; k++)
        {
            if (statements[k] is not HAssign { Target: HField { Object: HArg { Index: < 0 } } target, Value: var formula } || !covered.Add(target.Field)) return null;
            if (!fields.TryGetValue(target.Field, out HExpr? held)) return null;
            switch (formula)
            {
                case HArg { Index: >= 0 } taken when taken.Index < arguments.Length:
                    if (arguments[taken.Index] is { } bound)
                    {
                        if (!HirBuilder.IsPure(bound) || !HirCleanup.Same(bound, held)) return null;
                    }
                    else arguments[taken.Index] = held;
                    break;
                case HConst constant:
                    if (held is not HConst same || !SameConst(constant.Value, same.Value)) return null;
                    break;
                default:
                    return null;
            }
        }
        if (fields.Keys.Any(f => !covered.Contains(f))) return null;
        var result = new HExpr[arguments.Length];
        for (int k = 0; k < result.Length; k++)
        {
            if (arguments[k] is not { } argument) return null;
            result[k] = argument;
        }
        return result;
    }

    /// <summary>
    /// Matches what a constructor stores in a field (written in terms of its parameters) against what a site
    /// stores there, finding the value each parameter must have had.
    /// </summary>
    private static bool Unify(HExpr? formula, HExpr? actual, HExpr?[] arguments, bool whole = false)
    {
        if (formula == null || actual == null) return formula == null && actual == null;
        switch (formula)
        {
            case HArg { Index: >= 0 } a:
                if (a.Index >= arguments.Length) return false;
                if (arguments[a.Index] is { } bound) return HirBuilder.IsPure(bound) && HirCleanup.Same(bound, actual);
                // Something that does work (a call) can be what a parameter was given only where it is the whole
                // of what the last store puts in: the constructor call then stands where it was computed.
                if (!HirBuilder.IsPure(actual) && !whole) return false;
                arguments[a.Index] = actual;
                return true;
            case HConst c:
                return actual is HConst ac && SameConst(c.Value, ac.Value);
            case HField f:
                return actual is HField af && ReferenceEquals(f.Field, af.Field) && Unify(f.Object, af.Object, arguments);
            case HUnary u:
                return actual is HUnary au && u.Op == au.Op && Unify(u.Operand, au.Operand, arguments);
            case HBinary b:
                return actual is HBinary ab && b.Op == ab.Op && Unify(b.Left, ab.Left, arguments) && Unify(b.Right, ab.Right, arguments);
            case HCompare c:
                return actual is HCompare ac2 && c.Op == ac2.Op && Unify(c.Left, ac2.Left, arguments) && Unify(c.Right, ac2.Right, arguments);
            case HConv c:
                return actual is HConv ac3 && c.Kind == ac3.Kind && Unify(c.Operand, ac3.Operand, arguments);
            case HSelect s:
                return actual is HSelect sel && Unify(s.Condition, sel.Condition, arguments) && Unify(s.WhenTrue, sel.WhenTrue, arguments) && Unify(s.WhenFalse, sel.WhenFalse, arguments);
            case HTypeExpr t:
                return actual is HTypeExpr at && t.Op == at.Op && t.Op != HTypeOp.Allocate && SameType(t.Target, at.Target) && Unify(t.Operand, at.Operand, arguments);
            case HNewObject n:
            {
                if (actual is not HNewObject an || !ReferenceEquals(n.Constructor, an.Constructor) || n.Arguments.Length != an.Arguments.Length || !IsStruct(n.Type)) return false;
                for (int i = 0; i < n.Arguments.Length; i++)
                    if (!Unify(n.Arguments[i], an.Arguments[i], arguments))
                        return false;
                return true;
            }
            default:
                return false;
        }
    }

    /// <summary>
    /// "t = value; return t;" and "t = value; place = t;" with a temporary that serves nothing else: the value
    /// goes where it is going.
    /// </summary>
    private static bool ForwardWholeValues(HMethod method, MethodPipeline pipeline)
    {
        bool any = false;
        Usage usage = Usage.Of(method);
        foreach (HBlock block in method.Blocks)
        {
            List<HStmt> s = block.Statements;
            for (int i = 0; i + 1 < s.Count; i++)
            {
                if (s[i] is not HAssign { Target: HLocal t, Value: var value } || !usage.IsTemp(t.Variable) || !IsStruct(t.Variable.Type)) continue;
                switch (s[i + 1])
                {
                    case HReturn { Value: HLocal r } ret when ReferenceEquals(r.Variable, t.Variable):
                        ret.Value = value;
                        break;
                    case HAssign { Value: HLocal r } next when ReferenceEquals(r.Variable, t.Variable) && !Mentions(next.Target, t.Variable) &&
                                                                 (InVariable(next.Target) || HirBuilder.IsPure(value)):
                        next.Value = value;
                        break;
                    default:
                        continue;
                }
                s.RemoveAt(i);
                usage = Usage.Of(method);
                any = true;
                i = Math.Max(-1, i - 2);
            }
        }
        if (!NoArgumentCopies && ForwardArgumentCopies(method, pipeline)) any = true;
        return any;
    }

    private static readonly bool NoArgumentCopies = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_ARGUMENT_COPIES") != null;

    /// <summary>
    /// "t = v; f(.., t, ..)": a struct copied into a variable only to be handed to a call, which gets a copy of
    /// its own anyway - "f(.., v, ..)". The compiler makes that copy in one place and not in another (code pasted
    /// in from a method that hands its parameter on, where the place already has the value in a variable of its
    /// own), so the two read alike once neither has it. Only for a value no call can change - a variable, a part of one,
    /// or a struct written out of such (the call's other arguments are worked out before it is handed over) - and a copy
    /// nothing looks at afterwards (the variable may be a slot the place uses for one thing after another).
    /// </summary>
    private static bool ForwardArgumentCopies(HMethod method, MethodPipeline pipeline)
    {
        bool any = false;
        Usage usage = Usage.Of(method);
        foreach (HBlock block in method.Blocks)
        {
            List<HStmt> s = block.Statements;
            for (int i = 0; i + 1 < s.Count; i++)
            {
                if (s[i] is not HAssign { Target: HLocal t, Value: var value } || (t.Variable.AddressTaken && AddressNamed(method, t.Variable)) || !IsStruct(t.Variable.Type) ||
                    !(value is HLocal or HArg or HField && CallProofIn(method, value) || Written(value, pipeline)) || Mentions(value, t.Variable) || !SameType(value.Type, t.Variable.Type)) continue;
                HCall? call = s[i + 1] switch
                {
                    HEval { Expression: HCall c } => c,
                    HAssign { Target: var target, Value: HCall c } when !Mentions(target, t.Variable) => c,
                    _ => null,
                };
                if (call == null || Mentions(call.This, t.Variable)) continue;
                int at = -1, named = 0;
                for (int k = 0; k < call.Arguments.Length; k++)
                {
                    if (call.Arguments[k] is HLocal { Variable: var v } && ReferenceEquals(v, t.Variable)) at = k;
                    if (Mentions(call.Arguments[k], t.Variable)) named++;
                }
                // (A variable set once and read once is a temporary of this alone, in a try region too.)
                if (at < 0 || named != 1 || !(usage.IsTemp(t.Variable) || InlineFolding.Renewed(method, block, i + 2, t.Variable))) continue;
                call.Arguments[at] = value;
                s.RemoveAt(i);
                usage = Usage.Of(method);
                any = true;
                i = Math.Max(-1, i - 2);
            }
        }
        return any;
    }

    private static readonly bool NoUnionCopies = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_UNION_COPIES") != null;
    private static readonly bool NoNullableFlags = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_NULLABLE_FLAGS") != null;

    /// <summary>
    /// A struct made anew from the bytes of another of its type, read through a field that lies over the others:
    /// "new Color32((byte)c.rgba, (byte)(c.rgba >> 8), (byte)(c.rgba >> 16), (byte)(c.rgba >> 24))" is "c". The
    /// compiler copies a small struct as one number; read back as fields, the number is the union's field over
    /// them all (and that field is the type's own business). Each byte the constructor fills must come from
    /// the same byte of the same struct, and every byte that is a field's must be filled.
    /// </summary>
    private static bool UnionCopies(HMethod method, ProgramAnalysis program, MethodPipeline pipeline)
    {
        bool any = false;
        HExpr? Map(HExpr e)
        {
            if (e is not HNewObject made || !IsStruct(made.Type) || made.Arguments.Length == 0 || CopiedBytes(made, program, pipeline) is not { } whole) return null;
            any = true;
            return whole;
        }
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
                EnumeratorLoops.Rewrite(s, Map);
        return any;
    }

    private static readonly bool NoHeldCopies = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_HELD_COPIES") != null;

    /// <summary>
    /// The same copy with other things worked out in between: the bytes are read into registers where the source
    /// names the struct ("t1 = s._data0; t2 = s._data1"), and the copy is put together where it is handed on
    /// ("f(new S(t1, t2), ..)"). The struct is taken whole where its bytes were read - "c = s" - and the copy
    /// used where it was made, so that it is still read when the source read it. The struct must not change
    /// between the first of the reads and the last.
    /// </summary>
    private static bool HeldUnionCopies(HMethod method, ProgramAnalysis program, MethodPipeline pipeline)
    {
        bool any = false;
        Usage usage = Usage.Of(method);
        foreach (HBlock block in method.Blocks)
        {
            List<HStmt> statements = block.Statements;
            for (int i = 0; i < statements.Count; i++)
            {
                var made = new List<HNewObject>();
                FinallyFolding.Visit(statements[i], e =>
                {
                    if (e is HNewObject { Arguments.Length: > 0 } n && IsStruct(n.Type) && n.Arguments.Any(a => a is HLocal)) made.Add(n);
                });
                foreach (HNewObject candidate in made)
                {
                    var reads = new List<int>();
                    int at = i;
                    HExpr? Held(HVar temp)
                    {
                        if (!usage.IsTemp(temp)) return null;
                        for (int k = at - 1; k >= 0; k--)
                            if (statements[k] is HAssign { Target: HLocal { Variable: var set }, Value: var value } && ReferenceEquals(set, temp))
                            {
                                if (value is not HField) return null;
                                reads.Add(k);
                                return value;
                            }
                        return null;
                    }
                    if (CopiedBytes(candidate, program, pipeline, Held) is not { } source || reads.Count == 0) continue;
                    // (Every part came through a variable: a part named in place is read later than the others.)
                    if (reads.Distinct().Count() != candidate.Arguments.Length) continue;
                    reads.Sort();
                    if (!Movable(source, statements, reads[0], reads[^1], null)) continue;
                    HVar copy = method.NewLocal(candidate.Type!, "s");
                    var whole = new HLocal(copy) { Type = candidate.Type };
                    statements[reads[0]] = new HAssign(new HLocal(copy) { Type = candidate.Type }, source);
                    EnumeratorLoops.Rewrite(statements[i], e => ReferenceEquals(e, candidate) ? whole : null);
                    for (int k = reads.Count - 1; k >= 1; k--) statements.RemoveAt(reads[k]);
                    i -= reads.Count - 1;
                    usage = Usage.Of(method);
                    any = true;
                    break;
                }
            }
        }
        return any;
    }

    private static HExpr? CopiedBytes(HNewObject made, ProgramAnalysis program, MethodPipeline pipeline, Func<HVar, HExpr?>? held = null)
    {
        TypeSig type = made.Type!;
        if (type.Definition is not { } definition || (definition.Flags & TypeDef.LayoutMask) != TypeDef.ExplicitLayout) return null;
        TypeLayout layout = program.Layouts.Of(type);
        if (!layout.Known || layout.Size <= 0 || layout.Size > 64) return null;
        TypeSig[] classArguments = type is GenericInstSig g ? g.Arguments : [];
        if (pipeline.ConstructorBody(made.Constructor, classArguments) is not { } body) return null;
        FieldSlot? SlotOf(FieldDef f)
        {
            foreach (FieldSlot slot in layout.Fields)
                if (ReferenceEquals(slot.Field, f))
                    return slot;
            return null;
        }
        // What each byte holds once the constructor is done: a byte of one of its parameters, or not that.
        var from = new (int Parameter, int Byte)[layout.Size];
        Array.Fill(from, (-1, -1));
        var placed = new Dictionary<int, (int Offset, int Size)>();
        List<HStmt> statements = body.Blocks[0].Statements;
        for (int k = 0; k < statements.Count - 1; k++)
        {
            if (statements[k] is not HAssign { Target: HField { Object: HArg { Index: < 0 } } target, Value: var value } || SlotOf(target.Field) is not { } slot ||
                slot.Offset < 0 || slot.Offset + slot.Size > layout.Size)
                return null;
            int parameter = value is HArg { Index: >= 0 } p && p.Index < made.Arguments.Length ? p.Index : value is HConst ? -1 : -2;
            if (parameter == -2) return null;
            if (parameter >= 0)
            {
                if (placed.ContainsKey(parameter)) return null;
                placed[parameter] = (slot.Offset, slot.Size);
            }
            for (int b = 0; b < slot.Size; b++) from[slot.Offset + b] = (parameter, b);
        }
        foreach (FieldSlot slot in layout.Fields)
            for (int b = slot.Offset; b < slot.Offset + slot.Size && b < layout.Size; b++)
                if (from[b].Parameter < 0)
                    return null;
        if (placed.Count != made.Arguments.Length) return null;

        HExpr? whole = null;
        foreach ((int parameter, (int offset, int size)) in placed)
        {
            // The argument: a field of the other struct, shifted down to the bytes wanted and cut to their width.
            HExpr argument = made.Arguments[parameter];
            // (A part read into a variable earlier: see HeldUnionCopies.)
            if (held != null && argument is HLocal { Variable: var kept } && held(kept) is { } read0) argument = read0;
            int width = size;
            while (argument is HConv { Kind: var kind } conv)
            {
                int to = kind switch
                {
                    HConvKind.I1 or HConvKind.U1 => 1,
                    HConvKind.I2 or HConvKind.U2 => 2,
                    HConvKind.I4 or HConvKind.U4 => 4,
                    HConvKind.I8 or HConvKind.U8 => 8,
                    _ => 0,
                };
                if (to == 0) return null;
                width = Math.Min(width, to);
                argument = conv.Operand;
            }
            if (width != size) return null;
            int shift = 0;
            if (argument is HBinary { Op: HBinaryOp.Shr or HBinaryOp.ShrUn, Right: HConst { Value: var bits } } shifted && Whole(bits) is { } by && by % 8 == 0)
            {
                shift = (int)by / 8;
                argument = shifted.Left;
                while (argument is HConv { Kind: HConvKind.I8 or HConvKind.U8 or HConvKind.I4 or HConvKind.U4 } wider) argument = wider.Operand;
            }
            if (argument is not HField { Object: { } of, Field: var over } || !SameType(of.Type, type) || SlotOf(over) is not { } read) return null;
            // (Signed or not, a shift leaves the bytes wanted as they are while they lie within the field.)
            if (read.Offset + shift != offset || shift + size > read.Size) return null;
            if (whole == null) whole = of;
            else if (!Twins(whole, of)) return null;
        }
        return whole;

        static long? Whole(object? value) => value switch
        {
            int n => n,
            long n => n,
            uint n => n,
            byte n => n,
            _ => null,
        };
    }

    /// <summary>The same expression written twice - calls included (a value the builder wrote out at each of its uses).</summary>
    private static bool Twins(HExpr a, HExpr b)
    {
        if (HirCleanup.Same(a, b)) return true;
        switch (a, b)
        {
            case (HCall x, HCall y):
                if (!ReferenceEquals(x.Method, y.Method) || x.Virtual != y.Virtual || x.Arguments.Length != y.Arguments.Length ||
                    (x.This == null) != (y.This == null) || (x.This != null && !Twins(x.This, y.This!)))
                    return false;
                for (int k = 0; k < x.Arguments.Length; k++)
                    if (!Twins(x.Arguments[k], y.Arguments[k]))
                        return false;
                return true;
            case (HField x, HField y):
                return ReferenceEquals(x.Field, y.Field) && x.Object != null && y.Object != null && Twins(x.Object, y.Object);
            default:
                return false;
        }
    }

    /// <summary>CallProof, with a variable whose address the statements never name (see AddressNamed) counted as one nothing points to.</summary>
    private static bool CallProofIn(HMethod method, HExpr e) => e switch
    {
        HLocal l => !l.Variable.AddressTaken || !AddressNamed(method, l.Variable),
        HField { Object: { } o } f => !f.Field.IsStatic && o.Type is { IsValueType: true } and not (ByRefSig or PointerSig) && CallProofIn(method, o),
        _ => CallProof(e),
    };

    /// <summary>A struct written out from values no call can change, by a constructor that only stores them: making it does nothing else.</summary>
    private static bool Written(HExpr value, MethodPipeline pipeline) =>
        value is HNewObject { Constructor: var constructor } made && IsStruct(made.Type) && made.Arguments.All(a => CallProof(a)) && OnlyStores(constructor, made.Type, pipeline);
}
