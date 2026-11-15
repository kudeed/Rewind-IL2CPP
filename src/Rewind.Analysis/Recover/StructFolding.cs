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
        bool any = false;
        foreach (HBlock block in method.Blocks)
        {
            // Inner structs first: folding "a.p.x = ..; a.p.y = .." into "a.p = .." is what lets "a" fold next.
            for (int round = 0; round < 6 && FoldBlock(method, block, program, pipeline); round++) any = true;
            if (DropRepeatedClears(block)) any = true;
        }
        if (ForwardWholeValues(method)) any = true;
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

    private static bool FoldBlock(HMethod method, HBlock block, ProgramAnalysis program, MethodPipeline pipeline)
    {
        List<HStmt> s = block.Statements;
        bool any = false;
        Usage usage = Usage.Of(method);
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

            HStmt? folded = Fold(method, place, owner, stores, s, end, program, pipeline, whole: shared != null);
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
        ProgramAnalysis program, MethodPipeline pipeline, bool whole = false)
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
        bool Settled(Store store) => store.TempAt >= 0 || store.Index == end || Movable(store.Value, statements, store.Index, end, null) ||
                                     (works && CallProof(store.Value) && Movable(store.Value, statements, store.Index, end - 1, null));
        bool Independent(HExpr value)
        {
            // What the new value is made of must not be the place that is being overwritten.
            foreach (HExpr read in ReadsOf(value))
                if (MayOverlap(read, place))
                    return false;
            return true;
        }

        // A copy: every field from the same field of one other struct.
        if (complete)
        {
            HExpr? source = null;
            bool copy = true;
            foreach (Store store in stores)
            {
                if (Unconverted(store.Value, store.Field.Type) is not HField { Object: { } from } read || !ReferenceEquals(read.Field, store.Field) ||
                    !SameType(from.Type, type) || (source != null && !HirCleanup.Same(source, from)) || !Settled(store))
                {
                    copy = false;
                    break;
                }
                source ??= from;
            }
            // The other struct is named once for each field, so naming it must do nothing - unless there is
            // one field only, read where it is stored: then it is named once here as well.
            if (copy && source != null && !HirCleanup.Same(source, place) &&
                (HirBuilder.IsPure(source) || (stores.Count == 1 && stores[0].TempAt < 0)))
                return new HAssign(place, source);
        }

        // Building a struct in its own constructor is that constructor's body, not a use of it.
        bool ownConstruction = place is HArg { Index: < 0 } && method.Method.IsConstructor && ReferenceEquals(method.Method.DeclaringType, owner);
        if (ownConstruction) return null;
        if (!stores.All(Settled)) return null;

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
            bool matches = true;
            for (int k = 0; k < formulas.Count - 1 && matches; k++)
            {
                matches = formulas[k] is HAssign { Target: HField { Object: HArg { Index: < 0 } } target, Value: var formula } &&
                          assigned.Add(target.Field) && values.TryGetValue(target.Field, out Store? actual) &&
                          Unify(formula, actual.Value, arguments, actual.Index == end && actual.TempAt < 0);
            }
            if (!matches) continue;
            // A field the constructor leaves alone is zero in a new struct.
            if (stores.Any(x => !assigned.Contains(x.Field) && !IsZero(x.Value))) continue;
            if (arguments.Any(a => a != null && !Independent(a))) continue;
            best = constructor;
            bestArguments = arguments;
        }
        if (best == null || bestArguments == null) return null;

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
    private static bool ForwardWholeValues(HMethod method)
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
        return any;
    }
}
