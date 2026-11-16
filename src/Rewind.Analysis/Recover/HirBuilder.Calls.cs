using Rewind.Analysis.Abi;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Runtime;
using Rewind.Analysis.X64;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

public sealed partial class HirBuilder
{
    // ---- argument access ---------------------------------------------------------------------------------------

    private static Node? Input(Node call, ArgSlotKind kind, int index)
    {
        var info = (CallInfo)call.Aux!;
        for (int i = 0; i < info.Slots.Count && i < call.In.Length; i++)
            if (info.Slots[i].Kind == kind && info.Slots[i].Index == index)
                return call.In[i];
        return null;
    }

    /// <summary>The value passed in argument position <paramref name="position"/> when it is an integer/pointer.</summary>
    private static Node? IntAt(Node call, int position) =>
        position < Win64Abi.RegisterSlots ? Input(call, ArgSlotKind.IntReg, position) : Input(call, ArgSlotKind.Stack, position - Win64Abi.RegisterSlots);

    private HExpr FloatAt(Node call, int position, bool isDouble)
    {
        TypeSig type = isDouble ? _double : _float;
        if (position >= Win64Abi.RegisterSlots)
        {
            Node? slot = Input(call, ArgSlotKind.Stack, position - Win64Abi.RegisterSlots);
            if (slot == null) return Missing(type);
            Sem s = Eval(slot);
            if (s is SPair pair) return AsFloat(pair.Low, type);           // a float occupies the low half of its stack slot
            if (s is SVal v) return AsFloat(v.Expr, type);
            return AsFloat(Value(slot), type);
        }
        Node? lo = Input(call, ArgSlotKind.FloatReg, position * 4);
        if (lo == null) return Missing(type);
        if (!isDouble) return AsFloat(FloatValue(lo), type);
        Node? hi = Input(call, ArgSlotKind.FloatReg, position * 4 + 1);
        if (Eval(lo) is SHalf { High: false } l && hi != null && Eval(hi) is SHalf { High: true } h && ReferenceEquals(l.Whole, h.Whole))
            return l.Whole;
        if (Eval(lo) is SVal { Expr: HConst { Value: int low } } && hi != null && Eval(hi) is SVal { Expr: HConst { Value: int high } })
            return new HConst(BitConverter.Int64BitsToDouble((long)(uint)high << 32 | (uint)low), _double);
        HExpr bits = CombineParts([new Part(0, 4, HalfBits(lo)), new Part(4, 4, hi != null ? HalfBits(hi) : new HConst(0, _int))], 8);
        return ValueFromBits(bits, _double, 8);
    }

    /// <summary>
    /// A float argument is a float whatever register its bits travelled through: a value the recovery knows only
    /// as an integer (a constant moved into the vector register, a merged general register) is its bit pattern.
    /// </summary>
    private HExpr AsFloat(HExpr e, TypeSig type)
    {
        TypeSig? have = e.Type ?? (e as HLocal)?.Variable.Type;
        if (have == null || IsFloat(have)) return e;
        return Coerce(e, type);
    }

    private HExpr Missing(TypeSig type)
    {
        Problem("call argument was not captured");
        return new HOpaque("missing_argument") { Type = type };
    }

    private Dictionary<int, Node> Projections(Node call)
    {
        var result = new Dictionary<int, Node>();
        List<Node> nodes = call.Block!.Nodes;
        for (int i = _position[call] + 1; i < nodes.Count && nodes[i].Op == Op.Proj && ReferenceEquals(nodes[i].In[0], call); i++)
            result[(int)nodes[i].Imm] = nodes[i];
        return result;
    }

    private bool IsUsed(Node n) => _uses.TryGetValue(n, out List<Node>? uses) && uses.Count != 0;

    // ---- frame object types ------------------------------------------------------------------------------------

    private bool IsFrameAddress(Node n, out int offset)
    {
        offset = 0;
        if (!_fn.Params.TryGetValue(X64Lifter.VarRsp, out Node? sp0)) return false;
        if (ReferenceEquals(n, sp0)) return true;
        if (n.Op == Op.Add && ReferenceEquals(n.In[0], sp0) && n.In[1].IsConst)
        {
            offset = (int)IrBuilder.SImm(n.In[1]);
            return true;
        }
        return false;
    }

    private static TypeSig? PointeeOf(MethodAbi abi, int position)
    {
        foreach (AbiParam p in abi.Params)
        {
            if (p.Position != position) continue;
            if (p.Role == ParamRole.ReturnBuffer) return abi.ReturnType;
            if (p.Pass == PassKind.Indirect) return p.Type;
            if (p.Type is ByRefSig byRef) return byRef.ElementType;
            if (p.Type is PointerSig pointer && !pointer.ElementType.IsVoid) return pointer.ElementType;
            if (p.Role == ParamRole.This && p.Type?.Definition is { IsValueType: true }) return p.Type;
        }
        return null;
    }

    /// <summary>
    /// To call a method of Object, ValueType or Enum on a value (rule.ToString() on an enum, say), generated
    /// code does not allocate a box: it writes an object header - the class and a mark meaning "not a real
    /// object" - right in front of a copy of the value on the stack, and passes the address of that. In
    /// managed terms the address is the boxed value.
    /// </summary>
    private void FindFakeBoxes()
    {
        Dictionary<int, TypeSig>? classes = null;
        HashSet<int>? marks = null;
        foreach (Block b in _fn.Blocks)
        {
            foreach (Node n in b.Nodes)
            {
                if (n.Dead || n.Op != Op.Store || !IsFrameAddress(n.In[0], out int offset)) continue;
                Node value = n.In[1];
                if (value.Op == Op.SlotValue)
                {
                    if (EvalKlass(value) is { IsValueType: true } type) (classes ??= [])[offset] = type;
                }
                else if (value.IsConst && value.Type == VT.I64 && value.Imm == -1) (marks ??= []).Add(offset);
            }
        }
        // The same, done by the runtime's constructor: Il2CppFakeBox<T>(box, klass, &value).
        foreach (Block b in _fn.Blocks)
            foreach (Node n in b.Nodes)
                if (!n.Dead && n.Op == Op.Call && n.Aux is CallInfo { Indirect: false, Intrinsic: null } ci &&
                    _p.Helpers.KindAt(ci.Target) == HelperKind.FakeBoxInit && IntAt(n, 0) is { } box && IsFrameAddress(box, out int at) &&
                    IntAt(n, 1) is { } klass && EvalKlass(klass) is { IsValueType: true } boxed)
                {
                    _fakeBoxes[at] = boxed;
                    _frameTypes[at + _header] = boxed;
                }
        if (classes == null || marks == null) return;
        foreach (var (offset, type) in classes)
        {
            if (!marks.Contains(offset + _ptr)) continue;
            _fakeBoxes[offset] = type;
            _frameTypes[offset + _header] = type;
        }
    }

    /// <summary>
    /// Stack memory handed to a call takes its type from what the callee expects there: a struct receiver, a
    /// by-reference argument, a struct passed or returned through a hidden pointer, a value being boxed.
    /// </summary>
    private void InferFrameTypes()
    {
        foreach (Block b in _fn.Blocks)
        {
            foreach (Node call in b.Nodes)
            {
                if (call.Dead || call.Op is not (Op.Call or Op.TailCall) || call.Aux is not CallInfo info || info.Intrinsic != null) continue;
                for (int i = 0; i < call.In.Length && i < info.Slots.Count; i++)
                {
                    if (!IsFrameAddress(call.In[i], out int offset)) continue;
                    ArgSlot slot = info.Slots[i];
                    int position = slot.Kind == ArgSlotKind.IntReg ? slot.Index : slot.Kind == ArgSlotKind.Stack ? slot.Index + Win64Abi.RegisterSlots : -1;
                    if (position < 0) continue;
                    TypeSig? type = null;
                    if (!info.Indirect)
                    {
                        CallTarget target = _p.Resolve(info.Target);
                        if (target.Helper is { } helper && !target.IsManaged)
                        {
                            if (helper.Kind == HelperKind.Box && position == 1 && IntAt(call, 0) is { } k) type = EvalKlass(k);
                            else if (helper.Kind is HelperKind.UnboxAny or HelperKind.UnboxNullable && position == 2 && IntAt(call, 1) is { } k2) type = EvalKlass(k2);
                        }
                        else
                        {
                            if (NoReachableAssemblies)
                            {
                                foreach (MethodDef m in target.Methods)
                                    if ((type = PointeeOf(_p.Abi.For(m, [], []), position)) != null) break;
                                if (type == null)
                                    foreach (MethodInst inst in target.Insts)
                                        if ((type = PointeeOf(_p.Abi.For(inst), position)) != null) break;
                            }
                            else
                            {
                                // Of the methods that share the code, only those this code could call say anything:
                                // the first of them that takes a pointer there, where few do. Where more do (an empty
                                // function serves thousands of methods), the first is a guess unless they all say the
                                // same; which was called is then decided with the call, and the type with it.
                                var pointees = new List<TypeSig>();
                                bool differ = false;
                                int wanted = SharedPointeeLimit == int.MaxValue ? 1 : 64;
                                void Add(TypeSig t)
                                {
                                    if (pointees.Count != 0 && !ReferenceEquals(t, pointees[0]) && t.Key != pointees[0].Key) differ = true;
                                    pointees.Add(t);
                                }
                                foreach (MethodDef m in target.Methods)
                                    if (pointees.Count < wanted && Reachable(m.DeclaringType.Assembly) && PointeeOf(_p.Abi.For(m, [], []), position) is { } t)
                                        Add(t);
                                foreach (MethodInst inst in target.Insts)
                                    if (pointees.Count < wanted && Reachable(inst.Method.DeclaringType.Assembly) && PointeeOf(_p.Abi.For(inst), position) is { } t)
                                        Add(t);
                                if (pointees.Count != 0 && (pointees.Count <= SharedPointeeLimit || !differ)) type = pointees[0];
                            }
                        }
                    }
                    if (type != null && !Open(type) && Nameable(type)) _frameTypes.TryAdd(offset, type);
                }
            }
        }
        SpreadFrameTypes();
        DropCoveredFrameTypes();
    }

    /// <summary>
    /// Stack memory typed from a call on a field of a struct local ("machine.builder.Start(ref machine)" types
    /// both the machine and, inside it, the builder) is one object, the struct: the inner type is the type of
    /// the struct's field at that place and adds nothing. Types that do not agree with the field stay - that is
    /// memory used for two things.
    /// </summary>
    private void DropCoveredFrameTypes()
    {
        if (_frameTypes.Count < 2) return;
        foreach (var (inner, innerType) in _frameTypes.ToList())
        {
            if (_fakeBoxes.ContainsKey(inner - _header)) continue;
            foreach (var (outer, outerType) in _frameTypes)
            {
                if (outer >= inner || !IsStructType(outerType) || Open(outerType)) continue;
                if (inner >= outer + _p.Layouts.SizeOf(outerType).Size) continue;
                TypeSig type = outerType;
                int offset = inner - outer;
                bool covered = false;
                for (int depth = 0; depth < 8; depth++)
                {
                    if (_p.Layouts.FieldAt(type, offset) is not { } slot) break;
                    if (slot.Offset == offset && (slot.Type.Key == innerType.Key || (IsReference(slot.Type) && IsReference(innerType))))
                    {
                        covered = true;
                        break;
                    }
                    if (!IsStructType(slot.Type)) break;
                    offset -= slot.Offset;
                    type = slot.Type;
                }
                if (!covered) continue;
                _frameTypes.Remove(inner);
                break;
            }
        }
    }

    /// <summary>The storage location a pointer argument refers to.</summary>
    private HExpr? LocationOf(Node pointer, TypeSig? expected)
    {
        // (What the code cannot name says nothing about its stack.)
        if (!Nameable(expected)) expected = null;
        Sem s = Eval(pointer);
        switch (s)
        {
            case SRef r:
                return r.Location;
            case SFrame f:
            {
                // An address inside a struct local is the address of one of its fields (or of the fields that
                // start there): nothing new is learned about the stack.
                if (!_frameTypes.ContainsKey(f.Offset) && FrameObjectAt(f.Offset) is int enclosing && IsStructType(_frameTypes[enclosing]))
                {
                    int wanted = expected != null && !Open(expected) ? _p.Layouts.SizeOf(expected).Size : -1;
                    if (FramePlace(f.Offset, wanted) is PLocation field &&
                        (expected == null || wanted < 0 || _p.Layouts.SizeOf(field.Type).Size == wanted))
                        return field.Location;
                }
                if (expected != null && !_frameTypes.ContainsKey(f.Offset))
                {
                    _frameTypes[f.Offset] = expected;
                    // Learned only now: statements already translated may have treated these bytes as loose
                    // slots. Building again with the type known from the start puts them in one variable.
                    if (!Open(expected))
                    {
                        RefinedFrameTypes[f.Offset] = expected;
                        FrameTypesRefined = true;
                    }
                }
                if (expected != null && !Open(expected))
                {
                    if (!_frameVotes.TryGetValue(f.Offset, out HashSet<TypeSig>? votes)) _frameVotes[f.Offset] = votes = [];
                    votes.Add(expected);
                }
                return FramePlace(f.Offset, -1) is PLocation loc ? loc.Location : null;
            }
            case SStatics statics:
            {
                // The address of a class's static data is the address of its first static field.
                TypeDef? owner = statics.Type.Definition;
                FieldDef? first = owner?.Fields.FirstOrDefault(f => f.IsStatic && !f.IsLiteral && f.Offset == 0);
                if (first == null) return null;
                TypeSig fieldType = statics.Type is GenericInstSig generic ? _m.Sigs.Substitute(first.Type, generic.Arguments, []) : first.Type;
                return new HField { Object = null, Field = first, DeclaringType = statics.Type, Type = fieldType };
            }
            case SVal { Type: ByRefSig byRef } v:
                return new HDeref(v.Expr) { Type = byRef.ElementType };
            case SVal { Type: PointerSig pointerType } v:
                return new HDeref(v.Expr) { Type = pointerType.ElementType };
            default:
                return null;
        }
    }

    // ---- results -----------------------------------------------------------------------------------------------

    private void FinishCall(Node call, HExpr expr, ReturnKind kind, TypeSig returnType, bool tail)
    {
        expr.Type ??= returnType;
        if (tail)
        {
            if (kind == ReturnKind.Void || _abi.Return == ReturnKind.Void)
            {
                Emit(new HEval(expr), call.Addr);
                Emit(new HReturn(null), call.Addr);
            }
            else Emit(new HReturn(expr), call.Addr);
            return;
        }

        Dictionary<int, Node> projs = Projections(call);
        switch (kind)
        {
            case ReturnKind.Void:
                Emit(new HEval(expr), call.Addr);
                break;
            case ReturnKind.Double:
            {
                projs.TryGetValue(CallResult.FloatLane0, out Node? lo);
                projs.TryGetValue(CallResult.FloatLane1, out Node? hi);
                if ((lo != null && IsUsed(lo)) || (hi != null && IsUsed(hi)))
                {
                    HVar t = Temp(_double, VT.F64);
                    Emit(new HAssign(new HLocal(t) { Type = _double }, expr), call.Addr);
                    var whole = new HLocal(t) { Type = _double };
                    if (lo != null) _sem[lo] = new SHalf(whole, false, null);
                    if (hi != null) _sem[hi] = new SHalf(whole, true, null);
                }
                else Emit(new HEval(expr), call.Addr);
                break;
            }
            default:
            {
                int which = kind == ReturnKind.Float ? CallResult.FloatLane0 : CallResult.IntReturn;
                if (!projs.TryGetValue(which, out Node? result) || !IsUsed(result))
                {
                    Emit(new HEval(expr), call.Addr);
                    break;
                }
                if (_materialize.Contains(result) || expr is HOpaque)
                {
                    HVar t = Temp(returnType, result.Type);
                    Emit(new HAssign(new HLocal(t) { Type = t.Type }, expr), call.Addr);
                    _sem[result] = new SVal(new HLocal(t) { Type = t.Type });
                }
                else _sem[result] = new SVal(expr); // folded into its single, immediately following consumer
                break;
            }
        }
    }

    // ---- dispatch ----------------------------------------------------------------------------------------------

    private static readonly bool NoNamedCopies = Environment.GetEnvironmentVariable("REWIND_NO_NAMED_COPIES") != null;

    /// <summary>
    /// A function that no table lists, handed a method's descriptor exactly where that method takes its own: the
    /// compiler writes small methods out a second time next to their callers, and code shared between
    /// instantiations hands such a copy its descriptor as it would the original. The caller thereby says which
    /// method it means; that the code at the address is that method's is then checked (read as the method, both
    /// must give the same statements).
    /// </summary>
    private CallTarget? NamedCopy(Node call, ulong address)
    {
        // Only in the method asked for: a check started from within another's would start others in turn. (In
        // the reading that a check compares, the function being checked calling itself is the method calling
        // itself.)
        bool own = _p.OwnTranslation && _p.Translations == 1;
        if (!own && !_p.CheckingCopies) return null;
        for (int position = 0; position < Win64Abi.RegisterSlots; position++)
        {
            if (IntAt(call, position) is not { } handed || Peek(handed) is not SMethod named) continue;
            MethodAbi abi = named.Inst != null ? _p.Abi.For(named.Inst) : _p.Abi.For(named.Method, [], []);
            if (abi.Params[^1].Position != position) continue;
            if (!(_p.AssumedCopy(address, named.Method) || (own && _p.IsCopyOf(address, named.Method, named.Inst)))) continue;
            _h.Notes.Add($"call target 0x{address:X} is handed the descriptor of {named.Method.FullName} and has the same recovered code: a private copy of it");
            var target = new CallTarget();
            if (named.Inst != null) target.Insts.Add(named.Inst);
            else target.Methods.Add(named.Method);
            return target;
        }
        return null;
    }

    private void EmitCall(Node call, bool tail)
    {
        var info = (CallInfo)call.Aux!;
        if (info.Intrinsic != null)
        {
            EmitIntrinsic(call, info);
            return;
        }
        if (info.Indirect)
        {
            EmitIndirectCall(call, tail);
            return;
        }
        CallTarget target = _p.Resolve(info.Target);
        if (!target.IsManaged && target.Helper == null && InvokerShape(info.Target) is { } invoker)
        {
            EmitHelperCall(call, invoker, tail);
            return;
        }
        if (!target.IsManaged && target.Helper == null && !NoNamedCopies && NamedCopy(call, info.Target) is { } named) target = named;
        if (target.IsManaged)
        {
            EmitManagedCall(call, target, tail);
            return;
        }
        if (target.Helper != null)
        {
            EmitHelperCall(call, target.Helper, tail);
            return;
        }
        Problem($"call to unidentified native function 0x{info.Target:X}");
        var args = new List<HExpr>();
        for (int i = 0; i < 4; i++)
            if (IntAt(call, i) is { } a && Eval(a) is not SJunk)
                args.Add(Value(a));
        FinishCall(call, new HOpaque($"native_0x{info.Target:X}", args.ToArray()) { Type = _long }, info.NoReturn ? ReturnKind.Void : ReturnKind.Integer, _long, tail);
        if (info.NoReturn) Emit(new HThrow(new HOpaque("noreturn")), call.Addr);
    }

    private void EmitIntrinsic(Node call, CallInfo info)
    {
        if (TryEmitBlockOp(call)) return;
        HExpr[] args = call.In.Select(Value).ToArray();
        var expr = new HOpaque(info.Intrinsic!, args) { Type = TypeForBits(call.Type) };
        if (info.Intrinsic == "memory_barrier") return; // volatile access marker
        Problem($"intrinsic {info.Intrinsic}");
        if (call.Type != VT.None && IsUsed(call))
        {
            HVar t = Temp(null, call.Type);
            Emit(new HAssign(new HLocal(t) { Type = t.Type }, expr), call.Addr);
            _sem[call] = new SVal(new HLocal(t) { Type = t.Type });
        }
        else Emit(new HEval(expr), call.Addr);
    }

    // ---- managed calls -----------------------------------------------------------------------------------------

    private bool IsAssignable(TypeSig? from, TypeSig to)
    {
        if (from == null) return true;
        if (ReferenceEquals(from, to)) return true;
        if (to is PrimitiveSig { Element: Rewind.Runtime.Il2CppTypeEnum.Object }) return IsReference(from);
        TypeDef? target = to.Definition;
        if (target == null) return false;
        for (TypeSig? t = from; t?.Definition != null;)
        {
            TypeDef def = t.Definition;
            if (ReferenceEquals(def, target)) return true;
            if (target.IsInterface)
                foreach (TypeSig i in def.Interfaces)
                    if (ReferenceEquals(i.Definition, target))
                        return true;
            if (def.BaseType == null) break;
            t = _m.Sigs.Substitute(def.BaseType, t is GenericInstSig g ? g.Arguments : [], []);
        }
        return false;
    }

    /// <summary>The nearest type both fit in: one of them when it takes the other, else the first base class of one that takes the other.</summary>
    private TypeSig JoinTypes(TypeSig a, TypeSig b)
    {
        if (IsAssignable(b, a)) return a;
        if (IsAssignable(a, b)) return b;
        for (TypeSig? t = a; t?.Definition != null;)
        {
            TypeDef def = t.Definition;
            if (def.BaseType == null) break;
            t = _m.Sigs.Substitute(def.BaseType, t is GenericInstSig g ? g.Arguments : [], []);
            if (t != null && IsAssignable(b, t)) return t;
        }
        return _object;
    }

    /// <summary>
    /// The form of a generic argument that decides which compiled body an instantiation uses: all reference
    /// types share one body, an enum shares with its underlying integer type, other value types stand alone.
    /// </summary>
    private TypeSig CanonicalArgument(TypeSig t)
    {
        if (IsReference(t)) return _object;
        if (t.Definition is { IsEnum: true, EnumUnderlyingType: { } underlying }) return underlying;
        if (t is GenericInstSig g) return _m.Sigs.GenericInst(g.Definition!, g.Arguments.Select(CanonicalArgument).ToArray());
        return t;
    }

    private bool SharesCode(TypeSig a, TypeSig b)
    {
        if (a is not GenericInstSig ga || b is not GenericInstSig gb || !ReferenceEquals(ga.Definition, gb.Definition)) return false;
        if (ga.Arguments.Length != gb.Arguments.Length) return false;
        for (int i = 0; i < ga.Arguments.Length; i++)
            if (!ReferenceEquals(CanonicalArgument(ga.Arguments[i]), CanonicalArgument(gb.Arguments[i])))
                return false;
        return true;
    }

    /// <summary>
    /// The generic arguments with which <paramref name="declaring"/> appears in the type of a receiver (looking
    /// through base classes and interfaces): the instantiation a call on that receiver really refers to.
    /// </summary>
    private TypeSig[]? DeclaringArguments(TypeSig? type, TypeDef declaring)
    {
        for (int depth = 0; type != null && depth < 32; depth++)
        {
            if (type is GenericInstSig g && ReferenceEquals(g.Definition, declaring))
                return g.Arguments.Any(Open) ? null : g.Arguments;
            TypeDef? def = type.Definition;
            if (def == null) return null;
            TypeSig[] arguments = type is GenericInstSig inst ? inst.Arguments : [];
            if (declaring.IsInterface)
                foreach (TypeSig i in def.Interfaces)
                    if (_m.Sigs.Substitute(i, arguments, []) is GenericInstSig gi && ReferenceEquals(gi.Definition, declaring) &&
                        !gi.Arguments.Any(Open))
                        return gi.Arguments;
            if (def.BaseType == null) return null;
            type = _m.Sigs.Substitute(def.BaseType, arguments, []);
        }
        return null;
    }

    /// <summary>Whether IL in the current method could name <paramref name="callee"/> at all.</summary>
    private bool IsAccessible(MethodDef callee)
    {
        TypeDef from = _method.DeclaringType, owner = callee.DeclaringType;
        bool Within(TypeDef inner, TypeDef outer)
        {
            for (TypeDef? t = inner; t != null; t = t.DeclaringType)
                if (ReferenceEquals(t, outer))
                    return true;
            return false;
        }
        bool Derives(TypeDef type, TypeDef ancestor)
        {
            int guard = 0;
            for (TypeDef? t = type; t != null && guard++ < 64; t = t.BaseType?.Definition)
                if (ReferenceEquals(t, ancestor))
                    return true;
            return false;
        }
        bool sameAssembly = ReferenceEquals(from.Assembly, owner.Assembly);
        bool family = false;
        for (TypeDef? t = from; t != null && !family; t = t.DeclaringType) family = Derives(t, owner);
        return (callee.Flags & MethodDef.AccessMask) switch
        {
            6 => true,                               // public
            1 => Within(from, owner),                // private
            3 => sameAssembly,                       // internal
            4 => family || Within(from, owner),      // protected
            5 => family || sameAssembly,             // protected internal
            2 => family && sameAssembly,             // private protected
            _ => Within(from, owner),
        };
    }

    /// <summary>What a value is, without using it (see _peeking).</summary>
    private Sem Peek(Node n)
    {
        _peeking++;
        try
        {
            return Eval(n);
        }
        finally
        {
            _peeking--;
        }
    }

    private int Score(Node call, MethodDef method, TypeSig[] classArgs, TypeSig[] methodArgs, MethodInst? inst)
    {
        _peeking++;
        try
        {
            return ScoreCore(call, method, classArgs, methodArgs, inst);
        }
        finally
        {
            _peeking--;
        }
    }

    private int ScoreCore(Node call, MethodDef method, TypeSig[] classArgs, TypeSig[] methodArgs, MethodInst? inst)
    {
        MethodAbi abi = _p.Abi.For(method, classArgs, methodArgs);
        int score = 0;
        foreach (AbiParam p in abi.Params)
        {
            if (p.Role == ParamRole.MethodInfo)
            {
                // Generic methods receive their own MethodInfo: an exact identification when present.
                if (IntAt(call, p.Position) is { } mi && Eval(mi) is SMethod sm)
                {
                    if (inst != null && sm.Inst != null && ReferenceEquals(sm.Inst, inst)) score += 1000;
                    else if (inst == null && sm.Inst == null && ReferenceEquals(sm.Method, method)) score += 1000;
                    else if (ReferenceEquals(sm.Method, method)) score += 200;
                    else score -= 500;
                }
                continue;
            }
            if (p.Pass == PassKind.Float || p.Type == null) continue;
            Node? node = IntAt(call, p.Position);
            if (node == null) continue;
            Sem s = Eval(node);
            // An argument the caller never set: this method takes more than the call passes.
            if (p.Role == ParamRole.Argument && (node.Op == Op.Undef || (node.Op == Op.Param && s is SJunk))) score -= 15;
            // A runtime class pointer is no object a method could be called on: what is called takes no receiver
            // (a static method sharing the code) and the register merely still holds it.
            if (p.Role == ParamRole.This && !NoReachableAssemblies && s is SKlass) score -= 50;
            // A method of a struct is called on the address of one. A receiver that is no address of anything
            // (a number, a leftover) means the call is to something else that shares this code.
            if (p.Role == ParamRole.This && p.Type.Definition is { IsValueType: true } &&
                s is not (SRef or SFrame or SUnboxed or SStatics) && !(s is SVal { Type: ByRefSig or PointerSig }) &&
                !(s is SVal { Type: { } boxed } && IsReference(boxed)))
                score -= 40;
            // A constructor runs a constructor of its base class (or another of its own) on the object it is
            // building, once, before anything else is called on it. An empty base constructor shares its code
            // with every other empty method of the program; of all of those, this is the one that is meant.
            if (p.Role == ParamRole.This && !_baseConstructorCalled && _method.Name == ".ctor" && method.Name == ".ctor" &&
                !ReferenceEquals(method, _method) && s is SVal { Expr: HArg { Index: -1 } } &&
                (ReferenceEquals(method.DeclaringType, _method.DeclaringType.BaseType?.Definition) || ReferenceEquals(method.DeclaringType, _method.DeclaringType) ||
                 // (The base class's constructor pasted in: the one it calls in turn is further up.)
                 (!NoFreshReceivers && Derives(_method.DeclaringType, method.DeclaringType))))
                score += 40;
            // Before a constructor has run the one of its base class, nothing but stores is done to the object:
            // an empty method of its class called there is the empty base constructor that shares its code.
            if (p.Role == ParamRole.This && !NoFreshReceivers && !_baseConstructorCalled && _method.Name == ".ctor" && !_method.IsStatic &&
                !_method.DeclaringType.IsValueType && method.Name != ".ctor" && s is SVal { Expr: HArg { Index: -1 } })
                score -= 40;
            // The first thing run on a freshly allocated object is a constructor of its class or of a class it
            // derives from ("new T()", or T's constructor pasted in and its base constructor called). An empty
            // constructor shares its code with every other empty method - a Dispose that does nothing, say - and
            // calling one of those on an object no constructor has run on is not what was written.
            if (p.Role == ParamRole.This && !NoFreshReceivers && s is SNewObject { Constructed: false } fresh && fresh.Type.Definition is { } allocated)
            {
                if (method.Name != ".ctor") score -= 40;
                else if (Derives(allocated, method.DeclaringType)) score += 40;
                else score -= 100;
            }
            TypeSig? actual = s switch
            {
                SVal v => v.Type,
                SRef r => r.Type,
                SNewObject o => o.Type,
                // The address of a stack object: what lives there (a struct local as receiver or by reference,
                // a value boxed in place as an object).
                SFrame f when _fakeBoxes.ContainsKey(f.Offset) => _object,
                SFrame f when _frameTypes.TryGetValue(f.Offset, out TypeSig? local) => local,
                _ => null,
            };
            if (actual == null) continue;
            TypeSig expected = p.Type is ByRefSig byRef ? byRef.ElementType : p.Type;
            if (p.Role == ParamRole.ReturnBuffer) expected = abi.ReturnType;
            if (ReferenceEquals(actual, expected)) score += p.Role == ParamRole.This ? 20 : 4;
            else if (SharesCode(actual, expected)) score += p.Role == ParamRole.This ? 16 : 3;
            else if (IsReference(actual) && IsReference(expected))
                score += IsAssignable(actual, expected) ? (p.Role == ParamRole.This ? 10 : 2) : (p.Role == ParamRole.This ? -100 : -20);
            else if (IsReference(actual) != IsReference(expected) && !(s is SRef)) score -= 30;
        }
        // What the call gives goes straight into a place whose type is known (a field, a typed piece of the
        // stack): of the methods that share this code, the one that gives that type is the one written.
        if (!NoResultPlaces && abi.ReturnType is { IsVoid: false } gives && ResultPlace(call) is { } wanted &&
            (ReferenceEquals(gives, wanted) || gives.Key == wanted.Key))
            score += 6;
        // A method calling the same-named method of a base type is the usual "base.Method()" shape.
        if (method.Name == _method.Name && !ReferenceEquals(method, _method)) score += 3;
        // Code that could not have been written here (a private member of an unrelated class) can still show
        // up through inlining, so this is a strong hint rather than a rule.
        if (!IsAccessible(method)) score -= 25;
        // An assembly's code can only name what is in it or in the assemblies it uses: a plugin cannot call into
        // the game that uses it. (Inlined code comes from such assemblies too, so it is no exception.)
        if (!NoReachableAssemblies && !Reachable(method.DeclaringType.Assembly)) score -= 200;
        return score;
    }

    /// <summary>More methods than this taking a pointer where one piece of code they share is handed one (see InferFrameTypes): the first of them is a guess.</summary>
    private static readonly int SharedPointeeLimit = int.TryParse(Environment.GetEnvironmentVariable("REWIND_SHARED_POINTEE_LIMIT"), out int limit) ? limit : 2;
    private static readonly bool NoReachableAssemblies = Environment.GetEnvironmentVariable("REWIND_NO_REACHABLE_ASSEMBLIES") != null;

    /// <summary>
    /// Whether IL of this method's assembly can name a type at all (it and its type arguments come from the
    /// assembly or one it refers to directly): a type it cannot name is never what one of its locals is.
    /// </summary>
    private bool Nameable(TypeSig? type) => NoReachableAssemblies || AssemblyScope.Names(_method.DeclaringType.Assembly, type);

    /// <summary>
    /// Whether code of this method's assembly can end up calling into <paramref name="assembly"/>: it is the
    /// assembly itself or one it refers to, directly or through others (see AssemblyScope).
    /// </summary>
    private bool Reachable(AssemblyModel assembly) => NoReachableAssemblies || AssemblyScope.Reaches(_method.DeclaringType.Assembly, assembly);

    private static readonly bool NoResultPlaces = Environment.GetEnvironmentVariable("REWIND_NO_RESULT_PLACES") != null;
    private static readonly bool NoFreshReceivers = Environment.GetEnvironmentVariable("REWIND_NO_FRESH_RECEIVERS") != null;

    /// <summary>Whether <paramref name="type"/> is <paramref name="ancestor"/> or derives from it.</summary>
    private static bool Derives(TypeDef type, TypeDef ancestor)
    {
        int guard = 0;
        for (TypeDef? t = type; t != null && guard++ < 64; t = t.BaseType?.Definition)
            if (ReferenceEquals(t, ancestor))
                return true;
        return false;
    }

    private readonly Dictionary<Node, TypeSig?> _resultPlaces = [];

    /// <summary>
    /// The type of the place a call's result is put into as it comes back - a field of an object, a piece of
    /// the stack whose type is known; null when it goes anywhere else.
    /// </summary>
    private TypeSig? ResultPlace(Node call)
    {
        if (_resultPlaces.TryGetValue(call, out TypeSig? known)) return known;
        TypeSig? type = null;
        if (call.Block != null && _position.ContainsKey(call) && Projections(call).TryGetValue(CallResult.IntReturn, out Node? result))
        {
            var holders = new List<Node> { result };
            if (_uses.TryGetValue(result, out List<Node>? direct))
                foreach (Node use in direct)
                    if (!use.Dead && use.Op == Op.Trunc)
                        holders.Add(use);
            foreach (Node holder in holders)
            {
                if (type != null || !_uses.TryGetValue(holder, out List<Node>? uses)) continue;
                foreach (Node store in uses)
                {
                    if (store.Dead || store.Op != Op.Store || !ReferenceEquals(store.In[1], holder) || !ReferenceEquals(store.Block, call.Block)) continue;
                    Node address = store.In[0];
                    int bytes = holder.Type.Bytes();
                    TypeSig? found = null;
                    if (IsFrameAddress(address, out int offset))
                    {
                        if (_frameTypes.TryGetValue(offset, out TypeSig? local)) found = local;
                    }
                    else if (address.Op == Op.Add && address.In[1].IsConst && Peek(address.In[0]) is SVal { Type: { } owner } &&
                             IsReference(owner) && !Open(owner))
                    {
                        int at = (int)IrBuilder.SImm(address.In[1]);
                        if (_p.Layouts.FieldAt(owner, at) is { } slot && slot.Offset == at) found = slot.Type;
                    }
                    // The whole of the place, not a part of something bigger there.
                    if (found != null && !Open(found) && (IsReference(found) ? bytes == 8 : _p.Layouts.SizeOf(found).Size == bytes))
                    {
                        type = found;
                        break;
                    }
                }
            }
        }
        return _resultPlaces[call] = type;
    }

    private void EmitManagedCall(Node call, CallTarget target, bool tail)
    {
        MethodDef? best = null;
        MethodInst? bestInst = null;
        int bestScore = int.MinValue;
        var ties = new List<MethodDef>();
        void Consider(MethodDef m, MethodInst? inst)
        {
            int score = Score(call, m, inst?.ClassArguments ?? [], inst?.MethodArguments ?? [], inst);
            if (score > bestScore)
            {
                bestScore = score;
                best = m;
                bestInst = inst;
                ties.Clear();
            }
            else if (score == bestScore && !ReferenceEquals(m, best)) ties.Add(m);
        }
        foreach (MethodDef m in target.Methods) Consider(m, null);
        foreach (MethodInst inst in target.Insts) Consider(inst.Method, inst);
        if (best == null)
        {
            Problem("managed call with no candidates");
            return;
        }
        // One function that only gives a constant, and it is the code of methods of several return types
        // ("PlayerRef.None", "TickTimer.None", ... are all "return 0"): which of them was written cannot be
        // told from the call, and guessing one gives the result a type it may not have. What it gives is
        // certain.
        if (!tail && ties.Count != 0 && ties.Any(t => !ReferenceEquals(t.ReturnType, best.ReturnType)) && ConstantFunction(best.Address) is { } given)
        {
            if (Projections(call).TryGetValue(CallResult.IntReturn, out Node? result))
                _sem[result] = new SVal(result.Type == VT.I64 ? new HConst(given, _long) : new HConst((int)given, _int));
            return;
        }
        // One function that only hands back what it is given ("mov eax, ecx; ret"), and it is the code of
        // methods that take and give different things (a layer mask from a number, a number from a layer
        // mask, an easing function from its mode, ...): which of them was written cannot be told from the
        // call, and guessing one names types that may have nothing to do with the place. What it gives is
        // certain: what it was given. Where that is a struct's own number, the struct's methods are
        // recognized by the field it ends up in.
        if (!tail && !NoIdentityCalls && ties.Count != 0 && ties.Any(t => !SameShape(t, best!)) && IdentityFunction(best.Address) is { } width &&
            IntAt(call, 0) is { } handed && Projections(call).TryGetValue(CallResult.IntReturn, out Node? back))
        {
            Sem passed = Eval(handed);
            // A number written out: what comes back is its low half.
            if (width == 32 && passed is SVal { Expr: HConst { Value: var number } })
            {
                long? plain = number switch
                {
                    int i => i, uint u => u, long l => l, ulong ul => unchecked((long)ul), short s => s, ushort us => us, byte b => b, sbyte sb => sb,
                    _ => null,
                };
                if (plain is { } low) passed = new SVal(new HConst(unchecked((int)low), _int));
            }
            // A number made wider on its way into the register: its low half is the number itself.
            else if (width == 32 && passed is SVal { Expr: HConv { Kind: HConvKind.U8 or HConvKind.I8, Operand: { } narrow } } &&
                     BitsOf(narrow.Type) is > 0 and <= 32 && !IsFloat(narrow.Type))
                passed = new SVal(narrow);
            bool whole = width == 64 || passed is SVal { Type: var held } && (held == null ? back.Type != VT.I64 : BitsOf(held) is > 0 and <= 32 || (IsStructType(held) && _p.Layouts.SizeOf(held).Item1 <= 4));
            if (whole && passed is not (SJunk or SPair or SParts or SHalf))
            {
                _sem[back] = passed;
                return;
            }
        }
        // Every method known to share this code is in an assembly this code cannot reach: what was called is
        // something else with the same code (a helper the compiler made, folded with them by the linker). What a
        // tiny body computes is certain; anything else is called as one of them, and said to be uncertain.
        if (!NoReachableAssemblies && !Reachable(best.DeclaringType.Assembly))
        {
            if (!tail && Projections(call).TryGetValue(CallResult.IntReturn, out Node? sharedResult))
            {
                if (ConstantFunction(best.Address) is { } constant)
                {
                    _sem[sharedResult] = new SVal(sharedResult.Type == VT.I64 ? new HConst(constant, _long) : new HConst((int)constant, _int));
                    return;
                }
                if (SumFunction(best.Address) is { } wide && IntAt(call, 0) is { } left && IntAt(call, 1) is { } right)
                {
                    TypeSig type = wide ? _long : _int;
                    HExpr Operand(Node n)
                    {
                        HExpr v = IntValue(n);
                        return wide || BitsOf(v.Type) is > 0 and <= 32 ? v : new HConv(HConvKind.I4, v) { Type = _int };
                    }
                    _sem[sharedResult] = new SVal(new HBinary(HBinaryOp.Add, Operand(left), Operand(right)) { Type = type });
                    return;
                }
            }
            Problem($"call to code shared only by methods this assembly cannot reach ({best.DeclaringType.Name}.{best.Name})");
        }
        BuildCall(call, best, bestInst?.ClassArguments ?? [], bestInst?.MethodArguments ?? [], isVirtual: false, tail, ties, skipFirst: false);
    }

    private readonly Dictionary<ulong, bool?> _sumFunctions = [];

    /// <summary>
    /// A function that only adds its first two arguments ("lea eax, [rcx+rdx]; ret"): true when it does so in 64
    /// bits, false in 32, null for any other function.
    /// </summary>
    private bool? SumFunction(ulong address)
    {
        if (address == 0) return null;
        if (_sumFunctions.TryGetValue(address, out bool? known)) return known;
        bool? wide = null;
        X64Cfg cfg = X64Cfg.Build(_p.Context, address);
        if (cfg.Blocks.Count == 1 && cfg.Blocks[0].Instructions.Count == 2 && cfg.Blocks[0].Instructions[1].Mnemonic == Iced.Intel.Mnemonic.Ret)
        {
            Iced.Intel.Instruction lea = cfg.Blocks[0].Instructions[0];
            if (lea.Mnemonic == Iced.Intel.Mnemonic.Lea && lea.Op0Kind == Iced.Intel.OpKind.Register && lea.Op0Register is Iced.Intel.Register.EAX or Iced.Intel.Register.RAX &&
                lea.MemoryDisplacement64 == 0 && lea.MemoryIndexScale == 1 &&
                ((lea.MemoryBase == Iced.Intel.Register.RCX && lea.MemoryIndex == Iced.Intel.Register.RDX) || (lea.MemoryBase == Iced.Intel.Register.RDX && lea.MemoryIndex == Iced.Intel.Register.RCX)))
                wide = lea.Op0Register == Iced.Intel.Register.RAX;
        }
        return _sumFunctions[address] = wide;
    }

    private static readonly bool NoIdentityCalls = Environment.GetEnvironmentVariable("REWIND_NO_IDENTITY_CALLS") != null;

    /// <summary>Whether two methods take and give the same things.</summary>
    private static bool SameShape(MethodDef a, MethodDef b)
    {
        if (a.IsStatic != b.IsStatic || !ReferenceEquals(a.ReturnType, b.ReturnType) || a.Parameters.Length != b.Parameters.Length) return false;
        if (!a.IsStatic && !ReferenceEquals(a.DeclaringType, b.DeclaringType)) return false;
        for (int i = 0; i < a.Parameters.Length; i++)
            if (!ReferenceEquals(a.Parameters[i].Type, b.Parameters[i].Type))
                return false;
        return true;
    }

    private readonly Dictionary<ulong, int> _identityFunctions = [];

    /// <summary>
    /// For a function that only hands back its first argument ("mov eax, ecx; ret"): how many bits of it
    /// (32 or 64); null for any other.
    /// </summary>
    private int? IdentityFunction(ulong address)
    {
        if (address == 0) return null;
        if (!_identityFunctions.TryGetValue(address, out int known))
        {
            known = 0;
            X64Cfg cfg = X64Cfg.Build(_p.Context, address);
            if (cfg.Blocks.Count == 1 && cfg.Blocks[0].Instructions.Count is >= 2 and <= 6 && cfg.Blocks[0].Instructions[^1].Mnemonic == Iced.Intel.Mnemonic.Ret)
            {
                // Which registers hold the first argument, and how many bits of it: only moves between
                // registers (and padding) on the way to the one results come back in.
                var holds = new Dictionary<Iced.Intel.Register, int> { [Iced.Intel.Register.RCX] = 64 };
                bool plain = true;
                for (int i = 0; i < cfg.Blocks[0].Instructions.Count - 1 && plain; i++)
                {
                    Iced.Intel.Instruction move = cfg.Blocks[0].Instructions[i];
                    if (move.Mnemonic == Iced.Intel.Mnemonic.Nop) continue;
                    // Padding the linker puts first, so the function can be patched while it runs.
                    if (move.Mnemonic == Iced.Intel.Mnemonic.Xchg && move.Op0Kind == Iced.Intel.OpKind.Register && move.Op1Kind == Iced.Intel.OpKind.Register && move.Op0Register == move.Op1Register) continue;
                    plain = false;
                    if (move.Mnemonic != Iced.Intel.Mnemonic.Mov || move.Op0Kind != Iced.Intel.OpKind.Register || move.Op1Kind != Iced.Intel.OpKind.Register) break;
                    int bits = Iced.Intel.RegisterExtensions.GetSize(move.Op0Register) * 8;
                    if (bits is not (32 or 64) || Iced.Intel.RegisterExtensions.GetSize(move.Op1Register) * 8 != bits) break;
                    Iced.Intel.Register from = Iced.Intel.RegisterExtensions.GetFullRegister(move.Op1Register), to = Iced.Intel.RegisterExtensions.GetFullRegister(move.Op0Register);
                    if (!holds.TryGetValue(from, out int had))
                    {
                        // Something else moved over a register that held it: gone from there.
                        holds.Remove(to);
                        plain = true;
                        continue;
                    }
                    holds[to] = Math.Min(had, bits);
                    plain = true;
                }
                if (plain && holds.TryGetValue(Iced.Intel.Register.RAX, out int back)) known = back;
            }
            _identityFunctions[address] = known;
        }
        return known == 0 ? null : known;
    }

    private static readonly bool ForwardersMayStore = Environment.GetEnvironmentVariable("REWIND_FORWARDERS_MAY_STORE") != null;
    private static readonly bool NoParameterSlots = Environment.GetEnvironmentVariable("REWIND_NO_PARAMETER_SLOTS") != null;
    private readonly Dictionary<ulong, bool> _writesMemory = [];

    /// <summary>Whether a (short) function writes to memory: one that does is more than a jump to another.</summary>
    private bool WritesMemory(ulong address)
    {
        if (ForwardersMayStore) return false;
        if (_writesMemory.TryGetValue(address, out bool known)) return known;
        bool writes = false;
        foreach (var block in X64Cfg.Build(_p.Context, address).Blocks)
            foreach (Iced.Intel.Instruction i in block.Instructions)
                if (i.OpCount > 0 && i.Op0Kind == Iced.Intel.OpKind.Memory &&
                    i.Mnemonic is not (Iced.Intel.Mnemonic.Cmp or Iced.Intel.Mnemonic.Test or Iced.Intel.Mnemonic.Push or Iced.Intel.Mnemonic.Jmp or Iced.Intel.Mnemonic.Call))
                    writes = true;
        return _writesMemory[address] = writes;
    }

    private static readonly bool NoInvokerShapes = Environment.GetEnvironmentVariable("REWIND_NO_INVOKER_SHAPES") != null;
    private static readonly bool NoGenericInvokerShapes = Environment.GetEnvironmentVariable("REWIND_NO_GENERIC_INVOKERS") != null;
    private static readonly bool NoRgctxCalls = Environment.GetEnvironmentVariable("REWIND_NO_RGCTX_CALLS") != null;
    private static readonly Dictionary<ulong, HelperInfo?> InvokerShapes = [];

    /// <summary>
    /// Whether a function without a name is one of those IL2CPP makes for calling a method by its slot:
    /// "Virtual...Invoker::Invoke(slot, obj, args...)" or "Interface...Invoker::Invoke(slot, interfaceClass, obj,
    /// args...)". Told by what it does: the slot arrives as a 16-bit number in the first argument, the class is
    /// read from the object (the second argument, or the third), the class's table is read - at the slot, or
    /// after the search of the interface offsets, where the only call is the runtime's slow path for that
    /// search - and what the table holds is called.
    /// </summary>
    private HelperInfo? InvokerShape(ulong address)
    {
        if (address == 0 || NoInvokerShapes) return null;
        if (InvokerShapes.TryGetValue(address, out HelperInfo? known)) return known;
        HelperInfo? found = null;
        X64Cfg cfg = X64Cfg.Build(_p.Context, address);
        int count = 0;
        foreach (var block in cfg.Blocks) count += block.Instructions.Count;
        if (cfg.Blocks.Count is >= 1 and <= 16 && count is >= 6 and <= 96)
        {
            // Which argument each register still holds, in the first stretch.
            var holds = new Dictionary<Iced.Intel.Register, Iced.Intel.Register>
            {
                [Iced.Intel.Register.RDX] = Iced.Intel.Register.RDX,
                [Iced.Intel.Register.R8] = Iced.Intel.Register.R8,
            };
            Iced.Intel.Register objectIn = Iced.Intel.Register.None, classIn = Iced.Intel.Register.None;
            bool slot = false, entry = false, offsets = false, through = false, others = false, slow = false, generic = false;
            bool first = true;
            foreach (var block in cfg.Blocks)
            {
                foreach (Iced.Intel.Instruction i in block.Instructions)
                {
                    bool load = i.Mnemonic == Iced.Intel.Mnemonic.Mov && i.Op0Kind == Iced.Intel.OpKind.Register && i.Op1Kind == Iced.Intel.OpKind.Memory;
                    if (i.Mnemonic == Iced.Intel.Mnemonic.Movzx && i.Op1Kind == Iced.Intel.OpKind.Register && i.Op1Register == Iced.Intel.Register.CX) slot = true;
                    // The class of the object: read through the register an argument came in, or a copy of it.
                    if (first && load && classIn == Iced.Intel.Register.None && i.MemoryIndex == Iced.Intel.Register.None && i.MemoryDisplacement64 == 0 &&
                        holds.TryGetValue(i.MemoryBase, out Iced.Intel.Register argument))
                    {
                        objectIn = argument;
                        classIn = i.Op0Register;
                    }
                    else if (classIn != Iced.Intel.Register.None && i.Op1Kind == Iced.Intel.OpKind.Memory && i.MemoryBase == classIn)
                    {
                        long at = (long)i.MemoryDisplacement64;
                        if (load && i.MemoryIndex != Iced.Intel.Register.None && i.MemoryIndexScale == 8 && at == _p.Klass.VTable) entry = true;
                        if (i.MemoryIndex == Iced.Intel.Register.None && (at == _p.Klass.InterfaceOffsets || at == _p.Klass.InterfaceOffsetsCount)) offsets = true;
                    }
                    if (i.Mnemonic == Iced.Intel.Mnemonic.Call || i.Mnemonic == Iced.Intel.Mnemonic.Jmp)
                    {
                        if (i.Op0Kind == Iced.Intel.OpKind.Register) through = true;
                        else if (i.Mnemonic == Iced.Intel.Mnemonic.Call && i.Op0Kind == Iced.Intel.OpKind.NearBranch64)
                        {
                            HelperKind? asked = _p.Resolve(i.NearBranchTarget).Helper?.Kind;
                            if (asked == HelperKind.InterfaceInvokeDataSlow) slow = true;
                            else if (asked == HelperKind.GetGenericVirtualMethod) generic = true;
                            else others = true;
                        }
                        else if (i.Mnemonic == Iced.Intel.Mnemonic.Call) others = true;
                    }
                    if (first && i.Op0Kind == Iced.Intel.OpKind.Register)
                    {
                        // (What is written to no longer holds the argument; a plain copy holds what its source held.)
                        Iced.Intel.Register written = Iced.Intel.RegisterExtensions.GetFullRegister(i.Op0Register);
                        Iced.Intel.Register? copied = i.Mnemonic == Iced.Intel.Mnemonic.Mov && i.Op1Kind == Iced.Intel.OpKind.Register && i.Op0Register == written &&
                                                      holds.TryGetValue(i.Op1Register, out Iced.Intel.Register from) ? from : null;
                        bool reads = i.Mnemonic is Iced.Intel.Mnemonic.Cmp or Iced.Intel.Mnemonic.Test or Iced.Intel.Mnemonic.Push;
                        if (!reads)
                        {
                            holds.Remove(written);
                            if (copied is { } same) holds[written] = same;
                        }
                    }
                }
                first = false;
            }
            // Invoke(method, obj, args...) of a generic virtual method: no slot number comes in (the method
            // has it), and the runtime is asked which version of the method the object's class has.
            if (generic && through && !others && !slot && objectIn == Iced.Intel.Register.RDX && !NoGenericInvokerShapes)
            {
                if (offsets) found = new HelperInfo(HelperKind.GenericInterfaceInvoker, 0, false, true, "GenericInterfaceInvoker (known by its code)");
                else if (entry && !slow) found = new HelperInfo(HelperKind.GenericVirtualInvoker, 0, false, true, "GenericVirtualInvoker (known by its code)");
            }
            else if (slot && through && !others && !generic)
            {
                if (objectIn == Iced.Intel.Register.RDX && entry && !offsets && !slow)
                    found = new HelperInfo(HelperKind.VirtualInvoker, 0, false, true, "VirtualInvoker (known by its code)");
                else if (objectIn == Iced.Intel.Register.R8 && offsets)
                    found = new HelperInfo(HelperKind.InterfaceInvoker, 0, false, true, "InterfaceInvoker (known by its code)");
            }
        }
        return InvokerShapes[address] = found;
    }

    private readonly Dictionary<ulong, long?> _constantFunctions = [];
    private static readonly bool NoByteConstants = Environment.GetEnvironmentVariable("REWIND_NO_BYTE_CONSTANTS") != null;

    /// <summary>What a function gives when giving a constant is all it does ("xor eax, eax; ret"); null for any other.</summary>
    private long? ConstantFunction(ulong address)
    {
        if (address == 0) return null;
        if (_constantFunctions.TryGetValue(address, out long? known)) return known;
        long? value = null;
        X64Cfg cfg = X64Cfg.Build(_p.Context, address);
        if (cfg.Blocks.Count == 1 && cfg.Blocks[0].Instructions.Count == 2 && cfg.Blocks[0].Instructions[1].Mnemonic == Iced.Intel.Mnemonic.Ret)
        {
            Iced.Intel.Instruction set = cfg.Blocks[0].Instructions[0];
            bool whole = set.Op0Kind == Iced.Intel.OpKind.Register && set.Op0Register is Iced.Intel.Register.EAX or Iced.Intel.Register.RAX;
            if (whole && set.Mnemonic == Iced.Intel.Mnemonic.Xor && set.Op1Kind == Iced.Intel.OpKind.Register && set.Op1Register == set.Op0Register) value = 0;
            else if (whole && set.Mnemonic == Iced.Intel.Mnemonic.Mov && set.Op0Register == Iced.Intel.Register.EAX && set.Op1Kind == Iced.Intel.OpKind.Immediate32)
                value = set.Immediate32;
            else if (whole && set.Mnemonic == Iced.Intel.Mnemonic.Mov && set.Op0Register == Iced.Intel.Register.RAX &&
                     set.Op1Kind is Iced.Intel.OpKind.Immediate32to64 or Iced.Intel.OpKind.Immediate64)
                value = (long)set.GetImmediate(1);
            // A yes/no or a byte: only the low byte of the register is set, and only it is looked at ("mov al, 1").
            else if (!NoByteConstants && set.Mnemonic == Iced.Intel.Mnemonic.Mov && set.Op0Kind == Iced.Intel.OpKind.Register &&
                     set.Op0Register == Iced.Intel.Register.AL && set.Op1Kind == Iced.Intel.OpKind.Immediate8)
                value = set.Immediate8;
        }
        return _constantFunctions[address] = value;
    }

    /// <summary>Builds the call expression for a chosen method from the captured argument values.</summary>
    private void BuildCall(Node call, MethodDef method, TypeSig[] classArgs, TypeSig[] methodArgs, bool isVirtual, bool tail,
        List<MethodDef>? alternatives, bool skipFirst, Node? receiverOverride = null, int shift = 0)
    {
        MethodAbi abi = _p.Abi.For(method, classArgs, methodArgs);

        // One compiled body serves every instantiation that differs only in reference types, so the callee's
        // address cannot say whether this is List<Creature>.Add or List<string>.Add. Two things can: the
        // method descriptor the shared code is handed, and the type of the receiver.
        foreach (AbiParam p in abi.Params)
        {
            if (p.Role != ParamRole.MethodInfo || IntAt(call, p.Position + shift) is not { } descriptor) continue;
            // The hidden method argument is whatever the register held unless the callee is generic: only looked at.
            if (Peek(descriptor) is SMethod { Inst: { } named } sm && ReferenceEquals(sm.Method, method) &&
                !named.ClassArguments.Any(Open) && !named.MethodArguments.Any(Open))
            {
                classArgs = named.ClassArguments;
                methodArgs = named.MethodArguments;
                abi = _p.Abi.For(method, classArgs, methodArgs);
            }
        }
        if (!method.IsStatic && method.DeclaringType.GenericParameters.Length != 0 && abi.This != null)
        {
            Node? receiverNode = receiverOverride ?? IntAt(call, abi.This.Position + shift);
            TypeSig? receiverType = receiverNode == null ? null : Eval(receiverNode) switch
            {
                SNewObject o => o.Type,
                SVal v => v.Type,
                SRef r => r.Type,
                _ => null,
            };
            if (receiverNode != null && receiverType != null && DeclaringArguments(receiverType, method.DeclaringType) == null &&
                _castTypes.TryGetValue(receiverNode, out List<TypeSig>? receiverCasts) && receiverCasts.Count == 1)
                receiverType = receiverCasts[0];
            if (DeclaringArguments(receiverType, method.DeclaringType) is { } exact)
            {
                classArgs = exact;
                abi = _p.Abi.For(method, classArgs, methodArgs);
            }
        }
        ChosenCalls[call] = (method, abi, shift);

        HExpr? thisExpr = null;
        var args = new HExpr[method.Parameters.Length];
        HExpr? returnLocation = null;

        foreach (AbiParam p in abi.Params)
        {
            int position = p.Position + shift;
            switch (p.Role)
            {
                case ParamRole.MethodInfo:
                    break;
                case ParamRole.ReturnBuffer:
                {
                    Node? node = IntAt(call, position);
                    returnLocation = node != null ? LocationOf(node, abi.ReturnType) : null;
                    if (returnLocation == null) Problem("return buffer location not recovered");
                    break;
                }
                case ParamRole.This:
                {
                    Node? node = receiverOverride ?? IntAt(call, position);
                    if (node == null) { thisExpr = Missing(p.Type!); break; }
                    if (p.Type!.Definition is { IsValueType: true })
                    {
                        thisExpr = LocationOf(node, p.Type);
                        if (thisExpr == null)
                        {
                            Problem($"struct receiver location not recovered on {method.DeclaringType.Name}.{method.Name}");
                            thisExpr = Value(node);
                        }
                    }
                    else
                    {
                        thisExpr = Value(node);
                        // A struct wrapping the object (see IsReferenceWrapper): the receiver is the object.
                        if (thisExpr.Type is { } held && IsReferenceWrapper(held)) thisExpr = Coerce(thisExpr, p.Type);
                        if (Eval(node) is SNewObject) { }
                        else if (_castTypes.TryGetValue(node, out List<TypeSig>? casts) && casts.Count == 1 && !IsAssignable(thisExpr.Type, p.Type))
                            thisExpr = new HTypeExpr(HTypeOp.CastClass, casts[0], thisExpr) { Type = casts[0] };
                    }
                    break;
                }
                case ParamRole.Argument:
                {
                    TypeSig type = p.Type!;
                    HExpr arg;
                    if (p.Pass == PassKind.Float) arg = FloatAt(call, position, p.IsDouble);
                    else
                    {
                        Node? node = IntAt(call, position);
                        if (node == null) arg = Missing(type);
                        else if (p.Pass == PassKind.Indirect)
                        {
                            arg = LocationOf(node, type) ?? Value(node);
                        }
                        else if (type is ByRefSig byRef)
                        {
                            HExpr? location = LocationOf(node, byRef.ElementType);
                            arg = location != null ? new HAddressOf(location) { Type = type } : Value(node);
                        }
                        else
                        {
                            arg = ValueFor(node, type);
                            if (IsReference(type) && _castTypes.TryGetValue(node, out List<TypeSig>? casts) && casts.Count == 1 &&
                                !IsAssignable(arg.Type, type) && IsAssignable(casts[0], type))
                                arg = new HTypeExpr(HTypeOp.CastClass, casts[0], arg) { Type = casts[0] };
                        }
                    }
                    args[p.ArgumentIndex] = arg;
                    break;
                }
            }
        }
        _ = skipFirst;

        TypeSig? declaring = classArgs.Length != 0 && method.DeclaringType.GenericParameters.Length != 0
            ? _m.Sigs.GenericInst(method.DeclaringType, classArgs)
            : null;

        // A constructor call on a freshly allocated object is "new T(args)".
        Node? receiver = receiverOverride ?? (abi.This != null ? IntAt(call, abi.This.Position + shift) : null);
        if (method.Name == ".ctor" && receiver != null && Eval(receiver) is SNewObject { Constructed: false } fresh)
        {
            fresh.Constructed = true;
            bool inlined = false;
            if (fresh.Type.Definition is { } allocated && !ReferenceEquals(allocated, method.DeclaringType))
            {
                // The object is of a derived class but a base class constructor is called on it: the class's
                // own constructor was inlined here. When that constructor does nothing except pass its
                // arguments on to this very call, "new Derived(args)" is the same thing.
                ulong target = call.Aux is CallInfo { Indirect: false } direct ? direct.Target : 0;
                MethodDef? own = null;
                foreach (MethodDef c in allocated.Methods)
                {
                    if (c.Name != ".ctor" || c.IsStatic || c.Address == 0 || c.Parameters.Length != method.Parameters.Length) continue;
                    // A forwarder: at most a register set-up (the unused method descriptor) and a jump to the target.
                    if (c.Address == target || (_p.Code.Get(c.Address) is { Instructions: <= 3, Callees.Count: 1 } code &&
                                                _p.Code.ThunkTarget(code.Callees[0]) == _p.Code.ThunkTarget(target) && !WritesMemory(c.Address)))
                    {
                        own = c;
                        break;
                    }
                }
                if (own != null)
                {
                    method = own;
                    declaring = fresh.Type is GenericInstSig ? fresh.Type : null;
                }
                // Otherwise the statements of the class's constructor were pasted here, and this call is the
                // first of them. It stays an ordinary call on the raw object; putting the constructor back is
                // done afterwards, on the finished statements (ConstructorFolding).
                else inlined = true;
            }
            if (!inlined)
            {
                if (fresh.Allocation != null)
                {
                    if (!_cur.Statements.Remove(fresh.Allocation))
                        foreach (HBlock block in _h.Blocks)
                            if (block.Statements.Remove(fresh.Allocation))
                                break;
                    fresh.Allocation = null;
                }
                var created = new HNewObject { Constructor = method, DeclaringType = declaring, Arguments = args, Type = fresh.Type };
                Emit(new HAssign(new HLocal(fresh.Variable) { Type = fresh.Type }, created), call.Addr);
                if (tail) Emit(new HReturn(null), call.Addr);
                return;
            }
        }

        // Calling a virtual method of a base class directly from an override is "base.Method()"; any other
        // direct call to a virtual method is ordinary dispatch that the compiler devirtualized.
        bool virtualCall = isVirtual;
        if (!isVirtual && method.IsVirtual && !method.DeclaringType.IsValueType)
        {
            bool onThis = thisExpr is HArg { Index: -1 };
            bool baseCall = onThis && !ReferenceEquals(method.DeclaringType, _method.DeclaringType);
            virtualCall = !baseCall;
        }

        var expr = new HCall
        {
            Method = method,
            DeclaringType = declaring,
            MethodArguments = methodArgs,
            This = thisExpr,
            Arguments = args,
            Virtual = virtualCall,
            Type = abi.ReturnType,
        };
        if (alternatives != null) expr.Alternatives.AddRange(alternatives);
        if (method.Name == ".ctor" && _method.Name == ".ctor" && thisExpr is HArg { Index: -1 }) _baseConstructorCalled = true;

        if (abi.Return == ReturnKind.Buffer)
        {
            if (returnLocation != null) Emit(new HAssign(returnLocation, expr), call.Addr);
            else Emit(new HEval(expr), call.Addr);
            // The function also returns the buffer address.
            if (Projections(call).TryGetValue(CallResult.IntReturn, out Node? address) && returnLocation != null)
                _sem[address] = new SRef(returnLocation, abi.ReturnType);
            if (tail)
            {
                if (_abi.Return == ReturnKind.Buffer && _returnBuffer != null) Emit(new HReturn(new HLocal(_returnBuffer) { Type = _returnBuffer.Type }), call.Addr);
                else Emit(new HReturn(returnLocation), call.Addr);
            }
            return;
        }
        FinishCall(call, expr, abi.Return, abi.ReturnType, tail);
    }

    // ---- indirect calls: virtual dispatch and delegates --------------------------------------------------------

    /// <summary>
    /// The method a vtable slot denotes for a receiver of the given static type: the least derived method that
    /// occupies the slot, which is the one a compiler names in a callvirt.
    /// </summary>
    private MethodDef? FindVirtual(TypeSig? type, int slot)
    {
        MethodDef? found = null;
        TypeSig? start = type == null ? null : Declared(type);
        // A value of a type parameter: what is known of it is the class its constraints name - or, failing
        // that, that it is an object.
        if (start is GenericParamSig open && !NoParameterSlots)
            start = open.Parameter.Constraints.FirstOrDefault(c => c.Definition is { IsInterface: false, IsValueType: false }) ?? _object;
        for (TypeSig? t = start; t?.Definition != null;)
        {
            TypeDef def = t.Definition;
            foreach (MethodDef m in def.Methods)
                if (m.HasSlot && m.Slot == slot && m.IsVirtual && !m.IsStatic)
                    found = m;
            if (def.BaseType == null) break;
            t = _m.Sigs.Substitute(def.BaseType, t is GenericInstSig g ? g.Arguments : [], []);
        }
        return found;
    }

    /// <summary>
    /// "ldvirtftn": a virtual slot of an object's class read as a value - what a delegate made from a virtual
    /// method ("new Action(this.OnChanged)") is constructed with.
    /// </summary>
    private HExpr? VirtualPointer(SVTable entry)
    {
        if (Value(entry.Object) is not HArg receiver) return null;
        MethodDef? method;
        TypeSig? declaring = null;
        if (entry.Interface is { } iface)
        {
            method = iface.Definition?.Methods.FirstOrDefault(m => m.HasSlot && m.Slot == entry.Slot);
            if (iface is GenericInstSig) declaring = iface;
        }
        else
        {
            TypeSig? receiverType = receiver.Type;
            if (_castTypes.TryGetValue(entry.Object, out List<TypeSig>? casts) && casts.Count == 1) receiverType = casts[0];
            method = FindVirtual(receiverType, entry.Slot);
            if (method != null && receiverType is GenericInstSig g && ReferenceEquals(g.Definition, method.DeclaringType)) declaring = g;
            else if (method != null && method.DeclaringType.GenericParameters.Length != 0) return null; // declared in a generic base: not followed
        }
        if (method == null || method.GenericParameters.Length != 0) return null;
        return new HMethodPointer { Method = method, DeclaringType = declaring, VirtualOn = receiver, Type = _nint };
    }

    private void EmitIndirectCall(Node call, bool tail)
    {
        Node targetNode = call.In[0];
        Sem target = Eval(targetNode);

        if (target is SNativeCode native)
        {
            // The implementation takes the method's own arguments (and no trailing method descriptor).
            BuildCall(call, native.Method, [], [], isVirtual: false, tail, null, skipFirst: false);
            return;
        }
        if (target is SPInvoke pinvoke)
        {
            if (TryBuildPInvokeCall(call, pinvoke.Method, tail)) return;
            Problem($"marshaled arguments of a call to {pinvoke.Method.Name} not recovered");
        }
        if (target is SVTable { MethodInfo: false, Interface: { } iface } it)
        {
            MethodDef? interfaceMethod = iface.Definition?.Methods.FirstOrDefault(m => m.HasSlot && m.Slot == it.Slot);
            if (interfaceMethod != null)
            {
                BuildCall(call, interfaceMethod, iface is GenericInstSig gi ? gi.Arguments : [], [], isVirtual: true, tail, null, skipFirst: false, receiverOverride: it.Object);
                return;
            }
            Problem($"interface slot {it.Slot} not found on {iface.DisplayName}");
        }
        else if (target is SVTable { MethodInfo: false } vt)
        {
            HExpr receiver = Value(vt.Object);
            TypeSig? receiverType = receiver.Type;
            if (_castTypes.TryGetValue(vt.Object, out List<TypeSig>? casts) && casts.Count == 1) receiverType = casts[0];
            if (receiverType != null) receiverType = Declared(receiverType);
            MethodDef? method = FindVirtual(receiverType, vt.Slot);
            if (method != null)
            {
                TypeSig[] classArgs = receiverType is GenericInstSig g && ReferenceEquals(g.Definition, method.DeclaringType) ? g.Arguments : [];
                BuildCall(call, method, classArgs, [], isVirtual: true, tail, null, skipFirst: false);
                return;
            }
            Problem($"virtual slot {vt.Slot} not found on {receiverType?.DisplayName ?? "unknown type"}");
        }
        else if ((target is SVal { Expr: HField { Field.Name: "invoke_impl", Object: not null } } ||
                  (target is SVal { Expr: HLocal held } && _fieldTemps.TryGetValue(held.Variable, out HField? loaded) && loaded is { Field.Name: "invoke_impl", Object: not null })) &&
                 ((target as SVal)!.Expr is HField direct ? direct.Object : _fieldTemps[((HLocal)((SVal)target).Expr).Variable].Object) is { } del)
        {
            // Delegate invocation: invoke_impl(method_code, args..., method). The managed call is Invoke(args).
            TypeDef? delegateType = del.Type?.Definition;
            MethodDef? invoke = delegateType?.Methods.FirstOrDefault(m => m.Name == "Invoke");
            if (invoke != null && delegateType != null)
            {
                TypeSig[] classArgs = del.Type is GenericInstSig g ? g.Arguments : [];
                BuildDelegateInvoke(call, del, invoke, classArgs, tail);
                return;
            }
            Problem("delegate type for invocation not recovered");
        }
        else Problem($"indirect call through {target.GetType().Name[1..]}");

        var args = new List<HExpr> { Value(targetNode) };
        for (int i = 0; i < 4; i++)
            if (IntAt(call, i) is { } a && Eval(a) is not SJunk)
                args.Add(Value(a));
        FinishCall(call, new HOpaque("call_indirect", args.ToArray()) { Type = _long }, ReturnKind.Integer, _long, tail);
    }

    /// <summary>
    /// A call through the function a P/Invoke declaration imports, with the arguments as the inlined wrapper
    /// marshaled them, as a call of the declaration with the managed values. Only marshaling that maps back
    /// exactly is undone: values passed as they are, bools passed as 4-byte BOOL, and strings pinned as UTF-16.
    /// </summary>
    private bool TryBuildPInvokeCall(Node call, MethodDef method, bool tail)
    {
        if (!method.IsStatic || method.GenericParameters.Length != 0) return false;
        PInvokeImport? import = _p.PInvokeOf(method);
        var arguments = new HExpr[method.Parameters.Length];
        for (int i = 0; i < arguments.Length; i++)
        {
            TypeSig type = method.Parameters[i].Type;
            if (IsFloat(type))
            {
                arguments[i] = FloatAt(call, i, BitsOf(type) == 64);
                continue;
            }
            if (IntAt(call, i) is not { } native || Unmarshal(native, type, import) is not { } value) return false;
            arguments[i] = value;
        }
        TypeSig returnType = method.ReturnType;
        ReturnKind kind;
        if (returnType.IsVoid) kind = ReturnKind.Void;
        else if (IsFloat(returnType)) kind = BitsOf(returnType) == 64 ? ReturnKind.Double : ReturnKind.Float;
        else if (IsPassedAsIs(returnType) || ReferenceEquals(returnType, _bool)) kind = ReturnKind.Integer;
        else return false;
        FinishCall(call, new HCall { Method = method, Arguments = arguments, Type = returnType }, kind, returnType, tail);
        return true;
    }

    /// <summary>Types the marshaler passes unchanged: numbers, chars, pointers, native ints, enums.</summary>
    private static bool IsPassedAsIs(TypeSig type) => type switch
    {
        PointerSig => true,
        PrimitiveSig { Element: Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 or Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 or Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4
            or Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 or Il2CppTypeEnum.I or Il2CppTypeEnum.U } => true,
        _ => type.Definition is { IsEnum: true },
    };

    /// <summary>A struct the marshaler hands over in place: all its instance fields are numbers, pointers, enums or such structs.</summary>
    private static bool IsBlittableStruct(TypeSig type, int depth = 0)
    {
        if (depth > 8 || type.Definition is not { IsValueType: true, IsEnum: false } definition || type is PrimitiveSig || type is GenericInstSig) return false;
        foreach (FieldDef field in definition.Fields)
        {
            if (field.IsStatic) continue;
            if (!IsPassedAsIs(field.Type) && !IsBlittableStruct(field.Type, depth + 1)) return false;
        }
        return true;
    }

    private HExpr? Unmarshal(Node native, TypeSig type, PInvokeImport? import)
    {
        if (IsPassedAsIs(type)) return ValueFor(native, type);
        if (type is ByRefSig byRef && (IsPassedAsIs(byRef.ElementType) || IsBlittableStruct(byRef.ElementType)))
        {
            // ref/out of something the marshaler does not convert: the location itself is passed.
            HExpr? location = LocationOf(native, byRef.ElementType);
            return location == null ? null : new HAddressOf(location) { Type = type };
        }
        if (ReferenceEquals(type, _bool))
        {
            // BOOL: the bool widened to four bytes.
            HExpr value = Value(native);
            while (value is HConv conv && !ReferenceEquals(value.Type, _bool)) value = conv.Operand;
            return ReferenceEquals(value.Type, _bool) ? value : null;
        }
        if (ReferenceEquals(type, _string) && import?.CharSet == PInvokeImport.CharSetUnicode)
        {
            // Pinned UTF-16: s == null ? null : &s._firstChar.
            if (Value(native) is HSelect { WhenTrue: var a, WhenFalse: var b })
            {
                HExpr? Chars(HExpr e) => e is HAddressOf { Target: HField { Field.Name: "_firstChar", Object: { } s } } && ReferenceEquals(s.Type, _string) ? s : null;
                bool IsNull(HExpr e) => e is HConst { Value: null or 0L or 0 };
                if (Chars(b) is { } fromB && IsNull(a)) return fromB;
                if (Chars(a) is { } fromA && IsNull(b)) return fromA;
            }
            return null;
        }
        return null;
    }

    private void BuildDelegateInvoke(Node call, HExpr del, MethodDef invoke, TypeSig[] classArgs, bool tail)
    {
        MethodAbi abi = _p.Abi.For(invoke, classArgs, []);
        ChosenCalls[call] = (invoke, abi, 0);
        var args = new HExpr[invoke.Parameters.Length];
        HExpr? returnLocation = null;
        foreach (AbiParam p in abi.Params)
        {
            switch (p.Role)
            {
                case ParamRole.ReturnBuffer:
                    returnLocation = IntAt(call, p.Position) is { } rb ? LocationOf(rb, abi.ReturnType) : null;
                    break;
                case ParamRole.Argument:
                {
                    TypeSig type = p.Type!;
                    if (p.Pass == PassKind.Float) args[p.ArgumentIndex] = FloatAt(call, p.Position, p.IsDouble);
                    else if (IntAt(call, p.Position) is not { } node) args[p.ArgumentIndex] = Missing(type);
                    else if (p.Pass == PassKind.Indirect) args[p.ArgumentIndex] = LocationOf(node, type) ?? Value(node);
                    else if (type is ByRefSig byRef && LocationOf(node, byRef.ElementType) is { } location)
                        args[p.ArgumentIndex] = new HAddressOf(location) { Type = type };
                    else args[p.ArgumentIndex] = ValueFor(node, type);
                    break;
                }
            }
        }
        var expr = new HCall
        {
            Method = invoke,
            DeclaringType = classArgs.Length != 0 ? del.Type : null,
            This = del,
            Arguments = args,
            Virtual = true,
            Type = abi.ReturnType,
        };
        if (abi.Return == ReturnKind.Buffer)
        {
            if (returnLocation != null) Emit(new HAssign(returnLocation, expr), call.Addr);
            else Emit(new HEval(expr), call.Addr);
            if (tail) Emit(new HReturn(_returnBuffer != null ? new HLocal(_returnBuffer) { Type = _returnBuffer.Type } : returnLocation), call.Addr);
            return;
        }
        FinishCall(call, expr, abi.Return, abi.ReturnType, tail);
    }

    // ---- runtime helpers ---------------------------------------------------------------------------------------

    private HExpr NewException(string typeName)
    {
        TypeDef? type = _m.FindType(typeName);
        MethodDef? ctor = type?.Methods.FirstOrDefault(m => m.Name == ".ctor" && m.Parameters.Length == 0);
        if (type == null || ctor == null) return new HOpaque("new_" + typeName.Replace('.', '_'));
        return new HNewObject { Constructor = ctor, Arguments = [], Type = type.Sig };
    }

    /// <summary>
    /// A call to the System.Math (or MathF) method that a C runtime math function stands for. Unity's class
    /// library predates MathF in older versions; there the single precision form is the double method between
    /// two conversions, which computes the same value.
    /// </summary>
    private HExpr MathCall(string name, bool isDouble, params HExpr[] args)
    {
        TypeSig type = isDouble ? _double : _float;
        MethodDef? Find(string typeName, TypeSig operand) => _m.FindType(typeName)?.Methods.FirstOrDefault(m =>
            m.IsStatic && m.Name == name && m.Parameters.Length == args.Length && ReferenceEquals(m.ReturnType, operand) &&
            m.Parameters.All(p => ReferenceEquals(p.Type, operand)));

        MethodDef? method = isDouble ? Find("System.Math", _double) : Find("System.MathF", _float) ?? Find("System.Math", _float);
        if (method != null) return new HCall { Method = method, Arguments = args, Type = type };
        if (!isDouble && Find("System.Math", _double) is { } wide)
        {
            HExpr[] widened = args.Select(a => (HExpr)new HConv(HConvKind.R8, a) { Type = _double }).ToArray();
            return new HConv(HConvKind.R4, new HCall { Method = wide, Arguments = widened, Type = _double }) { Type = _float };
        }
        Problem($"math function {name} has no managed counterpart in this build");
        return new HOpaque(name.ToLowerInvariant(), args) { Type = type };
    }

    private void EmitHelperCall(Node call, HelperInfo helper, bool tail)
    {
        Dictionary<int, Node> projs = Projections(call);
        projs.TryGetValue(CallResult.IntReturn, out Node? result);
        Node? a0 = IntAt(call, 0), a1 = IntAt(call, 1), a2 = IntAt(call, 2);

        switch (helper.Kind)
        {
            case HelperKind.MathFunction:
            {
                var operands = new HExpr[helper.FloatArgs];
                for (int i = 0; i < operands.Length; i++) operands[i] = FloatAt(call, i, helper.IsDouble);
                TypeSig type = helper.IsDouble ? _double : _float;
                // fmod is the IL "rem" instruction applied to floating point operands.
                HExpr value = helper.MathName == "fmod" && operands.Length == 2
                    ? new HBinary(HBinaryOp.Rem, operands[0], operands[1]) { Type = type }
                    : MathCall(helper.MathName, helper.IsDouble, operands);
                FinishCall(call, value, helper.IsDouble ? ReturnKind.Double : ReturnKind.Float, type, tail);
                return;
            }
            case HelperKind.Modf:
            {
                // modf(x, &whole): the whole part is x truncated toward zero, the result is what is left - and
                // for an infinity a zero of its sign, where "x - whole" would give NaN.
                TypeSig type = helper.IsDouble ? _double : _float;
                Node? pointer = IntAt(call, 1);
                HExpr? location = pointer != null ? LocationOf(pointer, type) : null;
                MethodDef? isInfinity = _m.FindType(helper.IsDouble ? "System.Double" : "System.Single")?.Methods
                    .FirstOrDefault(m => m.Name == "IsInfinity" && m.IsStatic && m.Parameters.Length == 1);
                if (location == null || isInfinity == null) break;
                HVar x = _h.NewLocal(type, "t"), whole = _h.NewLocal(type, "t");
                HExpr X() => new HLocal(x) { Type = type };
                HExpr Whole() => new HLocal(whole) { Type = type };
                Emit(new HAssign(X(), FloatAt(call, 0, helper.IsDouble)), call.Addr);
                Emit(new HAssign(Whole(), MathCall("Truncate", helper.IsDouble, [X()])), call.Addr);
                Emit(new HAssign(location, Whole()), call.Addr);
                HExpr zero = helper.IsDouble ? new HConst(0.0, type) : new HConst(0f, type);
                HExpr fraction = new HSelect(new HCall { Method = isInfinity, Arguments = [X()], Type = _bool },
                    new HBinary(HBinaryOp.Div, zero, X()) { Type = type },
                    new HBinary(HBinaryOp.Sub, X(), Whole()) { Type = type }) { Type = type };
                FinishCall(call, fraction, helper.IsDouble ? ReturnKind.Double : ReturnKind.Float, type, tail);
                return;
            }
            case HelperKind.ObjectNew:
            {
                TypeSig? type = a0 != null ? EvalKlass(a0) : null;
                if (type == null) break;
                HVar variable = _h.NewLocal(type, "o");
                if (result != null)
                {
                    // Until a constructor call claims it, the object is what the machine made: zeroed memory of
                    // that class.
                    var fresh = new SNewObject(type, variable)
                    {
                        Allocation = new HAssign(new HLocal(variable) { Type = type }, new HTypeExpr(HTypeOp.Allocate, type, null) { Type = type }),
                    };
                    Emit(fresh.Allocation, call.Addr);
                    _sem[result] = fresh;
                }
                return;
            }
            case HelperKind.SzArrayNew:
            {
                TypeSig? type = a0 != null ? EvalKlass(a0) : null;
                if (type is not SzArraySig array || a1 == null) break;
                FinishCall(call, new HNewArray(array.ElementType, IntValue(a1)) { Type = type }, ReturnKind.Integer, type, tail);
                return;
            }
            case HelperKind.Box:
            {
                TypeSig? type = a0 != null ? EvalKlass(a0) : null;
                if (type == null || a1 == null) break;
                HExpr? location = LocationOf(a1, type);
                if (location == null) break;
                FinishCall(call, new HTypeExpr(HTypeOp.Box, type, location) { Type = _object }, ReturnKind.Integer, _object, tail);
                return;
            }
            case HelperKind.Unbox:
                if (a0 == null || result == null) break;
                _sem[result] = new SUnboxed(a0);
                return;
            case HelperKind.IsInst:
            {
                TypeSig? type = a1 != null ? EvalKlass(a1) : null;
                if (type == null || a0 == null) break;
                FinishCall(call, new HTypeExpr(HTypeOp.IsInst, type, Value(a0)) { Type = type }, ReturnKind.Integer, type, tail);
                return;
            }
            case HelperKind.InterlockedCompareExchange or HelperKind.InterlockedExchange:
            {
                // The runtime's implementation works on raw pointers; the method it stands for is generic in
                // the type of the location.
                bool compare = helper.Kind == HelperKind.InterlockedCompareExchange;
                if (a0 == null || a1 == null || (compare && a2 == null)) break;
                HExpr? location = LocationOf(a0, null);
                TypeSig? type = location?.Type;
                MethodDef? method = _m.FindType("System.Threading.Interlocked")?.Methods.FirstOrDefault(m =>
                    m.Name == (compare ? "CompareExchange" : "Exchange") && m.GenericParameters.Length == 1 && m.Parameters.Length == (compare ? 3 : 2));
                if (location == null || type == null || method == null || !IsReference(type)) break;
                HExpr[] arguments = compare
                    ? [new HAddressOf(location) { Type = _m.Sigs.ByRef(type) }, ValueFor(a1, type), ValueFor(a2!, type)]
                    : [new HAddressOf(location) { Type = _m.Sigs.ByRef(type) }, ValueFor(a1, type)];
                FinishCall(call, new HCall { Method = method, MethodArguments = [type], Arguments = arguments, Type = type }, ReturnKind.Integer, type, tail);
                return;
            }
            case HelperKind.IsAssignableFrom:
            {
                // class_is_assignable_from(K, obj->klass): "obj is K" (the object is not null: its class was read).
                if (a0 == null || a1 == null || EvalKlass(a0) is not { } type || Eval(a1) is not SObjKlass { Object: var subject }) break;
                // (Of a struct type the object is a boxed one: there is one or there is none, as with any object.)
                HExpr test = new HCompare(HCompareOp.Ne, new HTypeExpr(HTypeOp.IsInst, type, Value(subject)) { Type = type }, new HConst(null, IsReference(type) ? type : _object)) { Type = _bool };
                FinishCall(call, test, ReturnKind.Integer, _bool, tail);
                return;
            }
            case HelperKind.CxxThrow:
            {
                // In a catch handler IL2CPP passes an exception on by throwing a copy of its wrapper: the first
                // argument points at a frame slot that was just given the caught exception.
                if (a0 != null && IsFrameAddress(a0, out int copyAt) && StoredBefore(call, copyAt) is { } stored &&
                    Eval(stored) is SVal { Expr: HLocal { Variable: var thrown } } &&
                    _h.TryRegions.Values.FirstOrDefault(r => ReferenceEquals(r.Exception, thrown)) is { } caughtIn &&
                    InHandlerOf(call.Block!.Scope, caughtIn.Index))
                {
                    Emit(new HThrow(null), call.Addr);
                    return;
                }
                Problem("C++ exception thrown by native code");
                Emit(new HThrow(new HOpaque("cxx_throw")), call.Addr);
                return;
            }
            case HelperKind.CastClass:
            {
                TypeSig? type = a1 != null ? EvalKlass(a1) : null;
                if (type == null || a0 == null) break;
                FinishCall(call, new HTypeExpr(HTypeOp.CastClass, type, Value(a0)) { Type = type }, ReturnKind.Integer, type, tail);
                return;
            }
            case HelperKind.GetType:
            {
                // The MethodInfo of the Type.GetType overload is passed along: it names the method exactly.
                int bools = helper.IntArgs - 3;
                Node? descriptor = IntAt(call, 1 + bools);
                if (a0 == null || descriptor == null || Eval(descriptor) is not SMethod { Method: var getType }) break;
                var arguments = new List<HExpr> { ValueFor(a0, _string) };
                for (int i = 0; i < bools; i++)
                    if (IntAt(call, 1 + i) is { } flag) arguments.Add(ValueFor(flag, _bool));
                if (getType.Parameters.Length != arguments.Count) break;
                FinishCall(call, new HCall { Method = getType, Arguments = arguments.ToArray(), Type = getType.ReturnType }, ReturnKind.Integer, getType.ReturnType, tail);
                return;
            }
            case HelperKind.Memcpy or HelperKind.Memset:
            {
                if (tail && _abi.Return != ReturnKind.Void) break;
                if (!TryEmitBlockOp(call)) break;
                if (result != null && a0 != null) _sem[result] = Eval(a0); // both return the destination
                if (tail) Emit(new HReturn(null), call.Addr);
                return;
            }
            case HelperKind.InitObj:
            {
                if (a0 == null) break;
                HExpr? location = LocationOf(a0, null);
                if (location?.Type == null) break;
                Emit(new HAssign(location, new HTypeExpr(HTypeOp.Default, location.Type, null) { Type = location.Type }), call.Addr);
                if (tail) Emit(new HReturn(null), call.Addr);
                return;
            }
            case HelperKind.FakeBoxInit:
            {
                // The box header was registered before translation (FindFakeBoxes); what remains is the copy of
                // the value into the box.
                if (a0 == null || a2 == null || !IsFrameAddress(a0, out int boxAt) || !_fakeBoxes.TryGetValue(boxAt, out TypeSig? boxed)) break;
                HExpr? source = LocationOf(a2, boxed);
                if (source == null) break;
                Emit(new HAssign(new HLocal(FrameVar(boxAt + _header, boxed)) { Type = boxed }, source), call.Addr);
                if (result != null) _sem[result] = new SFrame(boxAt);
                return;
            }
            case HelperKind.RaiseProfileException:
            {
                TypeDef? exceptionType = _m.FindType("System.NotSupportedException");
                MethodDef? ctor = exceptionType?.Methods.FirstOrDefault(m => m.Name == ".ctor" && m.Parameters.Length == 1 &&
                    ReferenceEquals(m.Parameters[0].Type, _string));
                if (exceptionType == null || ctor == null) break;
                MethodDef subject = a0 != null && Eval(a0) is SMethod { Method: var m } ? m : _method;
                _h.Notes.Add("this method throws NotSupportedException when called (IL2CPP removed its body); the message text is approximate");
                Emit(new HThrow(new HNewObject { Constructor = ctor, Arguments = [new HConst(subject.FullName, _string)], Type = exceptionType.Sig }), call.Addr);
                return;
            }
            case HelperKind.Throw:
                if (a0 == null) break;
                Emit(new HThrow(Value(a0)), call.Addr);
                return;
            case HelperKind.StoreLastError:
                return; // part of calling a declaration with SetLastError, which the call itself does
            case HelperKind.Rethrow:
                // Outside a catch clause (the code after a try/finally's handler) this throws the stored exception again.
                Emit(new HThrow(a0 != null ? ValueFor(a0, _m.FindType("System.Exception")?.Sig ?? _object) : null), call.Addr);
                return;
            case HelperKind.ThrowNullReference:
                Emit(new HThrow(NewException("System.NullReferenceException")), call.Addr);
                return;
            case HelperKind.ThrowIndexOutOfRange:
                Emit(new HThrow(NewException("System.IndexOutOfRangeException")), call.Addr);
                return;
            case HelperKind.ThrowDivideByZero:
                Emit(new HThrow(NewException("System.DivideByZeroException")), call.Addr);
                return;
            case HelperKind.ThrowInvalidCast:
                Emit(new HThrow(NewException("System.InvalidCastException")), call.Addr);
                return;
            case HelperKind.GetOverflowException:
                FinishCall(call, NewException("System.OverflowException"), ReturnKind.Integer, _object, tail);
                return;
            case HelperKind.GetArrayTypeMismatchException:
                FinishCall(call, NewException("System.ArrayTypeMismatchException"), ReturnKind.Integer, _object, tail);
                return;
            case HelperKind.GetIndexOutOfRangeException:
                FinishCall(call, NewException("System.IndexOutOfRangeException"), ReturnKind.Integer, _object, tail);
                return;
            case HelperKind.VirtualInvoker:
            {
                // Invoke(slot, obj, args...)
                if (a0 == null || !a0.IsConst || a1 == null) break;
                HExpr receiver = Value(a1);
                TypeSig? receiverType = receiver.Type;
                if (_castTypes.TryGetValue(a1, out List<TypeSig>? casts) && casts.Count == 1) receiverType = casts[0];
                MethodDef? method = FindVirtual(receiverType, (int)a0.UImm);
                if (method == null) break;
                TypeSig[] classArgs = receiverType is GenericInstSig g && ReferenceEquals(g.Definition, method.DeclaringType) ? g.Arguments : [];
                BuildCall(call, method, classArgs, [], isVirtual: true, tail, null, skipFirst: false, receiverOverride: a1, shift: 1);
                return;
            }
            case HelperKind.InterfaceInvoker:
            {
                // Invoke(slot, interfaceClass, obj, args...)
                if (a0 == null || !a0.IsConst || a1 == null || a2 == null) break;
                TypeSig? iface = EvalKlass(a1);
                int slot = (int)a0.UImm;
                MethodDef? method = iface?.Definition?.Methods.FirstOrDefault(m => m.HasSlot && m.Slot == slot);
                if (method == null) break;
                TypeSig[] classArgs = iface is GenericInstSig g ? g.Arguments : [];
                BuildCall(call, method, classArgs, [], isVirtual: true, tail, null, skipFirst: false, receiverOverride: a2, shift: 2);
                return;
            }
            case HelperKind.RgctxData:
            {
                // il2cpp_rgctx_data(rgctx, index): the entry, as a read of the table gives it.
                if (NoRgctxCalls || tail || a0 == null || a1 == null || !a1.IsConst || Eval(a0) is not SRgctx context) break;
                Sem entry = RgctxValue(context, (int)a1.UImm);
                if (entry is SJunk) break;
                if (Projections(call).TryGetValue(CallResult.IntReturn, out Node? held)) _sem[held] = entry;
                return;
            }
            case HelperKind.GenericVirtualInvoker:
            case HelperKind.GenericInterfaceInvoker:
            {
                // Invoke(method, obj, args...): which method, with which type arguments, is the value handed over.
                if (NoGenericInvokerShapes || a0 == null || a1 == null || Eval(a0) is not SMethod { Method: var generic } named) break;
                TypeSig[] ofClass = named.Inst?.ClassArguments ?? [];
                TypeSig[] ofMethod = named.Inst?.MethodArguments ?? [];
                if (generic.IsStatic || generic.GenericParameters.Length == 0 || generic.GenericParameters.Length != ofMethod.Length) break;
                BuildCall(call, generic, ofClass, ofMethod, isVirtual: true, tail, null, skipFirst: false, receiverOverride: a1, shift: 1);
                return;
            }
        }

        Problem($"runtime helper {helper.Kind} not translated");
        var args = new List<HExpr>();
        for (int i = 0; i < Math.Min(4, Math.Max(helper.IntArgs, 0)); i++)
            if (IntAt(call, i) is { } a && Eval(a) is not SJunk)
                args.Add(Value(a));
        var opaque = new HOpaque(helper.Kind.ToString(), args.ToArray()) { Type = _long };
        if (helper.NoReturn)
        {
            Emit(new HEval(opaque), call.Addr);
            Emit(new HThrow(new HOpaque("noreturn")), call.Addr);
            return;
        }
        FinishCall(call, opaque, helper.ReturnsValue ? ReturnKind.Integer : ReturnKind.Void, _long, tail);
    }
}
