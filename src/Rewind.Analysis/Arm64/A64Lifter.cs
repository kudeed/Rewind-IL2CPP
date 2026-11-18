using Rewind.Analysis.Ir;
using Rewind.Analysis.X64;
using Rewind.Binary;

namespace Rewind.Analysis.Arm64;

/// <summary>
/// Translates A64 machine code into SSA IR. Like the x64 lifter it is only about what the instructions do; the
/// IR it makes has the same shapes where the machines agree (32-bit results zero-extended into 64-bit
/// registers, 32-bit lanes for the floating-point registers, flags kept as the operands that set them).
/// </summary>
public sealed class A64Lifter : IMachineLifter
{
    /// <summary>Variables: x0-x30 are 0-30, then sp, the NZCV flags, the thread pointer and the SIMD/FP lanes (four 32-bit lanes per register).</summary>
    public const int VarSp = 31, VarFlags = 32, VarTpidr = 33, VarV = 34, VarCount = VarV + 32 * 4;

    /// <summary>The TPIDR_EL0 system register as MRS encodes it.</summary>
    private const long Tpidr = 0xDE82;

    private static readonly VT[] VarTypes = MakeVarTypes();

    private static VT[] MakeVarTypes()
    {
        var types = new VT[VarCount];
        for (int i = 0; i <= VarSp; i++) types[i] = VT.I64;
        types[VarFlags] = VT.Flags;
        types[VarTpidr] = VT.I64;
        for (int i = VarV; i < VarCount; i++) types[i] = VT.I32;
        return types;
    }

    private readonly ILiftContext _ctx;
    private readonly NativeImage _image;
    private Function _fn = null!;
    private IrBuilder _b = null!;
    private SsaBuilder _ssa = null!;
    private Block _block = null!;
    private readonly Dictionary<string, int> _unsupported = [];

    public IReadOnlyDictionary<string, int> UnsupportedCounts => _unsupported;

    public A64Lifter(ILiftContext context)
    {
        _ctx = context;
        _image = context.Image;
    }

    /// <summary>The flags a conditional compare leaves: the inner comparison's when Cond held, the immediate nzcv otherwise.</summary>
    private sealed record CondFlags(Node Cond, Node Inner, int Nzcv);

    public Function Lift(ulong start)
    {
        A64Cfg cfg = A64Cfg.Build(_ctx, start);
        _fn = new Function { Address = start, End = cfg.Limit, Regs = RegisterModel.Arm64 };
        _fn.Problems.AddRange(cfg.Problems);
        // Code reached only by unwinding (cleanups, catch clauses) is not lifted yet: such a function would
        // come out without its handlers, so it is marked.
        if (_image is ElfImage elf && elf.ExceptionTableOf(start) is { HasLandingPads: true })
            _fn.Problems.Add("exception handling not reconstructed: landing pads are not lifted for AArch64 yet");
        _b = new IrBuilder(_fn);
        _ssa = new SsaBuilder(_fn, VarTypes);
        if (cfg.Blocks.Count == 0) return _fn;

        var rawOf = new Dictionary<Block, A64Block>();
        var blockAt = new Dictionary<ulong, Block>();
        foreach (A64Block raw in cfg.Blocks)
        {
            var block = new Block { Id = _fn.Blocks.Count, Start = raw.Start, End = raw.EndAddress };
            _fn.Blocks.Add(block);
            blockAt[raw.Start] = block;
            rawOf[block] = raw;
        }
        foreach (A64Block raw in cfg.Blocks)
        {
            Block from = blockAt[raw.Start];
            foreach (ulong successor in raw.Successors)
                if (blockAt.TryGetValue(successor, out Block? to))
                {
                    from.Succs.Add(to);
                    to.Preds.Add(from);
                }
        }

        // A function whose first instruction is also a jump target needs a separate entry block.
        if (_fn.Blocks[0].Preds.Count != 0)
        {
            Block first = _fn.Blocks[0];
            var entry = new Block { Start = start, End = start };
            entry.Succs.Add(first);
            first.Preds.Insert(0, entry);
            _fn.Blocks.Insert(0, entry);
        }

        var order = new List<Block>();
        var visited = new HashSet<Block>();
        var stack = new Stack<(Block Block, int Next)>();
        visited.Add(_fn.Entry);
        stack.Push((_fn.Entry, 0));
        while (stack.Count > 0)
        {
            var (b, next) = stack.Pop();
            if (next < b.Succs.Count)
            {
                stack.Push((b, next + 1));
                if (visited.Add(b.Succs[next])) stack.Push((b.Succs[next], 0));
            }
            else order.Add(b);
        }
        order.Reverse();
        _fn.Blocks.RemoveAll(b => !visited.Contains(b));
        foreach (Block b in _fn.Blocks) b.Preds.RemoveAll(p => !visited.Contains(p));
        for (int i = 0; i < _fn.Blocks.Count; i++) _fn.Blocks[i].Id = i;

        var filled = new HashSet<Block>();
        foreach (Block block in order)
        {
            if (block.Preds.All(filled.Contains)) _ssa.Seal(block);
            _block = block;
            _b.Current = block;
            if (rawOf.TryGetValue(block, out A64Block? raw)) LiftBlock(block, raw);
            else
            {
                _b.CurrentAddr = start;
                _b.Raw(Op.Jump, VT.None);
            }
            filled.Add(block);
            foreach (Block s in block.Succs)
                if (!_ssa.IsSealed(s) && s.Preds.All(filled.Contains))
                    _ssa.Seal(s);
        }
        foreach (Block block in _fn.Blocks) _ssa.Seal(block);
        _ssa.Finish();
        return _fn;
    }

    // ---- registers ---------------------------------------------------------------------------------------------

    private Node Var(int variable) => _ssa.Read(variable, _block);
    private void SetVar(int variable, Node value) => _ssa.Write(variable, _block, value);

    private static VT IntType(bool is64) => is64 ? VT.I64 : VT.I32;
    private Node C(VT type, long value) => _b.Const(type, value);

    /// <summary>A general register as 64 bits (the zero register reads as 0).</summary>
    private Node X(byte r) => r switch
    {
        A64Instruction.Zr => C(VT.I64, 0),
        A64Instruction.Sp => Var(VarSp),
        _ => Var(r),
    };

    private Node R(byte r, bool is64) => is64 ? X(r) : _b.Trunc(X(r), VT.I32);

    /// <summary>Writes a general register; 32-bit results clear the upper half. Writes to the zero register vanish.</summary>
    private void SetR(byte r, bool is64, Node value)
    {
        if (r == A64Instruction.Zr) return;
        Node full = value.Type == VT.I64 ? value : _b.ZExt(value, VT.I64);
        SetVar(r == A64Instruction.Sp ? VarSp : r, full);
    }

    private static int LaneVar(int v, int lane) => VarV + v * 4 + lane;
    private Node Lane(int v, int lane) => Var(LaneVar(v, lane));
    private void SetLane(int v, int lane, Node value) => SetVar(LaneVar(v, lane), value);
    private Node ZeroLane() => C(VT.I32, 0);
    private Node Qword(int v, int half) => _b.Concat(Lane(v, half * 2 + 1), Lane(v, half * 2));

    private void SetQword(int v, int half, Node value)
    {
        SetLane(v, half * 2, _b.Trunc(value, VT.I32));
        SetLane(v, half * 2 + 1, _b.Trunc(_b.Shift(Op.ShrU, value, C(VT.I8, 32)), VT.I32));
    }

    /// <summary>Writes the low <paramref name="bytes"/> of a SIMD/FP register from raw bits and clears the rest, as scalar writes do.</summary>
    private void SetScalarBits(int v, Node bits, int bytes)
    {
        switch (bytes)
        {
            case 16:
                throw new InvalidOperationException("use SetLanes for 128-bit values");
            case 8:
                SetQword(v, 0, bits);
                SetLane(v, 2, ZeroLane());
                SetLane(v, 3, ZeroLane());
                return;
            default:
                SetLane(v, 0, bits.Type == VT.I32 ? bits : _b.ZExt(bits, VT.I32));
                SetLane(v, 1, ZeroLane());
                SetLane(v, 2, ZeroLane());
                SetLane(v, 3, ZeroLane());
                return;
        }
    }

    private Node ScalarBits(int v, int bytes) => bytes switch
    {
        8 => Qword(v, 0),
        4 => Lane(v, 0),
        2 => _b.Trunc(Lane(v, 0), VT.I16),
        _ => _b.Trunc(Lane(v, 0), VT.I8),
    };

    private Node Fp(int v, int size)
    {
        if (size == 2) throw new NotSupportedException("half precision");
        return _b.BitsToF(ScalarBits(v, size));
    }

    private void SetFp(int v, Node value) => SetScalarBits(v, _b.FToBits(value), value.Type == VT.F64 ? 8 : 4);

    private static VT FpType(int size) => size == 8 ? VT.F64 : VT.F32;

    // ---- operands ----------------------------------------------------------------------------------------------

    private Node ShiftBy(Node value, A64Shift shift, int amount)
    {
        if (amount == 0) return value;
        Node count = C(VT.I8, amount);
        return shift switch
        {
            A64Shift.Lsl => _b.Shift(Op.Shl, value, count),
            A64Shift.Lsr => _b.Shift(Op.ShrU, value, count),
            A64Shift.Asr => _b.Shift(Op.ShrS, value, count),
            _ => _b.Shift(Op.Ror, value, count),
        };
    }

    private Node Widen(Node value, VT to, bool signed)
    {
        if (value.Type == to) return value;
        if (value.Type.Bits() > to.Bits()) return _b.Trunc(value, to);
        return signed ? _b.SExt(value, to) : _b.ZExt(value, to);
    }

    /// <summary>Register <paramref name="r"/> extended as <paramref name="extend"/> says, to <paramref name="to"/>, then shifted left.</summary>
    private Node Extended(byte r, A64Extend extend, int amount, VT to)
    {
        Node x = X(r);
        Node value = extend switch
        {
            A64Extend.Uxtb => Widen(_b.Trunc(x, VT.I8), to, false),
            A64Extend.Uxth => Widen(_b.Trunc(x, VT.I16), to, false),
            A64Extend.Uxtw => Widen(_b.Trunc(x, VT.I32), to, false),
            A64Extend.Sxtb => Widen(_b.Trunc(x, VT.I8), to, true),
            A64Extend.Sxth => Widen(_b.Trunc(x, VT.I16), to, true),
            A64Extend.Sxtw => Widen(_b.Trunc(x, VT.I32), to, true),
            _ => Widen(x, to, false),
        };
        return amount == 0 ? value : _b.Shift(Op.Shl, value, C(VT.I8, amount));
    }

    private Node ShiftedRm(in A64Instruction i) => ShiftBy(R(i.Rm, i.Is64), i.Shift, i.Amount);

    private static long Mask(int width) => width >= 64 ? -1L : (1L << width) - 1;

    // ---- flags and conditions ----------------------------------------------------------------------------------

    private Node Flags(FlagKind kind, params Node[] inputs)
    {
        Node f = _b.Raw(Op.Flags, VT.Flags, inputs);
        f.Imm = (long)kind;
        return f;
    }

    private void SetFlags(FlagKind kind, params Node[] inputs) => SetVar(VarFlags, Flags(kind, inputs));

    private Node BoolOr(Node a, Node b) => a.IsConst ? (a.Imm != 0 ? a : b) : b.IsConst ? (b.Imm != 0 ? b : a) : _b.Raw(Op.Or, VT.I1, a, b);
    private Node BoolAnd(Node a, Node b) => a.IsConst ? (a.Imm != 0 ? b : a) : b.IsConst ? (b.Imm != 0 ? a : b) : _b.Raw(Op.And, VT.I1, a, b);
    private Node True => C(VT.I1, 1);
    private Node False => C(VT.I1, 0);

    /// <summary>The condition <paramref name="cc"/> over the flags as they are now.</summary>
    private Node Condition(int cc)
    {
        if (cc >= 14) return True;
        return ConditionOf(cc, Var(VarFlags), 0);
    }

    private Node ConditionOf(int cc, Node f, int depth)
    {
        if (cc >= 14) return True;
        if (f.Op != Op.Flags || depth > 8) return Opaque(cc, f);
        if (f.Aux is CondFlags cf)
        {
            Node inner = ConditionOf(cc, cf.Inner, depth + 1);
            bool otherwise = NzcvHolds(cc, cf.Nzcv);
            // cond ? inner : constant
            return otherwise ? BoolOr(_b.NotBool(cf.Cond), inner) : BoolAnd(cf.Cond, inner);
        }
        switch ((FlagKind)f.Imm)
        {
            case FlagKind.Sub: return SubCondition(cc, f.In[0], f.In[1]) ?? Opaque(cc, f);
            case FlagKind.Add:
            {
                Node a = f.In[0], b = f.In[1];
                // "cmn a, #k" sets the flags "cmp a, #-k" does, for every k but 0 and the most negative number.
                if (b.IsConst && b.UImm != 0 && b.UImm != (1UL << (b.Type.Bits() - 1)))
                    return SubCondition(cc, a, _b.Const(b.Type, -b.Imm)) ?? Opaque(cc, f);
                switch (cc)
                {
                    case 0: return _b.Cmp(Op.CmpEq, _b.Add(a, b), Zero(a));
                    case 1: return _b.Cmp(Op.CmpNe, _b.Add(a, b), Zero(a));
                    case 2: return _b.Raw(Op.AddOvfU, VT.I1, a, b);
                    case 3: return _b.NotBool(_b.Raw(Op.AddOvfU, VT.I1, a, b));
                    case 4: return _b.Cmp(Op.CmpLtS, _b.Add(a, b), Zero(a));
                    case 5: return _b.Cmp(Op.CmpLeS, Zero(a), _b.Add(a, b));
                    case 6: return _b.Raw(Op.AddOvfS, VT.I1, a, b);
                    case 7: return _b.NotBool(_b.Raw(Op.AddOvfS, VT.I1, a, b));
                }
                return Opaque(cc, f);
            }
            case FlagKind.Logic:
            {
                Node r = f.In[0];
                return cc switch
                {
                    0 => _b.Cmp(Op.CmpEq, r, Zero(r)),
                    1 => _b.Cmp(Op.CmpNe, r, Zero(r)),
                    2 or 6 or 8 => False,           // C = V = 0
                    3 or 7 or 9 => True,
                    4 or 11 => _b.Cmp(Op.CmpLtS, r, Zero(r)),
                    5 or 10 => _b.Cmp(Op.CmpLeS, Zero(r), r),
                    12 => _b.Cmp(Op.CmpLtS, Zero(r), r),
                    _ => _b.Cmp(Op.CmpLeS, r, Zero(r)),
                };
            }
            case FlagKind.FCompare:
            {
                Node a = f.In[0], b = f.In[1];
                Node Raw(Op op, Node x, Node y) => _b.Raw(op, VT.I1, x, y);
                // fcmp: equal 0110, less 1000, greater 0010, unordered 0011.
                return cc switch
                {
                    0 => Raw(Op.FCmpEq, a, b),
                    1 => _b.NotBool(Raw(Op.FCmpEq, a, b)),
                    2 => _b.NotBool(Raw(Op.FCmpLt, a, b)),     // hs: not less
                    3 => Raw(Op.FCmpLt, a, b),                 // lo: less
                    4 => Raw(Op.FCmpLt, a, b),                 // mi: less
                    5 => _b.NotBool(Raw(Op.FCmpLt, a, b)),
                    6 => Raw(Op.FCmpUnord, a, b),
                    7 => _b.NotBool(Raw(Op.FCmpUnord, a, b)),
                    8 => _b.NotBool(Raw(Op.FCmpLe, a, b)),     // hi: greater or unordered
                    9 => Raw(Op.FCmpLe, a, b),                 // ls: less or equal
                    10 => Raw(Op.FCmpLe, b, a),                // ge: greater or equal
                    11 => _b.NotBool(Raw(Op.FCmpLe, b, a)),    // lt: less or unordered
                    12 => Raw(Op.FCmpLt, b, a),                // gt: greater
                    _ => _b.NotBool(Raw(Op.FCmpLt, b, a)),     // le: less, equal or unordered
                };
            }
        }
        return Opaque(cc, f);
    }

    private Node Zero(Node like) => _b.Const(like.Type, 0);

    /// <summary>The condition after "cmp a, b" (subs).</summary>
    private Node? SubCondition(int cc, Node a, Node b) => cc switch
    {
        0 => _b.Cmp(Op.CmpEq, a, b),
        1 => _b.Cmp(Op.CmpNe, a, b),
        2 => _b.Cmp(Op.CmpLeU, b, a),
        3 => _b.Cmp(Op.CmpLtU, a, b),
        4 => _b.Cmp(Op.CmpLtS, _b.Sub(a, b), Zero(a)),
        5 => _b.Cmp(Op.CmpLeS, Zero(a), _b.Sub(a, b)),
        6 => _b.Raw(Op.SubOvfS, VT.I1, a, b),
        7 => _b.NotBool(_b.Raw(Op.SubOvfS, VT.I1, a, b)),
        8 => _b.Cmp(Op.CmpLtU, b, a),
        9 => _b.Cmp(Op.CmpLeU, a, b),
        10 => _b.Cmp(Op.CmpLeS, b, a),
        11 => _b.Cmp(Op.CmpLtS, a, b),
        12 => _b.Cmp(Op.CmpLtS, b, a),
        13 => _b.Cmp(Op.CmpLeS, a, b),
        _ => null,
    };

    /// <summary>Whether condition <paramref name="cc"/> holds for the flag values <paramref name="nzcv"/>.</summary>
    private static bool NzcvHolds(int cc, int nzcv)
    {
        bool n = (nzcv & 8) != 0, z = (nzcv & 4) != 0, c = (nzcv & 2) != 0, v = (nzcv & 1) != 0;
        bool r = (cc >> 1) switch
        {
            0 => z,
            1 => c,
            2 => n,
            3 => v,
            4 => c && !z,
            5 => n == v,
            6 => n == v && !z,
            _ => true,
        };
        return (cc & 1) != 0 && cc != 15 ? !r : r;
    }

    private Node Opaque(int cc, Node flags)
    {
        _fn.Problems.Add($"condition '{A64Format.Condition(cc)}' on {(flags.Op == Op.Flags ? ((FlagKind)flags.Imm).ToString() : flags.Op.ToString())} flags not modelled at 0x{_b.CurrentAddr:X}");
        Node n = _b.Raw(Op.FlagCond, VT.I1, flags);
        n.Imm = cc;
        return n;
    }

    // ---- memory ------------------------------------------------------------------------------------------------

    /// <summary>The address an access uses, and the base register's new value when it writes back.</summary>
    private (Node Address, Node? WriteBack) AddressOf(in A64Instruction i)
    {
        Node baseValue = X(i.Rn);
        switch (i.Mode)
        {
            case A64Mode.RegOffset:
                return (_b.Add(baseValue, Extended(i.Rm, i.Extend, i.Amount, VT.I64)), null);
            case A64Mode.PreIndex:
            {
                Node at = _b.Add(baseValue, C(VT.I64, i.Imm));
                return (at, at);
            }
            case A64Mode.PostIndex:
                return (baseValue, _b.Add(baseValue, C(VT.I64, i.Imm)));
            default:
                return (_b.Add(baseValue, C(VT.I64, i.Imm)), null);
        }
    }

    private void WriteBack(in A64Instruction i, Node? value)
    {
        if (value != null) SetR(i.Rn, true, value);
    }

    /// <summary>Loads from memory, folding reads of read-only image data into constants.</summary>
    private Node LoadAt(Node address, VT type)
    {
        if (address.IsConst)
        {
            ulong va = (ulong)address.Imm;
            ImageSection? section = _image.SectionAt(va);
            // (The GOT, through which position-independent code reaches the metadata, is constant once relocated.)
            bool constant = section != null && !section.IsExecutable && (!section.IsWritable || (type == VT.I64 && _image.IsReadOnlyAfterLoad(va)));
            if (constant && _image.IsMapped(va, type.Bytes()))
            {
                long raw = type.Bytes() switch
                {
                    1 => _image.U8(va),
                    2 => _image.U16(va),
                    4 => _image.U32(va),
                    _ => (long)_image.U64(va),
                };
                return _b.Const(type, raw);
            }
        }
        return _b.Load(address, type);
    }

    private Node At(Node address, int offset) => offset == 0 ? address : _b.Add(address, C(VT.I64, offset));

    /// <summary>Loads one register's worth (general or SIMD/FP) from <paramref name="address"/> into register <paramref name="rt"/>.</summary>
    private void LoadInto(in A64Instruction i, byte rt, Node address)
    {
        if (i.Vector)
        {
            switch (i.Size)
            {
                case 16:
                    SetQword(rt, 0, LoadAt(address, VT.I64));
                    SetQword(rt, 1, LoadAt(At(address, 8), VT.I64));
                    return;
                case 8:
                    SetScalarBits(rt, LoadAt(address, VT.I64), 8);
                    return;
                default:
                    SetScalarBits(rt, LoadAt(address, VTExtensions.IntOfBytes(i.Size)), 4);
                    return;
            }
        }
        Node value = LoadAt(address, VTExtensions.IntOfBytes(i.Size));
        if (i.Signed) value = _b.SExt(value, i.Is64 ? VT.I64 : VT.I32);
        SetR(rt, i.Is64, value);
    }

    private void StoreFrom(in A64Instruction i, byte rt, Node address)
    {
        if (i.Vector)
        {
            switch (i.Size)
            {
                case 16:
                    _b.Store(address, Qword(rt, 0));
                    _b.Store(At(address, 8), Qword(rt, 1));
                    return;
                default:
                    _b.Store(address, ScalarBits(rt, i.Size));
                    return;
            }
        }
        Node value = X(rt);
        if (i.Size != 8) value = _b.Trunc(value, VTExtensions.IntOfBytes(i.Size));
        _b.Store(address, value);
    }

    // ---- calls -------------------------------------------------------------------------------------------------

    private const int SpeculativeStackSlots = 4;

    private Node[] CaptureArguments(CallInfo info, CallShape? shape, Node? indirectTarget)
    {
        var inputs = new List<Node>();
        if (indirectTarget != null)
        {
            inputs.Add(indirectTarget);
            info.Slots.Add(new ArgSlot(ArgSlotKind.Target, 0));
        }
        Node sp = Var(VarSp);
        void Add(ArgSlot slot)
        {
            switch (slot.Kind)
            {
                case ArgSlotKind.IntReg: inputs.Add(X((byte)slot.Index)); break;
                case ArgSlotKind.FloatReg: inputs.Add(Lane(slot.Index / 4, slot.Index % 4)); break;
                case ArgSlotKind.Stack: inputs.Add(_b.Load(At(sp, 8 * slot.Index), VT.I64)); break;
                default: return;
            }
            info.Slots.Add(slot);
        }
        if (shape?.Slots is { } exact)
        {
            foreach (ArgSlot slot in exact) Add(slot);
            return inputs.ToArray();
        }
        // Not known: everything an argument may be in (x8 too: a struct returned through memory).
        for (int r = 0; r <= 8; r++) Add(new ArgSlot(ArgSlotKind.IntReg, r));
        for (int v = 0; v < 8; v++)
        {
            Add(new ArgSlot(ArgSlotKind.FloatReg, v * 4));
            Add(new ArgSlot(ArgSlotKind.FloatReg, v * 4 + 1));
        }
        for (int s = 0; s < SpeculativeStackSlots; s++) Add(new ArgSlot(ArgSlotKind.Stack, s));
        return inputs.ToArray();
    }

    private void AfterCall(Node call, CallShape? shape, CallReturn returns)
    {
        Node Proj(int which, VT type)
        {
            Node p = _b.Raw(Op.Proj, type, call);
            p.Imm = which;
            return p;
        }
        bool any = returns == CallReturn.Unknown;
        int ints = shape?.IntResults ?? 1, floats = shape?.FloatResults ?? 1;
        SetVar(0, any || returns == CallReturn.Integer ? Proj(CallResult.IntReturn, VT.I64) : _b.Undef(VT.I64));
        SetVar(1, ints >= 2 && returns == CallReturn.Integer ? Proj(CallResult.IntReturn2, VT.I64) : _b.Undef(VT.I64));
        for (int r = 2; r <= 18; r++) SetVar(r, _b.Undef(VT.I64));
        SetVar(30, _b.Undef(VT.I64));
        bool floating = any || returns is CallReturn.Float or CallReturn.Double;
        bool wide = any || returns == CallReturn.Double;
        int[] lane0 = [CallResult.FloatLane0, CallResult.Float1Lane0, CallResult.Float2Lane0, CallResult.Float3Lane0];
        int[] lane1 = [CallResult.FloatLane1, CallResult.Float1Lane1, CallResult.Float2Lane1, CallResult.Float3Lane1];
        for (int v = 0; v < 32; v++)
        {
            bool result = floating && v < floats;
            bool preserved = v is >= 8 and < 16;
            if (!preserved || result)
            {
                SetLane(v, 0, result ? Proj(lane0[v], VT.I32) : _b.Undef(VT.I32));
                SetLane(v, 1, result && wide ? Proj(lane1[v], VT.I32) : _b.Undef(VT.I32));
            }
            // Only the bottom 64 bits of v8-v15 survive a call.
            SetLane(v, 2, _b.Undef(VT.I32));
            SetLane(v, 3, _b.Undef(VT.I32));
        }
        SetVar(VarFlags, _b.Undef(VT.Flags));
    }

    private void EmitCall(in A64Instruction i, bool tail, bool noReturn)
    {
        var info = new CallInfo { NoReturn = noReturn };
        Node? indirect = null;
        CallShape? shape = null;
        CallReturn returns = CallReturn.Unknown;
        if (i.Op is A64Op.Bl or A64Op.B)
        {
            info.Target = i.Target;
            shape = _ctx.ShapeOf(info.Target);
            returns = shape?.Returns ?? _ctx.ReturnOf(info.Target);
        }
        else
        {
            info.Indirect = true;
            indirect = X(i.Rn);
        }
        Node[] inputs = CaptureArguments(info, shape, indirect);
        Node call = _b.Raw(tail ? Op.TailCall : Op.Call, VT.None, inputs);
        call.Aux = info;
        if (!tail) AfterCall(call, shape, returns);
    }

    private Node Intrinsic(string name, VT type, params Node[] inputs)
    {
        Node call = _b.Raw(Op.Call, type, inputs);
        call.Aux = new CallInfo { Intrinsic = name };
        return call;
    }

    // ---- blocks ------------------------------------------------------------------------------------------------

    private void LiftBlock(Block block, A64Block raw)
    {
        int count = raw.Instructions.Count;
        for (int k = 0; k < count; k++)
        {
            A64Instruction ins = raw.Instructions[k];
            _b.CurrentAddr = ins.Address;
            bool last = k == count - 1;
            try
            {
                if (last && LiftTerminator(ins, raw, block)) return;
                LiftInstruction(ins);
            }
            catch (NotSupportedException e)
            {
                _fn.Problems.Add($"0x{ins.Address:X} {ins.Op}: {e.Message}");
            }
        }
        if (block.Terminator == null)
        {
            if (raw.End == BlockEnd.FallThrough && block.Succs.Count == 1) _b.Raw(Op.Jump, VT.None);
            else _b.Raw(Op.Unreachable, VT.None);
        }
    }

    private Node[] ReturnValues() =>
    [
        Var(0), Lane(0, 0), Lane(0, 1),
        Var(1), Lane(1, 0), Lane(1, 1), Lane(2, 0), Lane(2, 1), Lane(3, 0), Lane(3, 1),
    ];

    private bool LiftTerminator(in A64Instruction ins, A64Block raw, Block block)
    {
        switch (raw.End)
        {
            case BlockEnd.Jump:
                _b.Raw(Op.Jump, VT.None);
                return true;
            case BlockEnd.Branch:
            {
                Node cond = ins.Op switch
                {
                    A64Op.BCond => Condition(ins.Cond),
                    A64Op.Cbz => _b.Cmp(Op.CmpEq, R(ins.Rd, ins.Is64), C(IntType(ins.Is64), 0)),
                    A64Op.Cbnz => _b.Cmp(Op.CmpNe, R(ins.Rd, ins.Is64), C(IntType(ins.Is64), 0)),
                    _ => BitTest(ins),
                };
                if (block.Succs.Count != 2)
                {
                    // A conditional jump to another function (or a target not decoded): only one way is known.
                    _fn.Problems.Add($"conditional branch with one known target at 0x{ins.Address:X}");
                    _b.Raw(block.Succs.Count == 1 ? Op.Jump : Op.Unreachable, VT.None);
                    return true;
                }
                _b.Raw(Op.Branch, VT.None, cond);
                return true;
            }
            case BlockEnd.Switch:
            {
                Node? index = SwitchIndex(raw);
                if (index == null)
                {
                    _fn.Problems.Add($"jump table index not recovered at 0x{ins.Address:X}");
                    index = _b.Undef(VT.I64);
                }
                Node sw = _b.Raw(Op.Switch, VT.None, index);
                sw.Aux = new List<Block>(block.Succs);
                return true;
            }
            case BlockEnd.Return:
                _b.Raw(Op.Return, VT.None, ReturnValues());
                return true;
            case BlockEnd.TailCall:
            case BlockEnd.IndirectTailCall:
                EmitCall(ins, tail: true, noReturn: false);
                return true;
            case BlockEnd.NoReturnCall:
                EmitCall(ins, tail: false, noReturn: true);
                _b.Raw(Op.Unreachable, VT.None);
                return true;
            case BlockEnd.Trap:
                if (ins.Op is not (A64Op.Brk or A64Op.Udf or A64Op.Hlt) && !ins.IsInvalid) LiftInstruction(ins);
                _b.Raw(Op.Unreachable, VT.None);
                return true;
            default:
                return false;
        }
    }

    /// <summary>tbz/tbnz: a test of one bit; the sign bit is a comparison with zero.</summary>
    private Node BitTest(in A64Instruction ins)
    {
        int bit = (int)ins.Imm;
        bool is64 = bit >= 32;
        Node value = R(ins.Rd, is64);
        bool set = ins.Op == A64Op.Tbnz;
        if (bit == (is64 ? 63 : 31))
            return set ? _b.Cmp(Op.CmpLtS, value, Zero(value)) : _b.Cmp(Op.CmpLeS, Zero(value), value);
        Node masked = _b.And(value, C(value.Type, 1L << bit));
        return _b.Cmp(set ? Op.CmpNe : Op.CmpEq, masked, Zero(masked));
    }

    /// <summary>The index of a jump table dispatch: the register the table load was indexed by, as it is at the jump.</summary>
    private Node? SwitchIndex(A64Block raw)
    {
        // Find the table load again: the last register-offset load in the block (the CFG checked the shape).
        for (int k = raw.Instructions.Count - 2; k >= 0; k--)
        {
            A64Instruction load = raw.Instructions[k];
            if (load.Op != A64Op.Ldr || load.Mode != A64Mode.RegOffset || load.Vector) continue;
            for (int j = k + 1; j < raw.Instructions.Count - 1; j++)
                if (A64Cfg.Writes(raw.Instructions[j], load.Rm)) return null;
            return Extended(load.Rm, load.Extend, 0, VT.I64);
        }
        return null;
    }

    // ---- instructions ------------------------------------------------------------------------------------------

    private void Unknown(in A64Instruction i, string? what = null)
    {
        string key = what ?? i.Op.ToString();
        _unsupported[key] = _unsupported.GetValueOrDefault(key) + 1;
        throw new NotSupportedException($"instruction not modelled (0x{i.Word:X8})");
    }

    private void LiftInstruction(in A64Instruction i)
    {
        VT t = IntType(i.Is64);
        int bits = i.Is64 ? 64 : 32;
        switch (i.Op)
        {
            case A64Op.Nop or A64Op.Prfm or A64Op.Clrex:
                return;

            case A64Op.Barrier:
                Intrinsic("memory_barrier", VT.None);
                return;

            // ---- immediate data processing
            case A64Op.Adr or A64Op.Adrp:
                SetR(i.Rd, true, C(VT.I64, (long)i.Target));
                return;
            case A64Op.AddImm or A64Op.SubImm:
            {
                Node a = R(i.Rn, i.Is64), b = C(t, i.Imm);
                Node r = i.Op == A64Op.AddImm ? _b.Add(a, b) : _b.Sub(a, b);
                if (i.SetFlags) SetFlags(i.Op == A64Op.AddImm ? FlagKind.Add : FlagKind.Sub, a, b);
                SetR(i.Rd, i.Is64, r);
                return;
            }
            case A64Op.AndImm or A64Op.OrrImm or A64Op.EorImm:
            {
                Node a = R(i.Rn, i.Is64), b = C(t, i.Imm);
                Node r = i.Op switch { A64Op.AndImm => _b.And(a, b), A64Op.OrrImm => _b.Or(a, b), _ => _b.Xor(a, b) };
                if (i.SetFlags) SetFlags(FlagKind.Logic, r);
                SetR(i.Rd, i.Is64, r);
                return;
            }
            case A64Op.MovZ:
                SetR(i.Rd, i.Is64, C(t, i.Imm << i.Amount));
                return;
            case A64Op.MovN:
                SetR(i.Rd, i.Is64, C(t, ~(i.Imm << i.Amount)));
                return;
            case A64Op.MovK:
            {
                Node old = R(i.Rd, i.Is64);
                Node kept = _b.And(old, C(t, ~(0xFFFFL << i.Amount)));
                SetR(i.Rd, i.Is64, _b.Or(kept, C(t, i.Imm << i.Amount)));
                return;
            }
            case A64Op.Ubfm or A64Op.Sbfm or A64Op.Bfm:
                SetR(i.Rd, i.Is64, Bitfield(i, t, bits));
                return;
            case A64Op.Extr:
            {
                int lsb = (int)i.Imm;
                Node hi = R(i.Rn, i.Is64), lo = R(i.Rm, i.Is64);
                Node r = lsb == 0 ? lo
                    : i.Rn == i.Rm ? _b.Shift(Op.Ror, lo, C(VT.I8, lsb))
                    : _b.Or(_b.Shift(Op.ShrU, lo, C(VT.I8, lsb)), _b.Shift(Op.Shl, hi, C(VT.I8, bits - lsb)));
                SetR(i.Rd, i.Is64, r);
                return;
            }

            // ---- register data processing
            case A64Op.AddReg or A64Op.SubReg or A64Op.AddExt or A64Op.SubExt:
            {
                Node a = R(i.Rn, i.Is64);
                Node b = i.Op is A64Op.AddReg or A64Op.SubReg ? ShiftedRm(i) : Extended(i.Rm, i.Extend, i.Amount, t);
                bool add = i.Op is A64Op.AddReg or A64Op.AddExt;
                Node r = add ? _b.Add(a, b) : i.Rn == A64Instruction.Zr ? _b.Neg(b) : _b.Sub(a, b);
                if (i.SetFlags) SetFlags(add ? FlagKind.Add : FlagKind.Sub, a, b);
                SetR(i.Rd, i.Is64, r);
                return;
            }
            case A64Op.And or A64Op.Bic or A64Op.Orr or A64Op.Orn or A64Op.Eor or A64Op.Eon:
            {
                Node a = R(i.Rn, i.Is64), b = ShiftedRm(i);
                if (i.Op is A64Op.Bic or A64Op.Orn or A64Op.Eon) b = _b.Not(b);
                Node r = i.Op switch
                {
                    A64Op.And or A64Op.Bic => _b.And(a, b),
                    A64Op.Orr or A64Op.Orn => _b.Or(a, b),
                    _ => _b.Xor(a, b),
                };
                if (i.SetFlags) SetFlags(FlagKind.Logic, r);
                SetR(i.Rd, i.Is64, r);
                return;
            }
            case A64Op.Adc or A64Op.Sbc:
            {
                if (i.SetFlags) Unknown(i, i.Op + "s");
                Node a = R(i.Rn, i.Is64), b = R(i.Rm, i.Is64);
                Node carry = _b.ZExt(Condition(2), t);
                Node r = i.Op == A64Op.Adc
                    ? _b.Add(_b.Add(a, b), carry)
                    : _b.Sub(_b.Sub(a, b), _b.Sub(C(t, 1), carry));
                SetR(i.Rd, i.Is64, r);
                return;
            }
            case A64Op.CcmpReg or A64Op.CcmpImm or A64Op.CcmnReg or A64Op.CcmnImm:
            {
                Node a = R(i.Rn, i.Is64);
                Node b = i.Op is A64Op.CcmpImm or A64Op.CcmnImm ? C(t, i.Imm2) : R(i.Rm, i.Is64);
                Node cond = Condition(i.Cond);
                Node inner = Flags(i.Op is A64Op.CcmpReg or A64Op.CcmpImm ? FlagKind.Sub : FlagKind.Add, a, b);
                Node f = Flags(FlagKind.Other, cond, inner);
                f.Aux = new CondFlags(cond, inner, (int)i.Imm);
                SetVar(VarFlags, f);
                return;
            }
            case A64Op.Csel or A64Op.Csinc or A64Op.Csinv or A64Op.Csneg:
            {
                Node cond = Condition(i.Cond);
                Node r;
                if (i.Rn == A64Instruction.Zr && i.Rm == A64Instruction.Zr && i.Op is A64Op.Csinc or A64Op.Csinv)
                {
                    // cset / csetm: 1 (or all ones) when the inverted condition holds.
                    Node holds = _b.NotBool(cond);
                    r = i.Op == A64Op.Csinc ? _b.ZExt(holds, t) : _b.SExt(holds, t);
                }
                else
                {
                    Node a = R(i.Rn, i.Is64), b = R(i.Rm, i.Is64);
                    Node other = i.Op switch
                    {
                        A64Op.Csinc => _b.Add(b, C(t, 1)),
                        A64Op.Csinv => _b.Not(b),
                        A64Op.Csneg => _b.Neg(b),
                        _ => b,
                    };
                    r = _b.Select(cond, a, other);
                }
                SetR(i.Rd, i.Is64, r);
                return;
            }
            case A64Op.Udiv or A64Op.Sdiv:
                SetR(i.Rd, i.Is64, _b.Raw(i.Op == A64Op.Udiv ? Op.DivU : Op.DivS, t, R(i.Rn, i.Is64), R(i.Rm, i.Is64)));
                return;
            case A64Op.Lslv or A64Op.Lsrv or A64Op.Asrv or A64Op.Rorv:
            {
                Op op = i.Op switch { A64Op.Lslv => Op.Shl, A64Op.Lsrv => Op.ShrU, A64Op.Asrv => Op.ShrS, _ => Op.Ror };
                Node count = _b.And(_b.Trunc(X(i.Rm), VT.I8), C(VT.I8, bits - 1));
                SetR(i.Rd, i.Is64, _b.Shift(op, R(i.Rn, i.Is64), count));
                return;
            }
            case A64Op.Rev:
                SetR(i.Rd, i.Is64, _b.Raw(Op.Bswap, t, R(i.Rn, i.Is64)));
                return;
            case A64Op.Clz:
                SetR(i.Rd, i.Is64, _b.Raw(Op.Lzcnt, t, R(i.Rn, i.Is64)));
                return;
            case A64Op.Madd or A64Op.Msub:
            {
                Node product = _b.Mul(R(i.Rn, i.Is64), R(i.Rm, i.Is64));
                Node r = i.Op == A64Op.Madd
                    ? (i.Ra == A64Instruction.Zr ? product : _b.Add(R(i.Ra, i.Is64), product))
                    : (i.Ra == A64Instruction.Zr ? _b.Neg(product) : _b.Sub(R(i.Ra, i.Is64), product));
                SetR(i.Rd, i.Is64, r);
                return;
            }
            case A64Op.Smaddl or A64Op.Smsubl or A64Op.Umaddl or A64Op.Umsubl:
            {
                bool signed = i.Op is A64Op.Smaddl or A64Op.Smsubl;
                Node a = Widen(R(i.Rn, false), VT.I64, signed), b = Widen(R(i.Rm, false), VT.I64, signed);
                Node product = _b.Mul(a, b);
                bool add = i.Op is A64Op.Smaddl or A64Op.Umaddl;
                Node r = i.Ra == A64Instruction.Zr ? (add ? product : _b.Neg(product)) : add ? _b.Add(X(i.Ra), product) : _b.Sub(X(i.Ra), product);
                SetR(i.Rd, true, r);
                return;
            }
            case A64Op.Smulh or A64Op.Umulh:
                SetR(i.Rd, true, _b.Raw(i.Op == A64Op.Smulh ? Op.MulHiS : Op.MulHiU, VT.I64, X(i.Rn), X(i.Rm)));
                return;

            // ---- memory
            case A64Op.Ldr:
            {
                var (address, back) = AddressOf(i);
                LoadInto(i, i.Rd, address);
                WriteBack(i, back);
                return;
            }
            case A64Op.Str:
            {
                var (address, back) = AddressOf(i);
                StoreFrom(i, i.Rd, address);
                WriteBack(i, back);
                return;
            }
            case A64Op.Ldp:
            {
                var (address, back) = AddressOf(i);
                LoadInto(i, i.Rd, address);
                LoadInto(i, i.Ra, At(address, i.Size));
                WriteBack(i, back);
                return;
            }
            case A64Op.Stp:
            {
                var (address, back) = AddressOf(i);
                // Both values are read before either store (stp x0, x1, [x0] stores the old x0).
                StoreFrom(i, i.Rd, address);
                StoreFrom(i, i.Ra, At(address, i.Size));
                WriteBack(i, back);
                return;
            }
            case A64Op.LdrLit:
                LoadInto(i, i.Rd, C(VT.I64, (long)i.Target));
                return;
            case A64Op.Ldar:
            {
                Node value = _b.Load(X(i.Rn), VTExtensions.IntOfBytes(i.Size));
                Intrinsic("memory_barrier", VT.None);
                SetR(i.Rd, i.Is64, value);
                return;
            }
            case A64Op.Stlr:
            {
                Intrinsic("memory_barrier", VT.None);
                Node value = X(i.Rd);
                if (i.Size != 8) value = _b.Trunc(value, VTExtensions.IntOfBytes(i.Size));
                _b.Store(X(i.Rn), value);
                return;
            }
            case A64Op.Ldxr or A64Op.Ldaxr:
                SetR(i.Rd, i.Is64, Widen(Intrinsic("load_exclusive", VTExtensions.IntOfBytes(i.Size), X(i.Rn)), IntType(i.Is64), false));
                return;
            case A64Op.Stxr or A64Op.Stlxr:
            {
                Node value = X(i.Rd);
                if (i.Size != 8) value = _b.Trunc(value, VTExtensions.IntOfBytes(i.Size));
                SetR(i.Ra, false, Intrinsic("store_exclusive", VT.I32, X(i.Rn), value));
                return;
            }
            case A64Op.Swp or A64Op.LdAdd:
            {
                VT type = VTExtensions.IntOfBytes(i.Size);
                Node operand = i.Size == 8 ? X(i.Ra) : _b.Trunc(X(i.Ra), type);
                Node old = Intrinsic(i.Op == A64Op.Swp ? "atomic_exchange" : "atomic_fetch_add", type, X(i.Rn), operand);
                SetR(i.Rd, i.Is64, Widen(old, IntType(i.Is64), false));
                return;
            }
            case A64Op.Cas:
            {
                VT type = VTExtensions.IntOfBytes(i.Size);
                Node expected = i.Size == 8 ? X(i.Ra) : _b.Trunc(X(i.Ra), type);
                Node desired = i.Size == 8 ? X(i.Rd) : _b.Trunc(X(i.Rd), type);
                Node old = Intrinsic("atomic_compare_exchange", type, X(i.Rn), expected, desired);
                SetR(i.Ra, i.Is64, Widen(old, IntType(i.Is64), false));
                return;
            }

            // ---- calls inside a block
            case A64Op.Bl or A64Op.Blr:
                EmitCall(i, tail: false, noReturn: false);
                return;

            // ---- system
            case A64Op.Mrs when i.Imm == Tpidr:
                SetR(i.Rd, true, Var(VarTpidr));
                return;

            // ---- scalar floating point
            case A64Op.FMov:
                SetScalarBits(i.Rd, ScalarBits(i.Rn, i.FpSize), i.FpSize == 8 ? 8 : 4);
                return;
            case A64Op.FMovImm:
            {
                if (i.FpSize == 2) Unknown(i, "FMovImm (half)");
                ulong value = A64Decoder.FpImmediate((int)i.Imm, i.FpSize);
                SetScalarBits(i.Rd, C(i.FpSize == 8 ? VT.I64 : VT.I32, (long)value), i.FpSize);
                return;
            }
            case A64Op.FMovToGp:
                if (i.FpSize == 2) Unknown(i, "FMovToGp (half)");
                SetR(i.Rd, i.Is64, i.Is64 ? Qword(i.Rn, 0) : Lane(i.Rn, 0));
                return;
            case A64Op.FMovFromGp:
                if (i.FpSize == 2) Unknown(i, "FMovFromGp (half)");
                SetScalarBits(i.Rd, i.Is64 ? X(i.Rn) : R(i.Rn, false), i.Is64 ? 8 : 4);
                return;
            case A64Op.FMovToGpHigh:
                SetR(i.Rd, true, Qword(i.Rn, 1));
                return;
            case A64Op.FMovFromGpHigh:
                SetQword(i.Rd, 1, X(i.Rn));
                return;
            case A64Op.FAbs or A64Op.FNeg or A64Op.FSqrt:
            {
                Op op = i.Op switch { A64Op.FAbs => Op.FAbs, A64Op.FNeg => Op.FNeg, _ => Op.FSqrt };
                Node a = Fp(i.Rn, i.FpSize);
                SetFp(i.Rd, _b.Raw(op, a.Type, a));
                return;
            }
            case A64Op.FCvt:
            {
                if (i.FpSize == 2 || i.Imm == 2) Unknown(i, "FCvt (half)");
                Node a = Fp(i.Rn, i.FpSize);
                SetFp(i.Rd, i.Imm == 8 ? _b.Raw(Op.FExt, VT.F64, a) : _b.Raw(Op.FTrunc, VT.F32, a));
                return;
            }
            case A64Op.FAdd or A64Op.FSub or A64Op.FMul or A64Op.FDiv or A64Op.FMax or A64Op.FMin or A64Op.FMaxNm or A64Op.FMinNm or A64Op.FNMul:
            {
                Node a = Fp(i.Rn, i.FpSize), b = Fp(i.Rm, i.FpSize);
                Op op = i.Op switch
                {
                    A64Op.FAdd => Op.FAdd, A64Op.FSub => Op.FSub, A64Op.FMul or A64Op.FNMul => Op.FMul, A64Op.FDiv => Op.FDiv,
                    A64Op.FMax or A64Op.FMaxNm => Op.FMax, _ => Op.FMin,
                };
                Node r = _b.Raw(op, a.Type, a, b);
                if (i.Op == A64Op.FNMul) r = _b.Raw(Op.FNeg, r.Type, r);
                SetFp(i.Rd, r);
                return;
            }
            case A64Op.FMAdd or A64Op.FMSub or A64Op.FNMAdd or A64Op.FNMSub:
            {
                // Fused in the machine; the source wrote a product and a sum.
                Node a = Fp(i.Ra, i.FpSize), n = Fp(i.Rn, i.FpSize), m = Fp(i.Rm, i.FpSize);
                Node product = _b.Raw(Op.FMul, n.Type, n, m);
                Node r = i.Op switch
                {
                    A64Op.FMAdd => _b.Raw(Op.FAdd, n.Type, a, product),
                    A64Op.FMSub => _b.Raw(Op.FSub, n.Type, a, product),
                    A64Op.FNMAdd => _b.Raw(Op.FSub, n.Type, _b.Raw(Op.FNeg, n.Type, a), product),
                    _ => _b.Raw(Op.FSub, n.Type, product, a),
                };
                SetFp(i.Rd, r);
                return;
            }
            case A64Op.FCmp or A64Op.FCmpe:
            {
                Node a = Fp(i.Rn, i.FpSize);
                Node b = i.Imm == 1 ? FZero(a.Type) : Fp(i.Rm, i.FpSize);
                SetFlags(FlagKind.FCompare, a, b);
                return;
            }
            case A64Op.FCcmp or A64Op.FCcmpe:
            {
                Node a = Fp(i.Rn, i.FpSize), b = Fp(i.Rm, i.FpSize);
                Node cond = Condition(i.Cond);
                Node inner = Flags(FlagKind.FCompare, a, b);
                Node f = Flags(FlagKind.Other, cond, inner);
                f.Aux = new CondFlags(cond, inner, (int)i.Imm);
                SetVar(VarFlags, f);
                return;
            }
            case A64Op.FCsel:
            {
                Node cond = Condition(i.Cond);
                Node a = Fp(i.Rn, i.FpSize), b = Fp(i.Rm, i.FpSize);
                SetFp(i.Rd, _b.Select(cond, a, b));
                return;
            }
            case A64Op.Scvtf or A64Op.Ucvtf:
            {
                if (i.FpSize == 2) Unknown(i, i.Op + " (half)");
                Node a = R(i.Rn, i.Is64);
                SetFp(i.Rd, _b.Raw(i.Op == A64Op.Scvtf ? Op.SIntToF : Op.UIntToF, FpType(i.FpSize), a));
                return;
            }
            case A64Op.FCvtToInt:
            {
                if (i.FpSize == 2) Unknown(i, "FCvtToInt (half)");
                if ((A64Rounding)i.Imm != A64Rounding.Zero) Unknown(i, "FCvtToInt (" + (A64Rounding)i.Imm + ")");
                Node a = Fp(i.Rn, i.FpSize);
                SetR(i.Rd, i.Is64, _b.Raw(i.Signed ? Op.FToSInt : Op.FToUInt, t, a));
                return;
            }

            // ---- SIMD
            case A64Op.Movi:
            {
                ulong pattern = i.Target;
                bool q = (i.Imm2 & 1) != 0;
                SetQword(i.Rd, 0, C(VT.I64, (long)pattern));
                SetQword(i.Rd, 1, C(VT.I64, q ? (long)pattern : 0));
                return;
            }
            case A64Op.VMov:
            {
                bool q = (i.Imm2 & 1) != 0;
                Node[] lanes = [Lane(i.Rn, 0), Lane(i.Rn, 1), q ? Lane(i.Rn, 2) : ZeroLane(), q ? Lane(i.Rn, 3) : ZeroLane()];
                for (int lane = 0; lane < 4; lane++) SetLane(i.Rd, lane, lanes[lane]);
                return;
            }
            case A64Op.VAnd or A64Op.VOrr or A64Op.VEor or A64Op.VBic:
            {
                bool q = (i.Imm2 & 1) != 0;
                var lanes = new Node[4];
                for (int lane = 0; lane < 4; lane++)
                {
                    if (!q && lane >= 2) { lanes[lane] = ZeroLane(); continue; }
                    Node a = Lane(i.Rn, lane), b = Lane(i.Rm, lane);
                    lanes[lane] = i.Op switch
                    {
                        A64Op.VAnd => _b.And(a, b),
                        A64Op.VOrr => _b.Or(a, b),
                        A64Op.VEor => _b.Xor(a, b),
                        _ => _b.And(a, _b.Not(b)),
                    };
                }
                for (int lane = 0; lane < 4; lane++) SetLane(i.Rd, lane, lanes[lane]);
                return;
            }
            case A64Op.VFAdd or A64Op.VFSub or A64Op.VFMul or A64Op.VFDiv:
            {
                bool q = (i.Imm2 & 1) != 0;
                Op op = i.Op switch { A64Op.VFAdd => Op.FAdd, A64Op.VFSub => Op.FSub, A64Op.VFMul => Op.FMul, _ => Op.FDiv };
                if (i.ElemSize == 8)
                {
                    Node[] halves = new Node[2];
                    for (int h = 0; h < 2; h++)
                        halves[h] = _b.FToBits(_b.Raw(op, VT.F64, _b.BitsToF(Qword(i.Rn, h)), _b.BitsToF(Qword(i.Rm, h))));
                    SetQword(i.Rd, 0, halves[0]);
                    SetQword(i.Rd, 1, halves[1]);
                    return;
                }
                var lanes = new Node[4];
                for (int lane = 0; lane < 4; lane++)
                    lanes[lane] = !q && lane >= 2
                        ? ZeroLane()
                        : _b.FToBits(_b.Raw(op, VT.F32, _b.BitsToF(Lane(i.Rn, lane)), _b.BitsToF(Lane(i.Rm, lane))));
                for (int lane = 0; lane < 4; lane++) SetLane(i.Rd, lane, lanes[lane]);
                return;
            }
            case A64Op.DupScalar:
            {
                if (i.ElemSize == 4) SetScalarBits(i.Rd, Lane(i.Rn, (int)i.Imm), 4);
                else if (i.ElemSize == 8) SetScalarBits(i.Rd, Qword(i.Rn, (int)i.Imm), 8);
                else Unknown(i, "DupScalar (small)");
                return;
            }
            case A64Op.Dup:
            {
                bool q = (i.Imm2 & 1) != 0;
                if (i.ElemSize == 4)
                {
                    Node e = Lane(i.Rn, (int)i.Imm);
                    for (int lane = 0; lane < 4; lane++) SetLane(i.Rd, lane, !q && lane >= 2 ? ZeroLane() : e);
                }
                else if (i.ElemSize == 8 && q)
                {
                    Node e = Qword(i.Rn, (int)i.Imm);
                    SetQword(i.Rd, 0, e);
                    SetQword(i.Rd, 1, e);
                }
                else Unknown(i, "Dup (small)");
                return;
            }
            case A64Op.DupGp:
            {
                bool q = (i.Imm2 & 1) != 0;
                if (i.ElemSize == 4)
                {
                    Node e = R(i.Rn, false);
                    for (int lane = 0; lane < 4; lane++) SetLane(i.Rd, lane, !q && lane >= 2 ? ZeroLane() : e);
                }
                else if (i.ElemSize == 8 && q)
                {
                    Node e = X(i.Rn);
                    SetQword(i.Rd, 0, e);
                    SetQword(i.Rd, 1, e);
                }
                else Unknown(i, "DupGp (small)");
                return;
            }
            case A64Op.Ins:
            {
                if (i.ElemSize == 4) SetLane(i.Rd, (int)i.Imm, Lane(i.Rn, (int)i.Imm2));
                else if (i.ElemSize == 8) SetQword(i.Rd, (int)i.Imm, Qword(i.Rn, (int)i.Imm2));
                else Unknown(i, "Ins (small)");
                return;
            }
            case A64Op.InsGp:
            {
                if (i.ElemSize == 4) SetLane(i.Rd, (int)i.Imm, R(i.Rn, false));
                else if (i.ElemSize == 8) SetQword(i.Rd, (int)i.Imm, X(i.Rn));
                else Unknown(i, "InsGp (small)");
                return;
            }
            case A64Op.Umov or A64Op.Smov:
            {
                Node e;
                if (i.ElemSize == 8) e = Qword(i.Rn, (int)i.Imm);
                else if (i.ElemSize == 4) e = Lane(i.Rn, (int)i.Imm);
                else
                {
                    int perLane = 4 / i.ElemSize;
                    int lane = (int)i.Imm / perLane, part = (int)i.Imm % perLane;
                    Node shifted = _b.Shift(Op.ShrU, Lane(i.Rn, lane), C(VT.I8, part * i.ElemSize * 8));
                    e = _b.Trunc(shifted, VTExtensions.IntOfBytes(i.ElemSize));
                }
                SetR(i.Rd, i.Is64, Widen(e, IntType(i.Is64), i.Op == A64Op.Smov));
                return;
            }
        }
        Unknown(i);
    }

    private Node FZero(VT type)
    {
        Node c = _fn.NewNode(Op.Const, type, null);
        c.Imm = 0;
        return c;
    }

    /// <summary>UBFM, SBFM and BFM, written as the extractions, extensions and shifts they are aliases of.</summary>
    private Node Bitfield(in A64Instruction i, VT t, int bits)
    {
        int r = (int)i.Imm, s = (int)i.Imm2;
        Node x = R(i.Rn, i.Is64);
        Node Count(int c) => C(VT.I8, c);
        switch (i.Op)
        {
            case A64Op.Ubfm:
                if (s >= r)
                {
                    int width = s - r + 1;
                    if (r == 0 && width is 8 or 16 or 32 && width < bits) return _b.ZExt(_b.Trunc(x, VTExtensions.IntOfBytes(width / 8)), t);
                    Node shifted = _b.Shift(Op.ShrU, x, Count(r));
                    return r + width == bits ? shifted : _b.And(shifted, C(t, Mask(width)));
                }
                else
                {
                    int width = s + 1, shift = bits - r;
                    Node field = width + shift == bits ? x : _b.And(x, C(t, Mask(width)));
                    return _b.Shift(Op.Shl, field, Count(shift));
                }
            case A64Op.Sbfm:
                if (s >= r)
                {
                    int width = s - r + 1;
                    if (r == 0 && width is 8 or 16 or 32 && width < bits) return _b.SExt(_b.Trunc(x, VTExtensions.IntOfBytes(width / 8)), t);
                    if (s == bits - 1) return _b.Shift(Op.ShrS, x, Count(r));
                    return _b.Shift(Op.ShrS, _b.Shift(Op.Shl, x, Count(bits - 1 - s)), Count(bits - width));
                }
                else
                {
                    int width = s + 1, shift = bits - r;
                    Node field = width is 8 or 16 or 32 && width < bits
                        ? _b.SExt(_b.Trunc(x, VTExtensions.IntOfBytes(width / 8)), t)
                        : _b.Shift(Op.ShrS, _b.Shift(Op.Shl, x, Count(bits - width)), Count(bits - width));
                    return _b.Shift(Op.Shl, field, Count(shift));
                }
            default:
            {
                Node dst = R(i.Rd, i.Is64);
                if (s >= r)
                {
                    int width = s - r + 1;
                    Node field = _b.And(_b.Shift(Op.ShrU, x, Count(r)), C(t, Mask(width)));
                    return _b.Or(_b.And(dst, C(t, ~Mask(width))), field);
                }
                else
                {
                    int width = s + 1, shift = bits - r;
                    Node field = _b.Shift(Op.Shl, _b.And(x, C(t, Mask(width))), Count(shift));
                    return _b.Or(_b.And(dst, C(t, ~(Mask(width) << shift))), field);
                }
            }
        }
    }
}
