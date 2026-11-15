using System.Text;

namespace Rewind.Analysis.Ir;

/// <summary>Value types of the machine-level IR. Integers are bit patterns; signedness lives in the operation.</summary>
public enum VT : byte { None, I1, I8, I16, I32, I64, F32, F64, Flags }

public static class VTExtensions
{
    public static int Bits(this VT t) => t switch
    {
        VT.I1 => 1, VT.I8 => 8, VT.I16 => 16, VT.I32 or VT.F32 => 32, VT.I64 or VT.F64 => 64, _ => 0,
    };

    public static int Bytes(this VT t) => (t.Bits() + 7) / 8;
    public static bool IsInt(this VT t) => t is VT.I1 or VT.I8 or VT.I16 or VT.I32 or VT.I64;
    public static bool IsFloat(this VT t) => t is VT.F32 or VT.F64;

    public static VT IntOfBytes(int bytes) => bytes switch
    {
        1 => VT.I8, 2 => VT.I16, 4 => VT.I32, 8 => VT.I64,
        _ => throw new ArgumentOutOfRangeException(nameof(bytes), bytes, "no integer type of that size"),
    };

    public static ulong Mask(this VT t) => t.Bits() >= 64 ? ulong.MaxValue : (1UL << t.Bits()) - 1;
}

public enum Op : byte
{
    // leaves
    Const, Param, Undef,
    /// <summary>The (initialized) content of a metadata slot: Imm is the slot's address. Never changes once set.</summary>
    SlotValue,

    // integer arithmetic and logic (operands and result share one type, except shifts' count)
    Add, Sub, Mul, MulHiS, MulHiU, DivS, DivU, RemS, RemU, And, Or, Xor, Shl, ShrU, ShrS, Rol, Ror, Neg, Not,
    Bswap, Popcnt, Lzcnt, Tzcnt,

    // integer comparisons, result I1 (greater-than forms are written by swapping operands)
    CmpEq, CmpNe, CmpLtS, CmpLeS, CmpLtU, CmpLeU,

    // overflow predicates, result I1
    AddOvfS, AddOvfU, SubOvfS, SubOvfU, MulOvfS, MulOvfU,

    // floating point
    FAdd, FSub, FMul, FDiv, FNeg, FAbs, FSqrt, FMin, FMax,
    /// <summary>Ordered comparisons: false when either operand is NaN.</summary>
    FCmpEq, FCmpLt, FCmpLe,
    /// <summary>True when either operand is NaN.</summary>
    FCmpUnord,

    // conversions
    ZExt, SExt, Trunc, SIntToF, UIntToF, FToSInt, FToUInt, FExt, FTrunc, BitsToF, FToBits,
    /// <summary>Concat(hi, lo): a 64-bit value from two 32-bit halves.</summary>
    Concat,

    Select, Phi,

    /// <summary>
    /// A managed-level operation recognized from a native idiom; Imm is an <see cref="IdiomKind"/>. Pure:
    /// it stands for the result of a lookup that changes nothing.
    /// </summary>
    Idiom,

    // memory and calls (ordered effects)
    Load, Store, Call,
    /// <summary>One result of a call: Imm selects which (see <see cref="CallResult"/>).</summary>
    Proj,

    /// <summary>Pseudo value describing how the CPU flags were last set: Imm is a <see cref="FlagKind"/>.</summary>
    Flags,
    /// <summary>A condition read from flags that could not be expressed over its operands; Imm is the x86 condition code.</summary>
    FlagCond,

    // block terminators
    Jump, Branch, Switch, Return, TailCall, Unreachable,
}

public enum FlagKind { Sub, Test, Add, Logic, IncDec, FCompare, Shift, Neg, Mul, Other }

public enum IdiomKind
{
    None,
    /// <summary>
    /// InterfaceEntry(object, interface class, slot): the { code, method descriptor } pair that implements
    /// slot <c>slot</c> of the interface for the object's run-time class.
    /// </summary>
    InterfaceEntry,
    /// <summary>
    /// InternalCall(name): the native implementation of the "extern" method with that internal-call name
    /// (the input is the address of the name's text). Never null.
    /// </summary>
    InternalCall,
    /// <summary>TryEntry: the condition of a try region's gate, "an exception was raised in the region". Aux = region index.</summary>
    TryEntry,
    /// <summary>CaughtWrapper: what a handler finds in its catch object slot (a reference to the caught exception). Aux = region index.</summary>
    CaughtWrapper,
    /// <summary>LostRegister: a callee-saved register written in a try region, as the handler sees it - its value depends on where the exception was raised.</summary>
    LostRegister,
    /// <summary>PInvokeTarget(cache slot): the native function a P/Invoke declaration imports, resolved on first use and cached in the slot.</summary>
    PInvokeTarget,
}

public static class CallResult
{
    public const int IntReturn = 0, FloatLane0 = 1, FloatLane1 = 2, FloatLane2 = 3, FloatLane3 = 4;
}

/// <summary>Extra data attached to a Call or TailCall node.</summary>
public sealed class CallInfo
{
    /// <summary>Direct target address, or 0 for an indirect call (the target value is then input 0).</summary>
    public ulong Target;
    public bool Indirect;
    /// <summary>Non-null for operations the CPU performs in one instruction (atomics, block moves, barriers).</summary>
    public string? Intrinsic;
    /// <summary>The call does not return (the compiler placed a trap after it).</summary>
    public bool NoReturn;
    /// <summary>Names the inputs: which register or outgoing stack slot each captured value came from.</summary>
    public List<ArgSlot> Slots = [];
}

/// <summary>Where a captured call argument lived: an integer register, a float register lane, or a stack slot.</summary>
public readonly record struct ArgSlot(ArgSlotKind Kind, int Index)
{
    public override string ToString() => Kind switch
    {
        ArgSlotKind.IntReg => "r" + Index,
        ArgSlotKind.FloatReg => "x" + Index / 4 + "." + Index % 4,
        ArgSlotKind.Stack => "stk" + Index,
        _ => "target",
    };
}

public enum ArgSlotKind { Target, IntReg, FloatReg, Stack }

public sealed class Node
{
    public int Id;
    public Op Op;
    public VT Type;
    public Node[] In = [];
    public long Imm;
    public object? Aux;
    public Block? Block;
    /// <summary>Address of the machine instruction this node came from (0 for synthesized nodes).</summary>
    public ulong Addr;
    /// <summary>Set when a pass removes the node; removed nodes are skipped everywhere.</summary>
    public bool Dead;

    public bool IsConst => Op == Op.Const;
    public ulong UImm => (ulong)Imm & Type.Mask();

    public bool IsTerminator => Op is Op.Jump or Op.Branch or Op.Switch or Op.Return or Op.TailCall or Op.Unreachable;

    /// <summary>Nodes whose position in the block matters: they read or change state.</summary>
    public bool IsEffect => Op is Op.Load or Op.Store or Op.Call || IsTerminator;

    public bool IsConstValue(long value) => Op == Op.Const && Imm == value;

    public override string ToString() => "%" + Id;
}

public sealed class Block
{
    public int Id;
    public ulong Start, End;
    public List<Node> Phis = [];
    /// <summary>All non-phi nodes created for this block, in machine order.</summary>
    public List<Node> Nodes = [];
    public List<Block> Preds = [], Succs = [];
    /// <summary>
    /// Where the block sits among the function's try regions (see Function.TryRegions): -1 outside all of them,
    /// 2r inside the protected code of region r, 2r+1 inside its handler. Nested regions chain through Outer.
    /// </summary>
    public int Scope = -1;
    public Node? Terminator => Nodes.Count != 0 && Nodes[^1].IsTerminator ? Nodes[^1] : null;

    public override string ToString() => "B" + Id;
}

/// <summary>
/// A protected region of the machine code (a C++ try block) and its handler. Control enters the region through a
/// gate block that "branches" on an exception: one way into the protected code, the other into the handler
/// (the catch funclet, lifted as part of the function), which continues in the function afterwards.
/// </summary>
public sealed class TryRegionInfo
{
    public int Index;
    /// <summary>The scope the try statement itself is in (its gate's Block.Scope).</summary>
    public int Outer = -1;
    /// <summary>The catch funclet's address (0: the region has no code and was left out).</summary>
    public ulong Funclet;
}

/// <summary>Marks (as Node.Aux) a store that only keeps a register's value for exception handlers.</summary>
public sealed class HandlerSave
{
    public static readonly HandlerSave Instance = new();
    private HandlerSave() { }
}

/// <summary>One lifted native function in SSA form.</summary>
public sealed class Function
{
    public ulong Address;
    public ulong End;
    public List<Block> Blocks = [];
    /// <summary>Try regions, indexed by the try block's number in the exception tables.</summary>
    public List<TryRegionInfo> TryRegions = [];

    /// <summary>True when the block is protected code of some try region, directly or through nesting.</summary>
    public bool IsProtected(Block b)
    {
        for (int s = b.Scope, guard = 0; s >= 0 && guard < 64; guard++)
        {
            if ((s & 1) == 0) return true;
            s = TryRegions[s >> 1].Outer;
        }
        return false;
    }

    /// <summary>
    /// True when the block is protected code of try region <paramref name="region"/>: directly, or as part of a
    /// try statement nested in it (protected code and handler alike - an exception leaving either arrives at
    /// the region's handler).
    /// </summary>
    public bool IsProtectedBy(Block b, int region)
    {
        for (int s = b.Scope, guard = 0; s >= 0 && guard < 64; guard++, s = TryRegions[s >> 1].Outer)
            if (s == 2 * region) return true;
        return false;
    }

    /// <summary>The gates of the try regions: blocks ending in a branch on IdiomKind.TryEntry; Succs = [handler, protected code].</summary>
    public IEnumerable<(Block Gate, int Region)> TryGates()
    {
        foreach (Block b in Blocks)
            if (b.Terminator is { Op: Op.Branch } t && b.Succs.Count == 2 && IsTryEntry(t.In[0]))
                yield return (b, (int)t.In[0].Aux!);
    }

    public static bool IsTryEntry(Node n) => n.Op == Op.Idiom && n.Imm == (long)IdiomKind.TryEntry && n.Aux is int;
    public Block Entry => Blocks[0];
    public int NextId;
    public List<string> Problems = [];

    /// <summary>Entry values of machine registers, keyed by variable number (see the lifter's register map).</summary>
    public Dictionary<int, Node> Params = [];

    /// <summary>
    /// Entry values of stack slots, keyed by offset from the entry stack pointer. Slots above the return address
    /// are where stack-passed arguments arrive.
    /// </summary>
    public Dictionary<int, Node> StackParams = [];

    /// <summary>Marks a Param node that stands for a stack slot rather than a register.</summary>
    public const long StackParamBase = 1L << 32;

    public Node NewNode(Op op, VT type, Block? block, params Node[] inputs) =>
        new() { Id = NextId++, Op = op, Type = type, In = inputs, Block = block };

    public string Dump(Func<Node, string?>? annotate = null)
    {
        var sb = new StringBuilder();
        sb.AppendLine($"function 0x{Address:X}");
        foreach (Block b in Blocks)
        {
            sb.Append($"{b}: [0x{b.Start:X}..0x{b.End:X})");
            if (b.Preds.Count != 0) sb.Append("  preds " + string.Join(",", b.Preds));
            if (b.Succs.Count != 0) sb.Append("  succs " + string.Join(",", b.Succs));
            sb.AppendLine();
            foreach (Node n in b.Phis)
                if (!n.Dead)
                    sb.AppendLine("    " + Describe(n, annotate));
            foreach (Node n in b.Nodes)
                if (!n.Dead)
                    sb.AppendLine("    " + Describe(n, annotate));
        }
        foreach (string p in Problems) sb.AppendLine("  ! " + p);
        return sb.ToString();
    }

    public static string Describe(Node n, Func<Node, string?>? annotate = null)
    {
        var sb = new StringBuilder();
        if (n.Type != VT.None) sb.Append($"%{n.Id}:{n.Type} = ");
        sb.Append(n.Op);
        switch (n.Op)
        {
            case Op.Const:
                sb.Append(n.Type.IsFloat()
                    ? " " + (n.Type == VT.F32 ? BitConverter.Int32BitsToSingle((int)n.Imm).ToString("R") : BitConverter.Int64BitsToDouble(n.Imm).ToString("R"))
                    : " 0x" + n.UImm.ToString("X"));
                break;
            case Op.Param:
                sb.Append(n.Imm >= StackParamBase / 2 ? $" stack{n.Imm - StackParamBase:+0;-0}" : " v" + n.Imm);
                break;
            case Op.Flags:
                sb.Append(" " + (FlagKind)n.Imm);
                break;
            case Op.SlotValue:
                sb.Append(" 0x" + n.Imm.ToString("X"));
                break;
            case Op.FlagCond:
            case Op.Proj:
                sb.Append(" #" + n.Imm);
                break;
            case Op.Idiom:
                sb.Append(" " + (IdiomKind)n.Imm);
                break;
            case Op.Call:
            case Op.TailCall:
                if (n.Aux is CallInfo ci)
                {
                    sb.Append(ci.Intrinsic != null ? " " + ci.Intrinsic : ci.Indirect ? " indirect" : $" 0x{ci.Target:X}");
                    if (ci.NoReturn) sb.Append(" noreturn");
                }
                break;
        }
        if (n.In.Length != 0)
        {
            sb.Append(' ');
            for (int i = 0; i < n.In.Length; i++)
            {
                if (i != 0) sb.Append(", ");
                if (n.Aux is CallInfo info && i < info.Slots.Count) sb.Append(info.Slots[i]).Append('=');
                Node input = n.In[i];
                sb.Append(input.Op == Op.Const && !input.Type.IsFloat() ? "0x" + input.UImm.ToString("X") : input.ToString());
            }
        }
        if (n.Op == Op.Switch && n.Aux is List<Block> targets) sb.Append(" -> " + string.Join(",", targets));
        string? note = annotate?.Invoke(n);
        if (note != null) sb.Append("    ; ").Append(note);
        if (n.Addr != 0 && n.IsEffect) sb.Append($"    @0x{n.Addr:X}");
        return sb.ToString();
    }
}
