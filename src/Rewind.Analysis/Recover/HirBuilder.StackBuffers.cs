using Rewind.Analysis.Abi;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Passes;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// "stackalloc byte[n]": memory on the stack the program only ever reaches through its address.
///
/// IL2CPP turns a stackalloc of constant size into alloca, which the compiler makes part of the frame: an
/// object of n bytes, zeroed, whose address is put in a Span or handed to a method that takes a pointer. The
/// code never reads or writes it itself. Such an object is no variable of a type: it is a buffer, and its
/// addresses are the buffer's pointer plus an offset.
/// </summary>
public sealed partial class HirBuilder
{
    private static readonly bool NoStackBuffers = Environment.GetEnvironmentVariable("REWIND_NO_STACK_BUFFERS") != null;

    /// <summary>Stack buffers: frame offset of the object to its size and the variable holding its pointer.</summary>
    private readonly Dictionary<int, (int Size, HVar Pointer)> _stackBuffers = [];

    private void PlanStackBuffers()
    {
        if (NoStackBuffers || _l.Frame.Count == 0) return;
        Dictionary<Node, List<Node>>? uses = null;
        // A read only handed to calls as an outgoing stack argument (an unknown function's arguments are read
        // from where they would be): it asks nothing of the memory.
        bool OnlyPassed(Node load)
        {
            uses ??= DeadCode.Uses(_fn);
            if (!uses.TryGetValue(load, out List<Node>? users)) return true;
            foreach (Node user in users)
            {
                if (user.Op is not (Op.Call or Op.TailCall) || user.Aux is not CallInfo info) return false;
                for (int i = 0; i < user.In.Length; i++)
                    if (ReferenceEquals(user.In[i], load) && (i >= info.Slots.Count || info.Slots[i].Kind != ArgSlotKind.Stack))
                        return false;
            }
            return true;
        }
        // The stack objects, and the zeroed stretches of them (a buffer the compiler laid next to other locals
        // makes one object with them; the zeroing says how far the buffer goes).
        var candidates = new List<FrameObject>(_l.Frame);
        foreach (Block b in _fn.Blocks)
            foreach (Node n in b.Nodes)
                if (!n.Dead && n.Op is Op.Call or Op.TailCall && BlockCopies.Of(n, _p.Helpers, tail: true) is { IsCopy: false, Bytes: >= 8 } zeroing &&
                    zeroing.Operand.IsConstValue(0) && IsFrameAddress(zeroing.Destination, out int start) &&
                    !candidates.Any(c => c.Offset == start && c.Size == zeroing.Bytes))
                    candidates.Add(new FrameObject { Offset = start, Size = zeroing.Bytes });
        foreach (FrameObject o in candidates)
        {
            if (o.Size < 8 || o.Size > 1 << 16 || _fakeBoxes.ContainsKey(o.Offset)) continue;
            if (_stackBuffers.Any(kv => o.Offset < kv.Key + kv.Value.Size && kv.Key < o.Offset + o.Size)) continue;
            bool Inside(int at) => at >= o.Offset && at < o.Offset + o.Size;
            bool direct = false, asData = false;
            foreach (Block b in _fn.Blocks)
            {
                foreach (Node n in b.Nodes)
                {
                    if (n.Dead) continue;
                    if (n.Op is Op.Load or Op.Store && IsFrameAddress(n.In[0], out int at) && Inside(at))
                    {
                        if (n.Op == Op.Load && OnlyPassed(n)) continue;
                        direct = true;
                        break;
                    }
                    // Its address kept in memory (the pointer of a Span).
                    if (n.Op == Op.Store && IsFrameAddress(n.In[1], out int kept) && Inside(kept)) asData = true;
                    if (n.Op is not (Op.Call or Op.TailCall) || n.Aux is not CallInfo info) continue;
                    BlockOp? block = BlockCopies.Of(n, _p.Helpers, tail: true);
                    for (int i = 0; i < n.In.Length && i < info.Slots.Count; i++)
                    {
                        if (!IsFrameAddress(n.In[i], out int handed) || !Inside(handed)) continue;
                        // The zeroing of the whole of it (stackalloc memory is zeroed): no access.
                        if (block is { IsCopy: false } fill && handed == o.Offset && fill.Bytes == o.Size && fill.Operand.IsConstValue(0) &&
                            ReferenceEquals(fill.Destination, n.In[i])) continue;
                        if (block != null) { direct = true; break; } // copied to or from: what is in it matters here
                        ArgSlot slot = info.Slots[i];
                        int position = slot.Kind == ArgSlotKind.IntReg ? slot.Index : slot.Kind == ArgSlotKind.Stack ? slot.Index + _fn.Regs.FirstStackPosition : -1;
                        // A reference or a struct handed over by address: a variable after all. A pointer, a
                        // native integer, native code: the address as data.
                        if (position < 0 || ReferenceParameterAt(info, position)) { direct = true; break; }
                        asData = true;
                    }
                    if (direct) break;
                }
                if (direct) break;
            }
            if (direct || !asData) continue;
            TypeSig pointer = _m.Sigs.Pointer(_byte);
            _stackBuffers[o.Offset] = (o.Size, _h.NewLocal(pointer, "buffer"));
        }
    }

    /// <summary>
    /// Whether a method called takes something by reference at this position: a ref or out parameter, a struct
    /// passed by address, the struct a method is called on, the buffer a struct is returned in. (Indirect calls
    /// and native functions say nothing: no.)
    /// </summary>
    private bool ReferenceParameterAt(CallInfo info, int position)
    {
        if (info.Indirect) return false;
        static bool At(MethodAbi abi, int position) => abi.Params.Any(p => p.Position == position &&
            (p.Type is ByRefSig || p.Pass == PassKind.Indirect || p.Role == ParamRole.ReturnBuffer ||
             (p.Role == ParamRole.This && p.Type?.Definition is { IsValueType: true })));
        CallTarget target = _p.Resolve(info.Target);
        foreach (MethodDef m in target.Methods.Take(8))
            if (At(_p.Abi.For(m, [], []), position)) return true;
        foreach (MethodInst inst in target.Insts.Take(8))
            if (At(_p.Abi.For(inst), position)) return true;
        return false;
    }

    /// <summary>The address <paramref name="offset"/> as a stack buffer's pointer plus an offset, or null outside every buffer.</summary>
    private HExpr? BufferAddress(int offset)
    {
        foreach (var (start, (size, variable)) in _stackBuffers)
        {
            if (offset < start || offset >= start + size) continue;
            HExpr p = new HLocal(variable) { Type = variable.Type };
            return offset == start ? p : new HBinary(HBinaryOp.Add, p, new HConst(offset - start, _int)) { Type = variable.Type };
        }
        return null;
    }

    /// <summary>Whether a block operation is the zeroing of a whole stack buffer (which stackalloc did already).</summary>
    private bool ZeroesStackBuffer(BlockOp op) =>
        !op.IsCopy && op.Operand.IsConstValue(0) && IsFrameAddress(op.Destination, out int at) &&
        _stackBuffers.TryGetValue(at, out var buffer) && buffer.Size == op.Bytes;

    /// <summary>Each buffer's "stackalloc byte[n]", first thing in the method.</summary>
    private void DeclareStackBuffers()
    {
        if (_stackBuffers.Count == 0 || _h.Blocks.Count == 0) return;
        int at = 0;
        foreach (var (_, (size, variable)) in _stackBuffers.OrderBy(kv => kv.Key))
        {
            var allocation = new HTypeExpr(HTypeOp.StackAlloc, _byte, new HConst(size, _int)) { Type = variable.Type };
            _h.Blocks[0].Statements.Insert(at++, new HAssign(new HLocal(variable) { Type = variable.Type }, allocation));
        }
    }
}
