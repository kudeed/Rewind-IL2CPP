using Rewind.Analysis.Ir;
using Rewind.Analysis.Runtime;

namespace Rewind.Analysis.Passes;

/// <summary>
/// A copy or a fill of a run of bytes: the C runtime's memcpy/memset, the single instruction that does the same
/// (rep movs, rep stos), or a copy loop recognized here. Operand is the source address of a copy, the byte value
/// of a fill.
/// </summary>
public readonly record struct BlockOp(bool IsCopy, Node Destination, Node Operand, Node Size, int DestinationInput, int OperandInput)
{
    /// <summary>The number of bytes when it is a constant, else -1.</summary>
    public int Bytes => Size.IsConst && IrBuilder.SImm(Size) is > 0 and <= BlockCopies.Largest ? (int)IrBuilder.SImm(Size) : -1;
}

/// <summary>
/// Recognizes the compiler's block copies.
///
/// A large struct is assigned with a loop that moves a fixed number of bytes per round (MSVC: 128, through
/// vector registers), followed by straight-line moves of whatever is left. Read literally that is pointer
/// arithmetic over untyped memory; what the program did is copy one object. The loop becomes one "memcpy"
/// operation - the same thing the single-instruction form (rep movs) is lifted to - and moves that continue
/// exactly where a memcpy stopped are taken into it.
/// </summary>
public static class BlockCopies
{
    public const string Copy = "memcpy";
    public const int Largest = 1 << 24;

    /// <summary>The block operation a call node is, if it is one (a jump to the function too, with <paramref name="tail"/>).</summary>
    public static BlockOp? Of(Node call, RuntimeHelpers helpers, bool tail = false)
    {
        if (call.Dead || !(call.Op == Op.Call || (tail && call.Op == Op.TailCall)) || call.Aux is not CallInfo info || info.Indirect) return null;
        if (info.Intrinsic != null)
        {
            if (call.In.Length != 3) return null;
            if (info.Intrinsic == Copy) return new BlockOp(true, call.In[0], call.In[1], call.In[2], 0, 1);
            if (info.Intrinsic.StartsWith("memset", StringComparison.Ordinal))
            {
                // Wider fills repeat a 2-, 4- or 8-byte value: the same as a byte fill only when that value is zero.
                if (info.Intrinsic != "memset1" && !call.In[1].IsConstValue(0)) return null;
                return new BlockOp(false, call.In[0], call.In[1], call.In[2], 0, 1);
            }
            return null;
        }
        HelperKind kind = helpers.KindAt(info.Target);
        if (kind is not (HelperKind.Memcpy or HelperKind.Memset)) return null;
        int d = -1, o = -1, s = -1;
        for (int i = 0; i < call.In.Length && i < info.Slots.Count; i++)
        {
            if (info.Slots[i].Kind != ArgSlotKind.IntReg) continue;
            if (info.Slots[i].Index == 0) d = i;
            else if (info.Slots[i].Index == 1) o = i;
            else if (info.Slots[i].Index == 2) s = i;
        }
        if (d < 0 || o < 0 || s < 0) return null;
        return new BlockOp(kind == HelperKind.Memcpy, call.In[d], call.In[o], call.In[s], d, o);
    }

    /// <summary>
    /// How a block operation touches the memory behind input <paramref name="input"/>: how many bytes, and
    /// whether it reads or writes them. False when the call is no block operation of known size, or the input is
    /// not one of its addresses.
    /// </summary>
    public static bool Access(Node call, int input, RuntimeHelpers helpers, out int bytes, out bool reads, out bool writes)
    {
        bytes = -1;
        reads = writes = false;
        if (Of(call, helpers) is not { } op || op.Bytes < 0) return false;
        if (input == op.DestinationInput) writes = true;
        else if (op.IsCopy && input == op.OperandInput) reads = true;
        else return false;
        bytes = op.Bytes;
        return true;
    }

    /// <summary>Turns copy loops into single copies. True when any was found (the blocks then want a cleanup).</summary>
    public static bool CollapseLoops(Function fn)
    {
        if (!fn.Blocks.Any(b => b.Succs.Contains(b))) return false;
        DeadCode.Run(fn);
        bool changed = false;
        foreach (Block b in fn.Blocks)
            if (b.Succs.Contains(b) && CollapseLoop(fn, b))
                changed = true;
        return changed;
    }

    private static Node Narrowless(Node n)
    {
        while (n.Op is Op.ZExt or Op.Trunc) n = n.In[0];
        return n;
    }

    private static bool CollapseLoop(Function fn, Block b)
    {
        if (b.Preds.Count != 2 || b.Succs.Count != 2 || b.Terminator is not { Op: Op.Branch } term) return false;
        int self = b.Preds.IndexOf(b);
        if (self < 0 || ReferenceEquals(b.Preds[1 - self], b)) return false;
        int entry = 1 - self;
        int back = b.Succs.IndexOf(b);
        if (back < 0 || ReferenceEquals(b.Succs[1 - back], b)) return false;
        Block exit = b.Succs[1 - back];

        var inside = new HashSet<Node>();
        foreach (Node n in b.Phis) if (!n.Dead) inside.Add(n);
        foreach (Node n in b.Nodes) if (!n.Dead) inside.Add(n);

        // What changes per round: two addresses stepping by the same amount, and a countdown.
        Node? counter = null;
        long rounds = 0;
        var pointers = new Dictionary<Node, (Node Init, long Step)>();
        foreach (Node phi in b.Phis)
        {
            if (phi.Dead) continue;
            if (phi.In.Length != 2) return false;
            Node init = phi.In[entry], next = Narrowless(phi.In[self]);
            if (next.Op != Op.Add || !inside.Contains(next) || !next.In[1].IsConst || !ReferenceEquals(Narrowless(next.In[0]), phi)) return false;
            long step = IrBuilder.SImm(next.In[1]);
            if (step == -1 && init.IsConst && counter == null)
            {
                counter = phi;
                rounds = (long)init.UImm;
            }
            else if (step > 0 && phi.Type == VT.I64 && ReferenceEquals(phi.In[self], next)) pointers[phi] = (init, step);
            else return false;
        }
        if (counter == null || pointers.Count != 2 || rounds < 1) return false;

        // The loop goes round while the countdown has not reached its end.
        Node cond = term.In[0];
        if (cond.Op is not (Op.CmpNe or Op.CmpEq) || !inside.Contains(cond) || !cond.In[1].IsConst) return false;
        if ((cond.Op == Op.CmpNe ? 0 : 1) != back) return false;
        if (!CounterValue(cond.In[0], counter, inside, out long tested) || tested != (long)cond.In[1].UImm) return false;

        // An address inside the loop: one of the stepping addresses plus a constant.
        (Node Base, long Offset) Address(Node n)
        {
            long k = 0;
            while (n.Op == Op.Add && n.In[1].IsConst && inside.Contains(n))
            {
                k += IrBuilder.SImm(n.In[1]);
                n = n.In[0];
            }
            return (n, k);
        }

        Node? source = null, destination = null, firstStore = null;
        var loads = new Dictionary<Node, long>();
        var stored = new List<(long Start, long End)>();
        foreach (Node n in b.Nodes)
        {
            if (n.Dead || ReferenceEquals(n, term)) continue;
            if (n.Op == Op.Load)
            {
                var (p, k) = Address(n.In[0]);
                if (!pointers.ContainsKey(p) || (source != null && !ReferenceEquals(source, p)) || n.Type.Bytes() == 0) return false;
                source = p;
                loads[n] = k;
            }
            else if (n.Op == Op.Store)
            {
                var (p, k) = Address(n.In[0]);
                if (!pointers.ContainsKey(p) || (destination != null && !ReferenceEquals(destination, p))) return false;
                destination = p;
                if (!loads.TryGetValue(n.In[1], out long from) || from != k) return false;
                stored.Add((k, k + n.In[1].Type.Bytes()));
                firstStore ??= n;
            }
            else if (n.IsEffect) return false;
        }
        if (source == null || destination == null || firstStore == null || ReferenceEquals(source, destination)) return false;
        long stride = pointers[source].Step;
        if (pointers[destination].Step != stride || stored.Count != loads.Count) return false;
        stored.Sort();
        long end = 0;
        foreach (var (start, stop) in stored)
        {
            if (start != end) return false;
            end = stop;
        }
        if (end != stride || rounds * stride > Largest) return false;

        // What the loop leaves behind for the code after it: the addresses and the countdown as they are in the
        // last round. Anything else seen from outside (a value that was copied) means this is no plain copy.
        var uses = DeadCode.Uses(fn);
        var leftovers = new List<(Node Old, Node? Base, long Value)>();
        foreach (Node n in inside)
        {
            if (!uses.TryGetValue(n, out List<Node>? users) || users.All(inside.Contains)) continue;
            var (p, k) = Address(n);
            if (pointers.TryGetValue(p, out var pointer)) leftovers.Add((n, pointer.Init, (rounds - 1) * stride + k));
            else if (CounterValue(n, counter, inside, out long value)) leftovers.Add((n, null, value));
            else return false;
        }

        Node sourceInit = pointers[source].Init, destinationInit = pointers[destination].Init;
        foreach (Node n in b.Phis) n.Dead = true;
        foreach (Node n in b.Nodes) n.Dead = true;
        b.Phis.Clear();
        b.Nodes.Clear();
        var builder = new IrBuilder(fn) { Current = b, CurrentAddr = firstStore.Addr };
        Node call = builder.Raw(Op.Call, VT.None, destinationInit, sourceInit, builder.Const(VT.I64, rounds * stride));
        call.Aux = new CallInfo { Intrinsic = Copy };
        var replace = new Dictionary<Node, Node>();
        foreach (var (old, at, value) in leftovers)
            replace[old] = at != null ? builder.Add(at, builder.Const(VT.I64, value)) : builder.Const(old.Type, value);
        builder.CurrentAddr = term.Addr;
        builder.Raw(Op.Jump, VT.None);
        b.Preds.RemoveAt(self);
        b.Succs.Clear();
        b.Succs.Add(exit);
        if (replace.Count != 0)
            foreach (Block block in fn.Blocks)
            {
                foreach (Node n in block.Phis)
                    for (int i = 0; i < n.In.Length; i++)
                        if (replace.TryGetValue(n.In[i], out Node? r)) n.In[i] = r;
                foreach (Node n in block.Nodes)
                    for (int i = 0; i < n.In.Length; i++)
                        if (replace.TryGetValue(n.In[i], out Node? r)) n.In[i] = r;
            }
        return true;
    }

    /// <summary>The value of a node computed from the countdown alone, in the loop's last round (where the countdown is 1).</summary>
    private static bool CounterValue(Node n, Node counter, HashSet<Node> inside, out long value)
    {
        value = 0;
        if (ReferenceEquals(n, counter))
        {
            value = 1;
            return true;
        }
        if (!inside.Contains(n)) return false;
        switch (n.Op)
        {
            case Op.Add when n.In[1].IsConst && CounterValue(n.In[0], counter, inside, out long a):
                value = (long)((ulong)(a + n.In[1].Imm) & n.Type.Mask());
                return true;
            case Op.Sub when n.In[1].IsConst && CounterValue(n.In[0], counter, inside, out long s):
                value = (long)((ulong)(s - n.In[1].Imm) & n.Type.Mask());
                return true;
            case Op.Trunc or Op.ZExt when CounterValue(n.In[0], counter, inside, out long t):
                value = (long)((ulong)t & n.Type.Mask());
                return true;
            default:
                return false;
        }
    }

    private static (Node Base, long Offset) Split(Node n)
    {
        long k = 0;
        while (n.Op == Op.Add && n.In[1].IsConst)
        {
            k += IrBuilder.SImm(n.In[1]);
            n = n.In[0];
        }
        return (n, k);
    }

    /// <summary>
    /// Takes the moves that follow a copy and continue it - a load just past the copied source bytes, stored just
    /// past the copied destination bytes - into the copy. True when any copy grew.
    /// </summary>
    public static bool Extend(Function fn)
    {
        Dictionary<Node, List<Node>>? uses = null;
        bool changed = false;
        foreach (Block b in fn.Blocks)
        {
            for (int i = 0; i < b.Nodes.Count; i++)
            {
                Node call = b.Nodes[i];
                if (call.Dead || call.Op != Op.Call || call.Aux is not CallInfo { Intrinsic: Copy } || call.In.Length != 3 || !call.In[2].IsConst) continue;
                long size = IrBuilder.SImm(call.In[2]);
                if (size <= 0) continue;
                var (dBase, dOff) = Split(call.In[0]);
                var (sBase, sOff) = Split(call.In[1]);
                var loads = new Dictionary<Node, long>();
                var pairs = new List<(long Start, long End, Node Load, Node Store)>();
                for (int j = i + 1; j < b.Nodes.Count; j++)
                {
                    Node n = b.Nodes[j];
                    if (n.Dead) continue;
                    if (n.Op == Op.Load)
                    {
                        var (p, k) = Split(n.In[0]);
                        if (!ReferenceEquals(p, sBase) || k < sOff + size) break;
                        // Both on the stack: the bytes read must not be ones the copy writes.
                        if (ReferenceEquals(sBase, dBase) && k + n.Type.Bytes() > dOff && k < dOff + size + 0x1000) break;
                        loads[n] = k - sOff - size;
                    }
                    else if (n.Op == Op.Store)
                    {
                        var (p, k) = Split(n.In[0]);
                        if (!ReferenceEquals(p, dBase) || !loads.TryGetValue(n.In[1], out long from) || from != k - dOff - size) break;
                        pairs.Add((from, from + n.In[1].Type.Bytes(), n.In[1], n));
                    }
                    else if (n.IsEffect) break;
                }
                if (pairs.Count == 0) continue;
                pairs.Sort((x, y) => x.Start.CompareTo(y.Start));
                uses ??= DeadCode.Uses(fn);
                long end = 0;
                int taken = 0;
                foreach (var (start, stop, load, _) in pairs)
                {
                    if (start != end || !uses.TryGetValue(load, out List<Node>? users) || users.Count != 1) break;
                    end = stop;
                    taken++;
                }
                if (taken == 0) continue;
                for (int k = 0; k < taken; k++)
                {
                    pairs[k].Load.Dead = true;
                    pairs[k].Store.Dead = true;
                }
                Node total = fn.NewNode(Op.Const, VT.I64, null);
                total.Imm = size + end;
                call.In[2] = total;
                b.Nodes.RemoveAll(n => n.Dead);
                uses = null;
                changed = true;
                i = b.Nodes.IndexOf(call) - 1; // look again: what follows may continue the longer copy
            }
        }
        return changed;
    }
}
