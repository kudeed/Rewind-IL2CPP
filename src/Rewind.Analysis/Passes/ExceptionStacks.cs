using Rewind.Analysis.Ir;
using Rewind.Analysis.Runtime;
using Rewind.Analysis.X64;

namespace Rewind.Analysis.Passes;

/// <summary>
/// IL2CPP keeps the exceptions being handled in a small stack of its own (ExceptionSupportStack: an array of
/// references followed by a count, both in the function's frame). A catch handler pushes the exception it
/// caught; the catch block reads it back as "the top" and pops it when done. The managed program has no such
/// stack: the top is simply the exception the enclosing catch caught.
///
/// Followed through the function - the count as "some value plus a constant", the array's entries by index -
/// a read of the top finds the value that was pushed. When every read is explained this way the stack has no
/// role left: its reads become the pushed values and its bookkeeping goes. When one is not, nothing changes.
///
/// The compiler pastes the stack's operations in place or calls them (push, pop, top), sometimes both in one
/// function; either form is followed.
/// </summary>
public static class ExceptionStacks
{
    private readonly record struct Count(int Symbol, int Delta);

    private sealed class State
    {
        public Count Count;
        public Dictionary<(int Symbol, int Index), Node> Entries = [];

        public State Clone() => new() { Count = Count, Entries = new Dictionary<(int, int), Node>(Entries) };

        public bool Same(State other)
        {
            if (Count != other.Count || Entries.Count != other.Entries.Count) return false;
            foreach (var (key, value) in Entries)
                if (!other.Entries.TryGetValue(key, out Node? o) || !ReferenceEquals(o, value))
                    return false;
            return true;
        }
    }

    /// <summary>One use of the stack: a read or write of the count or of an entry, or a call of one of its operations.</summary>
    private sealed class Access
    {
        public Node Node = null!;
        public bool IsStore, IsCount;
        /// <summary>For an entry: the count load its index comes from (null: a fixed index), and what is added to it.</summary>
        public Node? CountLoad;
        public int Bias;
        /// <summary>For a call: which operation, the value pushed, the node holding what pop or top returned.</summary>
        public HelperKind Call;
        public Node? Pushed, Result;

        public bool Changes => IsStore || Call is HelperKind.ExceptionStackPush or HelperKind.ExceptionStackPop;
    }

    private static Node? IntArgument(Node call, int position)
    {
        if (call.Aux is not CallInfo info) return null;
        for (int i = 0; i < call.In.Length && i < info.Slots.Count; i++)
            if (info.Slots[i].Kind == ArgSlotKind.IntReg && info.Slots[i].Index == position)
                return call.In[i];
        return null;
    }

    private static HelperKind OperationOf(Node n, RuntimeHelpers helpers)
    {
        if (n.Dead || n.Op != Op.Call || n.Aux is not CallInfo { Indirect: false, Intrinsic: null } info) return HelperKind.None;
        HelperKind kind = helpers.KindAt(info.Target);
        return kind is HelperKind.ExceptionStackPush or HelperKind.ExceptionStackPop or HelperKind.ExceptionStackTop ? kind : HelperKind.None;
    }

    public static bool Run(Function fn, RuntimeHelpers helpers)
    {
        if (fn.TryRegions.Count == 0 || !fn.Params.TryGetValue(X64Lifter.VarRsp, out Node? sp0)) return false;

        bool Stack(Node n, out int offset)
        {
            long k = 0;
            while (n.Op == Op.Add && n.In[1].IsConst)
            {
                k += IrBuilder.SImm(n.In[1]);
                n = n.In[0];
            }
            offset = (int)k;
            return ReferenceEquals(n, sp0) && k is > -0x4000000 and < 0x4000000;
        }

        // An entry address: stack pointer + constant + 8 * (count read from the frame, plus a constant).
        bool Indexed(Node address, out int storage, out int counter, out Node countLoad, out int bias, List<Node> path)
        {
            storage = counter = bias = 0;
            countLoad = null!;
            long k = 0;
            Node? scaled = null;
            bool hasSp = false;
            var work = new Stack<Node>();
            work.Push(address);
            int budget = 12;
            while (work.Count > 0)
            {
                Node n = work.Pop();
                if (n.IsConst) k += IrBuilder.SImm(n);
                else if (ReferenceEquals(n, sp0))
                {
                    if (hasSp) return false;
                    hasSp = true;
                }
                else if (n.Op == Op.Add && n.Type == VT.I64 && budget-- > 0)
                {
                    work.Push(n.In[0]);
                    work.Push(n.In[1]);
                }
                else if (scaled != null) return false;
                else scaled = n;
            }
            if (!hasSp || scaled == null) return false;
            Node index;
            if (scaled.Op == Op.Mul && scaled.In[1].IsConstValue(8)) index = scaled.In[0];
            else if (scaled.Op == Op.Shl && scaled.In[1].IsConst && scaled.In[1].UImm == 3) index = scaled.In[0];
            else return false;
            if (index.Op is not (Op.SExt or Op.ZExt)) return false;
            Node y = index.In[0];
            path.Add(scaled);
            path.Add(index);
            if (y.Op == Op.Add && y.In[1].IsConst)
            {
                bias = (int)IrBuilder.SImm(y.In[1]);
                path.Add(y);
                y = y.In[0];
            }
            if (y.Op != Op.Load || y.Type != VT.I32 || !Stack(y.In[0], out counter)) return false;
            // The additions between the address and the scaled index.
            bool Leads(Node n)
            {
                if (ReferenceEquals(n, scaled)) return true;
                if (n.Op != Op.Add || n.Type != VT.I64) return false;
                bool leads = Leads(n.In[0]) | Leads(n.In[1]);
                if (leads) path.Add(n);
                return leads;
            }
            Leads(address);
            countLoad = y;
            storage = (int)k;
            return true;
        }

        // 1. Candidates: a count slot and the array it indexes.
        var candidates = new Dictionary<int, int>(); // count offset -> array offset
        var rejected = new HashSet<int>();
        var scratch = new List<Node>();
        foreach (Block b in fn.Blocks)
            foreach (Node n in b.Nodes)
            {
                if (n.Dead || n.Op is not (Op.Load or Op.Store)) continue;
                scratch.Clear();
                if (Stack(n.In[0], out _) || !Indexed(n.In[0], out int storage, out int counter, out _, out _, scratch)) continue;
                if (candidates.TryGetValue(counter, out int known) && known != storage) rejected.Add(counter);
                candidates[counter] = storage;
            }
        // Stacks used through calls: the count sits right after the array, and the (pasted) constructor zeroes it.
        var called = new HashSet<int>();
        foreach (Block b in fn.Blocks)
            foreach (Node n in b.Nodes)
                if (OperationOf(n, helpers) != HelperKind.None && IntArgument(n, 0) is { } self && Stack(self, out int at))
                    called.Add(at);
        foreach (int storage in called)
        {
            if (candidates.ContainsValue(storage)) continue;
            int counter = int.MaxValue;
            foreach (Block b in fn.Blocks)
                foreach (Node n in b.Nodes)
                    if (!n.Dead && n.Op == Op.Store && n.In[1].Type == VT.I32 && n.In[1].IsConstValue(0) && Stack(n.In[0], out int at) &&
                        at > storage && (at - storage) % 8 == 0 && at - storage <= 128 && at < counter)
                        counter = at;
            if (counter != int.MaxValue && !candidates.ContainsKey(counter)) candidates[counter] = storage;
        }
        bool changed = false;
        foreach (var (counter, storage) in candidates)
        {
            if (rejected.Contains(counter)) continue;
            int slots = (counter - storage) / 8;
            if (counter <= storage || (counter - storage) % 8 != 0 || slots > 16) continue;
            changed |= Resolve(fn, helpers, sp0, counter, storage, slots, Stack, Indexed);
        }
        if (changed) DeadCode.Run(fn);
        return changed;
    }

    private delegate bool StackTest(Node n, out int offset);
    private delegate bool IndexedTest(Node address, out int storage, out int counter, out Node countLoad, out int bias, List<Node> path);

    /// <summary>When set, told which check gave up on a stack (for debugging).</summary>
    public static Action<string>? Trace;

    private static bool Bail(int check)
    {
        Trace?.Invoke($"exception stack not resolved (check {check})");
        return false;
    }

    private static bool Resolve(Function fn, RuntimeHelpers helpers, Node sp0, int counter, int storage, int slots, StackTest stack, IndexedTest indexed)
    {
        int end = counter + 4;
        var accesses = new Dictionary<Node, Access>();
        Dictionary<Node, List<Node>>? callUses = null;
        var inner = new HashSet<Node>(); // the values in between: indexes, addresses, the count plus one

        // A read that is only handed to calls as a stack argument: the compiler put the stack where arguments
        // beyond the fourth would go (no call here has any), and a call's possible arguments are read from
        // there as they stand. Such a read asks nothing of the stack.
        bool OnlyPassed(Node load)
        {
            callUses ??= DeadCode.Uses(fn);
            if (!callUses.TryGetValue(load, out List<Node>? users)) return false;
            foreach (Node user in users)
            {
                if (user.Op is not (Op.Call or Op.TailCall) || user.Aux is not CallInfo info) return false;
                for (int i = 0; i < user.In.Length; i++)
                    if (ReferenceEquals(user.In[i], load) && (i >= info.Slots.Count || info.Slots[i].Kind != ArgSlotKind.Stack))
                        return false;
            }
            return true;
        }

        foreach (Block b in fn.Blocks)
        {
            foreach (Node phi in b.Phis)
                foreach (Node input in phi.In)
                    if (stack(input, out int at) && at >= storage && at < end)
                        return Bail(1);
            foreach (Node n in b.Nodes)
            {
                if (n.Dead) continue;
                if (n.Op is Op.Load or Op.Store)
                {
                    int size = n.Op == Op.Load ? n.Type.Bytes() : n.In[1].Type.Bytes();
                    if (stack(n.In[0], out int at))
                    {
                        if (at + size <= storage || at >= end)
                        {
                            // elsewhere in the frame
                        }
                        else if (n.Op == Op.Load && size == 8 && OnlyPassed(n))
                        {
                            // not a question to the stack
                        }
                        else if (at == counter && size == 4) accesses[n] = new Access { Node = n, IsStore = n.Op == Op.Store, IsCount = true };
                        // The count zeroed together with the padding after it.
                        else if (at == counter && size == 8 && n.Op == Op.Store && n.In[1].IsConstValue(0))
                            accesses[n] = new Access { Node = n, IsStore = true, IsCount = true };
                        else if (at < counter && size == 8 && (at - storage) % 8 == 0 && at >= storage)
                            accesses[n] = new Access { Node = n, IsStore = n.Op == Op.Store, Bias = (at - storage) / 8 };
                        else
                        {
                            Trace?.Invoke($"stack at {storage}, count at {counter}: {n.Op} of {size} bytes at {at} (value {(n.Op == Op.Store ? Function.Describe(n.In[1]) : "")})");
                            return Bail(2);
                        }
                    }
                    else
                    {
                        var path = new List<Node>();
                        if (indexed(n.In[0], out int s, out int c, out Node countLoad, out int bias, path) && c == counter)
                        {
                            if (s != storage || size != 8) return Bail(3);
                            accesses[n] = new Access { Node = n, IsStore = n.Op == Op.Store, CountLoad = countLoad, Bias = bias };
                            inner.UnionWith(path);
                        }
                    }
                    if (n.Op == Op.Store && stack(n.In[1], out int kept) && kept >= storage && kept < end) return Bail(4);
                }
                else if (OperationOf(n, helpers) is var operation && operation != HelperKind.None && IntArgument(n, 0) is { } self &&
                         stack(self, out int selfAt) && selfAt >= storage && selfAt < end)
                {
                    if (selfAt != storage) return Bail(5);
                    var access = new Access { Node = n, Call = operation };
                    if (operation == HelperKind.ExceptionStackPush)
                    {
                        if (IntArgument(n, 1) is not { Type: VT.I64 } pushed || (stack(pushed, out int kept) && kept >= storage && kept < end)) return Bail(6);
                        access.Pushed = pushed;
                    }
                    else
                    {
                        callUses ??= DeadCode.Uses(fn);
                        if (callUses.TryGetValue(n, out List<Node>? results))
                            foreach (Node result in results)
                            {
                                if (result.Op != Op.Proj) return Bail(7);
                                if (result.Imm != CallResult.IntReturn) continue;
                                if (access.Result != null) return Bail(8);
                                access.Result = callUses.ContainsKey(result) ? result : null;
                            }
                    }
                    // Its other arguments are whatever the registers held; only the first is the stack.
                    for (int i = 0; i < n.In.Length; i++)
                        if (!ReferenceEquals(n.In[i], self) && stack(n.In[i], out int other) && other >= storage && other < end)
                            return Bail(9);
                    accesses[n] = access;
                }
                else
                {
                    // The stack's own memory handed to anything else: not ours to reason about.
                    for (int i = 0; i < n.In.Length; i++)
                        if (stack(n.In[i], out int at) && at >= storage && at < end && !(n.Op == Op.Add && i == 0 && n.In[1].IsConst))
                            return Bail(10);
                }
            }
        }
        if (!accesses.Values.Any(a => !a.IsCount)) return Bail(11);

        // The count is only ever stored back, changed by a constant, or used as an index.
        foreach (Access a in accesses.Values)
            if (a.Call == HelperKind.None && a.IsCount && a.IsStore && a.Node.In[1] is { Op: Op.Add } sum && sum.In[1].IsConst &&
                accesses.TryGetValue(sum.In[0], out Access? from) && from is { IsCount: true, IsStore: false })
                inner.Add(sum);
        var uses = DeadCode.Uses(fn);
        foreach (Node n in inner.Concat(accesses.Values.Where(a => a.IsCount && !a.IsStore).Select(a => a.Node)))
        {
            if (!uses.TryGetValue(n, out List<Node>? users)) continue;
            foreach (Node user in users)
            {
                if (inner.Contains(user)) continue;
                if (!accesses.TryGetValue(user, out Access? access) || access.Call != HelperKind.None) return Bail(12);
                bool asAddress = ReferenceEquals(user.In[0], n) && !access.IsCount;
                bool asCount = access.IsCount && access.IsStore && ReferenceEquals(user.In[1], n);
                if (!asAddress && !asCount) return Bail(13);
                if (asAddress && access.IsStore && ReferenceEquals(user.In[1], n)) return Bail(14);
            }
        }

        // 2. Follow the count and the entries through the function.
        var cfg = new Cfg(fn);
        var blockSymbol = new Dictionary<Block, int>();
        for (int i = 0; i < fn.Blocks.Count; i++) blockSymbol[fn.Blocks[i]] = 2 + i;
        int StoreSymbol(Node store) => 0x100000 + store.Id;

        bool Changes(Block b) => b.Nodes.Any(n => !n.Dead && accesses.TryGetValue(n, out Access? a) && a.Changes);
        bool Protects(int region, Block b)
        {
            for (int s = b.Scope, guard = 0; s >= 0 && guard < 64; guard++, s = fn.TryRegions[s >> 1].Outer)
                if (s == 2 * region) return true;
            return false;
        }
        // Handlers: entered from anywhere in their region. With the stack untouched in the region that is the
        // state at the region's gate; otherwise the count is some unknown value and no entry is known.
        var handlers = new Dictionary<Block, (Block Gate, bool Dirty)>();
        foreach (var (gate, region) in fn.TryGates())
            handlers[gate.Succs[0]] = (gate, fn.Blocks.Any(b => Protects(region, b) && Changes(b)));

        var outStates = new Dictionary<Block, State>();
        var forwarded = new Dictionary<Node, Node>();
        bool failed = false;

        State? In(Block b)
        {
            if (ReferenceEquals(b, fn.Entry)) return new State { Count = new Count(1, 0) };
            if (handlers.TryGetValue(b, out var handler))
            {
                if (handler.Dirty) return new State { Count = new Count(blockSymbol[b], 0) };
                return outStates.TryGetValue(handler.Gate, out State? atGate) ? atGate.Clone() : null;
            }
            State? merged = null;
            foreach (Block p in b.Preds)
            {
                if (!outStates.TryGetValue(p, out State? o)) continue;
                if (merged == null)
                {
                    merged = o.Clone();
                    continue;
                }
                if (merged.Count != o.Count)
                {
                    merged.Count = new Count(blockSymbol[b], 0);
                    merged.Entries.Clear();
                    continue;
                }
                foreach (var key in merged.Entries.Keys.ToList())
                    if (!o.Entries.TryGetValue(key, out Node? other) || !ReferenceEquals(other, merged.Entries[key]))
                        merged.Entries.Remove(key);
            }
            // Once the count had to be given a name of this block's, entries of other names say nothing.
            if (merged != null && merged.Count.Symbol == blockSymbol[b])
                foreach (var key in merged.Entries.Keys.Where(k => k.Symbol != blockSymbol[b]).ToList())
                    merged.Entries.Remove(key);
            return merged;
        }

        void Step(Block b, State state, bool record)
        {
            var seen = new Dictionary<Node, Count>(); // count loads of this block -> what they read
            foreach (Node n in b.Nodes)
            {
                if (n.Dead || !accesses.TryGetValue(n, out Access? a)) continue;
                if (a.Call == HelperKind.ExceptionStackPush)
                {
                    foreach (var other in state.Entries.Keys.Where(k => k.Symbol != state.Count.Symbol).ToList()) state.Entries.Remove(other);
                    state.Entries[(state.Count.Symbol, state.Count.Delta)] = a.Pushed!;
                    state.Count = new Count(state.Count.Symbol, state.Count.Delta + 1);
                    continue;
                }
                if (a.Call != HelperKind.None)
                {
                    var top = (state.Count.Symbol, state.Count.Delta - 1);
                    if (record && a.Result != null)
                    {
                        if (state.Entries.TryGetValue(top, out Node? value)) forwarded[a.Result] = value;
                        else failed = true;
                    }
                    if (a.Call == HelperKind.ExceptionStackPop)
                    {
                        state.Entries.Remove(top);
                        state.Count = new Count(state.Count.Symbol, state.Count.Delta - 1);
                    }
                    continue;
                }
                if (a.IsCount)
                {
                    if (!a.IsStore)
                    {
                        seen[n] = state.Count;
                        continue;
                    }
                    Node value = n.In[1];
                    if (value.IsConst) state.Count = new Count(0, (int)IrBuilder.SImm(value));
                    else if (value.Op == Op.Add && value.In[1].IsConst && seen.TryGetValue(value.In[0], out Count old))
                        state.Count = new Count(old.Symbol, old.Delta + (int)IrBuilder.SImm(value.In[1]));
                    else if (seen.TryGetValue(value, out Count same)) state.Count = same;
                    else state.Count = new Count(StoreSymbol(n), 0);
                    continue;
                }
                (int Symbol, int Index) key;
                if (a.CountLoad == null) key = (0, a.Bias);
                else if (seen.TryGetValue(a.CountLoad, out Count at)) key = (at.Symbol, at.Delta + a.Bias);
                else
                {
                    // An index read in another block: not followed.
                    if (a.IsStore) state.Entries.Clear();
                    else if (record) failed = true;
                    continue;
                }
                if (a.IsStore)
                {
                    foreach (var other in state.Entries.Keys.Where(k => k.Symbol != key.Symbol).ToList()) state.Entries.Remove(other);
                    state.Entries[key] = n.In[1];
                }
                else if (record)
                {
                    if (state.Entries.TryGetValue(key, out Node? pushed)) forwarded[n] = pushed;
                    else failed = true;
                }
            }
        }

        bool moving = true;
        for (int round = 0; moving && round < 40; round++)
        {
            moving = false;
            foreach (Block b in cfg.ReversePostOrder)
            {
                State? state = In(b);
                if (state == null) continue;
                Step(b, state, record: false);
                if (!outStates.TryGetValue(b, out State? old) || !old.Same(state))
                {
                    outStates[b] = state;
                    moving = true;
                }
            }
        }
        if (moving) return Bail(16);
        foreach (Block b in cfg.ReversePostOrder)
        {
            State? state = In(b);
            if (state == null) continue;
            Step(b, state, record: true);
            if (failed) return Bail(17);
        }

        // 3. Every read is a pushed value: the reads become those values, the rest goes.
        Node Final(Node n)
        {
            for (int guard = 0; guard < 64 && forwarded.TryGetValue(n, out Node? next); guard++) n = next;
            return n;
        }
        foreach (Block b in fn.Blocks)
        {
            foreach (Node n in b.Phis)
                for (int i = 0; i < n.In.Length; i++) n.In[i] = Final(n.In[i]);
            foreach (Node n in b.Nodes)
                for (int i = 0; i < n.In.Length; i++) n.In[i] = Final(n.In[i]);
        }
        foreach (Access a in accesses.Values)
        {
            if (a.IsCount && a.IsStore && a.Call == HelperKind.None && a.Node.In[1].Type == VT.I64)
            {
                // The count was zeroed together with the four bytes after it: those are still zeroed.
                Block? home = fn.Blocks.FirstOrDefault(b => b.Nodes.Contains(a.Node));
                if (home != null)
                {
                    Node offset = fn.NewNode(Op.Const, VT.I64, null);
                    offset.Imm = counter + 4;
                    Node address = fn.NewNode(Op.Add, VT.I64, home, sp0, offset);
                    home.Nodes.Insert(home.Nodes.IndexOf(a.Node), address);
                    a.Node.In = [address, fn.NewNode(Op.Const, VT.I32, null)];
                    continue;
                }
            }
            a.Node.Dead = true;
            if (a.Call != HelperKind.None && uses.TryGetValue(a.Node, out List<Node>? results))
                foreach (Node result in results) result.Dead = true;
        }
        foreach (Block b in fn.Blocks) b.Nodes.RemoveAll(n => n.Dead);
        return true;
    }
}
