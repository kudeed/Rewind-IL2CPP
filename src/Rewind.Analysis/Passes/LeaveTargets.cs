using Rewind.Analysis.Ir;
using Rewind.Analysis.X64;

namespace Rewind.Analysis.Passes;

/// <summary>
/// Up to Unity 2020, IL2CPP leaves a try statement through its finally handler by number. Each way out pushes
/// where it is headed on a small stack of numbers in the frame ("__leave_targets": some ints followed by their
/// count) and goes to the clean-up code; behind it the code asks for the top of that stack and jumps there.
/// The C++ compiler copies the clean-up code to the ways out but keeps one copy of the asking, so the machine
/// code finds its way on from numbers in memory - which is nothing a managed program does.
///
/// Every number pushed is a constant and the count starts from a constant, so along any one path the whole
/// stack is known. Where paths with different stacks meet and the stack is asked afterwards, the block they
/// meet in is given back to each way in: they were separate before the compiler merged them. Once every
/// question has one answer the reads are those numbers, the branches on them go one way, and what is left is
/// each way out with the clean-up code and its own continuation - the shape a finally handler is recovered from.
///
/// All of it is tried on a copy of the function first: nothing changes unless every read of an entry is
/// answered, nothing else can reach the stack's memory, and its address goes nowhere.
/// </summary>
public static class LeaveTargets
{
    /// <summary>When set, told why a stack was left alone (for debugging). REWIND_LEAVE_TRACE sends it to the error stream.</summary>
    public static Action<string>? Trace = Environment.GetEnvironmentVariable("REWIND_LEAVE_TRACE") != null ? text => Console.Error.WriteLine("[leave] " + text) : null;

    private const int Reach = 64, MaxSplits = 24, MaxBlocks = 24, MaxNodes = 600, MaxAdded = 160, MaxWays = 8, MaxRounds = 60;

    public static bool Run(Function fn)
    {
        if (fn.TryRegions.Count == 0 || !fn.Params.ContainsKey(X64Lifter.VarRsp)) return false;
        bool changed = false;
        foreach (int counter in Counters(fn))
        {
            if (!Resolve(Copy(fn), counter)) continue;
            changed |= Resolve(fn, counter);
        }
        return changed;
    }

    // ---- addresses in the frame ----

    private static bool Fixed(Node sp0, Node n, out int offset)
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

    /// <summary>Stack pointer + constant + 4 * index. The sums in between and the scaled index go to path.</summary>
    private static bool Indexed(Node sp0, Node address, out int offset, out Node index, List<Node>? path)
    {
        offset = 0;
        index = null!;
        if (address.Op != Op.Add) return false;
        long k = 0;
        Node? scaled = null;
        bool hasSp = false;
        var sums = new List<Node>();
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
                sums.Add(n);
                work.Push(n.In[0]);
                work.Push(n.In[1]);
            }
            else if (scaled != null) return false;
            else scaled = n;
        }
        if (!hasSp || scaled == null || k is <= -0x4000000 or >= 0x4000000) return false;
        if (scaled.Op == Op.Mul && scaled.In[1].IsConstValue(4)) index = scaled.In[0];
        else if (scaled.Op == Op.Shl && scaled.In[1].IsConst && scaled.In[1].UImm == 2) index = scaled.In[0];
        else return false;
        offset = (int)k;
        if (path != null)
        {
            path.AddRange(sums);
            path.Add(scaled);
        }
        return true;
    }

    /// <summary>True when the value is made of constants and of what is read from 4-byte frame slots (which go to slots).</summary>
    private static bool FromCount(Node sp0, Node n, HashSet<int> slots, HashSet<Node> seen, int depth)
    {
        if (!seen.Add(n)) return true;
        if (depth > 32) return false;
        switch (n.Op)
        {
            case Op.Const:
                return true;
            case Op.ZExt or Op.SExt or Op.Trunc:
                return FromCount(sp0, n.In[0], slots, seen, depth + 1);
            case Op.Add or Op.Sub when n.In[1].IsConst:
                return FromCount(sp0, n.In[0], slots, seen, depth + 1);
            case Op.Phi:
                foreach (Node input in n.In)
                    if (!FromCount(sp0, input, slots, seen, depth + 1))
                        return false;
                return true;
            case Op.Load when n.Type == VT.I32 && Fixed(sp0, n.In[0], out int at):
                slots.Add(at);
                return true;
            default:
                return false;
        }
    }

    /// <summary>The frame slots that count a stack of numbers: what indexes a read of an int from the frame.</summary>
    private static List<int> Counters(Function fn)
    {
        Node sp0 = fn.Params[X64Lifter.VarRsp];
        var counters = new List<int>();
        foreach (Block b in fn.Blocks)
            foreach (Node n in b.Nodes)
            {
                if (n.Dead || n.Op != Op.Load || n.Type != VT.I32 || !Indexed(sp0, n.In[0], out _, out Node index, null)) continue;
                var slots = new HashSet<int>();
                if (!FromCount(sp0, index, slots, [], 0) || slots.Count != 1) continue;
                int counter = slots.First();
                if (!counters.Contains(counter)) counters.Add(counter);
            }
        return counters;
    }

    // ---- what is known about the stack ----

    private readonly record struct Val(bool Known, long Value)
    {
        public static Val Of(long value) => new(true, value);
    }

    private enum Rank { Top, Known, Unknown }

    private readonly record struct Got(Rank Rank, long Value)
    {
        public static readonly Got Top = new(Rank.Top, 0), Unknown = new(Rank.Unknown, 0);
        public static Got Of(long value) => new(Rank.Known, value);
        public bool Known => Rank == Rank.Known;
    }

    private sealed class State
    {
        public Val Count;
        public Dictionary<int, long> Cells = [];

        public State Clone() => new() { Count = Count, Cells = new Dictionary<int, long>(Cells) };

        /// <summary>Keeps what both say. True when that is less than this said before.</summary>
        public bool Meet(State other)
        {
            bool less = false;
            if (Count.Known && Count != other.Count)
            {
                Count = default;
                less = true;
            }
            foreach (int cell in Cells.Keys.ToList())
                if (!other.Cells.TryGetValue(cell, out long value) || value != Cells[cell])
                {
                    Cells.Remove(cell);
                    less = true;
                }
            return less;
        }
    }

    private enum Kind { CountLoad, CellLoad, Store, IndexedLoad, IndexedStore, Foreign }

    private sealed class Access
    {
        public Kind Kind;
        /// <summary>The frame offset; for an indexed access, the constant part of it.</summary>
        public int Offset;
        public int Size;
        public Node? Index;
        /// <summary>
        /// Set when the index is made of constants alone (the compiler knew the count on that path): the access
        /// is the stack's only where it turns out to land in it.
        /// </summary>
        public bool Perhaps;
    }

    private sealed class Analysis(Function fn, Node sp0, int counter)
    {
        private readonly Dictionary<Node, Access> _accesses = [];
        private readonly Dictionary<Node, Block> _home = [];
        /// <summary>The loads reached so far: what each reads.</summary>
        private readonly Dictionary<Node, Val> _read = [];
        /// <summary>Indexed loads: the frame offset each reads (int.MinValue: not always the same).</summary>
        private readonly Dictionary<Node, int> _cell = [];
        private readonly Dictionary<Block, State> _in = [], _out = [];
        /// <summary>Branches reached so far: the one successor they go to (-1: either).</summary>
        private readonly Dictionary<Block, int> _only = [];
        private readonly Dictionary<Block, (Block Gate, int Region)> _handlers = [];
        /// <summary>Per try region: the stack wherever an exception can be raised in it.</summary>
        private readonly Dictionary<int, State> _raised = [];
        private readonly HashSet<int> _canRaise = [];
        private readonly HashSet<Node> _paths = [];
        private Dictionary<Node, List<Node>>? _uses;
        private Cfg _cfg = null!;

        private Dictionary<Node, List<Node>> Uses => _uses ??= DeadCode.Uses(fn);

        /// <summary>A read whose only use is to be handed to calls as a stack argument they do not take.</summary>
        private bool OnlyPassed(Node load)
        {
            if (!Uses.TryGetValue(load, out List<Node>? users)) return true;
            foreach (Node user in users)
            {
                if (user.Op is not (Op.Call or Op.TailCall) || user.Aux is not CallInfo info) return false;
                for (int i = 0; i < user.In.Length; i++)
                    if (ReferenceEquals(user.In[i], load) && (i >= info.Slots.Count || info.Slots[i].Kind != ArgSlotKind.Stack))
                        return false;
            }
            return true;
        }

        private IEnumerable<int> RegionsAround(Block b)
        {
            for (int s = b.Scope, guard = 0; s >= 0 && guard < 64; guard++, s = fn.TryRegions[s >> 1].Outer)
                if ((s & 1) == 0)
                    yield return s >> 1;
        }

        private bool Collect()
        {
            foreach (Block b in fn.Blocks)
            {
                foreach (Node n in b.Phis) _home[n] = b;
                foreach (Node n in b.Nodes)
                {
                    _home[n] = b;
                    if (n.Dead) continue;
                    if (n.Op is Op.Call or Op.TailCall)
                        foreach (int region in RegionsAround(b))
                            _canRaise.Add(region);
                    if (n.Op is not (Op.Load or Op.Store)) continue;
                    bool store = n.Op == Op.Store;
                    int size = (store ? n.In[1].Type : n.Type).Bytes();
                    if (Fixed(sp0, n.In[0], out int at))
                    {
                        if (at + size <= counter - Reach || at >= counter + 4) continue;
                        // Whole ints of the stack, or constants written over two of them at once.
                        bool whole = at <= counter && (counter - at) % 4 == 0 && (size == 4 || (size == 8 && store && n.In[1].IsConst));
                        Kind kind;
                        if (whole) kind = store ? Kind.Store : at == counter ? Kind.CountLoad : Kind.CellLoad;
                        else if (!store && OnlyPassed(n)) continue;
                        else kind = Kind.Foreign;
                        _accesses[n] = new Access { Kind = kind, Offset = at, Size = size };
                    }
                    else
                    {
                        var path = new List<Node>();
                        if (!Indexed(sp0, n.In[0], out int k, out Node index, path)) continue;
                        var slots = new HashSet<int>();
                        if (!FromCount(sp0, index, slots, [], 0) || slots.Count > 1 || (slots.Count == 1 && !slots.Contains(counter))) continue;
                        bool perhaps = slots.Count == 0;
                        if (size != 4)
                        {
                            if (perhaps) continue;
                            return false;
                        }
                        if (!perhaps)
                            foreach (Node p in path)
                                if (!Fixed(sp0, p, out _))
                                    _paths.Add(p);
                        _accesses[n] = new Access { Kind = store ? Kind.IndexedStore : Kind.IndexedLoad, Offset = k, Size = size, Index = index, Perhaps = perhaps };
                    }
                }
            }
            return _accesses.Values.Any(a => a.Kind == Kind.IndexedLoad);
        }

        private static long Signed(long value, VT type)
        {
            int unused = 64 - type.Bits();
            return unused is <= 0 or >= 64 ? value : (value << unused) >> unused;
        }

        private Got Eval(Node n, int depth = 0, HashSet<Node>? open = null)
        {
            if (depth > 32) return Got.Unknown;
            switch (n.Op)
            {
                case Op.Const:
                    return Got.Of((long)n.UImm);
                case Op.Load:
                    if (_read.TryGetValue(n, out Val read)) return read.Known ? Got.Of(read.Value) : Got.Unknown;
                    return _accesses.TryGetValue(n, out Access? a) && a.Kind is Kind.CountLoad or Kind.CellLoad or Kind.IndexedLoad ? Got.Top : Got.Unknown;
                case Op.Add or Op.Sub when n.In[1].IsConst:
                {
                    Got x = Eval(n.In[0], depth + 1, open);
                    if (!x.Known) return x;
                    long k = (long)n.In[1].UImm;
                    return Got.Of((long)((ulong)(n.Op == Op.Add ? x.Value + k : x.Value - k) & n.Type.Mask()));
                }
                case Op.ZExt:
                    return Eval(n.In[0], depth + 1, open);
                case Op.SExt:
                {
                    Got x = Eval(n.In[0], depth + 1, open);
                    return x.Known ? Got.Of((long)((ulong)Signed(x.Value, n.In[0].Type) & n.Type.Mask())) : x;
                }
                case Op.Trunc:
                {
                    Got x = Eval(n.In[0], depth + 1, open);
                    return x.Known ? Got.Of((long)((ulong)x.Value & n.Type.Mask())) : x;
                }
                case Op.CmpEq or Op.CmpNe:
                {
                    Got x = Eval(n.In[0], depth + 1, open), y = Eval(n.In[1], depth + 1, open);
                    if (x.Rank == Rank.Unknown || y.Rank == Rank.Unknown) return Got.Unknown;
                    if (!x.Known || !y.Known) return Got.Top;
                    return Got.Of((x.Value == y.Value) == (n.Op == Op.CmpEq) ? 1 : 0);
                }
                case Op.Phi:
                {
                    // What the ways in reached so far agree on.
                    open ??= [];
                    if (!open.Add(n)) return Got.Top;
                    Got merged = Got.Top;
                    foreach (Node input in n.In)
                    {
                        Got x = Eval(input, depth + 1, open);
                        if (x.Rank == Rank.Top) continue;
                        if (x.Rank == Rank.Unknown || (merged.Known && merged.Value != x.Value))
                        {
                            merged = Got.Unknown;
                            break;
                        }
                        merged = x;
                    }
                    open.Remove(n);
                    return merged;
                }
                default:
                    return Got.Unknown;
            }
        }

        /// <summary>True for where an entry of the stack can be: a whole int not far before the count.</summary>
        private bool InStack(int at) => at < counter && at >= counter - Reach && (counter - at) % 4 == 0;

        private bool Feasible(Block from, Block to) =>
            !_only.TryGetValue(from, out int only) || only < 0 || ReferenceEquals(from.Succs[only], to);

        private State? Enter(Block b)
        {
            if (ReferenceEquals(b, fn.Entry)) return new State();
            if (_handlers.TryGetValue(b, out var handler))
            {
                // Entered from wherever the region can raise; from nowhere, the stack is as it was at the gate.
                if (_canRaise.Contains(handler.Region)) return _raised.TryGetValue(handler.Region, out State? raised) ? raised.Clone() : null;
                return _out.TryGetValue(handler.Gate, out State? gate) ? gate.Clone() : null;
            }
            State? merged = null;
            foreach (Block p in b.Preds)
            {
                if (!_out.TryGetValue(p, out State? o) || !Feasible(p, b)) continue;
                if (merged == null) merged = o.Clone();
                else merged.Meet(o);
            }
            return merged;
        }

        /// <summary>Lets what is kept say no more than the new finding. True when that changed it.</summary>
        private static bool Lower<TKey>(Dictionary<TKey, State> kept, TKey key, State found) where TKey : notnull
        {
            if (kept.TryGetValue(key, out State? old)) return old.Meet(found);
            kept[key] = found.Clone();
            return true;
        }

        private bool Record(Node load, Val found)
        {
            if (!_read.TryGetValue(load, out Val old))
            {
                _read[load] = found;
                return true;
            }
            if (!old.Known || old == found) return false;
            _read[load] = default;
            return true;
        }

        private void Put(State state, int at, int size, Got value)
        {
            void Set(int offset, long? part)
            {
                if (offset == counter) state.Count = part is { } count ? Val.Of(count) : default;
                else if (offset > counter) return;
                else if (part is { } cell) state.Cells[offset] = cell;
                else state.Cells.Remove(offset);
            }
            Set(at, value.Known ? value.Value & 0xFFFFFFFF : null);
            if (size == 8) Set(at + 4, value.Known ? (value.Value >> 32) & 0xFFFFFFFF : null);
        }

        private bool Sweep()
        {
            bool changed = false;
            var raised = new Dictionary<int, State>();
            foreach (Block b in _cfg.ReversePostOrder)
            {
                State? entering = Enter(b);
                if (entering == null) continue;
                changed |= Lower(_in, b, entering);
                State state = _in[b].Clone();
                foreach (Node n in b.Nodes)
                {
                    if (n.Dead) continue;
                    if (n.Op is Op.Call or Op.TailCall)
                        foreach (int region in RegionsAround(b))
                        {
                            if (raised.TryGetValue(region, out State? so)) so.Meet(state);
                            else raised[region] = state.Clone();
                        }
                    if (!_accesses.TryGetValue(n, out Access? a)) continue;
                    switch (a.Kind)
                    {
                        case Kind.CountLoad:
                            changed |= Record(n, state.Count);
                            break;
                        case Kind.CellLoad:
                            changed |= Record(n, state.Cells.TryGetValue(a.Offset, out long cell) ? Val.Of(cell) : default);
                            break;
                        case Kind.Store:
                            Put(state, a.Offset, a.Size, Eval(n.In[1]));
                            break;
                        case Kind.IndexedLoad:
                        {
                            Got index = Eval(a.Index!);
                            if (index.Rank == Rank.Top) break;
                            if (!index.Known)
                            {
                                if (!a.Perhaps) changed |= Record(n, default);
                                break;
                            }
                            int at = a.Offset + 4 * (int)Signed(index.Value, a.Index!.Type);
                            if (a.Perhaps && !InStack(at)) break;
                            if (_cell.TryGetValue(n, out int before) && before != at) at = int.MinValue;
                            _cell[n] = at;
                            changed |= Record(n, state.Cells.TryGetValue(at, out long entry) ? Val.Of(entry) : default);
                            break;
                        }
                        case Kind.IndexedStore:
                        {
                            Got index = Eval(a.Index!);
                            if (index.Known)
                            {
                                int at = a.Offset + 4 * (int)Signed(index.Value, a.Index!.Type);
                                if (!a.Perhaps || InStack(at)) Put(state, at, 4, Eval(n.In[1]));
                            }
                            else if (!a.Perhaps) state.Cells.Clear();
                            break;
                        }
                    }
                }
                if (b.Terminator is { Op: Op.Branch } t && b.Succs.Count == 2)
                {
                    Got condition = Eval(t.In[0]);
                    int only = condition.Known ? condition.Value != 0 ? 0 : 1 : -1;
                    if (!_only.TryGetValue(b, out int known))
                    {
                        _only[b] = only;
                        changed = true;
                    }
                    else if (known >= 0 && known != only)
                    {
                        _only[b] = -1;
                        changed = true;
                    }
                }
                changed |= Lower(_out, b, state);
            }
            foreach (var (region, state) in raised) changed |= Lower(_raised, region, state);
            return changed;
        }

        public bool Run()
        {
            if (!Collect())
            {
                Trace?.Invoke($"leave targets of 0x{fn.Address:X} counted at {counter}: not a stack of numbers");
                return false;
            }
            _cfg = new Cfg(fn);
            foreach (var (gate, region) in fn.TryGates()) _handlers[gate.Succs[0]] = (gate, region);
            for (int round = 0; round < MaxRounds; round++)
                if (!Sweep())
                    return true;
            Trace?.Invoke($"leave targets counted at {counter}: not settled in {MaxRounds} rounds");
            return false;
        }

        // ---- where paths with different stacks meet ----

        /// <summary>The block where what a path knew of the count (or of one entry) is lost to another path.</summary>
        private Block? Lost(Block from, int? cell)
        {
            bool Has(State s) => cell is { } c ? s.Cells.ContainsKey(c) : s.Count.Known;
            var seen = new HashSet<Block>();
            var work = new Queue<Block>();
            work.Enqueue(from);
            while (work.Count > 0)
            {
                Block b = work.Dequeue();
                if (!seen.Add(b) || !_in.TryGetValue(b, out State? entering) || Has(entering)) continue;
                if (ReferenceEquals(b, fn.Entry) || _handlers.ContainsKey(b)) continue;
                foreach (Block p in b.Preds)
                    if (Feasible(p, b) && _out.TryGetValue(p, out State? o) && Has(o))
                        return b;
                foreach (Block p in b.Preds) work.Enqueue(p);
            }
            return null;
        }

        private Block? Blame(Node n, int depth)
        {
            if (depth > 24) return null;
            switch (n.Op)
            {
                case Op.Phi:
                {
                    bool some = false;
                    foreach (Node input in n.In)
                    {
                        Got x = Eval(input);
                        if (x.Known) some = true;
                        else if (x.Rank == Rank.Unknown && Blame(input, depth + 1) is { } deeper) return deeper;
                    }
                    return some ? _home.GetValueOrDefault(n) : null;
                }
                case Op.Add or Op.Sub or Op.ZExt or Op.SExt or Op.Trunc:
                    return Blame(n.In[0], depth + 1);
                case Op.Load when _accesses.TryGetValue(n, out Access? a) && _home.TryGetValue(n, out Block? home):
                    switch (a.Kind)
                    {
                        case Kind.CountLoad:
                            return Lost(home, null);
                        case Kind.CellLoad:
                            return Lost(home, a.Offset);
                        case Kind.IndexedLoad:
                            Got index = Eval(a.Index!);
                            return index.Known ? Lost(home, a.Offset + 4 * (int)Signed(index.Value, a.Index!.Type)) : Blame(a.Index!, depth + 1);
                    }
                    return null;
                default:
                    return null;
            }
        }

        /// <summary>
        /// A read that has no one answer yet, as the block that asks and the block before it where paths that
        /// knew different stacks meet.
        /// </summary>
        public (Block Meet, Block Asks)? NextSplit(HashSet<(Block, Block)> refused)
        {
            var asked = new HashSet<int>(_cell.Values);
            foreach (Block b in _cfg.ReversePostOrder)
                foreach (Node n in b.Nodes)
                {
                    if (n.Dead || !_accesses.TryGetValue(n, out Access? a) || !_read.TryGetValue(n, out Val read) || read.Known) continue;
                    if (a.Kind is not (Kind.CountLoad or Kind.CellLoad or Kind.IndexedLoad)) continue;
                    if (a.Kind == Kind.CellLoad && !asked.Contains(a.Offset)) continue;
                    if (Blame(n, 0) is { } at && !refused.Contains((at, b))) return (at, b);
                }
            return null;
        }

        // ---- the outcome ----

        private static readonly bool Detailed = Environment.GetEnvironmentVariable("REWIND_LEAVE_DETAIL") != null;

        /// <summary>The function with what is known of the stack on entry to each block (for debugging).</summary>
        private string Describe()
        {
            static string Show(State s) =>
                $"count {(s.Count.Known ? s.Count.Value.ToString() : "?")}, entries {{{string.Join(", ", s.Cells.OrderBy(c => c.Key).Select(c => $"{c.Key}: 0x{c.Value:X}"))}}}";
            var text = new System.Text.StringBuilder();
            foreach (Block b in fn.Blocks)
            {
                text.Append($"{b}: preds {string.Join(",", b.Preds)} succs {string.Join(",", b.Succs)}");
                text.Append(_in.TryGetValue(b, out State? entering) ? "  in: " + Show(entering) : "  not reached");
                if (_only.TryGetValue(b, out int only) && only >= 0) text.Append($"  goes to {b.Succs[only]} only");
                text.AppendLine();
                foreach (Node n in b.Phis)
                    if (!n.Dead && n.Type is VT.I32 or VT.I64 && Eval(n) is { Rank: not Rank.Unknown } merged)
                        text.AppendLine($"    {Function.Describe(n)}   = {(merged.Known ? merged.Value.ToString() : "top")}");
                foreach (Node n in b.Nodes)
                {
                    if (n.Dead || !_accesses.TryGetValue(n, out Access? a)) continue;
                    text.Append($"    {Function.Describe(n)}   {a.Kind} at {a.Offset}");
                    if (_read.TryGetValue(n, out Val read)) text.Append(read.Known ? $" reads {read.Value}" : " reads ?");
                    if (_cell.TryGetValue(n, out int cell)) text.Append($" (entry at {cell})");
                    text.AppendLine();
                    for (Node? x = a.Index; x != null && x.In.Length != 0; x = x.In[0])
                        text.AppendLine($"        index: {Function.Describe(x)}{(x.Op == Op.Phi ? " in " + _home.GetValueOrDefault(x) : "")}");
                }
            }
            return text.ToString();
        }

        /// <summary>
        /// With the reads constant, what was computed from them is: comparisons, choices between two values,
        /// widened and narrowed copies. They are worked out here so that nothing of the stack is left to see.
        /// </summary>
        private void Fold()
        {
            for (int round = 0; round < 16; round++)
            {
                var folded = new Dictionary<Node, Node>();
                foreach (Block b in fn.Blocks)
                    foreach (Node n in b.Nodes)
                    {
                        if (n.Dead) continue;
                        if (n.Op == Op.Select && n.In[0].IsConst) folded[n] = n.In[0].UImm != 0 ? n.In[1] : n.In[2];
                        else if (n.Op is Op.CmpEq or Op.CmpNe or Op.ZExt or Op.SExt or Op.Trunc || (n.Op is Op.Add or Op.Sub && n.Type == VT.I32))
                        {
                            if (!n.In.All(i => i.IsConst) || Eval(n) is not { Known: true } value) continue;
                            Node constant = fn.NewNode(Op.Const, n.Type, null);
                            constant.Imm = (long)((ulong)value.Value & n.Type.Mask());
                            folded[n] = constant;
                        }
                    }
                if (folded.Count == 0) return;
                foreach (Block b in fn.Blocks)
                {
                    foreach (Node n in b.Phis)
                        for (int i = 0; i < n.In.Length; i++)
                            if (folded.TryGetValue(n.In[i], out Node? simpler))
                                n.In[i] = simpler;
                    foreach (Node n in b.Nodes)
                        for (int i = 0; i < n.In.Length; i++)
                            if (folded.TryGetValue(n.In[i], out Node? simpler))
                                n.In[i] = simpler;
                    b.Nodes.RemoveAll(n =>
                    {
                        if (!folded.ContainsKey(n)) return false;
                        n.Dead = true;
                        return true;
                    });
                }
            }
        }

        public bool Commit()
        {
            // Every entry asked for has its answer, and the entries lie where a stack before the count would.
            int low = counter;
            foreach (var (load, a) in _accesses)
            {
                if (a.Kind != Kind.IndexedLoad || !_read.TryGetValue(load, out Val read)) continue;
                if (!read.Known || !_cell.TryGetValue(load, out int at) || at >= counter || at < counter - Reach || (counter - at) % 4 != 0)
                {
                    Trace?.Invoke($"leave targets of 0x{fn.Address:X} counted at {counter}: %{load.Id} has no one answer{(Detailed ? "\n" + Describe() : "")}");
                    return false;
                }
                low = Math.Min(low, at);
            }
            if (low == counter)
            {
                Trace?.Invoke($"leave targets of 0x{fn.Address:X} counted at {counter}: no entry is read on a path that is taken{(Detailed ? "\n" + Describe() : "")}");
                return false;
            }

            // Nothing else reads or writes that memory, and its address goes nowhere.
            foreach (var (n, a) in _accesses)
                if (a.Kind == Kind.Foreign && a.Offset < counter + 4 && a.Offset + a.Size > low)
                {
                    Trace?.Invoke($"leave targets counted at {counter}: %{n.Id} reaches into the stack");
                    return false;
                }
            foreach (var (x, users) in Uses)
            {
                bool path = _paths.Contains(x);
                if (!path && !(Fixed(sp0, x, out int at) && at >= low && at < counter + 4)) continue;
                foreach (Node user in users)
                {
                    if (user.Op == Op.Load && ReferenceEquals(user.In[0], x)) continue;
                    if (user.Op == Op.Store && ReferenceEquals(user.In[0], x) && !ReferenceEquals(user.In[1], x)) continue;
                    if (user.Op == Op.Add && (_paths.Contains(user) || (!path && user.In[1].IsConst))) continue;
                    Trace?.Invoke($"leave targets counted at {counter}: the address %{x.Id} is used by %{user.Id}");
                    return false;
                }
            }

            var replaced = new Dictionary<Node, Node>();
            foreach (var (load, read) in _read)
            {
                if (!read.Known || (_accesses[load].Kind == Kind.CellLoad && _accesses[load].Offset < low)) continue;
                Node constant = fn.NewNode(Op.Const, load.Type, null);
                constant.Imm = (long)((ulong)read.Value & load.Type.Mask());
                replaced[load] = constant;
            }
            foreach (Block b in fn.Blocks)
            {
                foreach (Node n in b.Phis)
                    for (int i = 0; i < n.In.Length; i++)
                        if (replaced.TryGetValue(n.In[i], out Node? constant))
                            n.In[i] = constant;
                foreach (Node n in b.Nodes)
                    for (int i = 0; i < n.In.Length; i++)
                        if (replaced.TryGetValue(n.In[i], out Node? constant))
                            n.In[i] = constant;
                // A branch on the stack that goes one way says so outright.
                if (_only.TryGetValue(b, out int only) && only >= 0 && b.Terminator is { Op: Op.Branch } t && b.Succs.Count == 2 && !t.In[0].IsConst)
                {
                    Node way = fn.NewNode(Op.Const, VT.I1, null);
                    way.Imm = only == 0 ? 1 : 0;
                    t.In[0] = way;
                }
            }
            Fold();
            DeadCode.Run(fn);
            return true;
        }
    }

    private static bool Resolve(Function fn, int counter)
    {
        Node sp0 = fn.Params[X64Lifter.VarRsp];
        var refused = new HashSet<(Block, Block)>();
        int most = fn.Blocks.Count + MaxAdded;
        for (int guard = 0; guard < 4 * MaxSplits; guard++)
        {
            var analysis = new Analysis(fn, sp0, counter);
            if (!analysis.Run()) return false;
            if (analysis.NextSplit(refused) is not { } split) return analysis.Commit();
            if (refused.Count < MaxSplits && Region(fn, split.Meet, split.Asks) is { } region && fn.Blocks.Count + region.Count * (split.Meet.Preds.Count - 1) <= most)
            {
                Trace?.Invoke($"leave targets of 0x{fn.Address:X}: {split.Meet} to {split.Asks} given to each way in ({region.Count} blocks, {split.Meet.Preds.Count(p => !region.Contains(p))} ways)");
                Separate(fn, split.Meet, region);
            }
            else Trace?.Invoke($"leave targets of 0x{fn.Address:X}: {split.Meet} to {split.Asks} cannot be given to each way in");
            // Asked for again, the same two blocks have nothing more to give.
            refused.Add(split);
        }
        return false;
    }

    // ---- giving the code between a meeting of paths and a question back to each path ----

    /// <summary>
    /// The blocks on the ways from where the paths meet to where the stack is asked: the clean-up code they
    /// share. Loops among them belong to it; a try statement in between ends the attempt (null), and so does
    /// anything that would make the copies ill-formed.
    /// </summary>
    private static HashSet<Block>? Region(Function fn, Block meet, Block asks)
    {
        bool Barrier(Block b)
        {
            if (ReferenceEquals(b, fn.Entry)) return true;
            if (b.Terminator is { Op: Op.Branch } own && Function.IsTryEntry(own.In[0])) return true;
            foreach (Block p in b.Preds)
                if (p.Terminator is { Op: Op.Branch } t && Function.IsTryEntry(t.In[0]))
                    return true;
            return false;
        }
        HashSet<Block> Reach(Block from, Func<Block, List<Block>> next)
        {
            var seen = new HashSet<Block> { from };
            var work = new Stack<Block>();
            work.Push(from);
            while (work.Count > 0)
                foreach (Block b in next(work.Pop()))
                    if (!Barrier(b) && seen.Add(b))
                        work.Push(b);
            return seen;
        }
        if (Barrier(meet) || Barrier(asks)) return null;
        HashSet<Block> region = Reach(meet, b => b.Succs);
        region.IntersectWith(Reach(asks, b => b.Preds));
        region.Add(meet);
        if (region.Count > MaxBlocks) return null;
        int nodes = 0;
        foreach (Block b in region)
        {
            nodes += b.Nodes.Count;
            if (b.Preds.Distinct().Count() != b.Preds.Count) return null;
            foreach (Node phi in b.Phis)
                if (!phi.Dead && phi.In.Length != b.Preds.Count)
                    return null;
        }
        if (nodes > MaxNodes) return null;
        // Paths come in at the meeting block: at least two from outside.
        int ways = meet.Preds.Count(p => !region.Contains(p));
        return ways is >= 2 and <= MaxWays ? region : null;
    }

    private static void Separate(Function fn, Block meet, HashSet<Block> region)
    {
        List<Block> order = fn.Blocks.Where(region.Contains).ToList();
        List<Block> ways = meet.Preds.Where(p => !region.Contains(p)).ToList();

        // What the region computes and code after it reads: each of those readers needs the value of the copy
        // its path came through.
        var home = new Dictionary<Node, Block>();
        foreach (Block b in fn.Blocks)
        {
            foreach (Node n in b.Phis) home[n] = b;
            foreach (Node n in b.Nodes) home[n] = b;
        }
        var uses = DeadCode.Uses(fn);
        var exposed = new List<(Node Value, List<Node> Readers)>();
        foreach (Block b in order)
            foreach (Node value in b.Phis.Concat(b.Nodes))
            {
                if (value.Dead || !uses.TryGetValue(value, out List<Node>? users)) continue;
                List<Node> readers = users.Where(u => home.TryGetValue(u, out Block? at) && !region.Contains(at)).Distinct().ToList();
                if (readers.Count != 0) exposed.Add((value, readers));
            }

        var copies = new List<(Dictionary<Block, Block> Blocks, Dictionary<Node, Node> Values)>();
        for (int way = 1; way < ways.Count; way++)
        {
            Block entry = ways[way];
            var blocks = new Dictionary<Block, Block>();
            var values = new Dictionary<Node, Node>();
            Node Of(Node n) => values.GetValueOrDefault(n, n);
            foreach (Block b in order)
            {
                var c = new Block { Start = b.Start, End = b.End, Scope = b.Scope };
                blocks[b] = c;
                foreach (Node n in b.Phis.Concat(b.Nodes))
                {
                    if (n.Dead) continue;
                    Node x = fn.NewNode(n.Op, n.Type, c);
                    x.Imm = n.Imm;
                    x.Addr = n.Addr;
                    values[n] = x;
                    (n.Op == Op.Phi ? c.Phis : c.Nodes).Add(x);
                }
            }
            foreach (Block b in order)
            {
                Block c = blocks[b];
                // The copy is entered from the copies of the region's own blocks, and at the top by this way in.
                var kept = new List<int>();
                for (int i = 0; i < b.Preds.Count; i++)
                {
                    Block p = b.Preds[i];
                    if (region.Contains(p)) c.Preds.Add(blocks[p]);
                    else if (ReferenceEquals(b, meet) && ReferenceEquals(p, entry)) c.Preds.Add(p);
                    else continue;
                    kept.Add(i);
                }
                foreach (Node n in b.Phis)
                    if (!n.Dead)
                        values[n].In = kept.Select(i => Of(n.In[i])).ToArray();
                foreach (Node n in b.Nodes)
                {
                    if (n.Dead) continue;
                    Node x = values[n];
                    x.In = n.In.Select(Of).ToArray();
                    x.Aux = n.Aux switch
                    {
                        CallInfo info => new CallInfo { Target = info.Target, Indirect = info.Indirect, Intrinsic = info.Intrinsic, NoReturn = info.NoReturn, Slots = [.. info.Slots] },
                        List<Block> targets => targets.Select(t => blocks.GetValueOrDefault(t, t)).ToList(),
                        _ => n.Aux,
                    };
                }
                foreach (Block s in b.Succs) c.Succs.Add(blocks.GetValueOrDefault(s, s));
            }
            // Each block after the region gets one more way in per edge, bringing the copy's values.
            foreach (Block b in order)
                foreach (Block s in b.Succs.Distinct())
                {
                    if (region.Contains(s)) continue;
                    var edges = new List<int>();
                    for (int i = 0; i < s.Preds.Count; i++)
                        if (ReferenceEquals(s.Preds[i], b))
                            edges.Add(i);
                    foreach (int edge in edges)
                    {
                        s.Preds.Add(blocks[b]);
                        foreach (Node phi in s.Phis)
                        {
                            if (phi.Dead || edge >= phi.In.Length) continue;
                            var inputs = new Node[phi.In.Length + 1];
                            phi.In.CopyTo(inputs, 0);
                            inputs[^1] = Of(phi.In[edge]);
                            phi.In = inputs;
                        }
                    }
                }
            for (int i = 0; i < entry.Succs.Count; i++)
                if (ReferenceEquals(entry.Succs[i], meet))
                    entry.Succs[i] = blocks[meet];
            if (entry.Terminator is { Op: Op.Switch, Aux: List<Block> cases })
                for (int i = 0; i < cases.Count; i++)
                    if (ReferenceEquals(cases[i], meet))
                        cases[i] = blocks[meet];
            foreach (Block b in order) fn.Blocks.Add(blocks[b]);
            copies.Add((blocks, values));
        }

        // The region itself stays for the first way in.
        for (int i = meet.Preds.Count - 1; i >= 0; i--)
        {
            if (region.Contains(meet.Preds[i]) || ReferenceEquals(meet.Preds[i], ways[0])) continue;
            meet.Preds.RemoveAt(i);
            foreach (Node phi in meet.Phis)
                if (!phi.Dead && i < phi.In.Length)
                    phi.In = [.. phi.In[..i], .. phi.In[(i + 1)..]];
        }
        for (int i = 0; i < fn.Blocks.Count; i++) fn.Blocks[i].Id = i;
        if (exposed.Count == 0) return;

        var types = exposed.Select(e => e.Value.Type).ToArray();
        var ssa = new SsaBuilder(fn, types, variable => fn.NewNode(Op.Undef, types[variable], null));
        foreach (Block b in fn.Blocks) ssa.Seal(b);
        var parts = new HashSet<Block>(region);
        for (int v = 0; v < exposed.Count; v++) ssa.Write(v, home[exposed[v].Value], exposed[v].Value);
        foreach (var (blocks, values) in copies)
        {
            parts.UnionWith(blocks.Values);
            for (int v = 0; v < exposed.Count; v++) ssa.Write(v, blocks[home[exposed[v].Value]], values[exposed[v].Value]);
        }
        for (int v = 0; v < exposed.Count; v++)
        {
            Node value = exposed[v].Value;
            foreach (Node reader in exposed[v].Readers)
            {
                Block at = home[reader];
                for (int i = 0; i < reader.In.Length; i++)
                {
                    if (!ReferenceEquals(reader.In[i], value)) continue;
                    if (reader.Op != Op.Phi) reader.In[i] = ssa.Read(v, at);
                    // A merged value takes what its way in brings; the ways in from the region and its copies
                    // already bring their own.
                    else if (i < at.Preds.Count && !parts.Contains(at.Preds[i])) reader.In[i] = ssa.Read(v, at.Preds[i]);
                }
            }
        }
        ssa.Finish();
    }

    // ---- a copy to try things on ----

    private static Function Copy(Function fn)
    {
        var copy = new Function { Address = fn.Address, End = fn.End, NextId = fn.NextId, TryRegions = fn.TryRegions };
        var blocks = new Dictionary<Block, Block>();
        foreach (Block b in fn.Blocks)
        {
            var c = new Block { Id = b.Id, Start = b.Start, End = b.End, Scope = b.Scope };
            blocks[b] = c;
            copy.Blocks.Add(c);
        }
        var nodes = new Dictionary<Node, Node>();
        var pending = new Stack<Node>();
        Node Of(Node n)
        {
            if (nodes.TryGetValue(n, out Node? c)) return c;
            c = new Node { Id = n.Id, Op = n.Op, Type = n.Type, Imm = n.Imm, Addr = n.Addr, Dead = n.Dead };
            if (n.Block != null) c.Block = blocks.GetValueOrDefault(n.Block);
            c.Aux = n.Aux switch
            {
                CallInfo info => new CallInfo { Target = info.Target, Indirect = info.Indirect, Intrinsic = info.Intrinsic, NoReturn = info.NoReturn, Slots = [.. info.Slots] },
                List<Block> targets => targets.Select(t => blocks.GetValueOrDefault(t, t)).ToList(),
                _ => n.Aux,
            };
            nodes[n] = c;
            pending.Push(n);
            return c;
        }
        void Close()
        {
            while (pending.Count > 0)
            {
                Node n = pending.Pop();
                var inputs = new Node[n.In.Length];
                for (int i = 0; i < inputs.Length; i++) inputs[i] = Of(n.In[i]);
                nodes[n].In = inputs;
            }
        }
        foreach (Block b in fn.Blocks)
        {
            Block c = blocks[b];
            foreach (Node n in b.Phis) c.Phis.Add(Of(n));
            foreach (Node n in b.Nodes) c.Nodes.Add(Of(n));
            foreach (Block p in b.Preds) c.Preds.Add(blocks[p]);
            foreach (Block s in b.Succs) c.Succs.Add(blocks[s]);
        }
        foreach (var (key, value) in fn.Params) copy.Params[key] = Of(value);
        foreach (var (key, value) in fn.StackParams) copy.StackParams[key] = Of(value);
        Close();
        return copy;
    }
}
