using Rewind.Analysis.Ir;
using Rewind.Analysis.X64;

namespace Rewind.Analysis.Passes;

/// <summary>
/// Gives each lifetime of a reused stack slot a place of its own.
///
/// The C++ compiler puts locals whose lifetimes do not overlap into the same stack memory: a struct of one type,
/// and later a struct of another type in the same bytes. Read as one object, that memory holds two different
/// types. Here the accesses to a stack object are grouped by which writes their reads see (reaching definitions,
/// per piece of the object, with every access that spans several pieces tying them together); each group after
/// the first moves to fresh stack memory. No group can observe another's data, so the program means the same.
/// Applied only to the objects the high-level form found contradictory.
///
/// The same goes for the memory above the return address, the space the caller set aside for the function (the
/// home slots of the register arguments, the stack arguments): the compiler keeps locals there as well, a spilled
/// "this" in one place, an enum to box and then a caught exception in the next. What that memory held on entry
/// is a stack argument, though: a group that reads it stays where the caller put it.
/// </summary>
public static class StackSplitting
{
    /// <summary>The return address: no part of any object.</summary>
    private const int ReturnSlot = 8;

    private static readonly bool BelowOnly = Environment.GetEnvironmentVariable("REWIND_NO_CALLER_SLOTS") != null;
    private static readonly bool KeepTopHalves = Environment.GetEnvironmentVariable("REWIND_NO_TOP_HALVES") != null;

    private static bool Owned(int offset) => offset < 0 || (offset >= ReturnSlot && !BelowOnly);

    /// <summary>
    /// A stack address goes into a stack slot the compiler also writes 32 bits at a time (an outgoing argument:
    /// an address for one call, an int for the next); as values, the slot is two cells, and the address is cut
    /// in two - "address >> 32" here, "trunc(rsp) + c" (no stack address any more) for the bottom. Where paths
    /// meet the cells are merged, and every later call is handed the two halves joined as what the slot
    /// "holds". True when that is all that happens to the top half: followed through narrowing, merging and
    /// joining, every use is an input of a call that does not take it - or takes the bottom half of the slot
    /// only (an int, a float), where it is the top half of the joined value. The address then went nowhere,
    /// and is not kept in a value after all.
    /// </summary>
    internal static bool TopHalfEndsNowhere(Node user, int input, Function fn, Func<Node, int, int>? escapeExtent,
        Func<Node, int, bool>? lowHalfOnly, ref Dictionary<Node, List<(Node User, int Input)>>? uses)
    {
        if (user.Op != Op.ShrU || input != 0 || !user.In[1].IsConstValue(32) || escapeExtent == null) return false;
        uses ??= UsesOf(fn);
        // What is followed: the half itself (32 bits; the shift before it is narrowed counts as that), and
        // 64-bit values that have it as their top half.
        var seen = new HashSet<Node> { user };
        var work = new Stack<(Node Value, bool Joined)>();
        work.Push((user, false));
        while (work.Count > 0)
        {
            var (value, joined) = work.Pop();
            if (!uses.TryGetValue(value, out var users)) continue;
            foreach (var (by, at) in users)
            {
                bool next;
                if (by.Op is Op.Call or Op.TailCall)
                {
                    if (escapeExtent(by, at) == StackPromotion.NotTaken) continue;
                    if (joined && lowHalfOnly != null && lowHalfOnly(by, at)) continue;
                    return false;
                }
                else if (by.Op == Op.Phi) next = joined;
                else if (by.Op == Op.Trunc && ReferenceEquals(value, user)) next = false; // the shifted address, narrowed: the half
                else if (by.Op == Op.Trunc && joined && by.Type.Bits() <= 32) continue;  // the bottom half of a joined value: not this
                else if (by.Op == Op.Concat && !joined && at == 0 && !ReferenceEquals(value, user)) next = true;
                else return false;
                if (seen.Count > 512) return false;
                if (seen.Add(by)) work.Push((by, next));
            }
        }
        return true;
    }

    private static Dictionary<Node, List<(Node User, int Input)>> UsesOf(Function fn)
    {
        var found = new Dictionary<Node, List<(Node User, int Input)>>();
        void Note(Node n)
        {
            for (int i = 0; i < n.In.Length; i++)
            {
                if (!found.TryGetValue(n.In[i], out var list)) found[n.In[i]] = list = [];
                list.Add((n, i));
            }
        }
        foreach (Block b in fn.Blocks)
        {
            foreach (Node phi in b.Phis)
                if (!phi.Dead) Note(phi);
            foreach (Node n in b.Nodes)
                if (!n.Dead) Note(n);
        }
        return found;
    }

    private static readonly bool NoMergedArguments = Environment.GetEnvironmentVariable("REWIND_NO_MERGED_ARGUMENTS") != null;

    /// <summary>
    /// One call reached from several paths, each with a stack object of its own to hand over: the address the
    /// call takes is merged from theirs. Where that is all the merged address is for - every use is an input of
    /// a call that reaches a known number of bytes through it - the calls that take it; null otherwise. The
    /// address is then kept in no value that could be used elsewhere: each call reads or writes one of the
    /// objects, and which one is the only thing not known.
    /// </summary>
    internal static List<(Node Call, int Input, int Extent)>? MergedArgument(Node phi, Function fn, Func<Node, int, int>? escapeExtent,
        ref Dictionary<Node, List<(Node User, int Input)>>? uses)
    {
        if (NoMergedArguments || escapeExtent == null || phi.Op != Op.Phi) return null;
        uses ??= UsesOf(fn);
        if (!uses.TryGetValue(phi, out var users) || users.Count == 0 || users.Count > 8) return null;
        var calls = new List<(Node Call, int Input, int Extent)>();
        foreach (var (by, at) in users)
        {
            if (by.Op != Op.Call || by.Block == null) return null;
            int extent = escapeExtent(by, at);
            if (extent <= 0) return null;
            calls.Add((by, at, extent));
        }
        return calls;
    }

    /// <summary>When set, told what was decided for each object (for debugging).</summary>
    public static Action<string>? Trace;
    public static bool Detail = Environment.GetEnvironmentVariable("REWIND_SPLIT_DETAIL") != null;

    private sealed class Access(Node user, int input, int start, int end, bool uses, bool defines)
    {
        public Node User = user;
        public int Input = input;
        public int Start = start, End = end;
        public bool Uses = uses, Defines = defines;
        public int Id;
        /// <summary>
        /// For a way into a merged address (User: the merged value, Input: the way in): the call the merged
        /// address is handed to. The access happens there, and only when that way was taken - so what it writes
        /// adds to what the object may hold and replaces nothing.
        /// </summary>
        public Node? At;
        public Node Where => At ?? User;
        /// <summary>
        /// Set where the access can be told to one way in: the block that way comes from. The call stands in the
        /// block the ways meet in with nothing written to the object before it, and that block leads nowhere
        /// else - so what the call finds in the object is what was there at the end of that block, and what it
        /// writes is written on that way only. The access is then counted there, like any other.
        /// </summary>
        public Block? Path;
    }

    /// <summary>Splits the stack objects covering <paramref name="offsets"/>; returns how many lifetimes moved.</summary>
    /// <param name="removable">True for a call that does nothing but write the memory behind that input (a fill, the destination of a copy).</param>
    public static int Run(Function fn, IEnumerable<int> offsets, Func<Node, int, int>? escapeExtent = null, Func<Node, int, bool>? writesOnly = null,
        Func<Node, int, bool>? readsOnly = null, Func<Node, int, bool>? removable = null, Func<int, int>? reach = null, Func<Node, int, bool>? lowHalfOnly = null)
    {
        Trace?.Invoke($"function 0x{fn.Address:X}");
        // An address kept in a value (stored, merged) can be used from anywhere, but only to get at the object it
        // points to: as far as that object is known to extend (reach), else everything above it.
        int Reach(int at) => reach?.Invoke(at) is int known and > 0 ? at + known : int.MaxValue;
        // A handler is entered from anywhere in its region: it sees what the region's blocks wrote, each write.
        var handlerOf = new Dictionary<Block, int>();
        foreach (var (gate, region) in fn.TryGates()) handlerOf[gate.Succs[0]] = region;
        if (!fn.Params.TryGetValue(X64Lifter.VarRsp, out Node? sp0)) return 0;
        bool IsStackAddress(Node n, out int offset)
        {
            offset = 0;
            if (ReferenceEquals(n, sp0)) return true;
            if (n.Op != Op.Add || !ReferenceEquals(n.In[0], sp0) || !n.In[1].IsConst) return false;
            long value = IrBuilder.SImm(n.In[1]);
            if (value is <= -0x4000000 or >= 0x4000000) return false;
            offset = (int)value;
            return true;
        }

        // Every use of a stack address of the function's own memory.
        var all = new List<Access>();
        var escaped = new List<(int Start, int End, Node By)>();
        Dictionary<Node, List<(Node User, int Input)>>? uses = null;
        foreach (Block b in fn.Blocks)
            foreach (Node n in b.Nodes)
            {
                if (n.Dead) continue;
                for (int i = 0; i < n.In.Length; i++)
                {
                    if (!IsStackAddress(n.In[i], out int at) || !Owned(at)) continue;
                    if (n.Op == Op.Load && i == 0) all.Add(new Access(n, i, at, at + n.Type.Bytes(), true, false));
                    else if (n.Op == Op.Store && i == 0) all.Add(new Access(n, i, at, at + n.In[1].Type.Bytes(), false, true));
                    else if (n.Op is Op.Call)
                    {
                        int extent = escapeExtent?.Invoke(n, i) ?? -1;
                        if (extent == StackPromotion.NotTaken) continue; // what the slot held before: no argument of this call
                        bool reads = !(writesOnly?.Invoke(n, i) ?? false) || extent <= 0;
                        bool writes = !(readsOnly?.Invoke(n, i) ?? false) || extent <= 0;
                        all.Add(new Access(n, i, at, extent > 0 ? at + extent : int.MaxValue, reads, writes));
                    }
                    // The top half of an address, cut off where the address went into a stack slot kept as two
                    // 32-bit cells (an outgoing argument), that no call takes afterwards.
                    else if (!KeepTopHalves && TopHalfEndsNowhere(n, i, fn, escapeExtent, lowHalfOnly, ref uses)) { }
                    else escaped.Add((at, Reach(at), n)); // kept in a value, stored, combined: not followed
                }
            }
        foreach (Block b in fn.Blocks)
            foreach (Node phi in b.Phis)
            {
                if (phi.Dead) continue;
                bool any = false, every = true;
                foreach (Node input in phi.In)
                {
                    if (IsStackAddress(input, out int at) && Owned(at)) any = true;
                    else every = false;
                }
                if (!any) continue;
                // A merged address that is only handed to calls: each way in is an access those calls make.
                if (every && MergedArgument(phi, fn, escapeExtent, ref uses) is { } handed)
                {
                    for (int way = 0; way < phi.In.Length; way++)
                    {
                        IsStackAddress(phi.In[way], out int at);
                        foreach (var (call, input, extent) in handed)
                            all.Add(new Access(phi, way, at, at + extent, !(writesOnly?.Invoke(call, input) ?? false), !(readsOnly?.Invoke(call, input) ?? false)) { At = call });
                    }
                    continue;
                }
                foreach (Node input in phi.In)
                    if (IsStackAddress(input, out int at) && Owned(at)) escaped.Add((at, Reach(at), phi));
            }

        // How far a call given a stack address may reach when its extent is not known: the function's locals end
        // at the return address; above it, as far as anything here touches that memory.
        int above = ReturnSlot;
        foreach (Access a in all)
            if (a.Start >= ReturnSlot) above = Math.Max(above, a.End != int.MaxValue ? a.End : a.Start + 8);
        int Top(int at) => at < 0 ? 0 : above;

        // Moved lifetimes go below everything the function uses (earlier rounds' moves included).
        int lowest = 0;
        foreach (Access a in all) lowest = Math.Min(lowest, a.Start);
        foreach (var e in escaped) lowest = Math.Min(lowest, e.Start);
        int moved = 0, nextBase = Math.Min(-0x40000, (lowest & ~0xFF) - 0x100);
        var done = new HashSet<int>();
        foreach (int offset in offsets.OrderBy(o => o))
        {
            if (!Owned(offset) || done.Contains(offset)) continue;
            // The object: everything that overlaps the offset, transitively.
            int start = offset, end = offset + 1;
            bool grew = true;
            while (grew)
            {
                grew = false;
                foreach (Access a in all)
                {
                    int aEnd = Math.Min(a.End, Top(a.Start));
                    if (a.Start < end && start < aEnd && (a.Start < start || aEnd > end))
                    {
                        start = Math.Min(start, a.Start);
                        end = Math.Max(end, aEnd);
                        grew = true;
                    }
                }
            }
            for (int o = start; o < end; o++) done.Add(o);
            if (escaped.Any(e => e.Start < end && start < e.End))
            {
                Trace?.Invoke($"object [{start}, {end}) at {offset}: its address is kept in a value ({Function.Describe(escaped.First(e => e.Start < end && start < e.End).By)})");
                if (Trace != null && Detail)
                    foreach (Access a in all.Where(a => a.End == int.MaxValue && a.Start < end && start < Top(a.Start)).Take(12))
                    {
                        string text = Function.Describe(a.User);
                        Trace($"    reach unknown from {a.Start}: {(text.Length > 150 ? text[..150] : text)}");
                    }
                continue;
            }
            var accesses = all.Where(a => a.Start < end && start < Math.Min(a.End, Top(a.Start))).ToList();
            if (accesses.Count < 2 || accesses.Count > 400)
            {
                Trace?.Invoke($"object [{start}, {end}) at {offset}: {accesses.Count} accesses");
                continue;
            }
            // Calls see the whole object from their address on.
            foreach (Access a in accesses) a.End = Math.Min(a.End, end);
            if (accesses.Any(a => a.Start < start || a.End > end)) continue;

            // Pieces: between every access boundary.
            var bounds = new SortedSet<int>();
            foreach (Access a in accesses)
            {
                bounds.Add(a.Start);
                bounds.Add(a.End);
            }
            int[] edges = bounds.ToArray();
            int pieces = edges.Length - 1;
            if (pieces > 64)
            {
                Trace?.Invoke($"object [{start}, {end}) at {offset}: {pieces} pieces");
                continue;
            }
            int PieceOf(int at) => Array.BinarySearch(edges, at);
            for (int i = 0; i < accesses.Count; i++) accesses[i].Id = i;
            int entryBase = accesses.Count; // one "whatever was there" definition per piece

            var parent = new int[accesses.Count + pieces];
            for (int i = 0; i < parent.Length; i++) parent[i] = i;
            int Find(int x)
            {
                while (parent[x] != x) x = parent[x] = parent[parent[x]];
                return x;
            }
            void Union(int a, int b) => parent[Find(a)] = Find(b);
            // One way into a merged address is one address, whichever call takes it: its accesses stay together.
            var ways = new Dictionary<(Node, int), int>();
            foreach (Access a in accesses)
            {
                if (a.At == null) continue;
                if (ways.TryGetValue((a.User, a.Input), out int first)) Union(a.Id, first);
                else ways[(a.User, a.Input)] = a.Id;
            }

            // Reaching definitions per piece, block by block.
            foreach (Access a in accesses)
            {
                a.Path = null;
                if (a.At == null) continue;
                Block join = a.User.Block!;
                if (!ReferenceEquals(a.At.Block, join) || a.Input >= join.Preds.Count || join.Preds[a.Input].Succs.Count != 1) continue;
                int callAt = join.Nodes.IndexOf(a.At);
                bool writtenBefore = false;
                foreach (Access other in accesses)
                    if (other.Defines && !ReferenceEquals(other.Where, a.At) && ReferenceEquals(other.Where.Block, join) && join.Nodes.IndexOf(other.Where) < callAt)
                    {
                        writtenBefore = true;
                        break;
                    }
                if (!writtenBefore) a.Path = join.Preds[a.Input];
            }
            var byBlock = accesses.GroupBy(a => a.Path ?? a.Where.Block!)
                .ToDictionary(g => g.Key, g => g.OrderBy(a => a.Path != null ? int.MaxValue : a.Where.Block!.Nodes.IndexOf(a.Where)).ToList());
            var cfg = new Cfg(fn);
            var outSets = new Dictionary<Block, HashSet<int>[]>();
            HashSet<int>[] In(Block b)
            {
                var sets = new HashSet<int>[pieces];
                for (int p = 0; p < pieces; p++) sets[p] = [];
                if (ReferenceEquals(b, fn.Entry))
                    for (int p = 0; p < pieces; p++) sets[p].Add(entryBase + p);
                foreach (Block pred in b.Preds)
                    if (outSets.TryGetValue(pred, out HashSet<int>[]? o))
                        for (int p = 0; p < pieces; p++) sets[p].UnionWith(o[p]);
                if (handlerOf.TryGetValue(b, out int region))
                    foreach (Block inside in fn.Blocks)
                    {
                        if (!fn.IsProtectedBy(inside, region)) continue;
                        if (outSets.TryGetValue(inside, out HashSet<int>[]? o))
                            for (int p = 0; p < pieces; p++) sets[p].UnionWith(o[p]);
                        if (!byBlock.TryGetValue(inside, out List<Access>? written)) continue;
                        foreach (Access a in written)
                            if (a.Defines)
                                for (int p = PieceOf(a.Start); p < PieceOf(a.End); p++) sets[p].Add(a.Id);
                    }
                return sets;
            }
            void Step(Access a, HashSet<int>[] sets, bool record)
            {
                int first = PieceOf(a.Start), last = PieceOf(a.End);
                if (record && a.Uses)
                    for (int p = first; p < last; p++)
                        foreach (int d in sets[p]) Union(a.Id, d);
                if (a.Defines)
                    for (int p = first; p < last; p++)
                    {
                        if (a.At != null && a.Path == null) sets[p].Add(a.Id); // on one way in only: what was there may still be
                        else sets[p] = [a.Id];
                    }
            }
            bool changed = true;
            for (int round = 0; changed && round < 32; round++)
            {
                changed = false;
                foreach (Block b in cfg.ReversePostOrder)
                {
                    HashSet<int>[] sets = In(b);
                    if (byBlock.TryGetValue(b, out List<Access>? list))
                        foreach (Access a in list) Step(a, sets, record: false);
                    if (!outSets.TryGetValue(b, out HashSet<int>[]? old) || !Enumerable.Range(0, pieces).All(p => old[p].SetEquals(sets[p])))
                    {
                        outSets[b] = sets;
                        changed = true;
                    }
                }
            }
            if (changed)
            {
                Trace?.Invoke($"object [{start}, {end}) at {offset}: lifetimes did not settle");
                continue; // did not settle: leave the object as it is
            }
            foreach (Block b in cfg.ReversePostOrder)
            {
                if (!byBlock.TryGetValue(b, out List<Access>? list)) continue;
                HashSet<int>[] sets = In(b);
                foreach (Access a in list) Step(a, sets, record: true);
            }

            // Groups; the largest stays where it is (or the ones that read what the caller left there).
            // A lifetime made of writes alone is never read: its stores and fills do nothing.
            foreach (var unread in accesses.GroupBy(a => Find(a.Id)).ToList())
            {
                if (unread.Any(a => a.Uses) || !unread.All(a => a.At == null && (a.User.Op == Op.Store || (removable?.Invoke(a.User, a.Input) ?? false)))) continue;
                foreach (Access a in unread)
                {
                    a.User.Dead = true;
                    a.User.Block!.Nodes.Remove(a.User);
                    accesses.Remove(a);
                }
                Trace?.Invoke($"object [{start}, {end}) at {offset}: writes that nothing reads removed");
                moved++;
            }
            // A removed copy also stops reading its source, here or in another object.
            accesses.RemoveAll(a => a.User.Dead || a.At is { Dead: true });
            all.RemoveAll(a => a.User.Dead || a.At is { Dead: true });
            var groups = accesses.GroupBy(a => Find(a.Id)).OrderByDescending(g => g.Count()).ToList();
            if (Trace != null && Detail)
                foreach (Access a in accesses.OrderBy(a => a.Where.Block!.Id).ThenBy(a => a.Where.Block!.Nodes.IndexOf(a.Where)))
                {
                    string text = Function.Describe(a.User);
                    Trace($"    {a.Where.Block} [{a.Start}, {a.End}) {(a.Uses ? "reads" : "")}{(a.Defines ? " writes" : "")} group {Find(a.Id)}: {(text.Length > 90 ? text[..90] : text)}");
                }
            Trace?.Invoke($"object [{start}, {end}) at {offset}: {accesses.Count} accesses, {pieces} pieces, {groups.Count} lifetimes");
            if (groups.Count < 2) continue;
            // What the caller left above the return address is read where it is; the other lifetimes move.
            var entered = new HashSet<int>();
            for (int p = 0; p < pieces; p++)
                if (edges[p] >= 0)
                    entered.Add(Find(entryBase + p));
            List<IGrouping<int, Access>> moving = groups.Any(g => entered.Contains(g.Key))
                ? groups.Where(g => !entered.Contains(g.Key)).ToList()
                : groups.Skip(1).ToList();
            int size = end - start;
            foreach (var group in moving)
            {
                int newStart = nextBase;
                nextBase -= Math.Max(0x100, (size + 0xFF) & ~0xFF);
                // (Several calls may take one merged address: its way in is given the new address once.)
                var redirected = new HashSet<(Node, int)>();
                foreach (Access a in group)
                {
                    if (!redirected.Add((a.User, a.Input))) continue;
                    // The new address stands before what uses it: for a way into a merged address, at the end
                    // of the block that way comes from.
                    Block block = a.At != null ? a.User.Block!.Preds[a.Input] : a.User.Block!;
                    Node constant = fn.NewNode(Op.Const, VT.I64, block);
                    constant.Imm = newStart + (a.Start - start);
                    Node address = fn.NewNode(Op.Add, VT.I64, block, sp0, constant);
                    int at = a.At != null ? Math.Max(0, block.Nodes.Count - 1) : block.Nodes.IndexOf(a.User);
                    block.Nodes.Insert(at, constant);
                    block.Nodes.Insert(at + 1, address);
                    a.User.In[a.Input] = address;
                }
                moved++;
            }
        }
        return moved;
    }
}
