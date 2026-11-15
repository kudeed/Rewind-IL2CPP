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
/// </summary>
public static class StackSplitting
{
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
    }

    /// <summary>Splits the stack objects covering <paramref name="offsets"/>; returns how many lifetimes moved.</summary>
    /// <param name="removable">True for a call that does nothing but write the memory behind that input (a fill, the destination of a copy).</param>
    public static int Run(Function fn, IEnumerable<int> offsets, Func<Node, int, int>? escapeExtent = null, Func<Node, int, bool>? writesOnly = null,
        Func<Node, int, bool>? readsOnly = null, Func<Node, int, bool>? removable = null, Func<int, int>? reach = null)
    {
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

        // Every use of a stack address below the entry stack pointer.
        var all = new List<Access>();
        var escaped = new List<(int Start, int End, Node By)>();
        foreach (Block b in fn.Blocks)
            foreach (Node n in b.Nodes)
            {
                if (n.Dead) continue;
                for (int i = 0; i < n.In.Length; i++)
                {
                    if (!IsStackAddress(n.In[i], out int at) || at >= 0) continue;
                    if (n.Op == Op.Load && i == 0) all.Add(new Access(n, i, at, at + n.Type.Bytes(), true, false));
                    else if (n.Op == Op.Store && i == 0) all.Add(new Access(n, i, at, at + n.In[1].Type.Bytes(), false, true));
                    else if (n.Op is Op.Call)
                    {
                        int extent = escapeExtent?.Invoke(n, i) ?? -1;
                        bool reads = !(writesOnly?.Invoke(n, i) ?? false) || extent <= 0;
                        bool writes = !(readsOnly?.Invoke(n, i) ?? false) || extent <= 0;
                        all.Add(new Access(n, i, at, extent > 0 ? at + extent : int.MaxValue, reads, writes));
                    }
                    else escaped.Add((at, Reach(at), n)); // kept in a value, stored, combined: not followed
                }
            }
        foreach (Block b in fn.Blocks)
            foreach (Node phi in b.Phis)
                foreach (Node input in phi.In)
                    if (IsStackAddress(input, out int at) && at < 0) escaped.Add((at, Reach(at), phi));

        int moved = 0, nextBase = -0x40000;
        var done = new HashSet<int>();
        foreach (int offset in offsets.OrderBy(o => o))
        {
            if (offset >= 0 || done.Contains(offset)) continue;
            // The object: everything that overlaps the offset, transitively.
            int start = offset, end = offset + 1;
            bool grew = true;
            while (grew)
            {
                grew = false;
                foreach (Access a in all)
                {
                    int aEnd = Math.Min(a.End, 0);
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
                continue;
            }
            var accesses = all.Where(a => a.Start < end && start < Math.Min(a.End, 0)).ToList();
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

            // Reaching definitions per piece, block by block.
            var byBlock = accesses.GroupBy(a => a.User.Block!).ToDictionary(g => g.Key, g => g.OrderBy(a => a.User.Block!.Nodes.IndexOf(a.User)).ToList());
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
                    for (int p = first; p < last; p++) sets[p] = [a.Id];
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

            // Groups; the largest stays where it is.
            // A lifetime made of writes alone is never read: its stores and fills do nothing.
            foreach (var unread in accesses.GroupBy(a => Find(a.Id)).ToList())
            {
                if (unread.Any(a => a.Uses) || !unread.All(a => a.User.Op == Op.Store || (removable?.Invoke(a.User, a.Input) ?? false))) continue;
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
            accesses.RemoveAll(a => a.User.Dead);
            all.RemoveAll(a => a.User.Dead);
            var groups = accesses.GroupBy(a => Find(a.Id)).OrderByDescending(g => g.Count()).ToList();
            if (Trace != null && Detail)
                foreach (Access a in accesses.OrderBy(a => a.User.Block!.Id).ThenBy(a => a.User.Block!.Nodes.IndexOf(a.User)))
                {
                    string text = Function.Describe(a.User);
                    Trace($"    {a.User.Block} [{a.Start}, {a.End}) {(a.Uses ? "reads" : "")}{(a.Defines ? " writes" : "")} group {Find(a.Id)}: {(text.Length > 90 ? text[..90] : text)}");
                }
            Trace?.Invoke($"object [{start}, {end}) at {offset}: {accesses.Count} accesses, {pieces} pieces, {groups.Count} lifetimes");
            if (groups.Count < 2) continue;
            int size = end - start;
            foreach (var group in groups.Skip(1))
            {
                int newStart = nextBase;
                nextBase -= Math.Max(0x100, (size + 0xFF) & ~0xFF);
                foreach (Access a in group)
                {
                    Block block = a.User.Block!;
                    Node constant = fn.NewNode(Op.Const, VT.I64, block);
                    constant.Imm = newStart + (a.Start - start);
                    Node address = fn.NewNode(Op.Add, VT.I64, block, sp0, constant);
                    int at = block.Nodes.IndexOf(a.User);
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
