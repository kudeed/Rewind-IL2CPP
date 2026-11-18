using Rewind.Analysis.Ir;
using Rewind.Analysis.X64;

namespace Rewind.Analysis.Passes;

/// <summary>Stack memory whose address is observable (passed to a call, indexed, compared): a real local.</summary>
public sealed class FrameObject
{
    /// <summary>Offset from the stack pointer at function entry.</summary>
    public int Offset;
    public int Size;
    public override string ToString() => $"frame[{(Offset < 0 ? "-" : "+")}0x{Math.Abs(Offset):X}, {Size}]";
}

/// <summary>
/// Turns stack slots into SSA values. Slots that are only ever read and written directly (spilled registers,
/// saved callee registers, simple locals) disappear into value flow. Slots whose address escapes stay in
/// memory and are reported as frame objects, to become address-taken locals.
/// </summary>
public static class StackPromotion
{
    public const int StackParamVarBase = 0x10000;
    /// <summary>What the "how far does this call reach" question answers for an input the call does not take at all.</summary>
    public const int NotTaken = int.MinValue;
    private static readonly bool KeepTopHalves = Environment.GetEnvironmentVariable("REWIND_NO_TOP_HALVES") != null;
    private static readonly bool NoEntryArguments = Environment.GetEnvironmentVariable("REWIND_NO_ENTRY_ARGUMENTS") != null;

    private readonly record struct Access(Node User, int Offset, int Size, bool IsStore);

    /// <summary>
    /// An argument of one or two bytes passed on the stack is written with a store of that size ("mov byte ptr
    /// [rsp+20h], 1" for a bool); the call is modelled as reading the whole eight-byte slot. Bytes written one
    /// way and read another cannot become a value, so the slot stayed in memory - one variable for every call
    /// that passes anything in that position. Here the call is given the stored value itself (the other bytes
    /// of the slot are not part of the argument), where the slot is read by calls only.
    /// </summary>
    private static void ForwardSmallArguments(Function fn, Node sp0)
    {
        bool Stack(Node n, out int offset)
        {
            offset = 0;
            if (n.Op != Op.Add || !ReferenceEquals(n.In[0], sp0) || !n.In[1].IsConst) return false;
            long value = IrBuilder.SImm(n.In[1]);
            if (value is <= -0x4000000 or >= 0x4000000) return false;
            offset = (int)value;
            return true;
        }

        var argumentLoads = new HashSet<Node>();
        foreach (Block b in fn.Blocks)
            foreach (Node n in b.Nodes)
                if (!n.Dead && n.Op is Op.Call or Op.TailCall && n.Aux is CallInfo info)
                    for (int i = 0; i < info.Slots.Count && i < n.In.Length; i++)
                        if (info.Slots[i].Kind == ArgSlotKind.Stack && n.In[i].Op == Op.Load)
                            argumentLoads.Add(n.In[i]);
        if (argumentLoads.Count == 0) return;
        // Every other look at the stack: a read, or an address that goes somewhere.
        var others = new List<(int Offset, int Size)>();
        foreach (Block b in fn.Blocks)
        {
            foreach (Node n in b.Phis)
                foreach (Node input in n.In)
                    if (Stack(input, out int o))
                        others.Add((o, int.MaxValue / 2));
            foreach (Node n in b.Nodes)
            {
                if (n.Dead) continue;
                for (int i = 0; i < n.In.Length; i++)
                {
                    if (!Stack(n.In[i], out int o)) continue;
                    if (n.Op == Op.Load && i == 0)
                    {
                        if (!argumentLoads.Contains(n)) others.Add((o, n.Type.Bytes()));
                    }
                    else if (n.Op == Op.Store && i == 0) { }
                    else if (n.Op == Op.Add && i == 0 && n.In[1].IsConst) { } // another way of writing a stack address
                    else if (n.Op == Op.Return) { }
                    else others.Add((o, int.MaxValue / 2));
                }
            }
        }

        foreach (Block b in fn.Blocks)
        {
            bool any = false;
            for (int k = 0; k < b.Nodes.Count; k++)
            {
                Node call = b.Nodes[k];
                if (call.Dead || call.Op is not (Op.Call or Op.TailCall) || call.Aux is not CallInfo info) continue;
                for (int i = 0; i < info.Slots.Count && i < call.In.Length; i++)
                {
                    if (info.Slots[i].Kind != ArgSlotKind.Stack) continue;
                    Node load = call.In[i];
                    if (load.Op != Op.Load || load.Dead || load.Type != VT.I64 || !Stack(load.In[0], out int at)) continue;
                    if (others.Any(r => r.Offset < at + 8 && at < (long)r.Offset + r.Size)) continue;
                    // What was stored for this call: the last store to the slot before it, in straight-line code.
                    Node? store = null;
                    for (int j = k - 1; j >= 0; j--)
                    {
                        Node m = b.Nodes[j];
                        if (m.Dead) continue;
                        if (m.Op is Op.Call or Op.TailCall) break;
                        if (m.Op != Op.Store || !Stack(m.In[0], out int to)) continue;
                        int size = m.In[1].Type.Bytes();
                        if (to >= at + 8 || at >= to + size) continue;
                        if (to == at && size is 1 or 2 && m.In[1].Type.IsInt()) store = m;
                        break;
                    }
                    if (store == null) continue;
                    Node value = store.In[1];
                    Node wide;
                    if (value.IsConst)
                    {
                        wide = fn.NewNode(Op.Const, VT.I64, null);
                        wide.Imm = (long)value.UImm;
                    }
                    else
                    {
                        wide = fn.NewNode(Op.ZExt, VT.I64, b, value);
                        wide.Addr = call.Addr;
                        b.Nodes.Insert(k, wide);
                        k++;
                    }
                    call.In[i] = wide;
                    store.Dead = true;
                    bool used = false;
                    foreach (Node n in b.Nodes)
                        if (!n.Dead && !ReferenceEquals(n, load) && Array.IndexOf(n.In, load) >= 0) { used = true; break; }
                    if (!used) load.Dead = true;
                    any = true;
                }
            }
            if (any) b.Nodes.RemoveAll(n => n.Dead);
        }
    }

    /// <param name="escapeExtent">
    /// For a stack address used as input <c>index</c> of <c>user</c> (a call argument, typically): how many
    /// bytes the callee may touch, or -1 when unknown.
    /// </param>
    /// <param name="stackArguments">
    /// The arguments the method is handed on the stack: offset from the entry stack pointer -> size in bytes.
    /// </param>
    public static List<FrameObject> Run(Function fn, Func<Node, int, int>? escapeExtent = null, IReadOnlyDictionary<int, int>? stackArguments = null, Func<Node, int, bool>? lowHalfOnly = null)
    {
        var frameObjects = new List<FrameObject>();
        if (!fn.Params.TryGetValue(fn.Regs.StackPointer, out Node? sp0)) return frameObjects;
        if (Environment.GetEnvironmentVariable("REWIND_NO_SMALL_ARGUMENTS") == null) ForwardSmallArguments(fn, sp0);

        bool IsStackAddress(Node n, out int offset)
        {
            if (ReferenceEquals(n, sp0))
            {
                offset = 0;
                return true;
            }
            if (n.Op == Op.Add && ReferenceEquals(n.In[0], sp0) && n.In[1].IsConst)
            {
                long value = IrBuilder.SImm(n.In[1]);
                if (value is > -0x4000000 and < 0x4000000)
                {
                    offset = (int)value;
                    return true;
                }
            }
            offset = 0;
            return false;
        }

        // 1. Collect direct accesses and escapes.
        var accesses = new List<Access>();
        var escapes = new List<(int Offset, int Extent)>();
        Dictionary<Node, List<(Node User, int Input)>>? uses = null;
        // Try regions: a slot written in protected code and read where an exception leads keeps living in
        // memory, so the handler and the code after it see the value of the moment the exception was raised.
        var afterException = new HashSet<Block>();
        foreach (var (gate, _) in fn.TryGates())
        {
            var work = new Stack<Block>();
            work.Push(gate.Succs[0]);
            while (work.Count > 0)
                foreach (Block s in work.Pop().Succs)
                    if (afterException.Add(s)) work.Push(s);
            afterException.Add(gate.Succs[0]);
        }
        var protectedStores = new List<(int Offset, int Size)>();
        var exceptionLoads = new List<(int Offset, int Size)>();
        // The loads a call reads its stack-passed arguments with: they read what was stored for that call, just
        // before it. Nothing an exception could have left there is ever looked at through them.
        var argumentLoads = new HashSet<Node>();
        if (afterException.Count != 0 && Environment.GetEnvironmentVariable("REWIND_NO_ARGUMENT_SLOTS") == null)
            foreach (Block b in fn.Blocks)
                foreach (Node n in b.Nodes)
                    if (!n.Dead && n.Op is Op.Call or Op.TailCall && n.Aux is CallInfo info)
                        for (int i = 0; i < info.Slots.Count && i < n.In.Length; i++)
                            if (info.Slots[i].Kind == ArgSlotKind.Stack && n.In[i].Op == Op.Load)
                                argumentLoads.Add(n.In[i]);
        foreach (Block b in fn.Blocks)
        {
            bool isProtected = afterException.Count != 0 && fn.IsProtected(b), seesException = afterException.Contains(b);
            foreach (Node n in b.Phis)
            {
                if (n.Dead) continue;
                // A merged address that is only handed to calls reaches what those calls reach, from each of
                // the objects it may be the address of.
                int reached = -1;
                if (n.In.All(input => IsStackAddress(input, out _)) && StackSplitting.MergedArgument(n, fn, escapeExtent, ref uses) is { } handed)
                    foreach (var (_, _, extent) in handed) reached = Math.Max(reached, extent);
                foreach (Node input in n.In)
                    if (IsStackAddress(input, out int o))
                        escapes.Add((o, reached));
            }
            foreach (Node n in b.Nodes)
            {
                if (n.Dead) continue;
                for (int i = 0; i < n.In.Length; i++)
                {
                    if (!IsStackAddress(n.In[i], out int offset)) continue;
                    if (n.Op == Op.Load && i == 0 && seesException && !argumentLoads.Contains(n)) exceptionLoads.Add((offset, n.Type.Bytes()));
                    if (n.Op == Op.Store && i == 0 && isProtected) protectedStores.Add((offset, n.In[1].Type.Bytes()));
                    if (n.Op == Op.Load && i == 0) accesses.Add(new Access(n, offset, n.Type.Bytes(), false));
                    else if (n.Op == Op.Store && i == 0) accesses.Add(new Access(n, offset, n.In[1].Type.Bytes(), true));
                    else if (n.Op == Op.Add && i == 0 && n.In[1].IsConst) { } // another canonical stack address
                    else if (n.Op is Op.Call or Op.TailCall)
                    {
                        // (An input the call does not take - what the slot held before - is no use of the address.)
                        int extent = escapeExtent?.Invoke(n, i) ?? -1;
                        if (extent != NotTaken) escapes.Add((offset, extent));
                    }
                    else if (n.Op == Op.Return) { } // returning the frame pointer value itself is meaningless
                    else if (!KeepTopHalves && StackSplitting.TopHalfEndsNowhere(n, i, fn, escapeExtent, lowHalfOnly, ref uses)) { }
                    else escapes.Add((offset, -1));
                }
            }
        }
        // Kept in memory for what an exception leaves there - as far as those uses go (see FreeOfExceptions).
        bool noWebs = Environment.GetEnvironmentVariable("REWIND_NO_SLOT_WEBS") != null;
        var keptForExceptions = new List<(int Offset, int Size)>();
        foreach (var (offset, size) in protectedStores)
            if (exceptionLoads.Any(l => l.Offset < offset + size && offset < l.Offset + l.Size))
            {
                if (noWebs) escapes.Add((offset, size));
                else keptForExceptions.Add((offset, size));
            }

        // The uses of a slot that have nothing to do with what an exception leaves in it: those no write in
        // protected code can reach and that reach no read where an exception leads. The compiler uses a slot
        // again and again for different things; one of them being kept in memory says nothing about the others.
        // Every use here covers the whole slot, so each write replaces what was there.
        Dictionary<Node, (Block Block, int Index)>? where = null;
        List<Access>? FreeOfExceptions(List<Access> items)
        {
            if (where == null)
            {
                where = [];
                foreach (Block b in fn.Blocks)
                    for (int i = 0; i < b.Nodes.Count; i++)
                        where[b.Nodes[i]] = (b, i);
            }
            int n = items.Count;
            int[] parent = new int[n + 1]; // one more: what the slot held on entry
            for (int i = 0; i <= n; i++) parent[i] = i;
            int Find(int x)
            {
                while (parent[x] != x) x = parent[x] = parent[parent[x]];
                return x;
            }
            void Union(int a, int b)
            {
                a = Find(a);
                b = Find(b);
                if (a != b) parent[a] = b;
            }

            var inBlock = new Dictionary<Block, List<int>>();
            for (int i = 0; i < n; i++)
            {
                if (!where.TryGetValue(items[i].User, out var at)) return null;
                if (!inBlock.TryGetValue(at.Block, out List<int>? list)) inBlock[at.Block] = list = [];
                list.Add(i);
            }
            var lastStore = new Dictionary<Block, int>();
            foreach (var (b, list) in inBlock)
            {
                list.Sort((x, y) => where[items[x].User].Index.CompareTo(where[items[y].User].Index));
                for (int k = list.Count - 1; k >= 0; k--)
                    if (items[list[k]].IsStore)
                    {
                        lastStore[b] = list[k];
                        break;
                    }
            }
            // The writes that reach the start of each block.
            var reaches = new Dictionary<Block, HashSet<int>>();
            foreach (Block b in fn.Blocks) reaches[b] = [];
            foreach (Block b in fn.Blocks)
                if (b.Preds.Count == 0)
                    reaches[b].Add(n);
            if (fn.Blocks.Count != 0) reaches[fn.Blocks[0]].Add(n);
            var work = new Queue<Block>(fn.Blocks);
            var queued = new HashSet<Block>(fn.Blocks);
            while (work.Count > 0)
            {
                Block b = work.Dequeue();
                queued.Remove(b);
                HashSet<int> leaves = lastStore.TryGetValue(b, out int last) ? [last] : reaches[b];
                foreach (Block next in b.Succs)
                {
                    if (!reaches.TryGetValue(next, out HashSet<int>? into) || ReferenceEquals(into, leaves)) continue;
                    int before = into.Count;
                    into.UnionWith(leaves);
                    if (into.Count != before && queued.Add(next)) work.Enqueue(next);
                }
            }
            foreach (var (b, list) in inBlock)
            {
                int current = -1;
                foreach (int i in list)
                {
                    if (items[i].IsStore)
                    {
                        current = i;
                        continue;
                    }
                    if (current >= 0) Union(i, current);
                    else
                        foreach (int reaching in reaches[b])
                            Union(i, reaching);
                }
            }
            // What an exception has to do with: everything written in protected code, everything read where
            // an exception leads.
            int kept = -1;
            for (int i = 0; i < n; i++)
            {
                Block b = where[items[i].User].Block;
                bool tied = items[i].IsStore ? fn.IsProtected(b) : afterException.Contains(b) && !argumentLoads.Contains(items[i].User);
                if (!tied) continue;
                if (kept < 0) kept = i;
                else Union(i, kept);
            }
            if (kept < 0) return null;
            int root = Find(kept);
            var free = new List<Access>();
            for (int i = 0; i < n; i++)
                if (Find(i) != root)
                    free.Add(items[i]);
            return free;
        }
        if (accesses.Count == 0 && escapes.Count == 0) return frameObjects;

        // 2. Escaped byte ranges. An escape of unknown extent taints everything above it in the frame.
        var escaped = new List<(int Start, int End)>();
        foreach (var (offset, extent) in escapes)
        {
            // A local lies below the return address (offset 0) and ends there at the latest.
            bool below = offset < 0 && Environment.GetEnvironmentVariable("REWIND_NO_FRAME_BOUND") == null;
            escaped.Add((offset, extent > 0 ? offset + extent : below ? 0 : int.MaxValue));
        }

        bool IsEscaped(int start, int end)
        {
            foreach (var (s, e) in escaped)
                if (start < e && s < end)
                    return true;
            return false;
        }

        // 3. Group accesses into regions of overlapping byte ranges.
        accesses.Sort((x, y) => x.Offset != y.Offset ? x.Offset.CompareTo(y.Offset) : y.Size.CompareTo(x.Size));
        var regions = new List<(int Start, int End, List<Access> Items)>();
        foreach (Access a in accesses)
        {
            if (regions.Count != 0 && a.Offset < regions[^1].End)
            {
                var last = regions[^1];
                last.Items.Add(a);
                regions[^1] = (last.Start, Math.Max(last.End, a.Offset + a.Size), last.Items);
            }
            else regions.Add((a.Offset, a.Offset + a.Size, [a]));
        }

        // 4. Decide per region: one variable, 4-byte cells, or leave in memory.
        var cellOf = new Dictionary<int, int>();          // frame offset -> variable index
        var cellType = new List<VT>();
        var cellOffset = new List<int>();
        var promoted = new HashSet<Node>();

        int NewCell(int offset, VT type)
        {
            cellOf[offset] = cellType.Count;
            cellType.Add(type);
            cellOffset.Add(offset);
            return cellType.Count - 1;
        }

        foreach (var (start, end, items) in regions)
        {
            if (IsEscaped(start, end))
            {
                continue;
            }
            bool uniform = items.All(a => a.Offset == start && a.Size == end - start);
            if (keptForExceptions.Any(k => k.Offset < end && start < k.Offset + k.Size))
            {
                if (!uniform || FreeOfExceptions(items) is not { Count: > 0 } free) continue;
                NewCell(start, VTExtensions.IntOfBytes(end - start));
                foreach (Access a in free) promoted.Add(a.User);
                continue;
            }
            if (uniform)
            {
                NewCell(start, VTExtensions.IntOfBytes(end - start));
                foreach (Access a in items) promoted.Add(a.User);
                continue;
            }
            // Mixed 4- and 8-byte accesses on 4-byte boundaries: split into 4-byte cells.
            bool splittable = (start & 3) == 0 && ((end - start) & 3) == 0 &&
                              items.All(a => a.Size is 4 or 8 && ((a.Offset - start) & 3) == 0);
            if (!splittable) continue;
            for (int o = start; o < end; o += 4) NewCell(o, VT.I32);
            foreach (Access a in items) promoted.Add(a.User);
        }

        // Everything touched but not promoted is a frame object. Merge adjacent/overlapping ranges.
        var memory = new List<(int Start, int End)>();
        foreach (var (start, end, items) in regions)
            if (!items.All(a => promoted.Contains(a.User)))
                memory.Add((start, end));
        foreach (var (offset, extent) in escapes)
            memory.Add((offset, extent > 0 ? offset + extent : offset + 1));
        memory.Sort();
        foreach (var (start, end) in memory)
        {
            if (frameObjects.Count != 0 && start <= frameObjects[^1].Offset + frameObjects[^1].Size)
            {
                FrameObject last = frameObjects[^1];
                last.Size = Math.Max(last.Size, end - last.Offset);
            }
            else frameObjects.Add(new FrameObject { Offset = start, Size = end - start });
        }

        // An argument handed over on the stack whose slot stays memory - its address goes somewhere ("ref" of the
        // parameter), or it is read where an exception leads: what that memory holds when the method starts is
        // the argument. Nothing in the code says so (the caller wrote it), so it is said here, as a store on
        // entry. (Without it the slot is a variable nothing was put in, and reads as zero.)
        if (stackArguments != null && !NoEntryArguments && fn.Entry.Preds.Count == 0)
        {
            int inserted = 0;
            foreach (var (at, bytes) in stackArguments.OrderBy(kv => kv.Key))
            {
                if (bytes is not (1 or 2 or 4 or 8)) continue;
                bool read = false, handedOn = false;
                // (The slot is read as wide as the code reads it: a bool loaded as four bytes, of which one is looked at.)
                int width = bytes;
                foreach (Access a in accesses)
                    if (!a.IsStore && !promoted.Contains(a.User) && a.Offset < at + 8 && at < a.Offset + a.Size)
                    {
                        read = true;
                        if (a.Offset == at && a.Size is 2 or 4 or 8 && a.Size > width) width = a.Size;
                    }
                foreach (var (offset, _) in escapes)
                    if (offset >= at && offset < at + 8)
                        handedOn = true;
                if (!read && !handedOn) continue;
                // (Part of it may still have become a value: that part reads the same entry value.)
                VT type = cellOf.TryGetValue(at, out int cell) ? cellType[cell] : VTExtensions.IntOfBytes(width);
                if (!fn.StackParams.TryGetValue(at, out Node? param))
                {
                    param = fn.NewNode(Op.Param, type, null);
                    param.Imm = Function.StackParamBase + at;
                    fn.StackParams[at] = param;
                }
                // (Said once: the pass runs again as more of the stack is understood.)
                bool said = false;
                foreach (Node n in fn.Entry.Nodes)
                    if (!n.Dead && n.Op == Op.Store && ReferenceEquals(n.In[1], param))
                        said = true;
                if (said) continue;
                ulong address = fn.Entry.Nodes.Count != 0 ? fn.Entry.Nodes[0].Addr : fn.Address;
                Node offsetNode = fn.NewNode(Op.Const, VT.I64, null);
                offsetNode.Imm = at;
                Node slot = fn.NewNode(Op.Add, VT.I64, fn.Entry, sp0, offsetNode);
                slot.Addr = address;
                Node store = fn.NewNode(Op.Store, VT.None, fn.Entry, slot, param);
                store.Addr = address;
                fn.Entry.Nodes.Insert(inserted++, slot);
                fn.Entry.Nodes.Insert(inserted++, store);
            }
        }

        if (cellType.Count == 0) return frameObjects;

        // 5. SSA renaming of the promoted cells. A cell read before any write holds whatever the caller left
        // there: for offsets above the return address, a stack-passed argument.
        Node EntryValue(int cell)
        {
            int offset = cellOffset[cell];
            if (!fn.StackParams.TryGetValue(offset, out Node? param))
            {
                param = fn.NewNode(Op.Param, cellType[cell], null);
                param.Imm = Function.StackParamBase + offset;
                fn.StackParams[offset] = param;
            }
            return param;
        }
        var ssa = new SsaBuilder(fn, cellType.ToArray(), EntryValue);
        var replace = new Dictionary<Node, Node>();
        var cfg = new Cfg(fn);
        var filled = new HashSet<Block>();
        var builder = new IrBuilder(fn);

        foreach (Block block in cfg.ReversePostOrder)
        {
            if (block.Preds.All(filled.Contains)) ssa.Seal(block);
            var old = block.Nodes;
            block.Nodes = new List<Node>(old.Count);
            builder.Current = block;
            foreach (Node n in old)
            {
                if (n.Dead) continue;
                if (!promoted.Contains(n))
                {
                    block.Nodes.Add(n);
                    continue;
                }
                IsStackAddress(n.In[0], out int offset);
                builder.CurrentAddr = n.Addr;
                if (n.Op == Op.Load)
                {
                    Node value;
                    int cell = cellOf[offset];
                    if (cellType[cell].Bytes() == n.Type.Bytes()) value = ssa.Read(cell, block);
                    else value = builder.Concat(ssa.Read(cellOf[offset + 4], block), ssa.Read(cell, block)); // 8-byte read of two cells
                    replace[n] = value;
                }
                else
                {
                    Node value = n.In[1];
                    int cell = cellOf[offset];
                    if (cellType[cell].Bytes() == value.Type.Bytes()) ssa.Write(cell, block, value);
                    else
                    {
                        ssa.Write(cell, block, builder.Trunc(value, VT.I32));
                        ssa.Write(cellOf[offset + 4], block,
                            builder.Trunc(builder.Shift(Op.ShrU, value, builder.Const(VT.I8, 32)), VT.I32));
                    }
                }
                n.Dead = true;
            }
            filled.Add(block);
            foreach (Block s in block.Succs)
                if (!ssa.IsSealed(s) && s.Preds.All(filled.Contains))
                    ssa.Seal(s);
        }
        foreach (Block block in fn.Blocks) ssa.Seal(block);
        ssa.Finish();

        // 6. Apply replacements everywhere.
        Node Resolve(Node n)
        {
            while (replace.TryGetValue(n, out Node? next)) n = ssa.Resolve(next);
            return ssa.Resolve(n);
        }
        foreach (Block block in fn.Blocks)
        {
            foreach (Node n in block.Phis)
                for (int i = 0; i < n.In.Length; i++) n.In[i] = Resolve(n.In[i]);
            foreach (Node n in block.Nodes)
                for (int i = 0; i < n.In.Length; i++) n.In[i] = Resolve(n.In[i]);
        }
        return frameObjects;
    }
}
