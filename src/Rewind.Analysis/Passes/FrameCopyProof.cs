using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Passes;

/// <summary>A byte-proven copy of one closed stack value, including split pointer words.</summary>
public sealed record FrameCopyPlan(int Source, int Target, int Size, Node Complete,
    IReadOnlyList<Node> Stores, IReadOnlyList<Node> Dependencies);

public static class FrameCopyProof
{
    public static int? Offset(Function fn, Node address, int depth = 0)
    {
        if (depth > 12 || !fn.Params.TryGetValue(fn.Regs.StackPointer, out Node? sp)) return null;
        if (ReferenceEquals(address, sp)) return 0;
        if (address.Op is not (Op.Add or Op.Sub) || address.In.Length != 2 || !address.In[1].IsConst ||
            Offset(fn, address.In[0], depth + 1) is not int start) return null;
        long result = address.Op == Op.Add ? (long)start + IrBuilder.SImm(address.In[1]) : (long)start - IrBuilder.SImm(address.In[1]);
        return result is >= int.MinValue and <= int.MaxValue ? (int)result : null;
    }

    private static FrameCopyPlan? Refuse(out string reason, string message) { reason = message; return null; }

    /// <summary>
    /// Proves every named byte is forwarded from the same offset of one unchanged stack object. The caller
    /// must independently prove source/target are the same closed managed type and the consumer takes it.
    /// Padding may be ignored only after all named fields, including full reference words, are covered.
    /// </summary>
    public static FrameCopyPlan? TryProve(Function fn, Block block, IReadOnlyList<Node> region,
        int target, int size, IReadOnlyList<(int Offset, int Size)> fields, out string reason)
    {
        if (size <= 0 || size > 4096 || fields.Count == 0 || (long)target + size > int.MaxValue)
            return Refuse(out reason, "Invalid or unbounded closed layout");
        int previous = 0;
        foreach (var field in fields.OrderBy(f => f.Offset))
        {
            if (field.Offset < previous || field.Size <= 0 || (long)field.Offset + field.Size > size)
                return Refuse(out reason, "Overlapping or out-of-bounds named fields");
            previous = field.Offset + field.Size;
        }
        var stores = new List<Node>();
        foreach (Node node in region.Where(n => !n.Dead))
        {
            if (node.Op is Op.Call or Op.TailCall) return Refuse(out reason, "Call splits target copy");
            if (node.Op is not (Op.Load or Op.Store)) continue;
            int width = node.Op == Op.Load ? node.Type.Bytes() : node.In[1].Type.Bytes();
            int? at = Offset(fn, node.In[0]);
            if (node.Op == Op.Store && at == null) return Refuse(out reason, "Unbounded intervening store");
            if (at == null || at >= (long)target + size || target >= (long)at + width) continue;
            if (node.Op == Op.Load) return Refuse(out reason, "Target observed before complete copy");
            if (at < target || (long)at + width > (long)target + size)
                return Refuse(out reason, "Store crosses target object");
            stores.Add(node);
        }
        if (stores.Count < 2) return Refuse(out reason, "Not a segmented copy");
        var dependencies = new HashSet<Node>();
        var loads = new HashSet<Node>();
        var cache = new Dictionary<Node, int?[]?>();
        int?[]? Bytes(Node n, int depth = 0)
        {
            if (depth > 24 || n.Dead) return null;
            if (cache.TryGetValue(n, out var known)) return known;
            int width = n.Type.Bytes();
            if (width is <= 0 or > 8) return null;
            int?[]? result = null;
            if (n.Op == Op.Load && Offset(fn, n.In[0]) is int start)
            {
                result = Enumerable.Range(0, width).Select(i => (int?)(start + i)).ToArray();
                loads.Add(n);
            }
            else if (n.Op == Op.Trunc && Bytes(n.In[0], depth + 1) is { } wider && width <= wider.Length)
                result = wider.Take(width).ToArray();
            else if (n.Op == Op.ZExt && Bytes(n.In[0], depth + 1) is { } narrow && width >= narrow.Length)
                result = narrow.Concat(Enumerable.Repeat<int?>(null, width - narrow.Length)).ToArray();
            else if (n.Op == Op.Concat && n.In.Length == 2 && width == 8 &&
                     Bytes(n.In[1], depth + 1) is { Length: 4 } low && Bytes(n.In[0], depth + 1) is { Length: 4 } high)
                result = low.Concat(high).ToArray();
            else if (n.Op == Op.ShrU && n.In[1].IsConst && IrBuilder.SImm(n.In[1]) is >= 0 and < 64 and var shift &&
                     shift % 8 == 0 && Bytes(n.In[0], depth + 1) is { } bits && width == bits.Length)
                result = bits.Skip((int)shift / 8).Concat(Enumerable.Repeat<int?>(null, (int)shift / 8)).ToArray();
            if (result != null) dependencies.Add(n);
            cache[n] = result;
            return result;
        }
        var origins = new int?[size];
        foreach (Node store in stores)
        {
            if (Bytes(store.In[1]) is not { } bytes) return Refuse(out reason, "Value is not proven byte transport");
            int at = Offset(fn, store.In[0])!.Value - target;
            Array.Copy(bytes, 0, origins, at, bytes.Length);
        }
        int first = fields.Min(f => f.Offset);
        if (origins[first] is not int firstOrigin) return Refuse(out reason, "First named field has no source");
        int source = firstOrigin - first;
        if ((long)source < (long)target + size && (long)target < (long)source + size)
            return Refuse(out reason, "Source and target overlap");
        foreach (var field in fields)
            for (int i = field.Offset; i < field.Offset + field.Size; i++)
                if (origins[i] != source + i) return Refuse(out reason, "Named field is partial, reordered or comes from different memory");
        foreach (Node load in loads)
            if (Offset(fn, load.In[0]) is not int at || at < source || (long)at + load.Type.Bytes() > (long)source + size)
                return Refuse(out reason, "Transport reads outside source object");
        Node complete = stores[^1];
        var cfg = new Cfg(fn);
        bool StackDerived(Node value)
        {
            // Phi cycles are finite dataflow graphs. A loop counter is not a stack address merely because
            // recursively visiting its backedge reaches a depth limit; an actual path to SP is required.
            var pending = new Stack<Node>();
            var visited = new HashSet<Node>();
            pending.Push(value);
            while (pending.TryPop(out Node? n))
            {
                if (!visited.Add(n)) continue;
                if (fn.Params.TryGetValue(fn.Regs.StackPointer, out Node? sp) && ReferenceEquals(n, sp)) return true;
                if (n.Op is Op.Load or Op.Proj or Op.Const or Op.Param) continue;
                foreach (Node input in n.In) pending.Push(input);
            }
            return false;
        }
        bool MayAddressSource(Node n) => Offset(fn, n) is int at
            ? at >= source && at < (long)source + size
            : StackDerived(n);
        foreach (Node load in loads)
        {
            if (load.Block is not { } origin || !cfg.Dominates(origin, block))
                return Refuse(out reason, "Source snapshot does not dominate copy");
            var todo = new Stack<(Block Block, int End)>();
            todo.Push((block, block.Nodes.IndexOf(complete)));
            var seen = new HashSet<(Block Block, int End)>();
            while (todo.TryPop(out var visit))
            {
                if (!seen.Add(visit)) continue;
                int begin = ReferenceEquals(visit.Block, origin) ? visit.Block.Nodes.IndexOf(load) + 1 : 0;
                if (begin > visit.End + 1) return Refuse(out reason, "Load follows complete copy");
                for (int k = begin; k <= visit.End; k++)
                {
                    Node n = visit.Block.Nodes[k];
                    if (n.Dead) continue;
                    if (n.Op == Op.Store)
                    {
                        if (Offset(fn, n.In[0]) is not int at) return Refuse(out reason, "Source may be changed by unknown store");
                        if (at < (long)source + size && source < (long)at + n.In[1].Type.Bytes())
                            return Refuse(out reason, "Source changes after snapshot");
                    }
                    if (n.Op is Op.Call or Op.TailCall)
                        foreach (Node input in n.In)
                            if (MayAddressSource(input))
                                return Refuse(out reason, "Call may mutate source snapshot");
                }
                if (!ReferenceEquals(visit.Block, origin))
                    foreach (Block predecessor in visit.Block.Preds) todo.Push((predecessor, predecessor.Nodes.Count - 1));
            }
        }
        // A parked pointer could let later code reach the source without a direct frame argument.
        foreach (Node n in fn.Blocks.SelectMany(b => b.Nodes))
            if (!n.Dead && n.Op == Op.Store && MayAddressSource(n.In[1]))
                return Refuse(out reason, "Source address escapes through memory");
        reason = "All named bytes retain source offsets; source is unchanged on every path";
        return new(source, target, size, complete, stores, dependencies.ToArray());
    }
}
