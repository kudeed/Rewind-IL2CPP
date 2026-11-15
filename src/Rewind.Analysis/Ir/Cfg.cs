namespace Rewind.Analysis.Ir;

/// <summary>Orderings and dominance for a function's control flow graph.</summary>
public sealed class Cfg
{
    public readonly List<Block> ReversePostOrder = [];
    private readonly Dictionary<Block, int> _rpoIndex = [];
    private readonly Dictionary<Block, Block?> _idom = [];

    public Cfg(Function fn)
    {
        if (fn.Blocks.Count == 0) return;
        var visited = new HashSet<Block>();
        var post = new List<Block>();
        // Iterative depth-first search (functions can be deep enough to overflow the native stack).
        var stack = new Stack<(Block Block, int Next)>();
        stack.Push((fn.Entry, 0));
        visited.Add(fn.Entry);
        while (stack.Count > 0)
        {
            var (block, next) = stack.Pop();
            if (next < block.Succs.Count)
            {
                stack.Push((block, next + 1));
                Block s = block.Succs[next];
                if (visited.Add(s)) stack.Push((s, 0));
            }
            else post.Add(block);
        }
        post.Reverse();
        ReversePostOrder.AddRange(post);
        for (int i = 0; i < post.Count; i++) _rpoIndex[post[i]] = i;
        ComputeDominators(fn.Entry);
    }

    public bool IsReachable(Block b) => _rpoIndex.ContainsKey(b);
    public int Order(Block b) => _rpoIndex.GetValueOrDefault(b, int.MaxValue);
    public Block? ImmediateDominator(Block b) => _idom.GetValueOrDefault(b);

    /// <summary>Cooper, Harvey and Kennedy's iterative dominator algorithm.</summary>
    private void ComputeDominators(Block entry)
    {
        _idom[entry] = entry;
        bool changed = true;
        while (changed)
        {
            changed = false;
            for (int i = 1; i < ReversePostOrder.Count; i++)
            {
                Block b = ReversePostOrder[i];
                Block? best = null;
                foreach (Block p in b.Preds)
                {
                    if (!_idom.ContainsKey(p)) continue;
                    best = best == null ? p : Intersect(p, best);
                }
                if (best != null && (!_idom.TryGetValue(b, out Block? old) || !ReferenceEquals(old, best)))
                {
                    _idom[b] = best;
                    changed = true;
                }
            }
        }
        _idom[entry] = null;
    }

    private Block Intersect(Block a, Block b)
    {
        while (!ReferenceEquals(a, b))
        {
            while (_rpoIndex[a] > _rpoIndex[b]) a = _idom[a]!;
            while (_rpoIndex[b] > _rpoIndex[a]) b = _idom[b]!;
        }
        return a;
    }

    public bool Dominates(Block a, Block b)
    {
        for (Block? x = b; x != null; x = _idom.GetValueOrDefault(x))
            if (ReferenceEquals(x, a))
                return true;
        return false;
    }
}
