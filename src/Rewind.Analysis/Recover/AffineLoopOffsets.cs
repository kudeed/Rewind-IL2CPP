using Rewind.Analysis.Ir;
using Rewind.Analysis.Passes;

namespace Rewind.Analysis.Recover;

/// <summary>Represent a paired native offset induction by its unchanged unit-step index.
/// The identity holds modulo 2^64, including wraparound; it introduces no division or memory access.</summary>
internal static class AffineLoopOffsets
{
    private static bool Step(Node value, Node phi, out long delta)
    {
        delta = 0;
        if (value is not { Op: Op.Add, Type: VT.I64, In.Length: 2 } || value.Dead) return false;
        Node? constant = value.In[0] == phi && value.In[1].IsConst ? value.In[1] : value.In[1] == phi && value.In[0].IsConst ? value.In[0] : null;
        if (constant is not { Type: VT.I64 }) return false;
        delta = constant.Imm; return true;
    }

    internal static int Run(Function fn)
    {
        if (fn.TryRegions.Count != 0 || fn.Blocks.Count == 0) return 0;
        var cfg = new Cfg(fn); int count = 0;
        foreach (var head in fn.Blocks)
        {
            if (head.Preds.Count != 2 || !cfg.IsReachable(head)) continue;
            foreach (var index in head.Phis.ToArray())
            {
                if (index.Dead || index.Type != VT.I64 || index.Op != Op.Phi || index.In.Length != 2) continue;
                for (int back = 0; back < 2; back++)
                {
                    var tail = head.Preds[back];
                    if (tail == head || !cfg.Dominates(head, tail) || !index.In[1-back].IsConstValue(0) ||
                        !Step(index.In[back], index, out long step) || step is not (1 or -1)) continue;
                    foreach (var offset in head.Phis.ToArray())
                    {
                        if (offset == index || offset.Dead || offset.Op != Op.Phi || offset.Type != VT.I64 || offset.In.Length != 2 ||
                            !Step(offset.In[back], offset, out long delta) || delta is < -4096 or > 4096 or 0) continue;
                        Node seed = offset.In[1-back];
                        if (seed.Type != VT.I64 || seed.Dead || seed.Op == Op.Undef ||
                            (seed.Block is { } origin && (origin == head || !cfg.Dominates(origin, head))) ||
                            seed.Block == null && seed.Op is not (Op.Const or Op.Param or Op.SlotValue)) continue;
                        long stride = delta / step;
                        if (stride == 1 && seed.IsConstValue(0)) continue;
                        Node factor = fn.NewNode(Op.Const, VT.I64, null); factor.Imm = stride;
                        Node product = fn.NewNode(Op.Mul, VT.I64, head, index, factor);
                        Node affine = fn.NewNode(Op.Add, VT.I64, head, seed, product);
                        head.Nodes.InsertRange(0, [product, affine]);
                        foreach (var block in fn.Blocks)
                        foreach (var n in block.Phis.Concat(block.Nodes))
                            for (int i = 0; i < n.In.Length; i++) if (n.In[i] == offset) n.In[i] = affine;
                        offset.Dead = true; count++;
                    }
                }
            }
        }
        if (count != 0) DeadCode.Run(fn);
        return count;
    }
}
