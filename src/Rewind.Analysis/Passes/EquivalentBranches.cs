using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Passes;

/// <summary>Removes a control choice only when both arms make the same exact equality decision.</summary>
public static class EquivalentBranches
{
    private static bool Same(Node a, Node b) => ReferenceEquals(a, b) ||
        a.Op == Op.Const && b.Op == Op.Const && a.Type == b.Type && a.Imm == b.Imm;

    private static Node? Comparison(Block arm)
    {
        if (arm.Phis.Count != 0 || arm.Succs.Count != 2 || ReferenceEquals(arm.Succs[0], arm.Succs[1])) return null;
        var nodes = arm.Nodes.Where(n => !n.Dead).ToArray();
        if (nodes.Length != 2 || nodes[0] is not { Op: Op.CmpEq or Op.CmpNe, Type: VT.I1 } condition ||
            condition.In.Length != 2 || condition.In[0].Type != condition.In[1].Type ||
            condition.In[0].Type.IsFloat() || nodes[1] is not { Op: Op.Branch } term || term.In.Length != 1 ||
            !ReferenceEquals(term.In[0], condition)) return null;
        return condition;
    }

    public static int Run(Function fn)
    {
        if (fn.TryRegions.Count != 0) return 0;
        int changed = 0;
        foreach (Block guard in fn.Blocks.ToArray())
        {
            if (!fn.Blocks.Contains(guard) || guard.Scope != -1 || guard.Terminator is not { Op: Op.Branch } term ||
                term.In.Length != 1 || Function.IsTryEntry(term.In[0]) || guard.Succs.Count != 2) continue;
            Block a = guard.Succs[0], b = guard.Succs[1];
            if (ReferenceEquals(a, b) || ReferenceEquals(a, guard) || ReferenceEquals(b, guard) ||
                a.Scope != -1 || b.Scope != -1 || a.Preds.Count != 1 || b.Preds.Count != 1 ||
                !ReferenceEquals(a.Preds[0], guard) || !ReferenceEquals(b.Preds[0], guard) ||
                Comparison(a) is not { } left || Comparison(b) is not { } right) continue;
            bool operands = Same(left.In[0], right.In[0]) && Same(left.In[1], right.In[1]) ||
                Same(left.In[0], right.In[1]) && Same(left.In[1], right.In[0]);
            if (!operands) continue;
            int reverse = left.Op == right.Op ? 0 : 1;
            if (!ReferenceEquals(a.Succs[0], b.Succs[reverse]) || !ReferenceEquals(a.Succs[1], b.Succs[1 - reverse]) ||
                a.Succs.Any(s => ReferenceEquals(s, guard) || ReferenceEquals(s, a) || ReferenceEquals(s, b))) continue;
            var cfg = new Cfg(fn);
            bool Available(Node n) => n.Block == null && n.Op is Op.Param or Op.Const or Op.SlotValue ||
                n.Block is { } at && at != a && at != b && cfg.Dominates(at, guard) &&
                (at != guard || guard.Nodes.IndexOf(n) >= 0 && guard.Nodes.IndexOf(n) < guard.Nodes.IndexOf(term));
            if (!left.In.All(Available) || !right.In.All(Available)) continue;
            var uses = DeadCode.Uses(fn);
            bool Private(Node condition, Block owner) => !uses.TryGetValue(condition, out var readers) ||
                readers.All(n => n.Dead || ReferenceEquals(n, owner.Terminator));
            if (!Private(left, a) || !Private(right, b)) continue;
            bool samePhis = true;
            foreach (Block join in a.Succs)
            {
                int ia = join.Preds.IndexOf(a), ib = join.Preds.IndexOf(b);
                if (ia < 0 || ib < 0 || join.Preds.Count(p => ReferenceEquals(p, a)) != 1 ||
                    join.Preds.Count(p => ReferenceEquals(p, b)) != 1 ||
                    join.Phis.Any(phi => phi.In.Length != join.Preds.Count || !Same(phi.In[ia], phi.In[ib])))
                { samePhis = false; break; }
            }
            if (!samePhis) continue;
            // Preserve every guard operation and the retained arm. Only the redundant pure arm disappears.
            foreach (Block join in b.Succs)
            {
                int index = join.Preds.IndexOf(b);
                join.Preds.RemoveAt(index);
                foreach (Node phi in join.Phis) phi.In = phi.In.Where((_, i) => i != index).ToArray();
            }
            foreach (Node node in b.Nodes) node.Dead = true;
            b.Preds.Clear(); b.Succs.Clear();
            fn.Blocks.Remove(b);
            term.Op = Op.Jump; term.In = [];
            guard.Succs = [a];
            changed++;
        }
        if (changed != 0)
            for (int i = 0; i < fn.Blocks.Count; i++) fn.Blocks[i].Id = i;
        return changed;
    }
}
