using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Passes;

/// <summary>Removes values nothing observes. Stores, calls and block terminators are the roots.</summary>
public static class DeadCode
{
    public static int Run(Function fn)
    {
        var live = new HashSet<Node>();
        var work = new Stack<Node>();

        void Mark(Node n)
        {
            if (!n.Dead && live.Add(n)) work.Push(n);
        }

        foreach (Block b in fn.Blocks)
            foreach (Node n in b.Nodes)
                if (!n.Dead && (n.Op is Op.Store or Op.Call || n.IsTerminator))
                    Mark(n);

        while (work.Count > 0)
        {
            Node n = work.Pop();
            foreach (Node input in n.In) Mark(input);
        }

        int removed = 0;
        foreach (Block b in fn.Blocks)
        {
            removed += b.Nodes.RemoveAll(n =>
            {
                if (live.Contains(n)) return false;
                n.Dead = true;
                return true;
            });
            removed += b.Phis.RemoveAll(n =>
            {
                if (live.Contains(n)) return false;
                n.Dead = true;
                return true;
            });
        }
        return removed;
    }

    /// <summary>Use lists for every live node, in block order (a node appears once per input position).</summary>
    public static Dictionary<Node, List<Node>> Uses(Function fn)
    {
        var uses = new Dictionary<Node, List<Node>>();
        void Record(Node user)
        {
            foreach (Node input in user.In)
            {
                if (!uses.TryGetValue(input, out List<Node>? list)) uses[input] = list = [];
                list.Add(user);
            }
        }
        foreach (Block b in fn.Blocks)
        {
            foreach (Node n in b.Phis) if (!n.Dead) Record(n);
            foreach (Node n in b.Nodes) if (!n.Dead) Record(n);
        }
        return uses;
    }
}
