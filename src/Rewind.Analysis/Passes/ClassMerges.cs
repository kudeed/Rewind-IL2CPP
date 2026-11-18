using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Passes;

/// <summary>
/// Undoes a merge of code that differs only in which class (or method) it is about.
///
/// "new A(x)" on one path and "new B(x)" on another, with A and B laid out alike, compile to the same
/// instructions but for the class - so the compiler keeps one copy of them and brings the class along in a
/// register. The managed program has no "class in a variable" there: it has two allocations. The shared block
/// is given back to each way in, with the class that way brings; what the copies compute meets again in the
/// blocks after them.
/// </summary>
public static class ClassMerges
{
    private const int MaxNodes = 64, MaxWays = 4;

    /// <param name="isClassOrMethod">True when a metadata slot holds a class or a method (what must not travel in a variable).</param>
    /// <summary>
    /// The same un-merging on request: the blocks of the given merged values are given back to each way in.
    /// Asked for once the method has been translated and a merged object turned out to be used as a class none
    /// of its values has in common - "a.x = 1" and "b.y = 1" compiled into one store at one offset.
    /// </summary>
    public static bool SplitAt(Function fn, IEnumerable<Node> merged)
    {
        bool changed = false;
        foreach (Node phi in merged)
        {
            if (phi.Dead || phi.Op != Op.Phi) continue;
            Block? j = fn.Blocks.FirstOrDefault(b => b.Phis.Contains(phi));
            if (j == null || j.Preds.Count < 2 || j.Preds.Count > MaxWays || j.Nodes.Count > MaxNodes) continue;
            if (!Separable(fn, j, DeadCode.Uses(fn))) continue;
            Split(fn, j);
            changed = true;
        }
        if (changed)
            for (int i = 0; i < fn.Blocks.Count; i++) fn.Blocks[i].Id = i;
        return changed;
    }

    /// <param name="isMetadataSlot">
    /// When given: also undo a merge in which each way in brings the address of a metadata slot (what the
    /// metadata initializer is handed) - the same code for two string literals or two classes, kept once.
    /// </param>
    public static bool Run(Function fn, Func<ulong, bool> isClassOrMethod, Func<ulong, bool>? isMetadataSlot = null)
    {
        bool changed = false;
        for (int round = 0; round < 4; round++)
        {
            Dictionary<Node, List<Node>>? uses = null;
            bool any = false;
            foreach (Block j in fn.Blocks.ToList())
            {
                if (!MergesClasses(j, isClassOrMethod) && (isMetadataSlot == null || !MergesSlotAddresses(j, isMetadataSlot))) continue;
                uses ??= DeadCode.Uses(fn);
                if (!Separable(fn, j, uses)) continue;
                Split(fn, j);
                uses = null;
                any = true;
            }
            if (!any) break;
            changed = true;
        }
        if (changed)
            for (int i = 0; i < fn.Blocks.Count; i++) fn.Blocks[i].Id = i;
        return changed;
    }

    private static bool MergesClasses(Block j, Func<ulong, bool> isClassOrMethod)
    {
        if (j.Preds.Count < 2 || j.Preds.Count > MaxWays || j.Nodes.Count > MaxNodes) return false;
        foreach (Node phi in j.Phis)
        {
            if (phi.Dead || phi.In.Length != j.Preds.Count) continue;
            // Each way in brings a class: one named outright, or one read from somewhere (an object's own class).
            bool all = true, differ = false, named = false;
            foreach (Node input in phi.In)
            {
                if (input.Op == Op.SlotValue && isClassOrMethod((ulong)input.Imm)) named = true;
                else if (input.Op != Op.Load || input.Type != VT.I64) { all = false; break; }
                if (!ReferenceEquals(input, phi.In[0]) && !(input.Op == Op.SlotValue && phi.In[0].Op == Op.SlotValue && input.Imm == phi.In[0].Imm)) differ = true;
            }
            if (all && differ && named) return true;
        }
        return false;
    }

    private static bool MergesSlotAddresses(Block j, Func<ulong, bool> isMetadataSlot)
    {
        if (j.Preds.Count < 2 || j.Preds.Count > MaxWays || j.Nodes.Count > MaxNodes) return false;
        foreach (Node phi in j.Phis)
        {
            if (phi.Dead || phi.In.Length != j.Preds.Count || !phi.Type.IsInt()) continue;
            if (phi.In.All(i => i.IsConst && isMetadataSlot(i.UImm)) && phi.In.Any(i => i.UImm != phi.In[0].UImm)) return true;
        }
        return false;
    }

    private static bool Separable(Function fn, Block j, Dictionary<Node, List<Node>> uses)
    {
        if (ReferenceEquals(j, fn.Entry) || j.Preds.Contains(j) || j.Succs.Contains(j)) return false;
        if (j.Preds.Distinct().Count() != j.Preds.Count) return false;
        // Try statements keep their shape: nothing next to a gate is copied.
        if (j.Terminator is { Op: Op.Branch } own && Function.IsTryEntry(own.In[0])) return false;
        foreach (Block p in j.Preds)
            if (p.Terminator is { Op: Op.Branch } t && Function.IsTryEntry(t.In[0]))
                return false;
        foreach (Node phi in j.Phis)
            if (!phi.Dead && phi.In.Length != j.Preds.Count)
                return false;

        // What the block computes may be used after it only where the ways meet again: as what a merged value
        // of a following block takes from this block.
        var inside = new HashSet<Node>();
        foreach (Node n in j.Phis) if (!n.Dead) inside.Add(n);
        foreach (Node n in j.Nodes) if (!n.Dead) inside.Add(n);
        var merges = new Dictionary<Node, Block>();
        foreach (Block s in j.Succs)
            foreach (Node phi in s.Phis)
                if (!phi.Dead) merges[phi] = s;
        foreach (Node n in inside)
        {
            if (!uses.TryGetValue(n, out List<Node>? users)) continue;
            foreach (Node user in users)
            {
                if (inside.Contains(user)) continue;
                if (!merges.TryGetValue(user, out Block? at) || user.In.Length != at.Preds.Count) return false;
                for (int i = 0; i < user.In.Length; i++)
                    if (ReferenceEquals(user.In[i], n) && !ReferenceEquals(at.Preds[i], j))
                        return false;
            }
        }
        return true;
    }

    private static object? CopyAux(object? aux) => aux switch
    {
        CallInfo c => new CallInfo { Target = c.Target, Indirect = c.Indirect, Intrinsic = c.Intrinsic, NoReturn = c.NoReturn, Slots = [.. c.Slots] },
        List<Block> targets => new List<Block>(targets),
        _ => aux,
    };

    private static void Split(Function fn, Block j)
    {
        int ways = j.Preds.Count;
        for (int way = 1; way < ways; way++)
        {
            Block p = j.Preds[way];
            var copy = new Block { Start = j.Start, End = j.End, Scope = j.Scope };
            var map = new Dictionary<Node, Node>();
            foreach (Node phi in j.Phis)
                if (!phi.Dead) map[phi] = phi.In[way];
            foreach (Node n in j.Nodes)
            {
                if (n.Dead) continue;
                var inputs = new Node[n.In.Length];
                for (int i = 0; i < inputs.Length; i++) inputs[i] = map.GetValueOrDefault(n.In[i], n.In[i]);
                Node c = fn.NewNode(n.Op, n.Type, copy, inputs);
                c.Imm = n.Imm;
                c.Addr = n.Addr;
                c.Aux = CopyAux(n.Aux);
                copy.Nodes.Add(c);
                map[n] = c;
            }
            copy.Preds.Add(p);
            foreach (Block s in j.Succs) copy.Succs.Add(s);
            // Each block after gets one more way in (per edge), bringing the copy's values.
            foreach (Block s in j.Succs.Distinct())
            {
                var edges = new List<int>();
                for (int i = 0; i < s.Preds.Count; i++)
                    if (ReferenceEquals(s.Preds[i], j)) edges.Add(i);
                foreach (int edge in edges)
                {
                    s.Preds.Add(copy);
                    foreach (Node phi in s.Phis)
                    {
                        if (phi.Dead || edge >= phi.In.Length) continue;
                        var inputs = new Node[phi.In.Length + 1];
                        phi.In.CopyTo(inputs, 0);
                        inputs[^1] = map.GetValueOrDefault(phi.In[edge], phi.In[edge]);
                        phi.In = inputs;
                    }
                }
            }
            for (int i = 0; i < p.Succs.Count; i++)
                if (ReferenceEquals(p.Succs[i], j)) p.Succs[i] = copy;
            if (p.Terminator is { Op: Op.Switch, Aux: List<Block> targets })
                for (int i = 0; i < targets.Count; i++)
                    if (ReferenceEquals(targets[i], j)) targets[i] = copy;
            fn.Blocks.Add(copy);
        }
        // The block itself stays for the first way in.
        foreach (Node phi in j.Phis)
            if (!phi.Dead) phi.In = [phi.In[0]];
        j.Preds.RemoveRange(1, ways - 1);
    }
}
