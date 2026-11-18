using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Passes;

/// <summary>
/// Removes what only moves leftovers around.
///
/// A register that holds nothing meaningful - a scratch register on entry, an argument register the method has
/// no parameter for - still gets read: writing one byte of it ("mov al, 1") keeps the other seven, and the
/// compiler copies a struct's padding out of whatever register is at hand. Any value is right for such bits,
/// so they are taken to be zero: masking a leftover gives zero, and storing one to the stack does nothing.
/// </summary>
public static class UndefinedValues
{
    /// <param name="isLeftover">True for an entry value (a Param node) that the calling convention gives no meaning.</param>
    public static bool Run(Function fn, Func<Node, bool> isLeftover)
    {
        var known = new Dictionary<Node, bool>();
        bool Leftover(Node n, int depth = 0)
        {
            if (known.TryGetValue(n, out bool answer)) return answer;
            if (depth > 12) return false;
            answer = n.Op switch
            {
                Op.Undef => true,
                Op.Param => isLeftover(n),
                Op.Trunc or Op.ZExt or Op.SExt or Op.Not or Op.Neg => Leftover(n.In[0], depth + 1),
                Op.Shl or Op.ShrU or Op.ShrS when n.In[1].IsConst => Leftover(n.In[0], depth + 1),
                Op.And or Op.Or or Op.Xor or Op.Add or Op.Sub when n.In.Length == 2 => Leftover(n.In[0], depth + 1) && Leftover(n.In[1], depth + 1),
                _ => false,
            };
            known[n] = answer;
            return answer;
        }

        if (!fn.Params.TryGetValue(fn.Regs.StackPointer, out Node? sp0)) return false;
        bool OnStack(Node address)
        {
            for (int depth = 0; depth < 4; depth++)
            {
                if (ReferenceEquals(address, sp0)) return true;
                if (address.Op != Op.Add || !address.In[1].IsConst) return false;
                address = address.In[0];
            }
            return false;
        }

        var replace = new Dictionary<Node, Node>();
        Node Resolve(Node n)
        {
            for (int guard = 0; guard < 16 && replace.TryGetValue(n, out Node? next); guard++) n = next;
            return n;
        }
        bool changed = false;
        foreach (Block b in fn.Blocks)
        {
            foreach (Node n in b.Nodes)
            {
                if (n.Dead) continue;
                switch (n.Op)
                {
                    case Op.Store when Leftover(n.In[1]) && OnStack(n.In[0]):
                        n.Dead = true;
                        changed = true;
                        break;
                    // Part of a leftover, picked out with a mask: zero.
                    case Op.And when n.In.Length == 2 && n.In[1].IsConst && Leftover(n.In[0]):
                    {
                        Node zero = fn.NewNode(Op.Const, n.Type, null);
                        replace[n] = zero;
                        n.Dead = true;
                        changed = true;
                        break;
                    }
                    // "leftover with a part replaced": with the leftover zero, the part.
                    case Op.Or when n.In.Length == 2:
                    {
                        Node left = Resolve(n.In[0]), right = Resolve(n.In[1]);
                        Node? kept = left.IsConstValue(0) && replace.ContainsKey(n.In[0]) ? right
                            : right.IsConstValue(0) && replace.ContainsKey(n.In[1]) ? left : null;
                        if (kept == null || kept.Type != n.Type) break;
                        replace[n] = kept;
                        n.Dead = true;
                        changed = true;
                        break;
                    }
                }
            }
        }
        if (!changed) return false;
        foreach (Block b in fn.Blocks)
        {
            b.Nodes.RemoveAll(n => n.Dead);
            foreach (Node n in b.Phis)
                for (int i = 0; i < n.In.Length; i++) n.In[i] = Resolve(n.In[i]);
            foreach (Node n in b.Nodes)
                for (int i = 0; i < n.In.Length; i++) n.In[i] = Resolve(n.In[i]);
        }
        return true;
    }
}
