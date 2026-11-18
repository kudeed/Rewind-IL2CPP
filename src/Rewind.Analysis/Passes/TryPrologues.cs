using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Passes;

/// <summary>
/// Stack stores at the very start of a try statement, before anything in it can raise an exception, belong to
/// the code before it.
///
/// With table-driven exception handling (AArch64: Itanium landing pads) only calls raise exceptions. The handler
/// is entered from the try statement's gate, as if an exception could come before the first instruction; a
/// value the protected code stores first thing - the variable of a using statement, the address of it that the
/// shared finally code reads - then looks unset on the handler's way. Nothing between the gate and the first call
/// can be skipped by an exception, so those stores are made before the gate: the handler sees them, as the
/// program does.
/// </summary>
public static class TryPrologues
{
    public static bool Run(Function fn)
    {
        if (fn.TryRegions.Count == 0 || !fn.Params.TryGetValue(fn.Regs.StackPointer, out Node? sp0)) return false;
        bool OnStack(Node address) =>
            ReferenceEquals(address, sp0) || (address.Op == Op.Add && ReferenceEquals(address.In[0], sp0) && address.In[1].IsConst);
        bool changed = false;
        foreach (var (gate, _) in fn.TryGates().ToList())
        {
            Block body = gate.Succs[1];
            if (body.Preds.Count != 1 || !ReferenceEquals(body.Preds[0], gate) || body.Phis.Count != 0) continue;
            var moved = new List<Node>();
            var inside = new HashSet<Node>(body.Nodes);
            foreach (Node n in body.Nodes)
            {
                if (n.Dead) continue;
                // Address arithmetic, and reads and writes of the stack, in their order.
                bool available = n.In.All(i => !inside.Contains(i) || moved.Contains(i));
                bool move = available && (n.Op == Op.Add && n.Type == VT.I64 && n.In[1].IsConst ||
                                          n.Op is Op.Store or Op.Load && OnStack(n.In[0]));
                if (!move) break;
                moved.Add(n);
            }
            if (!moved.Any(n => n.Op == Op.Store)) continue;
            int at = gate.Nodes.Count - 1; // before the branch on the gate
            foreach (Node n in moved)
            {
                body.Nodes.Remove(n);
                n.Block = gate;
                gate.Nodes.Insert(at++, n);
            }
            changed = true;
        }
        return changed;
    }
}
