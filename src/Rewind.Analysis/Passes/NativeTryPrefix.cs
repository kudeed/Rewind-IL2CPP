using Rewind.Analysis.Ir;
using Rewind.Binary;

namespace Rewind.Analysis.Passes;

/// <summary>
/// A conservative correction of a widened Itanium try gate. A linear entry
/// prefix can include a call that is explicitly outside all landing pads,
/// followed by the stores that initialize the object used by the handler.
/// Put that prefix before the artificial gate, keeping its native ordering.
/// Do not infer protection from a missing call-site entry.
/// </summary>
internal static class NativeTryPrefix
{
    internal static bool Unprotected(ulong pc, IReadOnlyList<CallSite> sites)
    {
        if (pc == 0) return false;
        var matching = sites.Where(s => s.Start <= pc && pc < s.End).ToArray();
        return matching is [{LandingPad:0, Action:0, Filter:0}];
    }

    internal static int Run(Function fn, IReadOnlyList<CallSite> sites)
    {
        if (Environment.GetEnvironmentVariable("REWIND_NO_NATIVE_TRY_PREFIX") != null ||
            fn.TryRegions.Count == 0 || !fn.Params.TryGetValue(fn.Regs.StackPointer, out Node? sp)) return 0;
        int result = 0;
        int Depth(int region)
        {
            int depth = 0;
            for (int scope = fn.TryRegions[region].Outer; scope >= 0 && depth <= fn.TryRegions.Count; depth++)
                scope = fn.TryRegions[scope >> 1].Outer;
            return depth;
        }
        // Move through an inner gate before its outer gate. Every moved
        // memory operation/call must have explicit native evidence that no
        // landing pad protects it, including the surrounding region.
        foreach (var (gate, region) in fn.TryGates().OrderByDescending(g => Depth(g.Region)).ToArray())
        {
            if (gate.Scope != fn.TryRegions[region].Outer) continue;
            Block body = gate.Succs[1];
            if (body.Scope != 2 * region || body.Preds.Count != 1 || body.Preds[0] != gate ||
                body.Phis.Any(p => !p.Dead) || body.Terminator == null) continue;
            var inside = body.Nodes.ToHashSet();
            var moved = new List<Node>();
            var available = new HashSet<Node>();
            bool callSeen = false, parked = false;
            bool Stack(Node n) => n == sp || n is {Op:Op.Add,Type:VT.I64,In.Length:2} &&
                n.In[0] == sp && n.In[1].IsConst;
            foreach (Node n in body.Nodes)
            {
                if (n.Dead) continue;
                if (n.IsTerminator || n.In.Any(i => inside.Contains(i) && !available.Contains(i))) break;
                if (n.Op == Op.Call)
                {
                    if (n.Aux is not CallInfo {Indirect:false,Intrinsic:null,NoReturn:false} ||
                        !Unprotected(n.Addr,sites)) break;
                    callSeen = true;
                }
                else if (n.Op is Op.Load or Op.Store)
                {
                    if (!Unprotected(n.Addr,sites)) break;
                    if (callSeen && n.Op == Op.Store && n.In[1].Type == VT.I64 && Stack(n.In[1])) parked = true;
                }
                else if (n.Op is not (Op.Add or Op.Sub or Op.Proj or Op.Const or Op.Trunc or Op.ZExt or Op.SExt or Op.Concat or
                    Op.CmpEq or Op.CmpNe or Op.And or Op.Or or Op.Xor or Op.Shl or Op.ShrU or Op.ShrS or
                    Op.BitsToF or Op.FToBits)) break;
                moved.Add(n); available.Add(n);
            }
            // Only this compiler shape is accepted: at least one definitely
            // unprotected call, and a subsequent parked stack pointer.
            // The ordinary TryPrologues pass handles store-only prefixes.
            if (!callSeen || !parked) continue;
            // The TryEntry predicate is the artificial exceptional fork.
            // Put preparation before it as well as before the branch, so an
            // enclosing gate can move this prefix out in its own turn.
            int at = gate.Terminator is { In.Length: 1 } branch
                ? gate.Nodes.IndexOf(branch.In[0]) : -1;
            if (at < 0) continue;
            foreach (Node n in moved)
            {
                body.Nodes.Remove(n);
                n.Block = gate;
                gate.Nodes.Insert(at++,n);
            }
            result += moved.Count;
        }
        return result;
    }
}
