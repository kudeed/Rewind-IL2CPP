using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Recover;

// This proof is used only by the native metadata cold-arm proof. General
// constant folding keeps rejecting cyclic phis. A page can survive nested
// native loops through phis without changing any of its integer bits.
internal static class StableMetadataPagePhiProof
{
    internal static bool TryAddress(Function fn, Node address, out ulong value)
    {
        if (Normalizer.FlagConstant(address, out value)) return true;
        value = 0;
        if (address is not { Op: Op.Add, Type: VT.I64, In.Length: 2 } ||
            address.In[0].Op != Op.Phi ||
            address.In[1] is not { IsConst: true, Type: VT.I64 } offset || offset.UImm >= 4096)
            return false;

        var blocks = fn.Blocks.ToHashSet();
        var reachable = new HashSet<Block>();
        var pendingBlocks = new Stack<Block>();
        pendingBlocks.Push(fn.Entry);
        while (pendingBlocks.TryPop(out var block))
        {
            if (!blocks.Contains(block)) return false;
            if (!reachable.Add(block)) continue;
            foreach (var successor in block.Succs) pendingBlocks.Push(successor);
        }

        var pending = new Stack<Node>();
        var seen = new HashSet<Node>();
        pending.Push(address.In[0]);
        ulong page = 0;
        bool seeded = false;
        while (pending.TryPop(out var phi))
        {
            if (!seen.Add(phi)) continue;
            if (seen.Count > 256 || phi.Op != Op.Phi || phi.Type != VT.I64 ||
                phi.Block is not { } owner || owner == fn.Entry ||
                !reachable.Contains(owner) || !owner.Phis.Contains(phi) ||
                phi.In.Length == 0 || phi.In.Length != owner.Preds.Count ||
                owner.Preds.Any(p => !blocks.Contains(p) || !p.Succs.Contains(owner)))
                return false;
            foreach (var input in phi.In)
            {
                if (input.Type != VT.I64) return false;
                if (input.Op == Op.Phi)
                {
                    pending.Push(input);
                    continue;
                }
                // A changing induction expression, load, parameter or undef
                // is never a page seed, even when some arms are literal.
                if (!input.IsConst || input.UImm == 0 || (input.UImm & 4095) != 0 ||
                    seeded && input.UImm != page)
                    return false;
                page = input.UImm;
                seeded = true;
            }
        }
        if (!seeded || page > ulong.MaxValue - offset.UImm) return false;
        value = page + offset.UImm;
        return true;
    }
    // Exact integer snapshots carried unchanged through real CFG loops. This
    // is limited to metadata slot arguments and their initialization mark;
    // general folding still rejects cyclic phis.
    internal static bool TryValue(Function fn, Node root, out ulong value)
    {
        if (Normalizer.FlagConstant(root, out value)) return true;
        value = 0;
        if (root.Op != Op.Phi || root.Type != VT.I64) return false;
        var blocks = fn.Blocks.ToHashSet();
        var reachable = new HashSet<Block>();
        var work = new Stack<Block>();work.Push(fn.Entry);
        while (work.TryPop(out var block))
        {
            if (!blocks.Contains(block)) return false;
            if (!reachable.Add(block)) continue;
            foreach (var successor in block.Succs) work.Push(successor);
        }
        var pending = new Stack<Node>();pending.Push(root);
        var seen = new HashSet<Node>();var grounded = new HashSet<Node>();bool seeded = false;ulong exact = 0;
        while (pending.TryPop(out var phi))
        {
            if (!seen.Add(phi)) continue;
            if (seen.Count > 256 || phi.Op != Op.Phi || phi.Type != VT.I64 ||
                phi.Block is not { } owner || owner == fn.Entry || !reachable.Contains(owner) ||
                !owner.Phis.Contains(phi) || phi.In.Length == 0 || phi.In.Length != owner.Preds.Count ||
                owner.Preds.Any(p => !blocks.Contains(p) || !p.Succs.Contains(owner))) return false;
            foreach (var input in phi.In)
            {
                if (input.Type != VT.I64) return false;
                if (input.Op == Op.Phi) { pending.Push(input);continue; }
                if (!input.IsConst || seeded && input.UImm != exact) return false;
                exact = input.UImm;seeded = true;grounded.Add(phi);
            }
        }
        if (!seeded) return false;
        // Every dependency component must reach a real constant seed. One
        // seeded arm cannot justify a separate uninitialized cycle.
        for (int pass=0;pass<seen.Count;pass++)
        {
            int before=grounded.Count;
            foreach(var phi in seen)
                if(phi.In.Any(input=>input.Op==Op.Phi && grounded.Contains(input)))grounded.Add(phi);
            if(before==grounded.Count)break;
        }
        if(seen.Any(phi=>!grounded.Contains(phi)))return false;
        value = exact;return true;
    }

}
