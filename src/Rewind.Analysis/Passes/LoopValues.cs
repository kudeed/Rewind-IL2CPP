using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;

namespace Rewind.Analysis.Passes;

/// <summary>
/// Undoes what an optimizing compiler does to the variables of a loop, so that merged values read as the
/// program's own variables again:
///
/// - a 32-bit variable kept in a 64-bit register becomes a 32-bit merged value again;
/// - two registers that carry the same value around a loop become one value;
/// - a pointer that walks an array in step with a counter ("strength reduction") becomes the address of
///   element [counter] again, which is also what makes the access expressible as an array access at all:
///   the compiler computes "address of element 0" before the loop even when the array is empty, something
///   the source never did.
/// </summary>
public static class LoopValues
{
    /// <param name="callObserves">
    /// Optional: how many low bits of a value a call looks at when the value is one of its arguments (a bool
    /// parameter looks at 8, whatever else the register holds).
    /// </param>
    public static bool Run(Function fn, Func<Node, Node, int>? callObserves = null)
    {
        bool changed = false;
        for (int round = 0; round < 4; round++)
        {
            bool step = MergeCongruentPhis(fn);
            step |= NarrowPhis(fn);
            step |= NarrowToObserved(fn, callObserves);
            if (step) DeadCode.Run(fn);
            step |= RewritePointerInduction(fn);
            step |= RewriteScaledOffsets(fn);
            if (!step) break;
            DeadCode.Run(fn);
            changed = true;
        }
        return changed;
    }

    // ---- shared helpers ----------------------------------------------------------------------------------------

    private static void Replace(Function fn, Dictionary<Node, Node> replace)
    {
        if (replace.Count == 0) return;
        Node Resolve(Node n)
        {
            int guard = 0;
            while (replace.TryGetValue(n, out Node? next) && guard++ < 64) n = next;
            return n;
        }
        foreach (Block b in fn.Blocks)
        {
            foreach (Node n in b.Phis)
                for (int i = 0; i < n.In.Length; i++) n.In[i] = Resolve(n.In[i]);
            foreach (Node n in b.Nodes)
                for (int i = 0; i < n.In.Length; i++) n.In[i] = Resolve(n.In[i]);
        }
    }

    /// <summary>Re-applies the folding of extensions and truncations after their operands changed.</summary>
    private static void Refold(Function fn)
    {
        var replace = new Dictionary<Node, Node>();
        bool changed = true;
        for (int round = 0; changed && round < 8; round++)
        {
            changed = false;
            foreach (Block b in fn.Blocks)
            {
                foreach (Node n in b.Nodes)
                {
                    if (n.Dead || n.In.Length != 1) continue;
                    Node inner = n.In[0];
                    if (n.Op == Op.Trunc && inner.Op is Op.ZExt or Op.SExt)
                    {
                        Node source = inner.In[0];
                        if (source.Type == n.Type)
                        {
                            replace[n] = source;
                            n.Dead = true;
                        }
                        else if (source.Type.Bits() > n.Type.Bits()) n.In = [source];
                        else
                        {
                            n.Op = inner.Op;
                            n.In = [source];
                        }
                        changed = true;
                    }
                    else if (n.Op == Op.Trunc && inner.Op == Op.Trunc)
                    {
                        n.In = [inner.In[0]];
                        changed = true;
                    }
                    else if (n.Op is Op.ZExt or Op.SExt && inner.Op == Op.ZExt)
                    {
                        n.Op = Op.ZExt; // the sign bit of a zero-extended value is clear
                        n.In = [inner.In[0]];
                        changed = true;
                    }
                    else if (n.Op == Op.SExt && inner.Op == Op.SExt)
                    {
                        n.In = [inner.In[0]];
                        changed = true;
                    }
                }
                b.Nodes.RemoveAll(x => x.Dead);
            }
            if (replace.Count != 0)
            {
                Replace(fn, replace);
                replace.Clear();
            }
        }
    }

    // ---- one value in two registers ----------------------------------------------------------------------------

    private static bool SameAssuming(Node x, Node y, Node a, Node b, int depth = 0)
    {
        if (ReferenceEquals(x, y)) return true;
        if ((ReferenceEquals(x, a) && ReferenceEquals(y, b)) || (ReferenceEquals(x, b) && ReferenceEquals(y, a))) return true;
        if (depth > 10 || x.Op != y.Op || x.Type != y.Type || x.In.Length != y.In.Length) return false;
        switch (x.Op)
        {
            case Op.Const or Op.SlotValue:
                return x.Imm == y.Imm;
            case Op.Load or Op.Call or Op.Proj or Op.Phi or Op.Param or Op.Undef or Op.Store:
                return false;
        }
        if (x.IsTerminator || x.Imm != y.Imm) return false;
        for (int i = 0; i < x.In.Length; i++)
            if (!SameAssuming(x.In[i], y.In[i], a, b, depth + 1))
                return false;
        return true;
    }

    private static bool MergeCongruentPhis(Function fn)
    {
        var replace = new Dictionary<Node, Node>();
        foreach (Block block in fn.Blocks)
        {
            List<Node> phis = block.Phis;
            if (phis.Count < 2 || phis.Count > 96) continue;
            for (int i = 0; i < phis.Count; i++)
            {
                Node a = phis[i];
                if (a.Dead || a.Type == VT.Flags) continue;
                for (int j = i + 1; j < phis.Count; j++)
                {
                    Node b = phis[j];
                    if (b.Dead || b.Type != a.Type || b.In.Length != a.In.Length) continue;
                    bool same = true;
                    for (int k = 0; k < a.In.Length && same; k++) same = SameAssuming(a.In[k], b.In[k], a, b);
                    if (!same) continue;
                    replace[b] = a;
                    b.Dead = true;
                }
            }
            phis.RemoveAll(p => p.Dead);
        }
        if (replace.Count == 0) return false;
        Replace(fn, replace);
        return true;
    }

    // ---- 32-bit values in 64-bit registers ---------------------------------------------------------------------

    private enum Narrowing { Zero, Sign, Unobserved }

    private static bool NarrowPhis(Function fn)
    {
        var candidates = new List<Node>();
        foreach (Block b in fn.Blocks)
            foreach (Node phi in b.Phis)
                if (!phi.Dead && phi.Type == VT.I64)
                    candidates.Add(phi);
        if (candidates.Count == 0) return false;
        Dictionary<Node, List<Node>> uses = DeadCode.Uses(fn);

        HashSet<Node> Fixpoint(Func<Node, HashSet<Node>, bool> qualifies)
        {
            var set = new HashSet<Node>(candidates);
            bool removed = true;
            while (removed)
            {
                removed = false;
                foreach (Node phi in candidates)
                    if (set.Contains(phi) && !qualifies(phi, set))
                    {
                        set.Remove(phi);
                        removed = true;
                    }
            }
            return set;
        }

        // Every way into the value produced only 32 significant bits, extended one way.
        HashSet<Node> zero = Fixpoint((phi, set) => phi.In.All(x =>
            (x.Op == Op.ZExt && x.In[0].Type.Bits() <= 32) || (x.IsConst && (ulong)x.Imm <= uint.MaxValue) || x.Op == Op.Undef ||
            (x.Op == Op.Phi && set.Contains(x))));
        HashSet<Node> sign = Fixpoint((phi, set) => phi.In.All(x =>
            (x.Op == Op.SExt && x.In[0].Type.Bits() <= 32) || (x.IsConst && x.Imm >= int.MinValue && x.Imm <= int.MaxValue) || x.Op == Op.Undef ||
            (x.Op == Op.Phi && set.Contains(x))));
        // Or: nothing ever looks at more than the low 32 bits.
        HashSet<Node> unobserved = Fixpoint((phi, set) => uses.TryGetValue(phi, out List<Node>? users) && users.All(u =>
            (u.Op == Op.Trunc && u.Type.Bits() <= 32) || (u.Op == Op.Phi && set.Contains(u))));

        var chosen = new Dictionary<Node, Narrowing>();
        foreach (Node phi in candidates)
        {
            if (zero.Contains(phi)) chosen[phi] = Narrowing.Zero;
            else if (sign.Contains(phi)) chosen[phi] = Narrowing.Sign;
            else if (unobserved.Contains(phi)) chosen[phi] = Narrowing.Unobserved;
        }
        // A merged value may only take inputs from merged values narrowed the same way; drop the rest.
        bool dropped = true;
        while (dropped)
        {
            dropped = false;
            foreach (Node phi in candidates)
            {
                if (!chosen.TryGetValue(phi, out Narrowing kind) || kind == Narrowing.Unobserved) continue;
                foreach (Node x in phi.In)
                    if (x.Op == Op.Phi && x.Type == VT.I64 && (!chosen.TryGetValue(x, out Narrowing other) || other != kind))
                    {
                        chosen.Remove(phi);
                        dropped = true;
                        break;
                    }
            }
        }
        if (chosen.Count == 0) return false;

        var narrow = new Dictionary<Node, Node>();
        foreach (Node phi in chosen.Keys)
        {
            Node small = fn.NewNode(Op.Phi, VT.I32, phi.Block);
            small.Addr = phi.Addr;
            narrow[phi] = small;
        }

        var builder = new IrBuilder(fn) { InsertBeforeTerminator = true };
        foreach (var (phi, small) in narrow)
        {
            Block block = phi.Block!;
            var inputs = new Node[phi.In.Length];
            for (int i = 0; i < inputs.Length; i++)
            {
                Node x = phi.In[i];
                if (x.Op == Op.Phi && narrow.TryGetValue(x, out Node? other)) inputs[i] = other;
                else if (x.IsConst) inputs[i] = builder.Const(VT.I32, x.Imm);
                else if (x.Op == Op.Undef) inputs[i] = builder.Undef(VT.I32);
                else
                {
                    // Computed where the value enters: at the end of the predecessor it comes from.
                    Block pred = i < block.Preds.Count ? block.Preds[i] : block;
                    builder.Current = pred;
                    builder.CurrentAddr = pred.Terminator?.Addr ?? 0;
                    inputs[i] = builder.Trunc(x, VT.I32);
                }
            }
            small.In = inputs;
            block.Phis.Add(small);
        }

        var replace = new Dictionary<Node, Node>();
        foreach (var (phi, small) in narrow)
        {
            Block block = phi.Block!;
            Node wide = fn.NewNode(chosen[phi] == Narrowing.Sign ? Op.SExt : Op.ZExt, VT.I64, block, small);
            wide.Addr = phi.Addr;
            block.Nodes.Insert(0, wide);
            replace[phi] = wide;
            phi.Dead = true;
        }
        foreach (Block b in fn.Blocks) b.Phis.RemoveAll(p => p.Dead);
        Replace(fn, replace);
        Refold(fn);
        return true;
    }

    // ---- small values in wide registers ------------------------------------------------------------------------

    /// <summary>
    /// A bool or byte produced by "setcc al" or "mov al, x" occupies one byte of a register whose other bytes
    /// keep whatever was there. When such registers merge, the merged value is "old junk with a new low byte" -
    /// but if nothing ever looks beyond that byte, the merged value simply is the byte. This narrows merged
    /// values to the widest part any use observes.
    /// </summary>
    private static bool NarrowToObserved(Function fn, Func<Node, Node, int>? callObserves)
    {
        var candidates = new List<Node>();
        foreach (Block b in fn.Blocks)
            foreach (Node phi in b.Phis)
                if (!phi.Dead && phi.Type is VT.I64 or VT.I32 or VT.I16)
                    candidates.Add(phi);
        // The same for a single partial write: "(old register with its low part cleared) | new low part".
        var partials = new Dictionary<Node, Block>();
        foreach (Block b in fn.Blocks)
            foreach (Node n in b.Nodes)
            {
                if (n.Dead || n.Op != Op.Or || n.Type is not (VT.I64 or VT.I32 or VT.I16) || n.In.Length != 2) continue;
                Node? cleared = n.In[0].Op == Op.And ? n.In[0] : n.In[1].Op == Op.And ? n.In[1] : null;
                if (cleared == null || cleared.In.Length != 2 || !cleared.In[1].IsConst) continue;
                ulong kept = cleared.In[1].UImm, low = ~kept & n.Type.Mask();
                if (low is not (0xFF or 0xFFFF or 0xFFFFFFFF)) continue;
                partials[n] = b;
                candidates.Add(n);
            }
        if (candidates.Count == 0) return false;
        Dictionary<Node, List<Node>> uses = DeadCode.Uses(fn);

        // Which bits of each merged value anything observes. Followed through the operations that pass bits
        // along without looking at them (masking, combining, extending, low-bit arithmetic) up to the next merge,
        // so a flag kept in the low byte of a register whose upper bits were never set is seen as a byte.
        var demanded = new Dictionary<Node, ulong>();
        foreach (Node phi in candidates) demanded[phi] = 0;
        static ulong Low(int bits) => bits >= 64 ? ulong.MaxValue : (1UL << bits) - 1;
        static ulong UpToTop(ulong mask) => mask == 0 ? 0 : Low(64 - System.Numerics.BitOperations.LeadingZeroCount(mask));
        ulong Need(Node n, int depth)
        {
            ulong full = n.Type.Mask();
            if (depth > 8) return full;
            if (!uses.TryGetValue(n, out List<Node>? users) || users.Count == 0) return depth == 0 ? full : 0;
            ulong need = 0;
            foreach (Node u in users)
            {
                ulong m;
                switch (u.Op)
                {
                    case Op.Trunc: m = u.Type.Mask(); break;
                    case Op.Phi when demanded.TryGetValue(u, out ulong through) && u.Type == n.Type: m = through; break;
                    case Op.And when u.In.Length == 2 && (u.In[1].IsConst || u.In[0].IsConst):
                        m = (u.In[1].IsConst ? u.In[1].UImm : u.In[0].UImm) & Need(u, depth + 1); break;
                    case Op.And or Op.Or or Op.Xor when u.Type == n.Type: m = Need(u, depth + 1); break;
                    case Op.ZExt or Op.SExt: m = Need(u, depth + 1) & full; break;
                    case Op.Add or Op.Sub or Op.Mul when u.Type == n.Type: m = UpToTop(Need(u, depth + 1)); break;
                    case Op.Shl when ReferenceEquals(u.In[0], n) && u.In[1].IsConst: m = Need(u, depth + 1) >> (int)Math.Min(63, u.In[1].UImm); break;
                    case Op.Call or Op.TailCall when callObserves != null: m = Low(Math.Min(n.Type.Bits(), callObserves(u, n))); break;
                    default: m = full; break;
                }
                need |= m & full;
                if (need == full) break;
            }
            return need;
        }
        bool grew = true;
        for (int round = 0; grew && round < 16; round++)
        {
            grew = false;
            foreach (Node phi in candidates)
            {
                ulong need = Need(phi, 0) | demanded[phi];
                if (need == demanded[phi]) continue;
                demanded[phi] = need;
                grew = true;
            }
        }
        var observed = new Dictionary<Node, int>();
        foreach (Node phi in candidates)
        {
            ulong need = demanded[phi];
            int top = need == 0 ? 0 : 64 - System.Numerics.BitOperations.LeadingZeroCount(need);
            observed[phi] = top == 0 ? 0 : top <= 8 ? 8 : top <= 16 ? 16 : top <= 32 ? 32 : 64;
        }

        var narrow = new Dictionary<Node, Node>();
        foreach (Node phi in candidates)
        {
            int bits = observed[phi];
            if (partials.ContainsKey(phi)) continue;
            if (bits >= phi.Type.Bits() || bits == 0) continue;
            Node small = fn.NewNode(Op.Phi, VTExtensions.IntOfBytes(bits / 8), phi.Block);
            small.Addr = phi.Addr;
            narrow[phi] = small;
        }
        var builder = new IrBuilder(fn) { InsertBeforeTerminator = true };
        // Partial writes nothing looks past the low part of: the low part, widened.
        Dictionary<Node, Node>? whole = null;
        foreach (var (n, block) in partials)
        {
            int bits = observed[n];
            if (bits >= n.Type.Bits() || bits == 0 || !block.Nodes.Contains(n)) continue;
            var positioned = new IrBuilder(fn);
            positioned.PositionBefore(block, n);
            Node part = TruncateParts(positioned, n, VTExtensions.IntOfBytes(bits / 8), narrow, 0);
            if (part.Op == Op.Trunc && ReferenceEquals(part.In[0], n)) continue; // nothing gained
            (whole ??= [])[n] = positioned.ZExt(part, n.Type);
        }
        if (whole != null)
        {
            Replace(fn, whole);
            if (narrow.Count == 0)
            {
                Refold(fn);
                return true;
            }
        }
        if (narrow.Count == 0) return false;

        foreach (var (phi, small) in narrow)
        {
            Block block = phi.Block!;
            var inputs = new Node[phi.In.Length];
            for (int i = 0; i < inputs.Length; i++)
            {
                Node x = phi.In[i];
                if (x.Op == Op.Phi && narrow.TryGetValue(x, out Node? other) && other.Type == small.Type) inputs[i] = other;
                else if (x.IsConst) inputs[i] = builder.Const(small.Type, x.Imm);
                else if (x.Op == Op.Undef) inputs[i] = builder.Undef(small.Type);
                else
                {
                    Block pred = i < block.Preds.Count ? block.Preds[i] : block;
                    builder.Current = pred;
                    builder.CurrentAddr = pred.Terminator?.Addr ?? 0;
                    inputs[i] = TruncateParts(builder, x, small.Type, narrow, 0);
                }
            }
            small.In = inputs;
            block.Phis.Add(small);
        }

        var replace = new Dictionary<Node, Node>();
        foreach (var (phi, small) in narrow)
        {
            Block block = phi.Block!;
            Node wide = fn.NewNode(Op.ZExt, phi.Type, block, small);
            wide.Addr = phi.Addr;
            block.Nodes.Insert(0, wide);
            replace[phi] = wide;
            phi.Dead = true;
        }
        foreach (Block b in fn.Blocks) b.Phis.RemoveAll(p => p.Dead);
        Replace(fn, replace);
        Refold(fn);
        return true;
    }

    /// <summary>
    /// The low bits of a value, taken through the bitwise operations that built it: masks that clear those bits
    /// give zero and masks that keep them disappear, so what never reaches the low bits (an undefined upper part)
    /// is not part of the result.
    /// </summary>
    private static Node TruncateParts(IrBuilder builder, Node x, VT type, Dictionary<Node, Node> narrowed, int depth)
    {
        ulong mask = type.Mask();
        if (x.IsConst) return builder.Const(type, (long)(x.UImm & mask));
        if (x.Op == Op.Undef) return builder.Undef(type);
        if (x.Op == Op.Phi && narrowed.TryGetValue(x, out Node? small) && small.Type == type) return small;
        if (depth < 6)
        {
            if (x.Op is Op.ZExt or Op.SExt && x.In[0].Type.Bits() >= type.Bits())
                return x.In[0].Type == type ? x.In[0] : TruncateParts(builder, x.In[0], type, narrowed, depth + 1);
            if (x.Op == Op.And && x.In.Length == 2 && (x.In[0].IsConst || x.In[1].IsConst))
            {
                Node other = x.In[1].IsConst ? x.In[0] : x.In[1];
                ulong keep = (x.In[1].IsConst ? x.In[1].UImm : x.In[0].UImm) & mask;
                if (keep == 0) return builder.Const(type, 0);
                Node part = TruncateParts(builder, other, type, narrowed, depth + 1);
                return keep == mask ? part : builder.And(part, builder.Const(type, (long)keep));
            }
            if (x.Op is Op.Or or Op.Xor && x.In.Length == 2)
            {
                Node l = TruncateParts(builder, x.In[0], type, narrowed, depth + 1), r = TruncateParts(builder, x.In[1], type, narrowed, depth + 1);
                if (l.IsConstValue(0)) return r;
                if (r.IsConstValue(0)) return l;
                if (l.IsConst && r.IsConst) return builder.Const(type, x.Op == Op.Or ? (long)((l.UImm | r.UImm) & mask) : (long)((l.UImm ^ r.UImm) & mask));
                return x.Op == Op.Or ? builder.Or(l, r) : builder.Xor(l, r);
            }
        }
        return builder.Trunc(x, type);
    }

    // ---- a pointer that walks in step with a counter -----------------------------------------------------------

    private readonly record struct Induction(Node Phi, Node Start, long Step, Node Increment);

    private static bool TryInduction(Node phi, Block header, Cfg cfg, out Induction induction)
    {
        induction = default;
        if (phi.In.Length != header.Preds.Count || phi.In.Length < 2) return false;
        Node? start = null, increment = null;
        long step = 0;
        for (int i = 0; i < phi.In.Length; i++)
        {
            Node x = phi.In[i];
            bool back = cfg.Dominates(header, header.Preds[i]);
            if (back)
            {
                if (x.Op != Op.Add || !ReferenceEquals(x.In[0], phi) || !x.In[1].IsConst) return false;
                long s = IrBuilder.SImm(x.In[1]);
                if (increment != null && s != step) return false;
                step = s;
                increment = x;
            }
            else
            {
                if (start != null && !Normalizer.SameValue(start, x)) return false;
                start = x;
            }
        }
        if (start == null || increment == null || step == 0) return false;
        induction = new Induction(phi, start, step, increment);
        return true;
    }

    /// <summary>
    /// "for (i = 0; i &lt; n; i++) use(a[i])" compiled with the index already multiplied: the loop counts a byte
    /// offset, from the offset of the first element in steps of the element size, and no counter is left. Read
    /// back as a counter from zero in steps of one, with the offset computed from it - which is what shows
    /// the element being accessed.
    /// </summary>
    private static bool RewriteScaledOffsets(Function fn)
    {
        var cfg = new Cfg(fn);
        Dictionary<Node, List<Node>>? uses = null;
        bool changed = false;
        foreach (Block header in fn.Blocks)
        {
            if (header.Preds.Count < 2 || header.Phis.Count == 0) continue;
            if (!header.Preds.Any(p => cfg.Dominates(header, p))) continue;
            foreach (Node phi in header.Phis.ToList())
            {
                if (phi.Dead || phi.Type != VT.I64 || !TryInduction(phi, header, cfg, out Induction offset)) continue;
                if (!offset.Start.IsConst || offset.Step is < 2 or > 4096) continue;
                long first = IrBuilder.SImm(offset.Start), step = offset.Step;
                if (first is < 0 or > 1 << 20) continue;
                uses ??= DeadCode.Uses(fn);

                // Every use is address arithmetic or a comparison with a constant.
                bool addresses = false, fits = true;
                var compares = new List<(Node Cmp, bool OfNext)>();
                void Check(Node value, bool isNext)
                {
                    if (!uses!.TryGetValue(value, out List<Node>? users)) return;
                    foreach (Node u in users)
                    {
                        if (!fits) return;
                        if (ReferenceEquals(u, phi) && isNext) continue;
                        if (ReferenceEquals(u, offset.Increment) && !isNext) continue;
                        if (u.Op == Op.Add && u.Type == VT.I64)
                        {
                            Node other = ReferenceEquals(u.In[0], value) ? u.In[1] : u.In[0];
                            if (!other.IsConst) addresses = true;
                            continue;
                        }
                        if (u.Op is Op.CmpEq or Op.CmpNe or Op.CmpLtS or Op.CmpLeS or Op.CmpLtU or Op.CmpLeU && (u.In[0].IsConst ^ u.In[1].IsConst))
                        {
                            compares.Add((u, isNext));
                            continue;
                        }
                        fits = false;
                    }
                }
                Check(phi, false);
                Check(offset.Increment, true);
                if (!fits || !addresses) continue;
                Block? stepBlock = fn.Blocks.FirstOrDefault(b => b.Nodes.Contains(offset.Increment));
                if (stepBlock == null) continue;

                // The counter, its step, and the offset computed from it.
                Node counter = fn.NewNode(Op.Phi, VT.I32, header);
                counter.Addr = phi.Addr;
                Node one = fn.NewNode(Op.Const, VT.I32, null);
                one.Imm = 1;
                Node next = fn.NewNode(Op.Add, VT.I32, stepBlock, counter, one);
                next.Addr = offset.Increment.Addr;
                stepBlock.Nodes.Insert(stepBlock.Nodes.IndexOf(offset.Increment), next);
                var inputs = new Node[phi.In.Length];
                for (int i = 0; i < inputs.Length; i++)
                {
                    if (ReferenceEquals(phi.In[i], offset.Increment)) inputs[i] = next;
                    else
                    {
                        inputs[i] = fn.NewNode(Op.Const, VT.I32, null);
                    }
                }
                counter.In = inputs;
                header.Phis.Add(counter);
                var b = new IrBuilder(fn) { Current = header, InsertIndex = 0, CurrentAddr = header.Start };
                Node wide = b.Raw(Op.ZExt, VT.I64, counter);
                Node scaled = b.Add(b.Mul(wide, b.Const(VT.I64, step)), b.Const(VT.I64, first));
                b.InsertIndex = -1;

                // Comparisons with a constant that is a whole number of steps away become comparisons of the counter.
                foreach (var (cmp, ofNext) in compares)
                {
                    int constant = cmp.In[0].IsConst ? 0 : 1;
                    long limit = IrBuilder.SImm(cmp.In[constant]) - first;
                    if (limit < 0 || limit % step != 0 || limit / step > int.MaxValue) continue;
                    Node count = fn.NewNode(Op.Const, VT.I32, null);
                    count.Imm = limit / step;
                    cmp.In[constant] = count;
                    cmp.In[1 - constant] = ofNext ? next : counter;
                }
                foreach (Block block in fn.Blocks)
                {
                    foreach (Node n in block.Phis)
                        if (!ReferenceEquals(n, phi))
                            for (int i = 0; i < n.In.Length; i++)
                                if (ReferenceEquals(n.In[i], phi)) n.In[i] = scaled;
                    foreach (Node n in block.Nodes)
                    {
                        if (ReferenceEquals(n, scaled)) continue;
                        for (int i = 0; i < n.In.Length; i++)
                            if (ReferenceEquals(n.In[i], phi)) n.In[i] = scaled;
                    }
                }
                phi.Dead = true;
                header.Phis.Remove(phi);
                changed = true;
                uses = null;
            }
        }
        return changed;
    }

    /// <summary>True when <paramref name="value"/> is <paramref name="of"/> times a constant plus a constant.</summary>
    private static bool Affine(Node value, Node of, out long mul, out long add, int depth = 0)
    {
        mul = 0;
        add = 0;
        if (ReferenceEquals(value, of) || Normalizer.SameValue(value, of))
        {
            mul = 1;
            return true;
        }
        if (depth > 6) return false;
        switch (value.Op)
        {
            case Op.Add when value.In[1].IsConst && Affine(value.In[0], of, out mul, out add, depth + 1):
                add += IrBuilder.SImm(value.In[1]);
                return true;
            case Op.Sub when value.In[1].IsConst && Affine(value.In[0], of, out mul, out add, depth + 1):
                add -= IrBuilder.SImm(value.In[1]);
                return true;
            case Op.Mul when value.In[1].IsConst && Affine(value.In[0], of, out mul, out add, depth + 1):
                mul *= IrBuilder.SImm(value.In[1]);
                add *= IrBuilder.SImm(value.In[1]);
                return true;
            case Op.Shl when value.In[1].IsConst && value.In[1].UImm < 16 && Affine(value.In[0], of, out mul, out add, depth + 1):
                mul <<= (int)value.In[1].UImm;
                add <<= (int)value.In[1].UImm;
                return true;
            default:
                return false;
        }
    }

    private static bool RewritePointerInduction(Function fn)
    {
        var cfg = new Cfg(fn);
        Dictionary<Node, List<Node>>? uses = null;
        bool changed = false;

        foreach (Block header in fn.Blocks)
        {
            if (header.Preds.Count < 2 || header.Phis.Count < 2) continue;
            bool isLoop = false;
            foreach (Block p in header.Preds)
                if (cfg.Dominates(header, p))
                    isLoop = true;
            if (!isLoop) continue;

            var inductions = new List<Induction>();
            foreach (Node phi in header.Phis)
                if (!phi.Dead && phi.Type is VT.I32 or VT.I64 && TryInduction(phi, header, cfg, out Induction found))
                    inductions.Add(found);
            if (inductions.Count < 2) continue;
            uses ??= DeadCode.Uses(fn);

            foreach (Induction pointer in inductions)
            {
                if (pointer.Phi.Type != VT.I64) continue;
                // A pointer - or a byte offset into an array - is something memory is accessed through:
                // directly, or after adding a constant or a base.
                if (!uses.TryGetValue(pointer.Phi, out List<Node>? users)) continue;
                bool addresses = false;
                foreach (Node u in users)
                {
                    if (u.Op is Op.Load or Op.Store && ReferenceEquals(u.In[0], pointer.Phi)) addresses = true;
                    else if (u.Op == Op.Add && !ReferenceEquals(u, pointer.Increment) && uses.TryGetValue(u, out List<Node>? inner) &&
                             inner.Any(w => (w.Op is Op.Load or Op.Store && ReferenceEquals(w.In[0], u)) ||
                                            (w.Op == Op.Add && uses.TryGetValue(w, out List<Node>? outer) &&
                                             outer.Any(x => x.Op is Op.Load or Op.Store && ReferenceEquals(x.In[0], w))))) addresses = true;
                }
                if (!addresses) continue;

                // A loop that runs backwards ("for (i = n - 1; i >= 0; i--)") starts both from values only known
                // when it runs; there the pointer's start is the counter's start times the element size plus
                // a constant, and so is the pointer at every step.
                Induction? related = null;
                long relatedAdd = 0;
                foreach (Induction candidate in inductions)
                {
                    if (ReferenceEquals(candidate.Phi, pointer.Phi) || candidate.Phi.Type != VT.I64 || candidate.Start.IsConst) continue;
                    if (candidate.Step == 0 || pointer.Step % candidate.Step != 0 || candidate.Phi.In.Length != pointer.Phi.In.Length) continue;
                    long ratio = pointer.Step / candidate.Step;
                    if (ratio is < 2 or > 4096) continue;
                    if (!Affine(pointer.Start, candidate.Start, out long mul, out long add) || mul != ratio) continue;
                    related = candidate;
                    relatedAdd = add;
                    break;
                }
                if (related is { } r)
                {
                    var rb = new IrBuilder(fn) { Current = header, InsertIndex = 0, CurrentAddr = header.Start };
                    Node computed = rb.Add(rb.Mul(r.Phi, rb.Const(VT.I64, pointer.Step / r.Step)), rb.Const(VT.I64, relatedAdd));
                    rb.InsertIndex = -1;
                    foreach (Block block in fn.Blocks)
                    {
                        foreach (Node n in block.Phis)
                            if (!ReferenceEquals(n, pointer.Phi))
                                for (int i = 0; i < n.In.Length; i++)
                                    if (ReferenceEquals(n.In[i], pointer.Phi)) n.In[i] = computed;
                        foreach (Node n in block.Nodes)
                        {
                            if (ReferenceEquals(n, computed) || ReferenceEquals(n, pointer.Increment)) continue;
                            for (int i = 0; i < n.In.Length; i++)
                                if (ReferenceEquals(n.In[i], pointer.Phi)) n.In[i] = computed;
                        }
                    }
                    changed = true;
                    uses = null;
                    break;
                }
                if (pointer.Step <= 0) continue;

                // The counter it keeps step with: prefer one that counts by one from a constant.
                Induction? counter = null;
                foreach (Induction candidate in inductions)
                {
                    if (ReferenceEquals(candidate.Phi, pointer.Phi) || candidate.Step <= 0 || pointer.Step % candidate.Step != 0) continue;
                    if (!candidate.Start.IsConst) continue;
                    // Both must advance on exactly the same paths: same increments on the same back edges.
                    if (candidate.Phi.In.Length != pointer.Phi.In.Length) continue;
                    if (counter == null || (candidate.Step == 1 && counter.Value.Step != 1) ||
                        (candidate.Phi.Type == VT.I32 && counter.Value.Phi.Type != VT.I32 && candidate.Step == counter.Value.Step))
                        counter = candidate;
                }
                if (counter is not { } c) continue;

                long scale = pointer.Step / c.Step;
                long first = IrBuilder.SImm(c.Start);
                // address = start + scale * (counter - first), computed at the top of the loop.
                var b = new IrBuilder(fn) { Current = header, InsertIndex = 0, CurrentAddr = header.Start };
                Node count = c.Phi.Type == VT.I64 ? c.Phi : b.Raw(Op.ZExt, VT.I64, c.Phi);
                if (first != 0) count = b.Add(count, b.Const(VT.I64, -first));
                Node address = b.Add(pointer.Start, b.Mul(count, b.Const(VT.I64, scale)));
                b.InsertIndex = -1;

                foreach (Block block in fn.Blocks)
                {
                    foreach (Node n in block.Phis)
                        if (!ReferenceEquals(n, pointer.Phi))
                            for (int i = 0; i < n.In.Length; i++)
                                if (ReferenceEquals(n.In[i], pointer.Phi)) n.In[i] = address;
                    foreach (Node n in block.Nodes)
                    {
                        if (ReferenceEquals(n, address) || ReferenceEquals(n, pointer.Increment)) continue;
                        for (int i = 0; i < n.In.Length; i++)
                            if (ReferenceEquals(n.In[i], pointer.Phi)) n.In[i] = address;
                    }
                }
                changed = true;
                uses = null;
                break; // use lists are stale; the next round picks up further pointers of this loop
            }
            if (uses == null && changed) uses = DeadCode.Uses(fn);
        }
        return changed;
    }
}
