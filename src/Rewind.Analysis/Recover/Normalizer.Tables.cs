using Rewind.Analysis.Ir;
using Rewind.Binary;

namespace Rewind.Analysis.Recover;

public sealed partial class Normalizer
{
    /// <summary>Lookup tables longer than this stay loads, and so do those with more entries than MaxTableTests apart from the commonest.</summary>
    private const int MaxTableEntries = 256, MaxTableTests = 32;

    /// <summary>
    /// A switch that only picks a value is compiled (by clang above all) into a table of those values in
    /// read-only data, indexed by the switched value after one bounds check: <c>if (x &lt;=u K) v = table[x]</c>.
    /// The table holds constants, so a read of entry x is the choice among them that x makes; with the bound
    /// known, the read becomes that choice (selects comparing x with each index). Its entries are often the
    /// addresses of metadata slots (string literals), which the slot reads then follow.
    /// </summary>
    private bool ExpandLookupTables()
    {
        bool changed = false;
        foreach (Block b in _fn.Blocks)
        {
            for (int i = 0; i < b.Nodes.Count; i++)
            {
                Node load = b.Nodes[i];
                if (load.Dead || load.Op != Op.Load || !load.Type.IsInt()) continue;
                int size = load.Type.Bytes();
                if (!TableRead(load.In[0], size, out ulong table, out Node index)) continue;
                // The value compared with the bound: the index itself or what was widened into it.
                Node compared = index.Op is Op.ZExt or Op.SExt ? index.In[0] : index;
                if ((Bound(b, index, compared) ?? InductionTableBound(_fn, b, compared)) is not long last || last >= MaxTableEntries) continue;
                // String-pointer tables are often longer than the original
                // linear-choice budget, and a long linear chain cannot later
                // be canonicalized as a choice among metadata slots.
                if (size == 8 && Environment.GetEnvironmentVariable("REWIND_NO_BALANCED_LITERAL_TABLES") == null &&
                    compared.Type.Bits() is >= 8 and <= 32 &&
                    LiteralLookupTable.TryRead(program.Model.Image, table, (int)last + 1,
                        slot => program.Model.ResolveUsageSlot(slot) is { Kind: Rewind.Model.UsageKind.StringLiteral },
                        out ulong[] literalEntries))
                {
                    int position = i;
                    _replace[load] = LiteralLookupTable.BuildChoice(_fn, b, ref position, compared, literalEntries, load.Addr);
                    load.Dead = true;
                    i = position;
                    changed = true;
                    continue;
                }
                if (size == 8 && Environment.GetEnvironmentVariable("REWIND_NO_METHOD_SLOT_TABLES") == null &&
                    compared.Type.Bits() is >= 8 and <= 32 &&
                    LiteralLookupTable.TryRead(program.Model.Image, table, (int)last + 1,
                        slot => program.Model.ResolveUsageSlot(slot) is { Kind: Rewind.Model.UsageKind.MethodDef, Method: { IsStatic: true, IsAbstract: false } m } &&
                            m.Address != 0 && m.GenericParameters.Length == 0 && m.DeclaringType.GenericParameters.Length == 0,
                        out ulong[] methodEntries))
                {
                    int position = i;
                    _replace[load] = LiteralLookupTable.BuildChoice(_fn, b, ref position, compared, methodEntries, load.Addr);
                    load.Dead = true;
                    i = position;
                    changed = true;
                    continue;
                }
                var entries = new long[last + 1];
                if (!ReadTable(table, size, entries)) continue;

                // The most common entry is what is left when no index matched (the bound leaves nothing else);
                // every other entry is tested for, from the end.
                long otherwise = entries.GroupBy(v => v).OrderByDescending(g => g.Count()).ThenBy(g => Array.IndexOf(entries, g.Key)).First().Key;
                if (entries.Count(v => v != otherwise) > MaxTableTests) continue;
                int at = i;
                Node result = _b.Const(load.Type, otherwise);
                for (long e = last; e >= 0; e--)
                {
                    if (entries[e] == otherwise) continue;
                    Node k = _fn.NewNode(Op.Const, compared.Type, null);
                    k.Imm = e;
                    Node test = NewNodeAt(b, at++, Op.CmpEq, VT.I1, load.Addr, compared, k);
                    result = NewNodeAt(b, at++, Op.Select, load.Type, load.Addr, test, _b.Const(load.Type, entries[e]), result);
                }
                _replace[load] = result;
                load.Dead = true;
                i = at;
                changed = true;
            }
            b.Nodes.RemoveAll(n => n.Dead);
        }
        return changed;
    }

    /// <summary>An address that is a constant plus an index scaled by the element size.</summary>
    private static bool TableRead(Node address, int size, out ulong table, out Node index)
    {
        table = 0;
        index = null!;
        if (address.Op != Op.Add || address.Type != VT.I64) return false;
        Node scaled;
        if (address.In[1].IsConst) (scaled, table) = (address.In[0], address.In[1].UImm);
        else if (address.In[0].IsConst) (scaled, table) = (address.In[1], address.In[0].UImm);
        else return false;
        int shift = size switch { 1 => 0, 2 => 1, 4 => 2, 8 => 3, _ => -1 };
        if (shift < 0) return false;
        if (shift == 0) index = scaled;
        else if (scaled.Op == Op.Shl && scaled.In[1].IsConstValue(shift)) index = scaled.In[0];
        else if (scaled.Op == Op.Mul && scaled.In[1].IsConstValue(size)) index = scaled.In[0];
        else return false;
        // A narrower value widened: its unsigned bound then bounds the index too.
        return index.Type.IsInt() && (index.Op is not (Op.ZExt or Op.SExt) || index.In[0].Type.IsInt() && index.In[0].Type.Bytes() <= 4);
    }

    /// <summary>
    /// The largest index the code reaching <paramref name="b"/> allows: an unsigned comparison of the index
    /// with a constant, on the edge into a chain of single-predecessor blocks ending here.
    /// </summary>
    internal static long? Bound(Block b, Node index, Node compared)
    {
        // Zero extension of an IR predicate admits exactly the two original table entries.
        // Sign extension would turn true into -1 and must retain the load.
        if (index.Op == Op.ZExt && compared.Type == VT.I1 && compared.Op is
            Op.CmpEq or Op.CmpNe or Op.CmpLtS or Op.CmpLeS or Op.CmpLtU or Op.CmpLeU or
            Op.FCmpEq or Op.FCmpLt or Op.FCmpLe or Op.FCmpUnord) return 1;
        Block child = b;
        for (int depth = 0; depth < 4 && child.Preds.Count == 1; depth++)
        {
            Block p = child.Preds[0];
            if (p.Terminator is { Op: Op.Branch } branch && p.Succs.Count == 2 && !ReferenceEquals(p.Succs[0], p.Succs[1]))
            {
                bool taken = ReferenceEquals(p.Succs[0], child);
                Node c = branch.In[0];
                // (The same value computed again, or widened with zeros, which an unsigned comparison does not mind.)
                bool Is(Node n)
                {
                    for (int strip = 0; strip < 3; strip++)
                    {
                        if (SameValue(n, compared) || SameValue(n, index)) return true;
                        if (n.Op != Op.ZExt || n.In.Length != 1) break;
                        n = n.In[0];
                    }
                    return false;
                }
                if (c.In.Length == 2)
                {
                    long? bound = c.Op switch
                    {
                        Op.CmpLtU when !taken && c.In[0].IsConst && Is(c.In[1]) => c.In[0].Imm,       // !(K <u x): x <= K
                        Op.CmpLtU when taken && c.In[1].IsConst && Is(c.In[0]) => c.In[1].Imm - 1,    // x <u N
                        Op.CmpLeU when taken && c.In[1].IsConst && Is(c.In[0]) => c.In[1].Imm,        // x <=u K
                        Op.CmpLeU when !taken && c.In[0].IsConst && Is(c.In[1]) => c.In[0].Imm - 1,   // !(N <=u x)
                        _ => null,
                    };
                    if (bound is long k && k >= 0) return k;
                    // (x & ~K) == 0 on this edge proves the unsigned domain [0,K].
                    // Require every high bit and no low bit in the original operand width.
                    if (c.Op is Op.CmpEq or Op.CmpNe && taken == (c.Op == Op.CmpEq))
                    {
                        Node? masked = c.In[1].IsConstValue(0) ? c.In[0] : c.In[0].IsConstValue(0) ? c.In[1] : null;
                        if (masked is { Op: Op.And, In.Length: 2 } && masked.Type.Bits() is >= 8 and <= 32)
                        {
                            Node? mask = masked.In[0].IsConst && Is(masked.In[1]) ? masked.In[0] :
                                masked.In[1].IsConst && Is(masked.In[0]) ? masked.In[1] : null;
                            if (mask != null)
                            {
                                ulong low = (~mask.UImm) & masked.Type.Mask();
                                if (low < MaxTableEntries && (low & (low + 1)) == 0) return (long)low;
                            }
                        }
                    }
                }
            }
            child = p;
        }
        return null;
    }

    // Exact zero-based, unit-stride induction terminated by next != N. The sole
    // backedge supplies that same next value; N <= 256 proves no modular wrap.
    internal static long? InductionTableBound(Function fn, Block use, Node index)
    {
        if (fn.TryRegions.Count != 0 || index is not { Op: Op.Phi, Type: VT.I64, In.Length: 2, Block: {} head } ||
            !head.Phis.Contains(index) || head.Preds.Count != 2) return null;
        var cfg = new Cfg(fn);
        if (!cfg.Dominates(head, use)) return null;
        for (int back = 0; back < 2; back++)
        {
            Block tail = head.Preds[back]; Node next = index.In[back];
            if (!index.In[1-back].IsConstValue(0) || tail == head || !cfg.Dominates(head, tail) ||
                next is not { Op: Op.Add, Type: VT.I64, In.Length: 2 } || next.Block != tail ||
                !(next.In[0] == index && next.In[1].IsConstValue(1) || next.In[1] == index && next.In[0].IsConstValue(1)) ||
                tail.Succs.Count != 2 || tail.Succs[0] != head || tail.Succs[1] == head ||
                tail.Terminator is not { Op: Op.Branch, In.Length: 1 } branch ||
                branch.In[0] is not { Op: Op.CmpNe, In.Length: 2 } cmp) continue;
            Node? end = cmp.In[0] == next && cmp.In[1].IsConst ? cmp.In[1] : cmp.In[1] == next && cmp.In[0].IsConst ? cmp.In[0] : null;
            if (end is { Type: VT.I64 } && end.Imm is > 0 and <= MaxTableEntries) return end.Imm - 1;
        }
        return null;
    }

    /// <summary>The entries of a table that holds the same values for the life of the program.</summary>
    private bool ReadTable(ulong table, int size, long[] entries)
    {
        NativeImage image = program.Model.Image;
        for (int e = 0; e < entries.Length; e++)
        {
            ulong va = table + (ulong)(e * size);
            ImageSection? section = image.SectionAt(va);
            if (section == null || section.IsExecutable || !image.IsMapped(va, size)) return false;
            if (section.IsWritable && !(size == 8 && image.IsReadOnlyAfterLoad(va))) return false;
            entries[e] = size switch
            {
                1 => image.U8(va),
                2 => image.U16(va),
                4 => image.U32(va),
                _ => (long)image.U64(va),
            };
        }
        return true;
    }

    // ---- reads through a choice of slots ---------------------------------------------------------------

    /// <summary>
    /// Whether <paramref name="n"/> is a choice among metadata slot addresses: a slot's address, or a select or
    /// phi of such choices (perhaps widened).
    /// </summary>
    private bool IsSlotChoice(Node n, int depth, HashSet<Node> open)
    {
        while (n.Op is Op.ZExt or Op.SExt && n.In.Length == 1) n = n.In[0];
        if (n.IsConst) return IsMetadataSlot(n.UImm);
        if (depth > 8 || !open.Add(n)) return false;
        bool result = n.Op switch
        {
            Op.Select when n.Block != null => IsSlotChoice(Resolve(n.In[1]), depth + 1, open) && IsSlotChoice(Resolve(n.In[2]), depth + 1, open),
            Op.Phi when n.Block is { } block && n.In.Length == block.Preds.Count && n.In.Length is >= 2 and <= 32 =>
                n.In.All(i => IsSlotChoice(Resolve(i), depth + 1, open)),
            _ => false,
        };
        open.Remove(n);
        return result;
    }

    /// <summary>The same choice over the slots' contents (call only when <see cref="IsSlotChoice"/> holds).</summary>
    private Node SlotRead(Node n, Dictionary<Node, Node> made)
    {
        while (n.Op is Op.ZExt or Op.SExt && n.In.Length == 1) n = n.In[0];
        if (n.IsConst) return SlotValue(n.UImm);
        if (made.TryGetValue(n, out Node? known)) return known;
        Node result;
        if (n.Op == Op.Select)
        {
            Block block = n.Block!;
            Node whenTrue = SlotRead(Resolve(n.In[1]), made), whenFalse = SlotRead(Resolve(n.In[2]), made);
            result = _fn.NewNode(Op.Select, VT.I64, block, n.In[0], whenTrue, whenFalse);
            result.Addr = n.Addr;
            int at = block.Nodes.IndexOf(n);
            block.Nodes.Insert(at < 0 ? 0 : at + 1, result);
        }
        else
        {
            Block block = n.Block!;
            result = _fn.NewNode(Op.Phi, VT.I64, block, new Node[n.In.Length]);
            made[n] = result;
            for (int i = 0; i < n.In.Length; i++) result.In[i] = SlotRead(Resolve(n.In[i]), made);
            block.Phis.Add(result);
        }
        made[n] = result;
        return result;
    }

    /// <summary>
    /// A choice of metadata slot addresses (a select or phi of constants, perhaps nested): the same choice over
    /// the slots' contents, or null.
    /// </summary>
    private Node? SlotChoice(Node slot)
    {
        if (slot.IsConst || !IsSlotChoice(slot, 0, [])) return null;
        return SlotRead(slot, []);
    }

    /// <summary>
    /// Slot reads that later passes made constant (copies of a block, one per way in, with the address each
    /// way brought): the slots' values, as everywhere else.
    /// </summary>
    public void CanonicalizeSlots(Function fn)
    {
        if (!ReferenceEquals(fn, _fn)) _slotValues.Clear();
        _fn = fn;
        _b = new IrBuilder(fn);
        _result ??= new NormalizeResult();
        _replace.Clear();
        CanonicalizeSlotLoads();
        ApplyReplacements();
    }
}
