using Rewind.Analysis.Ir;
using Rewind.Binary;

namespace Rewind.Analysis.Recover;

public sealed partial class Normalizer
{
    /// <summary>Lookup tables longer than this stay loads.</summary>
    private const int MaxTableEntries = 32;

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
                if (Bound(b, index, compared) is not long last || last >= MaxTableEntries) continue;
                var entries = new long[last + 1];
                if (!ReadTable(table, size, entries)) continue;

                // The most common entry is what is left when no index matched (the bound leaves nothing else);
                // every other entry is tested for, from the end.
                long otherwise = entries.GroupBy(v => v).OrderByDescending(g => g.Count()).ThenBy(g => Array.IndexOf(entries, g.Key)).First().Key;
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
        return index.Op is Op.ZExt or Op.SExt && index.In[0].Type.IsInt() && index.In[0].Type.Bytes() <= 4;
    }

    /// <summary>
    /// The largest index the code reaching <paramref name="b"/> allows: an unsigned comparison of the index
    /// with a constant, on the edge into a chain of single-predecessor blocks ending here.
    /// </summary>
    private static long? Bound(Block b, Node index, Node compared)
    {
        Block child = b;
        for (int depth = 0; depth < 4 && child.Preds.Count == 1; depth++)
        {
            Block p = child.Preds[0];
            if (p.Terminator is { Op: Op.Branch } branch && p.Succs.Count == 2 && !ReferenceEquals(p.Succs[0], p.Succs[1]))
            {
                bool taken = ReferenceEquals(p.Succs[0], child);
                Node c = branch.In[0];
                bool Is(Node n) => ReferenceEquals(n, compared) || ReferenceEquals(n, index);
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
                }
            }
            child = p;
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
            Op.Phi when n.Block is { } block && n.In.Length == block.Preds.Count && n.In.Length is >= 2 and <= 8 =>
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
