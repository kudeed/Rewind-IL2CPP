using Rewind.Analysis.Ir;
using Rewind.Model;
using Rewind.Analysis.X64;

namespace Rewind.Analysis.Recover;

public sealed partial class HirBuilder
{
    /// <summary>Stores that only park a stack address in a stack slot (the compiler's, not the program's).</summary>
    private readonly HashSet<Node> _spillStores = [];
    /// <summary>Loads that read such a parked address back: load -> the stack offset it is the address of.</summary>
    private readonly Dictionary<Node, int> _spillLoads = [];
    /// <summary>
    /// The same for a parked reference that is not a stack address: the "this" of a struct method, a by-reference
    /// parameter, the return buffer, the method's own descriptor (values whose meaning is fixed on entry).
    /// Load -> the value that was parked.
    /// </summary>
    private readonly Dictionary<Node, Node> _refLoads = [];

    private static readonly bool NoParkedDescriptors = Environment.GetEnvironmentVariable("REWIND_NO_PARKED_DESCRIPTORS") != null;

    /// <summary>
    /// A value that is a reference to a location from the start (bound in BindParameters), so safe to ask about
    /// before translation. The method's own descriptor is one too: code of a generic class that has a try
    /// statement keeps it in the frame, and reads what it calls on its type arguments through the copy.
    /// </summary>
    private bool IsBoundReference(Node n) => _sem.TryGetValue(n, out Sem? s) && (s is SRef || (s is SMethod && !NoParkedDescriptors));

    private const long ReferenceTargets = 1L << 40;

    /// <summary>
    /// IL never stores the address of a local into a local that is not a pointer, so a stack address written to
    /// a stack slot is the compiler parking a pointer (typically "this" for calls on a struct local) in memory it
    /// reuses. When every write that can reach a load of that slot parks the same address, the load is that
    /// address; the slot itself then plays no part in the program.
    /// </summary>
    private void PlanAddressSpills()
    {
        // Candidate slots: 8-byte stores of a stack address to a stack slot.
        var slots = new HashSet<int>();
        foreach (Block b in _fn.Blocks)
            foreach (Node n in b.Nodes)
                if (!n.Dead && n.Op == Op.Store && n.In[1].Type == VT.I64 && StackOffsetOf(n.In[0], 0) is int at &&
                    (StackOffsetOf(n.In[1], 0) is not null || IsBoundReference(n.In[1])))
                    slots.Add(at);
        if (slots.Count == 0) return;

        foreach (int slot in slots) PlanSlot(slot);
    }

    /// <summary>Loads of a catch object slot inside its handler: load -> try region.</summary>
    private readonly Dictionary<Node, int> _caughtLoads = [];
    /// <summary>The handler's stores of the caught exception's reference into its catch object slot.</summary>
    private readonly HashSet<Node> _caughtStores = [];

    /// <summary>
    /// A catch funclet finds a reference to the caught exception in a slot of the function's frame. Inside the
    /// handler, reading that slot reads the reference; the slot itself plays no part in the program (the C++
    /// catch object ends with the catch clause).
    /// </summary>
    private void PlanCaughtSlots()
    {
        foreach (Block b in _fn.Blocks)
            foreach (Node store in b.Nodes)
            {
                if (store.Dead || store.Op != Op.Store || store.In[1] is not { Op: Op.Idiom, Aux: int region } wrapper ||
                    (IdiomKind)wrapper.Imm != IdiomKind.CaughtWrapper || StackOffsetOf(store.In[0], 0) is not int slot) continue;
                var loads = new List<Node>();
                bool ok = true;
                foreach (Block c in _fn.Blocks)
                {
                    if (c.Scope != b.Scope) continue;
                    foreach (Node n in c.Nodes)
                    {
                        if (n.Dead || ReferenceEquals(n, store)) continue;
                        if (n.Op == Op.Load && StackOffsetOf(n.In[0], 0) is int at && at < slot + 8 && slot < at + n.Type.Bytes())
                        {
                            if (at != slot || n.Type != VT.I64) ok = false;
                            else loads.Add(n);
                        }
                        else if (n.Op == Op.Store && StackOffsetOf(n.In[0], 0) is int to && to < slot + 8 && slot < to + n.In[1].Type.Bytes())
                            ok = false;
                    }
                }
                if (!ok) continue;
                _caughtStores.Add(store);
                foreach (Node load in loads) _caughtLoads[load] = region;
            }
    }

    /// <summary>The value last stored to stack offset <paramref name="offset"/> before <paramref name="node"/> in its block.</summary>
    private Node? StoredBefore(Node node, int offset)
    {
        Block block = node.Block!;
        for (int i = block.Nodes.IndexOf(node) - 1; i >= 0; i--)
        {
            Node n = block.Nodes[i];
            if (n.Dead) continue;
            if (n.Op == Op.Store && StackOffsetOf(n.In[0], 0) == offset) return n.In[1];
            if (n.Op is Op.Call or Op.TailCall) return null;
        }
        return null;
    }

    /// <summary>True when code in <paramref name="scope"/> runs inside the handler of try region <paramref name="region"/>.</summary>
    private bool InHandlerOf(int scope, int region)
    {
        for (int s = scope, guard = 0; s >= 0 && guard < 64; guard++, s = _fn.TryRegions[s >> 1].Outer)
            if (s == 2 * region + 1) return true;
        return false;
    }

    /// <summary>Merged values that are one stack address whichever way they are reached: phi -> the offset.</summary>
    private readonly Dictionary<Node, int> _framePhis = [];
    /// <summary>The same for a reference bound on entry: phi -> the reference.</summary>
    private readonly Dictionary<Node, Node> _refPhis = [];

    /// <summary>
    /// A register holding the address of a local (or "this" of a struct method) across a try statement comes
    /// back, after an exception, from the stack slot the compiler parked it in. Where the paths meet, the value
    /// is merged from the address itself and the parked copy read back: one address, not a variable.
    /// </summary>
    private void PlanSameAddressPhis()
    {
        var references = new Dictionary<long, Node>();
        var merged = new Dictionary<Node, long>();
        long? Direct(Node n)
        {
            if (StackOffsetOf(n, 0) is int at) return at;
            if (_spillLoads.TryGetValue(n, out int parked)) return parked;
            Node? reference = _refLoads.TryGetValue(n, out Node? read) ? read : IsBoundReference(n) ? n : null;
            if (reference == null) return null;
            long key = ReferenceTargets + reference.Id;
            references[key] = reference;
            return key;
        }
        long? Known(Node n) => Direct(n) ?? (merged.TryGetValue(n, out long m) ? m : null);

        var phis = new List<Node>();
        foreach (Block b in _fn.Blocks)
            foreach (Node phi in b.Phis)
                if (!phi.Dead && phi.Type == VT.I64)
                    phis.Add(phi);
        if (phis.Count == 0) return;
        for (bool grew = true; grew;)
        {
            grew = false;
            foreach (Node phi in phis)
            {
                if (merged.ContainsKey(phi)) continue;
                foreach (Node input in phi.In)
                {
                    if (ReferenceEquals(input, phi) || Known(input) is not long key) continue;
                    merged[phi] = key;
                    grew = true;
                    break;
                }
            }
        }
        for (bool shrank = true; shrank;)
        {
            shrank = false;
            foreach (Node phi in merged.Keys.ToList())
            {
                long expected = merged[phi];
                foreach (Node input in phi.In)
                {
                    if (ReferenceEquals(input, phi) || Known(input) == expected) continue;
                    merged.Remove(phi);
                    shrank = true;
                    break;
                }
            }
        }
        foreach (var (phi, key) in merged)
        {
            if (key >= ReferenceTargets) _refPhis[phi] = references[key];
            else _framePhis[phi] = (int)key;
        }
    }

    private enum DefKind { Spill, Other }

    private readonly Dictionary<ulong, bool> _emptyFunctions = [];

    /// <summary>A function that does nothing: its code is a lone "ret", the code of every empty method of the program.</summary>
    private bool EmptyFunction(ulong address)
    {
        if (address == 0) return false;
        if (_emptyFunctions.TryGetValue(address, out bool known)) return known;
        X64Cfg cfg = X64Cfg.Build(_p.Context, address);
        bool empty = cfg.Blocks.Count == 1 && cfg.Blocks[0].Instructions.Count != 0 && cfg.Blocks[0].Instructions[^1].Mnemonic == Iced.Intel.Mnemonic.Ret;
        for (int i = 0; empty && i < cfg.Blocks[0].Instructions.Count - 1; i++)
            empty = cfg.Blocks[0].Instructions[i].Mnemonic == Iced.Intel.Mnemonic.Nop;
        return _emptyFunctions[address] = empty;
    }

    /// <summary>How many bytes follow stack offset <paramref name="at"/> in the stack object it lies in (256 when it lies in none).</summary>
    private int RestOfObject(int at)
    {
        if (!NoParkedDescriptors)
            foreach (Rewind.Analysis.Passes.FrameObject o in _l.Frame)
                if (at >= o.Offset && at < o.Offset + o.Size)
                    return o.Offset + o.Size - at;
        return 256;
    }

    private void PlanSlot(int slot)
    {
        int end = slot + 8;
        bool Overlaps(int start, int size) => start < end && slot < start + size;

        // The method's own descriptor, kept where the compiler keeps a register argument (one of the four places
        // above the return address) with nothing else ever stored there: the program cannot name that place,
        // so no call writes it - whatever addresses lie where a call of unknown shape might take arguments
        // (the compiler keeps "&method" among its locals, for the code of a finally block).
        bool descriptorHome = !NoParkedDescriptors && slot is >= 8 and < 40;
        if (descriptorHome)
            foreach (Block b in _fn.Blocks)
                foreach (Node n in b.Nodes)
                    if (!n.Dead && n.Op == Op.Store && StackOffsetOf(n.In[0], 0) is int to && Overlaps(to, n.In[1].Type.Bytes()) &&
                        !(to == slot && n.In[1].Type == VT.I64 && _sem.TryGetValue(n.In[1], out Sem? kept) && kept is SMethod))
                        descriptorHome = false;

        // Definitions and uses of the slot, in block order.
        // Targets: a stack offset, or (from ReferenceTargets on) the id of a bound reference value.
        var references = new Dictionary<long, Node>();
        var events = new Dictionary<Block, List<(Node Node, bool IsDef, DefKind Kind, long Target)>>();
        foreach (Block b in _fn.Blocks)
        {
            var list = new List<(Node, bool, DefKind, long)>();
            foreach (Node n in b.Nodes)
            {
                if (n.Dead) continue;
                if (n.Op == Op.Store && StackOffsetOf(n.In[0], 0) is int at && Overlaps(at, n.In[1].Type.Bytes()))
                {
                    long target = 0;
                    bool spill = false;
                    if (at == slot && n.In[1].Type == VT.I64)
                    {
                        if (StackOffsetOf(n.In[1], 0) is int parked)
                        {
                            spill = true;
                            target = parked;
                        }
                        else if (IsBoundReference(n.In[1]))
                        {
                            spill = true;
                            target = ReferenceTargets + n.In[1].Id;
                            references[target] = n.In[1];
                        }
                    }
                    list.Add((n, true, spill ? DefKind.Spill : DefKind.Other, target));
                }
                else if (n.Op == Op.Load && StackOffsetOf(n.In[0], 0) is int from && Overlaps(from, n.Type.Bytes()))
                    list.Add((n, false, DefKind.Other, 0));
                else if (n.Op is Op.Call or Op.TailCall)
                {
                    if (descriptorHome) continue;
                    // A function that does nothing writes nothing, whatever the registers hold as it is called.
                    if (!NoParkedDescriptors && n.Aux is CallInfo { Indirect: false, Target: var called } && EmptyFunction(called)) continue;
                    // A call handed a stack address may write the object there: all of it when its type is known,
                    // else what follows the address in the stack object it lies in (the frame was told apart
                    // into objects on that understanding), else anything at and after the address.
                    foreach (Node input in n.In)
                        if (StackOffsetOf(input, 0) is int arg && arg <= slot &&
                            slot < arg + (_frameTypes.TryGetValue(arg, out TypeSig? pointee) ? Math.Max(1, _p.Layouts.SizeOf(pointee).Size) : RestOfObject(arg)))
                        {
                            list.Add((n, true, DefKind.Other, 0));
                            break;
                        }
                }
            }
            if (list.Count != 0) events[b] = list;
        }

        // Reaching definitions of the slot at block ends (each definition replaces the slot's content).
        var handlerOf = new Dictionary<Block, int>();
        foreach (var (gate, region) in _fn.TryGates()) handlerOf[gate.Succs[0]] = region;
        var defsOut = new Dictionary<Block, HashSet<Node?>>();
        HashSet<Node?> In(Block b)
        {
            if (ReferenceEquals(b, _fn.Entry)) return [null]; // null: whatever the slot held on entry
            var set = new HashSet<Node?>();
            foreach (Block p in b.Preds)
                if (defsOut.TryGetValue(p, out HashSet<Node?>? o)) set.UnionWith(o);
            // A handler is entered from anywhere in its region: every write there may be the last one before it.
            if (handlerOf.TryGetValue(b, out int region))
                foreach (Block inside in _fn.Blocks)
                {
                    if (!_fn.IsProtectedBy(inside, region)) continue;
                    if (defsOut.TryGetValue(inside, out HashSet<Node?>? o)) set.UnionWith(o);
                    if (events.TryGetValue(inside, out var written))
                        foreach (var e in written)
                            if (e.IsDef) set.Add(e.Node);
                }
            return set;
        }
        bool changed = true;
        for (int round = 0; changed && round < 64; round++)
        {
            changed = false;
            foreach (Block b in _cfg.ReversePostOrder)
            {
                HashSet<Node?> outSet;
                if (events.TryGetValue(b, out var list) && list.LastOrDefault(e => e.IsDef) is { Node: not null } last)
                    outSet = [last.Node];
                else outSet = In(b);
                if (!defsOut.TryGetValue(b, out HashSet<Node?>? old) || !old.SetEquals(outSet))
                {
                    defsOut[b] = outSet;
                    changed = true;
                }
            }
        }

        var spillTarget = new Dictionary<Node, long>();
        foreach (var list in events.Values)
            foreach (var e in list)
                if (e.IsDef && e.Kind == DefKind.Spill)
                    spillTarget[e.Node] = e.Target;

        var resolved = new Dictionary<Node, long>();
        foreach (var (b, list) in events)
        {
            HashSet<Node?> reaching = In(b);
            foreach (var e in list)
            {
                if (e.IsDef)
                {
                    reaching = [e.Node];
                    continue;
                }
                bool anySpill = reaching.Any(d => d != null && spillTarget.ContainsKey(d));
                if (!anySpill) continue;
                // A load that can see a parked address must read exactly that address, from every way in.
                long? target = null;
                bool ok = e.Node.Type == VT.I64 && StackOffsetOf(e.Node.In[0], 0) == slot;
                foreach (Node? d in reaching)
                {
                    if (!ok) break;
                    if (d == null || !spillTarget.TryGetValue(d, out long t)) { ok = false; break; }
                    if (target != null && target != t) ok = false;
                    target = t;
                }
                if (!ok || target == null) return; // ambiguous: leave the slot as it is
                resolved[e.Node] = target.Value;
            }
        }
        foreach (Node store in spillTarget.Keys) _spillStores.Add(store);
        foreach (var (load, target) in resolved)
        {
            if (target >= ReferenceTargets) _refLoads[load] = references[target];
            else _spillLoads[load] = (int)target;
        }
    }
}
