using Rewind.Analysis.Ir;
using Rewind.Analysis.X64;

namespace Rewind.Analysis.Passes;

/// <summary>
/// Resolves stack addresses the compiler parks in stack slots.
///
/// A register holding the address of a local ("this" for calls on a struct, a captured variable for a finally
/// block) is saved to a stack slot when registers run out or a try statement begins, and read back later. Left
/// as it is, the address has been "stored somewhere" - which every later analysis must take to mean that the
/// local can be reached from anywhere. When every write that can reach a read of the slot parks the same
/// address, the read is that address; with all its reads resolved, the slot plays no part in the program.
/// </summary>
public static class ParkedAddresses
{
    private static readonly bool Tracing = Environment.GetEnvironmentVariable("REWIND_PARK_TRACE") != null;
    private static readonly bool NoPartialParks = Environment.GetEnvironmentVariable("REWIND_NO_PARTIAL_PARKS") != null;

    private static void Trace(string text)
    {
        if (Tracing) Console.WriteLine("  [park] " + text);
    }

    private enum Kind { Park, Other }

    /// <summary>
    /// Writes every "stack pointer + constant + constant" as one "stack pointer + constant". The builder folds
    /// these as it goes, but replacing a value by a stack address (a parked address read back, a promoted slot
    /// that held one) leaves the two-step form behind, and the stack analyses know only the one-step form.
    /// </summary>
    public static bool Canonicalize(Function fn)
    {
        if (!fn.Params.TryGetValue(fn.Regs.StackPointer, out Node? sp0)) return false;
        bool any = false;
        for (int round = 0; round < 6; round++)
        {
            bool changed = false;
            foreach (Block b in fn.Blocks)
                foreach (Node n in b.Nodes)
                {
                    if (n.Dead || n.Op is not (Op.Add or Op.Sub) || n.Type != VT.I64 || !n.In[1].IsConst) continue;
                    if (n.In[0] is not { Op: Op.Add, Dead: false } inner || !ReferenceEquals(inner.In[0], sp0) || !inner.In[1].IsConst) continue;
                    Node sum = fn.NewNode(Op.Const, VT.I64, null);
                    sum.Imm = IrBuilder.SImm(inner.In[1]) + (n.Op == Op.Add ? IrBuilder.SImm(n.In[1]) : -IrBuilder.SImm(n.In[1]));
                    n.Op = Op.Add;
                    n.In = [sp0, sum];
                    changed = true;
                }
            if (!changed) break;
            any = true;
        }
        return any;
    }

    /// <param name="escapeExtent">For a stack address passed as input <c>index</c> of a call: how many bytes the callee may touch, or -1.</param>
    public static bool Run(Function fn, Func<Node, int, int>? escapeExtent = null)
    {
        if (!fn.Params.TryGetValue(fn.Regs.StackPointer, out Node? sp0)) return false;

        int? Stack(Node n)
        {
            long k = 0;
            for (int depth = 0; depth < 8; depth++)
            {
                if (ReferenceEquals(n, sp0)) return k is > -0x4000000 and < 0x4000000 ? (int)k : null;
                if (n.Op == Op.Add && n.In[1].IsConst) k += IrBuilder.SImm(n.In[1]);
                else if (n.Op == Op.Sub && n.In[1].IsConst) k -= IrBuilder.SImm(n.In[1]);
                else return null;
                n = n.In[0];
            }
            return null;
        }

        var slots = new HashSet<int>();
        foreach (Block b in fn.Blocks)
            foreach (Node n in b.Nodes)
                if (!n.Dead && n.Op == Op.Store && n.In[1].Type == VT.I64 && Stack(n.In[0]) is int at && Stack(n.In[1]) is not null)
                    slots.Add(at);
        if (slots.Count == 0) return false;

        var handlerOf = new Dictionary<Block, int>();
        foreach (var (gate, region) in fn.TryGates()) handlerOf[gate.Succs[0]] = region;
        var cfg = new Cfg(fn);
        bool changed = false;
        foreach (int slot in slots.OrderBy(s => s)) changed |= Resolve(fn, sp0, slot, Stack, escapeExtent, handlerOf, cfg);
        if (changed)
            foreach (Block b in fn.Blocks) b.Nodes.RemoveAll(n => n.Dead);
        return changed;
    }

    private static bool Resolve(Function fn, Node sp0, int slot, Func<Node, int?> stack, Func<Node, int, int>? escapeExtent,
        Dictionary<Block, int> handlerOf, Cfg cfg)
    {
        int end = slot + 8;
        bool Overlaps(int start, int size) => start < end && slot < start + size;

        // Writes and reads of the slot, in block order.
        var events = new Dictionary<Block, List<(Node Node, bool IsDef, Kind Kind, int Target)>>();
        bool reachable = false; // some call may touch the slot through an address it is given
        foreach (Block b in fn.Blocks)
        {
            List<(Node, bool, Kind, int)>? list = null;
            foreach (Node n in b.Nodes)
            {
                if (n.Dead) continue;
                if (n.Op == Op.Store && stack(n.In[0]) is int at && Overlaps(at, n.In[1].Type.Bytes()))
                {
                    bool park = at == slot && n.In[1].Type == VT.I64 && stack(n.In[1]) is not null;
                    (list ??= []).Add((n, true, park ? Kind.Park : Kind.Other, park ? stack(n.In[1])!.Value : 0));
                }
                else if (n.Op == Op.Load && stack(n.In[0]) is int from && Overlaps(from, n.Type.Bytes()))
                    (list ??= []).Add((n, false, Kind.Other, 0));
                else if (n.Op is Op.Call or Op.TailCall)
                {
                    // A call handed a stack address may read and write the object there: as much of it as is known,
                    // else anything at and after the address.
                    for (int i = 0; i < n.In.Length; i++)
                    {
                        if (stack(n.In[i]) is not int arg || arg > slot) continue;
                        int extent = escapeExtent?.Invoke(n, i) ?? -1;
                        if (slot >= arg + (extent > 0 ? extent : 256)) continue;
                        (list ??= []).Add((n, true, Kind.Other, 0));
                        reachable = true;
                        break;
                    }
                }
            }
            if (list != null) events[b] = list;
        }

        // Which writes can be the last one before each point (each write replaces the slot's content).
        var defsOut = new Dictionary<Block, HashSet<Node?>>();
        HashSet<Node?> In(Block b)
        {
            if (ReferenceEquals(b, fn.Entry)) return [null]; // null: whatever the slot held on entry
            var set = new HashSet<Node?>();
            foreach (Block p in b.Preds)
                if (defsOut.TryGetValue(p, out HashSet<Node?>? o)) set.UnionWith(o);
            // A handler is entered from anywhere in its region: every write there may be the last one before it.
            if (handlerOf.TryGetValue(b, out int region))
                foreach (Block inside in fn.Blocks)
                {
                    if (!fn.IsProtectedBy(inside, region)) continue;
                    if (defsOut.TryGetValue(inside, out HashSet<Node?>? o)) set.UnionWith(o);
                    if (events.TryGetValue(inside, out var written))
                        foreach (var e in written)
                            if (e.IsDef) set.Add(e.Node);
                }
            return set;
        }
        bool moving = true;
        for (int round = 0; moving && round < 64; round++)
        {
            moving = false;
            foreach (Block b in cfg.ReversePostOrder)
            {
                HashSet<Node?> outSet;
                if (events.TryGetValue(b, out var list) && list.LastOrDefault(e => e.IsDef) is { Node: not null } last) outSet = [last.Node];
                else outSet = In(b);
                if (!defsOut.TryGetValue(b, out HashSet<Node?>? old) || !old.SetEquals(outSet))
                {
                    defsOut[b] = outSet;
                    moving = true;
                }
            }
        }
        if (moving) return false;

        var parked = new Dictionary<Node, int>();
        foreach (var list in events.Values)
            foreach (var e in list)
                if (e.IsDef && e.Kind == Kind.Park)
                    parked[e.Node] = e.Target;
        if (parked.Count == 0) return false;

        var resolved = new Dictionary<Node, int>();
        bool ambiguous = false;
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
                if (!reaching.Any(d => d != null && parked.ContainsKey(d))) continue;
                // A read that can see a parked address must read exactly that address, from every way in.
                int? target = null;
                bool ok = e.Node.Type == VT.I64 && stack(e.Node.In[0]) == slot;
                foreach (Node? d in reaching)
                {
                    if (!ok) break;
                    if (d == null || !parked.TryGetValue(d, out int t)) { ok = false; break; }
                    if (target != null && target != t) ok = false;
                    target = t;
                }
                if (!ok || target == null)
                {
                    // Ambiguous: this read stays a read (and the slot keeps its writes); the others are still known.
                    Trace($"slot {slot}: read at 0x{e.Node.Addr:X} sees {string.Join(", ", reaching.Select(d => d == null ? "entry" : d.Op + "@0x" + d.Addr.ToString("X")))}");
                    if (NoPartialParks) return false;
                    ambiguous = true;
                    continue;
                }
                resolved[e.Node] = target.Value;
            }
        }
        if (resolved.Count == 0 && (reachable || ambiguous)) return false;

        // The reads become the address itself.
        var replace = new Dictionary<Node, Node>();
        foreach (var (load, target) in resolved)
        {
            Block? home = fn.Blocks.FirstOrDefault(b => b.Nodes.Contains(load));
            if (home == null) return false;
            Node offset = fn.NewNode(Op.Const, VT.I64, null);
            offset.Imm = target;
            Node address = fn.NewNode(Op.Add, VT.I64, home, sp0, offset);
            address.Addr = load.Addr;
            home.Nodes.Insert(home.Nodes.IndexOf(load), address);
            replace[load] = address;
            load.Dead = true;
        }
        if (replace.Count != 0)
            foreach (Block b in fn.Blocks)
            {
                foreach (Node n in b.Phis)
                    for (int i = 0; i < n.In.Length; i++)
                        if (replace.TryGetValue(n.In[i], out Node? r)) n.In[i] = r;
                foreach (Node n in b.Nodes)
                    for (int i = 0; i < n.In.Length; i++)
                        if (replace.TryGetValue(n.In[i], out Node? r)) n.In[i] = r;
            }
        // With nothing left that could read them, the parking writes do nothing.
        if (!reachable && !ambiguous)
            foreach (Node store in parked.Keys) store.Dead = true;
        return replace.Count != 0 || (!reachable && !ambiguous);
    }
}
