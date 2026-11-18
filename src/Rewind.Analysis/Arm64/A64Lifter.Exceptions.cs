using Rewind.Analysis.Ir;
using Rewind.Analysis.X64;
using Rewind.Binary;

namespace Rewind.Analysis.Arm64;

/// <summary>
/// C++ exception handling as clang compiles it for AArch64 (the Itanium ABI), turned into the try regions the
/// rest of the pipeline knows from x64.
///
/// IL2CPP writes every managed try as "try { ... } catch (Il2CppExceptionWrapper&amp; e) { ... }". The calls in
/// the try block are listed in the function's exception table with a landing pad: code in the function itself
/// that the unwinder jumps to with the exception in x0 and the matched clause in x1. It calls
/// __cxa_begin_catch, which hands back the wrapper (whose first field is the managed exception), tests the
/// exception's class for each managed catch clause and leaves the C++ handler through __cxa_end_catch, after
/// which the code of the managed catch block runs as ordinary code of the function; or it throws the wrapper on
/// (__cxa_allocate_exception, __cxa_throw). A finally is the same with a handler that only keeps the exception.
///
/// So a landing pad is the handler of a try region, from the pad to the calls of __cxa_end_catch, and the code
/// after each of those is where the handler continues: what a catch funclet's continuation is on x64. The
/// region is the code that leads to the calls the pad protects. Try regions inside one another are not taken
/// apart yet; such a function says so.
/// </summary>
public sealed partial class A64Lifter
{
    private string? _ehFailure;
    private readonly Dictionary<Block, int> _gates = [];
    private readonly Dictionary<Block, (int Region, long Selector, List<int> Lost)> _landings = [];
    private ulong _beginCatch, _endCatch, _allocateException;
    private bool _importsKnown;

    private bool Fail(string why)
    {
        _ehFailure = why;
        return false;
    }

    private void FindUnwindImports()
    {
        if (_importsKnown) return;
        _importsKnown = true;
        if (_image is not ElfImage elf) return;
        foreach (var (stub, name) in elf.ImportStubs)
            switch (name)
            {
                case "__cxa_begin_catch": _beginCatch = stub; break;
                case "__cxa_end_catch": _endCatch = stub; break;
                case "__cxa_allocate_exception": _allocateException = stub; break;
            }
    }

    /// <summary>Branches whose way is known before lifting (a landing pad's test of the clause it was entered for).</summary>
    private readonly HashSet<Block> _decided = [];

    /// <summary>The code a landing pad leads to: clang gives calls separate pads that only jump to one shared handler.</summary>
    internal ulong CanonicalPad(ulong pad)
    {
        for (int hop = 0; hop < 4 && _image.IsMapped(pad, 4); hop++)
        {
            A64Instruction first = A64Decoder.Decode(_image.U32(pad), pad);
            if (first.Op != A64Op.B) break;
            pad = first.Target;
        }
        return pad;
    }

    /// <summary>
    /// Whether a call site holds a call of the program, and not only the runtime's own calls of a handler: the
    /// landing pad of an __cxa_end_catch (where clang has the catch's destructors run when ending the catch
    /// throws) is no try region of the program.
    /// </summary>
    private bool ProtectsProgramCalls(CallSite site)
    {
        for (ulong at = site.Start; at < site.End && _image.IsMapped(at, 4); at += 4)
        {
            A64Instruction i = A64Decoder.Decode(_image.U32(at), at);
            if (i.IsCall && !IsUnwindCall(i)) return true;
        }
        return false;
    }

    private bool IsUnwindCall(in A64Instruction i) =>
        i.Op == A64Op.Bl && i.Target != 0 && (i.Target == _beginCatch || i.Target == _endCatch || i.Target == _allocateException);

    /// <summary>The first instruction after the prologue (stack allocation, register saves, frame pointer).</summary>
    private ulong PrologueEnd(ulong start)
    {
        ulong at = start;
        for (int k = 0; k < 24 && _image.IsMapped(at, 4); k++, at += 4)
        {
            A64Instruction i = A64Decoder.Decode(_image.U32(at), at);
            bool part = (i.Op == A64Op.SubImm && !i.SetFlags && i.Rd == A64Instruction.Sp && i.Rn == A64Instruction.Sp) ||
                        (i.Op is A64Op.Stp or A64Op.Str && i.Rn == A64Instruction.Sp) ||
                        (i.Op == A64Op.AddImm && !i.SetFlags && i.Rd == 29 && i.Rn == A64Instruction.Sp) ||
                        i.Op == A64Op.Nop;
            if (!part) break;
        }
        return at;
    }

    /// <summary>
    /// Builds the try regions of a function whose exception table has landing pads that catch: tags each block
    /// with its region, puts a gate before each region's entry and a landing block before its handler. False
    /// when the shape is not one this handles.
    /// </summary>
    private bool PlanRegions(ItaniumExceptionTable table, List<ulong> pads, Dictionary<Block, A64Block> rawOf, Dictionary<ulong, Block> blockAt)
    {
        foreach (ulong pad in pads)
            if (!blockAt.ContainsKey(pad)) return Fail("landing pad not decoded");
        // A pad that ends a catch before beginning one passes the exception out of a handler it was raised in: it
        // leaves that catch and goes on to the handler around it. That end of a catch ends no handler.
        var passing = new HashSet<Block>();
        foreach (ulong address in pads)
        {
            Block b = blockAt[address];
            for (int hop = 0; hop < 4 && rawOf.TryGetValue(b, out A64Block? raw); hop++)
            {
                if (raw.Instructions.Any(i => i.Op == A64Op.Bl && i.Target == _beginCatch && _beginCatch != 0)) break;
                if (raw.Instructions.Count != 0 && raw.Instructions[^1].Op == A64Op.Bl && raw.Instructions[^1].Target == _endCatch && _endCatch != 0)
                {
                    passing.Add(b);
                    break;
                }
                if (b.Succs.Count != 1) break;
                b = b.Succs[0];
            }
        }
        bool EndsCatch(Block b) => !passing.Contains(b) && rawOf.TryGetValue(b, out A64Block? raw) && raw.Instructions.Count != 0 &&
                                   raw.Instructions[^1].Op == A64Op.Bl && raw.Instructions[^1].Target == _endCatch;
        HashSet<Block> Reach(Block from)
        {
            var seen = new HashSet<Block>();
            var work = new Stack<Block>();
            work.Push(from);
            while (work.Count > 0)
            {
                Block b = work.Pop();
                if (!seen.Add(b) || EndsCatch(b)) continue;
                foreach (Block s in b.Succs) work.Push(s);
            }
            return seen;
        }

        var sites = table.CallSites.Where(c => c.Catches && ProtectsProgramCalls(c)).ToList();
        var padSelector = new long[pads.Count];
        for (int i = 0; i < pads.Count; i++)
        {
            var filters = sites.Where(c => CanonicalPad(c.LandingPad) == pads[i]).Select(c => c.Filter).Distinct().ToList();
            if (filters.Count != 1) return Fail("a landing pad entered for different catch clauses");
            padSelector[i] = filters[0];
        }
        // A landing pad first tests the clause it was entered for: known here, so only one way is taken. (The pad
        // may copy the clause number elsewhere first, "mov x21, x1; ...; cmp w21, #1", and the test may come a
        // block or two later.)
        _decided.Clear();
        for (int t = 0; t < pads.Count; t++)
        {
            Block b = blockAt[pads[t]];
            var copies = new HashSet<byte> { 1 };
            for (int hop = 0; hop < 8 && rawOf.TryGetValue(b, out A64Block? raw); hop++)
            {
                int test = -1;
                for (int k = 0; k < raw.Instructions.Count - 1; k++)
                {
                    A64Instruction ins = raw.Instructions[k];
                    if (ins.Op == A64Op.SubImm && ins.SetFlags && ins.Rd == A64Instruction.Zr && copies.Contains(ins.Rn))
                    {
                        test = k;
                        continue;
                    }
                    if (ins.SetFlags || ins.Op is A64Op.FCmp or A64Op.FCmpe or A64Op.CcmpImm or A64Op.CcmpReg or A64Op.CcmnImm or A64Op.CcmnReg
                            or A64Op.FCcmp or A64Op.FCcmpe)
                        test = -1;
                    bool copy = (ins.Op == A64Op.Orr && ins.Rn == A64Instruction.Zr && ins.Amount == 0 && copies.Contains(ins.Rm)) ||
                                (ins.Op == A64Op.AddImm && !ins.SetFlags && ins.Imm == 0 && copies.Contains(ins.Rn));
                    foreach (byte r in copies.ToList())
                        if (A64Cfg.Writes(ins, r)) copies.Remove(r);
                    if (copy) copies.Add(ins.Rd);
                    if (ins.IsCall) copies.Clear();
                }
                if (raw.End == BlockEnd.Branch && b.Succs.Count == 2 && raw.Instructions[^1].Op == A64Op.BCond)
                {
                    A64Instruction branch = raw.Instructions[^1];
                    if (test >= 0 && branch.Cond is 0 or 1)
                    {
                        bool equal = padSelector[t] == raw.Instructions[test].Imm;
                        bool taken = branch.Cond == 0 ? equal : !equal;
                        Block dead = b.Succs[taken ? 1 : 0];
                        b.Succs.Remove(dead);
                        dead.Preds.Remove(b);
                        _decided.Add(b);
                    }
                    break;
                }
                // (A copy of the clause made in the last instruction of a block.)
                A64Instruction last = raw.Instructions[^1];
                if ((last.Op == A64Op.Orr && last.Rn == A64Instruction.Zr && last.Amount == 0 && copies.Contains(last.Rm)) ||
                    (last.Op == A64Op.AddImm && !last.SetFlags && last.Imm == 0 && copies.Contains(last.Rn)))
                    copies.Add(last.Rd);
                if (b.Succs.Count != 1 || raw.End is not (BlockEnd.FallThrough or BlockEnd.Jump)) break;
                b = b.Succs[0];
            }
        }

        // Pads whose code meets belong to one try region: clang gives calls pads of their own where the registers
        // need different fixing up before the shared handler.
        var reach = pads.Select(p => Reach(blockAt[p])).ToList();
        int[] parent = Enumerable.Range(0, pads.Count).ToArray();
        int Find(int x) => parent[x] == x ? x : parent[x] = Find(parent[x]);
        for (int i = 0; i < pads.Count; i++)
            for (int j = i + 1; j < pads.Count; j++)
                if (reach[i].Overlaps(reach[j])) parent[Find(i)] = Find(j);
        var roots = Enumerable.Range(0, pads.Count).Select(Find).Distinct().OrderBy(r => pads[r]).ToList();
        int count = roots.Count;
        int[] regionOfPad = Enumerable.Range(0, pads.Count).Select(i => roots.IndexOf(Find(i))).ToArray();
        int SitesOf(int pad) => sites.Count(c => CanonicalPad(c.LandingPad) == pads[pad]);
        var primary = new int[count];
        for (int t = 0; t < count; t++)
            primary[t] = Enumerable.Range(0, pads.Count).Where(i => regionOfPad[i] == t).OrderByDescending(SitesOf).ThenBy(i => pads[i]).First();
        for (int t = 0; t < count; t++) _fn.TryRegions.Add(new TryRegionInfo { Index = t, Funclet = pads[primary[t]] });
        int RegionOfCall(ulong address)
        {
            foreach (CallSite site in table.CallSites)
                if (address >= site.Start && address < site.End)
                    return site.Catches && ProtectsProgramCalls(site) && pads.IndexOf(CanonicalPad(site.LandingPad)) is int pad and >= 0 ? regionOfPad[pad] : -1;
            return -1;
        }
        var selector = new long[count];
        for (int t = 0; t < count; t++)
        {
            var filters = Enumerable.Range(0, pads.Count).Where(i => regionOfPad[i] == t).Select(i => padSelector[i]).Distinct().ToList();
            if (filters.Count != 1) return Fail("the landing pads of one try region enter different catch clauses");
            selector[t] = filters[0];
        }

        // The other pads of a region: their own code is dropped (the region is entered through its main pad), and
        // what they set before joining it is lost - unless the main pad sets it alike.
        var dropped = new HashSet<Block>();
        var padLost = new SortedSet<int>[count];
        for (int t = 0; t < count; t++)
        {
            padLost[t] = [];
            HashSet<Block> main = reach[primary[t]];
            var others = Enumerable.Range(0, pads.Count).Where(i => regionOfPad[i] == t && i != primary[t]).ToList();
            var mainOwn = new HashSet<Block>(main);
            foreach (int other in others) mainOwn.ExceptWith(reach[other]);
            var mainWrites = new Dictionary<int, uint>();
            foreach (Block b in mainOwn)
                foreach (A64Instruction ins in rawOf[b].Instructions)
                    foreach (int v in WrittenVariables(ins))
                        mainWrites[v] = ins.Word;
            foreach (int other in others)
                foreach (Block b in reach[other])
                {
                    if (main.Contains(b)) continue;
                    dropped.Add(b);
                    foreach (A64Instruction ins in rawOf[b].Instructions)
                        foreach (int v in ins.IsCall ? [] : WrittenVariables(ins))
                        {
                            if (mainWrites.TryGetValue(v, out uint word))
                            {
                                if (word != ins.Word) return Fail("the landing pads of one try region set up registers differently");
                                continue;
                            }
                            padLost[t].Add(v);
                        }
                }
        }

        var parentBlocks = _fn.Blocks.Where(b => !dropped.Contains(b)).ToList();

        // The handlers: from each landing pad up to where it ends the catch.
        var handlerOf = new Dictionary<Block, int>();
        var continuations = new List<Block>[count];
        for (int t = 0; t < count; t++)
        {
            continuations[t] = [];
            Block pad = blockAt[pads[primary[t]]];
            var work = new Stack<Block>();
            work.Push(pad);
            while (work.Count > 0)
            {
                Block b = work.Pop();
                if (handlerOf.TryGetValue(b, out int other))
                {
                    if (other != t) return Fail($"two handlers share code (0x{b.Start:X})");
                    continue;
                }
                handlerOf[b] = t;
                bool ends = EndsCatch(b);
                foreach (Block s in b.Succs)
                    if (ends)
                    {
                        if (!continuations[t].Contains(s)) continuations[t].Add(s);
                    }
                    else work.Push(s);
            }
        }
        var handlerCalls = new List<(int Handler, int Region)>();
        foreach (var (b, t) in handlerOf)
        {
            if (b.Preds.FirstOrDefault(p => !handlerOf.ContainsKey(p) && !dropped.Contains(p)) is { } outsider)
                return Fail($"a handler is also reached by the function's own code (0x{b.Start:X} from 0x{outsider.Start:X})");
            foreach (A64Instruction ins in rawOf[b].Instructions)
                if (ins.IsCall && !IsUnwindCall(ins) && RegionOfCall(ins.Address) is int u and >= 0) handlerCalls.Add((t, u));
        }
        for (int t = 0; t < count; t++)
            if (continuations[t].Any(handlerOf.ContainsKey)) return Fail("a catch continues inside a handler");

        // Which regions the calls of each block of the function's own code belong to (-1: none).
        var callRegions = new Dictionary<Block, HashSet<int>>();
        foreach (Block b in parentBlocks)
        {
            if (handlerOf.ContainsKey(b) || !rawOf.TryGetValue(b, out A64Block? raw)) continue;
            foreach (A64Instruction ins in raw.Instructions)
            {
                if (!ins.IsCall || IsUnwindCall(ins)) continue;
                if (!callRegions.TryGetValue(b, out HashSet<int>? set)) callRegions[b] = set = [];
                set.Add(RegionOfCall(ins.Address));
            }
        }
        // (A call that no landing pad protects cannot throw, or is outside every try: either way it belongs to no region.)
        if (callRegions.Values.Any(s => s.Count(r => r >= 0) > 1)) return Fail("a block mixes calls of different try regions");
        var protectedCalls = new List<Block>[count];
        for (int t = 0; t < count; t++)
            protectedCalls[t] = callRegions.Where(kv => kv.Value.Contains(t)).Select(kv => kv.Key).ToList();

        // Control flow of the function's own code, with the exceptional edges from protected calls to where
        // their handler continues.
        var own = parentBlocks.Where(b => !handlerOf.ContainsKey(b)).ToList();
        var ownSet = new HashSet<Block>(own);
        var succs = new Dictionary<Block, List<Block>>();
        var preds = new Dictionary<Block, List<Block>>();
        foreach (Block b in own)
        {
            succs[b] = b.Succs.Where(ownSet.Contains).ToList();
            preds[b] = b.Preds.Where(ownSet.Contains).ToList();
        }
        for (int t = 0; t < count; t++)
            foreach (Block from in protectedCalls[t])
                foreach (Block to in continuations[t])
                    if (ownSet.Contains(to) && !succs[from].Contains(to))
                    {
                        succs[from].Add(to);
                        preds[to].Add(from);
                    }
        Dictionary<Block, Block> idom = X64Lifter.Dominators(own[0], succs, preds);
        bool Dominates(Block a, Block b)
        {
            for (Block? x = b; x != null; x = idom.TryGetValue(x, out Block? up) && !ReferenceEquals(up, x) ? up : null)
                if (ReferenceEquals(x, a)) return true;
            return false;
        }

        var found = new List<(int Region, Block Entry, HashSet<Block> Body)>();
        for (int t = 0; t < count; t++)
        {
            List<Block> must = protectedCalls[t];
            if (must.Count == 0 || must.Any(b => !idom.ContainsKey(b))) continue; // nothing in it can raise an exception
            Block entry = must[0];
            foreach (Block b in must.Skip(1))
                while (!Dominates(entry, b)) entry = idom[entry];
            var body = new HashSet<Block>(must) { entry };
            var work = new Stack<Block>(must);
            while (work.Count > 0)
            {
                Block b = work.Pop();
                if (ReferenceEquals(b, entry)) continue;
                foreach (Block p in preds[b])
                    if (!continuations[t].Contains(p) && Dominates(entry, p) && body.Add(p)) work.Push(p);
            }
            if (body.Any(continuations[t].Contains)) return Fail("the catch continues inside its own try region");
            if (ReferenceEquals(entry, own[0])) return Fail("try region entry not found");
            found.Add((t, entry, body));
        }

        // Outermost first: a region's code is carved out of the scope its try statement is in.
        var made = new List<(int Region, Block Entry, List<Block> Outside, HashSet<Block> Body)>();
        foreach (var (t, entry, body) in found.OrderByDescending(f => f.Body.Count))
        {
            int outer = entry.Scope;
            if (body.Any(b => b.Scope != outer)) return Fail("try regions overlap");
            var outside = new List<Block>();
            foreach (Block b in body)
                foreach (Block p in b.Preds)
                {
                    if (body.Contains(p)) continue;
                    if (!ReferenceEquals(b, entry)) return Fail("try region entered in several places");
                    if (!outside.Contains(p)) outside.Add(p);
                }
            foreach (Block b in body) b.Scope = 2 * t;
            _fn.TryRegions[t].Outer = outer;
            made.Add((t, entry, outside, body));
        }
        // Every call a region protects is inside it (and not in one nested in it that catches for itself).
        foreach (var (b, regions) in callRegions)
            foreach (int r in regions)
                if (r >= 0 && b.Scope != 2 * r) return Fail("a protected call outside its try region");
        bool Encloses(int region, int scope)
        {
            for (int s = scope, guard = 0; s >= 0 && guard < 64; guard++, s = _fn.TryRegions[s >> 1].Outer)
                if (s == 2 * region) return true;
            return false;
        }
        // A handler's own calls are protected by a region around its try statement, if by any.
        foreach (var (handler, region) in handlerCalls)
            if (!Encloses(region, _fn.TryRegions[handler].Outer)) return Fail("try inside a catch clause");

        foreach (var (t, entry, outside, body) in made)
        {
            // Callee-saved registers the protected code writes: the unwinder gives the handler their values as
            // they were at the call that raised the exception, which one path into the handler cannot say.
            var lost = new SortedSet<int>(padLost[t]);
            foreach (Block b in body)
                foreach (A64Instruction ins in rawOf[b].Instructions)
                {
                    for (byte r = 19; r <= 29; r++)
                        if (A64Cfg.Writes(ins, r)) lost.Add(r);
                    if (A64Cfg.IsFpDestination(ins) && ins.Rd is >= 8 and < 16)
                        for (int lane = 0; lane < 2; lane++) lost.Add(LaneVar(ins.Rd, lane));
                    if (ins.Vector && ins.Op is A64Op.Ldr or A64Op.Ldp or A64Op.LdrLit)
                        foreach (byte v in ins.Op == A64Op.Ldp ? new[] { ins.Rd, ins.Ra } : new[] { ins.Rd })
                            if (v is >= 8 and < 16)
                                for (int lane = 0; lane < 2; lane++) lost.Add(LaneVar(v, lane));
                }

            var gate = new Block { Id = _fn.Blocks.Count, Start = entry.Start, End = entry.Start, Scope = _fn.TryRegions[t].Outer };
            _fn.Blocks.Add(gate);
            var landing = new Block { Id = _fn.Blocks.Count, Start = pads[primary[t]], End = pads[primary[t]], Scope = 2 * t + 1 };
            _fn.Blocks.Add(landing);
            foreach (Block p in outside)
                for (int i = 0; i < p.Succs.Count; i++)
                    if (ReferenceEquals(p.Succs[i], entry))
                    {
                        p.Succs[i] = gate;
                        gate.Preds.Add(p);
                    }
            entry.Preds.RemoveAll(outside.Contains);
            gate.Succs.Add(landing);
            landing.Preds.Add(gate);
            gate.Succs.Add(entry);
            entry.Preds.Add(gate);
            Block pad = blockAt[pads[primary[t]]];
            landing.Succs.Add(pad);
            pad.Preds.Add(landing);
            _gates[gate] = t;
            _landings[landing] = (t, selector[t], lost.ToList());
        }
        foreach (var (b, t) in handlerOf) b.Scope = 2 * t + 1;
        return true;
    }

    /// <summary>A branch whose way was settled before lifting: a plain jump to the one successor left.</summary>
    private bool LiftDecided(Block block)
    {
        if (!_decided.Contains(block) || block.Succs.Count != 1) return false;
        _b.Raw(Op.Jump, VT.None);
        return true;
    }

    /// <summary>The variables an instruction writes: general registers, and all four lanes of a SIMD/FP register it sets.</summary>
    private static IEnumerable<int> WrittenVariables(A64Instruction ins)
    {
        for (byte r = 0; r <= 30; r++)
            if (A64Cfg.Writes(ins, r)) yield return r;
        var vectors = new List<byte>();
        if (A64Cfg.IsFpDestination(ins)) vectors.Add(ins.Rd);
        if (ins.Vector && ins.Op is A64Op.Ldr or A64Op.Ldp or A64Op.LdrLit)
        {
            vectors.Add(ins.Rd);
            if (ins.Op == A64Op.Ldp) vectors.Add(ins.Ra);
        }
        foreach (byte v in vectors)
            for (int lane = 0; lane < 4; lane++) yield return LaneVar(v, lane);
    }

    /// <summary>The gate of a try region: "was an exception raised in the region?", the way into the handler.</summary>
    private void LiftGate(Block block, int region)
    {
        _b.CurrentAddr = block.Start;
        Node raised = _b.Raw(Op.Idiom, VT.I1);
        raised.Imm = (long)IdiomKind.TryEntry;
        raised.Aux = region;
        _b.Raw(Op.Branch, VT.None, raised);
    }

    /// <summary>
    /// Entering a landing pad: the exception in x0 (only handed to __cxa_begin_catch), the clause in x1, the
    /// scratch registers undefined, the callee-saved registers the region changes lost.
    /// </summary>
    private void LiftLanding(Block block, (int Region, long Selector, List<int> Lost) landing)
    {
        _b.CurrentAddr = block.Start;
        Clobber();
        SetVar(1, C(VT.I64, landing.Selector));
        foreach (int variable in landing.Lost)
        {
            Node lost = _b.Raw(Op.Idiom, VarTypes[variable]);
            lost.Imm = (long)IdiomKind.LostRegister;
            lost.Aux = variable;
            SetVar(variable, lost);
        }
        _b.Raw(Op.Jump, VT.None);
    }

    /// <summary>What a call leaves undefined: the scratch registers, the flags, the upper halves of v8-v15.</summary>
    private void Clobber()
    {
        for (int r = 0; r <= 18; r++) SetVar(r, _b.Undef(VT.I64));
        SetVar(30, _b.Undef(VT.I64));
        for (int v = 0; v < 32; v++)
        {
            if (v is < 8 or >= 16)
            {
                SetLane(v, 0, _b.Undef(VT.I32));
                SetLane(v, 1, _b.Undef(VT.I32));
            }
            SetLane(v, 2, _b.Undef(VT.I32));
            SetLane(v, 3, _b.Undef(VT.I32));
        }
        SetVar(VarFlags, _b.Undef(VT.Flags));
    }

    /// <summary>The runtime's own calls in a handler: they stand for the catch and are not calls of the program.</summary>
    private bool LiftUnwindCall(in A64Instruction i)
    {
        if (!IsUnwindCall(i) || (_block.Scope & 1) == 0 || _block.Scope < 0) return false;
        int region = _block.Scope >> 1;
        Clobber();
        if (i.Target == _beginCatch)
        {
            // The caught object: the wrapper, whose first field is the managed exception.
            Node wrapper = _b.Raw(Op.Idiom, VT.I64);
            wrapper.Imm = (long)IdiomKind.CaughtWrapper;
            wrapper.Aux = region;
            SetVar(0, wrapper);
        }
        else if (i.Target == _allocateException)
        {
            // The copy of the wrapper that "throw e" throws: memory of its own, like the frame slot MSVC uses.
            SetVar(0, _b.Add(Var(VarSp), C(VT.I64, -0x300000 - 0x1000L * region)));
        }
        return true;
    }
}
