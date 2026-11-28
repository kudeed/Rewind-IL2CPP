using Rewind.Analysis.Abi;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Runtime;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Passes;

/// <summary>
/// Expands a proved outlined cleanup before stack promotion. The frame loads remain real memory effects:
/// in particular, the pending exception is loaded after the managed call, even if the receiver aliases it.
/// A recognized body with an unproved caller remains an ordinary native call and keeps its diagnostic.
/// </summary>
public static class OutlinedCleanups
{
    public static bool Run(Function fn, ProgramAnalysis program)
    {
        if (fn.Regs.SharedPositions || program.Model.Image is not ElfImage ||
            !fn.Params.TryGetValue(fn.Regs.StackPointer, out Node? sp)) return false;
        var candidates = new List<(Node Call, OutlinedCleanup Cleanup)>();
        foreach (Block block in fn.Blocks)
            foreach (Node call in block.Nodes)
                if (!call.Dead && call.Op == Op.Call && call.Aux is CallInfo { Indirect: false, Intrinsic: null } info &&
                    program.OutlinedCleanupAt(info.Target) is { } cleanup) candidates.Add((call, cleanup));
        if (candidates.Count == 0) return false;

        UnrepresentedExceptionCleanups(fn, program, candidates.Select(c => c.Cleanup.Address).ToHashSet());

        // Discard only already-unused projections, not an observed result of the native call.
        DeadCode.Run(fn);
        bool changed = false;
        foreach (var (call, cleanup) in candidates)
        {
            if (call.Dead || call.Block == null || !fn.Blocks.Contains(call.Block)) continue;
            string? reason = null;
            Node? frame = IntegerInput(call, 0);
            if (call.Aux is not CallInfo { NoReturn: false } || call.Block.Terminator == null)
                reason = "unsupported call control flow";
            else if (HasObservedResult(fn, call)) reason = "native result is observed";
            else if (!ExceptionEdge(fn, program, call, out reason)) { }
            else if (frame == null || !FrameLifetime(fn, program, call, frame, sp, cleanup, out reason))
                reason ??= "cleanup frame argument is missing";
            if (reason != null)
            {
                fn.Problems.Add($"outlined cleanup at 0x{call.Addr:X} left native: {reason}");
                continue;
            }
            Expand(fn, call, frame!, cleanup);
            changed = true;
        }
        if (changed)
            for (int i = 0; i < fn.Blocks.Count; i++) fn.Blocks[i].Id = i;
        return changed;
    }

    private static Node? IntegerInput(Node call, int register)
    {
        if (call.Aux is not CallInfo info || info.Slots.Count != call.In.Length) return null;
        Node? value = null;
        for (int i = 0; i < info.Slots.Count; i++)
            if (info.Slots[i] == new ArgSlot(ArgSlotKind.IntReg, register))
            {
                if (value != null) return null;
                value = call.In[i];
            }
        return value;
    }

    private static bool HasObservedResult(Function fn, Node call)
    {
        foreach (Block block in fn.Blocks)
            foreach (Node node in block.Phis.Concat(block.Nodes))
                if (!node.Dead && node.In.Contains(call)) return true;
        return false;
    }

    private static void UnrepresentedExceptionCleanups(Function fn, ProgramAnalysis program, HashSet<ulong> targets)
    {
        if (program.Model.Image is not ElfImage image || image.ExceptionTableOf(fn.Address) is not { } table ||
            program.RangeOf(fn.Address) is not { } range) return;
        var represented = fn.Blocks.SelectMany(b => b.Nodes).Where(n => !n.Dead && n.Op is Op.Call or Op.TailCall)
            .Select(n => n.Addr).ToHashSet();
        var reported = new HashSet<ulong>();
        foreach (CallSite site in table.CallSites)
        {
            if (!site.CatchAll || site.LandingPad == 0 || site.Start < range.Start || site.End > range.End ||
                site.End <= site.Start || site.End - site.Start > 1024 || (site.Start & 3) != 0) continue;
            for (ulong at = site.Start; at + 4 <= site.End; at += 4)
            {
                if (!image.TrySpan(at, 4, out _)) break;
                A64Instruction i = A64Decoder.Decode(image.U32(at), at);
                if (i.Op == A64Op.Bl && targets.Contains(i.Target) && !represented.Contains(at) && reported.Add(at))
                    fn.Problems.Add($"outlined cleanup exception edge at 0x{at:X} is not represented by the lifter (catch-all landing pad 0x{site.LandingPad:X})");
            }
        }
    }

    private static bool StackOffset(Node n, Node sp, out int offset)
    {
        long sum = 0;
        int budget = 8;
        while (n.Op == Op.Add && n.In.Length == 2 && n.In[1].IsConst && budget-- > 0)
        {
            sum += IrBuilder.SImm(n.In[1]);
            n = n.In[0];
        }
        offset = (int)sum;
        return ReferenceEquals(n, sp) && sum is > -0x4000000 and < 0x4000000;
    }

    private static bool ExceptionEdge(Function fn, ProgramAnalysis program, Node call, out string? reason)
    {
        reason = "caller exception edge is not proved";
        if (program.Model.Image is not ElfImage image || call.Block == null || call.Addr > ulong.MaxValue - 4 ||
            program.RangeOf(fn.Address) is not { } range || call.Addr < range.Start || call.Addr + 4 > range.End ||
            fn.Problems.Any(p => p.StartsWith("exception handling not reconstructed:", StringComparison.Ordinal))) return false;
        // A missing LSDA record is not a record with LandingPad=0: a table gap may mean terminate.
        ItaniumExceptionTable? table = image.ExceptionTableOf(fn.Address);
        if (table == null) return false;
        List<CallSite> sites = table.CallSites.Where(s => s.Start < call.Addr + 4 && call.Addr < s.End).ToList();
        if (sites.Count != 1 || sites[0].Start > call.Addr || sites[0].End < call.Addr + 4) return false;
        CallSite site = sites[0];
        if (site.LandingPad == 0)
        {
            if (site.Action != 0 || site.CatchAll || !ValidScope(fn, call.Block.Scope, out int protectedBy) || protectedBy >= 0) return false;
            reason = null;
            return true;
        }
        if (!site.Catches || site.CatchAll || !ValidScope(fn, call.Block.Scope, out int region) || region < 0) return false;
        ulong pad = CanonicalPad(image, site.LandingPad);
        if (pad == 0 || CanonicalPad(image, fn.TryRegions[region].Funclet) != pad ||
            !fn.TryGates().Any(g => g.Region == region)) return false;
        reason = null;
        return true;
    }

    private static bool ValidScope(Function fn, int scope, out int protectedBy)
    {
        protectedBy = -1;
        var seen = new HashSet<int>();
        while (scope >= 0)
        {
            int region = scope >> 1;
            if (region >= fn.TryRegions.Count || !seen.Add(region)) return false;
            if (protectedBy < 0 && (scope & 1) == 0) protectedBy = region;
            scope = fn.TryRegions[region].Outer;
        }
        return scope == -1;
    }

    private static ulong CanonicalPad(NativeImage image, ulong address)
    {
        var seen = new HashSet<ulong>();
        for (int i = 0; i < 5; i++)
        {
            if (!seen.Add(address) || !image.IsCodeAddress(address) || !image.TrySpan(address, 4, out _)) return 0;
            A64Instruction instruction = A64Decoder.Decode(image.U32(address), address);
            if (instruction.Op != A64Op.B) return address;
            address = instruction.Target;
        }
        return 0;
    }

    private static bool FrameLifetime(Function fn, ProgramAnalysis program, Node call, Node frame, Node sp,
        OutlinedCleanup cleanup, out string? reason)
    {
        reason = "cleanup frame lifetime is not proved";
        if (frame.Type != VT.I64 || !StackOffset(frame, sp, out int offset) || offset > -OutlinedCleanup.FrameSize ||
            call.Block == null || !ReachingStores(call, sp, offset + 8, out List<Node> receiverStores) || receiverStores.Count != 1 ||
            !ReachingStores(call, sp, offset, out List<Node> exceptionStores)) return false;
        Node receiverStore = receiverStores[0];
        if (!StackOffset(receiverStore.In[1], sp, out int receiver) || receiver >= 0 ||
            (long)receiver + cleanup.ReceiverSize > 0 || receiverStore.Block == null) return false;
        if ((long)receiver < (long)offset + OutlinedCleanup.FrameSize && (long)offset < (long)receiver + cleanup.ReceiverSize) return false;
        var cfg = new Cfg(fn);
        if (!Dominates(cfg, receiverStore, call)) return false;

        // A paired full-width initialization starts this particular frame lifetime. Earlier uses of the
        // same stack bytes (a lock's flag, or another enumerator) do not supply either field's provenance.
        int storeAt = receiverStore.Block.Nodes.IndexOf(receiverStore);
        Node? zeroStore = null;
        for (int i = storeAt - 1; i >= 0; i--)
        {
            Node n = receiverStore.Block.Nodes[i];
            if (n.Dead || !n.IsEffect) continue;
            if (n.Op == Op.Store && n.In.Length == 2 && n.In[1].Type == VT.I64 && n.In[1].IsConstValue(0) &&
                n.Addr != 0 && n.Addr == receiverStore.Addr && StackOffset(n.In[0], sp, out int at) && at == offset) zeroStore = n;
            break;
        }
        if (zeroStore == null || !ReceiverInitialized(program, receiverStore, sp, receiver, cleanup.ReceiverType)) return false;
        foreach (Node store in exceptionStores)
        {
            if (ReferenceEquals(store, zeroStore)) continue;
            if (!Dominates(cfg, receiverStore, store) || !ManagedException(fn, store.In[1], [])) return false;
        }
        if (!LifetimeEffects(fn, program, call, receiverStore, sp, offset, cfg, out string? effectReason))
        {
            reason = effectReason;
            return false;
        }
        reason = null;
        return true;
    }

    private static bool Dominates(Cfg cfg, Node before, Node after) => before.Block != null && after.Block != null &&
        (ReferenceEquals(before.Block, after.Block)
            ? before.Block.Nodes.IndexOf(before) < after.Block.Nodes.IndexOf(after)
            : cfg.Dominates(before.Block, after.Block));

    /// <summary>Nearest full-width explicit definitions on every path; loops do not import a former lifetime.</summary>
    private static bool ReachingStores(Node before, Node sp, int offset, out List<Node> stores)
    {
        stores = [];
        if (before.Block == null) return false;
        var pending = new Stack<(Block Block, int End)>();
        pending.Push((before.Block, before.Block.Nodes.IndexOf(before)));
        var visited = new HashSet<(Block, int)>();
        int budget = 8192;
        while (pending.Count != 0)
        {
            var item = pending.Pop();
            if (!visited.Add(item)) continue;
            bool found = false;
            for (int i = item.End - 1; i >= 0; i--)
            {
                if (--budget == 0) return false;
                Node n = item.Block.Nodes[i];
                if (n.Dead || n.Op != Op.Store || n.In.Length != 2 || !StackOffset(n.In[0], sp, out int at)) continue;
                int width = n.In[1].Type.Bytes();
                if ((long)at >= (long)offset + 8 || (long)offset >= (long)at + width) continue;
                if (at != offset || width != 8 || n.In[1].Type != VT.I64) return false;
                if (!stores.Contains(n)) stores.Add(n);
                found = true;
                break;
            }
            if (found) continue;
            if (item.Block.Preds.Count == 0) return false;
            foreach (Block predecessor in item.Block.Preds) pending.Push((predecessor, predecessor.Nodes.Count));
        }
        return stores.Count != 0;
    }

    private static bool ManagedException(Function fn, Node node, HashSet<Node> seen)
    {
        if (node.Type != VT.I64 || !seen.Add(node)) return false;
        if (node.IsConstValue(0)) return true;
        if (node.Op == Op.Load && node.In.Length == 1 && node.In[0] is { Op: Op.Idiom, Aux: int region } wrapper &&
            wrapper.Imm == (long)IdiomKind.CaughtWrapper && region >= 0 && region < fn.TryRegions.Count) return true;
        return node.Op == Op.Phi && node.In.Length != 0 && node.In.All(n => ManagedException(fn, n, new HashSet<Node>(seen)));
    }

    private static bool LifetimeEffects(Function fn, ProgramAnalysis program, Node call, Node lifetime,
        Node sp, int frame, Cfg cfg, out string? reason)
    {
        reason = "cleanup frame effects are not proved";
        var work = new Stack<(Block Block, int End)>();
        work.Push((call.Block!, call.Block!.Nodes.IndexOf(call)));
        var seen = new HashSet<(Block, int)>();
        var handlers = new HashSet<int>();
        int budget = 16384;
        while (work.Count != 0)
        {
            var item = work.Pop();
            if (!seen.Add(item)) continue;
            if (!cfg.Dominates(lifetime.Block!, item.Block)) return false;
            if (item.Block.Phis.Any(p => !p.Dead && p.In.Any(n => CarriesStackAddress(n, sp, []))))
            {
                reason = "cleanup frame address escapes through a merge";
                return false;
            }
            // A synthetic try gate enters a handler without walking the throwing path. Its memory effects
            // must nevertheless count: include the protected blocks, not just the handler's CFG predecessors.
            for (int scope = item.Block.Scope, guard = 0; scope >= 0 && guard++ < fn.TryRegions.Count;)
            {
                int region = scope >> 1;
                if (region >= fn.TryRegions.Count) return false;
                if ((scope & 1) != 0 && handlers.Add(region))
                    foreach (Block protectedBlock in fn.Blocks)
                        if (fn.IsProtectedBy(protectedBlock, region)) work.Push((protectedBlock, protectedBlock.Nodes.Count));
                scope = fn.TryRegions[region].Outer;
            }
            bool reached = false;
            for (int i = item.End - 1; i >= 0; i--)
            {
                if (--budget == 0) return false;
                Node n = item.Block.Nodes[i];
                if (ReferenceEquals(n, lifetime)) { reached = true; break; }
                if (n.Dead) continue;
                bool frameValue = n.In.Any(v => CarriesStackAddress(v, sp, []));
                if (n.Op == Op.Store)
                {
                    if (CarriesStackAddress(n.In[1], sp, []))
                    {
                        reason = $"cleanup frame address escapes through store at 0x{n.Addr:X}";
                        return false;
                    }
                    if (StackOffset(n.In[0], sp, out int at))
                    {
                        int width = n.In[1].Type.Bytes();
                        if ((long)at < (long)frame + OutlinedCleanup.FrameSize && (long)frame < (long)at + width &&
                            !(at == frame && width == 8 && ManagedException(fn, n.In[1], [])))
                        {
                            reason = $"cleanup frame is changed at 0x{n.Addr:X}";
                            return false;
                        }
                    }
                    else
                    {
                        reason = $"store at 0x{n.Addr:X} may alias the cleanup frame";
                        return false;
                    }
                }
                else if (n.Op is Op.Call or Op.TailCall)
                {
                    if (!CallDisjointFromFrame(n, program, sp, frame))
                    {
                        reason = $"call at 0x{n.Addr:X} has unproved effects on the cleanup frame";
                        return false;
                    }
                }
                else if (frameValue && n.Op is not (Op.Add or Op.Load))
                {
                    reason = $"cleanup frame address has an unsupported use at 0x{n.Addr:X}";
                    return false;
                }
            }
            if (reached) continue;
            if (item.Block.Preds.Count == 0) return false;
            foreach (Block predecessor in item.Block.Preds) work.Push((predecessor, predecessor.Nodes.Count));
        }
        reason = null;
        return true;
    }

    private static bool CarriesStackAddress(Node value, Node sp, HashSet<Node> seen)
    {
        if (seen.Count > 128) return true;
        if (!seen.Add(value)) return false;
        if (StackOffset(value, sp, out _)) return true;
        if (value.Op == Op.Load)
        {
            // An address parked in another local is still an escape; merely loading it does not erase its
            // provenance. Heap loads cannot acquire this private frame without an earlier rejected escape.
            if (StackOffset(value.In[0], sp, out int at) && ReachingStores(value, sp, at, out var stores))
                return stores.Any(s => CarriesStackAddress(s.In[1], sp, new HashSet<Node>(seen)));
            return false;
        }
        if (value.Op == Op.Proj) return false; // A call handed this frame is rejected at that call, before its result matters.
        return value.Op is not (Op.Param or Op.Const or Op.SlotValue or Op.Idiom) &&
            value.In.Any(n => CarriesStackAddress(n, sp, new HashSet<Node>(seen)));
    }

    private static bool CallDisjointFromFrame(Node call, ProgramAnalysis program, Node sp, int frame)
    {
        if (call.Aux is not CallInfo { Indirect: false, Intrinsic: null } info || info.Slots.Count != call.In.Length) return false;
        HelperInfo? helper = program.Helpers.At(info.Target);
        MethodAbi? abi = BoundAbi(program, call);
        if (helper == null && abi == null) return false;
        for (int i = 0; i < call.In.Length; i++)
        {
            if (!StackOffset(call.In[i], sp, out int at))
            {
                if (CarriesStackAddress(call.In[i], sp, [])) return false;
                continue;
            }
            if (abi == null || info.Slots[i].Kind != ArgSlotKind.IntReg) return false;
            AbiParam? p = abi.Params.FirstOrDefault(p => p.Position == info.Slots[i].Index);
            int SizeOf(TypeSig type)
            {
                var layout = program.Layouts.SizeOf(type);
                return layout.Known ? layout.Size : -1;
            }
            int size = p?.Role == ParamRole.ReturnBuffer ? abi.ReturnSize
                : p?.Role == ParamRole.This && p.Type?.Definition is { IsValueType: true } ? SizeOf(p.Type)
                : p?.Type is ByRefSig byRef ? SizeOf(byRef.ElementType)
                : p?.Pass == PassKind.Indirect ? p.Size : -1;
            if (size <= 0 || (long)at < (long)frame + OutlinedCleanup.FrameSize && (long)frame < (long)at + size) return false;
        }
        return true;
    }

    private static MethodAbi? BoundAbi(ProgramAnalysis program, Node call)
    {
        if (call.Aux is not CallInfo { Indirect: false, Intrinsic: null } info) return null;
        var candidates = new List<(MethodDef Method, MethodInst? Instance)>();
        if (program.Model.MethodsByAddress.TryGetValue(info.Target, out var methods)) candidates.AddRange(methods.Select(m => (m, (MethodInst?)null)));
        if (program.Model.InstsByAddress.TryGetValue(info.Target, out var instances)) candidates.AddRange(instances.Select(i => (i.Method, (MethodInst?)i)));
        MethodAbi? found = null;
        foreach (var (method, instance) in candidates)
        {
            MethodAbi abi = instance == null ? program.Abi.For(method, [], []) : program.Abi.For(instance);
            AbiParam? descriptor = abi.Params.FirstOrDefault(p => p.Role == ParamRole.MethodInfo);
            MetadataUsage? usage = descriptor != null && IntegerInput(call, descriptor.Position) is { } input ? MethodUsage(program, input) : null;
            if (usage is { Kind: UsageKind.MethodRef, MethodInst: { } named } && ReferenceEquals(named.Method, method))
            {
                abi = program.Abi.For(named);
                if (abi.Known && OutlinedCleanup.HasCompatibleBody(program, info.Target, named)) return abi;
                return null;
            }
            if (method.DeclaringType.GenericParameters.Length != 0 || method.GenericParameters.Length != 0 || !abi.Known) continue;
            if (found != null) return null;
            found = abi;
        }
        return found;
    }

    private static MetadataUsage? MethodUsage(ProgramAnalysis program, Node input) => input.Op == Op.SlotValue
        ? program.Model.ResolveUsageSlot((ulong)input.Imm)
        : input.Op == Op.Load && input.In.Length == 1 && input.In[0].IsConst
            ? program.Model.ResolveUsageSlot(input.In[0].UImm) : null;

    /// <summary>
    /// The receiver was completely returned into this local before the frame was initialized. An initializer
    /// throwing cannot enter this lifetime. Only the immediately preceding call, through straight-line
    /// predecessors, is considered; a same-address object from an earlier loop is not an initializer.
    /// </summary>
    private static bool ReceiverInitialized(ProgramAnalysis program, Node frameStore, Node sp, int receiver, TypeSig type)
    {
        Block block = frameStore.Block!;
        int end = block.Nodes.IndexOf(frameStore);
        var visited = new HashSet<Block>();
        var between = new List<Node>();
        for (int budget = 0; budget < 16 && visited.Add(block); budget++)
        {
            for (int i = end - 1; i >= 0; i--)
            {
                Node n = block.Nodes[i];
                if (n.Dead) continue;
                if (n.Op == Op.Call)
                {
                    between.Reverse();
                    return InitializedOrCopied(program, n, between, sp, receiver, type);
                }
                between.Add(n);
            }
            if (block.Preds.Count != 1) return false;
            Block previous = block.Preds[0];
            // Never walk from a catch entry across the synthetic exception edge to its protected initializer.
            if (previous.Terminator is { Op: Op.Branch } branch && branch.In.Length == 1 &&
                Function.IsTryEntry(branch.In[0]) && ReferenceEquals(previous.Succs[0], block)) return false;
            block = previous;
            end = block.Nodes.Count;
        }
        return false;
    }

    private static bool InitializedOrCopied(ProgramAnalysis program, Node initializer, List<Node> after,
        Node sp, int receiver, TypeSig type)
    {
        int size = program.Layouts.SizeOf(type).Size;
        if (size <= 0 || size > 256) return false;
        if (after.Any(n => n.Op == Op.Store && !StackOffset(n.In[0], sp, out _))) return false;
        var writes = after.Where(n => n.Op == Op.Store && StackOffset(n.In[0], sp, out int at) &&
            (long)at < (long)receiver + size && (long)receiver < (long)at + n.In[1].Type.Bytes()).ToList();
        if (writes.Count == 0) return Initializes(program, initializer, sp, receiver, type);

        // A bounded, complete value copy from an sret temporary is also a completed initialization.
        // Each source byte must be read after sret and before any intervening write to it. This permits
        // reusing the temporary for the cleanup frame only after its complete value has been copied out.
        int? temporary = null;
        var covered = new bool[size];
        foreach (Node store in writes)
        {
            if (!StackOffset(store.In[0], sp, out int destination) || store.In[1] is not { Op: Op.Load, In.Length: 1 } load ||
                !StackOffset(load.In[0], sp, out int source) || !load.Type.IsInt()) return false;
            int width = load.Type.Bytes(), relative = destination - receiver;
            if (width is not (1 or 2 or 4 or 8) || relative < 0 || relative + width > size) return false;
            temporary ??= source - relative;
            if (source - relative != temporary.Value) return false;
            for (int k = relative; k < relative + width; k++)
                if (covered[k]) return false; else covered[k] = true;
            int readAt = after.IndexOf(load), writeAt = after.IndexOf(store);
            if (readAt < 0 || readAt >= writeAt) return false;
            for (int k = 0; k < readAt; k++)
            {
                Node prior = after[k];
                if (prior.Op != Op.Store) continue;
                if (!StackOffset(prior.In[0], sp, out int to) ||
                    (long)to < (long)source + width && (long)source < (long)to + prior.In[1].Type.Bytes()) return false;
            }
        }
        return covered.All(b => b) && temporary is { } buffer && Initializes(program, initializer, sp, buffer, type);
    }

    private static bool Initializes(ProgramAnalysis program, Node call, Node sp, int receiver, TypeSig type)
    {
        if (call.Aux is not CallInfo { Indirect: false, Intrinsic: null, NoReturn: false } info ||
            IntegerInput(call, 8) is not { } buffer || !StackOffset(buffer, sp, out int at) || at != receiver) return false;
        IEnumerable<(MethodDef Method, MethodInst? Instance)> candidates = [];
        if (program.Model.MethodsByAddress.TryGetValue(info.Target, out var methods))
            candidates = candidates.Concat(methods.Select(m => (m, (MethodInst?)null)));
        if (program.Model.InstsByAddress.TryGetValue(info.Target, out var instances))
            candidates = candidates.Concat(instances.Select(i => (i.Method, (MethodInst?)i)));
        foreach (var (method, instance) in candidates)
        {
            MethodAbi abi = instance == null ? program.Abi.For(method, [], []) : program.Abi.For(instance);
            AbiParam? descriptor = abi.Params.FirstOrDefault(p => p.Role == ParamRole.MethodInfo);
            if (descriptor == null || descriptor.Position is < 0 or > 7 || IntegerInput(call, descriptor.Position) is not { } input) continue;
            MetadataUsage? usage = input.Op == Op.SlotValue ? program.Model.ResolveUsageSlot((ulong)input.Imm)
                : input.Op == Op.Load && input.In.Length == 1 && input.In[0].IsConst
                    ? program.Model.ResolveUsageSlot(input.In[0].UImm) : null;
            if (usage is { Kind: UsageKind.MethodRef, MethodInst: { } specific } && ReferenceEquals(specific.Method, method))
            {
                if (!OutlinedCleanup.HasCompatibleBody(program, info.Target, specific)) continue;
                abi = program.Abi.For(specific);
            }
            else if (method.DeclaringType.GenericParameters.Length != 0 || method.GenericParameters.Length != 0) continue;
            if (abi.Known && abi.Return == ReturnKind.Buffer && abi.ReturnBuffer is { Position: 8 } &&
                abi.ReturnType.Key == type.Key && !abi.ReturnType.ContainsGenericParameter) return true;
        }
        return false;
    }

    private static void Expand(Function fn, Node call, Node frame, OutlinedCleanup cleanup)
    {
        Block block = call.Block!;
        int at = block.Nodes.IndexOf(call);
        var onward = new Block { Start = call.Addr + 4, End = block.End, Scope = block.Scope };
        var throwing = new Block { Start = call.Addr, End = call.Addr + 4, Scope = block.Scope };
        onward.Nodes.AddRange(block.Nodes.Skip(at + 1));
        foreach (Node n in onward.Nodes) n.Block = onward;
        block.Nodes.RemoveRange(at, block.Nodes.Count - at);
        onward.Succs.AddRange(block.Succs);
        foreach (Block successor in onward.Succs)
            for (int i = 0; i < successor.Preds.Count; i++)
                if (ReferenceEquals(successor.Preds[i], block)) successor.Preds[i] = onward;
        block.Succs.Clear();
        block.Succs.AddRange([throwing, onward]);
        throwing.Preds.Add(block);
        onward.Preds.Add(block);
        block.End = call.Addr + 4;
        fn.Blocks.AddRange([throwing, onward]);

        var b = new IrBuilder(fn) { Current = block, CurrentAddr = call.Addr };
        Node receiver = b.Load(b.Add(frame, b.Const(VT.I64, 8)), VT.I64);
        Node descriptor = fn.NewNode(Op.SlotValue, VT.I64, null);
        descriptor.Imm = (long)cleanup.MethodInfoSlot;
        call.In = [receiver, descriptor];
        call.Aux = new CallInfo
        {
            Target = cleanup.CleanupTarget,
            Slots = [new ArgSlot(ArgSlotKind.IntReg, 0), new ArgSlot(ArgSlotKind.IntReg, 1)],
        };
        block.Nodes.Add(call);
        Node pending = b.Load(frame, VT.I64);
        b.Raw(Op.Branch, VT.None, b.Cmp(Op.CmpNe, pending, b.Const(VT.I64, 0)));
        b.Current = throwing;
        Node rethrow = b.Raw(Op.Call, VT.None, pending);
        rethrow.Aux = new CallInfo
        {
            Target = cleanup.RethrowTarget, NoReturn = true,
            Slots = [new ArgSlot(ArgSlotKind.IntReg, 0)],
        };
        b.Raw(Op.Unreachable, VT.None);
    }
}
