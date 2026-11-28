using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Passes;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Block operations: memcpy and memset of a known number of bytes. IL has no such thing for managed data; what
/// the compiler turned into one was the assignment of a struct ("a = b", "a = default"), or of several adjacent
/// fields at once. Read back as that, the bytes never have to be named.
/// </summary>
public sealed partial class HirBuilder
{
    /// <summary>True when <paramref name="bytes"/> is exactly one value of the struct type.</summary>
    private bool CopiesWhole(TypeSig? type, int bytes)
    {
        if (type == null || !IsStructType(type) || Open(type)) return false;
        var (size, _, known) = _p.Layouts.SizeOf(type);
        return known && size == bytes;
    }

    /// <summary>
    /// How many bytes can be reached through the address of stack offset <paramref name="offset"/> once it is
    /// kept in a value: the object that starts there, when its type is known (a struct local, a value boxed in
    /// place). -1 when it is not.
    /// </summary>
    public int ReachThrough(int offset)
    {
        if (_fakeBoxes.TryGetValue(offset, out TypeSig? boxed)) return _header + Math.Max(1, _p.Layouts.SizeOf(boxed).Size);
        if (_frameTypes.TryGetValue(offset, out TypeSig? type) && !Open(type))
        {
            var (size, _, known) = _p.Layouts.SizeOf(type);
            if (known) return Math.Max(1, size);
        }
        return -1;
    }

    /// <summary>The start of the typed stack object that covers <paramref name="offset"/>, if any.</summary>
    private int? FrameObjectAt(int offset)
    {
        foreach (var (start, type) in _frameTypes)
            if (offset >= start && offset < start + Math.Max(1, _p.Layouts.SizeOf(type).Size))
                return start;
        return null;
    }

    /// <summary>
    /// A struct copied from one stack object to another: both are that struct. Known before translation, from
    /// the addresses alone, so the type of a temporary follows the chain of copies it is part of.
    /// </summary>
    private void SpreadFrameTypes()
    {
        List<(int To, int From, int Size)>? copies = null;
        // Copies made piece by piece (a struct moved eight bytes at a time): source offset and size of each
        // piece, grouped by how far apart source and destination are.
        Dictionary<int, List<(int From, int Size)>>? pieces = null;
        foreach (Block b in _fn.Blocks)
            foreach (Node n in b.Nodes)
            {
                if (n.Dead) continue;
                if (n.Op == Op.Call && BlockCopies.Of(n, _p.Helpers) is { IsCopy: true } op && op.Bytes > 0 &&
                    IsFrameAddress(op.Destination, out int to) && IsFrameAddress(op.Operand, out int from))
                    (copies ??= []).Add((to, from, op.Bytes));
                else if (n.Op == Op.Store && n.In[1] is { Op: Op.Load, Dead: false } load && IsFrameAddress(n.In[0], out int target) &&
                         IsFrameAddress(load.In[0], out int source) && target != source)
                {
                    pieces ??= [];
                    if (!pieces.TryGetValue(target - source, out List<(int, int)>? list)) pieces[target - source] = list = [];
                    list.Add((source, load.Type.Bytes()));
                }
            }
        // Runs of pieces that follow each other without a gap are one copy of that many bytes.
        if (pieces != null)
            foreach (var (delta, list) in pieces)
            {
                list.Sort();
                int start = list[0].From, end = start + list[0].Size;
                foreach (var (from, size) in list.Skip(1))
                {
                    if (from <= end)
                    {
                        end = Math.Max(end, from + size);
                        continue;
                    }
                    if (end - start > 8) (copies ??= []).Add((start + delta, start, end - start));
                    start = from;
                    end = from + size;
                }
                if (end - start > 8) (copies ??= []).Add((start + delta, start, end - start));
            }
        if (copies == null) return;

        // The struct at [offset, offset + size) of a typed stack object: the object itself, or the field of it
        // that is exactly those bytes.
        TypeSig? StructAt(int offset, int size)
        {
            if (FrameObjectAt(offset) is not int start) return null;
            TypeSig type = _frameTypes[start];
            int inner = offset - start;
            for (int depth = 0; depth < 8 && IsStructType(type) && !Open(type); depth++)
            {
                var (whole, _, known) = _p.Layouts.SizeOf(type);
                if (!known) return null;
                if (inner == 0 && whole == size) return type;
                if (_p.Layouts.FieldAt(type, inner) is not { } slot || inner + size > slot.Offset + slot.Size) return null;
                inner -= slot.Offset;
                type = slot.Type;
            }
            return null;
        }

        bool changed = true;
        for (int round = 0; changed && round < 8; round++)
        {
            changed = false;
            foreach (var (to, from, size) in copies)
            {
                // A memcpy can cover only a prefix of a larger job struct. Propagate
                // the complete copied fields, never the uninitialised rest of that owner.
                if (SpreadCopiedFrameFields(to, from, size) || SpreadCopiedFrameFields(from, to, size)) changed = true;
                bool knownTo = FrameObjectAt(to) != null, knownFrom = FrameObjectAt(from) != null;
                if (knownTo == knownFrom) continue;
                if (StructAt(knownTo ? to : from, size) is not { } type) continue;
                _frameTypes[knownTo ? from : to] = type;
                changed = true;
            }
        }
    }

    private bool SpreadCopiedFrameFields(int typed, int temporary, int size)
    {
        if (size <= 0 || (long)typed < (long)temporary + size && (long)temporary < (long)typed + size ||
            FrameObjectAt(typed) is not int ownerStart) return false;
        TypeSig owner = _frameTypes[ownerStart];
        if (!IsStructType(owner) || Open(owner)) return false;
        FieldSlot[]? fields = WholePublicFieldRange(_p.Layouts.Of(owner), typed - ownerStart, size);
        if (fields == null) return false;
        var planned = new List<(int Start, TypeSig Type)>();
        var replaced = new HashSet<int>();
        foreach (FieldSlot field in fields)
        {
            long begin = (long)temporary + field.Offset - (typed - ownerStart);
            if (begin < int.MinValue || begin + field.Size > int.MaxValue || field.Size <= 0) return false;
            int at = (int)begin;
            foreach (var (existingAt, existingType) in _frameTypes)
            {
                var existingSize = _p.Layouts.SizeOf(existingType);
                if (!existingSize.Known || existingSize.Size <= 0) return false;
                if ((long)existingAt >= begin + field.Size || begin >= (long)existingAt + existingSize.Size) continue;
                // An existing pointer/int may be an exact member of NativeArray<T>.
                // Preserve contradictory or crossing views for lifetime splitting.
                if (existingAt < at || (long)existingAt + existingSize.Size > begin + field.Size ||
                    !SameFrameFieldView(field.Type, existingAt - at, existingType, existingSize.Size)) return false;
                replaced.Add(existingAt);
            }
            planned.Add((at, field.Type));
        }
        if (planned.All(p => _frameTypes.TryGetValue(p.Start, out TypeSig? held) && held.Key == p.Type.Key)) return false;
        foreach (int at in replaced) _frameTypes.Remove(at);
        foreach (var (at, type) in planned) _frameTypes[at] = type;
        return true;
    }

    private bool SameFrameFieldView(TypeSig owner, int offset, TypeSig view, int size)
    {
        for (int depth = 0; depth < 8; depth++)
        {
            if (offset == 0 && owner.Key == view.Key && _p.Layouts.SizeOf(owner) is { Known: true, Size: var whole } && whole == size) return true;
            if (!IsStructType(owner) || Open(owner) || _p.Layouts.FieldAt(owner, offset) is not { } field ||
                offset < field.Offset || (long)offset + size > (long)field.Offset + field.Size) return false;
            offset -= field.Offset;
            owner = field.Type;
        }
        return false;
    }

    /// <summary>
    /// The place a block operation of <paramref name="size"/> bytes works on. Null for stack memory of no known
    /// type - unless <paramref name="expected"/> says what it holds: the stack object then gets that type.
    /// </summary>
    private Place? BlockPlace(Node address, int size, TypeSig? expected)
    {
        if (Eval(address) is SFrame f && FrameObjectAt(f.Offset) == null)
        {
            if (expected == null) return null;
            LocationOf(address, expected);
        }
        return ResolvePlace(address, size);
    }

    /// <summary>The struct a run of bytes lies in, when the place is such a run.</summary>
    private static (HExpr Owner, TypeSig Type, int Offset)? RunOf(Place? place) => place switch
    {
        PParts { Owner: { } owner, OwnerType: { } type } parts => (owner, type, parts.Offset),
        PChunk chunk => (chunk.Owner, chunk.OwnerType, chunk.Offset),
        _ => null,
    };

    /// <summary>
    /// The fields of <paramref name="type"/> that make up [offset, offset + size): whole fields, taken as large
    /// as possible (a struct field that lies inside the range is one field, not its parts). Fails when the range
    /// cuts a scalar or covers fields that overlap.
    /// </summary>
    private bool FieldsIn(HExpr owner, TypeSig type, int offset, int size, List<HExpr> output, int depth = 0)
    {
        if (depth > 8) return false;
        TypeLayout layout = _p.Layouts.Of(type);
        if (!layout.Known) return false;
        int previousEnd = int.MinValue;
        foreach (FieldSlot slot in layout.Fields.OrderBy(s => s.Offset))
        {
            int start = Math.Max(offset, slot.Offset), end = Math.Min(offset + size, slot.Offset + slot.Size);
            if (start >= end) continue;
            if (slot.Offset < previousEnd) return false; // a union
            previousEnd = slot.Offset + slot.Size;
            var field = new HField { Object = owner, Field = slot.Field, DeclaringType = type, Type = slot.Type };
            if (start == slot.Offset && end == slot.Offset + slot.Size) output.Add(field);
            else if (!IsStructType(slot.Type) || !FieldsIn(field, slot.Type, start - slot.Offset, end - start, output, depth + 1)) return false;
        }
        return output.Count != 0;
    }

    private HExpr DefaultOf(TypeSig type) =>
        IsReference(type) ? new HConst(null, type) : new HTypeExpr(HTypeOp.Default, type, null) { Type = type };

    private void NoteFrameMisfit(Node address)
    {
        if (Eval(address) is SFrame f) FrameConflicts.Add(FrameObjectAt(f.Offset) ?? f.Offset);
    }

    /// <summary>
    /// Translates a memcpy or memset of constant size into assignments. False (with nothing emitted) when the
    /// bytes are not a struct or a run of whole fields, or the two sides of a copy are not the same thing.
    /// </summary>
    private bool TryEmitBlockOp(Node call)
    {
        if (BlockCopies.Of(call, _p.Helpers, tail: true) is not { } op || op.Bytes < 0) return false;
        if (ZeroesStackBuffer(op)) return true; // (stackalloc memory starts zeroed)
        int size = op.Bytes;
        if (!op.IsCopy)
        {
            if (!op.Operand.IsConst || op.Operand.UImm != 0) return false;
            return TryEmitFill(op.Destination, size, call.Addr, quiet: false);
        }

        return TryEmitCopy(op.Destination, op.Operand, size, call.Addr, quiet: false);
    }

    /// <summary>
    /// <paramref name="size"/> bytes at an address set to zero, as assignments of default values. False (with
    /// nothing emitted, and - when quiet - nothing noted) when the bytes are not a struct or a run of whole fields.
    /// </summary>
    private bool TryEmitFill(Node toAddress, int size, ulong address, bool quiet)
    {
        Place? target = BlockPlace(toAddress, size, null);
        if (target == null)
        {
            if (quiet) return false;
            // Often the zeroing of a local the program never uses afterwards: splitting the stack object by
            // lifetime shows that (and removes the fill).
            _h.Notes.Add($"fill of {size} bytes of stack memory of unknown type");
            NoteFrameMisfit(toAddress);
            return false;
        }
        if (target is PLocation whole && whole.Type is { } wholeType && _p.Layouts.SizeOf(wholeType).Size == size)
        {
            Emit(new HAssign(whole.Location, DefaultOf(wholeType)), address);
            return true;
        }
        var fields = new List<HExpr>();
        if (RunOf(target) is { } run && FieldsIn(run.Owner, run.Type, run.Offset, size, fields))
        {
            foreach (HExpr field in fields) Emit(new HAssign(field, DefaultOf(field.Type!)), address);
            return true;
        }
        if (quiet) return false;
        _h.Notes.Add($"fill of {size} bytes does not line up with fields ({Describe(target)})");
        NoteFrameMisfit(toAddress);
        return false;
    }

    /// <summary>
    /// A copy of <paramref name="size"/> bytes from one address to another, as assignments. False (with nothing
    /// emitted, and - when quiet - nothing noted) when the two sides are not the same thing.
    /// </summary>
    private bool TryEmitCopy(Node toAddress, Node fromAddress, int size, ulong address, bool quiet)
    {
        if (TryEmitLeadingPaddingCopy(toAddress, fromAddress, size, address)) return true;
        if (TryEmitPartialFrameCopy(toAddress, fromAddress, size, address)) return true;
        Place? to = BlockPlace(toAddress, size, null), from = BlockPlace(fromAddress, size, null);
        if (to == null && from is PLocation { Type: var known } && CopiesWhole(known, size)) to = BlockPlace(toAddress, size, known);
        else if (from == null && to is PLocation { Type: var known2 } && CopiesWhole(known2, size)) from = BlockPlace(fromAddress, size, known2);
        if (to == null || from == null)
        {
            if (!quiet) _h.Notes.Add($"copy of {size} bytes of stack memory of unknown type ({Describe(to)} from {Describe(from)})");
            return false;
        }
        if (to is PLocation d && from is PLocation s && _p.Layouts.SizeOf(d.Type).Size == size && _p.Layouts.SizeOf(s.Type).Size == size)
        {
            // The same bytes may be a struct or the single field that fills it; either side can name either.
            foreach (PLocation target in Views(d))
                foreach (PLocation source in Views(s))
                    if (target.Type.Key == source.Type.Key)
                    {
                        Emit(new HAssign(target.Location, source.Location), address);
                        return true;
                    }
        }
        if (RunOf(to) is { } toRun && RunOf(from) is { } fromRun && toRun.Type.Key == fromRun.Type.Key && toRun.Offset == fromRun.Offset)
        {
            var targets = new List<HExpr>();
            var sources = new List<HExpr>();
            if (FieldsIn(toRun.Owner, toRun.Type, toRun.Offset, size, targets) && FieldsIn(fromRun.Owner, fromRun.Type, fromRun.Offset, size, sources) &&
                targets.Count == sources.Count)
            {
                for (int i = 0; i < targets.Count; i++) Emit(new HAssign(targets[i], sources[i]), address);
                return true;
            }
            if (to is PChunk toChunk && from is PChunk fromChunk && toChunk.Size == fromChunk.Size)
            {
                CopyChunk(toChunk, new SChunk(SnapshotOf(fromChunk.Owner, fromChunk.OwnerType, address), fromChunk.OwnerType, fromChunk.Offset, fromChunk.Size), address);
                return true;
            }
        }
        if (quiet) return false;
        _h.Notes.Add($"copy of {size} bytes between different things ({Describe(to)} from {Describe(from)})");
        if (IsFrameAddress(toAddress, out int copyTo) && IsFrameAddress(fromAddress, out int copyFrom))
        {
            string LayoutAt(int start) => string.Join("; ", _frameTypes.Where(p =>
                (long)p.Key < (long)start + size && (long)start < (long)p.Key + Math.Max(1, _p.Layouts.SizeOf(p.Value).Size))
                .OrderBy(p => p.Key).Select(p => $"{p.Key}:{p.Value.DisplayName}/{_p.Layouts.SizeOf(p.Value).Size}"));
            _h.Notes.Add($"rejected frame copy at 0x{address:X}: {size} bytes, destination {copyTo} [{LayoutAt(copyTo)}], source {copyFrom} [{LayoutAt(copyFrom)}]");
        }
        NoteFrameMisfit(toAddress);
        NoteFrameMisfit(fromAddress);
        return false;
    }

    // ---- structs copied piece by piece ---------------------------------------------------------------------------

    private static readonly bool NoPieceCopies = Environment.GetEnvironmentVariable("REWIND_NO_PIECE_COPIES") != null;

    /// <summary>
    /// A run of bytes moved from one place to another by straight-line loads and stores (a struct assigned
    /// sixteen bytes at a time, say): the addresses of its first byte on both sides, its size, and the loads
    /// and stores that make it up, in the order they stand.
    /// </summary>
    private sealed class PieceCopy
    {
        public required Node To, From;
        public required int Size;
        public required List<Node> Members;
        public required ulong Address;
    }

    /// <summary>By the store that completes it.</summary>
    private readonly Dictionary<Node, PieceCopy> _pieceCopies = [];
    private readonly HashSet<Node> _pieceMembers = [];

    private static (Node Base, long Offset) SplitAddress(Node n)
    {
        long k = 0;
        while (n.Op == Op.Add && n.In[1].IsConst)
        {
            k += IrBuilder.SImm(n.In[1]);
            n = n.In[0];
        }
        return (n, k);
    }

    /// <summary>
    /// Finds the copies made piece by piece. The pieces of a struct's assignment cut across its fields (eight
    /// bytes hold an int and half of what follows), so one by one they are loads and stores of nothing that has
    /// a name; together they are "a = b". They are taken together where nothing else that could matter happens
    /// between the first load and the last store: then the whole copy can stand where the last store does.
    /// </summary>
    private void FindPieceCopies()
    {
        if (NoPieceCopies) return;
        foreach (Block b in _fn.Blocks)
        {
            Dictionary<(Node To, Node From, long Apart), List<(long From, int Size, Node Load, Node Store)>>? groups = null;
            foreach (Node n in b.Nodes)
            {
                if (n.Dead || n.Op != Op.Store || n.In[1] is not { Op: Op.Load, Dead: false } load || !ReferenceEquals(load.Block, b)) continue;
                if (_spillStores.Contains(n) || _caughtStores.Contains(n) || _pieceMembers.Contains(n)) continue;
                if (!_uses.TryGetValue(load, out List<Node>? users) || users.Count != 1 || !_position.ContainsKey(load)) continue;
                int size = load.Type.Bytes();
                if (size <= 0) continue;
                var (toBase, toOffset) = SplitAddress(n.In[0]);
                var (fromBase, fromOffset) = SplitAddress(load.In[0]);
                groups ??= [];
                var key = (toBase, fromBase, toOffset - fromOffset);
                if (!groups.TryGetValue(key, out var list)) groups[key] = list = [];
                list.Add((fromOffset, size, load, n));
            }
            if (groups == null) continue;
            foreach (var ((toBase, fromBase, apart), list) in groups)
            {
                if (list.Count < 2) continue;
                list.Sort((x, y) => x.From.CompareTo(y.From));
                for (int i = 0; i < list.Count;)
                {
                    long start = list[i].From, end = start + list[i].Size;
                    int j = i + 1;
                    while (j < list.Count && list[j].From <= end)
                    {
                        end = Math.Max(end, list[j].From + list[j].Size);
                        j++;
                    }
                    if (end - start >= 16 && j - i >= 2) ConsiderPieces(b, list.GetRange(i, j - i), toBase, fromBase, apart, start, end);
                    i = j;
                }
            }
        }
    }

    private void ConsiderPieces(Block b, List<(long From, int Size, Node Load, Node Store)> pieces, Node toBase, Node fromBase, long apart, long start, long end)
    {
        // The same memory on both sides: what is written must not be what is read.
        if (ReferenceEquals(toBase, fromBase) && start + apart < end && start < end + apart) return;
        var members = new HashSet<Node>();
        int first = int.MaxValue, last = -1;
        foreach (var (_, _, load, store) in pieces)
        {
            if (_position[load] > _position[store]) return;
            members.Add(load);
            members.Add(store);
            first = Math.Min(first, _position[load]);
            last = Math.Max(last, _position[store]);
        }
        var ordered = new List<Node>();
        for (int k = first; k <= last; k++)
        {
            Node n = b.Nodes[k];
            if (n.Dead) continue;
            if (members.Contains(n))
            {
                ordered.Add(n);
                continue;
            }
            // In between: nothing that could do anything (a call), nothing that reads what the copy is writing,
            // and nothing stored where the copy reads or writes. Other stores are the pieces of another copy
            // made at the same time, as a rule: the compiler interleaves what it knows to be apart.
            if (n.Op is Op.Call or Op.TailCall) return;
            if (n.Op == Op.Load)
            {
                var (at, offset) = SplitAddress(n.In[0]);
                if (ReferenceEquals(at, toBase) && offset < end + apart && start + apart < offset + Math.Max(1, n.Type.Bytes())) return;
            }
            else if (n.Op == Op.Store)
            {
                var (at, offset) = SplitAddress(n.In[0]);
                int bytes = Math.Max(1, n.In[1].Type.Bytes());
                if (ReferenceEquals(at, fromBase) && offset < end && start < offset + bytes) return;
                if (ReferenceEquals(at, toBase) && offset < end + apart && start + apart < offset + bytes) return;
                // An address that is worked out (an element, something at a distance that varies) could be
                // anywhere in the same object.
                if (at.Op is Op.Add or Op.Sub or Op.Mul or Op.Shl) return;
            }
        }
        Node completes = b.Nodes[last];
        if (completes.Op != Op.Store || !members.Contains(completes)) return;
        _pieceCopies[completes] = new PieceCopy
        {
            To = pieces[0].Store.In[0], From = pieces[0].Load.In[0], Size = (int)(end - start), Members = ordered, Address = completes.Addr,
        };
        foreach (Node n in members) _pieceMembers.Add(n);
    }

    // ---- structs cleared piece by piece ---------------------------------------------------------------------------

    private static readonly bool NoPieceFills = Environment.GetEnvironmentVariable("REWIND_NO_PIECE_FILLS") != null;

    /// <summary>A run of bytes set to zero by straight-line stores: the address of its first byte, its size, the stores.</summary>
    private sealed class PieceFill
    {
        public required Node To;
        public required int Size;
        public required List<Node> Members;
        public required ulong Address;
    }

    /// <summary>By the store that begins it.</summary>
    private readonly Dictionary<Node, PieceFill> _pieceFills = [];
    private readonly HashSet<Node> _fillMembers = [];

    /// <summary>
    /// Finds the fills made piece by piece: zeros stored side by side over more bytes than one store covers. One
    /// by one they cut across fields ("eight zero bytes at offset 8 of a buffer of numbers"); together they are
    /// "x = default". They are taken together where nothing between the first and the last could see the
    /// difference: then the whole fill can stand where the first store does.
    /// </summary>
    private void FindPieceFills()
    {
        if (NoPieceFills) return;
        foreach (Block b in _fn.Blocks)
        {
            Dictionary<Node, List<(long At, int Size, Node Store)>>? groups = null;
            foreach (Node n in b.Nodes)
            {
                if (n.Dead || n.Op != Op.Store || !n.In[1].IsConst || n.In[1].UImm != 0 || !_position.ContainsKey(n)) continue;
                if (_spillStores.Contains(n) || _caughtStores.Contains(n) || _pieceMembers.Contains(n)) continue;
                int size = n.In[1].Type.Bytes();
                if (size <= 0) continue;
                var (at, offset) = SplitAddress(n.In[0]);
                groups ??= [];
                if (!groups.TryGetValue(at, out var list)) groups[at] = list = [];
                list.Add((offset, size, n));
            }
            if (groups == null) continue;
            foreach (var (at, list) in groups)
            {
                if (list.Count < 2) continue;
                list.Sort((x, y) => x.At.CompareTo(y.At));
                for (int i = 0; i < list.Count;)
                {
                    long start = list[i].At, end = start + list[i].Size;
                    int j = i + 1;
                    while (j < list.Count && list[j].At <= end)
                    {
                        end = Math.Max(end, list[j].At + list[j].Size);
                        j++;
                    }
                    if (end - start > 8 && j - i >= 2) ConsiderFill(b, list.GetRange(i, j - i), at, start, end);
                    i = j;
                }
            }
        }
    }

    private void ConsiderFill(Block b, List<(long At, int Size, Node Store)> pieces, Node at, long start, long end)
    {
        var members = new HashSet<Node>();
        int first = int.MaxValue, last = -1;
        foreach (var (_, _, store) in pieces)
        {
            members.Add(store);
            first = Math.Min(first, _position[store]);
            last = Math.Max(last, _position[store]);
        }
        var ordered = new List<Node>();
        for (int k = first; k <= last; k++)
        {
            Node n = b.Nodes[k];
            if (n.Dead) continue;
            if (members.Contains(n))
            {
                ordered.Add(n);
                continue;
            }
            // In between: nothing that could look at the bytes, and nothing else put into them.
            if (n.Op is Op.Call or Op.TailCall) return;
            if (n.Op is Op.Load or Op.Store)
            {
                var (other, offset) = SplitAddress(n.In[0]);
                int bytes = Math.Max(1, (n.Op == Op.Load ? n.Type : n.In[1].Type).Bytes());
                if (ReferenceEquals(other, at) && offset < end && start < offset + bytes) return;
            }
        }
        Node begins = b.Nodes[first];
        if (begins.Op != Op.Store || !members.Contains(begins)) return;
        _pieceFills[begins] = new PieceFill { To = pieces[0].Store.In[0], Size = (int)(end - start), Members = ordered, Address = begins.Addr };
        foreach (Node n in members) _fillMembers.Add(n);
    }

    /// <summary>
    /// Whether any store of a fill, taken alone, goes to nothing that has a name (it cuts across fields). Where
    /// every one is a store into a field or a variable, they are that - "a = 0; b = null" - and stay.
    /// </summary>
    private bool CutsAcrossFields(PieceFill fill)
    {
        _peeking++;
        try
        {
            foreach (Node store in fill.Members)
                if (ResolvePlace(store.In[0], store.In[1].Type.Bytes()) is PUnknown)
                    return true;
            return false;
        }
        finally
        {
            _peeking--;
        }
    }

    /// <summary>The copy as one, where its last piece is stored; failing that, its pieces one by one as the code has them.</summary>
    private void EmitPieceCopy(PieceCopy copy)
    {
        if (TryEmitCopy(copy.To, copy.From, copy.Size, copy.Address, quiet: true)) return;
        foreach (Node n in copy.Members)
        {
            if (n.Op == Op.Store) EmitStore(n);
            else if (_materialize.Contains(n)) Materialize(n);
        }
    }

    /// <summary>A struct, and - while a struct is nothing but one field of its own size - that field: the same bytes under each type.</summary>
    private List<PLocation> Views(PLocation place)
    {
        var views = new List<PLocation> { place };
        HExpr current = place.Location;
        TypeSig type = place.Type;
        for (int depth = 0; depth < 4 && IsStructType(type); depth++)
        {
            int size = _p.Layouts.SizeOf(type).Size;
            if (_p.Layouts.FieldAt(type, 0) is not { Offset: 0 } first || first.Size != size || !IsStructType(first.Type)) break;
            current = new HField { Object = current, Field = first.Field, DeclaringType = type, Type = first.Type };
            type = first.Type;
            views.Add(new PLocation(current, type));
        }
        return views;
    }

    private string Describe(Place? place) => place switch
    {
        null => "untyped stack memory",
        PLocation loc => $"{loc.Type.ShortName} of {_p.Layouts.SizeOf(loc.Type).Size} bytes",
        PParts { OwnerType: { } type } parts => $"bytes from {parts.Offset} of {type.ShortName}",
        PChunk chunk => $"bytes from {chunk.Offset} of {chunk.OwnerType.ShortName}",
        PUnknown unknown => unknown.Why,
        _ => place.GetType().Name[1..],
    };
}
