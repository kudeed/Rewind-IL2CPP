using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

public sealed partial class HirBuilder
{
    internal static FieldSlot[]? WholePublicFieldRange(TypeLayout layout, int offset, int size)
    {
        if (!layout.Known || offset < 0 || size <= 0 || (long)offset + size > layout.Size) return null;
        var fields = layout.Fields.Where(f => f.Offset < (long)offset + size && (long)f.Offset + f.Size > offset).OrderBy(f => f.Offset).ToArray();
        long at = offset;
        foreach (var f in fields)
        {
            if (f.Offset != at || f.Size <= 0 || f.Field.IsStatic || (f.Field.Attrs & FieldDef.AccessMask) != 6 ||
                (f.Field.Attrs & FieldDef.InitOnly) != 0) return null;
            at += f.Size;
        }
        return fields.Length > 1 && at == (long)offset + size ? fields : null;
    }

    private bool ExactNumericalValue(TypeSig type, HashSet<TypeSig> parents, int depth = 0)
    {
        if (depth > 8 || !parents.Add(type)) return false;
        try
        {
            if (type is PrimitiveSig p) return p.Element is Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 or Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 or Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 or Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 or Il2CppTypeEnum.R4 or Il2CppTypeEnum.R8;
            if (type is not TypeDefSig { Definition.IsValueType: true } || Open(type)) return false;
            var layout = _p.Layouts.Of(type); int end = 0;
            if (!layout.Known || layout.Fields.Length == 0) return false;
            foreach (var f in layout.Fields.OrderBy(f => f.Offset))
            {
                if (f.Offset < 0 || f.Size <= 0 || (long)f.Offset + f.Size > layout.Size || !ExactNumericalValue(f.Type, parents, depth + 1)) return false;
                // Private numerical union aliases (Color32.rgba) describe the same bytes.
                // A nonoverlapping public cover must still account for every byte exactly once.
                if ((f.Field.Attrs & FieldDef.AccessMask) != 6) continue;
                if (f.Offset != end) return false;
                end += f.Size;
            }
            return end == layout.Size;
        }
        finally { parents.Remove(type); }
    }

    // A compiler can keep only the tail fields of a struct in a stack temporary.
    // Keep each recorded whole field in its own typed local; never invent a larger owner spanning neighboring stack data.
    private bool TryEmitPartialFrameCopy(Node toAddress, Node fromAddress, int size, ulong address)
    {
        bool toFrame = IsFrameAddress(toAddress, out int to), fromFrame = IsFrameAddress(fromAddress, out int from);
        bool trace = _h.Method.Index == 26696 && Environment.GetEnvironmentVariable("REWIND_PARTIAL_FRAME_TRACE") != null;
        if (trace) Console.Error.WriteLine($"partial-copy address toFrame={toFrame} to={to} fromFrame={fromFrame} from={from} bytes={size}");
        if ((!toFrame && !fromFrame) || size <= 0) return false;
        bool bothFrames = toFrame && fromFrame;
        (HExpr Owner, TypeSig Type, int Offset)? recorded = null;
        if (bothFrames)
        {
            // Exact physical frame intervals must not alias. Preserve the recorded typed end;
            // the other end can be an otherwise untyped tail temporary.
            if ((long)to < (long)from + size && (long)from < (long)to + size) return false;
            var sourceRun = RunOf(BlockPlace(fromAddress, size, null));
            var targetRun = RunOf(BlockPlace(toAddress, size, null));
            // A Vector3 local at the beginning of a 96-byte tail is only its first field.
            // It cannot describe the whole copy; use the opposite end's proven parent layout.
            if (sourceRun is { } sr && WholePublicFieldRange(_p.Layouts.Of(sr.Type), sr.Offset, size) == null) sourceRun = null;
            if (targetRun is { } tr && WholePublicFieldRange(_p.Layouts.Of(tr.Type), tr.Offset, size) == null) targetRun = null;
            if ((sourceRun != null) == (targetRun != null)) return false;
            if (sourceRun != null) { recorded = sourceRun; fromFrame = false; }
            else { recorded = targetRun; toFrame = false; }
        }
        int frame = toFrame ? to : from;
        Node typedAddress = toFrame ? fromAddress : toAddress;
        // &array[i].normal still points inside the original UIVertex. Resolving 96 bytes through
        // Vector3 alone discards the neighboring fields; retain the exact recorded parent instead.
        if (recorded == null && Eval(typedAddress) is SRef { Location: HField { Object: { Type: TypeDefSig parent } owner } referencedField } reference &&
            referencedField.Type?.Key == reference.Type.Key && parent.Definition.IsValueType && !Open(parent))
        {
            var layout = _p.Layouts.Of(parent);
            var matches = layout.Fields.Where(f => ReferenceEquals(f.Field, referencedField.Field) && f.Type.Key == reference.Type.Key).ToArray();
            if (layout.Known && matches.Length == 1 && matches[0].Size > 0 && size > matches[0].Size &&
                (long)matches[0].Offset + size <= layout.Size)
                recorded = (owner, parent, matches[0].Offset);
        }
        else if (recorded == null) recorded = RunOf(BlockPlace(typedAddress, size, null));
        if (trace) Console.Error.WriteLine(recorded is {} observed ? $"partial-copy parent={observed.Type.DisplayName} offset={observed.Offset} owner={observed.Owner.GetType().Name}" : "partial-copy no recorded parent");
        if (recorded is not { } run || run.Type is not TypeDefSig { Definition.IsValueType: true } || Open(run.Type)) return false;
        bool stable = run.Owner is HElement { Array: HArg or HLocal, Index: var index } && IsPure(index) ||
            run.Owner is HLocal local && (bothFrames || !_frameVars.Values.Contains(local.Variable));
        if (trace) Console.Error.WriteLine($"partial-copy stable={stable} fields=" + string.Join(",", _p.Layouts.Of(run.Type).Fields.Select(f => $"{f.Field.Name}@{f.Offset}:{f.Size}:{f.Field.Attrs}")));
        if (!stable || WholePublicFieldRange(_p.Layouts.Of(run.Type), run.Offset, size) is not { } fields ||
            fields.Any(f => !ExactNumericalValue(f.Type, []))) return false;
        foreach (var field in fields)
        {
            long start = (long)frame + field.Offset - run.Offset;
            if (start < int.MinValue || start + field.Size > int.MaxValue) return false;
            bool exact = false;
            foreach (var (offset, type) in _frameTypes)
            {
                var layout = _p.Layouts.SizeOf(type);
                if (!layout.Known || layout.Size <= 0) return false;
                if (offset >= start + field.Size || start >= (long)offset + layout.Size) continue;
                if (offset != start || type.Key != field.Type.Key || layout.Size != field.Size) return false;
                exact = true;
            }
            if (!toFrame && !exact) return false;
        }
        foreach (var field in fields)
        {
            int offset = checked(frame + field.Offset - run.Offset);
            _frameTypes[offset] = field.Type;
            var temporary = new HLocal(FrameVar(offset, field.Type)) { Type = field.Type };
            var member = new HField { Object = run.Owner, Field = field.Field, DeclaringType = run.Type, Type = field.Type };
            Emit(toFrame ? new HAssign(temporary, member) : new HAssign(member, temporary), address);
        }
        _h.Notes.Add($"partial stack copy preserved {size} bytes as {fields.Length} complete fields");
        return true;
    }
}
