using Rewind.Analysis.Ir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

internal sealed record ProjectedEnumBox(int Offset, TypeSig Type, Node Header, Node Consumer);

/// <summary>
/// Recognizes the complete inline stack-box idiom when the class comes from a metadata initializer's
/// integer return instead of a SlotValue. No evaluator cache is used before the call has been processed.
/// </summary>
internal static class ProjectedEnumBoxes
{
    private static Node? Argument(Node call, int index)
    {
        if (call.Aux is not CallInfo info || call.In.Length != info.Slots.Count) return null;
        int at = info.Slots.FindIndex(slot => slot.Kind == ArgSlotKind.IntReg && slot.Index == index);
        return at >= 0 && info.Slots.Count(slot => slot.Kind == ArgSlotKind.IntReg && slot.Index == index) == 1 ? call.In[at] : null;
    }

    internal static ProjectedEnumBox? Match(Block block, Node header, Func<Node, int?> frameOffset,
        Func<ulong, bool> initializer, Func<ulong, TypeSig?> enumSlot, Func<ulong, bool> enumToString)
    {
        if (block.Scope != -1 || header.Dead || header.Op != Op.Store || header.Aux != null ||
            header.In is not [_, { Op: Op.Proj, Type: VT.I64, Imm: 0, Dead: false } projection] ||
            projection.Aux != null || projection.In is not [{ Op: Op.Call, Dead: false } init] ||
            init.Aux is not CallInfo { Indirect: false, Intrinsic: null, NoReturn: false } initInfo ||
            !initializer(initInfo.Target) || Argument(init, 0) is not { Op: Op.Const, Type: VT.I64, Dead: false, Aux: null } slot ||
            slot.In.Length != 0 || slot.UImm == 0 || (slot.UImm & 7) != 0 ||
            enumSlot(slot.UImm) is not TypeDefSig { Definition: { IsEnum: true, IsValueType: true, EnumUnderlyingType: PrimitiveSig underlying } } type ||
            type.ContainsGenericParameter || frameOffset(header.In[0]) is not int offset ||
            offset > int.MaxValue - 24) return null;
        int bytes = underlying.Element switch
        {
            Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 => 1,
            Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 => 2,
            Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 => 4,
            Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 => 8,
            _ => 0,
        };
        if (bytes == 0 || !ReferenceEquals(init.Block, block) || !ReferenceEquals(projection.Block, block) ||
            !ReferenceEquals(header.Block, block)) return null;
        int first = block.Nodes.IndexOf(init), at = block.Nodes.IndexOf(header);
        if (first < 0 || at <= first) return null;
        var stores = new List<Node>();
        for (int i = first + 1; i < block.Nodes.Count && i - first <= 128; i++)
        {
            Node n = block.Nodes[i];
            if (n.Dead) continue;
            if (!ReferenceEquals(n.Block, block)) return null;
            if (n.Op == Op.Call)
            {
                if (n.Aux is not CallInfo { Indirect: false, Intrinsic: null, NoReturn: false } info ||
                    !enumToString(info.Target) || n.In.Length != 2 || info.Slots.Count != 2 ||
                    Argument(n, 0) is not { } receiver || frameOffset(receiver) != offset ||
                    Argument(n, 1) is not { Op: Op.Const, Type: VT.I64, Imm: 0, Dead: false, Aux: null } methodInfo ||
                    methodInfo.In.Length != 0 || stores.Count != 3 || !ReferenceEquals(stores[1], header)) return null;
                Node payload = stores[0], mark = stores[2];
                if (frameOffset(payload.In[0]) != offset + 16 ||
                    payload.In[1].Type is not (VT.I8 or VT.I16 or VT.I32 or VT.I64) || payload.In[1].Type.Bytes() != bytes ||
                    frameOffset(mark.In[0]) != offset + 8 ||
                    mark.In[1] is not { Op: Op.Const, Type: VT.I64, Imm: -1, Dead: false, Aux: null } marker ||
                    marker.In.Length != 0) return null;
                return new ProjectedEnumBox(offset, type, header, n);
            }
            if (n.Op == Op.Store)
            {
                if (n.Aux != null || n.In.Length != 2 || n.In[1].Dead || stores.Count == 3) return null;
                stores.Add(n); continue;
            }
            // No load, other call, branch, hidden store or computation with a possible exception may
            // occur between the initializer and the consuming call. Only address formation and its
            // direct returned class are needed for this idiom.
            if (n.Op == Op.Proj && ReferenceEquals(n, projection)) continue;
            if (n.Op == Op.Add && n.Type == VT.I64 && n.Aux == null && n.In.Length == 2 && frameOffset(n) != null) continue;
            if (n.Op == Op.Const && n.Aux == null && n.In.Length == 0) continue;
            return null;
        }
        return null;
    }
}

public sealed partial class HirBuilder
{
    private readonly HashSet<Node> _projectedEnumHeaders = [];

    private void FindProjectedEnumBoxes()
    {
        if (_m.Image.Arch != Rewind.Binary.CpuArch.Arm64 || _ptr != 8 || _header != 16) return;
        int? Frame(Node node) => IsFrameAddress(node, out int offset) ? offset : null;
        TypeSig? EnumSlot(ulong address) => _m.ResolveUsageSlot(address) is
            { Kind: UsageKind.TypeInfo, Type: TypeDefSig { Definition.IsEnum: true } type } &&
            _p.Layouts.SizeOf(type) is { Known: true, Size: 1 or 2 or 4 or 8 } ? type : null;
        bool ToString(ulong address)
        {
            CallTarget target = _p.Resolve(address);
            return target.Helper == null && target.Insts.Count == 0 && target.Methods.Count == 1 &&
                target.Methods[0] is { Name: "ToString", IsStatic: false, IsGenericDefinition: false, Parameters.Length: 0 } method &&
                method.Address == address && (method.Flags & MethodDef.AccessMask) == 6 &&
                ReferenceEquals(method.DeclaringType, _m.FindType("System.Enum")) &&
                method.ReturnType is PrimitiveSig { Element: Il2CppTypeEnum.String };
        }
        var candidates = new List<ProjectedEnumBox>();
        foreach (Block block in _fn.Blocks)
            foreach (Node node in block.Nodes)
                if (node.Op == Op.Store && ProjectedEnumBoxes.Match(block, node, Frame, IsUnaryMetadataService, EnumSlot, ToString) is { } found)
                    candidates.Add(found);
        foreach (var group in candidates.GroupBy(c => c.Offset))
        {
            TypeSig type = group.First().Type;
            if (group.Any(c => c.Type.Key != type.Key) ||
                _fakeBoxes.TryGetValue(group.Key, out TypeSig? previous) && previous.Key != type.Key) continue;
            _fakeBoxes[group.Key] = type;
            _frameTypes[group.Key + _header] = type;
            foreach (ProjectedEnumBox box in group) _projectedEnumHeaders.Add(box.Header);
        }
    }
}
