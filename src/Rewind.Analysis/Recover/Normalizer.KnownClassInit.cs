using Rewind.Analysis.Ir;
using Rewind.Analysis.Runtime;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

public sealed partial class Normalizer
{
    private TypeSig? KnownClassForInit(Node value)
    {
        value = Resolve(value);
        if (value.Op == Op.SlotValue)
        {
            if (program.Defaults.Slots.TryGetValue(value.UImm, out TypeDef? type)) return type.Sig;
            return program.Model.ResolveUsageSlot(value.UImm) is { Kind: UsageKind.TypeInfo, Type: { } direct } ? direct : null;
        }
        if (value is not { Op: Op.Load, Type: VT.I64, In: [{ Op: Op.Add, In.Length: 2 } address] }) return null;
        Node descriptor, offset;
        if (address.In[0].IsConst) (descriptor, offset) = (Resolve(address.In[1]), address.In[0]);
        else (descriptor, offset) = (Resolve(address.In[0]), address.In[1]);
        if (!offset.IsConstValue(32) || descriptor.Op != Op.SlotValue ||
            program.Model.ResolveUsageSlot(descriptor.UImm) is not { Kind: UsageKind.MethodDef or UsageKind.MethodRef, Method: { } method } usage) return null;
        TypeSig[] arguments = usage.MethodInst?.ClassArguments ?? [];
        return arguments.Length == 0 ? method.DeclaringType.Sig : program.Model.Sigs.GenericInst(method.DeclaringType, arguments);
    }

    // Only the v39 initialized-and-no-error bit, with the original native slow
    // call independently identified. Metadata-only initialization of a type
    // without a managed .cctor is owned by the managed runtime.
    private void FoldKnownClassInitFlags()
    {
        if (program.Model.Image.Arch != CpuArch.Arm64 || program.Model.Version != Rewind.Metadata.MetaVersion.V39) return;
        var image = program.Model.Image;
        foreach (Block block in _fn.Blocks)
        {
            if (block.Terminator is not { Op: Op.Branch, In: [var condition] } branch ||
                condition.Op is not (Op.CmpEq or Op.CmpNe) || condition.In.Length != 2 || !condition.In[1].IsConstValue(0) ||
                condition.In[0] is not { Op: Op.And, In: [var bits, var mask] } || !mask.IsConstValue(1)) continue;
            if (bits.Op is Op.ZExt or Op.SExt && bits.In.Length == 1) bits = bits.In[0];
            if (bits is not { Op: Op.Load, Type: VT.I8 or VT.I16, In: [{ Op: Op.Add, In.Length: 2 } flagAddress] } ||
                !flagAddress.In[1].IsConstValue(program.Klass.Bitflags) || KnownClassForInit(flagAddress.In[0]) is not { } klass ||
                !(klass is ArraySig or SzArraySig || klass.Definition is { HasStaticConstructor: false }) ||
                !image.TrySpan(branch.Addr, 4, out _) || !TryClassInitBranch(image.U32(branch.Addr), branch.Addr, out ulong slow) ||
                slow < _fn.Address || slow >= _fn.End || !image.TrySpan(slow, 4, out _)) continue;
            uint call = image.U32(slow);
            if ((call & 0xfc000000u) != 0x94000000u) continue;
            long relative = ((long)(int)(call << 6) >> 6) * 4;
            if (program.Helpers.KindAt(unchecked((ulong)((long)slow + relative))) != HelperKind.ClassInitSlow) continue;
            branch.In[0] = _b.Const(VT.I1, condition.Op == Op.CmpNe ? 1 : 0);
            _result.ReceiverNotes.Add($"metadata-only class initialization at 0x{branch.Addr:X} for {klass.DisplayName}");
        }
    }
}
