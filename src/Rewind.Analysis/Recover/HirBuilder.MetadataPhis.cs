using Rewind.Analysis.Ir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

public sealed partial class HirBuilder
{
    /// <summary>
    /// Class-initialization paths can reload one MethodInfo's class/context before joining. Those are the
    /// same metadata identity on both paths, not integer variables. Describe only known immutable metadata;
    /// do not call Eval/Peek here, which could cache an unknown call result before its block is translated.
    /// </summary>
    private Sem? MergedMetadata(Node phi) => MetadataPhiJoin.Resolve(phi, _ptr, MetadataProjection);

    private Sem? MetadataProjection(Node node, Func<Node, Sem?> resolve)
    {
        if (_sem.TryGetValue(node, out Sem? bound) && MetadataPhiJoin.Known(bound)) return bound;
        if (node.Op == Op.SlotValue)
        {
            Sem slot = SlotSem(node);
            return MetadataPhiJoin.Known(slot) ? slot : null;
        }
        if (node.Op != Op.Load || node.In.Length != 1 || node.Type.Bytes() != _ptr) return null;
        Node address = node.In[0];
        long offset = 0;
        if (address.Op == Op.Add && address.In.Length == 2)
        {
            if (address.In[1].IsConst) { offset = IrBuilder.SImm(address.In[1]); address = address.In[0]; }
            else if (address.In[0].IsConst) { offset = IrBuilder.SImm(address.In[0]); address = address.In[1]; }
            else return null;
        }
        if (offset < 0 || offset % _ptr != 0) return null;
        switch (resolve(address))
        {
            case SKlass { Type: GenericInstSig { Definition: { } generic } instance } when offset == _p.Klass.RgctxData:
                return new SRgctx(_m.RgctxOf(generic.Assembly.ImageName, generic.Token), instance.Arguments, []);
            case SMethod method:
            {
                int klassAt = (_m.Version >= Rewind.Metadata.MetaVersion.V29_0 ? 4 : 3) * _ptr;
                TypeSig[] classes = method.Inst?.ClassArguments ?? [];
                if (offset == klassAt)
                    return new SKlass(classes.Length != 0 ? _m.Sigs.GenericInst(method.Method.DeclaringType, classes) : method.Method.DeclaringType.Sig);
                if (offset == klassAt + 3 * _ptr && method.Inst is { MethodArguments.Length: > 0 } instance)
                    return new SRgctx(_m.RgctxOf(method.Method.DeclaringType.Assembly.ImageName, method.Method.Token), instance.ClassArguments, instance.MethodArguments);
                return null;
            }
            case SRgctx context when offset / _ptr < context.Items.Count:
            {
                Sem value = RgctxValue(context, (int)(offset / _ptr));
                return MetadataPhiJoin.Known(value) ? value : null;
            }
            default:
                return null;
        }
    }
}
