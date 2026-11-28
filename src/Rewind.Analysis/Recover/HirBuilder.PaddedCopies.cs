using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

public sealed partial class HirBuilder
{
    // A native copy can start in alignment padding and then carry one complete
    // struct field. Padding has no managed field; the complete value does.
    internal static FieldSlot? LeadingPaddingField(TypeLayout layout,int offset,int size,int pointerSize)
    {
        long end=(long)offset+size;
        if(!layout.Known || offset<0 || size<=0 || end>layout.Size || pointerSize is not (4 or 8)) return null;
        var candidates=layout.Fields.Where(f=>f.Offset>offset && f.Offset-offset<pointerSize && (long)f.Offset+f.Size==end).ToArray();
        if(candidates.Length!=1)return null;
        FieldSlot field=candidates[0];
        if(field.Size<=0 || layout.Fields.Any(f=>f!=field && f.Offset<end && offset<(long)f.Offset+f.Size))return null;
        return field;
    }

    private bool TryEmitLeadingPaddingCopy(Node toAddress,Node fromAddress,int size,ulong address)
    {
        if(Eval(toAddress) is not SFrame to || Eval(fromAddress) is not SFrame from ||
            FrameObjectAt(to.Offset) is not int start || !_frameTypes.TryGetValue(start,out TypeSig? ownerType) ||
            !IsStructType(ownerType) || Open(ownerType))return false;
        TypeLayout layout=_p.Layouts.Of(ownerType);
        if(LeadingPaddingField(layout,to.Offset-start,size,_ptr) is not { } field ||
            !IsStructType(field.Type) || Open(field.Type))return false;
        int sourceOffset=from.Offset+field.Offset-(to.Offset-start);
        if(!_frameTypes.TryGetValue(sourceOffset,out TypeSig? sourceType) || sourceType.Key!=field.Type.Key ||
            _p.Layouts.SizeOf(sourceType) is not {Known:true} sourceSize || sourceSize.Size!=field.Size)return false;
        var owner=new HLocal(FrameVar(start,ownerType)){Type=ownerType};
        var target=new HField{Object=owner,Field=field.Field,DeclaringType=ownerType,Type=field.Type};
        var source=new HLocal(FrameVar(sourceOffset,sourceType)){Type=sourceType};
        Emit(new HAssign(target,source),address);
        return true;
    }
}
