using Rewind.Analysis.Hir;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>Only tightly packed, reference-free Unity Vector2/Vector3 values.
/// Do not generalize the ABI of a value type from a matching name or size.</summary>
internal static class VectorListValue
{
    internal static int Dimension(TypeSig? type,int header)
    {
        if(type is not TypeDefSig||type.Definition is not {IsValueType:true,IsEnum:false,IsGenericDefinition:false} d||
            d.Assembly.Name!="UnityEngine.CoreModule")return 0;
        int n=d.ReflectionName switch{"UnityEngine.Vector2"=>2,"UnityEngine.Vector3"=>3,_=>0};
        if(n==0||d.Sizes.InstanceSize!=header+4*n||
            (d.Flags&TypeDef.LayoutMask)!=TypeDef.SequentialLayout)return 0;
        var fields=d.Fields.Where(f=>!f.IsStatic).ToArray();
        if(fields.Length!=n)return 0;
        for(int i=0;i<n;i++)
        {
            var matches=fields.Where(f=>f.Name=="xyz"[i].ToString()).ToArray();
            if(matches.Length!=1||matches[0].Offset!=header+4*i||
                (matches[0].Attrs&FieldDef.AccessMask)!=6||
                matches[0].Type is not PrimitiveSig{Element:Il2CppTypeEnum.R4})return 0;
        }
        return n;
    }
    internal static bool ConstructorShape(NativeImage image,MethodDef ctor,TypeSig? type)
    {
        if(image.Arch!=CpuArch.Arm64||Dimension(type,2*image.PointerSize) is not (2 or 3)||
            !ReferenceEquals(type!.Definition,ctor.DeclaringType)||ctor.Name!=".ctor"||ctor.IsStatic||
            ctor.IsGenericDefinition||ctor.Address==0||!ctor.ReturnType.IsVoid||
            ctor.Parameters.Any(p=>p.Type is not PrimitiveSig{Element:Il2CppTypeEnum.R4}))return false;
        int n=Dimension(type,2*image.PointerSize);
        if(ctor.Parameters.Length!=n||image.SectionAt(ctor.Address) is not {IsExecutable:true} section||
            ctor.Address>ulong.MaxValue-(ulong)(4*(n+0))||ctor.Address+(ulong)(4*n)>section.End||
            !image.IsMapped(ctor.Address,4*n))return false;
        // stp s0,s1,[x0]; optional str s2,[x0,#8]; ret.
        return image.U32(ctor.Address)==0x2D000400u&&
            (n==2||image.U32(ctor.Address+4)==0xBD000802u)&&
            image.U32(ctor.Address+(ulong)(4*(n-1)))==0xD65F03C0u;
    }
}
