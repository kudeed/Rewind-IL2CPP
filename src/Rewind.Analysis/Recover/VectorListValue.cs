using Rewind.Analysis.Hir;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>Only exact public sequential Unity Vector2/Vector3/Vector4/Color float layouts.
/// Do not generalize the ABI of a value type from a matching name or size.</summary>
internal static class VectorListValue
{
    internal static int Dimension(TypeSig? type,int header)
    {
        if(type is not TypeDefSig||type.Definition is not {IsValueType:true,IsEnum:false,IsGenericDefinition:false} d||
            d.Assembly.Name!="UnityEngine.CoreModule")return 0;
        string names=d.ReflectionName switch
        {
            "UnityEngine.Vector2"=>"xy", "UnityEngine.Vector3"=>"xyz",
            "UnityEngine.Vector4"=>"xyzw", "UnityEngine.Color"=>"rgba", _=>""
        };
        int n=names.Length;
        if(n==0||d.Sizes.InstanceSize!=header+4*n||
            (d.Flags&TypeDef.LayoutMask)!=TypeDef.SequentialLayout)return 0;
        var fields=d.Fields.Where(f=>!f.IsStatic).ToArray();
        if(fields.Length!=n)return 0;
        for(int i=0;i<n;i++)
        {
            var matches=fields.Where(f=>f.Name==names[i].ToString()).ToArray();
            if(matches.Length!=1||matches[0].Offset!=header+4*i||
                (matches[0].Attrs&FieldDef.AccessMask)!=6||
                matches[0].Type is not PrimitiveSig{Element:Il2CppTypeEnum.R4})return 0;
        }
        return n;
    }
    internal static bool ValueOnlyLocal(HMethod method,SigFactory sigs,HVar variable)
    {
        if(!variable.Type.IsValueType||method.Problems.Count!=0||method.TryRegions.Count!=0)return false;
        // All explicit address constructions, pointer/opaque uses and
        // receiver calls are excluded. Substitution is required for a
        // value argument of a generic method.
        bool Mentions(HExpr? e)=>ConstructorFolding.Mentions(e,variable);
        bool Argument(HExpr e,TypeSig type)
        {
            if(!Mentions(e))return true;
            if(type is ByRefSig or PointerSig||type.ContainsGenericParameter)return false;
            return Safe(e)&&(e.Type??(e as HLocal)?.Variable.Type)?.Key==type.Key;
        }
        bool Safe(HExpr? e)
        {
            if(!Mentions(e))return true;
            switch(e)
            {
                case HLocal l:return l.Variable==variable&&(l.Type==null||l.Type.Key==variable.Type.Key);
                case HField f:return f.Object is HLocal l2&&l2.Variable==variable&&!f.Field.IsStatic&&
                    ReferenceEquals(f.Field.DeclaringType,variable.Type.Definition)&&f.Field.Type is PrimitiveSig{Element:Il2CppTypeEnum.R4};
                case HCall c:
                    if(Mentions(c.This)||c.Arguments.Length!=c.Method.Parameters.Length)return false;
                    var cls=(c.DeclaringType as GenericInstSig)?.Arguments??[];
                    return c.Arguments.Select((arg,i)=>Argument(arg,sigs.Substitute(c.Method.Parameters[i].Type,cls,c.MethodArguments))).All(x=>x);
                case HNewObject n:
                    if(n.Arguments.Length!=n.Constructor.Parameters.Length)return false;
                    var cl=(n.DeclaringType as GenericInstSig)?.Arguments??[];
                    return n.Arguments.Select((arg,i)=>Argument(arg,sigs.Substitute(n.Constructor.Parameters[i].Type,cl,[]))).All(x=>x);
                // Pure scalar arithmetic on known components only.
                case HBinary b:return b.Type is PrimitiveSig&&Safe(b.Left)&&Safe(b.Right);
                case HUnary u:return u.Type is PrimitiveSig&&Safe(u.Operand);
                case HCompare c:return Safe(c.Left)&&Safe(c.Right);
                default:return false;
            }
        }
        foreach(var b in method.Blocks)
        foreach(var s in b.Statements)
        {
            if(!ConstructorFolding.Mentions(s,variable))continue;
            bool ok=s switch
            {
                HAssign a=>Safe(a.Target)&&Safe(a.Value),
                HEval e=>Safe(e.Expression),
                HReturn r=>Safe(r.Value),
                HBranch br=>Safe(br.Condition),
                _=>false
            };
            // Array destinations containing the value local are never
            // accepted; the item itself is on the assignment's RHS.
            if(!ok)return false;
        }
        return true;
    }

    internal static bool ConstructorShape(NativeImage image,MethodDef ctor,TypeSig? type)
    {
        if(image.Arch!=CpuArch.Arm64||Dimension(type,2*image.PointerSize) is not (2 or 3 or 4)||
            !ReferenceEquals(type!.Definition,ctor.DeclaringType)||ctor.Name!=".ctor"||ctor.IsStatic||
            ctor.IsGenericDefinition||ctor.Address==0||!ctor.ReturnType.IsVoid||
            ctor.Parameters.Any(p=>p.Type is not PrimitiveSig{Element:Il2CppTypeEnum.R4}))return false;
        int n=Dimension(type,2*image.PointerSize);
        int instructions=n==2?2:3;
        int bytes=4*instructions;
        if(ctor.Parameters.Length!=n||image.SectionAt(ctor.Address) is not {IsExecutable:true} section||
            ctor.Address>ulong.MaxValue-(ulong)bytes||ctor.Address+(ulong)bytes>section.End||
            !image.IsMapped(ctor.Address,bytes))return false;
        // Exact original ARM64 component stores, then ret. Four components use
        // stp s2,s3,[x0,#8], independently executed without runtime shims.
        return image.U32(ctor.Address)==0x2D000400u&&
            (n==2||image.U32(ctor.Address+4)==(n==3?0xBD000802u:0x2D010C02u))&&
            image.U32(ctor.Address+(ulong)(bytes-4))==0xD65F03C0u;
    }
}
