using Rewind.Analysis.Hir;
using Rewind.Analysis.Runtime;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>Recover a public compound setter that stores a reference and
/// its position.z, inlined across an independent local field read. The
/// complete native target body and exact HIR operands must both match.</summary>
internal static class Arm64TargetPositionSetter
{
    internal static bool Matches(uint[] code, int first,int second,ulong address,ulong getter,Func<ulong,bool> nullThrow)
    {
        if(code.Length!=11||first<0||first%8!=0||first/8>4095||second<0||second%4!=0||second/4>4095)return false;
        ulong Branch(int i)=>unchecked((ulong)((long)address+4*i+((long)(int)(code[i]<<6)>>6)*4));
        return code[0]==0xa9bf4ffe&&code[1]==(0xf9000001u|((uint)(first/8)<<10))&&
            code[2]==0xb4000101&&code[3]==0xaa0003f3&&code[4]==0xaa0103e0&&code[5]==0xaa1f03e1&&
            (code[6]&0xfc000000u)==0x94000000u&&Branch(6)==getter&&
            code[7]==(0xbd000262u|((uint)(second/4)<<10))&&code[8]==0xa8c14ffe&&code[9]==0xd65f03c0&&
            (code[10]&0xfc000000u)==0x94000000u&&nullThrow(Branch(10));
    }

    internal static void Run(HMethod h,ProgramAnalysis p)
    {
        if(Environment.GetEnvironmentVariable("REWIND_NO_TARGET_POSITION_SETTER")!=null||
           p.Model.Image.Arch!=CpuArch.Arm64||h.TryRegions.Count!=0||h.Blocks.Any(b=>b.Scope!=-1)||
           h.Problems.Count!=0)return;
        var image=p.Model.Image;
        bool Direct(HCall c)=>!c.Virtual&&!c.Method.IsVirtual&&!c.Method.IsStatic&&!c.Method.IsAbstract&&!c.Method.IsGenericDefinition&&
            c.MethodArguments.Length==0&&c.DeclaringType==null;
        static bool Same(HExpr? a,HExpr? b)=>a is HLocal l&&b is HLocal r&&l.Variable==r.Variable;
        foreach(var block in h.Blocks)
        for(int i=0;i+2<block.Statements.Count;i++)
        {
            var s=block.Statements;
            if(s[i] is not HEval{Expression:HCall{This:HLocal receiver,Arguments:[HLocal target]} set}||
               !Direct(set)||set.Method.Parameters.Length!=1||!set.Method.ReturnType.IsVoid||
               receiver.Variable.Type is not TypeDefSig owner||owner.Definition!=set.Method.DeclaringType||owner.Definition.IsGenericDefinition||owner.Definition.IsValueType||
               receiver.Variable.AddressTaken||target.Variable.AddressTaken||
               target.Variable.Type.Definition is not {ReflectionName:"UnityEngine.Transform",Assembly.Name:"UnityEngine.CoreModule"}||
               set.Method.Parameters[0].Type.Key!=target.Variable.Type.Key||
               s[i+1] is not HAssign{Target:HLocal v,Value:HCall{Arguments.Length:0} get} pos||
               !Direct(get)||!Same(get.This,target)||get.Method.Name!="get_position"||
               get.Method.DeclaringType!=target.Variable.Type.Definition||
               get.Method.ReturnType.Definition is not {ReflectionName:"UnityEngine.Vector3",Assembly.Name:"UnityEngine.CoreModule"} vector||
               v.Variable.Type.Key!=get.Method.ReturnType.Key||get.Method.Address==0)continue;
            int j=i+2;
            // At most one plain this-field read to an independent local.
            if(s[j] is HAssign{Target:HLocal other,Value:HField{Object:HArg{Index:-1}} f}&&
               !other.Variable.AddressTaken&&other.Variable!=receiver.Variable&&other.Variable!=target.Variable&&other.Variable!=v.Variable&&
               f.Field.DeclaringType==h.Method.DeclaringType&&f.Field.DeclaringType!=owner.Definition&&
               !f.Field.IsStatic&&AccessorFolding.IsAccessible(f.Field,h.Method))j++;
            if(j>=s.Count||s[j] is not HAssign{Target:HField dst,Value:HField{Object:HLocal read} z} store||
               !Same(dst.Object,receiver)||dst.Field.DeclaringType!=owner.Definition||dst.Field.IsStatic||
               AccessorFolding.IsAccessible(dst.Field,h.Method)||dst.Field.Type is not PrimitiveSig{Element:Il2CppTypeEnum.R4}||
               read.Variable!=v.Variable||z.Field.DeclaringType!=vector||z.Field.Name!="z"||
               z.Field.Type is not PrimitiveSig{Element:Il2CppTypeEnum.R4})continue;
            if(h.Blocks.SelectMany(b=>b.Statements).Any(q=>q!=pos&&q!=store&&ConstructorFolding.Mentions(q,v.Variable)))continue;
            var fields=owner.Definition.Fields.Where(f=>!f.IsStatic&&f.Type.Key==target.Variable.Type.Key&&
                owner.Definition.Properties.Any(prop=>prop.Setter==set.Method&&AccessorIndex.AutoPropertyName(f)==prop.Name)).ToArray();
            if(fields.Length!=1||p.RangeOf(set.Method.Address) is not {} sr||sr.End-sr.Start!=8||
               image.U32(sr.Start)!=(0xf9000001u|((uint)(fields[0].Offset/8)<<10))||image.U32(sr.Start+4)!=0xd65f03c0)continue;
            var matches=owner.Definition.Methods.Where(m=>m!=h.Method&&!m.IsStatic&&!m.IsVirtual&&!m.IsAbstract&&!m.IsGenericDefinition&&
                (m.Flags&MethodDef.AccessMask)==6&&m.ReturnType.IsVoid&&m.Parameters.Length==1&&m.Parameters[0].Type.Key==target.Variable.Type.Key&&
                p.RangeOf(m.Address) is {} r&&r.End-r.Start==44&&Matches(Enumerable.Range(0,11).Select(k=>image.U32(r.Start+(ulong)k*4)).ToArray(),fields[0].Offset,dst.Field.Offset,r.Start,get.Method.Address,
                    pc=>p.Helpers.KindAt(pc)==HelperKind.ThrowNullReference)).ToArray();
            if(matches.Length!=1)continue;
            s[i]=new HEval(new HCall{Method=matches[0],This=receiver,Arguments=[target],Type=matches[0].ReturnType});
            s.RemoveAt(j);s.RemoveAt(i+1);h.Locals.Remove(v.Variable);
            h.Notes.Add($"compound target-position setter restored {matches[0].FullName}");
            // Keep the prior conservative private-field note: it does not
            // establish that every other private access is now legal.
        }
    }
}
