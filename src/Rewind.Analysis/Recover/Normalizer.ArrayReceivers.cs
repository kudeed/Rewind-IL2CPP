using Rewind.Analysis.Ir;
using Rewind.Analysis.Arm64;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

public sealed partial class Normalizer
{
    // Trace exactly a four-byte element load through the standard SZARRAY
    // data offset and one instance field read, not an arbitrary pointer tree.
    internal static Node? ArrayArgumentOwner(Node argument,int arrayOffset,out Node? arrayLoad,out long fieldOffset)
    {
        arrayLoad=null;fieldOffset=0;
        if(argument.Op is Op.ZExt or Op.SExt && argument.In.Length==1)argument=argument.In[0];
        if(argument.Op!=Op.Load||argument.Type!=VT.I32||argument.In.Length!=1)return null;
        static bool Offset(Node n,long value,out Node root)
        {
            root=n;
            if(n.Op!=Op.Add||n.In.Length!=2)return false;
            if(n.In[0].IsConstValue(value)){root=n.In[1];return true;}
            if(n.In[1].IsConstValue(value)){root=n.In[0];return true;}
            return false;
        }
        if(!Offset(argument.In[0],arrayOffset,out Node sum)||sum.Op!=Op.Add||sum.In.Length!=2)return null;
        Node? array=null,index=null;
        if(sum.In[0].Op==Op.Load){array=sum.In[0];index=sum.In[1];}
        else if(sum.In[1].Op==Op.Load){array=sum.In[1];index=sum.In[0];}
        if(array==null||array.Type!=VT.I64||array.In.Length!=1||index is not {Op:Op.Shl}||
            index.In.Length!=2||!index.In[1].IsConstValue(2)||array.In[0] is not {Op:Op.Add} address||
            address.In.Length!=2)return null;
        Node? offset=address.In[1].IsConst?address.In[1]:address.In[0].IsConst?address.In[0]:null;
        if(offset==null)return null;
        fieldOffset=offset.Imm;arrayLoad=array;
        return ReferenceEquals(offset,address.In[1])?address.In[0]:address.In[1];
    }

    internal static bool IsThisFieldValue(Node value,Node self,long offset,int depth=0)
    {
        if(depth>6)return false;
        if(value.Op==Op.Phi)
            return value.In.Length is >0 and <=8 && value.In.All(n=>IsThisFieldValue(n,self,offset,depth+1));
        if(value.Op!=Op.Load||value.Type!=VT.I64||value.In.Length!=1||
            value.In[0] is not {Op:Op.Add} address||address.In.Length!=2)return false;
        return ReferenceEquals(address.In[0],self)&&address.In[1].IsConstValue(offset)||
            ReferenceEquals(address.In[1],self)&&address.In[0].IsConstValue(offset);
    }

    private void RestoreArrayArgumentReceivers()
    {
        if(Environment.GetEnvironmentVariable("REWIND_NO_ARRAY_ARGUMENT_RECEIVER")!=null||
            Environment.GetEnvironmentVariable("REWIND_NO_GUARDED_RECEIVER")!=null||
            program.Model.Image.Arch!=CpuArch.Arm64||_fn.TryRegions.Count!=0||
            !program.Model.MethodsByAddress.TryGetValue(_fn.Address,out var callers)||callers.Count!=1||
            callers[0] is not {IsStatic:false,IsGenericDefinition:false} caller||
            caller.DeclaringType.IsValueType||caller.DeclaringType.IsGenericDefinition||
            !_fn.Params.TryGetValue(_fn.Regs.IntArgs[0],out Node? self))return;
        Cfg? cfg=null;
        foreach(Block block in _fn.Blocks)
        foreach(Node call in block.Nodes)
        {
            if(call.Dead||call.Op is not (Op.Call or Op.TailCall)||
                call.Aux is not CallInfo{Indirect:false,Intrinsic:null,NoReturn:false} ci||
                !program.Model.MethodsByAddress.TryGetValue(ci.Target,out var methods)||methods.Count!=1||
                methods[0] is not {IsStatic:false,IsVirtual:false,IsAbstract:false,IsConstructor:false,IsGenericDefinition:false} callee||
                callee.DeclaringType.IsValueType||callee.DeclaringType.IsGenericDefinition||
                callee.Parameters.Length<1||
                // Only exact int/enum first argument, passed in w1.
                callee.Parameters[0].Type is not { } parameter||
                !(parameter is PrimitiveSig{Element:Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4}||
                  parameter.Definition?.EnumUnderlyingType is PrimitiveSig{Element:Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4}))
                continue;
            var fields=caller.DeclaringType.Fields.Where(f=>!f.IsStatic&&f.Type is TypeDefSig&&
                ReferenceEquals(f.Type.Definition,callee.DeclaringType)).ToArray();
            if(fields.Length==0||IntArg(call,1) is not {} arg||
                ArrayArgumentOwner(arg,4*program.Model.Image.PointerSize,out Node? array,out long fieldOffset) is not {} owner||
                array==null||owner.Block==null||array.Block==null||owner.Dead||array.Dead)
                continue;
            var arrayFields=callee.DeclaringType.Fields.Where(f=>!f.IsStatic&&f.Offset==fieldOffset&&
                f.Type is SzArraySig s&&s.ElementType.Key==parameter.Key).ToArray();
            var origins=fields.Where(f=>IsThisFieldValue(owner,self,f.Offset)).ToArray();
            if(origins.Length!=1||arrayFields.Length!=1)continue;
            // The exact same object is already dereferenced by the original
            // array-field read; the value is kept in SSA, not reloaded.
            cfg??=new Cfg(_fn);
            if(!cfg.Dominates(owner.Block,array.Block)||!cfg.Dominates(array.Block,block)||
                (array.Block==block&&block.Nodes.IndexOf(array)>=block.Nodes.IndexOf(call)))continue;
            if(program.RangeOf(ci.Target) is not {} range||
                !Arm64ReceiverProof.IsUnused(program.Model.Image,range.Start,range.End))continue;
            int index=ci.Slots.FindIndex(s=>s.Kind==ArgSlotKind.IntReg&&s.Index==0);
            if(index<0||index>=call.In.Length||ReferenceEquals(call.In[index],owner))continue;
            call.In[index]=owner;
            _result.ReceiverNotes.Add($"array argument receiver at 0x{call.Addr:X} to 0x{ci.Target:X} via {caller.DeclaringType.ReflectionName}::{origins[0].Name}->{callee.DeclaringType.ReflectionName}::{arrayFields[0].Name}");
        }
    }
}
