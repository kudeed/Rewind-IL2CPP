using Rewind.Analysis.Abi;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Ir;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Analysis.Passes;

/// <summary>Reuses an already loaded, already dereferenced captured owner for an exact direct callee that never reads incoming x0.</summary>
public static class CapturedOwnerReceivers
{
    public static int Run(ProgramAnalysis program,Function fn,MethodDef caller,MethodAbi abi,Action<string> note)
    {
        var model=program.Model;
        if(model.Image.Arch!=CpuArch.Arm64||fn.TryRegions.Count!=0||fn.Blocks.Count==0||
           fn.Blocks.Any(b=>b.Scope!=-1)||caller.IsStatic||caller.IsConstructor||caller.IsGenericDefinition||
           caller.DeclaringType is not {IsValueType:false,IsGenericDefinition:false} state||abi.This is not {Position:0,Pass:PassKind.Integer}||
           !fn.Params.TryGetValue(fn.Regs.IntArgs[0],out Node? incoming))return 0;
        int changed=0;var proofs=new Dictionary<ulong,bool>();
        foreach(Node call in fn.Blocks.SelectMany(b=>b.Nodes))
        {
            if(call.Dead||call.Op is not (Op.Call or Op.TailCall)||
               call.Aux is not CallInfo {Indirect:false,Intrinsic:null,NoReturn:false} info||
               !model.MethodsByAddress.TryGetValue(info.Target,out var targets)||targets.Count!=1||
               model.InstsByAddress.ContainsKey(info.Target))continue;
            MethodDef callee=targets[0];
            if(callee.IsStatic||callee.IsConstructor||callee.IsVirtual||callee.IsAbstract||callee.IsGenericDefinition||
               callee.DeclaringType.IsValueType||callee.DeclaringType.IsGenericDefinition||
               callee.Address!=info.Target||program.RangeOf(info.Target) is not {} range)continue;
            TypeDef owner=callee.DeclaringType;
            bool same=ReferenceEquals(owner,state),captured=ReferenceEquals(owner,state.DeclaringType);
            if(!same&&!captured)continue;
            var fields=program.Layouts.Of(owner.Sig).Fields.Where(f=>!f.Field.IsStatic&&!f.Field.IsLiteral).Select(f=>(f.Offset,f.Size)).ToArray();
            var receiverSlots=info.Slots.Select((slot,index)=>(slot,index)).Where(x=>x.slot.Kind==ArgSlotKind.IntReg&&x.slot.Index==0).ToArray();
            if(receiverSlots.Length!=1||receiverSlots[0].index>=call.In.Length)continue;
            int index=receiverSlots[0].index;
            // The duplicate must be retained by an exact original reference argument ABI slot.
            // Return type and other parameters do not affect that preserved evaluation.
            Node? duplicate=null;
            MethodAbi targetAbi=program.Abi.For(callee,[],[]);
            if(targetAbi.Known&&targetAbi.This is {Position:0,Pass:PassKind.Integer})
                foreach(var parameter in targetAbi.Params)
                {
                    if(parameter.Role!=ParamRole.Argument||parameter.Pass!=PassKind.Integer||parameter.Count!=1||
                       parameter.Position is <1 or >7||parameter.Type?.Definition is not {IsValueType:false})continue;
                    var slots=info.Slots.Select((slot,at)=>(slot,at)).Where(x=>x.slot.Kind==ArgSlotKind.IntReg&&x.slot.Index==parameter.Position).ToArray();
                    if(slots.Length==1&&slots[0].at<call.In.Length&&ReferenceEquals(call.In[slots[0].at],call.In[index]))duplicate=call.In[index];
                }
            Node? held;string origin;
            if(same)
            {
                held=FindOwn(fn,call,call.In[index],incoming,fields,duplicate);origin=state.ReflectionName+"::this";
            }
            else
            {
                var captures=state.Fields.Where(f=>!f.IsStatic&&!f.IsLiteral&&f.Type is TypeDefSig type&&ReferenceEquals(type.Definition,owner)).ToArray();
                if(captures.Length!=1||captures[0].Offset is <16 or >4096||captures[0].Offset%8!=0)continue;
                held=Find(fn,call,call.In[index],incoming,captures[0].Offset,fields,
                    leaf=>model.ResolveUsageSlot((ulong)leaf.Imm) is {Kind:UsageKind.TypeInfo,Type:TypeDefSig},duplicate);
                origin=state.ReflectionName+"::"+captures[0].Name;
            }
            if(held==null||ReferenceEquals(held,call.In[index]))continue;
            if(!proofs.TryGetValue(info.Target,out bool unused))
            {
                unused=Arm64ReceiverProof.IsUnused(model.Image,range.Start,range.End);proofs.Add(info.Target,unused);
            }
            if(!unused)continue;
            call.In[index]=held;changed++;
            note($"receiver-independent captured owner at 0x{call.Addr:X} to 0x{callee.Address:X} via {origin}");
        }
        if(changed!=0)DeadCode.Run(fn);
        return changed;
    }

    /// <summary>The caller proves exact metadata field identities and callee entry independence separately. This proof adds no load, call, cast or null check.</summary>
    public static Node? Find(Function fn,Node call,Node receiver,Node incoming,int captureOffset,
        IReadOnlyList<(int Offset,int Size)> fields,Func<Node,bool> isKnownClass,Node? duplicateReference=null)
    {
        if(fn.Blocks.Count==0||fn.TryRegions.Count!=0||fn.Blocks.Any(b=>b.Scope!=-1)||
           call.Dead||call.Op is not (Op.Call or Op.TailCall)||call.Block==null||!fn.Blocks.Contains(call.Block)||
           !call.Block.Nodes.Contains(call)||incoming.Dead||incoming.Op!=Op.Param||incoming.Type!=VT.I64||
           receiver.Dead||receiver.Type!=VT.I64||captureOffset is <16 or >4096||captureOffset%8!=0||fields.Count==0)return null;
        var cfg=new Cfg(fn);
        if(!cfg.IsReachable(call.Block))return null;
        bool Before(Node a,Node b)=>a.Block!=null&&b.Block!=null&&cfg.IsReachable(a.Block)&&
            (a.Block==b.Block?a.Block.Nodes.IndexOf(a)>=0&&a.Block.Nodes.IndexOf(a)<a.Block.Nodes.IndexOf(b):cfg.Dominates(a.Block,b.Block));
        static bool Address(Node address,Node basis,int offset)=>address is {Dead:false,Op:Op.Add,Type:VT.I64,In.Length:2}&&
            (ReferenceEquals(address.In[0],basis)&&address.In[1].IsConstValue(offset)||ReferenceEquals(address.In[1],basis)&&address.In[0].IsConstValue(offset));
        var held=fn.Blocks.SelectMany(b=>b.Nodes).Where(n=>!n.Dead&&n.Op==Op.Load&&n.Type==VT.I64&&n.In.Length==1&&Address(n.In[0],incoming,captureOffset)&&Before(n,call)).ToArray();
        if(held.Length!=1)return null;
        Node owner=held[0];
        if(!ReferenceEquals(receiver,duplicateReference)&&!Ignored(receiver,owner,isKnownClass))return null;
        foreach(Node witness in fn.Blocks.SelectMany(b=>b.Nodes))
        {
            if(witness.Dead||witness.Op!=Op.Load||witness.In.Length!=1||!Before(owner,witness)||!Before(witness,call))continue;
            int width=witness.Type.Bytes();
            if(width<=0)continue;
            foreach(var field in fields)
            {
                // A complete ordinary recorded field read proves that the very same owner was nonnull.
                if(field.Offset<16||field.Offset>4096||field.Size!=width||!Address(witness.In[0],owner,field.Offset))continue;
                return owner;
            }
        }
        return null;
    }

    /// <summary>A stale reference duplicated as the sole explicit argument stays evaluated there; reuse only the already dereferenced incoming instance.</summary>
    public static Node? FindOwn(Function fn,Node call,Node receiver,Node incoming,
        IReadOnlyList<(int Offset,int Size)> fields,Node? duplicateReference)
    {
        if(!ReferenceEquals(receiver,duplicateReference)||fn.Blocks.Count==0||fn.TryRegions.Count!=0||fn.Blocks.Any(b=>b.Scope!=-1)||
           incoming.Dead||incoming.Op!=Op.Param||incoming.Type!=VT.I64||receiver.Dead||receiver.Type!=VT.I64||
           call.Dead||call.Op is not (Op.Call or Op.TailCall)||call.Block==null||!fn.Blocks.Contains(call.Block)||!call.Block.Nodes.Contains(call))return null;
        var cfg=new Cfg(fn);if(!cfg.IsReachable(call.Block))return null;
        foreach(Node witness in fn.Blocks.SelectMany(b=>b.Nodes))
        {
            if(witness.Dead||witness.Op!=Op.Load||witness.In.Length!=1||witness.Block==null||!cfg.IsReachable(witness.Block)||
               !(witness.Block==call.Block?witness.Block.Nodes.IndexOf(witness)<witness.Block.Nodes.IndexOf(call):cfg.Dominates(witness.Block,call.Block)))continue;
            Node address=witness.In[0];
            if(address.Dead||address.Op!=Op.Add||address.Type!=VT.I64||address.In.Length!=2)continue;
            foreach(var field in fields)
            {
                if(field.Offset<16||field.Offset>4096||field.Size<=0||field.Size!=witness.Type.Bytes())continue;
                if(ReferenceEquals(address.In[0],incoming)&&address.In[1].IsConstValue(field.Offset)||ReferenceEquals(address.In[1],incoming)&&address.In[0].IsConstValue(field.Offset))return incoming;
            }
        }
        return null;
    }

    private static bool Ignored(Node receiver,Node owner,Func<Node,bool> isKnownClass)
    {
        var active=new HashSet<Node>();var complete=new HashSet<Node>();var work=new Stack<(Node Node,bool Exit)>();work.Push((receiver,false));
        while(work.TryPop(out var item))
        {
            Node n=item.Node;
            if(item.Exit){active.Remove(n);complete.Add(n);continue;}
            if(n.Dead)return false;
            if(ReferenceEquals(n,owner)||(n.IsConstValue(0)||n.Op==Op.Undef)&&n.Type is VT.I32 or VT.I64)continue;
            if(n.Op==Op.SlotValue&&n.Type==VT.I64&&isKnownClass(n))continue;
            if(complete.Contains(n))continue;
            bool extension=n.Op==Op.ZExt&&n.Type==VT.I64&&n.In.Length==1&&n.In[0].Type==VT.I32;
            bool phi=n.Op==Op.Phi&&n.Type is VT.I32 or VT.I64&&n.In.Length>=2&&n.In.All(input=>input.Type==n.Type);
            if((!extension&&!phi)||!active.Add(n))return false;
            work.Push((n,true));for(int i=n.In.Length-1;i>=0;i--)work.Push((n.In[i],false));
        }
        return true;
    }
}
