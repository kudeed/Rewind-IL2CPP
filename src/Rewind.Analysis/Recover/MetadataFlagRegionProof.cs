using Rewind.Analysis.Ir;
using Rewind.Binary;

namespace Rewind.Analysis.Recover;

/// <summary>Recognizes a metadata-only cold arm, including register spills and a reload of that class's static-field pointer.</summary>
public static class MetadataFlagRegionProof
{
    // Optimized loops can carry the private initialization byte in a register:
    // phi(load(flag), 1, phi(...)). Require every leaf to be that exact byte or
    // the initialized value, and require a real load rather than a pure cycle.
    private static bool GuardFlag(Function fn, Node condition, out Node load, out bool initializedTrue)
    {
        if (Normalizer.FlagCondition(condition, out load, out initializedTrue)) return true;
        load = null!;
        initializedTrue = false;
        if (condition.Op is not (Op.CmpEq or Op.CmpNe) || condition.In.Length != 2) return false;
        Node value = condition.In[0], zero = condition.In[1];
        if (value.IsConstValue(0)) (value, zero) = (zero, value);
        if (!zero.IsConstValue(0)) return false;
        var pending = new Stack<Node>();
        var seen = new HashSet<Node>();
        pending.Push(value);
        ulong? address = null;
        while (pending.Count != 0)
        {
            Node n = pending.Pop();
            if (!seen.Add(n)) continue;
            if (seen.Count > 128) return false;
            if (Normalizer.FlagConstant(n, out ulong literal) && literal == 1) continue;
            if (n.Op == Op.Phi && n.In.Length != 0 && n.Type.IsInt())
            {
                foreach (Node input in n.In) pending.Push(input);
            }
            else if (n.Op is Op.ZExt or Op.Trunc && n.In.Length == 1 && n.In[0].Type.IsInt() && n.Type.Bits() >= 8)
                pending.Push(n.In[0]);
            else if (n is { Op: Op.Load, Type: VT.I8, In.Length: 1 } &&
                StableMetadataPagePhiProof.TryAddress(fn, n.In[0], out ulong at))
            {
                if (address != null && address != at) return false;
                address = at;
                load = n;
            }
            else return false;
        }
        initializedTrue = condition.Op == Op.CmpNe;
        return load != null;
    }

    public static bool TryProve(Function fn, Block guard, NativeImage image, Func<ulong,bool> metadataInit,
        Func<ulong,bool> metadataSlot, int staticFieldsOffset, out Node flag, out Node store, out ulong address)
    {
        flag=null!;store=null!;address=0;
        if(image.Arch!=CpuArch.Arm64 || image.Format!=ImageFormat.Elf || staticFieldsOffset<=0 ||
            guard.Terminator is not {Op:Op.Branch,In.Length:1} term || guard.Succs.Count!=2 ||
            guard.Scope!=-1 && (guard.Scope<0 || (guard.Scope&1)!=0 || !fn.TryRegions.Any(r=>r.Index==guard.Scope/2)) ||
            !GuardFlag(fn,term.In[0],out var read,out bool initializedTrue) ||
            !StableMetadataPagePhiProof.TryAddress(fn,read.In[0],out ulong va) || metadataSlot(va) ||
            image.SectionAt(va) is not {IsWritable:true,IsExecutable:false})return false;
        // Preserve all native exception boundaries. A metadata-only arm may be
        // inside one real try body, but never a handler or a scope transition.
        var cold=guard.Succs[initializedTrue?1:0];var warm=guard.Succs[initializedTrue?0:1];
        if(cold==warm || warm.Scope!=guard.Scope)return false;
        var chain=new List<Block>();Block previous=guard,current=cold;
        while(current!=warm)
        {
            if(chain.Count>=8 || current==fn.Entry || current==guard || chain.Contains(current) ||
                current.Scope!=guard.Scope || current.Preds.Count!=1 || current.Preds[0]!=previous ||
                current.Phis.Any(n=>!n.Dead) || current.Succs.Count!=1 || current.Terminator?.Op!=Op.Jump)return false;
            chain.Add(current);previous=current;current=current.Succs[0];
        }
        var nodes=chain.SelectMany(b=>b.Nodes).Where(n=>!n.Dead).ToArray();
        var calls=nodes.Where(n=>n.Op==Op.Call).ToArray();
        bool MarkOne(Node n)=>Normalizer.FlagConstant(n,out ulong markValue) && markValue==1 ||
            n is {Op:Op.Trunc,Type:VT.I8,In.Length:1} && n.In[0].Type==VT.I64 &&
            StableMetadataPagePhiProof.TryValue(fn,n.In[0],out ulong carriedValue) && carriedValue==1;
        var marks=nodes.Where(n=>n is {Op:Op.Store,In.Length:2} && n.In[1].Type==VT.I8 && StableMetadataPagePhiProof.TryAddress(fn,n.In[0],out ulong storedAddress) && storedAddress==va && MarkOne(n.In[1])).ToArray();
        if(calls.Length is <1 or >16 || marks.Length!=1 || calls.Any(call=>
            call.Aux is not CallInfo {Indirect:false,Intrinsic:null,NoReturn:false} ci || !metadataInit(ci.Target) ||
            Array.IndexOf(nodes,call)>=Array.IndexOf(nodes,marks[0])))return false;
        var mark=marks[0];
        bool Slot(Node n,out ulong slot,int depth=0)
        {
            slot=0;if(depth>8)return false;
            if(StableMetadataPagePhiProof.TryValue(fn,n,out slot))return metadataSlot(slot);
            if(n is {Op:Op.Load,Type:VT.I64,In.Length:1} && Normalizer.FlagConstant(n.In[0],out ulong got))
                return MetadataGotLoad.TryResolve(image,got,metadataSlot,out slot);
            if(n.Op!=Op.Phi || n.In.Length==0)return false;
            ulong exact=0;bool first=true;
            foreach(var input in n.In)
            {
                if(ReferenceEquals(input,n) || !Slot(input,out ulong value,depth+1) || !first && value!=exact)return false;
                exact=value;first=false;
            }
            slot=exact;return true;
        }
        var initializedSlots=new HashSet<ulong>();
        foreach(var call in calls)
        {
            var arg=Normalizer.IntArg(call,0);
            if(arg==null || !Slot(arg,out ulong initializedSlot))return false;
            initializedSlots.Add(initializedSlot);
        }
        fn.Params.TryGetValue(fn.Regs.StackPointer,out var sp);
        bool StackOffset(Node n,out long offset,int depth=0)
        {
            offset=0;if(depth>8 || sp==null)return false;
            if(ReferenceEquals(n,sp))return true;
            if(n.Op!=Op.Add || n.Type!=VT.I64 || n.In.Length!=2 || !Normalizer.FlagConstant(n.In[1],out ulong delta) ||
                !StackOffset(n.In[0],out long before,depth+1))return false;
            offset=unchecked(before+(long)delta);return true;
        }
        bool Stack(Node n)=>StackOffset(n,out long offset) && offset is >= -65536 and < 0;
        bool Class(Node n)=>n is {Op:Op.Load,Type:VT.I64,In.Length:1} && Slot(n.In[0],out ulong slot) && initializedSlots.Contains(slot);
        bool StaticAddress(Node n)=>n is {Op:Op.Add,Type:VT.I64,In.Length:2} && Class(n.In[0]) &&
            Normalizer.FlagConstant(n.In[1],out ulong offset) && offset==(ulong)staticFieldsOffset;
        foreach(var n in nodes)
        {
            switch(n.Op)
            {
                case Op.Call:case Op.Jump:case Op.Const:case Op.Proj:
                case Op.ZExt:case Op.Trunc:case Op.Concat:case Op.BitsToF:case Op.FToBits:break;
                case Op.ShrU:
                    if(n.In.Length!=2 || !n.In[1].IsConstValue(32))return false;
                    break;
                case Op.Add:
                    if(!StableMetadataPagePhiProof.TryAddress(fn,n,out _) && !Stack(n) && !StaticAddress(n))return false;
                    break;
                case Op.Store:
                    if(!ReferenceEquals(n,mark) && (n.In.Length!=2 || !Stack(n.In[0])))return false;
                    break;
                case Op.Load:
                    if(calls.Any(call=>n.Addr==call.Addr))break; // Speculative ABI reads attached to the identified unary service.
                    if(n.In.Length!=1 || !(Stack(n.In[0]) || Class(n) || n.Type==VT.I64 && StaticAddress(n.In[0]) ||
                        n.Type==VT.I64 && Slot(n,out _)))return false;
                    break;
                default:return false;
            }
        }
        if(!image.IsMapped(read.Addr,4) || !image.IsMapped(mark.Addr,4) ||
            (image.U32(read.Addr)&0xffc00000u)!=0x39400000u || (image.U32(mark.Addr)&0xffc00000u)!=0x39000000u)return false;
        flag=read;store=mark;address=va;return true;
    }
}
