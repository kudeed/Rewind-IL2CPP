using Rewind.Analysis.Ir;
using Rewind.Analysis.Runtime;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

public sealed partial class Normalizer
{
    // Native addresses can remain Add(Const page, Const offset) until late
    // SSA folding. Do not extend this to arbitrary pointer expressions.
    internal static bool FlagConstant(Node n, out ulong value,int depth=0)
    {
        value=0;
        if(depth>8)return false;
        if(n.IsConst){value=n.UImm;return true;}
        // A merge denotes a constant only when every incoming value proves
        // the same integer bit pattern at the same width. Unknown values and
        // cycles remain unproven; the depth limit also bounds mutual cycles.
        if(n.Op==Op.Phi&&n.Type.IsInt()&&n.In.Length>0)
        {
            ulong exact=0;bool first=true;
            foreach(var input in n.In)
            {
                if(ReferenceEquals(input,n)||input.Type!=n.Type||
                   !FlagConstant(input,out ulong incoming,depth+1)||!first&&incoming!=exact)
                    return false;
                exact=incoming;first=false;
            }
            value=exact;return true;
        }
        if(n.Op==Op.Add&&n.Type==VT.I64&&n.In.Length==2&&
           FlagConstant(n.In[0],out ulong a,depth+1)&&FlagConstant(n.In[1],out ulong b,depth+1))
        {value=unchecked(a+b);return true;}
        if(n.Op is Op.Trunc or Op.ZExt&&n.In.Length==1&&FlagConstant(n.In[0],out ulong v,depth+1))
        {value=v&n.Type.Mask();return true;}
        return false;
    }

    internal static bool FlagCondition(Node cond,out Node load,out bool initializedTrue)
    {
        load=null!;initializedTrue=false;
        if(cond.Op is not(Op.CmpEq or Op.CmpNe)||cond.In.Length!=2)return false;
        var a=cond.In[0];var b=cond.In[1];
        if(a.IsConstValue(0))(a,b)=(b,a);
        if(!b.IsConstValue(0))return false;
        if(a.Op==Op.ZExt&&a.In.Length==1)a=a.In[0];
        if(a is not{Op:Op.Load,Type:VT.I8,In.Length:1})return false;
        load=a;initializedTrue=cond.Op==Op.CmpNe;return true;
    }

    internal static bool FlagStore(Node n,ulong address)
        =>n is {Op:Op.Store,In.Length:2}&&n.In[1].Type==VT.I8&&
          FlagConstant(n.In[0],out ulong va)&&va==address&&
          FlagConstant(n.In[1],out ulong v)&&v==1;

    // Validate the cold arm while its real metadata initializer still exists.
    // The generated code performs only metadata initialization and marks
    // its private byte. Managed metadata resolution owns these operations.
    private void FoldLateMetadataFlags()
    {
        if(Environment.GetEnvironmentVariable("REWIND_NO_PROVEN_LATE_METADATA_FLAGS")!=null||
           program.Model.Image.Arch!=CpuArch.Arm64||
           program.Model.Image.Format!=ImageFormat.Elf)return;
        var image=program.Model.Image;
        int sites=0;
        foreach(var guard in _fn.Blocks.ToArray())
        {
            // Preserve the existing metadata normalization order. Canonicalize
            // only a flag whose native cold arm is independently proven to be
            // one unary metadata initializer plus private register spills and
            // reloads of that exact class's static-field pointer. The existing
            // initializer removal handles the now-literal byte addresses.
            if (MetadataFlagRegionProof.TryProve(_fn, guard, image,
                target => program.Helpers.KindAt(target) == HelperKind.MetadataInit,
                IsMetadataSlot, program.Klass.StaticFields, out var provenFlag, out var provenStore, out ulong provenAddress))
            {
                provenFlag.In[0] = _b.Const(VT.I64, unchecked((long)provenAddress));
                provenStore.In[0] = _b.Const(VT.I64, unchecked((long)provenAddress));
                provenStore.In[1] = _b.Const(VT.I8, 1);
                // Other reads can feed a register-carried loop flag. They
                // name the same proven private byte, even before constant
                // folding simplifies their page/address expressions.
                foreach (Block block in _fn.Blocks)
                    foreach (Node read in block.Nodes)
                        if (!read.Dead && read is { Op: Op.Load, Type: VT.I8, In.Length: 1 } &&
                            StableMetadataPagePhiProof.TryAddress(_fn, read.In[0], out ulong same) && same == provenAddress)
                            read.In[0] = _b.Const(VT.I64, unchecked((long)provenAddress));
                sites++;
                continue;
            }
            if(guard.Terminator is not{Op:Op.Branch,In.Length:1} term||guard.Succs.Count!=2||
               !FlagCondition(term.In[0],out var flag,out bool initializedTrue)||flag.Block!=guard||
               !FlagConstant(flag.In[0],out ulong address)||IsMetadataSlot(address)||
               image.SectionAt(address) is not{IsWritable:true,IsExecutable:false})continue;
            var warm=guard.Succs[initializedTrue?0:1];
            var cold=guard.Succs[initializedTrue?1:0];
            if(cold==warm||cold==_fn.Entry||cold.Preds.Count!=1||cold.Preds[0]!=guard||
               cold.Phis.Any(n=>!n.Dead)||cold.Succs.Count!=1||cold.Succs[0]!=warm||
               cold.Terminator?.Op!=Op.Jump||guard.Scope!=-1||cold.Scope!=-1||warm.Scope!=-1)continue;
            var stores=cold.Nodes.Where(n=>!n.Dead&&n.Op==Op.Store).ToArray();
            var calls=cold.Nodes.Where(n=>!n.Dead&&n.Op==Op.Call).ToArray();
            if(stores.Length!=1||calls.Length!=1||!FlagStore(stores[0],address)||
               cold.Nodes.IndexOf(calls[0])>=cold.Nodes.IndexOf(stores[0])||
               HelperOf(calls[0])!=HelperKind.MetadataInit)continue;
            var store=stores[0];var call=calls[0];
            // This pass covers only cases missed by the earlier constant-byte
            // pattern; do not perturb existing simple proven outputs.
            if(flag.In[0].IsConst&&store.In[0].IsConst&&store.In[1].IsConst)continue;
            var arg=IntArg(call,0);
            bool Slot(Node? n)
            {
                if(n==null)return false;
                if(FlagConstant(n,out ulong slot))return IsMetadataSlot(slot);
                return n is {Op:Op.Load,Type:VT.I64,In.Length:1}&&
                    FlagConstant(n.In[0],out ulong got)&&
                    MetadataGotLoad.TryResolve(image,got,IsMetadataSlot,out _);
            }
            if(!Slot(arg))continue;
            // Extra IR loads at the call address are the lifter's speculative
            // ABI argument reads, not native instructions. Any other load
            // must be a proven RELRO metadata pointer read.
            bool SafeRead(Node n)=>n.Addr==call.Addr||
                n.Type==VT.I64&&FlagConstant(n.In[0],out ulong got)&&
                MetadataGotLoad.TryResolve(image,got,IsMetadataSlot,out _);
            if(cold.Nodes.Any(n=>!n.Dead&&n.Op==Op.Load&&!SafeRead(n)))continue;
            if(!image.IsMapped(flag.Addr,4)||!image.IsMapped(store.Addr,4)||
               (image.U32(flag.Addr)&0xffc00000u)!=0x39400000u||
               (image.U32(store.Addr)&0xffc00000u)!=0x39000000u)continue;
            term.In[0]=_b.Const(VT.I1,initializedTrue?1:0);
            sites++;
        }
        if(sites>0)_result.ReceiverNotes.Add($"proven late metadata initialization guards: {sites} sites");
    }
}
