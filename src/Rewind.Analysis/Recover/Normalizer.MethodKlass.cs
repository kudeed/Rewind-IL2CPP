using Rewind.Analysis.Abi;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Runtime;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

public sealed partial class Normalizer
{
    internal static bool OwnMethodKlassLoad(Node n,Node info) =>
        n is {Op:Op.Load,Type:VT.I64,In:[{Op:Op.Add,In.Length:2} a]}&&
        (ReferenceEquals(a.In[0],info)&&a.In[1].IsConstValue(32)||
         ReferenceEquals(a.In[1],info)&&a.In[0].IsConstValue(32));

    internal static bool TryClassInitBranch(uint word,ulong pc,out ulong slow)
    {
        slow=0;
        // TBZ/TBNZ wN,#0; either the branch destination or fallthrough
        // is the actual slow helper call. Match the bit, not the register.
        if((word&0xfef80000u)!=0x36000000u)return false;
        long delta=((long)(int)(word<<13)>>18)*4;
        slow=(word&0x01000000u)!=0?pc+4:unchecked((ulong)((long)pc+delta));
        return true;
    }
    internal void FoldOwnMethodKlass(Function fn,MethodAbi? abi)
    {
        _fn=fn;_b=new IrBuilder(fn);_replace.Clear();
        if(Environment.GetEnvironmentVariable("REWIND_NO_OWN_METHOD_KLASS")!=null||
           program.Model.Image.Arch!=CpuArch.Arm64||program.Model.Version!=Rewind.Metadata.MetaVersion.V39||
           abi==null||_fn.TryRegions.Count!=0||
           abi.Params.SingleOrDefault(p=>p.Role==ParamRole.MethodInfo) is not {} mi||
           _fn.Regs.IsStackPosition(mi.Position)||_fn.Regs.IntRegisterOf(mi.Position) is not (>=0 and <8)||
           !_fn.Params.TryGetValue(_fn.Regs.IntArgs[_fn.Regs.IntRegisterOf(mi.Position)],out Node? info))return;
        var cfg=new Cfg(_fn);
        var loads=cfg.ReversePostOrder.SelectMany(b=>b.Nodes).Where(n=>!n.Dead&&OwnMethodKlassLoad(n,info)).ToArray();
        if(loads.Length<2)return;
        var image=program.Model.Image;
        int guards=0;
        foreach(var b in _fn.Blocks)
        {
            var branch=b.Terminator;
            if(branch is not {Op:Op.Branch,In.Length:1}||b.Succs.Count!=2||
               !image.TrySpan(branch.Addr,4,out _)||
               !TryClassInitBranch(image.U32(branch.Addr),branch.Addr,out ulong slow)||
               slow<fn.Address||slow>=fn.End||!image.TrySpan(slow,4,out _))continue;
            uint call=image.U32(slow);
            if((call&0xfc000000u)!=0x94000000u)continue;
            long delta=((long)(int)(call<<6)>>6)*4;
            if(program.Helpers.KindAt(unchecked((ulong)((long)slow+delta)))!=HelperKind.ClassInitSlow)continue;
            var cond=branch.In[0];
            if(cond.Op is not(Op.CmpEq or Op.CmpNe)||cond.In.Length!=2||!cond.In[1].IsConstValue(0)||
               cond.In[0] is not {Op:Op.And,In.Length:2} and||!and.In[1].IsConstValue(1))continue;
            var read=and.In[0];
            if(read.Op is Op.ZExt or Op.SExt&&read.In.Length==1)read=read.In[0];
            if(read is not {Op:Op.Load,Type:VT.I16,In:[{Op:Op.Add,In.Length:2} offset]}||
               !offset.In[1].IsConstValue(309)||!OwnMethodKlassLoad(offset.In[0],info))continue;
            // Original v39 shape: add xN,x0,#0x135; ldrh wR,[xN];
            // bit-0 test of wR with at most an independent CBZ in between.
            if(read.Addr<fn.Address+4||branch.Addr-read.Addr is not(4 or 8)||
               !image.TrySpan(read.Addr-4,8,out _))continue;
            uint add=image.U32(read.Addr-4),ldr=image.U32(read.Addr),test=image.U32(branch.Addr);
            uint reg=add&31;
            if(reg==31||add!=(0x91000000u|(309u<<10)|reg)||
               ldr!=(0x79400000u|(reg<<5)|(test&31)))continue;
            if(branch.Addr-read.Addr==8)
            {
                uint between=image.U32(read.Addr+4);
                if((between&0x7f000000u)!=0x34000000u||(between&31)==(test&31))continue;
            }
            // The known native slow call initializes that exact class. Only
            // remove the tested bit predicate, not any other reads of flags.
            branch.In[0]=_b.Const(VT.I1,cond.Op==Op.CmpNe?1:0);
            guards++;
        }
        if(guards==0)return;
        // MethodInfo::klass is immutable. Reuse only a dominating load.
        foreach(var n in loads)
        {
            var first=loads.FirstOrDefault(v=>v!=n&&!v.Dead&&v.Block!=null&&n.Block!=null&&
                cfg.Dominates(v.Block,n.Block)&&(v.Block!=n.Block||v.Block.Nodes.IndexOf(v)<n.Block.Nodes.IndexOf(n)));
            if(first!=null){_replace[n]=first;n.Dead=true;}
        }
        ApplyReplacements();
        foreach(var b in _fn.Blocks)b.Nodes.RemoveAll(n=>n.Dead);
        _result.ReceiverNotes.Add($"own method klass initialization: {guards} native guarded sites");
    }
}
