using Rewind.Analysis.Abi;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Runtime;
using Rewind.Binary;

namespace Rewind.Analysis.Recover;

public sealed partial class Normalizer
{
    // v39 MethodInfo::rgctx_data lazy initialization followed by the same
    // null-reference branch on each arm. Exact machine proof of the slow
    // helper and its method descriptor argument; no unrelated guards removed.
    internal static bool OwnRgctxGuardCode(NativeImage image,ulong pc,int info,int arg,Func<ulong,bool> helper)
    {
        if(info is <0 or >7||arg is <0 or >7||arg==info||pc<12||
           !image.TrySpan(pc-12,20,out _))return false;
        uint load=image.U32(pc-12),saveInfo=image.U32(pc-8),saveArg=image.U32(pc-4),branch=image.U32(pc),warm=image.U32(pc+4);
        uint r=load&31,mi=saveInfo&31,a=saveArg&31;
        if(r==31||mi is <19 or >28||a is <19 or >28||a==mi||r==mi||r==a||
           load!=(0xf9400000u|(7u<<10)|((uint)info<<5)|r)||
           saveInfo!=(0xaa0003e0u|((uint)info<<16)|mi)||saveArg!=(0xaa0003e0u|((uint)arg<<16)|a)||
           (branch&0xff00001fu)!=(0xb4000000u|r)||(warm&0xff00001fu)!=(0xb4000000u|a))return false;
        static ulong Dest(ulong at,uint word)=>unchecked((ulong)((long)at+((long)(int)(word<<8)>>13)*4));
        ulong cold=Dest(pc,branch),nil=Dest(pc+4,warm),common=pc+8;
        if(cold<=common||!image.TrySpan(cold,12,out _)||cold+12!=nil)return false;
        uint move=image.U32(cold),call=image.U32(cold+4),test=image.U32(cold+8);
        if(move!=(0xaa0003e0u|(mi<<16))||(call&0xfc000000u)!=0x94000000u||
           (test&0xff00001fu)!=(0xb5000000u|a)||Dest(cold+8,test)!=common)return false;
        ulong target=unchecked((ulong)((long)(cold+4)+((long)(int)(call<<6)>>6)*4));
        return helper(target);
    }

    internal void FoldOwnMethodRgctx(Function fn,MethodAbi abi)
    {
        if(Environment.GetEnvironmentVariable("REWIND_NO_OWN_METHOD_RGCTX")!=null||
           program.Model.Image.Arch!=CpuArch.Arm64||program.Model.Version!=Rewind.Metadata.MetaVersion.V39||
           fn.TryRegions.Count!=0||abi.Params.SingleOrDefault(p=>p.Role==ParamRole.MethodInfo) is not {} mi||
           abi.Params.Count(p=>p.Role==ParamRole.Argument)!=1||
           abi.Params.Single(p=>p.Role==ParamRole.Argument) is not {Pass:PassKind.Integer,Type:{IsValueType:false}} arg||
           fn.Regs.IsStackPosition(mi.Position)||fn.Regs.IsStackPosition(arg.Position))return;
        int infoReg=fn.Regs.IntRegisterOf(mi.Position),argReg=fn.Regs.IntRegisterOf(arg.Position);
        if(infoReg is <0 or >7||argReg is <0 or >7||
           !fn.Params.TryGetValue(fn.Regs.IntArgs[infoReg],out var info)||
           !fn.Params.TryGetValue(fn.Regs.IntArgs[argReg],out var value))return;
        var image=program.Model.Image;var b=fn.Entry;
        if(b.Terminator is not{Op:Op.Branch,In.Length:1} term||b.Succs.Count!=2||
           term.In[0] is not{Op:Op.CmpEq,In.Length:2} eq||!eq.In[1].IsConstValue(0)||
           eq.In[0] is not{Op:Op.Load,Type:VT.I64,In:[{Op:Op.Add,In.Length:2} address]}||
           address.In[0]!=info||!address.In[1].IsConstValue(56)||
           !OwnRgctxGuardCode(image,term.Addr,infoReg,argReg,x=>program.Helpers.KindAt(x)==HelperKind.RgctxInitSlow))return;
        var cold=b.Succs[0];var warm=b.Succs[1];
        if(cold.Preds.Count!=1||warm.Preds.Count!=1||cold.Succs.Count!=2||warm.Succs.Count!=2||
           cold.Succs[0]!=warm.Succs[1]||cold.Succs[1]!=warm.Succs[0]||
           warm.Terminator is not{Op:Op.Branch,In:[{Op:Op.CmpEq,In.Length:2} w]}||
           cold.Terminator is not{Op:Op.Branch,In:[{Op:Op.CmpNe,In.Length:2} c]}||
           w.In[0]!=value||c.In[0]!=value||!w.In[1].IsConstValue(0)||!c.In[1].IsConstValue(0)||
           cold.Nodes.Any(n=>!n.Dead&&n.IsEffect&&n!=cold.Terminator)||
           warm.Nodes.Any(n=>!n.Dead&&n.IsEffect&&n!=warm.Terminator))return;
        var no=fn.NewNode(Op.Const,VT.I1,null);no.Imm=0;term.In[0]=no;
        _result.ReceiverNotes.Add($"own method rgctx initialization at 0x{term.Addr:X}: exact native helper and equivalent null branches");
    }
}
