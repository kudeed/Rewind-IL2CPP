using Rewind.Analysis.Ir;
using Rewind.Analysis.Passes;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>Recover a paired index/interior-pointer induction in a bounded SZARRAY loop.
/// The original pointer never escapes except as the receiver of one typed struct call.
/// Recover that receiver from the same captured array and index, not a raw byte-offset byref.</summary>
internal static class ArrayCursorRecovery
{
    private static bool AddConst(Node n, long value, out Node root)
    {
        root = n;
        if(n.Dead||n.Op!=Op.Add||n.Type!=VT.I64||n.In.Length!=2)return false;
        if(n.In[1].IsConstValue(value)){root=n.In[0];return true;}
        if(n.In[0].IsConstValue(value)){root=n.In[1];return true;}
        return false;
    }

    private static bool Length(Node n, Node array, int at)
    {
        if(n.Op==Op.Trunc&&n.Type==VT.I32&&n.In.Length==1)n=n.In[0];
        return !n.Dead&&n.Op==Op.Load&&(n.Type is VT.I32 or VT.I64)&&n.In.Length==1
            &&AddConst(n.In[0],at,out var owner)&&owner==array;
    }

    // prove: exact captured array's element layout and exact managed receiver call,
    // obtained from the typed builder. A shape alone never authorizes recovery.
    internal static int Run(Function fn,int dataOffset,Func<Node,Node,int?> prove,Action<ulong,int>? note=null)
    {
        if(fn.TryRegions.Count!=0||dataOffset!=32)return 0;
        int changed=0;
        foreach(var head in fn.Blocks)
        {
            if(head.Scope!=-1||head.Preds.Count!=2||head.Succs.Count!=2||
               head.Terminator is not {Op:Op.Branch,In.Length:1} guard||
               guard.In[0] is not {Op:Op.CmpLeU,In.Length:2} compare)continue;
            var body=head.Succs[1];
            if(body==head||body.Scope!=-1||body.Preds.Count!=1||body.Preds[0]!=head||
               body.Succs.Count!=2||body.Succs[0]!=head||
               body.Terminator is not {Op:Op.Branch,In.Length:1} tail||
               tail.In[0] is not {Op:Op.CmpLtS,In.Length:2} bound)continue;
            int back=head.Preds.IndexOf(body);if(back<0)continue;
            var pre=head.Preds[1-back];
            if(pre==head||pre.Scope!=-1||pre.Succs.Count!=1||pre.Succs[0]!=head)continue;
            Node index=compare.In[1];
            if(index.Dead||index.Op!=Op.Phi||index.Type!=VT.I64||index.Block!=head||index.In.Length!=2||
               !index.In[1-back].IsConstValue(0)||!AddConst(index.In[back],1,out var i0)||i0!=index||
               index.In[back].Block!=body||bound.In[0]!=index.In[back])continue;
            if(compare.In[0] is not {Op:Op.ZExt,Type:VT.I64,In.Length:1} z||
               z.In[0] is not {Op:Op.Phi,Type:VT.I32,In.Length:2} len||len.Block!=head||
               bound.In[1] is not {Op:Op.SExt,Type:VT.I64,In.Length:1} signed||
               signed.In[0]!=len.In[back]||len.In[back].Block!=body)continue;
            var uses=DeadCode.Uses(fn);
            foreach(var cursor in head.Phis.ToArray())
            {
                if(cursor.Dead||cursor==index||cursor.Type!=VT.I64||cursor.In.Length!=2||
                   !AddConst(cursor.In[1-back],dataOffset,out var array)||
                   cursor.In[1-back].Block!=pre||cursor.In[back].Block!=body||
                   !Length(len.In[1-back],array,dataOffset-8)||!Length(len.In[back],array,dataOffset-8)||
                   !uses.TryGetValue(cursor,out var us)||us.Count!=2||
                   !uses.TryGetValue(cursor.In[back],out var incUses)||incUses.Count!=1||incUses[0]!=cursor)continue;
                Node increment=cursor.In[back];
                if(increment.Op!=Op.Add||increment.In.Length!=2)continue;
                var constant=increment.In.FirstOrDefault(n=>n.IsConst);
                if(constant==null||constant.Imm is <=0 or >4096||
                   !AddConst(increment,constant.Imm,out var p0)||p0!=cursor)continue;
                if(!us.Contains(increment))continue;
                Node? call=us.FirstOrDefault(n=>n!=increment);
                if(call==null||call.Op!=Op.Call||call.Block!=body||call.Aux is not CallInfo{Indirect:false,Intrinsic:null,NoReturn:false} ci)continue;
                int arg=ci.Slots.FindIndex(s=>s.Kind==ArgSlotKind.IntReg&&s.Index==0);
                if(arg<0||arg>=call.In.Length||call.In[arg]!=cursor||
                   call.In.Count(n=>n==cursor)!=1||prove(array,call)!=constant.Imm)continue;
                // The same captured array must dominate the loop. The checked unsigned
                // header and signed backedge keep i in [0, Int32.MaxValue) at every use.
                var cfg=new Cfg(fn);
                if(array.Block==null||!cfg.Dominates(array.Block,pre)||!cfg.Dominates(pre,head)||
                   (array.Block==pre&&pre.Nodes.IndexOf(array)>=pre.Nodes.IndexOf(cursor.In[1-back])))continue;
                int at=body.Nodes.IndexOf(call);if(at<0)continue;
                Node C(long v){var c=fn.NewNode(Op.Const,VT.I64,null);c.Imm=v;return c;}
                var scaled=fn.NewNode(Op.Mul,VT.I64,body,index,C(constant.Imm));
                var sum=fn.NewNode(Op.Add,VT.I64,body,array,scaled);
                var element=fn.NewNode(Op.Add,VT.I64,body,sum,C(dataOffset));
                body.Nodes.InsertRange(at,[scaled,sum,element]);
                call.In[arg]=element;
                cursor.Dead=true;increment.Dead=true;
                note?.Invoke(call.Addr,(int)constant.Imm);
                changed++;break;
            }
        }
        if(changed!=0)DeadCode.Run(fn);
        return changed;
    }
}
