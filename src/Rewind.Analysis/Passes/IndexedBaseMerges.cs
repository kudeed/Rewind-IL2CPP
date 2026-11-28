using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Passes;

/// <summary>Undo a merge of a base pointer with the same base plus a scaled
/// index when their only use is a fixed-offset load. Keeping the memory read
/// on the selected incoming path permits typed array recovery. Existing
/// ClassMerges checks separability and clones the exact IR, not its guess
/// about a managed type.</summary>
internal static class IndexedBaseMerges
{
    internal static bool Candidate(Block b,Node phi,Dictionary<Node,List<Node>> uses)
    {
        if(b.Scope!=-1||b.Preds.Count is <2 or >4||phi.Dead||phi.Op!=Op.Phi||phi.Type!=VT.I64||phi.In.Length!=b.Preds.Count||
           b.Terminator?.Op!=Op.Jump||b.Nodes.Count(n=>!n.Dead&&n.IsEffect&&!n.IsTerminator)!=1)return false;
        var a=phi.In[0];var c=phi.In[1];
        bool Shape(Node root,Node indexed)=>root.Type==VT.I64&&indexed is {Op:Op.Add,Type:VT.I64,In.Length:2}&&
           ReferenceEquals(root,indexed.In[0])&&indexed.In[1] is {Op:Op.Shl,Type:VT.I64,In.Length:2} shift&&shift.In[1].IsConstValue(3);
        bool same=phi.In.Length==2&&(Shape(a,c)||Shape(c,a));
        // Different arrays may also share the final native element load.
        // Require at least one scaled input and one bare loaded reference;
        // each base must be an actual load or a bounded merge of loads.
        bool Loaded(Node n,int depth=0)=>n.Type==VT.I64&&depth<=4&&
            (n.Op==Op.Load||n.Op==Op.Phi&&n.In.Length is >=2 and <=16&&n.In.All(x=>Loaded(x,depth+1)));
        bool Indexed(Node n)=>n is {Op:Op.Add,Type:VT.I64,In.Length:2}&&Loaded(n.In[0])&&
            n.In[1] is {Op:Op.Shl,Type:VT.I64,In.Length:2} scale&&scale.In[1].IsConstValue(3)&&
            scale.In[0] is {Op:Op.SExt or Op.ZExt,Type:VT.I64,In.Length:1} ext&&ext.In[0].Type==VT.I32;
        bool mixed=Environment.GetEnvironmentVariable("REWIND_NO_MIXED_INDEXED_MERGES")==null&&
            phi.In.Any(n=>Indexed(n))&&phi.In.Any(n=>Loaded(n))&&phi.In.All(n=>Indexed(n)||Loaded(n));
        if(!same&&!mixed)return false;
        if(!uses.TryGetValue(phi,out var pu)||pu.Count!=1||
           pu[0] is not {Op:Op.Add,Type:VT.I64,In.Length:2} address||
           address.Block!=b||!ReferenceEquals(address.In[0],phi)||!address.In[1].IsConstValue(32)||
           !uses.TryGetValue(address,out var au)||au.Count!=1||
           au[0] is not {Op:Op.Load,Type:VT.I64,In.Length:1} load||load.Block!=b)return false;
        return true;
    }
    public static bool Run(Function fn)
    {
        if(Environment.GetEnvironmentVariable("REWIND_NO_INDEXED_BASE_MERGES")!=null||fn.TryRegions.Count!=0)return false;
        var uses=DeadCode.Uses(fn);
        var candidates=fn.Blocks.SelectMany(b=>b.Phis.Where(phi=>Candidate(b,phi,uses))).ToArray();
        return candidates.Length!=0&&ClassMerges.SplitAt(fn,candidates);
    }
}
