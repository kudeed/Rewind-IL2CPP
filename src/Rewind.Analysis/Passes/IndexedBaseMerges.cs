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
        if(b.Scope!=-1||b.Preds.Count!=2||phi.Dead||phi.Op!=Op.Phi||phi.Type!=VT.I64||phi.In.Length!=2||
           b.Terminator?.Op!=Op.Jump||b.Nodes.Count(n=>!n.Dead&&n.IsEffect&&!n.IsTerminator)!=1)return false;
        var a=phi.In[0];var c=phi.In[1];
        bool Shape(Node root,Node indexed)=>root.Type==VT.I64&&indexed is {Op:Op.Add,Type:VT.I64,In.Length:2}&&
           ReferenceEquals(root,indexed.In[0])&&indexed.In[1] is {Op:Op.Shl,Type:VT.I64,In.Length:2} shift&&shift.In[1].IsConstValue(3);
        if(!Shape(a,c)&&!Shape(c,a))return false;
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
