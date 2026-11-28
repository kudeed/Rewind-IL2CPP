using Rewind.Analysis.Ir;
namespace Rewind.Analysis.Arm64;
public sealed partial class A64Lifter
{
    private static bool IsStackGuardAddress(Node address) =>
        address.Op==Op.Add && address.In.Length==2 && address.In[0] is {Op:Op.Param,Imm:VarTpidr} && address.In[1].IsConstValue(0x28);

    // A register alias can still be an incomplete phi when LoadAt first sees it.
    // Apply the same existing TLS-guard rule after SSA resolves those aliases.
    internal static int FoldResolvedStackGuardReads(Function fn)
    {
        int count=0;
        foreach(Block block in fn.Blocks)
            foreach(Node node in block.Nodes)
                if(!node.Dead && node.Op==Op.Load && node.Type==VT.I64 && node.In.Length==1 && IsStackGuardAddress(node.In[0]))
                {
                    node.Op=Op.Const;node.Imm=StackGuard;node.In=[];node.Aux=null;count++;
                }
        return count;
    }
}
