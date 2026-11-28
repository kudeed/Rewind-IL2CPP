using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Recover;

internal static class AlignedStackAddresses
{
    // AAPCS64 keeps entry SP aligned to sixteen bytes. OR with a low-bit mask
    // equals addition only when every bit set by the mask is proven clear.
    internal static int Run(Function fn)
    {
        if (!fn.Params.TryGetValue(fn.Regs.StackPointer, out Node? stack)) return 0;
        long? Offset(Node node, int depth)
        {
            if (depth > 16 || node.Type != VT.I64) return null;
            if (ReferenceEquals(node, stack)) return 0;
            if (node.In.Length != 2) return null;
            Node left = node.In[0], right = node.In[1];
            if (node.Op is Op.Add or Op.Or && left.IsConst && !right.IsConst) (left, right) = (right, left);
            if (!right.IsConst || Offset(left, depth + 1) is not long known) return null;
            return node.Op switch
            {
                Op.Add => unchecked(known + IrBuilder.SImm(right)),
                Op.Sub => unchecked(known - IrBuilder.SImm(right)),
                Op.Or when right.UImm < 16 && ((ulong)known & right.UImm) == 0 => unchecked(known + right.Imm),
                _ => null,
            };
        }
        int changed = 0;
        foreach (Block block in fn.Blocks)
            foreach (Node node in block.Nodes)
            {
                if (node.Dead || node.Op != Op.Or || Offset(node, 0) is not long offset) continue;
                Node constant = fn.NewNode(Op.Const, VT.I64, null); constant.Imm = offset;
                node.Op = Op.Add; node.In = [stack, constant]; changed++;
            }
        return changed;
    }
}
