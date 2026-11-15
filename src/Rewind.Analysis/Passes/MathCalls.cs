using Rewind.Analysis.Ir;
using Rewind.Analysis.Runtime;

namespace Rewind.Analysis.Passes;

/// <summary>
/// Compilers implement <c>sqrt</c> and <c>fabs</c> either as one instruction or as a call into the C runtime,
/// sometimes both in the same function ("use the instruction unless the input is negative"). Both forms compute
/// the same value, so calls are rewritten into the instruction's operation; the two paths then become identical
/// and the branch between them folds away.
/// </summary>
public static class MathCalls
{
    public static void Run(Function fn, RuntimeHelpers helpers)
    {
        var b = new IrBuilder(fn);
        Dictionary<Node, Node>? replace = null;

        foreach (Block block in fn.Blocks)
        {
            for (int i = 0; i < block.Nodes.Count; i++)
            {
                Node call = block.Nodes[i];
                if (call.Op is not (Op.Call or Op.TailCall) || call.Aux is not CallInfo { Indirect: false, Intrinsic: null } info) continue;
                if (helpers.At(info.Target) is not { Kind: HelperKind.MathFunction } helper) continue;
                Op op = helper.MathName switch { "Sqrt" => Op.FSqrt, "Abs" => Op.FAbs, _ => Op.Const };
                if (op == Op.Const) continue;

                Node? lane0 = null, lane1 = null;
                for (int k = 0; k < info.Slots.Count && k < call.In.Length; k++)
                {
                    if (info.Slots[k].Kind != ArgSlotKind.FloatReg) continue;
                    if (info.Slots[k].Index == 0) lane0 = call.In[k];
                    else if (info.Slots[k].Index == 1) lane1 = call.In[k];
                }
                if (lane0 == null || (helper.IsDouble && lane1 == null)) continue;

                b.PositionBefore(block, call);
                Node out0, out1;
                if (helper.IsDouble)
                {
                    Node value = b.Raw(op, VT.F64, b.BitsToF(b.Concat(lane1!, lane0)));
                    Node bits = b.FToBits(value);
                    out0 = b.Trunc(bits, VT.I32);
                    out1 = b.Trunc(b.Shift(Op.ShrU, bits, b.Const(VT.I8, 32)), VT.I32);
                }
                else
                {
                    Node value = b.Raw(op, VT.F32, b.BitsToF(lane0));
                    out0 = b.FToBits(value);
                    out1 = b.Undef(VT.I32);
                }
                i = block.Nodes.IndexOf(call);

                if (call.Op == Op.TailCall)
                {
                    // "jmp sqrt": the function returns what the operation produced.
                    call.Op = Op.Return;
                    call.Aux = null;
                    call.In = [b.Undef(VT.I64), out0, out1];
                    continue;
                }

                replace ??= [];
                call.Dead = true;
                for (int k = i + 1; k < block.Nodes.Count && block.Nodes[k].Op == Op.Proj && ReferenceEquals(block.Nodes[k].In[0], call); k++)
                {
                    Node proj = block.Nodes[k];
                    proj.Dead = true;
                    replace[proj] = proj.Imm switch
                    {
                        CallResult.FloatLane0 => out0,
                        CallResult.FloatLane1 => out1,
                        _ => b.Undef(proj.Type),
                    };
                }
            }
            block.Nodes.RemoveAll(n => n.Dead);
        }
        b.InsertIndex = -1;

        if (replace == null) return;
        Node Resolve(Node n)
        {
            while (replace.TryGetValue(n, out Node? next)) n = next;
            return n;
        }
        foreach (Block block in fn.Blocks)
        {
            foreach (Node n in block.Phis)
                for (int k = 0; k < n.In.Length; k++) n.In[k] = Resolve(n.In[k]);
            foreach (Node n in block.Nodes)
                for (int k = 0; k < n.In.Length; k++) n.In[k] = Resolve(n.In[k]);
        }
    }
}
