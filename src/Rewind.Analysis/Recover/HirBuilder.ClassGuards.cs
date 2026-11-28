using Rewind.Analysis.Ir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

public sealed partial class HirBuilder
{
    // The original class-equality branch remains in the graph, including its original
    // exception edge. Its successful edge must dominate every use of this SSA object.
    private TypeSig? ProvenReferenceClass(Node obj, Block? at)
    {
        if (_cfg == null || at == null || !_cfg.IsReachable(at)) return null;
        Block child = at;
        for (int guard = 0; guard < 64 && _cfg.ImmediateDominator(child) is { } p && p != child; guard++, child = p)
        {
            if (p.Terminator is not { Op: Op.Branch, In.Length: 1 } branch || p.Succs.Count != 2 || p.Succs[0] == p.Succs[1]) continue;
            Node c = branch.In[0];
            if (c.Op is not (Op.CmpEq or Op.CmpNe) || c.In.Length != 2) continue;
            Block same = p.Succs[c.Op == Op.CmpEq ? 0 : 1];
            if (same.Preds.Count != 1 || !_cfg.Dominates(same, at)) continue;
            TypeSig? type = (Eval(c.In[0]), Eval(c.In[1])) switch
            {
                (SObjKlass actual, SKlass expected) when ReferenceEquals(actual.Object, obj) => expected.Type,
                (SKlass expected, SObjKlass actual) when ReferenceEquals(actual.Object, obj) => expected.Type,
                _ => null,
            };
            if (type is TypeDefSig { Definition: { IsValueType: false, IsInterface: false, IsGenericDefinition: false } }) return type;
        }
        return null;
    }
}
