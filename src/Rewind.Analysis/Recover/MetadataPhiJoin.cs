using Rewind.Analysis.Ir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Joins metadata identities without turning them into managed integers. Every reachable input must have
/// the same identity; unknown inputs, cycles, malformed merges and oversized proofs are rejected.
/// The supplied projection describes only immutable metadata and does not evaluate arbitrary machine IR.
/// </summary>
internal static class MetadataPhiJoin
{
    internal static bool Known(Sem? value) => value is SKlass ||
        value is SMethod method && (method.Inst == null || ReferenceEquals(method.Method, method.Inst.Method)) ||
        value is SRgctx { Items.Count: > 0 };

    internal static bool Same(Sem left, Sem right) => (left, right) switch
    {
        (SKlass a, SKlass b) => a.Type.Key == b.Type.Key,
        (SMethod a, SMethod b) => ReferenceEquals(a.Method, b.Method) &&
            (a.Inst == null && b.Inst == null || a.Inst != null && b.Inst != null &&
             ReferenceEquals(a.Inst.Method, b.Inst.Method) && Arguments(a.Inst.ClassArguments, b.Inst.ClassArguments) &&
             Arguments(a.Inst.MethodArguments, b.Inst.MethodArguments)),
        (SRgctx a, SRgctx b) => a.Items.Count != 0 && ReferenceEquals(a.Items, b.Items) &&
            Arguments(a.ClassArguments, b.ClassArguments) && Arguments(a.MethodArguments, b.MethodArguments),
        _ => false,
    };

    private static bool Arguments(TypeSig[] a, TypeSig[] b) => a.Length == b.Length && a.Zip(b).All(pair => pair.First.Key == pair.Second.Key);

    internal static Sem? Resolve(Node phi, int pointerBytes, Func<Node, Func<Node, Sem?>, Sem?> describe)
    {
        if (phi.Op != Op.Phi || pointerBytes is not (4 or 8) || phi.Type.Bytes() != pointerBytes || phi.In.Length == 0) return null;
        var known = new Dictionary<Node, Sem?>();
        var active = new HashSet<Node>();
        int visited = 0;
        Sem? Visit(Node node)
        {
            if (known.TryGetValue(node, out Sem? cached)) return cached;
            if (++visited > 256 || active.Count >= 64 || node.Type.Bytes() != pointerBytes || !active.Add(node)) return null;
            Sem? result = null;
            if (node.Op == Op.Phi)
            {
                if (node.Block != null && node.In.Length > 0 && node.In.Length == node.Block.Preds.Count)
                {
                    bool same = true;
                    foreach (Node input in node.In)
                    {
                        Sem? value = Visit(input);
                        if (!Known(value) || result != null && !Same(result, value!)) { same = false; break; }
                        result ??= value;
                    }
                    if (!same) result = null;
                }
            }
            else result = describe(node, Visit);
            active.Remove(node);
            if (!Known(result)) result = null;
            known[node] = result;
            return result;
        }
        return Visit(phi);
    }
}
