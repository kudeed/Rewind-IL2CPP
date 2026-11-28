using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Passes;

/// <summary>Recognizes only an acyclic choice of incoming this and exact owner class metadata.</summary>
public static class OwnMetadataReceiverProof
{
    public static bool IsExact(Node receiver, Node incomingThis, Func<Node, bool> isOwnClass)
    {
        var pending = new Stack<(Node Node, bool Exit)>();
        var active = new HashSet<Node>();
        var complete = new HashSet<Node>();
        bool metadata = false;
        pending.Push((receiver, false));
        while (pending.TryPop(out var visit))
        {
            Node n = visit.Node;
            if (visit.Exit) { active.Remove(n); complete.Add(n); continue; }
            if (ReferenceEquals(n, incomingThis)) continue;
            if (!n.Dead && n.Op == Op.SlotValue && n.Type == VT.I64 && isOwnClass(n)) { metadata = true; continue; }
            if (complete.Contains(n)) continue;
            if (n.Dead || n.Op != Op.Phi || n.Type != VT.I64 || n.In.Length < 2 || !active.Add(n)) return false;
            pending.Push((n, true));
            for (int i = n.In.Length - 1; i >= 0; i--) pending.Push((n.In[i], false));
        }
        return metadata;
    }
}
