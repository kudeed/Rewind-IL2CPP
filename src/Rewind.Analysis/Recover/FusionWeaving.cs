using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Takes out what Photon Fusion's weaver put into a method after it was compiled.
///
/// The weaver rewrites the compiled assembly: a method marked as a remote procedure gets, in front of its own
/// statements, the code that sends the call over the network (and runs the method's statements only when the
/// call is to be made here as well); "OnDestroy", "OnEnable" and "OnDisable" of a simulation behaviour get one
/// statement that notes the event in the behaviour's flags. Neither is in the source, and compiling the source
/// again weaves both in again - so they are removed here, leaving the method as it was written.
///
/// (Networked properties, the third thing the weaver rewrites, are put back by GuardedAccessorFolding.)
/// </summary>
internal static class FusionWeaving
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_WEAVER_FOLD") != null;

    public static void Run(HMethod method)
    {
        if (Disabled || method.Blocks.Count == 0) return;
        bool changed = RemoveMessageFlag(method);
        changed |= RemoveSending(method);
        if (changed) HirCleanup.Run(method);
    }

    /// <summary>"Flags |= IsUnityDestroyed" and its like at the start of a Unity message of a simulation behaviour.</summary>
    private static bool RemoveMessageFlag(HMethod method)
    {
        MethodDef m = method.Method;
        if (m.IsStatic || m.Parameters.Length != 0 || m.Name is not ("OnDestroy" or "OnEnable" or "OnDisable")) return false;
        TypeDef? behaviour = null;
        int guard = 0;
        for (TypeDef? t = m.DeclaringType.BaseType?.Definition; t != null && guard++ < 64; t = t.BaseType?.Definition)
            if (t.Name == "SimulationBehaviour" && t.Namespace == "Fusion")
            {
                behaviour = t;
                break;
            }
        // Fusion's own classes are not woven: there the statement is source.
        if (behaviour == null || ReferenceEquals(behaviour.Assembly, m.DeclaringType.Assembly)) return false;
        List<HStmt> statements = method.Blocks[0].Statements;
        for (int i = 0; i < statements.Count; i++)
        {
            if (statements[i] is HAssign
                {
                    Target: HField { Object: HArg { Index: -1 }, Field: var written },
                    Value: HBinary { Op: HBinaryOp.Or or HBinaryOp.And, Left: HField { Object: HArg { Index: -1 }, Field: var read }, Right: HConst },
                } && ReferenceEquals(written, read) && written.Name == "Flags" && ReferenceEquals(written.DeclaringType, behaviour))
            {
                statements.RemoveAt(i);
                return true;
            }
            // Only the setting up of locals may come before it.
            if (statements[i] is not HAssign { Target: HLocal }) return false;
        }
        return false;
    }

    private static IEnumerable<HBlock> Successors(HBlock block)
    {
        if (block.Statements.Count == 0) yield break;
        switch (block.Statements[^1])
        {
            case HJump j: yield return j.Target; break;
            case HBranch b: yield return b.WhenTrue; yield return b.WhenFalse; break;
            case HSwitch s:
                foreach (HBlock t in s.Targets) yield return t;
                yield return s.Default;
                break;
        }
    }

    private static void Collect(HExpr? e, HashSet<HVar> into)
    {
        switch (e)
        {
            case null: return;
            case HLocal l: into.Add(l.Variable); return;
            case HField f: Collect(f.Object, into); return;
            case HElement el: Collect(el.Array, into); Collect(el.Index, into); return;
            case HArrayLength len: Collect(len.Array, into); return;
            case HAddressOf a: Collect(a.Target, into); return;
            case HDeref d: Collect(d.Pointer, into); return;
            case HUnary u: Collect(u.Operand, into); return;
            case HBinary b: Collect(b.Left, into); Collect(b.Right, into); return;
            case HCompare c: Collect(c.Left, into); Collect(c.Right, into); return;
            case HConv c: Collect(c.Operand, into); return;
            case HCall call:
                Collect(call.This, into);
                foreach (HExpr a in call.Arguments) Collect(a, into);
                return;
            case HNewObject n:
                foreach (HExpr a in n.Arguments) Collect(a, into);
                return;
            case HNewArray na: Collect(na.Length, into); return;
            case HTypeExpr t: Collect(t.Operand, into); return;
            case HCachedDelegate cached: Collect(cached.Creation, into); return;
            case HSelect s: Collect(s.Condition, into); Collect(s.WhenTrue, into); Collect(s.WhenFalse, into); return;
            case HOpaque o:
                foreach (HExpr a in o.Operands) Collect(a, into);
                return;
        }
    }

    private static HVar? Root(HExpr target) => target switch
    {
        HLocal l => l.Variable,
        HField { Object: { } owner } => Root(owner),
        _ => null,
    };

    /// <summary>
    /// A remote procedure starts with "if (!NetworkBehaviourUtils.CheckInvokeRpc(this)) { send it; return unless
    /// it is also to run here; }". What the test leads to when it holds is the method as written.
    /// </summary>
    private static bool RemoveSending(HMethod method)
    {
        HBlock entry = method.Blocks[0];
        if (entry.Statements.Count == 0 || entry.Statements[^1] is not HBranch branch) return false;
        HExpr condition = branch.Condition;
        bool negated = false;
        while (condition is HUnary { Op: HUnaryOp.LogicalNot, Operand: var inner })
        {
            negated = !negated;
            condition = inner;
        }
        if (condition is not HCall { This: null, Method: { Name: "CheckInvokeRpc", DeclaringType: { Name: "NetworkBehaviourUtils", Namespace: "Fusion" } } }) return false;
        HBlock own = negated ? branch.WhenFalse : branch.WhenTrue;
        if (own.Scope != -1) return false;

        // The method's own statements: everything that test leads to.
        var reached = new HashSet<HBlock> { own };
        var work = new Stack<HBlock>();
        work.Push(own);
        while (work.Count > 0)
        {
            HBlock b = work.Pop();
            foreach (HBlock s in Successors(b))
                if (reached.Add(s))
                    work.Push(s);
            foreach (HTryRegion r in method.TryRegions.Values)
                if (ReferenceEquals(r.Entry, b) && reached.Add(r.HandlerEntry))
                    work.Push(r.HandlerEntry);
        }
        if (reached.Contains(entry)) return false;
        var mentioned = new HashSet<HVar>();
        foreach (HBlock b in reached)
            foreach (HStmt s in b.Statements)
                switch (s)
                {
                    case HAssign a: Collect(a.Target, mentioned); Collect(a.Value, mentioned); break;
                    case HEval e: Collect(e.Expression, mentioned); break;
                    case HReturn r: Collect(r.Value, mentioned); break;
                    case HThrow t: Collect(t.Exception, mentioned); break;
                    case HBranch b2: Collect(b2.Condition, mentioned); break;
                    case HSwitch sw: Collect(sw.Value, mentioned); break;
                }

        // Of what comes before the test, only the setting up of locals those statements use stays.
        var kept = new List<HStmt>();
        for (int i = 0; i < entry.Statements.Count - 1; i++)
        {
            HStmt s = entry.Statements[i];
            if (s is not HAssign assign || Root(assign.Target) is not { } local) return false; // something the weaver does not put there
            if (mentioned.Contains(local)) kept.Add(s);
        }
        kept.Add(new HJump(own) { Address = branch.Address });
        entry.Statements.Clear();
        entry.Statements.AddRange(kept);
        return true;
    }
}
