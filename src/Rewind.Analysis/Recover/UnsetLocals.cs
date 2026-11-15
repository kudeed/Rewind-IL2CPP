using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Gives a first value to the variables that are used before anything was put in them.
///
/// Machine code may read a register or stack slot it never wrote: where only some of its bytes matter (a
/// struct of bytes built in a register: "x = (x &amp; ~0xFF) | b"), or on a path where the value read is not
/// used afterwards. As IL that is harmless - every local starts out as zero - but C# refuses a variable that
/// is not certain to have been assigned. So what IL does silently is written down: such a variable is set to
/// zero where the method starts.
/// </summary>
internal static class UnsetLocals
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_UNSET_LOCALS") != null;

    public static void Run(HMethod method)
    {
        if (Disabled || method.Blocks.Count == 0 || method.Locals.Count == 0) return;
        var index = new Dictionary<HVar, int>(method.Locals.Count);
        foreach (HVar v in method.Locals) index.TryAdd(v, index.Count);
        int words = (index.Count + 63) / 64;
        int count = method.Blocks.Count;
        var number = new Dictionary<HBlock, int>(count);
        for (int i = 0; i < count; i++) number[method.Blocks[i]] = i;

        // What flows into a block: from the blocks that lead to it, and - for the block a handler starts
        // with - whatever was certain where its protected region began.
        var from = new List<int>[count];
        for (int i = 0; i < count; i++) from[i] = [];
        bool entryIsTarget = false;
        for (int i = 0; i < count; i++)
        {
            List<HStmt> s = method.Blocks[i].Statements;
            if (s.Count == 0) continue;
            void To(HBlock target)
            {
                if (!number.TryGetValue(target, out int t)) return;
                from[t].Add(i);
                entryIsTarget |= t == 0;
            }
            switch (s[^1])
            {
                case HJump j: To(j.Target); break;
                case HBranch b: To(b.WhenTrue); To(b.WhenFalse); break;
                case HSwitch sw:
                    foreach (HBlock t in sw.Targets) To(t);
                    To(sw.Default);
                    break;
            }
        }
        // A method that comes back to its first block has no place "before everything" to write at.
        if (entryIsTarget) return;
        var handlerOf = new Dictionary<int, int>();
        var caught = new HashSet<HVar>();
        foreach (HTryRegion region in method.TryRegions.Values)
        {
            caught.Add(region.Exception);
            if (number.TryGetValue(region.HandlerEntry, out int handler) && number.TryGetValue(region.Entry, out int entry)) handlerOf[handler] = entry;
        }

        var into = new ulong[count][];
        var after = new ulong[count][];
        for (int i = 0; i < count; i++)
        {
            into[i] = new ulong[words];
            after[i] = new ulong[words];
            Array.Fill(into[i], i == 0 ? 0UL : ulong.MaxValue);
            Array.Fill(after[i], ulong.MaxValue);
        }

        var unset = new HashSet<HVar>();
        void Use(HExpr? e, ulong[] set, bool record)
        {
            FinallyFolding.Visit(e, x =>
            {
                if (x is not HLocal l || !index.TryGetValue(l.Variable, out int n) || caught.Contains(l.Variable)) return;
                if (record && (set[n >> 6] & (1UL << (n & 63))) == 0) unset.Add(l.Variable);
            });
        }
        void Flow(int b, ulong[] set, bool record)
        {
            foreach (HStmt s in method.Blocks[b].Statements)
            {
                switch (s)
                {
                    case HAssign { Target: HLocal whole } a:
                        Use(a.Value, set, record);
                        if (index.TryGetValue(whole.Variable, out int n)) set[n >> 6] |= 1UL << (n & 63);
                        break;
                    case HAssign a:
                        Use(a.Target, set, record);
                        Use(a.Value, set, record);
                        break;
                    case HEval e: Use(e.Expression, set, record); break;
                    case HReturn r: Use(r.Value, set, record); break;
                    case HThrow t: Use(t.Exception, set, record); break;
                    case HBranch br: Use(br.Condition, set, record); break;
                    case HSwitch sw: Use(sw.Value, set, record); break;
                }
            }
        }

        var scratch = new ulong[words];
        for (int round = 0; round < 64; round++)
        {
            bool changed = false;
            for (int b = 0; b < count; b++)
            {
                if (b != 0 && (from[b].Count != 0 || handlerOf.ContainsKey(b)))
                {
                    Array.Fill(scratch, ulong.MaxValue);
                    foreach (int p in from[b])
                        for (int w = 0; w < words; w++)
                            scratch[w] &= after[p][w];
                    if (handlerOf.TryGetValue(b, out int entry))
                        for (int w = 0; w < words; w++)
                            scratch[w] &= into[entry][w];
                    for (int w = 0; w < words; w++)
                        if (into[b][w] != scratch[w])
                        {
                            into[b][w] = scratch[w];
                            changed = true;
                        }
                }
                Array.Copy(into[b], scratch, words);
                Flow(b, scratch, false);
                for (int w = 0; w < words; w++)
                    if (after[b][w] != scratch[w])
                    {
                        after[b][w] = scratch[w];
                        changed = true;
                    }
            }
            if (!changed) break;
        }
        for (int b = 0; b < count; b++)
        {
            // A block nothing leads to is not run.
            if (b != 0 && from[b].Count == 0 && !handlerOf.ContainsKey(b)) continue;
            Array.Copy(into[b], scratch, words);
            Flow(b, scratch, true);
        }
        if (unset.Count == 0) return;

        var first = new List<HStmt>();
        ulong address = method.Blocks[0].Statements.Count != 0 ? method.Blocks[0].Statements[0].Address : 0;
        foreach (HVar v in method.Locals)
        {
            if (!unset.Contains(v) || Nothing(v.Type) is not { } zero) continue;
            first.Add(new HAssign(new HLocal(v) { Type = v.Type }, zero) { Address = address });
        }
        // In a constructor, what stands before the call of the base class's constructor is the field
        // initializers and nothing else: the variables get their first values after it - unless one of them
        // is used before.
        int at = 0;
        if (first.Count != 0 && InitializerOrder.BaseCall(method) is >= 0 and var call)
        {
            bool early = false;
            for (int k = 0; k <= call && !early; k++)
                foreach (HStmt set in first)
                    early |= ConstructorFolding.Mentions(method.Blocks[0].Statements[k], ((HLocal)((HAssign)set).Target).Variable);
            if (!early) at = call + 1;
        }
        method.Blocks[0].Statements.InsertRange(at, first);
    }

    /// <summary>What a variable of a type holds before anything is put in it; null for a type that has no such thing to write.</summary>
    private static HExpr? Nothing(TypeSig? type)
    {
        switch (type)
        {
            case null or ByRefSig or OpaqueSig:
                return null;
            case GenericParamSig:
                return new HTypeExpr(HTypeOp.Default, type, null) { Type = type };
            case PointerSig:
                return new HConst(0L, type);
            case PrimitiveSig p:
                return p.Element switch
                {
                    Il2CppTypeEnum.Boolean => new HConst(false, type),
                    Il2CppTypeEnum.R4 => new HConst(0f, type),
                    Il2CppTypeEnum.R8 => new HConst(0d, type),
                    Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 or Il2CppTypeEnum.I or Il2CppTypeEnum.U => new HConst(0L, type),
                    Il2CppTypeEnum.String or Il2CppTypeEnum.Object => new HConst(null, type),
                    Il2CppTypeEnum.Void or Il2CppTypeEnum.TypedByRef => null,
                    _ => new HConst(0, type),
                };
        }
        if (!type.IsValueType) return new HConst(null, type);
        return new HTypeExpr(HTypeOp.Default, type, null) { Type = type };
    }
}
