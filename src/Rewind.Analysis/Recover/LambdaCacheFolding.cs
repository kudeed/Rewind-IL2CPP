using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Puts the creation of cached delegates back into one expression.
///
/// A lambda that captures nothing is made once: the compiler keeps the delegate in a static field and writes
/// "Cache ?? (Cache = new D(instance, method))" wherever the lambda stands. In machine code that is a test and
/// two paths that meet again, and translated as such it stays two paths: correct, but a statement where the
/// source had an expression (which matters where only an expression may stand, as in the arguments of a base
/// constructor call), and not something the C# decompiler can show as the lambda it was.
///
/// Here the two paths become one HCachedDelegate value again, which is emitted exactly as the compiler does.
/// </summary>
internal static class LambdaCacheFolding
{
    private static bool IsDelegate(TypeSig? type)
    {
        TypeDef? definition = type?.Definition;
        for (int depth = 0; definition != null && depth < 8; depth++)
        {
            if (definition.FullName is "System.MulticastDelegate" or "System.Delegate") return depth > 0;
            definition = definition.BaseType?.Definition;
        }
        return false;
    }

    /// <summary>A static field the compiler made to keep a delegate in.</summary>
    private static bool IsCache(HExpr? e) =>
        e is HField { Object: null } f && f.Field.IsStatic && f.Field.Name.Length != 0 && f.Field.Name[0] == '<' && IsDelegate(f.Type ?? f.Field.Type);

    private static bool IsNull(HExpr e) => e is HConst { Value: null or 0 or 0L };

    /// <summary>True when something was put back.</summary>
    public static bool Run(HMethod method)
    {
        Dictionary<HBlock, int>? entries = null;
        bool any = false;
        // Blocks the two paths met in and nothing else leads to: (the block that now always goes there, it).
        var joins = new List<(HBlock Head, HBlock Next)>();
        foreach (HBlock block in method.Blocks)
        {
            if (block.Statements is not [.., HBranch branch]) continue;
            HExpr condition = branch.Condition;
            bool negated = false;
            while (condition is HUnary { Op: HUnaryOp.LogicalNot } not)
            {
                negated = !negated;
                condition = not.Operand;
            }
            if (condition is not HCompare { Op: HCompareOp.Eq or HCompareOp.Ne } test) continue;
            HExpr? subject = IsNull(test.Right) ? test.Left : IsNull(test.Left) ? test.Right : null;
            if (subject == null) continue;
            bool whenNull = (test.Op == HCompareOp.Eq) != negated;
            HBlock make = whenNull ? branch.WhenTrue : branch.WhenFalse, have = whenNull ? branch.WhenFalse : branch.WhenTrue;
            if (ReferenceEquals(make, have) || make.Scope != block.Scope || have.Scope != block.Scope) continue;

            // What is tested: the cache itself, or a variable that was just given its content.
            HField? cache = null;
            HVar? read = null;
            if (IsCache(subject)) cache = (HField)subject;
            else if (subject is HLocal held && block.Statements.Count >= 2 &&
                     block.Statements[^2] is HAssign { Target: HLocal loaded, Value: var from } && ReferenceEquals(loaded.Variable, held.Variable) && IsCache(from))
            {
                cache = (HField)from;
                read = held.Variable;
            }
            if (cache == null) continue;

            if (entries == null)
            {
                entries = [];
                foreach (HBlock b in method.Blocks)
                {
                    if (b.Statements.Count == 0) continue;
                    switch (b.Statements[^1])
                    {
                        case HJump j: entries[j.Target] = entries.GetValueOrDefault(j.Target) + 1; break;
                        case HBranch br:
                            entries[br.WhenTrue] = entries.GetValueOrDefault(br.WhenTrue) + 1;
                            entries[br.WhenFalse] = entries.GetValueOrDefault(br.WhenFalse) + 1;
                            break;
                        case HSwitch sw:
                            foreach (HBlock t in sw.Targets) entries[t] = entries.GetValueOrDefault(t) + 1;
                            entries[sw.Default] = entries.GetValueOrDefault(sw.Default) + 1;
                            break;
                    }
                }
                foreach (HTryRegion r in method.TryRegions.Values)
                {
                    entries[r.Entry] = entries.GetValueOrDefault(r.Entry) + 1;
                    entries[r.HandlerEntry] = entries.GetValueOrDefault(r.HandlerEntry) + 1;
                }
            }
            if (entries.GetValueOrDefault(make) != 1 || entries.GetValueOrDefault(have) != 1) continue;

            // The path that makes the delegate: [instance = Holder.<>9;] made = new D(instance, method); Cache = made; result = made;
            if (make.Statements is not [.., HJump after]) continue;
            HVar? made = null, result = null, instanceVariable = null;
            HNewObject? creation = null;
            HExpr? instance = null;
            bool stored = false, shape = true;
            for (int k = 0; k < make.Statements.Count - 1 && shape; k++)
            {
                switch (make.Statements[k])
                {
                    case HAssign { Target: HLocal t, Value: HField { Object: null } holder } when creation == null && instanceVariable == null:
                        instanceVariable = t.Variable;
                        instance = holder;
                        break;
                    case HAssign { Target: HLocal t, Value: HNewObject { Arguments: [var target, HMethodPointer] } n } when creation == null && IsDelegate(n.Type):
                        if (target is HLocal viaVariable)
                        {
                            if (instanceVariable == null || !ReferenceEquals(viaVariable.Variable, instanceVariable)) { shape = false; break; }
                        }
                        else if (target is not (HConst { Value: null } or HField { Object: null }) || instanceVariable != null) { shape = false; break; }
                        made = t.Variable;
                        creation = n;
                        break;
                    case HAssign { Target: HField { Object: null } to, Value: HLocal v } when made != null && !stored && ReferenceEquals(to.Field, cache.Field) && ReferenceEquals(v.Variable, made):
                        stored = true;
                        break;
                    case HAssign { Target: HLocal t, Value: HLocal v } when made != null && result == null && ReferenceEquals(v.Variable, made):
                        result = t.Variable;
                        break;
                    default:
                        shape = false;
                        break;
                }
            }
            if (!shape || creation == null || !stored || result == null) continue;

            // The path that has it already: result = what was read.
            if (have.Statements is not [HAssign { Target: HLocal kept, Value: var existing }, HJump meet] || !ReferenceEquals(meet.Target, after.Target) ||
                !ReferenceEquals(kept.Variable, result)) continue;
            bool sameValue = read != null ? existing is HLocal e && ReferenceEquals(e.Variable, read) : existing is HField { Object: null } again && ReferenceEquals(again.Field, cache.Field);
            if (!sameValue) continue;

            var newCreation = new HNewObject
            {
                Constructor = creation.Constructor,
                DeclaringType = creation.DeclaringType,
                Arguments = [instanceVariable != null ? instance! : creation.Arguments[0], creation.Arguments[1]],
                Type = creation.Type,
            };
            var value = new HCachedDelegate(new HField { Object = null, Field = cache.Field, DeclaringType = cache.DeclaringType, Type = cache.Type }, newCreation) { Type = creation.Type };
            ulong address = branch.Address;
            if (entries.GetValueOrDefault(after.Target) == 2 && after.Target.Scope == block.Scope && !ReferenceEquals(after.Target, block) &&
                !ReferenceEquals(after.Target, method.Blocks[0]))
                joins.Add((block, after.Target));
            block.Statements[^1] = new HAssign(new HLocal(result) { Type = result.Type }, value) { Address = address };
            block.Statements.Add(new HJump(after.Target) { Address = address });
            entries = null; // the blocks changed
            any = true;
        }
        // What came after the two paths is what comes after the expression: one run of statements again, as
        // it was written (and as the same code looks where it stands in a block of its own).
        Dictionary<HBlock, HBlock>? moved = null;
        foreach ((HBlock head, HBlock rest) in joins)
        {
            HBlock into = head;
            while (moved != null && moved.TryGetValue(into, out HBlock? further)) into = further;
            if (ReferenceEquals(into, rest) || into.Statements is not [.., HJump jump] || !ReferenceEquals(jump.Target, rest)) continue;
            into.Statements.RemoveAt(into.Statements.Count - 1);
            into.Statements.AddRange(rest.Statements);
            method.Blocks.Remove(rest);
            (moved ??= [])[rest] = into;
        }
        if (any) HirCleanup.Run(method);
        return any;
    }
}
