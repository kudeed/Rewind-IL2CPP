using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Constructors with branches, and constructors of base classes, put back.
///
/// A constructor that decides something ("_identifier = identifier ?? GetType().Name") is more than one run of
/// statements, and pasted into another method it spans several blocks there. Its statements are compared along
/// every way through it: the same statements, the same tests leading to the same places, until each way ends -
/// and every way that returns must go on at one place in the code at hand. What was matched becomes one call
/// of the constructor.
///
/// The constructor of a class runs its base class's constructor first, and the C++ compiler pastes that one in
/// too. So the base classes come first, the one furthest up first: at a creation site, the base constructor's
/// statements become a call of it on the new object, which the class's own constructor (whose statements were
/// recovered with that call in them) can then be found in. Inside a constructor, the same gives back
/// "base(...)" and "this(...)".
/// </summary>
internal static partial class ConstructorFolding
{
    private static readonly bool NoFlows = Environment.GetEnvironmentVariable("REWIND_NO_CONSTRUCTOR_FLOWS") != null;
    private const int MostStarts = 24;

    /// <summary>
    /// At a creation site whose constructor did not fold as one run: the base classes' constructors folded into
    /// calls on the new object, then the class's own, along its branches. True when "new T(...)" stands there.
    /// </summary>
    private static bool TryFoldChain(HMethod method, HBlock block, int at, HLocal target, TypeSig type, ProgramAnalysis program, MethodPipeline pipeline)
    {
        if (NoFlows || type.Definition is not { IsValueType: false } definition) return false;
        HVar created = target.Variable;
        bool changed = false;
        foreach (TypeSig ancestor in Ancestors(type, program))
            changed |= FoldCall(method, block, at + 1, created, ancestor, null, program, pipeline);
        if (changed && TryFold(block, at, target, type, program, pipeline)) return true;
        // The class's own constructor, along its branches.
        foreach ((MethodDef constructor, HMethod template) in Templates(definition, type, null, pipeline))
        {
            int last = Math.Min(block.Statements.Count - 1, at + 1 + MostStarts);
            for (int start = at + 1; start <= last; start++)
            {
                // (Only what comes before the first mention of the new object can be skipped.)
                if (start > at + 1 && Mentions(block.Statements[start - 1], created)) break;
                if (MatchFlow(template, block, start, created, constructor) is not { } match) continue;
                HExpr[] arguments = Arguments(match.Unifier, constructor, type, program);
                var creation = new HAssign(target, new HNewObject
                {
                    Constructor = constructor,
                    DeclaringType = type is GenericInstSig ? type : null,
                    Arguments = arguments,
                    Type = type,
                })
                { Address = block.Statements[at].Address };
                if (Apply(method, match, creation, at)) return true;
            }
        }
        return false;
    }

    /// <summary>
    /// In a constructor: the base classes' constructors pasted into it put back as calls on "this", and its
    /// class's other constructors ("this(...)").
    /// </summary>
    private static void FoldOwnChain(HMethod method, ProgramAnalysis program, MethodPipeline pipeline)
    {
        MethodDef own = method.Method;
        if (NoFlows || own.Name != ".ctor" || own.IsStatic || method.Blocks.Count == 0) return;
        TypeDef type = own.DeclaringType;
        if (type.IsValueType || type.GenericParameters.Length != 0) return;
        HBlock entry = method.Blocks[0];
        foreach (TypeSig ancestor in Ancestors(type.Sig, program))
            FoldCall(method, entry, 0, null, ancestor, null, program, pipeline);
        FoldCall(method, entry, 0, null, type.Sig, own, program, pipeline);
    }

    /// <summary>The base classes of a type, the one furthest up first, without System.Object; none with open type arguments.</summary>
    private static List<TypeSig> Ancestors(TypeSig type, ProgramAnalysis program)
    {
        var chain = new List<TypeSig>();
        TypeSig current = type;
        for (int guard = 0; guard < 32 && current.Definition is { BaseType: { } baseType } definition; guard++)
        {
            TypeSig[] arguments = current is GenericInstSig g ? g.Arguments : [];
            TypeSig next = arguments.Length != 0 ? program.Model.Sigs.Substitute(baseType, arguments, []) : baseType;
            if (next.Definition is not { BaseType: not null }) break; // System.Object
            if (next is GenericInstSig open && open.Arguments.Any(a => a is GenericParamSig)) break;
            chain.Add(next);
            current = next;
            _ = definition;
        }
        chain.Reverse();
        return chain;
    }

    /// <summary>The constructors of a type with complete statements, the longest first.</summary>
    private static List<(MethodDef Constructor, HMethod Template)> Templates(TypeDef definition, TypeSig type, MethodDef? except, MethodPipeline pipeline)
    {
        TypeSig[] classArguments = type is GenericInstSig g ? g.Arguments : [];
        var found = new List<(MethodDef, HMethod, int)>();
        foreach (MethodDef constructor in definition.Methods)
        {
            if (constructor.Name != ".ctor" || constructor.IsStatic || ReferenceEquals(constructor, except)) continue;
            if (pipeline.ConstructorFlow(constructor, classArguments) is not { } template) continue;
            int size = template.Blocks.Sum(b => b.Statements.Count);
            // (A constructor that does nothing at all would match anywhere.)
            if (size <= 1) continue;
            found.Add((constructor, template, size));
        }
        return [.. found.OrderByDescending(f => f.Item3).Select(f => (f.Item1, f.Item2))];
    }

    /// <summary>
    /// Folds the statements of one of <paramref name="owner"/>'s constructors, found at or after
    /// <paramref name="from"/> in <paramref name="block"/>, into a call of it on the object.
    /// </summary>
    private static bool FoldCall(HMethod method, HBlock block, int from, HVar? created, TypeSig owner, MethodDef? except,
        ProgramAnalysis program, MethodPipeline pipeline)
    {
        if (owner.Definition is not { } definition) return false;
        foreach ((MethodDef constructor, HMethod template) in Templates(definition, owner, except, pipeline))
        {
            // Another constructor of the class that only runs a base constructor: "base(...)" says the same
            // and is what stands there already.
            if (except != null && template.Blocks is [{ Statements: [HEval { Expression: HCall { Method.Name: ".ctor", This: HArg { Index: < 0 } } }, HReturn] }])
                continue;
            int last = Math.Min(block.Statements.Count - 1, from + MostStarts);
            for (int start = from; start <= last; start++)
            {
                if (block.Statements[start] is not (HAssign or HEval)) break;
                if (MatchFlow(template, block, start, created, constructor) is not { } match) continue;
                HExpr[] arguments = Arguments(match.Unifier, constructor, owner, program);
                var call = new HEval(new HCall
                {
                    Method = constructor,
                    DeclaringType = owner is GenericInstSig ? owner : null,
                    This = created == null ? new HArg(-1) { Type = method.Method.DeclaringType.Sig } : new HLocal(created) { Type = created.Type },
                    Arguments = arguments,
                    Type = constructor.ReturnType,
                })
                { Address = block.Statements[start].Address };
                if (Apply(method, match, call, -1)) return true;
            }
        }
        return false;
    }

    private static HExpr[] Arguments(Unifier unifier, MethodDef constructor, TypeSig owner, ProgramAnalysis program)
    {
        TypeSig[] classArguments = owner is GenericInstSig g ? g.Arguments : [];
        var arguments = new HExpr[constructor.Parameters.Length];
        for (int i = 0; i < arguments.Length; i++)
        {
            TypeSig parameter = constructor.Parameters[i].Type;
            if (classArguments.Length != 0) parameter = program.Model.Sigs.Substitute(parameter, classArguments, []);
            // A parameter the constructor never looks at: any value does.
            arguments[i] = unifier.Arguments[i] ?? (parameter.IsValueType || parameter is GenericParamSig
                ? new HTypeExpr(HTypeOp.Default, parameter, null) { Type = parameter }
                : new HConst(null, parameter));
        }
        return arguments;
    }

    /// <summary>How a constructor's statements were found at a site, way by way.</summary>
    private sealed class Flow(Unifier unifier, HBlock entry, int start)
    {
        public readonly Unifier Unifier = unifier;
        public readonly HBlock Entry = entry;
        public readonly int Start = start;
        /// <summary>Where at the site each block of the constructor starts.</summary>
        public readonly Dictionary<HBlock, (HBlock Block, int Index)> Mapped = [];
        /// <summary>The site's blocks that statements were found in, with the first statement used.</summary>
        public readonly Dictionary<HBlock, int> Touched = [];
        /// <summary>Where the site goes on when the constructor returns.</summary>
        public (HBlock Block, int Index)? Continuation;
        public int Counter;
        public int FirstEffect = int.MaxValue;
        /// <summary>Locals of the site given a value by the statements found.</summary>
        public readonly HashSet<HVar> Assigned = [];
    }

    private static Flow? MatchFlow(HMethod template, HBlock block, int start, HVar? created, MethodDef constructor)
    {
        var flow = new Flow(new Unifier(created, constructor.Parameters.Length) { Constructor = constructor }, block, start);
        if (!Match(flow, template.Blocks[0], block, start, 0) || flow.Continuation == null) return null;
        if (!flow.Unifier.ArgumentsHoldBefore(flow.FirstEffect, flow.Assigned)) return null;
        return flow;
    }

    /// <summary>The site position a jump at it leads to (the jumps passed count as used).</summary>
    private static (HBlock Block, int Index) Follow(Flow flow, HBlock block, int index)
    {
        for (int guard = 0; guard < 16 && index < block.Statements.Count && block.Statements[index] is HJump jump; guard++)
        {
            Touch(flow, block, index);
            block = jump.Target;
            index = 0;
        }
        return (block, index);
    }

    private static void Touch(Flow flow, HBlock block, int index)
    {
        if (!flow.Touched.TryGetValue(block, out int first) || index < first) flow.Touched[block] = index;
    }

    /// <summary>Whether a statement found does nothing but fill the new object (nothing else can see it yet).</summary>
    private static bool Inert(Flow flow, HStmt s) => s switch
    {
        HAssign { Target: HField { Object: { } o }, Value: var value } => flow.Unifier.IsCreated(o) && HirBuilder.IsPure(value),
        HEval { Expression: HCall { Method: { Name: ".ctor", Parameters.Length: 0 } m, This: { } o } } => flow.Unifier.IsCreated(o) && m.DeclaringType.BaseType == null,
        _ => false,
    };

    private static bool Match(Flow flow, HBlock constructor, HBlock block, int index, int depth)
    {
        if (depth > 64) return false;
        (block, index) = Follow(flow, block, index);
        if (flow.Mapped.TryGetValue(constructor, out (HBlock Block, int Index) known)) return known == (block, index);
        flow.Mapped[constructor] = (block, index);
        List<HStmt> statements = constructor.Statements;
        if (statements.Count == 0) return false;
        for (int k = 0; k < statements.Count - 1; k++)
        {
            (block, index) = Follow(flow, block, index);
            if (index >= block.Statements.Count) return false;
            HStmt site = block.Statements[index];
            if (statements[k] is not (HAssign or HEval) || site is not (HAssign or HEval)) return false;
            if (!flow.Unifier.Statement(statements[k], site, flow.Counter)) return false;
            Touch(flow, block, index);
            if (!Inert(flow, site)) flow.FirstEffect = Math.Min(flow.FirstEffect, flow.Counter);
            if (site is HAssign { Target: HLocal assigned }) flow.Assigned.Add(assigned.Variable);
            flow.Counter++;
            index++;
        }
        switch (statements[^1])
        {
            case HReturn { Value: null }:
            {
                (HBlock Block, int Index) next = Follow(flow, block, index);
                if (flow.Continuation is { } other) return other == next;
                flow.Continuation = next;
                return true;
            }
            case HJump jump:
                return Match(flow, jump.Target, block, index, depth + 1);
            case HBranch branch:
            {
                (block, index) = Follow(flow, block, index);
                if (index >= block.Statements.Count || block.Statements[index] is not HBranch test) return false;
                HExpr wanted = branch.Condition, found = test.Condition;
                bool inverted = false;
                if (wanted is HCompare c && found is HCompare f && c.Op != f.Op)
                {
                    if (f.Op != Negated(c.Op)) return false;
                    inverted = true;
                    found = new HCompare(c.Op, f.Left, f.Right) { Type = f.Type };
                }
                else if (found is HUnary { Op: HUnaryOp.LogicalNot, Operand: var inner } && wanted is not HUnary { Op: HUnaryOp.LogicalNot })
                {
                    inverted = true;
                    found = inner;
                }
                else if (wanted is HUnary { Op: HUnaryOp.LogicalNot, Operand: var wantedInner } && found is not HUnary { Op: HUnaryOp.LogicalNot })
                {
                    inverted = true;
                    wanted = wantedInner;
                }
                if (!flow.Unifier.Same(wanted, found, flow.Counter)) return false;
                Touch(flow, block, index);
                flow.FirstEffect = Math.Min(flow.FirstEffect, flow.Counter);
                flow.Counter++;
                HBlock yes = inverted ? test.WhenFalse : test.WhenTrue, no = inverted ? test.WhenTrue : test.WhenFalse;
                return Match(flow, branch.WhenTrue, yes, 0, depth + 1) && Match(flow, branch.WhenFalse, no, 0, depth + 1);
            }
            case HThrow thrown:
            {
                (block, index) = Follow(flow, block, index);
                if (index >= block.Statements.Count || block.Statements[index] is not HThrow at) return false;
                if ((thrown.Exception == null) != (at.Exception == null)) return false;
                if (thrown.Exception != null && !flow.Unifier.Same(thrown.Exception, at.Exception!, flow.Counter)) return false;
                Touch(flow, block, index);
                flow.FirstEffect = Math.Min(flow.FirstEffect, flow.Counter);
                flow.Counter++;
                return true;
            }
            default:
                return false;
        }
    }

    private static HCompareOp Negated(HCompareOp op) => op switch
    {
        HCompareOp.Eq => HCompareOp.Ne,
        HCompareOp.Ne => HCompareOp.Eq,
        HCompareOp.Lt => HCompareOp.Ge,
        HCompareOp.Ge => HCompareOp.Lt,
        HCompareOp.Le => HCompareOp.Gt,
        HCompareOp.Gt => HCompareOp.Le,
        HCompareOp.LtUn => HCompareOp.GeUn,
        HCompareOp.GeUn => HCompareOp.LtUn,
        HCompareOp.LeUn => HCompareOp.GtUn,
        _ => HCompareOp.LeUn,
    };

    /// <summary>
    /// Replaces what was found with one statement. Every block found must be entered only from what was found
    /// (it goes away), and the temporaries the site has for the constructor's must not be read anywhere else.
    /// </summary>
    private static bool Apply(HMethod method, Flow flow, HStmt replacement, int allocation)
    {
        HBlock entry = flow.Entry;
        int start = flow.Start;
        if (flow.Continuation is not { } continuation) return false;
        (HBlock next, int at) = continuation;
        var region = new HashSet<HBlock>(flow.Touched.Keys) { entry };
        if (flow.Touched.TryGetValue(entry, out int first) && first < start) return false;
        if (ReferenceEquals(next, entry))
        {
            // Straight through: the constructor's statements are a stretch of this block.
            if (region.Count != 1 || at < start) return false;
        }
        else if (region.Contains(next) ? at == 0 : at != 0) return false;
        foreach (HBlock b in region.Append(next))
            if (b.Scope != entry.Scope)
                return false;
        foreach (HTryRegion r in method.TryRegions.Values)
            foreach (HBlock b in region)
                if (!ReferenceEquals(b, entry) && (ReferenceEquals(r.Entry, b) || ReferenceEquals(r.HandlerEntry, b)))
                    return false;

        // Every way into a block that goes away comes from what goes away.
        var preds = new Dictionary<HBlock, List<HBlock>>();
        foreach (HBlock b in method.Blocks)
        {
            if (b.Statements.Count == 0) continue;
            IEnumerable<HBlock> targets = b.Statements[^1] switch
            {
                HJump j => [j.Target],
                HBranch br => [br.WhenTrue, br.WhenFalse],
                HSwitch sw => [.. sw.Targets, sw.Default],
                _ => [],
            };
            foreach (HBlock t in targets)
            {
                if (!preds.TryGetValue(t, out List<HBlock>? list)) preds[t] = list = [];
                list.Add(b);
            }
        }
        foreach (HBlock b in region)
        {
            if (ReferenceEquals(b, entry)) continue;
            if (ReferenceEquals(b, method.Blocks[0]) || flow.Touched[b] != 0) return false;
            foreach (HBlock p in preds.GetValueOrDefault(b) ?? [])
                if (!region.Contains(p))
                    return false;
        }

        // The site's temporaries for the constructor's are not read where the statements stay.
        IEnumerable<HStmt> Remaining()
        {
            foreach (HBlock b in method.Blocks)
            {
                if (ReferenceEquals(b, entry))
                {
                    for (int i = 0; i < start; i++) yield return b.Statements[i];
                    if (ReferenceEquals(next, entry))
                        for (int i = at; i < b.Statements.Count; i++) yield return b.Statements[i];
                }
                else if (ReferenceEquals(b, next))
                {
                    for (int i = at; i < b.Statements.Count; i++) yield return b.Statements[i];
                }
                else if (!region.Contains(b))
                {
                    foreach (HStmt s in b.Statements) yield return s;
                }
            }
        }
        if (flow.Unifier.SiteLocals.Count != 0)
            foreach (HStmt s in Remaining())
                foreach (HVar v in flow.Unifier.SiteLocals)
                    if (Reads(s, v))
                        return false;

        var statements = new List<HStmt>(entry.Statements.Take(start)) { replacement };
        if (ReferenceEquals(next, entry)) statements.AddRange(entry.Statements.Skip(at));
        else
        {
            statements.Add(new HJump(next) { Address = replacement.Address });
            if (at > 0) next.Statements.RemoveRange(0, at);
        }
        if (allocation >= 0) statements.RemoveAt(allocation);
        entry.Statements = statements;
        foreach (HBlock b in region)
            if (!ReferenceEquals(b, entry) && !ReferenceEquals(b, next))
                method.Blocks.Remove(b);
        return true;
    }

    /// <summary>Whether an expression reads "this".</summary>
    internal static bool MentionsThis(HExpr? e)
    {
        bool found = false;
        void Walk(HExpr? x)
        {
            if (found || x == null) return;
            switch (x)
            {
                case HArg { Index: < 0 }: found = true; break;
                case HField f: Walk(f.Object); break;
                case HElement el: Walk(el.Array); Walk(el.Index); break;
                case HArrayLength len: Walk(len.Array); break;
                case HAddressOf a: Walk(a.Target); break;
                case HDeref d: Walk(d.Pointer); break;
                case HUnary u: Walk(u.Operand); break;
                case HBinary b: Walk(b.Left); Walk(b.Right); break;
                case HCompare c: Walk(c.Left); Walk(c.Right); break;
                case HConv c: Walk(c.Operand); break;
                case HSelect s: Walk(s.Condition); Walk(s.WhenTrue); Walk(s.WhenFalse); break;
                case HCall call: Walk(call.This); foreach (HExpr a in call.Arguments) Walk(a); break;
                case HNewObject n: foreach (HExpr a in n.Arguments) Walk(a); break;
                case HNewArray na: Walk(na.Length); break;
                case HTypeExpr t: Walk(t.Operand); break;
                case HMethodPointer { VirtualOn: not null }: found = true; break;
                case HCachedDelegate cd: Walk(cd.Creation); break;
                case HOpaque o: foreach (HExpr a in o.Operands) Walk(a); break;
            }
        }
        Walk(e);
        return found;
    }
}
