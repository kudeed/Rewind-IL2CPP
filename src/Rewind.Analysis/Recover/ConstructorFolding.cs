using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Puts inlined constructors back.
///
/// "new T(args)" is compiled as "allocate; run T's constructor on it", and the C++ compiler often pastes the
/// constructor's statements in place of the call. What the machine code then shows is a raw allocation followed
/// by those statements - exact, but not how anyone would write it. Here the statements after an allocation are
/// compared with the bodies of T's constructors (recovered the same way from their own machine code); where
/// they are one constructor's statements with particular values in place of its parameters, they are replaced
/// by a call of that constructor with those values. Where nothing matches, the raw form stays: it does the same
/// thing either way.
/// </summary>
internal static class ConstructorFolding
{
    /// <param name="again">A second look, after other things were put back: only what is found now changes anything.</param>
    public static void Run(HMethod method, ProgramAnalysis program, MethodPipeline pipeline, bool again = false)
    {
        // Later allocations first, so that an object created inside another constructor's statements has
        // already taken its final form when the outer one is compared.
        for (int b = method.Blocks.Count - 1; b >= 0; b--)
        {
            HBlock block = method.Blocks[b];
            for (int i = block.Statements.Count - 1; i >= 0; i--)
            {
                if (i >= block.Statements.Count) continue;
                if (block.Statements[i] is not HAssign { Target: HLocal target, Value: HTypeExpr { Op: HTypeOp.Allocate } allocation }) continue;
                string problem = $"the constructor of {allocation.Target.ShortName} was inlined and could not be folded back";
                string note = $"the constructor of {allocation.Target.ShortName} was inlined here; the object is allocated raw and its statements follow";
                if (TryFold(block, i, target, allocation.Target, program, pipeline))
                {
                    if (again)
                    {
                        method.Problems.Remove(problem);
                        method.Notes.Remove(note);
                    }
                    continue;
                }
                if (again) continue;
                if (program.RawAllocator == null) method.Problems.Add(problem);
                else method.Notes.Add(note);
            }
        }
    }

    private static bool TryFold(HBlock block, int at, HLocal target, TypeSig type, ProgramAnalysis program, MethodPipeline pipeline)
    {
        TypeDef? definition = type.Definition;
        if (definition == null || definition.IsValueType) return false;
        TypeSig[] classArguments = type is GenericInstSig g ? g.Arguments : [];
        List<HStmt> site = block.Statements;
        HVar created = target.Variable;

        // The constructor's statements start at the first statement that touches the new object, or a little
        // before it (a value computed first and stored afterwards).
        int firstMention = at + 1;
        while (firstMention < site.Count && firstMention - at <= 8 && site[firstMention] is HAssign or HEval && !Mentions(site[firstMention], created))
            firstMention++;

        MethodDef? best = null;
        HExpr?[]? bestArguments = null;
        int bestStart = 0, bestLength = -1;
        foreach (MethodDef constructor in definition.Methods)
        {
            if (constructor.Name != ".ctor" || constructor.IsStatic) continue;
            HMethod? body = pipeline.ConstructorBody(constructor, classArguments);
            if (body == null) continue;
            List<HStmt> statements = body.Blocks[0].Statements;
            int length = statements.Count - 1; // without the final return
            if (length < bestLength || (length == bestLength && best != null && best.Parameters.Length <= constructor.Parameters.Length)) continue;

            int lastStart = length == 0 ? at + 1 : Math.Min(firstMention, site.Count - length);
            for (int start = at + 1; start <= lastStart; start++)
            {
                var unifier = new Unifier(created, constructor.Parameters.Length) { Constructor = constructor };
                bool matched = true;
                for (int k = 0; k < length && matched; k++)
                    matched = unifier.Statement(statements[k], site[start + k], k);
                if (!matched && Reordered(statements, length, site, start, created, constructor.Parameters.Length) is { } other)
                {
                    unifier = other;
                    matched = true;
                }
                if (!matched || !unifier.ArgumentsAreValid(site, start, length)) continue;
                best = constructor;
                bestArguments = unifier.Arguments;
                bestStart = start;
                bestLength = length;
                break;
            }
        }
        if (best == null || bestArguments == null) return false;

        var arguments = new HExpr[best.Parameters.Length];
        for (int i = 0; i < arguments.Length; i++)
        {
            TypeSig parameter = best.Parameters[i].Type;
            if (classArguments.Length != 0) parameter = program.Model.Sigs.Substitute(parameter, classArguments, []);
            // A parameter the constructor never looks at: any value does.
            arguments[i] = bestArguments[i] ?? (parameter.IsValueType || parameter is GenericParamSig
                ? new HTypeExpr(HTypeOp.Default, parameter, null) { Type = parameter }
                : new HConst(null, parameter));
        }
        var creation = new HAssign(target, new HNewObject
        {
            Constructor = best,
            DeclaringType = type is GenericInstSig ? type : null,
            Arguments = arguments,
            Type = type,
        })
        { Address = block.Statements[at].Address };

        if (bestLength > 0) site.RemoveRange(bestStart, bestLength);
        site.Insert(bestStart, creation);
        site.RemoveAt(at);
        return true;
    }

    /// <summary>
    /// The constructor's statements, found at the site with its stores into the new object in another order.
    /// The compiler puts those in whatever order suits it: nothing can see the object yet, and what is stored
    /// only computes. So between two statements that do something else, each store of the constructor is
    /// looked for among the site's stores there, by the field it goes to. Null when that does not work out.
    /// </summary>
    private static Unifier? Reordered(List<HStmt> statements, int length, List<HStmt> site, int start, HVar created, int parameters)
    {
        if (length < 2 || start + length > site.Count) return null;
        static FieldDef? Filled(HStmt s, Func<HExpr, bool> isObject) =>
            s is HAssign { Target: HField { Object: { } o } target, Value: var value } && !target.Field.IsStatic && isObject(o) && HirBuilder.IsPure(value) ? target.Field : null;
        bool This(HExpr e) => e is HArg { Index: < 0 };
        bool Created(HExpr e) => e is HLocal l && ReferenceEquals(l.Variable, created);

        var unifier = new Unifier(created, parameters);
        for (int a = 0; a < length;)
        {
            if (Filled(statements[a], This) == null)
            {
                // Anything else stands where it stands.
                if (Filled(site[start + a], Created) != null || !unifier.Statement(statements[a], site[start + a], a)) return null;
                a++;
                continue;
            }
            // A run of stores: the same fields are filled at the site over the same stretch.
            int b = a;
            while (b < length && Filled(statements[b], This) != null) b++;
            var used = new bool[b - a];
            for (int j = a; j < b; j++)
                if (Filled(site[start + j], Created) == null)
                    return null;
            for (int k = a; k < b; k++)
            {
                FieldDef field = Filled(statements[k], This)!;
                int at = -1;
                for (int j = a; j < b && at < 0; j++)
                    if (!used[j - a] && ReferenceEquals(Filled(site[start + j], Created), field))
                        at = j;
                if (at < 0 || !unifier.Statement(statements[k], site[start + at], at)) return null;
                used[at - a] = true;
            }
            a = b;
        }
        return unifier;
    }

    internal static bool Mentions(HStmt statement, HVar variable) => statement switch
    {
        HAssign a => Mentions(a.Target, variable) || Mentions(a.Value, variable),
        HEval e => Mentions(e.Expression, variable),
        HReturn r => r.Value != null && Mentions(r.Value, variable),
        HThrow t => t.Exception != null && Mentions(t.Exception, variable),
        HBranch b => Mentions(b.Condition, variable),
        HSwitch s => Mentions(s.Value, variable),
        _ => false,
    };

    internal static bool Mentions(HExpr? e, HVar variable) => e switch
    {
        null => false,
        HLocal l => ReferenceEquals(l.Variable, variable),
        HField f => Mentions(f.Object, variable),
        HElement el => Mentions(el.Array, variable) || Mentions(el.Index, variable),
        HArrayLength len => Mentions(len.Array, variable),
        HAddressOf a => Mentions(a.Target, variable),
        HDeref d => Mentions(d.Pointer, variable),
        HUnary u => Mentions(u.Operand, variable),
        HBinary b => Mentions(b.Left, variable) || Mentions(b.Right, variable),
        HCompare c => Mentions(c.Left, variable) || Mentions(c.Right, variable),
        HConv c => Mentions(c.Operand, variable),
        HCall call => Mentions(call.This, variable) || call.Arguments.Any(a => Mentions(a, variable)),
        HNewObject n => n.Arguments.Any(a => Mentions(a, variable)),
        HNewArray na => Mentions(na.Length, variable),
        HTypeExpr t => Mentions(t.Operand, variable),
        HSelect s => Mentions(s.Condition, variable) || Mentions(s.WhenTrue, variable) || Mentions(s.WhenFalse, variable),
        HOpaque o => o.Operands.Any(a => Mentions(a, variable)),
        _ => false,
    };

    private static bool ReadsMemory(HExpr? e) => e switch
    {
        null => false,
        HField or HElement or HDeref or HArrayLength => true,
        HAddressOf a => a.Target is HField { Object: { } o } ? ReadsMemory(o) : a.Target is HElement,
        HUnary u => ReadsMemory(u.Operand),
        HBinary b => ReadsMemory(b.Left) || ReadsMemory(b.Right),
        HCompare c => ReadsMemory(c.Left) || ReadsMemory(c.Right),
        HConv c => ReadsMemory(c.Operand),
        HTypeExpr t => ReadsMemory(t.Operand),
        HSelect s => ReadsMemory(s.Condition) || ReadsMemory(s.WhenTrue) || ReadsMemory(s.WhenFalse),
        _ => false,
    };

    /// <summary>Matches a constructor's statements against the statements at a creation site.</summary>
    private sealed class Unifier(HVar created, int parameters)
    {
        /// <summary>What the site has where the constructor has each parameter.</summary>
        public readonly HExpr?[] Arguments = new HExpr?[parameters];
        private readonly int[] _boundAt = new int[parameters];
        private readonly Dictionary<HVar, HVar> _locals = [];
        private readonly HashSet<HVar> _siteLocals = [];
        private int _statement;
        /// <summary>The constructor compared (for the types of its parameters); null where only their number is known.</summary>
        public MethodDef? Constructor;

        private static readonly bool NoSolving = Environment.GetEnvironmentVariable("REWIND_NO_SOLVED_ARGUMENTS") != null;

        /// <summary>The whole numbers tried for an argument: the small ones, and the round ones beyond.</summary>
        private static readonly long[] Tried = MakeTried();

        private static long[] MakeTried()
        {
            var tried = new List<long>();
            for (long n = -64; n <= 4096; n++) tried.Add(n);
            for (int k = 13; k <= 30; k++)
            {
                tried.Add((1L << k) - 1);
                tried.Add(1L << k);
            }
            for (long n = 5000; n <= 1_000_000_000; n *= 10)
            {
                tried.Add(n);
                tried.Add(n * 2);
            }
            tried.Add(int.MaxValue);
            tried.Add(int.MinValue);
            return [.. tried.Distinct()];
        }

        /// <summary>
        /// Finds the constant a parameter was handed that makes what the constructor computes with it come out
        /// as the constant the place has ("1f / (float)targetFPS" stands there as 0.033333335f: targetFPS was
        /// 30) - the compiler does that arithmetic itself where it knows the argument. Only for a whole number
        /// or a yes/no, and only when exactly one of the values tried gives that constant.
        /// </summary>
        private bool Solved(HExpr computed, object worked)
        {
            if (NoSolving || Constructor == null) return false;
            int parameter = -1;
            bool fine = true;
            void Look(HExpr? e)
            {
                switch (e)
                {
                    case HConst { Value: not null }:
                        break;
                    case HArg { Index: >= 0 } a when a.Index < Arguments.Length:
                        if (Arguments[a.Index] is { } bound) fine &= bound is HConst { Value: not null };
                        else if (parameter < 0 || parameter == a.Index) parameter = a.Index;
                        else fine = false;
                        break;
                    case HBinary b: Look(b.Left); Look(b.Right); break;
                    case HCompare c: Look(c.Left); Look(c.Right); break;
                    case HSelect s: Look(s.Condition); Look(s.WhenTrue); Look(s.WhenFalse); break;
                    case HConv c: Look(c.Operand); break;
                    case HUnary u: Look(u.Operand); break;
                    default: fine = false; break;
                }
            }
            Look(computed);
            if (!fine || Plain(worked) is not { } wanted) return false;
            if (parameter < 0) return Equal(Worth(computed, -1, 0), wanted);

            TypeSig type = Constructor.Parameters[parameter].Type;
            bool flag = type is PrimitiveSig { Element: Il2CppTypeEnum.Boolean };
            if (!flag && type is not PrimitiveSig { Element: Il2CppTypeEnum.I4 }) return false;
            long found = 0;
            int fits = 0;
            foreach (long candidate in flag ? [0L, 1L] : Tried)
            {
                if (!Equal(Worth(computed, parameter, candidate), wanted)) continue;
                found = candidate;
                if (++fits > 1) return false;
            }
            if (fits != 1) return false;
            Arguments[parameter] = flag ? new HConst(found != 0, type) : new HConst((int)found, type);
            _boundAt[parameter] = _statement;
            return true;
        }

        /// <summary>A constant as the arithmetic here has it: a whole number (yes/no as 1/0), a float or a double.</summary>
        private static object? Plain(object? value) => value switch
        {
            bool b => b ? 1L : 0L,
            int n => (long)n,
            long n => n,
            float f => f,
            double d => d,
            _ => null,
        };

        private static bool Equal(object? a, object b) => (a, b) switch
        {
            (long x, long y) => x == y,
            (float x, float y) => BitConverter.SingleToInt32Bits(x) == BitConverter.SingleToInt32Bits(y),
            (double x, double y) => BitConverter.DoubleToInt64Bits(x) == BitConverter.DoubleToInt64Bits(y),
            _ => false,
        };

        /// <summary>
        /// What an expression is worth with a parameter standing for a number; null where that is not certain
        /// (anything but plain arithmetic on 32-bit whole numbers, floats and doubles, each kept to its kind).
        /// </summary>
        private object? Worth(HExpr e, int parameter, long handed)
        {
            static object? Whole(long n) => n is >= int.MinValue and <= int.MaxValue ? n : null;
            switch (e)
            {
                case HConst c:
                    return Plain(c.Value) is long number ? Whole(number) : Plain(c.Value);
                case HArg a:
                    if (a.Index == parameter) return handed;
                    return a.Index >= 0 && a.Index < Arguments.Length && Arguments[a.Index] is HConst known && Plain(known.Value) is { } had ? (had is long w ? Whole(w) : had) : null;
                case HUnary { Op: HUnaryOp.Neg } u:
                    return Worth(u.Operand, parameter, handed) switch
                    {
                        long n => Whole(-n),
                        float f => -f,
                        double d => -d,
                        _ => null,
                    };
                case HUnary { Op: HUnaryOp.LogicalNot } u:
                    return Worth(u.Operand, parameter, handed) is long truth ? (truth == 0 ? 1L : 0L) : null;
                case HConv { Kind: HConvKind.R4 } c:
                    return Worth(c.Operand, parameter, handed) switch
                    {
                        long n => (float)(int)n,
                        float f => f,
                        double d => (float)d,
                        _ => null,
                    };
                case HConv { Kind: HConvKind.R8 } c:
                    return Worth(c.Operand, parameter, handed) switch
                    {
                        long n => (double)(int)n,
                        float f => (double)f,
                        double d => d,
                        _ => null,
                    };
                case HConv { Kind: HConvKind.I4 } c:
                    return Worth(c.Operand, parameter, handed) switch
                    {
                        long n => n,
                        float f when f > -2.0e9f && f < 2.0e9f => (long)(int)f,
                        double d when d > -2.0e9 && d < 2.0e9 => (long)(int)d,
                        _ => null,
                    };
                case HSelect s:
                    return Worth(s.Condition, parameter, handed) is long which ? Worth(which != 0 ? s.WhenTrue : s.WhenFalse, parameter, handed) : null;
                case HCompare c:
                {
                    int? order = (Worth(c.Left, parameter, handed), Worth(c.Right, parameter, handed)) switch
                    {
                        (long x, long y) => x.CompareTo(y),
                        // (A float that is no number is neither less nor more nor equal: left alone.)
                        (float x, float y) when !float.IsNaN(x) && !float.IsNaN(y) => x.CompareTo(y),
                        (double x, double y) when !double.IsNaN(x) && !double.IsNaN(y) => x.CompareTo(y),
                        _ => null,
                    };
                    if (order is not { } o) return null;
                    return c.Op switch
                    {
                        HCompareOp.Eq => o == 0 ? 1L : 0L,
                        HCompareOp.Ne => o != 0 ? 1L : 0L,
                        HCompareOp.Lt => o < 0 ? 1L : 0L,
                        HCompareOp.Le => o <= 0 ? 1L : 0L,
                        HCompareOp.Gt => o > 0 ? 1L : 0L,
                        HCompareOp.Ge => o >= 0 ? 1L : 0L,
                        _ => null,
                    };
                }
                case HBinary b:
                    return (b.Op, Worth(b.Left, parameter, handed), Worth(b.Right, parameter, handed)) switch
                    {
                        (HBinaryOp.Add, long x, long y) => Whole(x + y),
                        (HBinaryOp.Sub, long x, long y) => Whole(x - y),
                        (HBinaryOp.Mul, long x, long y) => Whole(x * y),
                        (HBinaryOp.Div, long x, long y) when y != 0 => Whole(x / y),
                        (HBinaryOp.Add, float x, float y) => x + y,
                        (HBinaryOp.Sub, float x, float y) => x - y,
                        (HBinaryOp.Mul, float x, float y) => x * y,
                        (HBinaryOp.Div, float x, float y) => x / y,
                        (HBinaryOp.Add, double x, double y) => x + y,
                        (HBinaryOp.Sub, double x, double y) => x - y,
                        (HBinaryOp.Mul, double x, double y) => x * y,
                        (HBinaryOp.Div, double x, double y) => x / y,
                        _ => null,
                    };
                default:
                    return null;
            }
        }

        public bool Statement(HStmt constructor, HStmt site, int index)
        {
            _statement = index;
            switch (constructor, site)
            {
                case (HAssign c, HAssign s):
                    if (c.Target is HLocal cl)
                    {
                        // A temporary of the constructor: the site has one of its own in the same role.
                        if (s.Target is not HLocal sl || ReferenceEquals(sl.Variable, created)) return false;
                        if (_locals.TryGetValue(cl.Variable, out HVar? known)) { if (!ReferenceEquals(known, sl.Variable)) return false; }
                        else if (!_siteLocals.Add(sl.Variable)) return false;
                        else _locals[cl.Variable] = sl.Variable;
                    }
                    else if (!Expression(c.Target, s.Target)) return false;
                    return Expression(c.Value, s.Value);
                case (HEval c, HEval s):
                    return Expression(c.Expression, s.Expression);
                default:
                    return false;
            }
        }

        private bool All(HExpr[] constructor, HExpr[] site)
        {
            if (constructor.Length != site.Length) return false;
            for (int i = 0; i < constructor.Length; i++)
                if (!Expression(constructor[i], site[i]))
                    return false;
            return true;
        }

        private static bool SameTypes(TypeSig[] a, TypeSig[] b)
        {
            if (a.Length != b.Length) return false;
            for (int i = 0; i < a.Length; i++)
                if (!ReferenceEquals(a[i], b[i]))
                    return false;
            return true;
        }

        private bool Expression(HExpr? constructor, HExpr? site)
        {
            if (constructor == null || site == null) return constructor == null && site == null;
            // A constant where the constructor computes: worked out by the compiler from a constant handed over.
            if (site is HConst { Value: { } worked } && constructor is HBinary or HSelect or HConv or HUnary && Solved(constructor, worked)) return true;
            switch (constructor)
            {
                case HArg { Index: < 0 }:
                    return site is HLocal self && ReferenceEquals(self.Variable, created);
                case HArg a:
                    if (a.Index >= Arguments.Length) return false;
                    if (Arguments[a.Index] is { } bound) return HirCleanup.Same(bound, site);
                    if (!HirBuilder.IsPure(site) || Mentions(site, created)) return false;
                    Arguments[a.Index] = site;
                    _boundAt[a.Index] = _statement;
                    return true;
                case HLocal l:
                    return site is HLocal sl && _locals.TryGetValue(l.Variable, out HVar? mapped) && ReferenceEquals(mapped, sl.Variable);
                case HConst c:
                    return site is HConst sc && Equals(c.Value, sc.Value);
                case HField f:
                    return site is HField sf && ReferenceEquals(f.Field, sf.Field) && Expression(f.Object, sf.Object);
                case HElement el:
                    return site is HElement se && Expression(el.Array, se.Array) && Expression(el.Index, se.Index);
                case HArrayLength len:
                    return site is HArrayLength sl2 && Expression(len.Array, sl2.Array);
                case HAddressOf addr:
                    return site is HAddressOf sa && Expression(addr.Target, sa.Target);
                case HDeref d:
                    return site is HDeref sd && Expression(d.Pointer, sd.Pointer);
                case HUnary u:
                    return site is HUnary su && u.Op == su.Op && Expression(u.Operand, su.Operand);
                case HBinary b:
                    return site is HBinary sb && b.Op == sb.Op && Expression(b.Left, sb.Left) && Expression(b.Right, sb.Right);
                case HCompare c:
                    return site is HCompare sc2 && c.Op == sc2.Op && Expression(c.Left, sc2.Left) && Expression(c.Right, sc2.Right);
                case HConv c:
                    return site is HConv sc3 && c.Kind == sc3.Kind && Expression(c.Operand, sc3.Operand);
                case HSelect s:
                    return site is HSelect ss && Expression(s.Condition, ss.Condition) && Expression(s.WhenTrue, ss.WhenTrue) && Expression(s.WhenFalse, ss.WhenFalse);
                case HTypeExpr t:
                    return site is HTypeExpr st && t.Op == st.Op && t.Op != HTypeOp.Allocate && ReferenceEquals(t.Target, st.Target) && Expression(t.Operand, st.Operand);
                case HCall call:
                    // Methods that share their machine code are told apart by guessing; the guess made in the
                    // constructor and the one made at the site can differ for what is the same call.
                    return site is HCall sc4 &&
                           (ReferenceEquals(call.Method, sc4.Method) ||
                            (call.Method.Parameters.Length == sc4.Method.Parameters.Length && call.Method.IsStatic == sc4.Method.IsStatic &&
                             (call.Alternatives.Contains(sc4.Method) || sc4.Alternatives.Contains(call.Method)))) &&
                           call.Virtual == sc4.Virtual &&
                           SameTypes(call.MethodArguments, sc4.MethodArguments) && Expression(call.This, sc4.This) && All(call.Arguments, sc4.Arguments);
                case HNewObject n:
                    return site is HNewObject sn && ReferenceEquals(n.Constructor, sn.Constructor) && All(n.Arguments, sn.Arguments);
                case HNewArray na:
                    return site is HNewArray sna && ReferenceEquals(na.ElementType, sna.ElementType) && Expression(na.Length, sna.Length);
                case HMethodPointer p:
                    return site is HMethodPointer sp && ReferenceEquals(p.Method, sp.Method) && SameTypes(p.MethodArguments, sp.MethodArguments) &&
                           p.VirtualOn?.Index == sp.VirtualOn?.Index;
                case HMemberToken m:
                    return site is HMemberToken sm && ReferenceEquals(m.Method, sm.Method) && ReferenceEquals(m.Field, sm.Field);
                case HCachedDelegate cached:
                    return site is HCachedDelegate kept && ReferenceEquals(cached.Cache.Field, kept.Cache.Field) && Expression(cached.Creation, kept.Creation);
                default:
                    return false;
            }
        }

        /// <summary>
        /// The values found for the parameters are computed once, before the constructor runs. That is the same
        /// as where they were found only if nothing the constructor did earlier could have changed them.
        /// </summary>
        public bool ArgumentsAreValid(List<HStmt> site, int start, int length)
        {
            // Statements that only fill the new object (which nothing else can see yet) change nothing an
            // argument could depend on.
            int firstEffect = length;
            for (int k = 0; k < length; k++)
            {
                bool inert = site[start + k] switch
                {
                    HAssign { Target: HField { Object: HLocal o }, Value: var value } => ReferenceEquals(o.Variable, created) && HirBuilder.IsPure(value),
                    HEval { Expression: HCall { Method: { Name: ".ctor", Parameters.Length: 0 } m, This: HLocal o } } =>
                        ReferenceEquals(o.Variable, created) && m.DeclaringType.BaseType == null,
                    _ => false,
                };
                if (!inert)
                {
                    firstEffect = k;
                    break;
                }
            }
            for (int i = 0; i < Arguments.Length; i++)
            {
                if (Arguments[i] is not { } value) continue;
                foreach (HVar inner in _siteLocals)
                    if (Mentions(value, inner))
                        return false;
                if (ReadsMemory(value) && _boundAt[i] > firstEffect) return false;
            }
            return true;
        }
    }
}
