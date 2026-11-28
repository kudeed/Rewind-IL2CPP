using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Puts small methods of other classes back where the C++ compiler pasted their statements.
///
/// What gives such a place away is a member the method could not have named: a private field of another class,
/// a private method of it. The source called something public there - "Quaternion.Euler(x, y, z)", "list.Add(x)",
/// "a == b" on two structs - and the compiler replaced the call with what that method does. Here the methods of
/// the class that owns the member are looked at (their statements recovered from their own machine code, the
/// same way); where the statements at hand are those of one of them, with particular values in place of its
/// parameters, they become a call of it again.
///
/// A method that runs straight through is compared statement by statement. One with branches is compared along
/// every way through it: the same tests leading to the same statements, until each way reaches a return - and
/// all of those must then go on at one place in the code at hand, with the returned value in one variable.
/// Methods of generic classes are taken from the code of some of their instantiations, with the type arguments
/// standing for whatever the place has there. What matches nothing stays as it is, which does the same thing
/// either way.
/// </summary>
internal sealed class InlineFolding(MethodPipeline pipeline, ProgramAnalysis program)
{
    private Il2CppModel Model => program.Model;
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_FOLD") != null;
    private static readonly bool NoFlows = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_FLOWS") != null;
    private static readonly bool NoGenerics = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_GENERICS") != null;
    private static readonly bool NoPutBack = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_PUT_BACK") != null;
    private static readonly bool NoHandedOn = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_HANDED_ON") != null;
    private static readonly bool NoKept = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_KEPT") != null;
    private static readonly bool NoWritten = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_WRITTEN") != null;
    private static readonly bool NoBehind = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_BEHIND") != null;
    private static readonly bool NoSlots = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_SLOTS") != null;
    private static readonly bool NoDecided = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_DECIDED") != null;
    private static readonly bool NoRenamedEnds = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_RENAMED_ENDS") != null;
    private static readonly bool NoStackParts = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_STACK_PARTS") != null;
    private static readonly bool NoStructFlows = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_STRUCT_FLOWS") != null;
    private static readonly bool NoElidedStores = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_ELIDED") != null;
    private static readonly bool NoWhole = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_WHOLE") != null;

    /// <summary>
    /// A struct made on the spot from plain values by a constructor that only stores them: a value written out.
    /// Making it computes nothing and touches nothing, so it is the same value wherever it is written.
    /// </summary>
    private bool Written(HExpr? e)
    {
        if (NoWritten || e is not HNewObject { Constructor: var constructor } made || made.Type is not { IsValueType: true }) return false;
        foreach (HExpr argument in made.Arguments)
            if (!HirBuilder.IsPure(argument) && !Written(argument))
                return false;
        return StructFolding.OnlyStores(constructor, made.Type, pipeline);
    }

    /// <summary>
    /// A struct handed to a method arrives in pieces where the compiler finds that convenient: its fields are
    /// read into registers at the top ("x = item.x; y = item.y") and the struct is put together again where it
    /// is stored ("items[n] = new Vector2(x, y)"). The method said "item" there. Puts the fields back where
    /// they are used, and the parameter back where all of it is made anew - for a parameter that the method
    /// neither changes nor takes the address of, so that it is the same all the way through.
    /// </summary>
    internal void WholeParameters(HMethod? h)
    {
        if (NoWhole || h == null || h.Blocks.Count == 0 || h.TryRegions.Count != 0) return;
        var sets = new Dictionary<HVar, int>();
        var touched = new HashSet<int>();
        static HExpr Root(HExpr e)
        {
            while (e is HField { Object: { } inside }) e = inside;
            return e;
        }
        foreach (HBlock b in h.Blocks)
            foreach (HStmt s in b.Statements)
            {
                if (s is HAssign { Target: var target })
                {
                    if (target is HLocal { Variable: var set }) sets[set] = sets.GetValueOrDefault(set) + 1;
                    if (Root(target) is HArg { Index: >= 0 } changed) touched.Add(changed.Index);
                }
                FinallyFolding.Visit(s, e =>
                {
                    if (e is HAddressOf { Target: var pointed } && Root(pointed) is HArg { Index: >= 0 } parameter) touched.Add(parameter.Index);
                });
            }
        var parts = new Dictionary<HVar, HField>();
        List<HStmt> entry = h.Blocks[0].Statements;
        foreach (HStmt s in entry)
            if (s is HAssign { Target: HLocal { Variable: var t }, Value: HField { Object: HArg { Index: >= 0 } p } part } &&
                sets[t] == 1 && !t.AddressTaken && !touched.Contains(p.Index) && !part.Field.IsStatic &&
                p.Type is { IsValueType: true } and not (ByRefSig or PointerSig))
                parts[t] = part;
        if (parts.Count == 0) return;

        // Only where it gives the parameter back whole somewhere: otherwise the method is left as it was read.
        HExpr? Whole(HExpr e)
        {
            if (e is not HNewObject { Constructor: var constructor } made || made.Type is not { IsValueType: true } type || made.Arguments.Length == 0) return null;
            int from = -1;
            var fields = new FieldDef[made.Arguments.Length];
            for (int k = 0; k < made.Arguments.Length; k++)
            {
                HField? read = made.Arguments[k] switch
                {
                    HLocal { Variable: var v } when parts.TryGetValue(v, out HField? known) => known,
                    HField { Object: HArg { Index: >= 0 } } direct => direct,
                    _ => null,
                };
                if (read is not { Object: HArg { Index: var index } owner } || touched.Contains(index) || (from >= 0 && index != from)) return null;
                if (owner.Type == null || owner.Type.Key != type.Key) return null;
                from = index;
                fields[k] = read.Field;
            }
            if (!StructFolding.OnlyStores(constructor, type, pipeline)) return null;
            TypeSig[] classArguments = type is GenericInstSig g ? g.Arguments : [];
            if (pipeline.ConstructorBody(constructor, classArguments) is not { } body) return null;
            List<HStmt> stores = body.Blocks[0].Statements;
            var stored = new HashSet<FieldDef>();
            for (int k = 0; k < stores.Count - 1; k++)
            {
                // Every field from the parameter of the same name's place: "this.F = parameter k" with the place handing over "item.F".
                if (stores[k] is not HAssign { Target: HField { Field: var field }, Value: HArg { Index: var parameter } } || parameter >= fields.Length ||
                    !ReferenceEquals(fields[parameter], field) || !stored.Add(field))
                    return null;
            }
            if (type.Definition == null || stored.Count != type.Definition.Fields.Count(f => !f.IsStatic)) return null;
            return new HArg(from) { Type = type };
        }
        bool any = false;
        foreach (HBlock b in h.Blocks)
            foreach (HStmt s in b.Statements)
                FinallyFolding.Visit(s, e => any |= Whole(e) != null);
        if (!any) return;

        entry.RemoveAll(s => s is HAssign { Target: HLocal { Variable: var t } } && parts.ContainsKey(t));
        foreach (HBlock b in h.Blocks)
            foreach (HStmt s in b.Statements)
            {
                EnumeratorLoops.Rewrite(s, e => Whole(e));
                EnumeratorLoops.Rewrite(s, e => e is HLocal { Variable: var v } && parts.TryGetValue(v, out HField? part)
                    ? new HField { Object = new HArg(((HArg)part.Object!).Index) { Type = part.Object!.Type }, Field = part.Field, DeclaringType = part.DeclaringType, Type = part.Type }
                    : null);
            }
        h.Locals.RemoveAll(parts.ContainsKey);
    }
    /// <summary>REWIND_INLINE_TRACE=text: says on the error stream what was made of the methods whose name contains the text.</summary>
    private static readonly string? Traced = Environment.GetEnvironmentVariable("REWIND_INLINE_TRACE");

    private static bool Tracing(MethodDef m) => Traced != null && m.FullName.Contains(Traced, StringComparison.Ordinal);

    /// <summary>REWIND_INLINE_SITE=text: says which members of other classes the methods whose name contains the text name, and how many models there are for each.</summary>
    private static readonly string? TracedSite = Environment.GetEnvironmentVariable("REWIND_INLINE_SITE");

    private sealed class Template
    {
        public required MethodDef Method;
        /// <summary>For a method of a generic class: the type arguments of the instantiation whose code this is.</summary>
        public TypeSig[] ClassArguments = [];
        /// <summary>... and the ones the place has (its code may be shared: every class runs what was made for "object").</summary>
        public TypeSig[] SiteArguments = [];
        /// <summary>... and the class as the place has it.</summary>
        public TypeSig? Declaring;
        /// <summary>A method with branches: what may have happened before each of its statements, on any way to it.</summary>
        public Dictionary<HStmt, Effects>? Before;
        /// <summary>What the method does before it returns (a method without branches).</summary>
        public List<HStmt> Statements = [];
        /// <summary>What it returns (null: nothing).</summary>
        public HExpr? Result;
        /// <summary>A method with branches: all of it.</summary>
        public HMethod? Flow;
        /// <summary>The fields it touches and the methods it calls.</summary>
        public readonly HashSet<object> Members = [];
        public int Size;
        // (Looked at on first use, by whichever thread uses the model first: each kept as one number, which
        // another thread reads whole or not at all.)
        private volatile int _early, _ownFirst;
        /// <summary>Whether it reads all its parameters before it does anything else (see ReadsFirst); null: not looked at yet.</summary>
        public bool? Early
        {
            get => _early == 0 ? null : _early == 2;
            set => _early = value == null ? 0 : value.Value ? 2 : 1;
        }
        /// <summary>Whether it names its object once, as the first thing it works out, and does not change it (see ThisFirst); null: not looked at yet.</summary>
        public bool? OwnFirst
        {
            get => _ownFirst == 0 ? null : _ownFirst == 2;
            set => _ownFirst = value == null ? 0 : value.Value ? 2 : 1;
        }
    }

    private HExpr[]? Reexpress(HNewObject made, MethodDef wanted) => StructFolding.Reexpress(made, wanted, pipeline);

    private static readonly bool NoZeroMade = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_ZERO_MADE") != null;

    /// <summary>
    /// Whether a struct constructor puts a parameter or a zero into every field of its struct: it makes the
    /// struct "default" exactly when it is given zeros.
    /// </summary>
    private bool ZeroMade(MethodDef constructor, TypeSig? made)
    {
        TypeSig[] classArguments = made is GenericInstSig g ? g.Arguments : [];
        if (pipeline.ConstructorBody(constructor, classArguments) is not { } body) return false;
        List<HStmt> statements = body.Blocks[0].Statements;
        var stored = new HashSet<FieldDef>();
        for (int k = 0; k < statements.Count - 1; k++)
        {
            if (statements[k] is not HAssign { Target: HField { Object: HArg { Index: < 0 } } target, Value: var value }) return false;
            bool fits = value switch
            {
                HArg { Index: >= 0 } => true,
                HConst { Value: null } => true,
                HConst { Value: float f } => BitConverter.SingleToInt32Bits(f) == 0,
                HConst { Value: double d } => BitConverter.DoubleToInt64Bits(d) == 0,
                HConst { Value: bool b } => !b,
                HConst { Value: int i } => i == 0,
                HConst { Value: long l } => l == 0,
                _ => false,
            };
            if (!fits) return false;
            stored.Add(target.Field);
        }
        return constructor.DeclaringType.Fields.Where(f => !f.IsStatic).All(stored.Contains);
    }

    /// <summary>The zero of a number type, or "null" of a reference: what a field of a "default" struct holds.</summary>
    private static HExpr? Zero(TypeSig? type) => type switch
    {
        PrimitiveSig { Element: Il2CppTypeEnum.R4 } => new HConst(0f, type),
        PrimitiveSig { Element: Il2CppTypeEnum.R8 } => new HConst(0.0, type),
        PrimitiveSig { Element: Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 } => new HConst(0L, type),
        PrimitiveSig { Element: Il2CppTypeEnum.Boolean } => new HConst(false, type),
        PrimitiveSig { Element: Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 or Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 or Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 or Il2CppTypeEnum.Char } =>
            new HConst(0, type),
        PrimitiveSig or PointerSig or ByRefSig or GenericParamSig or OpaqueSig => null,
        { IsValueType: false } => new HConst(null, type),
        _ => null,
    };

    // What pasted code is compared with is the same whoever makes it - nothing in it depends on the method that
    // first needs it - so it is kept for every pipeline of this one's kind and every thread
    // (RecoveryCache.Templates). What would be made while a recovery for another's use is under way would hold
    // just there, and is not kept at all (pasted code is put back in the method asked for, not in what that
    // asks for: it does not happen).
    private bool Made<T>(object key, out T? made) where T : class
    {
        object? found = null;
        bool known = pipeline.NothingUnderWay && pipeline.Kept.Templates.TryGetValue(key, out found);
        made = (T?)found;
        return known;
    }

    private T? Keep<T>(object key, T? made) where T : class
    {
        if (pipeline.NothingUnderWay) return (T?)pipeline.Kept.Templates.GetOrAdd(key, made);
        RecoveryStats.NotKept();
        return made;
    }

    private static int Rank(MethodDef m) => m.Name.StartsWith("op_", StringComparison.Ordinal) ? 0 : m.Name.StartsWith("get_", StringComparison.Ordinal) ? 1 : 2;

    /// <summary>The type whose code a type argument's code is shared with: every class runs what was made for "object".</summary>
    private TypeSig Shared(TypeSig type, bool enums)
    {
        if (type is PointerSig or ByRefSig or GenericParamSig or OpaqueSig) return type;
        if (!type.IsValueType) return program.Model.Sigs.Primitive(Il2CppTypeEnum.Object);
        if (enums && type is TypeDefSig { Definition: { IsEnum: true } definition })
        {
            foreach (FieldDef f in definition.Fields)
                if (!f.IsStatic)
                    return f.Type;
            return type;
        }
        if (type is GenericInstSig g)
        {
            var arguments = new TypeSig[g.Arguments.Length];
            bool changed = false;
            for (int i = 0; i < arguments.Length; i++)
            {
                arguments[i] = Shared(g.Arguments[i], enums);
                changed |= !ReferenceEquals(arguments[i], g.Arguments[i]);
            }
            return changed ? program.Model.Sigs.GenericInst(g.Definition, arguments) : type;
        }
        return type;
    }

    /// <summary>The compiled body a method of a generic class has for these type arguments: its own, or the one it shares.</summary>
    private MethodInst? InstanceFor(MethodDef m, TypeSig[] arguments)
    {
        IReadOnlyList<MethodInst> all = program.InstsOf(m);
        if (all.Count == 0) return null;
        for (int form = 0; form < 3; form++)
        {
            TypeSig[] wanted = form == 0 ? arguments : arguments.Select(a => Shared(a, form == 2)).ToArray();
            foreach (MethodInst inst in all)
            {
                if (inst.Address == 0 || inst.MethodArguments.Length != 0 || inst.ClassArguments.Length != wanted.Length) continue;
                bool same = true;
                for (int i = 0; i < wanted.Length && same; i++) same = ReferenceEquals(inst.ClassArguments[i], wanted[i]);
                if (same) return inst;
            }
        }
        return null;
    }

    /// <summary>The methods of the class a member belongs to; for a generic class, as compiled for the type arguments the place has.</summary>
    private List<Template> TemplatesOf(TypeDef type, TypeSig? instance) => TemplatesOf(type, instance, Levels);

    private List<Template> TemplatesOf(TypeDef type, TypeSig? instance, int level)
    {
        if (type.GenericParameters.Length == 0) return TemplatesOf(type, level);
        if (NoGenerics || instance is not GenericInstSig g || !ReferenceEquals(g.Definition, type) || g.ContainsGenericParameter) return [];
        if (Made(g, out List<Template>? known)) return known!;
        var list = new List<Template>();
        long started = RecoveryStats.Begin();
        foreach (MethodDef m in type.Methods)
        {
            if (m.IsAbstract || m.IsConstructor || m.GenericParameters.Length != 0 || m.Name == ".cctor") continue;
            if (InstanceFor(m, g.Arguments) is not { } inst) continue;
            if (program.Code.Get(inst.Address) is not { Instructions: <= 200 } code) continue;
            HMethod? body = pipeline.CoreBody(inst);
            Template? template = code.Instructions <= 96 ? Make(m, body) : null;
            if (template == null && !NoFlows) template = MakeFlow(m, body);
            if (Tracing(m))
            {
                Console.Error.WriteLine($"[inline] {inst} at 0x{inst.Address:X} for {g.ShortName}: {code.Instructions} instructions, {(body == null ? "not recovered" : body.Blocks.Count + " blocks")}, {(template == null ? "no template" : template.Flow != null ? "with branches" : "straight")}");
                if (body == null)
                    try { foreach (string problem in pipeline.Recover(inst).Problems.Distinct()) Console.Error.WriteLine("[inline]   ! " + problem); }
                    catch (Exception e) { Console.Error.WriteLine("[inline]   ! " + e.Message); }
                else Console.Error.WriteLine(HirPrinter.Print(body));
            }
            if (template == null) continue;
            template.ClassArguments = inst.ClassArguments;
            template.SiteArguments = g.Arguments;
            template.Declaring = g;
            list.Add(template);
        }
        list = list.OrderByDescending(t => t.Size).ThenBy(t => Rank(t.Method)).ToList();
        RecoveryStats.End(RecoveryStats.Kind.Templates, started);
        return Keep(g, list)!;
    }

    /// <summary>
    /// How many times over a method with branches is taken with what it has pasted in of other classes put
    /// back (see TemplatesOf): in the methods of those classes the same is done one time less, and so on down
    /// to their statements as they stand. What a class's list is must not depend on which class was asked for
    /// first, and two classes whose methods each have the other's pasted in would otherwise each wait for the
    /// other's list.
    /// </summary>
    private static readonly int Levels =
        int.TryParse(Environment.GetEnvironmentVariable("REWIND_INLINE_LEVELS"), out int levels) && levels >= 0 ? levels : 2;

    /// <summary>
    /// The methods of a class as their code reads: each as its statements stand, and each also with the private
    /// methods of its class put back that it has pasted in. In the order of the class's methods.
    /// </summary>
    private List<Template> PlainTemplatesOf(TypeDef type)
    {
        if (Made((type, -1), out List<Template>? known)) return known!;
        var list = new List<Template>();
        long started = RecoveryStats.Begin();
        (MethodDef? current, HashSet<MethodDef>? barred, bool decided, bool putBack, bool partly) = (_current, _barred, _decided, _putBack, _partly);
        try
        {
            foreach (MethodDef m in type.Methods)
            {
                if (m.Address == 0 || m.IsAbstract || m.IsConstructor || m.GenericParameters.Length != 0 || m.Name == ".cctor") continue;
                if (program.Code.Get(m.Address) is not { Instructions: <= 200 } code) continue;
                HMethod? body = pipeline.CoreBody(m);
                int had = list.Count;
                if (code.Instructions <= 96 && Make(m, body) is { } template) list.Add(template);
                else if (!NoFlows && MakeFlow(m, body) is { } flow) list.Add(flow);
                if (Tracing(m))
                {
                    Console.Error.WriteLine($"[inline] {m.FullName}: {code.Instructions} instructions, {(body == null ? "not recovered" : body.Blocks.Count + " blocks")}, {(list.Count == had ? "no model" : list[^1].Flow != null ? "a model with branches" : "a model")}");
                    if (body != null) Console.Error.WriteLine(HirPrinter.Print(body));
                }
            }
            // A method may itself have had a private method of its class pasted in, which the place at hand
            // calls instead ("Euler" is "Internal_FromEulerRad" of a vector, and that is the native call).
            // So each method is also taken with those put back.
            List<Template> raw = list.Where(t => t.Flow == null).OrderByDescending(t => t.Size).ToList();
            bool Hidden(object member) => member is MethodDef m && ReferenceEquals(m.DeclaringType, type) && (m.Flags & MethodDef.AccessMask) != 6;
            foreach (Template template in raw)
            {
                if (!template.Members.Any(Hidden)) continue;
                if (pipeline.FreshCoreBody(template.Method) is not { } own) continue;
                // (The method whose statements are looked at is this one, whoever asked for the list.)
                (_current, _barred, _decided, _putBack) = (template.Method, null, false, false);
                bool changed = false;
                for (int round = 0; round < 16; round++)
                {
                    if (!Pass(own, Hidden, (_, _) => raw, t => !ReferenceEquals(t.Method, template.Method) && (t.Method.Flags & MethodDef.AccessMask) != 6, false)) break;
                    changed = true;
                }
                if (changed && Make(template.Method, own) is { } folded)
                {
                    list.Add(folded);
                    if (Tracing(template.Method)) Console.Error.WriteLine($"[inline] {template.Method.FullName}: with its class's own methods put back\n{HirPrinter.Print(own)}");
                }
            }
        }
        finally
        {
            (_current, _barred, _decided, _putBack, _partly) = (current, barred, decided, putBack, partly);
            RecoveryStats.End(RecoveryStats.Kind.Templates, started);
        }
        return Keep((type, -1), list)!;
    }

    /// <summary>
    /// The methods of a class to compare pasted code with, the largest first. At level 0 as their code reads
    /// (PlainTemplatesOf). Above that, each method with branches also with what it has pasted in of other
    /// classes put back, as far as the lists of those classes one level down show it: its own code was compiled
    /// with its assembly, where the compiler pasted in what it liked; pasted into the code of another assembly,
    /// it was compiled again there, where only what is marked for it is pasted in and the rest is called.
    /// </summary>
    private List<Template> TemplatesOf(TypeDef type, int level)
    {
        if (NoFlows || NoPutBack) level = 0;
        if (Made((type, level), out List<Template>? known)) return known!;
        var list = new List<Template>(PlainTemplatesOf(type));
        if (level > 0)
        {
            long started = RecoveryStats.Begin();
            (MethodDef? current, HashSet<MethodDef>? barred, bool decided, bool putBack, bool partly) = (_current, _barred, _decided, _putBack, _partly);
            try
            {
                bool Elsewhere(object member) => !ReferenceEquals(member is FieldDef f ? f.DeclaringType : ((MethodDef)member).DeclaringType, type);
                List<Template> Below(TypeDef other, TypeSig? instance) => TemplatesOf(other, instance, level - 1);
                foreach (Template template in list.Where(t => t.Flow != null).ToList())
                {
                    if (!template.Members.Any(Elsewhere)) continue;
                    if (pipeline.FreshCoreBody(template.Method) is not { } own) continue;
                    bool changed = false;
                    for (int round = 0; round < 32; round++)
                    {
                        // (The method whose statements are looked at is this one, whoever asked for the list.)
                        (_current, _barred, _decided, _putBack) = (template.Method, null, false, false);
                        if (!Pass(own, Elsewhere, Below, t => !ReferenceEquals(t.Method, template.Method), true)) break;
                        changed = true;
                    }
                    if (!changed) continue;
                    Template? folded = MakeFlow(template.Method, own) ?? Make(template.Method, own);
                    if (Tracing(template.Method))
                        Console.Error.WriteLine($"[inline] {template.Method.FullName}: with what it calls put back, {(folded == null ? "no model" : folded.Flow != null ? "a model with branches" : "a model")}\n{HirPrinter.Print(own)}");
                    if (folded != null) list.Add(folded);
                }
            }
            finally
            {
                (_current, _barred, _decided, _putBack, _partly) = (current, barred, decided, putBack, partly);
                RecoveryStats.End(RecoveryStats.Kind.Templates, started);
            }
        }
        // The largest first: a method that calls another small one contains that one's statements too.
        list = list.OrderByDescending(t => t.Size).ThenBy(t => Rank(t.Method)).ToList();
        return Keep((type, level), list)!;
    }

    private static void Measure(Template template, IEnumerable<HStmt> statements, HExpr? result)
    {
        void Note(HExpr e)
        {
            template.Size++;
            switch (e)
            {
                case HField f: template.Members.Add(f.Field); break;
                case HCall c: template.Members.Add(c.Method); break;
                case HNewObject n: template.Members.Add(n.Constructor); break;
            }
        }
        foreach (HStmt s in statements) FinallyFolding.Visit(s, Note);
        FinallyFolding.Visit(result, Note);
    }

    private static Template? Make(MethodDef m, HMethod? h)
    {
        if (h == null || h.Blocks.Count != 1) return null;
        List<HStmt> all = h.Blocks[0].Statements;
        if (all.Count == 0 || all.Count > 9 || all[^1] is not HReturn ret) return null;
        var statements = all.Take(all.Count - 1).ToList();
        if (statements.Any(s => s is not (HAssign or HEval))) return null;
        HExpr? result = ret.Value;
        if (m.ReturnType.IsVoid != (result == null)) return null;
        // "r = X; return r" is "return X".
        if (result is HLocal { Variable: var returned } && statements.Count != 0 &&
            statements[^1] is HAssign { Target: HLocal { Variable: var set }, Value: var value } && ReferenceEquals(returned, set))
        {
            int mentions = 0;
            foreach (HStmt s in all) FinallyFolding.Visit(s, e => mentions += e is HLocal l && ReferenceEquals(l.Variable, returned) ? 1 : 0);
            if (mentions == 2)
            {
                result = value;
                statements.RemoveAt(statements.Count - 1);
            }
        }
        var template = new Template { Method = m, Statements = statements, Result = result };
        Measure(template, statements, result);
        // A method that only hands back a parameter or a constant has nothing to recognise it by; one that
        // only reads a field of its own object is an accessor (see AccessorFolding).
        if (statements.Count == 0 && result is null or HArg or HConst or HLocal or HField { Object: null or HArg }) return null;
        return template;
    }

    /// <summary>A method with branches, as something to compare with: no loops of its own making are excluded, only what cannot be compared.</summary>
    private static Template? MakeFlow(MethodDef m, HMethod? h)
    {
        if (h == null || h.Blocks.Count < 2 || h.Blocks.Count > 24 || h.TryRegions.Count != 0) return null;
        int count = 0, returns = 0;
        bool opaque = false;
        foreach (HBlock b in h.Blocks)
        {
            if (b.Statements.Count == 0) return null;
            for (int i = 0; i < b.Statements.Count; i++)
            {
                HStmt s = b.Statements[i];
                bool last = i == b.Statements.Count - 1;
                if (last ? s is not (HJump or HBranch or HSwitch or HReturn or HThrow) : s is not (HAssign or HEval)) return null;
                // A parameter the method changes is a variable of its own: the place has no such thing to name.
                if (s is HAssign { Target: var set })
                {
                    HExpr root = set;
                    while (root is HField { Object: { } inside } part && part.Field.DeclaringType.IsValueType) root = inside;
                    if (root is HArg { Index: >= 0, Type: not (ByRefSig or PointerSig) }) return null;
                }
                if (s is HReturn r)
                {
                    if (m.ReturnType.IsVoid != (r.Value == null)) return null;
                    returns++;
                }
                FinallyFolding.Visit(s, e => opaque |= e is HOpaque);
                count++;
            }
        }
        if (count > 64 || returns == 0 || opaque) return null;
        var template = new Template { Method = m, Flow = h };
        Measure(template, h.Blocks.SelectMany(b => b.Statements), null);
        return template;
    }

    private static bool Within(TypeDef inner, TypeDef outer)
    {
        for (TypeDef? t = inner; t != null; t = t.DeclaringType)
            if (ReferenceEquals(t, outer))
                return true;
        return false;
    }

    private static bool Derives(TypeDef type, TypeDef ancestor)
    {
        int guard = 0;
        for (TypeDef? t = type; t != null && guard++ < 64; t = t.BaseType?.Definition)
            if (ReferenceEquals(t, ancestor))
                return true;
        return false;
    }

    /// <summary>Whether <paramref name="from"/> could have named the method in source.</summary>
    internal static bool IsAccessible(MethodDef callee, MethodDef from)
    {
        TypeDef user = from.DeclaringType, owner = callee.DeclaringType;
        bool sameAssembly = ReferenceEquals(user.Assembly, owner.Assembly);
        bool family = false;
        for (TypeDef? t = user; t != null && !family; t = t.DeclaringType) family = Derives(t, owner);
        return (callee.Flags & MethodDef.AccessMask) switch
        {
            6 => true,
            1 => Within(user, owner),
            3 => sameAssembly,
            4 => family || Within(user, owner),
            5 => family || sameAssembly,
            2 => family && sameAssembly,
            _ => Within(user, owner),
        };
    }

    /// <summary>
    /// Whether a method is nothing but one call of another ("void OnDestroy() => Unregister();"). Pasted in, it
    /// reads exactly as that call written out does: where the place could have made the call itself, the code
    /// does not say which of the two the source had, and the call stays as it stands.
    /// </summary>
    private static bool OnlyCalls(Template template, MethodDef called) =>
        template.Flow == null &&
        (template.Result == null
            ? template.Statements is [HEval { Expression: HCall only }] && ReferenceEquals(only.Method, called)
            : template.Statements.Count == 0 && template.Result is HCall returned && ReferenceEquals(returned.Method, called));

    /// <summary>
    /// A value that is the same wherever in the block it is computed, as long as the variables it names are not
    /// assigned in between: constants, variables nothing points to, and parts of them.
    /// </summary>
    private static bool Stable(HExpr? e) => e switch
    {
        null => true,
        HConst => true,
        HLocal l => !l.Variable.AddressTaken,
        HArg a => a.Index >= 0 && a.Type is not (ByRefSig or PointerSig),
        HField { Object: { } o } f => o.Type is { IsValueType: true } and not (ByRefSig or PointerSig) && !f.Field.IsStatic && Stable(o),
        HUnary u => Stable(u.Operand),
        HBinary b => HirBuilder.IsPure(b) && Stable(b.Left) && Stable(b.Right),
        HCompare c => Stable(c.Left) && Stable(c.Right),
        HConv c => HirBuilder.IsPure(c) && Stable(c.Operand),
        _ => false,
    };

    private sealed class Counts
    {
        public readonly Dictionary<HVar, int> Defs = [], Reads = [];
        public Dictionary<HBlock, List<HBlock>>? Before;

        public static Counts Of(HMethod method)
        {
            var c = new Counts();
            foreach (HTryRegion r in method.TryRegions.Values) c.Defs[r.Exception] = c.Defs.GetValueOrDefault(r.Exception) + 2;
            foreach (HBlock b in method.Blocks)
            {
                HVar? set = null; // what the statement before this one assigned
                foreach (HStmt s in b.Statements)
                {
                    HVar? before = set;
                    void Read(HExpr e)
                    {
                        if (e is not HLocal l) return;
                        c.Reads[l.Variable] = c.Reads.GetValueOrDefault(l.Variable) + 1;
                        if (!ReferenceEquals(l.Variable, before)) c._carried.Add(l.Variable);
                    }
                    set = null;
                    if (s is HAssign { Target: HLocal target } a)
                    {
                        c.Defs[target.Variable] = c.Defs.GetValueOrDefault(target.Variable) + 1;
                        FinallyFolding.Visit(a.Value, Read);
                        set = target.Variable;
                    }
                    else FinallyFolding.Visit(s, Read);
                }
            }
            return c;
        }

        /// <summary>Variables read somewhere other than right behind an assignment to them (see IsTemp).</summary>
        private readonly HashSet<HVar> _carried = [];

        /// <summary>
        /// Set once and read once - or set and read any number of times, each read in the statement right behind
        /// an assignment (a slot used for one argument after another): nothing is carried from one use to the next.
        /// </summary>
        public bool IsTemp(HVar v) => (Defs.GetValueOrDefault(v) == 1 && Reads.GetValueOrDefault(v) == 1) ||
                                      (!NoSlots && Defs.GetValueOrDefault(v) > 1 && Reads.GetValueOrDefault(v) == Defs.GetValueOrDefault(v) && !_carried.Contains(v));

        /// <summary>The blocks that lead to each block.</summary>
        public Dictionary<HBlock, List<HBlock>> Predecessors(HMethod method)
        {
            if (Before != null) return Before;
            Before = [];
            void Edge(HBlock from, HBlock to)
            {
                if (!Before.TryGetValue(to, out List<HBlock>? list)) Before[to] = list = [];
                if (!list.Contains(from)) list.Add(from);
            }
            foreach (HBlock b in method.Blocks)
            {
                if (b.Statements.Count == 0) continue;
                switch (b.Statements[^1])
                {
                    case HJump j: Edge(b, j.Target); break;
                    case HBranch br: Edge(b, br.WhenTrue); Edge(b, br.WhenFalse); break;
                    case HSwitch sw:
                        foreach (HBlock t in sw.Targets) Edge(b, t);
                        Edge(b, sw.Default);
                        break;
                }
            }
            return Before;
        }
    }

    /// <summary>Compares a method's statements with the statements at a place, finding what stands for its parameters.</summary>
    private sealed class Unifier
    {
        public HExpr? This;
        public HExpr?[] Arguments;
        /// <summary>The position (in the method's statements) each parameter's value was found at; -1 for "this".</summary>
        public int[] BoundAt;
        public int ThisAt = -1;
        public Dictionary<HVar, HVar> Locals = [];
        public HashSet<HVar> SiteLocals = [];
        /// <summary>Statements of the block that only set a temporary whose value was looked through.</summary>
        public HashSet<int> Consumed = [];
        /// <summary>The block the site statement being compared is in.</summary>
        public List<HStmt> Site;
        /// <summary>Variables of the place to be read as the value they were just given (see FlowMatch).</summary>
        public Dictionary<HVar, HExpr>? Given;
        /// <summary>
        /// Whether a parameter may stand for something that does work (a call). Only where the method is a
        /// single expression that does none itself and reads each parameter once: then all that matters is
        /// the order the arguments are worked out in, which Order records.
        /// </summary>
        public bool Loose;
        public bool Working;
        public List<int> Order = [];
        private readonly Counts _counts;
        public Counts Counted => _counts;
        private readonly MethodDef _method;
        public MethodDef Method => _method;
        private readonly Template _template;
        private readonly InlineFolding _owner;
        /// <summary>Where the site statement being compared stands in the block, and the method's statement it is compared with.</summary>
        public int At, Position;

        public Unifier(InlineFolding owner, Template template, List<HStmt> site, Counts counts)
        {
            _owner = owner;
            _template = template;
            _method = template.Method;
            Arguments = new HExpr?[_method.Parameters.Length];
            BoundAt = new int[_method.Parameters.Length];
            Site = site;
            _counts = counts;
        }

        public Unifier Clone() => new(_owner, _template, Site, _counts)
        {
            This = This,
            ThisAt = ThisAt,
            Arguments = (HExpr?[])Arguments.Clone(),
            BoundAt = (int[])BoundAt.Clone(),
            Locals = new Dictionary<HVar, HVar>(Locals),
            SiteLocals = [.. SiteLocals],
            Consumed = [.. Consumed],
            Given = Given,
            At = At,
            Position = Position,
            Loose = Loose,
            Working = Working,
            Order = [.. Order],
        };

        public bool Statement(HStmt method, HStmt site)
        {
            switch (method, site)
            {
                case (HAssign m, HAssign s):
                    return Expression(m.Target, s.Target) && Expression(m.Value, s.Value);
                case (HEval m, HEval s):
                    return Expression(m.Expression, s.Expression);
                default:
                    return false;
            }
        }

        private bool All(HExpr[] method, HExpr[] site)
        {
            if (method.Length != site.Length) return false;
            for (int i = 0; i < method.Length; i++)
                if (!Expression(method[i], site[i]))
                    return false;
            return true;
        }

        /// <summary>
        /// The same type - or, in the code of a generic class, the same once the place's type arguments stand
        /// for the ones this code was compiled with.
        /// </summary>
        public bool Types(TypeSig? method, TypeSig? site)
        {
            if (method == null || site == null) return method == null && site == null;
            if (ReferenceEquals(method, site)) return true;
            TypeSig[] own = _template.ClassArguments;
            for (int i = 0; i < own.Length; i++)
                if (ReferenceEquals(method, own[i]) &&
                    (ReferenceEquals(site, _template.SiteArguments[i]) || ReferenceEquals(_owner.Shared(site, false), method) || ReferenceEquals(_owner.Shared(site, true), method)))
                    return true;
            if (own.Length == 0) return false;
            switch (method, site)
            {
                case (GenericInstSig a, GenericInstSig b):
                    if (!ReferenceEquals(a.Definition, b.Definition) || a.Arguments.Length != b.Arguments.Length) return false;
                    for (int i = 0; i < a.Arguments.Length; i++)
                        if (!Types(a.Arguments[i], b.Arguments[i]))
                            return false;
                    return true;
                case (SzArraySig a, SzArraySig b): return Types(a.ElementType, b.ElementType);
                case (ArraySig a, ArraySig b): return a.Rank == b.Rank && Types(a.ElementType, b.ElementType);
                case (PointerSig a, PointerSig b): return Types(a.ElementType, b.ElementType);
                case (ByRefSig a, ByRefSig b): return Types(a.ElementType, b.ElementType);
                default: return false;
            }
        }

        private bool SameTypes(TypeSig[] a, TypeSig[] b)
        {
            if (a.Length != b.Length) return false;
            for (int i = 0; i < a.Length; i++)
                if (!Types(a[i], b[i]))
                    return false;
            return true;
        }

        private static long? Whole(object? value) => value switch
        {
            bool b => b ? 1 : 0,
            byte n => n,
            sbyte n => n,
            short n => n,
            ushort n => n,
            char n => n,
            int n => n,
            uint n => n,
            long n => n,
            _ => null,
        };

        private static bool SameConst(object? a, object? b) => (a, b) switch
        {
            (float x, float y) => BitConverter.SingleToInt32Bits(x) == BitConverter.SingleToInt32Bits(y),
            (double x, double y) => BitConverter.DoubleToInt64Bits(x) == BitConverter.DoubleToInt64Bits(y),
            // "true" and 1 are one value written two ways.
            _ => Whole(a) is { } x && Whole(b) is { } y ? x == y : Equals(a, b),
        };

        /// <summary>A number that multiplied by <paramref name="factor"/> gives exactly <paramref name="product"/>: the plainest one, if any.</summary>
        private static float? Unfold(float product, float factor)
        {
            if (factor == 0f || float.IsNaN(product) || float.IsInfinity(product) || float.IsNaN(factor) || float.IsInfinity(factor)) return null;
            if (product == 0f) return BitConverter.SingleToInt32Bits(product) == 0 ? 0f : null;
            double exact = (double)product / factor;
            for (int digits = 0; digits <= 4; digits++)
            {
                float candidate = (float)Math.Round(exact, digits);
                if (BitConverter.SingleToInt32Bits((float)(candidate * factor)) == BitConverter.SingleToInt32Bits(product)) return candidate;
            }
            float direct = (float)exact;
            return BitConverter.SingleToInt32Bits((float)(direct * factor)) == BitConverter.SingleToInt32Bits(product) ? direct : null;
        }

        /// <summary>What a temporary of the block was last given before the statement being compared (only looked at).</summary>
        private HExpr? Defined(HVar temp)
        {
            if (!_counts.IsTemp(temp)) return null;
            for (int d = Math.Min(At, Site.Count) - 1; d >= 0 && At - d <= 24; d--)
                if (Site[d] is HAssign { Target: HLocal t } definition && ReferenceEquals(t.Variable, temp))
                    return definition.Value;
            return null;
        }

        /// <summary>The same struct written out twice: the same constructor given the same plain values.</summary>
        private static bool SameWritten(HExpr a, HExpr b)
        {
            if (a is HNewObject x && b is HNewObject y)
            {
                if (!ReferenceEquals(x.Constructor, y.Constructor) || x.Arguments.Length != y.Arguments.Length) return false;
                for (int i = 0; i < x.Arguments.Length; i++)
                    if (!SameWritten(x.Arguments[i], y.Arguments[i]))
                        return false;
                return true;
            }
            return HirCleanup.Same(a, b);
        }

        /// <summary>The value a temporary of the block was given, when using that value in its place changes nothing.</summary>
        private HExpr? Through(HVar temp)
        {
            if (!_counts.IsTemp(temp)) return null;
            for (int d = Math.Min(At, Site.Count) - 1; d >= 0 && At - d <= 24; d--)
            {
                if (Site[d] is not HAssign { Target: HLocal t } definition || !ReferenceEquals(t.Variable, temp)) continue;
                // The same value where it is used as where it was worked out: nothing in between changes what it
                // reads - or nothing is in between at all (then it may be anything, the result of a call too).
                bool next = !NoKept;
                for (int k = d + 1; k < At && next; k++) next = Consumed.Contains(k);
                if (!next && ((NoKept && !Stable(definition.Value)) || !StructFolding.Movable(definition.Value, Site, d, At - 1, null))) return null;
                Consumed.Add(d);
                return definition.Value;
            }
            return null;
        }

        /// <summary>
        /// Whether the actual receiver can name the method's declaring type.
        /// Inlining a method body is not enough to justify calling that
        /// method on an unrelated receiver (for example Int32.Equals
        /// must never be put back as String.Equals).
        /// </summary>
        public bool ReceiverCompatible(TypeSig? actual)
        {
            TypeSig expected = _template.Declaring ?? _method.DeclaringType.Sig;
            if (expected.IsValueType && actual is (ByRefSig or PointerSig)) actual = actual.ElementType;
            if (actual == null || actual.IsValueType != expected.IsValueType) return false;

            bool SameInstantiation(TypeSig wanted, TypeSig found)
            {
                if (wanted.Definition == null || !ReferenceEquals(wanted.Definition, found.Definition)) return false;
                if (wanted is GenericInstSig || found is GenericInstSig)
                    return ReferenceEquals(wanted, found);
                return wanted.Definition.GenericParameters.Length == 0 || ReferenceEquals(wanted, found);
            }
            TypeSig? Substitute(TypeSig current, TypeSig parent) =>
                current is GenericInstSig instance
                    ? _owner.Model.Sigs.Substitute(parent, instance.Arguments, [])
                    : parent;
            return InlineReceiverCompatibility.IsAssignable(expected, actual, SameInstantiation, Substitute);
        }

        public bool Expression(HExpr? method, HExpr? site)
        {
            if (method == null || site == null) return method == null && site == null;
            if (Given != null && site is HLocal { Variable: var named } && Given.TryGetValue(named, out HExpr? standing)) return Expression(method, standing);
            switch (method)
            {
                case HArg { Index: < 0 }:
                    // A struct's method is handed the address of the struct: the receiver is the place itself.
                    if (_method.DeclaringType.IsValueType && site is HAddressOf { Target: var self }) site = self;
                    if (!ReceiverCompatible(site.Type)) return false;
                    if (This != null) return HirCleanup.Same(This, site);
                    // Something that does work (a call that hands over the object) only for a method that reads
                    // its object once, before it does anything else: then it is worked out first either way.
                    if (!HirBuilder.IsPure(site) && !ThisFirst(_template)) return false;
                    This = site;
                    ThisAt = Position;
                    return true;
                case HArg a:
                    if (a.Index >= Arguments.Length) return false;
                    if (Arguments[a.Index] is { } bound)
                    {
                        if (HirBuilder.IsPure(bound)) return HirCleanup.Same(bound, site);
                        // A struct written out: written out again here, or kept in a temporary this time.
                        if (!_owner.Written(bound)) return false;
                        if (site is HLocal { Variable: var again } && Defined(again) is { } kept && _owner.Written(kept)) return SameWritten(bound, kept) && Through(again) != null;
                        return SameWritten(bound, site);
                    }
                    // The place may have the struct it hands over in a temporary of its own, made just before.
                    if (!NoWritten && site is HLocal { Variable: var holder } && Defined(holder) is { } made && _owner.Written(made) && Through(holder) is { } written)
                        site = written;
                    if (!HirBuilder.IsPure(site) && !_owner.Written(site))
                    {
                        if (!Loose) return false;
                        Working = true;
                    }
                    Arguments[a.Index] = site;
                    BoundAt[a.Index] = Position;
                    Order.Add(a.Index);
                    return true;
                case HLocal l:
                {
                    if (site is not HLocal sl) return false;
                    if (Locals.TryGetValue(l.Variable, out HVar? mapped)) return ReferenceEquals(mapped, sl.Variable);
                    if (!Types(l.Variable.Type, sl.Variable.Type) || !SiteLocals.Add(sl.Variable)) return false;
                    Locals[l.Variable] = sl.Variable;
                    return true;
                }
            }
            // The struct a method is running on, as a value.
            if (method is HDeref { Pointer: HArg { Index: < 0 } whole } && _method.DeclaringType.IsValueType) return Expression(whole, site);
            // A constant argument multiplied out by the compiler ("x * k" with x known): the x that gives it.
            if (method is HBinary { Op: HBinaryOp.Mul } product && site is HConst { Value: float folded } constant)
            {
                (HExpr variable, HExpr other) = product.Left is HConst ? (product.Right, product.Left) : (product.Left, product.Right);
                return variable is HArg { Index: >= 0 } && other is HConst { Value: float factor } && Unfold(folded, factor) is float original &&
                       Expression(variable, new HConst(original, constant.Type));
            }
            // What a parameter passed by reference refers to: the place whose address the site has there.
            if (method is HDeref { Pointer: HArg { Index: >= 0 } reference } && reference.Index < Arguments.Length &&
                _method.Parameters[reference.Index].Type is ByRefSig referenceType)
            {
                if (Arguments[reference.Index] is { } known) return known is HAddressOf { Target: var place } && HirCleanup.Same(place, site);
                if (site is not (HLocal or HArg or HField or HElement or HDeref) || !HirBuilder.IsPure(site)) return false;
                Arguments[reference.Index] = new HAddressOf(site) { Type = referenceType };
                BoundAt[reference.Index] = Position;
                return true;
            }
            // The site may have the value in a temporary where the method has it written out.
            if (site is HLocal { Variable: var temp })
                return Through(temp) is { } value && Expression(method, value);
            switch (method)
            {
                case HConst c:
                    return site is HConst sc && SameConst(c.Value, sc.Value);
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
                    return site is HTypeExpr st && t.Op == st.Op && t.Op != HTypeOp.Allocate && Types(t.Target, st.Target) && Expression(t.Operand, st.Operand);
                case HCall call:
                    return site is HCall sc4 &&
                           (ReferenceEquals(call.Method, sc4.Method) ||
                            (call.Method.Parameters.Length == sc4.Method.Parameters.Length && call.Method.IsStatic == sc4.Method.IsStatic &&
                             (call.Alternatives.Contains(sc4.Method) || sc4.Alternatives.Contains(call.Method)))) &&
                           call.Virtual == sc4.Virtual && Types(call.DeclaringType, sc4.DeclaringType) && Types(call.Constrained, sc4.Constrained) &&
                           SameTypes(call.MethodArguments, sc4.MethodArguments) && Expression(call.This, sc4.This) && All(call.Arguments, sc4.Arguments);
                case HNewObject n when !NoZeroMade && site is HTypeExpr { Op: HTypeOp.Default, Target: var cleared } && n.Constructor.DeclaringType.IsValueType &&
                                       Types(n.Type, cleared) && _owner.ZeroMade(n.Constructor, n.Type):
                {
                    // A struct with every field zero, which the place has as "default": made by a constructor that
                    // puts its parameters into the fields, it was given zeros ("Euler(0, 0, 0)").
                    foreach (HExpr argument in n.Arguments)
                        if (Zero(argument.Type) is not { } zero || !Expression(argument, zero))
                            return false;
                    return true;
                }
                case HNewObject n:
                    // The same struct value, made with another of its constructors (the place has the shortest
                    // that fits what was stored): as this method's constructor would have been given it.
                    if (site is HNewObject other && !ReferenceEquals(n.Constructor, other.Constructor) && n.Constructor.DeclaringType.IsValueType &&
                        ReferenceEquals(n.Constructor.DeclaringType, other.Constructor.DeclaringType) && Types(n.DeclaringType, other.DeclaringType) &&
                        _owner.Reexpress(other, n.Constructor) is { } again)
                        return All(n.Arguments, again);
                    return site is HNewObject sn && ReferenceEquals(n.Constructor, sn.Constructor) && Types(n.DeclaringType, sn.DeclaringType) && All(n.Arguments, sn.Arguments);
                case HNewArray na:
                    return site is HNewArray sna && Types(na.ElementType, sna.ElementType) && Expression(na.Length, sna.Length);
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
    }

    private static bool Mentions(HExpr? e, object member)
    {
        bool found = false;
        FinallyFolding.Visit(e, x => found |= x is HField f && ReferenceEquals(f.Field, member) || x is HCall c && ReferenceEquals(c.Method, member));
        return found;
    }

    private static bool Mentions(HStmt s, object member)
    {
        bool found = false;
        FinallyFolding.Visit(s, x => found |= x is HField f && ReferenceEquals(f.Field, member) || x is HCall c && ReferenceEquals(c.Method, member));
        return found;
    }

    private static bool HasCall(HExpr? e)
    {
        bool found = false;
        FinallyFolding.Visit(e, x => found |= x is HCall or HOpaque or HCachedDelegate || x is HNewObject { Constructor.DeclaringType.IsValueType: false } or HNewArray ||
                                        x is HTypeExpr { Op: HTypeOp.Allocate or HTypeOp.Box });
        return found;
    }

    public void Run(HMethod method)
    {
        if (Disabled) return;
        MethodDef current = method.Method;
        MethodDef? outer = _current;
        HashSet<MethodDef>? outerBarred = _barred;
        _current = current;
        _barred = pipeline.BarredFor(current);
        try
        {
            Fold(method, current);
        }
        finally
        {
            _current = outer;
            _barred = outerBarred;
        }
    }

    /// <summary>The method whose statements are being looked at (null outside Run).</summary>
    private MethodDef? _current;
    /// <summary>The methods that one must not be written as a call of.</summary>
    private HashSet<MethodDef>? _barred;
    private static readonly bool NoStoredBehind = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_STORED_BEHIND") != null;

    /// <summary>
    /// A write to the storage of another class's automatic property that the method could not have made through
    /// the property - it has no setter (only its class's constructors write it), or one the method may not call:
    /// the statement is of a method of that class, pasted in here.
    /// </summary>
    private bool StoredBehind(HStmt statement, HField f)
    {
        if (NoStoredBehind || _current is not { } current || !AccessorIndex.IsBackingField(f.Field)) return false;
        if (statement is not HAssign { Target: HField target } || !ReferenceEquals(target, f)) return false;
        TypeDef owner = f.Field.DeclaringType;
        if (Within(current.DeclaringType, owner)) return false; // the class itself (and what is nested in it) is the accessor's business
        string? name = AccessorIndex.AutoPropertyName(f.Field);
        foreach (PropertyDef p in owner.Properties)
            if (string.Equals(p.Name, name, StringComparison.Ordinal) && p.Setter is { } setter && setter.IsStatic == f.Field.IsStatic)
                return !IsAccessible(setter, current);
        return true;
    }

    /// <summary>Whether a class between this one and the method's own (this one included) has its own version of a virtual method.</summary>
    private static bool Overridden(MethodDef method, TypeDef from)
    {
        if (!method.HasSlot) return false;
        int guard = 0;
        for (TypeDef? t = from; t != null && guard++ < 64 && !ReferenceEquals(t, method.DeclaringType); t = t.BaseType?.Definition)
            foreach (MethodDef m in t.Methods)
                if (m.IsVirtual && !m.IsStatic && m.HasSlot && m.Slot == method.Slot)
                    return true;
        return false;
    }

    private void Fold(HMethod method, MethodDef current)
    {
        // Members named here that this method could not have named.
        bool Foreign(object member) => member is FieldDef f
            ? !AccessorIndex.IsBackingField(f) && !AccessorFolding.IsAccessible(f, current)
            : !IsAccessible((MethodDef)member, current);
        // (Not a method this one must not be written as a call of: see MethodPipeline.TwinOf.)
        HashSet<MethodDef>? barred = _barred;
        bool Usable(Template t) => !ReferenceEquals(t.Method, current) && IsAccessible(t.Method, current) && !(barred?.Contains(t.Method) ?? false);
        // The methods with branches first: the larger a method, the more of the smaller ones' statements it contains.
        _putBack = !NoPutBack;
        _putBackBudget = 48;
        for (int round = 0; round < 200 && Pass(method, Foreign, TemplatesOf, t => t.Flow != null && Usable(t), true); round++) { }
        _putBack = false;
        for (int round = 0; round < 400 && Pass(method, Foreign, TemplatesOf, Usable, true); round++) { }
        // What is still there may be a method with a test the place does not have: the compiler leaves a test of
        // a parameter out where a constant was handed over ("SetState(isOn, false)" has no "if (notify)").
        if (!NoDecided)
        {
            _decided = true;
            bool found = false;
            for (int round = 0; round < 200 && Pass(method, Foreign, TemplatesOf, t => t.Flow != null && Usable(t), true); round++) found = true;
            _decided = false;
            for (int round = 0; found && round < 400 && Pass(method, Foreign, TemplatesOf, Usable, true); round++) { }
        }
        for (int round = 0; round < 64 && Constructors(method); round++) { }
        // A struct made in one go now is read field by field and written back where it is handed on: those stores
        // put back what was there. Without them, the statements around may be a method's ("list.Add(item)").
        if (!NoWriteBacksBetween && WriteBacks.Run(method, program))
        {
            for (int round = 0; round < 200 && Pass(method, Foreign, TemplatesOf, t => t.Flow != null && Usable(t), true); round++) { }
            for (int round = 0; round < 400 && Pass(method, Foreign, TemplatesOf, Usable, true); round++) { }
        }
    }

    private static readonly bool NoWriteBacksBetween = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_WRITE_BACKS") != null;


    /// <summary>
    /// A constructor with branches ("_values = values ?? new Dictionary()"), pasted in after the allocation of
    /// its object: the statements after the allocation are the constructor's, run on the new object - and
    /// "x = allocate; x.ctor(...)" is "x = new T(...)". (Constructors without branches are put back before
    /// this, by ConstructorFolding.)
    /// </summary>
    private bool Constructors(HMethod method)
    {
        Counts? counts = null;
        foreach (HBlock block in method.Blocks)
        {
            for (int i = 0; i + 1 < block.Statements.Count; i++)
            {
                if (StructWrittenWhole(method, block, i, ref counts)) return true;
                if (block.Statements[i] is not HAssign { Target: HLocal { Variable: var created } target, Value: HTypeExpr { Op: HTypeOp.Allocate or HTypeOp.Default, Target: var type } made }) continue;
                // (A struct is made the same way, on a variable cleared first: "s = default; s..ctor(...)" is "s = new S(...)".)
                bool cleared = made.Op == HTypeOp.Default;
                if (cleared && (NoStructFlows || target.Type?.Key != type.Key)) continue;
                if (type is GenericInstSig || type.Definition is not { } definition || definition.IsValueType != cleared || definition.IsEnum ||
                    definition.GenericParameters.Length != 0) continue;
                foreach (MethodDef constructor in definition.Methods)
                {
                    if (constructor.Name != ".ctor" || constructor.IsStatic || constructor.Address == 0 || ReferenceEquals(constructor, method.Method)) continue;
                    if (!Made(constructor, out Template? template))
                        template = Keep(constructor, program.Code.Get(constructor.Address) is { Instructions: <= 200 } ? MakeFlow(constructor, pipeline.CoreBody(constructor)) : null);
                    if (template == null) continue;
                    counts ??= Counts.Of(method);
                    if (!TryFoldFlow(method, block, i + 1, template, counts)) continue;
                    // What stands there now is the call of the constructor on the object just allocated.
                    if (i + 1 < block.Statements.Count &&
                        block.Statements[i] is HAssign { Target: HLocal { Variable: var still }, Value: HTypeExpr { Op: HTypeOp.Allocate or HTypeOp.Default } } allocation && ReferenceEquals(still, created) &&
                        block.Statements[i + 1] is HEval { Expression: HCall { This: var receiver } call } &&
                        (receiver is HAddressOf { Target: var inner } ? inner : receiver) is HLocal { Variable: var on } && ReferenceEquals(on, created) &&
                        ReferenceEquals(call.Method, constructor) && !call.Arguments.Any(a => ConstructorFolding.Mentions(a, created)))
                    {
                        block.Statements[i] = new HAssign(new HLocal(created) { Type = target.Type }, new HNewObject { Constructor = constructor, Arguments = call.Arguments, Type = type })
                        {
                            Address = allocation.Address,
                        };
                        block.Statements.RemoveAt(i + 1);
                        method.Notes.Remove($"the constructor of {type.ShortName} was inlined here; the object is allocated raw and its statements follow");
                    }
                    return true;
                }
            }
        }
        return false;
    }

    /// <summary>
    /// A struct's constructor pasted onto a variable without clearing it first (it writes every field): the run
    /// starts at a store into a field only constructors write (readonly, or the storage of a property) - and
    /// "s..ctor(...)" is "s = new S(...)".
    /// </summary>
    private bool StructWrittenWhole(HMethod method, HBlock block, int i, ref Counts? counts)
    {
        if (NoStructFlows || NoWholeWrites) return false;
        if (block.Statements[i] is not HAssign { Target: HField { Object: HLocal { Variable: var made } local, Field: var field } }) return false;
        if (field.IsStatic || ((field.Attrs & FieldDef.InitOnly) == 0 && !AccessorIndex.IsBackingField(field))) return false;
        TypeSig? type = local.Type;
        if (type is null or GenericInstSig || type.Definition is not { IsValueType: true, IsEnum: false } definition || definition.GenericParameters.Length != 0 ||
            !ReferenceEquals(field.DeclaringType, definition)) return false;
        // (The first such store of a run: the one before it is something else.)
        if (i > 0 && block.Statements[i - 1] is HAssign { Target: HField { Object: HLocal { Variable: var before } } } && ReferenceEquals(before, made)) return false;
        foreach (MethodDef constructor in definition.Methods)
        {
            if (constructor.Name != ".ctor" || constructor.IsStatic || constructor.Address == 0 || ReferenceEquals(constructor, method.Method)) continue;
            if (!Made(constructor, out Template? template))
                template = Keep(constructor, program.Code.Get(constructor.Address) is { Instructions: <= 200 } ? MakeFlow(constructor, pipeline.CoreBody(constructor)) : null);
            if (template == null) continue;
            counts ??= Counts.Of(method);
            if (!TryFoldFlow(method, block, i, template, counts)) continue;
            if (i < block.Statements.Count && block.Statements[i] is HEval { Expression: HCall { This: var receiver } call } eval &&
                (receiver is HAddressOf { Target: var inner } ? inner : receiver) is HLocal { Variable: var on } && ReferenceEquals(on, made) &&
                ReferenceEquals(call.Method, constructor) && !call.Arguments.Any(a => ConstructorFolding.Mentions(a, made)))
                block.Statements[i] = new HAssign(new HLocal(made) { Type = type }, new HNewObject { Constructor = constructor, Arguments = call.Arguments, Type = type })
                {
                    Address = eval.Address,
                };
            return true;
        }
        return false;
    }

    private static readonly bool NoWholeWrites = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_WHOLE_WRITES") != null;

    /// <summary>Folds one place; true when it did (the statements have changed then).</summary>
    private bool Pass(HMethod method, Func<object, bool> gives, Func<TypeDef, TypeSig?, List<Template>> templates, Func<Template, bool> usable, bool inherited)
    {
        Counts? counts = null;
        foreach (HBlock block in method.Blocks)
        {
            for (int i = 0; i < block.Statements.Count; i++)
            {
                List<(object Member, TypeSig? Declaring)>? anchors = null;
                HStmt statement = block.Statements[i];
                FinallyFolding.Visit(statement, e =>
                {
                    (object? member, TypeSig? declaring) = e switch
                    {
                        HField f when gives(f.Field) || StoredBehind(statement, f) => (f.Field, f.DeclaringType ?? (f.Object?.Type is ByRefSig or PointerSig ? f.Object.Type.ElementType : f.Object?.Type)),
                        HCall c when gives(c.Method) => ((object?)c.Method, c.DeclaringType),
                        _ => (null, null),
                    };
                    if (member == null) return;
                    anchors ??= [];
                    if (!anchors.Contains((member, declaring))) anchors.Add((member, declaring));
                });
                if (anchors == null) continue;
                foreach ((object anchor, TypeSig? declaring) in anchors)
                {
                    TypeDef owner = anchor is FieldDef field ? field.DeclaringType : ((MethodDef)anchor).DeclaringType;
                    // The methods of the member's class - and those of the classes this one derives from: what a
                    // base class offers ("do I have authority?") is often made of members of other classes.
                    IEnumerable<Template> candidates = templates(owner, declaring);
                    if (inherited)
                    {
                        var others = new List<TypeDef>();
                        void Consider(TypeDef? type)
                        {
                            if (type != null && !ReferenceEquals(type, owner) && type.GenericParameters.Length == 0 && !others.Contains(type) && others.Count < 16) others.Add(type);
                        }
                        int guard = 0;
                        for (TypeDef? ancestor = method.Method.DeclaringType.BaseType?.Definition; ancestor != null && guard++ < 16; ancestor = ancestor.BaseType?.Definition) Consider(ancestor);
                        // ... and those of the classes of the member's assembly whose members are used around
                        // here: the same thing asked of another object ("hand.HasInputAuthority").
                        counts ??= Counts.Of(method);
                        Dictionary<HBlock, List<HBlock>> before = counts.Predecessors(method);
                        var near = new List<HBlock> { block };
                        for (int k = 0; k < near.Count && near.Count < 8; k++)
                            if (before.TryGetValue(near[k], out List<HBlock>? leading))
                                foreach (HBlock p in leading)
                                    if (!near.Contains(p) && near.Count < 8)
                                        near.Add(p);
                        foreach (HBlock b in near)
                            foreach (HStmt s in b.Statements)
                                FinallyFolding.Visit(s, e =>
                                {
                                    (TypeDef? used, TypeSig? on) = e switch
                                    {
                                        HCall c => (c.Method.DeclaringType, c.This?.Type),
                                        HField f => (f.Field.DeclaringType, f.Object?.Type),
                                        _ => ((TypeDef?)null, (TypeSig?)null),
                                    };
                                    if (used != null && ReferenceEquals(used.Assembly, owner.Assembly)) Consider(used);
                                    // The object it is used on may be of a class further down: what that class
                                    // inherits on the way is offered on the object too.
                                    if (on is ByRefSig or PointerSig) on = on.ElementType;
                                    int depth = 0;
                                    for (TypeDef? of = on?.Definition; of != null && depth++ < 16; of = of.BaseType?.Definition)
                                        if (ReferenceEquals(of.Assembly, owner.Assembly))
                                            Consider(of);
                                });
                        foreach (TypeDef other in others) candidates = candidates.Concat(templates(other, null));
                        candidates = candidates.OrderByDescending(c => c.Size).ToList();
                    }
                    if (TracedSite != null && method.Method.FullName.Contains(TracedSite, StringComparison.Ordinal))
                        Console.Error.WriteLine($"[inline-site] {method.Method.Name} L{block.Id}:{i}: {anchor} of {declaring?.ShortName ?? "?"}: {candidates.Count(t => t.Members.Contains(anchor))} of {candidates.Count()} models name it, {candidates.Count(t => t.Members.Contains(anchor) && usable(t))} usable");
                    foreach (Template template in candidates)
                    {
                        if (!template.Members.Contains(anchor) || !usable(template)) continue;
                        if (anchor is MethodDef called && OnlyCalls(template, called) && IsAccessible(called, method.Method)) continue;
                        // The call put back is named in this assembly's code: its class must be one that code can name.
                        if (!AssemblyScope.Names(method.Method.DeclaringType.Assembly, template.Method.DeclaringType.Assembly)) continue;
                        if (Tracing(template.Method)) Console.Error.WriteLine($"[inline] {method.Method.Name}: trying {template.Method.Name}{(template.Flow != null ? " (with branches)" : "")} for {anchor} at L{block.Id}:{i}");
                        counts ??= Counts.Of(method);
                        _partly = false;
                        if (template.Flow != null ? TryFoldFlow(method, block, i, template, counts) : TryFold(method, block, i, template, anchor, counts))
                        {
                            (method.PutBack ??= []).Add(template.Method);
                            return true;
                        }
                        if (template.Flow != null && _partly && _putBack && _putBackBudget > 0 && PutBack(method, block, template, counts)) return true;
                    }
                }
            }
        }
        return false;
    }

    /// <summary>Set while a method with branches is compared: its first statements were found at a place, the rest was not.</summary>
    private bool _partly;
    /// <summary>Whether the comparisons made now may take a test of a parameter as decided by a constant handed over.</summary>
    private bool _decided;
    /// <summary>Whether what a half-found method calls is put back at the place (in the methods being recovered, not in the models).</summary>
    private bool _putBack;
    private int _putBackBudget;

    /// <summary>
    /// A method with branches was not found where a member of it is used, though its first statements are
    /// there. What it calls may be pasted in at this place where the method itself has a call (the two were
    /// compiled apart). Those are put back first - each is the same code either way; true when one was.
    /// </summary>
    private bool PutBack(HMethod method, HBlock block, Template template, Counts counts)
    {
        _putBackBudget--;
        Dictionary<HBlock, List<HBlock>> before = counts.Predecessors(method);
        var near = new List<HBlock> { block };
        void Add(HBlock b)
        {
            if (near.Count < 24 && !near.Contains(b)) near.Add(b);
        }
        for (int k = 0; k < near.Count && near.Count < 24; k++)
        {
            if (before.TryGetValue(near[k], out List<HBlock>? leading))
                foreach (HBlock p in leading)
                    Add(p);
            if (near[k].Statements.Count == 0) continue;
            switch (near[k].Statements[^1])
            {
                case HJump j: Add(j.Target); break;
                case HBranch br: Add(br.WhenTrue); Add(br.WhenFalse); break;
            }
        }
        bool tracing = Tracing(template.Method);
        foreach (object member in template.Members)
        {
            if (member is not MethodDef callee || ReferenceEquals(callee, template.Method) || ReferenceEquals(callee, method.Method)) continue;
            if (callee.DeclaringType.GenericParameters.Length != 0 || callee.GenericParameters.Length != 0) continue;
            if (ReferenceEquals(method.Method, _current) && (_barred?.Contains(callee) ?? false)) continue;
            foreach (Template inner in TemplatesOf(callee.DeclaringType, Levels))
            {
                if (!ReferenceEquals(inner.Method, callee)) continue;
                foreach (HBlock b in near)
                    for (int i = 0; i < b.Statements.Count; i++)
                    {
                        object? anchor = null;
                        FinallyFolding.Visit(b.Statements[i], e =>
                        {
                            if (anchor != null) return;
                            if (e is HField f && inner.Members.Contains(f.Field)) anchor = f.Field;
                            else if (e is HCall c && inner.Members.Contains(c.Method)) anchor = c.Method;
                        });
                        if (anchor == null) continue;
                        if (anchor is MethodDef called && OnlyCalls(inner, called) && IsAccessible(called, method.Method)) continue;
                        if (!(inner.Flow != null ? TryFoldFlow(method, b, i, inner, counts) : TryFold(method, b, i, inner, anchor, counts))) continue;
                        (method.PutBack ??= []).Add(callee);
                        if (tracing) Console.Error.WriteLine($"[inline] {method.Method.Name}: {callee.FullName} put back for {template.Method.Name}");
                        return true;
                    }
            }
        }
        return false;
    }

    /// <summary>The call that stands for the statements compared: of the method, on what was found for "this", with what was found for its parameters.</summary>
    private HCall? MakeCall(Template template, Unifier unifier)
    {
        MethodDef m = template.Method;
        if (!m.IsStatic && (unifier.This == null || !unifier.ReceiverCompatible(unifier.This.Type))) return null;
        // (A struct worked out on the spot is a copy the method runs on: right for one that only reads it.)
        if (!m.IsStatic && m.DeclaringType.IsValueType && unifier.This is not (HLocal or HArg or HField or HElement or HDeref) && !ThisFirst(template)) return null;
        TypeSig? declaring = template.Declaring;
        TypeSig[] classArguments = template.SiteArguments;
        if (declaring != null && !m.IsStatic)
        {
            // The receiver must be what the statements were taken to be of.
            TypeSig? receiver = unifier.This?.Type;
            if (receiver is ByRefSig or PointerSig) receiver = receiver.ElementType;
            if (receiver is GenericInstSig g && ReferenceEquals(g.Definition, m.DeclaringType) && !ReferenceEquals(g, declaring)) return null;
        }
        var arguments = new HExpr[m.Parameters.Length];
        for (int p = 0; p < arguments.Length; p++)
        {
            TypeSig parameter = classArguments.Length != 0 ? program.Model.Sigs.Substitute(m.Parameters[p].Type, classArguments, []) : m.Parameters[p].Type;
            if (unifier.Arguments[p] is { } found) arguments[p] = found;
            // A place the method never uses: nothing to name.
            else if (parameter is ByRefSig or PointerSig || parameter.ContainsGenericParameter) return null;
            // A parameter the method never looks at: any value does.
            else arguments[p] = parameter.IsValueType ? new HTypeExpr(HTypeOp.Default, parameter, null) { Type = parameter } : new HConst(null, parameter);
        }
        // Found on "this" in a class that has its own version of the method: "base.M(...)". (A virtual call there
        // would come back to the class's own version - and could not have been pasted in.)
        bool viaBase = m.IsVirtual && !m.IsStatic && !m.DeclaringType.IsValueType && unifier.This is HArg { Index: -1 } &&
                       _current is { IsStatic: false } user && !ReferenceEquals(user.DeclaringType, m.DeclaringType) &&
                       Derives(user.DeclaringType, m.DeclaringType) && Overridden(m, user.DeclaringType);
        return new HCall
        {
            Method = m,
            DeclaringType = declaring,
            This = m.IsStatic ? null : unifier.This,
            Arguments = arguments,
            Virtual = m.IsVirtual && !m.DeclaringType.IsValueType && !viaBase,
            Type = classArguments.Length != 0 ? program.Model.Sigs.Substitute(m.ReturnType, classArguments, []) : m.ReturnType,
        };
    }

    /// <summary>
    /// A method that is one expression, which does nothing but compute from its parameters - each read once,
    /// all of them whatever happens, none of them a reference to something.
    /// </summary>
    private static bool OneExpression(Template template)
    {
        if (template.Statements.Count != 0 || template.Result == null || !HirBuilder.IsPure(template.Result)) return false;
        foreach (ParamDef p in template.Method.Parameters)
            if (p.Type is ByRefSig or PointerSig)
                return false;
        var seen = new HashSet<int>();
        bool once = true;
        FinallyFolding.Visit(template.Result, e =>
        {
            if (e is HArg { Index: >= 0 } a) once &= seen.Add(a.Index);
            if (e is HSelect) once = false;
        });
        return once;
    }

    /// <summary>What an expression is made from, in the order those are worked out.</summary>
    private static IEnumerable<HExpr?> Operands(HExpr e)
    {
        switch (e)
        {
            case HField f: yield return f.Object; break;
            case HElement el: yield return el.Array; yield return el.Index; break;
            case HArrayLength len: yield return len.Array; break;
            case HAddressOf a: yield return a.Target; break;
            case HDeref d: yield return d.Pointer; break;
            case HUnary u: yield return u.Operand; break;
            case HBinary b: yield return b.Left; yield return b.Right; break;
            case HCompare c: yield return c.Left; yield return c.Right; break;
            case HConv c: yield return c.Operand; break;
            case HCall call:
                yield return call.This;
                foreach (HExpr a in call.Arguments) yield return a;
                break;
            case HNewObject n:
                foreach (HExpr a in n.Arguments) yield return a;
                break;
            case HNewArray na: yield return na.Length; break;
            case HTypeExpr t: yield return t.Operand; break;
            case HCachedDelegate cached: yield return cached.Creation; break;
            case HSelect s: yield return s.Condition; yield return s.WhenTrue; yield return s.WhenFalse; break;
            case HOpaque o:
                foreach (HExpr a in o.Operands) yield return a;
                break;
        }
    }

    /// <summary>
    /// A method without branches that reads its parameters - each once, all of them whatever happens, none a
    /// reference to something - before it does anything else: until the last of them is read it only computes
    /// from them and from constants. What an argument does (a call) then comes before all the method does, at
    /// the place the method is pasted in just as where it is called.
    /// </summary>
    private static bool ReadsFirst(Template template)
    {
        if (template.Early is { } known) return known;
        bool fine = template.Flow == null && template.Method.Parameters.Length != 0;
        foreach (ParamDef p in template.Method.Parameters) fine &= p.Type is not (ByRefSig or PointerSig);
        var seen = new HashSet<int>();
        bool worked = false;
        void Walk(HExpr? e)
        {
            if (e == null || !fine) return;
            if (e is HArg { Index: >= 0 } a)
            {
                fine = !worked && seen.Add(a.Index);
                return;
            }
            if (e is HSelect)
            {
                // Only one of the two is worked out.
                bool reads = false;
                FinallyFolding.Visit(e, x => reads |= x is HArg { Index: >= 0 });
                if (reads)
                {
                    fine = false;
                    return;
                }
            }
            foreach (HExpr? operand in Operands(e)) Walk(operand);
            worked |= !(e is HConst or HLocal or HArg or HUnary or HCompare or HAddressOf { Target: HLocal } || (!NoCallFirst && e is HAddressOf { Target: HArg }) ||
                        e is HBinary or HConv && HirBuilder.IsPure(e) || e is HTypeExpr { Op: HTypeOp.Default or HTypeOp.SizeOf });
        }
        foreach (HStmt s in template.Statements)
        {
            if (!fine) break;
            switch (s)
            {
                case HAssign { Target: HLocal } a:
                    Walk(a.Value);
                    break;
                case HAssign a:
                    foreach (HExpr? operand in Operands(a.Target)) Walk(operand);
                    Walk(a.Value);
                    worked = true;
                    break;
                case HEval v:
                    Walk(v.Expression);
                    break;
                default:
                    fine = false;
                    break;
            }
        }
        if (fine) Walk(template.Result);
        fine &= seen.Count != 0;
        template.Early = fine;
        return fine;
    }

    private static readonly bool NoThisFirst = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_THIS_FIRST") != null;
    private static readonly bool NoTurned = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_TURNED") != null;

    /// <summary>
    /// Whether a method names its object once, as the first thing it works out (in its first statement), and
    /// only reads it there: the object may then be handed over as something that does work - a call,
    /// "this.Runner" in "this.Runner.Tick" - which is worked out where the method's first statement was, just
    /// as the call of the method works out its object first. (A struct is only read through, a field of it or
    /// all of it: a copy made on the spot, which the call then runs on, is the same to such a method.)
    /// </summary>
    private static bool ThisFirst(Template template)
    {
        if (template.OwnFirst is { } known) return known;
        bool fine = !NoThisFirst && !template.Method.IsStatic;
        HStmt? first = null;
        List<HStmt> all = [];
        if (fine)
        {
            if (template.Flow != null)
            {
                all.AddRange(template.Flow.Blocks.SelectMany(b => b.Statements));
                first = template.Flow.Blocks[0].Statements.FirstOrDefault();
            }
            else
            {
                all.AddRange(template.Statements);
                if (template.Result != null) all.Add(new HEval(template.Result));
                first = all.FirstOrDefault();
            }
            fine = first != null;
        }
        if (fine)
        {
            int named = 0, here = 0;
            foreach (HStmt s in all) FinallyFolding.Visit(s, e => named += e is HArg { Index: < 0 } ? 1 : 0);
            FinallyFolding.Visit(first!, e => here += e is HArg { Index: < 0 } ? 1 : 0);
            fine = named == 1 && here == 1;
        }
        if (fine)
        {
            // What stands around the mention: a field read through it, all of it, or (for a class) a call on it.
            HExpr? self = null, around = null;
            void Find(HExpr? e, HExpr? parent)
            {
                if (e == null || self != null) return;
                if (e is HArg { Index: < 0 })
                {
                    self = e;
                    around = parent;
                    return;
                }
                foreach (HExpr? operand in Operands(e)) Find(operand, e);
            }
            switch (first)
            {
                case HAssign a:
                    Find(a.Target, null);
                    if (self != null) fine = false; // (the object, or a part of it, is what is set)
                    Find(a.Value, null);
                    break;
                case HEval v: Find(v.Expression, null); break;
                case HBranch b: Find(b.Condition, null); break;
                case HReturn r: Find(r.Value, null); break;
                default: fine = false; break;
            }
            bool value = template.Method.DeclaringType.IsValueType;
            fine &= self != null && around switch
            {
                HField { Field.IsStatic: false } => true,
                HDeref => value,
                HCall c when !value => ReferenceEquals(c.This, self),
                _ => false,
            };
            fine &= self != null && WorkedOutFirst(first!, around ?? self);
        }
        template.OwnFirst = fine;
        return fine;
    }

    /// <summary>A value nothing done in between can change: see Stable; and the object a method of a class runs on.</summary>
    private static bool Settled(HExpr? e) => Stable(e) || e is HArg { Index: < 0, Type: { IsValueType: false } and not (ByRefSig or PointerSig) };

    /// <summary>
    /// Whether an expression of a statement is worked out before anything else in it that does work, or that
    /// work could change: what is put in its place is then the first thing the statement does.
    /// </summary>
    private static bool WorkedOutFirst(HStmt statement, HExpr wanted)
    {
        bool? In(HExpr? e)
        {
            if (e == null) return null;
            if (ReferenceEquals(e, wanted)) return true;
            bool clean = true;
            foreach (HExpr? operand in Operands(e))
            {
                if (In(operand) is { } inside) return inside && clean;
                clean &= Settled(operand);
            }
            return null;
        }
        switch (statement)
        {
            case HAssign a:
            {
                bool clean = true;
                if (a.Target is not HLocal)
                    foreach (HExpr? operand in Operands(a.Target))
                    {
                        if (In(operand) is { } inside) return inside && clean;
                        clean &= Settled(operand);
                    }
                return In(a.Value) is true && clean;
            }
            case HEval v: return In(v.Expression) is true;
            case HReturn r: return In(r.Value) is true;
            case HThrow th: return In(th.Exception) is true;
            case HBranch b: return In(b.Condition) is true;
            case HSwitch sw: return In(sw.Value) is true;
            default: return false;
        }
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

    /// <summary>
    /// Whether a variable only passes through a stretch of a block: the first thing done with it there is
    /// giving it a value - whole - and after the stretch that value is never looked at again.
    /// </summary>
    private static bool Passing(HMethod method, HBlock block, int start, int n, int from, HVar variable)
    {
        List<HStmt> site = block.Statements;
        bool given = false;
        for (int k = start; k < start + n && !given; k++)
        {
            if (site[k] is HAssign { Target: HLocal target, Value: var value } && ReferenceEquals(target.Variable, variable))
            {
                if (ConstructorFolding.Mentions(value, variable)) return false;
                given = true;
            }
            else if (ConstructorFolding.Mentions(site[k], variable)) return false;
        }
        return given && Renewed(method, block, from, variable);
    }

    /// <summary>
    /// Whether, from a position in a block on, a variable is given a new value - whole - before anything else
    /// is done with it, on every way the method can go on from there.
    /// </summary>
    internal static bool Renewed(HMethod method, HBlock block, int from, HVar variable)
    {
        // A struct may be given its next value field by field ("v.x = a; v.y = b"): a field given anew no longer
        // holds what the method left in it, and reading it then reads the place's own value. What is followed
        // along each way is which fields still hold the method's (null: the whole variable, as it is for
        // anything but a struct).
        FieldDef[]? fields = !NoPartsRenewed && variable.Type is { IsValueType: true } and not (PrimitiveSig or PointerSig or ByRefSig or OpaqueSig or GenericParamSig) &&
                             variable.Type.Definition is { IsEnum: false } definition
            ? definition.Fields.Where(f => !f.IsStatic).ToArray()
            : null;
        if (fields is { Length: 0 }) fields = null;
        var seen = new Dictionary<HBlock, HashSet<FieldDef>?>();
        var work = new Stack<(HBlock Block, int From, HashSet<FieldDef>? Held)>();
        work.Push((block, from, fields == null ? null : [.. fields]));
        while (work.Count != 0)
        {
            (HBlock b, int first, HashSet<FieldDef>? held) = work.Pop();
            bool renewed = false;
            for (int k = first; k < b.Statements.Count && !renewed; k++)
            {
                HStmt s = b.Statements[k];
                if (s is HAssign { Target: HLocal target, Value: var value } && ReferenceEquals(target.Variable, variable))
                {
                    if (ConstructorFolding.Mentions(value, variable)) return false;
                    renewed = true;
                }
                else if (held != null && s is HAssign { Target: HField { Object: HLocal { Variable: var whose }, Field: var part }, Value: var partValue } &&
                         ReferenceEquals(whose, variable) && !part.IsStatic)
                {
                    if (Observes(partValue, variable, held)) return false;
                    held = [.. held];
                    held.Remove(part);
                    renewed = held.Count == 0;
                }
                else if (held != null ? Observes(s, variable, held) : ConstructorFolding.Mentions(s, variable)) return false;
            }
            if (renewed) continue;
            // Where an exception can take the method elsewhere from any statement, the ways on are not these.
            if (method.TryRegions.Count != 0) return false;
            foreach (HBlock next in Successors(b))
            {
                // Each block is looked at again only with fields that were not looked for in it before.
                if (seen.TryGetValue(next, out HashSet<FieldDef>? before))
                {
                    if (before == null || (held != null && held.IsSubsetOf(before))) continue;
                    if (held == null) seen[next] = null;
                    else before.UnionWith(held);
                    work.Push((next, 0, held == null ? null : [.. seen[next]!]));
                    continue;
                }
                seen[next] = held == null ? null : [.. held];
                work.Push((next, 0, held == null ? null : [.. held]));
            }
        }
        return true;
    }

    private static readonly bool NoPartsRenewed = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_PARTS_RENEWED") != null;
    private static readonly bool NoSlotsOn = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_SLOTS_ON") != null;
    private static readonly bool NoAlikeCalls = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_ALIKE_CALLS") != null;
    private static readonly bool NoKeptParts = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_KEPT_PARTS") != null;
    private static readonly bool NoZeroStructs = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_ZERO_STRUCTS") != null;

    /// <summary>"default(T)" of a struct: a value every field of which is zero.</summary>
    private static bool ZeroStruct(HExpr? e) => !NoZeroStructs && e is HTypeExpr { Op: HTypeOp.Default, Target: { IsValueType: true } and not (PrimitiveSig or PointerSig or ByRefSig or GenericParamSig) };

    /// <summary>
    /// Whether something reads what one of <paramref name="held"/> holds in a struct variable: a field of it, or
    /// the variable whole (its address included).
    /// </summary>
    private static bool Observes(HStmt s, HVar variable, HashSet<FieldDef> held)
    {
        bool observed = false;
        int named = 0, apart = 0;
        FinallyFolding.Visit(s, e =>
        {
            if (e is HLocal l && ReferenceEquals(l.Variable, variable)) named++;
            else if (e is HField { Object: HLocal { Variable: var whose } } f && ReferenceEquals(whose, variable))
            {
                if (held.Contains(f.Field) || f.Field.IsStatic) observed = true;
                else apart++;
            }
        });
        return observed || named > apart;
    }

    private static bool Observes(HExpr? e, HVar variable, HashSet<FieldDef> held) => e != null && Observes(new HEval(e), variable, held);

    private static readonly bool NoApart = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_APART") != null;
    private static readonly bool NoCallFirst = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_CALL_FIRST") != null;
    private static readonly bool NoTempUse = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_TEMP_USE") != null;
    private const int ApartMost = 6;

    /// <summary>
    /// A method's statements at a place with a few of the place's own between them and before the use of what
    /// the method returns: "v = new Vector3(..); this.a = new Quaternion(..); q = Internal_FromEulerRad(&v)" for
    /// two lines of source, the second one "Quaternion.Euler(..)". Where each is (null: not found so).
    /// </summary>
    private (Unifier Unifier, int[] Positions)? Apart(Template template, List<HStmt> site, int at, Counts counts)
    {
        int n = template.Statements.Count;
        for (int start = at - n - 1; start >= 0 && start >= at - n - ApartMost; start--)
        {
            var unifier = new Unifier(this, template, site, counts);
            var pos = new int[n];
            int p = start, skipped = 0;
            bool found = true;
            for (int k = 0; k < n && found; k++)
            {
                found = false;
                for (; p < at && skipped <= ApartMost; p++)
                {
                    Unifier trial = unifier.Clone();
                    trial.At = p;
                    trial.Position = k;
                    if (trial.Statement(template.Statements[k], site[p]))
                    {
                        unifier = trial;
                        pos[k] = p++;
                        found = true;
                        break;
                    }
                    if (k == 0) break; // the first of them is where this try starts
                    skipped++;
                }
            }
            if (!found || skipped + (at - p) > ApartMost) continue;
            return (unifier, pos);
        }
        return null;
    }

    /// <summary>
    /// Whether what stands between a method's statements found apart (see Apart) does the same once those are
    /// all done at the use: plain stores that do no work and have nothing to do with the method's statements
    /// before them.
    /// </summary>
    private static bool Aside(List<HStmt> site, int[] pos, int user, HashSet<int> removed)
    {
        for (int p = pos[0] + 1; p < user; p++)
        {
            if (removed.Contains(p)) continue;
            if (site[p] is not HAssign a || HasCall(a.Value) || HasCall(a.Target)) return false;
            foreach (int q in pos)
                if (q < p && !Commute(site[q], site[p]))
                    return false;
        }
        return true;
    }

    private bool TryFold(HMethod method, HBlock block, int at, Template template, object anchor, Counts counts)
    {
        List<HStmt> site = block.Statements;
        int n = template.Statements.Count;
        MethodDef m = template.Method;
        // With statements of its own, a method may be given arguments that do work only where it reads them first.
        bool early = n != 0 && ReadsFirst(template);
        // The method's statement the member is in tells where its first statement would be.
        for (int a = 0; a <= n; a++)
        {
            if (a < n ? !Mentions(template.Statements[a], anchor) : !Mentions(template.Result, anchor)) continue;
            int start = at - a;
            if (start < 0 || start + n > site.Count || (a == n && start + n >= site.Count)) continue;

            var unifier = new Unifier(this, template, site, counts) { Loose = early };
            // Where each of the method's statements is at the place.
            var pos = new int[n];
            bool matched = true;
            for (int k = 0; k < n && matched; k++)
            {
                unifier.At = start + k;
                unifier.Position = k;
                pos[k] = start + k;
                matched = unifier.Statement(template.Statements[k], site[start + k]);
            }
            bool tracing = Tracing(m);
            if (tracing) Console.Error.WriteLine($"[inline] {m.FullName} in {method.Method.FullName} at L{block.Id}:{at}: statements {(matched ? "match" : "differ")}");
            if (tracing && !matched)
            {
                // (Which of them: the first one the place has differently.)
                var again = new Unifier(this, template, site, counts) { Loose = early };
                for (int k = 0; k < n; k++)
                {
                    again.At = start + k;
                    again.Position = k;
                    if (again.Statement(template.Statements[k], site[start + k])) continue;
                    Console.Error.WriteLine($"[inline]   the method has: {HirPrinter.Print(template.Statements[k], method).Trim()}");
                    Console.Error.WriteLine($"[inline]   the place has:  {HirPrinter.Print(site[start + k], method).Trim()}");
                    break;
                }
            }
            // The place may have other things of its own done between the method's statements and the use of what
            // it returns (the compiler worked the argument out early, then went on with something else): see Apart.
            bool apart = false;
            if (!matched && a == n && n != 0 && template.Result is not (null or HLocal) && !NoApart && Apart(template, site, at, counts) is { } found)
            {
                (unifier, pos) = found;
                start = pos[0];
                matched = apart = true;
                if (tracing) Console.Error.WriteLine($"[inline]   its statements are found apart, from {start} on");
            }
            if (!matched) continue;

            // What the method returns: nothing; a variable it filled (the site has its own in that role); or a
            // value, which the statement after must then contain.
            HVar? into = null;
            HExpr? replaced = null;
            bool negated = false;
            int user = -1;
            if (template.Result is HLocal { Variable: var returned } && unifier.Locals.TryGetValue(returned, out HVar? siteResult)) into = siteResult;
            else if (template.Result != null)
            {
                user = apart ? at : start + n;
                if (user >= site.Count) continue;
                // A method that only hands back what it reads, where the place keeps part of that read in a
                // temporary of its own ("t = list._data; n = *t - 1" for "n = list.Count - 1"): the member the method
                // is found by is in the temporary's statement, the value is used in the next one. That one is
                // looked at too; the temporary is read through (and goes with the call put back).
                int lastUser = user;
                if (!NoTempUse && !apart && n == 0 && user == at && at + 1 < site.Count &&
                    site[at] is HAssign { Target: HLocal { Variable: var held } } && counts.IsTemp(held))
                    lastUser = at + 1;
                // (A method that is one call of what it is handed, in order, reads its parameters first too.)
                bool loose = n == 0 ? OneExpression(template) || (!NoCallFirst && ReadsFirst(template)) : early && !apart;
                for (int u = user; u <= lastUser && replaced == null; u++)
                {
                    var candidates = new List<HExpr>();
                    FinallyFolding.Visit(site[u], candidates.Add);
                    foreach (HExpr candidate in candidates)
                    {
                        // An assignment's target is a place, not a value.
                        if (site[u] is HAssign { Target: var target } && ReferenceEquals(target, candidate)) continue;
                        Unifier trial = unifier.Clone();
                        trial.At = u;
                        trial.Position = n;
                        trial.Loose = loose;
                        bool turned = false;
                        if (!trial.Expression(template.Result, candidate))
                        {
                            // A test the place asks the other way round (the compiler turned it to suit its jump):
                            // the method's answer, negated.
                            if (NoTurned || template.Result is not HCompare { Op: var asked } question || candidate is not HCompare { Op: var other } ||
                                other != Opposite(asked) || (asked is not (HCompareOp.Eq or HCompareOp.Ne) && !(Whole(question.Left.Type) && Whole(question.Right.Type))))
                                continue;
                            trial = unifier.Clone();
                            trial.At = u;
                            trial.Position = n;
                            trial.Loose = loose;
                            if (!trial.Expression(new HCompare(other, question.Left, question.Right) { Type = question.Type }, candidate)) continue;
                            turned = true;
                        }
                        // Arguments that do work are worked out in the order of the parameters, after the object
                        // the method is called on: that must be the order they stand in here.
                        if (trial.Working)
                        {
                            bool ordered = Stable(trial.This) || ThisFirst(template);
                            for (int k = 1; k < trial.Order.Count && ordered; k++) ordered = trial.Order[k - 1] < trial.Order[k];
                            if (!ordered) continue;
                        }
                        // In the next statement, only through the temporary: the read must be the one it holds.
                        if (u != user && !trial.Consumed.Contains(at)) continue;
                        unifier = trial;
                        replaced = candidate;
                        negated = turned;
                        user = u;
                        break;
                    }
                }
                if (replaced == null)
                {
                    if (tracing) Console.Error.WriteLine("[inline]   its result is not in the statement after");
                    continue;
                }
            }
            else if (n == 0) continue;

            // Arguments that do work, found among the method's statements: they are worked out in the order of
            // the parameters, after the object the method is called on, and where the call is written - which
            // must be the first thing done there.
            if (n != 0 && unifier.Working)
            {
                bool ordered = Stable(unifier.This) || ThisFirst(template);
                for (int k = 1; k < unifier.Order.Count && ordered; k++) ordered = unifier.Order[k - 1] < unifier.Order[k];
                if (ordered && replaced != null) ordered = WorkedOutFirst(site[user], replaced);
                if (!ordered)
                {
                    if (tracing) Console.Error.WriteLine("[inline]   its arguments would be worked out in another order");
                    continue;
                }
            }

            // Temporaries of the method have temporaries of their own here; nothing else may use those.
            var removed = new HashSet<int>(unifier.Consumed);
            for (int k = 0; k < n; k++) removed.Add(pos[k]);
            if (apart && !Aside(site, pos, user, removed))
            {
                if (tracing) Console.Error.WriteLine("[inline]   what stands between its statements does not stay what it is");
                continue;
            }
            bool leaks = false;
            int last = replaced != null ? user : start + n - 1;
            foreach (HVar local in unifier.SiteLocals)
            {
                if (ReferenceEquals(local, into)) continue;
                // A stack slot the place uses for one thing after another: the method's temporary lives in it
                // from where it is given a value here - whole - to where the slot is given the next, on every
                // way on from here. What else the place keeps in the slot before and after is not the method's.
                bool passing = Passing(method, block, start, (replaced != null ? user : start + n) - start, last + 1, local);
                for (int b = 0; b < method.Blocks.Count && !leaks; b++)
                {
                    List<HStmt> statements = method.Blocks[b].Statements;
                    for (int k = 0; k < statements.Count && !leaks; k++)
                    {
                        if (ReferenceEquals(method.Blocks[b], block) && removed.Contains(k)) continue;
                        if (ReferenceEquals(method.Blocks[b], block) && k == user)
                        {
                            // only inside what is being replaced
                            int inside = 0, total = 0;
                            FinallyFolding.Visit(replaced, e => inside += e is HLocal l && ReferenceEquals(l.Variable, local) ? 1 : 0);
                            FinallyFolding.Visit(statements[k], e => total += e is HLocal l && ReferenceEquals(l.Variable, local) ? 1 : 0);
                            leaks = inside != total;
                            continue;
                        }
                        if (passing) continue;
                        leaks = ConstructorFolding.Mentions(statements[k], local);
                    }
                }
                if (leaks) break;
            }
            if (leaks)
            {
                if (tracing) Console.Error.WriteLine("[inline]   a temporary of it is used elsewhere");
                continue;
            }

            // The arguments are computed once, before the call: each must be worth the same there as where it
            // was found.
            int firstEffect = n + 1;
            for (int k = 0; k < n; k++)
            {
                bool inert = site[pos[k]] is HAssign { Target: HLocal target, Value: var value } && unifier.SiteLocals.Contains(target.Variable) && !HasCall(value);
                if (!inert)
                {
                    firstEffect = k;
                    break;
                }
            }
            bool valid = true;
            bool Check(HExpr? value, int boundAt)
            {
                if (value == null) return true;
                foreach (HVar local in unifier.SiteLocals)
                    if (ConstructorFolding.Mentions(value, local))
                        return false;
                return Stable(value) || boundAt <= firstEffect;
            }
            valid &= Check(unifier.This, unifier.ThisAt);
            for (int p = 0; p < unifier.Arguments.Length && valid; p++) valid &= Check(unifier.Arguments[p], unifier.BoundAt[p]);
            if (!valid)
            {
                if (tracing) Console.Error.WriteLine("[inline]   an argument is not worth the same before");
                continue;
            }

            if (MakeCall(template, unifier) is not { } call)
            {
                if (tracing) Console.Error.WriteLine("[inline]   no call could be written");
                continue;
            }
            if (tracing) Console.Error.WriteLine("[inline]   folded");
            ulong address = site[at].Address;
            HExpr answer = negated ? new HUnary(HUnaryOp.LogicalNot, call) { Type = call.Type } : call;
            if (replaced != null) EnumeratorLoops.Rewrite(site[user], e => ReferenceEquals(e, replaced) ? answer : null);
            var rebuilt = new List<HStmt>(site.Count);
            for (int k = 0; k < site.Count; k++)
            {
                if (k == start && n != 0 && replaced == null)
                {
                    HStmt folded = into != null
                        ? new HAssign(new HLocal(into) { Type = into.Type }, call) { Address = address }
                        : new HEval(call) { Address = address };
                    rebuilt.Add(folded);
                }
                if (!removed.Contains(k)) rebuilt.Add(site[k]);
            }
            site.Clear();
            site.AddRange(rebuilt);
            return true;
        }
        return false;
    }

    // ---- methods with branches ---------------------------------------------------------------------------------

    /// <summary>
    /// The statements that run one after another from a position on, across plain jumps, up to and including
    /// the one that ends them (a branch, a return, a throw - or a jump that leaves the try region).
    /// </summary>
    private static List<(HBlock Block, int Index)>? RunFrom(HBlock block, int index)
    {
        var run = new List<(HBlock, int)>();
        int scope = block.Scope;
        for (int hops = 0; hops < 64; hops++)
        {
            bool jumped = false;
            for (int i = index; i < block.Statements.Count; i++)
            {
                HStmt s = block.Statements[i];
                if (s is HJump j && j.Target.Scope == scope && !ReferenceEquals(j.Target, block))
                {
                    block = j.Target;
                    index = 0;
                    jumped = true;
                    break;
                }
                run.Add((block, i));
                if (s is HJump or HBranch or HSwitch or HReturn or HThrow or HEndFinally) return run;
                if (run.Count > 240) return null;
            }
            if (!jumped) return null;
        }
        return null;
    }

    /// <summary>The position control is at, past plain jumps.</summary>
    private static (HBlock Block, int Index) Past(HBlock block, int index)
    {
        for (int hops = 0; hops < 64 && index < block.Statements.Count && block.Statements[index] is HJump j && j.Target.Scope == block.Scope && !ReferenceEquals(j.Target, block); hops++)
            (block, index) = (j.Target, 0);
        return (block, index);
    }

    /// <summary>The field of an object (or the static field) an access is inside of; null when it is inside a variable or not known.</summary>
    private static FieldDef? HeapField(HField f, out bool known)
    {
        HField current = f;
        while (current.Field.DeclaringType.IsValueType && !current.Field.IsStatic && current.Object is HField inner) current = inner;
        known = true;
        if (current.Field.IsStatic || !current.Field.DeclaringType.IsValueType) return current.Field;
        // A part of a struct that is not itself a field: a variable's (nothing else reaches it), or something pointed to.
        known = current.Object is HLocal { Variable.AddressTaken: false } or HArg { Index: >= 0, Type: not (ByRefSig or PointerSig) };
        return null;
    }

    /// <summary>Whether a field access is a part of a variable of the method (a struct local, or a part of one of its parts).</summary>
    private static bool InVariable(HField f)
    {
        HField current = f;
        while (current.Field.DeclaringType.IsValueType && !current.Field.IsStatic && current.Object is HField inner) current = inner;
        return current.Field.DeclaringType.IsValueType && !current.Field.IsStatic && current.Object is HLocal;
    }

    /// <summary>Whether what <paramref name="writer"/> sets is something <paramref name="other"/> reads or sets.</summary>
    private static bool Disturbs(HAssign writer, HAssign other)
    {
        HExpr target = writer.Target;
        var path = new List<FieldDef>();
        while (target is HField { Object: { } inside } part && part.Field.DeclaringType.IsValueType && !part.Field.IsStatic && inside is HField or HLocal or HArg)
        {
            path.Insert(0, part.Field);
            target = inside;
        }
        switch (target)
        {
            // (A field of a struct variable: only what overlaps it - the field, a part of it, the variable whole.
            // Statements that are compared this way call nothing, so nothing reaches the variable through its address
            // in between.)
            case HLocal l when path.Count != 0 && !NoFieldPaths:
                return Overlaps(other, l.Variable, path);
            case HLocal l:
                return ConstructorFolding.Mentions(other, l.Variable);
            case HField f:
            {
                FieldDef? field = HeapField(f, out bool known);
                if (field == null || !known) return true;
                bool touched = false;
                FinallyFolding.Visit(other, e =>
                {
                    switch (e)
                    {
                        case HDeref: touched = true; break;
                        case HField g:
                            FieldDef? read = HeapField(g, out bool sure);
                            // (A part of a variable of the method is not in any object, whatever points to it.)
                            touched |= (!sure && (NoStackParts || !InVariable(g))) || ReferenceEquals(read, field);
                            break;
                    }
                });
                return touched;
            }
            default:
            {
                bool reads = false;
                FinallyFolding.Visit(other, e => reads |= e is HDeref or HElement || e is HField g && (HeapField(g, out bool sure) != null || !sure));
                return reads;
            }
        }
    }

    /// <summary>What statements may change: anything (a call), what is pointed to, array elements, particular fields of objects.</summary>
    private sealed class Effects
    {
        public bool Calls, Pointers, Elements;
        public readonly HashSet<FieldDef> Fields = [];

        public bool Add(Effects other)
        {
            bool changed = (other.Calls && !Calls) || (other.Pointers && !Pointers) || (other.Elements && !Elements);
            Calls |= other.Calls;
            Pointers |= other.Pointers;
            Elements |= other.Elements;
            foreach (FieldDef f in other.Fields) changed |= Fields.Add(f);
            return changed;
        }
    }

    private static Effects EffectsOf(HStmt s)
    {
        var effects = new Effects();
        bool calls = false;
        FinallyFolding.Visit(s, e => calls |= e is HCall or HOpaque or HCachedDelegate or HNewObject);
        effects.Calls = calls;
        if (s is HAssign { Target: var target })
            switch (target)
            {
                case HLocal:
                    break;
                case HElement:
                    effects.Elements = true;
                    break;
                case HField f:
                    FieldDef? field = HeapField(f, out bool known);
                    if (field != null) effects.Fields.Add(field);
                    else if (!known) effects.Pointers = true;
                    break;
                default:
                    effects.Pointers = true;
                    break;
            }
        return effects;
    }

    /// <summary>For each statement of a method: what the statements that may have run before it change.</summary>
    private static Dictionary<HStmt, Effects> BeforeEach(HMethod flow)
    {
        var entering = new Dictionary<HBlock, Effects>();
        foreach (HBlock b in flow.Blocks) entering[b] = new Effects();
        var before = new Dictionary<HStmt, Effects>();
        bool changed = true;
        for (int round = 0; changed && round < 64; round++)
        {
            changed = false;
            foreach (HBlock b in flow.Blocks)
            {
                var current = new Effects();
                current.Add(entering[b]);
                foreach (HStmt s in b.Statements)
                {
                    if (!before.TryGetValue(s, out Effects? seen)) before[s] = seen = new Effects();
                    seen.Add(current);
                    current.Add(EffectsOf(s));
                }
                var next = new List<HBlock>();
                switch (b.Statements[^1])
                {
                    case HJump j: next.Add(j.Target); break;
                    case HBranch br: next.Add(br.WhenTrue); next.Add(br.WhenFalse); break;
                    case HSwitch sw: next.AddRange(sw.Targets); next.Add(sw.Default); break;
                }
                foreach (HBlock to in next)
                    if (entering.TryGetValue(to, out Effects? e))
                        changed |= e.Add(current);
            }
        }
        return before;
    }

    /// <summary>What a value depends on besides variables of its own: a variable something points to, array elements, what a pointer leads to, fields of objects.</summary>
    private sealed class Sensitivity
    {
        public bool Taken, Elements, Pointers, Unknown;
        public readonly HashSet<FieldDef> Fields = [];
    }

    private static void Scan(HExpr? e, bool place, Sensitivity s)
    {
        switch (e)
        {
            case null or HConst or HArg or HMethodPointer or HMemberToken:
                return;
            case HLocal l:
                if (!place && l.Variable.AddressTaken) s.Taken = true;
                return;
            case HAddressOf a:
                Scan(a.Target, true, s);
                return;
            case HField f:
                if (f.Object == null)
                {
                    if (!place) s.Fields.Add(f.Field);
                    return;
                }
                if (f.Field.DeclaringType.IsValueType)
                {
                    Scan(f.Object, place, s);
                    return;
                }
                if (!place) s.Fields.Add(f.Field);
                Scan(f.Object, false, s);
                return;
            case HElement el:
                if (!place) s.Elements = true;
                Scan(el.Array, false, s);
                Scan(el.Index, false, s);
                return;
            case HDeref d:
                if (!place) s.Pointers = true;
                Scan(d.Pointer, false, s);
                return;
            case HArrayLength len: Scan(len.Array, false, s); return;
            case HUnary u: Scan(u.Operand, false, s); return;
            case HBinary b: Scan(b.Left, false, s); Scan(b.Right, false, s); return;
            case HCompare c: Scan(c.Left, false, s); Scan(c.Right, false, s); return;
            case HConv c: Scan(c.Operand, false, s); return;
            case HSelect sel: Scan(sel.Condition, false, s); Scan(sel.WhenTrue, false, s); Scan(sel.WhenFalse, false, s); return;
            case HTypeExpr t: Scan(t.Operand, false, s); return;
            default:
                s.Unknown = true;
                return;
        }
    }

    /// <summary>Whether a value may be different after those statements.</summary>
    private static bool Threatens(Effects before, Sensitivity s)
    {
        if (s.Unknown) return before.Calls || before.Pointers || before.Elements || before.Fields.Count != 0;
        bool memory = s.Taken || s.Elements || s.Pointers || s.Fields.Count != 0;
        if ((before.Calls || before.Pointers) && memory) return true;
        if (before.Elements && (s.Elements || s.Pointers)) return true;
        return before.Fields.Count != 0 && (s.Pointers || s.Fields.Overlaps(before.Fields));
    }

    private static readonly bool NoFieldPaths = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_FIELD_PATHS") != null;

    /// <summary>Whether the statement looks at or changes the part of the variable the path leads to (or what holds it, or what it holds).</summary>
    private static bool Overlaps(HStmt statement, HVar variable, List<FieldDef> path)
    {
        bool overlaps = false;
        void Look(HExpr e)
        {
            if (overlaps) return;
            // The access as a whole: the variable, and the fields of struct parts down to it.
            var fields = new List<FieldDef>();
            HExpr at = e;
            while (at is HField { Object: { } inside } part && part.Field.DeclaringType.IsValueType && !part.Field.IsStatic)
            {
                fields.Insert(0, part.Field);
                at = inside;
            }
            if (at is HLocal { Variable: var v } && ReferenceEquals(v, variable))
            {
                int common = Math.Min(fields.Count, path.Count);
                bool prefix = true;
                for (int k = 0; k < common && prefix; k++) prefix = ReferenceEquals(fields[k], path[k]);
                if (prefix) overlaps = true;
                return; // (Its own parts are this access.)
            }
            switch (e)
            {
                case HField f: if (f.Object != null) Look(f.Object); break;
                case HAddressOf a: if (Mentions(a.Target, variable)) overlaps = true; break;
                default:
                    FinallyFolding.Visit(e, x =>
                    {
                        if (!ReferenceEquals(x, e) && !overlaps && x is HField or HLocal) Look(x);
                        if (x is HAddressOf ad && Mentions(ad.Target, variable)) overlaps = true;
                    });
                    break;
            }
        }
        if (statement is HAssign a)
        {
            Look(a.Target);
            Look(a.Value);
        }
        else FinallyFolding.Visit(statement, x => { if (!overlaps && x is HField or HLocal) Look(x); });
        return overlaps;
    }

    private static bool Mentions(HExpr e, HVar v) => ConstructorFolding.Mentions(e, v);

    /// <summary>Whether two statements that follow each other do the same in the other order.</summary>
    private static bool Commute(HStmt first, HStmt second)
    {
        if (first is not HAssign a || second is not HAssign b) return false;
        if (HasCall(a.Value) || HasCall(b.Value) || HasCall(a.Target) || HasCall(b.Target)) return false;
        return !Disturbs(a, b) && !Disturbs(b, a);
    }

    private static HCompareOp Opposite(HCompareOp op) => op switch
    {
        HCompareOp.Eq => HCompareOp.Ne,
        HCompareOp.Ne => HCompareOp.Eq,
        HCompareOp.Lt => HCompareOp.Ge,
        HCompareOp.Le => HCompareOp.Gt,
        HCompareOp.Gt => HCompareOp.Le,
        HCompareOp.Ge => HCompareOp.Lt,
        HCompareOp.LtUn => HCompareOp.GeUn,
        HCompareOp.LeUn => HCompareOp.GtUn,
        HCompareOp.GtUn => HCompareOp.LeUn,
        _ => HCompareOp.LtUn,
    };

    private static HCompareOp Mirrored(HCompareOp op) => op switch
    {
        HCompareOp.Lt => HCompareOp.Gt,
        HCompareOp.Le => HCompareOp.Ge,
        HCompareOp.Gt => HCompareOp.Lt,
        HCompareOp.Ge => HCompareOp.Le,
        HCompareOp.LtUn => HCompareOp.GtUn,
        HCompareOp.LeUn => HCompareOp.GeUn,
        HCompareOp.GtUn => HCompareOp.LtUn,
        HCompareOp.GeUn => HCompareOp.LeUn,
        _ => op,
    };

    private static bool Whole(TypeSig? type) => type is PointerSig or ByRefSig || type is { IsValueType: false } ||
        type is PrimitiveSig { Element: not (Il2CppTypeEnum.R4 or Il2CppTypeEnum.R8) } || type is TypeDefSig { Definition.IsEnum: true };

    /// <summary>The test that holds exactly when this one does not; null when there is no telling (numbers that may be "not a number").</summary>
    private static HExpr? Negated(HExpr condition)
    {
        switch (condition)
        {
            case HUnary { Op: HUnaryOp.LogicalNot, Operand: var inner }:
                return inner;
            case HCompare c:
                if (c.Op is not (HCompareOp.Eq or HCompareOp.Ne) && !(Whole(c.Left.Type) && Whole(c.Right.Type))) return null;
                return new HCompare(Opposite(c.Op), c.Left, c.Right) { Type = c.Type };
            default:
                return new HUnary(HUnaryOp.LogicalNot, condition) { Type = condition.Type };
        }
    }

    /// <summary>The ways a test may be written: as it is, with its sides exchanged, and each of those turned around (true: the branches are exchanged then).</summary>
    private static IEnumerable<(HExpr Condition, bool Swapped)> Readings(HExpr condition)
    {
        yield return (condition, false);
        if (condition is HCompare c) yield return (new HCompare(Mirrored(c.Op), c.Right, c.Left) { Type = c.Type }, false);
        if (Negated(condition) is not { } negated) yield break;
        yield return (negated, true);
        if (negated is HCompare n) yield return (new HCompare(Mirrored(n.Op), n.Right, n.Left) { Type = n.Type }, true);
    }

    /// <summary>The comparison of a method that has branches with the code from one position on.</summary>
    private sealed class FlowMatch(Unifier unifier, int scope)
    {
        public Unifier U = unifier;
        /// <summary>The statements of the place that are the method's.</summary>
        public readonly HashSet<(HBlock Block, int Index)> Used = [];
        /// <summary>Where each "return" of the method leaves the place, with what it returns.</summary>
        public readonly List<(HExpr? Value, HBlock Block, int Index)> Exits = [];
        private readonly HashSet<(HBlock, int, HBlock, int)> _seen = [];
        /// <summary>How many statements of the method were compared; the first that did something; where its first stretch ended.</summary>
        public int Position, FirstEffect = int.MaxValue, EntryEnd = -1;
        private int _steps;
        /// <summary>For the trace: the method compared and the one it is looked for in.</summary>
        public HMethod? TracedFlow, TracedSite;
        /// <summary>Statements of the place among the method's first stretch that are the place's own, and stay.</summary>
        public readonly List<(HBlock Block, int Index)> Kept = [];
        /// <summary>Whether a test of a parameter may be missing at the place, decided by a constant handed over.</summary>
        public bool Decides;

        /// <summary>
        /// What the place has before its test that is not the method's: something of its own that the compiler
        /// worked out early (the object the next call is made on, read while a register was free). It may stay,
        /// before the call, where it does the same before the method's statements as among them - a value put
        /// into a variable of the place's, without a call. Only in the method's first stretch: what comes later
        /// is replaced whole.
        /// </summary>
        private bool Left(List<(HBlock Block, int Index)> site, bool[] used, bool entry)
        {
            List<(HBlock Block, int Index)>? kept = null;
            for (int c = 0; c < site.Count - 1; c++)
            {
                if (used[c]) continue;
                if (!entry || NoKept) return false;
                (HBlock b, int i) = site[c];
                if (!ReferenceEquals(b, site[0].Block)) return false;
                // (A field of a struct variable of the place too: the struct it hands over, filled in early.)
                if (b.Statements[i] is not HAssign { Target: var into, Value: var value } own || HasCall(value) || HasCall(into) ||
                    VariableOf(into) is not { } mine || U.SiteLocals.Contains(mine))
                    return false;
                for (int u = 0; u < site.Count - 1; u++)
                    if (used[u] && !Commute(site[u].Block.Statements[site[u].Index], own))
                        return false;
                (kept ??= []).Add((b, i));
            }
            if (kept != null) Kept.AddRange(kept);
            return true;
        }

        /// <summary>The variable a place is (a local), or is a part of (a field of a struct local, and so on); null for anything else.</summary>
        private static HVar? VariableOf(HExpr place)
        {
            if (place is HLocal { Variable: var whole }) return whole;
            if (NoKeptParts) return null;
            HExpr e = place;
            while (e is HField { Object: { } inside } f && !f.Field.IsStatic && inside.Type is { IsValueType: true } and not (PointerSig or ByRefSig)) e = inside;
            return !ReferenceEquals(e, place) && e is HLocal { Variable: var root, Type: not (PointerSig or ByRefSig) } ? root : null;
        }

        private void Take(List<(HBlock Block, int Index)> run, bool[] used, HBlock block, Unifier trial)
        {
            foreach (int d in trial.Consumed)
            {
                Used.Add((block, d));
                for (int k = 0; k < run.Count; k++)
                    if (ReferenceEquals(run[k].Block, block) && run[k].Index == d)
                        used[k] = true;
            }
        }

        /// <summary>
        /// A statement of the method the place does not have because the compiler found it changes nothing there:
        /// the clearing of the struct the method makes, or the store of zero (or of a parameter, which is then
        /// zero) into one of its fields - the compiler drops a store only where the field holds that value
        /// already (the place's struct was cleared, or given it before). Folded back, the call stores it again,
        /// which changes nothing either.
        /// </summary>
        private bool Elided(HStmt statement)
        {
            if (NoElidedStores) return false;
            bool Made(HExpr e) => e is HLocal { Variable: var v, Type: { IsValueType: true } } && !U.SiteLocals.Contains(v) || e is HArg { Index: -1, Type: ByRefSig or { IsValueType: true } };
            switch (statement)
            {
                case HAssign { Target: var target, Value: HTypeExpr { Op: HTypeOp.Default } } when Made(target):
                    return true;
                case HAssign { Target: HField { Object: { } owner, Field.IsStatic: false }, Value: var value } when Made(owner):
                    if (value is HConst { Value: null or false or 0 or 0L or 0f or 0d or (byte)0 or (sbyte)0 or (short)0 or (ushort)0 or 0u or 0ul }) return true;
                    if (value is not HArg { Index: >= 0 and var p } || p >= U.Arguments.Length || U.Arguments[p] != null) return false;
                    TypeSig type = U.Method.Parameters[p].Type;
                    if (type is ByRefSig or PointerSig || type.ContainsGenericParameter) return false;
                    object? zero = type switch
                    {
                        PrimitiveSig { Element: Rewind.Runtime.Il2CppTypeEnum.Boolean } => false,
                        PrimitiveSig { Element: Rewind.Runtime.Il2CppTypeEnum.I8 or Rewind.Runtime.Il2CppTypeEnum.U8 } => 0L,
                        PrimitiveSig { Element: Rewind.Runtime.Il2CppTypeEnum.R4 } => 0f,
                        PrimitiveSig { Element: Rewind.Runtime.Il2CppTypeEnum.R8 } => 0d,
                        { IsValueType: false } => null,
                        { Definition.IsEnum: true } or PrimitiveSig => 0,
                        _ => (object?)"struct",
                    };
                    if (zero is "struct") return false;
                    U.Arguments[p] = new HConst(zero, type);
                    U.BoundAt[p] = Position;
                    return true;
                default:
                    return false;
            }
        }

        private Unifier Trial(HBlock block, int at)
        {
            Unifier trial = U.Clone();
            trial.Site = block.Statements;
            trial.At = at;
            trial.Position = Position;
            trial.Consumed.Clear();
            return trial;
        }

        public bool Walk(HBlock methodBlock, int methodIndex, HBlock siteBlock, int siteIndex)
        {
            if (++_steps > 300 || siteBlock.Scope != scope) { if (TracedFlow != null) Console.Error.WriteLine("[inline]     steps or scope"); return false; }
            List<(HBlock Block, int Index)>? method = RunFrom(methodBlock, methodIndex), site = RunFrom(siteBlock, siteIndex);
            if (method == null || site == null) { if (TracedFlow != null) Console.Error.WriteLine($"[inline]     no run ({method == null}, {site == null})"); return false; }
            // Been here with the method at this point already (a loop, or two ways that meet): compared once.
            if (!_seen.Add((method[0].Block, method[0].Index, site[0].Block, site[0].Index))) return true;
            bool entry = EntryEnd < 0;
            var used = new bool[site.Count];
            int cursor = 0;
            for (int k = 0; k < method.Count - 1; k++)
            {
                HStmt statement = method[k].Block.Statements[method[k].Index];
                // The place may have the statements that do not depend on each other in another order.
                bool found = false;
                int skipped = 0;
                for (int c = cursor; c < site.Count - 1 && skipped <= 6 && !found; c++)
                {
                    if (used[c]) continue;
                    (HBlock b, int i) = site[c];
                    Unifier trial = Trial(b, i);
                    bool fits = trial.Statement(statement, b.Statements[i]);
                    for (int u = cursor; u < c && fits; u++)
                    {
                        if (used[u] || (ReferenceEquals(site[u].Block, b) && trial.Consumed.Contains(site[u].Index))) continue;
                        fits = Commute(site[u].Block.Statements[site[u].Index], b.Statements[i]);
                    }
                    if (!fits)
                    {
                        skipped++;
                        continue;
                    }
                    Take(site, used, b, trial);
                    used[c] = true;
                    Used.Add((b, i));
                    bool inert = b.Statements[i] is HAssign { Target: HLocal target, Value: var value } && trial.SiteLocals.Contains(target.Variable) && !HasCall(value);
                    if (entry && !inert && FirstEffect == int.MaxValue) FirstEffect = Position;
                    U = trial;
                    found = true;
                }
                if (!found && Elided(statement))
                {
                    if (TracedFlow != null) Console.Error.WriteLine($"[inline]     taken as left out: {HirPrinter.Print(statement, TracedFlow).Trim()}");
                    Position++;
                    continue;
                }
                if (!found)
                {
                    if (TracedFlow != null && TracedSite != null)
                    {
                        Console.Error.WriteLine($"[inline]     nothing for: {HirPrinter.Print(statement, TracedFlow).Trim()}");
                        for (int c = cursor; c < site.Count && c < cursor + 8; c++)
                            Console.Error.WriteLine($"[inline]       {(used[c] ? "taken" : "     ")} {HirPrinter.Print(site[c].Block.Statements[site[c].Index], TracedSite).Trim()}");
                    }
                    return false;
                }
                while (cursor < site.Count - 1 && used[cursor]) cursor++;
                Position++;
            }
            if (entry) EntryEnd = Position;

            HStmt last = method[^1].Block.Statements[method[^1].Index];
            if (last is HReturn ret)
            {
                // What is left here is the caller's. Where one of the method's statements comes after some of it
                // (each was found to do the same on either side of what it was looked for past), the caller's
                // statements stay, behind the call - for a method that hands nothing back; where a value is
                // returned, how the place goes on with it is looked at statement by statement.
                while (cursor < site.Count - 1 && used[cursor]) cursor++;
                for (int c = cursor; c < site.Count - 1; c++)
                    if (used[c] && (NoBehind || ret.Value != null))
                    { if (TracedFlow != null) Console.Error.WriteLine("[inline]     used after the return"); return false; }
                Exits.Add((ret.Value, site[cursor].Block, site[cursor].Index));
                return true;
            }

            (HBlock endBlock, int endIndex) = site[^1];
            HStmt end = endBlock.Statements[endIndex];
            if (!Decides || last is not HBranch test || Decided(test) is not { } ways) return Ended();

            // The method tests one of its parameters here and nothing else. The place has that test too where
            // it handed over something not known beforehand - that reading first. Where it handed over a
            // constant, the compiler knew how the test goes and left it out: the place goes straight on the
            // way the test leads with that constant.
            while (cursor < site.Count - 1 && used[cursor]) cursor++;
            for (int c = cursor; c < site.Count - 1; c++)
                if (used[c])
                    return Ended();
            (HBlock onBlock, int onIndex) = site[cursor];
            Mark mark = Save();
            if (Ended()) return true;
            foreach ((int parameter, HExpr? value, HBlock way) in ways)
            {
                Restore(mark);
                if (value != null)
                {
                    Unifier trial = U.Clone();
                    trial.Arguments[parameter] = value;
                    trial.BoundAt[parameter] = Position;
                    U = trial;
                }
                if (TracedFlow != null)
                {
                    object shown = (value ?? U.Arguments[parameter]) is HConst { Value: var v } ? v ?? "null" : "?";
                    Console.Error.WriteLine($"[inline]     no test of parameter {parameter} here: going on as with {shown}");
                }
                Position++;
                if (Walk(way, 0, onBlock, onIndex)) return true;
            }
            return false;

            // How the place ends this stretch the way the method does: the same test, the same throw.
            bool Ended()
            {
                switch (last, end)
                {
                    case (HBranch mb, HBranch sb):
                    {
                        bool? swapped = null;
                        foreach ((HExpr reading, bool exchanged) in Readings(sb.Condition))
                        {
                            Unifier trial = Trial(endBlock, endIndex);
                            if (!trial.Expression(mb.Condition, reading)) continue;
                            Take(site, used, endBlock, trial);
                            U = trial;
                            swapped = exchanged;
                            break;
                        }
                        if (swapped == null) { if (TracedFlow != null) Console.Error.WriteLine($"[inline]     test differs: {HirPrinter.Print(mb, TracedFlow).Trim()} / {HirPrinter.Print(sb, TracedSite!).Trim()}"); return false; }
                        if (!Left(site, used, entry))
                        {
                            if (TracedFlow != null)
                                for (int c = 0; c < site.Count - 1; c++)
                                    if (!used[c]) Console.Error.WriteLine($"[inline]     left before the test: {HirPrinter.Print(site[c].Block.Statements[site[c].Index], TracedSite!).Trim()}");
                            return false;
                        }
                        Used.Add((endBlock, endIndex));
                        Position++;
                        return Walk(mb.WhenTrue, 0, swapped.Value ? sb.WhenFalse : sb.WhenTrue, 0) &&
                               Walk(mb.WhenFalse, 0, swapped.Value ? sb.WhenTrue : sb.WhenFalse, 0);
                    }
                    case (HSwitch ms, HSwitch ss):
                    {
                        if (ms.Targets.Length != ss.Targets.Length) return false;
                        Unifier trial = Trial(endBlock, endIndex);
                        if (!trial.Expression(ms.Value, ss.Value)) return false;
                        Take(site, used, endBlock, trial);
                        U = trial;
                        while (cursor < site.Count - 1 && used[cursor]) cursor++;
                        if (cursor != site.Count - 1) return false;
                        Used.Add((endBlock, endIndex));
                        Position++;
                        for (int t = 0; t < ms.Targets.Length; t++)
                            if (!Walk(ms.Targets[t], 0, ss.Targets[t], 0))
                                return false;
                        return Walk(ms.Default, 0, ss.Default, 0);
                    }
                    case (HThrow mt, HThrow st):
                    {
                        Unifier trial = Trial(endBlock, endIndex);
                        if (!trial.Expression(mt.Exception, st.Exception)) return false;
                        Take(site, used, endBlock, trial);
                        U = trial;
                        while (cursor < site.Count - 1 && used[cursor]) cursor++;
                        if (cursor != site.Count - 1) return false;
                        Used.Add((endBlock, endIndex));
                        Position++;
                        return true;
                    }
                    default:
                        return false;
                }
            }
        }

        /// <summary>
        /// A test of the method's that looks at one of its parameters and nothing else ("if (notify)",
        /// "if (mode == 2)", "if (callback == null)"): the ways it goes for a constant handed over, each with
        /// that constant - or the one way, with none, where the constant the place handed over is known.
        /// </summary>
        private List<(int Parameter, HExpr? Value, HBlock Way)>? Decided(HBranch test)
        {
            HExpr condition = test.Condition;
            // Whether the test holds when the parameter is the value it is compared with.
            bool holds = true;
            while (condition is HUnary { Op: HUnaryOp.LogicalNot, Operand: var inner })
            {
                condition = inner;
                holds = !holds;
            }
            HArg asked;
            long against = 0;
            object? constant = null;
            bool nothing = false;
            switch (condition)
            {
                case HArg a:
                    // "if (flag)": holds when the flag is not 0.
                    asked = a;
                    holds = !holds;
                    break;
                case HCompare { Op: HCompareOp.Eq or HCompareOp.Ne, Left: HArg a, Right: HConst { Value: var compared } } c when Integral(compared) is { } number:
                    asked = a;
                    against = number;
                    constant = compared;
                    nothing = compared == null;
                    if (c.Op == HCompareOp.Ne) holds = !holds;
                    break;
                default:
                    return null;
            }
            if (asked.Index < 0 || asked.Index >= U.Arguments.Length) return null;
            HBlock same = holds ? test.WhenTrue : test.WhenFalse, other = holds ? test.WhenFalse : test.WhenTrue;
            if (U.Arguments[asked.Index] is { } handed)
            {
                if (handed is not HConst { Value: var known } || Integral(known) is not { } had) return null;
                var one = new List<(int Parameter, HExpr? Value, HBlock Way)>();
                one.Add((asked.Index, null, had == against ? same : other));
                return one;
            }

            TypeSig type = U.Method.Parameters[asked.Index].Type;
            var ways = new List<(int Parameter, HExpr? Value, HBlock Way)>();
            if (type is PrimitiveSig { Element: Il2CppTypeEnum.Boolean })
            {
                if (nothing || against is not (0 or 1)) return null;
                ways.Add((asked.Index, new HConst(against != 0, type), same));
                ways.Add((asked.Index, new HConst(against == 0, type), other));
                // The way that does something first: one that only returns is there wherever one looks.
                if (same.Statements.Count != 0 && same.Statements[0] is HReturn && !(other.Statements.Count != 0 && other.Statements[0] is HReturn)) ways.Reverse();
            }
            else if (nothing)
            {
                // "No object" handed over: the test for it is known to hold.
                if (type.IsValueType || type is PointerSig or ByRefSig or GenericParamSig || type.ContainsGenericParameter) return null;
                ways.Add((asked.Index, new HConst(null, type), same));
            }
            else if (type is PrimitiveSig { Element: Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 or Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 or Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 or
                                                     Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 or Il2CppTypeEnum.Char } || type is TypeDefSig { Definition.IsEnum: true })
            {
                // One of many values: only the one the test names is known from it.
                ways.Add((asked.Index, new HConst(constant, type), same));
            }
            else return null;
            return ways;
        }

        /// <summary>What a comparison has found so far, to go back to when one reading of a test does not hold.</summary>
        private sealed record Mark(Unifier U, (HBlock, int)[] Used, int Exits, int Kept, (HBlock, int, HBlock, int)[] Seen, int Position, int FirstEffect, int EntryEnd);

        private Mark Save() => new(U, [.. Used], Exits.Count, Kept.Count, [.. _seen], Position, FirstEffect, EntryEnd);

        private void Restore(Mark mark)
        {
            U = mark.U;
            Used.Clear();
            foreach ((HBlock b, int i) in mark.Used) Used.Add((b, i));
            Exits.RemoveRange(mark.Exits, Exits.Count - mark.Exits);
            Kept.RemoveRange(mark.Kept, Kept.Count - mark.Kept);
            _seen.Clear();
            foreach (var seen in mark.Seen) _seen.Add(seen);
            (Position, FirstEffect, EntryEnd) = (mark.Position, mark.FirstEffect, mark.EntryEnd);
        }
    }

    private static bool SameStatement(HStmt a, HStmt b) => (a, b) switch
    {
        (HAssign x, HAssign y) => HirCleanup.Same(x.Target, y.Target) && HirCleanup.Same(x.Value, y.Value),
        (HEval x, HEval y) => HirCleanup.Same(x.Expression, y.Expression),
        _ => false,
    };

    /// <summary>
    /// Whether going on at either position does the same: one position, or the same few statements (the
    /// compiler copies a short end of a loop or a method to each way that leads to it) up to one position.
    /// </summary>
    private static bool SameExit((HBlock Block, int Index) a, (HBlock Block, int Index) b, HashSet<(HBlock Block, int Index)>? taken = null, Counts? counts = null)
    {
        // The method's own statements among what is left are not part of how the place goes on.
        (HBlock Block, int Index) Own((HBlock Block, int Index) at)
        {
            while (taken != null && taken.Contains(at) && at.Index + 1 < at.Block.Statements.Count) at = Past(at.Block, at.Index + 1);
            return at;
        }
        // Each copy of the statements has temporaries of its own: one stands for its counterpart in the other.
        Dictionary<HVar, HVar>? counterpart = null;
        Dictionary<HVar, int>? readHere = null, readThere = null;
        bool Alike(HExpr? x, HExpr? y)
        {
            // Two copies of the same call are the same code (not the same value: each copy is run on one way).
            if (!NoAlikeCalls && x is HCall c && y is HCall d)
            {
                if (!ReferenceEquals(c.Method, d.Method) || c.Virtual != d.Virtual || !ReferenceEquals(c.DeclaringType, d.DeclaringType) ||
                    !ReferenceEquals(c.Constrained, d.Constrained) || c.MethodArguments.Length != d.MethodArguments.Length ||
                    c.Arguments.Length != d.Arguments.Length || !Alike(c.This, d.This))
                    return false;
                for (int k = 0; k < c.MethodArguments.Length; k++)
                    if (!ReferenceEquals(c.MethodArguments[k], d.MethodArguments[k]))
                        return false;
                for (int k = 0; k < c.Arguments.Length; k++)
                    if (!Alike(c.Arguments[k], d.Arguments[k]))
                        return false;
                return true;
            }
            if (counterpart == null) return HirCleanup.Same(x, y);
            if (ReferenceEquals(x, y)) return true;
            if (x == null || y == null || x.GetType() != y.GetType()) return false;
            switch (x)
            {
                case HLocal p:
                {
                    HVar other = ((HLocal)y).Variable;
                    if (counterpart.TryGetValue(p.Variable, out HVar? mapped))
                    {
                        if (!ReferenceEquals(mapped, other)) return false;
                        readHere![p.Variable] = readHere.GetValueOrDefault(p.Variable) + 1;
                        readThere![other] = readThere.GetValueOrDefault(other) + 1;
                        return true;
                    }
                    return ReferenceEquals(p.Variable, other);
                }
                case HField p: return ReferenceEquals(p.Field, ((HField)y).Field) && Alike(p.Object, ((HField)y).Object);
                case HArrayLength p: return Alike(p.Array, ((HArrayLength)y).Array);
                case HElement p: return Alike(p.Array, ((HElement)y).Array) && Alike(p.Index, ((HElement)y).Index);
                case HUnary p: return p.Op == ((HUnary)y).Op && Alike(p.Operand, ((HUnary)y).Operand);
                case HBinary p: return p.Op == ((HBinary)y).Op && Alike(p.Left, ((HBinary)y).Left) && Alike(p.Right, ((HBinary)y).Right);
                case HCompare p: return p.Op == ((HCompare)y).Op && Alike(p.Left, ((HCompare)y).Left) && Alike(p.Right, ((HCompare)y).Right);
                case HConv p: return p.Kind == ((HConv)y).Kind && Alike(p.Operand, ((HConv)y).Operand);
                case HDeref p: return Alike(p.Pointer, ((HDeref)y).Pointer);
                case HAddressOf p: return Alike(p.Target, ((HAddressOf)y).Target);
                default: return HirCleanup.Same(x, y);
            }
        }
        bool AlikeStatements(HStmt x, HStmt y)
        {
            if (counts == null || NoRenamedEnds) return SameStatement(x, y);
            switch (x, y)
            {
                case (HAssign p, HAssign q):
                    if (!Alike(p.Value, q.Value)) return false;
                    if (p.Target is HLocal { Variable: var here } && q.Target is HLocal { Variable: var there } && !ReferenceEquals(here, there))
                    {
                        if (counts.Defs.GetValueOrDefault(here) != 1 || counts.Defs.GetValueOrDefault(there) != 1 || here.AddressTaken || there.AddressTaken ||
                            here.Type?.Key != there.Type?.Key)
                            return false;
                        counterpart ??= [];
                        readHere ??= [];
                        readThere ??= [];
                        if (counterpart.TryGetValue(here, out HVar? known)) return ReferenceEquals(known, there);
                        counterpart[here] = there;
                        return true;
                    }
                    return Alike(p.Target, q.Target);
                case (HEval p, HEval q):
                    return Alike(p.Expression, q.Expression);
                default:
                    return false;
            }
        }
        // Nothing outside its copy reads such a temporary: every reading of it was one of those compared.
        bool Closed()
        {
            if (counterpart == null) return true;
            foreach (var (here, there) in counterpart)
                if (readHere!.GetValueOrDefault(here) != counts!.Reads.GetValueOrDefault(here) || readThere!.GetValueOrDefault(there) != counts.Reads.GetValueOrDefault(there))
                    return false;
            return true;
        }
        for (int step = 0; step < 8; step++)
        {
            a = Own(a);
            b = Own(b);
            if (ReferenceEquals(a.Block, b.Block) && a.Index == b.Index) return Closed();
            if (a.Block.Scope != b.Block.Scope) return false;
            HStmt x = a.Block.Statements[a.Index], y = b.Block.Statements[b.Index];
            switch (x, y)
            {
                case (HReturn r, HReturn q):
                    return (r.Value == null ? q.Value == null : q.Value != null && Alike(r.Value, q.Value)) && Closed();
                case (HBranch r, HBranch q):
                    return ReferenceEquals(r.WhenTrue, q.WhenTrue) && ReferenceEquals(r.WhenFalse, q.WhenFalse) && Alike(r.Condition, q.Condition) && Closed();
                case (HJump r, HJump q):
                    return ReferenceEquals(r.Target, q.Target) && Closed();
            }
            if (!AlikeStatements(x, y) || a.Index + 1 >= a.Block.Statements.Count || b.Index + 1 >= b.Block.Statements.Count) return false;
            a = Past(a.Block, a.Index + 1);
            b = Past(b.Block, b.Index + 1);
        }
        return false;
    }

    private static long? Integral(object? value) => value switch
    {
        // "no object": what a test of an object for being there compares with.
        null => 0,
        bool b => b ? 1 : 0,
        byte n => n,
        sbyte n => n,
        short n => n,
        ushort n => n,
        char n => n,
        int n => n,
        uint n => n,
        long n => n,
        _ => null,
    };

    /// <summary>Where a test of a variable at a position leads when the variable has a known value; null when that is not what stands there.</summary>
    private static (HBlock Block, int Index)? Leads(HVar variable, (HBlock Block, int Index) at, long value) =>
        Leads(e => e is HLocal l && ReferenceEquals(l.Variable, variable), at, value);

    /// <summary>The same, for a test of a value that stands in the test itself.</summary>
    private static (HBlock Block, int Index)? Leads(Func<HExpr, bool> result, (HBlock Block, int Index) at, long value, bool zero = false)
    {
        if (at.Block.Statements[at.Index] is not HBranch branch) return null;
        // zero: the value is a struct with nothing in it, of which the test reads a field (whole numbers only).
        bool InValue(HExpr e) => result(e) || (e is HField { Object: { } inside, Field.IsStatic: false } && InValue(inside));
        long? Worth(HExpr e) => e switch
        {
            HField { Object: { } inside, Type: var type } when zero && !NoZeroStructs && InValue(inside) && Whole(type) => 0,
            _ when zero && result(e) => null,
            _ when result(e) => value,
            HConst c => Integral(c.Value),
            HConv { Kind: HConvKind.I1 or HConvKind.U1 or HConvKind.I2 or HConvKind.U2 or HConvKind.I4 or HConvKind.U4 or HConvKind.I8 or HConvKind.U8 } c when value is 0 or 1 => Worth(c.Operand),
            HUnary { Op: HUnaryOp.LogicalNot } u => Worth(u.Operand) is { } v ? (v == 0 ? 1 : 0) : null,
            HCompare { Op: HCompareOp.Eq } c => Worth(c.Left) is { } a && Worth(c.Right) is { } b ? (a == b ? 1 : 0) : null,
            HCompare { Op: HCompareOp.Ne } c => Worth(c.Left) is { } a && Worth(c.Right) is { } b ? (a != b ? 1 : 0) : null,
            // Order, of whole numbers.
            HCompare { Op: var op } c when !NoZeroStructs && Whole(c.Left.Type) && Whole(c.Right.Type) && Worth(c.Left) is { } a && Worth(c.Right) is { } b => op switch
            {
                HCompareOp.Lt => a < b ? 1 : 0,
                HCompareOp.Le => a <= b ? 1 : 0,
                HCompareOp.Gt => a > b ? 1 : 0,
                HCompareOp.Ge => a >= b ? 1 : 0,
                HCompareOp.LtUn => (ulong)a < (ulong)b ? 1 : 0,
                HCompareOp.LeUn => (ulong)a <= (ulong)b ? 1 : 0,
                HCompareOp.GtUn => (ulong)a > (ulong)b ? 1 : 0,
                HCompareOp.GeUn => (ulong)a >= (ulong)b ? 1 : 0,
                _ => null,
            },
            _ => null,
        };
        if (Worth(branch.Condition) is not { } decided) return null;
        return Past(decided != 0 ? branch.WhenTrue : branch.WhenFalse, 0);
    }

    /// <summary>One reading of how a "return" hands its value on: the variable given it, after which statements, and where it goes on.</summary>
    private sealed class Handing
    {
        public required HVar Into;
        public required HExpr Value;
        public required Dictionary<HVar, HExpr> Given;
        public required (HBlock Block, int Index) After;
        public required List<(HBlock Block, int Index)> Taken;
        public required HBlock Block;
        public required int Index;
    }

    /// <summary>
    /// What the place does with a returned value: "r = value" - or, where the compiler joined the ends of two
    /// returns, "t = part; ... r = something of t".
    /// </summary>
    private static List<Handing> Handings(HBlock block, int index)
    {
        var result = new List<Handing>();
        var given = new Dictionary<HVar, HExpr>();
        var taken = new List<(HBlock, int)>();
        (HBlock b, int i) = Past(block, index);
        for (int step = 0; step < 3; step++)
        {
            if (b.Statements[i] is not HAssign { Target: HLocal target, Value: var value } || i + 1 >= b.Statements.Count) break;
            taken.Add((b, i));
            (HBlock nb, int ni) = Past(b, i + 1);
            result.Add(new Handing { Into = target.Variable, Value = value, Given = new Dictionary<HVar, HExpr>(given), After = (nb, ni), Taken = [.. taken], Block = b, Index = i });
            if (!HirBuilder.IsPure(value) || target.Variable.AddressTaken) break;
            given[target.Variable] = value;
            (b, i) = (nb, ni);
        }
        return result;
    }

    private static bool Returned(Unifier trial, HExpr? value, Handing handing, List<(HBlock Block, int Index)> taken)
    {
        trial.Site = handing.Block.Statements;
        trial.At = handing.Index;
        trial.Consumed.Clear();
        trial.Given = handing.Given.Count != 0 ? handing.Given : null;
        bool same = trial.Expression(value, handing.Value);
        trial.Given = null;
        if (!same) return false;
        foreach (int d in trial.Consumed) taken.Add((handing.Block, d));
        taken.AddRange(handing.Taken);
        return true;
    }

    private static HashSet<HBlock> Reachable(HMethod method)
    {
        var reached = new HashSet<HBlock>();
        var pending = new Stack<HBlock>();
        if (method.Blocks.Count != 0) pending.Push(method.Blocks[0]);
        while (true)
        {
            while (pending.Count != 0)
            {
                HBlock b = pending.Pop();
                if (!reached.Add(b) || b.Statements.Count == 0) continue;
                switch (b.Statements[^1])
                {
                    case HJump j: pending.Push(j.Target); break;
                    case HBranch br: pending.Push(br.WhenTrue); pending.Push(br.WhenFalse); break;
                    case HSwitch sw:
                        foreach (HBlock t in sw.Targets) pending.Push(t);
                        pending.Push(sw.Default);
                        break;
                }
            }
            foreach (HTryRegion r in method.TryRegions.Values)
                if (reached.Contains(r.Entry) && !reached.Contains(r.HandlerEntry))
                    pending.Push(r.HandlerEntry);
            if (pending.Count == 0) return reached;
        }
    }

    private bool TryFoldFlow(HMethod method, HBlock block, int at, Template template, Counts counts)
    {
        HMethod flow = template.Flow!;
        // Where the method's first statement would be: in this block, or in one that leads here.
        Dictionary<HBlock, List<HBlock>> before = counts.Predecessors(method);
        var starts = new List<HBlock> { block };
        for (int k = 0; k < starts.Count && starts.Count < 16; k++)
            if (before.TryGetValue(starts[k], out List<HBlock>? leading))
                foreach (HBlock p in leading)
                    if (p.Scope == block.Scope && !starts.Contains(p) && starts.Count < 16)
                        starts.Add(p);
        foreach (HBlock first in starts)
        {
            int from = ReferenceEquals(first, block) ? at : first.Statements.Count - 1;
            for (int start = from; start >= 0; start--)
            {
                var match = new FlowMatch(new Unifier(this, template, first.Statements, counts), first.Scope) { Decides = _decided };
                if (Tracing(template.Method)) (match.TracedFlow, match.TracedSite) = (flow, method);
                bool walked = match.Walk(flow.Blocks[0], 0, first, start);
                _partly |= !walked && match.Position != 0;
                if (Tracing(template.Method) && (walked || match.Position != 0))
                    Console.Error.WriteLine($"[inline] {method.Method.Name}: {template.Method.Name}<{string.Join(",", template.ClassArguments.Select(a => a.ShortName))}> at {first}[{start}]: {(walked ? "compared" : "differs")} after {match.Position} statements, {match.Exits.Count} returns");
                if (!walked) continue;
                if (!match.Used.Contains((block, at))) continue;
                bool done = Finish(method, template, match, first, start);
                if (Tracing(template.Method)) Console.Error.WriteLine($"[inline]   {(done ? "folded" : "not folded")}");
                if (done) return true;
            }
        }
        return false;
    }

    /// <summary>The comparison held: where the place goes on, what it does with the result, whether a call there does the same - and then the call.</summary>
    private bool Finish(HMethod method, Template template, FlowMatch match, HBlock first, int start)
    {
        MethodDef m = template.Method;
        bool Why(string reason)
        {
            if (Tracing(m)) Console.Error.WriteLine($"[inline]   {reason}");
            return false;
        }
        if (match.Exits.Count == 0) return false;
        (HBlock Block, int Index) next = Past(match.Exits[0].Block, match.Exits[0].Index);
        HVar? into = null;
        HExpr? replaced = null;
        (HBlock True, HBlock False)? ways = null;
        bool handedOn = false;
        var temporaries = new HashSet<HVar>();

        bool OneWayOn()
        {
            foreach (var exit in match.Exits)
                if (!SameExit(next, Past(exit.Block, exit.Index), match.Used, match.U.Counted))
                    return false;
            return true;
        }

        if (m.ReturnType.IsVoid)
        {
            if (!OneWayOn()) return Why("its returns do not go on at one place");
        }
        else
        {
            bool settled = false;
            // Every return gives its value to the same variable, and they go on at the same place - or, where
            // the value returned is a constant and the place tests the variable there, straight at where that
            // test leads with it (the compiler skips a test whose outcome it knows).
            foreach (var lead in match.Exits)
            {
                foreach (Handing handing in Handings(lead.Block, lead.Index))
                {
                    Unifier trial = match.U.Clone();
                    var taken = new List<(HBlock Block, int Index)>();
                    bool all = true;
                    foreach (var exit in match.Exits)
                    {
                        Handing? other = Handings(exit.Block, exit.Index).FirstOrDefault(h => ReferenceEquals(h.Into, handing.Into) && SameExit(h.After, handing.After));
                        if (other != null)
                        {
                            Unifier attempt = trial.Clone();
                            if (Returned(attempt, exit.Value, other, taken))
                            {
                                trial = attempt;
                                continue;
                            }
                        }
                        if (exit.Value is HConst { Value: var constant } && Integral(constant) is { } known && Leads(handing.Into, handing.After, known) is { } led &&
                            SameExit(led, Past(exit.Block, exit.Index))) continue;
                        all = false;
                        break;
                    }
                    if (!all) continue;
                    match.U = trial;
                    next = handing.After;
                    into = handing.Into;
                    foreach ((HBlock b, int i) in taken)
                    {
                        match.Used.Add((b, i));
                        if (b.Statements[i] is HAssign { Target: HLocal { Variable: var set } } && !ReferenceEquals(set, into)) temporaries.Add(set);
                    }
                    settled = true;
                    break;
                }
                if (settled) break;
            }
            // A yes or no that is only ever tested: every return says which, and each answer goes on at one place.
            if (!settled && match.Exits.Count >= 2 && m.ReturnType is PrimitiveSig { Element: Il2CppTypeEnum.Boolean } &&
                match.Exits.All(e => e.Value is HConst { Value: var v } && Integral(v) is 0 or 1))
            {
                (HBlock Block, int Index)? yes = null, no = null;
                bool agree = true;
                foreach (var exit in match.Exits)
                {
                    (HBlock Block, int Index) at = Past(exit.Block, exit.Index);
                    if (Integral(((HConst)exit.Value!).Value) == 1)
                    {
                        if (yes == null) yes = at;
                        else agree &= SameExit(yes.Value, at);
                    }
                    else
                    {
                        if (no == null) no = at;
                        else agree &= SameExit(no.Value, at);
                    }
                }
                if (agree && yes is { Index: 0 } whenTrue && no is { Index: 0 } whenFalse)
                {
                    ways = (whenTrue.Block, whenFalse.Block);
                    settled = true;
                }
            }
            // The method's own variable for the result is the place's too.
            if (!settled && match.Exits[0].Value is HLocal { Variable: var returned } && match.U.Locals.TryGetValue(returned, out HVar? kept) &&
                match.Exits.All(e => e.Value is HLocal l && ReferenceEquals(l.Variable, returned)) && OneWayOn())
            {
                into = kept;
                settled = true;
            }
            // One return, its value used on the spot.
            if (!settled && match.Exits.Count == 1)
            {
                HStmt user = next.Block.Statements[next.Index];
                var candidates = new List<HExpr>();
                FinallyFolding.Visit(user, candidates.Add);
                foreach (HExpr candidate in candidates)
                {
                    if (user is HAssign { Target: var place } && ReferenceEquals(place, candidate)) continue;
                    Unifier trial = match.U.Clone();
                    trial.Site = next.Block.Statements;
                    trial.At = next.Index;
                    trial.Consumed.Clear();
                    if (!trial.Expression(match.Exits[0].Value, candidate)) continue;
                    foreach (int d in trial.Consumed) match.Used.Add((next.Block, d));
                    match.U = trial;
                    replaced = candidate;
                    settled = true;
                    break;
                }
            }
            // One return computes its value and the place tests it on the spot; the others return constants and
            // go on where that test leads with them.
            // (A struct with nothing in it is a constant too: every field of it is zero.)
            if (!settled && match.Exits.Count >= 2 && match.Exits.Count(e => e.Value is not HConst && !ZeroStruct(e.Value)) == 1)
            {
                var computed = match.Exits.First(e => e.Value is not HConst && !ZeroStruct(e.Value));
                (HBlock Block, int Index) at = Past(computed.Block, computed.Index);
                if (at.Block.Statements[at.Index] is HBranch test)
                {
                    var candidates = new List<HExpr>();
                    FinallyFolding.Visit(test.Condition, candidates.Add);
                    foreach (HExpr candidate in candidates)
                    {
                        Unifier trial = match.U.Clone();
                        trial.Site = at.Block.Statements;
                        trial.At = at.Index;
                        trial.Consumed.Clear();
                        if (!trial.Expression(computed.Value, candidate)) continue;
                        bool all = true;
                        foreach (var other in match.Exits)
                        {
                            if (ZeroStruct(other.Value))
                            {
                                all &= Leads(e => ReferenceEquals(e, candidate), at, 0, zero: true) is { } cleared && SameExit(cleared, Past(other.Block, other.Index));
                                continue;
                            }
                            if (other.Value is not HConst { Value: var constant }) continue;
                            all &= Integral(constant) is { } known && Leads(e => ReferenceEquals(e, candidate), at, known) is { } led && SameExit(led, Past(other.Block, other.Index));
                        }
                        if (!all) continue;
                        foreach (int d in trial.Consumed) match.Used.Add((at.Block, d));
                        match.U = trial;
                        replaced = candidate;
                        next = at;
                        settled = true;
                        break;
                    }
                }
            }
            // What the method gives is what the place gives: each of its returns is a return of the place, of
            // the same value ("return x.Method();" with the method's own code in place of the call).
            if (!settled && !NoHandedOn && method.Method.ReturnType.Key == m.ReturnType.Key)
            {
                Unifier trial = match.U.Clone();
                var consumed = new List<(HBlock Block, int Index)>();
                bool all = true;
                foreach (var exit in match.Exits)
                {
                    (HBlock Block, int Index) at = Past(exit.Block, exit.Index);
                    if (at.Index >= at.Block.Statements.Count || at.Block.Statements[at.Index] is not HReturn { Value: { } given })
                    {
                        all = false;
                        break;
                    }
                    trial.Site = at.Block.Statements;
                    trial.At = at.Index;
                    trial.Consumed.Clear();
                    // A constant is what it is, however the place has it written ("true" as 1).
                    bool same = exit.Value is HConst { Value: var wanted } && given is HConst { Value: var had } && Integral(wanted) is { } a && Integral(had) is { } b
                        ? a == b
                        : trial.Expression(exit.Value, given);
                    if (!same)
                    {
                        all = false;
                        break;
                    }
                    foreach (int d in trial.Consumed) consumed.Add((at.Block, d));
                }
                if (all)
                {
                    foreach (var used in consumed) match.Used.Add(used);
                    match.U = trial;
                    handedOn = true;
                    settled = true;
                }
            }
            if (!settled) return Why("what it returns is not taken up here");
        }
        Unifier unifier = match.U;

        // The arguments are computed once, before the call: each must be worth the same there as wherever the
        // method uses it - nothing that may have run before a use can have changed it.
        Dictionary<HStmt, Effects> before = template.Before ??= BeforeEach(template.Flow!);
        bool Valid(HExpr? value, int parameter)
        {
            if (value == null) return true;
            foreach (HVar local in unifier.SiteLocals)
                if (ConstructorFolding.Mentions(value, local))
                    return false;
            foreach (HVar local in temporaries)
                if (ConstructorFolding.Mentions(value, local))
                    return false;
            if (Stable(value)) return true;
            // A struct written out: made of its values, where they are worth the same.
            if (Written(value))
            {
                foreach (HExpr part in ((HNewObject)value).Arguments)
                    if (!Valid(part, parameter))
                        return false;
                return true;
            }
            var sensitivity = new Sensitivity();
            Scan(value, false, sensitivity);
            foreach (HBlock b in template.Flow!.Blocks)
                foreach (HStmt s in b.Statements)
                {
                    bool uses = false;
                    FinallyFolding.Visit(s, e => uses |= e is HArg a && (parameter < 0 ? a.Index < 0 : a.Index == parameter));
                    if (uses && before.TryGetValue(s, out Effects? earlier) && Threatens(earlier, sensitivity)) return false;
                }
            return true;
        }
        // (A struct's method is called on the struct's place, not its value: a variable is the same place
        // throughout, whatever the method writes into it - a constructor writes all of it.)
        bool structPlace = !NoStructFlows && m.DeclaringType.IsValueType && unifier.This is HLocal or HAddressOf { Target: HLocal };
        if (!structPlace && !Valid(unifier.This, -1)) return Why("what it is called on is not worth the same before");
        for (int p = 0; p < unifier.Arguments.Length; p++)
            if (!Valid(unifier.Arguments[p], p))
                return Why($"argument {p} is not worth the same before");
        if (MakeCall(template, unifier) is not { } call) return Why("no call could be written");

        // The first block: what was before, the call, and how it goes on.
        HBlock target = next.Block;
        bool inside = ways == null && !handedOn && next.Index != 0;
        if (inside && ReferenceEquals(target, first) && next.Index <= start) return Why("the place goes on before the call");
        if (match.Kept.Count != 0 && ReferenceEquals(target, first)) return Why("statements of the place kept among its first ones");
        List<HStmt> old = [.. first.Statements];
        ulong address = old[start].Address;
        var rebuilt = new List<HStmt>();
        for (int k = 0; k < start; k++)
            if (!match.Used.Contains((first, k)))
                rebuilt.Add(old[k]);
        // What the place worked out early for itself, among the method's statements: it stays, before the call.
        foreach ((HBlock keptIn, int keptAt) in match.Kept)
            if (ReferenceEquals(keptIn, first) && keptAt >= start && keptAt < old.Count && !match.Used.Contains((first, keptAt)))
                rebuilt.Add(old[keptAt]);
        // Where the place goes on from the call.
        int continuation = rebuilt.Count;
        HStmt? user2 = null;
        if (replaced != null)
        {
            user2 = next.Block.Statements[next.Index];
            EnumeratorLoops.Rewrite(user2, e => ReferenceEquals(e, replaced) ? call : null);
        }
        else if (handedOn) rebuilt.Add(new HReturn(call) { Address = address });
        else if (ways == null) rebuilt.Add(into != null ? new HAssign(new HLocal(into) { Type = into.Type }, call) { Address = address } : new HEval(call) { Address = address });
        if (handedOn) { }
        else if (ways is { } answer) rebuilt.Add(new HBranch(call, answer.True, answer.False) { Address = address });
        else if (!inside) rebuilt.Add(new HJump(target) { Address = address });
        else
        {
            List<HStmt> rest = ReferenceEquals(target, first) ? old : target.Statements;
            for (int k = next.Index; k < rest.Count; k++)
                if (!match.Used.Contains((target, k)))
                    rebuilt.Add(rest[k]);
        }
        first.Statements.Clear();
        first.Statements.AddRange(rebuilt);

        // What can still be reached must not use what was the method's own; a block whose rest was taken over
        // must be gone.
        bool holds = true;
        HashSet<HBlock> reached = Reachable(method);
        if (inside && !ReferenceEquals(target, first) && reached.Contains(target)) holds = false;
        // A statement changed where it stands (the call written into it) must be reached from here only.
        if (holds && user2 != null && !inside)
            foreach (HBlock b in reached)
            {
                if (ReferenceEquals(b, first) || b.Statements.Count == 0) continue;
                bool leads = b.Statements[^1] switch
                {
                    HJump j => ReferenceEquals(j.Target, target),
                    HBranch br => ReferenceEquals(br.WhenTrue, target) || ReferenceEquals(br.WhenFalse, target),
                    HSwitch sw => ReferenceEquals(sw.Default, target) || sw.Targets.Any(x => ReferenceEquals(x, target)),
                    _ => false,
                };
                if (leads) holds = false;
            }
        if (holds)
        {
            var own = new List<HVar>();
            foreach (HVar local in unifier.SiteLocals)
                if (!ReferenceEquals(local, into))
                    own.Add(local);
            own.AddRange(temporaries);
            // Nothing that can still be reached may use them - or, for a stack slot the place uses for one thing
            // after another (the same temporary for the item of each "list.Add(..)" pasted in, one after the
            // other), nothing from the call on may look at what the method left in it; what the place puts in it
            // anew afterwards is its own.
            foreach (HVar local in own)
            {
                bool named = false;
                foreach (HBlock b in reached)
                {
                    foreach (HStmt s in b.Statements)
                        if (ConstructorFolding.Mentions(s, local))
                        {
                            named = true;
                            break;
                        }
                    if (named) break;
                }
                if (named && (NoSlotsOn || !Renewed(method, first, continuation, local)))
                {
                    holds = false;
                    break;
                }
            }
        }
        if (!holds)
        {
            if (user2 != null) EnumeratorLoops.Rewrite(user2, e => ReferenceEquals(e, call) ? replaced : null);
            first.Statements.Clear();
            first.Statements.AddRange(old);
            return Why("what was its own is used further on, or a part of it can still be reached");
        }
        HirCleanup.Run(method);
        return true;
    }
}
