using System.Collections;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text.Json;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;

internal static partial class Program
{
    private const BindingFlags All = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static | BindingFlags.Instance;
    private static readonly Type Inline = typeof(HirBuilder).Assembly.GetType("Rewind.Analysis.Recover.InlineFolding", true)!;
    private static readonly Type Counts = Inline.GetNestedType("Counts", BindingFlags.NonPublic)!;
    private static readonly SigFactory Sigs = new();
    private static readonly TypeSig Int = Sigs.Primitive(Il2CppTypeEnum.I4), Object = Sigs.Primitive(Il2CppTypeEnum.Object);
    private static int index, assertions;
    private static readonly List<string> Cases = [];
    private static void Check(bool good, string name)
    {
        assertions++;
        if (!good) throw new InvalidOperationException(name);
    }
    private static bool SameValue(object? a, object? b) => a is Dictionary<FieldDef, object?> x && b is Dictionary<FieldDef, object?> y
        ? x.Count == y.Count && x.All(p => y.TryGetValue(p.Key, out var v) && SameValue(p.Value, v)) : Equals(a, b);
    private static TypeDef Define(string name, bool value, params (string Name, TypeSig Type)[] fields)
    {
        var type = new TypeDef { Index = ++index, Name = name, IsValueType = value, Assembly = new AssemblyModel { Name = "TemplateFixture" } };
        type.Sig = Sigs.TypeDef(type);
        type.Fields = fields.Select(f => new FieldDef { Name = f.Name, DeclaringType = type, Type = f.Type, Attrs = FieldDef.InitOnly | 1 }).ToArray();
        return type;
    }
    private static HLocal Local(HVar variable) => new(variable) { Type = variable.Type };
    private static HField Field(HExpr owner, FieldDef field, TypeSig type) => new() { Object = owner, Field = field, DeclaringType = owner.Type, Type = type };
    private static HTypeExpr Zero(TypeSig type) => new(HTypeOp.Default, type, null) { Type = type };
    private static void Backing(object obj, string property, object value) => obj.GetType().GetField("<" + property + ">k__BackingField", All)!.SetValue(obj, value);

    private static LayoutCalculator Layouts(TypeSig root)
    {
        var layouts = (LayoutCalculator)RuntimeHelpers.GetUninitializedObject(typeof(LayoutCalculator));
        var cache = new Dictionary<TypeSig, TypeLayout>();
        typeof(LayoutCalculator).GetField("_cache", All)!.SetValue(layouts, cache);
        typeof(LayoutCalculator).GetField("_ptr", All)!.SetValue(layouts, 8);
        typeof(LayoutCalculator).GetField("_header", All)!.SetValue(layouts, 16);
        TypeLayout Build(TypeSig type)
        {
            if (cache.TryGetValue(type, out var found)) return found;
            var layout = new TypeLayout(); cache[type] = layout;
            int size = 0; var slots = new List<FieldSlot>();
            foreach (var field in type.Definition!.Fields.Where(f => !f.IsStatic))
            {
                var exact = Sigs.Substitute(field.Type, type is GenericInstSig g ? g.Arguments : [], []);
                int width = exact is PrimitiveSig primitive ? primitive.SizeOf(8) : exact.IsValueType ? Build(exact).Size : 8;
                size = (size + 7) / 8 * 8;
                slots.Add(new FieldSlot(field, exact, size, width)); size += width;
            }
            layout.Fields = [.. slots]; layout.Size = (size + 7) / 8 * 8; layout.DataSize = size; layout.Align = 8;
            return layout;
        }
        Build(root); return layouts;
    }

    private sealed record Fixture(HMethod Body, HLocal Result, MethodDef Method, TypeSig Receiver, TypeSig ReturnType, FieldDef Field,
        LayoutCalculator Layouts, object Folder, TypeSig[] Arguments);

    private static Fixture Fresh(TypeSig payload, bool extra = false)
    {
        var task = Define("Task`1", true);
        var parameter = new GenericParam { Index = ++index, Name = "T", OwnerType = task, Position = 0 };
        task.GenericParameters = [parameter];
        task.Fields = [new FieldDef { Name = "source", DeclaringType = task, Type = Object },
            new FieldDef { Name = "result", DeclaringType = task, Type = Sigs.GenericParam(parameter) },
            new FieldDef { Name = "token", DeclaringType = task, Type = Int }];
        var wrapper = Define("Wrapper`1", true);
        var wrapped = new GenericParam { Index = ++index, Name = "T", OwnerType = wrapper, Position = 0 };
        wrapper.GenericParameters = [wrapped];
        var field = new FieldDef { Name = "task", DeclaringType = wrapper,
            Type = Sigs.GenericInst(task, [Sigs.GenericParam(wrapped)]), Attrs = FieldDef.InitOnly | 1 };
        wrapper.Fields = extra ? [field, new FieldDef { Name = "other", DeclaringType = wrapper, Type = Int }] : [field];
        TypeSig receiver = Sigs.GenericInst(task, [payload]), result = Sigs.GenericInst(wrapper, [payload]);
        var method = new MethodDef { Name = "Wrap", DeclaringType = task, Flags = 6,
            ReturnType = Sigs.GenericInst(wrapper, [Sigs.GenericParam(parameter)]) };
        var h = new HMethod { Method = method };
        var block = new HBlock(); h.Blocks.Add(block);
        var local = Local(h.NewLocal(result));
        block.Statements.Add(new HAssign(local, Zero(result)));
        block.Statements.Add(new HAssign(Field(local, field, receiver), new HArg(-1) { Type = receiver }));
        block.Statements.Add(new HReturn(local));
        var layouts = Layouts(result);
        var model = (Il2CppModel)RuntimeHelpers.GetUninitializedObject(typeof(Il2CppModel)); Backing(model, "Sigs", Sigs);
        var program = (ProgramAnalysis)RuntimeHelpers.GetUninitializedObject(typeof(ProgramAnalysis));
        Backing(program, "Model", model); Backing(program, "Layouts", layouts);
        var folder = Activator.CreateInstance(Inline, All, null, [null, program], null)!;
        return new Fixture(h, local, method, receiver, result, field, layouts, folder, [payload]);
    }

    private static object Template(Fixture f)
    {
        object template = Inline.GetMethod("Make", All)!.Invoke(f.Folder, [f.Method, f.Body])
            ?? throw new InvalidOperationException("fixture has no template");
        Check(true, "fixture has a template");
        template.GetType().GetField("ClassArguments", All)!.SetValue(template, f.Arguments);
        template.GetType().GetField("SiteArguments", All)!.SetValue(template, f.Arguments);
        template.GetType().GetField("Declaring", All)!.SetValue(template, f.Receiver);
        return template;
    }
    private static List<HStmt> Statements(object template) => (List<HStmt>)template.GetType().GetField("Statements", All)!.GetValue(template)!;
    private static (HMethod Method, HBlock Block, HLocal Result) Caller(Fixture f, bool working = false)
    {
        var h = new HMethod { Method = new MethodDef { Name = "Caller", DeclaringType = Define("Game", false), ReturnType = f.ReturnType } };
        var b = new HBlock(); h.Blocks.Add(b); var result = Local(h.NewLocal(f.ReturnType));
        HExpr receiver = working ? new HCall { Method = new MethodDef { Name = "Factory", DeclaringType = h.Method.DeclaringType, Flags = MethodDef.Static | 6, ReturnType = f.Receiver }, Type = f.Receiver } : new HArg(0) { Type = f.Receiver };
        b.Statements.Add(new HAssign(Field(result, f.Field, f.Receiver), receiver));
        b.Statements.Add(new HReturn(result)); return (h, b, result);
    }
    private static bool Fold(Fixture f, object template, HMethod caller, HBlock block)
    {
        object counts = Counts.GetMethod("Of", All)!.Invoke(null, [caller])!;
        return (bool)Inline.GetMethod("TryFold", All)!.Invoke(f.Folder, [caller, block, 0, template, f.Field, counts])!;
    }

    private static void Positive(TypeSig payload, object value)
    {
        var f = Fresh(payload); var template = Template(f);
        Check(Statements(template).Count == 1, "complete closed generic template drops redundant default");
        Check(f.Body.Blocks[0].Statements[0] is HAssign { Value: HTypeExpr { Op: HTypeOp.Default } }, "shared recovered body is unchanged");
        foreach (bool working in new[] { false, true })
        {
            var caller = Caller(f, working); object source = new();
            var task = new Dictionary<FieldDef, object?> { [f.Receiver.Definition!.Fields[0]] = source,
                [f.Receiver.Definition.Fields[1]] = value, [f.Receiver.Definition.Fields[2]] = 3817 };
            var before = new Machine(f, caller.Method, task); var beforeResult = before.Run();
            Check(Fold(f, template, caller.Method, caller.Block), "public wrapper is recovered at its field-copy call site");
            Check(caller.Block.Statements[0] is HAssign { Value: HCall { Method: var called, Type: var type } } &&
                ReferenceEquals(called, f.Method) && type!.Key == f.ReturnType.Key, "call has exact substituted generic return type");
            var after = new Machine(f, caller.Method, task); var afterResult = after.Run();
            var copied = (Dictionary<FieldDef, object?>)afterResult[f.Field]!;
            Check(SameValue(beforeResult, afterResult) && ReferenceEquals(copied[f.Receiver.Definition.Fields[0]], source) && SameValue(copied[f.Receiver.Definition.Fields[1]], value) &&
                Equals(copied[f.Receiver.Definition.Fields[2]], 3817), "reference identity, result and token survive the public wrapper");
            Check(before.FactoryCalls == after.FactoryCalls && after.FactoryCalls == (working ? 1 : 0), "receiver is evaluated exactly once");
            if (working)
            {
                var throwing = new Machine(f, caller.Method, task) { ThrowFactory = true };
                try { throwing.Run(); Check(false, "throwing receiver must propagate"); }
                catch (ArithmeticException) { Check(throwing.FactoryCalls == 1, "receiver exception is preserved without reevaluation"); }
            }
        }
        Cases.Add("closed wrapper of " + payload.DisplayName);
    }

    private static void Negatives()
    {
        void Reject(string name, Action<Fixture> change, bool extra = false)
        {
            var f = Fresh(Int, extra); change(f); var template = Template(f);
            Check(Statements(template).First() is HAssign { Value: HTypeExpr { Op: HTypeOp.Default } }, name);
            Cases.Add(name);
        }
        Reject("partial instance-field coverage", _ => { }, true);
        Reject("unknown layout", f => f.Layouts.Of(f.ReturnType).Known = false);
        Reject("explicit overlapping layout", f => {
            f.ReturnType.Definition!.Flags |= TypeDef.ExplicitLayout;
            var other = f.ReturnType.Definition.Fields[1];
            f.Body.Blocks[0].Statements.Insert(2, new HAssign(Field(f.Result, other, Int), new HConst(9, Int)));
            f.Layouts.Of(f.ReturnType).Fields[1] = f.Layouts.Of(f.ReturnType).Fields[1] with { Offset = 0 };
        }, true);
        Reject("duplicate field stores", f => f.Body.Blocks[0].Statements.Insert(2, f.Body.Blocks[0].Statements[1]));
        Reject("wrong constructed declaring type", f => ((HField)((HAssign)f.Body.Blocks[0].Statements[1]).Target).DeclaringType = Sigs.GenericInst(f.ReturnType.Definition!, [Object]));
        Reject("inconsistent substituted layout field", f => f.Layouts.Of(f.ReturnType).Fields[0] = f.Layouts.Of(f.ReturnType).Fields[0] with { Type = Object });
        Reject("wrong RHS field type", f => ((HAssign)f.Body.Blocks[0].Statements[1]).Value = new HArg(-1) { Type = Object });
        Reject("wrong field expression type", f => ((HAssign)f.Body.Blocks[0].Statements[1]).Target.Type = Object);
        Reject("getter call can observe or throw", f => ((HAssign)f.Body.Blocks[0].Statements[1]).Value = new HCall {
            Method = new MethodDef { Name = "get_Task", DeclaringType = f.Receiver.Definition!, ReturnType = f.Receiver }, Type = f.Receiver });
        Reject("self read makes initialization visible", f => ((HAssign)f.Body.Blocks[0].Statements[1]).Value = Field(f.Result, f.Field, f.Receiver));
        Reject("call through the return buffer can observe default", f => f.Body.Blocks[0].Statements.Insert(1,
            new HEval(new HCall { Method = new MethodDef { Name = "Observe", DeclaringType = f.ReturnType.Definition! }, This = new HAddressOf(f.Result) { Type = Sigs.ByRef(f.ReturnType) } })));
        Reject("store to another local does not cover returned value", f => ((HField)((HAssign)f.Body.Blocks[0].Statements[1]).Target).Object = Local(f.Body.NewLocal(f.ReturnType)));
    }

    private sealed class Machine(Fixture f, HMethod caller, Dictionary<FieldDef, object?> input)
    {
        private readonly Dictionary<HVar, object?> locals = [];
        public int FactoryCalls;
        public bool ThrowFactory;
        private static object? Clone(object? value) => value is Dictionary<FieldDef, object?> fields ? fields.ToDictionary(p => p.Key, p => Clone(p.Value)) : value;
        private object? Get(HExpr e) => e switch {
            HArg => Clone(input), HLocal l => locals[l.Variable], HConst c => c.Value,
            HCall c when ReferenceEquals(c.Method, f.Method) => new Dictionary<FieldDef, object?> { [f.Field] = Clone(Get(c.This!)) },
            HCall => Factory(),
            _ => throw new NotSupportedException(e.GetType().Name)
        };
        private object? Factory()
        {
            FactoryCalls++;
            if (ThrowFactory) throw new ArithmeticException("original receiver failed");
            return Clone(input);
        }
        public Dictionary<FieldDef, object?> Run()
        {
            foreach (var s in caller.Blocks[0].Statements)
                switch (s)
                {
                    case HAssign { Target: HLocal l, Value: var value }: locals[l.Variable] = Clone(Get(value)); break;
                    case HAssign { Target: HField { Object: HLocal l } field, Value: var value }:
                        if (!locals.ContainsKey(l.Variable)) locals[l.Variable] = new Dictionary<FieldDef, object?>();
                        ((Dictionary<FieldDef, object?>)locals[l.Variable]!)[field.Field] = Clone(Get(value)); break;
                    case HReturn ret: return (Dictionary<FieldDef, object?>)Get(ret.Value!)!;
                }
            throw new InvalidOperationException("no return");
        }
    }

    private static void Main()
    {
        Positive(Int, 529);
        Positive(Object, new object());
        var payload = Define("ValuePayload", true, ("id", Int));
        Positive(payload.Sig, new Dictionary<FieldDef, object?> { [payload.Fields[0]] = 718 });
        Negatives();
        NestedCandidateDiscovery();
        ReturnBufferReceiverOrder();
        IgnoredResults();
        Arm64Results();
        StackResultLifetimes();
        WholeStructStores();
        ClosureReceivers();
        Console.WriteLine(JsonSerializer.Serialize(new { passed = true, assertions, cases = Cases,
            scope = "complete async recovery chain: exact wrapper templates, discarded effects, ARM64 pair returns, proven stack lifetimes typed wide stores and guarded closure receivers" }));
    }

    private static void NestedCandidateDiscovery()
    {
        var f = Fresh(Int);
        f.ReturnType.Definition!.DeclaringType = f.Receiver.Definition;
        object template = Template(f);
        var caller = Caller(f, working: true);
        Type element = template.GetType(), listType = typeof(List<>).MakeGenericType(element);
        var present = (IList)Activator.CreateInstance(listType)!; present.Add(template);
        object empty = Activator.CreateInstance(listType)!;
        var owner = System.Linq.Expressions.Expression.Parameter(typeof(TypeDef), "owner");
        var instance = System.Linq.Expressions.Expression.Parameter(typeof(TypeSig), "instance");
        Type providerType = typeof(Func<,,>).MakeGenericType(typeof(TypeDef), typeof(TypeSig), listType);
        var provider = System.Linq.Expressions.Expression.Lambda(providerType,
            System.Linq.Expressions.Expression.Condition(
                System.Linq.Expressions.Expression.Equal(owner, System.Linq.Expressions.Expression.Constant(f.Receiver.Definition)),
                System.Linq.Expressions.Expression.Constant(present, listType), System.Linq.Expressions.Expression.Constant(empty, listType)),
            owner, instance).Compile();
        var item = System.Linq.Expressions.Expression.Parameter(element, "template");
        var usable = System.Linq.Expressions.Expression.Lambda(typeof(Func<,>).MakeGenericType(element, typeof(bool)),
            System.Linq.Expressions.Expression.Constant(true), item).Compile();
        bool folded = (bool)Inline.GetMethod("Pass", All)!.Invoke(f.Folder,
            [caller.Method, (Func<object, bool>)(member => ReferenceEquals(member, f.Field)), provider, usable, false])!;
        Check(folded && caller.Block.Statements[0] is HAssign { Value: HCall { Method: var called } } && ReferenceEquals(called, f.Method),
            "normal member discovery finds an exact closed containing type's wrapper method");
        var enclosing = Inline.GetMethod("EnclosingType", All)!;
        Check(((TypeSig)enclosing.Invoke(f.Folder, [f.Receiver.Definition, f.ReturnType])!).Key == f.Receiver.Key,
            "outer generic arguments preserve the nested instance's exact payload");
        Check(enclosing.Invoke(f.Folder, [f.Receiver.Definition, f.ReturnType.Definition.Sig]) == null,
            "an open or missing nested instance never guesses outer type arguments");
        Cases.Add("nested generic wrapper candidate discovery through actual Pass");
    }

    private static void ReturnBufferReceiverOrder()
    {
        // ARM64's hidden result buffer is a local with AddressTaken, even when the recovered body only
        // writes its fields. A factory receiver still runs exactly once before that first write.
        var f = Fresh(Object);
        f.Result.Variable.AddressTaken = true;
        var template = Template(f);
        var caller = Caller(f, working: true);
        caller.Result.Variable.AddressTaken = true;
        object source = new(), payload = new();
        var task = new Dictionary<FieldDef, object?> {
            [f.Receiver.Definition!.Fields[0]] = source,
            [f.Receiver.Definition.Fields[1]] = payload,
            [f.Receiver.Definition.Fields[2]] = 4729 };
        var before = new Machine(f, caller.Method, task);
        object expected = before.Run();
        Check(Fold(f, template, caller.Method, caller.Block), "address-taken return storage does not falsely precede the factory receiver");
        var after = new Machine(f, caller.Method, task);
        Check(SameValue(expected, after.Run()) && before.FactoryCalls == 1 && after.FactoryCalls == 1,
            "return-buffer wrapper preserves payload identity and one factory evaluation");
        var throwing = new Machine(f, caller.Method, task) { ThrowFactory = true };
        try { throwing.Run(); Check(false, "return-buffer factory exception must propagate"); }
        catch (ArithmeticException) { Check(throwing.FactoryCalls == 1, "return-buffer factory exception is neither swallowed nor repeated"); }

        var order = Inline.GetMethod("WorkedOutFirst", All)!;
        HExpr value = new HArg(-1) { Type = f.Receiver };
        bool First(HExpr target) => (bool)order.Invoke(null, [new HAssign(target, value), value])!;
        var classOwner = Local(new HVar { Index = 900, Type = Define("ClassDestination", false).Sig, AddressTaken = true });
        Check(!First(Field(classOwner, f.Field, f.Receiver)), "address-taken class receiver is still read before RHS");
        var reference = new HArg(0) { Type = Sigs.ByRef(f.ReturnType) };
        Check(!First(Field(new HDeref(reference) { Type = f.ReturnType }, f.Field, f.Receiver)),
            "byref destination does not gain the fixed-local exception");
        Cases.Add("address-taken value return buffers and conservative destination evaluation order");
    }
}
