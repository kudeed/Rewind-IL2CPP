using System.Reflection;
using System.Security.Cryptography;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

var assembly = typeof(ProgramAnalysis).Assembly;
string sha = Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(assembly.Location)));
if (args.Length != 1 || args[0] != sha) throw new Exception("Analysis SHA mismatch: " + sha);
var run = assembly.GetType("Rewind.Analysis.Recover.ReadonlyPropertyAddressPhis", true)!
    .GetMethods(BindingFlags.Static | BindingFlags.NonPublic)
    .Single(m => m.Name == "Run" && m.GetParameters()[1].ParameterType == typeof(Func<FieldDef, MethodDef?>));
int positive = 0, negative = 0;
void Check(string name, Fixture f, int expected = 0, bool getter = true)
{
    string before = HirPrinter.Print(f.H);
    var statements = f.H.Blocks.SelectMany(b => b.Statements).ToArray();
    string? result = expected > 0 ? f.ExecuteCases() : null;
    Func<FieldDef, MethodDef?> accessors = field => getter && field == f.Position ? f.Getter : null;
    int Apply() => (int)run.Invoke(null, [f.H, accessors, new Func<TypeSig, TypeLayout>(_ => f.Layout)])!;
    int count = Apply();
    if (count != expected) throw new Exception(name + ": got " + count + ", expected " + expected);
    if (expected > 0)
    {
        if (f.ExecuteCases() != result) throw new Exception(name + ": scalar values/control flow/state changed");
        if (!statements.SequenceEqual(f.H.Blocks.SelectMany(b => b.Statements)))
            throw new Exception(name + ": statement/branch order changed");
        if (f.Phi.Type.Key != f.Scalar.Key || f.DefA.Target.Type?.Key != f.Scalar.Key ||
            f.DefB.Target.Type?.Key != f.Scalar.Key || f.Read.Value is not HLocal)
            throw new Exception(name + ": phi/read types not restored");
        if (Apply() != 0) throw new Exception(name + ": not idempotent");
        positive++;
    }
    else
    {
        if (before != HirPrinter.Print(f.H) || !statements.SequenceEqual(f.H.Blocks.SelectMany(b => b.Statements)))
            throw new Exception(name + ": rejected input modified");
        negative++;
    }
}
Check("float phi and first-field projection", new Fixture(), 1);
Check("double phi and exact eight-byte field", new Fixture(true), 1);
var direct = new Fixture(); ((HAddressOf)direct.DefB.Value).Target = direct.Component(direct.Start, direct.Y);
((HAddressOf)direct.DefB.Value).Type = direct.Sigs.ByRef(direct.Scalar); Check("both definitions explicit components", direct, 1);
var scalarView = new Fixture(); scalarView.DefB.Value.Type = scalarView.Sigs.ByRef(scalarView.Scalar);
Check("native scalar view of whole value address", scalarView, 1);
var nullOwners = new Fixture(); nullOwners.ClearDeclaringTypes(); Check("implicit exact declaring types", nullOwners, 1);
var tail = new Fixture(); tail.Skip.Statements.Insert(0, new HAssign(tail.Field(tail.Counter), new HConst(77, tail.Int)));
Check("mutation on path that never reads phi", tail, 1);
var diamond = new Fixture(); var bridge = new HBlock { Id = 6, Statements = [new HJump(diamond.Join)] };
diamond.H.Blocks.Add(bridge); diamond.Left.Statements[^1] = new HBranch(new HConst(true, diamond.Bool), diamond.Join, bridge);
Check("pure diamond after one definition", diamond, 1);

Check("unproven native getter", new Fixture(), getter: false);
var noProperty = new Fixture(); ((HAddressOf)noProperty.DefA.Value).Target = noProperty.Component(noProperty.Start, noProperty.Y);
Check("no inaccessible property in phi", noProperty);
var privateGetter = new Fixture(); privateGetter.Getter.Flags = 1; Check("private getter", privateGetter);
var virtualGetter = new Fixture(); virtualGetter.Getter.Flags |= 0x40; Check("virtual getter", virtualGetter);
var getterArgs = new Fixture(); getterArgs.Getter.Parameters = [new ParamDef { Type = getterArgs.Int }]; Check("getter with arguments", getterArgs);
var wrongGetterOwner = new Fixture(); wrongGetterOwner.Getter.DeclaringType = wrongGetterOwner.Caller; Check("wrong getter owner", wrongGetterOwner);
var wrongReturn = new Fixture(); wrongReturn.Getter.ReturnType = wrongReturn.Scalar; Check("wrong getter return type", wrongReturn);
var notBacking = new Fixture(); notBacking.Position.Name = "privatePosition"; Check("non-property inaccessible field", notBacking);
var wrongOwner = new Fixture(); ((HField)((HAddressOf)wrongOwner.DefA.Value).Target).DeclaringType = wrongOwner.Caller.Sig; Check("wrong explicit declaring type", wrongOwner);
var missingField = new Fixture(); missingField.Event.Fields = []; Check("unregistered owner field", missingField);
var unknownLayout = new Fixture(); unknownLayout.Layout.Known = false; Check("unknown layout", unknownLayout);
var overlap = new Fixture(); overlap.Layout.Fields[1] = new FieldSlot(overlap.Y, overlap.Scalar, 0, 4); Check("overlapping fields", overlap);
var explicitLayout = new Fixture(); explicitLayout.Vector.Flags = TypeDef.ExplicitLayout; Check("explicit struct layout", explicitLayout);
var size = new Fixture(); size.Layout.Fields[0] = new FieldSlot(size.X, size.Scalar, 0, 2); Check("wrong leading field size", size);
var offset = new Fixture(); offset.Layout.Size = 12; offset.Layout.Fields = [new(offset.X, offset.Scalar, 4, 4), new(offset.Y, offset.Scalar, 8, 4)]; Check("no field at byte zero", offset);
var hugeOffset = new Fixture(); hugeOffset.Layout.Fields[0] = new FieldSlot(hugeOffset.X, hugeOffset.Scalar, int.MaxValue, 4); Check("overflowing recorded offset", hugeOffset);
var hugeSize = new Fixture(); hugeSize.Layout.Fields[0] = new FieldSlot(hugeSize.X, hugeSize.Scalar, 4, int.MaxValue); Check("overflowing recorded size", hugeSize);
var privateFirst = new Fixture(); privateFirst.X.Attrs = 1; Check("inaccessible leading scalar", privateFirst);
var refHop = new Fixture(); refHop.Vector.IsValueType = false; Check("reference indirection inside field chain", refHop);
var typeMismatch = new Fixture(); ((HAddressOf)typeMismatch.DefA.Value).Target.Type = typeMismatch.Int; Check("field type mismatch", typeMismatch);
var localRoot = new Fixture(); var inner = (HField)((HField)((HAddressOf)localRoot.DefA.Value).Target).Object!;
inner.Object = localRoot.Local(localRoot.H.NewLocal(localRoot.Event.Sig)); Check("local receiver alias", localRoot);
var byrefRoot = new Fixture(); byrefRoot.H.Method.Parameters[0].Type = byrefRoot.Sigs.ByRef(byrefRoot.Event.Sig); Check("byref root parameter", byrefRoot);
var readType = new Fixture(); readType.Read.Value.Type = readType.Int; Check("wrong dereference width/type", readType);
var readTwice = new Fixture(); readTwice.Use.Statements.Insert(2, new HAssign(readTwice.Local(readTwice.Result), new HDeref(readTwice.Local(readTwice.Phi)) { Type = readTwice.Scalar })); Check("multiple pointer reads", readTwice);
var escaped = new Fixture(); escaped.Join.Statements.Insert(0, new HEval(escaped.Call(escaped.Local(escaped.Phi)))); Check("pointer escapes to call", escaped);
var write = new Fixture(); write.Join.Statements.Insert(0, new HAssign(new HDeref(write.Local(write.Phi)) { Type = write.Scalar }, write.Number(9))); Check("pointer store", write);
var argStore = new Fixture(); argStore.Join.Statements.Insert(0, new HAssign(new HArg(0) { Type = argStore.Event.Sig }, new HConst(null, argStore.Event.Sig))); Check("argument receiver overwritten", argStore);
var fieldStore = new Fixture(); fieldStore.Join.Statements.Insert(0, new HAssign(fieldStore.Field(fieldStore.Counter), new HConst(3, fieldStore.Int))); Check("intervening field store", fieldStore);
var call = new Fixture(); call.Join.Statements.Insert(0, new HEval(call.Call())); Check("intervening call", call);
var unknown = new Fixture(); unknown.Join.Statements.Insert(0, new HAssign(unknown.Local(unknown.ReadCounter), new HOpaque("unknown") { Type = unknown.Int })); Check("unknown intervening operation", unknown);
var addrTemp = new Fixture(); addrTemp.ReadCounter.AddressTaken = true; Check("write to aliased local", addrTemp);
var addrPhi = new Fixture(); addrPhi.Phi.AddressTaken = true; Check("address-taken phi", addrPhi);
var problem = new Fixture(); problem.H.Problems.Add("unresolved native operation"); Check("existing problem", problem);
var scope = new Fixture(); scope.Left.Scope = 0; Check("exception region", scope);
var undefined = new Fixture(); ((HBranch)undefined.Entry.Statements[^1]).WhenFalse = undefined.Join; Check("undefined incoming path", undefined);
var repeated = new Fixture(); repeated.Left.Statements.Insert(1, new HAssign(repeated.Local(repeated.Phi), new HAddressOf(repeated.Component(repeated.Start, repeated.Y)) { Type = repeated.Sigs.ByRef(repeated.Scalar) })); Check("two definitions on one path", repeated);
var loop = new Fixture(); loop.Join.Statements[^1] = new HBranch(loop.Field(loop.Gate), loop.Use, loop.Left); Check("loop can repeat definition", loop);
var later = new Fixture(); later.Use.Statements.Insert(2, new HAssign(later.Local(later.Phi), new HAddressOf(later.Component(later.Start, later.Y)) { Type = later.Sigs.ByRef(later.Scalar) })); Check("definition after the read", later);
var fewer = new Fixture(); fewer.Right.Statements.RemoveAt(0); Check("only one address definition", fewer);
var external = new Fixture(); external.Left.Statements[^1] = new HJump(new HBlock { Id = 99 }); Check("edge outside method", external);
var staticCaller = new Fixture(); staticCaller.H.Method.Flags |= MethodDef.Static; Check("this address in static method", staticCaller);
var valueCaller = new Fixture(); valueCaller.Caller.IsValueType = true; Check("value receiver root", valueCaller);
var generic = new Fixture(); generic.Event.GenericParameters = [new GenericParam { Name = "T" }]; Check("generic receiver layout", generic);
Console.WriteLine($"READONLY_PROPERTY_PHI_SMOKE_PASS positive={positive} negative={negative} both_directions=true use_and_skip_paths=true float_double_and_negative_zero=true original_statement_order=true idempotent=true analysis_sha256={sha}");

sealed class Fixture
{
    public readonly SigFactory Sigs = new();
    public readonly TypeSig Scalar, Int, Bool, Void;
    public readonly TypeDef Caller, Event, Vector;
    public readonly FieldDef Position, Start, X, Y, Mode, Gate, Counter;
    public readonly MethodDef Getter;
    public readonly HMethod H;
    public readonly HBlock Entry = new() { Id = 0 }, Left = new() { Id = 1 }, Right = new() { Id = 2 },
        Join = new() { Id = 3 }, Use = new() { Id = 4 }, Skip = new() { Id = 5 };
    public readonly HVar Phi, ReadCounter, Result;
    public readonly HAssign DefA, DefB, Read;
    public readonly TypeLayout Layout;
    private readonly bool Wide;
    public Fixture(bool wide = false)
    {
        Wide = wide; Scalar = Sigs.Primitive(wide ? Il2CppTypeEnum.R8 : Il2CppTypeEnum.R4);
        Int = Sigs.Primitive(Il2CppTypeEnum.I4); Bool = Sigs.Primitive(Il2CppTypeEnum.Boolean); Void = Sigs.Primitive(Il2CppTypeEnum.Void);
        var assembly = new AssemblyModel { Name = "Fixture" };
        Caller = new TypeDef { Index = 1, Name = "Caller", Assembly = assembly }; Caller.Sig = Sigs.TypeDef(Caller);
        Event = new TypeDef { Index = 2, Name = "Event", Assembly = assembly }; Event.Sig = Sigs.TypeDef(Event);
        Vector = new TypeDef { Index = 3, Name = "Vector", IsValueType = true, Assembly = assembly }; Vector.Sig = Sigs.TypeDef(Vector);
        X = new FieldDef { Name = "x", DeclaringType = Vector, Type = Scalar, Attrs = 6 };
        Y = new FieldDef { Name = "y", DeclaringType = Vector, Type = Scalar, Attrs = 6 }; Vector.Fields = [X, Y];
        Position = new FieldDef { Name = "<position>k__BackingField", DeclaringType = Event, Type = Vector.Sig, Attrs = 1 }; Event.Fields = [Position];
        Start = new FieldDef { Name = "start", DeclaringType = Caller, Type = Vector.Sig, Attrs = 1 };
        Mode = new FieldDef { Name = "direction", DeclaringType = Caller, Type = Bool, Attrs = 1 };
        Gate = new FieldDef { Name = "useFastSwipe", DeclaringType = Caller, Type = Bool, Attrs = 1 };
        Counter = new FieldDef { Name = "counter", DeclaringType = Caller, Type = Int, Attrs = 1 }; Caller.Fields = [Start, Mode, Gate, Counter];
        Getter = new MethodDef { Name = "get_position", DeclaringType = Event, ReturnType = Vector.Sig, Flags = 6 };
        H = new HMethod { Method = new MethodDef { Name = "Run", DeclaringType = Caller, ReturnType = Scalar,
            Parameters = [new ParamDef { Name = "eventData", Type = Event.Sig }] } };
        H.Blocks.AddRange([Entry, Left, Right, Join, Use, Skip]);
        Phi = H.NewLocal(Sigs.ByRef(Scalar)); ReadCounter = H.NewLocal(Int); Result = H.NewLocal(Scalar);
        DefA = new HAssign(Local(Phi), new HAddressOf(Component(Position, Y)) { Type = Sigs.ByRef(Scalar) });
        DefB = new HAssign(Local(Phi), new HAddressOf(Field(Start)) { Type = Sigs.ByRef(Vector.Sig) });
        Read = new HAssign(Local(Result), new HDeref(Local(Phi)) { Type = Scalar });
        Entry.Statements.Add(new HBranch(Field(Mode), Left, Right));
        Left.Statements.AddRange([DefA, new HJump(Join)]); Right.Statements.AddRange([DefB, new HJump(Join)]);
        Join.Statements.Add(new HBranch(Field(Gate), Use, Skip));
        Use.Statements.AddRange([new HAssign(Local(ReadCounter), Field(Counter)), Read, new HReturn(Local(Result))]);
        Skip.Statements.Add(new HReturn(Number(-999)));
        int n = wide ? 8 : 4;
        Layout = new TypeLayout { Known = true, Size = 2 * n, Align = n, Fields = [new(X, Scalar, 0, n), new(Y, Scalar, n, n)] };
    }
    public HLocal Local(HVar v) => new(v) { Type = v.Type };
    public HField Field(FieldDef f) => new() { Object = new HArg(f.DeclaringType == Event ? 0 : -1) { Type = f.DeclaringType.Sig }, Field = f, DeclaringType = f.DeclaringType.Sig, Type = f.Type };
    public HField Component(FieldDef vector, FieldDef part) => new() { Object = Field(vector), Field = part, DeclaringType = Vector.Sig, Type = Scalar };
    public HConst Number(double value) => new(Wide ? (object)value : (float)value, Scalar);
    public HCall Call(params HExpr[] arguments) => new() { Method = new MethodDef { Name = "Unknown", DeclaringType = Caller, ReturnType = Void, Flags = MethodDef.Static | 6 }, Arguments = arguments, Type = Void };
    public void ClearDeclaringTypes()
    {
        void Clear(HExpr expression)
        {
            if (expression is HAddressOf a) Clear(a.Target);
            if (expression is HField f) { f.DeclaringType = null; if (f.Object != null) Clear(f.Object); }
        }
        Clear(DefA.Value); Clear(DefB.Value);
    }
    public string ExecuteCases()
    {
        var outputs = new List<string>();
        foreach (bool direction in new[] { false, true }) foreach (bool enabled in new[] { false, true })
        foreach (double component in new[] { -0.0, -17.5, 13.25, double.PositiveInfinity })
        {
            object N(double x) => Wide ? (object)x : (float)x;
            var start = new Dictionary<FieldDef, object> { [X] = N(component), [Y] = N(-8.5) };
            var position = new Dictionary<FieldDef, object> { [X] = N(21.5), [Y] = N(component) };
            var caller = new Dictionary<FieldDef, object> { [Start] = start, [Mode] = direction, [Gate] = enabled, [Counter] = 12 };
            var data = new Dictionary<FieldDef, object> { [Position] = position };
            var locals = new Dictionary<HVar, object>();
            object Value(HExpr e) => e switch
            {
                HArg a => a.Index == -1 ? caller : data,
                HConst c => c.Value!, HLocal l => locals[l.Variable],
                HField f => ((Dictionary<FieldDef, object>)Value(f.Object!))[f.Field],
                HAddressOf a => Address(a.Target),
                HDeref d => ((Func<object>)Value(d.Pointer))(),
                _ => throw new Exception("Unexpected interpreter expression " + e.GetType().Name)
            };
            Func<object> Address(HExpr target)
            {
                // A managed field address captures its receiver now, including its null check.
                if (target.Type == Vector.Sig)
                {
                    var owner = (Dictionary<FieldDef, object>)Value(target);
                    return () => owner[X];
                }
                if (target is HField field)
                {
                    var owner = (Dictionary<FieldDef, object>)Value(field.Object!);
                    _ = owner[field.Field];
                    return () => owner[field.Field];
                }
                throw new Exception("Unsupported address target");
            }
            HBlock block = Entry; object? result = null;
            for (int steps = 0; steps < 32 && result == null; steps++)
            {
                HBlock? next = null;
                foreach (HStmt statement in block.Statements)
                    switch (statement)
                    {
                        case HAssign { Target: HLocal l, Value: var v }: locals[l.Variable] = Value(v); break;
                        case HAssign { Target: HField f, Value: var v }: ((Dictionary<FieldDef, object>)Value(f.Object!))[f.Field] = Value(v); break;
                        case HJump j: next = j.Target; break;
                        case HBranch b: next = (bool)Value(b.Condition) ? b.WhenTrue : b.WhenFalse; break;
                        case HReturn r: result = Value(r.Value!); break;
                        default: throw new Exception("Unexpected interpreter statement " + statement.GetType().Name);
                    }
                if (result == null) block = next ?? throw new Exception("Missing successor");
            }
            string Bits(object? v) => v is float f ? BitConverter.SingleToInt32Bits(f).ToString() : v is double d ? BitConverter.DoubleToInt64Bits(d).ToString() : throw new Exception("Missing numeric result");
            outputs.Add(Bits(result) + ":" + caller[Counter]);
        }
        return string.Join("|", outputs);
    }
}
