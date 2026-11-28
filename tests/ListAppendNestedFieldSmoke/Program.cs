
using Mono.Cecil;
using Mono.Cecil.Cil;
using Mono.Cecil.Rocks;
using System.Reflection;
using Assembly = System.Reflection.Assembly;
using TypeAttributes = Mono.Cecil.TypeAttributes;
using MethodAttributes = Mono.Cecil.MethodAttributes;
using FieldAttributes = Mono.Cecil.FieldAttributes;
using MethodBody = Mono.Cecil.Cil.MethodBody;

static void Check(bool value, string message) { if (!value) throw new Exception(message); }
var output = Assembly.Load("Rewind.Output");
var run = output.GetType("Rewind.Output.ListAppendIlFolding", true)!
    .GetMethod("Run", BindingFlags.NonPublic | BindingFlags.Static)!;
int Fold(MethodDefinition m) => (int)run.Invoke(null, new object[] { m.Body })!;
static string Shape(MethodDefinition m) =>
    string.Join("\n", m.Body.Instructions.Select(i => i.OpCode.Code + ":" + i.Operand));

using var resolver = new DefaultAssemblyResolver();
resolver.AddSearchDirectory(Path.GetDirectoryName(typeof(List<>).Assembly.Location)!);
using var asm = AssemblyDefinition.CreateAssembly(
    new AssemblyNameDefinition("ListAppendNestedPrivateFixture", new Version(1, 0)),
    "ListAppendNestedPrivateFixture",
    new ModuleParameters { Kind = ModuleKind.Dll, AssemblyResolver = resolver, Runtime = TargetRuntime.Net_4_0 });
var mod = asm.MainModule;
var i32 = mod.ImportReference(typeof(int));
var vd = mod.ImportReference(typeof(void));
var obj = mod.ImportReference(typeof(object));
var openList = mod.ImportReference(typeof(List<>));
var listType = new GenericInstanceType(openList);
listType.GenericArguments.Add(i32);
var gp = openList.GenericParameters[0];
var items = new FieldReference("_items", new ArrayType(gp), listType);
var version = new FieldReference("_version", i32, listType);
var sizeField = new FieldReference("_size", i32, listType);
var count = new MethodReference("get_Count", i32, listType) { HasThis = true };
var resize = new MethodReference("AddWithResize", vd, listType) { HasThis = true };
resize.Parameters.Add(new ParameterDefinition(gp));

TypeDefinition Type(string name, TypeDefinition? enclosing = null)
{
    var type = new TypeDefinition(enclosing == null ? "Fixture" : "", name,
        TypeAttributes.Class | (enclosing == null ? TypeAttributes.Public : TypeAttributes.NestedPublic), obj);
    if (enclosing == null) mod.Types.Add(type); else enclosing.NestedTypes.Add(type);
    return type;
}
var owner = Type("Owner");
var nested = Type("Nested", owner);
var middle = Type("Middle", owner);
var deep = Type("Deep", middle);
var unrelated = Type("Unrelated");
var unrelatedNested = Type("Nested", unrelated);
var secret = new FieldDefinition("Value", FieldAttributes.Private, i32);
owner.Fields.Add(secret);
var ctor = new MethodDefinition(".ctor",
    MethodAttributes.Public | MethodAttributes.HideBySig | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, vd);
ctor.Parameters.Add(new ParameterDefinition(i32)); owner.Methods.Add(ctor);
var ci = ctor.Body.GetILProcessor();
ci.Emit(OpCodes.Ldarg_0); ci.Emit(OpCodes.Call, mod.ImportReference(typeof(object).GetConstructor(System.Type.EmptyTypes)!));
ci.Emit(OpCodes.Ldarg_0); ci.Emit(OpCodes.Ldarg_1); ci.Emit(OpCodes.Stfld, secret); ci.Emit(OpCodes.Ret);

MethodDefinition ReadPrivate(TypeDefinition context, string name)
{
    var m = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static, i32);
    m.Parameters.Add(new ParameterDefinition(owner)); context.Methods.Add(m);
    var il = m.Body.GetILProcessor();
    il.Emit(OpCodes.Ldarg_0); il.Emit(OpCodes.Ldfld, secret); il.Emit(OpCodes.Ret);
    return m;
}
ReadPrivate(nested, "DirectRead");
ReadPrivate(deep, "DirectRead");

(MethodDefinition Method, Instruction[] Schedule, Instruction Slow, Instruction Join,
 VariableDefinition Source, VariableDefinition Value) Fixture(TypeDefinition context, string name)
{
    var m = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static, vd);
    context.Methods.Add(m);
    m.Parameters.Add(new ParameterDefinition(listType));
    m.Parameters.Add(new ParameterDefinition(owner));
    m.Body = new MethodBody(m) { InitLocals = true, MaxStackSize = 4 };
    var il = m.Body.GetILProcessor();
    VariableDefinition Local(TypeReference type)
    {
        var local = new VariableDefinition(type); m.Body.Variables.Add(local); return local;
    }
    var list = Local(listType); var array = Local(new ArrayType(i32));
    var size = Local(i32); var value = Local(i32); var source = Local(owner);
    il.Emit(OpCodes.Ldarg, m.Parameters[0]); il.Emit(OpCodes.Stloc, list);
    il.Emit(OpCodes.Ldarg, m.Parameters[1]); il.Emit(OpCodes.Stloc, source);
    il.Emit(OpCodes.Ldloc, list); il.Emit(OpCodes.Ldfld, items); il.Emit(OpCodes.Stloc, array);
    int first = m.Body.Instructions.Count;
    il.Emit(OpCodes.Ldloc, source); il.Emit(OpCodes.Ldfld, secret); il.Emit(OpCodes.Stloc, value);
    var schedule = m.Body.Instructions.Skip(first).ToArray();
    il.Emit(OpCodes.Ldloc, list); il.Emit(OpCodes.Ldloc, list);
    il.Emit(OpCodes.Ldfld, version); il.Emit(OpCodes.Ldc_I4, 1);
    il.Emit(OpCodes.Add); il.Emit(OpCodes.Stfld, version);
    il.Emit(OpCodes.Ldloc, list); il.Emit(OpCodes.Callvirt, count); il.Emit(OpCodes.Stloc, size);
    var slow = Instruction.Create(OpCodes.Nop); var join = Instruction.Create(OpCodes.Nop);
    il.Emit(OpCodes.Ldloc, array); il.Emit(OpCodes.Ldlen); il.Emit(OpCodes.Conv_I4);
    il.Emit(OpCodes.Ldloc, size); il.Emit(OpCodes.Cgt_Un); il.Emit(OpCodes.Ldc_I4, 0);
    il.Emit(OpCodes.Ceq); il.Emit(OpCodes.Brtrue, slow);
    il.Emit(OpCodes.Nop); il.Emit(OpCodes.Ldloc, list); il.Emit(OpCodes.Ldloc, size);
    il.Emit(OpCodes.Ldc_I4, 1); il.Emit(OpCodes.Add); il.Emit(OpCodes.Stfld, sizeField);
    il.Emit(OpCodes.Ldloc, array); il.Emit(OpCodes.Ldloc, size); il.Emit(OpCodes.Ldloc, value);
    il.Emit(OpCodes.Stelem_Any, i32); il.Emit(OpCodes.Br, join);
    il.Append(slow); il.Emit(OpCodes.Ldloc, list); il.Emit(OpCodes.Ldloc, value);
    il.Emit(OpCodes.Callvirt, resize);
    // An explicit separate slow tail limits this test to TryFold; the older
    // branch-preserving fallback does not accept this alternate layout.
    il.Emit(OpCodes.Nop); il.Emit(OpCodes.Br, join);
    il.Append(join); il.Emit(OpCodes.Ret);
    return (m, schedule, slow, join, source, value);
}
var positives = new[]
{
    Fixture(owner, "SameOwner"), Fixture(nested, "OneLevel"), Fixture(deep, "TwoLevels")
};
foreach (var f in positives)
{
    Check(Fold(f.Method) == 1, f.Method.Name + ": legal private read must fold");
    Check(f.Schedule[1].OpCode.Code == Code.Ldfld && f.Schedule[1].Operand == secret,
        "original private field read preserved");
    Check(f.Method.Body.Instructions.Count(i => i.Operand is MethodReference m && m.Name == "Add") == 1,
        "exactly one public append");
    Check(!f.Method.Body.Instructions.Any(i => i.Operand is FieldReference field &&
        field.Name is "_items" or "_size" or "_version"), "List private members remain");
    var order = f.Method.Body.Instructions;
    var check = order.First(i => i.Operand is MethodReference m && m.Name == "get_Count");
    var append = order.First(i => i.Operand is MethodReference m && m.Name == "Add");
    Check(order.IndexOf(check) < order.IndexOf(f.Schedule[1]) &&
        order.IndexOf(f.Schedule[1]) < order.IndexOf(append), "private read exception order");
    f.Method.Body.OptimizeMacros();
}

var staticSecret = new FieldDefinition("StaticValue", FieldAttributes.Private | FieldAttributes.Static, i32);
var wideSecret = new FieldDefinition("WideValue", FieldAttributes.Private, mod.ImportReference(typeof(long)));
owner.Fields.Add(staticSecret); owner.Fields.Add(wideSecret);
var negatives = new[]
{
    "UnrelatedOwner", "NestedInUnrelatedOwner", "WrongReceiver", "StaticField",
    "WrongFieldType", "OutsideEntry", "AddressEscape", "ArbitraryGetter"
};
foreach (var name in negatives)
{
    var context = name == "UnrelatedOwner" ? unrelated : name == "NestedInUnrelatedOwner" ? unrelatedNested : nested;
    var f = Fixture(context, name); var il = f.Method.Body.GetILProcessor();
    switch (name)
    {
        case "WrongReceiver":
            f.Source.VariableType = unrelated; break;
        case "StaticField":
            f.Schedule[1].Operand = staticSecret; break;
        case "WrongFieldType":
            f.Schedule[1].Operand = wideSecret; break;
        case "OutsideEntry":
            il.InsertBefore(f.Method.Body.Instructions[0], Instruction.Create(OpCodes.Br, f.Schedule[0])); break;
        case "AddressEscape":
            il.InsertBefore(f.Method.Body.Instructions[0], Instruction.Create(OpCodes.Ldloca, f.Value));
            il.InsertBefore(f.Method.Body.Instructions[1], Instruction.Create(OpCodes.Pop)); break;
        case "ArbitraryGetter":
            f.Schedule[1].OpCode = OpCodes.Callvirt;
            f.Schedule[1].Operand = new MethodReference("get_Value", i32, owner) { HasThis = true }; break;
    }
    var before = Shape(f.Method);
    Check(Fold(f.Method) == 0, name + ": unauthorized access/pattern accepted");
    Check(Shape(f.Method) == before, name + ": rejected body changed");
    context.Methods.Remove(f.Method);
}
owner.Fields.Remove(staticSecret); owner.Fields.Remove(wideSecret);

using var bytes = new MemoryStream(); asm.Write(bytes);
var validBytes = bytes.ToArray();
var runtime = Assembly.Load(validBytes);
var ownerType = runtime.GetType("Fixture.Owner", true)!;
int executions = 0;
static int Version(List<int> list) => (int)typeof(List<int>)
    .GetField("_version", BindingFlags.NonPublic | BindingFlags.Instance)!.GetValue(list)!;
foreach (var f in positives)
{
    var runtimeType = runtime.GetType(f.Method.DeclaringType.FullName.Replace('/', '+'), true)!;
    var method = runtimeType.GetMethod(f.Method.Name)!;
    foreach (int capacity in new[] { 0, 8 })
    foreach (int value in new[] { -13, 71 })
    {
        var list = new List<int>(capacity);
        var receiver = Activator.CreateInstance(ownerType, value)!;
        int before = Version(list);
        executions++; method.Invoke(null, new object?[] { list, receiver });
        Check(list.SequenceEqual(new[] { value }) && Version(list) == before + 1,
            f.Method.Name + ": wrong append/private value/version");
    }
    var kept = new List<int> { 5 }; var versionBefore = Version(kept);
    try { executions++; method.Invoke(null, new object?[] { kept, null }); throw new Exception("null field receiver accepted"); }
    catch (TargetInvocationException ex) when (ex.InnerException is NullReferenceException) { }
    Check(kept.SequenceEqual(new[] { 5 }) && Version(kept) == versionBefore,
        "field receiver null must precede List mutation");
    try { executions++; method.Invoke(null, new object?[] { null, Activator.CreateInstance(ownerType, 4) }); throw new Exception("null List accepted"); }
    catch (TargetInvocationException ex) when (ex.InnerException is NullReferenceException) { }
}
foreach (string name in new[] { "Fixture.Owner+Nested", "Fixture.Owner+Middle+Deep" })
{
    executions++;
    Check((int)runtime.GetType(name, true)!.GetMethod("DirectRead")!
        .Invoke(null, new[] { Activator.CreateInstance(ownerType, 93) })! == 93,
        "direct nested private read must execute independently of normalization");
}
if (args.Length == 1)
{
    Directory.CreateDirectory(args[0]);
    File.WriteAllBytes(Path.Combine(args[0], "nested-private-valid.dll"), validBytes);
    // A verifier negative control proves private field visibility is checked,
    // rather than silently skipped when the valid nested cases verify.
    asm.Name.Name = "ListAppendNestedPrivateFixtureInvalid";
    ReadPrivate(unrelated, "ForbiddenRead");
    asm.Write(Path.Combine(args[0], "unrelated-private-invalid.dll"));
}
Console.WriteLine($"LIST_APPEND_NESTED_FIELD_SMOKE_PASS folded_fixtures={positives.Length} nested_levels=2 negative_patterns={negatives.Length} runtime_invocations={executions} separate_direct_reads=2");
