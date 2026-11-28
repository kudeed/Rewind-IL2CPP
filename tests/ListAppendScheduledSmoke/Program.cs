
using Mono.Cecil;
using Mono.Cecil.Cil;
using Mono.Cecil.Rocks;
using System.Reflection;
using Assembly = System.Reflection.Assembly;
using TypeAttributes = Mono.Cecil.TypeAttributes;
using MethodAttributes = Mono.Cecil.MethodAttributes;
using FieldAttributes = Mono.Cecil.FieldAttributes;
using MethodBody = Mono.Cecil.Cil.MethodBody;

static void Check(bool value, string message)
{
    if (!value) throw new Exception(message);
}
var output = Assembly.Load("Rewind.Output");
var run = output.GetType("Rewind.Output.ListAppendIlFolding", true)!
    .GetMethod("Run", BindingFlags.NonPublic | BindingFlags.Static)!;
int Fold(MethodDefinition method) => (int)run.Invoke(null, new object[] { method.Body })!;
static string Shape(MethodDefinition method) => string.Join("\n",
    method.Body.Instructions.Select(i => i.OpCode.Code + ":" + i.Operand));

using var resolver = new DefaultAssemblyResolver();
resolver.AddSearchDirectory(Path.GetDirectoryName(typeof(List<>).Assembly.Location)!);
using var asm = AssemblyDefinition.CreateAssembly(
    new AssemblyNameDefinition("ListAppendScheduleFixture", new Version(1, 0)),
    "ListAppendScheduleFixture",
    new ModuleParameters { Kind = ModuleKind.Dll, AssemblyResolver = resolver, Runtime = TargetRuntime.Net_4_0 });
var mod = asm.MainModule;
var i32 = mod.ImportReference(typeof(int));
var i64 = mod.ImportReference(typeof(long));
var fp = mod.ImportReference(typeof(float));
var vd = mod.ImportReference(typeof(void));
var obj = mod.ImportReference(typeof(object));
var text = mod.ImportReference(typeof(string));
var openList = mod.ImportReference(typeof(List<>));
var gp = openList.GenericParameters[0];
var host = new TypeDefinition("Fixture", "AppendHost",
    TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed, obj);
mod.Types.Add(host);

(TypeDefinition Type, FieldDefinition Field) Holder(string name, TypeReference element)
{
    var type = new TypeDefinition("Fixture", name, TypeAttributes.Public | TypeAttributes.Class, obj);
    mod.Types.Add(type);
    var field = new FieldDefinition("Value", FieldAttributes.Public, element);
    type.Fields.Add(field);
    var ctor = new MethodDefinition(".ctor",
        MethodAttributes.Public | MethodAttributes.HideBySig | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, vd);
    type.Methods.Add(ctor);
    var il = ctor.Body.GetILProcessor();
    il.Emit(OpCodes.Ldarg_0);
    il.Emit(OpCodes.Call, mod.ImportReference(typeof(object).GetConstructor(Type.EmptyTypes)!));
    il.Emit(OpCodes.Ret);
    return (type, field);
}
var integerHolder = Holder("IntegerHolder", i32);
var floatHolder = Holder("FloatHolder", fp);

// A full, exact List.Add diamond. Array schedules use an Int64 index and
// unchecked index arithmetic; field and field-plus-float schedules protect
// both older matchers from regressions when the array case is extended.
(MethodDefinition Method, Instruction[] Schedule, Instruction Entry, Instruction Slow,
 Instruction Join, VariableDefinition Array, VariableDefinition Index,
 VariableDefinition Value, VariableDefinition Source) Fixture(
    string name, TypeReference element, string kind, bool separated = false)
{
    var listType = new GenericInstanceType(openList);
    listType.GenericArguments.Add(element);
    var items = new FieldReference("_items", new ArrayType(gp), listType);
    var version = new FieldReference("_version", i32, listType);
    var sizeField = new FieldReference("_size", i32, listType);
    var count = new MethodReference("get_Count", i32, listType) { HasThis = true };
    var resize = new MethodReference("AddWithResize", vd, listType) { HasThis = true };
    resize.Parameters.Add(new ParameterDefinition(gp));
    var method = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static, vd);
    host.Methods.Add(method);
    var holder = kind == "float" ? floatHolder : integerHolder;
    method.Parameters.Add(new ParameterDefinition(listType));
    method.Parameters.Add(new ParameterDefinition(kind == "array" ? new ArrayType(element) : holder.Type));
    if (kind == "array") method.Parameters.Add(new ParameterDefinition(i64));
    if (kind == "float")
    {
        method.Parameters.Add(new ParameterDefinition(fp));
        method.Parameters.Add(new ParameterDefinition(fp));
    }
    method.Body = new MethodBody(method) { InitLocals = true, MaxStackSize = 4 };
    var il = method.Body.GetILProcessor();
    VariableDefinition Local(TypeReference type)
    {
        var local = new VariableDefinition(type);
        method.Body.Variables.Add(local);
        return local;
    }
    var list = Local(listType);
    var array = Local(new ArrayType(element));
    var size = Local(i32);
    var value = Local(element);
    var source = Local(method.Parameters[1].ParameterType);
    var index = Local(i64);
    var factor = Local(fp);
    var left = Local(fp);
    var right = Local(fp);
    il.Emit(OpCodes.Ldarg, method.Parameters[0]); il.Emit(OpCodes.Stloc, list);
    il.Emit(OpCodes.Ldarg, method.Parameters[1]); il.Emit(OpCodes.Stloc, source);
    if (kind == "array")
    {
        il.Emit(OpCodes.Ldarg, method.Parameters[2]); il.Emit(OpCodes.Stloc, index);
    }
    if (kind == "float")
    {
        il.Emit(OpCodes.Ldarg, method.Parameters[2]); il.Emit(OpCodes.Stloc, left);
        il.Emit(OpCodes.Ldarg, method.Parameters[3]); il.Emit(OpCodes.Stloc, right);
    }
    var entry = Instruction.Create(OpCodes.Ldloc, list); il.Append(entry);
    il.Emit(OpCodes.Ldfld, items); il.Emit(OpCodes.Stloc, array);
    var begin = method.Body.Instructions.Count;
    il.Emit(OpCodes.Ldloc, source);
    if (kind == "array")
    {
        il.Emit(OpCodes.Ldloc, index); il.Emit(OpCodes.Ldc_I4, -4);
        il.Emit(OpCodes.Conv_I8); il.Emit(OpCodes.Add); il.Emit(OpCodes.Conv_I4);
        il.Emit(OpCodes.Ldelem_Any, element); il.Emit(OpCodes.Stloc, value);
    }
    else
    {
        il.Emit(OpCodes.Ldfld, holder.Field);
        il.Emit(OpCodes.Stloc, kind == "float" ? factor : value);
    }
    var schedule = method.Body.Instructions.Skip(begin).ToArray();
    il.Emit(OpCodes.Ldloc, list); il.Emit(OpCodes.Ldloc, list);
    il.Emit(OpCodes.Ldfld, version); il.Emit(OpCodes.Ldc_I4, 1);
    il.Emit(OpCodes.Add); il.Emit(OpCodes.Stfld, version);
    il.Emit(OpCodes.Ldloc, list); il.Emit(OpCodes.Callvirt, count); il.Emit(OpCodes.Stloc, size);
    if (kind == "float")
    {
        il.Emit(OpCodes.Ldloc, left); il.Emit(OpCodes.Ldloc, right);
        il.Emit(OpCodes.Sub); il.Emit(OpCodes.Conv_R4);
        il.Emit(OpCodes.Ldloc, factor); il.Emit(OpCodes.Mul);
        il.Emit(OpCodes.Conv_R4); il.Emit(OpCodes.Stloc, value);
    }
    var slow = Instruction.Create(OpCodes.Nop);
    var join = Instruction.Create(OpCodes.Nop);
    il.Emit(OpCodes.Ldloc, array); il.Emit(OpCodes.Ldlen); il.Emit(OpCodes.Conv_I4);
    il.Emit(OpCodes.Ldloc, size); il.Emit(OpCodes.Cgt_Un);
    il.Emit(OpCodes.Ldc_I4, 0); il.Emit(OpCodes.Ceq); il.Emit(OpCodes.Brtrue, slow);
    il.Emit(OpCodes.Nop); il.Emit(OpCodes.Ldloc, list); il.Emit(OpCodes.Ldloc, size);
    il.Emit(OpCodes.Ldc_I4, 1); il.Emit(OpCodes.Add); il.Emit(OpCodes.Stfld, sizeField);
    il.Emit(OpCodes.Ldloc, array); il.Emit(OpCodes.Ldloc, size); il.Emit(OpCodes.Ldloc, value);
    il.Emit(OpCodes.Stelem_Any, element); il.Emit(OpCodes.Br, join);
    il.Append(slow); il.Emit(OpCodes.Ldloc, list); il.Emit(OpCodes.Ldloc, value);
    il.Emit(OpCodes.Callvirt, resize);
    if (separated) { il.Emit(OpCodes.Nop); il.Emit(OpCodes.Br, join); }
    il.Append(join); il.Emit(OpCodes.Ret);
    return (method, schedule, entry, slow, join, array, index, value, source);
}

var arrayInt = Fixture("ArrayInt", i32, "array");
var arrayText = Fixture("ArrayText", text, "array", separated: true);
var legacyField = Fixture("LegacyField", i32, "field");
var legacyFloat = Fixture("LegacyFieldAndFloat", fp, "float", separated: true);
foreach (var fixture in new[] { arrayInt, arrayText, legacyField, legacyFloat })
{
    var isArray = fixture.Method.Name.StartsWith("Array", StringComparison.Ordinal);
    var read = fixture.Schedule[isArray ? 6 : 1];
    Check(Fold(fixture.Method) == 1, fixture.Method.Name + ": exact diamond must fold");
    Check(fixture.Method.Body.Instructions.Count(i => i.Operand is MethodReference mr && mr.Name == "Add") == 1,
        fixture.Method.Name + ": one public Add required");
    Check(!fixture.Method.Body.Instructions.Any(i => i.Operand is FieldReference f &&
        f.Name is "_items" or "_version" or "_size"), fixture.Method.Name + ": no private List members");
    if (isArray)
    {
        Check(read.OpCode.Code == Code.Ldelem_Any, "original throwing array read must survive");
        var instructions = fixture.Method.Body.Instructions;
        var check = instructions.First(i => i.Operand is MethodReference mr && mr.Name == "get_Count");
        var add = instructions.First(i => i.Operand is MethodReference mr && mr.Name == "Add");
        Check(instructions.IndexOf(check) < instructions.IndexOf(read) &&
            instructions.IndexOf(read) < instructions.IndexOf(add),
            "list null check, array read, version-changing append must remain ordered");
    }
    fixture.Method.Body.OptimizeMacros();
}

// Mutants must be rejected without rewriting even a single instruction.
// Separate slow tails prevent the older branch-preserving fallback from
// accepting a different supported shape while testing the exact new matcher.
var negativeNames = new[]
{
    "BranchInSchedule", "IndexWrongWidth", "WrongElementRead", "SourceAliasesItems",
    "DestinationAliasesIndex", "OutsideEntry", "AddressEscape", "CheckedArithmetic",
    "EffectfulRead", "ExtraArithmetic"
};
foreach (var name in negativeNames)
{
    var f = Fixture(name, i32, "array", separated: true);
    var il = f.Method.Body.GetILProcessor();
    switch (name)
    {
        case "BranchInSchedule":
            f.Schedule[6].OpCode = OpCodes.Br; f.Schedule[6].Operand = f.Join; break;
        case "IndexWrongWidth":
            f.Index.VariableType = i32; break;
        case "WrongElementRead":
            f.Schedule[6].Operand = fp; break;
        case "SourceAliasesItems":
            f.Schedule[0].Operand = f.Array; break;
        case "DestinationAliasesIndex":
            f.Schedule[7].Operand = f.Index; break;
        case "OutsideEntry":
            il.InsertBefore(f.Method.Body.Instructions[0], Instruction.Create(OpCodes.Br, f.Schedule[0])); break;
        case "AddressEscape":
            il.InsertBefore(f.Method.Body.Instructions[0], Instruction.Create(OpCodes.Ldloca, f.Value));
            il.InsertBefore(f.Method.Body.Instructions[1], Instruction.Create(OpCodes.Pop)); break;
        case "CheckedArithmetic":
            f.Schedule[4].OpCode = OpCodes.Add_Ovf; break;
        case "EffectfulRead":
            f.Schedule[6].OpCode = OpCodes.Call;
            f.Schedule[6].Operand = mod.ImportReference(typeof(GC).GetMethod(nameof(GC.Collect), Type.EmptyTypes)!);
            break;
        case "ExtraArithmetic":
            il.InsertBefore(f.Schedule[7], Instruction.Create(OpCodes.Neg)); break;
    }
    var before = Shape(f.Method);
    Check(Fold(f.Method) == 0, name + ": unsafe pattern accepted");
    Check(Shape(f.Method) == before, name + ": rejected body changed");
    host.Methods.Remove(f.Method);
}

// Persisting and loading the folded IL catches invalid operands and stack
// types that a metadata-only "one match" assertion cannot detect.
using var bytes = new MemoryStream();
asm.Write(bytes);
var runtime = Assembly.Load(bytes.ToArray());
var runtimeHost = runtime.GetType("Fixture.AppendHost", true)!;
static int Version(object list) => (int)list.GetType()
    .GetField("_version", BindingFlags.NonPublic | BindingFlags.Instance)!.GetValue(list)!;
int executions = 0;
void Invoke(string name, params object?[] arguments)
{
    executions++;
    runtimeHost.GetMethod(name)!.Invoke(null, arguments);
}
void Throws<T>(string name, params object?[] arguments) where T : Exception
{
    try { Invoke(name, arguments); }
    catch (TargetInvocationException ex) when (ex.InnerException is T) { return; }
    throw new Exception(name + ": expected " + typeof(T).Name);
}
foreach (var capacity in new[] { 0, 8 })
{
    var list = new List<int>(capacity) { 9 };
    var before = Version(list);
    Invoke("ArrayInt", list, new[] { 11, 17 }, 5L);
    Check(list.SequenceEqual(new[] { 9, 17 }) && Version(list) == before + 1, "array int append/value/version");
}
foreach (var capacity in new[] { 0, 8 })
{
    var list = new List<string?>(capacity);
    var before = Version(list);
    Invoke("ArrayText", list, new string?[] { "one", null }, 4L);
    Invoke("ArrayText", list, new string?[] { "one", null }, 5L);
    Check(list.SequenceEqual(new string?[] { "one", null }) && Version(list) == before + 2,
        "reference/null element append and resize");
}
foreach (var index in new[] { 3L, 6L, long.MinValue, long.MaxValue })
{
    var list = new List<int> { 23 };
    var before = Version(list);
    var expected = unchecked((int)(index - 4));
    if (expected >= 0 && expected < 2)
    {
        Invoke("ArrayInt", list, new[] { 11, 17 }, index);
        Check(list.Last() == new[] { 11, 17 }[expected], "unchecked index preserved");
    }
    else
    {
        var enumerator = list.GetEnumerator();
        Check(enumerator.MoveNext(), "seed enumerator");
        Throws<IndexOutOfRangeException>("ArrayInt", list, new[] { 11, 17 }, index);
        Check(list.SequenceEqual(new[] { 23 }) && Version(list) == before, "bounds failure must not mutate List");
        Check(!enumerator.MoveNext(), "bounds failure must preserve enumerator version");
    }
}
{
    var list = new List<int> { 23 };
    var before = Version(list);
    Throws<NullReferenceException>("ArrayInt", list, null, 4L);
    Check(list.SequenceEqual(new[] { 23 }) && Version(list) == before, "null source must not mutate List");
    // With both a null receiver and an out-of-bounds source index, the
    // receiver null exception must occur before array bounds checking.
    Throws<NullReferenceException>("ArrayInt", null, Array.Empty<int>(), 4L);
}
var integerType = runtime.GetType("Fixture.IntegerHolder", true)!;
var floatType = runtime.GetType("Fixture.FloatHolder", true)!;
foreach (var capacity in new[] { 0, 8 })
{
    var holder = Activator.CreateInstance(integerType)!;
    integerType.GetField("Value")!.SetValue(holder, 71);
    var list = new List<int>(capacity);
    var before = Version(list);
    Invoke("LegacyField", list, holder);
    Check(list.SequenceEqual(new[] { 71 }) && Version(list) == before + 1, "legacy field writer regression");
    Throws<NullReferenceException>("LegacyField", list, null);
    Check(list.Count == 1 && Version(list) == before + 1, "legacy field exception order");

    var floatOwner = Activator.CreateInstance(floatType)!;
    floatType.GetField("Value")!.SetValue(floatOwner, 2.5f);
    var values = new List<float>(capacity);
    var floatBefore = Version(values);
    Invoke("LegacyFieldAndFloat", values, floatOwner, 7.25f, 1.25f);
    Check(values.SequenceEqual(new[] { 15f }) && Version(values) == floatBefore + 1,
        "legacy field destination may differ from computed appended value");
    Throws<NullReferenceException>("LegacyFieldAndFloat", values, null, 7.25f, 1.25f);
    Check(values.Count == 1 && Version(values) == floatBefore + 1, "legacy float pre-version field exception");
}
Console.WriteLine($"PASS: 4 executable folded fixtures; {negativeNames.Length} rejected unchanged mutants; {executions} invocations; array null/bounds/version order and legacy field/float regressions");
