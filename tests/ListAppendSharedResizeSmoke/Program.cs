using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;
using Rewind.Output;
using TypeAttributes = Mono.Cecil.TypeAttributes;
using MethodAttributes = Mono.Cecil.MethodAttributes;
using ParameterAttributes = Mono.Cecil.ParameterAttributes;

using var fixture = new Fixture();
int positive = 0, negative = 0, operations = 0, failureCases = 0;
string Shape(MethodDefinition m) => string.Join("\n", m.Body.Instructions.Select(i => i.OpCode.Code + ":" + i.Operand));
void Good(string name, bool read, int constant)
{
    var c = fixture.Create(name, read, constant);
    if (ListAppendIlFolding.Run(c.Method.Body) != 2) throw new Exception(name + ": pair was not restored atomically");
    if (c.Method.Body.Instructions.Any(i => i.Operand is FieldReference f && f.Name is "_items" or "_size" or "_version") ||
        c.Method.Body.Instructions.Any(i => i.Operand is MethodReference m && m.Name == "AddWithResize"))
        throw new Exception(name + ": remaining List internals");
    if (ListAppendIlFolding.Run(c.Method.Body) != 0) throw new Exception(name + ": not idempotent");
    positive++;
}
void Bad(string name, Action<Case> change)
{
    var c = fixture.Create(name, true, 1); change(c);
    string before = Shape(c.Method); int locals = c.Method.Body.Variables.Count;
    if (ListAppendIlFolding.Run(c.Method.Body) != 0 || Shape(c.Method) != before || c.Method.Body.Variables.Count != locals)
        throw new Exception(name + ": partially rewrote an unproved shared pair");
    fixture.Host.Methods.Remove(c.Method); negative++;
}
Good("ReadAndConstant", true, 1);
Good("ArgumentAndNegativeConstant", false, -7);
Bad("ThirdIncomingSharedEdge", c => c.Method.Body.GetILProcessor().InsertBefore(c.Method.Body.Instructions[0], Instruction.Create(OpCodes.Br, c.Shared)));
Bad("ThirdIncomingSlowEdge", c => c.Method.Body.GetILProcessor().InsertBefore(c.Method.Body.Instructions[0], Instruction.Create(OpCodes.Br, c.SlowA)));
Bad("MissingSecondVersionProof", c => c.VersionB[2].OpCode = OpCodes.Nop);
Bad("SecondVersionIncrementTwo", c => c.VersionB[3].Operand = 2);
Bad("DifferentSlowValue", c => c.SlowB.Next!.Operand = 2);
Bad("DifferentPhi", c => c.SlowB.Next!.Next!.Operand = c.Other);
Bad("DifferentSharedReceiver", c =>
{
    var other = new ParameterDefinition("otherList", ParameterAttributes.None, fixture.List); c.Method.Parameters.Add(other); c.Shared.Next!.Operand = other;
});
Bad("SlowCallback", c => c.Method.Body.GetILProcessor().InsertBefore(c.SlowB.Next!, Instruction.Create(OpCodes.Call, fixture.Observe)));
Bad("PhiAddressEscapes", c =>
{
    var il = c.Method.Body.GetILProcessor(); il.InsertBefore(c.Method.Body.Instructions[^1], Instruction.Create(OpCodes.Ldloca, c.Phi));
    il.InsertBefore(c.Method.Body.Instructions[^1], Instruction.Create(OpCodes.Pop));
});
Bad("PostVersionIntegerDivide", c => { c.Calculation[1].Operand = 0; c.Calculation[2].OpCode = OpCodes.Div; });
Bad("PostVersionCheckedAdd", c => c.Calculation[2].OpCode = OpCodes.Add_Ovf);
Bad("PostVersionCallback", c => c.Method.Body.GetILProcessor().InsertBefore(c.Calculation[0], Instruction.Create(OpCodes.Call, fixture.Observe)));
Bad("ThrowingReadAfterVersion", c =>
{
    var il = c.Method.Body.GetILProcessor(); foreach (var i in c.Read) { il.Remove(i); il.InsertBefore(c.Calculation[0], i); }
});
Bad("WrongUnsignedCapacity", c => c.CapacityB[4].OpCode = OpCodes.Cgt);
Bad("DifferentFastContinuation", c => c.FastEndA.Operand = c.Method.Body.Instructions[^1]);
Bad("ArrayEscapesRegion", c => c.Method.Body.GetILProcessor().InsertBefore(c.Method.Body.Instructions[^1], Instruction.Create(OpCodes.Ldloc, c.ArrayA)));
Bad("CountAddressEscapes", c => c.Method.Body.GetILProcessor().InsertBefore(c.Method.Body.Instructions[^1], Instruction.Create(OpCodes.Ldloca, c.SizeB)));
Bad("ExceptionScope", c => c.Method.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
    { TryStart = c.Method.Body.Instructions[0], TryEnd = c.Join, HandlerStart = c.Join, HandlerEnd = null, CatchType = fixture.Module.ImportReference(typeof(Exception)) }));
Bad("WrongVersionMember", c => c.VersionB[2].Operand = new FieldReference("unrelatedVersion", fixture.Int, fixture.List));
Bad("SharedCallWrongMethod", c => c.Resize.Operand = fixture.Observe);
Bad("ThirdSharedPhysicalFallThrough", c =>
{
    var il = c.Method.Body.GetILProcessor();
    il.InsertBefore(c.Shared, Instruction.Create(OpCodes.Br, c.Shared));
    var third = Instruction.Create(OpCodes.Nop); il.InsertBefore(c.Shared, third);
    il.InsertBefore(c.Method.Body.Instructions[0], Instruction.Create(OpCodes.Br, third));
});
Bad("SecondArrayAddressEscapes", c => c.Method.Body.GetILProcessor().InsertBefore(c.Method.Body.Instructions[^1],
    Instruction.Create(OpCodes.Ldloca, (VariableDefinition)c.CapacityB[0].Operand)));
Bad("PostVersionReceiverWrite", c =>
{
    var il = c.Method.Body.GetILProcessor();
    il.InsertBefore(c.Calculation[0], Instruction.Create(OpCodes.Ldarg, c.Method.Parameters[0]));
    il.InsertBefore(c.Calculation[0], Instruction.Create(OpCodes.Starg, c.Method.Parameters[0]));
});
Bad("PostVersionSharedPhiWrite", c => c.Calculation[^1].Operand = c.Phi);
Bad("PostVersionOtherDiamondSizeWrite", c => c.Calculation[^1].Operand = c.SizeB);
Bad("GenericCountSpecification", c =>
{
    var call = c.Method.Body.Instructions.First(i => i.Operand is MethodReference m && m.Name == "get_Count");
    var generic = new GenericInstanceMethod((MethodReference)call.Operand); generic.GenericArguments.Add(fixture.Int); call.Operand = generic;
});
Bad("GenericResizeSpecification", c =>
{
    var generic = new GenericInstanceMethod((MethodReference)c.Resize.Operand); generic.GenericArguments.Add(fixture.Int); c.Resize.Operand = generic;
});

using var stream = new MemoryStream(); fixture.Assembly.Write(stream);
Type host = System.Reflection.Assembly.Load(stream.ToArray()).GetType("Fixture.SharedHost", true)!;
FieldInfo version = typeof(List<int>).GetField("_version", BindingFlags.Instance | BindingFlags.NonPublic)!;
int Call(MethodInfo method, List<int>? list, bool first, SourceHolder? source, int value) =>
    (int)method.Invoke(null, new object?[] { list, first, source, value })!;
foreach (string name in new[] { "ReadAndConstant", "ArgumentAndNegativeConstant" })
foreach (int capacity in new[] { 0, 1, 8, 64 })
{
    var actual = new List<int>(capacity); var expected = new List<int>(capacity); MethodInfo method = host.GetMethod(name)!;
    for (int n = 0; n < 50; n++)
    {
        bool first = n % 3 != 0;
        int value = n % 7 == 0 ? int.MaxValue : n % 11 == 0 ? int.MinValue : n - 23;
        var holder = new SourceHolder { Value = value };
        var old = actual.GetEnumerator(); old.MoveNext(); int oldVersion = (int)version.GetValue(actual)!;
        int result = Call(method, actual, first, holder, value);
        int wanted = first ? name == "ReadAndConstant" ? unchecked(value + 2) : value : name == "ReadAndConstant" ? 1 : -7;
        expected.Add(wanted);
        if (!actual.SequenceEqual(expected) || actual.Capacity != expected.Capacity || result != expected.Count ||
            (int)version.GetValue(actual)! != unchecked(oldVersion + 1)) throw new Exception(name + ": wrong value/capacity/continuation/version");
        bool invalidated = false; try { old.MoveNext(); } catch (InvalidOperationException) { invalidated = true; }
        if (!invalidated) throw new Exception(name + ": old enumerator remained valid");
        operations++;
    }
}
MethodInfo readMethod = host.GetMethod("ReadAndConstant")!;
foreach (int capacity in new[] { 1, 8 })
{
    var target = new List<int>(capacity) { 17 }; int oldVersion = (int)version.GetValue(target)!, oldCapacity = target.Capacity;
    var old = target.GetEnumerator();
    try { Call(readMethod, target, true, null, 4); throw new Exception("Expected null source"); }
    catch (TargetInvocationException e) when (e.InnerException is NullReferenceException) { }
    if (target.Count != 1 || target[0] != 17 || target.Capacity != oldCapacity || (int)version.GetValue(target)! != oldVersion || !old.MoveNext())
        throw new Exception("Pre-version source failure changed list or enumerator");
    failureCases++;
    // The unselected source read must remain unevaluated on the constant path.
    if (Call(readMethod, target, false, null, int.MaxValue) != 2 || target[1] != 1 || (int)version.GetValue(target)! != unchecked(oldVersion + 1))
        throw new Exception("Constant arm evaluated or depended on the other source");
    operations++;
}
foreach (bool first in new[] { false, true })
{
    try { Call(readMethod, null, first, new SourceHolder { Value = 5 }, 4); throw new Exception("Expected null receiver"); }
    catch (TargetInvocationException e) when (e.InnerException is NullReferenceException) { failureCases++; }
    var target = new List<int>(8) { 9 }; version.SetValue(target, int.MaxValue);
    var old = target.GetEnumerator();
    Call(readMethod, target, first, new SourceHolder { Value = int.MaxValue }, int.MaxValue);
    if ((int)version.GetValue(target)! != int.MinValue || target.Count != 2 || target[1] != (first ? unchecked(int.MaxValue + 2) : 1))
        throw new Exception("Unchecked version or item arithmetic changed");
    bool invalidated = false; try { old.MoveNext(); } catch (InvalidOperationException) { invalidated = true; }
    if (!invalidated) throw new Exception("Wrapped version did not invalidate enumerator");
    operations++;
}
Console.WriteLine($"SHARED_RESIZE_APPEND_SMOKE_PASS positive={positive} negative={negative} runtime_operations={operations} exception_cases={failureCases} pair_atomic=true capacity_and_values=true version_once_and_wrap=true enum_invalidated=true original_source_exception_order=true unselected_source_untouched=true");

public sealed class SourceHolder { public int Value; }
sealed record Case(MethodDefinition Method, Instruction[] VersionB, Instruction[] CapacityB, Instruction[] Read, Instruction[] Calculation,
    Instruction FastEndA, Instruction SlowA, Instruction SlowB, Instruction Shared, Instruction Resize, Instruction Join,
    VariableDefinition Phi, VariableDefinition Other, VariableDefinition ArrayA, VariableDefinition SizeB);
sealed class Fixture : IDisposable
{
    public readonly DefaultAssemblyResolver Resolver = new();
    public readonly AssemblyDefinition Assembly;
    public ModuleDefinition Module => Assembly.MainModule;
    public readonly TypeDefinition Host;
    public readonly TypeReference Int;
    public readonly GenericInstanceType List;
    public readonly MethodDefinition Observe;
    private readonly FieldReference Items, Version, Size, SourceValue;
    private readonly MethodReference Count, Resize;
    public Fixture()
    {
        Resolver.AddSearchDirectory(Path.GetDirectoryName(typeof(List<>).Assembly.Location)!); Resolver.AddSearchDirectory(AppContext.BaseDirectory);
        Assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("SharedResizeFixture", new Version(1, 0)), "SharedResizeFixture",
            new ModuleParameters { Kind = ModuleKind.Dll, AssemblyResolver = Resolver, Runtime = TargetRuntime.Net_4_0 });
        var m = Module; Int = m.ImportReference(typeof(int)); var open = m.ImportReference(typeof(List<>)); List = new GenericInstanceType(open); List.GenericArguments.Add(Int);
        Items = new FieldReference("_items", new ArrayType(open.GenericParameters[0]), List); Version = new FieldReference("_version", Int, List); Size = new FieldReference("_size", Int, List);
        Count = new MethodReference("get_Count", Int, List) { HasThis = true };
        Resize = new MethodReference("AddWithResize", m.TypeSystem.Void, List) { HasThis = true }; Resize.Parameters.Add(new ParameterDefinition(open.GenericParameters[0]));
        var reflectedField = m.ImportReference(typeof(SourceHolder).GetField(nameof(SourceHolder.Value))!);
        var sourceDefinition = reflectedField.Resolve();
        // Preserve the real field metadata scope (System.Runtime on .NET), rather than a reflection-forwarded CoreLib signature.
        SourceValue = m.ImportReference(sourceDefinition);
        Host = new TypeDefinition("Fixture", "SharedHost", TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed, m.TypeSystem.Object); m.Types.Add(Host);
        Observe = new MethodDefinition("Observe", MethodAttributes.Public | MethodAttributes.Static, m.TypeSystem.Void); Host.Methods.Add(Observe); Observe.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
    }
    public Case Create(string name, bool read, int constant)
    {
        var m = Module; var method = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static, Int); Host.Methods.Add(method); method.Body.InitLocals = true;
        ParameterDefinition Param(string n, TypeReference t) { var p = new ParameterDefinition(n, ParameterAttributes.None, t); method.Parameters.Add(p); return p; }
        var target = Param("list", List); var flag = Param("first", m.TypeSystem.Boolean); var source = Param("source", m.ImportReference(typeof(SourceHolder))); var input = Param("value", Int);
        VariableDefinition Local(TypeReference t) { var v = new VariableDefinition(t); method.Body.Variables.Add(v); return v; }
        var phi = Local(Int); var other = Local(Int); var arrayA = Local(new ArrayType(Int)); var sizeA = Local(Int); var arrayB = Local(new ArrayType(Int)); var sizeB = Local(Int); var readValue = Local(SourceValue.FieldType); var calculated = Local(Int);
        var il = method.Body.GetILProcessor(); var second = Instruction.Create(OpCodes.Nop); var slowA = Instruction.Create(OpCodes.Nop); var slowB = Instruction.Create(OpCodes.Nop); var shared = Instruction.Create(OpCodes.Nop); var join = Instruction.Create(OpCodes.Nop);
        void Add(params Instruction[] code) { foreach (var i in code) il.Append(i); }
        Instruction LoadTarget() => Instruction.Create(OpCodes.Ldarg, target);
        Instruction[] VersionCode() => [LoadTarget(), LoadTarget(), Instruction.Create(OpCodes.Ldfld, Version), Instruction.Create(OpCodes.Ldc_I4, 1), Instruction.Create(OpCodes.Add), Instruction.Create(OpCodes.Stfld, Version)];
        Instruction[] CapacityCode(VariableDefinition array, VariableDefinition size, Instruction slow) => [Instruction.Create(OpCodes.Ldloc, array), Instruction.Create(OpCodes.Ldlen), Instruction.Create(OpCodes.Conv_I4), Instruction.Create(OpCodes.Ldloc, size), Instruction.Create(OpCodes.Cgt_Un), Instruction.Create(OpCodes.Ldc_I4, 0), Instruction.Create(OpCodes.Ceq), Instruction.Create(OpCodes.Brtrue, slow)];
        Instruction ValueA() => read ? Instruction.Create(OpCodes.Ldloc, calculated) : Instruction.Create(OpCodes.Ldarg, input);
        Add(Instruction.Create(OpCodes.Ldarg, flag), Instruction.Create(OpCodes.Brfalse, second));
        Add(LoadTarget(), Instruction.Create(OpCodes.Ldfld, Items), Instruction.Create(OpCodes.Stloc, arrayA));
        Instruction[] reads = read ? [Instruction.Create(OpCodes.Ldarg, source), Instruction.Create(OpCodes.Ldfld, SourceValue), Instruction.Create(OpCodes.Stloc, readValue)] : [];
        Add(reads); Add(VersionCode()); Add(LoadTarget(), Instruction.Create(OpCodes.Callvirt, Count), Instruction.Create(OpCodes.Stloc, sizeA));
        Instruction[] calculation = read ? [Instruction.Create(OpCodes.Ldloc, readValue), Instruction.Create(OpCodes.Ldc_I4, 2), Instruction.Create(OpCodes.Add), Instruction.Create(OpCodes.Stloc, calculated)] : [];
        Add(calculation); Add(CapacityCode(arrayA, sizeA, slowA));
        Add(Instruction.Create(OpCodes.Nop), LoadTarget(), Instruction.Create(OpCodes.Ldloc, sizeA), Instruction.Create(OpCodes.Ldc_I4, 1), Instruction.Create(OpCodes.Add), Instruction.Create(OpCodes.Stfld, Size), Instruction.Create(OpCodes.Ldloc, arrayA), Instruction.Create(OpCodes.Ldloc, sizeA), ValueA(), Instruction.Create(OpCodes.Stelem_Any, Int));
        var endA = Instruction.Create(OpCodes.Br, join); Add(endA, second);
        Add(LoadTarget(), Instruction.Create(OpCodes.Ldfld, Items), Instruction.Create(OpCodes.Stloc, arrayB));
        var versionB = VersionCode(); Add(versionB); Add(LoadTarget(), Instruction.Create(OpCodes.Callvirt, Count), Instruction.Create(OpCodes.Stloc, sizeB));
        var capacityB = CapacityCode(arrayB, sizeB, slowB); Add(capacityB);
        Add(Instruction.Create(OpCodes.Nop), LoadTarget(), Instruction.Create(OpCodes.Ldloc, sizeB), Instruction.Create(OpCodes.Ldc_I4, 1), Instruction.Create(OpCodes.Add), Instruction.Create(OpCodes.Stfld, Size), Instruction.Create(OpCodes.Ldloc, arrayB), Instruction.Create(OpCodes.Ldloc, sizeB), Instruction.Create(OpCodes.Ldc_I4, constant), Instruction.Create(OpCodes.Stelem_Any, Int), Instruction.Create(OpCodes.Br, join));
        Add(slowA, ValueA(), Instruction.Create(OpCodes.Stloc, phi), Instruction.Create(OpCodes.Br, shared));
        Add(slowB, Instruction.Create(OpCodes.Ldc_I4, constant), Instruction.Create(OpCodes.Stloc, phi));
        var resize = Instruction.Create(OpCodes.Callvirt, Resize); Add(shared, LoadTarget(), Instruction.Create(OpCodes.Ldloc, phi), resize, join, LoadTarget(), Instruction.Create(OpCodes.Callvirt, Count), Instruction.Create(OpCodes.Ret));
        return new Case(method, versionB, capacityB, reads, calculation, endA, slowA, slowB, shared, resize, join, phi, other, arrayA, sizeB);
    }
    public void Dispose() { Assembly.Dispose(); Resolver.Dispose(); }
}
