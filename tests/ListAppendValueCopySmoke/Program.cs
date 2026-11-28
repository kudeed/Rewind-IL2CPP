using System.Collections;
using System.Numerics;
using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;
using Rewind.Output;
using TypeAttributes = Mono.Cecil.TypeAttributes;
using MethodAttributes = Mono.Cecil.MethodAttributes;
using FieldAttributes = Mono.Cecil.FieldAttributes;
using ParameterAttributes = Mono.Cecil.ParameterAttributes;

if (args.Contains("--capture-only", StringComparer.Ordinal)) { ValueCaptureCases.Run(); return; }

using var fixture = new Fixtures();
int positive = 0, negative = 0, runtime = 0;
string Shape(MethodDefinition method) => string.Join("\n", method.Body.Instructions.Select(i => i.OpCode.Code + ":" + i.Operand));
void Good(string name, bool read = false, bool repeated = false)
{
    var f = fixture.Create(name, read, repeated);
    if (ListAppendIlFolding.Run(f.Method.Body) != 1) throw new Exception(name + ": expected complete copy fold");
    if (f.Method.Body.Instructions.Any(i => i.Operand is FieldReference field && field.DeclaringType.FullName.StartsWith("System.Collections.Generic.List`1", StringComparison.Ordinal)) ||
        f.Method.Body.Instructions.Any(i => i.Operand is MethodReference m && m.Name == "AddWithResize"))
        throw new Exception(name + ": private List access remains");
    if (ListAppendIlFolding.Run(f.Method.Body) != 0) throw new Exception(name + ": not idempotent");
    positive++;
}
void Bad(string name, Action<Case> change, Action? reset = null)
{
    var f = fixture.Create(name);
    change(f);
    string before = Shape(f.Method); int locals = f.Method.Body.Variables.Count;
    if (ListAppendIlFolding.Run(f.Method.Body) != 0 || Shape(f.Method) != before || f.Method.Body.Variables.Count != locals)
        throw new Exception(name + ": rejected case changed");
    reset?.Invoke(); fixture.Host.Methods.Remove(f.Method); negative++;
}
Good("CompleteNestedValue");
Good("PreVersionArrayField", read: true);
Good("RedundantWritePreserved", repeated: true);
Bad("MissingComponent", f => f.RemoveWrite(fixture.Z));
Bad("MissingWholeField", f => f.RemoveWrite(fixture.Uv));
Bad("ExplicitRootLayout", _ => fixture.Vertex.Attributes = (fixture.Vertex.Attributes & ~TypeAttributes.LayoutMask) | TypeAttributes.ExplicitLayout,
    () => fixture.Vertex.Attributes = (fixture.Vertex.Attributes & ~TypeAttributes.LayoutMask) | TypeAttributes.SequentialLayout);
FieldDefinition? extra = null;
Bad("ReferencePayload", _ => { extra = new FieldDefinition("reference", FieldAttributes.Public, fixture.Module.TypeSystem.Object); fixture.Vertex.Fields.Add(extra); },
    () => fixture.Vertex.Fields.Remove(extra!));
Bad("ReadonlyDestinationField", _ => fixture.Position.IsInitOnly = true, () => fixture.Position.IsInitOnly = false);
Bad("WrongClrFieldType", f => f.Method.Body.Instructions.First(i => i.OpCode.Code == Code.Stfld && i.Operand == fixture.X).Operand =
    new FieldReference(fixture.X.Name, fixture.Module.TypeSystem.Double, fixture.X.DeclaringType));
Bad("UnknownCallbackAfterVersion", f => f.InsertInFast(Instruction.Create(OpCodes.Call, fixture.Observer)));
Bad("IntegerDivideCanThrow", f => f.InsertInFast(Instruction.Create(OpCodes.Ldarg, f.Packed), Instruction.Create(OpCodes.Ldc_I4, 0),
    Instruction.Create(OpCodes.Div), Instruction.Create(OpCodes.Stloc, f.Scratch)));
Bad("CheckedArithmeticCanThrow", f => f.InsertInFast(Instruction.Create(OpCodes.Ldarg, f.Packed), Instruction.Create(OpCodes.Ldc_I4, int.MaxValue),
    Instruction.Create(OpCodes.Add_Ovf), Instruction.Create(OpCodes.Stloc, f.Scratch)));
Bad("ThrowingReferenceRead", f =>
{
    var holder = new ParameterDefinition("holder", ParameterAttributes.None, fixture.Holder); f.Method.Parameters.Add(holder);
    f.InsertInFast(Instruction.Create(OpCodes.Ldarg, holder), Instruction.Create(OpCodes.Ldfld, fixture.HolderValue), Instruction.Create(OpCodes.Stloc, f.Scratch));
});
Bad("ArrayReadAfterVersion", f => f.InsertInFast(Instruction.Create(OpCodes.Ldarg, f.Source), Instruction.Create(OpCodes.Ldarg, f.Index),
    Instruction.Create(OpCodes.Ldelem_Any, fixture.Vector), Instruction.Create(OpCodes.Stloc, f.SourceValue)));
Bad("AppendElementReadback", f =>
{
    var at = f.FastWrites.First(i => i.Operand == fixture.X).Previous!;
    var il = f.Method.Body.GetILProcessor();
    foreach (var i in f.Root().Concat(new[] { Instruction.Create(OpCodes.Ldflda, fixture.Position), Instruction.Create(OpCodes.Ldfld, fixture.X) })) il.InsertBefore(at, i);
    il.Remove(at);
});
Bad("WrongArrayReceiver", f => f.FastRoots[1].Operand = f.OtherArray);
Bad("WrongElementIndex", f => f.FastRoots[1].Next!.Operand = f.Scratch);
Bad("AddressEscapes", f =>
{
    var pointer = new VariableDefinition(new ByReferenceType(fixture.Vertex)); f.Method.Body.Variables.Add(pointer);
    f.InsertInFast(f.Root().Concat(new[] { Instruction.Create(OpCodes.Stloc, pointer) }).ToArray());
});
Bad("OutsideArrayUse", f => f.Method.Body.GetILProcessor().InsertBefore(f.Join.Next!, Instruction.Create(OpCodes.Ldloc, f.Array)));
Bad("OutsideCountUse", f => f.Method.Body.GetILProcessor().InsertBefore(f.Join.Next!, Instruction.Create(OpCodes.Ldloc, f.Count)));
Bad("OutsideInteriorEntry", f => f.Method.Body.GetILProcessor().InsertBefore(f.Method.Body.Instructions[0], Instruction.Create(OpCodes.Br, f.FastRoots[1])));
Bad("WrongUnsignedCapacityDecision", f => f.Method.Body.Instructions.Single(i => i.OpCode.Code == Code.Cgt_Un).OpCode = OpCodes.Cgt);
Bad("UninitializedLocals", f => f.Method.Body.InitLocals = false);
Bad("ExceptionRegion", f => f.Method.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
    { TryStart = f.Method.Body.Instructions[0], TryEnd = f.Join, HandlerStart = f.Join, HandlerEnd = null, CatchType = fixture.Module.ImportReference(typeof(Exception)) }));
Bad("PrivateClrField", _ => fixture.Position.IsPublic = false, () => fixture.Position.IsPublic = true);
Bad("PartialExplicitPayload", f =>
{
    f.RemoveWrite(fixture.ColorField);
    foreach (var field in fixture.Channels)
    {
        var sequence = f.Root().Concat(new[] { Instruction.Create(OpCodes.Ldflda, fixture.ColorField), Instruction.Create(OpCodes.Ldc_I4, 0), Instruction.Create(OpCodes.Stfld, field) }).ToArray();
        foreach (var instruction in sequence) f.Method.Body.GetILProcessor().InsertBefore(f.FastEnd, instruction);
    }
});
Bad("UnknownConstructor", f => f.Method.Body.Instructions.First(i => i.OpCode.Code == Code.Newobj).Operand = fixture.UntrustedCtor);
Bad("SlowSideEffect", f => f.Method.Body.GetILProcessor().InsertBefore(f.Slow.Next!, Instruction.Create(OpCodes.Call, fixture.Observer)));
Bad("UnexpectedSlowControlFlow", f => f.Method.Body.GetILProcessor().InsertBefore(f.Slow.Next!, Instruction.Create(OpCodes.Br, f.Join)));
Bad("AliasedListLocalAddress", f => f.Method.Body.GetILProcessor().InsertBefore(f.Join.Next!, Instruction.Create(OpCodes.Ldloca, f.Count)));

using var stream = new MemoryStream(); fixture.Assembly.Write(stream);
var loaded = System.Reflection.Assembly.Load(stream.ToArray());
Type host = loaded.GetType("Fixture.Host", true)!, vertexType = loaded.GetType("Fixture.Vertex", true)!, colorType = loaded.GetType("Fixture.ColorBits", true)!;
Type listType = typeof(List<>).MakeGenericType(vertexType);
var versionField = listType.GetField("_version", BindingFlags.Instance | BindingFlags.NonPublic)!;
var capacityProperty = listType.GetProperty("Capacity")!;
var getEnumerator = listType.GetMethod("GetEnumerator", Type.EmptyTypes)!;
object Vertex(float x, float y, float z, uint packed)
{
    object color = Activator.CreateInstance(colorType)!;
    for (int i = 0; i < 4; i++) colorType.GetField(new[] { "r", "g", "b", "a" }[i])!.SetValue(color, (byte)(packed >> (i * 8)));
    object value = Activator.CreateInstance(vertexType)!;
    vertexType.GetField("position")!.SetValue(value, new Vector3(x, y, z));
    vertexType.GetField("uv")!.SetValue(value, new Vector4(x, y, z, -0.0f));
    vertexType.GetField("color")!.SetValue(value, color); return value;
}
string Bits(object value)
{
    var pos = (Vector3)vertexType.GetField("position")!.GetValue(value)!;
    var uv = (Vector4)vertexType.GetField("uv")!.GetValue(value)!;
    var color = vertexType.GetField("color")!.GetValue(value)!;
    return string.Join(",", new[] { pos.X, pos.Y, pos.Z, uv.X, uv.Y, uv.Z, uv.W }.Select(BitConverter.SingleToInt32Bits)) + ":" +
        string.Join(",", new[] { "r", "g", "b", "a" }.Select(n => colorType.GetField(n)!.GetValue(color))) + ":" +
        colorType.GetField("packed", BindingFlags.Instance | BindingFlags.NonPublic)!.GetValue(color);
}
void Invoke(MethodInfo method, IList? list, Vector3[]? source, int index, float x, float y, float z, uint packed) =>
    method.Invoke(null, new object?[] { list, source, index, x, y, z, packed });
foreach (string name in new[] { "CompleteNestedValue", "PreVersionArrayField", "RedundantWritePreserved" })
foreach (int initialCapacity in new[] { 0, 1, 4, 64 })
{
    MethodInfo method = host.GetMethod(name)!;
    var actual = (IList)Activator.CreateInstance(listType, new object[] { initialCapacity })!;
    var expected = (IList)Activator.CreateInstance(listType, new object[] { initialCapacity })!;
    for (int n = 0; n < 40; n++)
    {
        float x = n % 7 == 0 ? -0.0f : n % 11 == 0 ? BitConverter.Int32BitsToSingle(unchecked((int)0x7FC12345)) : n - 12.5f;
        float y = n + 0.25f, z = -n - 0.5f; uint color = unchecked(0xF0804000U + (uint)(n * 0x10201));
        var source = new[] { new Vector3(x, 91f, 92f) };
        IEnumerator old = (IEnumerator)getEnumerator.Invoke(actual, null)!; old.MoveNext();
        int version = (int)versionField.GetValue(actual)!;
        Invoke(method, actual, source, 0, x, y, z, color);
        expected.Add(Vertex(x, y, z, color));
        if (actual.Count != expected.Count || (int)capacityProperty.GetValue(actual)! != (int)capacityProperty.GetValue(expected)! ||
            (int)versionField.GetValue(actual)! != unchecked(version + 1)) throw new Exception(name + ": count/capacity/version changed");
        for (int j = 0; j < actual.Count; j++) if (Bits(actual[j]!) != Bits(expected[j]!)) throw new Exception(name + ": field bits changed");
        bool invalidated = false; try { old.MoveNext(); } catch (InvalidOperationException) { invalidated = true; }
        if (!invalidated) throw new Exception(name + ": prior enumerator stayed valid");
        runtime++;
    }
}
var readMethod = host.GetMethod("PreVersionArrayField")!;
foreach (int capacity in new[] { 1, 8 })
{
    var actual = (IList)Activator.CreateInstance(listType, new object[] { capacity })!; actual.Add(Vertex(1, 2, 3, 0xFE80AA12));
    foreach (var failure in new (Vector3[]? Source, int Index, Type Exception)[] { (null, 0, typeof(NullReferenceException)), ([], 0, typeof(IndexOutOfRangeException)), (new Vector3[1], -1, typeof(IndexOutOfRangeException)) })
    {
        int version = (int)versionField.GetValue(actual)!, originalCapacity = (int)capacityProperty.GetValue(actual)!;
        string oldValue = Bits(actual[0]!); IEnumerator old = (IEnumerator)getEnumerator.Invoke(actual, null)!;
        try { Invoke(readMethod, actual, failure.Source, failure.Index, 4, 5, 6, 7); throw new Exception("Expected source read failure"); }
        catch (TargetInvocationException e) when (e.InnerException?.GetType() == failure.Exception) { }
        if ((int)versionField.GetValue(actual)! != version || actual.Count != 1 || (int)capacityProperty.GetValue(actual)! != originalCapacity || Bits(actual[0]!) != oldValue || !old.MoveNext())
            throw new Exception("Pre-version source exception changed list state or enumerator");
        runtime++;
    }
}
try { Invoke(readMethod, null, [], 9, 1, 2, 3, 4); throw new Exception("Expected receiver null first"); }
catch (TargetInvocationException e) when (e.InnerException is NullReferenceException) { runtime++; }
Console.WriteLine($"LIST_VALUE_COPY_SMOKE_PASS positive={positive} negative={negative} runtime={runtime} full_field_bits=true growth_and_spare_capacity=true version_exactly_once=true enumerator_invalidated=true source_exceptions_before_version=true receiver_null_first=true");

ValueCaptureCases.Run();

sealed record Case(MethodDefinition Method, VariableDefinition Array, VariableDefinition Count, VariableDefinition OtherArray,
    VariableDefinition Scratch, VariableDefinition SourceValue, ParameterDefinition Source, ParameterDefinition Index, ParameterDefinition Packed,
    List<Instruction> FastRoots, List<Instruction> FastWrites, Instruction FastEnd, Instruction Slow, Instruction Join, TypeReference Element)
{
    public Instruction[] Root() => [Instruction.Create(OpCodes.Ldloc, Array), Instruction.Create(OpCodes.Ldloc, Count), Instruction.Create(OpCodes.Ldelema, Element)];
    public void InsertInFast(params Instruction[] instructions)
    { foreach (var i in instructions) Method.Body.GetILProcessor().InsertBefore(FastRoots[1], i); }
    public void RemoveWrite(FieldReference field)
    {
        Instruction store = FastWrites.First(i => i.Operand == field); var il = Method.Body.GetILProcessor();
        int at = FastRoots.FindLastIndex(root => Method.Body.Instructions.IndexOf(root) < Method.Body.Instructions.IndexOf(store));
        Instruction? current = FastRoots[at];
        while (current != null) { var next = current.Next; il.Remove(current); if (current == store) break; current = next; }
    }
}

sealed class Fixtures : IDisposable
{
    public readonly DefaultAssemblyResolver Resolver = new();
    public readonly AssemblyDefinition Assembly;
    public ModuleDefinition Module => Assembly.MainModule;
    public readonly TypeDefinition Host, Vertex, Color, Holder, Untrusted;
    public readonly TypeReference Vector, Vector4;
    public readonly FieldReference X, Y, Z;
    public readonly FieldDefinition Position, Uv, ColorField, HolderValue;
    public readonly FieldDefinition[] Channels;
    public readonly MethodDefinition Observer, UntrustedCtor;
    private readonly MethodReference Ctor3, Ctor4;
    public Fixtures()
    {
        Resolver.AddSearchDirectory(Path.GetDirectoryName(typeof(List<>).Assembly.Location)!);
        Assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("ListValueCopyFixtures", new Version(1, 0)), "ListValueCopyFixtures",
            new ModuleParameters { Kind = ModuleKind.Dll, AssemblyResolver = Resolver, Runtime = TargetRuntime.Net_4_0 });
        var m = Module; var valueBase = m.ImportReference(typeof(ValueType));
        Host = new TypeDefinition("Fixture", "Host", TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed, m.TypeSystem.Object); m.Types.Add(Host);
        Vertex = new TypeDefinition("Fixture", "Vertex", TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout | TypeAttributes.BeforeFieldInit, valueBase); m.Types.Add(Vertex);
        Color = new TypeDefinition("Fixture", "ColorBits", TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.ExplicitLayout | TypeAttributes.BeforeFieldInit, valueBase) { ClassSize = 4, PackingSize = 1 }; m.Types.Add(Color);
        Channels = new[] { "r", "g", "b", "a" }.Select((name, i) => new FieldDefinition(name, FieldAttributes.Public, m.TypeSystem.Byte) { Offset = i }).ToArray();
        foreach (var field in Channels) Color.Fields.Add(field);
        Color.Fields.Add(new FieldDefinition("packed", FieldAttributes.Private, m.TypeSystem.UInt32) { Offset = 0 });
        Vector = m.ImportReference(typeof(Vector3)); Vector4 = m.ImportReference(typeof(System.Numerics.Vector4));
        X = m.ImportReference(typeof(Vector3).GetField("X")!); Y = m.ImportReference(typeof(Vector3).GetField("Y")!); Z = m.ImportReference(typeof(Vector3).GetField("Z")!);
        Position = new FieldDefinition("position", FieldAttributes.Public, Vector); Uv = new FieldDefinition("uv", FieldAttributes.Public, Vector4); ColorField = new FieldDefinition("color", FieldAttributes.Public, Color);
        Vertex.Fields.Add(Position); Vertex.Fields.Add(Uv); Vertex.Fields.Add(ColorField);
        Ctor3 = m.ImportReference(typeof(Vector3).GetConstructor(new[] { typeof(float), typeof(float), typeof(float) })!);
        Ctor4 = m.ImportReference(typeof(System.Numerics.Vector4).GetConstructor(new[] { typeof(float), typeof(float), typeof(float), typeof(float) })!);
        Observer = new MethodDefinition("Observer", MethodAttributes.Public | MethodAttributes.Static, m.TypeSystem.Void); Host.Methods.Add(Observer); Observer.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
        Holder = new TypeDefinition("Fixture", "Holder", TypeAttributes.Public | TypeAttributes.Class, m.TypeSystem.Object); m.Types.Add(Holder);
        HolderValue = new FieldDefinition("value", FieldAttributes.Public, m.TypeSystem.Int32); Holder.Fields.Add(HolderValue);
        Untrusted = new TypeDefinition("Fixture", "CustomValue", TypeAttributes.Public | TypeAttributes.SequentialLayout | TypeAttributes.Sealed, valueBase); m.Types.Add(Untrusted);
        Untrusted.Fields.Add(new FieldDefinition("x", FieldAttributes.Public, m.TypeSystem.Single));
        UntrustedCtor = new MethodDefinition(".ctor", MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, m.TypeSystem.Void); Untrusted.Methods.Add(UntrustedCtor);
        UntrustedCtor.Body.Instructions.Add(Instruction.Create(OpCodes.Call, Observer)); UntrustedCtor.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
    }
    public Case Create(string name, bool sourceRead = false, bool repeated = false)
    {
        var m = Module; var open = m.ImportReference(typeof(List<>)); var list = new GenericInstanceType(open); list.GenericArguments.Add(Vertex);
        var generic = open.GenericParameters[0]; var items = new FieldReference("_items", new ArrayType(generic), list);
        var version = new FieldReference("_version", m.TypeSystem.Int32, list); var size = new FieldReference("_size", m.TypeSystem.Int32, list);
        var count = new MethodReference("get_Count", m.TypeSystem.Int32, list) { HasThis = true };
        var resize = new MethodReference("AddWithResize", m.TypeSystem.Void, list) { HasThis = true }; resize.Parameters.Add(new ParameterDefinition(generic));
        var method = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static, m.TypeSystem.Void); Host.Methods.Add(method); method.Body.InitLocals = true;
        ParameterDefinition Param(string n, TypeReference type) { var p = new ParameterDefinition(n, ParameterAttributes.None, type); method.Parameters.Add(p); return p; }
        var target = Param("list", list); var source = Param("source", new ArrayType(Vector)); var index = Param("index", m.TypeSystem.Int32);
        var x = Param("x", m.TypeSystem.Single); var y = Param("y", m.TypeSystem.Single); var z = Param("z", m.TypeSystem.Single); var packed = Param("packed", m.TypeSystem.UInt32);
        VariableDefinition Local(TypeReference type) { var v = new VariableDefinition(type); method.Body.Variables.Add(v); return v; }
        var array = Local(new ArrayType(Vertex)); var oldCount = Local(m.TypeSystem.Int32); var slowValue = Local(Vertex);
        var colorFast = Local(Color); var colorSlow = Local(Color); var input = Local(m.TypeSystem.Single);
        var other = Local(new ArrayType(Vertex)); var scratch = Local(m.TypeSystem.Int32); var sourceValue = Local(Vector);
        var il = method.Body.GetILProcessor(); void E(OpCode op) => il.Emit(op);
        void L(VariableDefinition v) => il.Emit(OpCodes.Ldloc, v); void A(ParameterDefinition p) => il.Emit(OpCodes.Ldarg, p);
        Instruction slow = Instruction.Create(OpCodes.Nop), join = Instruction.Create(OpCodes.Nop);
        A(target); il.Emit(OpCodes.Ldfld, items); il.Emit(OpCodes.Stloc, array);
        if (sourceRead) { A(source); A(index); il.Emit(OpCodes.Ldelema, Vector); il.Emit(OpCodes.Ldfld, X); il.Emit(OpCodes.Stloc, input); }
        A(target); A(target); il.Emit(OpCodes.Ldfld, version); il.Emit(OpCodes.Ldc_I4, 1); E(OpCodes.Add); il.Emit(OpCodes.Stfld, version);
        A(target); il.Emit(OpCodes.Callvirt, count); il.Emit(OpCodes.Stloc, oldCount);
        L(array); E(OpCodes.Ldlen); E(OpCodes.Conv_I4); L(oldCount); E(OpCodes.Cgt_Un); il.Emit(OpCodes.Ldc_I4, 0); E(OpCodes.Ceq); il.Emit(OpCodes.Brtrue, slow);
        E(OpCodes.Nop); A(target); L(oldCount); il.Emit(OpCodes.Ldc_I4, 1); E(OpCodes.Add); il.Emit(OpCodes.Stfld, size);
        var roots = new List<Instruction>(); var stores = new List<Instruction>();
        void Root()
        {
            var at = Instruction.Create(OpCodes.Ldloc, array); roots.Add(at); il.Append(at); L(oldCount); il.Emit(OpCodes.Ldelema, Vertex);
        }
        void Store(FieldReference field) { var at = Instruction.Create(OpCodes.Stfld, field); stores.Add(at); il.Append(at); }
        void InputX() { if (sourceRead) L(input); else A(x); }
        if (repeated) { Root(); il.Emit(OpCodes.Ldflda, Position); il.Emit(OpCodes.Ldc_R4, 999f); Store(X); }
        Root(); il.Emit(OpCodes.Ldflda, Position); InputX(); Store(X);
        Root(); il.Emit(OpCodes.Ldflda, Position); A(y); Store(Y);
        Root(); il.Emit(OpCodes.Ldflda, Position); A(z); Store(Z);
        Root(); InputX(); A(y); A(z); il.Emit(OpCodes.Ldc_R4, -0.0f); il.Emit(OpCodes.Newobj, Ctor4); Store(Uv);
        void ColorInit(VariableDefinition local)
        {
            for (int c = 0; c < 4; c++)
            {
                il.Emit(OpCodes.Ldloca, local); A(packed);
                if (c != 0) { il.Emit(OpCodes.Ldc_I4, c * 8); E(OpCodes.Shr_Un); }
                E(OpCodes.Conv_U1); il.Emit(OpCodes.Stfld, Channels[c]);
            }
        }
        ColorInit(colorFast); Root(); L(colorFast); Store(ColorField);
        Instruction fastEnd = Instruction.Create(OpCodes.Br, join); il.Append(fastEnd); il.Append(slow);
        il.Emit(OpCodes.Ldloca, slowValue); InputX(); A(y); A(z); il.Emit(OpCodes.Newobj, Ctor3); il.Emit(OpCodes.Stfld, Position);
        il.Emit(OpCodes.Ldloca, slowValue); InputX(); A(y); A(z); il.Emit(OpCodes.Ldc_R4, -0.0f); il.Emit(OpCodes.Newobj, Ctor4); il.Emit(OpCodes.Stfld, Uv);
        ColorInit(colorSlow); il.Emit(OpCodes.Ldloca, slowValue); L(colorSlow); il.Emit(OpCodes.Stfld, ColorField);
        A(target); L(slowValue); il.Emit(OpCodes.Callvirt, resize); il.Append(join); E(OpCodes.Ret);
        return new Case(method, array, oldCount, other, scratch, sourceValue, source, index, packed, roots, stores, fastEnd, slow, join, Vertex);
    }
    public void Dispose() { Assembly.Dispose(); Resolver.Dispose(); }
}
