using Mono.Cecil;
using Rewind.Metadata;
using Rewind.Analysis.Hir;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Output;
using Rewind.Runtime;
using System.Reflection;

static void Check(bool condition, string message) { if (!condition) throw new Exception(message); }
if (args.Length != 2) throw new ArgumentException("Expected native binary and metadata fixture paths");
Check(UnityVersion.TryParse("6000.3.11f1", out var unity), "Unity version");
var model = Il2CppModel.Load(NativeImage.Load(File.ReadAllBytes(args[0]), Path.GetFileName(args[0])), File.ReadAllBytes(args[1]), unity);
var sf = model.Sigs;
var i4 = sf.Primitive(Il2CppTypeEnum.I4); var i8 = sf.Primitive(Il2CppTypeEnum.I8);
var u4 = sf.Primitive(Il2CppTypeEnum.U4); var u8 = sf.Primitive(Il2CppTypeEnum.U8);
var r8 = sf.Primitive(Il2CppTypeEnum.R8); var boolean = sf.Primitive(Il2CppTypeEnum.Boolean);
var assembly = new AssemblyModel { Name = "NumericLocalFixture" };
var owner = new TypeDef { Index = -1, Name = "Numeric", Namespace = "Fixture", Assembly = assembly };
owner.Sig = sf.TypeDef(owner);
using var output = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition(assembly.Name, new Version(1, 0)), assembly.Name, ModuleKind.Dll);
var module = output.MainModule;
var type = new TypeDefinition("Fixture", "Numeric", Mono.Cecil.TypeAttributes.Public | Mono.Cecil.TypeAttributes.Abstract | Mono.Cecil.TypeAttributes.Sealed, module.TypeSystem.Object);
module.Types.Add(type);
var emitter = new AssemblyEmitter(model); emitter.Build();
var bodies = new BodyEmitter(emitter, model);
HArg Arg(int index, TypeSig type) => new(index) { Type = type };
HLocal Read(HVar variable) => new(variable); // Deliberately no expression annotation.
HMethod Method(string name, TypeSig result, params TypeSig[] parameters) => new()
{
    Method = new MethodDef { Name = name, DeclaringType = owner, Flags = MethodDef.Static,
        ReturnType = result, Parameters = parameters.Select(t => new ParamDef { Type = t }).ToArray() }
};
void Emit(HMethod method, params HStmt[] statements)
{
    var target = new MethodDefinition(method.Method.Name, Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static,
        emitter.Import(module, method.Method.ReturnType));
    foreach (var p in method.Method.Parameters) target.Parameters.Add(new ParameterDefinition(emitter.Import(module, p.Type)));
    type.Methods.Add(target); method.Blocks.Add(new HBlock { Id = 0, Statements = statements.ToList() });
    string? error = bodies.EmitTo(method.Method, method, target);
    Check(error == null, method.Method.Name + ": " + error);
}
var shift = Method("Shift", i4, i4, i8); var count = shift.NewLocal(i8);
Emit(shift, new HAssign(Read(count), Arg(1, i8)), new HReturn(new HBinary(HBinaryOp.Shr, Arg(0, i4), Read(count)) { Type = i4 }));
var add = Method("Add", i8, i8); var wide = add.NewLocal(i8);
Emit(add, new HAssign(Read(wide), Arg(0, i8)), new HReturn(new HBinary(HBinaryOp.Add, Read(wide), new HConst(1, i4)) { Type = i8 }));
var array = Method("Index", i4, sf.SzArray(i4), i8); var index = array.NewLocal(i8);
Emit(array, new HAssign(Read(index), Arg(1, i8)), new HReturn(new HElement { Array = Arg(0, sf.SzArray(i4)), Index = Read(index), Type = i4 }));
var unsigned = Method("Unsigned", u8, u4); var small = unsigned.NewLocal(u4);
Emit(unsigned, new HAssign(Read(small), Arg(0, u4)), new HReturn(new HBinary(HBinaryOp.Add, Read(small), new HConst(0x100000000L, u8)) { Type = u8 }));
var compare = Method("Less", boolean, u8); var compared = compare.NewLocal(u8);
Emit(compare, new HAssign(Read(compared), Arg(0, u8)), new HReturn(new HCompare(HCompareOp.Lt, Read(compared), new HConst(1, i4)) { Type = boolean }));
var store = Method("Store", i8, i4); var from = store.NewLocal(i4); var to = store.NewLocal(i8);
Emit(store, new HAssign(Read(from), Arg(0, i4)), new HAssign(Read(to), Read(from)), new HReturn(Read(to)));
var narrow = Method("Narrow", i4, i8); var narrowed = narrow.NewLocal(i8);
Emit(narrow, new HAssign(Read(narrowed), Arg(0, i8)), new HReturn(Read(narrowed)));
var floating = Method("Floating", r8, r8); var real = floating.NewLocal(r8);
Emit(floating, new HAssign(Read(real), Arg(0, r8)), new HReturn(new HBinary(HBinaryOp.Add, Read(real), new HConst(0.5d, r8)) { Type = r8 }));
HBinary Next(HVar variable) => new(HBinaryOp.Add, Read(variable), new HConst(1, i4)) { Type = i4 };
var indexNext = Method("IndexNext", i4, sf.SzArray(i4), i8); var nextIndex = indexNext.NewLocal(i8);
Emit(indexNext, new HAssign(Read(nextIndex), Arg(1, i8)), new HReturn(new HElement { Array = Arg(0, sf.SzArray(i4)), Index = Next(nextIndex), Type = i4 }));
var shiftNext = Method("ShiftNext", i4, i4, i8); var nextCount = shiftNext.NewLocal(i8);
Emit(shiftNext, new HAssign(Read(nextCount), Arg(1, i8)), new HReturn(new HBinary(HBinaryOp.Shr, Arg(0, i4), Next(nextCount)) { Type = i4 }));
var narrowNext = Method("NarrowNext", i4, i8); var nextValue = narrowNext.NewLocal(i8);
Emit(narrowNext, new HAssign(Read(nextValue), Arg(0, i8)), new HReturn(Next(nextValue)));
foreach (string name in new[] { "IndexNext", "ShiftNext", "NarrowNext" })
    Check(type.Methods.Single(m => m.Name == name).Body.Instructions.Any(i => i.OpCode == Mono.Cecil.Cil.OpCodes.Conv_I4), name + " must adapt its actual int64 stack result to int32");
// End-to-end fixture: native array-data pointer -> stack spill -> indexed
// managed ref load/store. Use the real HIR builder and emitted IL.
var refProgram = new Rewind.Analysis.ProgramAnalysis(model, new Rewind.Analysis.Runtime.RuntimeHelpers());
HMethod RecoverSpilledRef(string name, TypeSig element, bool write, int stride = 0, int displacement = 0, bool numericWrite = false)
{
    var method = Method(name, element, sf.SzArray(element), i8, element);
    var fn = new Rewind.Analysis.Ir.Function { Regs = Rewind.Analysis.Ir.RegisterModel.Arm64 };
    var block = new Rewind.Analysis.Ir.Block { Id = 0 }; fn.Blocks = [block];
    Rewind.Analysis.Ir.Node Param(int position, Rewind.Analysis.Ir.VT bits = Rewind.Analysis.Ir.VT.I64)
    {
        var node = fn.NewNode(Rewind.Analysis.Ir.Op.Param, bits, null);
        node.Imm = position; fn.Params[position] = node; return node;
    }
    var source = Param(0); var at = Param(1);
    var replacement = Param(2, refProgram.Layouts.SizeOf(element).Size == 4 ? Rewind.Analysis.Ir.VT.I32 : Rewind.Analysis.Ir.VT.I64);
    var sp = Param(fn.Regs.StackPointer);
    Rewind.Analysis.Ir.Node Constant(long value)
    {
        var node = fn.NewNode(Rewind.Analysis.Ir.Op.Const, Rewind.Analysis.Ir.VT.I64, null); node.Imm = value; return node;
    }
    Rewind.Analysis.Ir.Node Add(Rewind.Analysis.Ir.Op op, Rewind.Analysis.Ir.VT bits, params Rewind.Analysis.Ir.Node[] input)
    {
        var node = fn.NewNode(op, bits, block, input); block.Nodes.Add(node); return node;
    }
    var data = Add(Rewind.Analysis.Ir.Op.Add, Rewind.Analysis.Ir.VT.I64, source, Constant(32));
    var slot = Add(Rewind.Analysis.Ir.Op.Add, Rewind.Analysis.Ir.VT.I64, sp, Constant(-32));
    Add(Rewind.Analysis.Ir.Op.Store, Rewind.Analysis.Ir.VT.None, slot, data);
    if (numericWrite) Add(Rewind.Analysis.Ir.Op.Store, Rewind.Analysis.Ir.VT.None, slot, Constant(17));
    var read = Add(Rewind.Analysis.Ir.Op.Load, Rewind.Analysis.Ir.VT.I64, slot);
    var scaled = Add(Rewind.Analysis.Ir.Op.Mul, Rewind.Analysis.Ir.VT.I64, at, Constant(stride == 0 ? refProgram.Layouts.SizeOf(element).Size : stride));
    var address = Add(Rewind.Analysis.Ir.Op.Add, Rewind.Analysis.Ir.VT.I64, read, scaled);
    if (displacement != 0) address = Add(Rewind.Analysis.Ir.Op.Add, Rewind.Analysis.Ir.VT.I64, address, Constant(displacement));
    if (write) Add(Rewind.Analysis.Ir.Op.Store, Rewind.Analysis.Ir.VT.None, address, replacement);
    var loaded = Add(Rewind.Analysis.Ir.Op.Load, refProgram.Layouts.SizeOf(element).Size == 4 ? Rewind.Analysis.Ir.VT.I32 : Rewind.Analysis.Ir.VT.I64, address);
    Add(Rewind.Analysis.Ir.Op.Return, Rewind.Analysis.Ir.VT.None, loaded);
    var lifted = new Rewind.Analysis.Recover.LiftedMethod { Method = method.Method, Function = fn,
        Abi = refProgram.Abi.For(method.Method, [], []), Normalization = new Rewind.Analysis.Recover.NormalizeResult() };
    var first = new Rewind.Analysis.Recover.HirBuilder(refProgram, lifted); first.Build();
    var second = new Rewind.Analysis.Recover.HirBuilder(refProgram, lifted, knownFrameTypes: first.RefinedFrameTypes);
    return second.Build();
}
void EmitRecovered(HMethod method)
{
    Check(method.Problems.Count == 0, method.Method.Name + ": " + string.Join(";", method.Problems));
    var target = new MethodDefinition(method.Method.Name, Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static,
        emitter.Import(module, method.Method.ReturnType));
    foreach (var p in method.Method.Parameters) target.Parameters.Add(new ParameterDefinition(emitter.Import(module, p.Type)));
    type.Methods.Add(target);
    string? error = bodies.EmitTo(method.Method, method, target); Check(error == null, method.Method.Name + ": " + error);
    Check(target.Body.Variables.Any(v => v.VariableType is ByReferenceType), method.Method.Name + " lost managed reference");
}
var obj = sf.Primitive(Il2CppTypeEnum.Object);
EmitRecovered(RecoverSpilledRef("RefRead", i4, false));
EmitRecovered(RecoverSpilledRef("RefWrite", i4, true));
EmitRecovered(RecoverSpilledRef("ObjectRead", obj, false));
EmitRecovered(RecoverSpilledRef("ObjectWrite", obj, true));
foreach (var bad in new[] { RecoverSpilledRef("WrongStride", i4, false, stride: 3),
    RecoverSpilledRef("UnalignedOffset", i4, false, displacement: 1), RecoverSpilledRef("MixedNumeric", i4, false, numericWrite: true) })
    Check(bad.Problems.Count > 0, bad.Method.Name + " unsafe pointer interpretation accepted");

// Planning allocates frame views before deciding which copy form survives.
// Exercise the real local cleanup and frame checker with dead and live views.
HMethod CheckOverlappingFrame(bool live)
{
    var fixture = Method("FrameOverlap", i8);
    var lifted = new Rewind.Analysis.Recover.LiftedMethod { Method = fixture.Method,
        Function = new Rewind.Analysis.Ir.Function { Regs = Rewind.Analysis.Ir.RegisterModel.Arm64 },
        Abi = refProgram.Abi.For(fixture.Method, [], []), Normalization = new Rewind.Analysis.Recover.NormalizeResult() };
    var builder = new Rewind.Analysis.Recover.HirBuilder(refProgram, lifted);
    const BindingFlags access = BindingFlags.Instance | BindingFlags.NonPublic;
    var builderType = builder.GetType();
    var frameVar = builderType.GetMethod("FrameVar", access)!;
    var first = (HVar)frameVar.Invoke(builder, [-32, i8])!;
    var second = (HVar)frameVar.Invoke(builder, [-30, i8])!;
    var method = (HMethod)builderType.GetField("_h", access)!.GetValue(builder)!;
    method.Blocks.Add(new HBlock { Id = 0, Statements = [
        new HAssign(Read(first), new HConst(9L, i8)),
        new HAssign(Read(second), new HConst(17L, i8)),
        new HReturn(live ? new HBinary(HBinaryOp.Add, Read(first), Read(second)) { Type = i8 } : new HConst(0L, i8))] });
    Rewind.Analysis.Recover.HirCleanup.Run(method);
    builderType.GetMethod("CheckFrameVariables", access)!.Invoke(builder, []);
    return method;
}
var deadFrame = CheckOverlappingFrame(false);
Check(deadFrame.Problems.Count == 0 && deadFrame.Locals.Count == 0, "Unused planning locals caused frame conflict");
var liveFrame = CheckOverlappingFrame(true);
Check(liveFrame.Problems.Any(p => p.StartsWith("stack memory seen as two different objects")), "Live frame overlap was hidden");
Console.WriteLine("LIVE_FRAME_CONFLICT_SMOKE_PASS dead-locals-removed live-overlap-rejected");

// The integer IR comparison must use float register bits rather than float ordering.
var rawCompareDefinitions = new List<(string Name, Rewind.Analysis.Ir.Op Op, uint Constant)>();
var r4 = sf.Primitive(Il2CppTypeEnum.R4);
foreach (var operation in new[] { Rewind.Analysis.Ir.Op.CmpEq, Rewind.Analysis.Ir.Op.CmpNe, Rewind.Analysis.Ir.Op.CmpLtS, Rewind.Analysis.Ir.Op.CmpLeS, Rewind.Analysis.Ir.Op.CmpLtU, Rewind.Analysis.Ir.Op.CmpLeU })
foreach (uint threshold in new[] { 0u, 0x7f800000u })
{
    string name = "FloatRegisterBits_" + operation + "_" + threshold.ToString("x8");
    var prototype = Method(name, boolean, r4);
    var function = new Rewind.Analysis.Ir.Function { Regs = Rewind.Analysis.Ir.RegisterModel.Arm64 };
    var block = new Rewind.Analysis.Ir.Block { Id = 0 }; function.Blocks = [block];
    var parameter = function.NewNode(Rewind.Analysis.Ir.Op.Param, Rewind.Analysis.Ir.VT.I32, null);
    parameter.Imm = Rewind.Analysis.Arm64.A64Lifter.VarV; function.Params[(int)parameter.Imm] = parameter;
    Rewind.Analysis.Ir.Node AddCompareNode(Rewind.Analysis.Ir.Op op, Rewind.Analysis.Ir.VT valueType, params Rewind.Analysis.Ir.Node[] inputs)
    { var node = function.NewNode(op, valueType, block, inputs); block.Nodes.Add(node); return node; }
    var number = AddCompareNode(Rewind.Analysis.Ir.Op.BitsToF, Rewind.Analysis.Ir.VT.F32, parameter);
    var bits = AddCompareNode(Rewind.Analysis.Ir.Op.FToBits, Rewind.Analysis.Ir.VT.I32, number);
    var constant = function.NewNode(Rewind.Analysis.Ir.Op.Const, Rewind.Analysis.Ir.VT.I32, null); constant.Imm = threshold;
    var comparedBits = AddCompareNode(operation, Rewind.Analysis.Ir.VT.I1, constant, bits);
    AddCompareNode(Rewind.Analysis.Ir.Op.Return, Rewind.Analysis.Ir.VT.None, comparedBits);
    var lifted = new Rewind.Analysis.Recover.LiftedMethod { Method = prototype.Method, Function = function,
        Abi = refProgram.Abi.For(prototype.Method, [], []), Normalization = new Rewind.Analysis.Recover.NormalizeResult() };
    var recoveredCompare = new Rewind.Analysis.Recover.HirBuilder(refProgram, lifted).Build();
    Check(recoveredCompare.Problems.Count == 0, name + ": " + string.Join(";", recoveredCompare.Problems));
    var target = new MethodDefinition(name, Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Boolean);
    target.Parameters.Add(new ParameterDefinition(module.TypeSystem.Single)); type.Methods.Add(target);
    string? error = bodies.EmitTo(prototype.Method, recoveredCompare, target); Check(error == null, name + ": " + error);
    rawCompareDefinitions.Add((name, operation, threshold));
}

using var stream = new MemoryStream(); output.Write(stream);
var runtime = Assembly.Load(stream.ToArray()).GetType("Fixture.Numeric", true)!;
uint[] registerValues = [0u, 0x80000000u, 1u, 0x80000001u, 0x007fffffu, 0x807fffffu, 0x00800000u, 0x80800000u, 0x3dcccccdu, 0xbdcccccdu, 0x3f800000u, 0xbf800000u, 0x40000000u, 0xc0000000u, 0x7f7fffffu, 0xff7fffffu, 0x7f800000u, 0xff800000u, 0x7fc12345u, 0xffc12345u, 0x7fa12345u, 0xffa12345u, 0x7fffffffu, 0xffffffffu];
int rawCompareCases = 0;
foreach (var definition in rawCompareDefinitions)
{
    var call = runtime.GetMethod(definition.Name)!.CreateDelegate<Func<float, bool>>();
    foreach (uint bits in registerValues)
    {
        bool expected = definition.Op switch
        {
            Rewind.Analysis.Ir.Op.CmpEq => definition.Constant == bits,
            Rewind.Analysis.Ir.Op.CmpNe => definition.Constant != bits,
            Rewind.Analysis.Ir.Op.CmpLtS => unchecked((int)definition.Constant) < unchecked((int)bits),
            Rewind.Analysis.Ir.Op.CmpLeS => unchecked((int)definition.Constant) <= unchecked((int)bits),
            Rewind.Analysis.Ir.Op.CmpLtU => definition.Constant < bits,
            Rewind.Analysis.Ir.Op.CmpLeU => definition.Constant <= bits,
            _ => throw new InvalidOperationException("Unreviewed comparison fixture")
        };
        Check(call(BitConverter.Int32BitsToSingle(unchecked((int)bits))) == expected, "INTEGER_COMPARE_RAW_BITS " + definition.Name + " input=" + bits.ToString("x8"));
        rawCompareCases++;
    }
}
Console.WriteLine($"INTEGER_COMPARE_RAW_BITS_SMOKE_PASS methods={rawCompareDefinitions.Count} cases={rawCompareCases} signed-zero-inf-nan-subnormal raw-bit-ordering");

var shiftCall = runtime.GetMethod("Shift")!.CreateDelegate<Func<int, long, int>>();
var addCall = runtime.GetMethod("Add")!.CreateDelegate<Func<long, long>>();
var indexCall = runtime.GetMethod("Index")!.CreateDelegate<Func<int[], long, int>>();
var unsignedCall = runtime.GetMethod("Unsigned")!.CreateDelegate<Func<uint, ulong>>();
var compareCall = runtime.GetMethod("Less")!.CreateDelegate<Func<ulong, bool>>();
var storeCall = runtime.GetMethod("Store")!.CreateDelegate<Func<int, long>>();
var narrowCall = runtime.GetMethod("Narrow")!.CreateDelegate<Func<long, int>>();
var floatCall = runtime.GetMethod("Floating")!.CreateDelegate<Func<double, double>>();
var nextIndexCall = runtime.GetMethod("IndexNext")!.CreateDelegate<Func<int[], long, int>>();
var nextShiftCall = runtime.GetMethod("ShiftNext")!.CreateDelegate<Func<int, long, int>>();
var nextNarrowCall = runtime.GetMethod("NarrowNext")!.CreateDelegate<Func<long, int>>();
int cases = 0;
foreach (long c in new[] { long.MinValue, -65L, -33L, -1L, 0L, 1L, 31L, 32L, 33L, 63L, 64L, long.MaxValue })
foreach (int value in new[] { int.MinValue, -1, 0, 1, int.MaxValue })
{ Check(shiftCall(value, c) == value >> (int)c, "shift"); Check(nextShiftCall(value, c) == value >> unchecked((int)(c + 1)), "nested shift"); cases += 2; }
foreach (long value in new[] { long.MinValue, -1L, 0L, 0x80000000L, 0xffffffffL, long.MaxValue })
{ Check(addCall(value) == unchecked(value + 1), "add"); Check(narrowCall(value) == unchecked((int)value), "narrow"); Check(nextNarrowCall(value) == unchecked((int)(value + 1)), "nested narrow"); cases += 3; }
foreach (uint value in new[] { 0U, 1U, 0x80000000U, uint.MaxValue })
{ Check(unsignedCall(value) == value + 0x100000000UL, "unsigned widening"); cases++; }
foreach (ulong value in new[] { 0UL, 1UL, 0x8000000000000000UL, ulong.MaxValue })
{ Check(compareCall(value) == value < 1, "unsigned comparison"); cases++; }
foreach (int value in new[] { int.MinValue, -1, 0, 1, int.MaxValue })
{ Check(storeCall(value) == value, "store widening"); cases++; }
int[] values = [17, 29, 43];
for (int k = 0; k < values.Length; k++) { Check(indexCall(values, k) == values[k], "index"); cases++; }
foreach (long k in new[] { -1L, 0L, 1L, 0x100000000L })
{ Check(nextIndexCall(values, k) == values[unchecked((int)(k + 1))], "nested index low word"); cases++; }
bool rejected = false; try { indexCall(values, 3); } catch (IndexOutOfRangeException) { rejected = true; }
Check(rejected, "array exception swallowed");
foreach (double value in new[] { -1.25d, 0d, 8.5d }) { Check(floatCall(value) == value + 0.5, "floating local"); cases++; }
Console.WriteLine($"EMITTER_NUMERIC_LOCAL_SMOKE_PASS methods=11 cases={cases} array-error-preserved nested-stack-adaptation");

var refRead = runtime.GetMethod("RefRead")!.CreateDelegate<Func<int[], long, int, int>>();
var refWrite = runtime.GetMethod("RefWrite")!.CreateDelegate<Func<int[], long, int, int>>();
var objectRead = runtime.GetMethod("ObjectRead")!.CreateDelegate<Func<object[], long, object, object>>();
var objectWrite = runtime.GetMethod("ObjectWrite")!.CreateDelegate<Func<object[], long, object, object>>();
var random = new Random(0x28264cc); int refCases = 0;
int[] refValues = Enumerable.Range(0, 40).Select(_ => random.Next(int.MinValue, int.MaxValue)).ToArray();
object[] objects = Enumerable.Range(0, 40).Select(i => (object)("object" + i)).ToArray();
for (int k = 0; k < refValues.Length; k++)
{
    Check(refRead(refValues, k, 0) == refValues[k], "Spilled int ref load");
    int changed = random.Next(int.MinValue, int.MaxValue); var previous = refValues.ToArray();
    Check(refWrite(refValues, k, changed) == changed, "Spilled int ref store return");
    previous[k] = changed; Check(refValues.SequenceEqual(previous), "Spilled int ref store touched other elements");
    Check(ReferenceEquals(objectRead(objects, k, null!), objects[k]), "Spilled object ref load");
    object newObject = new byte[k + 1]; var priorObjects = objects.ToArray();
    Check(ReferenceEquals(objectWrite(objects, k, newObject), newObject), "Spilled object ref store return");
    priorObjects[k] = newObject; Check(objects.SequenceEqual(priorObjects), "Spilled object ref store touched other elements");
    GC.Collect(2, GCCollectionMode.Forced, true, true);
    Check(ReferenceEquals(objects[k], newObject), "Managed object ref not preserved after GC");
    refCases += 4;
}
foreach (var empty in new[] { Array.Empty<int>(), null! })
{
    bool threw = false;
    try { refRead(empty, 0, 0); }
    catch (IndexOutOfRangeException) when (empty != null) { threw = true; }
    catch (NullReferenceException) when (empty == null) { threw = true; }
    Check(threw, "Source array failure was swallowed");
}
Console.WriteLine($"MANAGED_REF_SPILL_SMOKE_PASS methods4 cases{refCases} negatives3 array-failures2 gc-reference-checks40");
