// Native fixtures: Unity 2022.3.62f2 ARM64 libil2cpp.so, SHA256
// c14148fa2bca4e8d09d0f5422db1b288fdcdaab8bf98f12a59988bf1e8da00f6.
// These tests never execute the native input or load a game model.
using System.Text.Json;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Runtime;
using Rewind.Binary;
using Rewind.Metadata;

static void Check(bool condition, string label) { if (!condition) throw new Exception(label); }
int positive = 0, negative = 0;
using JsonDocument fixtures = JsonDocument.Parse(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "native-bodies.json")));
var bodies = new Dictionary<ulong, A64Instruction[]>();
foreach (JsonElement fixture in fixtures.RootElement.EnumerateArray())
{
    ulong start = fixture.GetProperty("address").GetUInt64();
    byte[] bytes = Convert.FromHexString(fixture.GetProperty("bytes").GetString()!);
    bodies.Add(start, Enumerable.Range(0, bytes.Length / 4)
        .Select(i => A64Decoder.Decode(BitConverter.ToUInt32(bytes, i * 4), start + (ulong)i * 4)).ToArray());
}
var exports = new Dictionary<string, ulong>
{
    ["il2cpp_gchandle_get_target"] = 0x1F02C48,
    ["il2cpp_raise_exception"] = 0x1F029C8,
    ["il2cpp_class_from_system_type"] = 0x1F02470,
    ["il2cpp_class_from_il2cpp_type"] = 0x1F02498,
};
var imports = new Dictionary<ulong, string>
{
    [0x49CF880] = "__cxa_allocate_exception",
    [0x49CF890] = "__cxa_throw",
};
A64Instruction[] Body(ulong address) => bodies.GetValueOrDefault(address) ?? [];
ulong? Export(string name) => exports.TryGetValue(name, out ulong address) ? address : null;
string? Import(ulong address) => imports.GetValueOrDefault(address);
bool Data(ulong address) => address == 0x49D5C28;
bool ReadOnlyPointer(ulong address) => address == 0x4CF2478;
KlassLayout Layout() => KlassLayout.For(MetaVersion.V31_1, 8, new UnityVersion(2022, 3, 62, 'f', 2));
Arm64RuntimeDispatchShapes.ClassInitContract? Contract() =>
    Arm64RuntimeDispatchShapes.FromExports(Export, Body, Import, Data);
var known = Contract();
Check(known is { GetHandleTarget: 0x1F33E9C, Raise: 0x1F05A1C, MetadataInitializer: 0x1EE05B4 }, "public export and imported no-return anchors"); positive++;
var layout = Layout();
Check(layout.InitializationExceptionGCHandle == 0xD8 && layout.InitializationExceptionGCHandleSize == 4 &&
    layout.Bitflags == 0x135 && layout.CctorStarted == 0xDC && layout.CctorFinished == 0xE0,
    "2022 field widths and unchanged following offsets"); positive++;
bool Matches(A64Instruction[] ins) => Arm64RuntimeDispatchShapes.IsClassInitOneArgument(ins, layout, known!, Body, ReadOnlyPointer);
A64Instruction[] original = Body(0x1F4CF68);
Check(Matches(original), "complete native one-argument class initializer"); positive++;
Check(!Matches(Body(0x1F4CF94)), "bool overload can return null and must not alias"); negative++;
Check(!Matches(Body(0x1F4CFDC)), "class interface overload is not class initialization"); negative++;
Check(!Matches(original[..^1]), "throw path may not be truncated"); negative++;
Check(!Matches(original.Append(A64Decoder.Decode(0xD65F03C0, original[^1].Address + 4)).ToArray()), "extra return rejected"); negative++;
Check(!Matches(original.Concat(Body(0x1F4CF94)).ToArray()), "neighbouring overload cannot complete a body"); negative++;
for (int i = 0; i < original.Length; i++)
{
    A64Instruction[] mutant = (A64Instruction[])original.Clone();
    mutant[i] = A64Decoder.Decode(0, mutant[i].Address);
    Check(!Matches(mutant), "one-arg instruction mutation " + i); negative++;
}
A64Instruction[] initializer = Body(0x1EE05B4);
for (int i = 0; i < initializer.Length; i++)
{
    A64Instruction[] mutant = (A64Instruction[])initializer.Clone();
    mutant[i] = A64Decoder.Decode(0, mutant[i].Address);
    bodies[0x1EE05B4] = mutant;
    Check(!Matches(original), "initializer/EH instruction mutation " + i); negative++;
}
bodies[0x1EE05B4] = initializer;
foreach (ulong address in new ulong[] { 0x1F02C48, 0x1F029C8, 0x1F05A1C, 0x1F02470, 0x1F02498, 0x1EE0590 })
{
    A64Instruction[] source = Body(address);
    for (int i = 0; i < source.Length; i++)
    {
        A64Instruction[] mutant = (A64Instruction[])source.Clone();
        mutant[i] = A64Decoder.Decode(0, mutant[i].Address);
        bodies[address] = mutant;
        Check(Contract() == null, $"export chain instruction mutation {address:X}:{i}"); negative++;
    }
    bodies[address] = source;
}
layout.InitializationExceptionGCHandle += 4;
Check(!Matches(original), "different handle field rejected"); negative++;
layout = Layout(); layout.InitializationExceptionGCHandleSize = 8;
Check(!Matches(original), "pointer-width handle is a different runtime shape"); negative++;
layout = Layout(); layout.Bitflags++;
Check(!Matches(original), "different initialized-bit byte rejected"); negative++;
layout = Layout();
Check(!Arm64RuntimeDispatchShapes.IsClassInitOneArgument(original, layout, known! with { MetadataInitializer = 0x1EE0678 }, Body, ReadOnlyPointer), "different initializer cannot be a wildcard"); negative++;
Check(!Arm64RuntimeDispatchShapes.IsClassInitOneArgument(original, layout, known! with { Raise = 0x1F05A20 }, Body, ReadOnlyPointer), "interior/unanchored raiser rejected"); negative++;
Check(!Arm64RuntimeDispatchShapes.IsClassInitOneArgument(original, layout, known! with { GetHandleTarget = 0x1F33EA0 }, Body, ReadOnlyPointer), "different handle getter rejected"); negative++;
Check(!Arm64RuntimeDispatchShapes.IsClassInitOneArgument(original, layout, known!, Body, _ => false), "mutable/unresolved mutex pointer rejected"); negative++;
imports[0x49CF890] = "__cxa_begin_catch";
Check(Contract() == null, "returning imported endpoint cannot establish no-return"); negative++;
imports[0x49CF890] = "__cxa_throw";
exports.Remove("il2cpp_gchandle_get_target");
Check(Contract() == null, "missing public role anchor rejected"); negative++;
exports["il2cpp_gchandle_get_target"] = 0x1F02C48;
Check(Arm64RuntimeDispatchShapes.FromExports(Export, Body, Import, _ => false) == null, "invalid typeinfo literal rejected"); negative++;

byte[] payload = original.SelectMany(i => BitConverter.GetBytes(i.Word)).ToArray();
var image = new FixtureImage(payload);
var complete = new Arm64RuntimeDispatchShapes.CompleteBodies(image, [0x1100UL], _ => false);
Check(complete.Read(0x1100).Length == 11, "exact complete extent read"); positive++;
Check(complete.Read(0x1104).Length == 0, "interior address lacks exact FDE"); negative++;
var interior = new Arm64RuntimeDispatchShapes.CompleteBodies(image, [0x1100UL, 0x1110UL], _ => false);
Check(interior.Read(0x1100).Length == 0, "additional interior entry rejected"); negative++;
var managed = new Arm64RuntimeDispatchShapes.CompleteBodies(image, [0x1100UL], _ => true);
Check(managed.Read(0x1100).Length == 0, "managed body cannot be runtime shape"); negative++;
image.FunctionTable.Clear();
Check(new Arm64RuntimeDispatchShapes.CompleteBodies(image, [0x1100UL], _ => false).Read(0x1100).Length == 0,
    "export/call start without whole-function bound rejected"); negative++;
image.FunctionTable.Add(new FunctionRange(0x1100, 0x112C, 0, true));
Check(new Arm64RuntimeDispatchShapes.CompleteBodies(image, [0x1100UL], _ => false).Read(0x1100).Length == 0,
    "chained range is not standalone function"); negative++;
image.FunctionTable.Clear();
image.FunctionTable.Add(new FunctionRange(0x1100, 0x112C, 0));
image.FunctionTable.Add(new FunctionRange(0x1100, 0x1130, 0));
Check(new Arm64RuntimeDispatchShapes.CompleteBodies(image, [0x1100UL], _ => false).Read(0x1100).Length == 0,
    "conflicting whole-function bounds rejected"); negative++;

var result = new { pass = true, positive, negative };
File.WriteAllText(Path.Combine(AppContext.BaseDirectory, "result.json"), JsonSerializer.Serialize(result, new JsonSerializerOptions { WriteIndented = true }));
Console.WriteLine($"ARM64_RUNTIME_DISPATCH_SHAPE_PASS positive={positive} negative={negative}");

sealed class FixtureImage : NativeImage
{
    public override ImageFormat Format => ImageFormat.Elf;
    internal FixtureImage(byte[] body)
    {
        MemoryBase = 0x1000;
        Memory = new byte[0x1000];
        body.CopyTo(Memory, 0x100);
        Arch = CpuArch.Arm64;
        PointerSize = 8;
        Sections.Add(new ImageSection("code", 0x1000, 0x1000, SectionFlags.Read | SectionFlags.Execute));
        FunctionTable.Add(new FunctionRange(0x1100, 0x1100 + (ulong)body.Length, 0));
    }
}
