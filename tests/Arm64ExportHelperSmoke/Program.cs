using System.Security.Cryptography;
using System.Text.Json;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Runtime;
using Rewind.Binary;

using var fixture = JsonDocument.Parse(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "native-bodies.json")));
var bodies = new Dictionary<ulong, A64Instruction[]>();
var sizes = new Dictionary<ulong, int>();
foreach (JsonElement f in fixture.RootElement.GetProperty("functions").EnumerateArray())
{
    ulong at = f.GetProperty("address").GetUInt64();
    byte[] bytes = Convert.FromHexString(f.GetProperty("bytes").GetString()!);
    if (bytes.Length != f.GetProperty("length").GetInt32() ||
        Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant() != f.GetProperty("sha256").GetString())
        throw new Exception("native fixture bytes/extent/hash disagree");
    bodies[at] = Enumerable.Range(0, bytes.Length / 4).Select(i =>
        A64Decoder.Decode(BitConverter.ToUInt32(bytes, i * 4), at + (ulong)i * 4)).ToArray();
    sizes[at] = bytes.Length;
}
Dictionary<string, ulong> Named(string key) => fixture.RootElement.GetProperty(key).EnumerateObject()
    .ToDictionary(p => p.Name, p => p.Value.GetUInt64());
var exports = Named("exports");
var imports = Named("imports").ToDictionary(p => p.Value, p => p.Key);
var texts = Named("strings").ToDictionary(p => p.Value, p => p.Key);
A64Instruction[] Body(ulong at) => bodies.GetValueOrDefault(at) ?? [];
string? Text(ulong at) => texts.GetValueOrDefault(at);
string? Import(ulong at) => imports.GetValueOrDefault(at);
Dictionary<ulong, HelperInfo> Identify() => Arm64ExportHelperShapes.Identify(exports, sizes, Body, Text, Import);
int positive = 0, negative = 0;
void Check(bool condition, string label, bool accepted = false)
{
    if (!condition) throw new Exception(label);
    if (accepted) positive++; else negative++;
}
var actual = Identify();
Check(actual.GetValueOrDefault(0x1F2D9E0UL) is { Kind: HelperKind.ObjectNew, IntArgs: 1, ReturnsValue: true, NoReturn: false },
    "native one-argument object allocation chain", true);
Check(actual.GetValueOrDefault(0x1F2D9F4UL) is { Kind: HelperKind.ThrowIndexOutOfRange, IntArgs: 0, NoReturn: true, ReturnsValue: false },
    "native no-argument index throw chain", true);
Check(actual.GetValueOrDefault(0x1F05B10UL) is { Kind: HelperKind.GetIndexOutOfRangeException, ReturnsValue: true },
    "native factory exact exception identity", true);
Check(!actual.ContainsKey(exports["il2cpp_object_new"]), "catch-and-null API is not the throwing allocation helper");

void InstructionMutants(ulong at, Func<A64Instruction[], bool> matches)
{
    A64Instruction[] original = Body(at);
    Check(matches(original), "complete native function 0x" + at.ToString("X"), true);
    for (int i = 0; i < original.Length; i++)
    {
        var changed = (A64Instruction[])original.Clone();
        changed[i] = A64Decoder.Decode(0, original[i].Address);
        Check(!matches(changed), $"unrecognized instruction at 0x{at:X}+{i * 4}");
    }
    Check(!matches(original[..^1]), "truncated function");
    Check(!matches(original.Append(A64Decoder.Decode(0xD65F03C0, original[^1].NextAddress)).ToArray()), "neighbor instruction rejected");
}
InstructionMutants(0x1F02D74, ins => Arm64ExportHelperShapes.ObjectNewTarget(ins, Import) != null);
InstructionMutants(0x1F029C8, ins => Arm64ExportHelperShapes.PublicRaiser(ins) != null);
InstructionMutants(0x1F05A1C, ins => Arm64ExportHelperShapes.RaisesManagedException(ins, Import));
InstructionMutants(0x1F05B10, ins => Arm64ExportHelperShapes.IndexFactory(ins, Text));
InstructionMutants(0x1F063A0, ins => Arm64ExportHelperShapes.EmptyMessageFactory(ins,
    at => at == 0x1EE2A3C, at => at == 0x1EF5118, at => at == 0x1F654AC));

foreach (string name in new[] { "il2cpp_get_corlib", "il2cpp_class_from_name", "il2cpp_runtime_object_init", "il2cpp_raise_exception", "il2cpp_object_new" })
{
    ulong saved = exports[name]; exports.Remove(name);
    Check(!Identify().ContainsKey(0x1F2D9F4), "missing public contract " + name);
    exports[name] = saved;
}
foreach (string badType in new[] { "NullReferenceException", "OverflowException", "ArgumentException" })
{
    texts[0xD3329F] = badType;
    Check(!Identify().ContainsKey(0x1F2D9F4), "wrong exception type " + badType);
}
texts[0xD3329F] = "IndexOutOfRangeException";
texts[0xD15493] = "Game";
Check(!Identify().ContainsKey(0x1F2D9F4), "wrong exception namespace");
texts[0xD15493] = "System";
imports[0x49CF860] = "arbitrary_side_effect";
Check(!Identify().ContainsKey(0x1F2D9E0), "unproved catch side effect");
imports[0x49CF860] = "__cxa_begin_catch";
imports[0x49CF890] = "returns_normally";
Check(!Identify().ContainsKey(0x1F2D9F4), "raiser must end at actual __cxa_throw import");
imports[0x49CF890] = "__cxa_throw";

var literalImage = new LiteralImage(SectionFlags.Read, nul: true);
Check(Arm64ExportHelperShapes.ReadOnlyText(literalImage, 0x1000) == "System", "immutable complete literal", true);
foreach (SectionFlags extra in new[] { SectionFlags.Write, SectionFlags.Execute, SectionFlags.ZeroFill })
    Check(Arm64ExportHelperShapes.ReadOnlyText(new LiteralImage(SectionFlags.Read | extra, nul: true), 0x1000) == null,
        "nonliteral storage " + extra);
Check(Arm64ExportHelperShapes.ReadOnlyText(new LiteralImage(SectionFlags.Read, nul: false), 0x1000) == null, "missing NUL in section");
literalImage.Sections.Add(new ImageSection("mutable-alias", 0x1002, 3, SectionFlags.Read | SectionFlags.Write));
Check(Arm64ExportHelperShapes.ReadOnlyText(literalImage, 0x1000) == null, "overlapping mutable mapping");

var objectAlias = Body(0x1F2D9E0);
bodies[0x1F2D9E0] = [objectAlias[0], A64Decoder.Decode(0xD65F03C0, objectAlias[0].NextAddress)];
sizes[0x1F2D9E0] = 8;
Check(!Identify().ContainsKey(0x1F2D9E0), "branch prefix in a longer function is not an alias");
bodies[0x1F2D9E0] = objectAlias; sizes[0x1F2D9E0] = 4;
var internalAlias = Body(0x1EF5118);
bodies[0x1EF5118] = [A64Decoder.Decode(0x14000000, 0x1EF5118)];
Check(!Identify().ContainsKey(0x1F2D9E0), "cyclic object-new branch chain");
bodies[0x1EF5118] = internalAlias;
var throwing = Body(0x1F2D9F4);
bodies[0x1F2D9F4] = throwing.Append(A64Decoder.Decode(0xD65F03C0, throwing[^1].NextAddress)).ToArray();
sizes[0x1F2D9F4] = 12;
Check(!Identify().ContainsKey(0x1F2D9F4), "returning call wrapper is not a proven noreturn helper");

Console.WriteLine(JsonSerializer.Serialize(new { pass = true, positive, negative,
    native_sha256 = fixture.RootElement.GetProperty("native_sha256").GetString() }));

sealed class LiteralImage : NativeImage
{
    public override ImageFormat Format => ImageFormat.Elf;
    public LiteralImage(SectionFlags flags, bool nul)
    {
        MemoryBase = 0x1000;
        Memory = nul ? [83, 121, 115, 116, 101, 109, 0] : [83, 121, 115, 116, 101, 109];
        Sections.Add(new ImageSection("literal", 0x1000, (ulong)Memory.Length, flags));
    }
}
