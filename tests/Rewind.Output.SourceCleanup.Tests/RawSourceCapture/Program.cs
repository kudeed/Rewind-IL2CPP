using System.Reflection;
using System.Security.Cryptography;
using System.Text.Json;
using ICSharpCode.Decompiler;
using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.OutputVisitor;
using ICSharpCode.Decompiler.TypeSystem;
using Mono.Cecil;
using RewindDecompiler = Rewind.Output.Decompiler;

if (args.Length != 2) throw new ArgumentException("assembly.dll new-output-directory");
string input = Path.GetFullPath(args[0]), output = Path.GetFullPath(args[1]);
if (!File.Exists(input) || Directory.Exists(output)) throw new InvalidOperationException("Input required and output must be new");
Directory.CreateDirectory(output);
string Hash(string path) { using var s = File.OpenRead(path); return Convert.ToHexString(SHA256.HashData(s)).ToLowerInvariant(); }
string before = Hash(input);
var names = new[] {
    "Paper2.Economy.Controller.EconomyController",
    "Paper2.LevelEnd.View.LevelEndScreenView",
    "Paper2.ServiceLocator.Controller.AbstractChildServiceController"
};
var rewind = typeof(RewindDecompiler).Assembly;
var factory = typeof(RewindDecompiler).GetMethod("NewDecompiler", BindingFlags.NonPublic | BindingFlags.Static)!;
CSharpDecompiler New(bool machines = false, bool iteratorsOnly = false, bool closures = false) =>
    (CSharpDecompiler)factory.Invoke(null, [input, Path.GetDirectoryName(input)!, (LanguageVersion)900,
        machines, iteratorsOnly, closures])!;
bool Check(string type, string method, object tree) => (bool)rewind.GetType("Rewind.Output." + type)!
    .GetMethod(method, BindingFlags.Public | BindingFlags.Static)!.Invoke(null, [tree])!;
string Transform(string method, string source)
{
    object[] arguments = [source];
    typeof(RewindDecompiler).GetMethod(method, BindingFlags.NonPublic | BindingFlags.Static)!.Invoke(null, arguments);
    return (string)arguments[0];
}
var reports = new List<object>();
var decompiler = New();
using var assembly = AssemblyDefinition.ReadAssembly(input);
IEnumerable<TypeDefinition> Descendants(TypeDefinition type)
{
    yield return type;
    foreach (var nested in type.NestedTypes)
    foreach (var child in Descendants(nested)) yield return child;
}
foreach (string name in names)
{
    var tree = decompiler.DecompileType(new FullTypeName(name));
    bool machines = Check("IteratorCheck", "HasStuckIterator", tree), closures;
    if (machines) tree = New(true, true).DecompileType(new FullTypeName(name));
    closures = Check("ClosureCheck", "NamesMissingClosure", tree);
    if (closures) tree = New(machines, machines, true).DecompileType(new FullTypeName(name));
    using var writer = new StringWriter();
    tree.AcceptVisitor(new CSharpOutputVisitor(writer, new DecompilerSettings((LanguageVersion)900).CSharpFormattingOptions));
    string raw = writer.ToString();
    string marked = Transform("MarkFailedMembers", raw);
    string sanitized = Transform("SanitizeIdentifiers", marked);
    string cleaned = Transform("SourceCleanup", sanitized);
    string prefix = Path.Combine(output, name.Split('.').Last());
    File.WriteAllText(prefix + ".raw.cs.txt", raw);
    File.WriteAllText(prefix + ".sanitized.cs.txt", sanitized);
    File.WriteAllText(prefix + ".cleaned.cs.txt", cleaned);
    var top = assembly.MainModule.Types.Single(t => t.FullName == name);
    var il = new List<object>();
    foreach (var owner in Descendants(top))
    foreach (var method in owner.Methods.Where(m => m.HasBody && m.Body.ExceptionHandlers.Count != 0))
    {
        il.Add(new {
            owner = owner.FullName, method = method.FullName, token = method.MetadataToken.ToUInt32().ToString("X8"),
            locals = method.Body.Variables.Select(v => new { index = v.Index, type = v.VariableType.FullName }),
            handlers = method.Body.ExceptionHandlers.Select(h => new { kind = h.HandlerType.ToString(),
                catchType = h.CatchType?.FullName, start = h.HandlerStart?.Offset, end = h.HandlerEnd?.Offset }),
            instructions = method.Body.Instructions.Select(i => new { offset = i.Offset,
                opcode = i.OpCode.Name, operand = i.Operand?.ToString() })
        });
    }
    File.WriteAllText(prefix + ".recovered-il.json", JsonSerializer.Serialize(il, new JsonSerializerOptions { WriteIndented = true }));
    reports.Add(new { type = name, machines, closures, raw_sha256 = Hash(prefix + ".raw.cs.txt"),
        sanitized_sha256 = Hash(prefix + ".sanitized.cs.txt"), cleaned_sha256 = Hash(prefix + ".cleaned.cs.txt"),
        recovered_il_sha256 = Hash(prefix + ".recovered-il.json"), scope = "existing recovered IL; no native lift or execution" });
    Console.WriteLine(JsonSerializer.Serialize(reports[^1]));
}
if (Hash(input) != before) throw new InvalidOperationException("Input assembly changed");
var report = new { input, input_sha256 = before, rewind_output_sha256 = Hash(rewind.Location), types = reports };
File.WriteAllText(Path.Combine(output, "capture.json"), JsonSerializer.Serialize(report, new JsonSerializerOptions { WriteIndented = true }));
Console.WriteLine(JsonSerializer.Serialize(new { complete = true, count = reports.Count, output }));
