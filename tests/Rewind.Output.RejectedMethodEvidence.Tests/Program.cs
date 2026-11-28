using System.Globalization;
using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using System.Security.Cryptography;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;
using Rewind.Output;
using AssemblyDefinition = Mono.Cecil.AssemblyDefinition;
using ModuleDefinition = Mono.Cecil.ModuleDefinition;
using TypeReference = Mono.Cecil.TypeReference;
using CecilMethod = Mono.Cecil.MethodDefinition;
using CecilType = Mono.Cecil.TypeDefinition;
using CecilMethodAttributes = Mono.Cecil.MethodAttributes;
using CecilTypeAttributes = Mono.Cecil.TypeAttributes;

internal static class Program
{
    private static readonly BindingFlags Hidden = BindingFlags.Static | BindingFlags.NonPublic;
    private static readonly MethodInfo Evidence = typeof(Decompiler).Assembly.GetType("Rewind.Output.RejectedMethodEvidence")!
        .GetMethod("Write", Hidden)!;
    private static readonly MethodInfo Source = typeof(Decompiler).GetMethod("WriteSource", Hidden)!;
    private static readonly string RunId = Guid.NewGuid().ToString("N");
    private static int assertions;
    private static string work = "", journal = "", report = "";
    private static string? native;

    private static int Main(string[] args)
    {
        string selected = "eh,branches,locals,metadata";
        for (int i = 0; i < args.Length; i++)
        {
            if (i + 1 == args.Length) throw new ArgumentException("Every option requires a value.");
            string value = args[++i];
            switch (args[i - 1])
            {
                case "--group": selected = value; break;
                case "--work-dir": work = value; break;
                case "--journal": journal = value; break;
                case "--report": report = value; break;
                case "--source-assembly": native = value; break;
                default: throw new ArgumentException("Unknown option: " + args[i - 1]);
            }
        }
        if (work.Length == 0) work = Path.Combine(Path.GetTempPath(), "rewind-rejected-evidence-" + RunId);
        Directory.CreateDirectory(work);
        if (journal.Length == 0) journal = Path.Combine(work, "groups.jsonl");
        if (report.Length == 0) report = Path.Combine(work, "results.json");
        var groups = new (string Id, Action Run)[]
        {
            ("eh", Exceptions), ("branches", Branches), ("locals", Locals),
            ("metadata", Metadata), ("native", NativeSource)
        };
        var requested = selected.Split(',', StringSplitOptions.RemoveEmptyEntries).ToHashSet(StringComparer.Ordinal);
        if (requested.Except(groups.Select(g => g.Id)).Any()) throw new ArgumentException("Unknown group.");
        var results = new List<object>();
        bool failed = false;
        foreach (var group in groups.Where(g => requested.Contains(g.Id)))
        {
            int before = assertions;
            string? error = null;
            try { group.Run(); }
            catch (Exception ex) { error = Unwrap(ex).ToString(); failed = true; }
            var item = new { run_id = RunId, group = group.Id, status = error == null ? "pass" : "fail", assertions = assertions - before, error };
            results.Add(item);
            string line = JsonSerializer.Serialize(item);
            Console.WriteLine(line);
            File.AppendAllText(journal, line + Environment.NewLine);
        }
        File.WriteAllText(report, JsonSerializer.Serialize(new
        {
            suite = "rejected-method-read-only-evidence", run_id = RunId,
            output_binary_sha256 = Hash(File.ReadAllBytes(typeof(Decompiler).Assembly.Location)),
            groups = results, assertions,
            scope = "New evidence-only fixtures and optional already-exported DLL source pass. No native export, Unity or historical tests."
        }, new JsonSerializerOptions { WriteIndented = true }) + Environment.NewLine);
        return failed ? 1 : 0;
    }

    private static Exception Unwrap(Exception e) => e is TargetInvocationException { InnerException: { } inner } ? inner : e;
    private static string Hash(byte[] bytes) => Convert.ToHexStringLower(SHA256.HashData(bytes));
    private static void Require(bool condition, string message)
    {
        assertions++;
        if (!condition) throw new InvalidOperationException(message);
    }

    private static string Reject(uint token) => $"// ILSpy could not decompile this member: Error decompiling @{token:X8} Fixture.Case";
    private static string[] Write(string dll, string directory, string text) =>
        ((IEnumerable<string>)Evidence.Invoke(null, [dll, directory, text])!).ToArray();

    private sealed record Fixture(string Path, uint Token);
    private static Fixture Make(string name, Action<ModuleDefinition, CecilMethod, ILProcessor> emit)
    {
        string path = Path.Combine(work, name + ".dll");
        using var a = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition(name, new Version(1, 0)), name, ModuleKind.Dll);
        var module = a.MainModule;
        var type = new CecilType("Fixture", "Case", CecilTypeAttributes.Public | CecilTypeAttributes.Class, module.TypeSystem.Object);
        module.Types.Add(type);
        var method = new CecilMethod("Run", CecilMethodAttributes.Public | CecilMethodAttributes.Static, module.TypeSystem.Void);
        method.Parameters.Add(new ParameterDefinition("receiver", Mono.Cecil.ParameterAttributes.None, module.TypeSystem.Object));
        type.Methods.Add(method);
        method.Body.InitLocals = true;
        method.Body.MaxStackSize = 3;
        method.Body.Variables.Add(new VariableDefinition(module.TypeSystem.IntPtr));
        emit(module, method, method.Body.GetILProcessor());
        a.Write(path);
        using var read = AssemblyDefinition.ReadAssembly(path);
        uint token = read.MainModule.Types.Single(t => t.FullName == "Fixture.Case").Methods.Single().MetadataToken.ToUInt32();
        return new Fixture(path, token);
    }

    private static MethodReference Virtual(ModuleDefinition module) =>
        new("ToString", module.TypeSystem.String, module.TypeSystem.Object) { HasThis = true };
    private static void Pointer(ModuleDefinition module, ILProcessor il)
    {
        il.Append(il.Create(OpCodes.Ldarg_0));
        il.Append(il.Create(OpCodes.Ldvirtftn, Virtual(module)));
        il.Append(il.Create(OpCodes.Stloc_0));
    }

    private static string Check(Fixture f, string suffix)
    {
        byte[] before = File.ReadAllBytes(f.Path);
        string[] paths = Write(f.Path, Path.Combine(work, suffix), Reject(f.Token));
        Require(paths.Length == 1, suffix + ": exactly one rejected-method sidecar");
        Require(File.ReadAllBytes(f.Path).SequenceEqual(before), suffix + ": authoritative DLL bytes unchanged");
        string text = File.ReadAllText(paths[0]);
        Require(text.Contains("C# SOURCE REJECTED", StringComparison.Ordinal), suffix + ": rejection is explicit");
        Require(text.Contains("assembly_sha256: " + Hash(before), StringComparison.Ordinal), suffix + ": original assembly hash");
        using var pe = new PEReader(new MemoryStream(before, writable: false));
        var metadata = pe.GetMetadataReader();
        var handle = System.Reflection.Metadata.Ecma335.MetadataTokens.MethodDefinitionHandle((int)(f.Token & 0x00FFFFFF));
        int rva = metadata.GetMethodDefinition(handle).RelativeVirtualAddress;
        var body = pe.GetMethodBody(rva);
        byte[] bodyBytes = pe.GetSectionData(rva).GetContent(0, body.Size).ToArray();
        Require(Field(text, "method_body_hex") == Convert.ToHexString(bodyBytes), suffix + ": full raw method body including EH");
        Require(Field(text, "method_body_sha256") == Hash(bodyBytes), suffix + ": full method-body hash");
        Require(Field(text, "il_hex") == Convert.ToHexString(body.GetILBytes() ?? []), suffix + ": exact original IL bytes");
        Require(text.Contains("ldvirtftn", StringComparison.Ordinal), suffix + ": original function pointer remains visible");
        foreach (ExceptionRegion region in body.ExceptionRegions)
        {
            Require(text.Contains($"{region.Kind}: try IL_{region.TryOffset:X4}..IL_{region.TryOffset + region.TryLength:X4}", StringComparison.Ordinal), suffix + ": EH try boundaries");
            Require(text.Contains($"handler IL_{region.HandlerOffset:X4}..IL_{region.HandlerOffset + region.HandlerLength:X4}", StringComparison.Ordinal), suffix + ": EH handler boundaries");
        }
        return text;
    }

    private static string Field(string text, string key) => text.Split('\n')
        .Single(line => line.StartsWith(key + ": ", StringComparison.Ordinal))[(key.Length + 2)..].TrimEnd('\r');

    private static void Exceptions()
    {
        foreach (ExceptionHandlerType kind in new[] { ExceptionHandlerType.Catch, ExceptionHandlerType.Finally, ExceptionHandlerType.Filter })
        {
            Fixture f = Make("eh-" + kind, (module, method, il) =>
            {
                var start = il.Create(OpCodes.Nop);
                var handler = il.Create(kind == ExceptionHandlerType.Finally ? OpCodes.Nop : OpCodes.Pop);
                var end = il.Create(OpCodes.Ret);
                il.Append(start);
                Pointer(module, il);
                il.Append(il.Create(OpCodes.Leave, end));
                Instruction? filter = null;
                if (kind == ExceptionHandlerType.Filter)
                {
                    filter = il.Create(OpCodes.Pop);
                    il.Append(filter);
                    il.Append(il.Create(OpCodes.Ldc_I4_1));
                    il.Append(il.Create(OpCodes.Endfilter));
                }
                il.Append(handler);
                Pointer(module, il);
                il.Append(kind == ExceptionHandlerType.Finally ? il.Create(OpCodes.Endfinally) : il.Create(OpCodes.Leave, end));
                il.Append(end);
                method.Body.ExceptionHandlers.Add(new ExceptionHandler(kind)
                {
                    TryStart = start, TryEnd = filter ?? handler,
                    HandlerStart = handler, HandlerEnd = end,
                    FilterStart = filter,
                    CatchType = kind == ExceptionHandlerType.Catch ? new TypeReference("System", "Exception", module, module.TypeSystem.CoreLibrary) : null
                });
            });
            string text = Check(f, "eh-output-" + kind);
            Require(text.Contains("  " + kind + ": try ", StringComparison.Ordinal), "EH kind " + kind + " recorded");
        }
    }

    private static void Branches()
    {
        Fixture boundary = Make("branch-boundary", (module, method, il) =>
        {
            var end = il.Create(OpCodes.Ret);
            il.Append(il.Create(OpCodes.Ldarg_0));
            il.Append(il.Create(OpCodes.Brfalse_S, end));
            Pointer(module, il); // 8 bytes. The removed normalizer expanded ldvirtftn by 7 bytes.
            for (int i = 0; i < 119; i++) il.Append(il.Create(OpCodes.Nop));
            il.Append(end); // Original short displacement is exactly 127.
        });
        string text = Check(boundary, "branch-boundary-output");
        byte[] ilBytes = Convert.FromHexString(Field(text, "il_hex"));
        Require(ilBytes[1] == 0x2C && ilBytes[2] == 0x7F, "short conditional branch remains at valid +127 boundary");
        Require(text.Contains("brfalse.s", StringComparison.Ordinal), "original short branch opcode is readable");

        Fixture table = Make("branch-switch", (module, method, il) =>
        {
            var first = il.Create(OpCodes.Nop);
            var second = il.Create(OpCodes.Nop);
            var end = il.Create(OpCodes.Ret);
            il.Append(il.Create(OpCodes.Ldc_I4_0));
            il.Append(il.Create(OpCodes.Switch, new[] { first, second }));
            il.Append(il.Create(OpCodes.Br, end));
            il.Append(first);
            Pointer(module, il);
            il.Append(il.Create(OpCodes.Br, end));
            il.Append(second);
            Pointer(module, il);
            il.Append(end);
        });
        string switchText = Check(table, "branch-switch-output");
        Require(switchText.Split('\n').Any(l => l.Contains("switch", StringComparison.Ordinal) && l.Contains(", IL_", StringComparison.Ordinal)), "all switch targets remain in evidence");
    }

    private static void Locals()
    {
        foreach (OpCode read in new[] { OpCodes.Ldloc_0, OpCodes.Ldloca, OpCodes.Ldloca_S })
        {
            Fixture f = Make("local-" + read.Name!.Replace('.', '-'), (module, method, il) =>
            {
                Pointer(module, il);
                il.Append(read == OpCodes.Ldloc_0 ? il.Create(read) : il.Create(read, method.Body.Variables[0]));
                il.Append(il.Create(OpCodes.Pop));
                il.Append(il.Create(OpCodes.Ret));
            });
            string text = Check(f, "local-output-" + read.Name);
            Require(text.Contains("V_0: System.IntPtr", StringComparison.Ordinal), read.Name + ": native pointer local retained");
            Require(text.Contains(read.Name!, StringComparison.Ordinal), read.Name + ": original live/address use retained");
        }
    }

    private static void Metadata()
    {
        const string marker = "__call_indirect(m1, m2, m3) | __native_0x34452F4(__frame())";
        Fixture f = Make("metadata", (module, method, il) =>
        {
            Pointer(module, il);
            il.Append(il.Create(OpCodes.Ldstr, marker));
            il.Append(il.Create(OpCodes.Pop));
            il.Append(il.Create(OpCodes.Ret));
        });
        string text = Check(f, "metadata-output");
        Require(text.Contains(marker, StringComparison.Ordinal), "unresolved operand strings remain complete");
        byte[] original = File.ReadAllBytes(f.Path);
        string[] repeated = Write(f.Path, Path.Combine(work, "dedup"), Reject(f.Token) + "\n" + Reject(f.Token));
        Require(repeated.Length == 1, "duplicate rejected token emits one sidecar");
        string ordinary = $"var s = \"{Reject(f.Token)}\";\n// Error decompiling @{f.Token:X8}\n// ILSpy could not decompile this member: @01000001\n";
        string unusedDirectory = Path.Combine(work, "not-created");
        Require(Write(f.Path, unusedDirectory, ordinary).Length == 0, "ordinary source and non-method tokens are not evidence requests");
        Require(!Directory.Exists(unusedDirectory), "no unrelated output directory is created");
        string obstacle = Path.Combine(work, "output-is-a-file");
        File.WriteAllText(obstacle, "existing file");
        bool failed = false;
        try { Write(f.Path, obstacle, Reject(f.Token)); }
        catch (Exception e) when (Unwrap(e) is IOException or UnauthorizedAccessException) { failed = true; }
        Require(failed, "evidence output failure is reported");
        Require(File.ReadAllBytes(f.Path).SequenceEqual(original), "output failure cannot alter authoritative DLL");
    }

    private static void NativeSource()
    {
        if (native == null) throw new ArgumentException("native group requires --source-assembly pointing to the existing v3 DLL.");
        string assemblyPath = Path.GetFullPath(native);
        byte[] before = File.ReadAllBytes(assemblyPath);
        string directory = Path.Combine(work, "native-source");
        var logs = new List<string>();
        var result = new DecompileResult();
        var options = new DecompileOptions
        {
            StateMachines = true,
            Language = ICSharpCode.Decompiler.CSharp.LanguageVersion.CSharp9,
            Log = line => { lock (logs) logs.Add(line); }
        };
        Source.Invoke(null, [assemblyPath, Path.GetDirectoryName(assemblyPath)!, directory, result, options]);
        File.WriteAllLines(Path.Combine(work, "native-source.log"), logs);
        Require(File.ReadAllBytes(assemblyPath).SequenceEqual(before), "native source-only pass leaves the authoritative DLL unchanged");
        Require(result.TypesWithErrors == 1, "AddToTaskList remains an explicit ILSpy source rejection");
        Require(result.Clean == 0 && result.Recovered == 0, "source-only pass does not claim new recovered methods");
        string manager = File.ReadAllText(Path.Combine(directory, "BehaviorDesigner", "Runtime", "BehaviorManager.cs"));
        Require(manager.Contains("// ILSpy could not decompile this member: Error decompiling @06000092", StringComparison.Ordinal), "original member rejection survives");
        string sidecar = File.ReadAllText(Path.Combine(directory, "rejected-il", "06000092.il"));
        Require(Field(sidecar, "assembly_sha256") == Hash(before), "native sidecar refers to original v3 DLL hash");
        Require(sidecar.Contains("15 part(s) of this method were not recovered", StringComparison.Ordinal), "all original recovery gaps remain explicit");
        Require(sidecar.Contains("__call_indirect(m1, m2, m3", StringComparison.Ordinal), "unresolved indirect operands are retained, not replaced with defaults");
        Require(sidecar.Contains("__native_0x34452F4", StringComparison.Ordinal), "unresolved native helper is retained");
        Require(sidecar.Split('\n').Count(line => line.Contains("ldvirtftn", StringComparison.Ordinal)) == 2, "both original function-pointer instructions remain");
    }
}
