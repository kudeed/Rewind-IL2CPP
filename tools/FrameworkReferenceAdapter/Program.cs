using System.Globalization;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using Mono.Cecil;
using Mono.Cecil.Cil;
using Rewind.Output;

internal static class Program
{
    internal static readonly JsonSerializerOptions JsonOptions = new() { WriteIndented = true };
    internal static string Hash(string path) => Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(path))).ToLowerInvariant();

    private static int Main(string[] args)
    {
        try
        {
            if (args.Length == 2 && args[0] == "--self-test") return SelfTests.Run(args[1]);
            if (args.Length != 4 || args[0] != "--references" || args[2] != "--output")
            {
                Console.Error.WriteLine("Usage: FrameworkReferenceAdapter --references REFERENCES.json --output NEW_DIRECTORY\n       FrameworkReferenceAdapter --self-test NEW_DIRECTORY");
                return 2;
            }
            AdaptReferences(Path.GetFullPath(args[1]), Path.GetFullPath(args[3]));
            return 0;
        }
        catch (Exception ex) { Console.Error.WriteLine(ex); return 1; }
    }

    private static void AdaptReferences(string manifestPath, string output)
    {
        if (Directory.Exists(output) || File.Exists(output)) throw new IOException("Output must be a new directory: " + output);
        JsonObject original = JsonNode.Parse(File.ReadAllText(manifestPath))!.AsObject();
        JsonObject mapped = original.DeepClone().AsObject();
        string[] framework = original.Select(x => x.Value!.AsObject())
            .Where(x => x["kind"]!.GetValue<string>() == "Unity_framework_reference")
            .Select(x => Path.GetFullPath(x["path"]!.GetValue<string>())).ToArray();
        using var profile = new TargetFrameworkReferenceAdapter(framework);
        using var resolver = new DefaultAssemblyResolver();
        foreach (string directory in original.Select(x => x.Value!["path"]!.GetValue<string>())
                     .Select(p => Path.GetDirectoryName(Path.GetFullPath(p))!).Distinct()) resolver.AddSearchDirectory(directory);
        Directory.CreateDirectory(Path.Combine(output, "assemblies"));
        var results = new List<object>();
        int changedAssemblies = 0, changedReferences = 0;
        foreach (var entry in original.OrderBy(x => x.Key, StringComparer.Ordinal))
        {
            JsonObject description = entry.Value!.AsObject();
            if (description["kind"]!.GetValue<string>() != "metadata_only_reference") continue;
            string input = Path.GetFullPath(description["path"]!.GetValue<string>());
            string inputHash = Hash(input);
            using var assembly = AssemblyDefinition.ReadAssembly(input, new ReaderParameters
            {
                InMemory = true, ReadingMode = ReadingMode.Deferred, ReadSymbols = false, AssemblyResolver = resolver,
            });
            if (assembly.Modules.Count != 1 || assembly.Name.HasPublicKey ||
                (assembly.MainModule.Attributes & ModuleAttributes.StrongNameSigned) != 0)
                throw new InvalidOperationException("Only unsigned, single-module recovered reference copies are accepted: " + input);
            string beforeBody = BodyFingerprint(assembly.MainModule);
            FrameworkReferenceAdaptation result = profile.Adapt(assembly.MainModule);
            string? rewritten = null, outputHash = null;
            if (result.ChangedTypeReferences > 0)
            {
                string name = assembly.Name.Name;
                if (name != Path.GetFileName(name) || name.IndexOfAny(Path.GetInvalidFileNameChars()) >= 0)
                    throw new InvalidDataException("Unsafe assembly name in input metadata.");
                rewritten = Path.Combine(output, "assemblies", name + ".dll");
                if (File.Exists(rewritten)) throw new IOException("Duplicate output assembly: " + name);
                assembly.Write(rewritten, new WriterParameters { DeterministicMvid = true, Timestamp = 0 });
                using var check = AssemblyDefinition.ReadAssembly(rewritten, new ReaderParameters
                {
                    InMemory = true, ReadingMode = ReadingMode.Deferred, ReadSymbols = false, AssemblyResolver = resolver,
                });
                if (BodyFingerprint(check.MainModule) != beforeBody)
                    throw new InvalidDataException("Method instruction fingerprint changed: " + input);
                outputHash = Hash(rewritten);
                JsonObject updated = mapped[entry.Key]!.AsObject();
                updated["path"] = rewritten;
                updated["kind"] = "framework_adapted_metadata_only_reference";
                updated["original_path"] = input;
                updated["original_sha256"] = inputHash;
                updated["sha256"] = outputHash;
                updated["runtime_verified"] = false;
                changedAssemblies++;
                changedReferences += result.ChangedTypeReferences;
            }
            if (Hash(input) != inputHash) throw new IOException("Source changed during reference adaptation: " + input);
            results.Add(new { assembly = entry.Key, original_path = input, original_sha256 = inputHash,
                output_path = rewritten, output_sha256 = outputHash, method_instruction_sha256 = beforeBody,
                adaptation = result });
        }
        string mapPath = Path.Combine(output, "REFERENCE_MAP.json");
        File.WriteAllText(mapPath, mapped.ToJsonString(JsonOptions) + "\n");
        var receipt = new
        {
            schema = 1, operation = "exact_target_framework_reference_adaptation", reference_only = true,
            runtime_verified = false, method_bodies_recovered = false, original_manifest = manifestPath,
            original_manifest_sha256 = Hash(manifestPath), changed_assemblies = changedAssemblies,
            changed_type_references = changedReferences, profile = profile.Profile, assemblies = results,
        };
        File.WriteAllText(Path.Combine(output, "ADAPTATION_RECEIPT.json"), JsonSerializer.Serialize(receipt, JsonOptions) + "\n");
        Console.WriteLine(JsonSerializer.Serialize(new { output, changed_assemblies = changedAssemblies,
            changed_type_references = changedReferences, reference_only = true, runtime_verified = false }, JsonOptions));
    }

    // A metadata rewrite necessarily changes token bytes. Compare typed opcodes, target instruction ordinals,
    // member/type names, and constants instead. This does not validate the original recovered method bodies.
    internal static string BodyFingerprint(ModuleDefinition module)
    {
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        void Add(string text) => hash.AppendData(Encoding.UTF8.GetBytes(text + "\n"));
        foreach (MethodDefinition method in module.GetTypes().SelectMany(t => t.Methods))
        {
            if (!method.HasBody) continue;
            Add(method.FullName);
            var indexes = method.Body.Instructions.Select((instruction, index) => (instruction, index))
                .ToDictionary(x => x.instruction, x => x.index);
            foreach (Instruction instruction in method.Body.Instructions)
            {
                string operand = instruction.Operand switch
                {
                    null => "",
                    Instruction target => "branch:" + indexes[target],
                    Instruction[] targets => "switch:" + string.Join(",", targets.Select(x => indexes[x])),
                    VariableDefinition variable => "local:" + variable.Index,
                    ParameterDefinition parameter => "arg:" + parameter.Index,
                    IFormattable value => value.ToString(null, CultureInfo.InvariantCulture),
                    _ => instruction.Operand.ToString() ?? "",
                };
                Add(instruction.OpCode.Name + " " + JsonSerializer.Serialize(operand));
            }
            foreach (ExceptionHandler handler in method.Body.ExceptionHandlers)
            {
                int Index(Instruction? value) => value is null ? -1 : indexes[value];
                Add($"handler:{handler.HandlerType}:{handler.CatchType?.FullName}:{Index(handler.TryStart)}:{Index(handler.TryEnd)}:{Index(handler.HandlerStart)}:{Index(handler.HandlerEnd)}:{Index(handler.FilterStart)}");
            }
        }
        return Convert.ToHexString(hash.GetHashAndReset()).ToLowerInvariant();
    }
}
