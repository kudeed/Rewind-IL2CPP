using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;
using Rewind.Output;

internal static class SelfTests
{
    private static readonly Version Version = new(1, 0, 0, 0);
    private static AssemblyDefinition Assembly(string name) => AssemblyDefinition.CreateAssembly(
        new AssemblyNameDefinition(name, Version), name + ".dll", ModuleKind.Dll);
    private static AssemblyNameReference Scope(AssemblyDefinition assembly) => new(assembly.Name.Name, assembly.Name.Version);
    private static AssemblyNameReference RegisterScope(ModuleDefinition module, AssemblyNameReference scope)
    {
        AssemblyNameReference? existing = module.AssemblyReferences.FirstOrDefault(x => x.FullName == scope.FullName);
        if (existing is not null) return existing;
        module.AssemblyReferences.Add(scope);
        return scope;
    }
    private static TypeDefinition Define(AssemblyDefinition assembly, string ns, string name, bool isPublic = true)
    {
        var type = new TypeDefinition(ns, name, isPublic ? TypeAttributes.Public : TypeAttributes.NotPublic);
        assembly.MainModule.Types.Add(type);
        return type;
    }
    private static void Forward(AssemblyDefinition assembly, string ns, string name, AssemblyNameReference scope) =>
        assembly.MainModule.ExportedTypes.Add(new ExportedType(ns, name, assembly.MainModule, RegisterScope(assembly.MainModule, scope))
        { Attributes = TypeAttributes.Public | TypeAttributes.Forwarder });
    private static string Save(AssemblyDefinition assembly, string directory)
    {
        string path = Path.Combine(directory, assembly.Name.Name + ".dll");
        assembly.Write(path, new WriterParameters { DeterministicMvid = true, Timestamp = 0 });
        return path;
    }

    public static int Run(string directory)
    {
        directory = Path.GetFullPath(directory);
        if (Directory.Exists(directory) || File.Exists(directory)) throw new IOException("Self-test output must be new.");
        Directory.CreateDirectory(directory);
        var passed = new List<string>();
        void Check(bool condition, string name)
        {
            if (!condition) throw new InvalidDataException("Failed: " + name);
            passed.Add(name);
        }
        using var target = Assembly("Fixture.Target");
        Define(target, "System", "Object");
        Define(target, "Example", "ForwardedObject");
        TypeDefinition memory = Define(target, "System", "Memory`1");
        memory.GenericParameters.Add(new GenericParameter("T", memory));
        Define(target, "System.Threading.Tasks.Sources", "IValueTaskSource");
        var outer = Define(target, "Example", "Outer");
        outer.NestedTypes.Add(new TypeDefinition("", "Inner", TypeAttributes.NestedPublic));
        Define(target, "Example", "TargetPrivate", false);
        Define(target, "Example", "HiddenOwner");
        Define(target, "Example", "BrokenForwarder");
        Define(target, "Example", "Cycle");
        string targetPath = Save(target, directory);

        using var facade = Assembly("Fixture.Facade");
        Forward(facade, "Example", "ForwardedObject", Scope(target));
        Forward(facade, "Example", "Cycle", new AssemblyNameReference("Fixture.Core", Version));
        string facadePath = Save(facade, directory);
        using var core = Assembly("Fixture.Core");
        Forward(core, "Example", "ForwardedObject", Scope(facade));
        Define(core, "Example", "HiddenOwner", false);
        Forward(core, "Example", "BrokenForwarder", new AssemblyNameReference("Missing.Framework", Version));
        Forward(core, "Example", "Cycle", Scope(facade));
        string corePath = Save(core, directory);
        string[] profilePaths = [corePath, facadePath, targetPath];
        var originalHashes = profilePaths.ToDictionary(p => p, Program.Hash);

        using var client = Assembly("Fixture.Client");
        TypeDefinition consumer = Define(client, "Example", "Consumer");
        TypeReference Ref(string ns, string name, AssemblyNameReference? scope = null) =>
            new(ns, name, client.MainModule, RegisterScope(client.MainModule, scope ?? Scope(core)));
        void Field(string name, TypeReference type) => consumer.Fields.Add(new(name, FieldAttributes.Public, type));
        var memoryReference = Ref("System", "Memory`1");
        memoryReference.GenericParameters.Add(new GenericParameter("T", memoryReference));
        var generic = new GenericInstanceType(memoryReference);
        generic.GenericArguments.Add(client.MainModule.TypeSystem.Int32);
        Field("Memory", generic);
        Field("ValueTaskSource", Ref("System.Threading.Tasks.Sources", "IValueTaskSource"));
        // System.Object has a special ELEMENT_TYPE_OBJECT encoding. Use an ordinary exact-name type to
        // exercise an actual TypeRef forwarding chain, rather than a primitive signature element.
        Field("Object", Ref("Example", "ForwardedObject"));
        Field("Nested", new TypeReference("", "Inner", client.MainModule, Scope(core))
            { DeclaringType = Ref("Example", "Outer") });
        Field("Missing", Ref("Example", "Absent"));
        Field("PrivateTarget", Ref("Example", "TargetPrivate"));
        Field("PrivateOwner", Ref("Example", "HiddenOwner"));
        Field("BrokenForwarder", Ref("Example", "BrokenForwarder"));
        Field("Cycle", Ref("Example", "Cycle"));
        Field("VendorMemory", Ref("System", "Memory`1", new AssemblyNameReference("Vendor.SDK", Version)));
        Field("WrongVersion", Ref("System", "Memory`1", new AssemblyNameReference(core.Name.Name, new Version(2, 0, 0, 0))));
        var method = new MethodDefinition("Value", MethodAttributes.Public | MethodAttributes.Static, client.MainModule.TypeSystem.Int32);
        method.Body.Instructions.Add(Instruction.Create(OpCodes.Ldc_I4, 7));
        method.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
        consumer.Methods.Add(method);
        string clientPath = Save(client, directory);
        string clientHash = Program.Hash(clientPath);
        using var loaded = AssemblyDefinition.ReadAssembly(clientPath, new ReaderParameters { InMemory = true });
        string bodyHash = Program.BodyFingerprint(loaded.MainModule);
        using var profile = new TargetFrameworkReferenceAdapter(profilePaths);
        FrameworkReferenceAdaptation result = profile.Adapt(loaded.MainModule);
        string outputPath = Path.Combine(directory, "Fixture.Client.adapted.dll");
        loaded.Write(outputPath, new WriterParameters { DeterministicMvid = true, Timestamp = 0 });
        using var check = AssemblyDefinition.ReadAssembly(outputPath, new ReaderParameters { InMemory = true });
        var fields = check.MainModule.GetType("Example.Consumer").Fields.ToDictionary(f => f.Name, f => f.FieldType);
        string Owner(string field) => ((AssemblyNameReference)fields[field].Scope).Name;
        File.WriteAllText(Path.Combine(directory, "ADAPTATION.json"), JsonSerializer.Serialize(new
        {
            adaptation = result,
            field_scopes = fields.ToDictionary(x => x.Key, x => x.Value.Scope.ToString()),
        }, Program.JsonOptions) + "\n");
        Check(Owner("Memory") == target.Name.Name, "missing generic type moved to exact public target definition");
        Check(fields["Memory"] is GenericInstanceType g && g.GenericArguments.Single().FullName == "System.Int32",
            "generic arity and argument survived emission");
        Check(Owner("ValueTaskSource") == target.Name.Name, "interface ownership retargeted");
        Check(Owner("Object") == core.Name.Name, "existing two-hop forwarder preserved original scope");
        Check(Owner("Nested") == target.Name.Name && fields["Nested"].FullName == "Example.Outer/Inner",
            "nested type family resolved and preserved");
        Check(Owner("Missing") == core.Name.Name, "absent type not guessed");
        Check(Owner("PrivateTarget") == core.Name.Name, "private target not substituted");
        Check(Owner("PrivateOwner") == core.Name.Name, "existing private ownership not bypassed");
        Check(Owner("BrokenForwarder") == core.Name.Name && result.Decisions.Any(d => d.Status == "unresolved_forwarder"),
            "missing forwarder destination rejected despite same-named candidate");
        Check(Owner("Cycle") == core.Name.Name, "cyclic forwarder rejected");
        Check(Owner("VendorMemory") == "Vendor.SDK", "unlisted SDK scope unchanged");
        Check(((AssemblyNameReference)fields["WrongVersion"].Scope).Version == new Version(2, 0, 0, 0) &&
            result.Decisions.Any(d => d.Status == "source_identity_mismatch"), "mismatched source identity rejected");
        Check(Program.BodyFingerprint(check.MainModule) == bodyHash, "method instructions unchanged after rewrite");
        Check(Program.Hash(clientPath) == clientHash && originalHashes.All(x => Program.Hash(x.Key) == x.Value),
            "original reference and client files immutable");
        Check(result.Decisions.Where(d => d.Status == "retargeted").All(d => d.Evidence.All(e => e.Token != 0 && File.Exists(e.Path))),
            "retargeting backed by persisted TypeDef token and file evidence");

        using var alternative = Assembly("Fixture.Alternative");
        TypeDefinition duplicate = Define(alternative, "System", "Memory`1");
        duplicate.GenericParameters.Add(new GenericParameter("T", duplicate));
        string alternativePath = Save(alternative, directory);
        using var ambiguousProfile = new TargetFrameworkReferenceAdapter([.. profilePaths, alternativePath]);
        using var ambiguousClient = AssemblyDefinition.ReadAssembly(clientPath, new ReaderParameters { InMemory = true });
        FrameworkReferenceAdaptation ambiguous = ambiguousProfile.Adapt(ambiguousClient.MainModule);
        FieldDefinition ambiguousMemory = ambiguousClient.MainModule.GetType("Example.Consumer").Fields.Single(f => f.Name == "Memory");
        Check(((AssemblyNameReference)ambiguousMemory.FieldType.Scope).Name == core.Name.Name &&
            ambiguous.Decisions.Any(d => d.Types.Contains("System.Memory`1") && d.Status == "ambiguous"),
            "ambiguous public definitions rejected");
        string receipt = Path.Combine(directory, "SELF_TEST_RECEIPT.json");
        File.WriteAllText(receipt, JsonSerializer.Serialize(new { passed = passed.Count, checks = passed,
            scope = "synthetic metadata reference adaptation; no game runtime claim", runtime_verified = false }, Program.JsonOptions) + "\n");
        Console.WriteLine(File.ReadAllText(receipt));
        return 0;
    }
}
