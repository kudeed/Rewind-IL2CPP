using System.Collections.Concurrent;
using System.Diagnostics;
using System.Reflection.Metadata;
using System.Text;
using ICSharpCode.Decompiler;
using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.OutputVisitor;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.Metadata;
using ICSharpCode.Decompiler.TypeSystem;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;

namespace Rewind.Output;

public sealed class DecompileOptions
{
    public string OutputDirectory = "out";
    /// <summary>Assemblies whose method bodies are recovered; null means all of them.</summary>
    public Func<AssemblyModel, bool>? Assemblies;
    /// <summary>Also turn the rebuilt assemblies into C# source files.</summary>
    public bool WriteSource = true;
    /// <summary>
    /// The C# version the source is written in. A game's source compiled with the compiler of its Unity version
    /// (C# 9 for Unity 2021.2 and later), and source that is to go back into such a project must not use anything
    /// newer (the unsigned shift operator, file-scoped namespaces, ...).
    /// </summary>
    public LanguageVersion Language = LanguageVersion.Latest;
    /// <summary>
    /// Write iterators and async methods as the state machine classes the compiler made of them, instead of
    /// turning them back into "yield return" and "await". That turning back succeeds only where the recovered
    /// code has exactly the shape the C# compiler gives such a class; the class itself is always what ran.
    /// </summary>
    public bool StateMachines;
    /// <summary>Keep compiler-generated local methods and closures as members.</summary>
    public bool RawClosures;
    /// <summary>Preserve explicit single-precision rounding in C# output.</summary>
    public bool PreserveFloatBoundaries = true;
    /// <summary>Keep raw private runtime operations for explicit source projection; bypass lossy cleanup.</summary>
    public bool PreservePrivateInternals = true;
    /// <summary>Optional exact top-level type filter for source-only export.</summary>
    public HashSet<string>? SourceTypes;
    /// <summary>
    /// How many threads recover method bodies; zero for the default (REWIND_THREADS, else one per processor).
    /// What comes out is the same for any number.
    /// </summary>
    public int Threads;
    public Action<string> Log = _ => { };
}

public sealed class DecompileResult
{
    public int Methods, Recovered, Clean, WithGaps, NotEmitted, Crashed;
    /// <summary>Methods of generic types and generic methods: with a body their reference-type instantiations share, and how many of those were recovered completely.</summary>
    public int GenericShared, GenericClean, GenericWithGaps;
    public int Types, TypesWithErrors;
    public Dictionary<string, int> EmitFailures = [];
    public List<string> AssembliesWritten = [];
}

/// <summary>Runs the whole pipeline: recover method bodies, rebuild the assemblies with them, write C# source.</summary>
public static partial class Decompiler
{
    public static DecompileResult Run(Il2CppModel model, ProgramAnalysis? program, DecompileOptions options)
    {
        var result = new DecompileResult();
        var sw = Stopwatch.StartNew();
        var emitter = new AssemblyEmitter(model);
        emitter.Build();
        options.Log($"rebuilt {model.Assemblies.Length} assemblies ({sw.ElapsedMilliseconds} ms)");

        var selected = new HashSet<AssemblyModel>(model.Assemblies.Where(a => options.Assemblies?.Invoke(a) ?? true));
        var report = new StringBuilder();
        var evidence = new RecoveryEvidence(model, program, selected);
        // A row names the method in full: the assembly and the parameter types tell overloads and same-named types
        // in different assemblies apart, which "Type::Method" alone does not.
        static string Row(string kind, MethodDef method, string reason) =>
            $"{kind}\t{method.FullName}\t{reason}\t{method.DeclaringType.Assembly.Name}\t{method.FullName}({string.Join(", ", method.Parameters.Select(p => p.Type.DisplayName))})";

        if (program != null)
        {
            sw.Restart();
            foreach (Rewind.Analysis.Runtime.PInvokeImport import in program.PInvokeDeclarations) emitter.SetImport(import);
            var bodies = new BodyEmitter(emitter, model) { RawAllocator = program.RawAllocator, TypeFromHandle = program.TypeFromHandle };
            bool genericBodies = Environment.GetEnvironmentVariable("REWIND_NO_GENERIC_BODIES") == null;
            bool genericGaps = Environment.GetEnvironmentVariable("REWIND_NO_GENERIC_GAPS") == null;
            // What is to be recovered, in the order of the methods: a method's own code, or - for a generic
            // definition, which has no single compiled body, only its instantiations have - the one that its
            // instantiations over reference types share. That one does the same whatever those types are:
            // recovered with the definition's own type parameters as the arguments, it is the definition's body.
            // Where parts of it are left open they are marked as in any other method (the placeholder said
            // nothing of what the method does; what was recovered around a gap does).
            var work = new List<(MethodDef Method, MethodInst? Shared)>();
            var sharedGaps = new HashSet<MethodDef>();
            foreach (MethodDef method in model.Methods)
            {
                if (!selected.Contains(method.DeclaringType.Assembly)) continue;
                if (!AssemblyEmitter.HasIlBody(method)) continue;
                if (method.DeclaringType.GenericParameters.Length != 0 || method.GenericParameters.Length != 0)
                {
                    if (genericBodies && SharedBody(model, program, method) is { } open) work.Add((method, open));
                }
                else if (method.Address != 0) work.Add((method, null));
            }
            // Recovered on several threads; written into the assemblies, counted and reported here, one after
            // the other in the order of the methods, so that the output does not depend on the threads.
            RecoveryThreads.Run(program, work.Count, options.Threads,
                (pipeline, i) =>
                {
                    try
                    {
                        return (Recovered: work[i].Shared is { } open ? pipeline.Recover(open) : pipeline.Recover(work[i].Method), Failure: (Exception?)null);
                    }
                    catch (Exception e)
                    {
                        return (Recovered: (HMethod?)null, Failure: e);
                    }
                },
                (i, recovered) =>
                {
                    MethodDef method = work[i].Method;
                    if (work[i].Shared != null)
                    {
                        result.GenericShared++;
                        try
                        {
                            if (recovered.Failure != null) throw recovered.Failure;
                            HMethod generic = recovered.Recovered!;
                            if (generic.Problems.Count != 0)
                            {
                                sharedGaps.Add(method);
                                report.AppendLine(Row("generic, gaps", method, string.Join(" | ", generic.Problems.Distinct().Take(6))));
                                if (!genericGaps)
                                {
                                    evidence.Record(method, work[i].Shared!.Address, "generic_gaps_not_emitted", generic);
                                    return;
                                }
                            }
                            string? refused = bodies.Emit(method, generic);
                            evidence.Record(method, work[i].Shared!.Address, refused != null ? "not_emitted" : generic.Problems.Count == 0 ? "clean" : "gaps", generic, refused);
                            if (refused != null) report.AppendLine(Row("generic, not emitted", method, refused));
                            else if (generic.Problems.Count == 0) result.GenericClean++;
                            else result.GenericWithGaps++;
                        }
                        catch (Exception e)
                        {
                            report.AppendLine(Row("generic, failed", method, $"{e.GetType().Name}: {e.Message}"));
                            evidence.Record(method, work[i].Shared!.Address, "failed", recovered.Recovered, $"{e.GetType().Name}: {e.Message}");
                        }
                        return;
                    }
                    result.Methods++;
                    try
                    {
                        if (recovered.Failure != null) throw recovered.Failure;
                        HMethod h = recovered.Recovered!;
                        result.Recovered++;
                        string? why = bodies.Emit(method, h);
                        evidence.Record(method, method.Address, why != null ? "not_emitted" : h.Problems.Count == 0 ? "clean" : "gaps", h, why);
                        if (why != null)
                        {
                            result.NotEmitted++;
                            result.EmitFailures[why] = result.EmitFailures.GetValueOrDefault(why) + 1;
                            report.AppendLine(Row("not emitted", method, why));
                        }
                        else if (h.Problems.Count == 0) result.Clean++;
                        else
                        {
                            result.WithGaps++;
                            report.AppendLine(Row("gaps", method, string.Join(" | ", h.Problems.Distinct().Take(6))));
                        }
                    }
                    catch (Exception e)
                    {
                        result.Crashed++;
                        report.AppendLine(Row("failed", method, $"{e.GetType().Name}: {e.Message}"));
                        evidence.Record(method, method.Address, "failed", recovered.Recovered, $"{e.GetType().Name}: {e.Message}");
                    }
                });
            ClosedArraySpecializations.Run(model,program,emitter,bodies,work.Select(w=>w.Method),sharedGaps,options);
            options.Log($"method bodies: {result.Methods} with native code, {result.Clean} recovered completely, {result.WithGaps} with gaps marked in the output, " +
                        $"{result.NotEmitted + result.Crashed} left as stubs ({sw.ElapsedMilliseconds} ms)");
            if (result.GenericShared != 0)
                options.Log($"generic definitions: {result.GenericShared} with a body shared by their reference-type instantiations, {result.GenericClean} of them recovered completely, " +
                            $"{result.GenericWithGaps} with gaps marked in the output");
        }

        sw.Restart();
        string assemblyDirectory = Path.Combine(options.OutputDirectory, "assemblies");
        result.AssembliesWritten = emitter.Write(assemblyDirectory);
        foreach (string warning in emitter.Warnings.Take(20)) options.Log("warning: " + warning);
        options.Log($"wrote {result.AssembliesWritten.Count} assemblies to {assemblyDirectory} ({sw.ElapsedMilliseconds} ms)");

        Directory.CreateDirectory(options.OutputDirectory);
        File.WriteAllText(Path.Combine(options.OutputDirectory, "recovery-report.tsv"), report.ToString());
        evidence.Write(options.OutputDirectory);

        if (options.WriteSource)
        {
            sw.Restart();
            string sourceDirectory = Path.Combine(options.OutputDirectory, "src");
            foreach (AssemblyModel asm in model.Assemblies)
            {
                if (!selected.Contains(asm)) continue;
                string path = result.AssembliesWritten.FirstOrDefault(p =>
                    string.Equals(Path.GetFileNameWithoutExtension(p), Path.GetFileNameWithoutExtension(asm.ImageName), StringComparison.OrdinalIgnoreCase)) ?? "";
                if (path.Length == 0) continue;
                WriteSource(path, assemblyDirectory, Path.Combine(sourceDirectory, asm.Name), result, options);
            }
            options.Log($"C# source: {result.Types} types written to {sourceDirectory}, {result.TypesWithErrors} with parts the C# decompiler rejected ({sw.ElapsedMilliseconds} ms)");
        }
        return result;
    }

    /// <summary>
    /// The compiled body that a generic definition's instantiations share, as an instantiation over the
    /// definition's own type parameters; null when there is none (the definition is not used at all).
    /// Instantiations over reference types share one body. With full generic sharing (Unity 2022 and later)
    /// those over value types share another, compiled for IL2CPP's placeholder types
    /// (Unity.IL2CPP.Metadata.__Il2CppFullySharedGenericType / __Il2CppFullySharedGenericStructType): a
    /// definition only ever used with value types still has that one, and what it does with its type
    /// parameters (typeof(T) and the like) reads back the same way. The reference-type body comes first.
    /// </summary>
    private static MethodInst? SharedBody(Il2CppModel model, ProgramAnalysis program, MethodDef method)
    {
        static bool IsObject(TypeSig t) => t is PrimitiveSig { Element: Rewind.Runtime.Il2CppTypeEnum.Object };
        static bool IsFullyShared(TypeSig t) => t is TypeDefSig { Definition: { Namespace: "Unity.IL2CPP.Metadata" } d }
            && d.Name.StartsWith("__Il2CppFullyShared", StringComparison.Ordinal);
        ulong fullyShared = 0;
        foreach (MethodInst inst in program.InstsOf(method))
        {
            if (inst.Address == 0) continue;
            if (inst.ClassArguments.All(IsObject) && inst.MethodArguments.All(IsObject)) return Open(inst.Address);
            if (fullyShared == 0 && Environment.GetEnvironmentVariable("REWIND_NO_FULLY_SHARED_BODIES") == null
                && inst.ClassArguments.Concat(inst.MethodArguments).All(a => IsObject(a) || IsFullyShared(a)))
                fullyShared = inst.Address;
        }
        return fullyShared == 0 ? null : Open(fullyShared);

        MethodInst Open(ulong address) => new MethodInst
        {
            Method = method,
            ClassArguments = method.DeclaringType.GenericParameters.Select(p => (TypeSig)model.Sigs.GenericParam(p)).ToArray(),
            MethodArguments = method.GenericParameters.Select(p => (TypeSig)model.Sigs.GenericParam(p)).ToArray(),
            Address = address,
        };
    }

    private static string SafeName(string name)
    {
        var sb = new StringBuilder(name.Length);
        foreach (char c in name)
            sb.Append(char.IsLetterOrDigit(c) || c is '_' or '.' or '-' ? c : '_');
        string s = sb.ToString();
        return s.Length > 120 ? s[..120] : s.Length == 0 ? "_" : s;
    }

    private static CSharpDecompiler NewDecompiler(string assemblyPath, string assemblyDirectory, LanguageVersion language, bool stateMachines, bool iteratorsOnly = false,
        bool closures = false)
    {
        var module = new PEFile(assemblyPath);
        var resolver = new UniversalAssemblyResolver(assemblyPath, false, module.Metadata.DetectTargetFrameworkId());
        resolver.AddSearchDirectory(assemblyDirectory);
        var settings = new DecompilerSettings(language)
        {
            ThrowOnAssemblyResolveErrors = false,
            // Compiler-generated members are part of what was compiled; keep the names as they are.
            ShowXmlDocumentation = false,
            // Keep explicit delegate constructions; a method-group cast can
            // be ill-typed on C# 9 and may introduce caching on newer compilers.
            UseImplicitMethodGroupConversion = false,
        };
        if (stateMachines)
        {
            settings.YieldReturn = false;
            if (!iteratorsOnly) settings.AsyncAwait = false;
        }
        // Lambdas and local functions as the closure classes the compiler made (see ClosureCheck).
        if (closures)
        {
            settings.AnonymousMethods = false;
            settings.LocalFunctions = false;
            settings.ExpressionTrees = false;
        }
        return new CSharpDecompiler(module, resolver, settings);
    }

    /// <summary>Export an already recovered assembly without rerunning native analysis.</summary>
    public static DecompileResult ExportSource(string assemblyPath, string targetDirectory, DecompileOptions options)
    {
        var result = new DecompileResult();
        string fullPath = Path.GetFullPath(assemblyPath);
        WriteSource(fullPath, Path.GetDirectoryName(fullPath)!, targetDirectory, result, options);
        return result;
    }

    /// <summary>Decompiles one rebuilt assembly into one C# file per top-level type.</summary>
    private static void WriteSource(string assemblyPath, string assemblyDirectory, string targetDirectory, DecompileResult result, DecompileOptions options)
    {
        if (!options.PreservePrivateInternals)
            throw new ArgumentException("Lossy source cleanup is disabled: preserve private operations and resolve unsupported code with typed recovery or semantic source projection.", nameof(options));
        Action<string> log = options.Log;
        using var sourceImage = new SourceFloatBoundaries(assemblyPath, options.PreserveFloatBoundaries);
        assemblyPath = sourceImage.AssemblyPath;
        if (sourceImage.Calls != 0)
            log($"source precision: {sourceImage.Calls} explicit rounding boundaries, {sourceImage.Negations} typed negations in temporary {Path.GetFileName(assemblyPath)}");
        List<(string File, FullTypeName Name)> types = [];
        try
        {
            using var probe = new PEFile(assemblyPath);
            MetadataReader reader = probe.Metadata;
            var used = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
            foreach (TypeDefinitionHandle handle in reader.TypeDefinitions)
            {
                TypeDefinition definition = reader.GetTypeDefinition(handle);
                if (!definition.GetDeclaringType().IsNil) continue; // nested types come with their parent
                string name = reader.GetString(definition.Name), ns = reader.GetString(definition.Namespace);
                if (name is "<Module>" or "__Rewind" || name == SourceFloatBoundaries.HelperName && ns.Length == 0) continue;
                if (options.SourceTypes != null && !options.SourceTypes.Contains(ns.Length == 0 ? name : ns + "." + name)) continue;
                string relative = Path.Combine(ns.Length == 0 ? "" : Path.Combine(ns.Split('.').Select(SafeName).ToArray()), SafeName(name));
                string unique = relative;
                for (int n = 2; !used.Add(unique); n++) unique = relative + "_" + n;
                types.Add((unique + ".cs", handle.GetFullTypeName(reader)));
            }
        }
        catch (Exception e)
        {
            log($"warning: {Path.GetFileName(assemblyPath)} could not be opened for source output: {e.Message}");
            return;
        }

        if (options.SourceTypes != null && types.Count != options.SourceTypes.Count)
            throw new InvalidDataException("one or more requested top-level source types were not found");
        Directory.CreateDirectory(targetDirectory);
        int errors = 0, iteratorsKept = 0, closuresKept = 0, markersUsed = 0, precisionUsed = 0;
        var work = new ConcurrentQueue<(string File, FullTypeName Name)>(types);
        int workers = Math.Max(1, Math.Min(Environment.ProcessorCount, 1 + types.Count / 64));
        var threads = new List<Thread>();
        for (int w = 0; w < workers; w++)
        {
            var thread = new Thread(() =>
            {
                CSharpDecompiler decompiler;
                CSharpDecompiler? machines = null, closures = null;
                bool machinesUsed = false;
                // (What DecompileTypeAsString writes with: the formatting of these settings, which NewDecompiler keeps.)
                CSharpFormattingOptions format = new DecompilerSettings(options.Language).CSharpFormattingOptions;
                try
                {
                    decompiler = NewDecompiler(assemblyPath, assemblyDirectory, options.Language, options.StateMachines, closures: options.RawClosures);
                }
                catch (Exception e)
                {
                    log($"warning: C# decompiler could not load {Path.GetFileName(assemblyPath)}: {e.Message}");
                    return;
                }
                while (work.TryDequeue(out var item))
                {
                    string text;
                    bool failed = false;
                    try
                    {
                        SyntaxTree tree = decompiler.DecompileType(item.Name);
                        // An iterator whose rebuilt "yield return"s could never advance: the type is written with its
                        // state machines as classes instead (see IteratorCheck).
                        if (!options.StateMachines && !NoIteratorCheck && IteratorCheck.HasStuckIterator(tree))
                        {
                            machines ??= NewDecompiler(assemblyPath, assemblyDirectory, options.Language, stateMachines: true, iteratorsOnly: true, closures: options.RawClosures);
                            tree = machines.DecompileType(item.Name);
                            machinesUsed = true;
                            Interlocked.Increment(ref iteratorsKept);
                        }
                        // A closure class named and not written: the type with its closures as classes.
                        if (!NoClosureCheck && ClosureCheck.NamesMissingClosure(tree))
                        {
                            CSharpDecompiler with = machinesUsed
                                ? NewDecompiler(assemblyPath, assemblyDirectory, options.Language, stateMachines: true, iteratorsOnly: true, closures: true)
                                : closures ??= NewDecompiler(assemblyPath, assemblyDirectory, options.Language, options.StateMachines, closures: true);
                            tree = with.DecompileType(item.Name);
                            Interlocked.Increment(ref closuresKept);
                        }
                        machinesUsed = false;
                        var writer = new StringWriter();
                        tree.AcceptVisitor(new CSharpOutputVisitor(writer, format));
                        text = writer.ToString();
                    }
                    catch (Exception e)
                    {
                        failed = true;
                        text = DecompileMemberwise(decompiler, item.Name, e);
                    }
                    if (MarkFailedMembers(ref text)) failed = true;
                    SanitizeIdentifiers(ref text);
                    if (text.Contains("__Rewind.", StringComparison.Ordinal)) Interlocked.Exchange(ref markersUsed, 1);
                    if (sourceImage.Calls != 0 && text.Contains(SourceFloatBoundaries.HelperName, StringComparison.Ordinal))
                        Interlocked.Exchange(ref precisionUsed, 1);
                    if (failed) Interlocked.Increment(ref errors);
                    string file = Path.Combine(targetDirectory, item.File);
                    Directory.CreateDirectory(Path.GetDirectoryName(file)!);
                    File.WriteAllText(file, text);
                }
            }, 256 << 20);
            thread.Start();
            threads.Add(thread);
        }
        foreach (Thread t in threads) t.Join();
        // The marker calls the written bodies make (__Rewind.Note, .Opaque, .Effect) name a type the body writer
        // adds to the rebuilt assembly; it is not written from the metadata, so the file that declares it is.
        if (markersUsed != 0) File.WriteAllText(Path.Combine(targetDirectory, "__Rewind.cs"), MarkerHelper);
        if (precisionUsed != 0) File.WriteAllText(Path.Combine(targetDirectory, SourceFloatBoundaries.HelperName + ".cs"), SourceFloatBoundaries.HelperSource);
        if (iteratorsKept != 0)
            log($"note:     {iteratorsKept} types written with their iterators as state machine classes: the C# decompiler's \"yield return\" for them could not advance");
        if (closuresKept != 0)
            log($"note:     {closuresKept} types written with their lambdas and local functions as closure classes: a body named a closure class the C# decompiler left out");
        lock (result)
        {
            result.Types += types.Count;
            result.TypesWithErrors += errors;
        }
    }

    private static readonly bool NoClosureCheck = Environment.GetEnvironmentVariable("REWIND_NO_CLOSURE_CHECK") != null;
    private static readonly bool NoIteratorCheck = Environment.GetEnvironmentVariable("REWIND_NO_ITERATOR_CHECK") != null;

    private const string FailedMember = "// ILSpy could not decompile this member";

    /// <summary>
    /// The type the marker calls in the written bodies need. Its members say what the decompiler could not put back:
    /// <c>Note</c> does nothing (a gap whose code is not needed to compile), <c>Opaque</c> and <c>Effect</c> throw if
    /// the method is ever called, because the value or the call they stand for was not recovered.
    /// </summary>
    private const string MarkerHelper = """
        internal static class __Rewind
        {
            internal static T Opaque<T>(string what) { throw new System.NotSupportedException(what); }
            internal static void Effect(string what) { throw new System.NotSupportedException(what); }
            internal static void Note(string what) { }
            internal static ref T Ref<T>(T value) => ref RefCell<T>.Value;
            internal static int Sign(System.Numerics.BigInteger value) => value.Sign;
            private static class RefCell<T> { internal static T Value; }
            internal static uint StringHash(string s) { uint num = 0u; if (s != null) { num = 2166136261u; for (int i = 0; i < s.Length; i++) num = (s[i] ^ num) * 16777619u; } return num; }
            internal static UnityEngine.Vector3 Slerp(in UnityEngine.Vector3 a, in UnityEngine.Vector3 b, float t) => UnityEngine.Vector3.Slerp(a, b, t);
            internal static UnityEngine.Vector3 RotateTowards(in UnityEngine.Vector3 current, in UnityEngine.Vector3 target, float maxRadiansDelta, float maxMagnitudeDelta) => UnityEngine.Vector3.RotateTowards(current, target, maxRadiansDelta, maxMagnitudeDelta);
            internal static UnityEngine.Vector3 Normalize(in UnityEngine.Vector3 v) => UnityEngine.Vector3.Normalize(v);
            internal static UnityEngine.Vector3 Cross(in UnityEngine.Vector3 a, in UnityEngine.Vector3 b) => UnityEngine.Vector3.Cross(a, b);
            internal static UnityEngine.Vector3 Project(in UnityEngine.Vector3 v, in UnityEngine.Vector3 onNormal) => UnityEngine.Vector3.Project(v, onNormal);
            internal static UnityEngine.Vector3 ProjectOnPlane(in UnityEngine.Vector3 v, in UnityEngine.Vector3 planeNormal) => UnityEngine.Vector3.ProjectOnPlane(v, planeNormal);
            internal static UnityEngine.Quaternion Slerp(in UnityEngine.Quaternion a, in UnityEngine.Quaternion b, float t) => UnityEngine.Quaternion.Slerp(a, b, t);
            internal static UnityEngine.Quaternion Lerp(in UnityEngine.Quaternion a, in UnityEngine.Quaternion b, float t) => UnityEngine.Quaternion.Lerp(a, b, t);
            internal static UnityEngine.Quaternion AngleAxis(float angle, in UnityEngine.Vector3 axis) => UnityEngine.Quaternion.AngleAxis(angle, axis);
            internal static UnityEngine.Quaternion FromToRotation(in UnityEngine.Vector3 from, in UnityEngine.Vector3 to) => UnityEngine.Quaternion.FromToRotation(from, to);
            internal static UnityEngine.Quaternion Inverse(in UnityEngine.Quaternion q) => UnityEngine.Quaternion.Inverse(q);
            internal static UnityEngine.Quaternion LookRotation(in UnityEngine.Vector3 forward, in UnityEngine.Vector3 upwards) => UnityEngine.Quaternion.LookRotation(forward, upwards);
            internal static UnityEngine.Matrix4x4 TRS(in UnityEngine.Vector3 pos, in UnityEngine.Quaternion q, in UnityEngine.Vector3 s) => UnityEngine.Matrix4x4.TRS(pos, q, s);
            internal static UnityEngine.Matrix4x4 Inverse(in UnityEngine.Matrix4x4 m) => m.inverse;
            internal static bool TestPlanesAABB(UnityEngine.Plane[] planes, in UnityEngine.Bounds bounds) => UnityEngine.GeometryUtility.TestPlanesAABB(planes, bounds);
        }
        """ + "\n";

    /// <summary>
    /// A member the C# decompiler gave up on comes out as a body of comments: an empty method, which compiles and
    /// does nothing. That must not pass for recovered code, so the body is given the marker a gap has. True when
    /// there was such a member.
    /// </summary>
    private static bool MarkFailedMembers(ref string text)
    {
        if (!text.Contains(FailedMember, StringComparison.Ordinal)) return false;
        var sb = new StringBuilder(text.Length + 256);
        int at = 0;
        while (at < text.Length)
        {
            int end = text.IndexOf('\n', at);
            end = end < 0 ? text.Length : end + 1;
            ReadOnlySpan<char> line = text.AsSpan(at, end - at);
            ReadOnlySpan<char> trimmed = line.TrimStart();
            if (trimmed.StartsWith(FailedMember, StringComparison.Ordinal))
            {
                sb.Append(line[..(line.Length - trimmed.Length)]);
                sb.Append("__Rewind.Note(\"the C# decompiler could not write this member: its code is in the rebuilt assembly only\");");
                sb.Append(line.EndsWith("\r\n", StringComparison.Ordinal) ? "\r\n" : "\n");
            }
            sb.Append(line);
            at = end;
        }
        text = sb.ToString();
        return true;
    }

    /// <summary>
    /// When a whole type cannot be decompiled because one member trips the C# decompiler, decompile the members
    /// one by one so that a single bad method costs only itself.
    /// </summary>
    private static string DecompileMemberwise(CSharpDecompiler decompiler, FullTypeName name, Exception whole)
    {
        var sb = new StringBuilder();
        sb.AppendLine($"// The C# decompiler could not process this type as a whole ({whole.GetType().Name}); members follow one by one.");
        try
        {
            ITypeDefinition? type = decompiler.TypeSystem.MainModule.GetTypeDefinition(name);
            if (type == null) return sb.AppendLine("// type not found").ToString();
            sb.AppendLine($"// {type.FullName}");
            foreach (IMember member in type.Members)
            {
                if (member.MetadataToken.IsNil) continue;
                try
                {
                    sb.AppendLine(decompiler.DecompileAsString(member.MetadataToken));
                }
                catch (Exception e)
                {
                    string reason = (e.InnerException ?? e).Message.Split('\n')[0];
                    sb.AppendLine($"// {member.Name}: not decompiled ({reason})");
                }
            }
        }
        catch (Exception e)
        {
            sb.AppendLine("// " + e.Message.Split('\n')[0]);
        }
        return sb.ToString();
    }
}
