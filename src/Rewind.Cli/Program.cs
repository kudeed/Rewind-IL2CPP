using System.Diagnostics;
using Rewind.Binary;
using Rewind.Input;
using Rewind.Metadata;
using Rewind.Model;
using Rewind.Output;

namespace Rewind.Cli;

internal static class Program
{
    private const string Usage = """
        rewind - Unity IL2CPP decompiler

        usage:
          rewind info <input>                 show what the input is and whether it can be read
          rewind dump <input> [-o <dir>]      write dump.cs: every type and member with addresses and offsets
          rewind decompile <input> [-o <dir>] rebuild the .NET assemblies with recovered method bodies and write
                                              C# source (assemblies/, src/, recovery-report.tsv, recovery-evidence.jsonl)

        <input> may be a game folder, the game's .exe, an APK / XAPK / APKS / AAB, an IPA,
        or the IL2CPP binary itself (GameAssembly.dll, libil2cpp.so, UnityFramework).

        options:
          -o, --out <dir>        output directory (default: ./rewind-out)
          --metadata <file>      use this global-metadata.dat instead of searching for one
          --binary <file>        use this native binary instead of searching for one
          --abi <name>           preferred Android ABI inside a package (arm64-v8a, armeabi-v7a, x86_64, x86)
          --unity <version>      Unity version, when it cannot be detected (e.g. 2022.3.33f1)
          --assembly <name>      decompile: only this assembly (repeatable; default: all)
          --no-source            decompile: write the assemblies only, skip C# source
          --csharp <version>     decompile: write source for this C# version (e.g. 9 for a Unity 2021.2+ project;
                                 default: the latest)
          --state-machines       decompile: write iterators and async methods as the classes the compiler made of
                                 them (no "yield return" or "await")
          --signatures <path>    decompile: signature file or folder for recognizing runtime functions
          --threads <n>          decompile: recover method bodies on this many threads (default: one per processor,
                                 or REWIND_THREADS). The output is the same for any number; 1 keeps the debugging
                                 traces of one method together
          -v, --verbose          print progress details
        """;

    private sealed class Options
    {
        public string Command = "";
        public string? Input, OutDir, Metadata, Binary, Abi, Unity, Signatures, CSharp;
        public bool StateMachines;
        public int Threads;
        public List<string> Assemblies = [];
        public bool Verbose, NoSource;
    }

    private static int Main(string[] args)
    {
        // The desktop app reads this tool's output through a pipe and asks for UTF-8, so that paths outside the
        // console's code page come through intact. The console's code page is changed only when asked.
        if (Environment.GetEnvironmentVariable("REWIND_UTF8_OUTPUT") == "1")
        {
            try
            {
                Console.OutputEncoding = new System.Text.UTF8Encoding(false);
            }
            catch (IOException)
            {
                // No console to change.
            }
        }

        // Method recovery walks deep expression trees recursively; give it room.
        int exit = 0;
        var worker = new Thread(() => exit = Run(args), 1 << 30);
        worker.Start();
        worker.Join();
        return exit;
    }

    private static int Run(string[] args)
    {
        Options? o = Parse(args);
        if (o == null)
        {
            Console.WriteLine(Usage);
            return 2;
        }

        try
        {
            return o.Command switch
            {
                "info" => Info(o),
                "dump" => Dump(o),
                "decompile" => Decompile(o),
                _ => UnknownCommand(o.Command),
            };
        }
        catch (InputException e)
        {
            Console.Error.WriteLine("error: " + e.Message);
            return 1;
        }
        catch (MetadataFormatException e)
        {
            Console.Error.WriteLine("error: " + e.Message);
            return e.NotStandardFormat ? 3 : 1;
        }
        catch (Exception e) when (e is InvalidDataException or NotSupportedException or IOException)
        {
            Console.Error.WriteLine("error: " + e.Message);
            return 1;
        }
    }

    private static int UnknownCommand(string command)
    {
        Console.Error.WriteLine($"error: unknown command '{command}'");
        Console.WriteLine(Usage);
        return 2;
    }

    private static Options? Parse(string[] args)
    {
        if (args.Length == 0 || args[0] is "-h" or "--help" or "help") return null;
        var o = new Options { Command = args[0] };
        for (int i = 1; i < args.Length; i++)
        {
            string a = args[i];
            string? Next() => i + 1 < args.Length ? args[++i] : null;
            switch (a)
            {
                case "-o" or "--out": o.OutDir = Next(); break;
                case "--metadata": o.Metadata = Next(); break;
                case "--binary": o.Binary = Next(); break;
                case "--abi": o.Abi = Next(); break;
                case "--unity": o.Unity = Next(); break;
                case "--signatures": o.Signatures = Next(); break;
                case "--csharp": o.CSharp = Next(); break;
                case "--state-machines": o.StateMachines = true; break;
                case "--threads":
                    if (!int.TryParse(Next(), out o.Threads) || o.Threads < 1)
                    {
                        Console.Error.WriteLine("error: --threads takes a number of threads, 1 or more");
                        return null;
                    }
                    break;
                case "--assembly": if (Next() is { } name) o.Assemblies.Add(name); break;
                case "--no-source": o.NoSource = true; break;
                case "-v" or "--verbose": o.Verbose = true; break;
                default:
                    if (a.StartsWith('-'))
                    {
                        Console.Error.WriteLine($"error: unknown option '{a}'");
                        return null;
                    }
                    if (o.Input != null)
                    {
                        Console.Error.WriteLine($"error: unexpected argument '{a}'");
                        return null;
                    }
                    o.Input = a;
                    break;
            }
        }
        if (o.Input == null)
        {
            Console.Error.WriteLine("error: no input given");
            return null;
        }
        return o;
    }

    private static (GameInput Input, NativeImage Image, Il2CppModel Model) Load(Options o)
    {
        var sw = Stopwatch.StartNew();
        GameInput input = InputResolver.Resolve(o.Input!, o.Metadata, o.Binary, o.Abi);
        UnityVersion? unity = input.UnityVersion;
        if (o.Unity != null)
        {
            if (!UnityVersion.TryParse(o.Unity, out UnityVersion parsed))
                throw new InputException($"'{o.Unity}' is not a Unity version (expected something like 2022.3.33f1).");
            unity = parsed;
        }

        Console.WriteLine($"binary:   {input.BinaryName} ({input.Binary.Length / 1048576.0:F1} MB)");
        Console.WriteLine($"metadata: {input.MetadataName} ({input.Metadata.Length / 1048576.0:F1} MB)");
        foreach (string note in input.Notes) Console.WriteLine("note:     " + note);

        NativeImage image = NativeImage.Load(input.Binary, input.BinaryName);
        Il2CppModel model = Il2CppModel.Load(image, input.Metadata, unity, o.Verbose ? Console.WriteLine : null);

        Console.WriteLine($"target:   {image.Format} {image.Arch} ({image.Os}), Unity {unity?.ToString() ?? "version not detected"}, " +
                          $"metadata v{MetaVersion.Describe(model.Version)}");
        Console.WriteLine($"content:  {model.Assemblies.Length} assemblies, {model.Types.Length} types, {model.Methods.Length} methods, " +
                          $"{model.MethodInsts.Length} generic instantiations");
        if (o.Verbose) Console.WriteLine($"loaded in {sw.ElapsedMilliseconds} ms");
        return (input, image, model);
    }

    private static int Info(Options o)
    {
        var (_, image, model) = Load(o);
        int withBody = model.Methods.Count(m => m.Address != 0);
        int distinct = model.MethodsByAddress.Count;
        Console.WriteLine($"code:     {withBody} methods have native bodies at {distinct} distinct addresses" +
                          (withBody > distinct ? $" ({withBody - distinct} share code with another method)" : ""));
        Console.WriteLine("assemblies:");
        foreach (AssemblyModel a in model.Assemblies.OrderByDescending(a => a.Types.Count))
            Console.WriteLine($"  {a.Name,-48} {a.Types.Count,6} types");
        _ = image;
        return 0;
    }

    private static int Decompile(Options o)
    {
        var (_, image, model) = Load(o);
        string outDir = Path.GetFullPath(o.OutDir ?? "rewind-out");

        Rewind.Analysis.ProgramAnalysis? program = null;
        if (image.Arch is CpuArch.X64 or CpuArch.Arm64)
        {
            IEnumerable<string> files = o.Signatures == null
                ? Rewind.Analysis.Runtime.HelperDiscovery.DefaultSignatureFiles()
                : Directory.Exists(o.Signatures) ? Directory.EnumerateFiles(o.Signatures, "*.sig") : [o.Signatures];
            var found = Rewind.Analysis.Runtime.HelperDiscovery.Discover(model, files, Console.WriteLine);
            Console.WriteLine($"runtime:  {found.Kinds} kinds of support function identified using {found.Source}");
            if (found.Kinds < 20)
                Console.WriteLine("warning:  the runtime's support functions were not recognized (no signature library matches this " +
                                  "Unity version and build configuration); method bodies will be largely incomplete.");
            else if (!found.ExactVersion)
                Console.WriteLine("note:     no signature library for exactly this Unity version; the closest one was used.");
            program = new Rewind.Analysis.ProgramAnalysis(model, found.Helpers, found.Context);
        }
        else
        {
            Console.WriteLine($"note:     method bodies are recovered for x64 and ARM64 code only so far; this {image.Arch} build gets complete " +
                              "types and signatures, with placeholder bodies.");
        }

        var options = new DecompileOptions
        {
            OutputDirectory = outDir,
            WriteSource = !o.NoSource,
            Log = Console.WriteLine,
        };
        if (o.CSharp != null) options.Language = ParseLanguage(o.CSharp);
        options.StateMachines = o.StateMachines;
        options.Threads = o.Threads;
        if (o.Assemblies.Count != 0)
        {
            var wanted = new HashSet<string>(o.Assemblies.Select(a => a.EndsWith(".dll", StringComparison.OrdinalIgnoreCase) ? a[..^4] : a), StringComparer.OrdinalIgnoreCase);
            var missing = wanted.Where(w => !model.Assemblies.Any(a => string.Equals(a.Name, w, StringComparison.OrdinalIgnoreCase))).ToList();
            if (missing.Count != 0) throw new InputException("no such assembly in this game: " + string.Join(", ", missing));
            options.Assemblies = a => wanted.Contains(a.Name);
        }
        DecompileResult result = Rewind.Output.Decompiler.Run(model, program, options);
        Console.WriteLine($"done:     output in {outDir}");
        _ = result;
        return 0;
    }

    /// <summary>"9", "9.0", "7.3", "latest" as a version of the C# language.</summary>
    private static ICSharpCode.Decompiler.CSharp.LanguageVersion ParseLanguage(string text)
    {
        if (text.Equals("latest", StringComparison.OrdinalIgnoreCase)) return ICSharpCode.Decompiler.CSharp.LanguageVersion.Latest;
        string[] parts = text.Split('.');
        if (parts.Length is 1 or 2 && int.TryParse(parts[0], out int major) && major is >= 1 and <= 99)
        {
            int minor = 0;
            if (parts.Length == 1 || (int.TryParse(parts[1], out minor) && minor is >= 0 and <= 9))
            {
                var version = (ICSharpCode.Decompiler.CSharp.LanguageVersion)(major * 100 + minor);
                if (Enum.IsDefined(version)) return version;
            }
        }
        throw new InputException($"'{text}' is not a C# version the source writer knows (expected something like 9 or 7.3).");
    }

    private static int Dump(Options o)
    {
        var (_, _, model) = Load(o);
        string outDir = Path.GetFullPath(o.OutDir ?? "rewind-out");
        Directory.CreateDirectory(outDir);
        var sw = Stopwatch.StartNew();
        string dumpPath = Path.Combine(outDir, "dump.cs");
        new DumpWriter(model).Write(dumpPath);
        Console.WriteLine($"wrote {dumpPath} ({new FileInfo(dumpPath).Length / 1048576.0:F1} MB, {sw.ElapsedMilliseconds} ms)");
        return 0;
    }
}
