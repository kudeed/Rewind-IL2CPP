using System.Diagnostics;
using Rewind.Binary;
using Rewind.Metadata;
using Rewind.Runtime;

namespace Rewind.Lab;

/// <summary>Development harness: probes builds and compares results with ground truth from our own test games.</summary>
internal static class Program
{
    private static int Main(string[] args)
    {
        // Recovery walks expression trees recursively; real games contain very deep ones.
        int result = 0;
        var worker = new Thread(() => result = Run(args), 1 << 30);
        worker.Start();
        worker.Join();
        return result;
    }

    private static int Run(string[] args)
    {
        if (args.Length == 0)
        {
            Console.WriteLine("usage: rewind-lab probe <binary> <global-metadata.dat> [symbols.tsv]");
            return 2;
        }
        // REWIND_RECOVERY_STATS=live: the same every ten seconds while it runs (what is it doing so long?).
        using var live = Environment.GetEnvironmentVariable("REWIND_RECOVERY_STATS") == "live"
            ? new Timer(_ => Console.Error.WriteLine(Rewind.Analysis.Recover.RecoveryStats.Report()), null, 10000, 10000)
            : null;
        try
        {
            int code = args[0] switch
            {
                "probe" => Probe(args[1], args[2], args.Length > 3 ? args[3] : null),
                "truth-model" => TruthModel.Run(LoadModel(args[1]), args[2]),
                "check" => Check(args),
                "emit" => Emit(args[1], args[2]),
                "type-info" => TypeInfo(args),
                "lift" => LiftLab.Dump(LoadModel(args[1]), args[2], args.Length > 3 ? args[3] : null),
                "lift-stats" => LiftLab.Stats(LoadModel(args[1])),
                "norm" => LiftLab.Normalized(LoadModel(args[1]), args[2], args[3]),
                "ir" => LiftLab.PipelineIr(LoadModel(args[1]), args[2], args[3]),
                "generic-try" => GenericLab.Run(LoadModel(args[1]), args[2], args.Length > 3 && args[3] != "-" ? args[3] : null, args.Length > 4 && args[4] != "-" ? args[4] : null, args.Length > 5 ? int.Parse(args[5]) : 6),
                "pinvoke" => LiftLab.PInvoke(LoadModel(args[1]), args[2]),
                "pinvoke-check" => PInvokeCheck.Run(args[1], args[2]),
                "cfg" => CfgProbe(LoadModel(args[1]), Convert.ToUInt64(args[2], 16)),
                "marker-patterns" => LiftLab.MarkerPatterns(LoadModel(args[1]), args[2], args[3], args.Length > 4 ? args[4] : null),
                "copy-check" => LiftLab.CopyCheck(LoadModel(args[1]), args[2], Convert.ToUInt64(args[3], 16), Convert.ToUInt64(args[4], 16)),
                "inline-why" => LiftLab.InlineWhy(LoadModel(args[1]), args[2], Convert.ToUInt64(args[3], 16)),
                "frame-dump" => LiftLab.FrameDump(LoadModel(args[1]), args[2], args[3]),
                "pdb-labels" => PdbLabels.Run(LoadModel(args[1]), args[2], args[3], args[4], args.Length > 5 && args[5] == "oracle"),
                "hir" => LiftLab.Hir(LoadModel(args[1]), args[2], args[3], args.Length > 4 ? int.Parse(args[4]) : 12),
                "type-stats" => TypeLab.Run(LoadModel(args[1]), args[2], args.Length > 3 && args[3] != "-" ? args[3] : null, args.Length > 4 ? int.Parse(args[4]) : 2),
                "hir-stats" => LiftLab.HirStats(LoadModel(args[1]), args[2], args.Length > 3 && args[3] != "-" ? args[3] : null, args.Length > 4 && args[4] == "examples"),
                "layout-check" => LayoutCheck.Run(LoadModel(args[1])),
                "call-stats" => CallStats.Run(LoadModel(args[1]), args[2], args.Length > 3 ? int.Parse(args[3]) : 80),
                "truth-dll" => TruthDll.Run(args[1], args[2]),
                "sig-build" => SigLab.Build(args[1], args[2..]),
                "inline-check" => InlineLab.Check(LoadModel(args[1]), args[2]),
                "gap-cover" => GapCover.Run(LoadModel(args[1]), args[2], args.Length > 3 ? args[3] : null),
                "eh-stats" => EhLab.Stats(LoadModel(args[1]), args.Length > 2 ? args[2] : null),
                "diff-exec" => DiffExec.Run(args[1], args[2], args[3], args.Length > 4 && args[4] != "-" ? args[4] : null, args.Length > 5 ? int.Parse(args[5]) : 60),
                "nearest" => CodeLab.Nearest(LoadModel(args[1]), args[2], args[3..]),
                "code" => CodeLab.Run(LoadModel(args[1]), args[2], args[3..]),
                "sig-apply" => SigLab.Apply(args[1], LoadModel(args[2]), args.Length > 3 ? args[3] : null),
                "sig-near" => SigLab.Near(args[1], LoadModel(args[2]), args[3..]),
                "klass-probe" => KlassLab.Probe(LoadModel(args[1])),
                _ => Fail($"unknown command '{args[0]}'"),
            };
            // REWIND_RECOVERY_STATS: where the time of recovering went (gap-cover reports it itself, with more).
            if (Rewind.Analysis.Recover.RecoveryStats.On && args[0] != "gap-cover") Console.Error.WriteLine(Rewind.Analysis.Recover.RecoveryStats.Report());
            return code;
        }
        catch (Exception e)
        {
            Console.Error.WriteLine(e);
            return 1;
        }
    }

    private static int Fail(string message)
    {
        Console.Error.WriteLine(message);
        return 2;
    }

    /// <summary>type-info &lt;input&gt; &lt;reflection name&gt;...: raw metadata facts about types, for debugging.</summary>
    private static int TypeInfo(string[] args)
    {
        Rewind.Model.Il2CppModel model = LoadModel(args[1]);
        for (int i = 2; i < args.Length; i++)
        {
            Rewind.Model.TypeDef? type = model.FindType(args[i]);
            if (type == null)
            {
                Console.WriteLine($"{args[i]}: not found");
                continue;
            }
            TypeDefRow row = model.Metadata.Types[type.Index];
            Console.WriteLine($"{type.ReflectionName}: flags 0x{row.Flags:X} bitfield 0x{row.Bitfield:X} packCode {row.PackingSizeCode} " +
                              $"specifiedPackCode {row.SpecifiedPackingSizeCode} packIsDefault {row.PackingSizeIsDefault} " +
                              $"sizeIsDefault {row.ClassSizeIsDefault} instanceSize 0x{type.Sizes.InstanceSize:X} nativeSize {type.Sizes.NativeSize}");
            foreach (Rewind.Model.FieldDef f in type.Fields)
                Console.WriteLine($"    {(f.IsStatic ? "static " : "")}{f.Type.DisplayName} {f.Name} @0x{f.Offset:X}");
            foreach (Rewind.Model.MethodDef m in type.Methods) Console.WriteLine($"    method {m.Name} flags 0x{m.Flags:X} impl 0x{m.ImplFlags:X} @0x{m.Address:X}");
        }
        return 0;
    }

    /// <summary>cfg &lt;input&gt; &lt;hex address&gt;: how the function at an address decodes (blocks, endings, problems).</summary>
    private static int CfgProbe(Rewind.Model.Il2CppModel model, ulong address)
    {
        var context = new Rewind.Analysis.ModelCodeContext(model);
        var cfg = Rewind.Analysis.X64.X64Cfg.Build(context, address);
        Console.WriteLine($"limit 0x{cfg.Limit:X}, {cfg.Blocks.Count} blocks, {cfg.Blocks.Sum(b => b.Instructions.Count)} instructions");
        foreach (var b in cfg.Blocks)
        {
            Console.WriteLine($"  0x{b.Start:X} {b.Instructions.Count} {b.End} -> {string.Join(",", b.Successors.Select(x => "0x" + x.ToString("X")))}");
            foreach (var ins in b.Instructions) Console.WriteLine($"      0x{ins.IP:X}  {ins}");
        }
        foreach (string p in cfg.Problems) Console.WriteLine("  problem: " + p);
        return 0;
    }

    /// <summary>emit &lt;input&gt; &lt;outDir&gt;: writes the rebuilt assemblies.</summary>
    private static int Emit(string input, string outDir)
    {
        Rewind.Model.Il2CppModel model = LoadModel(input);
        var sw = Stopwatch.StartNew();
        var emitter = new Rewind.Output.AssemblyEmitter(model);
        emitter.Build();
        long buildMs = sw.ElapsedMilliseconds;
        sw.Restart();
        List<string> written = emitter.Write(outDir);
        Console.WriteLine($"emitted {written.Count}/{model.Assemblies.Length} assemblies to {outDir} (build {buildMs} ms, write {sw.ElapsedMilliseconds} ms)");
        foreach (string w in emitter.Warnings.Take(30)) Console.WriteLine("  warning: " + w);
        if (emitter.Warnings.Count > 30) Console.WriteLine($"  ... {emitter.Warnings.Count - 30} more warnings");
        return 0;
    }

    /// <summary>check &lt;input&gt; [--symbols file.tsv] [--managed dir]: loads any input and compares with truth data.</summary>
    private static int Check(string[] args)
    {
        Rewind.Model.Il2CppModel model = LoadModel(args[1]);
        for (int i = 2; i + 1 < args.Length; i += 2)
        {
            if (args[i] == "--symbols") CompareWithSymbols(model.Image, model.Metadata, model.Binary, args[i + 1]);
            else if (args[i] == "--managed") TruthModel.Run(model, args[i + 1]);
        }
        return 0;
    }

    /// <summary>Loads a model from anything the input resolver understands (folder, exe, apk, ...).</summary>
    internal static Rewind.Model.Il2CppModel LoadModel(string path)
    {
        var sw = Stopwatch.StartNew();
        Rewind.Input.GameInput input = Rewind.Input.InputResolver.Resolve(path);
        NativeImage image = NativeImage.Load(input.Binary, input.BinaryName);
        var model = Rewind.Model.Il2CppModel.Load(image, input.Metadata, input.UnityVersion, Console.WriteLine);
        Console.WriteLine($"loaded {input.Kind}: {image.Format}/{image.Arch}/{image.Os}, unity {input.UnityVersion?.ToString() ?? "unknown"}, " +
                          $"metadata v{MetaVersion.Describe(model.Version)}, {model.Types.Length} types, {model.Methods.Length} methods " +
                          $"({sw.ElapsedMilliseconds} ms)");
        return model;
    }

    private static int Probe(string binaryPath, string metadataPath, string? symbolsPath)
    {
        var sw = Stopwatch.StartNew();
        byte[] metaBytes = File.ReadAllBytes(metadataPath);
        NativeImage image = NativeImage.Load(File.ReadAllBytes(binaryPath), binaryPath);
        Console.WriteLine($"image: {image.Format} {image.Arch} {image.Os} base=0x{image.ImageBase:X} sections={image.Sections.Count} " +
                          $"exports={image.Exports.Count} functions={image.FunctionTable.Count} ({sw.ElapsedMilliseconds} ms)");
        foreach (ImageSection s in image.Sections)
            Console.WriteLine($"  {s.Name,-12} 0x{s.Va:X} +0x{s.Size:X} {s.Flags}");

        int major = MetadataFile.ReadMajorVersion(metaBytes);
        Console.WriteLine($"metadata: declared version {major}, {metaBytes.Length:N0} bytes");

        MetadataFile? metadata = null;
        Il2CppBinary? binary = null;
        Il2CppBinary.Anchors? anchors = null;
        foreach (int candidate in MetaVersion.Candidates(major))
        {
            try
            {
                sw.Restart();
                MetadataFile parsed = MetadataFile.Parse(metaBytes, candidate);
                long parseMs = sw.ElapsedMilliseconds;
                sw.Restart();
                anchors ??= Il2CppBinary.FindAnchors(image, parsed);
                long anchorMs = sw.ElapsedMilliseconds;
                sw.Restart();
                binary = Il2CppBinary.Load(image, parsed, candidate, anchors);
                metadata = parsed;
                Console.WriteLine($"layout {MetaVersion.Describe(candidate)}: OK (parse {parseMs} ms, anchors {anchorMs} ms, tables {sw.ElapsedMilliseconds} ms)");
                break;
            }
            catch (Exception e) when (e is MetadataFormatException or RegistrationNotFoundException)
            {
                Console.WriteLine($"layout {MetaVersion.Describe(candidate)}: rejected - {e.Message}");
            }
        }
        if (metadata == null || binary == null) return 1;

        Console.WriteLine($"widths: {metadata.Widths}");
        Console.WriteLine($"images={metadata.Images.Length} types={metadata.Types.Length} methods={metadata.Methods.Length} " +
                          $"fields={metadata.Fields.Length} params={metadata.Parameters.Length} stringLiterals={metadata.StringLiteralCount}");
        Console.WriteLine($"codeReg=0x{binary.CodeRegistrationVa:X} metaReg=0x{binary.MetadataRegistrationVa:X}");
        Console.WriteLine($"il2cppTypes={binary.TableTypeCount} (+{binary.Types.Count - binary.TableTypeCount} unregistered) " +
                          $"genericInsts={binary.TableGenericInstCount} (+{binary.GenericInsts.Count - binary.TableGenericInstCount}) " +
                          $"methodSpecs={binary.MethodSpecs.Length} genericMethods={binary.GenericMethodTable.Length} " +
                          $"genericMethodPointers={binary.GenericMethodPointers.Length} invokers={binary.InvokerPointers.Length}");

        if (symbolsPath != null) CompareWithSymbols(image, metadata, binary, symbolsPath);
        return 0;
    }

    /// <summary>Checks every method pointer we resolved against the PDB symbol at that address.</summary>
    private static void CompareWithSymbols(NativeImage image, MetadataFile metadata, Il2CppBinary binary, string symbolsPath)
    {
        var namesAt = new Dictionary<ulong, List<string>>();
        foreach (string line in File.ReadLines(symbolsPath))
        {
            string[] parts = line.Split('\t', 3);
            if (parts.Length < 3) continue;
            ulong va = image.ImageBase + Convert.ToUInt64(parts[0], 16);
            if (!namesAt.TryGetValue(va, out List<string>? list)) namesAt[va] = list = [];
            list.Add(parts[2]);
        }

        int total = 0, withPointer = 0, matched = 0, mismatched = 0, noSymbol = 0;
        var examples = new List<string>();
        foreach (ImageRow im in metadata.Images)
        {
            if (!binary.ModulesByName.TryGetValue(im.Name, out RawCodeGenModule? module)) continue;
            for (int t = im.TypeStart; t < im.TypeStart + (int)im.TypeCount; t++)
            {
                TypeDefRow type = metadata.Types[t];
                string typeName = metadata.GetString(type.NameIndex);
                for (int m = type.MethodStart; m < type.MethodStart + type.MethodCount; m++)
                {
                    MethodDefRow method = metadata.Methods[m];
                    total++;
                    int rid = (int)(method.Token & 0xFFFFFF);
                    if (rid == 0 || rid > module.MethodPointers.Length) continue;
                    ulong va = module.MethodPointers[rid - 1];
                    if (va == 0) continue;
                    withPointer++;
                    if (!namesAt.TryGetValue(va, out List<string>? names))
                    {
                        noSymbol++;
                        continue;
                    }
                    // il2cpp names functions <Type>_<Method>_m<hash>; '.' and other punctuation become '_'.
                    string methodName = metadata.GetString(method.NameIndex);
                    string expected = Sanitize(typeName) + "_" + Sanitize(methodName) + "_m";
                    bool ok = false;
                    foreach (string n in names)
                        if (n.Contains(expected, StringComparison.Ordinal))
                        {
                            ok = true;
                            break;
                        }
                    if (ok) matched++;
                    else
                    {
                        mismatched++;
                        if (examples.Count < 12) examples.Add($"{im.Name}: {typeName}::{methodName} @0x{va:X} -> {names[0]} (+{names.Count - 1})");
                    }
                }
            }
        }
        Console.WriteLine($"symbol check: methods={total} withPointer={withPointer} nameMatch={matched} nameMismatch={mismatched} noSymbol={noSymbol}");
        foreach (string e in examples) Console.WriteLine("  mismatch: " + e);
    }

    private static string Sanitize(string name)
    {
        // il2cpp keeps [A-Za-z0-9_], maps '.', '`' and '/' to '_', and writes anything else as U + hex code.
        var sb = new System.Text.StringBuilder(name.Length);
        foreach (char c in name)
        {
            if (char.IsAsciiLetterOrDigit(c) || c == '_') sb.Append(c);
            else if (c is '.' or '`' or '/') sb.Append('_');
            else sb.Append('U').Append(((int)c).ToString(c < 0x100 ? "X2" : "X4"));
        }
        return sb.ToString();
    }
}
