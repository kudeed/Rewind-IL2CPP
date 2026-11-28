using System.Globalization;
using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;
using AssemblyDefinition = Mono.Cecil.AssemblyDefinition;
using MemberReference = Mono.Cecil.MemberReference;

namespace Rewind.Output;

/// <summary>
/// Read-only evidence for members ILSpy rejected. The recovered assembly remains authoritative:
/// no instruction, local, exception region, marker or function pointer is rewritten for source output.
/// </summary>
internal static class RejectedMethodEvidence
{
    private const string Rejected = "// ILSpy could not decompile this member:";

    internal static IReadOnlyList<string> Write(string assemblyPath, string sourceDirectory, string sourceText)
    {
        uint[] tokens = RejectedTokens(sourceText).Distinct().Order().ToArray();
        if (tokens.Length == 0) return [];

        // Read a stable snapshot. Cecil and PEReader both see these same original bytes, and this
        // code never opens the assembly for writing, including when evidence output fails.
        byte[] original = File.ReadAllBytes(assemblyPath);
        string assemblyHash = Convert.ToHexStringLower(SHA256.HashData(original));
        using var cecilStream = new MemoryStream(original, writable: false);
        using var assembly = AssemblyDefinition.ReadAssembly(cecilStream,
            new ReaderParameters { ReadingMode = ReadingMode.Deferred, InMemory = true, ReadWrite = false });
        using var peStream = new MemoryStream(original, writable: false);
        using var pe = new PEReader(peStream);
        var paths = new List<string>();

        foreach (uint token in tokens)
        {
            if (assembly.MainModule.LookupToken(unchecked((int)token)) is not Mono.Cecil.MethodDefinition method || !method.HasBody)
                continue;

            var raw = pe.GetMethodBody(method.RVA);
            byte[] ilBytes = raw.GetILBytes() ?? [];
            byte[] bodyBytes = pe.GetSectionData(method.RVA).GetContent(0, raw.Size).ToArray();
            var text = new StringBuilder();
            text.AppendLine("// C# SOURCE REJECTED: exact recovered IL evidence, not a recovered C# body.");
            text.AppendLine("// Recovery gaps and opaque operands are preserved. This is not runtime acceptance.");
            text.AppendLine($"assembly: {Path.GetFileName(assemblyPath)}");
            text.AppendLine($"assembly_sha256: {assemblyHash}");
            text.AppendLine($"module_mvid: {assembly.MainModule.Mvid:D}");
            text.AppendLine($"method_token: 0x{token:X8}");
            text.AppendLine($"method: {method.FullName}");
            text.AppendLine($"method_rva: 0x{method.RVA:X}");
            text.AppendLine($"method_body_size: {bodyBytes.Length}");
            text.AppendLine($"method_body_sha256: {Convert.ToHexStringLower(SHA256.HashData(bodyBytes))}");
            text.AppendLine($"method_body_hex: {Convert.ToHexString(bodyBytes)}");
            text.AppendLine($"il_size: {ilBytes.Length}");
            text.AppendLine($"il_hex: {Convert.ToHexString(ilBytes)}");
            text.AppendLine($"max_stack: {raw.MaxStack}");
            text.AppendLine($"init_locals: {raw.LocalVariablesInitialized}");
            text.AppendLine("locals:");
            foreach (VariableDefinition variable in method.Body.Variables)
                text.AppendLine($"  V_{variable.Index}: {variable.VariableType.FullName}");
            text.AppendLine("exception_regions:");
            foreach (ExceptionRegion region in raw.ExceptionRegions)
            {
                int filter = region.Kind == ExceptionRegionKind.Filter ? region.FilterOffset : -1;
                int catchToken = region.Kind == ExceptionRegionKind.Catch
                    ? System.Reflection.Metadata.Ecma335.MetadataTokens.GetToken(region.CatchType) : 0;
                text.AppendLine($"  {region.Kind}: try IL_{region.TryOffset:X4}..IL_{region.TryOffset + region.TryLength:X4}; " +
                    $"handler IL_{region.HandlerOffset:X4}..IL_{region.HandlerOffset + region.HandlerLength:X4}; " +
                    $"filter_offset {filter}; catch_token 0x{catchToken:X8}");
            }
            text.AppendLine("instructions:");
            foreach (Instruction instruction in method.Body.Instructions)
                text.AppendLine($"  IL_{instruction.Offset:X4}: {instruction.OpCode.Name,-12} {Operand(instruction.Operand)}".TrimEnd());

            string directory = Path.Combine(sourceDirectory, "rejected-il");
            Directory.CreateDirectory(directory);
            string path = Path.Combine(directory, $"{token:X8}.il");
            File.WriteAllText(path, text.ToString(), new UTF8Encoding(encoderShouldEmitUTF8Identifier: false));
            paths.Add(path);
        }
        return paths;
    }

    private static IEnumerable<uint> RejectedTokens(string source)
    {
        using var reader = new StringReader(source);
        while (reader.ReadLine() is { } line)
        {
            string comment = line.TrimStart();
            if (!comment.StartsWith(Rejected, StringComparison.Ordinal)) continue;
            // Parse only ILSpy's explicit rejection line, never code, string literals or general comments.
            int marker = comment.IndexOf('@', Rejected.Length);
            if (marker < 0 || marker + 9 > comment.Length) continue;
            string value = comment.Substring(marker + 1, 8);
            if (marker + 9 < comment.Length && char.IsAsciiHexDigit(comment[marker + 9])) continue;
            if (uint.TryParse(value, NumberStyles.HexNumber, CultureInfo.InvariantCulture, out uint token) &&
                (token & 0xFF000000) == 0x06000000 && (token & 0x00FFFFFF) != 0)
                yield return token;
        }
    }

    private static string Operand(object? operand) => operand switch
    {
        null => "",
        Instruction target => $"IL_{target.Offset:X4}",
        Instruction[] targets => string.Join(", ", targets.Select(target => $"IL_{target.Offset:X4}")),
        VariableDefinition variable => $"V_{variable.Index} ({variable.VariableType.FullName})",
        ParameterDefinition parameter => $"arg {parameter.Index}: {parameter.Name} ({parameter.ParameterType.FullName})",
        MemberReference member => member.FullName,
        string value => JsonSerializer.Serialize(value),
        IFormattable value => value.ToString(null, CultureInfo.InvariantCulture) ?? "",
        _ => operand.ToString() ?? "",
    };
}
