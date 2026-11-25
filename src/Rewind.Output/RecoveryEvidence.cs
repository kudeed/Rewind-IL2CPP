using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Output;

/// <summary>
/// Machine-readable recovery ledger. One row per selected method definition, including
/// clean, skipped and failed methods. Original metadata tokens are scoped to their
/// assembly; native addresses are not unique method identities (generic sharing).
/// </summary>
internal sealed class RecoveryEvidence(Il2CppModel model, ProgramAnalysis? program, HashSet<AssemblyModel> selected)
{
    private sealed record Outcome(string Status, ulong BodyAddress, string? Reason, string[] Problems,
        string[] Notes, NativeCallObservation[] UnidentifiedNativeCalls);
    private readonly Dictionary<int, Outcome> _outcomes = [];
    private static readonly JsonSerializerOptions JsonOptions = new() { PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower };

    public void Record(MethodDef method, ulong bodyAddress, string status, HMethod? recovered = null, string? reason = null)
    {
        var row = new Outcome(status, bodyAddress, reason,
            recovered?.Problems.Distinct().ToArray() ?? [],
            recovered?.Notes.Distinct().ToArray() ?? [],
            recovered?.UnidentifiedNativeCalls.Distinct().OrderBy(c => c.InstructionAddress).ThenBy(c => c.TargetAddress).ToArray() ?? []);
        if (!_outcomes.TryAdd(method.Index, row))
            throw new InvalidOperationException($"Duplicate recovery evidence for method definition {method.Index}");
    }

    private static string Hex(ulong v) => $"0x{v:X}";

    public void Write(string directory)
    {
        using var writer = new StreamWriter(Path.Combine(directory, "recovery-evidence.jsonl"), false, new UTF8Encoding(false));
        foreach (MethodDef m in model.Methods)
        {
            if (!selected.Contains(m.DeclaringType.Assembly)) continue;
            bool generic = m.IsGenericDefinition || m.DeclaringType.GenericParameters.Length != 0;
            if (!_outcomes.TryGetValue(m.Index, out Outcome? o))
            {
                string status = !AssemblyEmitter.HasIlBody(m) ? "no_managed_body"
                    : program == null ? "unsupported_architecture"
                    : generic ? "generic_body_not_selected"
                    : m.Address == 0 ? "no_native_body" : "not_attempted";
                o = new Outcome(status, 0, null, [], [], []);
            }
            var range = o.BodyAddress != 0 ? program?.RangeOf(o.BodyAddress) : null;
            string? rangeHash = null;
            if (range is { } r && r.End > r.Start && r.End - r.Start <= int.MaxValue &&
                model.Image.TrySpan(r.Start, (int)(r.End - r.Start), out var bytes))
                rangeHash = Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant();
            var row = new
            {
                schema_version = 1,
                assembly = m.DeclaringType.Assembly.Name,
                image = m.DeclaringType.Assembly.ImageName,
                assembly_index = m.DeclaringType.Assembly.Index,
                method_index = m.Index,
                metadata_token = Hex(m.Token),
                declaring_type = m.DeclaringType.ReflectionName,
                method_name = m.Name,
                return_type = m.ReturnType.DisplayName,
                parameter_types = m.Parameters.Select(p => p.Type.DisplayName).ToArray(),
                parameter_names = m.Parameters.Select(p => p.Name).ToArray(),
                generic_arity = m.GenericParameters.Length,
                declaring_type_generic_arity = m.DeclaringType.GenericParameters.Length,
                is_static = m.IsStatic,
                is_virtual = m.IsVirtual,
                arch = model.Image.Arch.ToString(),
                image_base = Hex(model.Image.ImageBase),
                definition_address = Hex(m.Address),
                body_address = Hex(o.BodyAddress),
                body_rva = o.BodyAddress != 0 && o.BodyAddress >= model.Image.ImageBase ? Hex(o.BodyAddress - model.Image.ImageBase) : null,
                native_range = range is { } n ? new { start = Hex(n.Start), end = Hex(n.End), mapped_bytes_sha256 = rangeHash, source = "native_function_table" } : null,
                status = o.Status,
                reason = o.Reason,
                problems = o.Problems,
                notes = o.Notes,
                // Observations during final HIR construction; not proof that an
                // operation survived optimization, or a complete native call graph.
                unidentified_native_calls = o.UnidentifiedNativeCalls.Select(c => new
                {
                    instruction_address = Hex(c.InstructionAddress),
                    target_address = Hex(c.TargetAddress),
                    c.IsTail,
                    c.NoReturn
                }).ToArray()
            };
            writer.WriteLine(JsonSerializer.Serialize(row, JsonOptions));
        }
    }
}
