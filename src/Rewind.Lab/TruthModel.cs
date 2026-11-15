using System.Text;
using System.Text.RegularExpressions;
using Mono.Cecil;
using Rewind.Model;

namespace Rewind.Lab;

/// <summary>
/// Compares the recovered model with the exact IL assemblies the IL2CPP converter consumed (the "Managed"
/// folder in a build's backup directory): every type, field, method signature, property and event.
/// </summary>
internal static partial class TruthModel
{
    [GeneratedRegex(@" mod(req|opt)\([^)]*\)")]
    private static partial Regex Modifier();

    private static string Normalize(string cecilName) =>
        Modifier().Replace(cecilName, "").Replace("0...", "");

    /// <summary>Formats a signature the way Mono.Cecil prints TypeReference.FullName.</summary>
    public static string CecilName(TypeSig sig)
    {
        var sb = new StringBuilder();
        Append(sb, sig);
        return sb.ToString();
    }

    private static void Append(StringBuilder sb, TypeSig sig)
    {
        switch (sig)
        {
            case PrimitiveSig p:
                sb.Append(p.Definition?.ReflectionName ?? p.Element.ToString());
                break;
            case TypeDefSig d:
                sb.Append(d.Definition.ReflectionName);
                break;
            case GenericInstSig g:
                sb.Append(g.Definition.ReflectionName).Append('<');
                for (int i = 0; i < g.Arguments.Length; i++)
                {
                    if (i != 0) sb.Append(',');
                    Append(sb, g.Arguments[i]);
                }
                sb.Append('>');
                break;
            case SzArraySig s:
                Append(sb, s.ElementType);
                sb.Append("[]");
                break;
            case ArraySig a:
                Append(sb, a.ElementType);
                sb.Append('[').Append(',', a.Rank - 1).Append(']');
                break;
            case PointerSig p:
                Append(sb, p.ElementType);
                sb.Append('*');
                break;
            case ByRefSig r:
                Append(sb, r.ElementType);
                sb.Append('&');
                break;
            case GenericParamSig gp:
                sb.Append(gp.Parameter.Name);
                break;
            default:
                sb.Append(sig.DisplayName);
                break;
        }
    }

    public static int Run(Il2CppModel model, string managedDir)
    {
        var resolver = new DefaultAssemblyResolver();
        resolver.AddSearchDirectory(managedDir);
        var parameters = new ReaderParameters { AssemblyResolver = resolver, ReadingMode = ReadingMode.Deferred };

        int assemblies = 0, missingAssemblies = 0;
        int types = 0, typeMissing = 0, baseOk = 0, baseBad = 0, ifaceOk = 0, ifaceBad = 0;
        int fields = 0, fieldBad = 0, methods = 0, methodBad = 0, props = 0, propBad = 0, events = 0, eventBad = 0;
        int generics = 0, genericBad = 0, flagsBad = 0;
        var problems = new List<string>();

        void Problem(string text)
        {
            if (problems.Count < 40) problems.Add(text);
        }

        foreach (AssemblyModel asm in model.Assemblies)
        {
            string path = Path.Combine(managedDir, asm.ImageName);
            if (!File.Exists(path))
            {
                missingAssemblies++;
                Console.WriteLine($"no truth file for image '{asm.ImageName}' ({asm.Types.Count} types)");
                continue;
            }
            assemblies++;
            using AssemblyDefinition cecil = AssemblyDefinition.ReadAssembly(path, parameters);
            var truth = new Dictionary<string, TypeDefinition>(StringComparer.Ordinal);
            foreach (TypeDefinition t in cecil.MainModule.GetTypes()) truth.TryAdd(t.FullName, t);

            if (truth.Count != asm.Types.Count)
                Problem($"{asm.ImageName}: type count {asm.Types.Count} vs truth {truth.Count}");

            foreach (TypeDef def in asm.Types)
            {
                types++;
                if (!truth.TryGetValue(def.ReflectionName, out TypeDefinition? t))
                {
                    typeMissing++;
                    Problem($"{asm.ImageName}: type {def.ReflectionName} not in truth");
                    continue;
                }

                if ((uint)t.Attributes != def.Flags)
                {
                    flagsBad++;
                    Problem($"{def}: flags 0x{def.Flags:X} vs 0x{(uint)t.Attributes:X}");
                }

                string expectedBase = t.BaseType == null ? "" : Normalize(t.BaseType.FullName);
                string actualBase = def.BaseType == null ? "" : CecilName(def.BaseType);
                if (expectedBase == actualBase) baseOk++;
                else
                {
                    baseBad++;
                    Problem($"{def}: base '{actualBase}' vs '{expectedBase}'");
                }

                var expectedIfaces = t.Interfaces.Select(i => Normalize(i.InterfaceType.FullName)).OrderBy(s => s, StringComparer.Ordinal).ToList();
                var actualIfaces = def.Interfaces.Select(CecilName).OrderBy(s => s, StringComparer.Ordinal).ToList();
                if (expectedIfaces.SequenceEqual(actualIfaces)) ifaceOk++;
                else
                {
                    ifaceBad++;
                    Problem($"{def}: interfaces [{string.Join("; ", actualIfaces)}] vs [{string.Join("; ", expectedIfaces)}]");
                }

                generics++;
                if (!t.GenericParameters.Select(g => g.Name).SequenceEqual(def.GenericParameters.Select(g => g.Name)))
                {
                    genericBad++;
                    Problem($"{def}: generic parameters differ");
                }

                // Fields, in declaration order.
                if (t.Fields.Count != def.Fields.Length)
                {
                    fieldBad++;
                    Problem($"{def}: field count {def.Fields.Length} vs {t.Fields.Count}");
                }
                else
                {
                    for (int i = 0; i < def.Fields.Length; i++)
                    {
                        fields++;
                        FieldDefinition tf = t.Fields[i];
                        FieldDef f = def.Fields[i];
                        string expected = Normalize(tf.FieldType.FullName);
                        string actual = CecilName(f.Type);
                        if (tf.Name != f.Name || expected != actual || (ushort)tf.Attributes != f.Attrs)
                        {
                            fieldBad++;
                            Problem($"{def}::{f.Name}: '{actual}' attrs 0x{f.Attrs:X} vs '{tf.Name}' '{expected}' attrs 0x{(ushort)tf.Attributes:X}");
                        }
                    }
                }

                // Methods, in declaration order.
                if (t.Methods.Count != def.Methods.Length)
                {
                    methodBad++;
                    Problem($"{def}: method count {def.Methods.Length} vs {t.Methods.Count}");
                }
                else
                {
                    for (int i = 0; i < def.Methods.Length; i++)
                    {
                        methods++;
                        MethodDefinition tm = t.Methods[i];
                        MethodDef m = def.Methods[i];
                        bool ok = tm.Name == m.Name
                                  && tm.Parameters.Count == m.Parameters.Length
                                  && Normalize(tm.ReturnType.FullName) == CecilName(m.ReturnType)
                                  && (ushort)tm.Attributes == m.Flags
                                  && (ushort)tm.ImplAttributes == m.ImplFlags
                                  && tm.MetadataToken.ToUInt32() == m.Token
                                  && tm.GenericParameters.Select(g => g.Name).SequenceEqual(m.GenericParameters.Select(g => g.Name));
                        string detail = "";
                        if (ok)
                        {
                            for (int p = 0; p < m.Parameters.Length; p++)
                            {
                                ParameterDefinition tp = tm.Parameters[p];
                                ParamDef mp = m.Parameters[p];
                                if (tp.Name != mp.Name || Normalize(tp.ParameterType.FullName) != CecilName(mp.Type) ||
                                    (ushort)tp.Attributes != mp.Attrs)
                                {
                                    ok = false;
                                    detail = $" param {p}: '{mp.Name}' '{CecilName(mp.Type)}' 0x{mp.Attrs:X} vs '{tp.Name}' '{Normalize(tp.ParameterType.FullName)}' 0x{(ushort)tp.Attributes:X}";
                                    break;
                                }
                            }
                        }
                        else
                        {
                            detail = $" sig: '{m.Name}' ret '{CecilName(m.ReturnType)}' flags 0x{m.Flags:X}/0x{m.ImplFlags:X} token 0x{m.Token:X} vs '{tm.Name}' ret '{Normalize(tm.ReturnType.FullName)}' flags 0x{(ushort)tm.Attributes:X}/0x{(ushort)tm.ImplAttributes:X} token 0x{tm.MetadataToken.ToUInt32():X}";
                        }
                        if (!ok)
                        {
                            methodBad++;
                            Problem($"{def}::{m.Name}:{detail}");
                        }
                    }
                }

                if (t.Properties.Count != def.Properties.Length) { propBad++; Problem($"{def}: property count differs"); }
                else
                    for (int i = 0; i < def.Properties.Length; i++)
                    {
                        props++;
                        PropertyDefinition tp = t.Properties[i];
                        PropertyDef p = def.Properties[i];
                        if (tp.Name != p.Name || tp.GetMethod?.Name != p.Getter?.Name || tp.SetMethod?.Name != p.Setter?.Name)
                        {
                            propBad++;
                            Problem($"{def}: property {p.Name} vs {tp.Name}");
                        }
                    }

                if (t.Events.Count != def.Events.Length) { eventBad++; Problem($"{def}: event count differs"); }
                else
                    for (int i = 0; i < def.Events.Length; i++)
                    {
                        events++;
                        EventDefinition te = t.Events[i];
                        EventDef e = def.Events[i];
                        if (te.Name != e.Name || te.AddMethod?.Name != e.Add?.Name || te.RemoveMethod?.Name != e.Remove?.Name ||
                            Normalize(te.EventType.FullName) != CecilName(e.Type))
                        {
                            eventBad++;
                            Problem($"{def}: event {e.Name} vs {te.Name}");
                        }
                    }
            }
        }

        Console.WriteLine($"assemblies compared: {assemblies} (no truth file for {missingAssemblies})");
        Console.WriteLine($"types: {types}  missing-in-truth: {typeMissing}  flags-bad: {flagsBad}");
        Console.WriteLine($"base types: ok {baseOk}  bad {baseBad}    interface lists: ok {ifaceOk}  bad {ifaceBad}");
        Console.WriteLine($"generic parameter lists: {generics}  bad {genericBad}");
        Console.WriteLine($"fields: {fields}  bad {fieldBad}");
        Console.WriteLine($"methods: {methods}  bad {methodBad}");
        Console.WriteLine($"properties: {props}  bad {propBad}    events: {events}  bad {eventBad}");
        foreach (string p in problems) Console.WriteLine("  ! " + p);
        return 0;
    }
}
