using Mono.Cecil;

namespace Rewind.Lab;

/// <summary>
/// Compares assemblies we emitted with the original assemblies, both read back through Mono.Cecil: metadata
/// tokens, signatures, constants, layout, explicit overrides and custom attributes (including arguments).
/// </summary>
internal static class TruthDll
{
    private sealed class Counter(string name)
    {
        public readonly string Name = name;
        public int Total, Bad;
        public readonly List<string> Samples = [];

        public void Check(bool ok, Func<string> describe)
        {
            Total++;
            if (ok) return;
            Bad++;
            if (Samples.Count < 6) Samples.Add(describe());
        }
    }

    private static string Arg(CustomAttributeArgument a)
    {
        object? v = a.Value;
        switch (v)
        {
            case null: return a.Type.FullName + ":null";
            case CustomAttributeArgument inner: return "box(" + Arg(inner) + ")";
            case CustomAttributeArgument[] items: return a.Type.FullName + ":[" + string.Join(",", items.Select(Arg)) + "]";
            case TypeReference t: return "typeof(" + t.FullName + ")";
            default: return a.Type.FullName + ":" + Convert.ToString(v, System.Globalization.CultureInfo.InvariantCulture);
        }
    }

    private static string Attr(CustomAttribute a)
    {
        try
        {
            var parts = new List<string>();
            parts.AddRange(a.ConstructorArguments.Select(Arg));
            parts.AddRange(a.Fields.OrderBy(f => f.Name, StringComparer.Ordinal).Select(f => "F:" + f.Name + "=" + Arg(f.Argument)));
            parts.AddRange(a.Properties.OrderBy(p => p.Name, StringComparer.Ordinal).Select(p => "P:" + p.Name + "=" + Arg(p.Argument)));
            return a.Constructor.FullName + "(" + string.Join("; ", parts) + ")";
        }
        catch (Exception e)
        {
            return a.Constructor.FullName + "(<unreadable: " + e.GetType().Name + ">)";
        }
    }

    private static List<string> Attrs(ICustomAttributeProvider p) =>
        p.HasCustomAttributes ? p.CustomAttributes.Select(Attr).OrderBy(s => s, StringComparer.Ordinal).ToList() : [];

    public static int Run(string emittedDir, string truthDir)
    {
        var emittedResolver = new DefaultAssemblyResolver();
        emittedResolver.AddSearchDirectory(emittedDir);
        var truthResolver = new DefaultAssemblyResolver();
        truthResolver.AddSearchDirectory(truthDir);

        var typeTokens = new Counter("type tokens");
        var typeShape = new Counter("type attributes/base/interfaces/layout");
        var fieldTokens = new Counter("field tokens");
        var fieldShape = new Counter("field type/attributes/constant/offset/data");
        var methodTokens = new Counter("method tokens");
        var methodShape = new Counter("method signature/attributes");
        var overrides = new Counter("explicit overrides");
        var paramShape = new Counter("parameter name/type/attributes/default");
        var props = new Counter("properties");
        var events = new Counter("events");
        var attrs = new Counter("custom attributes (with arguments)");
        var generics = new Counter("generic parameters (flags/constraints)");
        int compared = 0, missing = 0;

        foreach (string truthPath in Directory.GetFiles(truthDir, "*.dll").OrderBy(p => p, StringComparer.OrdinalIgnoreCase))
        {
            string emittedPath = Path.Combine(emittedDir, Path.GetFileName(truthPath));
            if (!File.Exists(emittedPath))
            {
                missing++;
                Console.WriteLine($"not emitted: {Path.GetFileName(truthPath)}");
                continue;
            }
            compared++;
            using AssemblyDefinition truth = AssemblyDefinition.ReadAssembly(truthPath, new ReaderParameters { AssemblyResolver = truthResolver });
            using AssemblyDefinition ours = AssemblyDefinition.ReadAssembly(emittedPath, new ReaderParameters { AssemblyResolver = emittedResolver });
            string asm = Path.GetFileNameWithoutExtension(truthPath);

            attrs.Check(Attrs(truth).SequenceEqual(Attrs(ours)), () => $"{asm} [assembly]: ours {string.Join(" | ", Attrs(ours).Take(3))} / truth {string.Join(" | ", Attrs(truth).Take(3))}");

            var ourTypes = new Dictionary<string, TypeDefinition>(StringComparer.Ordinal);
            foreach (TypeDefinition t in ours.MainModule.GetTypes()) ourTypes.TryAdd(t.FullName, t);

            foreach (TypeDefinition t in truth.MainModule.GetTypes())
            {
                if (!ourTypes.TryGetValue(t.FullName, out TypeDefinition? o))
                {
                    typeShape.Check(false, () => $"{asm}: {t.FullName} missing");
                    continue;
                }
                typeTokens.Check(t.MetadataToken == o.MetadataToken, () => $"{t.FullName}: {o.MetadataToken} vs {t.MetadataToken}");
                bool layoutOk = t.PackingSize == o.PackingSize && t.ClassSize == o.ClassSize;
                typeShape.Check(
                    t.Attributes == o.Attributes && t.BaseType?.FullName == o.BaseType?.FullName && layoutOk &&
                    t.Interfaces.Select(i => i.InterfaceType.FullName).OrderBy(s => s, StringComparer.Ordinal)
                        .SequenceEqual(o.Interfaces.Select(i => i.InterfaceType.FullName).OrderBy(s => s, StringComparer.Ordinal)),
                    () => $"{t.FullName}: attrs {o.Attributes}/{t.Attributes} base {o.BaseType?.FullName}/{t.BaseType?.FullName} " +
                          $"pack {o.PackingSize}/{t.PackingSize} size {o.ClassSize}/{t.ClassSize}");
                attrs.Check(Attrs(t).SequenceEqual(Attrs(o)), () => $"{t.FullName}: ours [{string.Join(" | ", Attrs(o))}] truth [{string.Join(" | ", Attrs(t))}]");
                CheckGenerics(generics, t.FullName, t, o);

                if (t.Fields.Count != o.Fields.Count) fieldShape.Check(false, () => $"{t.FullName}: field count");
                else
                    for (int i = 0; i < t.Fields.Count; i++)
                    {
                        FieldDefinition tf = t.Fields[i], of = o.Fields[i];
                        fieldTokens.Check(tf.MetadataToken == of.MetadataToken, () => $"{tf.FullName}: {of.MetadataToken} vs {tf.MetadataToken}");
                        bool constantOk = tf.HasConstant == of.HasConstant && (!tf.HasConstant || Equals(tf.Constant, of.Constant));
                        bool dataOk = tf.InitialValue.AsSpan().SequenceEqual(of.InitialValue);
                        bool offsetOk = tf.Offset == of.Offset;
                        // IL2CPP records function pointer types as native int.
                        bool typeOk = tf.FieldType.FullName == of.FieldType.FullName || tf.FieldType.IsFunctionPointer;
                        fieldShape.Check(tf.Name == of.Name && typeOk && tf.Attributes == of.Attributes && constantOk && dataOk && offsetOk,
                            () => $"{tf.FullName}: type {of.FieldType.FullName} attrs {of.Attributes}/{tf.Attributes} const {of.Constant ?? "null"}/{tf.Constant ?? "null"} " +
                                  $"offset {of.Offset}/{tf.Offset} data {of.InitialValue.Length}/{tf.InitialValue.Length}");
                        attrs.Check(Attrs(tf).SequenceEqual(Attrs(of)), () => $"{tf.FullName}: ours [{string.Join(" | ", Attrs(of))}] truth [{string.Join(" | ", Attrs(tf))}]");
                    }

                if (t.Methods.Count != o.Methods.Count) methodShape.Check(false, () => $"{t.FullName}: method count");
                else
                    for (int i = 0; i < t.Methods.Count; i++)
                    {
                        MethodDefinition tm = t.Methods[i], om = o.Methods[i];
                        methodTokens.Check(tm.MetadataToken == om.MetadataToken, () => $"{tm.FullName}: {om.MetadataToken} vs {tm.MetadataToken}");
                        methodShape.Check(tm.FullName == om.FullName && tm.Attributes == om.Attributes && tm.ImplAttributes == om.ImplAttributes &&
                                          tm.HasBody == om.HasBody,
                            () => $"{tm.FullName}: ours {om.FullName} attrs {om.Attributes}/{tm.Attributes} impl {om.ImplAttributes}/{tm.ImplAttributes} body {om.HasBody}/{tm.HasBody}");
                        overrides.Check(
                            tm.Overrides.Select(x => x.FullName).OrderBy(s => s, StringComparer.Ordinal)
                                .SequenceEqual(om.Overrides.Select(x => x.FullName).OrderBy(s => s, StringComparer.Ordinal)),
                            () => $"{tm.FullName}: ours [{string.Join(" | ", om.Overrides.Select(x => x.FullName))}] truth [{string.Join(" | ", tm.Overrides.Select(x => x.FullName))}]");
                        attrs.Check(Attrs(tm).SequenceEqual(Attrs(om)), () => $"{tm.FullName}: ours [{string.Join(" | ", Attrs(om))}] truth [{string.Join(" | ", Attrs(tm))}]");
                        CheckGenerics(generics, tm.FullName, tm, om);
                        for (int p = 0; p < tm.Parameters.Count && p < om.Parameters.Count; p++)
                        {
                            ParameterDefinition tp = tm.Parameters[p], op = om.Parameters[p];
                            bool constantOk = tp.HasConstant == op.HasConstant && (!tp.HasConstant || Equals(tp.Constant, op.Constant));
                            paramShape.Check(tp.Name == op.Name && tp.Attributes == op.Attributes && constantOk,
                                () => $"{tm.FullName} #{p}: {op.Name}/{tp.Name} attrs {op.Attributes}/{tp.Attributes} const {op.Constant ?? "null"}/{tp.Constant ?? "null"}");
                            attrs.Check(Attrs(tp).SequenceEqual(Attrs(op)), () => $"{tm.FullName} #{p}: ours [{string.Join(" | ", Attrs(op))}] truth [{string.Join(" | ", Attrs(tp))}]");
                        }
                    }

                if (t.Properties.Count != o.Properties.Count) props.Check(false, () => $"{t.FullName}: property count");
                else
                    for (int i = 0; i < t.Properties.Count; i++)
                    {
                        PropertyDefinition tp = t.Properties[i], op = o.Properties[i];
                        props.Check(tp.FullName == op.FullName && tp.Attributes == op.Attributes && tp.MetadataToken == op.MetadataToken &&
                                    tp.GetMethod?.Name == op.GetMethod?.Name && tp.SetMethod?.Name == op.SetMethod?.Name,
                            () => $"{tp.FullName}: ours {op.FullName} attrs {op.Attributes}/{tp.Attributes} token {op.MetadataToken}/{tp.MetadataToken}");
                        attrs.Check(Attrs(tp).SequenceEqual(Attrs(op)), () => $"{tp.FullName}: attributes");
                    }

                if (t.Events.Count != o.Events.Count) events.Check(false, () => $"{t.FullName}: event count");
                else
                    for (int i = 0; i < t.Events.Count; i++)
                    {
                        EventDefinition te = t.Events[i], oe = o.Events[i];
                        events.Check(te.FullName == oe.FullName && te.Attributes == oe.Attributes && te.MetadataToken == oe.MetadataToken,
                            () => $"{te.FullName}: ours {oe.FullName} attrs {oe.Attributes}/{te.Attributes}");
                        attrs.Check(Attrs(te).SequenceEqual(Attrs(oe)), () => $"{te.FullName}: attributes");
                    }
            }
        }

        Console.WriteLine($"assemblies compared: {compared}, not emitted: {missing}");
        foreach (Counter c in new[] { typeTokens, typeShape, generics, fieldTokens, fieldShape, methodTokens, methodShape, overrides, paramShape, props, events, attrs })
        {
            Console.WriteLine($"{c.Name,-44} {c.Total - c.Bad,7} / {c.Total,-7} ok" + (c.Bad == 0 ? "" : $"   ({c.Bad} differ)"));
            foreach (string s in c.Samples) Console.WriteLine("      " + s);
        }
        return 0;
    }

    private static void CheckGenerics(Counter counter, string owner, IGenericParameterProvider truth, IGenericParameterProvider ours)
    {
        if (!truth.HasGenericParameters && !ours.HasGenericParameters) return;
        if (truth.GenericParameters.Count != ours.GenericParameters.Count)
        {
            counter.Check(false, () => $"{owner}: generic parameter count");
            return;
        }
        for (int i = 0; i < truth.GenericParameters.Count; i++)
        {
            GenericParameter t = truth.GenericParameters[i], o = ours.GenericParameters[i];
            counter.Check(t.Name == o.Name && t.Attributes == o.Attributes &&
                          t.Constraints.Select(c => c.ConstraintType.FullName).OrderBy(s => s, StringComparer.Ordinal)
                              .SequenceEqual(o.Constraints.Select(c => c.ConstraintType.FullName).OrderBy(s => s, StringComparer.Ordinal)),
                () => $"{owner}<{t.Name}>: attrs {o.Attributes}/{t.Attributes} constraints [{string.Join(",", o.Constraints.Select(c => c.ConstraintType.FullName))}]/[{string.Join(",", t.Constraints.Select(c => c.ConstraintType.FullName))}]");
        }
    }
}
