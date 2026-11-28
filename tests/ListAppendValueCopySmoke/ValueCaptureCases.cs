using System.Collections;
using System.Numerics;
using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;
using Rewind.Output;

internal static class ValueCaptureCases
{
    private sealed record Capture(Case Body, List<Instruction> Stores);
    public static void Run()
    {
        using var fixture = new Fixtures();
        int positives = 0, negatives = 0, operations = 0, exceptions = 0;
        Capture Create(string name, bool wholePayload = false)
        {
            Case body = fixture.Create(name); var il = body.Method.Body.GetILProcessor(); var stores = new List<Instruction>();
            VariableDefinition NewColor()
            {
                var local = new VariableDefinition(fixture.Color); body.Method.Body.Variables.Add(local); return local;
            }
            void After(Instruction cursor, IEnumerable<Instruction> code)
            {
                foreach (var instruction in code) { il.InsertAfter(cursor, instruction); cursor = instruction; }
            }
            if (wholePayload)
            {
                foreach (var store in body.Method.Body.Instructions.Where(i => i.OpCode.Code == Code.Stfld && i.Operand == fixture.ColorField).ToArray())
                {
                    Instruction load = store.Previous!; var captured = NewColor();
                    var capture = Instruction.Create(OpCodes.Stloc, captured); stores.Add(capture);
                    After(load, [capture, Instruction.Create(OpCodes.Ldloc, captured)]);
                }
            }
            else
            {
                // The scalar-byte writer captures a complete Color32 with its destination address pending.
                var reads = body.Method.Body.Instructions.Where(i => i.OpCode.Code == Code.Ldarg && i.Operand == body.Packed).ToArray();
                var source = NewColor(); Instruction first = body.Method.Body.Instructions[0];
                for (int channel = 0; channel < 4; channel++)
                {
                    var prefix = new List<Instruction> { Instruction.Create(OpCodes.Ldloca, source), Instruction.Create(OpCodes.Ldarg, body.Packed) };
                    if (channel != 0) { prefix.Add(Instruction.Create(OpCodes.Ldc_I4, channel * 8)); prefix.Add(Instruction.Create(OpCodes.Shr_Un)); }
                    prefix.Add(Instruction.Create(OpCodes.Conv_U1)); prefix.Add(Instruction.Create(OpCodes.Stfld, fixture.Channels[channel]));
                    foreach (var instruction in prefix) il.InsertBefore(first, instruction);
                }
                foreach (var read in reads)
                {
                    read.OpCode = OpCodes.Ldloc; read.Operand = source; var captured = NewColor();
                    var capture = Instruction.Create(OpCodes.Stloc, captured); stores.Add(capture);
                    var code = new List<Instruction> { capture };
                    for (int channel = 0; channel < 4; channel++)
                    {
                        code.Add(Instruction.Create(OpCodes.Ldloca, captured)); code.Add(Instruction.Create(OpCodes.Ldfld, fixture.Channels[channel]));
                        if (channel != 0)
                        {
                            code.Add(Instruction.Create(OpCodes.Ldc_I4, channel * 8)); code.Add(Instruction.Create(OpCodes.Shl)); code.Add(Instruction.Create(OpCodes.Or));
                        }
                    }
                    After(read, code);
                }
            }
            return new Capture(body, stores);
        }
        void Good(string name, bool whole)
        {
            var c = Create(name, whole);
            if (ListAppendIlFolding.Run(c.Body.Method.Body) != 1) throw new Exception(name + ": capture was not restored");
            if (c.Body.Method.Body.Instructions.Any(i => i.Operand is FieldReference f && f.DeclaringType.FullName.StartsWith("System.Collections.Generic.List`1", StringComparison.Ordinal)) ||
                c.Body.Method.Body.Instructions.Any(i => i.Operand is MethodReference m && m.Name == "AddWithResize"))
                throw new Exception(name + ": private append remained");
            if (ListAppendIlFolding.Run(c.Body.Method.Body) != 0) throw new Exception(name + ": not idempotent");
            positives++;
        }
        void Bad(string name, Action<Capture> change)
        {
            var c = Create(name); change(c);
            string Shape() => string.Join("\n", c.Body.Method.Body.Instructions.Select(i => i.OpCode.Code + ":" + i.Operand));
            string before = Shape(); int locals = c.Body.Method.Body.Variables.Count;
            if (ListAppendIlFolding.Run(c.Body.Method.Body) != 0 || Shape() != before || c.Body.Method.Body.Variables.Count != locals)
                throw new Exception(name + ": unsafe capture was changed");
            fixture.Host.Methods.Remove(c.Body.Method); negatives++;
        }
        Good("CapturedColorBits", false);
        Good("CapturedWholePayload", true);
        Bad("CaptureOverwritesPendingRoot", c => c.Stores[0].Operand = c.Stores[0].Previous!.Previous!.Operand);
        Bad("TwoPendingAddresses", c => c.Body.Method.Body.GetILProcessor().InsertBefore(c.Stores[0].Previous!.Previous!,
            Instruction.Create(OpCodes.Ldloca, (VariableDefinition)c.Stores[0].Operand)));
        Bad("ValueBelowPendingAddress", c => c.Body.Method.Body.GetILProcessor().InsertBefore(c.Stores[0].Previous!.Previous!, Instruction.Create(OpCodes.Ldc_I4, 4)));
        Bad("CaptureStoresAnAddress", c => c.Stores[0].Previous!.OpCode = OpCodes.Ldloca);
        Bad("CaptureLocalIsByReference", c =>
        {
            var address = new VariableDefinition(new ByReferenceType(fixture.Color)); c.Body.Method.Body.Variables.Add(address); c.Stores[0].Operand = address;
        });
        Bad("CallbackWithPendingAddress", c => c.Body.Method.Body.GetILProcessor().InsertAfter(c.Stores[0], Instruction.Create(OpCodes.Call, fixture.Observer)));
        Bad("CaptureOverwritesCount", c => c.Stores[0].Operand = c.Body.Count);
        Bad("PendingReadFromDestination", c =>
        {
            var il = c.Body.Method.Body.GetILProcessor(); Instruction read = c.Stores[0].Previous!;
            foreach (var instruction in c.Body.Root().Concat(new[] { Instruction.Create(OpCodes.Ldfld, fixture.ColorField) })) il.InsertBefore(read, instruction);
            il.Remove(read);
        });
        using var stream = new MemoryStream(); fixture.Assembly.Write(stream);
        var assembly = System.Reflection.Assembly.Load(stream.ToArray());
        Type host = assembly.GetType("Fixture.Host", true)!, vertex = assembly.GetType("Fixture.Vertex", true)!, color = assembly.GetType("Fixture.ColorBits", true)!;
        Type listType = typeof(List<>).MakeGenericType(vertex);
        var version = listType.GetField("_version", BindingFlags.Instance | BindingFlags.NonPublic)!;
        var capacity = listType.GetProperty("Capacity")!; var enumerator = listType.GetMethod("GetEnumerator", Type.EmptyTypes)!;
        object Expected(float x, float y, float z, uint bits)
        {
            object rgba = Activator.CreateInstance(color)!;
            for (int n = 0; n < 4; n++) color.GetField(new[] { "r", "g", "b", "a" }[n])!.SetValue(rgba, (byte)(bits >> (n * 8)));
            object value = Activator.CreateInstance(vertex)!;
            vertex.GetField("position")!.SetValue(value, new Vector3(x, y, z));
            vertex.GetField("uv")!.SetValue(value, new Vector4(x, y, z, -0.0f)); vertex.GetField("color")!.SetValue(value, rgba); return value;
        }
        string Bits(object value)
        {
            var p = (Vector3)vertex.GetField("position")!.GetValue(value)!;
            var uv = (Vector4)vertex.GetField("uv")!.GetValue(value)!; object rgba = vertex.GetField("color")!.GetValue(value)!;
            return string.Join(",", new[] { p.X, p.Y, p.Z, uv.X, uv.Y, uv.Z, uv.W }.Select(BitConverter.SingleToInt32Bits)) + ":" +
                string.Join(",", new[] { "r", "g", "b", "a" }.Select(n => color.GetField(n)!.GetValue(rgba))) + ":" +
                color.GetField("packed", BindingFlags.Instance | BindingFlags.NonPublic)!.GetValue(rgba);
        }
        uint[] colors = [0, 1, 0xFF, 0x100, 0x10000, 0x1000000, 0x80000000, 0xFF000000, 0xFFFFFFFF,
            0x00112233, 0xF0804001, 0x80FF7F01, 0xDEADBEEF, 0x55555555, 0xAAAAAAAA, 0x12345678];
        foreach (string name in new[] { "CapturedColorBits", "CapturedWholePayload" })
        {
            MethodInfo method = host.GetMethod(name)!;
            foreach (int startCapacity in new[] { 0, 1, 8, 64 })
            {
                var actual = (IList)Activator.CreateInstance(listType, new object[] { startCapacity })!;
                var expected = (IList)Activator.CreateInstance(listType, new object[] { startCapacity })!;
                for (int n = 0; n < colors.Length; n++)
                {
                    float x = n % 3 == 0 ? -0.0f : n % 3 == 1 ? BitConverter.Int32BitsToSingle(unchecked((int)0x7FC13579)) : n + 0.25f;
                    float y = -n - 0.5f, z = n * 0.5f; int previous = (int)version.GetValue(actual)!;
                    IEnumerator old = (IEnumerator)enumerator.Invoke(actual, null)!; old.MoveNext();
                    method.Invoke(null, new object?[] { actual, Array.Empty<Vector3>(), 0, x, y, z, colors[n] }); expected.Add(Expected(x, y, z, colors[n]));
                    if (actual.Count != expected.Count || (int)capacity.GetValue(actual)! != (int)capacity.GetValue(expected)! ||
                        (int)version.GetValue(actual)! != unchecked(previous + 1)) throw new Exception(name + ": wrong count/capacity/version");
                    for (int i = 0; i < actual.Count; i++) if (Bits(actual[i]!) != Bits(expected[i]!)) throw new Exception(name + ": changed payload bits");
                    bool invalidated = false; try { old.MoveNext(); } catch (InvalidOperationException) { invalidated = true; }
                    if (!invalidated) throw new Exception(name + ": old enumerator remained valid");
                    operations++;
                }
            }
            try { method.Invoke(null, new object?[] { null, Array.Empty<Vector3>(), 0, 1f, 2f, 3f, uint.MaxValue }); throw new Exception("Expected null receiver"); }
            catch (TargetInvocationException e) when (e.InnerException is NullReferenceException) { exceptions++; }
        }
        Console.WriteLine($"LIST_VALUE_CAPTURE_SMOKE_PASS positive={positives} negative={negatives} runtime_operations={operations} exception_cases={exceptions} local_and_element_pending_address=true all_color_and_float_bits=true capacity=true version_once=true enum_invalidated=true");
    }
}
