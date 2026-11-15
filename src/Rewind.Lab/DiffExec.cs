using System.Collections;
using System.Globalization;
using System.Reflection;
using System.Runtime.Loader;
using System.Text;

namespace Rewind.Lab;

/// <summary>
/// Behavioural check of recovered code: loads the game's original managed assembly (from a build of ours) and
/// the assembly rebuilt from the native binary side by side, calls the same static methods with the same
/// inputs, and compares what comes back - results, thrown exception types, and changes made to arguments.
/// </summary>
internal static class DiffExec
{
    /// <summary>Loads one copy of the assembly under test; everything it references comes from the original build.</summary>
    private sealed class Sandbox(string name, string testedAssembly, string dependencyDirectory) : AssemblyLoadContext(name, isCollectible: false)
    {
        private static readonly string[] Framework = ["mscorlib", "netstandard", "System", "System.Core", "System.Private.CoreLib", "System.Runtime"];

        protected override Assembly? Load(AssemblyName assemblyName)
        {
            string simple = assemblyName.Name ?? "";
            if (string.Equals(simple, Path.GetFileNameWithoutExtension(testedAssembly), StringComparison.OrdinalIgnoreCase))
                return LoadFromAssemblyPath(testedAssembly);
            // The class library is the host's own: the game's copy belongs to another runtime.
            if (Framework.Contains(simple) || simple.StartsWith("System.", StringComparison.Ordinal)) return null;
            string candidate = Path.Combine(dependencyDirectory, simple + ".dll");
            return File.Exists(candidate) ? LoadFromAssemblyPath(candidate) : null;
        }

        public Assembly Tested => LoadFromAssemblyPath(testedAssembly);
    }

    private static readonly int[] Ints = [0, 1, -1, 2, 3, 5, 7, 10, 31, 32, 33, 64, 100, -100, 255, 256, 1000, 65535, 65536, 123456789, -987654321, int.MaxValue, int.MinValue, int.MaxValue - 1];
    private static readonly long[] Longs = [0, 1, -1, 2, 10, 255, 4294967295, 4294967296, -4294967296, long.MaxValue, long.MinValue, 1234567890123];
    private static readonly double[] Doubles = [0, 1, -1, 0.5, -0.5, 2, 3.75, 1e10, -1e10, 1e-10, double.NaN, double.PositiveInfinity, double.NegativeInfinity, double.Epsilon, 123.456];
    private static readonly string?[] Strings = [null, "", "a", " ", "alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "hello world", " x", "12", "-7", "abc"];

    /// <summary>Set while sampling inputs for a method that calls itself: deep recursion would end the process.</summary>
    [ThreadStatic] private static bool _smallInputs;
    [ThreadStatic] private static bool _moderateInputs;
    private static readonly int[] ModerateInts = [0, 1, -1, 2, 3, 5, 7, 10, 31, 32, 33, 64, 100, -100, 255, 256, 1000, -1000, 65535, 65536];

    private static int IlSize(MethodInfo method)
    {
        try
        {
            return method.GetMethodBody()?.GetILAsByteArray()?.Length ?? 0;
        }
        catch (Exception)
        {
            return int.MaxValue;
        }
    }

    private static bool CallsItself(MethodInfo method)
    {
        byte[]? il;
        try
        {
            il = method.GetMethodBody()?.GetILAsByteArray();
        }
        catch (Exception)
        {
            return false; // a body that names types this runtime lacks cannot be inspected (nor run)
        }
        if (il == null) return false;
        int token = method.MetadataToken;
        for (int i = 0; i + 4 < il.Length; i++)
            if (il[i] is 0x28 or 0x6F && BitConverter.ToInt32(il, i + 1) == token)
                return true;
        return false;
    }

    private static object? Sample(Type type, Random random, int round)
    {
        T Pick<T>(T[] values) => round < values.Length ? values[round] : values[random.Next(values.Length)];
        // Anything but a small leaf method may loop or allocate in proportion to its arguments.
        if (_moderateInputs && !_smallInputs)
        {
            if (type == typeof(int)) return round < 20 ? ModerateInts[round] : random.Next(-70000, 70000);
            if (type == typeof(uint)) return (uint)(round < 20 ? Math.Abs(ModerateInts[round]) : random.Next(0, 70000));
            if (type == typeof(long)) return (long)(round < 20 ? ModerateInts[round] : random.Next(-70000, 70000));
            if (type == typeof(ulong)) return (ulong)(round < 20 ? Math.Abs(ModerateInts[round]) : random.Next(0, 70000));
        }
        if (_smallInputs && (type == typeof(int) || type == typeof(long) || type == typeof(uint) || type == typeof(ulong)))
            return Convert.ChangeType(round < 24 ? round - 3 : random.Next(0, 24), type, CultureInfo.InvariantCulture);
        if (type == typeof(int)) return round < Ints.Length || random.Next(3) == 0 ? Pick(Ints) : random.Next(-1000, 1000);
        if (type == typeof(uint)) return unchecked((uint)(int)Sample(typeof(int), random, round)!);
        if (type == typeof(long)) return round < Longs.Length || random.Next(3) == 0 ? Pick(Longs) : (long)random.Next(-100000, 100000);
        if (type == typeof(ulong)) return unchecked((ulong)(long)Sample(typeof(long), random, round)!);
        if (type == typeof(short)) return unchecked((short)(int)Sample(typeof(int), random, round)!);
        if (type == typeof(ushort)) return unchecked((ushort)(int)Sample(typeof(int), random, round)!);
        if (type == typeof(byte)) return unchecked((byte)(int)Sample(typeof(int), random, round)!);
        if (type == typeof(sbyte)) return unchecked((sbyte)(int)Sample(typeof(int), random, round)!);
        if (type == typeof(char)) return (char)(round < 6 ? "a e\tz0"[round] : random.Next(32, 127));
        if (type == typeof(bool)) return (round + random.Next(2)) % 2 == 0;
        if (type == typeof(double)) return round < Doubles.Length || random.Next(3) == 0 ? Pick(Doubles) : random.NextDouble() * 200 - 100;
        if (type == typeof(float)) return (float)(double)Sample(typeof(double), random, round)!;
        if (type == typeof(nint)) return (nint)(long)Sample(typeof(long), random, round)!;
        if (type == typeof(string)) return Pick(Strings);
        if (type == typeof(object)) return (round % 3) switch { 0 => null, 1 => (object)Sample(typeof(int), random, round)!, _ => Pick(Strings) };
        if (type.IsArray && type.GetArrayRank() == 1)
        {
            Type element = type.GetElementType()!;
            if (ReferenceEquals(Sample(element, new Random(1), 5), Unsupported)) return Unsupported;
            if (round == 0) return null;
            int length = round == 1 ? 0 : round == 2 ? 1 : random.Next(2, 9);
            Array array = Array.CreateInstance(element, length);
            for (int i = 0; i < length; i++)
            {
                object? value = Sample(element, random, random.Next(40));
                if (ReferenceEquals(value, Unsupported)) return Unsupported;
                if (value == null && element.IsValueType) return null;
                array.SetValue(value, i);
            }
            return array;
        }
        if (type.IsEnum) return Enum.ToObject(type, random.Next(0, 6));
        return Unsupported;
    }

    private static readonly object Unsupported = new();

    /// <summary>A value as text, in a form that is equal exactly when two results mean the same thing.</summary>
    private static string Canon(object? value, int depth = 0)
    {
        switch (value)
        {
            case null: return "null";
            case string s: return "\"" + s + "\"";
            case float f: return "f:" + BitConverter.SingleToInt32Bits(float.IsNaN(f) ? float.NaN : f).ToString("X8");
            case double d: return "d:" + BitConverter.DoubleToInt64Bits(double.IsNaN(d) ? double.NaN : d).ToString("X16");
            case bool or char or sbyte or byte or short or ushort or int or uint or long or ulong or nint or nuint:
                return value.GetType().Name + ":" + Convert.ToString(value, CultureInfo.InvariantCulture);
        }
        Type type = value.GetType();
        if (type.IsEnum) return "enum:" + Convert.ToInt64(value, CultureInfo.InvariantCulture);
        if (depth > 4) return "…";
        if (value is IEnumerable sequence && (type.IsArray || type.Namespace == "System.Collections.Generic"))
        {
            var sb = new StringBuilder("[");
            int n = 0;
            foreach (object? item in sequence)
            {
                if (n++ > 200) break;
                sb.Append(Canon(item, depth + 1)).Append(',');
            }
            return sb.Append(']').ToString();
        }
        if (type.Namespace == null || !type.Namespace.StartsWith("System", StringComparison.Ordinal) || type.IsValueType)
        {
            // An object of the game's own types: its fields, by name.
            var sb = new StringBuilder(type.Name).Append('{');
            for (Type? t = type; t != null && t != typeof(object) && t != typeof(ValueType); t = t.BaseType)
                foreach (FieldInfo f in t.GetFields(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly).OrderBy(f => f.Name, StringComparer.Ordinal))
                {
                    object? fieldValue;
                    try { fieldValue = f.GetValue(value); }
                    catch { fieldValue = "?"; }
                    sb.Append(f.Name).Append('=').Append(Canon(fieldValue, depth + 1)).Append(';');
                }
            return sb.Append('}').ToString();
        }
        return type.FullName ?? type.Name;
    }

    private static object? Clone(object? value)
    {
        if (value is Array array) return array.Clone();
        return value;
    }

    private const int CallTimeoutMs = 1500;
    private static int _abandoned;

    /// <summary>
    /// Runs one call with a time limit: some inputs make a method loop forever (in the original too), and a
    /// stuck call cannot be interrupted, only left behind.
    /// </summary>
    private static string Invoke(MethodInfo method, object?[] arguments)
    {
        if (_abandoned >= 24) return "timeout (not run: too many stuck calls)";
        string? outcome = null;
        var thread = new Thread(() => outcome = InvokeDirect(method, arguments), 16 << 20) { IsBackground = true, Priority = ThreadPriority.BelowNormal };
        thread.Start();
        if (thread.Join(CallTimeoutMs)) return outcome ?? "no outcome";
        Interlocked.Increment(ref _abandoned);
        return "timeout";
    }

    private static string InvokeDirect(MethodInfo method, object?[] arguments)
    {
        string outcome;
        try
        {
            object? result = method.Invoke(null, arguments);
            outcome = "ret " + Canon(result);
        }
        catch (TargetInvocationException e)
        {
            Exception inner = e.InnerException ?? e;
            outcome = "throw " + inner.GetType().FullName;
            if (inner is InvalidProgramException or MissingMethodException or MissingFieldException or TypeLoadException or BadImageFormatException or EntryPointNotFoundException)
                outcome += " <" + inner.Message.Split('\n')[0] + ">";
        }
        catch (Exception e)
        {
            outcome = "invoke-failed " + e.GetType().Name;
        }
        // Arrays and by-ref values may have been changed by the call: that is part of the behaviour.
        return outcome + " | args " + string.Join(",", arguments.Select(a => Canon(a)));
    }

    /// <summary>diff-exec &lt;recovered dir&gt; &lt;original Managed dir&gt; &lt;assembly&gt; [type filter] [samples]</summary>
    public static int Run(string recoveredDirectory, string originalDirectory, string assemblyName, string? typeFilter, int samples)
    {
        string file = assemblyName.EndsWith(".dll", StringComparison.OrdinalIgnoreCase) ? assemblyName : assemblyName + ".dll";
        string original = Path.GetFullPath(Path.Combine(originalDirectory, file)), recovered = Path.GetFullPath(Path.Combine(recoveredDirectory, file));
        string dependencies = Path.GetFullPath(originalDirectory);
        Assembly truth = new Sandbox("original", original, dependencies).Tested;
        Assembly ours = new Sandbox("recovered", recovered, dependencies).Tested;

        int methods = 0, identical = 0, different = 0, skipped = 0, notRunnable = 0;
        long calls = 0;
        var failures = new List<string>();
        var unrunnable = new Dictionary<string, int>();

        foreach (Type type in truth.GetTypes().OrderBy(t => t.FullName, StringComparer.Ordinal))
        {
            if (typeFilter != null && !(type.FullName ?? "").Contains(typeFilter, StringComparison.Ordinal)) continue;
            if (type.IsGenericTypeDefinition) continue;
            Type? mirror = ours.GetType(type.FullName!, false);
            if (mirror == null) continue;
            foreach (MethodInfo method in type.GetMethods(BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly))
            {
                if (method.IsGenericMethodDefinition || method.Name.StartsWith('<')) continue;
                ParameterInfo[] parameters = method.GetParameters();
                MethodInfo? twin = mirror.GetMethods(BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly)
                    .FirstOrDefault(m => m.Name == method.Name && m.GetParameters().Select(p => p.ParameterType.FullName).SequenceEqual(parameters.Select(p => p.ParameterType.FullName)));
                if (twin == null) continue;
                ParameterInfo[] twinParameters = twin.GetParameters();

                var random = new Random(12345);
                _smallInputs = CallsItself(method) || CallsItself(twin);
                _moderateInputs = IlSize(method) > 24;
                bool supported = true;
                int same = 0, total = 0;
                string? firstDifference = null;
                string? blocker = null;
                for (int round = 0; round < samples && supported; round++)
                {
                    var a = new object?[parameters.Length];
                    var b = new object?[parameters.Length];
                    for (int i = 0; i < parameters.Length; i++)
                    {
                        Type pt = parameters[i].ParameterType;
                        bool byRef = pt.IsByRef;
                        if (byRef) pt = pt.GetElementType()!;
                        object? value = Sample(pt, random, round);
                        if (ReferenceEquals(value, Unsupported)) { supported = false; break; }
                        a[i] = value;
                        // Enum and array arguments belong to each side's own copy of the types.
                        Type other = twinParameters[i].ParameterType.IsByRef ? twinParameters[i].ParameterType.GetElementType()! : twinParameters[i].ParameterType;
                        b[i] = value != null && other.IsEnum ? Enum.ToObject(other, Convert.ToInt64(value, CultureInfo.InvariantCulture)) : Clone(value);
                        a[i] = Clone(a[i]);
                    }
                    if (!supported) break;
                    string expected = Invoke(method, a), actual = Invoke(twin, b);
                    calls += 2;
                    // The original itself may need the engine (native calls): then there is nothing to compare.
                    if (expected.Contains("System.Security.SecurityException", StringComparison.Ordinal) || expected.Contains("MissingMethodException", StringComparison.Ordinal) ||
                        expected.Contains("TypeLoadException", StringComparison.Ordinal) || expected.Contains("EntryPointNotFoundException", StringComparison.Ordinal) ||
                        expected.Contains("TypeInitializationException", StringComparison.Ordinal))
                    {
                        blocker = expected.Split('|')[0].Trim();
                        break;
                    }
                    total++;
                    bool stuck = expected.StartsWith("timeout", StringComparison.Ordinal) || actual.StartsWith("timeout", StringComparison.Ordinal);
                    if (expected == actual) same++;
                    else firstDifference ??= $"({string.Join(", ", a.Select(x => Canon(x)))}) original: {expected.Split('|')[0].Trim()}  recovered: {actual.Split('|')[0].Trim()}";
                    if (stuck) break; // do not pile up stuck threads for one method
                }
                if (!supported) { skipped++; continue; }
                if (blocker != null && total == 0)
                {
                    notRunnable++;
                    unrunnable[blocker] = unrunnable.GetValueOrDefault(blocker) + 1;
                    continue;
                }
                methods++;
                if (same == total) identical++;
                else
                {
                    different++;
                    failures.Add($"  {type.Name}.{method.Name}: {same}/{total} inputs agree; first difference {firstDifference}");
                }
            }
        }

        Console.WriteLine($"differential execution of {assemblyName}: {methods} static methods compared on up to {samples} inputs each ({calls} calls)");
        Console.WriteLine($"  behave identically: {identical}");
        Console.WriteLine($"  differ:             {different}");
        Console.WriteLine($"  not comparable:     {skipped} (parameter types the harness cannot construct), {notRunnable} (original needs the game engine to run)");
        foreach (string f in failures.Take(60)) Console.WriteLine(f);
        if (failures.Count > 60) Console.WriteLine($"  ... {failures.Count - 60} more");
        Console.Out.Flush();
        // Stuck calls left behind would keep the process alive.
        Environment.Exit(different == 0 ? 0 : 1);
        return 0;
    }
}
