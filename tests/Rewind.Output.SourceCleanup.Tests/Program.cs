using System.Reflection;
using System.Text.Json;
using System.Text.RegularExpressions;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Rewind.Output;

internal static class Program
{
    private static int assertions;
    private static int compilations;
    private static readonly List<object> Cases = [];

    private static void Check(bool condition, string name)
    {
        assertions++;
        if (!condition) throw new InvalidOperationException(name);
    }

    private static (Assembly Assembly, Diagnostic[] Diagnostics) Compile(string source, params string[] symbols)
    {
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!)
            .Split(Path.PathSeparator).Select(path => MetadataReference.CreateFromFile(path));
        var tree = CSharpSyntaxTree.ParseText(source, new CSharpParseOptions(LanguageVersion.CSharp9,
            preprocessorSymbols: symbols));
        var compilation = CSharpCompilation.Create("EmitterRegression_" + Guid.NewGuid().ToString("N"),
            [tree], references, new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
        using var output = new MemoryStream();
        var result = compilation.Emit(output);
        compilations++;
        Check(result.Success, "generated source compiles: " + string.Join(" | ",
            result.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error)));
        return (Assembly.Load(output.ToArray()), result.Diagnostics.ToArray());
    }

    private static void EqualityCases()
    {
        string original = File.ReadAllText(Path.Combine(AppContext.BaseDirectory,
            "fixtures", "SerializableSystemType.recovered.cs.txt"));
        string emitted = Decompiler.CleanupForRegression(original);
        Check(emitted.Contains("object.ReferenceEquals(a, b)"), "native reference check is explicit");
        Check(emitted.Contains("return !(a == b);"), "paired inequality complements equality");
        Check(emitted == Decompiler.CleanupForRegression(emitted), "equality cleanup is stable on a second pass");
        var (assembly, _) = Compile(emitted);
        Type wrapper = assembly.GetType("SerializableSystemType")!;
        object?[] values = [null,
            Activator.CreateInstance(wrapper, typeof(int)),
            Activator.CreateInstance(wrapper, typeof(int)),
            Activator.CreateInstance(wrapper, typeof(string))];
        Type?[] payloads = [null, typeof(int), typeof(int), typeof(string)];
        MethodInfo eq = wrapper.GetMethod("op_Equality")!;
        MethodInfo ne = wrapper.GetMethod("op_Inequality")!;
        for (int i = 0; i < values.Length; i++)
        for (int j = 0; j < values.Length; j++)
        {
            // Independent expectation: native pointer-equal / null / tail-call Type.Equals branches.
            bool expected = ReferenceEquals(values[i], values[j]) ||
                (values[i] is not null && values[j] is not null && payloads[i] == payloads[j]);
            bool equal = (bool)eq.Invoke(null, [values[i], values[j]])!;
            bool unequal = (bool)ne.Invoke(null, [values[i], values[j]])!;
            Check(equal == expected, $"native equality case {i},{j}");
            Check(unequal == !expected, $"inequality complement case {i},{j}");
        }
        Check(values[1]!.GetHashCode() == values[2]!.GetHashCode(), "equal Type wrappers have equal hashes");

        // Repair the exact incorrect helper already emitted by R4, without rewriting unknown bodies.
        string r4 = original.Insert(original.LastIndexOf('}'), "\npublic static bool operator !=(SerializableSystemType a, SerializableSystemType b)\n{\nreturn !object.ReferenceEquals(a, b);\n}\n");
        Check(Decompiler.CleanupForRegression(r4).Contains("return !(a == b);"), "R4 incorrect helper is repaired");
        string unknown = original.Replace("return a.Equals(b);", "return false;");
        Check(!Decompiler.CleanupForRegression(unknown).Contains("operator !="), "unknown equality shape is not guessed");
        Cases.Add(new { name = "SerializableSystemType", pairs = 16,
            evidence = "PAP 0x06000987 / ARM64 0x3E3EEC8; paired != is source compatibility" });
    }

    private static void ModifierCases()
    {
        const string source = """
            public class UIController
            {
                public UIController() { }
                public UIController(int value) { }
            }
            public class CountryShapesController
            {
                public CountryShapesController() { }
            }
            public class Holder
            {
                public UIController UIController;
                public CountryShapesController CountryShapesController;
                public int _data;
            }
            public class Parent { public int _owner; }
            public class Child : Parent { public new int _owner; }
            """;
        string emitted = Decompiler.CleanupForRegression(source);
        Check(!emitted.Contains("new UIController()") && !emitted.Contains("new UIController(int"),
            "constructors are never given a new modifier");
        Check(!emitted.Contains("new CountryShapesController()"), "country constructor is unchanged");
        Check(!emitted.Contains("new UIController UIController;"), "member type names do not imply hiding");
        Check(emitted.Contains("public new int _owner;"), "explicit original hiding modifier is preserved");
        var (_, diagnostics) = Compile(emitted);
        Check(!diagnostics.Any(d => d.Id is "CS0106" or "CS0109"), "no injected invalid or unnecessary new");

        const string fields = """
            using System;
            public class Camera { }
            public class Component { public object camera; }
            public class WorldCameraController : Component
            {
                private Camera camera;
                private new Action m_EnteredZone;
            }
            """;
        string fieldOutput = Decompiler.CleanupForRegression(fields);
        Check(fieldOutput.Contains("internal new Camera camera;"), "camera rule sees widened accessibility");
        Check(fieldOutput.Contains("internal Action m_EnteredZone;"), "event field rule sees widened accessibility");
        var (_, fieldDiagnostics) = Compile(fieldOutput);
        Check(!fieldDiagnostics.Any(d => d.Id is "CS0108" or "CS0109"), "specific field hiding diagnostics fixed");
        Cases.Add(new { name = "member_modifiers", preserves_original_new = true });
    }

    private static void OptionalAdCases()
    {
        // Isolated generator fixture, not a replacement gameplay service.
        const string source = """
            using System;
            public class GameAbandonmentController
            {
                public bool BannerShown;
                public int CallbackCount;
                public int PauseCount;
                public void Awake()
                {
                    Action<IronSourceAdInfo> value3 = OnAdLeftApplicationEvent;
                    IronSourceBannerEvents.onAdLeftApplicationEvent += value3;
                }
                public void OnDestroy()
                {
                    Action<IronSourceAdInfo> value3 = OnAdLeftApplicationEvent;
                    IronSourceBannerEvents.onAdLeftApplicationEvent -= value3;
                }
                private void OnAdLeftApplicationEvent(IronSourceAdInfo _)
                {
                    BannerShown = true;
                    CallbackCount++;
                }
                public void OnApplicationPause(bool paused)
                {
                    if (paused) PauseCount++;
                }
            }
            """;
        string emitted = Decompiler.CleanupForRegression(source);
        Check(Regex.Matches(emitted, "#if PAP_ENABLE_AD_SDK").Count == 3, "both event directions and callback are guarded");
        Check(emitted.Contains("BannerShown = true;\n") && emitted.Contains("CallbackCount++;"),
            "callback body is preserved rather than removed");
        Check(emitted.Contains("Optional ad SDK hook:"), "optional hook intent remains visible");
        Check(emitted == Decompiler.CleanupForRegression(emitted), "ad guards are not duplicated on a second pass");

        var (withoutSdk, _) = Compile(emitted);
        Type defaultType = withoutSdk.GetType("GameAbandonmentController")!;
        object defaultController = Activator.CreateInstance(defaultType)!;
        defaultType.GetMethod("Awake")!.Invoke(defaultController, null);
        defaultType.GetMethod("OnApplicationPause")!.Invoke(defaultController, [true]);
        Check((int)defaultType.GetField("PauseCount")!.GetValue(defaultController)! == 1,
            "game pause logic remains in the default build");
        Check(defaultType.GetMethod("OnAdLeftApplicationEvent", BindingFlags.Instance | BindingFlags.NonPublic) is null,
            "default build needs no SDK-only parameter type");

        const string sdkFixture = """
            public class IronSourceAdInfo { }
            public static class IronSourceBannerEvents
            {
                public static System.Action<IronSourceAdInfo> onAdLeftApplicationEvent;
                public static void Raise() { onAdLeftApplicationEvent?.Invoke(new IronSourceAdInfo()); }
            }
            """;
        var (withSdk, _) = Compile(emitted + "\n" + sdkFixture, "PAP_ENABLE_AD_SDK");
        Type enabledType = withSdk.GetType("GameAbandonmentController")!;
        object controller = Activator.CreateInstance(enabledType)!;
        MethodInfo raise = withSdk.GetType("IronSourceBannerEvents")!.GetMethod("Raise")!;
        enabledType.GetMethod("Awake")!.Invoke(controller, null);
        raise.Invoke(null, null);
        Check((bool)enabledType.GetField("BannerShown")!.GetValue(controller)!, "enabled callback preserves state mutation");
        Check((int)enabledType.GetField("CallbackCount")!.GetValue(controller)! == 1, "subscription fires exactly once");
        enabledType.GetMethod("OnDestroy")!.Invoke(controller, null);
        raise.Invoke(null, null);
        Check((int)enabledType.GetField("CallbackCount")!.GetValue(controller)! == 1, "unsubscription retains its direction");
        Cases.Add(new { name = "optional_ad_hooks", configurations = 2, callback_body_preserved = true });
    }

    private static void EmbeddedAssignmentCases()
    {
        const string source = """
            using System;
            public class Holder { public object _list; }
            public static class AssignmentCase
            {
                public static int Calls;
                public static Holder Holder = new Holder();
                public static object Echo(object value, string punctuation)
                {
                    Calls++;
                    return value;
                }
                public static Exception Preserve(Exception incoming)
                {
                    Holder holder = Holder;
                    return (Exception)(object)(holder._list = ((object)Echo(incoming, "a)b")));
                }
            }
            """;
        string emitted = Decompiler.CleanupForRegression(source);
        Check(emitted.Contains("(holder._list = ((object)Echo(incoming, \"a)b\")))"),
            "balanced embedded store and nested cast/call are preserved");
        Check(!emitted.Contains("__RewindPreservedListAssignment"), "no protection marker leaks to output");
        Check(!emitted.Contains("(null)(object)"), "embedded store does not become a malformed null fragment");
        var (assembly, _) = Compile(emitted);
        Type test = assembly.GetType("AssignmentCase")!;
        var exception = new InvalidOperationException("fixture");
        object? returned = test.GetMethod("Preserve")!.Invoke(null, [exception]);
        object holder = test.GetField("Holder")!.GetValue(null)!;
        Check(ReferenceEquals(exception, returned), "original expression result is preserved");
        Check(ReferenceEquals(exception, holder.GetType().GetField("_list")!.GetValue(holder)),
            "original assignment side effect is preserved");
        Check((int)test.GetField("Calls")!.GetValue(null)! == 1, "nested call is evaluated exactly once");
        string bulk = "public class BulkHolder { public object _list; }\npublic static class Bulk {\n"
            + "public static void Assign(BulkHolder holder, object value) {\n"
            + string.Join("\n", Enumerable.Range(0, 12).Select(i => $"object result{i} = (holder._list = value);"))
            + "\n}\n}\n";
        string bulkOutput = Decompiler.CleanupForRegression(bulk);
        Check(Regex.Matches(bulkOutput, @"\(holder\._list = value\)").Count == 12,
            "batch markers 1 and 10 do not overlap");
        Check(!bulkOutput.Contains("__RewindPreservedListAssignment"), "all batch markers are restored");
        Compile(bulkOutput);
        Cases.Add(new { name = "embedded_list_assignment", preserves_store = true, preserves_value = true });
    }

    private static void CapturedCatchCases(string directory)
    {
        int count = 0;
        foreach (string name in new[] { "EconomyController", "LevelEndScreenView", "AbstractChildServiceController" })
        {
            string input = Path.Combine(directory, name + ".sanitized.cs.txt");
            string original = File.ReadAllText(input);
            string emitted = Decompiler.CleanupForRegression(original);
            foreach (string line in original.Split('\n').Where(line =>
                line.Contains("(Exception)(object)(") && line.Contains("._list =")))
            {
                Check(emitted.Contains(line.Trim()), name + " retains complete recovered catch store");
                count++;
            }
            Check(!emitted.Contains("(null)(object)list"), name + " has no truncated catch cast");
            File.WriteAllText(Path.Combine(directory, name + ".r5-cleaned.cs.txt"), emitted);
        }
        Check(count == 6, "all six evidenced catch expressions (including two formerly hidden list2 cases) preserved");
        Cases.Add(new { name = "captured_catch_expressions", count, scope = "syntax and side-effect preservation, not native catch equivalence" });
    }

    public static int Main(string[] args)
    {
        try
        {
            EqualityCases();
            ModifierCases();
            OptionalAdCases();
            EmbeddedAssignmentCases();
            if (args.Length == 2 && args[0] == "--captures") CapturedCatchCases(args[1]);
            Console.WriteLine(JsonSerializer.Serialize(new { passed = true, assertions, compilations, cases = Cases }));
            return 0;
        }
        catch (Exception error)
        {
            Console.Error.WriteLine(error);
            Console.WriteLine(JsonSerializer.Serialize(new { passed = false, assertions, compilations, error = error.Message }));
            return 1;
        }
    }
}

namespace Rewind.Output
{
    public static partial class Decompiler
    {
        internal static string CleanupForRegression(string source)
        {
            SourceCleanup(ref source);
            return source;
        }
    }
}
