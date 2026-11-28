using Rewind.Output;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using System.Reflection;

int cases = 0;
void Check(string input, string expected)
{
    string actual = Decompiler.SanitizeForTest(input);
    if (actual != expected) throw new Exception($"Expected:\n{expected}\nActual:\n{actual}");
    if (Decompiler.SanitizeForTest(actual) != actual) throw new Exception("Not idempotent: " + actual);
    cases++;
}
Check("int <Value>k__BackingField; <Value>k__BackingField = 7;",
      "int _rewind_cg_Value_k__BackingField; _rewind_cg_Value_k__BackingField = 7;");
Check("source.<predicate>P = predicate; source.<value>d = value;",
      "source._rewind_cg_predicate_P = predicate; source._rewind_cg_value_d = value;");
string hex = new('A', 64);
Check("_PrivateImplementationDetails_." + hex, "_PrivateImplementationDetails_._" + hex);
Check("<Work>d__3 state; <>c__DisplayClass0 cache;", "Work_d__3 state; _c__DisplayClass0 cache;");
Check("string s = \"<br>Please <Work>d__3 <Value>k__BackingField\"; // <Work>d__3\nint <X>k__BackingField;",
      "string s = \"<br>Please <Work>d__3 <Value>k__BackingField\"; // <Work>d__3\nint _rewind_cg_X_k__BackingField;");
Check("/* <Work>d__3\n<>c__DisplayClass0 */ char c = '<'; int <X>k__BackingField;",
      "/* <Work>d__3\n<>c__DisplayClass0 */ char c = '<'; int _rewind_cg_X_k__BackingField;");
Check("string s = @\"one \"\"<Work>d__3\"\"\ntwo\"; int <X>k__BackingField;",
      "string s = @\"one \"\"<Work>d__3\"\"\ntwo\"; int _rewind_cg_X_k__BackingField;");
Check("string s = $\"{F(\"<Work>d__3 }\")} <Value>k__BackingField\"; int <X>k__BackingField;",
      "string s = $\"{F(\"<Work>d__3 }\")} <Value>k__BackingField\"; int _rewind_cg_X_k__BackingField;");
Check("string s = $@\"{F(@\"<Work>d__3 }\")} <Value>k__BackingField\"; int <X>k__BackingField;",
      "string s = $@\"{F(@\"<Work>d__3 }\")} <Value>k__BackingField\"; int _rewind_cg_X_k__BackingField;");
Check("string s = \"\"\"<Work>d__3 { \"quote\" }\"\"\"; int <X>k__BackingField;",
      "string s = \"\"\"<Work>d__3 { \"quote\" }\"\"\"; int _rewind_cg_X_k__BackingField;");
Check("string s = $$\"\"\"<Work>d__3 {{F(\"x}\")}}\"\"\"; int <X>k__BackingField;",
      "string s = $$\"\"\"<Work>d__3 {{F(\"x}\")}}\"\"\"; int _rewind_cg_X_k__BackingField;");
Check("string s = $\"{1:0//0}\"; int <X>k__BackingField;",
      "string s = $\"{1:0//0}\"; int _rewind_cg_X_k__BackingField;");
Check("string s = $\"{(flag ? 1 : 2):0/*0}\"; int <X>k__BackingField;",
      "string s = $\"{(flag ? 1 : 2):0/*0}\"; int _rewind_cg_X_k__BackingField;");
Check("string s = $\"{global::X.F(\"}\"):0//0}\"; int <X>k__BackingField;",
      "string s = $\"{global::X.F(\"}\"):0//0}\"; int _rewind_cg_X_k__BackingField;");
Check("string s = $$\"\"\"{{1:0//0}}\"\"\"; int <X>k__BackingField;",
      "string s = $$\"\"\"{{1:0//0}}\"\"\"; int _rewind_cg_X_k__BackingField;");
// Actual C#9 export failures: only the expression identifier changes. The
// diagnostic prose, format string, and any literal compiler-shaped names stay exact.
Check("PaperLogger.LogError($\"[AutoRun] Perf report finalization failed: {<e>5__5}\", LogCategory.AutoRun);",
      "PaperLogger.LogError($\"[AutoRun] Perf report finalization failed: {e_5__5}\", LogCategory.AutoRun);");
Check("Debug.LogError($\"Error reconnecting: {<>7__wrap2}\");",
      "Debug.LogError($\"Error reconnecting: {_7__wrap2}\");");
Check("var s = $\"[Vfx] Starting test for: {<instance>5__4}\";",
      "var s = $\"[Vfx] Starting test for: {instance_5__4}\";");
Check("var s = $\"Spawn bot: area={num41:F6}, id={<skinModel>5__3.Id}\";",
      "var s = $\"Spawn bot: area={num41:F6}, id={skinModel_5__3.Id}\";");
Check("var s = $\"{{<literal>d__3}} {<value>5__2,10:F2}\";",
      "var s = $\"{{<literal>d__3}} {value_5__2,10:F2}\";");
Check("var s = $@\"\"\"<literal>d__3\"\" {<value>5__2}\";",
      "var s = $@\"\"\"<literal>d__3\"\" {value_5__2}\";");
Check("var s = @$\"{<value>5__2} <literal>d__3\";",
      "var s = @$\"{value_5__2} <literal>d__3\";");
Check("var s = $\"{F($\"{<e>5__5} <literal>d__3\")}\";",
      "var s = $\"{F($\"{e_5__5} <literal>d__3\")}\";");
Check("var s = $\"{<value>5__2 /* <literal>d__3 } */ :0//<format>d__3}\";",
      "var s = $\"{value_5__2 /* <literal>d__3 } */ :0//<format>d__3}\";");
Check("var s = $\"{(flag ? <left>5__1 : <right>5__2):0/*<format>d__3}\";",
      "var s = $\"{(flag ? left_5__1 : right_5__2):0/*<format>d__3}\";");
Check("var s = $\"{global::F(<value>5__2, \"<literal>d__3 }\")}:<format>d__3\";",
      "var s = $\"{global::F(value_5__2, \"<literal>d__3 }\")}:<format>d__3\";");
Check("var s = $$\"\"\"{<literal>d__3} {{<value>5__2}}\"\"\";",
      "var s = $$\"\"\"{<literal>d__3} {{value_5__2}}\"\"\";");
Check("var s = $$\"\"\"{{{<value>5__2}}} <literal>d__3\"\"\";",
      "var s = $$\"\"\"{{{value_5__2}}} <literal>d__3\"\"\";");
Check("var s = $\"{F(new[] { <left>5__1, <right>5__2 })}\";",
      "var s = $\"{F(new[] { left_5__1, right_5__2 })}\";");
Check("var s = $\"{<unclosed>5__1", "var s = $\"{<unclosed>5__1");
Check("var __RewindProtected0__ = \"<Work>d__3\"; int <X>k__BackingField;",
      "var __RewindProtected0__ = \"<Work>d__3\"; int _rewind_cg_X_k__BackingField;");
Check("List<T>P; List<T>d;", "List<T>P; List<T>d;");
Check("List</* note */int>d__3 = new();", "List</* note */int>d__3 = new();");
Check("List<int>d__3 = new();", "List<int>d__3 = new();");
Check("item.<Value>k__BackingField.Text = F(\"; <Work>d__3\");",
      "{ var __b = item.Value; __b.Text = F(\"; <Work>d__3\"); item.Value = __b; }");
string accessor = "string IThing.get_Name()\n{\nreturn \"{ <Work>d__3 }\";\n}\n";
string converted = Decompiler.SanitizeForTest(accessor);
if (!converted.Contains("string IThing.Name") || !converted.Contains("get\n")
    || !converted.Contains("\"{ <Work>d__3 }\"") || converted.Contains("get_Name"))
    throw new Exception("Explicit accessor regression: " + converted);
cases++;
var protectedFixture = SourceTextProtection.Mask("string s = \"keep\";");
bool rejected = false;
try { protectedFixture.Restore("string s = \"lost\";"); }
catch (InvalidOperationException) { rejected = true; }
if (!rejected) throw new Exception("Lost protected token was not rejected.");
cases++;
// Compile and execute the rewritten expressions with C#9. A counter detects
// duplication or loss of expression evaluation; literal metadata-shaped text
// must remain byte-for-byte visible in the resulting string.
string fixture = """
using System;
using System.Globalization;
public static class Fixture
{
    static int Calls;
    static string Next() { Calls++; return "ok"; }
    public static string Run()
    {
        CultureInfo.CurrentCulture = CultureInfo.InvariantCulture;
        var <e>5__5 = Next();
        var <>7__wrap2 = Next();
        var <value>5__2 = 2.5;
        string result = $"{{<literal>d__3}} {<e>5__5} {<>7__wrap2} {<value>5__2:F2} {Next()}";
        result += $@" | ""<literal>d__3"" {<e>5__5}";
        result += $" | {$"{<e>5__5} <literal>d__3"}";
        return result + " | " + Calls;
    }
}
""";
string sanitizedFixture = Decompiler.SanitizeForTest(fixture);
var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator)
    .Select(path => MetadataReference.CreateFromFile(path));
var compilation = CSharpCompilation.Create("SanitizationFixture", [CSharpSyntaxTree.ParseText(sanitizedFixture,
    new CSharpParseOptions(LanguageVersion.CSharp9))], references,
    new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
using var bytes = new MemoryStream();
var emitted = compilation.Emit(bytes);
if (!emitted.Success) throw new Exception(string.Join("\n", emitted.Diagnostics));
var assembly = Assembly.Load(bytes.ToArray());
var output = (string)assembly.GetType("Fixture")!.GetMethod("Run")!.Invoke(null, null)!;
const string expectedOutput = "{<literal>d__3} ok ok 2.50 ok | \"<literal>d__3\" ok | ok <literal>d__3 | 3";
if (output != expectedOutput) throw new Exception("Interpolation runtime behavior: " + output);
cases++;
Console.WriteLine($"PASS {cases} source-sanitization cases (literal preservation, idempotence, C#9 compilation and evaluation count)");

namespace Rewind.Output
{
    public static partial class Decompiler
    {
        public static string SanitizeForTest(string text)
        {
            SanitizeIdentifiers(ref text);
            return text;
        }
    }
}
