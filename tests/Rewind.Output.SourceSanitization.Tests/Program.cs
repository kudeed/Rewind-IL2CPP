using Rewind.Output;

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
Console.WriteLine($"PASS {cases} source-sanitization cases (including literal preservation and idempotence)");

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
