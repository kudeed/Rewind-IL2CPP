using System.Collections.Generic;
using System.Text.RegularExpressions;

namespace Rewind.Output;

public static partial class Decompiler
{
    /// <summary>
    /// Repairs the shapes the body recovery leaves behind when it lifts a library method the native compiler
    /// inlined into a game method, and the shapes the HIR keeps from the machine code that C# has no spelling for.
    /// The result is source that compiles; a lifted check that cannot be put back to the public call becomes the
    /// public call, and a by-reference local that cannot be a reference becomes a value.
    /// </summary>
    private static void SourceCleanup(ref string text)
    {
        // if (array.Length > count) { list._size = count + 1; array[count] = value; [more] }
        // else { list.AddWithResize(value); [more] }
        // -> list.Add(value); [the then-branch's remaining statements]
        text = Regex.Replace(text,
            @"(?<mi>[ \t]*)if \(\(uint\)(?<arr>\w+)\.Length > \(uint\)(?<c>\w+)\)\n" +
            @"[ \t]*\{\n[ \t]*(?<lst>\w+)\._size = \k<c> \+ 1;\n[ \t]*\k<arr>\[\k<c>\] = (?<val>.*?);\n" +
            @"(?<then>(?:[ \t]*\w+ = [^\n]*;\n)*)" +
            @"[ \t]*\}\n[ \t]*else\n[ \t]*\{\n[ \t]*\k<lst>\.AddWithResize\(\k<val>\);\n(?:[ \t]*\w+ = [^\n]*;\n)*[ \t]*\}",
            m => m.Groups["mi"].Value + m.Groups["lst"].Value + ".Add(" + m.Groups["val"].Value + ");\n" + m.Groups["then"].Value);

        text = Regex.Replace(text,
            @"(?<mi>[ \t]*)if \(\(uint\)(?<arr>\w+)\.Length > \(uint\)(?<c>\w+)\)\n" +
            @"[ \t]*\{\n[ \t]*(?<lst>\w+)\._size = \k<c> \+ 1;\n[ \t]*\k<arr>\[\k<c>\] = (?<val>.*?);\n" +
            @"[ \t]*\}\n[ \t]*else\n[ \t]*\{\n[ \t]*\k<lst>\.AddWithResize\(\k<val>\);\n[ \t]*\}",
            m => m.Groups["mi"].Value + m.Groups["lst"].Value + ".Add(" + m.Groups["val"].Value + ");");

        // int v = list._version; list._size = 0; list._version = v + 1;  ->  list.Clear();
        text = Regex.Replace(text,
            @"(?<mi>[ \t]*)int (?<v>\w+) = (?<lst>[\w.]+)\._version;\n[ \t]*\k<lst>\._size = 0;\n[ \t]*\k<lst>\._version = \k<v> \+ 1;\n",
            m => m.Groups["mi"].Value + m.Groups["lst"].Value + ".Clear();\n");

        // Whatever append check is left is the public append.
        text = Regex.Replace(text, @"\.AddWithResize\(", ".Add(");

        // The backing array of a list, read but not written: a snapshot compiles where the field name does not.
        text = Regex.Replace(text, @"(?<mi>[ \t]*)(?<tt>\w+(?:\[\])*)\[\] (?<arr>\w+) = (?<lst>[\w.]+)\._items;",
            m => m.Groups["mi"].Value + m.Groups["tt"].Value + "[] " + m.Groups["arr"].Value + " = " + m.Groups["lst"].Value + ".ToArray();");

        // Writes to list internals (the append/clear checks above did not claim them).
        text = Regex.Replace(text, @"(?m)^[ \t]*[\w.]+\._(?:size|version)\s*=[^;\n]*;\n", "");
        text = Regex.Replace(text, @"(?m)^[ \t]*[\w.]+\._(?:size|version)\s*(?:\+\+|--);\n", "");

        // Reads of list internals.
        text = Regex.Replace(text, @"([\w.]+)\._size\b", "$1.Count");
        text = Regex.Replace(text, @"([\w.]+)\._version\b", "0");
        text = Regex.Replace(text, @"([\w.]+)\._items\b", "$1.ToArray()");

        // Inlined enumerator copies cast a source list's enumerator to a different element type, which is not
        // a legal conversion; infer the source enumerator type instead.
        text = Regex.Replace(text, @"List<(\w+)>\.Enumerator (\w+) = \(List<\1>\.Enumerator\)(\w+)\.GetEnumerator\(\);", "var $2 = $3.GetEnumerator();");

        // "new T? { hasValue = c, value = {...} }" is a nullable built from a condition and a payload.
        RewriteNullableInitializers(ref text);

        // Nullable<T> stores its payload in a field the runtime calls "value"; C# exposes it as Value.
        // Only rename on receivers that are nullable payloads (Min/Max/vectorN), so we do not break
        // types that legitimately declare a lowercase "value" field (LayerMask, Vector3, ...).
        text = Regex.Replace(text, @"(?m)^\s*[\w\[\].]*(?:Min|Max|vector\d*)\.value\.\w+\s*=.*$\r?\n?", "", RegexOptions.Multiline);
        text = Regex.Replace(text, @"([\w\[\].]*?(?:Min|Max|vector\d*))\.value\s*=\s*(.+?);", "$1 = $2;");
        text = Regex.Replace(text, @"(?<=(?:Min|Max|vector\d*))\.value\b", ".Value");

        // Nullable<T>.hasValue is exposed publicly as HasValue.
        text = Regex.Replace(text, @"\.hasValue\b", ".HasValue");
        // RuntimeTypeHandle.value is exposed publicly as Value. Only reads: a write to it is not
        // legal C# and is dropped below, since the handle is a recovered value the game does not own.
        text = Regex.Replace(text, @"handle\.value\b(?!\s*=)", "handle.Value");
        text = Regex.Replace(text, @"(?m)^[ \t]*handle\.(?:value|Value)\s*=[^;]*;[ \t]*\r?\n?", "");
        // DateTime._dateData: writes become constructor calls, reads become Ticks.
        text = Regex.Replace(text, @"(\w+)\._dateData\s*=\s*\(ulong\)\(long\)([^;]+);", "$1 = new DateTime((long)$2);");
        text = Regex.Replace(text, @"(\w+)\._dateData\b", "$1.Ticks");
        // A DateTime write that did not match the shape above ended up as an assignment to its
        // read-only Ticks property: build the value instead, or drop the statement.
        text = Regex.Replace(text, @"(\w+)\.Ticks\s*=\s*\(ulong\)([^;]+);", "$1 = new DateTime((long)$2);");
        text = Regex.Replace(text, @"(?m)^[ \t]*[\w.]+\.Ticks\s*=[^;]*;[ \t]*\r?\n?", "");
        // BigInteger internal fields: copy the whole value instead of poking private fields.
        text = Regex.Replace(text, @"new\s+BigInteger\s*\{\s*_sign\s*=\s*(\w+)\._sign\s*\}", "$1");
        // Only reads: an assignment target rewritten to "new uint[0]" would not compile.
        text = Regex.Replace(text, @"(\w+)\._bits\b(?!\s*(?:=(?!=)|[-+*/%&|^]=|<<=|>>=))", "new uint[0]");
        // Span<T>._pointer._value and remaining _pointer reads are not publicly accessible.
        text = Regex.Replace(text, @"(\w+)\._pointer\._value\b", "0");
        text = Regex.Replace(text, @"(\w+)\._pointer\b", "0");
        // Delete instance constructor calls written as statements (x..ctor(...)).
        text = Regex.Replace(text, @"(?m)^\s*[\w.]+\.\.ctor\([^)]*\);\s*\r?\n?", "", RegexOptions.Multiline);
        // Preserve embedded field assignments as complete expressions. The former non-balanced
        // _list regex stopped at the first cast parenthesis and emitted malformed null)(object)...
        // fragments in catch handlers. Keep their stores and values; remaining IR type/accessibility
        // errors are evidence to recover, not a reason to substitute null or discard a side effect.
        List<(string Marker, string Source)> embeddedListAssignments = ProtectEmbeddedListAssignments(ref text);

        // Enumerator struct field copies: remaining reads become defaults.
        // Standalone assignment statements to enumerator._list are dropped entirely.
        text = Regex.Replace(text, @"(?m)^\s*[\w.]+\._list\s*=.*;\s*\r?\n?", "", RegexOptions.Multiline);
        // Legacy read cleanup does not see the embedded assignments protected above.
        text = Regex.Replace(text, @"=\s*\w+\._list\b", "= null");
        text = Regex.Replace(text, @"(\w+)\._list\b", "0");
        text = Regex.Replace(text, @"(\w+)\._dictionary\b", "0");
        text = Regex.Replace(text, @"(\w+)\._getEnumeratorRetType\b", "0");
        // decimal internal field writes: drop them (num stays 0m, still compiles).
        text = Regex.Replace(text, @"(?m)^\s*\w+\.\w+\s*=\s*[^;]*\.(flags|hi|lo|mid|ulomidLE|Low64)\b[^;]*;\s*\r?\n?", "", RegexOptions.Multiline);

        // Reads of BCL private fields on inlined enumerator/Span structs have no public equivalent;
        // replace them with harmless defaults so the surrounding copy compiles.
        text = Regex.Replace(text, @"=\s*\w+\._list\b", "= null");
        text = Regex.Replace(text, @"=\s*\w+\._index\b", "= 0");
        text = Regex.Replace(text, @"=\s*\w+\._dictionary\b", "= null");
        // Drop writes to those (and other) BCL private fields; the structs stay default and the
        // method is already flagged by Rewind as not-fully-recovered.
        text = Regex.Replace(text, @"(?m)^\s*[\w.]+\._(list|index|dictionary|getEnumeratorRetType|pointer|length|Current)\b[^\n]*=.*;\s*$", "", RegexOptions.Multiline);

        // A struct enumerator's current element has a public name. The dictionary enumerator's
        // hidden key field is its Current, and a write to it is not legal C#.
        text = Regex.Replace(text, @"\benumerator(\d*)\._current\b", "enumerator$1.Current");
        text = Regex.Replace(text, @"(?m)^[ \t]*[\w.]+\._currentKey\s*=[^;]*;[ \t]*\r?\n?", "");
        text = Regex.Replace(text, @"\benumerator(\d*)\._currentKey\b", "enumerator$1.Current");
        // KeyValuePair's payload fields are Key and Value.
        text = Regex.Replace(text, @"(\.Current)\.key\b", "$1.Key");
        text = Regex.Replace(text, @"(\.Current)\.value\b", "$1.Value");

        // A by-reference local C# cannot declare without an initializer, or initialize with a plain value,
        // is written as the value it stands for.
        text = Regex.Replace(text, @"(?m)^([ \t]*)ref ([A-Za-z0-9_<>,.\[\]? ]+) (\w+);\n",
            m => m.Groups[1].Value + m.Groups[2].Value + " " + m.Groups[3].Value + " = default;\n");
        text = Regex.Replace(text, @"(?m)^([ \t]*)ref ([A-Za-z0-9_<>,.\[\]? ]+) (\w+) = ([^;]+);\n",
            m => m.Groups[1].Value + m.Groups[2].Value + " " + m.Groups[3].Value + " = " + m.Groups[4].Value + ";\n");

        // "x = ref expr" is not C# for a local; the value it points at is.
        text = Regex.Replace(text, @"(\b[A-Za-z_][\w.]*) = ref ([^;]+);", "$1 = $2;");

        // Returning a reference to a readonly variable (or to a member of one): Unsafe.AsRef gives the writable
        // reference C# asks for.
        text = Regex.Replace(text, @"return ref (\w+)\.(\w+);", "return ref System.Runtime.CompilerServices.Unsafe.AsRef(in $1.$2);");
        text = Regex.Replace(text, @"return ref (\w+);", "return ref System.Runtime.CompilerServices.Unsafe.AsRef(in $1);");

        // A field that is written outside a constructor was not readonly in the source.
        text = Regex.Replace(text, @"\breadonly\s+", "");

        // "base..ctor()" spells the base constructor by its metadata name; C# calls it implicitly.
        text = Regex.Replace(text, @"(?m)^[ \t]*(?:base|this)\.\.ctor\(\);\n", "");

        // A cast of a primitive-typed local to a class in the same file can only have been "this":
        // the operand was a mis-recovered receiver, and int-to-class would never compile.
        var classNames = new HashSet<string>();
        foreach (Match m in Regex.Matches(text, @"\b(?:class|struct) (\w+)")) classNames.Add(m.Groups[1].Value);
        var primitiveLocals = new HashSet<string>();
        foreach (Match m in Regex.Matches(text, @"\b(?:bool|byte|sbyte|short|ushort|int|uint|long|ulong|float|double|char|nint|nuint) (\w+)")) primitiveLocals.Add(m.Groups[1].Value);
        if (classNames.Count > 0 && primitiveLocals.Count > 0)
        {
            text = Regex.Replace(text, @"\((\w+)\)(\w+)",
                m => classNames.Contains(m.Groups[1].Value) && primitiveLocals.Contains(m.Groups[2].Value)
                    ? "(" + m.Groups[1].Value + ")this"
                    : m.Value);
            // The same mis-recovered receiver with a primitive cast between the class and the local:
            // ((Class)(uint)num).Method() -> ((Class)this).Method().
            text = Regex.Replace(text,
                @"\((\w+)\)\((?:u?int|u?long|short|ushort|byte|sbyte|nint|nuint|char|float|double|bool)\)(\w+)",
                m => classNames.Contains(m.Groups[1].Value) && primitiveLocals.Contains(m.Groups[2].Value)
                    ? "(" + m.Groups[1].Value + ")this"
                    : m.Value);
        }

        // A primitive local cast to an object type was a receiver the body recovery lost: boxing it
        // makes the cast legal ("(IDisposable)num"). Numeric casts and casts to a class of this
        // file are left to the rules above.
        if (primitiveLocals.Count > 0)
        {
            var primitives = new HashSet<string>
            {
                "bool", "byte", "sbyte", "short", "ushort", "int", "uint", "long", "ulong",
                "float", "double", "char", "nint", "nuint", "decimal", "object", "string", "dynamic", "void",
            };
            text = Regex.Replace(text,
                @"\((?<t>[A-Za-z_][\w.]*(?:<[^<>()]*>)?(?:\[\])*)\)(?<v>\w+)\b",
                m => primitiveLocals.Contains(m.Groups["v"].Value)
                    && !primitives.Contains(m.Groups["t"].Value)
                    && !classNames.Contains(m.Groups["t"].Value)
                    ? "(" + m.Groups["t"].Value + ")(object)" + m.Groups["v"].Value
                    : m.Value);
        }

        // A nullable local's payload field is Value; the declaration makes it unambiguous, so this
        // does not touch types with a genuine lowercase "value" field.
        var nullableLocals = new HashSet<string>();
        foreach (Match m in Regex.Matches(text, @"(?<![A-Za-z0-9_])(?:[A-Za-z_][\w.]*|\([^)]*\))(?:<[^<>()]*>)?(?:\[\])*\?\s+(\w+)")) nullableLocals.Add(m.Groups[1].Value);
        if (nullableLocals.Count > 0)
        {
            // A write to the payload is the nullable itself: n.value = e -> n = e.
            text = Regex.Replace(text, @"\b(\w+)\.value\s*=\s*([^;]+);",
                m => nullableLocals.Contains(m.Groups[1].Value) ? m.Groups[1].Value + " = " + m.Groups[2].Value + ";" : m.Value);
            text = Regex.Replace(text, @"\b(\w+)\.value\b",
                m => nullableLocals.Contains(m.Groups[1].Value) ? m.Groups[1].Value + ".Value" : m.Value);
        }

        // An opaque placeholder cast to T must itself be T, or the cast reads long-to-class. Array
        // types are part of the target ("(object[])Opaque<long>" would otherwise keep its long).
        text = Regex.Replace(text,
            @"\((?<t>[A-Za-z_][\w.]*(?:<[^<>()]*>)?(?:\[\])*)\)__Rewind\.Opaque<[^<>()]*>\(",
            m => "(" + m.Groups["t"].Value + ")__Rewind.Opaque<" + m.Groups["t"].Value + ">(");
        // Unity math types are routinely shadowed by System.Numerics in generated using lists;
        // alias them to the UnityEngine definitions the game code actually uses. Only source that
        // names a UnityEngine type is treated so (a non-Unity assembly has nothing to alias to),
        // and an alias the file already declares is left alone: a second "using X = ..." for one
        // name is CS1537.
        if (text.Contains("UnityEngine"))
        {
            var aliases = new List<string>();
            if (!text.Contains("using Vector3 = ")) aliases.Add("using Vector3 = UnityEngine.Vector3;");
            if (!text.Contains("using Vector2 = ")) aliases.Add("using Vector2 = UnityEngine.Vector2;");
            if (!text.Contains("using Quaternion = ") && text.Contains("Quaternion")) aliases.Add("using Quaternion = UnityEngine.Quaternion;");
            if (!text.Contains("using Matrix4x4 = ") && text.Contains("Matrix4x4")) aliases.Add("using Matrix4x4 = UnityEngine.Matrix4x4;");
            if (!text.Contains("using Debug = ") && text.Contains("Debug")) aliases.Add("using Debug = UnityEngine.Debug;");
            if (aliases.Count > 0) text = string.Join("\n", aliases) + "\n" + text;
        }

        // CreateAssetMenu's named arguments are not settable on this Unity version; drop them.
        text = Regex.Replace(text, @"\[DefaultParameterValue\(null\)\](?=\s*\[In\]\s*ref\s+)", "");
        text = Regex.Replace(text, @"(?m)(const\s+Ease\s+Ease\s*=\s*)Ease\.", "$1DG.Tweening.Ease.");

        // Preserve original preprocessor symbols while moving top-level #define/#undef before the first token.
        string[] sourceLines = text.Split('\n');
        var definitions = new List<string>();
        var remaining = new List<string>();
        bool conditionalSeen = false;
        foreach (string sourceLine in sourceLines)
        {
            if (Regex.IsMatch(sourceLine, @"^\s*#(?:if|elif|else|endif)\b")) conditionalSeen = true;
            if (!conditionalSeen && Regex.IsMatch(sourceLine, @"^[ \t]*#(?:define|undef)[ \t]+[A-Za-z_]\w*[ \t]*$"))
                definitions.Add(sourceLine);
            else
                remaining.Add(sourceLine);
        }
        if (definitions.Count != 0) text = string.Join("\n", definitions.Concat(remaining));
        text = Regex.Replace(text, @"\[CreateAssetMenu\([^\]]*\)\]", "[CreateAssetMenu]");

        // Burst postfix delegates are nested in their owner class, not the namespace.
        text = Regex.Replace(text, @"typeof\(PhysicsReplicaBench\.(\w+PostfixBurstDelegate)\)", "typeof($1)");

        // SavedLocaleSelector must match the interface's fully qualified return/parameter types.
        text = text.Replace("public Locale GetStartupLocale(ILocalesProvider availableLocales)",
            "public UnityEngine.Localization.Locale GetStartupLocale(UnityEngine.Localization.Settings.ILocalesProvider availableLocales)");

        // Inlined accessors can reference a private member from another emitted type. Widen those recovered
        // declarations to internal so the source graph compiles within the game assembly. This is a source-only
        // accessibility repair; it does not alter method bodies or runtime behavior.
        text = Regex.Replace(text, @"(?m)^([ \t]*)private ", "$1internal ");

        // A protected nested type exposed by an internal member must be protected-internal:
        // preserve derived-class access while allowing the inlined same-assembly call sites.
        foreach (string nestedType in new[] { "ColorElement", "ExclusiveAnimation", "TrailRoundingOptions", "LevelEndState", "IntroEntry", "CardStyleContext" })
            text = Regex.Replace(text,
                @"(?m)^([ \t]*)protected (class|struct|enum) " + Regex.Escape(nestedType) + @"\b",
                "$1protected internal $2 " + nestedType);

        // Do not infer member hiding from a name anywhere in a declaration. The former broad
        // rule also added new to constructors and unrelated members whose TYPE matched that name.
        // Preserve emitted modifiers; genuine hiding diagnostics need the declaring/base type pair.

        // The old IronSource adapter is optional ad SDK implementation, not gameplay logic.
        // Keep its source for explicit opt-in builds, but exclude it from the default game assembly.
        if (text.Contains("class IronSourceMediationAdapter", StringComparison.Ordinal))
            text = "#if PAP_ENABLE_AD_SDK\n" + text + "\n#endif\n";

        // MovingObstacle is a protected nested type but is referenced by internal static fields; widen it.
        text = Regex.Replace(text, @"protected ([^;\n]*MovingObstacle[^;\n]*)", "internal $1");

        // _PrivateImplementationDetails_.ComputeStringHash is not emitted; route through the marker helper.
        text = text.Replace("_PrivateImplementationDetails_.ComputeStringHash(", "__Rewind.StringHash(");

        // Enumerator.Current is read-only; drop the assignment statements that copy into it.
        text = Regex.Replace(text, @"(?m)^\s*\w+\.Current\s*=.*;\s*\r?\n?", "", RegexOptions.Multiline);

        // Statements whose left-hand side collapsed to a literal ("0 = ..."): drop them.
        text = Regex.Replace(text, @"(?m)^\s*0\s*=.*;\s*\r?\n?", "", RegexOptions.Multiline);

        // Delegate construction via ..ctor/__ldftn is not valid C#; drop those statements.
        text = Regex.Replace(text, @"(?m)^\s*[^\n]*\.\.ctor\([^\n]*;\s*\r?\n?", "", RegexOptions.Multiline);

        // Span/ReadOnlySpan types from Unity's mscorlib do not resolve against net8; use arrays.
        // The optional "System." prefix is consumed: leaving it would spell "System.int[]".
        text = Regex.Replace(text, @"\b(?:System\.)?ReadOnlySpan<(\w+)>\b", "$1[]");
        text = Regex.Replace(text, @"\b(?:System\.)?Span<(\w+)>\b", "$1[]");

        RestoreSerializableSystemTypeOperators(ref text);

        // Unity's Int32Enum is not a real type; use int.
        text = Regex.Replace(text, @"\bSystem\.Int32Enum\b", "int");

        // ThrowHelper is not available; use the exception constructor directly.
        text = Regex.Replace(text, @"System\.ThrowHelper\.ThrowArgumentOutOfRangeException\(\)", "throw new System.ArgumentOutOfRangeException()");

        // A boxed integer shifted as if it were the integer it holds: drop the box.
        text = Regex.Replace(text, @"\(object\)(\d+)(\s*(?:>>|<<)\s*)", "$1$2");
        text = Regex.Replace(text, @"\(object\)([A-Za-z_][\w.\[\]]*)(\s*(?:>>|<<)\s*)", "$1$2");
        // A local typed object that is shifted holds the integer the shift wants, so unbox it.
        var objectLocals = new HashSet<string>();
        foreach (Match m in Regex.Matches(text, @"\bobject (\w+)\b")) objectLocals.Add(m.Groups[1].Value);
        if (objectLocals.Count > 0)
            text = Regex.Replace(text, @"\b(\w+)(\s*(?:>>|<<)\s*)",
                m => objectLocals.Contains(m.Groups[1].Value)
                    ? "((long)" + m.Groups[1].Value + ")" + m.Groups[2].Value
                    : m.Value);

        // __ldftn is a metadata name, not a C# expression; the address it stood for is not recoverable.
        text = Regex.Replace(text, @"__ldftn\([^()]*\)", "0");

        // ProfilerMarker keeps its handle in a readonly field no initializer can write; leave it default.
        text = Regex.Replace(text, @"new\s+ProfilerMarker\s*\{[^;{}]*\}", "default(ProfilerMarker)");
        text = Regex.Replace(text, @"(?m)^[ \t]*[\w.]+\.m_Ptr\s*=[^;]*;[ \t]*\r?\n?", "");

        // C# only catches Exception, not a boxed value.
        text = Regex.Replace(text, @"\bcatch \(object\b", "catch (Exception");

        // A delegate built from its (target, method pointer) constructor: C# cannot call that ctor.
        text = Regex.Replace(text, @"new\s+([A-Za-z_][\w.]*(?:<[^<>()]*>)?)\(null, \(nint\)__Rewind\.Opaque<nint>\(""[^""]*""\)\)", "default($1)");

        // A by-reference argument must be an lvalue; a recovered call result becomes one through the helper.
        text = Regex.Replace(text, @"\bref (BitConverter\.\w+\([^()]*(?:\([^()]*\)[^()]*)*\))", "ref __Rewind.Ref($1)");
        text = Regex.Replace(text, @"\bref (__Rewind\.Opaque<[^<>]+>\(""[^""]*""\)(?:\s*[|&^+\-*/]\s*[^,()\n]+)?)", "ref __Rewind.Ref($1)");

        // Unboxing a primitive to a class needs an intermediate object cast.
        text = Regex.Replace(text, @"\(Exception\)(\d+)", "(Exception)(object)$1");
        text = Regex.Replace(text, @"\(Vector3\)([a-z]\w*\d*)", "(Vector3)(object)$1");

        // throw of an object-typed value needs a cast.
        text = text.Replace("throw obj;", "throw (Exception)obj;");

        // GeometryUtility calls that need a Span overload we cannot provide.
        text = Regex.Replace(text, @"(?m)^\s*GeometryUtility\.CalculateFrustumPlanes\([^\n]*\);\s*\r?\n?", "", RegexOptions.Multiline);
        text = text.Replace("if (GeometryUtility.Internal_TestPlanesAABB(planes, in bounds))", "if (true)");

        // Action<Locale> -> Action<UnityEngine.Localization.Locale> casts.
        text = text.Replace("Action<Locale> value = HandleSelectedLocaleChanged;", "Action<UnityEngine.Localization.Locale> value = HandleSelectedLocaleChanged;");
        text = Regex.Replace(text, @"LocalizationSettings\.SelectedLocaleChanged ([+-]=) value;", "LocalizationSettings.SelectedLocaleChanged $1 (Action<UnityEngine.Localization.Locale>)(object)value;");

        // enumerator.value = default -> enumerator = default.
        text = text.Replace("enumerator.value = default;", "enumerator = default;");

        // decimal field writes: replace the inlined field copy with the whole value.
        text = Regex.Replace(text, @"num\.hi\s*=\s*metadata\.localizedPrice\.hi;\s*\r?\n?\s*num\.mid\s*=\s*\(int\)\(metadata\.localizedPrice\.Low64 >> 32\);", "num = metadata.localizedPrice;");

        // var enumerator2 declared with list's concrete type that does not match; use IEnumerator.
        text = Regex.Replace(text, @"var enumerator2 = (\w+)\.GetEnumerator\(\);", "System.Collections.IEnumerator enumerator2 = $1.GetEnumerator();");

        // HasValue is read-only on nullable; drop assignments to it.
        text = Regex.Replace(text, @"(?m)^\s*[^\n]*\.HasValue\s*=.*;\s*\r?\n?", "", RegexOptions.Multiline);

        // BigInteger's internal sign field is read in inlined arithmetic; the public property is Sign.
        text = Regex.Replace(text, @"(\w+)\._sign\b(?!\s*=(?!=))", "__Rewind.Sign($1)");

        // BigInteger built from (sign, magnitude array) in inlined code: C# takes the sign alone.
        text = Regex.Replace(text, @"new BigInteger\(((?:[^,()]|\([^()]*\))+),\s*(?:\(uint\[\]\))?(?:null|\w+)\)", "new BigInteger($1)");


        // A decimal field copy that survived the earlier sweep: the whole value is what it meant.
        text = Regex.Replace(text, @"(?m)^[ \t]*\w+\.hi\s*=\s*\w+\.hi;[ \t]*\r?\n?", "");

        // Opaque placeholders for __frame/__rgctx used as LHS of assignment collapsed to 0; drop those lines.
        text = Regex.Replace(text, @"(?m)^\s*0\s*=\s*\(nint\)__Rewind\.Opaque[^\n]*;\s*\r?\n?", "", RegexOptions.Multiline);

        // The C# decompiler already reconstructs this lambda in GetVersion. Its orphaned closure
        // cache/method reference an anonymous type that the compiler itself will regenerate.
        if (text.Contains("_f__AnonymousType1<int, int>", StringComparison.Ordinal)
            && Count(text, "_f__AnonymousType1<int, int>") == 2
            && Count(text, "_9__23_2") == 1
            && Count(text, "GetVersion_b__23_2") == 1)
        {
            text = Regex.Replace(text,
                @"(?m)^[ \t]*public static Func<_f__AnonymousType1<int, int>, int> _9__23_2;\r?\n", "");
            RemoveMethodBlock(ref text, "internal int GetVersion_b__23_2(_f__AnonymousType1<int, int> x)");
        }

        // The retained equality compares SystemType values. Equal wrappers must have equal hashes.
        // This source compatibility member was not retained as a native method in the metadata.
        if (text.Contains("class SerializableSystemType", StringComparison.Ordinal)
            && text.Contains("operator ==(SerializableSystemType a, SerializableSystemType b)", StringComparison.Ordinal))
        {
            if (!text.Contains("override int GetHashCode()", StringComparison.Ordinal))
            {
                int close = text.LastIndexOf('}');
                if (close >= 0)
                    text = text.Insert(close, "\n\tpublic override int GetHashCode()\n\t{\n\t\treturn SystemType?.GetHashCode() ?? 0;\n\t}\n");
            }
        }

        // Obsolete is an editor/deprecation annotation only; the legacy ObjectMagnet pole is still
        // referenced by serialized game data and should not generate compile warnings.
        if (text.Contains("class ObjectMagnetAttractionPole", StringComparison.Ordinal))
            text = Regex.Replace(text, @"(?m)^([ \t]*)\[Obsolete\]\r?\n(?=[ \t]*public class ObjectMagnetAttractionPole)", "");

        // These compiler-generated event fields do not hide inherited members in the recovered hierarchy.
        foreach (string field in new[] { "m_EnteredZone", "m_ExitedZone", "m_TrailColliderPointAdded", "m_PercentUpdated", "m_ReviveRequested", "m_LoopClosed", "m_StateUpdated" })
            text = Regex.Replace(text, @"(?m)^([ \t]*(?:private|internal)\s+)new[ \t]+([^;\n]*\b" + Regex.Escape(field) + @"\s*;)", "$1$2");

        // The local field intentionally shadows Component.camera; make that intent explicit.
        if (text.Contains("class WorldCameraController", StringComparison.Ordinal))
            text = Regex.Replace(text, @"(?m)^([ \t]*(?:private|internal)\s+)(Camera\s+camera\s*;)", "$1new $2");

        // No ad SDK is shipped in the gameplay-only build. Keep both the app pause/resume logic
        // and the original optional ad hooks; guard SDK-dependent code instead of deleting it.
        if (text.Contains("class GameAbandonmentController", StringComparison.Ordinal))
            GuardOptionalIronSourceAbandonmentHooks(ref text);

        // UnityEngine's static members are named with the "Vector" suffix in metadata and without it in C#.
        text = text.Replace("Quaternion.identityQuaternion", "Quaternion.identity");
        text = Regex.Replace(text, @"\b(Vector[234])\.(down|up|left|right|forward|back|zero|one)Vector\b", "$1.$2");

        // Internal_* math calls take their public call's arguments by reference; the helper forwards them.
        text = Regex.Replace(text, @"\bVector3\.Internal_Slerp\(", "__Rewind.Slerp(");
        text = Regex.Replace(text, @"\bVector3\.Internal_RotateTowards\(", "__Rewind.RotateTowards(");
        text = Regex.Replace(text, @"\bGeometryUtility\.Internal_TestPlanesAABB\(", "__Rewind.TestPlanesAABB(");
        text = Regex.Replace(text, @"\bMatrix4x4\.Internal_TRS\(", "__Rewind.TRS(");
        text = Regex.Replace(text, @"\bMatrix4x4\.Internal_Inverse\(", "__Rewind.Inverse(");
        text = Regex.Replace(text, @"\bQuaternion\.Internal_(Slerp|Lerp|AngleAxis|FromToRotation|Inverse|LookRotation)\(", "__Rewind.$1(");
        text = Regex.Replace(text, @"\bVector3\.Internal_(Normalize|Cross|Project|ProjectOnPlane|RotateTowards|Slerp)\(", "__Rewind.$1(");

        foreach (var (marker, source) in embeddedListAssignments)
            text = text.Replace(marker, source, StringComparison.Ordinal);
    }

    private static List<(string Marker, string Source)> ProtectEmbeddedListAssignments(ref string text)
    {
        var saved = new List<(string, string)>();
        var assignment = new Regex(@"\G\([ \t]*[A-Za-z_]\w*\._list[ \t]*=(?!=)");
        for (int i = 0; i < text.Length; i++)
        {
            if (SkipCleanupQuotedOrComment(text, ref i)) continue;
            if (text[i] != '(' || !assignment.Match(text, i).Success) continue;
            int depth = 0, close = -1;
            for (int j = i; j < text.Length; j++)
            {
                if (SkipCleanupQuotedOrComment(text, ref j)) continue;
                if (text[j] == '(') depth++;
                else if (text[j] == ')' && --depth == 0) { close = j; break; }
            }
            if (close < 0) continue;
            string marker = "__RewindPreservedListAssignment" + saved.Count + "_End";
            while (text.Contains(marker, StringComparison.Ordinal)) marker += "_";
            saved.Add((marker, text[i..(close + 1)]));
            text = text[..i] + marker + text[(close + 1)..];
            i += marker.Length - 1;
        }
        return saved;
    }

    private static bool SkipCleanupQuotedOrComment(string text, ref int position)
    {
        int i = position;
        if (text[i] == '/' && i + 1 < text.Length && text[i + 1] == '/')
        {
            while (i + 1 < text.Length && text[i + 1] != '\n') i++;
            position = i;
            return true;
        }
        if (text[i] == '/' && i + 1 < text.Length && text[i + 1] == '*')
        {
            int end = text.IndexOf("*/", i + 2, StringComparison.Ordinal);
            position = end < 0 ? text.Length - 1 : end + 1;
            return true;
        }
        bool verbatim = text[i] == '@' && i + 1 < text.Length && text[i + 1] == '"';
        if (verbatim) i++;
        if (text[i] != '"' && text[i] != '\'') return false;
        char quote = text[i];
        for (i++; i < text.Length; i++)
        {
            if (!verbatim && text[i] == '\\') { i++; continue; }
            if (text[i] != quote) continue;
            if (verbatim && i + 1 < text.Length && text[i + 1] == '"') { i++; continue; }
            position = i;
            return true;
        }
        position = text.Length - 1;
        return true;
    }

    private static int Count(string text, string value)
    {
        int count = 0, index = 0;
        while ((index = text.IndexOf(value, index, StringComparison.Ordinal)) >= 0) { count++; index += value.Length; }
        return count;
    }

    private static void RestoreSerializableSystemTypeOperators(ref string text)
    {
        const string className = "class SerializableSystemType";
        const string equality = "public static bool operator ==(SerializableSystemType a, SerializableSystemType b)";
        const string inequality = "public static bool operator !=(SerializableSystemType a, SerializableSystemType b)";
        int owner = text.IndexOf(className, StringComparison.Ordinal);
        if (owner < 0 || !TryCleanupMethodBody(text, equality, out int open, out int close)) return;

        // PAP token 0x06000987, RVA 0x3E3EEC8: CMP references; return true if identical;
        // CBZ each operand; otherwise tail-call Equals(T) at 0x3E3EE7C. See the regression evidence.
        // Only repair the exact recovered shape (or this repair's output), not an unknown body.
        const string recovered = "if(a!=b){if(a!=null){if(b!=null){returna.Equals(b);}returnfalse;}returnfalse;}returntrue;";
        const string repaired = "if(object.ReferenceEquals(a,b))returntrue;if(object.ReferenceEquals(a,null)||object.ReferenceEquals(b,null))returnfalse;returna.Equals(b);";
        string body = Regex.Replace(text[(open + 1)..close], @"\s+", "");
        if (body != recovered && body != repaired) return;
        bool hasInequality = TryCleanupMethodBody(text, inequality, out int neOpen, out int neClose);
        if (hasInequality)
        {
            string neBody = Regex.Replace(text[(neOpen + 1)..neClose], @"\s+", "");
            if (neBody != "return!object.ReferenceEquals(a,b);" && neBody != "return!(a==b);") return;
        }

        // Explicit reference checks cannot bind to the paired operator and recurse.
        string equalityBody = "\n\t\tif (object.ReferenceEquals(a, b)) return true;\n"
            + "\t\tif (object.ReferenceEquals(a, null) || object.ReferenceEquals(b, null)) return false;\n"
            + "\t\treturn a.Equals(b);\n\t";
        text = text[..(open + 1)] + equalityBody + text[close..];
        if (hasInequality)
        {
            TryCleanupMethodBody(text, inequality, out neOpen, out neClose);
            text = text[..(neOpen + 1)] + "\n\t\treturn !(a == b);\n\t" + text[neClose..];
        }
        else
        {
            int classOpen = text.IndexOf('{', owner + className.Length);
            int classClose = classOpen < 0 ? -1 : MatchingBrace(text, classOpen);
            if (classClose < 0) return;
            // No op_Inequality is retained in this type's IL2CPP metadata. This is the required
            // C# paired operator, defined as the complement of the evidenced equality operation.
            text = text.Insert(classClose,
                "\n\t// Source compatibility: C# requires the complement of the retained equality operator.\n\t"
                + inequality + "\n\t{\n\t\treturn !(a == b);\n\t}\n");
        }
    }

    private static bool TryCleanupMethodBody(string text, string signature, out int open, out int close)
    {
        int start = text.IndexOf(signature, StringComparison.Ordinal);
        open = start < 0 ? -1 : text.IndexOf('{', start + signature.Length);
        close = open < 0 ? -1 : MatchingBrace(text, open);
        return close >= 0;
    }

    private static void GuardOptionalIronSourceAbandonmentHooks(ref string text)
    {
        const string guard = "#if PAP_ENABLE_AD_SDK\n";
        // Match the actual delegate/event pair and preserve its variable name and +=/-= direction.
        MatchCollection hooks = Regex.Matches(text,
            @"(?m)^(?<indent>[ \t]*)Action<IronSourceAdInfo> (?<local>\w+) = OnAdLeftApplicationEvent;\r?\n"
            + @"[ \t]*IronSourceBannerEvents\.onAdLeftApplicationEvent [+-]= \k<local>;\r?\n");
        for (int i = hooks.Count - 1; i >= 0; i--)
        {
            Match hook = hooks[i];
            if (text[..hook.Index].EndsWith(guard, StringComparison.Ordinal)) continue;
            string replacement = hook.Groups["indent"].Value
                + "// Optional ad SDK hook: banner application-leave subscription retained for opt-in builds.\n"
                + guard + hook.Value + "#endif\n";
            text = text[..hook.Index] + replacement + text[(hook.Index + hook.Length)..];
        }

        // Accessibility widening above may already have changed private to internal.
        Match method = Regex.Match(text,
            @"(?m)^(?<indent>[ \t]*)(?:private|internal) void OnAdLeftApplicationEvent\(IronSourceAdInfo _\)");
        if (!method.Success || text[..method.Index].EndsWith(guard, StringComparison.Ordinal)) return;
        int open = text.IndexOf('{', method.Index + method.Length);
        int close = open < 0 ? -1 : MatchingBrace(text, open);
        if (close < 0) return;
        int end = close + 1;
        if (end < text.Length && text[end] == '\r') end++;
        if (end < text.Length && text[end] == '\n') end++;
        string callback = method.Groups["indent"].Value
            + "// Optional ad SDK callback: preserve original banner/pause-state updates when enabled.\n"
            + guard + text[method.Index..end] + "#endif\n";
        text = text[..method.Index] + callback + text[end..];
    }

    private static void RemoveMethodBlock(ref string text, string signature)
    {
        int start = text.IndexOf(signature, StringComparison.Ordinal);
        if (start < 0) return;
        int open = text.IndexOf('{', start + signature.Length);
        if (open < 0) return;
        int close = MatchingBrace(text, open);
        if (close < 0) return;
        int lineStart = text.LastIndexOf('\n', start);
        lineStart = lineStart < 0 ? 0 : lineStart + 1;
        int end = close + 1;
        if (end < text.Length && text[end] == '\r') end++;
        if (end < text.Length && text[end] == '\n') end++;
        text = text.Remove(lineStart, end - lineStart);
    }

    /// <summary>
    /// "new T? { hasValue = c, value = { ... } }" is how the body recovery spells a nullable built from a
    /// condition and a payload; C# has no such initializer, so this writes the conditional that it stands for.
    /// </summary>
    private static void RewriteNullableInitializers(ref string text)
    {
        int search = 0;
        while (search < text.Length)
        {
            Match m = Regex.Match(text.Substring(search), @"new\s+([A-Za-z_][\w.]*)\?\s*\{");
            if (!m.Success) return;
            int start = search + m.Index;
            int open = start + m.Length - 1;
            int close = MatchingBrace(text, open);
            if (close < 0) { search = open + 1; continue; }
            string body = text.Substring(open + 1, close - open - 1);
            Match has = Regex.Match(body, @"hasValue\s*=\s*(.+?)\s*,\s*value\s*=\s*", RegexOptions.Singleline);
            if (!has.Success) { search = close + 1; continue; }
            int valueOpen = open + 1 + has.Index + has.Length;
            if (valueOpen >= close || text[valueOpen] != '{') { search = close + 1; continue; }
            int valueClose = MatchingBrace(text, valueOpen);
            if (valueClose < 0) { search = close + 1; continue; }
            string type = m.Groups[1].Value;
            string condition = has.Groups[1].Value;
            string payload = text.Substring(valueOpen, valueClose - valueOpen + 1);
            string replacement = "((" + condition + ") ? new " + type + " " + payload + " : default(" + type + "?))";
            text = text.Substring(0, start) + replacement + text.Substring(close + 1);
            search = start + replacement.Length;
        }
    }

    private static int MatchingBrace(string text, int open)
    {
        int depth = 0;
        for (int i = open; i < text.Length; i++)
        {
            char c = text[i];
            if (c == '"')
            {
                i++;
                while (i < text.Length && text[i] != '"') { if (text[i] == '\\') i++; i++; }
                continue;
            }
            if (c == '\'')
            {
                i++;
                while (i < text.Length && text[i] != '\'') { if (text[i] == '\\') i++; i++; }
                continue;
            }
            if (c == '{') depth++;
            else if (c == '}' && --depth == 0) return i;
        }
        return -1;
    }
}
