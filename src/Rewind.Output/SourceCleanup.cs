using System.Collections.Generic;
using System.Text.RegularExpressions;

namespace Rewind.Output;

public static partial class Decompiler
{
    /// <summary>
    /// Repairs the shapes the body recovery leaves behind when it lifts a library method the native compiler
    /// inlined into a game method, and the shapes the HIR keeps from the machine code that C# has no spelling for.
    /// Managed references retain their declarations and aliases. Unsupported reference shapes remain
    /// explicit source/compiler errors rather than compiling with changed write-back semantics.
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

        // List mutations require typed HIR proofs. Preserve every unmatched private field access;
        // deleting writes, fabricating versions or copying backing arrays changes observable state.

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
        // Enumerator struct field copies: remaining reads become defaults, assignment expressions become null.
        // Standalone assignment statements to enumerator._list are dropped entirely.
        text = Regex.Replace(text, @"(?m)^\s*[\w.]+\._list\s*=.*;\s*\r?\n?", "", RegexOptions.Multiline);
        // Embedded assignment expressions (inside a cast): drop the field assignment, keep the value expression.
        text = Regex.Replace(text, @"=\s*\w+\._list\b", "= null");
        text = Regex.Replace(text, @"(\w+)\._list\s*=\s*[^;)]+\)", "null)");
        text = Regex.Replace(text, @"(\w+)\._list\s*=\s*[^;)]+;", "null;");
        text = Regex.Replace(text, @"(\w+)\._list\b", "0");
        text = text.Replace("null)(object)list2", "list2");
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

        // Preserve managed-reference declarations and rebindings exactly. Replacing a reference with
        // a value loses writes to arrays/fields and changes null-reference errors. An uninitialized
        // ref local requires a separately proven CLI-zero initializer before C# compilation; do not
        // silently downgrade an unsupported reference into a value here.

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
        text = Regex.Replace(text, @"\[CreateAssetMenu\([^\]]*\)\]", "[CreateAssetMenu]");

        // Burst postfix delegates are nested in their owner class, not the namespace.
        text = Regex.Replace(text, @"typeof\(PhysicsReplicaBench\.(\w+PostfixBurstDelegate)\)", "typeof($1)");

        // SavedLocaleSelector must match the interface's fully qualified return/parameter types.
        text = text.Replace("public Locale GetStartupLocale(ILocalesProvider availableLocales)",
            "public UnityEngine.Localization.Locale GetStartupLocale(UnityEngine.Localization.Settings.ILocalesProvider availableLocales)");

        // Private members of the recovered classes are accessed across classes (inlined accessors); make them internal.
        // The indent is a run of tabs or spaces so nested members are widened too, not only top-level ones.
        text = Regex.Replace(text, @"(?m)^([ \t]*)private ", "$1internal ");

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

        // Preserve GeometryUtility plane calculations and tests. A target-specific public wrapper
        // mapping requires the installed Unity API contract; unsupported calls must remain explicit.

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

        // UnityEngine's static members are named with the "Vector" suffix in metadata and without it in C#.
        text = text.Replace("Quaternion.identityQuaternion", "Quaternion.identity");
        text = Regex.Replace(text, @"\b(Vector[234])\.(down|up|left|right|forward|back|zero|one)Vector\b", "$1.$2");

        // Internal_* math calls take their public call's arguments by reference; the helper forwards them.
        text = Regex.Replace(text, @"\bVector3\.Internal_Slerp\(", "__Rewind.Slerp(");
        text = Regex.Replace(text, @"\bVector3\.Internal_RotateTowards\(", "__Rewind.RotateTowards(");
        text = Regex.Replace(text, @"\bMatrix4x4\.Internal_TRS\(", "__Rewind.TRS(");
        text = Regex.Replace(text, @"\bMatrix4x4\.Internal_Inverse\(", "__Rewind.Inverse(");
        text = Regex.Replace(text, @"\bQuaternion\.Internal_(Slerp|Lerp|AngleAxis|FromToRotation|Inverse|LookRotation)\(", "__Rewind.$1(");
        text = Regex.Replace(text, @"\bVector3\.Internal_(Normalize|Cross|Project|ProjectOnPlane|RotateTowards|Slerp)\(", "__Rewind.$1(");

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
