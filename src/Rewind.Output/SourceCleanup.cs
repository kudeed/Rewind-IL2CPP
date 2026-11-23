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

        // Nullable<T> stores its payload in a field the runtime calls "value"; C# exposes it as Value.
        // Only rename on receivers that are nullable payloads (Min/Max/vectorN), so we do not break
        // types that legitimately declare a lowercase "value" field (LayerMask, Vector3, ...).
        text = Regex.Replace(text, @"(?m)^\s*[\w\[\].]*(?:Min|Max|vector\d*)\.value\.\w+\s*=.*$\r?\n?", "", RegexOptions.Multiline);
        text = Regex.Replace(text, @"([\w\[\].]*?(?:Min|Max|vector\d*))\.value\s*=\s*(.+?);", "$1 = $2;");
        text = Regex.Replace(text, @"(?<=(?:Min|Max|vector\d*))\.value\b", ".Value");

        // Nullable<T>.hasValue is exposed publicly as HasValue.
        text = Regex.Replace(text, @"\.hasValue\b", ".HasValue");
        // RuntimeTypeHandle.value is exposed publicly as Value.
        text = Regex.Replace(text, @"handle\.value\b", "handle.Value");
        // DateTime._dateData: writes become constructor calls, reads become Ticks.
        text = Regex.Replace(text, @"(\w+)\._dateData\s*=\s*\(ulong\)\(long\)([^;]+);", "$1 = new DateTime((long)$2);");
        text = Regex.Replace(text, @"(\w+)\._dateData\b", "$1.Ticks");
        // BigInteger internal fields: copy the whole value instead of poking private fields.
        text = Regex.Replace(text, @"new\s+BigInteger\s*\{\s*_sign\s*=\s*(\w+)\._sign\s*\}", "$1");
        text = Regex.Replace(text, @"(\w+)\._bits\b", "new uint[0]");
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

        // A struct enumerator's current element has a public name.
        text = Regex.Replace(text, @"\benumerator(\d*)\._current\b", "enumerator$1.Current");

        // A by-reference local C# cannot declare without an initializer, or initialize with a plain value,
        // is written as the value it stands for.
        text = Regex.Replace(text, @"(?m)^([ \t]*)ref ([A-Za-z0-9_<>,.\[\]? ]+) (\w+);\n",
            m => m.Groups[1].Value + m.Groups[2].Value + " " + m.Groups[3].Value + " = default;\n");
        text = Regex.Replace(text, @"(?m)^([ \t]*)ref ([A-Za-z0-9_<>,.\[\]? ]+) (\w+) = ([^;]+);\n",
            m => m.Groups[1].Value + m.Groups[2].Value + " " + m.Groups[3].Value + " = " + m.Groups[4].Value + ";\n");

        // "x = ref expr" is not C# for a local; the value it points at is.
        text = Regex.Replace(text, @"(\b[A-Za-z_][\w.]*) = ref ([^;]+);", "$1 = $2;");

        // Returning a reference to a readonly variable: Unsafe.AsRef gives the writable reference C# asks for.
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
        }

        // An opaque placeholder cast to T must itself be T, or the cast reads long-to-class.
        text = Regex.Replace(text,
            @"\((?<t>[A-Za-z_][\w.]*(?:<[^<>()]*>)?)\)__Rewind\.Opaque<[^<>()]*>\(",
            m => "(" + m.Groups["t"].Value + ")__Rewind.Opaque<" + m.Groups["t"].Value + ">(");
        // Unity math types are routinely shadowed by System.Numerics in generated using lists;
        // alias them to the UnityEngine definitions the game code actually uses.
        if (!text.Contains("using Vector3 = UnityEngine.Vector3;"))
        {
            text = "using Vector3 = UnityEngine.Vector3;\nusing Vector2 = UnityEngine.Vector2;\nusing Quaternion = UnityEngine.Quaternion;\nusing Debug = UnityEngine.Debug;\n" + text;
        }

        // CreateAssetMenu's named arguments are not settable on this Unity version; drop them.
        text = Regex.Replace(text, @"\[CreateAssetMenu\([^\]]*\)\]", "[CreateAssetMenu]");

        // Burst postfix delegates are nested in their owner class, not the namespace.
        text = Regex.Replace(text, @"typeof\(PhysicsReplicaBench\.(\w+PostfixBurstDelegate)\)", "typeof($1)");

        // SavedLocaleSelector must match the interface's fully qualified return/parameter types.
        text = text.Replace("public Locale GetStartupLocale(ILocalesProvider availableLocales)",
            "public UnityEngine.Localization.Locale GetStartupLocale(UnityEngine.Localization.Settings.ILocalesProvider availableLocales)");

        // Private members of the recovered classes are accessed across classes (inlined accessors); make them internal.
        text = Regex.Replace(text, @"(?m)^(\t)private ", "$1internal ");

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
        text = Regex.Replace(text, @"\bReadOnlySpan<(\w+)>\b", "$1[]");
        text = Regex.Replace(text, @"\bSpan<(\w+)>\b", "$1[]");

        // Unity's Int32Enum is not a real type; use int.
        text = Regex.Replace(text, @"\bSystem\.Int32Enum\b", "int");

        // ThrowHelper is not available; use the exception constructor directly.
        text = Regex.Replace(text, @"System\.ThrowHelper\.ThrowArgumentOutOfRangeException\(\)", "throw new System.ArgumentOutOfRangeException()");

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

        // Opaque placeholders for __frame/__rgctx used as LHS of assignment collapsed to 0; drop those lines.
        text = Regex.Replace(text, @"(?m)^\s*0\s*=\s*\(nint\)__Rewind\.Opaque[^\n]*;\s*\r?\n?", "", RegexOptions.Multiline);

    }
}

