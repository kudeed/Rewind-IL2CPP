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
    }
}
