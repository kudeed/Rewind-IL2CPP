using System.Text.RegularExpressions;

namespace Rewind.Output;

public static partial class Decompiler
{
    /// <summary>
    /// Repairs the shapes the body recovery leaves behind when it lifts a library method the native compiler
    /// inlined into a game method. The most common is <c>List&lt;T&gt;.Add</c>: its code is written out as reads and
    /// writes of the list's private fields (<c>_items</c>, <c>_size</c>, <c>_version</c>) plus a call to the private
    /// <c>AddWithResize</c>, which no source outside the class library can name. The check and the append are put
    /// back to the public call, and the backing-array read to <c>ToArray()</c>, which compiles.
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

        // The backing array of a list, read but not written: a snapshot compiles where the field name does not.
        text = Regex.Replace(text, @"(?<mi>[ \t]*)(?<tt>\w+)\[\] (?<arr>\w+) = (?<lst>\w+)\._items;\n",
            m => m.Groups["mi"].Value + m.Groups["tt"].Value + "[] " + m.Groups["arr"].Value + " = " + m.Groups["lst"].Value + ".ToArray();\n");

        // The version bump the append did is not needed once the append is the public call.
        text = Regex.Replace(text, @"[ \t]*\w+\._version\+\+;\n", "");
    }
}
