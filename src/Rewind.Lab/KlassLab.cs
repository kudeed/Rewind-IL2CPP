using Iced.Intel;
using Rewind.Analysis.Runtime;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Lab;

/// <summary>
/// klass-probe &lt;input&gt;: which offsets of the runtime's class record the game's code reads, next to the offsets
/// the layout for its version says. For checking the layout of a Unity version against a real build.
/// </summary>
internal static class KlassLab
{
    public static int Probe(Il2CppModel model)
    {
        NativeImage image = model.Image;
        if (image.Arch is not (CpuArch.X64 or CpuArch.Arm64))
        {
            Console.WriteLine("x64 and ARM64 only");
            return 2;
        }
        KlassLayout byVersion = KlassLayout.For(model.Version, image.PointerSize, model.UnityVersion);
        KlassLayout measured = KlassLayout.Measure(model, Console.WriteLine);
        Console.WriteLine($"by version: cctor_finished 0x{byVersion.CctorFinished:X}, interface_offsets_count 0x{byVersion.InterfaceOffsetsCount:X}, " +
                          $"typeHierarchyDepth 0x{byVersion.TypeHierarchyDepth:X}, bitflags 0x{byVersion.Bitflags:X}, vtable 0x{byVersion.VTable:X}");
        Console.WriteLine($"measured:   cctor_finished 0x{measured.CctorFinished:X}, interface_offsets_count 0x{measured.InterfaceOffsetsCount:X}, " +
                          $"typeHierarchyDepth 0x{measured.TypeHierarchyDepth:X}, bitflags 0x{measured.Bitflags:X}, vtable 0x{measured.VTable:X}, " +
                          $"has_cctor test at 0x{measured.HasCctorByte:X} mask 0x{measured.HasCctorMask:X}");
        if (Environment.GetEnvironmentVariable("REWIND_KLASS_RAW") == null) return 0;

        // The raw picture: every displacement in the neighbourhood, by how the code reads it.
        var compares = new SortedDictionary<long, int>();
        var words = new SortedDictionary<long, int>();
        var bytes = new SortedDictionary<long, int>();
        var tests = new SortedDictionary<(long, long), int>();
        foreach (FunctionRange f in image.FunctionTable)
        {
            int length = (int)(f.End - f.Start);
            if (length <= 0 || !image.TrySpan(f.Start, length, out ReadOnlySpan<byte> code)) continue;
            var decoder = Decoder.Create(64, new ByteArrayCodeReader(code.ToArray()), f.Start);
            while (decoder.IP < f.End)
            {
                decoder.Decode(out Instruction ins);
                if (ins.IsInvalid) break;
                if (ins.MemoryBase is Register.None or Register.RSP or Register.RBP or Register.RIP || ins.MemoryIndex != Register.None) continue;
                long d = (long)ins.MemoryDisplacement64;
                if (ins.Mnemonic == Mnemonic.Cmp && ins.Op0Kind == OpKind.Memory && ins.MemorySize is MemorySize.UInt32 or MemorySize.Int32 && d is >= 0xD0 and <= 0xF0)
                    compares[d] = compares.GetValueOrDefault(d) + 1;
                else if (ins.Mnemonic == Mnemonic.Movzx && ins.Op1Kind == OpKind.Memory && d is >= 0x120 and <= 0x138)
                {
                    var into = ins.MemorySize is MemorySize.UInt16 or MemorySize.Int16 ? words : bytes;
                    into[d] = into.GetValueOrDefault(d) + 1;
                }
                else if (ins.Mnemonic == Mnemonic.Test && ins.Op0Kind == OpKind.Memory && ins.MemorySize is MemorySize.UInt8 or MemorySize.Int8 &&
                         ins.Op1Kind is OpKind.Immediate8 && d is >= 0x120 and <= 0x138)
                    tests[(d, ins.Immediate8)] = tests.GetValueOrDefault((d, (long)ins.Immediate8)) + 1;
            }
        }
        Console.WriteLine("cmp dword [reg+d], x:   " + string.Join(", ", compares.Select(kv => $"0x{kv.Key:X}: {kv.Value}")));
        Console.WriteLine("movzx r, word [reg+d]:  " + string.Join(", ", words.Select(kv => $"0x{kv.Key:X}: {kv.Value}")));
        Console.WriteLine("movzx r, byte [reg+d]:  " + string.Join(", ", bytes.Select(kv => $"0x{kv.Key:X}: {kv.Value}")));
        Console.WriteLine("test byte [reg+d], imm: " + string.Join(", ", tests.Select(kv => $"0x{kv.Key.Item1:X}&0x{kv.Key.Item2:X}: {kv.Value}")));
        return 0;
    }
}
