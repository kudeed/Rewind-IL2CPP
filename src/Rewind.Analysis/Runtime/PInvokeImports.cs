using System.Text;
using Iced.Intel;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// What a P/Invoke declaration imports, as IL2CPP's generated wrapper spells it out: the library and entry point
/// (the metadata does not keep them), the calling convention and character set, and the static where the resolved
/// function pointer is cached - the same static is used wherever the wrapper was inlined, which is how a call
/// through it is recognized as a call of the declaration.
/// </summary>
public sealed record PInvokeImport(MethodDef Method, string Module, string EntryPoint, int CallingConvention, int CharSet,
    bool NoMangle, bool SetLastError, ulong CacheSlot)
{
    /// <summary>Il2CppCharSet: CHARSET_ANSI, CHARSET_UNICODE, CHARSET_NOT_SPECIFIED.</summary>
    public const int CharSetAnsi = 0, CharSetUnicode = 1;
}

public static class PInvokeImports
{
    /// <summary>Reads every P/Invoke declaration's wrapper. Declarations whose wrapper does not have the expected shape are left out.</summary>
    public static List<PInvokeImport> Scan(Il2CppModel model, RuntimeHelpers helpers)
    {
        var resolvers = new HashSet<ulong>(helpers.AddressesOf(HelperKind.ResolvePInvoke));
        var lastError = new HashSet<ulong>(helpers.AddressesOf(HelperKind.StoreLastError));
        var result = new List<PInvokeImport>();
        if (resolvers.Count == 0) return result;
        foreach (MethodDef method in model.Methods)
        {
            if ((method.Flags & MethodDef.PInvokeImpl) == 0 || method.Address == 0) continue;
            if (Read(model.Image, method, resolvers, lastError) is { } import) result.Add(import);
        }
        return result;
    }

    private readonly record struct Value(bool StackRelative, long Number);

    private static PInvokeImport? Read(NativeImage image, MethodDef method, HashSet<ulong> resolvers, HashSet<ulong> lastError)
    {
        ReadOnlySpan<byte> span = image.SpanToSectionEnd(method.Address);
        if (span.Length == 0) return null;
        var decoder = Iced.Intel.Decoder.Create(64, new ByteArrayCodeReader(span[..Math.Min(span.Length, 4096)].ToArray()), method.Address);
        var registers = new Dictionary<Register, Value>();
        var memory = new Dictionary<long, long>();   // stack offset (from the entry stack pointer) -> stored value
        Dictionary<long, long>? described = null;    // the same, as it was at the call of the resolver
        long depth = 0;                              // stack pointer relative to entry
        long? arguments = null;
        ulong slot = 0;
        bool setLastError = false, called = false;

        long? StackAddress(in Instruction ins)
        {
            if (ins.MemoryIndex != Register.None) return null;
            if (ins.MemoryBase == Register.RSP) return depth + (long)ins.MemoryDisplacement64;
            if (registers.TryGetValue(ins.MemoryBase, out Value b) && b.StackRelative) return b.Number + (long)ins.MemoryDisplacement64;
            return null;
        }

        for (int i = 0; i < 400; i++)
        {
            decoder.Decode(out Instruction ins);
            // A wrapper whose last act is the native call leaves by a jump through the resolved pointer, not by a
            // ret: what follows is the next function.
            if (ins.IsInvalid || ins.FlowControl is FlowControl.Return or FlowControl.IndirectBranch) break;
            Register dest = ins.OpCount > 0 && ins.Op0Kind == OpKind.Register ? ins.Op0Register.GetFullRegister() : Register.None;
            switch (ins.Mnemonic)
            {
                case Mnemonic.Mov when dest != Register.None && ins.Op1Kind == OpKind.Register && ins.Op1Register == Register.RSP:
                    registers[dest] = new Value(true, depth);
                    continue;
                case Mnemonic.Push:
                    depth -= 8;
                    continue;
                case Mnemonic.Sub when dest == Register.RSP && ins.Op1Kind != OpKind.Register:
                    depth -= (long)ins.GetImmediate(1);
                    continue;
                case Mnemonic.Add when dest == Register.RSP && ins.Op1Kind != OpKind.Register:
                    depth += (long)ins.GetImmediate(1);
                    continue;
                case Mnemonic.Lea when dest != Register.None:
                    if (ins.IsIPRelativeMemoryOperand) registers[dest] = new Value(false, (long)ins.IPRelativeMemoryAddress);
                    else if (StackAddress(ins) is long at) registers[dest] = new Value(true, at);
                    else registers.Remove(dest);
                    continue;
                case Mnemonic.Mov when dest != Register.None && ins.Op1Kind is OpKind.Immediate32 or OpKind.Immediate64 or OpKind.Immediate32to64:
                    registers[dest] = new Value(false, (long)ins.GetImmediate(1));
                    continue;
                case Mnemonic.Mov when ins.Op0Kind == OpKind.Memory && StackAddress(ins) is long to:
                    if (ins.Op1Kind is OpKind.Immediate8 or OpKind.Immediate16 or OpKind.Immediate32 or OpKind.Immediate32to64)
                        memory[to] = (long)ins.GetImmediate(1);
                    else if (ins.Op1Kind == OpKind.Register && registers.TryGetValue(ins.Op1Register.GetFullRegister(), out Value v) && !v.StackRelative)
                        memory[to] = v.Number;
                    else memory.Remove(to);
                    continue;
                case Mnemonic.Mov when ins.IsIPRelativeMemoryOperand && ins.Op0Kind == OpKind.Memory && ins.Op1Register == Register.RAX && arguments != null && slot == 0:
                    slot = ins.IPRelativeMemoryAddress;
                    continue;
                case Mnemonic.Call when ins.Op0Kind is OpKind.NearBranch64:
                    if (arguments == null && resolvers.Contains(ins.NearBranchTarget) && registers.TryGetValue(Register.RCX, out Value args) && args.StackRelative)
                    {
                        // Only the first one, with the stack as it is now: later code (were the end of the
                        // wrapper missed, another wrapper's) writes over the same slots.
                        arguments = args.Number;
                        described = new Dictionary<long, long>(memory);
                    }
                    else if (lastError.Contains(ins.NearBranchTarget) && called) setLastError = true;
                    registers.Clear();
                    continue;
                case Mnemonic.Call:
                    called = arguments != null; // the call through the resolved pointer
                    registers.Clear();
                    continue;
            }
            if (dest != Register.None) registers.Remove(dest);
        }
        if (arguments is not long p || slot == 0 || described == null) return null;
        memory = described;
        // PInvokeArguments: StringView<Il2CppNativeChar> moduleName { str, length }, StringView<char> entryPoint,
        // callingConvention, charSet, parameterSize, isNoMangle.
        if (!memory.TryGetValue(p, out long moduleAt) || !memory.TryGetValue(p + 8, out long moduleLength) ||
            !memory.TryGetValue(p + 16, out long entryAt) || !memory.TryGetValue(p + 24, out long entryLength)) return null;
        if (moduleLength is <= 0 or > 260 || entryLength is <= 0 or > 1024) return null;
        string? module = ReadString(image, (ulong)moduleAt, (int)moduleLength, allowWide: true);
        string? entry = ReadString(image, (ulong)entryAt, (int)entryLength, allowWide: false);
        if (module == null || entry == null) return null;
        int convention = (int)memory.GetValueOrDefault(p + 32);
        int charSet = (int)memory.GetValueOrDefault(p + 36, PInvokeImport.CharSetAnsi);
        bool noMangle = memory.GetValueOrDefault(p + 44) != 0;
        return new PInvokeImport(method, module, entry, convention, charSet, noMangle, setLastError, slot);
    }

    private static string? ReadString(NativeImage image, ulong at, int length, bool allowWide)
    {
        ReadOnlySpan<byte> bytes = image.SpanToSectionEnd(at);
        if (bytes.Length < length) return null;
        // Native strings are UTF-16 on Windows: every other byte of an ASCII name is zero.
        if (allowWide && bytes.Length >= 2 * length && bytes[1] == 0 && (length < 2 || bytes[3] == 0))
            return Encoding.Unicode.GetString(bytes[..(2 * length)]);
        string text = Encoding.UTF8.GetString(bytes[..length]);
        return text.All(c => c >= ' ' && c < 0x7F) ? text : null;
    }
}
