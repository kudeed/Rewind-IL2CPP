// Added by xob0t (2026): helpers behind widening wrappers, array accessors by shape.
using Iced.Intel;
using Rewind.Analysis.Arm64;
using Rewind.Binary;
using Rewind.Model;
using Decoder = Iced.Intel.Decoder;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// Finds runtime support functions whose own few instructions say what they are, where no signature library
/// recognized them.
/// </summary>
public static class HelperShapes
{
    private static readonly bool NoWidened = Environment.GetEnvironmentVariable("REWIND_NO_WIDENED_HELPERS") != null;

    /// <summary>Adds what the code shows to <paramref name="helpers"/>; returns a line for the log, or null.</summary>
    public static string? Identify(Il2CppModel model, ModelCodeContext context, CodeIndex code, RuntimeHelpers helpers)
    {
        if (model.Image.Arch is not (CpuArch.X64 or CpuArch.Arm64)) return null;
        var found = new List<string>();
        if (model.Image.Arch == CpuArch.Arm64)
        {
            if (!NoArm64Thunks && AddArm64Thunks(model, context, helpers) is > 0 and var thunks)
                found.Add($"{thunks} thunks of support functions");
            if (!NoArm64Exceptions && AddArm64ExceptionStubs(model, context, helpers) is > 0 and var exceptions)
                found.Add($"{exceptions} exception throwers");
            return found.Count == 0 ? null : "shapes:   found by their code: " + string.Join("; ", found);
        }
        if (!NoWidened && AddWidenedTargets(model, context, code, helpers) is > 0 and var widened)
            found.Add($"{widened} called through a function that only widens arguments");
        if (!NoAccessors && AddArrayAccessors(model, context, code, helpers) is { Count: > 0 } accessors)
            found.Add($"{accessors.Count} array element accessors (" + string.Join(", ", accessors.Take(8).Select(a => $"0x{a:X}")) + (accessors.Count > 8 ? ", ...)" : ")"));
        return found.Count == 0 ? null : "shapes:   found by their code: " + string.Join("; ", found);
    }

    private static readonly bool NoAccessors = Environment.GetEnvironmentVariable("REWIND_NO_ACCESSOR_SHAPES") != null;
    private static readonly bool NoArm64Thunks = Environment.GetEnvironmentVariable("REWIND_NO_ARM64_THUNKS") != null;

    /// <summary>
    /// The compiler leaves small functions that do nothing but hand their arguments to a support function: a
    /// bare branch, a branch after setting a flag the generated code passes, or a call whose result is dropped
    /// before returning. They are the same helper; the signature library only has room for a few of them.
    /// </summary>
    private static int AddArm64Thunks(Il2CppModel model, ModelCodeContext context, RuntimeHelpers helpers)
    {
        int added = 0;
        for (int pass = 0; pass < 4; pass++)
        {
            int before = added;
            foreach (ulong start in context.FunctionStarts)
            {
                if (context.IsManaged(start) || helpers.At(start) != null) continue;
                if (Arm64Stub(model, start) is not { } stub || helpers.At(stub.Target) is not { } info) continue;
                HelperInfo? alias = stub.Kind switch
                {
                    // A branch is the helper itself.
                    Arm64StubKind.Branch => info,
                    // "mov w1, #1; b initializer": a flag the initializer's managed meaning does not have.
                    Arm64StubKind.FlagBranch when info.Kind == HelperKind.MetadataInitInline => info,
                    // "bl initializer; dmb; ret": the initializer whose result is not used.
                    Arm64StubKind.CallBarrierReturn when info.Kind == HelperKind.MetadataInitInline =>
                        info with { Kind = HelperKind.MetadataInit, NoReturn = false, ReturnsValue = false },
                    _ => null,
                };
                if (alias == null) continue;
                helpers.Add(start, alias with { Name = info.Name + " (thunk)" });
                added++;
            }
            if (added == before) break;
        }
        return added;
    }

    private static readonly bool NoArm64Exceptions = Environment.GetEnvironmentVariable("REWIND_NO_ARM64_EXCEPTIONS") != null;

    /// <summary>
    /// An out-of-line throw: the runtime keeps a function per exception and message ("Arithmetic operation
    /// resulted in an overflow."), which builds the exception and jumps to the raiser. The message says which.
    /// </summary>
    private static int AddArm64ExceptionStubs(Il2CppModel model, ModelCodeContext context, RuntimeHelpers helpers)
    {
        int added = 0;
        foreach (ulong start in context.FunctionStarts)
        {
            if (context.IsManaged(start) || helpers.At(start) != null) continue;
            if (Arm64ExceptionStub(model, start) is not { } info) continue;
            helpers.Add(start, info);
            added++;
        }
        return added;
    }

    private static HelperInfo? Arm64ExceptionStub(Il2CppModel model, ulong start)
    {
        ReadOnlySpan<byte> bytes = model.Image.SpanToSectionEnd(start);
        if (bytes.Length < 20) return null;
        ulong page = 0, text = 0;
        bool call = false, tail = false;
        for (int i = 0; i < 8 && (i + 1) * 4 <= bytes.Length; i++)
        {
            A64Instruction ins = A64Decoder.Decode(BitConverter.ToUInt32(bytes[(i * 4)..]), start + (ulong)(i * 4));
            if (ins.Op == A64Op.Adrp) page = ins.Target;
            else if (ins.Op == A64Op.AddImm && ins.Rn == ins.Rd && page != 0) text = page + (ulong)ins.Imm;
            else if (ins.Op == A64Op.Bl) call = true;
            else if (ins.Op == A64Op.B && i != 0) { tail = true; break; }
        }
        if (!call || !tail || text == 0 || model.Image.TryCString(text, 200) is not { Length: > 10 } message) return null;
        HelperKind kind;
        if (message.Contains("overflow", StringComparison.OrdinalIgnoreCase)) kind = HelperKind.GetOverflowException;
        else if (message.Contains("Object reference not set", StringComparison.Ordinal)) kind = HelperKind.ThrowNullReference;
        else if (message.Contains("outside the bounds", StringComparison.Ordinal)) kind = HelperKind.ThrowIndexOutOfRange;
        else if (message.Contains("divide by zero", StringComparison.OrdinalIgnoreCase)) kind = HelperKind.ThrowDivideByZero;
        else if (message.Contains("cast is not valid", StringComparison.OrdinalIgnoreCase)) kind = HelperKind.ThrowInvalidCast;
        else return null;
        // (The overflow helper is otherwise the one that makes the exception; this one raises it.)
        return new HelperInfo(kind, 0, true, false, "exception thrower (by its code)");
    }

    private enum Arm64StubKind { Branch, FlagBranch, CallBarrierReturn }

    private static (Arm64StubKind Kind, ulong Target)? Arm64Stub(Il2CppModel model, ulong start)
    {
        ReadOnlySpan<byte> bytes = model.Image.SpanToSectionEnd(start);
        if (bytes.Length < 8) return null;
        A64Instruction first = A64Decoder.Decode(BitConverter.ToUInt32(bytes), start);
        if (first.Op == A64Op.B && first.Target != start) return (Arm64StubKind.Branch, first.Target);
        if (first.Op == A64Op.MovZ && first.Rd >= 1 && first.Rd <= 7)
        {
            A64Instruction second = A64Decoder.Decode(BitConverter.ToUInt32(bytes[4..]), start + 4);
            if (second.Op == A64Op.B && second.Target != start) return (Arm64StubKind.FlagBranch, second.Target);
            return null;
        }
        if (first.Op != A64Op.Bl) return null;
        A64Instruction next = A64Decoder.Decode(BitConverter.ToUInt32(bytes[4..]), start + 4);
        if (next.Op == A64Op.Barrier)
        {
            if (bytes.Length < 12) return null;
            A64Instruction last = A64Decoder.Decode(BitConverter.ToUInt32(bytes[8..]), start + 8);
            if (last.Op == A64Op.Ret) return (Arm64StubKind.CallBarrierReturn, first.Target);
            return null;
        }
        // "bl helper; ret": the result is returned as it is.
        if (next.Op == A64Op.Ret) return (Arm64StubKind.Branch, first.Target);
        return null;
    }

    /// <summary>
    /// An array type's own element accessors (GetAt, SetAt, GetAddressAt), which the compiler keeps as functions
    /// of their own, one per element type: the library has those of the types its builds used. Each is the
    /// bounds check and one access, and nothing else: "cmp edx, [rcx+max_length]; jae throw; one load, store or
    /// lea of [rcx+rdx*size+elements] from or into the argument or result register; ret", the throw being a call
    /// to the identified index-out-of-range thrower. Only accessors of values in one register come out this way
    /// (references go through a write barrier, structs are copied), which is what the translation takes.
    /// </summary>
    private static List<ulong> AddArrayAccessors(Il2CppModel model, ModelCodeContext context, CodeIndex code, RuntimeHelpers helpers)
    {
        var added = new List<ulong>();
        if (!helpers.ByAddress.Values.Any(i => i.Kind == HelperKind.ThrowIndexOutOfRange)) return added;
        foreach (ulong start in context.FunctionStarts)
        {
            if (context.IsManaged(start) || helpers.At(start) != null || ArrayAccessor(model, code, helpers, start) is not { } kind) continue;
            string name = kind switch { HelperKind.ArrayGetAt => "GetAt", HelperKind.ArraySetAt => "SetAt", _ => "GetAddressAt" };
            helpers.Add(start, kind == HelperKind.ArraySetAt
                ? new HelperInfo(kind, 3, false, false, name + " (by its code)")
                : new HelperInfo(kind, 2, false, true, name + " (by its code)"));
            added.Add(start);
        }
        return added;
    }

    private const int ArrayLengthOffset = 0x18, ArrayElementsOffset = 0x20;

    private static HelperKind? ArrayAccessor(Il2CppModel model, CodeIndex code, RuntimeHelpers helpers, ulong start)
    {
        List<Instruction> body = Decode(model, start, 8);
        int i = 0;
        int frame = 0;
        if (i < body.Count && body[i] is { Mnemonic: Mnemonic.Sub, Op0Register: Register.RSP, Op1Kind: OpKind.Immediate8to64 or OpKind.Immediate32to64 } sub)
        {
            frame = (int)sub.GetImmediate(1);
            i++;
        }
        // The bounds check.
        if (i + 1 >= body.Count || body[i] is not { Mnemonic: Mnemonic.Cmp, Op0Kind: OpKind.Register, Op1Kind: OpKind.Memory } check ||
            check.Op0Register is not (Register.EDX or Register.RDX) || check.MemoryBase != Register.RCX || check.MemoryIndex != Register.None ||
            check.MemoryDisplacement64 != ArrayLengthOffset)
            return null;
        if (body[i + 1] is not { Mnemonic: Mnemonic.Jae, Op0Kind: OpKind.NearBranch64 } jump || !Throws(model, code, helpers, jump.NearBranchTarget)) return null;
        i += 2;
        // The access.
        if (i >= body.Count) return null;
        Instruction access = body[i++];
        HelperKind kind;
        bool element(int operand) =>
            access.GetOpKind(operand) == OpKind.Memory && access.MemoryBase == Register.RCX && access.MemoryIndex == Register.RDX &&
            access.MemoryDisplacement64 == ArrayElementsOffset && access.MemorySegment == Register.DS;
        if (access.Mnemonic == Mnemonic.Lea && access.Op0Register == Register.RAX && element(1)) kind = HelperKind.ArrayGetAddressAt;
        else if (access.Mnemonic is Mnemonic.Mov or Mnemonic.Movss or Mnemonic.Movsd && element(0) && access.Op1Kind == OpKind.Register &&
                 access.Op1Register.GetFullRegister() is Register.R8 or Register.ZMM2)
            kind = HelperKind.ArraySetAt;
        else if (access.Mnemonic is Mnemonic.Mov or Mnemonic.Movzx or Mnemonic.Movsx or Mnemonic.Movss or Mnemonic.Movsd && element(1) &&
                 access.Op0Kind == OpKind.Register && access.Op0Register.GetFullRegister() is Register.RAX or Register.ZMM0)
            kind = HelperKind.ArrayGetAt;
        else return null;
        // Nothing else before the return.
        if (frame != 0)
        {
            if (i >= body.Count || body[i] is not { Mnemonic: Mnemonic.Add, Op0Register: Register.RSP } add || (int)add.GetImmediate(1) != frame) return null;
            i++;
        }
        return i < body.Count && body[i].Mnemonic == Mnemonic.Ret && body[i].OpCount == 0 ? kind : null;
    }

    /// <summary>Whether the code at the address calls or jumps to the index-out-of-range thrower first thing.</summary>
    private static bool Throws(Il2CppModel model, CodeIndex code, RuntimeHelpers helpers, ulong at)
    {
        List<Instruction> body = Decode(model, at, 1);
        return body.Count == 1 && body[0].Mnemonic is Mnemonic.Call or Mnemonic.Jmp && body[0].Op0Kind == OpKind.NearBranch64 &&
               (helpers.KindAt(body[0].NearBranchTarget) == HelperKind.ThrowIndexOutOfRange ||
                helpers.KindAt(code.ThunkTarget(body[0].NearBranchTarget)) == HelperKind.ThrowIndexOutOfRange);
    }

    private static List<Instruction> Decode(Il2CppModel model, ulong start, int count)
    {
        var list = new List<Instruction>();
        ReadOnlySpan<byte> bytes = model.Image.SpanToSectionEnd(start);
        if (bytes.Length == 0) return list;
        var decoder = Decoder.Create(64, new ByteArrayCodeReader(bytes[..Math.Min(bytes.Length, count * 15)].ToArray()), start);
        while (list.Count < count)
        {
            decoder.Decode(out Instruction ins);
            if (ins.IsInvalid) break;
            list.Add(ins);
            if (ins.FlowControl is FlowControl.Return or FlowControl.UnconditionalBranch) break;
        }
        return list;
    }

    /// <summary>
    /// A support function can be a wrapper that does nothing but widen its 32-bit arguments to 64 bits and jump to
    /// the function that does the work: SZArrayNew(klass, uint32 length) is "mov edx, edx; jmp Array::NewSpecific".
    /// The library recognizes the wrapper, but code built with whole-program optimization mostly calls the function
    /// behind it, passing the length already widened. That function does what the wrapper does, for every argument
    /// the wrapper can pass on, and is the same helper. (Not where something else is known to be there, nor a
    /// compiled method, nor where the wrapper does anything but widen a register into itself.)
    /// </summary>
    private static int AddWidenedTargets(Il2CppModel model, ModelCodeContext context, CodeIndex code, RuntimeHelpers helpers)
    {
        int added = 0;
        foreach (var (address, info) in helpers.ByAddress.ToList())
        {
            if (info.Kind == HelperKind.None || WidenedJumpTarget(model, address) is not { } next) continue;
            ulong target = code.ThunkTarget(next);
            foreach (ulong at in new[] { next, target }.Distinct())
            {
                if (at == address || context.IsManaged(at) || helpers.At(at) != null) continue;
                helpers.Add(at, info with { Name = info.Name + " (the function it widens its arguments for)" });
                added++;
            }
        }
        return added;
    }

    /// <summary>Where the function jumps when all it does before is "mov r32, r32" of an argument register into itself.</summary>
    private static ulong? WidenedJumpTarget(Il2CppModel model, ulong start)
    {
        ReadOnlySpan<byte> bytes = model.Image.SpanToSectionEnd(start);
        if (bytes.Length == 0) return null;
        var decoder = Decoder.Create(64, new ByteArrayCodeReader(bytes[..Math.Min(bytes.Length, 64)].ToArray()), start);
        bool widens = false;
        for (int i = 0; i < 5; i++)
        {
            decoder.Decode(out Instruction ins);
            if (ins.IsInvalid) return null;
            if (ins.Mnemonic == Mnemonic.Jmp && ins.Op0Kind == OpKind.NearBranch64)
                return widens ? ins.NearBranchTarget : null;
            if (ins.Mnemonic != Mnemonic.Mov || ins.Op0Kind != OpKind.Register || ins.Op1Kind != OpKind.Register ||
                ins.Op0Register != ins.Op1Register || ins.Op0Register is not (Register.ECX or Register.EDX or Register.R8D or Register.R9D))
                return null;
            widens = true;
        }
        return null;
    }
}
