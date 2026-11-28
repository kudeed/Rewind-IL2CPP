using Rewind.Analysis.Abi;
using Rewind.Analysis.Arm64;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// An outlined AArch64 cleanup: call one exact managed method on frame[1], then read frame[0]
/// and rethrow that exception if it is non-null. This is a description of the native body,
/// not permission to replace any caller: its frame lifetime and exception edge need their own proof.
/// </summary>
public sealed record OutlinedCleanup(ulong Address, ulong CleanupTarget, ulong MethodInfoSlot,
    MethodInst Method, TypeSig ReceiverType, int ReceiverSize, ulong RethrowTarget)
{
    public const int FrameSize = 16;

    /// <summary>
    /// Only the complete, bounded twelve-instruction form is accepted. No method names, game addresses,
    /// matching RET bodies, adjustor thunks or inferred generic instantiation addresses are evidence here.
    /// </summary>
    public static OutlinedCleanup? Recognize(ProgramAnalysis program, ulong address)
    {
        NativeImage image = program.Model.Image;
        if (image is not ElfImage elf || image.Arch != CpuArch.Arm64 || image.PointerSize != 8 ||
            program.Abi.Regs.SharedPositions || !image.IsCodeAddress(address) ||
            program.RangeOf(address) is not { } range || range.Start != address || range.Chained ||
            range.End <= address || range.End - address != 48 ||
            !image.TrySpan(address, 48, out _) || !image.IsCodeAddress(range.End - 1) ||
            program.Model.MethodsByAddress.ContainsKey(address) || program.Model.InstsByAddress.ContainsKey(address) ||
            program.Helpers.At(address) != null || elf.ExceptionTableOf(address) != null) return null;

        var code = new A64Instruction[12];
        for (int i = 0; i < code.Length; i++) code[i] = A64Decoder.Decode(image.U32(address + 4UL * (ulong)i), address + 4UL * (ulong)i);
        byte saved = code[0].Ra, temporary = code[1].Rd;
        if (saved is < 19 or > 28 || temporary is < 8 or > 17) return null;
        static bool Memory(in A64Instruction i, A64Op op, byte to, byte from, long offset,
            A64Mode mode = A64Mode.Offset) => i.Op == op && i.Rd == to && i.Rn == from &&
                i.Imm == offset && i.Mode == mode && i.Size == 8 && !i.Vector && !i.Signed;
        if (!Memory(code[0], A64Op.Stp, 30, A64Instruction.Sp, -16, A64Mode.PreIndex) || code[0].Ra != saved ||
            code[1].Op != A64Op.Adrp || !code[1].Is64 ||
            code[2].Op != A64Op.Orr || !code[2].Is64 || code[2].SetFlags || code[2].Rd != saved ||
            code[2].Rn != A64Instruction.Zr || code[2].Rm != 0 || code[2].Amount != 0 || code[2].Shift != A64Shift.Lsl ||
            !Memory(code[3], A64Op.Ldr, temporary, temporary, code[3].Imm) || code[3].Imm < 0 ||
            !Memory(code[4], A64Op.Ldr, 0, 0, 8) ||
            !Memory(code[5], A64Op.Ldr, 1, temporary, 0) ||
            code[6].Op != A64Op.Bl ||
            !Memory(code[7], A64Op.Ldr, 0, saved, 0) ||
            code[8].Op != A64Op.Cbnz || !code[8].Is64 || code[8].Rd != 0 || code[8].Target != address + 44 ||
            !Memory(code[9], A64Op.Ldp, 30, A64Instruction.Sp, 16, A64Mode.PostIndex) || code[9].Ra != saved ||
            code[10].Op != A64Op.Ret || code[10].Rn != 30 || code[10].Word != 0xD65F03C0 ||
            code[11].Op != A64Op.Bl) return null;

        ulong got = code[1].Target + (ulong)code[3].Imm;
        if (got < code[1].Target || got > ulong.MaxValue - 7 || got % 8 != 0 || !image.IsDataAddress(got) ||
            !image.IsReadOnlyAfterLoad(got) || !image.IsReadOnlyAfterLoad(got + 7) || !image.TryPtr(got, out ulong slot) || slot % 8 != 0 ||
            !image.IsDataAddress(slot) || program.Model.ResolveUsageSlot(slot) is not
                { Kind: UsageKind.MethodRef, MethodInst: { } specific }) return null;

        MethodDef method = specific.Method;
        if (method.IsStatic || !method.ReturnType.IsVoid || method.Parameters.Length != 0 ||
            !method.DeclaringType.IsValueType || method.DeclaringType.IsEnum ||
            specific.ClassArguments.Length != method.DeclaringType.GenericParameters.Length ||
            specific.MethodArguments.Length != method.GenericParameters.Length ||
            specific.ClassArguments.Any(t => t.ContainsGenericParameter) ||
            specific.MethodArguments.Any(t => t.ContainsGenericParameter) ||
            !HasCompatibleBody(program, code[6].Target, specific)) return null;

        MethodAbi abi = program.Abi.For(specific);
        if (!PlainInstanceAbi(abi) || abi.This!.Type is not { } receiver || receiver.ContainsGenericParameter) return null;
        var layout = program.Layouts.SizeOf(receiver);
        if (!layout.Known || layout.Size <= 0 || layout.Size > 0x100000) return null;
        if (program.Helpers.At(code[11].Target) is not
            { Kind: HelperKind.Rethrow, IntArgs: 1, NoReturn: true, ReturnsValue: false, FloatArgs: 0 }) return null;

        return new OutlinedCleanup(address, code[6].Target, slot, specific, receiver, layout.Size, code[11].Target);
    }

    internal static bool HasRegisteredBody(Il2CppModel model, ulong address, MethodDef method)
    {
        if (address == 0 || !model.Image.IsCodeAddress(address)) return false;
        return model.MethodsByAddress.TryGetValue(address, out var definitions) && definitions.Any(m => m.Address == address && ReferenceEquals(m, method)) ||
               model.InstsByAddress.TryGetValue(address, out var instances) && instances.Any(i => i.Address == address && ReferenceEquals(i.Method, method));
    }

    /// <summary>
    /// Supplying a specific MethodInfo proves context, but cannot make an unrelated value-type
    /// specialization into the right body. Only exact arguments or closed reference sharing are accepted.
    /// </summary>
    internal static bool HasCompatibleBody(ProgramAnalysis program, ulong address, MethodInst specific)
    {
        if (!HasRegisteredBody(program.Model, address, specific.Method)) return false;
        MethodAbi wanted = program.Abi.For(specific);
        if (!wanted.Known || specific.ClassArguments.Length != specific.Method.DeclaringType.GenericParameters.Length ||
            specific.MethodArguments.Length != specific.Method.GenericParameters.Length ||
            specific.ClassArguments.Any(t => !ClosedArgument(t, 0)) || specific.MethodArguments.Any(t => !ClosedArgument(t, 0))) return false;
        if (specific.ClassArguments.Length == 0 && specific.MethodArguments.Length == 0 &&
            program.Model.MethodsByAddress.TryGetValue(address, out var definitions) &&
            definitions.Any(m => m.Address == address && ReferenceEquals(m, specific.Method) && SameAbi(program, wanted, program.Abi.For(m, [], [])))) return true;
        return program.Model.InstsByAddress.TryGetValue(address, out var instances) && instances.Any(i =>
            i.Address == address && ReferenceEquals(i.Method, specific.Method) && SharedArguments(specific.ClassArguments, i.ClassArguments) &&
            SharedArguments(specific.MethodArguments, i.MethodArguments) && SameAbi(program, wanted, program.Abi.For(i)));
    }

    private static bool SharedArguments(TypeSig[] specific, TypeSig[] body)
    {
        if (specific.Length != body.Length) return false;
        for (int i = 0; i < specific.Length; i++)
            if (!ClosedArgument(specific[i], 0) || !ClosedArgument(body[i], 0) ||
                specific[i].Key != body[i].Key && !(ClosedReference(specific[i]) && ClosedReference(body[i]))) return false;
        return true;
    }

    private static bool ClosedArgument(TypeSig type, int depth) => depth < 16 && (type switch
    {
        PrimitiveSig p => p.Element is not (Il2CppTypeEnum.Void or Il2CppTypeEnum.TypedByRef),
        TypeDefSig t => t.Definition.GenericParameters.Length == 0,
        GenericInstSig g => g.Arguments.Length == g.Definition.GenericParameters.Length && g.Arguments.All(a => ClosedArgument(a, depth + 1)),
        SzArraySig a => ClosedArgument(a.ElementType, depth + 1),
        ArraySig a => ClosedArgument(a.ElementType, depth + 1),
        _ => false,
    });

    private static bool ClosedReference(TypeSig type) => ClosedArgument(type, 0) && (type switch
    {
        PrimitiveSig p => p.Element is Il2CppTypeEnum.Object or Il2CppTypeEnum.String,
        TypeDefSig or GenericInstSig => type.Definition is { IsValueType: false },
        SzArraySig or ArraySig => true,
        _ => false,
    });

    private static bool SameAbi(ProgramAnalysis program, MethodAbi a, MethodAbi b)
    {
        if (!a.Known || !b.Known || a.Return != b.Return || a.ReturnSize != b.ReturnSize ||
            a.ReturnCount != b.ReturnCount || a.ReturnIsDouble != b.ReturnIsDouble || a.Params.Count != b.Params.Count ||
            !SameValueLayout(program, a.ReturnType, b.ReturnType)) return false;
        for (int i = 0; i < a.Params.Count; i++)
        {
            AbiParam x = a.Params[i], y = b.Params[i];
            if (x.Role != y.Role || x.Position != y.Position || x.Pass != y.Pass || x.Size != y.Size || x.Count != y.Count ||
                x.IsDouble != y.IsDouble || !SameValueLayout(program, x.Type, y.Type)) return false;
        }
        return true;
    }

    private static bool SameValueLayout(ProgramAnalysis program, TypeSig? a, TypeSig? b)
    {
        if (a?.Key == b?.Key) return true;
        if (a?.Definition is not { IsValueType: true } && b?.Definition is not { IsValueType: true }) return true;
        if (a == null || b == null || a.Definition is not { IsValueType: true } || b.Definition is not { IsValueType: true }) return false;
        TypeLayout x = program.Layouts.Of(a), y = program.Layouts.Of(b);
        return x.Known && y.Known && x.Size == y.Size && x.Align == y.Align && x.Fields.Length == y.Fields.Length &&
            x.Fields.Zip(y.Fields).All(pair => ReferenceEquals(pair.First.Field, pair.Second.Field) &&
                pair.First.Offset == pair.Second.Offset && pair.First.Size == pair.Second.Size);
    }

    private static bool PlainInstanceAbi(MethodAbi abi) => abi.Known && abi.Return == ReturnKind.Void &&
        abi.Params.Count == 2 && abi.Params[0] is { Role: ParamRole.This, Position: 0, Pass: PassKind.Integer, Size: 8, Count: 1 } &&
        abi.Params[1] is { Role: ParamRole.MethodInfo, Position: 1, Pass: PassKind.Integer, Size: 8, Count: 1 };
}
