using Rewind.Analysis.Ir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Abi;

public enum ParamRole
{
    /// <summary>Hidden pointer to the caller's buffer for a struct return value.</summary>
    ReturnBuffer,
    This,
    Argument,
    /// <summary>The trailing MethodInfo* every IL2CPP method receives.</summary>
    MethodInfo,
}

public enum PassKind
{
    /// <summary>Integer register (or stack slot) holding the value itself: integers, references, small structs.</summary>
    Integer,
    /// <summary>Float register holding a float or double.</summary>
    Float,
    /// <summary>Integer register (or stack slot) holding a pointer to a caller-made copy of a struct.</summary>
    Indirect,
    /// <summary>AArch64: a struct of 9-16 bytes in two consecutive integer registers (or two stack slots).</summary>
    IntegerPair,
    /// <summary>
    /// AArch64: a struct of one to four floats or doubles (a homogeneous floating-point aggregate), one member
    /// in each of Count consecutive floating-point registers; IsDouble tells the members' type.
    /// </summary>
    FloatAggregate,
}

/// <summary>
/// StructInRegisterPair (AArch64): a struct of 9-16 bytes in x0 and x1. FloatAggregate (AArch64): a struct of
/// floats or doubles, one member in each of v0-v3.
/// </summary>
public enum ReturnKind { Void, Integer, Float, Double, StructInRegister, Buffer, StructInRegisterPair, FloatAggregate }

/// <summary>One parameter of the native function, in native order. Count: registers taken (pairs and aggregates).</summary>
public sealed record AbiParam(ParamRole Role, int ArgumentIndex, TypeSig? Type, PassKind Pass, int Position, bool IsDouble, int Size, int Count = 1);

/// <summary>How one managed method is called at the machine level.</summary>
public sealed class MethodAbi
{
    public List<AbiParam> Params = [];
    public ReturnKind Return;
    public TypeSig ReturnType = null!;
    public int ReturnSize;
    public bool Known = true;
    /// <summary>The selected native body uses IL2CPP's explicit fully shared return buffer.</summary>
    public bool UsesFullySharedReturnBuffer;

    /// <summary>FloatAggregate returns: how many members, and whether they are doubles.</summary>
    public int ReturnCount = 1;
    public bool ReturnIsDouble;

    public AbiParam? This => Params.FirstOrDefault(p => p.Role == ParamRole.This);
    public AbiParam? ReturnBuffer => Params.FirstOrDefault(p => p.Role == ParamRole.ReturnBuffer);
}

/// <summary>How managed methods are called on one machine (see <see cref="RegisterModel"/> for the positions).</summary>
public abstract class CallingConvention
{
    public abstract RegisterModel Regs { get; }

    /// <summary>
    /// Calling convention of a method, optionally with generic arguments substituted (pass empty arrays for the
    /// open definition).
    /// </summary>
    public abstract MethodAbi For(MethodDef method, TypeSig[] classArgs, TypeSig[] methodArgs);

    public MethodAbi For(MethodInst inst) => For(inst.Method, inst.ClassArguments, inst.MethodArguments);

    /// <summary>The convention for code of this image's machine.</summary>
    public static CallingConvention Of(Il2CppModel model, LayoutCalculator layouts) =>
        model.Image.Arch == Rewind.Binary.CpuArch.Arm64 ? new Aapcs64Abi(model, layouts) : new Win64Abi(model, layouts);
}

/// <summary>
/// The Windows x64 calling convention as it applies to IL2CPP's generated functions:
/// <c>Ret Method([Ret* buffer,] [This* __this,] args..., const MethodInfo* method)</c>.
/// Every parameter takes one slot; slots 0-3 are rcx/rdx/r8/r9 or xmm0-3, the rest go on the stack.
/// </summary>
public sealed class Win64Abi(Il2CppModel model, LayoutCalculator layouts) : CallingConvention
{
    public override RegisterModel Regs => RegisterModel.Win64;

    private readonly Dictionary<(MethodDef, string), MethodAbi> _cache = [];

    public const int RegisterSlots = 4;

    private static bool IsRegisterSized(int size) => size is 1 or 2 or 4 or 8;

    private (PassKind Pass, bool IsDouble, int Size, bool Known) Classify(TypeSig type)
    {
        switch (type)
        {
            case PrimitiveSig p:
                if (p.Element == Il2CppTypeEnum.R4) return (PassKind.Float, false, 4, true);
                if (p.Element == Il2CppTypeEnum.R8) return (PassKind.Float, true, 8, true);
                if (p.Element == Il2CppTypeEnum.TypedByRef) return (PassKind.Indirect, false, 16, true);
                return (PassKind.Integer, false, p.SizeOf(8), true);
            case ByRefSig or PointerSig or SzArraySig or ArraySig:
                return (PassKind.Integer, false, 8, true);
            case GenericParamSig:
                return (PassKind.Integer, false, 8, false);
        }
        TypeDef? def = type.Definition;
        if (def == null) return (PassKind.Integer, false, 8, false);
        if (!def.IsValueType) return (PassKind.Integer, false, 8, true);
        if (def.IsEnum && def.EnumUnderlyingType != null) return Classify(def.EnumUnderlyingType);
        var (size, _, known) = layouts.SizeOf(type);
        return IsRegisterSized(size) ? (PassKind.Integer, false, size, known) : (PassKind.Indirect, false, size, known);
    }

    /// <summary>
    /// Calling convention of a method, optionally with generic arguments substituted (pass empty arrays for the
    /// open definition).
    /// </summary>
    public override MethodAbi For(MethodDef method, TypeSig[] classArgs, TypeSig[] methodArgs)
    {
        string key = classArgs.Length == 0 && methodArgs.Length == 0
            ? ""
            : string.Join(",", classArgs.Select(a => a.Key)) + "|" + string.Join(",", methodArgs.Select(a => a.Key));
        if (_cache.TryGetValue((method, key), out MethodAbi? cached)) return cached;

        var abi = new MethodAbi();
        TypeSig ret = model.Sigs.Substitute(method.ReturnType, classArgs, methodArgs);
        abi.ReturnType = ret;
        int position = 0;

        if (ret.IsVoid) abi.Return = ReturnKind.Void;
        else
        {
            var (pass, isDouble, size, known) = Classify(ret);
            abi.Known &= known;
            abi.ReturnSize = size;
            bool isStruct = ret.Definition is { IsValueType: true, IsEnum: false } && ret is not PrimitiveSig;
            if (pass == PassKind.Float) abi.Return = isDouble ? ReturnKind.Double : ReturnKind.Float;
            else if (pass == PassKind.Indirect)
            {
                abi.Return = ReturnKind.Buffer;
                abi.Params.Add(new AbiParam(ParamRole.ReturnBuffer, -1, ret, PassKind.Integer, position++, false, 8));
            }
            else abi.Return = isStruct ? ReturnKind.StructInRegister : ReturnKind.Integer;
        }

        if (!method.IsStatic)
        {
            TypeSig thisType = method.DeclaringType.Sig;
            if (classArgs.Length != 0 && method.DeclaringType.GenericParameters.Length != 0)
                thisType = model.Sigs.GenericInst(method.DeclaringType, classArgs);
            abi.Params.Add(new AbiParam(ParamRole.This, -1, thisType, PassKind.Integer, position++, false, 8));
        }

        for (int i = 0; i < method.Parameters.Length; i++)
        {
            TypeSig type = model.Sigs.Substitute(method.Parameters[i].Type, classArgs, methodArgs);
            var (pass, isDouble, size, known) = Classify(type);
            abi.Known &= known;
            abi.Params.Add(new AbiParam(ParamRole.Argument, i, type, pass, position++, isDouble, size));
        }

        abi.Params.Add(new AbiParam(ParamRole.MethodInfo, -1, null, PassKind.Integer, position, false, 8));
        _cache[(method, key)] = abi;
        return abi;
    }
}

/// <summary>
/// The AArch64 procedure call standard (AAPCS64, as Android uses it) for IL2CPP's generated functions:
/// integers and pointers in x0-x7, floats and doubles in v0-v7, counted separately; a struct of up to 8 bytes in
/// one integer register and of 9-16 bytes in two; a struct of one to four floats (or doubles) in as many
/// floating-point registers; larger structs by reference to a copy. A struct too large for registers comes back
/// through the buffer x8 points to, which is not one of the argument registers. What does not fit in registers
/// goes on the stack in 8-byte slots, from the entry stack pointer up.
/// </summary>
public sealed class Aapcs64Abi(Il2CppModel model, LayoutCalculator layouts) : CallingConvention
{
    private readonly Dictionary<(MethodDef, string), MethodAbi> _cache = [];

    public override RegisterModel Regs => RegisterModel.Arm64;

    private const int Registers = 8;
    private const int ReturnBufferPosition = 8;

    private enum Class { Integer, Float, Pair, Aggregate, Indirect }

    private (Class Class, bool IsDouble, int Size, int Count, bool Known) Classify(TypeSig type)
    {
        switch (type)
        {
            case PrimitiveSig p:
                if (p.Element == Il2CppTypeEnum.R4) return (Class.Float, false, 4, 1, true);
                if (p.Element == Il2CppTypeEnum.R8) return (Class.Float, true, 8, 1, true);
                if (p.Element == Il2CppTypeEnum.TypedByRef) return (Class.Indirect, false, 16, 1, true);
                return (Class.Integer, false, p.SizeOf(8), 1, true);
            case ByRefSig or PointerSig or SzArraySig or ArraySig:
                return (Class.Integer, false, 8, 1, true);
            case GenericParamSig:
                return (Class.Integer, false, 8, 1, false);
        }
        TypeDef? def = type.Definition;
        if (def == null) return (Class.Integer, false, 8, 1, false);
        if (!def.IsValueType) return (Class.Integer, false, 8, 1, true);
        if (def.IsEnum && def.EnumUnderlyingType != null) return Classify(def.EnumUnderlyingType);
        var (size, _, known) = layouts.SizeOf(type);
        if (Homogeneous(type, 0) is { } hfa && hfa.Count is >= 1 and <= 4) return (Class.Aggregate, hfa.IsDouble, size, hfa.Count, known);
        if (size <= 8) return (Class.Integer, false, size, 1, known);
        if (size <= 16) return (Class.Pair, false, size, 2, known);
        return (Class.Indirect, false, size, 1, known);
    }

    /// <summary>
    /// When every field of the struct (through nested structs) is a float, or every one a double, and the fields
    /// tile it: how many there are. Null otherwise.
    /// </summary>
    private (int Count, bool IsDouble)? Homogeneous(TypeSig type, int depth)
    {
        if (depth > 8) return null;
        if (type is PrimitiveSig p)
            return p.Element switch { Il2CppTypeEnum.R4 => (1, false), Il2CppTypeEnum.R8 => (1, true), _ => null };
        TypeDef? def = type.Definition;
        if (def is not { IsValueType: true } || def.IsEnum) return null;
        TypeLayout layout = layouts.Of(type);
        if (!layout.Known || layout.Fields.Length == 0) return null;
        int count = 0;
        bool? isDouble = null;
        int expected = 0;
        foreach (FieldSlot field in layout.Fields.OrderBy(f => f.Offset))
        {
            if (field.Offset != expected) return null;
            if (Homogeneous(field.Type, depth + 1) is not { } inner) return null;
            if (isDouble != null && isDouble != inner.IsDouble) return null;
            isDouble = inner.IsDouble;
            count += inner.Count;
            expected = field.Offset + field.Size;
            if (count > 4) return null;
        }
        if (isDouble == null || expected != layout.Size) return null;
        return (count, isDouble.Value);
    }

    public override MethodAbi For(MethodDef method, TypeSig[] classArgs, TypeSig[] methodArgs)
    {
        string key = classArgs.Length == 0 && methodArgs.Length == 0
            ? ""
            : string.Join(",", classArgs.Select(a => a.Key)) + "|" + string.Join(",", methodArgs.Select(a => a.Key));
        if (_cache.TryGetValue((method, key), out MethodAbi? cached)) return cached;

        var abi = new MethodAbi();
        TypeSig ret = model.Sigs.Substitute(method.ReturnType, classArgs, methodArgs);
        abi.ReturnType = ret;
        int ngrn = 0, nsrn = 0, nsaa = 0;

        if (ret.IsVoid) abi.Return = ReturnKind.Void;
        else
        {
            var (kind, isDouble, size, count, known) = Classify(ret);
            abi.Known &= known;
            abi.ReturnSize = size;
            bool isStruct = ret.Definition is { IsValueType: true, IsEnum: false } && ret is not PrimitiveSig;
            switch (kind)
            {
                case Class.Float:
                    abi.Return = isDouble ? ReturnKind.Double : ReturnKind.Float;
                    break;
                case Class.Aggregate:
                    abi.Return = ReturnKind.FloatAggregate;
                    abi.ReturnCount = count;
                    abi.ReturnIsDouble = isDouble;
                    break;
                case Class.Pair:
                    abi.Return = ReturnKind.StructInRegisterPair;
                    break;
                case Class.Indirect:
                    abi.Return = ReturnKind.Buffer;
                    abi.Params.Add(new AbiParam(ParamRole.ReturnBuffer, -1, ret, PassKind.Integer, ReturnBufferPosition, false, 8));
                    break;
                default:
                    abi.Return = isStruct ? ReturnKind.StructInRegister : ReturnKind.Integer;
                    break;
            }
        }

        int IntegerPosition(int registers)
        {
            if (ngrn + registers <= Registers)
            {
                int at = ngrn;
                ngrn += registers;
                return at;
            }
            ngrn = Registers;
            int slot = nsaa;
            nsaa += registers;
            return RegisterModel.Arm64.FirstStackPosition + slot;
        }

        if (!method.IsStatic)
        {
            TypeSig thisType = method.DeclaringType.Sig;
            if (classArgs.Length != 0 && method.DeclaringType.GenericParameters.Length != 0)
                thisType = model.Sigs.GenericInst(method.DeclaringType, classArgs);
            abi.Params.Add(new AbiParam(ParamRole.This, -1, thisType, PassKind.Integer, IntegerPosition(1), false, 8));
        }

        for (int i = 0; i < method.Parameters.Length; i++)
        {
            TypeSig type = model.Sigs.Substitute(method.Parameters[i].Type, classArgs, methodArgs);
            var (kind, isDouble, size, count, known) = Classify(type);
            abi.Known &= known;
            switch (kind)
            {
                case Class.Float or Class.Aggregate:
                {
                    int registers = kind == Class.Float ? 1 : count;
                    int position;
                    if (nsrn + registers <= Registers)
                    {
                        position = RegisterModel.Arm64.FirstFloatPosition + nsrn;
                        nsrn += registers;
                    }
                    else
                    {
                        nsrn = Registers;
                        position = RegisterModel.Arm64.FirstStackPosition + nsaa;
                        nsaa += (size + 7) / 8;
                    }
                    abi.Params.Add(new AbiParam(ParamRole.Argument, i, type, kind == Class.Float ? PassKind.Float : PassKind.FloatAggregate,
                        position, isDouble, size, registers));
                    break;
                }
                case Class.Pair:
                    abi.Params.Add(new AbiParam(ParamRole.Argument, i, type, PassKind.IntegerPair, IntegerPosition(2), false, size, 2));
                    break;
                case Class.Indirect:
                    abi.Params.Add(new AbiParam(ParamRole.Argument, i, type, PassKind.Indirect, IntegerPosition(1), false, size));
                    break;
                default:
                    abi.Params.Add(new AbiParam(ParamRole.Argument, i, type, PassKind.Integer, IntegerPosition(1), false, size));
                    break;
            }
        }

        abi.Params.Add(new AbiParam(ParamRole.MethodInfo, -1, null, PassKind.Integer, IntegerPosition(1), false, 8));
        _cache[(method, key)] = abi;
        return abi;
    }
}
