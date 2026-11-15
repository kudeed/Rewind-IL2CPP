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
}

public enum ReturnKind { Void, Integer, Float, Double, StructInRegister, Buffer }

/// <summary>One parameter of the native function, in native order.</summary>
public sealed record AbiParam(ParamRole Role, int ArgumentIndex, TypeSig? Type, PassKind Pass, int Position, bool IsDouble, int Size);

/// <summary>How one managed method is called at the machine level.</summary>
public sealed class MethodAbi
{
    public List<AbiParam> Params = [];
    public ReturnKind Return;
    public TypeSig ReturnType = null!;
    public int ReturnSize;
    public bool Known = true;

    public AbiParam? This => Params.FirstOrDefault(p => p.Role == ParamRole.This);
    public AbiParam? ReturnBuffer => Params.FirstOrDefault(p => p.Role == ParamRole.ReturnBuffer);
}

/// <summary>
/// The Windows x64 calling convention as it applies to IL2CPP's generated functions:
/// <c>Ret Method([Ret* buffer,] [This* __this,] args..., const MethodInfo* method)</c>.
/// Every parameter takes one slot; slots 0-3 are rcx/rdx/r8/r9 or xmm0-3, the rest go on the stack.
/// </summary>
public sealed class Win64Abi(Il2CppModel model, LayoutCalculator layouts)
{
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
    public MethodAbi For(MethodDef method, TypeSig[] classArgs, TypeSig[] methodArgs)
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

    public MethodAbi For(MethodInst inst) => For(inst.Method, inst.ClassArguments, inst.MethodArguments);
}
