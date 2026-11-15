namespace Rewind.Runtime;

/// <summary>ECMA-335 element types as used by Il2CppType (il2cpp-blob.h).</summary>
public enum Il2CppTypeEnum : byte
{
    End = 0x00, Void = 0x01, Boolean = 0x02, Char = 0x03, I1 = 0x04, U1 = 0x05, I2 = 0x06, U2 = 0x07,
    I4 = 0x08, U4 = 0x09, I8 = 0x0A, U8 = 0x0B, R4 = 0x0C, R8 = 0x0D, String = 0x0E, Ptr = 0x0F,
    ByRef = 0x10, ValueType = 0x11, Class = 0x12, Var = 0x13, Array = 0x14, GenericInst = 0x15,
    TypedByRef = 0x16, I = 0x18, U = 0x19, FnPtr = 0x1B, Object = 0x1C, SzArray = 0x1D, MVar = 0x1E,
    CModReqd = 0x1F, CModOpt = 0x20, Internal = 0x21, Modifier = 0x40, Sentinel = 0x41, Pinned = 0x45,
    Enum = 0x55, Il2CppTypeIndex = 0xFF,
}

/// <summary>One Il2CppType record from the binary, with its links resolved to table indexes.</summary>
public sealed class RawType
{
    public ulong Va;
    public ulong Data;
    public ushort Attrs;
    public Il2CppTypeEnum Type;
    public bool ByRef, Pinned;
    public int NumMods;

    /// <summary>Class/ValueType: type definition index. Var/MVar: generic parameter index. Otherwise -1.</summary>
    public int DefinitionIndex = -1;

    /// <summary>Ptr/SzArray/Array: index of the element Il2CppType. Otherwise -1.</summary>
    public int ElementType = -1;

    public int ArrayRank;

    /// <summary>GenericInst: type definition index of the generic type, and the instantiation's argument list.</summary>
    public int GenericTypeDefinition = -1;
    public int GenericInst = -1;
}

/// <summary>An Il2CppGenericInst: an ordered list of type arguments (indexes into the type table).</summary>
public sealed class RawGenericInst
{
    public ulong Va;
    public int[] TypeArgs = [];
}

public readonly record struct RawMethodSpec(int MethodDefinitionIndex, int ClassInstIndex, int MethodInstIndex);

public readonly record struct RawGenericMethodFunction(int MethodSpecIndex, int MethodPointerIndex, int InvokerIndex, int AdjustorThunkIndex);

public readonly record struct RawTypeSizes(uint InstanceSize, int NativeSize, uint StaticFieldsSize, uint ThreadStaticFieldsSize);

public readonly record struct RawRgctxRange(uint Token, int Start, int Length);

/// <summary>Kinds of runtime generic context entry (il2cpp-metadata.h, Il2CppRGCTXDataType).</summary>
public enum RgctxKind { Invalid = 0, Type = 1, Class = 2, Method = 3, Array = 4, Constrained = 5 }

/// <summary>
/// One runtime generic context entry. For Type/Class/Array, <see cref="Index"/> is a type index. For Method it
/// is a method spec index. For Constrained, <see cref="Index"/> is the constrained type and
/// <see cref="EncodedMethod"/> the encoded method being called on it.
/// </summary>
public readonly record struct RawRgctxEntry(RgctxKind Kind, int Index, uint EncodedMethod);

/// <summary>One entry of a runtime generic context, resolved: a type (for Type, Class, Array) or a method.</summary>
public readonly record struct RgctxItem(RgctxKind Kind, Rewind.Model.TypeSig? Type, Rewind.Model.MethodInst? Method);

public sealed class RawCodeGenModule
{
    public ulong Va;
    public string Name = "";
    public ulong[] MethodPointers = [];
    public int[] InvokerIndices = [];
    public Dictionary<uint, ulong> AdjustorThunks = [];
    public RawRgctxRange[] RgctxRanges = [];
    public RawRgctxEntry[] Rgctxs = [];
    public ulong ModuleInitializer;
}
