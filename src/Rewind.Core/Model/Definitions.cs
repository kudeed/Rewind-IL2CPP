using Rewind.Runtime;

namespace Rewind.Model;

public sealed class AssemblyModel
{
    public int Index;
    public string Name = "";          // "mscorlib"
    public string ImageName = "";     // "mscorlib.dll"
    public Version Version = new(0, 0, 0, 0);
    public string Culture = "";
    public ulong PublicKeyToken;
    public byte[] PublicKey = [];
    public uint Flags, HashAlg, Token;
    public List<TypeDef> Types = [];
    public List<AssemblyModel> References = [];
    public RawCodeGenModule? Module;
    public MethodDef? EntryPoint;
    public int CustomAttributeStart = -1, CustomAttributeCount;

    public override string ToString() => Name;
}

public sealed class TypeDef
{
    public int Index;
    public AssemblyModel Assembly = null!;
    public string Name = "";
    public string Namespace = "";
    public uint Flags;
    public uint Token;
    public TypeDef? DeclaringType;
    public List<TypeDef> NestedTypes = [];
    public TypeSig? BaseType;
    public TypeSig[] Interfaces = [];
    public FieldDef[] Fields = [];
    public MethodDef[] Methods = [];
    public PropertyDef[] Properties = [];
    public EventDef[] Events = [];
    public GenericParam[] GenericParameters = [];

    public bool IsValueType, IsEnum, HasFinalizer, HasStaticConstructor, IsBlittable, IsByRefLike;
    public int PackingSize;            // 0 = default
    public bool PackingSizeIsDefault = true, ClassSizeIsDefault = true;

    /// <summary>Sizes computed by the IL2CPP converter (instance size includes the 2-pointer object header).</summary>
    public RawTypeSizes Sizes;

    /// <summary>The signature that names this type itself (its "byval" Il2CppType).</summary>
    public TypeSig Sig = null!;

    /// <summary>For enums: the integral type that stores the value.</summary>
    public TypeSig? EnumUnderlyingType;

    /// <summary>Encoded vtable entries exactly as stored; decode with <see cref="Il2CppModel.DecodeVTableEntry"/>.</summary>
    public uint[] VTable = [];

    /// <summary>For each interface implemented: the vtable slot where that interface's methods start.</summary>
    public (TypeSig Interface, int Offset)[] InterfaceOffsets = [];

    public int CustomAttributeIndex = -1;

    public const uint VisibilityMask = 0x7, Interface = 0x20, Abstract = 0x80, Sealed = 0x100,
        SpecialName = 0x400, Serializable = 0x2000, LayoutMask = 0x18, ExplicitLayout = 0x10, SequentialLayout = 0x8,
        BeforeFieldInit = 0x100000;

    public bool IsInterface => (Flags & Interface) != 0;
    public bool IsAbstract => (Flags & Abstract) != 0;
    public bool IsSealed => (Flags & Sealed) != 0;
    public bool IsNested => DeclaringType != null;
    public bool IsGenericDefinition => GenericParameters.Length != 0;

    /// <summary>True for System.Delegate descendants (set while building the model).</summary>
    public bool IsDelegate;

    /// <summary>Reflection-style full name: Namespace.Outer/Inner`1.</summary>
    public string ReflectionName
    {
        get
        {
            if (DeclaringType != null) return DeclaringType.ReflectionName + "/" + Name;
            return Namespace.Length == 0 ? Name : Namespace + "." + Name;
        }
    }

    /// <summary>C#-style full name: Namespace.Outer.Inner (arity suffixes removed).</summary>
    public string FullName
    {
        get
        {
            if (DeclaringType != null) return DeclaringType.FullName + "." + StripArity(Name);
            return Namespace.Length == 0 ? StripArity(Name) : Namespace + "." + StripArity(Name);
        }
    }

    public static string StripArity(string name)
    {
        int tick = name.LastIndexOf('`');
        return tick > 0 && tick < name.Length - 1 && char.IsAsciiDigit(name[tick + 1]) ? name[..tick] : name;
    }

    public static int ArityOf(string name)
    {
        int tick = name.LastIndexOf('`');
        return tick > 0 && int.TryParse(name.AsSpan(tick + 1), out int n) ? n : 0;
    }

    public override string ToString() => ReflectionName;
}

public sealed class GenericParam
{
    public int Index;
    public string Name = "";
    public int Position;
    public ushort Flags;
    public bool IsMethodParameter;
    public TypeDef? OwnerType;
    public MethodDef? OwnerMethod;
    public TypeSig[] Constraints = [];

    public const ushort Covariant = 1, Contravariant = 2, ReferenceTypeConstraint = 4,
        NotNullableValueTypeConstraint = 8, DefaultConstructorConstraint = 0x10;

    public override string ToString() => Name;
}

public sealed class FieldDef
{
    public int Index;
    public TypeDef DeclaringType = null!;
    public string Name = "";
    public TypeSig Type = null!;
    public ushort Attrs;
    public uint Token;

    /// <summary>
    /// Offset exactly as IL2CPP records it. For instance fields this counts from the start of the boxed object,
    /// so a struct's first field is at 2 * pointer size; for static fields it is the offset in the static block.
    /// -1 means thread-static (or unavailable).
    /// </summary>
    public int Offset = -1;

    public bool HasDefault;
    public int DefaultTypeIndex = -1, DefaultDataIndex = -1;
    public int CustomAttributeIndex = -1;

    public const ushort AccessMask = 0x7, Static = 0x10, InitOnly = 0x20, Literal = 0x40, NotSerialized = 0x80,
        SpecialName = 0x200, HasFieldRva = 0x100, HasDefaultFlag = 0x8000;

    public bool IsStatic => (Attrs & Static) != 0;
    public bool IsLiteral => (Attrs & Literal) != 0;
    public bool IsThreadStatic => IsStatic && !IsLiteral && Offset == -1;

    public override string ToString() => DeclaringType.ReflectionName + "::" + Name;
}

public sealed class ParamDef
{
    public int Index;
    public int Position;
    public string Name = "";
    public TypeSig Type = null!;
    public ushort Attrs;
    public uint Token;
    public bool HasDefault;
    public int DefaultTypeIndex = -1, DefaultDataIndex = -1;
    public int CustomAttributeIndex = -1;

    public const ushort In = 1, Out = 2, Optional = 0x10, HasDefaultFlag = 0x1000;

    public bool IsOut => (Attrs & Out) != 0 && (Attrs & In) == 0;
    public bool IsIn => (Attrs & In) != 0 && (Attrs & Out) == 0;
}

public sealed class MethodDef
{
    public int Index;
    public TypeDef DeclaringType = null!;
    public string Name = "";
    public TypeSig ReturnType = null!;
    public ParamDef[] Parameters = [];
    public GenericParam[] GenericParameters = [];
    public ushort Flags, ImplFlags, Slot;
    public uint Token, ReturnParameterToken;

    /// <summary>Virtual address of the compiled body; 0 when the method has none of its own.</summary>
    public ulong Address;

    /// <summary>For value type instance methods called through an interface or delegate: unboxing thunk.</summary>
    public ulong AdjustorThunk;

    public int InvokerIndex = -1;
    public int CustomAttributeIndex = -1;

    public const ushort AccessMask = 0x7, Static = 0x10, Final = 0x20, Virtual = 0x40, HideBySig = 0x80,
        NewSlot = 0x100, Abstract = 0x400, SpecialName = 0x800, RtSpecialName = 0x1000, PInvokeImpl = 0x2000;

    public const ushort InvalidSlot = 0xFFFF;

    public bool IsStatic => (Flags & Static) != 0;
    public bool IsVirtual => (Flags & Virtual) != 0;
    public bool IsAbstract => (Flags & Abstract) != 0;
    public bool IsConstructor => Name is ".ctor" or ".cctor";
    public bool IsGenericDefinition => GenericParameters.Length != 0;
    public bool HasSlot => Slot != InvalidSlot;

    public string FullName => DeclaringType.ReflectionName + "::" + Name;

    public override string ToString() => FullName;
}

public sealed class PropertyDef
{
    public TypeDef DeclaringType = null!;
    public string Name = "";
    public MethodDef? Getter, Setter;
    public uint Attrs, Token;
    public int CustomAttributeIndex = -1;
}

public sealed class EventDef
{
    public TypeDef DeclaringType = null!;
    public string Name = "";
    public TypeSig Type = null!;
    public MethodDef? Add, Remove, Raise;
    public uint Token;
    public int CustomAttributeIndex = -1;
}

/// <summary>
/// A method together with the generic arguments it is used with: an instantiated generic method, a method of
/// an instantiated generic type, or both.
/// </summary>
public sealed class MethodInst
{
    public int SpecIndex;
    public MethodDef Method = null!;
    public TypeSig[] ClassArguments = [];
    public TypeSig[] MethodArguments = [];

    /// <summary>Compiled body for this instantiation (often shared by several instantiations); 0 if none.</summary>
    public ulong Address;
    public ulong AdjustorThunk;
    public int InvokerIndex = -1;

    public override string ToString()
    {
        string type = Method.DeclaringType.ReflectionName;
        if (ClassArguments.Length != 0) type += "<" + string.Join(", ", ClassArguments.Select(a => a.DisplayName)) + ">";
        string name = Method.Name;
        if (MethodArguments.Length != 0) name += "<" + string.Join(", ", MethodArguments.Select(a => a.DisplayName)) + ">";
        return type + "::" + name;
    }
}
