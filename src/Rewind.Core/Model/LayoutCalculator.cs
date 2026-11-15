using Rewind.Binary;
using Rewind.Runtime;

namespace Rewind.Model;

/// <summary>One instance field's place inside its type.</summary>
public readonly record struct FieldSlot(FieldDef Field, TypeSig Type, int Offset, int Size);

/// <summary>
/// Layout of a type's instance data. For classes, offsets and <see cref="Size"/> count from the start of the
/// object (including the two-pointer header). For value types they count from the start of the unboxed value.
/// </summary>
public sealed class TypeLayout
{
    public int Size;
    public int Align = 1;
    /// <summary>Size without trailing padding; a derived class may start its fields here under the Itanium ABI.</summary>
    public int DataSize;
    public FieldSlot[] Fields = [];
    /// <summary>False when some part could not be determined (open generics, unknown types).</summary>
    public bool Known = true;
}

/// <summary>
/// Computes sizes and field offsets. IL2CPP records exact offsets for type definitions, taken from the C++
/// compiler; this class uses those where they exist and reproduces the same C++ struct layout rules for
/// instantiated generic types, whose layouts are not recorded.
/// </summary>
public sealed class LayoutCalculator
{
    private readonly Il2CppModel _model;
    private readonly int _ptr;
    private readonly int _header;
    private readonly Dictionary<TypeSig, TypeLayout> _cache = [];
    private readonly HashSet<TypeSig> _inProgress = [];

    /// <summary>
    /// MSVC starts a derived class's fields at the base's full size. The Itanium ABI (clang on Android, iOS,
    /// Linux, macOS) lets them start inside the base's trailing padding.
    /// </summary>
    public bool ReuseBaseTailPadding { get; set; }

    public LayoutCalculator(Il2CppModel model)
    {
        _model = model;
        _ptr = model.Image.PointerSize;
        _header = 2 * _ptr;
        ReuseBaseTailPadding = model.Image.Format != ImageFormat.PE;
    }

    private static int AlignUp(int value, int align) => align <= 1 ? value : (value + align - 1) / align * align;

    /// <summary>Alignment of 8-byte primitives: 4 on 32-bit x86 outside Windows, otherwise 8.</summary>
    private int WideAlign => _model.Image.Arch == CpuArch.X86 && _model.Image.Format != ImageFormat.PE ? 4 : 8;

    /// <summary>Size and alignment of a value of this type when stored in a field, local or array element.</summary>
    /// <summary>
    /// Type parameters known to stand for reference types: those of a generic definition, while the body that
    /// its instantiations over reference types share is read. Each is one pointer. Any other type parameter's
    /// size is not known.
    /// </summary>
    public HashSet<GenericParam>? ReferenceParameters;

    public (int Size, int Align, bool Known) SizeOf(TypeSig sig)
    {
        switch (sig)
        {
            case GenericParamSig own when ReferenceParameters != null && ReferenceParameters.Contains(own.Parameter):
                return (_ptr, _ptr, true);
            case PrimitiveSig p:
            {
                int size = p.SizeOf(_ptr);
                if (p.Element == Il2CppTypeEnum.TypedByRef) return (2 * _ptr, _ptr, true);
                if (size == 8) return (8, _ptr == 8 ? 8 : WideAlign, true);
                return (size, Math.Max(1, size), true);
            }
            case PointerSig or ByRefSig or SzArraySig or ArraySig:
                return (_ptr, _ptr, true);
            case OpaqueSig { Kind: SigKind.FunctionPointer }:
                return (_ptr, _ptr, true);
            case GenericParamSig or OpaqueSig:
                return (_ptr, _ptr, false);
        }
        TypeDef? def = sig.Definition;
        if (def == null) return (_ptr, _ptr, false);
        if (!def.IsValueType) return (_ptr, _ptr, true);
        if (def.IsEnum) return def.EnumUnderlyingType != null ? SizeOf(def.EnumUnderlyingType) : (4, 4, true);
        TypeLayout layout = Of(sig);
        return (layout.Size, layout.Align, layout.Known);
    }

    /// <summary>Layout of a class or struct, by signature (so generic instantiations get their own layout).</summary>
    public TypeLayout Of(TypeSig sig)
    {
        // What depends on type parameters being references holds only while they are known to be: not remembered.
        bool open = ReferenceParameters != null && sig.ContainsGenericParameter;
        if (!open && _cache.TryGetValue(sig, out TypeLayout? cached)) return cached;
        TypeDef? def = sig.Definition;
        if (def == null || !_inProgress.Add(sig)) return new TypeLayout { Size = _ptr, Align = _ptr, DataSize = _ptr, Known = false };
        try
        {
            TypeSig[] typeArgs = sig is GenericInstSig g ? g.Arguments : [];
            TypeLayout layout = typeArgs.Length == 0 ? FromRecorded(def) : Compute(def, typeArgs);
            if (!open) _cache[sig] = layout;
            return layout;
        }
        finally
        {
            _inProgress.Remove(sig);
        }
    }

    /// <summary>A type definition: IL2CPP's recorded offsets are authoritative.</summary>
    private TypeLayout FromRecorded(TypeDef def)
    {
        int bias = def.IsValueType ? _header : 0;
        var slots = new List<FieldSlot>();
        int align = 1, end = def.IsValueType ? 0 : BaseDataEnd(def, []);
        bool known = true;
        foreach (FieldDef f in def.Fields)
        {
            if (f.IsStatic) continue;
            var (size, fieldAlign, fieldKnown) = SizeOf(f.Type);
            known &= fieldKnown;
            if (f.Offset < bias)
            {
                known = false;
                continue;
            }
            int offset = f.Offset - bias;
            slots.Add(new FieldSlot(f, f.Type, offset, size));
            align = Math.Max(align, fieldAlign);
            end = Math.Max(end, offset + size);
        }
        if (def.PackingSize > 0) align = Math.Min(align, def.PackingSize);

        int recorded = (int)def.Sizes.InstanceSize - bias;
        var layout = new TypeLayout { Fields = slots.ToArray(), Align = def.IsValueType ? align : Math.Max(align, _ptr), Known = known };
        if (def.Sizes.InstanceSize != 0 && recorded > 0)
        {
            layout.Size = recorded;
        }
        else
        {
            layout.Size = Math.Max(def.IsValueType ? 1 : _header, AlignUp(end, layout.Align));
            if (def.GenericParameters.Length != 0) layout.Known = false;
        }
        layout.DataSize = Math.Max(end, def.IsValueType ? 0 : _header);
        return layout;
    }

    private int BaseDataEnd(TypeDef def, TypeSig[] typeArgs)
    {
        if (def.BaseType == null) return _header;
        TypeSig baseSig = _model.Sigs.Substitute(def.BaseType, typeArgs, []);
        TypeLayout baseLayout = Of(baseSig);
        return ReuseBaseTailPadding ? baseLayout.DataSize : baseLayout.Size;
    }

    /// <summary>
    /// Where a type's static fields are in its static data (thread-local ones are kept elsewhere and not given).
    /// A generic type has no recorded places - each instantiation lays its own out when it is first used, one
    /// field after another in the order they are declared, each aligned to its own size.
    /// </summary>
    public List<FieldSlot> Statics(TypeSig sig)
    {
        var slots = new List<FieldSlot>();
        TypeDef? def = sig.Definition;
        if (def == null) return slots;
        TypeSig[] typeArgs = sig is GenericInstSig g ? g.Arguments : [];
        bool recorded = def.GenericParameters.Length == 0;
        int pack = def.PackingSize, offset = 0;
        foreach (FieldDef f in def.Fields)
        {
            if (!f.IsStatic || f.IsLiteral || f.Offset < 0) continue;
            TypeSig type = typeArgs.Length != 0 ? _model.Sigs.Substitute(f.Type, typeArgs, []) : f.Type;
            var (size, align, _) = SizeOf(type);
            int at = f.Offset;
            if (!recorded)
            {
                if (pack > 0) align = Math.Min(align, pack);
                at = AlignUp(offset, align);
                offset = at + size;
            }
            slots.Add(new FieldSlot(f, type, at, size));
        }
        return slots;
    }

    /// <summary>
    /// Runs the computed layout on a type definition that also has recorded offsets, so the two can be compared.
    /// </summary>
    public TypeLayout Recompute(TypeDef def) => Compute(def, []);

    /// <summary>An instantiated generic type: lay the fields out the way the C++ compiler would.</summary>
    private TypeLayout Compute(TypeDef def, TypeSig[] typeArgs)
    {
        bool isValue = def.IsValueType;
        bool explicitLayout = (def.Flags & TypeDef.LayoutMask) == TypeDef.ExplicitLayout;
        int bias = isValue ? _header : 0;
        int pack = def.PackingSize;

        int offset, align;
        if (isValue)
        {
            offset = 0;
            align = 1;
        }
        else
        {
            offset = BaseDataEnd(def, typeArgs);
            align = _ptr;
            if (def.BaseType != null) align = Math.Max(align, Of(_model.Sigs.Substitute(def.BaseType, typeArgs, [])).Align);
        }

        var slots = new List<FieldSlot>();
        bool known = true;
        int end = offset;
        foreach (FieldDef f in def.Fields)
        {
            if (f.IsStatic) continue;
            TypeSig type = _model.Sigs.Substitute(f.Type, typeArgs, []);
            var (size, fieldAlign, fieldKnown) = SizeOf(type);
            known &= fieldKnown;
            if (pack > 0) fieldAlign = Math.Min(fieldAlign, pack);

            int at;
            if (explicitLayout && f.Offset >= bias)
            {
                at = f.Offset - bias; // explicit offsets do not depend on the type arguments
            }
            else
            {
                at = AlignUp(offset, fieldAlign);
                offset = at + size;
            }
            slots.Add(new FieldSlot(f, type, at, size));
            align = Math.Max(align, fieldAlign);
            end = Math.Max(end, at + size);
        }

        int total = AlignUp(end, align);
        if (isValue && total == 0) total = 1; // an empty C++ struct still occupies a byte
        return new TypeLayout
        {
            Fields = slots.ToArray(),
            Size = total,
            Align = align,
            DataSize = end,
            Known = known,
        };
    }

    /// <summary>
    /// Finds the field that covers <paramref name="offset"/>, looking through base classes. Offsets are in the
    /// same frame as <see cref="TypeLayout"/> (object-relative for classes, value-relative for structs).
    /// </summary>
    /// <summary>
    /// A field that occupies exactly the bytes [offset, offset + size): in a union (explicit layout, overlapping
    /// fields) the one an access of that size means. Integer fields are preferred over floating point ones, which
    /// the caller can still reinterpret; unsigned over signed.
    /// </summary>
    public FieldSlot? FieldExactly(TypeSig sig, int offset, int size)
    {
        static int Rank(TypeSig t) => t is PrimitiveSig p
            ? p.Element switch
            {
                Rewind.Runtime.Il2CppTypeEnum.U1 or Rewind.Runtime.Il2CppTypeEnum.U2 or Rewind.Runtime.Il2CppTypeEnum.U4 or Rewind.Runtime.Il2CppTypeEnum.U8 => 0,
                Rewind.Runtime.Il2CppTypeEnum.I1 or Rewind.Runtime.Il2CppTypeEnum.I2 or Rewind.Runtime.Il2CppTypeEnum.I4 or Rewind.Runtime.Il2CppTypeEnum.I8 => 1,
                Rewind.Runtime.Il2CppTypeEnum.R4 or Rewind.Runtime.Il2CppTypeEnum.R8 => 3,
                _ => 2,
            }
            : 2;
        for (TypeSig? current = sig; current?.Definition != null;)
        {
            TypeLayout layout = Of(current);
            FieldSlot? best = null;
            foreach (FieldSlot slot in layout.Fields)
                if (slot.Offset == offset && slot.Size == size && (best == null || Rank(slot.Type) < Rank(best.Value.Type)))
                    best = slot;
            if (best != null) return best;
            TypeDef def = current.Definition;
            if (def.IsValueType || def.BaseType == null) break;
            current = _model.Sigs.Substitute(def.BaseType, current is GenericInstSig g ? g.Arguments : [], []);
        }
        return null;
    }

    public FieldSlot? FieldAt(TypeSig sig, int offset)
    {
        for (TypeSig? current = sig; current?.Definition != null;)
        {
            TypeLayout layout = Of(current);
            foreach (FieldSlot slot in layout.Fields)
                if (offset >= slot.Offset && offset < slot.Offset + Math.Max(1, slot.Size))
                    return slot;
            TypeDef def = current.Definition;
            if (def.IsValueType || def.BaseType == null) break;
            current = _model.Sigs.Substitute(def.BaseType, current is GenericInstSig g ? g.Arguments : [], []);
        }
        return null;
    }
}
