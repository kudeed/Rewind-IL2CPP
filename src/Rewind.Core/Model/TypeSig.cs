using System.Text;
using Rewind.Runtime;

namespace Rewind.Model;

public enum SigKind { Primitive, TypeDef, GenericInst, SzArray, Array, Pointer, ByRef, GenericParam, FunctionPointer, Unknown }

/// <summary>
/// A resolved type signature. Instances are interned per <see cref="Il2CppModel"/>, so two signatures from the
/// same model describe the same type exactly when they are the same object.
/// </summary>
public abstract class TypeSig
{
    public abstract SigKind Kind { get; }

    /// <summary>Canonical text used for interning; also a stable identity for diagnostics.</summary>
    public string Key { get; internal set; } = "";

    /// <summary>The type definition behind this signature (the generic definition for instantiations).</summary>
    public virtual TypeDef? Definition => null;

    public virtual bool IsValueType => false;
    public virtual TypeSig? ElementType => null;

    /// <summary>True when the signature mentions a generic parameter anywhere.</summary>
    public virtual bool ContainsGenericParameter => false;

    public bool IsVoid => this is PrimitiveSig { Element: Il2CppTypeEnum.Void };

    /// <summary>C#-style display name, e.g. <c>System.Collections.Generic.List&lt;int&gt;</c>.</summary>
    public string DisplayName
    {
        get
        {
            var sb = new StringBuilder();
            AppendName(sb, fullyQualified: true);
            return sb.ToString();
        }
    }

    public string ShortName
    {
        get
        {
            var sb = new StringBuilder();
            AppendName(sb, fullyQualified: false);
            return sb.ToString();
        }
    }

    public abstract void AppendName(StringBuilder sb, bool fullyQualified);

    public override string ToString() => DisplayName;
}

public sealed class PrimitiveSig(Il2CppTypeEnum element, TypeDef? definition) : TypeSig
{
    public Il2CppTypeEnum Element { get; } = element;
    public override SigKind Kind => SigKind.Primitive;
    public override TypeDef? Definition { get; } = definition;

    public override bool IsValueType => Element is not (Il2CppTypeEnum.String or Il2CppTypeEnum.Object or Il2CppTypeEnum.Void);

    public static string Keyword(Il2CppTypeEnum e) => e switch
    {
        Il2CppTypeEnum.Void => "void",
        Il2CppTypeEnum.Boolean => "bool",
        Il2CppTypeEnum.Char => "char",
        Il2CppTypeEnum.I1 => "sbyte",
        Il2CppTypeEnum.U1 => "byte",
        Il2CppTypeEnum.I2 => "short",
        Il2CppTypeEnum.U2 => "ushort",
        Il2CppTypeEnum.I4 => "int",
        Il2CppTypeEnum.U4 => "uint",
        Il2CppTypeEnum.I8 => "long",
        Il2CppTypeEnum.U8 => "ulong",
        Il2CppTypeEnum.R4 => "float",
        Il2CppTypeEnum.R8 => "double",
        Il2CppTypeEnum.String => "string",
        Il2CppTypeEnum.Object => "object",
        Il2CppTypeEnum.I => "nint",
        Il2CppTypeEnum.U => "nuint",
        Il2CppTypeEnum.TypedByRef => "System.TypedReference",
        _ => e.ToString(),
    };

    /// <summary>Size in bytes of the value on a 64-bit target; 0 for void.</summary>
    public int SizeOf(int pointerSize) => Element switch
    {
        Il2CppTypeEnum.Boolean or Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 => 1,
        Il2CppTypeEnum.Char or Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 => 2,
        Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 or Il2CppTypeEnum.R4 => 4,
        Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 or Il2CppTypeEnum.R8 => 8,
        Il2CppTypeEnum.Void => 0,
        _ => pointerSize,
    };

    public override void AppendName(StringBuilder sb, bool fullyQualified) => sb.Append(Keyword(Element));
}

/// <summary>A non-generic class/struct, or a generic type definition used without arguments.</summary>
public sealed class TypeDefSig(TypeDef definition) : TypeSig
{
    public override SigKind Kind => SigKind.TypeDef;
    public override TypeDef Definition { get; } = definition;
    public override bool IsValueType => Definition.IsValueType;

    public override void AppendName(StringBuilder sb, bool fullyQualified) =>
        sb.Append(fullyQualified ? Definition.FullName : Definition.Name);
}

public sealed class GenericInstSig(TypeDef definition, TypeSig[] arguments) : TypeSig
{
    public override SigKind Kind => SigKind.GenericInst;
    public override TypeDef Definition { get; } = definition;
    public TypeSig[] Arguments { get; } = arguments;
    public override bool IsValueType => Definition.IsValueType;

    public override bool ContainsGenericParameter
    {
        get
        {
            foreach (TypeSig a in Arguments)
                if (a.ContainsGenericParameter)
                    return true;
            return false;
        }
    }

    public override void AppendName(StringBuilder sb, bool fullyQualified)
    {
        // A nested type repeats its enclosing types' generic parameters, so the argument list is flat:
        // Outer`1.Inner`2 instantiated with [A, B, C] reads Outer<A>.Inner<B, C>.
        var chain = new List<TypeDef>();
        for (TypeDef? d = Definition; d != null; d = d.DeclaringType) chain.Add(d);
        chain.Reverse();

        if (fullyQualified && chain[0].Namespace.Length != 0) sb.Append(chain[0].Namespace).Append('.');
        int next = 0;
        for (int i = 0; i < chain.Count; i++)
        {
            TypeDef d = chain[i];
            bool innermost = i == chain.Count - 1;
            int own = innermost ? Arguments.Length - next : Math.Min(TypeDef.ArityOf(d.Name), Arguments.Length - next);
            if (fullyQualified || innermost)
            {
                if (fullyQualified && i > 0) sb.Append('.');
                sb.Append(TypeDef.StripArity(d.Name));
                if (own > 0)
                {
                    sb.Append('<');
                    for (int k = 0; k < own; k++)
                    {
                        if (k != 0) sb.Append(", ");
                        Arguments[next + k].AppendName(sb, fullyQualified);
                    }
                    sb.Append('>');
                }
            }
            next += Math.Max(0, own);
        }
    }
}

public sealed class SzArraySig(TypeSig element) : TypeSig
{
    public override SigKind Kind => SigKind.SzArray;
    public override TypeSig ElementType { get; } = element;
    public override bool ContainsGenericParameter => ElementType.ContainsGenericParameter;

    public override void AppendName(StringBuilder sb, bool fullyQualified)
    {
        ElementType.AppendName(sb, fullyQualified);
        sb.Append("[]");
    }
}

public sealed class ArraySig(TypeSig element, int rank) : TypeSig
{
    public override SigKind Kind => SigKind.Array;
    public override TypeSig ElementType { get; } = element;
    public int Rank { get; } = rank;
    public override bool ContainsGenericParameter => ElementType.ContainsGenericParameter;

    public override void AppendName(StringBuilder sb, bool fullyQualified)
    {
        ElementType.AppendName(sb, fullyQualified);
        sb.Append('[').Append(',', Math.Max(0, Rank - 1)).Append(']');
    }
}

public sealed class PointerSig(TypeSig element) : TypeSig
{
    public override SigKind Kind => SigKind.Pointer;
    public override TypeSig ElementType { get; } = element;
    public override bool IsValueType => true;
    public override bool ContainsGenericParameter => ElementType.ContainsGenericParameter;

    public override void AppendName(StringBuilder sb, bool fullyQualified)
    {
        ElementType.AppendName(sb, fullyQualified);
        sb.Append('*');
    }
}

public sealed class ByRefSig(TypeSig element) : TypeSig
{
    public override SigKind Kind => SigKind.ByRef;
    public override TypeSig ElementType { get; } = element;
    public override bool ContainsGenericParameter => ElementType.ContainsGenericParameter;

    public override void AppendName(StringBuilder sb, bool fullyQualified)
    {
        sb.Append("ref ");
        ElementType.AppendName(sb, fullyQualified);
    }
}

public sealed class GenericParamSig(GenericParam parameter) : TypeSig
{
    public override SigKind Kind => SigKind.GenericParam;
    public GenericParam Parameter { get; } = parameter;
    public override bool ContainsGenericParameter => true;
    public override void AppendName(StringBuilder sb, bool fullyQualified) => sb.Append(Parameter.Name);
}

/// <summary>Function pointers and anything the type table encodes that we do not model yet.</summary>
public sealed class OpaqueSig(SigKind kind, string text) : TypeSig
{
    public override SigKind Kind { get; } = kind;
    public string Text { get; } = text;
    public override bool IsValueType => Kind == SigKind.FunctionPointer;
    public override void AppendName(StringBuilder sb, bool fullyQualified) => sb.Append(Text);
}
