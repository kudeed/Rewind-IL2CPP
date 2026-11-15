using System.Globalization;
using System.Text;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Output;

/// <summary>C# spellings for modifiers and constants, shared by the text dump and other writers.</summary>
public static class CSharpFormat
{
    public static string TypeVisibility(TypeDef type) => (type.Flags & TypeDef.VisibilityMask) switch
    {
        1 or 2 => "public",
        3 => "private",
        4 => "protected",
        5 => "internal",
        6 => "private protected",
        7 => "protected internal",
        _ => "internal",
    };

    public static string MemberVisibility(int access) => access switch
    {
        1 => "private",
        2 => "private protected",
        3 => "internal",
        4 => "protected",
        5 => "protected internal",
        6 => "public",
        _ => "private",
    };

    public static string TypeKeyword(TypeDef type)
    {
        if (type.IsInterface) return "interface";
        if (type.IsEnum) return "enum";
        if (type.IsDelegate) return "delegate";
        if (type.IsValueType) return "struct";
        return "class";
    }

    public static string TypeModifiers(TypeDef type)
    {
        var sb = new StringBuilder(TypeVisibility(type));
        if (type.IsInterface || type.IsEnum || type.IsDelegate || type.IsValueType) return sb.ToString();
        if (type.IsAbstract && type.IsSealed) sb.Append(" static");
        else if (type.IsAbstract) sb.Append(" abstract");
        else if (type.IsSealed) sb.Append(" sealed");
        return sb.ToString();
    }

    public static string FieldModifiers(FieldDef field)
    {
        var sb = new StringBuilder(MemberVisibility(field.Attrs & FieldDef.AccessMask));
        if (field.IsLiteral) sb.Append(" const");
        else
        {
            if (field.IsStatic) sb.Append(" static");
            if ((field.Attrs & FieldDef.InitOnly) != 0) sb.Append(" readonly");
        }
        return sb.ToString();
    }

    public static string MethodModifiers(MethodDef method)
    {
        var sb = new StringBuilder();
        if (!method.DeclaringType.IsInterface) sb.Append(MemberVisibility(method.Flags & MethodDef.AccessMask));
        if (method.IsStatic) sb.Append(" static");
        if (method.DeclaringType.IsInterface) return sb.ToString().TrimStart();
        if (method.IsAbstract) sb.Append(" abstract");
        else if (method.IsVirtual)
        {
            bool newSlot = (method.Flags & MethodDef.NewSlot) != 0;
            bool final = (method.Flags & MethodDef.Final) != 0;
            if (newSlot && final) { }                      // interface implementation, not virtual in C#
            else if (newSlot) sb.Append(" virtual");
            else sb.Append(final ? " sealed override" : " override");
        }
        if ((method.Flags & MethodDef.PInvokeImpl) != 0 || (method.ImplFlags & 0x1000) != 0) sb.Append(" extern");
        return sb.ToString().TrimStart();
    }

    public static string Literal(string value)
    {
        var sb = new StringBuilder(value.Length + 2);
        sb.Append('"');
        foreach (char c in value) AppendChar(sb, c, '"');
        sb.Append('"');
        return sb.ToString();
    }

    private static void AppendChar(StringBuilder sb, char c, char quote)
    {
        switch (c)
        {
            case '\\': sb.Append("\\\\"); break;
            case '\0': sb.Append("\\0"); break;
            case '\a': sb.Append("\\a"); break;
            case '\b': sb.Append("\\b"); break;
            case '\f': sb.Append("\\f"); break;
            case '\n': sb.Append("\\n"); break;
            case '\r': sb.Append("\\r"); break;
            case '\t': sb.Append("\\t"); break;
            case '\v': sb.Append("\\v"); break;
            default:
                if (c == quote) sb.Append('\\').Append(c);
                else if (char.IsControl(c) || char.IsSurrogate(c) || c == (char)0x2028 || c == (char)0x2029 || c == (char)0x85)
                    sb.Append("\\u").Append(((int)c).ToString("X4"));
                else sb.Append(c);
                break;
        }
    }

    /// <summary>Formats a decoded constant (see <see cref="BlobDecoder"/>) as a C# expression.</summary>
    public static string Constant(object? value)
    {
        switch (value)
        {
            case null: return "null";
            case bool b: return b ? "true" : "false";
            case string s: return Literal(s);
            case char c:
            {
                var sb = new StringBuilder("'");
                AppendChar(sb, c, '\'');
                return sb.Append('\'').ToString();
            }
            case float f:
                if (float.IsNaN(f)) return "float.NaN";
                if (float.IsPositiveInfinity(f)) return "float.PositiveInfinity";
                if (float.IsNegativeInfinity(f)) return "float.NegativeInfinity";
                return f.ToString("R", CultureInfo.InvariantCulture) + "f";
            case double d:
                if (double.IsNaN(d)) return "double.NaN";
                if (double.IsPositiveInfinity(d)) return "double.PositiveInfinity";
                if (double.IsNegativeInfinity(d)) return "double.NegativeInfinity";
                string text = d.ToString("R", CultureInfo.InvariantCulture);
                return text.Contains('.') || text.Contains('E') ? text : text + ".0";
            case uint u: return u.ToString(CultureInfo.InvariantCulture) + "u";
            case long l: return l.ToString(CultureInfo.InvariantCulture) + "L";
            case ulong ul: return ul.ToString(CultureInfo.InvariantCulture) + "UL";
            case EnumConstant e: return EnumText(e);
            case TypeConstant t: return "typeof(" + t.Type.DisplayName + ")";
            case ArrayConstant a:
                return "new[] { " + string.Join(", ", a.Items.Select(Constant)) + " }";
            case IFormattable f2: return f2.ToString(null, CultureInfo.InvariantCulture);
            default: return value.ToString() ?? "null";
        }
    }

    private static string EnumText(EnumConstant e)
    {
        long numeric = Convert.ToInt64(e.Value is ulong u ? unchecked((long)u) : e.Value, CultureInfo.InvariantCulture);
        return "(" + e.EnumType.FullName + ")" + numeric.ToString(CultureInfo.InvariantCulture);
    }

    public static string Attribute(CustomAttribute attribute)
    {
        string name = attribute.AttributeType.FullName;
        if (name.EndsWith("Attribute", StringComparison.Ordinal)) name = name[..^9];
        var args = new List<string>();
        foreach (object? a in attribute.Arguments) args.Add(Constant(a));
        foreach (var (field, value) in attribute.Fields) args.Add(field.Name + " = " + Constant(value));
        foreach (var (property, value) in attribute.Properties) args.Add(property.Name + " = " + Constant(value));
        return args.Count == 0 ? "[" + name + "]" : "[" + name + "(" + string.Join(", ", args) + ")]";
    }

    public static string ParameterPrefix(ParamDef parameter)
    {
        if (parameter.Type is not ByRefSig) return "";
        if (parameter.IsOut) return "out ";
        if (parameter.IsIn) return "in ";
        return "ref ";
    }

    public static string ParameterType(ParamDef parameter) =>
        parameter.Type is ByRefSig byRef ? byRef.ElementType.DisplayName : parameter.Type.DisplayName;

    public static bool IsPrimitiveKeyword(TypeSig sig) => sig is PrimitiveSig { Element: not Il2CppTypeEnum.TypedByRef };
}
