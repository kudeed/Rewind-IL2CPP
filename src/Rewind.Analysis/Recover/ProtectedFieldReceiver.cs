using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Family visibility also restricts the receiver of an instance field access: a derived class cannot use
/// the protected field on an unrelated sibling or on an instance known only as the base class. Inlining a
/// public getter may leave exactly such an access. The regular field check must also succeed.
/// </summary>
internal static class ProtectedFieldReceiver
{
    public static bool Allows(FieldDef field, MethodDef from, HExpr? receiver)
    {
        int access = field.Attrs & FieldDef.AccessMask;
        if (field.IsStatic || access is not (2 or 4 or 5)) return true;
        if (access == 5 && ReferenceEquals(from.DeclaringType.Assembly, field.DeclaringType.Assembly))
            return true; // family-or-assembly is already allowed through assembly visibility

        TypeDef? receiverType = receiver is HArg { Index: -1 } && !from.IsStatic
            ? from.DeclaringType
            : receiver?.Type?.Definition;
        for (TypeDef? user = from.DeclaringType; user != null; user = user.DeclaringType)
        {
            // The declaring class and its nested classes may access the field on any instance of it.
            if (ReferenceEquals(user, field.DeclaringType)) return true;
            if (Derives(user, field.DeclaringType) && receiverType != null && Derives(receiverType, user))
                return true;
        }
        return false;
    }

    private static bool Derives(TypeDef type, TypeDef ancestor)
    {
        int guard = 0;
        for (TypeDef? current = type; current != null && guard++ < 64; current = current.BaseType?.Definition)
            if (ReferenceEquals(current, ancestor)) return true;
        return false;
    }
}
