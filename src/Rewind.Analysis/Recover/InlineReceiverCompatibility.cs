using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Proves that a receiver's static type can name an inlined instance
/// method. The caller supplies model-specific generic substitution and
/// type-instantiation equality; unknown/open receiver types fail closed.
/// </summary>
internal static class InlineReceiverCompatibility
{
    internal static bool IsAssignable(
        TypeSig expected,
        TypeSig actual,
        Func<TypeSig, TypeSig, bool> sameInstantiation,
        Func<TypeSig, TypeSig, TypeSig?> substitute)
    {
        if (expected.IsValueType != actual.IsValueType ||
            expected.Definition == null || actual.Definition == null ||
            expected.ContainsGenericParameter || actual.ContainsGenericParameter)
            return false;
        if (expected.IsValueType) return sameInstantiation(expected, actual);
        var pending = new Stack<TypeSig>();
        var visited = new HashSet<TypeSig>();
        pending.Push(actual);
        while (pending.TryPop(out TypeSig? candidate))
        {
            if (!visited.Add(candidate)) continue;
            if (candidate.ContainsGenericParameter || candidate.IsValueType) continue;
            if (visited.Count > 256) return false;
            if (sameInstantiation(expected, candidate)) return true;
            if (candidate.Definition is not { } definition) continue;
            if (definition.BaseType is { } parent && substitute(candidate, parent) is { } baseType) pending.Push(baseType);
            foreach (TypeSig iface in definition.Interfaces)
                if (substitute(candidate, iface) is { } implemented) pending.Push(implemented);
        }
        return false;
    }
}
