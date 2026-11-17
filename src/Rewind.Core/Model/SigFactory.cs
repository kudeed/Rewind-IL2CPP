using Rewind.Runtime;

namespace Rewind.Model;

/// <summary>Creates interned <see cref="TypeSig"/> instances and performs generic substitution.</summary>
public sealed class SigFactory
{
    // (Shared by every thread that recovers methods: two that ask for the same type at the same time must get
    // the same instance, since types are compared by reference.)
    private readonly System.Collections.Concurrent.ConcurrentDictionary<string, TypeSig> _interned = new(StringComparer.Ordinal);

    private T Intern<T>(string key, Func<T> create) where T : TypeSig
    {
        if (_interned.TryGetValue(key, out TypeSig? existing)) return (T)existing;
        T sig = create();
        sig.Key = key;
        // (Made twice by two threads: the one that got there first is the type; the other is dropped unseen.)
        return (T)_interned.GetOrAdd(key, sig);
    }

    public PrimitiveSig Primitive(Il2CppTypeEnum element, TypeDef? definition = null) =>
        Intern("P" + (int)element, () => new PrimitiveSig(element, definition));

    public TypeDefSig TypeDef(TypeDef definition) =>
        Intern("D" + definition.Index, () => new TypeDefSig(definition));

    public GenericInstSig GenericInst(TypeDef definition, TypeSig[] arguments)
    {
        string key = "G" + definition.Index + "<" + string.Join(",", arguments.Select(a => a.Key)) + ">";
        return Intern(key, () => new GenericInstSig(definition, arguments));
    }

    public SzArraySig SzArray(TypeSig element) => Intern("S[" + element.Key + "]", () => new SzArraySig(element));

    public ArraySig Array(TypeSig element, int rank) =>
        Intern("A" + rank + "[" + element.Key + "]", () => new ArraySig(element, rank));

    public PointerSig Pointer(TypeSig element) => Intern("*" + element.Key, () => new PointerSig(element));

    public ByRefSig ByRef(TypeSig element) => Intern("&" + element.Key, () => new ByRefSig(element));

    public GenericParamSig GenericParam(GenericParam parameter) =>
        Intern("V" + parameter.Index, () => new GenericParamSig(parameter));

    public OpaqueSig Opaque(SigKind kind, string text) => Intern("?" + (int)kind + ":" + text, () => new OpaqueSig(kind, text));

    /// <summary>
    /// Replaces generic parameters by the supplied arguments: type parameters from
    /// <paramref name="classArguments"/>, method parameters from <paramref name="methodArguments"/>.
    /// Parameters with no supplied argument are left in place.
    /// </summary>
    public TypeSig Substitute(TypeSig sig, TypeSig[] classArguments, TypeSig[] methodArguments)
    {
        if (!sig.ContainsGenericParameter) return sig;
        switch (sig)
        {
            case GenericParamSig gp:
            {
                TypeSig[] source = gp.Parameter.IsMethodParameter ? methodArguments : classArguments;
                int position = gp.Parameter.Position;
                return position < source.Length ? source[position] : sig;
            }
            case GenericInstSig gi:
            {
                var args = new TypeSig[gi.Arguments.Length];
                for (int i = 0; i < args.Length; i++)
                    args[i] = Substitute(gi.Arguments[i], classArguments, methodArguments);
                return GenericInst(gi.Definition, args);
            }
            case SzArraySig sz:
                return SzArray(Substitute(sz.ElementType, classArguments, methodArguments));
            case ArraySig arr:
                return Array(Substitute(arr.ElementType, classArguments, methodArguments), arr.Rank);
            case PointerSig ptr:
                return Pointer(Substitute(ptr.ElementType, classArguments, methodArguments));
            case ByRefSig byRef:
                return ByRef(Substitute(byRef.ElementType, classArguments, methodArguments));
            default:
                return sig;
        }
    }
}
