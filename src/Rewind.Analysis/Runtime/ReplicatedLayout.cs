using Rewind.Model;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// What lies where in the replicated memory of a networked object.
///
/// Photon Fusion keeps the state of a NetworkBehaviour in a block of 4-byte words the object's "Ptr" points
/// at. When it rewrites a class at build time it gives every "[Networked]" property its words and records
/// them on the property: [NetworkedWeaved(first word, number of words)]. The machine code reads and writes
/// that memory through the pointer, a word or two at a time, with nothing to say what the words are. This
/// says it: the property at an offset, and with it the type of what is kept there.
/// </summary>
public sealed class ReplicatedLayout(Il2CppModel model)
{
    /// <summary>A property's place: where its bytes start from "Ptr", how many there are, and its declared type.</summary>
    public readonly record struct Slot(PropertyDef Property, int Offset, int Size, TypeSig Type);

    private readonly Dictionary<TypeDef, Slot[]> _own = [];
    private readonly BlobDecoder _blobs = new(model);

    /// <summary>The property of a class (or of one it derives from) whose words include the byte at <paramref name="offset"/>.</summary>
    public Slot? At(TypeDef? type, long offset)
    {
        int guard = 0;
        for (TypeDef? t = type; t != null && guard++ < 32; t = t.BaseType?.Definition)
            foreach (Slot slot in Own(t))
                if (offset >= slot.Offset && offset < slot.Offset + slot.Size)
                    return slot;
        return null;
    }

    private Slot[] Own(TypeDef type)
    {
        if (_own.TryGetValue(type, out Slot[]? known)) return known;
        var list = new List<Slot>();
        if (type.GenericParameters.Length == 0)
        {
            foreach (PropertyDef p in type.Properties)
            {
                if (p.Getter is not { IsStatic: false } getter) continue;
                List<CustomAttribute> attributes;
                try { attributes = _blobs.ReadAttributes(type.Assembly, p.Token, p.CustomAttributeIndex); }
                catch (Exception) { continue; }
                foreach (CustomAttribute a in attributes)
                {
                    if (a.AttributeType.Name != "NetworkedWeavedAttribute" || a.Arguments.Length < 2) continue;
                    if (a.Arguments[0] is not int first || a.Arguments[1] is not int words || first < 0 || words <= 0) continue;
                    list.Add(new Slot(p, first * 4, words * 4, getter.ReturnType));
                }
            }
        }
        return _own[type] = list.ToArray();
    }
}
