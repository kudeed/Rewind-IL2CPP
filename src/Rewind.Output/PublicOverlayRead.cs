using Mono.Cecil;
using Mono.Cecil.Cil;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Output;

/// <summary>
/// Recover the inaccessible Color32 integer overlay through the four public
/// bytes. Require the original explicit-layout metadata, not a guessed
/// correspondence of names. The caller supplies the already evaluated struct
/// exactly once; the emitted integer is the original little-endian word.
/// </summary>
internal static class PublicOverlayRead
{
    internal static bool TryColor32(FieldDef packed, TypeSig? owner, int header, out FieldDef[] channels)
    {
        channels = [];
        var t = packed.DeclaringType;
        if (owner is not TypeDefSig || !ReferenceEquals(owner.Definition,t) ||
            t.ReflectionName != "UnityEngine.Color32" || t.Assembly.Name != "UnityEngine.CoreModule" ||
            !t.IsValueType || t.IsEnum || t.GenericParameters.Length != 0 ||
            (t.Flags & TypeDef.LayoutMask) != TypeDef.ExplicitLayout ||
            t.Sizes.InstanceSize != header + 4 ||
            packed.Name != "rgba" || packed.IsStatic || (packed.Attrs & FieldDef.AccessMask) == 6 ||
            packed.Offset != header || packed.Type is not PrimitiveSig {Element:Il2CppTypeEnum.I4})
            return false;
        var fields=t.Fields.Where(f=>!f.IsStatic).ToArray();
        if(fields.Length!=5||!fields.Contains(packed))return false;
        var result=new FieldDef[4];
        string[] names=["r","g","b","a"];
        for(int i=0;i<4;i++)
        {
            var hits=fields.Where(f=>f.Name==names[i]).ToArray();
            if(hits.Length!=1 || hits[0].Offset!=header+i || (hits[0].Attrs&FieldDef.AccessMask)!=6 ||
                hits[0].Type is not PrimitiveSig {Element:Il2CppTypeEnum.U1})return false;
            result[i]=hits[0];
        }
        channels=result;
        return true;
    }

    internal static void Emit(ILProcessor il, VariableDefinition snapshot, FieldReference[] channels)
    {
        if(channels.Length!=4)throw new ArgumentException("expected four byte channels");
        // Stack initially has one struct value. Snapshot before accessing
        // channels, preserving evaluation count of property/call receivers.
        il.Emit(OpCodes.Stloc,snapshot);
        for(int i=0;i<4;i++)
        {
            il.Emit(OpCodes.Ldloca,snapshot);
            il.Emit(OpCodes.Ldfld,channels[i]);
            if(i!=0)
            {
                il.Emit(OpCodes.Ldc_I4,i*8);
                il.Emit(OpCodes.Shl);
                il.Emit(OpCodes.Or);
            }
        }
    }
}
