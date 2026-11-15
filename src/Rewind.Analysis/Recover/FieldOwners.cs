using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Gives each field access the class the field is declared in, as the object's class instantiates it.
///
/// A field is found by its place in the object, whatever class of the hierarchy declares it; the access is
/// built with the class of the object at hand. For a field of a generic base class that is the wrong one to
/// name: "sheet._resources" with sheet an OreDataSheet is a field of ResourceSheet&lt;OreData&gt;, and what
/// follows - the accessor a private field is read through, the methods of the base that were pasted in -
/// is looked up by that class.
/// </summary>
internal static class FieldOwners
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_FIELD_OWNERS") != null;

    public static void Run(HMethod method, Il2CppModel model)
    {
        if (Disabled) return;
        void Fix(HExpr e)
        {
            if (e is not HField { DeclaringType: { } named } f) return;
            TypeDef declared = f.Field.DeclaringType;
            if (ReferenceEquals(named.Definition, declared)) return;
            TypeSig? t = named;
            for (int depth = 0; depth < 32 && t?.Definition != null; depth++)
            {
                TypeDef definition = t.Definition;
                if (ReferenceEquals(definition, declared))
                {
                    f.DeclaringType = t;
                    return;
                }
                if (definition.BaseType == null) return;
                t = model.Sigs.Substitute(definition.BaseType, t is GenericInstSig g ? g.Arguments : [], []);
            }
        }
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
                FinallyFolding.Visit(s, Fix);
    }
}
