using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Puts the making of a struct back into one expression.
///
/// "new Keyframe(0.65f, 0.25f)" is compiled as: a temporary cleared, the constructor run on it, the temporary
/// used. Translated statement by statement that is "k = default; k..ctor(0.65f, 0.25f);" - the same thing, but
/// two statements where the source had an expression, and with the clearing left standing on its own once the
/// rest is read as "new".
/// </summary>
internal static class StructConstruction
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_CONSTRUCTION") != null;

    public static bool Run(HMethod method)
    {
        if (Disabled) return false;
        bool any = false;
        foreach (HBlock block in method.Blocks)
        {
            List<HStmt> s = block.Statements;
            for (int i = 0; i + 1 < s.Count; i++)
            {
                if (s[i] is not HAssign { Target: HLocal { Variable: var made } target, Value: HTypeExpr { Op: HTypeOp.Default } }) continue;
                if (s[i + 1] is not HEval { Expression: HCall { Method: { Name: ".ctor", IsStatic: false } constructor, This: { } on } call }) continue;
                HExpr receiver = on is HAddressOf { Target: var inner } ? inner : on;
                if (receiver is not HLocal { Variable: var same } || !ReferenceEquals(same, made)) continue;
                if (!constructor.DeclaringType.IsValueType || !ReferenceEquals(made.Type.Definition, constructor.DeclaringType)) continue;
                if (call.Arguments.Any(a => ConstructorFolding.Mentions(a, made))) continue;
                s[i] = new HAssign(target, new HNewObject
                {
                    Constructor = constructor,
                    DeclaringType = made.Type is GenericInstSig ? made.Type : null,
                    Arguments = call.Arguments,
                    Type = made.Type,
                })
                { Address = s[i].Address };
                s.RemoveAt(i + 1);
                any = true;
            }
        }
        return any;
    }
}
