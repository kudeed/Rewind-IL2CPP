using ICSharpCode.Decompiler.CSharp.Syntax;

namespace Rewind.Output;

/// <summary>
/// Finds C# that names a closure class it does not declare.
///
/// The C# compiler keeps the variables lambdas and local functions share in a class (or, for local functions
/// only, a struct) of its own: "&lt;&gt;c__DisplayClass12_0". The C# decompiler turns its uses back into lambdas
/// and local functions, and leaves the class out of the output - every use is expected to go. Where one does not
/// (a body it could not turn back), the output still names the class, and nothing declares it. Such a type is
/// then written with lambdas and local functions as the closure classes the compiler made: exactly what the code
/// does, and C# that compiles.
/// </summary>
internal static class ClosureCheck
{
    public static bool NamesMissingClosure(AstNode tree)
    {
        var declared = new HashSet<string>(StringComparer.Ordinal);
        foreach (TypeDeclaration t in tree.Descendants.OfType<TypeDeclaration>()) declared.Add(t.Name);
        foreach (AstNode n in tree.Descendants)
        {
            string? name = n switch
            {
                SimpleType s => s.Identifier,
                MemberType m => m.MemberName,
                _ => null,
            };
            if (name != null && IsClosure(name) && !declared.Contains(name)) return true;
        }
        return false;
    }

    private static bool IsClosure(string name) => name.StartsWith("<>c__DisplayClass", StringComparison.Ordinal);
}
