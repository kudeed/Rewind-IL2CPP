using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Internals of the core library that inlined library code leaves behind, put back as the public method that
/// stands for them.
///
/// "Array.Empty&lt;T&gt;()" does nothing but read a static field of an internal class ("EmptyArray&lt;T&gt;.Value"),
/// and the C++ compiler pastes that read in wherever it is called. The class cannot be named outside the core
/// library, so the read neither compiles nor runs in a rebuilt assembly; the call it came from does the same
/// thing and can.
/// </summary>
internal static class LibraryInternals
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_LIBRARY_INTERNALS") != null;

    public static void Run(HMethod method, ProgramAnalysis program)
    {
        if (Disabled) return;
        MethodDef? empty = null;
        bool looked = false;
        HExpr? Map(HExpr e)
        {
            switch (e)
            {
                // Its address is something else: left alone.
                case HAddressOf { Target: HField f } when IsEmptyArray(f):
                    return e;
                case HField { Object: null, DeclaringType: GenericInstSig { Arguments: [var element] } } f when IsEmptyArray(f):
                    if (!looked)
                    {
                        looked = true;
                        empty = program.Model.FindType("System.Array")?.Methods.FirstOrDefault(m =>
                            m.Name == "Empty" && m.IsStatic && m.GenericParameters.Length == 1 && m.Parameters.Length == 0);
                    }
                    return empty == null ? null : new HCall { Method = empty, MethodArguments = [element], Type = f.Type };
                default:
                    return null;
            }
        }
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
            {
                // Only reads: a store into the field (never written outside the library) stays as it is.
                if (s is HAssign { Target: HField target } assign && IsEmptyArray(target))
                {
                    assign.Value = EnumeratorLoops.Rewrite(assign.Value, Map);
                    continue;
                }
                EnumeratorLoops.Rewrite(s, Map);
            }
    }

    private static bool IsEmptyArray(HField f) =>
        f.Field.IsStatic && f.Field.Name == "Value" && f.Field.DeclaringType is { Name: "EmptyArray`1", Namespace: "System" };
}
