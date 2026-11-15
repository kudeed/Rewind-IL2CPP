using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Puts the field initializers of a constructor in the order the fields are declared.
///
/// "float speed = 2f; List&lt;int&gt; items = new();" become stores at the start of every constructor of the class,
/// before the base class's constructor is called, in the order the fields stand in the class. The C++ compiler
/// keeps what does work (making the list) in that order and puts the plain stores of constants wherever suits
/// it - differently in each constructor. Read back, the same initializers then stand in another order in each
/// constructor, which is not what was written, and not something a C# decompiler can show as initializers
/// again (it needs every constructor to begin with the same statements).
///
/// Before that call nothing can look at the object, so the order of stores that only compute cannot be told
/// from outside: they are put back in field order. What does work keeps its place among its like; if that is
/// not field order already, nothing is touched.
/// </summary>
internal static class InitializerOrder
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_INITIALIZER_ORDER") != null;

    /// <summary>Where the constructor of the base class (or another of this class) is called in the first block; -1 when it is not.</summary>
    internal static int BaseCall(HMethod method)
    {
        if (method.Method.Name != ".ctor" || method.Method.IsStatic || method.Blocks.Count == 0) return -1;
        List<HStmt> entry = method.Blocks[0].Statements;
        for (int k = 0; k < entry.Count; k++)
            if (entry[k] is HEval { Expression: HCall { This: HArg { Index: < 0 }, Method.Name: ".ctor" } })
                return k;
        return -1;
    }

    public static void Run(HMethod method)
    {
        if (Disabled) return;
        int call = BaseCall(method);
        if (call < 2) return;
        List<HStmt> entry = method.Blocks[0].Statements;
        TypeDef owner = method.Method.DeclaringType;
        var fields = new Dictionary<FieldDef, int>();
        int position = 0;
        foreach (FieldDef field in owner.Fields) fields[field] = position++;

        var stores = new List<(int Field, bool Computes, HStmt Statement)>();
        var seen = new HashSet<int>();
        for (int k = 0; k < call; k++)
        {
            if (entry[k] is not HAssign { Target: HField { Object: HArg { Index: < 0 } } target, Value: var value } || target.Field.IsStatic) return;
            if (!fields.TryGetValue(target.Field, out int index) || !seen.Add(index)) return;
            // An initializer cannot name the object it is for.
            bool self = false;
            FinallyFolding.Visit(value, e => self |= e is HArg { Index: < 0 });
            if (self) return;
            stores.Add((index, HirBuilder.IsPure(value), entry[k]));
        }
        // What does work stands in the order it was written: the order of the fields, or this is something else.
        int last = -1;
        foreach (var store in stores)
        {
            if (store.Computes) continue;
            if (store.Field < last) return;
            last = store.Field;
        }
        var ordered = stores.OrderBy(s => s.Field).ToList();
        for (int k = 0; k < call; k++) entry[k] = ordered[k].Statement;
    }
}
