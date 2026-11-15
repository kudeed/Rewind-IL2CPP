using System.Diagnostics;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Lab;

/// <summary>
/// type-stats &lt;binary&gt; &lt;signatures&gt; [assembly] [examples]: recovers every method and looks at each place a
/// value is put (assignments, arguments, returns): the kind of value the place takes against the kind it is
/// given. A number where a reference belongs, a struct where a number belongs: statements that are wrong as
/// they stand, by kind and by what the value is, with examples.
/// </summary>
public static class TypeLab
{
    private static string Kind(TypeSig? type)
    {
        switch (type)
        {
            case null: return "?";
            case ByRefSig: return "Ref";
            case PointerSig: return "Ptr";
            case GenericParamSig: return "T";
            case PrimitiveSig p:
                return p.Element switch
                {
                    Il2CppTypeEnum.Boolean or Il2CppTypeEnum.Char or Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 or Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 or
                        Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 => "I4",
                    Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 => "I8",
                    Il2CppTypeEnum.I or Il2CppTypeEnum.U => "I",
                    Il2CppTypeEnum.R4 => "F4",
                    Il2CppTypeEnum.R8 => "F8",
                    Il2CppTypeEnum.Void => "void",
                    _ => "Obj",
                };
        }
        if (type.Definition is { IsEnum: true, EnumUnderlyingType: { } underlying }) return Kind(underlying);
        if (type.IsValueType) return "VT";
        return "Obj";
    }

    private static string Shape(HExpr e) => e switch
    {
        HConst { Value: null } => "null",
        HConst c => "const " + (c.Value?.GetType().Name ?? "?"),
        HLocal l => "local " + (l.Variable.Name.TrimEnd('0', '1', '2', '3', '4', '5', '6', '7', '8', '9')),
        HArg => "argument",
        HField => "field",
        HCall => "call",
        HNewObject => "new",
        HConv c => "conv " + c.Kind,
        HBinary b => "binary " + b.Op,
        HDeref => "deref",
        HElement => "element",
        HSelect => "select",
        HTypeExpr t => "type " + t.Op,
        HOpaque o => "opaque " + o.Text,
        _ => e.GetType().Name,
    };

    private static bool Fits(string place, string value, HExpr given)
    {
        if (place == value || place is "?" or "T" or "void" || value is "?" or "T") return true;
        // A number written out goes wherever numbers go; nothing is every reference.
        if (given is HConst { Value: null }) return place is "Obj" or "Ptr" or "Ref" or "I";
        if (given is HConst && place is "I4" or "I8" or "I" && value is "I4" or "I8" or "I") return true;
        // Addresses are addresses.
        if (place is "Ptr" or "Ref" or "I" && value is "Ptr" or "Ref" or "I") return true;
        return false;
    }

    public static int Run(Il2CppModel model, string symbolsPath, string? assemblyFilter, int examplesPerKind)
    {
        ProgramAnalysis program = LiftLab.MakeProgram(model, symbolsPath);
        var pipeline = new MethodPipeline(program);
        var watch = Stopwatch.StartNew();
        var counts = new Dictionary<string, int>();
        var methods = new Dictionary<string, HashSet<string>>();
        var examples = new Dictionary<string, List<string>>();
        int total = 0, withMismatch = 0, crashed = 0;

        foreach (MethodDef method in model.Methods)
        {
            if (method.Address == 0) continue;
            if (assemblyFilter != null && method.DeclaringType.Assembly.Name != assemblyFilter) continue;
            if (method.DeclaringType.GenericParameters.Length != 0 || method.GenericParameters.Length != 0) continue;
            if (!Rewind.Output.AssemblyEmitter.HasIlBody(method)) continue;
            total++;
            HMethod h;
            try
            {
                h = pipeline.Recover(method);
            }
            catch (Exception)
            {
                crashed++;
                continue;
            }
            bool any = false;
            void Note(string where, TypeSig? place, HExpr? given, HStmt statement)
            {
                if (given == null) return;
                string wanted = Kind(place), got = Kind(given.Type);
                if (Fits(wanted, got, given)) return;
                string key = $"{where}: takes {wanted}, given {got} ({Shape(given)})";
                counts[key] = counts.GetValueOrDefault(key) + 1;
                if (!methods.TryGetValue(key, out HashSet<string>? set)) methods[key] = set = [];
                set.Add(method.FullName);
                if (!examples.TryGetValue(key, out List<string>? list)) examples[key] = list = [];
                if (list.Count < examplesPerKind) list.Add($"{method.FullName}\n          {HirPrinter.Print(statement, h).Trim()}");
                any = true;
            }
            void Calls(HStmt statement)
            {
                Rewind.Analysis.Recover.FinallyFoldingAccess.Visit(statement, e =>
                {
                    MethodDef? callee = e switch { HCall c => c.Method, HNewObject n => n.Constructor, _ => null };
                    if (callee == null || callee.DeclaringType.GenericParameters.Length != 0 || callee.GenericParameters.Length != 0) return;
                    HExpr[] arguments = e is HCall call ? call.Arguments : ((HNewObject)e).Arguments;
                    for (int i = 0; i < arguments.Length && i < callee.Parameters.Length; i++)
                        Note("argument", callee.Parameters[i].Type, arguments[i], statement);
                });
            }
            foreach (HBlock block in h.Blocks)
                foreach (HStmt statement in block.Statements)
                {
                    switch (statement)
                    {
                        case HAssign { Target: HLocal local } a: Note("variable", local.Variable.Type, a.Value, statement); break;
                        case HAssign { Target: HField field } a: Note("field", field.Type ?? field.Field.Type, a.Value, statement); break;
                        case HAssign a: Note("place", a.Target.Type, a.Value, statement); break;
                        case HReturn { Value: { } value }: Note("return", method.ReturnType, value, statement); break;
                    }
                    Calls(statement);
                }
            if (any) withMismatch++;
        }

        Console.WriteLine($"{total} methods, {withMismatch} with a value of the wrong kind somewhere, {crashed} crashed ({watch.ElapsedMilliseconds} ms)");
        foreach (var (key, count) in counts.OrderByDescending(kv => methods[kv.Key].Count).Take(60))
        {
            Console.WriteLine($"{methods[key].Count,6} methods {count,7} places  {key}");
            foreach (string example in examples[key]) Console.WriteLine("        " + example);
        }
        return 0;
    }
}
