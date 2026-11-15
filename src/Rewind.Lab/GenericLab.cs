using System.Diagnostics;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Lab;

/// <summary>
/// generic-try &lt;binary&gt; &lt;signatures&gt; [assembly|-] [name filter|-] [how many to print]: every method of a
/// generic type and every generic method that has an IL body, recovered from the compiled body that its
/// instantiations over reference types share, with its own type parameters as the type arguments. Says how
/// many have such a body, how many are recovered completely that way, and prints some.
/// </summary>
public static class GenericLab
{
    private static bool IsObject(TypeSig t) => t is PrimitiveSig { Element: Il2CppTypeEnum.Object };

    public static int Run(Il2CppModel model, string symbolsPath, string? assembly, string? filter, int print)
    {
        ProgramAnalysis program = LiftLab.MakeProgram(model, symbolsPath);
        var pipeline = new MethodPipeline(program);
        var watch = Stopwatch.StartNew();
        int total = 0, withShared = 0, clean = 0, crashed = 0, shown = 0, onlyValueTypes = 0, none = 0;
        var problems = new Dictionary<string, int>();
        foreach (MethodDef method in model.Methods)
        {
            if (method.DeclaringType.GenericParameters.Length == 0 && method.GenericParameters.Length == 0) continue;
            if (assembly != null && method.DeclaringType.Assembly.Name != assembly) continue;
            if (filter != null && !method.FullName.Contains(filter, StringComparison.Ordinal)) continue;
            if (!Rewind.Output.AssemblyEmitter.HasIlBody(method)) continue;
            total++;
            MethodInst? shared = null;
            bool any = false;
            foreach (MethodInst inst in program.InstsOf(method))
            {
                if (inst.Address == 0) continue;
                any = true;
                if (inst.ClassArguments.All(IsObject) && inst.MethodArguments.All(IsObject))
                {
                    shared = inst;
                    break;
                }
            }
            if (shared == null)
            {
                if (any) onlyValueTypes++;
                else none++;
                continue;
            }
            withShared++;
            var open = new MethodInst
            {
                Method = method,
                ClassArguments = method.DeclaringType.GenericParameters.Select(p => (TypeSig)model.Sigs.GenericParam(p)).ToArray(),
                MethodArguments = method.GenericParameters.Select(p => (TypeSig)model.Sigs.GenericParam(p)).ToArray(),
                Address = shared.Address,
            };
            try
            {
                HMethod h = pipeline.Recover(open);
                if (h.Problems.Count == 0) clean++;
                foreach (string problem in h.Problems.Distinct())
                {
                    string key = System.Text.RegularExpressions.Regex.Replace(problem, @"%\d+|\d+", "N");
                    problems[key] = problems.GetValueOrDefault(key) + 1;
                }
                if (shown++ < print)
                {
                    Console.WriteLine($"// shared body at 0x{shared.Address:X}");
                    Console.WriteLine(HirPrinter.Print(h));
                    foreach (string problem in h.Problems.Distinct().Take(6)) Console.WriteLine("  ! " + problem);
                }
            }
            catch (Exception e)
            {
                crashed++;
                if (shown++ < print) Console.WriteLine($"{method.FullName}: {e.GetType().Name}: {e.Message}");
            }
        }
        Console.WriteLine($"{total} generic methods with IL bodies: {withShared} with a body shared by reference types ({clean} recovered completely, {crashed} crashed), " +
                          $"{onlyValueTypes} compiled for value types only, {none} not compiled at all ({watch.ElapsedMilliseconds} ms)");
        Console.WriteLine($"named copies: {program.NamedChecks} checked, {program.NamedCopies} found ({program.NamedCheckTime} ms)");
        foreach (var (key, count) in problems.OrderByDescending(kv => kv.Value).Take(25)) Console.WriteLine($"{count,6}  {key}");
        return 0;
    }
}
