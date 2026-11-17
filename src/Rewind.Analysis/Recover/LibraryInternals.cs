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
///
/// "a == b" of two strings is a method of its own ("String.op_Equality") that does nothing but call
/// "String.Equals(a, b)", which is what is left where it was pasted in. The two do the same; nearly all source
/// says "==", and a "switch" over strings is recognized by it (the compiler writes one as a run of "==" behind a
/// test of the string's hash).
/// </summary>
internal static class LibraryInternals
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_LIBRARY_INTERNALS") != null;
    private static readonly bool NoStringEquality = Environment.GetEnvironmentVariable("REWIND_NO_STRING_EQUALITY") != null;

    public static void Run(HMethod method, ProgramAnalysis program)
    {
        if (Disabled) return;
        MethodDef? empty = null;
        bool looked = false;
        // (Not in the string class itself: "==" there is the method that makes this call.)
        bool strings = !NoStringEquality && method.Method.DeclaringType.FullName != "System.String";
        MethodDef? equality = null;
        bool lookedEquality = false;
        HExpr? Map(HExpr e)
        {
            switch (e)
            {
                case HCall { This: null, Arguments.Length: 2 } call when strings && IsStringEquals(call.Method):
                    if (!lookedEquality)
                    {
                        lookedEquality = true;
                        equality = StringEquality(program);
                    }
                    // (In place: what it compares is looked at like anything else. Where the two methods are one
                    // function in the image, "==" is among the methods the call may be, and they change places.)
                    if (equality != null && (call.Alternatives.Count == 0 || call.Alternatives.Contains(equality)))
                    {
                        if (call.Alternatives.Remove(equality)) call.Alternatives.Add(call.Method);
                        call.Method = equality;
                    }
                    return null;
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
        if (equality != null) SplitSharedTests(method, equality);
    }

    /// <summary>
    /// Cases of a "switch" over strings that lead to the same code ("case "a": case "b":") each compare the
    /// string with their own text, and the C++ compiler made one comparison of them: each case puts its text in a
    /// variable and jumps to the comparison they share. Each case gets its comparison back, with its own text
    /// (the shape a "switch" over strings is recognized by).
    /// </summary>
    private static void SplitSharedTests(HMethod method, MethodDef equality)
    {
        for (int index = 1; index < method.Blocks.Count; index++)
        {
            HBlock shared = method.Blocks[index];
            if (shared.Statements is not [HBranch test]) continue;
            int negations = 0;
            HExpr asked = test.Condition;
            while (asked is HUnary { Op: HUnaryOp.LogicalNot, Operand: var inner })
            {
                asked = inner;
                negations++;
            }
            if (asked is not HCall { This: null, Arguments: [var subject, HLocal { Variable: var text }] } call || !ReferenceEquals(call.Method, equality)) continue;
            if (subject is not (HLocal or HArg) || (subject is HLocal { Variable: var compared } && ReferenceEquals(compared, text))) continue;
            if (method.TryRegions.Values.Any(r => ReferenceEquals(r.Entry, shared) || ReferenceEquals(r.HandlerEntry, shared))) continue;

            // Who comes here: only jumps, each right behind "text = "...";".
            var from = new List<HBlock>();
            bool otherwise = false;
            int mentions = 0;
            foreach (HBlock b in method.Blocks)
            {
                foreach (HStmt s in b.Statements)
                    if (ConstructorFolding.Mentions(s, text))
                        mentions++;
                if (b.Statements.Count == 0) continue;
                switch (b.Statements[^1])
                {
                    case HJump jump when ReferenceEquals(jump.Target, shared):
                        if (b.Scope == shared.Scope && b.Statements.Count >= 2 &&
                            b.Statements[^2] is HAssign { Target: HLocal { Variable: var set }, Value: HConst { Value: string } } && ReferenceEquals(set, text))
                            from.Add(b);
                        else otherwise = true;
                        break;
                    case HBranch branch when ReferenceEquals(branch.WhenTrue, shared) || ReferenceEquals(branch.WhenFalse, shared):
                        otherwise = true;
                        break;
                    case HSwitch choice when ReferenceEquals(choice.Default, shared) || choice.Targets.Any(t => ReferenceEquals(t, shared)):
                        otherwise = true;
                        break;
                }
            }
            // (The variable is nothing but the text on its way to the comparison.)
            if (otherwise || from.Count < 2 || mentions != from.Count + 1) continue;

            foreach (HBlock b in from)
            {
                var own = (HAssign)b.Statements[^2];
                HExpr same = subject is HLocal local ? new HLocal(local.Variable) { Type = local.Type } : new HArg(((HArg)subject).Index) { Type = subject.Type };
                HExpr question = new HCall { Method = equality, Arguments = [same, own.Value], Type = call.Type };
                for (int i = 0; i < negations; i++) question = new HUnary(HUnaryOp.LogicalNot, question) { Type = call.Type };
                ulong address = b.Statements[^1].Address;
                b.Statements.RemoveRange(b.Statements.Count - 2, 2);
                b.Statements.Add(new HBranch(question, test.WhenTrue, test.WhenFalse) { Address = address });
            }
            method.Blocks.RemoveAt(index--);
            method.Locals.Remove(text);
        }
    }

    private static bool IsString(TypeSig type) => type is PrimitiveSig { Element: Rewind.Runtime.Il2CppTypeEnum.String };

    private static bool IsStringEquals(MethodDef m) =>
        m.Name == "Equals" && m.IsStatic && m.GenericParameters.Length == 0 && m.Parameters.Length == 2 && m.DeclaringType.FullName == "System.String" &&
        IsString(m.Parameters[0].Type) && IsString(m.Parameters[1].Type);

    private static MethodDef? StringEquality(ProgramAnalysis program) =>
        program.Model.FindType("System.String")?.Methods.FirstOrDefault(m =>
            m.Name == "op_Equality" && m.IsStatic && m.Parameters.Length == 2 && IsString(m.Parameters[0].Type) && IsString(m.Parameters[1].Type));

    private static bool IsEmptyArray(HField f) =>
        f.Field.IsStatic && f.Field.Name == "Value" && f.Field.DeclaringType is { Name: "EmptyArray`1", Namespace: "System" };
}
