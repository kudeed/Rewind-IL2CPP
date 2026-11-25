using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// A bounded method-metadata lookup can merge code pointers just before
/// constructing a static delegate. CLI can represent such a pointer merge,
/// but C# cannot spell it. Move delegate construction into the leaves of
/// the choice, retaining exactly one allocation on the selected path.
/// Only a closed, pure, single-use return diamond is accepted.
/// </summary>
internal static class DelegateChoiceFolding
{
    private static bool Scalar(HExpr e, HVar pointer) => e switch
    {
        HConst { Value: int or long or bool } => true,
        HArg { Index: >= 0 } => true,
        HLocal l => !ReferenceEquals(l.Variable, pointer) && !l.Variable.AddressTaken,
        HCompare c => Scalar(c.Left, pointer) && Scalar(c.Right, pointer),
        HConv c when c.Kind < HConvKind.OvfI1 => Scalar(c.Operand, pointer),
        HUnary u => Scalar(u.Operand, pointer),
        HBinary { Op: HBinaryOp.Add or HBinaryOp.Sub or HBinaryOp.And or HBinaryOp.Or or HBinaryOp.Xor } b =>
            Scalar(b.Left, pointer) && Scalar(b.Right, pointer),
        _ => false
    };

    internal static HExpr? MakeChoice(HExpr expr, HNewObject template, MethodDef invoke, HVar pointer, ref int leaves, int depth = 0)
    {
        if (depth > 8 || leaves >= 128) return null;
        if (expr is HMethodPointer { VirtualOn: null, MethodArguments.Length: 0, DeclaringType: null } p)
        {
            MethodDef m = p.Method;
            if (!m.IsStatic || m.IsVirtual || m.IsAbstract || m.IsConstructor || m.Address == 0 ||
                m.IsGenericDefinition || m.DeclaringType.GenericParameters.Length != 0 ||
                m.ReturnType.Key != invoke.ReturnType.Key || m.Parameters.Length != invoke.Parameters.Length ||
                !m.Parameters.Zip(invoke.Parameters).All(q => q.First.Type.Key == q.Second.Type.Key))
                return null;
            leaves++;
            return new HNewObject { Constructor = template.Constructor, DeclaringType = template.DeclaringType,
                Type = template.Type, Arguments = [template.Arguments[0], p] };
        }
        if (expr is not HSelect s || !Scalar(s.Condition, pointer)) return null;
        HExpr? yes = MakeChoice(s.WhenTrue, template, invoke, pointer, ref leaves, depth + 1);
        if (yes == null) return null;
        HExpr? no = MakeChoice(s.WhenFalse, template, invoke, pointer, ref leaves, depth + 1);
        return no == null ? null : new HSelect(s.Condition, yes, no) { Type = template.Type };
    }

    public static void Run(HMethod method)
    {
        if (Environment.GetEnvironmentVariable("REWIND_NO_DELEGATE_CHOICE_FOLDING") != null ||
            method.TryRegions.Count != 0 || method.Blocks.Any(b => b.Scope != -1) || method.Blocks.Count < 3) return;
        // A precise CFG pattern: each predecessor assigns the same pointer
        // local and unconditionally jumps to a final block that consumes it
        // exactly once in new D(null,p), then returns that new object.
        foreach (HBlock join in method.Blocks.ToArray())
        {
            if (ReferenceEquals(join,method.Blocks[0])) continue;
            if (join.Statements is not [HAssign { Target: HLocal obj, Value: HNewObject creation } assignment, HReturn { Value: HLocal returned }] ||
                !ReferenceEquals(obj.Variable, returned.Variable) || obj.Variable.AddressTaken ||
                creation.Arguments is not [HConst { Value: null }, HLocal function] || function.Variable.AddressTaken ||
                ReferenceEquals(obj.Variable,function.Variable) ||
                creation.Type?.Definition is not { IsDelegate: true } definition ||
                creation.Type is not TypeDefSig || definition.GenericParameters.Length != 0 ||
                creation.Constructor.DeclaringType != definition || creation.Constructor.Name != ".ctor" ||
                creation.Constructor.IsStatic || creation.Constructor.Parameters.Length != 2 ||
                creation.Constructor.Parameters[0].Type is not PrimitiveSig { Element: Il2CppTypeEnum.Object } ||
                creation.Constructor.Parameters[1].Type is not PrimitiveSig { Element: Il2CppTypeEnum.I } ||
                method.Method.ReturnType.Key != creation.Type.Key)
                continue;
            var invokes = definition.Methods.Where(m => m.Name == "Invoke" && !m.IsStatic).ToArray();
            if (invokes.Length != 1) continue;
            var incoming = new List<HBlock>();
            bool invalid = false;
            foreach (HBlock b in method.Blocks)
            {
                foreach (HStmt statement in b.Statements)
                {
                    if (statement is HJump jump && ReferenceEquals(jump.Target,join))
                    {
                        if (!ReferenceEquals(statement,b.Statements.Last()) || b == join) invalid = true;
                        incoming.Add(b);
                    }
                    else if (statement is HBranch branch && (ReferenceEquals(branch.WhenTrue,join) || ReferenceEquals(branch.WhenFalse,join)) ||
                             statement is HSwitch sw && (ReferenceEquals(sw.Default,join) || sw.Targets.Contains(join)))
                        invalid = true;
                }
            }
            if (invalid || incoming.Count is < 2 or > 16 || incoming.Distinct().Count()!=incoming.Count) continue;
            var changes = new List<(HBlock Block, HAssign Assign, HExpr Value)>();
            int leaves = 0;
            foreach (HBlock pred in incoming)
            {
                if (pred.Statements is not [HAssign { Target: HLocal local } set, HJump] ||
                    !ReferenceEquals(local.Variable,function.Variable)) { invalid = true; break; }
                HExpr? value = MakeChoice(set.Value,creation,invokes[0],function.Variable,ref leaves);
                if (value == null) { invalid = true; break; }
                changes.Add((pred,set,value));
            }
            if (invalid || leaves < 2) continue;
            // Neither local may be mentioned by any other statement.
            var allowed = changes.Select(c => (HStmt)c.Assign).Append(assignment).Append(join.Statements[1]).ToHashSet();
            if (method.Blocks.SelectMany(b=>b.Statements).Any(s=>!allowed.Contains(s) &&
                (ConstructorFolding.Mentions(s,obj.Variable)||ConstructorFolding.Mentions(s,function.Variable)))) continue;
            foreach (var c in changes)
                c.Block.Statements = [new HReturn(c.Value) { Address = assignment.Address }];
            method.Blocks.Remove(join);
            method.Locals.Remove(function.Variable);
            method.Locals.Remove(obj.Variable);
            method.Notes.Add($"static delegate choice: {leaves} proven method leaves");
            return;
        }
    }
}
