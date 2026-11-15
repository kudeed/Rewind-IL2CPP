using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Puts inlined delegate constructors back.
///
/// "new D(target, Method)" is compiled as an allocation followed by the delegate constructor IL2CPP generates,
/// which the C++ compiler pastes in place: it fills System.Delegate's private fields (the method, the target,
/// the code pointers). After the normalizer removed the part that picks the invoke stub (see
/// Normalizer.CollapseDelegateInits), what remains are stores to those fields right after the allocation; they
/// become the constructor call again. Code cannot write those fields itself, so leaving them would not be
/// valid either way.
/// </summary>
internal static class DelegateFolding
{
    public static void Run(HMethod method, ProgramAnalysis program)
    {
        foreach (HBlock block in method.Blocks)
            for (int i = block.Statements.Count - 1; i >= 0; i--)
                if (block.Statements[i] is HAssign { Target: HLocal target, Value: HTypeExpr { Op: HTypeOp.Allocate } allocation } &&
                    IsDelegate(allocation.Target))
                    TryFold(method, block, i, target, allocation.Target, program);
        // Anything left writing those fields is a constructor that was not recognized.
        if (method.Method.DeclaringType.FullName is "System.Delegate" or "System.MulticastDelegate") return;
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
                if (s is HAssign { Target: HField field } && IsDelegateField(field.Field))
                {
                    method.Problems.Add("inlined delegate constructor not folded back");
                    return;
                }
    }

    private static bool IsDelegate(TypeSig type)
    {
        TypeDef? definition = type.Definition;
        for (int depth = 0; definition != null && depth < 8; depth++)
        {
            if (definition.FullName is "System.MulticastDelegate" or "System.Delegate") return depth > 0;
            definition = definition.BaseType?.Definition;
        }
        return false;
    }

    private static bool IsDelegateField(FieldDef field) => field.DeclaringType.FullName is "System.Delegate" or "System.MulticastDelegate";

    private static void TryFold(HMethod method, HBlock block, int at, HLocal target, TypeSig type, ProgramAnalysis program)
    {
        List<HStmt> site = block.Statements;
        HVar created = target.Variable;
        HExpr? function = null, instance = null;
        var internalStores = new List<int>();
        int end = at + 1;
        for (; end < site.Count && end - at <= 24; end++)
        {
            HStmt s = site[end];
            if (s is HAssign { Target: HField { Object: HLocal owner } field } assign && ReferenceEquals(owner.Variable, created) && IsDelegateField(field.Field))
            {
                internalStores.Add(end);
                if (field.Field.Name == "method") function = assign.Value;
                else if (field.Field.Name == "m_target") instance = assign.Value;
                else if (ConstructorFolding.Mentions(assign.Value, created) && assign.Value is not HLocal) break;
                continue;
            }
            if (ConstructorFolding.Mentions(s, created) || s is HJump or HBranch or HSwitch or HReturn or HThrow) break;
        }
        if (function is not HMethodPointer pointer || internalStores.Count == 0) return;
        TypeSig objectType = program.Model.Sigs.Primitive(Il2CppTypeEnum.Object);
        instance ??= new HConst(null, objectType);

        // Every other mention of the delegate's private fields would be left dangling.
        foreach (HBlock b in method.Blocks)
            for (int k = 0; k < b.Statements.Count; k++)
            {
                if (ReferenceEquals(b, block) && internalStores.Contains(k)) continue;
                if (MentionsDelegateField(b.Statements[k], created)) return;
            }

        TypeDef definition = type.Definition!;
        MethodDef? constructor = definition.Methods.FirstOrDefault(m => m.Name == ".ctor" && !m.IsStatic && m.Parameters.Length == 2);
        if (constructor == null) return;
        var creation = new HAssign(target, new HNewObject
        {
            Constructor = constructor,
            DeclaringType = type is GenericInstSig ? type : null,
            Arguments = [instance, pointer],
            Type = type,
        })
        { Address = site[at].Address };
        for (int k = internalStores.Count - 1; k >= 0; k--) site.RemoveAt(internalStores[k]);
        site[at] = creation;
    }

    private static bool MentionsDelegateField(HStmt statement, HVar variable) => statement switch
    {
        HAssign a => MentionsDelegateField(a.Target, variable) || MentionsDelegateField(a.Value, variable),
        HEval e => MentionsDelegateField(e.Expression, variable),
        HReturn r => MentionsDelegateField(r.Value, variable),
        HThrow t => MentionsDelegateField(t.Exception, variable),
        HBranch b => MentionsDelegateField(b.Condition, variable),
        HSwitch s => MentionsDelegateField(s.Value, variable),
        _ => false,
    };

    private static bool MentionsDelegateField(HExpr? e, HVar variable) => e switch
    {
        null => false,
        HField { Object: HLocal owner } f when ReferenceEquals(owner.Variable, variable) && IsDelegateField(f.Field) => true,
        HField f => MentionsDelegateField(f.Object, variable),
        HElement el => MentionsDelegateField(el.Array, variable) || MentionsDelegateField(el.Index, variable),
        HArrayLength len => MentionsDelegateField(len.Array, variable),
        HAddressOf a => MentionsDelegateField(a.Target, variable),
        HDeref d => MentionsDelegateField(d.Pointer, variable),
        HUnary u => MentionsDelegateField(u.Operand, variable),
        HBinary b => MentionsDelegateField(b.Left, variable) || MentionsDelegateField(b.Right, variable),
        HCompare c => MentionsDelegateField(c.Left, variable) || MentionsDelegateField(c.Right, variable),
        HConv c => MentionsDelegateField(c.Operand, variable),
        HCall call => MentionsDelegateField(call.This, variable) || call.Arguments.Any(a => MentionsDelegateField(a, variable)),
        HNewObject n => n.Arguments.Any(a => MentionsDelegateField(a, variable)),
        HNewArray na => MentionsDelegateField(na.Length, variable),
        HTypeExpr t => MentionsDelegateField(t.Operand, variable),
        HSelect s => MentionsDelegateField(s.Condition, variable) || MentionsDelegateField(s.WhenTrue, variable) || MentionsDelegateField(s.WhenFalse, variable),
        HOpaque o => o.Operands.Any(a => MentionsDelegateField(a, variable)),
        _ => false,
    };
}
