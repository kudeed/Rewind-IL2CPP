using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// The compiler shares the last call of inlined wrappers by merging their scalar arguments first.
/// Put that one consumer back at the end of every incoming path, where InlineFolding can compare
/// the complete expression with the original public method. No access is made legal by this pass:
/// every field read and call stays, in the same order, until a complete wrapper is proved.
/// </summary>
internal static class MergedInlineArguments
{
    public static bool Run(HMethod method)
    {
        if (method.TryRegions.Count != 0 || method.Blocks.Count is < 3 or > 512 ||
            method.Blocks.Any(b => b.Scope != -1)) return false;
        bool changed = false;
        for (int round = 0; round < 32; round++)
        {
            bool one = false;
            foreach (HBlock join in method.Blocks.Skip(1))
                if (TrySplit(method, join)) { changed = one = true; break; }
            if (!one) break;
        }
        return changed;
    }

    private static bool Scalar(TypeSig? type) => type is PrimitiveSig { Element:
        Il2CppTypeEnum.Boolean or Il2CppTypeEnum.Char or Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 or
        Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 or Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 or
        Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 or Il2CppTypeEnum.R4 or Il2CppTypeEnum.R8 };

    private static bool SameType(TypeSig? left, TypeSig? right) =>
        left != null && right != null && left.Key == right.Key;

    private static IEnumerable<HBlock> Successors(HBlock block) => block.Statements.LastOrDefault() switch
    {
        HJump jump => [jump.Target],
        HBranch branch => [branch.WhenTrue, branch.WhenFalse],
        HSwitch choice => [.. choice.Targets, choice.Default],
        _ => [],
    };

    // A phi's expression view can be unannotated after its declaration has acquired the input type.
    // Use that declaration only when the view does not contradict it; no new type is inferred here.
    private static TypeSig? TypeOf(HExpr expression) => expression.Type ?? (expression is HLocal local ? local.Variable.Type : null);

    private static bool DeclaredLocal(HLocal local) =>
        SameType(TypeOf(local), local.Variable.Type) && local.Variable.Type is not (ByRefSig or PointerSig or OpaqueSig);

    private static bool StableLocal(HLocal local) => !local.Variable.AddressTaken && DeclaredLocal(local);

    // A value read at exactly its former position. Calls, native loads, addresses, static fields and
    // checked operations are deliberately excluded; no hidden write can change a later argument.
    private static bool Read(HExpr value, HashSet<HVar> merging, HashSet<HVar> observed, int depth = 0)
    {
        if (depth > 32 || !Scalar(TypeOf(value))) return false;
        switch (value)
        {
            case HConst constant:
                return constant.Value is bool or char or sbyte or byte or short or ushort or int or uint or long or ulong or float or double;
            case HLocal local:
                if (!StableLocal(local) || merging.Contains(local.Variable)) return false;
                observed.Add(local.Variable);
                return true;
            case HArg { Index: >= 0 }:
                return true;
            case HField { Object: HLocal receiver } field:
                if (field.Field.IsStatic || !StableLocal(receiver) || TypeOf(receiver) is not { IsValueType: false } ||
                    !SameType(field.Type, field.Field.Type) || !SameType(TypeOf(receiver), field.Field.DeclaringType.Sig)) return false;
                observed.Add(receiver.Variable);
                return true;
            case HUnary unary:
                return Read(unary.Operand, merging, observed, depth + 1);
            case HBinary binary when binary.Op is HBinaryOp.Add or HBinaryOp.Sub or HBinaryOp.Mul or
                HBinaryOp.And or HBinaryOp.Or or HBinaryOp.Xor or HBinaryOp.Shl or HBinaryOp.Shr or HBinaryOp.ShrUn:
                return Read(binary.Left, merging, observed, depth + 1) && Read(binary.Right, merging, observed, depth + 1);
            case HCompare compare:
                return Read(compare.Left, merging, observed, depth + 1) && Read(compare.Right, merging, observed, depth + 1);
            case HConv convert when convert.Kind is HConvKind.I1 or HConvKind.U1 or HConvKind.I2 or HConvKind.U2 or
                HConvKind.I4 or HConvKind.U4 or HConvKind.I8 or HConvKind.U8 or HConvKind.R4 or HConvKind.R8 or HConvKind.RUn:
                return Read(convert.Operand, merging, observed, depth + 1);
            default:
                return false;
        }
    }

    private static bool TrySplit(HMethod method, HBlock join)
    {
        if (join.Statements.Count == 0) return false;
        HStmt use = join.Statements[0];
        HStmt distributed = use;
        HStmt? remaining = null;
        HVar? temporary = null;
        // A clean CoreBody may already inline "s = new S(phi...); F(s)" into F(new S(phi...)).
        // With one argument and a static receiver there is no earlier argument evaluation to cross:
        // distribute only the construction, and keep the enclosing call at its original join position.
        if (use is HAssign { Target: HLocal assigned, Value: HCall { Arguments: [HNewObject nested] } outer } &&
            StableLocal(assigned) && outer.This == null && outer.Method.IsStatic && !outer.Method.IsConstructor &&
            !outer.Virtual && !outer.Method.IsVirtual && outer.Constrained == null && outer.Alternatives.Count == 0 &&
            outer.MethodArguments.Length == 0 && outer.Method.GenericParameters.Length == 0 &&
            outer.Method.DeclaringType.GenericParameters.Length == 0 && outer.Method.Parameters.Length == 1 &&
            SameType(outer.Method.Parameters[0].Type, nested.Type) && SameType(outer.Type, outer.Method.ReturnType) &&
            SameType(TypeOf(assigned), outer.Type) && nested.Type is { } nestedType)
        {
            temporary = new HVar { Index = method.Locals.Count, Name = "mergedStruct" + method.Locals.Count, Type = nestedType };
            distributed = new HAssign(new HLocal(temporary) { Type = nestedType }, nested) { Address = use.Address };
            remaining = HirCopy.Of(use, e => ReferenceEquals(e, nested) ? new HLocal(temporary) { Type = nestedType } : null);
            if (remaining == null) return false;
        }
        HExpr[] arguments;
        MethodDef consumer;
        var observed = new HashSet<HVar>();
        bool inaccessible = false;
        switch (distributed)
        {
            case HEval { Expression: HCall call } when !call.Virtual && call.Constrained == null &&
                call.Alternatives.Count == 0 && call.MethodArguments.Length == 0 && !call.Method.IsVirtual &&
                call.Type is PrimitiveSig { Element: Il2CppTypeEnum.Void } && SameType(call.Type, call.Method.ReturnType) && !call.Method.IsConstructor:
                if (call.Method.IsStatic ? call.This != null :
                    call.This is not HLocal receiver || !StableLocal(receiver) || TypeOf(receiver) is not { IsValueType: false } ||
                    !SameType(TypeOf(receiver), call.Method.DeclaringType.Sig)) return false;
                if (call.This is HLocal instance) observed.Add(instance.Variable);
                consumer = call.Method;
                arguments = call.Arguments;
                inaccessible = !InlineFolding.IsAccessible(consumer, method.Method);
                break;
            case HAssign { Target: HLocal output, Value: HNewObject creation } when
                DeclaredLocal(output) && creation.Constructor.IsConstructor && !creation.Constructor.IsStatic &&
                creation.Constructor.DeclaringType.IsValueType && SameType(TypeOf(output), creation.Type) &&
                SameType(creation.Type, creation.Constructor.DeclaringType.Sig):
                consumer = creation.Constructor;
                arguments = creation.Arguments;
                // Struct construction may leave the former frame local marked AddressTaken after its
                // address expressions were folded away. The full-method address scan below still applies.
                observed.Add(output.Variable);
                break;
            default:
                return false;
        }
        if (consumer.GenericParameters.Length != 0 || consumer.DeclaringType.GenericParameters.Length != 0 ||
            arguments.Length is < 1 or > 8 || consumer.Parameters.Length != arguments.Length) return false;
        var variables = new List<HVar>();
        for (int i = 0; i < arguments.Length; i++)
        {
            if (arguments[i] is not HLocal local || !StableLocal(local) || !Scalar(TypeOf(local)) ||
                !SameType(TypeOf(local), consumer.Parameters[i].Type) || variables.Contains(local.Variable) ||
                observed.Contains(local.Variable)) return false;
            variables.Add(local.Variable);
        }
        var merging = variables.ToHashSet();
        var incoming = method.Blocks.Where(b => Successors(b).Contains(join)).ToList();
        if (incoming.Count is < 2 or > 8 || incoming.Contains(join)) return false;
        // No implicit entry or malformed edge, and no consumer on a loop's back edge.
        if (method.Blocks.Any(b => Successors(b).Any(next => !method.Blocks.Contains(next)))) return false;
        var reached = new HashSet<HBlock>();
        var pending = new Stack<HBlock>(Successors(join));
        while (pending.TryPop(out HBlock? next))
        {
            if (incoming.Contains(next) || ReferenceEquals(next, join)) return false;
            if (reached.Add(next)) foreach (HBlock later in Successors(next)) pending.Push(later);
        }
        var tails = new List<(HBlock Block, int Start, HAssign[] Assignments)>();
        foreach (HBlock before in incoming)
        {
            if (before.Statements.LastOrDefault() is not HJump jump || !ReferenceEquals(jump.Target, join)) return false;
            int start = before.Statements.Count - variables.Count - 1;
            if (start < 0) return false;
            var assignments = new HAssign[variables.Count];
            for (int i = 0; i < variables.Count; i++)
            {
                if (before.Statements[start + i] is not HAssign { Target: HLocal target } assignment ||
                    !ReferenceEquals(target.Variable, variables[i]) || !SameType(TypeOf(target), target.Variable.Type) ||
                    !SameType(TypeOf(assignment.Value), TypeOf(target)) || !Read(assignment.Value, merging, observed)) return false;
                assignments[i] = assignment;
                FinallyFolding.Visit(assignment.Value, e =>
                {
                    if (e is HField field && !AccessorFolding.IsAccessible(field.Field, method.Method)) inaccessible = true;
                });
            }
            tails.Add((before, start, assignments));
        }
        if (!inaccessible) return false;
        // Each merged scalar is used once, by this consumer, and assigned exactly on the proven incoming paths.
        var allowed = tails.SelectMany(t => t.Assignments).ToHashSet();
        var reads = variables.ToDictionary(v => v, _ => 0);
        var writes = variables.ToDictionary(v => v, _ => 0);
        bool unexpected = false;
        foreach (HBlock block in method.Blocks)
            foreach (HStmt statement in block.Statements)
            {
                HLocal? target = statement is HAssign { Target: HLocal local } ? local : null;
                FinallyFolding.Visit(statement, e =>
                {
                    if (e is HAddressOf address)
                        FinallyFolding.Visit(address.Target, pointed =>
                        {
                            if (pointed is HLocal local && (merging.Contains(local.Variable) || observed.Contains(local.Variable))) unexpected = true;
                        });
                    if (e is not HLocal named || !merging.Contains(named.Variable)) return;
                    if (ReferenceEquals(e, target))
                    {
                        writes[named.Variable]++;
                        if (statement is not HAssign assignment || !allowed.Contains(assignment)) unexpected = true;
                    }
                    else
                    {
                        reads[named.Variable]++;
                        if (!ReferenceEquals(statement, use)) unexpected = true;
                    }
                });
            }
        if (unexpected || variables.Any(v => reads[v] != 1 || writes[v] != incoming.Count)) return false;
        var copies = new List<HStmt>();
        foreach (var (_, _, assignments) in tails)
        {
            var values = variables.Select((v, i) => (v, Value: assignments[i].Value)).ToDictionary(p => p.v, p => p.Value);
            HExpr? Map(HExpr expression) => expression is HLocal local && values.TryGetValue(local.Variable, out HExpr? value)
                ? HirCopy.Of(value) : null;
            if (HirCopy.Of(distributed, Map) is not { } copy) return false;
            copies.Add(copy);
        }
        for (int i = 0; i < tails.Count; i++)
        {
            var (block, start, _) = tails[i];
            block.Statements.RemoveRange(start, variables.Count);
            block.Statements.Insert(start, copies[i]);
        }
        if (remaining != null)
        {
            method.Locals.Add(temporary!);
            join.Statements[0] = remaining;
        }
        else join.Statements.RemoveAt(0);
        return true;
    }
}
