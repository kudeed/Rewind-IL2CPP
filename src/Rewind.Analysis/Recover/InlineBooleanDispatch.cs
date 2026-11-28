using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Recovers a wrapper which chooses one of two producers with a boolean and passes its result to one
/// consumer. A constant branch can leave only consumer(producer()) at the site, without the wrapper's
/// branch-merge temporaries. Every statement of both original paths must fit this shape.
/// </summary>
internal static class InlineBooleanDispatch
{
    internal static bool TryFold(HMethod caller, HMethod body, HStmt site, out HCall? folded)
    {
        folded = null;
        MethodDef wrapper = body.Method;
        if (body.Problems.Count != 0 || body.TryRegions.Count != 0 || body.Blocks.Count != 4 ||
            body.Blocks.Any(block => block.Scope != -1) || wrapper.IsStatic || wrapper.IsVirtual || wrapper.IsConstructor ||
            wrapper.GenericParameters.Length != 0 || wrapper.DeclaringType.GenericParameters.Length != 0 ||
            wrapper.DeclaringType.IsValueType || !wrapper.ReturnType.IsVoid ||
            wrapper.Parameters is not [{ Type: PrimitiveSig { Element: Il2CppTypeEnum.Boolean } }] ||
            (wrapper.Flags & MethodDef.AccessMask) != 6 ||
            body.Blocks[0].Statements is not [HBranch branch]) return false;

        HExpr condition = branch.Condition;
        bool reversed = false;
        if (condition is HUnary { Op: HUnaryOp.LogicalNot } negated) { condition = negated.Operand; reversed = true; }
        if (condition is not HArg { Index: 0 }) return false;
        HBlock whenTrue = reversed ? branch.WhenFalse : branch.WhenTrue;
        HBlock whenFalse = reversed ? branch.WhenTrue : branch.WhenFalse;
        if (!Arm(whenTrue, wrapper, out HCall? trueProducer, out HVar? trueMerge, out HBlock? trueJoin) ||
            !Arm(whenFalse, wrapper, out HCall? falseProducer, out HVar? falseMerge, out HBlock? falseJoin) ||
            !ReferenceEquals(trueMerge, falseMerge) || !ReferenceEquals(trueJoin, falseJoin) ||
            ReferenceEquals(trueProducer!.Method, falseProducer!.Method)) return false;
        HBlock join = trueJoin!;
        var expectedBlocks = new HashSet<HBlock> { body.Blocks[0], whenTrue, whenFalse, join };
        if (expectedBlocks.Count != 4 || !body.Blocks.All(expectedBlocks.Contains) ||
            join.Statements is not [HEval { Expression: HCall consumer }, HReturn { Value: null }] ||
            !Plain(consumer, 1) || consumer.This is not HArg { Index: -1 } ||
            consumer.Arguments[0] is not HLocal argument || !ReferenceEquals(argument.Variable, trueMerge) ||
            trueProducer.Method.ReturnType.Key != consumer.Method.Parameters[0].Type.Key ||
            falseProducer.Method.ReturnType.Key != consumer.Method.Parameters[0].Type.Key) return false;

        if (site is not HEval { Expression: HCall actualConsumer } ||
            !SameCall(consumer, actualConsumer) || actualConsumer.This is not HLocal receiver ||
            actualConsumer.Arguments[0] is not HCall actualProducer || !Plain(actualProducer, 0) ||
            actualProducer.This is not HLocal otherReceiver || !ReferenceEquals(receiver.Variable, otherReceiver.Variable) ||
            !Receiver(caller, receiver, wrapper.DeclaringType) || !Receiver(caller, otherReceiver, wrapper.DeclaringType)) return false;
        bool chosen;
        if (SameCall(trueProducer, actualProducer)) chosen = true;
        else if (SameCall(falseProducer, actualProducer)) chosen = false;
        else return false;

        // These are nonvirtual calls in the recovered native body. Keep that dispatch, including execution
        // with a null receiver: the original producer/consumer sequence inside the wrapper remains the same.
        folded = new HCall
        {
            Method = wrapper, This = receiver, Type = wrapper.ReturnType,
            Arguments = [new HConst(chosen, wrapper.Parameters[0].Type)],
        };
        return true;
    }

    private static bool Arm(HBlock block, MethodDef wrapper, out HCall? producer, out HVar? merged, out HBlock? join)
    {
        producer = null; merged = null; join = null;
        if (block.Statements.Count is not (2 or 3) ||
            block.Statements[0] is not HAssign { Target: HLocal first, Value: HCall call } ||
            block.Statements[^1] is not HJump jump || !Plain(call, 0) || call.This is not HArg { Index: -1 } ||
            !ReferenceEquals(call.Method.DeclaringType, wrapper.DeclaringType) || call.Method.ReturnType.IsVoid ||
            call.Method.ReturnType.IsValueType || call.Method.ReturnType is ByRefSig or PointerSig ||
            first.Variable.AddressTaken || first.Variable.Type?.Key != call.Method.ReturnType.Key) return false;
        HVar result = first.Variable;
        if (block.Statements.Count == 3)
        {
            if (block.Statements[1] is not HAssign { Target: HLocal target, Value: HLocal from } ||
                !ReferenceEquals(from.Variable, first.Variable) || target.Variable.AddressTaken ||
                target.Variable.Type?.Key != call.Method.ReturnType.Key) return false;
            result = target.Variable;
        }
        producer = call; merged = result; join = jump.Target;
        return true;
    }

    private static bool Plain(HCall call, int arguments) => !call.Method.IsStatic && !call.Method.IsVirtual &&
        !call.Virtual && call.Constrained == null && call.MethodArguments.Length == 0 && call.Alternatives.Count == 0 &&
        call.Method.GenericParameters.Length == 0 && call.Method.DeclaringType.GenericParameters.Length == 0 &&
        call.Arguments.Length == arguments && call.Method.Parameters.Length == arguments &&
        (call.DeclaringType == null || call.DeclaringType.Key == call.Method.DeclaringType.Sig.Key) &&
        (call.Type == null || call.Type.Key == call.Method.ReturnType.Key);

    private static bool SameCall(HCall template, HCall site) => ReferenceEquals(template.Method, site.Method) &&
        Plain(site, template.Arguments.Length) && template.Virtual == site.Virtual &&
        ReferenceEquals(template.ReceiverIndependentTarget, site.ReceiverIndependentTarget);

    private static bool Receiver(HMethod caller, HLocal expression, TypeDef owner)
    {
        HVar local = expression.Variable;
        if (local.AddressTaken || local.Type?.Key != owner.Sig.Key ||
            (expression.Type != null && expression.Type.Key != owner.Sig.Key)) return false;
        bool escaped = false;
        foreach (HBlock block in caller.Blocks)
            foreach (HStmt statement in block.Statements)
                FinallyFolding.Visit(statement, e =>
                {
                    if (e is HAddressOf address && ConstructorFolding.Mentions(address.Target, local)) escaped = true;
                });
        return !escaped;
    }
}
