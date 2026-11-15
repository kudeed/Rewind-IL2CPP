using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Gives constants the type of the place they go to.
///
/// Machine code sets a float field with a plain 32-bit store of the number's bit pattern ("mov [x], 3F800000h"
/// is "x = 1f"). Read as the whole number it looks like, the constant would be converted on the way - a
/// different value altogether (1065353216f). Wherever a whole-number constant stands where a float or double
/// is expected (an assignment, an argument, an operand of float arithmetic or of a comparison with a float),
/// it is the number with those bits; and the other way round for a float constant where a whole number is
/// expected.
/// </summary>
internal static class ConstantTyping
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_CONSTANT_TYPING") != null;

    public static void Run(HMethod method, ProgramAnalysis program)
    {
        if (Disabled) return;
        var walker = new Walker(program);
        TypeSig returns = method.Method.ReturnType;
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
                switch (s)
                {
                    case HAssign a:
                        walker.Walk(a.Target);
                        walker.Walk(a.Value);
                        a.Value = Fit(a.Value, a.Target.Type);
                        break;
                    case HEval e:
                        walker.Walk(e.Expression);
                        break;
                    case HReturn r when r.Value != null:
                        walker.Walk(r.Value);
                        if (!returns.ContainsGenericParameter) r.Value = Fit(r.Value, returns);
                        break;
                    case HThrow t:
                        walker.Walk(t.Exception);
                        break;
                    case HBranch b:
                        walker.Walk(b.Condition);
                        break;
                    case HSwitch sw:
                        walker.Walk(sw.Value);
                        break;
                }
    }

    private static bool Real(TypeSig? type) => type is PrimitiveSig { Element: Il2CppTypeEnum.R4 or Il2CppTypeEnum.R8 };

    private static int? Bits32(object? value) => value switch
    {
        int n => n,
        uint n => unchecked((int)n),
        long n when n is >= int.MinValue and <= uint.MaxValue => unchecked((int)n),
        _ => null,
    };

    private static long? Bits64(object? value) => value switch
    {
        long n => n,
        // Only "nothing" is the same in any width.
        int n when n == 0 => 0L,
        uint n when n == 0 => 0L,
        _ => null,
    };

    /// <summary>The value as what is expected there: a constant of the other kind is the one with the same bits.</summary>
    private static HExpr Fit(HExpr value, TypeSig? expected)
    {
        if (expected is not PrimitiveSig p) return value;
        if (value is HSelect s)
        {
            s.WhenTrue = Fit(s.WhenTrue, expected);
            s.WhenFalse = Fit(s.WhenFalse, expected);
            return value;
        }
        if (value is not HConst c) return value;
        switch (p.Element)
        {
            case Il2CppTypeEnum.R4:
                if (Bits32(c.Value) is { } single) return new HConst(BitConverter.Int32BitsToSingle(single), expected);
                break;
            case Il2CppTypeEnum.R8:
                if (Bits64(c.Value) is { } wide) return new HConst(BitConverter.Int64BitsToDouble(wide), expected);
                break;
            case Il2CppTypeEnum.I4:
            case Il2CppTypeEnum.U4:
                if (c.Value is float f) return new HConst(BitConverter.SingleToInt32Bits(f), expected);
                break;
            case Il2CppTypeEnum.I8:
            case Il2CppTypeEnum.U8:
                if (c.Value is double d) return new HConst(BitConverter.DoubleToInt64Bits(d), expected);
                break;
        }
        return value;
    }

    private sealed class Walker(ProgramAnalysis program)
    {
        private void Arguments(HExpr[] arguments, MethodDef method, TypeSig? declaring, TypeSig[] methodArguments)
        {
            TypeSig[] classArguments = declaring is GenericInstSig g ? g.Arguments : [];
            for (int i = 0; i < arguments.Length; i++)
            {
                Walk(arguments[i]);
                if (i >= method.Parameters.Length) continue;
                TypeSig parameter = method.Parameters[i].Type;
                if (parameter.ContainsGenericParameter)
                {
                    if (classArguments.Length == 0 && methodArguments.Length == 0) continue;
                    parameter = program.Model.Sigs.Substitute(parameter, classArguments, methodArguments);
                }
                arguments[i] = Fit(arguments[i], parameter);
            }
        }

        public void Walk(HExpr? e)
        {
            switch (e)
            {
                case null:
                    return;
                case HCall c:
                    Walk(c.This);
                    Arguments(c.Arguments, c.Method, c.DeclaringType, c.MethodArguments);
                    return;
                case HNewObject n:
                    Arguments(n.Arguments, n.Constructor, n.DeclaringType, []);
                    return;
                case HBinary b:
                    Walk(b.Left);
                    Walk(b.Right);
                    if (Real(b.Type) && b.Op is HBinaryOp.Add or HBinaryOp.Sub or HBinaryOp.Mul or HBinaryOp.Div or HBinaryOp.Rem)
                    {
                        b.Left = Fit(b.Left, b.Type);
                        b.Right = Fit(b.Right, b.Type);
                    }
                    return;
                case HCompare c:
                    Walk(c.Left);
                    Walk(c.Right);
                    if (Real(c.Left.Type)) c.Right = Fit(c.Right, c.Left.Type);
                    else if (Real(c.Right.Type)) c.Left = Fit(c.Left, c.Right.Type);
                    return;
                case HSelect s:
                    Walk(s.Condition);
                    Walk(s.WhenTrue);
                    Walk(s.WhenFalse);
                    if (Real(s.Type))
                    {
                        s.WhenTrue = Fit(s.WhenTrue, s.Type);
                        s.WhenFalse = Fit(s.WhenFalse, s.Type);
                    }
                    return;
                case HField f: Walk(f.Object); return;
                case HElement el: Walk(el.Array); Walk(el.Index); return;
                case HArrayLength len: Walk(len.Array); return;
                case HAddressOf a: Walk(a.Target); return;
                case HDeref d: Walk(d.Pointer); return;
                case HUnary u: Walk(u.Operand); return;
                case HConv c: Walk(c.Operand); return;
                case HTypeExpr t: Walk(t.Operand); return;
                case HNewArray na: Walk(na.Length); return;
                case HCachedDelegate cached: Walk(cached.Creation); return;
                case HOpaque o:
                    foreach (HExpr operand in o.Operands) Walk(operand);
                    return;
            }
        }
    }
}
