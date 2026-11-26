using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Output;

/// <summary>
/// A native GPR may carry a packed value type. That does not make the corresponding
/// managed local an integer evaluation-stack operand. Refuse the invalid scalar
/// instruction rather than emit a conversion or an Opaque value that fabricates a lane.
/// Unknown types are not proof of an aggregate; this is deliberately a narrow gate.
/// </summary>
internal static class AggregateNumericOperands
{
    private static bool Aggregate(TypeSig? type) =>
        type is { IsValueType: true } and not PrimitiveSig &&
        type.Definition is { IsEnum: false } d &&
        d.FullName is not ("System.IntPtr" or "System.UIntPtr" or
            "System.Boolean" or "System.Char" or "System.SByte" or "System.Byte" or
            "System.Int16" or "System.UInt16" or "System.Int32" or "System.UInt32" or
            "System.Int64" or "System.UInt64" or "System.Single" or "System.Double");

    internal static string? Error(string op, HExpr operand, TypeSig? declaredArgument = null)
    {
        // Locals and fields are pushed using their declared IL types; a scalar
        // annotation on the HIR expression must not hide an actual aggregate.
        TypeSig? declared = operand switch
        {
            HLocal local => local.Variable.Type,
            HArg => declaredArgument,
            HField field => field.Field.Type,
            HCall call => call.Method.ReturnType,
            _ => null,
        };
        TypeSig? invalid = Aggregate(declared) ? declared :
            Aggregate(operand.Type) ? operand.Type : null;
        return invalid == null ? null :
            $"aggregate scalar operand: {op} on {invalid.DisplayName}; recover typed field/lane from native evidence";
    }
}
