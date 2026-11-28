using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Arm64;

public sealed partial class A64Lifter
{
    private Node FloatConstant(VT type, double value) => C(type,
        type == VT.F32 ? BitConverter.SingleToInt32Bits((float)value) : BitConverter.DoubleToInt64Bits(value));

    /// <summary>
    /// A general-register fixed-point conversion has the same rounded significand as the integer conversion,
    /// scaled by an exact power of two. For the supported F32/F64 destinations and at most 64 fractional
    /// bits this scaling neither overflows nor produces a subnormal result, so it adds no second rounding.
    /// </summary>
    private Node FixedToFloat(Node integer, VT type, bool unsigned, int fractionalBits)
    {
        Node converted = _b.Raw(unsigned ? Op.UIntToF : Op.SIntToF, type, integer);
        return fractionalBits == 0 ? converted
            : _b.Raw(Op.FMul, type, converted, FloatConstant(type, Math.ScaleB(1.0, -fractionalBits)));
    }

    /// <summary>
    /// ARM floating-to-integer conversion saturates to the destination range and maps NaN to zero.
    /// An ordinary managed conversion does not specify these out-of-range results. Keep the guards in IR
    /// so only a representable input reaches that conversion; later native CSELs remain separate operations.
    /// </summary>
    private Node SaturatingFloatToInt(Node value, VT type, bool signed)
    {
        int bits = type.Bits();
        long minimum = signed ? bits == 64 ? long.MinValue : int.MinValue : 0;
        long maximum = signed ? bits == 64 ? long.MaxValue : int.MaxValue
            : bits == 64 ? -1L : uint.MaxValue;
        double upper = Math.ScaleB(1.0, signed ? bits - 1 : bits);
        double lower = signed ? -upper : 0.0;
        Node zero = C(type, 0);
        Node conversion = _b.Raw(signed ? Op.FToSInt : Op.FToUInt, type, value);
        Node high = _b.Raw(Op.FCmpLe, VT.I1, FloatConstant(value.Type, upper), value);
        Node low = _b.Raw(Op.FCmpLe, VT.I1, value, FloatConstant(value.Type, lower));
        Node nan = _b.Raw(Op.FCmpUnord, VT.I1, value, value);
        return _b.Select(nan, zero,
            _b.Select(low, C(type, minimum), _b.Select(high, C(type, maximum), conversion)));
    }
}
