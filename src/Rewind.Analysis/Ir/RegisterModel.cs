namespace Rewind.Analysis.Ir;

/// <summary>
/// How a lifter numbers the machine's registers as variables (Function.Params) and where the calling convention
/// puts arguments, so that the passes after lifting need not know which machine the code came from.
///
/// Argument positions (AbiParam.Position, and the positions call arguments are looked up by) are the
/// convention's own numbering: Win64 numbers every parameter in order, 0-3 in registers (rcx/xmm0 .. r9/xmm3)
/// and the rest on the stack; AArch64 counts integer registers (0-7, and 8 for the struct return address in
/// x8), floating-point registers (16-23 for v0-v7) and stack slots (32 and up) separately.
/// </summary>
public sealed class RegisterModel
{
    public required string Name { get; init; }
    /// <summary>Variable of the stack pointer.</summary>
    public required int StackPointer { get; init; }
    /// <summary>Variable of the integer register of each integer argument register position.</summary>
    public required int[] IntArgs { get; init; }
    /// <summary>Variable of lane 0 of floating-point register 0; lanes are 32 bits, four to a register.</summary>
    public required int FloatBase { get; init; }
    /// <summary>Callee-saved general registers, as variables (the stack pointer included where it is one).</summary>
    public required int[] CalleeSaved { get; init; }
    /// <summary>Variable of the integer return register.</summary>
    public int IntReturn { get; init; }
    /// <summary>Offset from the entry stack pointer of the first stack-passed argument slot.</summary>
    public required int StackArgBase { get; init; }
    /// <summary>Offsets from the entry stack pointer at and above which the caller's memory starts (return address included).</summary>
    public required int CallerArea { get; init; }
    /// <summary>First position that is a stack slot.</summary>
    public required int FirstStackPosition { get; init; }
    /// <summary>First floating-point register position, or -1 when float and integer arguments share positions.</summary>
    public required int FirstFloatPosition { get; init; }

    public bool SharedPositions => FirstFloatPosition < 0;

    public int FloatLane(int register, int lane) => FloatBase + register * 4 + lane;

    public bool IsStackPosition(int position) => position >= FirstStackPosition;

    /// <summary>The integer register number (CallInfo slot index) of a register position, or -1.</summary>
    public int IntRegisterOf(int position) =>
        position < 0 || position >= FirstStackPosition || (!SharedPositions && position >= FirstFloatPosition) ? -1 : position;

    /// <summary>The floating-point register number of a register position, or -1.</summary>
    public int FloatRegisterOf(int position)
    {
        if (position < 0 || position >= FirstStackPosition) return -1;
        if (SharedPositions) return position;
        return position >= FirstFloatPosition ? position - FirstFloatPosition : -1;
    }

    /// <summary>Stack slot index (CallInfo slot index) of a stack position.</summary>
    public int StackSlotOf(int position) => position - FirstStackPosition;

    /// <summary>The position of an integer register or stack slot a call argument came from (-1 for others).</summary>
    public int IntPositionOfSlot(ArgSlot slot) => slot.Kind switch
    {
        ArgSlotKind.IntReg => slot.Index,
        ArgSlotKind.Stack => FirstStackPosition + slot.Index,
        _ => -1,
    };

    /// <summary>The position of a call argument's slot, floating-point registers included (-1 for the target).</summary>
    public int PositionOfSlot(ArgSlot slot) => slot.Kind == ArgSlotKind.FloatReg
        ? (SharedPositions ? slot.Index / 4 : FirstFloatPosition + slot.Index / 4)
        : IntPositionOfSlot(slot);

    /// <summary>Offset from the entry stack pointer of a stack position's slot.</summary>
    public int StackOffsetOf(int position) => StackArgBase + 8 * (position - FirstStackPosition);

    /// <summary>Win64: rsp is variable 4, arguments in rcx, rdx, r8, r9 / xmm0-3, the stack arguments above the return address and home area.</summary>
    public static readonly RegisterModel Win64 = new()
    {
        Name = "win64",
        StackPointer = 4,
        IntArgs = [1, 2, 8, 9],
        FloatBase = 16,
        CalleeSaved = [3, 5, 6, 7, 12, 13, 14, 15],
        IntReturn = 0,
        StackArgBase = 0x28,
        CallerArea = 8,
        FirstStackPosition = 4,
        FirstFloatPosition = -1,
    };

    /// <summary>AArch64 (AAPCS64): x0-x30 are variables 0-30, sp 31; arguments in x0-x7 and v0-v7, stack arguments at the entry stack pointer.</summary>
    public static readonly RegisterModel Arm64 = new()
    {
        Name = "arm64",
        StackPointer = 31,
        IntArgs = [0, 1, 2, 3, 4, 5, 6, 7, 8],
        FloatBase = 34,
        CalleeSaved = [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31],
        IntReturn = 0,
        StackArgBase = 0,
        CallerArea = 0,
        FirstStackPosition = 32,
        FirstFloatPosition = 16,
    };
}
