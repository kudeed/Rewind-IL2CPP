namespace Rewind.Analysis.Arm64;

/// <summary>
/// Operations of the A64 instruction set, in canonical form: aliases are decoded as what they stand for (CMP is
/// SUBS to the zero register, MOV is ORR or ADD, LSL is UBFM), so the lifter has fewer cases to know.
/// </summary>
public enum A64Op : byte
{
    Invalid,
    /// <summary>A valid encoding this decoder does not take apart.</summary>
    Unknown,

    // PC-relative and immediate data processing
    Adr, Adrp, AddImm, SubImm, AndImm, OrrImm, EorImm, MovZ, MovN, MovK, Sbfm, Bfm, Ubfm, Extr,

    // register data processing (Rm shifted by Shift/Amount, or extended by Extend/Amount for the *Ext forms)
    AddReg, SubReg, AddExt, SubExt, And, Bic, Orr, Orn, Eor, Eon, Adc, Sbc,
    /// <summary>Conditional compares: Imm is the nzcv value used when Cond fails; Imm2 the immediate of the immediate forms.</summary>
    CcmpReg, CcmnReg, CcmpImm, CcmnImm,
    Csel, Csinc, Csinv, Csneg,
    Udiv, Sdiv, Lslv, Lsrv, Asrv, Rorv, Rbit, Rev16, Rev32, Rev, Clz, Cls,
    /// <summary>Rd = Ra + Rn * Rm (and the subtracting and widening forms); Ra is the zero register for MUL.</summary>
    Madd, Msub, Smaddl, Smsubl, Umaddl, Umsubl, Smulh, Umulh,

    // control flow and system
    B, Bl, BCond, Cbz, Cbnz, Tbz, Tbnz, Br, Blr, Ret, Brk, Udf, Hlt, Svc, Nop, Barrier, Clrex,
    /// <summary>Read of a system register; Imm is its encoding (op0:op1:CRn:CRm:op2).</summary>
    Mrs, Msr, Sys,

    // memory
    Ldr, Str, Ldp, Stp,
    /// <summary>Load from Target (PC-relative literal).</summary>
    LdrLit, Prfm,
    Ldxr, Stxr, Ldaxr, Stlxr, Ldar, Stlr, Ldxp, Stxp, Ldaxp, Stlxp,
    /// <summary>Large-system-extension atomics: Ra is Rs (the operand), Rd the register receiving the old value.</summary>
    Cas, Casp, Swp, LdAdd, LdClr, LdEor, LdSet, LdSmax, LdSmin, LdUmax, LdUmin,

    // scalar floating point (FpSize gives the precision: 2, 4 or 8 bytes)
    FMov, FMovImm,
    /// <summary>Bit copies between general and FP registers (Is64 gives the general register's width).</summary>
    FMovToGp, FMovFromGp, FMovToGpHigh, FMovFromGpHigh,
    FAbs, FNeg, FSqrt,
    /// <summary>Precision change: from FpSize to Imm bytes.</summary>
    FCvt,
    /// <summary>Round to an integral value: Imm is the rounding (see <see cref="A64Rounding"/>).</summary>
    FRint,
    FAdd, FSub, FMul, FDiv, FMax, FMin, FMaxNm, FMinNm, FNMul,
    FMAdd, FMSub, FNMAdd, FNMSub,
    /// <summary>Compare Rn with Rm, or with zero when Imm is 1.</summary>
    FCmp, FCmpe, FCcmp, FCcmpe, FCsel,
    Scvtf, Ucvtf,
    /// <summary>Float to integer: Imm is the rounding (see <see cref="A64Rounding"/>), Signed the result's signedness.</summary>
    FCvtToInt,

    // SIMD (vector) operations the compiler uses on scalars and for copies. Q (Imm2 bit 0) selects 128 bits.
    /// <summary>Move of an expanded immediate into a vector register: Target holds the 64-bit pattern.</summary>
    Movi,
    /// <summary>Copy of a vector register (ORR with both sources the same).</summary>
    VMov,
    /// <summary>Element Imm (of ElemSize bytes) of Vn duplicated into every element / into a scalar.</summary>
    Dup, DupScalar,
    /// <summary>General register Rn duplicated into every element of ElemSize bytes.</summary>
    DupGp,
    /// <summary>Vd[Imm] = Vn[Imm2] (elements of ElemSize bytes).</summary>
    Ins,
    /// <summary>Vd[Imm] = general register Rn.</summary>
    InsGp,
    /// <summary>General register Rd = element Imm of Vn, zero- or sign-extended.</summary>
    Umov, Smov,
    VAnd, VOrr, VEor, VBic,
    /// <summary>Bitwise modified immediate, Target contains the expanded mask.</summary>
    VOrImm, VBicImm,
    /// <summary>Element-wise float arithmetic on vectors (ElemSize 4 or 8).</summary>
    VFAdd, VFSub, VFMul, VFDiv,
    /// <summary>An element-wise or rearranging SIMD operation: Imm is its <see cref="VecKind"/>.</summary>
    VecOp,
    /// <summary>LD1/ST1 of element Amount (ElemSize bytes); LD1R, the element loaded into every element.</summary>
    Ld1Lane, St1Lane, Ld1R,
    /// <summary>Some other SIMD operation.</summary>
    Vector,
}

public enum A64Shift : byte { Lsl, Lsr, Asr, Ror }

public enum A64Extend : byte { Uxtb, Uxth, Uxtw, Uxtx, Sxtb, Sxth, Sxtw, Sxtx }

public enum A64Mode : byte { Offset, PreIndex, PostIndex, RegOffset }

/// <summary>Rounding of FRINT* and FCVT*.</summary>
public enum A64Rounding : byte { Nearest, PlusInfinity, MinusInfinity, Zero, NearestAway, Current, CurrentExact }

/// <summary>
/// One decoded A64 instruction. General registers are numbered 0-30, <see cref="Zr"/> (31) is the zero register
/// and <see cref="Sp"/> (32) the stack pointer: the decoder resolves which of the two an encoding's 31 means.
/// SIMD and FP registers are numbered 0-31 in the same fields.
/// </summary>
public struct A64Instruction
{
    public const byte Zr = 31, Sp = 32;

    public ulong Address;
    public uint Word;
    public A64Op Op;
    /// <summary>64-bit general registers (sf), or for loads the width of the destination register.</summary>
    public bool Is64;
    public bool SetFlags;
    /// <summary>Destination (Rt for memory accesses).</summary>
    public byte Rd;
    public byte Rn, Rm;
    /// <summary>Third source (Ra), the second register of a pair (Rt2), or the status/operand register Rs.</summary>
    public byte Ra;
    public long Imm, Imm2;
    public A64Shift Shift;
    public byte Amount;
    public A64Extend Extend;
    public byte Cond;
    /// <summary>Memory access size in bytes (1, 2, 4, 8 or 16).</summary>
    public byte Size;
    /// <summary>Sign-extending load; signed conversion.</summary>
    public bool Signed;
    /// <summary>The transferred register is a SIMD/FP register.</summary>
    public bool Vector;
    public A64Mode Mode;
    /// <summary>Scalar FP precision in bytes (2, 4, 8).</summary>
    public byte FpSize;
    /// <summary>Vector element size in bytes.</summary>
    public byte ElemSize;
    /// <summary>Branch target, literal address or ADR/ADRP result.</summary>
    public ulong Target;

    public readonly ulong NextAddress => Address + 4;
    public readonly bool IsInvalid => Op == A64Op.Invalid;

    public readonly bool IsBranch => Op is A64Op.B or A64Op.BCond or A64Op.Cbz or A64Op.Cbnz or A64Op.Tbz or A64Op.Tbnz or A64Op.Br or A64Op.Ret;
    public readonly bool IsCall => Op is A64Op.Bl or A64Op.Blr;

    public override readonly string ToString() => A64Format.Describe(this);
}
