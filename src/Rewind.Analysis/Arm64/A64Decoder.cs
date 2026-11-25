namespace Rewind.Analysis.Arm64;

/// <summary>
/// Decodes A64 (AArch64) instruction words. Covers the base integer instructions, loads and stores, branches,
/// system hints and barriers, scalar floating point and the SIMD moves compilers use for copies and scalars;
/// anything else valid comes out as <see cref="A64Op.Unknown"/> or <see cref="A64Op.Vector"/>.
/// </summary>
public static partial class A64Decoder
{
    private static uint Bits(uint w, int hi, int lo) => (w >> lo) & ((1u << (hi - lo + 1)) - 1);
    private static bool Bit(uint w, int b) => ((w >> b) & 1) != 0;
    private static long SignExtend(ulong value, int bits) => (long)(value << (64 - bits)) >> (64 - bits);

    /// <summary>Register field as a general register where 31 is the zero register.</summary>
    private static byte R(uint w, int lo) => (byte)Bits(w, lo + 4, lo);
    /// <summary>Register field as a general register where 31 is the stack pointer.</summary>
    private static byte RSp(uint w, int lo)
    {
        byte r = (byte)Bits(w, lo + 4, lo);
        return r == 31 ? A64Instruction.Sp : r;
    }

    public static A64Instruction Decode(uint w, ulong address)
    {
        var i = new A64Instruction { Address = address, Word = w, Op = A64Op.Invalid };
        switch (Bits(w, 28, 25))
        {
            case 0b1000 or 0b1001: DataImmediate(w, ref i); break;
            case 0b1010 or 0b1011: BranchSystem(w, ref i); break;
            case 0b0100 or 0b0110 or 0b1100 or 0b1110: LoadStore(w, ref i); break;
            case 0b0101 or 0b1101: DataRegister(w, ref i); break;
            case 0b0111 or 0b1111: SimdFp(w, ref i); break;
            case 0b0000:
                if (Bits(w, 31, 16) == 0) i.Op = A64Op.Udf;
                break;
        }
        return i;
    }

    // ---- data processing, immediate ----------------------------------------------------------------------------

    private static void DataImmediate(uint w, ref A64Instruction i)
    {
        i.Is64 = Bit(w, 31);
        switch (Bits(w, 25, 23))
        {
            case 0b000 or 0b001:
            {
                // ADR / ADRP
                long imm = SignExtend((Bits(w, 23, 5) << 2) | Bits(w, 30, 29), 21);
                i.Rd = R(w, 0);
                i.Is64 = true;
                if (Bit(w, 31))
                {
                    i.Op = A64Op.Adrp;
                    i.Target = (ulong)((long)(i.Address & ~0xFFFUL) + (imm << 12));
                }
                else
                {
                    i.Op = A64Op.Adr;
                    i.Target = (ulong)((long)i.Address + imm);
                }
                i.Imm = (long)i.Target;
                return;
            }
            case 0b010:
            {
                // ADD/SUB (immediate)
                i.SetFlags = Bit(w, 29);
                i.Op = Bit(w, 30) ? A64Op.SubImm : A64Op.AddImm;
                i.Imm = Bits(w, 21, 10) << (Bit(w, 22) ? 12 : 0);
                i.Rn = RSp(w, 5);
                i.Rd = i.SetFlags ? R(w, 0) : RSp(w, 0);
                return;
            }
            case 0b011:
                return; // add/sub immediate with tags (memory tagging): not used by application code
            case 0b100:
            {
                // logical (immediate)
                int n = (int)Bits(w, 22, 22);
                if (!i.Is64 && n == 1) return;
                if (!DecodeBitMasks(n, (int)Bits(w, 15, 10), (int)Bits(w, 21, 16), i.Is64, out ulong mask)) return;
                uint opc = Bits(w, 30, 29);
                i.Op = opc switch { 0 => A64Op.AndImm, 1 => A64Op.OrrImm, 2 => A64Op.EorImm, _ => A64Op.AndImm };
                i.SetFlags = opc == 3;
                i.Imm = (long)mask;
                i.Rn = R(w, 5);
                i.Rd = i.SetFlags ? R(w, 0) : RSp(w, 0);
                return;
            }
            case 0b101:
            {
                // move wide
                uint opc = Bits(w, 30, 29);
                int hw = (int)Bits(w, 22, 21);
                if (opc == 1 || (!i.Is64 && hw >= 2)) return;
                i.Op = opc switch { 0 => A64Op.MovN, 2 => A64Op.MovZ, _ => A64Op.MovK };
                i.Imm = Bits(w, 20, 5);
                i.Amount = (byte)(hw * 16);
                i.Rd = R(w, 0);
                return;
            }
            case 0b110:
            {
                // bitfield
                uint opc = Bits(w, 30, 29);
                if (opc == 3 || Bits(w, 22, 22) != (i.Is64 ? 1u : 0u)) return;
                i.Op = opc switch { 0 => A64Op.Sbfm, 1 => A64Op.Bfm, _ => A64Op.Ubfm };
                i.Imm = Bits(w, 21, 16);  // immr
                i.Imm2 = Bits(w, 15, 10); // imms
                if (!i.Is64 && (i.Imm > 31 || i.Imm2 > 31)) { i.Op = A64Op.Invalid; return; }
                i.Rn = R(w, 5);
                i.Rd = R(w, 0);
                return;
            }
            case 0b111:
            {
                // extract
                if (Bits(w, 30, 29) != 0 || Bit(w, 21) || Bits(w, 22, 22) != (i.Is64 ? 1u : 0u)) return;
                i.Op = A64Op.Extr;
                i.Rm = R(w, 16);
                i.Imm = Bits(w, 15, 10);
                if (!i.Is64 && i.Imm > 31) { i.Op = A64Op.Invalid; return; }
                i.Rn = R(w, 5);
                i.Rd = R(w, 0);
                return;
            }
        }
    }

    /// <summary>The bit pattern of a logical immediate (DecodeBitMasks of the architecture manual).</summary>
    public static bool DecodeBitMasks(int n, int imms, int immr, bool is64, out ulong mask)
    {
        mask = 0;
        int combined = (n << 6) | (~imms & 0x3F);
        if (combined == 0) return false;
        int len = 31 - System.Numerics.BitOperations.LeadingZeroCount((uint)combined);
        if (len < 1) return false;
        int levels = (1 << len) - 1;
        int s = imms & levels, r = immr & levels;
        if (s == levels) return false;
        int esize = 1 << len;
        ulong elemMask = esize == 64 ? ulong.MaxValue : (1UL << esize) - 1;
        ulong welem = (1UL << (s + 1)) - 1;
        ulong rotated = r == 0 ? welem : ((welem >> r) | (welem << (esize - r))) & elemMask;
        ulong result = 0;
        for (int at = 0; at < 64; at += esize) result |= rotated << at;
        mask = is64 ? result : result & 0xFFFFFFFF;
        return true;
    }

    // ---- branches, exceptions, system --------------------------------------------------------------------------

    private static void BranchSystem(uint w, ref A64Instruction i)
    {
        if ((w & 0x7C000000) == 0x14000000)
        {
            // B / BL
            i.Op = Bit(w, 31) ? A64Op.Bl : A64Op.B;
            i.Target = (ulong)((long)i.Address + (SignExtend(Bits(w, 25, 0), 26) << 2));
            return;
        }
        if ((w & 0xFF000010) == 0x54000000)
        {
            i.Op = A64Op.BCond;
            i.Cond = (byte)Bits(w, 3, 0);
            i.Target = (ulong)((long)i.Address + (SignExtend(Bits(w, 23, 5), 19) << 2));
            return;
        }
        if ((w & 0x7E000000) == 0x34000000)
        {
            i.Op = Bit(w, 24) ? A64Op.Cbnz : A64Op.Cbz;
            i.Is64 = Bit(w, 31);
            i.Rd = R(w, 0);
            i.Target = (ulong)((long)i.Address + (SignExtend(Bits(w, 23, 5), 19) << 2));
            return;
        }
        if ((w & 0x7E000000) == 0x36000000)
        {
            i.Op = Bit(w, 24) ? A64Op.Tbnz : A64Op.Tbz;
            i.Imm = (Bits(w, 31, 31) << 5) | Bits(w, 23, 19);
            i.Is64 = Bit(w, 31);
            i.Rd = R(w, 0);
            i.Target = (ulong)((long)i.Address + (SignExtend(Bits(w, 18, 5), 14) << 2));
            return;
        }
        if ((w & 0xFE000000) == 0xD6000000)
        {
            // unconditional branch (register), with the pointer-authenticating variants
            uint opc = Bits(w, 24, 21), op2 = Bits(w, 20, 16), op3 = Bits(w, 15, 10), op4 = Bits(w, 4, 0);
            if (op2 != 0x1F) return;
            bool plain = op3 == 0 && op4 == 0;
            bool authZero = (op3 is 2 or 3) && op4 == 0x1F;       // BRAAZ, BLRAAZ, RETAA, ...
            bool authReg = (op3 is 2 or 3) && (opc is 8 or 9);    // BRAA, BLRAA (modifier in Rd field)
            i.Rn = R(w, 5);
            switch (opc)
            {
                case 0 when plain || authZero: i.Op = A64Op.Br; return;
                case 1 when plain || authZero: i.Op = A64Op.Blr; return;
                case 2 when plain: i.Op = A64Op.Ret; return;
                case 2 when (op3 is 2 or 3) && i.Rn == 31 && op4 == 0x1F: i.Op = A64Op.Ret; i.Rn = 30; return;
                case 8 when authReg: i.Op = A64Op.Br; return;
                case 9 when authReg: i.Op = A64Op.Blr; return;
            }
            return;
        }
        if ((w & 0xFF000000) == 0xD4000000)
        {
            uint opc = Bits(w, 23, 21), ll = Bits(w, 1, 0);
            i.Imm = Bits(w, 20, 5);
            if (opc == 1 && ll == 0) i.Op = A64Op.Brk;
            else if (opc == 2 && ll == 0) i.Op = A64Op.Hlt;
            else if (opc == 0 && ll == 1) i.Op = A64Op.Svc;
            return;
        }
        if ((w & 0xFFC00000) == 0xD5000000)
        {
            // system
            if ((w & 0xFFFFF01F) == 0xD503201F) { i.Op = A64Op.Nop; return; }          // hints: NOP, YIELD, BTI, PAC*SP...
            if ((w & 0xFFFFF0FF) == 0xD503305F) { i.Op = A64Op.Clrex; return; }
            if ((w & 0xFFFFF09F) == 0xD503309F) { i.Op = A64Op.Barrier; i.Imm = Bits(w, 7, 5); return; } // DSB, DMB, ISB, SB
            i.Rd = R(w, 0);
            i.Imm = Bits(w, 20, 5);
            if ((w & 0xFFF00000) == 0xD5300000) { i.Op = A64Op.Mrs; return; }
            if ((w & 0xFFF00000) == 0xD5100000) { i.Op = A64Op.Msr; return; }
            i.Op = A64Op.Sys;
        }
    }

    // ---- loads and stores --------------------------------------------------------------------------------------

    private static void LoadStore(uint w, ref A64Instruction i)
    {
        bool v = Bit(w, 26);
        i.Vector = v;
        uint size = Bits(w, 31, 30);

        if ((w & 0x3F000000) == 0x08000000)
        {
            if (v) return;
            // exclusive and acquire/release accesses
            bool o2 = Bit(w, 23), l = Bit(w, 22), o1 = Bit(w, 21), o0 = Bit(w, 15);
            i.Ra = R(w, 16);
            i.Rn = RSp(w, 5);
            i.Rd = R(w, 0);
            i.Size = (byte)(1 << (int)size);
            i.Is64 = size == 3;
            if (o2 && o1)
            {
                // CAS family (and CASP when the size field is 0x for pairs)
                i.Op = A64Op.Cas;
                i.Imm = (l ? 1 : 0) | (o0 ? 2 : 0); // acquire, release
                return;
            }
            if (!o2 && o1)
            {
                // pairs: only 32/64-bit
                if (size < 2) { i.Op = A64Op.Casp; return; }
                i.Imm2 = R(w, 10);
                i.Op = l ? (o0 ? A64Op.Ldaxp : A64Op.Ldxp) : (o0 ? A64Op.Stlxp : A64Op.Stxp);
                return;
            }
            if (!o2) i.Op = l ? (o0 ? A64Op.Ldaxr : A64Op.Ldxr) : (o0 ? A64Op.Stlxr : A64Op.Stxr);
            else i.Op = l ? A64Op.Ldar : A64Op.Stlr; // (o0=0 forms are LDLAR/STLLR: same ordering here)
            return;
        }

        if ((w & 0x3B000000) == 0x18000000)
        {
            // load register (literal)
            uint opc = Bits(w, 31, 30);
            i.Target = (ulong)((long)i.Address + (SignExtend(Bits(w, 23, 5), 19) << 2));
            i.Rd = (byte)Bits(w, 4, 0);
            i.Mode = A64Mode.Offset;
            if (v)
            {
                if (opc == 3) return;
                i.Op = A64Op.LdrLit;
                i.Size = (byte)(4 << (int)opc);
                return;
            }
            switch (opc)
            {
                case 0: i.Op = A64Op.LdrLit; i.Size = 4; break;
                case 1: i.Op = A64Op.LdrLit; i.Size = 8; i.Is64 = true; break;
                case 2: i.Op = A64Op.LdrLit; i.Size = 4; i.Signed = true; i.Is64 = true; break;
                default: i.Op = A64Op.Prfm; break;
            }
            return;
        }

        if ((w & 0x3A000000) == 0x28000000)
        {
            // load/store pair
            uint opc = Bits(w, 31, 30);
            bool load = Bit(w, 22);
            i.Mode = Bits(w, 24, 23) switch { 1 => A64Mode.PostIndex, 3 => A64Mode.PreIndex, _ => A64Mode.Offset };
            int scale;
            if (v)
            {
                if (opc == 3) return;
                scale = 2 + (int)opc;
            }
            else
            {
                if (opc == 3 || (opc == 1 && !load) || (opc == 1 && Bits(w, 24, 23) == 0)) return;
                scale = opc == 2 ? 3 : 2;
                i.Signed = opc == 1;
                i.Is64 = opc != 0;
            }
            i.Op = load ? A64Op.Ldp : A64Op.Stp;
            i.Size = (byte)(1 << scale);
            i.Imm = SignExtend(Bits(w, 21, 15), 7) << scale;
            i.Ra = (byte)Bits(w, 14, 10);
            i.Rn = RSp(w, 5);
            i.Rd = (byte)Bits(w, 4, 0);
            return;
        }

        if ((w & 0x3B200C00) == 0x38200000 && !v)
        {
            // atomic memory operations (LSE)
            uint o3 = Bits(w, 15, 15), opc = Bits(w, 14, 12);
            i.Size = (byte)(1 << (int)size);
            i.Is64 = size == 3;
            i.Ra = R(w, 16);
            i.Rn = RSp(w, 5);
            i.Rd = R(w, 0);
            i.Imm = (Bit(w, 23) ? 1 : 0) | (Bit(w, 22) ? 2 : 0); // acquire, release
            if (o3 == 1)
            {
                if (opc == 0) i.Op = A64Op.Swp;
                else i.Op = A64Op.Unknown; // LDAPR and friends
                return;
            }
            i.Op = opc switch
            {
                0 => A64Op.LdAdd, 1 => A64Op.LdClr, 2 => A64Op.LdEor, 3 => A64Op.LdSet,
                4 => A64Op.LdSmax, 5 => A64Op.LdSmin, 6 => A64Op.LdUmax, _ => A64Op.LdUmin,
            };
            return;
        }

        bool unsignedOffset = (w & 0x3B000000) == 0x39000000;
        bool other = (w & 0x3B200000) == 0x38000000;
        bool registerOffset = (w & 0x3B200C00) == 0x38200800;
        if (!unsignedOffset && !other && !registerOffset)
        {
            if ((w & 0xBF000000) == 0x0C000000 || (w & 0xBF000000) == 0x0D000000)
            {
                // SIMD structure loads/stores
                if (!DecodeStructure(w, ref i)) i.Op = A64Op.Vector;
            }
            return;
        }
        uint kind = Bits(w, 23, 22);
        int accessScale;
        if (v)
        {
            accessScale = (int)size | (kind >= 2 ? 4 : 0);
            if (accessScale > 4) return;
            i.Op = (kind & 1) != 0 ? A64Op.Ldr : A64Op.Str;
        }
        else
        {
            accessScale = (int)size;
            switch (kind)
            {
                case 0: i.Op = A64Op.Str; i.Is64 = size == 3; break;
                case 1: i.Op = A64Op.Ldr; i.Is64 = size == 3; break;
                case 2:
                    if (size == 3)
                    {
                        i.Op = A64Op.Prfm;
                        if (other && Bits(w, 11, 10) != 0) i.Op = A64Op.Invalid;
                        return;
                    }
                    i.Op = A64Op.Ldr; i.Signed = true; i.Is64 = true; break;
                default:
                    if (size >= 2) return;
                    i.Op = A64Op.Ldr; i.Signed = true; i.Is64 = false; break;
            }
        }
        i.Size = (byte)(1 << accessScale);
        i.Rn = RSp(w, 5);
        i.Rd = (byte)Bits(w, 4, 0);
        if (unsignedOffset)
        {
            i.Mode = A64Mode.Offset;
            i.Imm = Bits(w, 21, 10) << accessScale;
        }
        else if (registerOffset)
        {
            uint option = Bits(w, 15, 13);
            if ((option & 2) == 0) { i.Op = A64Op.Invalid; return; }
            i.Mode = A64Mode.RegOffset;
            i.Rm = R(w, 16);
            i.Extend = (A64Extend)option;
            i.Amount = (byte)(Bit(w, 12) ? accessScale : 0);
        }
        else
        {
            i.Imm = SignExtend(Bits(w, 20, 12), 9);
            switch (Bits(w, 11, 10))
            {
                case 0: i.Mode = A64Mode.Offset; break;      // LDUR/STUR
                case 1: i.Mode = A64Mode.PostIndex; break;
                case 2: i.Mode = A64Mode.Offset; break;      // unprivileged LDTR/STTR: same at user level
                default: i.Mode = A64Mode.PreIndex; break;
            }
        }
    }

    // ---- data processing, register -----------------------------------------------------------------------------

    private static void DataRegister(uint w, ref A64Instruction i)
    {
        i.Is64 = Bit(w, 31);
        i.Rd = R(w, 0);
        i.Rn = R(w, 5);
        i.Rm = R(w, 16);
        if ((w & 0x1F000000) == 0x0A000000)
        {
            // logical (shifted register)
            uint opc = Bits(w, 30, 29);
            bool n = Bit(w, 21);
            i.Shift = (A64Shift)Bits(w, 23, 22);
            i.Amount = (byte)Bits(w, 15, 10);
            if (!i.Is64 && i.Amount > 31) return;
            i.SetFlags = opc == 3;
            i.Op = (opc, n) switch
            {
                (0, false) or (3, false) => A64Op.And,
                (0, true) or (3, true) => A64Op.Bic,
                (1, false) => A64Op.Orr,
                (1, true) => A64Op.Orn,
                (2, false) => A64Op.Eor,
                _ => A64Op.Eon,
            };
            return;
        }
        if ((w & 0x1F200000) == 0x0B000000)
        {
            // add/subtract (shifted register)
            i.Shift = (A64Shift)Bits(w, 23, 22);
            if (i.Shift == A64Shift.Ror) return;
            i.Amount = (byte)Bits(w, 15, 10);
            if (!i.Is64 && i.Amount > 31) return;
            i.SetFlags = Bit(w, 29);
            i.Op = Bit(w, 30) ? A64Op.SubReg : A64Op.AddReg;
            return;
        }
        if ((w & 0x1F200000) == 0x0B200000)
        {
            // add/subtract (extended register)
            if (Bits(w, 23, 22) != 0) return;
            i.Extend = (A64Extend)Bits(w, 15, 13);
            i.Amount = (byte)Bits(w, 12, 10);
            if (i.Amount > 4) return;
            i.SetFlags = Bit(w, 29);
            i.Op = Bit(w, 30) ? A64Op.SubExt : A64Op.AddExt;
            i.Rn = RSp(w, 5);
            i.Rd = i.SetFlags ? R(w, 0) : RSp(w, 0);
            return;
        }
        if ((w & 0x1FE0FC00) == 0x1A000000)
        {
            i.SetFlags = Bit(w, 29);
            i.Op = Bit(w, 30) ? A64Op.Sbc : A64Op.Adc;
            return;
        }
        if ((w & 0x1FE00410) == 0x1A400000 && Bit(w, 29))
        {
            // conditional compare (register or immediate)
            bool immediate = Bit(w, 11);
            i.Cond = (byte)Bits(w, 15, 12);
            i.Imm = Bits(w, 3, 0);
            i.SetFlags = true;
            if (immediate) i.Imm2 = Bits(w, 20, 16);
            i.Op = (Bit(w, 30), immediate) switch
            {
                (true, false) => A64Op.CcmpReg,
                (true, true) => A64Op.CcmpImm,
                (false, false) => A64Op.CcmnReg,
                _ => A64Op.CcmnImm,
            };
            return;
        }
        if ((w & 0x1FE00000) == 0x1A800000 && !Bit(w, 29))
        {
            // conditional select
            i.Cond = (byte)Bits(w, 15, 12);
            uint op2 = Bits(w, 11, 10);
            i.Op = (Bit(w, 30), op2) switch
            {
                (false, 0) => A64Op.Csel,
                (false, 1) => A64Op.Csinc,
                (true, 0) => A64Op.Csinv,
                (true, 1) => A64Op.Csneg,
                _ => A64Op.Invalid,
            };
            return;
        }
        if ((w & 0x5FE00000) == 0x1AC00000)
        {
            // data processing (2 source)
            i.Op = Bits(w, 15, 10) switch
            {
                0b000010 => A64Op.Udiv,
                0b000011 => A64Op.Sdiv,
                0b001000 => A64Op.Lslv,
                0b001001 => A64Op.Lsrv,
                0b001010 => A64Op.Asrv,
                0b001011 => A64Op.Rorv,
                _ => A64Op.Unknown, // CRC32, PAC
            };
            return;
        }
        if ((w & 0x5FFF0000) == 0x5AC00000)
        {
            // data processing (1 source)
            uint opcode = Bits(w, 15, 10);
            i.Op = opcode switch
            {
                0 => A64Op.Rbit,
                1 => A64Op.Rev16,
                2 => i.Is64 ? A64Op.Rev32 : A64Op.Rev,
                3 when i.Is64 => A64Op.Rev,
                4 => A64Op.Clz,
                5 => A64Op.Cls,
                _ => A64Op.Unknown,
            };
            return;
        }
        if ((w & 0x1F000000) == 0x1B000000)
        {
            // data processing (3 source)
            if (Bits(w, 30, 29) != 0) return;
            i.Ra = R(w, 10);
            bool o0 = Bit(w, 15);
            i.Op = Bits(w, 23, 21) switch
            {
                0 => o0 ? A64Op.Msub : A64Op.Madd,
                1 when i.Is64 => o0 ? A64Op.Smsubl : A64Op.Smaddl,
                2 when i.Is64 && !o0 => A64Op.Smulh,
                5 when i.Is64 => o0 ? A64Op.Umsubl : A64Op.Umaddl,
                6 when i.Is64 && !o0 => A64Op.Umulh,
                _ => A64Op.Invalid,
            };
        }
    }

    // ---- SIMD and floating point -------------------------------------------------------------------------------

    private static byte FpSizeOf(uint ptype) => ptype switch { 0 => 4, 1 => 8, 3 => 2, _ => 0 };

    private static void SimdFp(uint w, ref A64Instruction i)
    {
        i.Rd = (byte)Bits(w, 4, 0);
        i.Rn = (byte)Bits(w, 9, 5);
        i.Rm = (byte)Bits(w, 20, 16);
        if ((w & 0x5F000000) == 0x1E000000 && !Bit(w, 29) && ScalarFp(w, ref i)) return;
        if ((w & 0xFF000000) == 0x1F000000)
        {
            // FP data processing (3 source)
            i.FpSize = FpSizeOf(Bits(w, 23, 22));
            if (i.FpSize == 0) return;
            i.Ra = (byte)Bits(w, 14, 10);
            i.Op = (Bit(w, 21), Bit(w, 15)) switch
            {
                (false, false) => A64Op.FMAdd,
                (false, true) => A64Op.FMSub,
                (true, false) => A64Op.FNMAdd,
                _ => A64Op.FNMSub,
            };
            return;
        }
        Advanced(w, ref i);
    }

    private static bool ScalarFp(uint w, ref A64Instruction i)
    {
        uint ptype = Bits(w, 23, 22);
        // Fixed-point integer to float: convert, then scale by 2^-fbits.
        // The permitted power-of-two scaling stays in the normal FP32/64
        // range for every nonzero integer, so it introduces no extra rounding.
        if (!Bit(w, 21) && Bits(w, 30, 29) == 0 && Bits(w, 20, 19) == 0 &&
            Bits(w, 18, 16) is 2 or 3 && ptype is 0 or 1)
        {
            i.Is64 = Bit(w, 31);
            int fbits = 64 - (int)Bits(w, 15, 10);
            if (fbits > (i.Is64 ? 64 : 32)) return false;
            i.FpSize = FpSizeOf(ptype);
            i.Op = Bits(w, 18, 16) == 2 ? A64Op.Scvtf : A64Op.Ucvtf;
            i.Signed = i.Op == A64Op.Scvtf;
            i.Amount = (byte)fbits;
            return true;
        }
        if (Bit(w, 21) && Bits(w, 15, 10) == 0 && Bits(w, 30, 29) == 0)
        {
            // conversion between floating point and integer
            i.Is64 = Bit(w, 31);
            uint rmode = Bits(w, 20, 19), opcode = Bits(w, 18, 16);
            i.FpSize = FpSizeOf(ptype);
            i.Rd = (byte)Bits(w, 4, 0);
            i.Rn = (byte)Bits(w, 9, 5);
            switch (rmode, opcode)
            {
                case (0, 2): i.Op = A64Op.Scvtf; i.Signed = true; break;
                case (0, 3): i.Op = A64Op.Ucvtf; break;
                case (0, 6) when ptype != 2: i.Op = A64Op.FMovToGp; break;
                case (0, 7) when ptype != 2: i.Op = A64Op.FMovFromGp; break;
                case (1, 6) when ptype == 2 && i.Is64: i.Op = A64Op.FMovToGpHigh; i.FpSize = 8; break;
                case (1, 7) when ptype == 2 && i.Is64: i.Op = A64Op.FMovFromGpHigh; i.FpSize = 8; break;
                case (_, 0 or 1 or 4 or 5):
                    i.Op = A64Op.FCvtToInt;
                    i.Signed = (opcode & 1) == 0;
                    i.Imm = (long)((opcode >= 4) ? A64Rounding.NearestAway : rmode switch
                    {
                        0 => A64Rounding.Nearest, 1 => A64Rounding.PlusInfinity, 2 => A64Rounding.MinusInfinity, _ => A64Rounding.Zero,
                    });
                    if (opcode >= 4 && rmode != 0) { i.Op = A64Op.Invalid; return true; }
                    break;
                default: return false;
            }
            if (i.FpSize == 0 && i.Op is not (A64Op.FMovToGpHigh or A64Op.FMovFromGpHigh)) i.Op = A64Op.Invalid;
            return true;
        }
        if (Bit(w, 31) || Bit(w, 29) || !Bit(w, 21)) return false;
        i.FpSize = FpSizeOf(ptype);
        if (i.FpSize == 0) return false;
        if ((w & 0x5F207C00) == 0x1E204000)
        {
            // FP data processing (1 source)
            uint opcode = Bits(w, 20, 15);
            switch (opcode)
            {
                case 0: i.Op = A64Op.FMov; return true;
                case 1: i.Op = A64Op.FAbs; return true;
                case 2: i.Op = A64Op.FNeg; return true;
                case 3: i.Op = A64Op.FSqrt; return true;
                case 4 or 5 or 7:
                    i.Op = A64Op.FCvt;
                    i.Imm = opcode == 4 ? 4 : opcode == 5 ? 8 : 2;
                    return true;
                case >= 8 and <= 15 when opcode != 13:
                    i.Op = A64Op.FRint;
                    i.Imm = (long)(opcode switch
                    {
                        8 => A64Rounding.Nearest, 9 => A64Rounding.PlusInfinity, 10 => A64Rounding.MinusInfinity,
                        11 => A64Rounding.Zero, 12 => A64Rounding.NearestAway, 14 => A64Rounding.CurrentExact, _ => A64Rounding.Current,
                    });
                    return true;
            }
            i.Op = A64Op.Unknown;
            return true;
        }
        if ((w & 0x5F203C00) == 0x1E202000)
        {
            // FP compare
            uint opcode2 = Bits(w, 4, 0);
            if ((opcode2 & 7) != 0 || Bits(w, 15, 14) != 0) return false;
            i.Op = (opcode2 & 0x10) != 0 ? A64Op.FCmpe : A64Op.FCmp;
            i.Imm = (opcode2 & 8) != 0 ? 1 : 0;
            return true;
        }
        if ((w & 0x5F201FE0) == 0x1E201000)
        {
            i.Op = A64Op.FMovImm;
            i.Imm = Bits(w, 20, 13);
            return true;
        }
        if ((w & 0x5F200C00) == 0x1E200400)
        {
            i.Op = Bit(w, 4) ? A64Op.FCcmpe : A64Op.FCcmp;
            i.Cond = (byte)Bits(w, 15, 12);
            i.Imm = Bits(w, 3, 0);
            return true;
        }
        if ((w & 0x5F200C00) == 0x1E200800)
        {
            i.Op = Bits(w, 15, 12) switch
            {
                0 => A64Op.FMul, 1 => A64Op.FDiv, 2 => A64Op.FAdd, 3 => A64Op.FSub, 4 => A64Op.FMax, 5 => A64Op.FMin,
                6 => A64Op.FMaxNm, 7 => A64Op.FMinNm, 8 => A64Op.FNMul, _ => A64Op.Invalid,
            };
            return true;
        }
        if ((w & 0x5F200C00) == 0x1E200C00)
        {
            i.Op = A64Op.FCsel;
            i.Cond = (byte)Bits(w, 15, 12);
            return true;
        }
        return false;
    }

    /// <summary>The 64-bit value an AdvSIMD modified immediate stands for (AdvSIMDExpandImm), or null when reserved.</summary>
    public static ulong? ExpandSimdImmediate(int op, int cmode, ulong imm8)
    {
        static ulong Replicate32(ulong v) => (v & 0xFFFFFFFF) | (v & 0xFFFFFFFF) << 32;
        static ulong Replicate16(ulong v) => Replicate32((v & 0xFFFF) | (v & 0xFFFF) << 16);
        switch (cmode >> 1)
        {
            case 0: return Replicate32(imm8);
            case 1: return Replicate32(imm8 << 8);
            case 2: return Replicate32(imm8 << 16);
            case 3: return Replicate32(imm8 << 24);
            case 4: return Replicate16(imm8);
            case 5: return Replicate16(imm8 << 8);
            case 6:
                return (cmode & 1) == 0 ? Replicate32(imm8 << 8 | 0xFF) : Replicate32(imm8 << 16 | 0xFFFF);
        }
        // cmode 1110 / 1111
        if ((cmode & 1) == 0)
        {
            if (op == 0)
            {
                ulong b = imm8 & 0xFF;
                return b | b << 8 | b << 16 | b << 24 | b << 32 | b << 40 | b << 48 | b << 56;
            }
            ulong result = 0;
            for (int bit = 0; bit < 8; bit++)
                if ((imm8 >> bit & 1) != 0)
                    result |= 0xFFUL << (bit * 8);
            return result;
        }
        if (op == 0)
        {
            // single-precision FMOV immediate, replicated
            ulong a = imm8 >> 7 & 1, b = imm8 >> 6 & 1, rest = imm8 & 0x3F;
            ulong bits = a << 31 | (b ^ 1) << 30 | (b != 0 ? 0x1FUL << 25 : 0) | rest << 19;
            return Replicate32(bits);
        }
        {
            ulong a = imm8 >> 7 & 1, b = imm8 >> 6 & 1, rest = imm8 & 0x3F;
            return a << 63 | (b ^ 1) << 62 | (b != 0 ? 0xFFUL << 54 : 0) | rest << 48;
        }
    }

    /// <summary>The FP value of an 8-bit FMOV immediate, as the bits of a float (size 4) or double (size 8).</summary>
    public static ulong FpImmediate(int imm8, int size)
    {
        ulong a = (ulong)(imm8 >> 7 & 1), b = (ulong)(imm8 >> 6 & 1), rest = (ulong)(imm8 & 0x3F);
        return size switch
        {
            8 => a << 63 | (b ^ 1) << 62 | (b != 0 ? 0xFFUL << 54 : 0) | rest << 48,
            4 => a << 31 | (b ^ 1) << 30 | (b != 0 ? 0x1FUL << 25 : 0) | rest << 19,
            _ => a << 15 | (b ^ 1) << 14 | (b != 0 ? 0x3UL << 12 : 0) | rest << 6,
        };
    }

    /// <summary>Which class of SIMD instruction an encoding the decoder leaves as <see cref="A64Op.Vector"/> is (for statistics).</summary>
    public static string VectorClass(uint w)
    {
        if ((w & 0xBF000000) == 0x0C000000 || (w & 0xBF000000) == 0x0D000000) return (Bit(w, 22) ? "ld" : "st") + (Bit(w, 24) ? " single structure" : " multiple structures");
        if ((w & 0x9F200400) == 0x0E200400) return $"three same U{Bits(w, 29, 29)} size{Bits(w, 23, 22)} op{Bits(w, 15, 11):X}";
        if ((w & 0x9F3E0C00) == 0x0E200800) return $"two-reg misc U{Bits(w, 29, 29)} size{Bits(w, 23, 22)} op{Bits(w, 16, 12):X}";
        if ((w & 0x9F3E0C00) == 0x0E300800) return $"across lanes U{Bits(w, 29, 29)} op{Bits(w, 16, 12):X}";
        if ((w & 0xBF208C00) == 0x0E000800) return $"permute op{Bits(w, 14, 12)}";
        if ((w & 0xBF208400) == 0x2E000000) return "ext";
        if ((w & 0xBF208C00) == 0x0E000000) return "table lookup";
        if ((w & 0x9F800400) == 0x0F000400) return $"shift by immediate U{Bits(w, 29, 29)} op{Bits(w, 15, 11):X}";
        if ((w & 0x9F200400) == 0x0E200000) return $"three different U{Bits(w, 29, 29)} op{Bits(w, 15, 12):X}";
        if ((w & 0x9F000400) == 0x0F000000) return $"by element U{Bits(w, 29, 29)} op{Bits(w, 15, 12):X}";
        if ((w & 0xDF3E0C00) == 0x5E300800) return $"scalar pairwise U{Bits(w, 29, 29)} op{Bits(w, 16, 12):X}";
        if ((w & 0xDF200400) == 0x5E200400) return $"scalar three same U{Bits(w, 29, 29)} op{Bits(w, 15, 11):X}";
        if ((w & 0xDF3E0C00) == 0x5E200800) return $"scalar two-reg misc U{Bits(w, 29, 29)} op{Bits(w, 16, 12):X}";
        if ((w & 0xDF800400) == 0x5F000400) return $"scalar shift by immediate U{Bits(w, 29, 29)} op{Bits(w, 15, 11):X}";
        if ((w & 0xDF000400) == 0x5F000000) return $"scalar by element op{Bits(w, 15, 12):X}";
        if ((w & 0x9FF80400) == 0x0F000400) return "modified immediate (orr/bic)";
        return $"other 0x{w:X8}";
    }

    private static void Advanced(uint w, ref A64Instruction i)
    {
        bool q = Bit(w, 30);
        i.Imm2 = q ? 1 : 0;
        if ((w & 0x9FF80400) == 0x0F000400)
        {
            // modified immediate: MOVI, MVNI, ORR, BIC, FMOV (vector)
            int op = (int)Bits(w, 29, 29), cmode = (int)Bits(w, 15, 12);
            ulong imm8 = Bits(w, 18, 16) << 5 | Bits(w, 9, 5);
            bool isOrrBic = cmode < 12 && (cmode & 1) == 1;
            if (isOrrBic)
            {
                if (ExpandSimdImmediate(op, cmode, imm8) is not ulong mask) return;
                i.Op = op == 0 ? A64Op.VOrImm : A64Op.VBicImm;
                i.Target = mask;
                return;
            }
            if (cmode == 15 && op == 1 && !q) return;
            ulong? value = ExpandSimdImmediate(op, cmode, imm8);
            if (value == null) return;
            ulong pattern = value.Value;
            // MVNI: the inverted pattern (cmode 1110 with op 1 is MOVI's 64-bit form, not MVNI).
            if (op == 1 && cmode < 14) pattern = ~pattern;
            i.Op = A64Op.Movi;
            i.Target = pattern;
            return;
        }
        if ((w & 0x9FE08400) == 0x0E000400)
        {
            // copy: DUP, INS, UMOV, SMOV
            uint imm5 = Bits(w, 20, 16), imm4 = Bits(w, 14, 11);
            int size = System.Numerics.BitOperations.TrailingZeroCount(imm5);
            if (size > 3) return;
            i.ElemSize = (byte)(1 << size);
            i.Imm = imm5 >> (size + 1);
            if (Bit(w, 29))
            {
                if (!q) return;
                i.Op = A64Op.Ins;
                i.Imm2 = imm4 >> size;
                return;
            }
            switch (imm4)
            {
                case 0: i.Op = A64Op.Dup; break;
                case 1: i.Op = A64Op.DupGp; break;
                case 3 when q: i.Op = A64Op.InsGp; break;
                case 5: i.Op = A64Op.Smov; i.Is64 = q; break;
                case 7: i.Op = A64Op.Umov; i.Is64 = q; break;
                default: return;
            }
            i.Imm2 = q ? 1 : 0;
            return;
        }
        if (DecodeVec(w, ref i)) return;
        if ((w & 0xFFE0FC00) == 0x5E000400)
        {
            // DUP (element), scalar: "mov s0, v1.s[1]"
            uint imm5 = Bits(w, 20, 16);
            int size = System.Numerics.BitOperations.TrailingZeroCount(imm5);
            if (size > 3) return;
            i.ElemSize = (byte)(1 << size);
            i.Imm = imm5 >> (size + 1);
            i.Op = A64Op.DupScalar;
            return;
        }
        if ((w & 0x9F200400) == 0x0E200400)
        {
            // three registers of the same type
            uint u = Bits(w, 29, 29), size = Bits(w, 23, 22), opcode = Bits(w, 15, 11);
            if (opcode == 0b00011)
            {
                // logical: AND, BIC, ORR, ORN (u=0); EOR, BSL, BIT, BIF (u=1)
                i.Op = (u, size) switch
                {
                    (0, 0) => A64Op.VAnd,
                    (0, 1) => A64Op.VBic,
                    (0, 2) => i.Rn == i.Rm ? A64Op.VMov : A64Op.VOrr,
                    (1, 0) => A64Op.VEor,
                    _ => A64Op.Vector,
                };
                return;
            }
            bool sz = (size & 1) != 0, high = (size & 2) != 0;
            i.ElemSize = (byte)(sz ? 8 : 4);
            if (sz && !q) { i.Op = A64Op.Vector; return; }
            i.Op = (u, high, opcode) switch
            {
                (0, false, 0b11010) => A64Op.VFAdd,
                (0, true, 0b11010) => A64Op.VFSub,
                (1, false, 0b11011) => A64Op.VFMul,
                (1, false, 0b11111) => A64Op.VFDiv,
                _ => A64Op.Vector,
            };
            return;
        }
        i.Op = A64Op.Vector;
    }
}
