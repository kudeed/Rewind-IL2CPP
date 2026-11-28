namespace Rewind.Analysis.Arm64;

/// <summary>
/// The SIMD operations the lifter takes apart element by element (A64Op.VecOp, in Imm). Elements are ElemSize
/// bytes; the vector is 16 bytes when Q (Imm2 bit 0) is set, 8 otherwise; Imm2 bit 1 marks the scalar form (one
/// element, the rest of the register cleared).
/// </summary>
public enum VecKind : byte
{
    None,
    // integer, element-wise
    Add, Sub, Mul, CmEq, CmTst, CmGt, CmGe, CmHi, CmHs, SMax, SMin, UMax, UMin, Bsl, Bit, Bif,
    Neg, Abs, Not, CmEqZero, CmGtZero, CmGeZero, CmLeZero, CmLtZero,
    // floating point, element-wise
    FAdd, FSub, FMul, FDiv, FMla, FMls, FMax, FMin, FMaxNm, FMinNm, FAbd, FCmEq, FCmGe, FCmGt, FNeg, FAbs, FSqrt,
    Scvtf, Ucvtf, FCvtzs, FCvtzu,
    // by element: the second operand is element Amount of Rm
    MulElem, MlaElem, MlsElem, FMulElem, FMlaElem, FMlsElem,
    // shifts by an immediate (Amount)
    Shl, Ushr, Sshr,
    /// <summary>Widening (Amount: shift): the low (or, with Q, high) half's elements to twice their size.</summary>
    Ushll, Sshll,
    /// <summary>Narrowing: elements of twice ElemSize cut to ElemSize, into the low (or, with Q, high) half.</summary>
    Xtn,
    // rearranging
    Zip1, Zip2, Uzp1, Uzp2, Trn1, Trn2,
    /// <summary>Bytes Amount and on of Rn:Rm (EXT).</summary>
    Ext,
    // reductions
    /// <summary>Scalar pairwise: element 0 + element 1 (FADDP, ADDP).</summary>
    FAddPair, AddPair,
    AddV, SMaxV, SMinV, UMaxV, UMinV, FMaxV, FMinV, FMaxNmV, FMinNmV,
    // floating-point comparison with zero; appended to preserve existing kind values
    FCmLtZero,
}

public static partial class A64Decoder
{
    private static byte ElemBytes(uint size) => (byte)(1 << (int)size);

    /// <summary>The SIMD encodings taken apart element by element; false when the encoding is none of them.</summary>
    private static bool DecodeVec(uint w, ref A64Instruction i)
    {
        bool q = Bit(w, 30), u = Bit(w, 29);
        uint size = Bits(w, 23, 22);
        bool sz = (size & 1) != 0, a = (size & 2) != 0;
        VecKind kind = VecKind.None;
        bool scalar = false;

        if ((w & 0x9F200400) == 0x0E200400 || (w & 0xDF200400) == 0x5E200400)
        {
            // three registers of the same type (vector, or scalar)
            scalar = (w & 0xDF200400) == 0x5E200400;
            uint opcode = Bits(w, 15, 11);
            bool fp = opcode >= 0b11000;
            if (fp)
            {
                kind = (u, a, opcode) switch
                {
                    (false, false, 0b11010) => VecKind.FAdd,
                    (false, true, 0b11010) => VecKind.FSub,
                    (true, true, 0b11010) => VecKind.FAbd,
                    (true, false, 0b11011) => VecKind.FMul,
                    (true, false, 0b11111) => VecKind.FDiv,
                    (false, false, 0b11001) => VecKind.FMla,
                    (false, true, 0b11001) => VecKind.FMls,
                    (false, false, 0b11100) => VecKind.FCmEq,
                    (true, false, 0b11100) => VecKind.FCmGe,
                    (true, true, 0b11100) => VecKind.FCmGt,
                    (false, false, 0b11110) => VecKind.FMax,
                    (false, true, 0b11110) => VecKind.FMin,
                    (false, false, 0b11000) => VecKind.FMaxNm,
                    (false, true, 0b11000) => VecKind.FMinNm,
                    _ => VecKind.None,
                };
                i.ElemSize = (byte)(sz ? 8 : 4);
                if (!scalar && sz && !q) kind = VecKind.None;
                if (scalar && kind is VecKind.FMla or VecKind.FMls) kind = VecKind.None;
            }
            else
            {
                kind = (u, opcode) switch
                {
                    (false, 0b10000) => VecKind.Add,
                    (true, 0b10000) => VecKind.Sub,
                    (false, 0b10011) when size != 3 => VecKind.Mul,
                    (true, 0b10001) => VecKind.CmEq,
                    (false, 0b10001) => VecKind.CmTst,
                    (false, 0b00110) => VecKind.CmGt,
                    (false, 0b00111) => VecKind.CmGe,
                    (true, 0b00110) => VecKind.CmHi,
                    (true, 0b00111) => VecKind.CmHs,
                    (false, 0b01100) => VecKind.SMax,
                    (false, 0b01101) => VecKind.SMin,
                    (true, 0b01100) => VecKind.UMax,
                    (true, 0b01101) => VecKind.UMin,
                    (true, 0b00011) when size == 1 => VecKind.Bsl,
                    (true, 0b00011) when size == 2 => VecKind.Bit,
                    (true, 0b00011) when size == 3 => VecKind.Bif,
                    _ => VecKind.None,
                };
                i.ElemSize = kind is VecKind.Bsl or VecKind.Bit or VecKind.Bif ? (byte)8 : ElemBytes(size);
                if (scalar && size != 3) kind = VecKind.None;
                if (!scalar && size == 3 && !q) kind = VecKind.None;
            }
        }
        else if ((w & 0x9F3E0C00) == 0x0E200800 || (w & 0xDF3E0C00) == 0x5E200800)
        {
            // two-register miscellaneous (vector, or scalar)
            scalar = (w & 0xDF3E0C00) == 0x5E200800;
            uint opcode = Bits(w, 16, 12);
            i.ElemSize = ElemBytes(size);
            switch (opcode)
            {
                case 0b01011: kind = u ? VecKind.Neg : VecKind.Abs; break;
                case 0b00101 when u && size == 0 && !scalar: kind = VecKind.Not; break;
                case 0b01001: kind = u ? VecKind.CmLeZero : VecKind.CmEqZero; break;
                case 0b01000: kind = u ? VecKind.CmGeZero : VecKind.CmGtZero; break;
                case 0b01010 when !u: kind = VecKind.CmLtZero; break;
                case 0b10010 when !u && !scalar && size != 3: kind = VecKind.Xtn; break;
                case 0b01110 when a && !u: kind = VecKind.FCmLtZero; i.ElemSize = (byte)(sz ? 8 : 4); break;
                case 0b01111 when a: kind = u ? VecKind.FNeg : VecKind.FAbs; i.ElemSize = (byte)(sz ? 8 : 4); break;
                case 0b11111 when a && u: kind = VecKind.FSqrt; i.ElemSize = (byte)(sz ? 8 : 4); break;
                case 0b11101 when !a: kind = u ? VecKind.Ucvtf : VecKind.Scvtf; i.ElemSize = (byte)(sz ? 8 : 4); break;
                case 0b11011 when a: kind = u ? VecKind.FCvtzu : VecKind.FCvtzs; i.ElemSize = (byte)(sz ? 8 : 4); break;
            }
            if (scalar && kind is VecKind.Not or VecKind.Xtn) kind = VecKind.None;
            if (scalar && kind is VecKind.Neg or VecKind.Abs or VecKind.CmEqZero or VecKind.CmGtZero or VecKind.CmGeZero or VecKind.CmLeZero or VecKind.CmLtZero && size != 3)
                kind = VecKind.None;
            if (!scalar && i.ElemSize == 8 && !q && kind != VecKind.Xtn) kind = VecKind.None;
        }
        else if ((w & 0xDF3E0C00) == 0x5E300800)
        {
            // scalar pairwise
            uint opcode = Bits(w, 16, 12);
            scalar = true;
            if (u && opcode == 0b01101 && !a) { kind = VecKind.FAddPair; i.ElemSize = (byte)(sz ? 8 : 4); }
            else if (!u && opcode == 0b11011 && size == 3) { kind = VecKind.AddPair; i.ElemSize = 8; }
        }
        else if ((w & 0x9F3E0C00) == 0x0E300800)
        {
            // across lanes
            uint opcode = Bits(w, 16, 12);
            i.ElemSize = ElemBytes(size);
            kind = (u, opcode) switch
            {
                (false, 0b11011) => VecKind.AddV,
                (false, 0b01010) => VecKind.SMaxV,
                (true, 0b01010) => VecKind.UMaxV,
                (false, 0b11010) => VecKind.SMinV,
                (true, 0b11010) => VecKind.UMinV,
                (true, 0b01111) => a ? VecKind.FMinV : VecKind.FMaxV,
                (true, 0b01100) => a ? VecKind.FMinNmV : VecKind.FMaxNmV,
                _ => VecKind.None,
            };
            if (kind is VecKind.FMaxV or VecKind.FMinV or VecKind.FMaxNmV or VecKind.FMinNmV)
            {
                i.ElemSize = 4;
                if (sz || !q) kind = VecKind.None;
            }
            else if (size == 3) kind = VecKind.None;
        }
        else if ((w & 0xBF208C00) == 0x0E000800)
        {
            // permute
            i.ElemSize = ElemBytes(size);
            kind = Bits(w, 14, 12) switch
            {
                1 => VecKind.Uzp1, 2 => VecKind.Trn1, 3 => VecKind.Zip1, 5 => VecKind.Uzp2, 6 => VecKind.Trn2, 7 => VecKind.Zip2, _ => VecKind.None,
            };
            if (size == 3 && !q) kind = VecKind.None;
        }
        else if ((w & 0xBF208400) == 0x2E000000)
        {
            kind = VecKind.Ext;
            i.ElemSize = 1;
            i.Amount = (byte)Bits(w, 14, 11);
            if (!q && i.Amount >= 8) kind = VecKind.None;
        }
        else if ((w & 0x9F800400) == 0x0F000400 && Bits(w, 22, 19) != 0)
        {
            // shift by immediate
            uint immh = Bits(w, 22, 19), shiftField = Bits(w, 22, 16);
            int esize = immh >= 8 ? 8 : immh >= 4 ? 4 : immh >= 2 ? 2 : 1;
            uint opcode = Bits(w, 15, 11);
            i.ElemSize = (byte)esize;
            switch (opcode)
            {
                case 0b00000:
                    kind = u ? VecKind.Ushr : VecKind.Sshr;
                    i.Amount = (byte)(esize * 16 - shiftField);
                    break;
                case 0b01010 when !u:
                    kind = VecKind.Shl;
                    i.Amount = (byte)(shiftField - esize * 8);
                    break;
                case 0b10100 when esize < 8:
                    kind = u ? VecKind.Ushll : VecKind.Sshll;
                    i.Amount = (byte)(shiftField - esize * 8);
                    break;
            }
            if (esize == 8 && !q && kind is not (VecKind.Ushll or VecKind.Sshll)) kind = VecKind.None;
        }
        else if ((w & 0x9F000400) == 0x0F000000 || (w & 0xDF000400) == 0x5F000000)
        {
            // by element
            scalar = (w & 0xDF000400) == 0x5F000000;
            uint opcode = Bits(w, 15, 12);
            uint h = Bits(w, 11, 11), l = Bits(w, 21, 21), m = Bits(w, 20, 20);
            bool fp = opcode is 0b1001 or 0b0001 or 0b0101 && !u;
            if (fp)
            {
                kind = opcode switch { 0b1001 => VecKind.FMulElem, 0b0001 => VecKind.FMlaElem, _ => VecKind.FMlsElem };
                if (!sz) { i.ElemSize = 4; i.Amount = (byte)(h << 1 | l); i.Rm = (byte)Bits(w, 20, 16); }
                else if (l == 0) { i.ElemSize = 8; i.Amount = (byte)h; i.Rm = (byte)Bits(w, 20, 16); if (!q && !scalar) kind = VecKind.None; }
                else kind = VecKind.None;
                // (Bit 23 is set in the single- and double-precision forms; clear, it is the half-precision one.)
                if (!a) kind = VecKind.None;
            }
            else if (!scalar && opcode is 0b1000 or 0b0000 or 0b0100 && (opcode == 0b1000 ? !u : u))
            {
                kind = opcode switch { 0b1000 => VecKind.MulElem, 0b0000 => VecKind.MlaElem, _ => VecKind.MlsElem };
                if (size == 1) { i.ElemSize = 2; i.Amount = (byte)(h << 2 | l << 1 | m); i.Rm = (byte)Bits(w, 19, 16); }
                else if (size == 2) { i.ElemSize = 4; i.Amount = (byte)(h << 1 | l); i.Rm = (byte)Bits(w, 20, 16); }
                else kind = VecKind.None;
            }
        }
        if (kind == VecKind.None) return false;
        i.Op = A64Op.VecOp;
        i.Imm = (long)kind;
        i.Imm2 = (q ? 1 : 0) | (scalar ? 2 : 0);
        return true;
    }

    /// <summary>
    /// LD1/ST1 of one register (16 or 8 bytes, as LDR/STR of a Q or D register), and LD1/ST1 of one element
    /// (A64Op.Ld1Lane / St1Lane / Ld1R), with or without a post-index.
    /// </summary>
    private static bool DecodeStructure(uint w, ref A64Instruction i)
    {
        bool q = Bit(w, 30), load = Bit(w, 22), post = Bit(w, 23);
        byte rm = (byte)Bits(w, 20, 16);
        i.Rn = Bits(w, 9, 5) == 31 ? A64Instruction.Sp : (byte)Bits(w, 9, 5);
        i.Rd = (byte)Bits(w, 4, 0);
        i.Vector = true;
        if ((w & 0xBF20F000) == 0x0C007000 && (post || rm == 0))
        {
            // multiple structures, one register: the whole register in byte order
            i.Op = load ? A64Op.Ldr : A64Op.Str;
            i.Size = (byte)(q ? 16 : 8);
            i.Mode = post ? A64Mode.PostIndex : A64Mode.Offset;
            i.Imm = post ? i.Size : 0;
            return !post || rm == 31;
        }
        if ((w & 0xBF000000) == 0x0D000000 && !Bit(w, 21) && (post || rm == 0))
        {
            uint opcode = Bits(w, 15, 13), s = Bits(w, 12, 12), size = Bits(w, 11, 10);
            int index;
            byte esize;
            switch (opcode)
            {
                case 0b000: esize = 1; index = (int)((q ? 8u : 0) | s << 2 | size); break;
                case 0b010 when (size & 1) == 0: esize = 2; index = (int)((q ? 4u : 0) | s << 1 | size >> 1); break;
                case 0b100 when size == 0: esize = 4; index = (int)((q ? 2u : 0) | s); break;
                case 0b100 when size == 1 && s == 0: esize = 8; index = q ? 1 : 0; break;
                case 0b110 when load && s == 0: esize = (byte)(1 << (int)size); index = 0; break;
                default: return false;
            }
            i.Op = opcode == 0b110 ? A64Op.Ld1R : load ? A64Op.Ld1Lane : A64Op.St1Lane;
            i.ElemSize = esize;
            i.Size = esize;
            i.Amount = (byte)index;
            i.Imm2 = q ? 1 : 0;
            i.Mode = post ? A64Mode.PostIndex : A64Mode.Offset;
            i.Imm = post ? esize : 0;
            return !post || rm == 31;
        }
        return false;
    }
}
