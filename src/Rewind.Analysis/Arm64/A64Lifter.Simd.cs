using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Arm64;

/// <summary>
/// SIMD instructions, lifted element by element over the four 32-bit lanes a register is kept in: what the
/// vector instruction computes is written out for each element as the scalar operation it is.
/// </summary>
public sealed partial class A64Lifter
{
    private static VT ElemType(int bytes) => VTExtensions.IntOfBytes(bytes);

    /// <summary>Element <paramref name="index"/> (of <paramref name="bytes"/> bytes) of SIMD register <paramref name="v"/>.</summary>
    private Node Elem(int v, int bytes, int index)
    {
        if (bytes == 4) return Lane(v, index);
        if (bytes == 8) return Qword(v, index);
        int lane = index * bytes / 4, shift = index * bytes % 4 * 8;
        Node value = Lane(v, lane);
        if (shift != 0) value = _b.Shift(Op.ShrU, value, C(VT.I8, shift));
        return _b.Trunc(value, ElemType(bytes));
    }

    /// <summary>Writes one element, leaving the rest of the register as it is.</summary>
    private void SetElem(int v, int bytes, int index, Node value)
    {
        if (bytes == 4) { SetLane(v, index, value); return; }
        if (bytes == 8) { SetQword(v, index, value); return; }
        int lane = index * bytes / 4, shift = index * bytes % 4 * 8;
        uint mask = (bytes == 1 ? 0xFFu : 0xFFFFu) << shift;
        Node kept = _b.And(Lane(v, lane), C(VT.I32, ~mask));
        Node put = _b.ZExt(value, VT.I32);
        if (shift != 0) put = _b.Shift(Op.Shl, put, C(VT.I8, shift));
        SetLane(v, lane, _b.Or(kept, put));
    }

    /// <summary>
    /// Writes a whole register from its elements; the elements past the given ones (the upper half of a 64-bit
    /// vector, all but the first of a scalar) are zero.
    /// </summary>
    private void SetElems(int v, int bytes, Node?[] elements)
    {
        int perRegister = 16 / bytes;
        Node Element(int k) => k < elements.Length && elements[k] != null ? elements[k]! : C(ElemType(bytes), 0);
        if (bytes == 8)
        {
            SetQword(v, 0, Element(0));
            SetQword(v, 1, Element(1));
            return;
        }
        var lanes = new Node[4];
        int perLane = 4 / bytes;
        for (int lane = 0; lane < 4; lane++)
        {
            if (bytes == 4) { lanes[lane] = Element(lane); continue; }
            Node? combined = null;
            for (int k = 0; k < perLane; k++)
            {
                Node part = _b.ZExt(Element(lane * perLane + k), VT.I32);
                if (k != 0) part = _b.Shift(Op.Shl, part, C(VT.I8, k * bytes * 8));
                combined = combined == null ? part : _b.Or(combined, part);
            }
            lanes[lane] = combined!;
        }
        _ = perRegister;
        for (int lane = 0; lane < 4; lane++) SetLane(v, lane, lanes[lane]);
    }

    private Node AllOnes(Node condition, VT type) => _b.Select(condition, C(type, -1), C(type, 0));

    private Node AsF(Node bits) => _b.BitsToF(bits);
    private Node Bits(Node f) => _b.FToBits(f);

    private void LiftVec(in A64Instruction ins)
    {
        A64Instruction i = ins;
        var kind = (VecKind)i.Imm;
        bool q = (i.Imm2 & 1) != 0, scalar = (i.Imm2 & 2) != 0;
        int bytes = i.ElemSize;
        VT t = ElemType(bytes);
        int count = scalar ? 1 : (q ? 16 : 8) / bytes;
        VT ft = bytes == 8 ? VT.F64 : VT.F32;
        Node A(int k) => Elem(i.Rn, bytes, k);
        Node B(int k) => Elem(i.Rm, bytes, k);
        Node D(int k) => Elem(i.Rd, bytes, k);
        Node F(Node bits) => AsF(bits);
        var result = new Node?[count];

        switch (kind)
        {
            // ---- integer, element-wise
            case VecKind.Add or VecKind.Sub or VecKind.Mul or VecKind.CmEq or VecKind.CmTst or VecKind.CmGt or VecKind.CmGe or VecKind.CmHi or
                VecKind.CmHs or VecKind.SMax or VecKind.SMin or VecKind.UMax or VecKind.UMin:
                for (int k = 0; k < count; k++)
                {
                    Node a = A(k), b = B(k);
                    result[k] = kind switch
                    {
                        VecKind.Add => _b.Add(a, b),
                        VecKind.Sub => _b.Sub(a, b),
                        VecKind.Mul => _b.Mul(a, b),
                        VecKind.CmEq => AllOnes(_b.Cmp(Op.CmpEq, a, b), t),
                        VecKind.CmTst => AllOnes(_b.Cmp(Op.CmpNe, _b.And(a, b), C(t, 0)), t),
                        VecKind.CmGt => AllOnes(_b.Cmp(Op.CmpLtS, b, a), t),
                        VecKind.CmGe => AllOnes(_b.Cmp(Op.CmpLeS, b, a), t),
                        VecKind.CmHi => AllOnes(_b.Cmp(Op.CmpLtU, b, a), t),
                        VecKind.CmHs => AllOnes(_b.Cmp(Op.CmpLeU, b, a), t),
                        VecKind.SMax => _b.Select(_b.Cmp(Op.CmpLtS, a, b), b, a),
                        VecKind.SMin => _b.Select(_b.Cmp(Op.CmpLtS, b, a), b, a),
                        VecKind.UMax => _b.Select(_b.Cmp(Op.CmpLtU, a, b), b, a),
                        _ => _b.Select(_b.Cmp(Op.CmpLtU, b, a), b, a),
                    };
                }
                break;
            case VecKind.Bsl or VecKind.Bit or VecKind.Bif:
                for (int k = 0; k < (q ? 2 : 1); k++)
                {
                    Node d = Qword(i.Rd, k), n = Qword(i.Rn, k), m = Qword(i.Rm, k);
                    result[k] = kind switch
                    {
                        VecKind.Bsl => _b.Or(_b.And(d, n), _b.And(_b.Not(d), m)),
                        VecKind.Bit => _b.Or(_b.And(d, _b.Not(m)), _b.And(n, m)),
                        _ => _b.Or(_b.And(d, m), _b.And(n, _b.Not(m))),
                    };
                }
                SetElems(i.Rd, 8, result);
                return;
            case VecKind.Neg or VecKind.Abs or VecKind.Not or VecKind.CmEqZero or VecKind.CmGtZero or VecKind.CmGeZero or VecKind.CmLeZero or VecKind.CmLtZero:
                for (int k = 0; k < count; k++)
                {
                    Node a = A(k), zero = C(t, 0);
                    result[k] = kind switch
                    {
                        VecKind.Neg => _b.Neg(a),
                        VecKind.Abs => _b.Select(_b.Cmp(Op.CmpLtS, a, zero), _b.Neg(a), a),
                        VecKind.Not => _b.Not(a),
                        VecKind.CmEqZero => AllOnes(_b.Cmp(Op.CmpEq, a, zero), t),
                        VecKind.CmGtZero => AllOnes(_b.Cmp(Op.CmpLtS, zero, a), t),
                        VecKind.CmGeZero => AllOnes(_b.Cmp(Op.CmpLeS, zero, a), t),
                        VecKind.CmLeZero => AllOnes(_b.Cmp(Op.CmpLeS, a, zero), t),
                        _ => AllOnes(_b.Cmp(Op.CmpLtS, a, zero), t),
                    };
                }
                break;

            // ---- floating point, element-wise
            case VecKind.FAdd or VecKind.FSub or VecKind.FMul or VecKind.FDiv or VecKind.FMax or VecKind.FMin or VecKind.FMaxNm or VecKind.FMinNm or
                VecKind.FAbd or VecKind.FMla or VecKind.FMls or VecKind.FCmEq or VecKind.FCmGe or VecKind.FCmGt:
                for (int k = 0; k < count; k++)
                {
                    Node a = F(A(k)), b = F(B(k));
                    result[k] = kind switch
                    {
                        VecKind.FAdd => Bits(_b.Raw(Op.FAdd, ft, a, b)),
                        VecKind.FSub => Bits(_b.Raw(Op.FSub, ft, a, b)),
                        VecKind.FMul => Bits(_b.Raw(Op.FMul, ft, a, b)),
                        VecKind.FDiv => Bits(_b.Raw(Op.FDiv, ft, a, b)),
                        VecKind.FMax or VecKind.FMaxNm => Bits(_b.Raw(Op.FMax, ft, a, b)),
                        VecKind.FMin or VecKind.FMinNm => Bits(_b.Raw(Op.FMin, ft, a, b)),
                        VecKind.FAbd => Bits(_b.Raw(Op.FAbs, ft, _b.Raw(Op.FSub, ft, a, b))),
                        VecKind.FMla => Bits(_b.Raw(Op.FAdd, ft, F(D(k)), _b.Raw(Op.FMul, ft, a, b))),
                        VecKind.FMls => Bits(_b.Raw(Op.FSub, ft, F(D(k)), _b.Raw(Op.FMul, ft, a, b))),
                        VecKind.FCmEq => AllOnes(_b.Raw(Op.FCmpEq, VT.I1, a, b), t),
                        VecKind.FCmGe => AllOnes(_b.Raw(Op.FCmpLe, VT.I1, b, a), t),
                        _ => AllOnes(_b.Raw(Op.FCmpLt, VT.I1, b, a), t),
                    };
                }
                break;
            case VecKind.FNeg or VecKind.FAbs or VecKind.FSqrt:
                for (int k = 0; k < count; k++)
                {
                    Op op = kind switch { VecKind.FNeg => Op.FNeg, VecKind.FAbs => Op.FAbs, _ => Op.FSqrt };
                    result[k] = Bits(_b.Raw(op, ft, F(A(k))));
                }
                break;
            case VecKind.FCmLtZero:
                for (int k = 0; k < count; k++)
                    result[k] = AllOnes(_b.Raw(Op.FCmpLt, VT.I1, F(A(k)), FZero(ft)), t);
                break;
            case VecKind.Scvtf or VecKind.Ucvtf:
                for (int k = 0; k < count; k++)
                    result[k] = Bits(_b.Raw(kind == VecKind.Scvtf ? Op.SIntToF : Op.UIntToF, ft, A(k)));
                break;
            case VecKind.FCvtzs or VecKind.FCvtzu:
                for (int k = 0; k < count; k++)
                    result[k] = SaturatingFloatToInt(F(A(k)), t, kind == VecKind.FCvtzs);
                break;

            // ---- by element
            case VecKind.MulElem or VecKind.MlaElem or VecKind.MlsElem:
            {
                Node b = Elem(i.Rm, bytes, i.Amount);
                for (int k = 0; k < count; k++)
                {
                    Node product = _b.Mul(A(k), b);
                    result[k] = kind switch { VecKind.MulElem => product, VecKind.MlaElem => _b.Add(D(k), product), _ => _b.Sub(D(k), product) };
                }
                break;
            }
            case VecKind.FMulElem or VecKind.FMlaElem or VecKind.FMlsElem:
            {
                Node b = F(Elem(i.Rm, bytes, i.Amount));
                for (int k = 0; k < count; k++)
                {
                    Node product = _b.Raw(Op.FMul, ft, F(A(k)), b);
                    result[k] = Bits(kind switch
                    {
                        VecKind.FMulElem => product,
                        VecKind.FMlaElem => _b.Raw(Op.FAdd, ft, F(D(k)), product),
                        _ => _b.Raw(Op.FSub, ft, F(D(k)), product),
                    });
                }
                break;
            }

            // ---- shifts and size changes
            case VecKind.Shl or VecKind.Ushr or VecKind.Sshr:
                for (int k = 0; k < count; k++)
                {
                    Node a = A(k);
                    int width = bytes * 8;
                    result[k] = kind switch
                    {
                        VecKind.Shl => _b.Shift(Op.Shl, a, C(VT.I8, i.Amount)),
                        VecKind.Ushr => i.Amount >= width ? C(t, 0) : _b.Shift(Op.ShrU, a, C(VT.I8, i.Amount)),
                        _ => _b.Shift(Op.ShrS, a, C(VT.I8, Math.Min(i.Amount, width - 1))),
                    };
                }
                break;
            case VecKind.Ushll or VecKind.Sshll:
            {
                int wide = bytes * 2, n = 8 / bytes, first = q ? n : 0;
                var widened = new Node?[n];
                for (int k = 0; k < n; k++)
                {
                    Node e = Widen(Elem(i.Rn, bytes, first + k), ElemType(wide), kind == VecKind.Sshll);
                    widened[k] = i.Amount == 0 ? e : _b.Shift(Op.Shl, e, C(VT.I8, i.Amount));
                }
                SetElems(i.Rd, wide, widened);
                return;
            }
            case VecKind.Xtn:
            {
                int n = 8 / bytes;
                var narrowed = new Node[n];
                for (int k = 0; k < n; k++) narrowed[k] = _b.Trunc(Elem(i.Rn, bytes * 2, k), t);
                if (!q)
                {
                    SetElems(i.Rd, bytes, narrowed);
                    return;
                }
                for (int k = 0; k < n; k++) SetElem(i.Rd, bytes, n + k, narrowed[k]);
                return;
            }

            // ---- rearranging
            case VecKind.Zip1 or VecKind.Zip2 or VecKind.Uzp1 or VecKind.Uzp2 or VecKind.Trn1 or VecKind.Trn2:
            {
                var a = new Node[count];
                var b = new Node[count];
                for (int k = 0; k < count; k++) { a[k] = A(k); b[k] = B(k); }
                int half = count / 2;
                for (int k = 0; k < count; k++)
                {
                    int pair = k / 2;
                    bool second = (k & 1) != 0;
                    result[k] = kind switch
                    {
                        VecKind.Zip1 => second ? b[pair] : a[pair],
                        VecKind.Zip2 => second ? b[half + pair] : a[half + pair],
                        VecKind.Uzp1 => k < half ? a[2 * k] : b[2 * (k - half)],
                        VecKind.Uzp2 => k < half ? a[2 * k + 1] : b[2 * (k - half) + 1],
                        VecKind.Trn1 => second ? b[k - 1] : a[k],
                        _ => second ? b[k] : a[k + 1],
                    };
                }
                break;
            }
            case VecKind.Ext:
            {
                int length = q ? 16 : 8;
                for (int k = 0; k < length; k++)
                {
                    int from = i.Amount + k;
                    result = result.Length == length ? result : new Node?[length];
                    result[k] = from < length ? Elem(i.Rn, 1, from) : Elem(i.Rm, 1, from - length);
                }
                SetElems(i.Rd, 1, result);
                return;
            }

            // ---- reductions
            case VecKind.FAddPair:
                SetScalarBits(i.Rd, Bits(_b.Raw(Op.FAdd, ft, F(Elem(i.Rn, bytes, 0)), F(Elem(i.Rn, bytes, 1)))), bytes);
                return;
            case VecKind.AddPair:
                SetScalarBits(i.Rd, _b.Add(Qword(i.Rn, 0), Qword(i.Rn, 1)), 8);
                return;
            case VecKind.AddV or VecKind.SMaxV or VecKind.SMinV or VecKind.UMaxV or VecKind.UMinV or VecKind.FMaxV or VecKind.FMinV or VecKind.FMaxNmV or VecKind.FMinNmV:
            {
                int n = (q ? 16 : 8) / bytes;
                Node acc = A(0);
                for (int k = 1; k < n; k++)
                {
                    Node e = A(k);
                    acc = kind switch
                    {
                        VecKind.AddV => _b.Add(acc, e),
                        VecKind.SMaxV => _b.Select(_b.Cmp(Op.CmpLtS, acc, e), e, acc),
                        VecKind.SMinV => _b.Select(_b.Cmp(Op.CmpLtS, e, acc), e, acc),
                        VecKind.UMaxV => _b.Select(_b.Cmp(Op.CmpLtU, acc, e), e, acc),
                        VecKind.UMinV => _b.Select(_b.Cmp(Op.CmpLtU, e, acc), e, acc),
                        VecKind.FMaxV or VecKind.FMaxNmV => Bits(_b.Raw(Op.FMax, VT.F32, F(acc), F(e))),
                        _ => Bits(_b.Raw(Op.FMin, VT.F32, F(acc), F(e))),
                    };
                }
                SetScalarBits(i.Rd, bytes < 4 ? _b.ZExt(acc, VT.I32) : acc, bytes == 8 ? 8 : 4);
                return;
            }
            default:
                Unknown(i, "VecOp " + kind);
                return;
        }

        if (scalar)
        {
            Node r = result[0]!;
            SetScalarBits(i.Rd, bytes < 4 ? _b.ZExt(r, VT.I32) : r, bytes == 8 ? 8 : 4);
            return;
        }
        SetElems(i.Rd, bytes, result);
    }

    /// <summary>LD1/ST1 of one element, and LD1R (one element loaded into every element).</summary>
    private void LiftLaneAccess(in A64Instruction i)
    {
        var (address, back) = AddressOf(i);
        int bytes = i.ElemSize;
        bool q = (i.Imm2 & 1) != 0;
        switch (i.Op)
        {
            case A64Op.Ld1Lane:
                SetElem(i.Rd, bytes, i.Amount, LoadAt(address, ElemType(bytes)));
                break;
            case A64Op.St1Lane:
                _b.Store(address, Elem(i.Rd, bytes, i.Amount));
                break;
            default:
            {
                Node value = LoadAt(address, ElemType(bytes));
                var all = new Node?[(q ? 16 : 8) / bytes];
                for (int k = 0; k < all.Length; k++) all[k] = value;
                SetElems(i.Rd, bytes, all);
                break;
            }
        }
        WriteBack(i, back);
    }
}
