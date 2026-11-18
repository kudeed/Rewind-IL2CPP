using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Passes;

/// <summary>
/// A 64-bit division by a constant, as compilers emit it: the high half of a multiplication by a "magic"
/// number, shifted, with a correction for negative dividends (signed) or an added step for large magic numbers
/// (unsigned). C# has no 128-bit multiplication to say that with; the division the compiler started from says
/// it exactly.
///
/// A constant is accepted only when computing the magic number and shift for it (the method of Hacker's
/// Delight, chapter 10, which MSVC and LLVM use) gives back exactly the ones in the code. The result is then
/// the quotient for every dividend, and the sequence becomes "x / c".
/// </summary>
public static class ConstantDivisions
{
    public static bool Run(Function fn)
    {
        bool changed = false;
        foreach (Block b in fn.Blocks)
            foreach (Node n in b.Nodes)
            {
                if (n.Dead || n.Type != VT.I64 || n.In.Length != 2) continue;
                (Node X, ulong D, bool Signed)? found = Signed(n) is var (sx, sd) ? (sx, (ulong)sd, true)
                    : Unsigned(n) is var (ux, ud) ? (ux, ud, false) : null;
                if (found is not var (x, d, signed)) continue;
                Node divisor = fn.NewNode(Op.Const, VT.I64, null);
                divisor.Imm = (long)d;
                n.Op = signed ? Op.DivS : Op.DivU;
                n.In = [x, divisor];
                changed = true;
            }
        return changed;
    }

    private static bool Shifted(Node n, Op op, int amount, out Node value)
    {
        value = null!;
        if (n.Op != op || !n.In[1].IsConstValue(amount)) return false;
        value = n.In[0];
        return true;
    }

    /// <summary>The constant and the other operand of a multiplication's high half.</summary>
    private static bool MagicProduct(Node n, Op op, out Node x, out ulong magic)
    {
        x = null!;
        magic = 0;
        if (n.Op != op || n.In.Length != 2) return false;
        if (n.In[1].IsConst && !n.In[0].IsConst) (x, magic) = (n.In[0], n.In[1].UImm);
        else if (n.In[0].IsConst && !n.In[1].IsConst) (x, magic) = (n.In[1], n.In[0].UImm);
        else return false;
        return true;
    }

    /// <summary>
    /// q = mulhi(x, M) [+ x] >> s, then q + (q >>> 63), q + (x >>> 63) or q - (x >> 63): x / d for a d above one.
    /// </summary>
    private static (Node X, long D)? Signed(Node n)
    {
        Node? q = null, signOf = null;
        if (n.Op == Op.Add)
        {
            for (int k = 0; k < 2 && q == null; k++)
                if (Shifted(n.In[1 - k], Op.ShrU, 63, out Node s)) (q, signOf) = (n.In[k], s);
        }
        else if (n.Op == Op.Sub && Shifted(n.In[1], Op.ShrS, 63, out Node s)) (q, signOf) = (n.In[0], s);
        if (q == null || signOf == null) return null;

        int shift = 0;
        Node core = q;
        if (q.Op == Op.ShrS && q.In[1].IsConst && q.In[1].Imm is > 0 and < 64)
        {
            shift = (int)q.In[1].Imm;
            core = q.In[0];
        }
        Node x;
        ulong magic;
        bool added = false;
        if (!MagicProduct(core, Op.MulHiS, out x, out magic))
        {
            if (core.Op != Op.Add) return null;
            int k = core.In[0].Op == Op.MulHiS ? 0 : core.In[1].Op == Op.MulHiS ? 1 : -1;
            if (k < 0 || !MagicProduct(core.In[k], Op.MulHiS, out x, out magic) || !ReferenceEquals(core.In[1 - k], x)) return null;
            added = true;
        }
        if (!ReferenceEquals(signOf, q) && !ReferenceEquals(signOf, x)) return null;
        // The multiplier is used as an unsigned number above 2^63 exactly when x is added back.
        if (((long)magic < 0) != added) return null;

        UInt128 power = UInt128.One << (64 + shift);
        UInt128 estimate = power / magic;
        for (UInt128 d = estimate > 2 ? estimate - 1 : 2; d <= estimate + 1; d++)
        {
            if (d < 2 || d > long.MaxValue) continue;
            var (m, s) = SignedMagic((long)d);
            if ((ulong)m == magic && s == shift) return (x, (long)d);
        }
        return null;
    }

    /// <summary>
    /// mulhi_un(x, M) >>> s, or with the added step t = mulhi_un(x, M); (((x - t) >>> 1) + t) >>> (s - 1): x / d.
    /// </summary>
    private static (Node X, ulong D)? Unsigned(Node n)
    {
        int shift = 0;
        Node core = n;
        if (n.Op == Op.ShrU && n.In[1].IsConst && n.In[1].Imm is > 0 and < 64)
        {
            shift = (int)n.In[1].Imm;
            core = n.In[0];
        }
        Node x;
        ulong magic;
        bool add = false;
        if (!MagicProduct(core, Op.MulHiU, out x, out magic))
        {
            // ((x - t) >>> 1) + t
            if (core.Op != Op.Add) return null;
            int k = core.In[0].Op == Op.MulHiU ? 0 : core.In[1].Op == Op.MulHiU ? 1 : -1;
            if (k < 0) return null;
            Node t = core.In[k];
            if (!Shifted(core.In[1 - k], Op.ShrU, 1, out Node difference) || difference.Op != Op.Sub ||
                !ReferenceEquals(difference.In[1], t) || !MagicProduct(t, Op.MulHiU, out x, out magic) ||
                !ReferenceEquals(difference.In[0], x)) return null;
            add = true;
            shift += 1;
        }
        else if (shift == 0) return null; // (a bare high half is no division)

        UInt128 power = UInt128.One << (64 + shift);
        UInt128 multiplier = add ? ((UInt128)1 << 64) + magic : magic;
        UInt128 estimate = power / multiplier;
        for (UInt128 d = estimate > 2 ? estimate - 1 : 2; d <= estimate + 1; d++)
        {
            if (d < 2 || d > ulong.MaxValue || ((ulong)d & ((ulong)d - 1)) == 0) continue;
            var (m, s, a) = UnsignedMagic((ulong)d);
            if (m == magic && s == shift && a == add) return (x, (ulong)d);
        }
        return null;
    }

    /// <summary>Hacker's Delight, magic for signed division by d (2 &lt;= d), 64 bits: the multiplier and the shift.</summary>
    internal static (long M, int S) SignedMagic(long d)
    {
        const ulong two63 = 1UL << 63;
        ulong ad = (ulong)Math.Abs(d);
        ulong t = two63 + ((ulong)d >> 63);
        ulong anc = t - 1 - t % ad;
        int p = 63;
        ulong q1 = two63 / anc, r1 = two63 - q1 * anc;
        ulong q2 = two63 / ad, r2 = two63 - q2 * ad;
        ulong delta;
        do
        {
            p++;
            q1 *= 2;
            r1 *= 2;
            if (r1 >= anc) { q1++; r1 -= anc; }
            q2 *= 2;
            r2 *= 2;
            if (r2 >= ad) { q2++; r2 -= ad; }
            delta = ad - r2;
        } while (q1 < delta || (q1 == delta && r1 == 0));
        long m = (long)(q2 + 1);
        if (d < 0) m = -m;
        return (m, p - 64);
    }

    /// <summary>Hacker's Delight, magic for unsigned division by d (2 &lt;= d), 64 bits: the multiplier, the shift, and whether the add step is needed.</summary>
    internal static (ulong M, int S, bool Add) UnsignedMagic(ulong d)
    {
        bool add = false;
        int p = 63;
        ulong nc = ulong.MaxValue - (0 - d) % d;
        ulong q1 = 0x8000000000000000UL / nc, r1 = 0x8000000000000000UL - q1 * nc;
        ulong q2 = 0x7FFFFFFFFFFFFFFFUL / d, r2 = 0x7FFFFFFFFFFFFFFFUL - q2 * d;
        ulong delta;
        do
        {
            p++;
            if (r1 >= nc - r1) { q1 = 2 * q1 + 1; r1 = 2 * r1 - nc; }
            else { q1 = 2 * q1; r1 = 2 * r1; }
            if (r2 + 1 >= d - r2)
            {
                if (q2 >= 0x7FFFFFFFFFFFFFFFUL) add = true;
                q2 = 2 * q2 + 1;
                r2 = 2 * r2 + 1 - d;
            }
            else
            {
                if (q2 >= 0x8000000000000000UL) add = true;
                q2 = 2 * q2;
                r2 = 2 * r2 + 1;
            }
            delta = d - 1 - r2;
        } while (p < 128 && (q1 < delta || (q1 == delta && r1 == 0)));
        return (q2 + 1, p - 64, add);
    }
}
