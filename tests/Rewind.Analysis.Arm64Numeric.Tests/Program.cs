using System.Numerics;
using System.Reflection;
using System.Security.Cryptography;
using System.Text.Json;
using Rewind.Analysis;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Analysis.X64;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Runtime;
using RuntimeHelpers = System.Runtime.CompilerServices.RuntimeHelpers;

internal static class Program
{
    private const BindingFlags All = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static;
    private static int assertions;
    private static readonly List<string> passed = [];
    private static readonly List<string> failed = [];

    private static int Main(string[] args)
    {
        if (args.Length != 0 && args[0] == "--native")
        {
            int result = 1;
            // Real recovery recursively walks substantially deeper trees than these small fixtures.
            var worker = new Thread(() => { try { result = Native(args); } catch (Exception e) { Console.Error.WriteLine(e); } }, 1 << 28);
            worker.Start(); worker.Join();
            return result;
        }
        if (args.Length != 0 && args[0] is "--help" or "-h")
        {
            Console.WriteLine("arm64 numeric tests [--report file.json]\n  --native <elf> <metadata> <signature.sig> [full-name-filter] [limit]");
            return 0;
        }
        string? report = null;
        if (args.Length == 2 && args[0] == "--report") report = args[1];
        else if (args.Length != 0) throw new ArgumentException("Only --report <file> or --native ... are supported.");
        Run("GPR fixed-point decoder and float scaling", FixedConversions);
        Run("reserved and unsupported encodings are not accepted", InvalidConversions);
        Run("FCMLT zero masks and clearing of unwritten lanes", CompareZero);
        Run("FCMLT/FNEG/BIT and BSL preserve lane bits", ConditionalNegation);
        Run("scalar FCVTZS/FCVTZU saturate all four integer widths/signs", ScalarSaturation);
        Run("SIMD FCVTZS/FCVTZU share saturation and lane clearing", VectorSaturation);
        Run("native infinity CSEL remains an observable conditional", InfinitySelections);
        Run("UInt64 and Int64 saturation constants retain HIR type and bits", HirIntegerConstants);
        var summary = new { suite = "arm64-numeric", assertions, passed, failed,
            analysis_binary_sha256 = HashFile(typeof(A64Lifter).Assembly.Location),
            scope = "Only the new numeric fixtures; no historical suites or Unity are invoked." };
        string json = JsonSerializer.Serialize(summary, new JsonSerializerOptions { WriteIndented = true });
        Console.WriteLine(json);
        if (report != null) File.WriteAllText(report, json + Environment.NewLine);
        return failed.Count == 0 ? 0 : 1;
    }

    private static void Run(string name, Action body)
    {
        try { body(); passed.Add(name); }
        catch (Exception e) { failed.Add(name + ": " + e.Message); Console.Error.WriteLine(e); }
    }

    private static void Check(bool condition, string label)
    {
        assertions++;
        if (!condition) throw new InvalidOperationException(label);
    }

    private static string HashFile(string path) => Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(path)));
    private static ulong Mask(int bits) => bits == 64 ? ulong.MaxValue : (1UL << bits) - 1;
    private static long Signed(ulong value, int bits) => bits == 64 ? unchecked((long)value) : unchecked((long)((value & Mask(bits)) ^ (1UL << (bits - 1))) - (1L << (bits - 1)));
    private static ulong FBits(double value, int bytes) => bytes == 4 ? BitConverter.SingleToUInt32Bits((float)value) : BitConverter.DoubleToUInt64Bits(value);
    private static double FValue(ulong bits, int bytes) => bytes == 4 ? BitConverter.UInt32BitsToSingle((uint)bits) : BitConverter.UInt64BitsToDouble(bits);
    private static int FBytes(VT type) => type == VT.F32 ? 4 : type == VT.F64 ? 8 : throw new InvalidOperationException("Expected a float IR value.");

    private sealed class Image : NativeImage
    {
        public override ImageFormat Format => ImageFormat.Elf;
        public Image()
        {
            Arch = CpuArch.Arm64; PointerSize = 8; MemoryBase = 0; Memory = new byte[0x2000];
            Sections.Add(new ImageSection("fixture", 0x1000, 0x100, SectionFlags.Read | SectionFlags.Execute));
        }
    }

    private sealed class Context : ILiftContext
    {
        public NativeImage Image { get; } = new Image();
        public bool IsFunctionStart(ulong address) => address == 0x1000;
        public ulong NextFunctionStart(ulong address) => address < 0x1100 ? 0x1100UL : 0;
        public bool IsNoReturn(ulong address) => false;
        public CallShape? ShapeOf(ulong address) => null;
    }

    private sealed class Fixture
    {
        public readonly Function Function = new() { Regs = RegisterModel.Arm64, Address = 0x1000 };
        public readonly Block Block = new() { Start = 0x1000 };
        public readonly IrBuilder Builder;
        public readonly SsaBuilder Ssa;
        public readonly A64Lifter Lifter = new(new Context());
        public readonly Dictionary<ulong, ulong> Memory = [];
        private ulong nextInput = 0x100000;
        private ulong nextInstruction = 0x1000;
        private static readonly MethodInfo Lift = typeof(A64Lifter).GetMethod("LiftInstruction", All)!;

        public Fixture()
        {
            Function.Blocks.Add(Block); Builder = new IrBuilder(Function) { Current = Block };
            Ssa = new SsaBuilder(Function, (VT[])typeof(A64Lifter).GetField("VarTypes", All)!.GetValue(null)!);
            Ssa.Seal(Block);
            Set(Lifter, "_fn", Function); Set(Lifter, "_b", Builder); Set(Lifter, "_ssa", Ssa); Set(Lifter, "_block", Block);
        }

        public Node Input(VT type, ulong bits)
        {
            ulong address = nextInput; nextInput += 16; Memory[address] = bits;
            return Builder.Raw(Op.Load, type, Builder.Const(VT.I64, unchecked((long)address)));
        }

        public void Gpr(int register, ulong value) => Ssa.Write(register, Block, Input(VT.I64, value));
        public void GprConstant(int register, ulong value) => Ssa.Write(register, Block, Builder.Const(VT.I64, unchecked((long)value)));
        public void Poison(int register)
        {
            for (int lane = 0; lane < 4; lane++) Ssa.Write(A64Lifter.VarV + 4 * register + lane, Block, Builder.Const(VT.I32, 0xA5C3E79B));
        }

        public void Fp(int register, int bytes, ulong bits, bool effect = true)
        {
            Node value = effect ? Input(bytes == 4 ? VT.I32 : VT.I64, bits) : Builder.Const(bytes == 4 ? VT.I32 : VT.I64, unchecked((long)bits));
            WriteElement(register, bytes, 0, value);
        }

        public void Vector(int register, int bytes, ulong[] values)
        {
            for (int k = 0; k < values.Length; k++) WriteElement(register, bytes, k, Input(bytes == 4 ? VT.I32 : VT.I64, values[k]));
        }

        private void WriteElement(int register, int bytes, int element, Node value)
        {
            int at = A64Lifter.VarV + register * 4 + element * bytes / 4;
            Ssa.Write(at, Block, Builder.Trunc(value, VT.I32));
            if (bytes == 8) Ssa.Write(at + 1, Block, Builder.Trunc(Builder.Shift(Op.ShrU, value, Builder.Const(VT.I8, 32)), VT.I32));
        }

        public void Execute(uint word)
        {
            A64Instruction instruction = A64Decoder.Decode(word, nextInstruction);
            Builder.CurrentAddr = nextInstruction; nextInstruction += 4;
            try { Lift.Invoke(Lifter, [instruction]); }
            catch (TargetInvocationException e) when (e.InnerException != null) { System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(e.InnerException).Throw(); }
        }

        public Node Register(int register) => Ssa.Read(register, Block);
        public Node[] Lanes(int register) => Enumerable.Range(0, 4).Select(k => Ssa.Read(A64Lifter.VarV + 4 * register + k, Block)).ToArray();
        public Evaluator Evaluate() => new(Memory);
    }

    private static void Set(object instance, string name, object value) => instance.GetType().GetField(name, All)!.SetValue(instance, value);

    // Only observed results are interpreted. The SSA cache evaluates each input load once even when guards,
    // conversion and subsequent CSELs all refer to it. Raw float-to-integer conversion deliberately REJECTS
    // NaN/Infinity/out-of-range input: a broken guard cannot accidentally pass through the host CLR's cast.
    private sealed class Evaluator(Dictionary<ulong, ulong> memory)
    {
        private readonly Dictionary<Node, ulong> cache = [];
        public readonly Dictionary<ulong, int> Reads = [];
        public ulong Value(Node node)
        {
            if (cache.TryGetValue(node, out ulong existing)) return existing;
            ulong A() => Value(node.In[0]);
            ulong B() => Value(node.In[1]);
            double FA() => FValue(A(), FBytes(node.In[0].Type));
            double FB() => FValue(B(), FBytes(node.In[1].Type));
            ulong Bool(bool value) => value ? 1UL : 0;
            ulong Float(double value) => FBits(value, FBytes(node.Type));
            ulong result = node.Op switch
            {
                Op.Const => unchecked((ulong)node.Imm),
                Op.Load => Read(A()),
                Op.Select => Value(node.In[A() != 0 ? 1 : 2]),
                Op.ZExt or Op.Trunc or Op.BitsToF or Op.FToBits => A(),
                Op.SExt => unchecked((ulong)Signed(A(), node.In[0].Type.Bits())),
                Op.Concat => ((A() & uint.MaxValue) << 32) | (B() & uint.MaxValue),
                Op.Add => unchecked(A() + B()), Op.Sub => unchecked(A() - B()), Op.Mul => unchecked(A() * B()),
                Op.And => A() & B(), Op.Or => A() | B(), Op.Xor => A() ^ B(), Op.Not => ~A(), Op.Neg => unchecked(0UL - A()),
                Op.Shl => A() << (int)(B() & (node.Type.Bits() == 64 ? 63UL : 31UL)),
                Op.ShrU => A() >> (int)(B() & (node.Type.Bits() == 64 ? 63UL : 31UL)),
                Op.ShrS => unchecked((ulong)(Signed(A(), node.In[0].Type.Bits()) >> (int)(B() & (node.Type.Bits() == 64 ? 63UL : 31UL)))),
                Op.CmpEq => Bool(A() == B()), Op.CmpNe => Bool(A() != B()),
                Op.CmpLtU => Bool(A() < B()), Op.CmpLeU => Bool(A() <= B()),
                Op.CmpLtS => Bool(Signed(A(), node.In[0].Type.Bits()) < Signed(B(), node.In[1].Type.Bits())),
                Op.CmpLeS => Bool(Signed(A(), node.In[0].Type.Bits()) <= Signed(B(), node.In[1].Type.Bits())),
                Op.FCmpEq => Bool(FA() == FB()), Op.FCmpLt => Bool(FA() < FB()), Op.FCmpLe => Bool(FA() <= FB()),
                Op.FCmpUnord => Bool(double.IsNaN(FA()) || double.IsNaN(FB())),
                Op.FNeg => A() ^ (1UL << (node.Type.Bits() - 1)),
                Op.FAbs => A() & ~(1UL << (node.Type.Bits() - 1)),
                Op.FAdd => Float(FA() + FB()), Op.FSub => Float(FA() - FB()),
                Op.FMul => Float(FA() * FB()), Op.FDiv => Float(FA() / FB()),
                Op.FExt or Op.FTrunc => Float(FA()),
                Op.SIntToF => node.Type == VT.F32
                    ? BitConverter.SingleToUInt32Bits((float)Signed(A(), node.In[0].Type.Bits()))
                    : BitConverter.DoubleToUInt64Bits((double)Signed(A(), node.In[0].Type.Bits())),
                Op.UIntToF => node.Type == VT.F32 ? BitConverter.SingleToUInt32Bits((float)A()) : BitConverter.DoubleToUInt64Bits((double)A()),
                Op.FToSInt => RawInteger(FA(), node.Type.Bits(), true),
                Op.FToUInt => RawInteger(FA(), node.Type.Bits(), false),
                _ => throw new NotSupportedException("Observed unsupported IR: " + node.Op + " at 0x" + node.Addr.ToString("X"))
            };
            result &= node.Type.Mask(); cache[node] = result;
            return result;
        }

        private ulong Read(ulong address)
        {
            Reads[address] = Reads.GetValueOrDefault(address) + 1;
            return memory.TryGetValue(address, out ulong bits) ? bits : throw new InvalidOperationException("Unexpected read address.");
        }

        public void AtMostOnce(string label) => Check(Reads.Values.All(n => n == 1), label + ": shared SSA input was evaluated repeatedly");
        public uint[] Lanes(Node[] nodes) => nodes.Select(n => (uint)Value(n)).ToArray();
    }

    private static ulong RawInteger(double value, int bits, bool signed)
    {
        if (!double.IsFinite(value)) throw new InvalidOperationException("An unguarded nonfinite input reached raw IR conversion.");
        BigInteger n = new(value), lo = signed ? -(BigInteger.One << (bits - 1)) : BigInteger.Zero;
        BigInteger hi = (BigInteger.One << (signed ? bits - 1 : bits)) - 1;
        if (n < lo || n > hi) throw new InvalidOperationException("An unguarded overflow reached raw IR conversion.");
        return (ulong)(n & ((BigInteger.One << bits) - 1));
    }

    // Independent arithmetic oracle: truncate via arbitrary-precision integer, then clamp to the destination
    // range. It does not duplicate the lifter's floating threshold/Select tree or use an overflowing CLR cast.
    private static ulong Saturation(ulong raw, int fpBytes, int bits, bool signed)
    {
        double f = FValue(raw, fpBytes);
        if (double.IsNaN(f)) return 0;
        BigInteger lo = signed ? -(BigInteger.One << (bits - 1)) : BigInteger.Zero;
        BigInteger hi = (BigInteger.One << (signed ? bits - 1 : bits)) - 1;
        BigInteger n = double.IsNegativeInfinity(f) ? lo : double.IsPositiveInfinity(f) ? hi : new BigInteger(f);
        n = BigInteger.Min(hi, BigInteger.Max(lo, n));
        return (ulong)(n & ((BigInteger.One << bits) - 1));
    }

    private static uint FixedWord(bool unsigned, bool wide, int fpBytes, int fractionalBits, byte rn = 13, byte rd = 7) =>
        0x1E020000U | (unsigned ? 1U << 16 : 0) | (wide ? 1U << 31 : 0) |
        (fpBytes == 8 ? 1U << 22 : fpBytes == 2 ? 3U << 22 : 0) | ((uint)(64 - fractionalBits) << 10) | ((uint)rn << 5) | rd;
    private static uint IntegerFloatWord(bool unsigned, bool wide, int fpBytes, byte rn = 13, byte rd = 7) =>
        FixedWord(unsigned, wide, fpBytes, 64, rn, rd) | (1U << 21);
    private static uint FloatIntegerWord(bool unsigned, bool wide, int fpBytes, byte rn = 4, byte rd = 9) =>
        0x1E380000U | (unsigned ? 1U << 16 : 0) | (wide ? 1U << 31 : 0) | (fpBytes == 8 ? 1U << 22 : 0) | ((uint)rn << 5) | rd;

    private static void FixedConversions()
    {
        foreach (uint word in new uint[] { 0x1E028500, 0x1E0286A0 })
        {
            A64Instruction i = A64Decoder.Decode(word, 0x1000);
            Check(i.Op == A64Op.Scvtf && i.FpSize == 4 && !i.Is64 && i.Imm == 31, "Real Noise fixed SCVTF word 0x" + word.ToString("X8"));
            foreach (uint raw in new uint[] { 0x80000000, 0x7FFFFFFF, 0xFFFFFFFF })
            {
                var f = new Fixture(); f.Gpr(i.Rn, 0xABCDEF1200000000UL | raw); f.Poison(i.Rd); f.Execute(word);
                var eval = f.Evaluate(); uint[] lanes = eval.Lanes(f.Lanes(i.Rd));
                uint expected = BitConverter.SingleToUInt32Bits(MathF.ScaleB(unchecked((int)raw), -31));
                Check(lanes.SequenceEqual(new uint[] { expected, 0, 0, 0 }), "Original Noise instruction word evaluates its actual W register");
                eval.AtMostOnce("original fixed SCVTF");
            }
        }
        foreach (bool unsigned in new[] { false, true })
        foreach (bool wide in new[] { false, true })
        foreach (int fpBytes in new[] { 4, 8 })
        foreach (int fbits in new[] { 0, 1, 7, 31, 32, wide ? 63 : 32, wide ? 64 : 32 }.Distinct())
        {
            uint word = fbits == 0 ? IntegerFloatWord(unsigned, wide, fpBytes) : FixedWord(unsigned, wide, fpBytes, fbits);
            A64Instruction i = A64Decoder.Decode(word, 0x1000);
            Check(i.Op == (unsigned ? A64Op.Ucvtf : A64Op.Scvtf) && i.Imm == fbits && i.FpSize == fpBytes && i.Is64 == wide && i.Rn == 13 && i.Rd == 7,
                "SCVTF/UCVTF width, registers and 64-scale decoding");
            // The existing HIR RUn->R4 lowering has not proved direct UInt64->F32 rounding.
            // The newly decoded fixed-point form deliberately remains unsupported (checked below).
            if (unsigned && wide && fpBytes == 4 && fbits != 0) continue;
            ulong[] samples = wide
                ? [0, 1, 127, 0x8000000000000000, 0x7FFFFFFFFFFFFFFF, ulong.MaxValue, 0xFEDCBA9876543210]
                : [0, 1, 127, 0x80000000, 0x7FFFFFFF, uint.MaxValue, 0xFEDCBA98];
            foreach (ulong value in samples)
            {
                var f = new Fixture(); f.Gpr(13, wide ? value : 0xA1B2C3D400000000UL | value); f.Poison(7); f.Execute(word);
                double d = unsigned ? (double)value : Signed(value, wide ? 64 : 32);
                ulong expected = fpBytes == 4
                    ? BitConverter.SingleToUInt32Bits(MathF.ScaleB(unsigned ? (float)value : (float)Signed(value, wide ? 64 : 32), -fbits))
                    : BitConverter.DoubleToUInt64Bits(Math.ScaleB(d, -fbits));
                var eval = f.Evaluate(); uint[] lanes = eval.Lanes(f.Lanes(7));
                Check(lanes[0] == (uint)expected && lanes[1] == (fpBytes == 8 ? (uint)(expected >> 32) : 0) && lanes[2] == 0 && lanes[3] == 0,
                    $"Fixed conversion result/zero lanes word={word:X8}, input={value:X16}");
                Check(eval.Reads.Count == 1, "One GPR source load is observed"); eval.AtMostOnce("fixed conversion");
            }
        }
    }

    private static void InvalidConversions()
    {
        foreach (bool unsigned in new[] { false, true })
        foreach (bool wide in new[] { false, true })
        {
            uint reserved = FixedWord(unsigned, wide, 4, 1) | (2U << 22);
            Check(A64Decoder.Decode(reserved, 0).Op is not (A64Op.Scvtf or A64Op.Ucvtf), "Reserved ptype=2 is rejected");
            var f = new Fixture(); f.Poison(7); f.Gpr(13, 42); Node[] before = f.Lanes(7);
            uint half = FixedWord(unsigned, wide, 2, 1); A64Instruction i = A64Decoder.Decode(half, 0);
            if (i.Op is A64Op.Scvtf or A64Op.Ucvtf)
            {
                bool refused = false;
                try { f.Execute(half); } catch (NotSupportedException) { refused = true; }
                Check(refused && f.Lifter.UnsupportedCounts.Values.Sum() == 1, "Unsupported half reports failure");
                Check(before.Zip(f.Lanes(7)).All(p => ReferenceEquals(p.First, p.Second)), "Unsupported half cannot fake a destination value");
            }
            else Check(i.Op == A64Op.Invalid, "Half must be rejected or explicitly unsupported");
        }
        foreach (bool unsigned in new[] { false, true })
        foreach (int fpBytes in new[] { 4, 8 })
        foreach (int scale in new[] { 0, 1, 17, 31 })
            Check(A64Decoder.Decode(FixedWord(unsigned, false, fpBytes, 64 - scale), 0).Op is not (A64Op.Scvtf or A64Op.Ucvtf),
                "32-bit fixed input rejects scale below 32");
        foreach (int fbits in new[] { 1, 31, 64 })
        {
            // This exact integer distinguishes direct rounding from an intermediate double:
            // direct F32 is 2^63+2^40; double->F32 first lands on the halfway value and yields 2^63.
            const ulong doubleRoundingWitness = (1UL << 63) + (1UL << 39) + 1;
            var f = new Fixture(); f.Gpr(13, doubleRoundingWitness); f.Poison(7); Node[] before = f.Lanes(7);
            bool refused = false;
            try { f.Execute(FixedWord(true, true, 4, fbits)); } catch (NotSupportedException) { refused = true; }
            Check(refused && f.Lifter.UnsupportedCounts.Values.Sum() == 1, "New fixed UInt64->F32 is explicitly unsupported until direct HIR rounding is proved");
            Check(before.Zip(f.Lanes(7)).All(p => ReferenceEquals(p.First, p.Second)), "Unsupported UInt64->F32 cannot fake a scaled result");
        }
    }

    private readonly record struct Shape(string Name, uint Base, int Bytes, int Count, bool Scalar)
    {
        public bool Q => (Base & (1U << 30)) != 0;
        public uint Word(uint operation, byte rn = 0, byte rd = 1) => (Base & 0x50400000U) | operation | ((uint)rn << 5) | rd;
    }
    private static readonly Shape[] Shapes = [new("2S", 0, 4, 2, false), new("4S", 0x40000000, 4, 4, false),
        new("2D", 0x40400000, 8, 2, false), new("S", 0x50000000, 4, 1, true), new("D", 0x50400000, 8, 1, true)];
    private static ulong[] FloatPatterns(int bytes) => bytes == 4
        ? [0, 0x80000000, 0xBF800000, 0x3F800000, 0xFF800000, 0x7F800000, 0x7FC12345, 0xFFC32110, 1, 0x80000001]
        : [0, 0x8000000000000000, 0xBFF0000000000000, 0x3FF0000000000000, 0xFFF0000000000000, 0x7FF0000000000000,
           0x7FF8123456789ABC, 0xFFF8321098765432, 1, 0x8000000000000001];
    private static uint[] ExpectedLanes(ulong[] elements, int bytes, int count)
    {
        uint[] lanes = new uint[4];
        for (int k = 0; k < count; k++) { lanes[k * bytes / 4] = (uint)elements[k]; if (bytes == 8) lanes[k * 2 + 1] = (uint)(elements[k] >> 32); }
        return lanes;
    }

    private static void CompareZero()
    {
        foreach (Shape shape in Shapes)
        {
            uint word = shape.Word(0x0EA0E800); A64Instruction i = A64Decoder.Decode(word, 0x1000);
            Check(i.Op == A64Op.VecOp && ((VecKind)i.Imm).ToString() == "FCmLtZero" && i.ElemSize == shape.Bytes && ((i.Imm2 & 2) != 0) == shape.Scalar && ((i.Imm2 & 1) != 0) == shape.Q,
                "FCMLT zero decoder " + shape.Name);
            ulong[] patterns = FloatPatterns(shape.Bytes);
            for (int offset = 0; offset < patterns.Length; offset++)
            {
                ulong[] input = Enumerable.Range(0, 16 / shape.Bytes).Select(k => patterns[(offset + k) % patterns.Length]).ToArray();
                var f = new Fixture(); f.Vector(0, shape.Bytes, input); f.Poison(1); f.Execute(word);
                ulong[] masks = input.Select(v => FValue(v, shape.Bytes) < 0 ? Mask(shape.Bytes * 8) : 0).ToArray();
                var eval = f.Evaluate();
                Check(eval.Lanes(f.Lanes(1)).SequenceEqual(ExpectedLanes(masks, shape.Bytes, shape.Count)), "Ordered mask/all-ones and zeroed lanes " + shape.Name);
                eval.AtMostOnce("FCMLT " + shape.Name);
            }
        }
        Check(A64Decoder.Decode(0x0EE0E801, 0).Op != A64Op.VecOp, "Unallocated vector 1D FCMLT is not accepted");
        Check(A64Decoder.Decode(0x0EA0E801, 0).Rd == 1, "Real Noise sign-mask word preserves destination v1");
    }

    private static void ConditionalNegation()
    {
        foreach (Shape shape in Shapes.Where(s => !s.Scalar))
        foreach (bool bit in new[] { false, true })
        {
            ulong[] patterns = FloatPatterns(shape.Bytes);
            for (int offset = 0; offset < patterns.Length; offset++)
            {
                ulong[] input = Enumerable.Range(0, 16 / shape.Bytes).Select(k => patterns[(offset + k) % patterns.Length]).ToArray();
                var f = new Fixture(); f.Vector(0, shape.Bytes, input); f.Poison(1); f.Poison(2);
                f.Execute(shape.Word(0x0EA0E800, 0, 1)); // FCMLT v1, v0, #0
                f.Execute(shape.Word(0x2EA0F800, 0, 2)); // FNEG v2, v0
                uint q = shape.Q ? 1U << 30 : 0;
                // BIT v0,v2,v1, or BSL v1,v2,v0. Both choose -input only for an ordered negative lane.
                f.Execute(bit ? 0x2EA01C00U | q | (1U << 16) | (2U << 5) : 0x2E601C00U | q | (2U << 5) | 1U);
                ulong sign = 1UL << (shape.Bytes * 8 - 1);
                ulong[] expected = input.Select(v => FValue(v, shape.Bytes) < 0 ? v ^ sign : v).ToArray();
                var eval = f.Evaluate();
                Check(eval.Lanes(f.Lanes(bit ? 0 : 1)).SequenceEqual(ExpectedLanes(expected, shape.Bytes, shape.Count)),
                    $"FCMLT/FNEG/{(bit ? "BIT" : "BSL")} {shape.Name} keeps -0 and NaN payload/sign");
                eval.AtMostOnce("conditional negation");
            }
        }
    }

    private static IEnumerable<ulong> ConversionPatterns(int fpBytes, int bits, bool signed)
    {
        double upper = Math.ScaleB(1.0, signed ? bits - 1 : bits), lower = signed ? -upper : 0;
        double Prev(double v) => fpBytes == 4 ? MathF.BitDecrement((float)v) : Math.BitDecrement(v);
        double Next(double v) => fpBytes == 4 ? MathF.BitIncrement((float)v) : Math.BitIncrement(v);
        return FloatPatterns(fpBytes).Concat(new[] { -2.75, -1.5, -0.5, 0.5, 1.5, 2.75,
            Prev(upper), upper, Next(upper), Prev(lower), lower, Next(lower),
            Math.ScaleB(1, 31), Math.ScaleB(1, 32), Math.ScaleB(1, 63), Math.ScaleB(1, 64),
            -Math.ScaleB(1, 63), fpBytes == 4 ? float.MaxValue : double.MaxValue,
            fpBytes == 4 ? -float.MaxValue : -double.MaxValue }.Select(v => FBits(v, fpBytes))).Distinct();
    }

    private static void ScalarSaturation()
    {
        foreach (bool signed in new[] { false, true })
        foreach (int bits in new[] { 32, 64 })
        foreach (int fpBytes in new[] { 4, 8 })
        {
            uint word = FloatIntegerWord(!signed, bits == 64, fpBytes);
            A64Instruction i = A64Decoder.Decode(word, 0);
            Check(i.Op == A64Op.FCvtToInt && i.Signed == signed && i.Is64 == (bits == 64) && i.FpSize == fpBytes && i.Imm == (long)A64Rounding.Zero,
                "FCVTZS/FCVTZU register decoder");
            foreach (ulong raw in ConversionPatterns(fpBytes, bits, signed))
            {
                var f = new Fixture(); f.Fp(4, fpBytes, raw); f.GprConstant(9, ulong.MaxValue); f.Execute(word);
                var eval = f.Evaluate(); Node output = f.Register(9);
                ulong expected = Saturation(raw, fpBytes, bits, signed);
                Check(eval.Value(output) == expected, $"Saturating scalar signed={signed} bits={bits} fp={fpBytes} raw={raw:X16}");
                Check(eval.Value(output) == expected && eval.Reads.Count == 1, "Observed conversion is memoized and 32-bit writes clear high bits");
                eval.AtMostOnce("scalar saturation");
            }
        }
    }

    private static void VectorSaturation()
    {
        foreach (Shape shape in Shapes)
        foreach (bool signed in new[] { false, true })
        {
            uint word = shape.Word(signed ? 0x0EA1B800U : 0x2EA1B800U);
            A64Instruction i = A64Decoder.Decode(word, 0);
            Check(i.Op == A64Op.VecOp && (VecKind)i.Imm == (signed ? VecKind.FCvtzs : VecKind.FCvtzu), "SIMD conversion decoder " + shape.Name);
            ulong[] patterns = ConversionPatterns(shape.Bytes, shape.Bytes * 8, signed).ToArray();
            for (int offset = 0; offset < patterns.Length; offset++)
            {
                ulong[] input = Enumerable.Range(0, 16 / shape.Bytes).Select(k => patterns[(offset + k) % patterns.Length]).ToArray();
                var f = new Fixture(); f.Vector(0, shape.Bytes, input); f.Poison(1); f.Execute(word);
                ulong[] expected = input.Select(v => Saturation(v, shape.Bytes, shape.Bytes * 8, signed)).ToArray();
                var eval = f.Evaluate();
                Check(eval.Lanes(f.Lanes(1)).SequenceEqual(ExpectedLanes(expected, shape.Bytes, shape.Count)), "SIMD saturation and write-zero " + shape.Name);
                eval.AtMostOnce("vector saturation");
            }
        }
    }

    private static void InfinitySelections()
    {
        foreach (int bits in new[] { 32, 64 })
        foreach (int fpBytes in new[] { 4, 8 })
        foreach (bool reversed in new[] { false, true })
        foreach (bool differentValue in new[] { false, true })
        foreach (ulong sentinel in new[] { 1UL << (bits - 1), 17UL })
        foreach (ulong raw in ConversionPatterns(fpBytes, bits, true))
        {
            double[] comparisons = differentValue ? [double.PositiveInfinity, 2.75, double.NaN] : [FValue(raw, fpBytes)];
            foreach (double compared in comparisons)
            {
                var f = new Fixture(); f.Fp(4, fpBytes, raw); f.Fp(5, fpBytes, FBits(double.PositiveInfinity, fpBytes), false);
                if (differentValue) f.Fp(6, fpBytes, FBits(compared, fpBytes));
                f.GprConstant(8, sentinel); f.Execute(FloatIntegerWord(false, bits == 64, fpBytes));
                byte compareRegister = differentValue ? (byte)6 : (byte)4;
                f.Execute(0x1E202000U | (fpBytes == 8 ? 1U << 22 : 0) | (5U << 16) | ((uint)compareRegister << 5));
                byte rn = reversed ? (byte)9 : (byte)8, rm = reversed ? (byte)8 : (byte)9;
                f.Execute(0x1A800000U | (bits == 64 ? 1U << 31 : 0) | ((uint)rm << 16) | (reversed ? 1U << 12 : 0) | ((uint)rn << 5));
                ulong expected = compared == double.PositiveInfinity ? sentinel : Saturation(raw, fpBytes, bits, true);
                var eval = f.Evaluate();
                Check(eval.Value(f.Register(0)) == expected, $"CSEL preserved bits={bits} reversed={reversed} foreign={differentValue} raw={raw:X16}");
                eval.AtMostOnce("infinity CSEL");
            }
        }
    }

    private static void HirIntegerConstants()
    {
        var sigs = new SigFactory();
        var hir = (HirBuilder)RuntimeHelpers.GetUninitializedObject(typeof(HirBuilder));
        foreach ((string field, Il2CppTypeEnum element) in new[] { ("_bool", Il2CppTypeEnum.Boolean), ("_float", Il2CppTypeEnum.R4),
            ("_double", Il2CppTypeEnum.R8), ("_int", Il2CppTypeEnum.I4), ("_uint", Il2CppTypeEnum.U4),
            ("_long", Il2CppTypeEnum.I8), ("_ulong", Il2CppTypeEnum.U8) }) Set(hir, field, sigs.Primitive(element));
        Set(hir, "_ptr", 8);
        MethodInfo coerce = typeof(HirBuilder).GetMethod("Coerce", All)!;
        TypeSig u64 = sigs.Primitive(Il2CppTypeEnum.U8), i64 = sigs.Primitive(Il2CppTypeEnum.I8);
        foreach ((long bits, TypeSig target) in new[] { (-1L, u64), (long.MaxValue, i64), (long.MinValue, i64) })
        {
            var result = (HConst)coerce.Invoke(hir, [new HConst(bits, i64), target])!;
            Check(ReferenceEquals(result.Type, target) && unchecked((ulong)Convert.ToInt64(result.Value)) == unchecked((ulong)bits),
                "HIR coercion retains saturation constant type and complete 64-bit payload");
        }
    }

    private static int Native(string[] args)
    {
        if (args.Length < 4 || args.Length > 6) throw new ArgumentException("--native <elf> <metadata> <signature.sig> [filter] [limit]");
        string filter = args.Length > 4 ? args[4] : "AssetKits.ParticleImage.Noise::ValCoord|AssetKits.ParticleImage.Noise::SingleCellular|AssetKits.ParticleImage.Noise::FastFloor|AssetKits.ParticleImage.ParticleData::Simulate";
        int limit = args.Length > 5 ? int.Parse(args[5]) : 4;
        if (limit < 1) throw new ArgumentOutOfRangeException(nameof(limit));
        byte[] binary = File.ReadAllBytes(args[1]), metadata = File.ReadAllBytes(args[2]);
        NativeImage image = NativeImage.Load(binary, args[1]);
        Il2CppModel model = Il2CppModel.Load(image, metadata, null, Console.WriteLine);
        if (image.Arch != CpuArch.Arm64) throw new InvalidOperationException("Native numeric probe requires ARM64.");
        Console.WriteLine(JsonSerializer.Serialize(new { binary_sha256 = Convert.ToHexStringLower(SHA256.HashData(binary)),
            metadata_sha256 = Convert.ToHexStringLower(SHA256.HashData(metadata)), signature_sha256 = HashFile(args[3]),
            analysis_binary_sha256 = HashFile(typeof(A64Lifter).Assembly.Location), filter, limit }));
        var context = new ModelCodeContext(model); context.DiscoverCallTargets();
        var index = new Rewind.Analysis.Runtime.CodeIndex(context);
        var library = Rewind.Analysis.Runtime.HelperLibrary.Load(args[3]);
        var matched = library.Match(index, image, context.FunctionStarts.Where(a => !context.IsManaged(a)), out var matchReport,
            context.FunctionStarts.Where(context.IsManaged));
        Console.WriteLine("helpers: " + matchReport);
        Rewind.Analysis.Runtime.HelperDiscovery.AddImportStubs(image, matched);
        foreach (string message in Rewind.Analysis.Runtime.HelperDiscovery.Complete(model, context, index, matched)) Console.WriteLine(message);
        var program = new ProgramAnalysis(model, matched, context);
        var pipeline = new MethodPipeline(program);
        string[] filters = filter.Split('|', StringSplitOptions.RemoveEmptyEntries);
        int recovered = 0, crashes = 0;
        foreach (MethodDef method in model.Methods.Where(m => m.Address != 0 && filters.Any(f => m.FullName.Contains(f, StringComparison.Ordinal))).Take(limit))
        {
            Console.WriteLine($"=== {method.FullName} @0x{method.Address:X}");
            try
            {
                HMethod h = pipeline.Recover(method); Console.WriteLine(HirPrinter.Print(h));
                foreach (string note in h.Notes.Distinct()) Console.WriteLine("  # " + note);
                foreach (string problem in h.Problems.Distinct()) Console.WriteLine("  ! " + problem);
                recovered++;
            }
            catch (Exception e) { crashes++; Console.WriteLine($"CRASH {e.GetType().Name}: {e.Message}"); }
        }
        Console.WriteLine(JsonSerializer.Serialize(new { native_recovered = recovered, crashes,
            note = "HIR evidence for before/after comparison; existing recovery problems are reported, not silently reclassified as passes." }));
        return recovered == 0 || crashes != 0 ? 1 : 0;
    }
}
