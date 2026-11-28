using System.Buffers.Binary;
using System.Reflection;
using System.Security.Cryptography;
using System.Text.Json;
using Rewind.Analysis;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Ir;
using Rewind.Analysis.X64;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Runtime;

internal static class Program
{
    private const BindingFlags All = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static;
    private static int assertions;
    private static readonly List<string> passed = [];
    private static readonly List<string> failed = [];

    private sealed record Arrangement(string Name, uint Word, int ElementBytes, bool Q, string ExpectedHex);

    // Explicit instruction words and output bytes for input 00 01 ... 0F. These anchors do not
    // calculate the expected permutation with the lifter's index-XOR implementation.
    private static readonly Arrangement[] Arrangements =
    [
        new("8B",  0x0E200820, 1, false, "07060504030201000000000000000000"),
        new("16B", 0x4E200820, 1, true,  "07060504030201000F0E0D0C0B0A0908"),
        new("4H",  0x0E600820, 2, false, "06070405020300010000000000000000"),
        new("8H",  0x4E600820, 2, true,  "06070405020300010E0F0C0D0A0B0809"),
        new("2S",  0x0EA00820, 4, false, "04050607000102030000000000000000"),
        new("4S",  0x4EA00820, 4, true,  "04050607000102030C0D0E0F08090A0B"),
    ];

    private static int Main(string[] args)
    {
        string? report = null;
        if (args.Length == 2 && args[0] == "--report") report = args[1];
        else if (args.Length != 0) throw new ArgumentException("Usage: arm64 REV64 tests [--report file.json]");
        Run("six legal encodings and literal element permutations", LiteralArrangements);
        Run("aliases, V31, float payload bits and upper-half clearing", AliasesAndBits);
        Run("five original ParticleData.Simulate instructions", NativeSites);
        Run("reserved scalar/64-bit-element and neighboring encodings", RejectedEncodings);
        Run("malformed lifted arrangements remain unsupported", RejectedLiftArrangements);
        var summary = new
        {
            suite = "arm64-rev64", assertions, passed, failed,
            analysis_binary_sha256 = Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(typeof(A64Lifter).Assembly.Location))),
            scope = "Only new REV64 fixtures. No numeric/history suite, Unity, or native recovery is invoked."
        };
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
        public readonly Dictionary<ulong, uint> Memory = [];
        private ulong nextInput = 0x100000;
        private ulong nextInstruction = 0x1000;
        private static readonly MethodInfo Lift = typeof(A64Lifter).GetMethod("LiftInstruction", All)!;

        public Fixture()
        {
            Function.Blocks.Add(Block); Builder = new IrBuilder(Function) { Current = Block };
            Ssa = new SsaBuilder(Function, (VT[])typeof(A64Lifter).GetField("VarTypes", All)!.GetValue(null)!);
            Ssa.Seal(Block);
            Set("_fn", Function); Set("_b", Builder); Set("_ssa", Ssa); Set("_block", Block);
        }

        private void Set(string name, object value) => typeof(A64Lifter).GetField(name, All)!.SetValue(Lifter, value);

        public void Poison(int register)
        {
            for (int k = 0; k < 4; k++)
                Ssa.Write(A64Lifter.VarV + register * 4 + k, Block, Builder.Const(VT.I32, 0xDACEB001L + k));
        }

        public void Vector(int register, byte[] bytes)
        {
            Check(bytes.Length == 16, "fixture input register size");
            for (int k = 0; k < 4; k++)
            {
                ulong address = nextInput; nextInput += 16;
                Memory[address] = BinaryPrimitives.ReadUInt32LittleEndian(bytes.AsSpan(k * 4, 4));
                // Nonconstant SSA input prevents constant folding from hiding a broken permutation.
                Node value = Builder.Raw(Op.Load, VT.I32, Builder.Const(VT.I64, unchecked((long)address)));
                Ssa.Write(A64Lifter.VarV + register * 4 + k, Block, value);
            }
        }

        public Node[] Lanes(int register) => Enumerable.Range(0, 4).Select(k => Ssa.Read(A64Lifter.VarV + register * 4 + k, Block)).ToArray();

        public void Execute(uint word) => Execute(A64Decoder.Decode(word, nextInstruction));

        public void Execute(A64Instruction instruction)
        {
            Builder.CurrentAddr = nextInstruction; nextInstruction += 4;
            try { Lift.Invoke(Lifter, [instruction]); }
            catch (TargetInvocationException e) when (e.InnerException != null)
            { System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(e.InnerException).Throw(); }
        }
    }

    // Interpret only the integer data-flow operations emitted by this permutation. Floating-point
    // arithmetic is deliberately not accepted: it could quiet a NaN or change signed-zero bits.
    private sealed class Evaluator(Dictionary<ulong, uint> memory)
    {
        private readonly Dictionary<Node, ulong> cache = [];
        public readonly Dictionary<ulong, int> Reads = [];

        private ulong Value(Node node)
        {
            if (cache.TryGetValue(node, out ulong result)) return result;
            Check(node.Type is not (VT.F32 or VT.F64), "REV64 must not convert lane bits to floating point");
            ulong A() => Value(node.In[0]);
            ulong B() => Value(node.In[1]);
            result = node.Op switch
            {
                Op.Const => unchecked((ulong)node.Imm),
                Op.Load => Read(A()),
                Op.Trunc or Op.ZExt => A(),
                Op.And => A() & B(),
                Op.Or => A() | B(),
                Op.Shl => A() << (int)B(),
                Op.ShrU => A() >> (int)B(),
                _ => throw new NotSupportedException("Unexpected REV64 IR operation: " + node.Op)
            };
            result &= node.Type.Mask(); cache[node] = result;
            return result;
        }

        private ulong Read(ulong address)
        {
            Reads[address] = Reads.GetValueOrDefault(address) + 1;
            return memory.TryGetValue(address, out uint value) ? value : throw new InvalidOperationException("Unexpected input address");
        }

        public byte[] Bytes(Node[] lanes)
        {
            byte[] bytes = new byte[16];
            for (int k = 0; k < 4; k++) BinaryPrimitives.WriteUInt32LittleEndian(bytes.AsSpan(k * 4, 4), (uint)Value(lanes[k]));
            return bytes;
        }
    }

    private static uint WithRegisters(uint word, byte rd, byte rn) => (word & ~0x3FFU) | (uint)rn << 5 | rd;

    private static byte[] Bits(params uint[] words)
    {
        Check(words.Length == 4, "four 32-bit payload words");
        byte[] bytes = new byte[16];
        for (int k = 0; k < 4; k++) BinaryPrimitives.WriteUInt32LittleEndian(bytes.AsSpan(k * 4, 4), words[k]);
        return bytes;
    }

    private static byte[] Oracle(byte[] source, int elementBytes, bool q)
    {
        byte[] output = new byte[16];
        // Reverse an array of whole byte-slice elements independently in each 8-byte block.
        // Bytes within an element are never reversed; q=0 leaves the upper output bytes zero.
        for (int block = 0; block < (q ? 2 : 1); block++)
        {
            byte[][] elements = Enumerable.Range(0, 8 / elementBytes)
                .Select(k => source.AsSpan(block * 8 + k * elementBytes, elementBytes).ToArray()).ToArray();
            Array.Reverse(elements);
            for (int k = 0; k < elements.Length; k++) elements[k].CopyTo(output, block * 8 + k * elementBytes);
        }
        return output;
    }

    private static void Verify(uint word, byte[] source, byte[] expected, string label)
    {
        A64Instruction i = A64Decoder.Decode(word, 0x1000);
        Check(i.Op == A64Op.VecOp && (VecKind)i.Imm == VecKind.Rev64, label + ": decode REV64");
        var f = new Fixture(); f.Poison(i.Rd); f.Vector(i.Rn, source);
        Node[] originalSource = f.Lanes(i.Rn);
        f.Execute(word);
        Check(f.Lifter.UnsupportedCounts.Count == 0, label + ": supported lift");
        var evaluator = new Evaluator(f.Memory);
        byte[] actual = evaluator.Bytes(f.Lanes(i.Rd));
        Check(actual.SequenceEqual(expected), label + ": result " + Convert.ToHexString(actual));
        Check(evaluator.Reads.Count == ((i.Imm2 & 1) == 0 ? 2 : 4), label + ": only used 32-bit input lanes read");
        Check(evaluator.Reads.Values.All(v => v == 1), label + ": each SSA input evaluated once");
        if (i.Rn != i.Rd)
            Check(originalSource.Zip(f.Lanes(i.Rn)).All(p => ReferenceEquals(p.First, p.Second)), label + ": distinct source untouched");
    }

    private static void LiteralArrangements()
    {
        Check((byte)VecKind.FCmLtZero == 76, "old VecKind ordinal retained");
        Check((byte)VecKind.Rev64 == 77, "REV64 appended after existing enum values");
        byte[] source = Enumerable.Range(0, 16).Select(k => (byte)k).ToArray();
        foreach (Arrangement a in Arrangements)
        {
            A64Instruction i = A64Decoder.Decode(a.Word, 0x1000);
            Check(i.ElemSize == a.ElementBytes && i.Imm2 == (a.Q ? 1 : 0), a.Name + ": element/width/scalar flags");
            Check(i.Rn == 1 && i.Rd == 0, a.Name + ": explicit operand fields");
            Verify(a.Word, source, Convert.FromHexString(a.ExpectedHex), a.Name);
        }
    }

    private static void AliasesAndBits()
    {
        byte[][] sources =
        [
            Bits(0x00000000, 0x80000000, 0x7F800000, 0xFF800000),
            Bits(0x7FC01234, 0xFFA12345, 0x00000001, 0x80000001),
            Bits(0x3F800000, 0xBF800000, 0xFFFFFFFF, 0x01020304),
            Bits(0xF1E2D3C4, 0xB5A69788, 0x796A5B4C, 0x3D2E1F00),
        ];
        (byte rd, byte rn)[] registers = [(0, 1), (3, 3), (31, 0), (0, 31), (31, 31)];
        foreach (Arrangement a in Arrangements)
        foreach (byte[] source in sources)
        foreach ((byte rd, byte rn) in registers)
            Verify(WithRegisters(a.Word, rd, rn), source, Oracle(source, a.ElementBytes, a.Q), a.Name + $" v{rd},v{rn}");

        foreach (Arrangement a in Arrangements)
        {
            var f = new Fixture(); byte[] source = sources[1]; f.Vector(7, source);
            uint word = WithRegisters(a.Word, 7, 7); f.Execute(word); f.Execute(word);
            byte[] expected = (byte[])source.Clone();
            if (!a.Q) Array.Clear(expected, 8, 8);
            Check(new Evaluator(f.Memory).Bytes(f.Lanes(7)).SequenceEqual(expected), a.Name + ": alias involution and upper clear");
        }
    }

    private static void NativeSites()
    {
        (ulong rva, uint word, byte rd, byte rn)[] sites =
        [
            (0x6E4B620, 0x0EA00863, 3, 3),
            (0x6E4B624, 0x0EA00800, 0, 0),
            (0x6E4B734, 0x0EA00860, 0, 3),
            (0x6E4B850, 0x0EA00802, 2, 0),
            (0x6E4B9F8, 0x0EA00900, 0, 8),
        ];
        byte[] source = Bits(0x80000000, 0x7FC12345, 0x7F800000, 0xFFA00001);
        byte[] expected = Bits(0x7FC12345, 0x80000000, 0, 0);
        foreach (var site in sites)
        {
            A64Instruction i = A64Decoder.Decode(site.word, site.rva);
            Check(i.Rd == site.rd && i.Rn == site.rn && i.ElemSize == 4 && i.Imm2 == 0, "native operand map @" + site.rva.ToString("X"));
            Verify(site.word, source, expected, "native @" + site.rva.ToString("X"));
        }
    }

    private static void RejectedEncodings()
    {
        uint[] words =
        [
            0x0EE00820, 0x4EE00820, // size=3: no 1D/2D arrangement
            0x5E200820, 0x5E600820, 0x5EA00820, 0x5EE00820, // no scalar REV64
            0x7E200820, 0x7E600820, 0x7EA00820, 0x7EE00820,
            0x2E200820, 0x6E200820, // U=1: adjacent REV32, not REV64
            0x0E201820, 0x4E201820, // adjacent REV16, not REV64
        ];
        foreach (uint word in words)
        {
            A64Instruction i = A64Decoder.Decode(word, 0x1000);
            Check(i.Op != A64Op.VecOp || (VecKind)i.Imm != VecKind.Rev64, "reject/non-alias 0x" + word.ToString("X8"));
        }
        foreach (int bit in new[] { 10, 11, 17, 18, 19, 20, 21, 24, 28, 29, 31 })
        {
            uint word = 0x0E200820U ^ (1U << bit);
            A64Instruction i = A64Decoder.Decode(word, 0x1000);
            Check(i.Op != A64Op.VecOp || (VecKind)i.Imm != VecKind.Rev64, "fixed REV64 encoding bit " + bit);
        }
    }

    private static void RejectedLiftArrangements()
    {
        foreach ((byte bytes, long flags) in new (byte, long)[] { (8, 0), (8, 1), (1, 2), (2, 3), (4, 3), (8, 3) })
        {
            var f = new Fixture();
            bool threw = false;
            try
            {
                f.Execute(new A64Instruction { Address = 0x1000, Word = 0, Op = A64Op.VecOp,
                    Imm = (long)VecKind.Rev64, Imm2 = flags, ElemSize = bytes, Rd = 0, Rn = 1 });
            }
            catch (NotSupportedException) { threw = true; }
            Check(threw && f.Lifter.UnsupportedCounts.Values.Sum() == 1, "reject malformed lifted REV64 bytes=" + bytes + " flags=" + flags);
        }
    }
}
