using System.Buffers.Binary;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Ir;
using Rewind.Analysis.X64;
using Rewind.Binary;

internal static partial class Program
{
    private sealed class VeneerImage : NativeImage
    {
        public override ImageFormat Format => ImageFormat.Elf;
        public VeneerImage(ulong target)
        {
            Arch = CpuArch.Arm64;
            PointerSize = 8;
            MemoryBase = 0;
            Memory = new byte[0x4000];
            Sections.Add(new ImageSection("body", 0x1000, 0x40, SectionFlags.Read | SectionFlags.Execute));
            Sections.Add(new ImageSection("veneer", target, 8, SectionFlags.Read | SectionFlags.Execute));
        }
        public void Word(ulong at, uint word) => BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan((int)at, 4), word);
    }

    private sealed class VeneerContext(VeneerImage image) : ILiftContext
    {
        public NativeImage Image => image;
        public readonly HashSet<ulong> Starts = [0x1000, 0x1040];
        public readonly HashSet<ulong> NoReturn = [];
        public bool IsFunctionStart(ulong address) => Starts.Contains(address);
        public ulong NextFunctionStart(ulong address) => Starts.Where(a => a > address).DefaultIfEmpty(0UL).Min();
        public bool IsNoReturn(ulong target) => NoReturn.Contains(target);
        public CallShape? ShapeOf(ulong target) => null;
    }

    private sealed record VeneerFixture(VeneerImage Image, VeneerContext Context, ulong Target, uint Load, byte Register, int Offset);

    private static uint VeneerBranch(ulong from, ulong to, bool link = false)
    {
        long displacement = checked((long)to - (long)from);
        if ((displacement & 3) != 0 || displacement < -(1L << 27) || displacement >= 1L << 27)
            throw new ArgumentException("branch fixture out of range");
        return (link ? 0x94000000U : 0x14000000U) | ((uint)(displacement >> 2) & 0x03FFFFFFU);
    }

    private static VeneerFixture Veneer(uint load = 0xF940E273, ulong target = 0x2000)
    {
        A64Instruction decoded = A64Decoder.Decode(load, target);
        var image = new VeneerImage(target);
        image.Word(0x1000, 0xAA0003E0U | decoded.Rd); // mov xN, x0
        image.Word(0x1004, VeneerBranch(0x1004, target));
        image.Word(0x1008, 0xAA0003E0U | ((uint)decoded.Rd << 16)); // mov x0, xN
        image.Word(0x100C, 0x91001C00); // add x0, x0, #7: continuation must survive
        image.Word(0x1010, 0xD65F03C0); // ret
        if (target < 0x4000)
        {
            image.Word(target, load);
            image.Word(target + 4, VeneerBranch(target + 4, 0x1008));
        }
        return new VeneerFixture(image, new VeneerContext(image), target, load, decoded.Rd, checked((int)decoded.Imm));
    }

    private sealed class VeneerMemory(ulong expectedAddress, ulong value, bool fail)
    {
        public readonly List<ulong> Reads = [];
        public ulong Read(ulong address)
        {
            Reads.Add(address);
            if (address != expectedAddress) throw new InvalidOperationException("wrong native load address");
            if (fail) throw new ArithmeticException("observed load failure");
            return value;
        }
    }

    // Execute the original branch/load/branch bytes, independently of CFG normalization and SSA lifting.
    // Only the fixture's documented integer instructions are interpreted; unsupported instructions fail.
    private static (ulong Result, ulong OtherRegister) RunVeneerNative(VeneerFixture f, VeneerMemory memory, ulong argument, ulong other)
    {
        ulong[] registers = new ulong[31];
        registers[0] = argument;
        registers[1] = other;
        ulong pc = 0x1000;
        for (int steps = 0; steps < 32; steps++)
        {
            A64Instruction i = A64Decoder.Decode(f.Image.U32(pc), pc);
            pc += 4;
            switch (i.Op)
            {
                case A64Op.Orr when i.Rn == A64Instruction.Zr && i.Is64:
                    registers[i.Rd] = registers[i.Rm];
                    break;
                case A64Op.AddImm when i.Is64:
                    registers[i.Rd] = unchecked(registers[i.Rn] + (ulong)i.Imm);
                    break;
                case A64Op.Ldr when i.Size == 8 && !i.Vector && i.Mode == A64Mode.Offset:
                    registers[i.Rd] = memory.Read(unchecked(registers[i.Rn] + (ulong)i.Imm));
                    break;
                case A64Op.B:
                    pc = i.Target;
                    break;
                case A64Op.Ret:
                    return (registers[0], registers[1]);
                default:
                    throw new NotSupportedException("native fixture " + i);
            }
        }
        throw new InvalidOperationException("native fixture did not return");
    }

    // Evaluate the actual A64Lifter output. Memoization models one execution of each SSA load, including
    // repeated uses. This compares observable values/read counts against the unfused native fixture.
    private static (ulong Result, ulong OtherRegister) RunVeneerIr(Function function, VeneerMemory memory, ulong argument, ulong other)
    {
        var values = new Dictionary<Node, ulong>();
        ulong Value(Node n)
        {
            if (values.TryGetValue(n, out ulong v)) return v;
            ulong result = n.Op switch
            {
                Op.Const => unchecked((ulong)n.Imm),
                Op.Param => function.Params.Single(p => ReferenceEquals(p.Value, n)).Key switch
                {
                    0 => argument, 1 => other,
                    _ => throw new InvalidOperationException("unexpected observable register")
                },
                Op.Add => unchecked(Value(n.In[0]) + Value(n.In[1])),
                Op.Load => memory.Read(Value(n.In[0])),
                Op.ZExt => Value(n.In[0]),
                Op.Trunc => n.Type == VT.I32 ? (uint)Value(n.In[0]) : throw new NotSupportedException("trunc width"),
                _ => throw new NotSupportedException("IR fixture " + n.Op)
            };
            values[n] = result;
            return result;
        }
        Node ret = function.Blocks.SelectMany(b => b.Nodes).Single(n => !n.Dead && n.Op == Op.Return);
        return (Value(ret.In[0]), Value(ret.In[3])); // ARM64 x0 and x1 return snapshots
    }

    private static void BranchVeneers()
    {
        // Real PAP load words from five Collect/LevelEnd veneers and PowersChestView.DOFloat. Neither
        // recognition nor recovery consults those names, RVAs, metadata tokens or concrete offsets.
        uint[] words = [0xF9458673, 0xF940E273, 0xF944C2D6, 0xF9406673, 0xF940E273, 0xF9430AB5];
        foreach (var (word, occurrence) in words.Select((w, n) => (w, n)))
        {
            var f = Veneer(word, occurrence % 2 == 0 ? 0x2000UL : 0x800UL);
            A64Cfg cfg = A64Cfg.Build(f.Context, 0x1000);
            Check(cfg.Problems.Count == 0 && cfg.Limit == 0x1040, "veneer keeps the original function extent");
            Check(cfg.LoadBranchVeneers.Count == 1 && cfg.LoadBranchVeneers[0x1004] == f.Target, "original out-of-line address is recorded");
            A64Instruction atSite = cfg.Blocks.SelectMany(b => b.Instructions).Single(i => i.Address == 0x1004);
            Check(atSite.Op == A64Op.Ldr && atSite.Word == word && atSite.Rd == f.Register && atSite.Rn == f.Register,
                "one proved register-relative effect replaces the branch");
            Check(cfg.Blocks.All(b => b.Start < 0x1040 && b.End != BlockEnd.TailCall) &&
                  cfg.Blocks.SelectMany(b => b.Instructions).Any(i => i.Address == 0x100C),
                "the continuation stays in this method without importing a remote function");
            var lifter = new A64Lifter(f.Context);
            Function lifted = lifter.Lift(0x1000);
            Check(lifted.Problems.Count == 0 && lifter.UnsupportedCounts.Count == 0, "actual A64 lifting accepts the recovered continuation");
            Check(!lifted.Blocks.SelectMany(b => b.Nodes).Any(n => !n.Dead && n.Op is Op.Call or Op.TailCall),
                "a returning load veneer introduces no call or ABI clobbers");
            foreach (ulong value in new[] { 0UL, 0x1020304050607080UL, ulong.MaxValue - 2 })
            {
                const ulong argument = 0x9000, other = 0x8877665544332211;
                ulong address = argument + (uint)f.Offset;
                var nativeMemory = new VeneerMemory(address, value, false);
                var irMemory = new VeneerMemory(address, value, false);
                var nativeResult = RunVeneerNative(f, nativeMemory, argument, other);
                var irResult = RunVeneerIr(lifted, irMemory, argument, other);
                Check(nativeResult == irResult && irResult.Result == unchecked(value + 7) && irResult.OtherRegister == other,
                    "loaded bits, continuation arithmetic and unrelated x1 are preserved");
                Check(nativeMemory.Reads.SequenceEqual(irMemory.Reads) && irMemory.Reads.Count == 1,
                    "the original memory location is read exactly once");
            }
            foreach (bool nativeExecution in new[] { true, false })
            {
                var memory = new VeneerMemory(0x9000UL + (uint)f.Offset, 7, true);
                try
                {
                    if (nativeExecution) RunVeneerNative(f, memory, 0x9000, 42);
                    else RunVeneerIr(lifted, memory, 0x9000, 42);
                    Check(false, "load failure must propagate before the continuation");
                }
                catch (ArithmeticException)
                {
                    Check(memory.Reads.Count == 1, "both executions preserve the failing load without retry or suppression");
                }
            }
        }
        Cases.Add("ARM64 returning load veneers: six original words, forward/backward islands, exact load/continuation semantics");

        var split = Veneer();
        A64Cfg splitCfg = A64Cfg.Build(split.Context, 0x1000, null, [0x1004, 0x1008]);
        Check(splitCfg.Blocks.Select(b => b.Start).SequenceEqual(new ulong[] { 0x1000, 0x1004, 0x1008 }),
            "existing exception/call-site leaders remain at their original addresses");
        Check(splitCfg.Blocks[1].End == BlockEnd.FallThrough && splitCfg.Blocks[1].Successors.SequenceEqual(new ulong[] { 0x1008 }),
            "the substituted load retains the same-scope continuation edge");

        void Reject(string name, Action<VeneerFixture> change, ulong target = 0x2000)
        {
            var f = Veneer(target: target);
            change(f);
            A64Cfg cfg = A64Cfg.Build(f.Context, 0x1000);
            Check(cfg.LoadBranchVeneers.Count == 0, name + " is not a proved load veneer");
            Check(cfg.Blocks.SelectMany(b => b.Instructions).Single(i => i.Address == 0x1004).Op != A64Op.Ldr,
                name + " retains its original control-transfer instruction");
        }
        Reject("ordinary external tail call", f => f.Image.Word(f.Target, 0xD65F03C0));
        Reject("call rather than branch", f => f.Image.Word(0x1004, VeneerBranch(0x1004, f.Target, link: true)));
        Reject("known target entry", f => f.Context.Starts.Add(f.Target));
        Reject("known second-instruction entry", f => f.Context.Starts.Add(f.Target + 4));
        Reject("known no-return target", f => f.Context.NoReturn.Add(f.Target));
        Reject("continuation starts another function", f => f.Context.Starts.Add(0x1008));
        Reject("wrong return skips an instruction", f => f.Image.Word(f.Target + 4, VeneerBranch(f.Target + 4, 0x100C)));
        Reject("return to branch site loops", f => f.Image.Word(f.Target + 4, VeneerBranch(f.Target + 4, 0x1004)));
        Reject("return via link register", f => f.Image.Word(f.Target + 4, 0xD65F03C0));
        Reject("second instruction calls", f => f.Image.Word(f.Target + 4, VeneerBranch(f.Target + 4, 0x1008, link: true)));
        Reject("longer island with intervening nop", f => f.Image.Word(f.Target + 4, 0xD503201F));
        Reject("different source register", f => f.Image.Word(f.Target, 0xF940E293));
        Reject("32-bit register load", f => f.Image.Word(f.Target, 0xB940E273));
        Reject("vector load", f => f.Image.Word(f.Target, 0xFD40E273));
        Reject("PC-relative literal load", f => f.Image.Word(f.Target, 0x58000013));
        Reject("store has a different effect", f => f.Image.Word(f.Target, 0xF900E273));
        Reject("writeback load", f => f.Image.Word(f.Target, 0xF8408E73));
        Reject("stack source and zero destination", f => f.Image.Word(f.Target, 0xF94003FF));
        Reject("target is data", f => f.Image.Sections[1] = f.Image.Sections[1] with { Flags = SectionFlags.Read });
        Reject("target crosses executable section", f => f.Image.Sections[1] = f.Image.Sections[1] with { Size = 4 });
        Reject("unmapped target", _ => { }, 0x5000);
        Cases.Add("ARM64 load veneer rejection: calls, entries, wrong returns, register effects, extra code and mapping boundaries");
    }
}
