using System.Buffers.Binary;
using System.Text;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Runtime;
using Rewind.Analysis.X64;
using Rewind.Binary;
using HelperTable = Rewind.Analysis.Runtime.RuntimeHelpers;

internal static partial class Program
{
    private sealed class ExceptionImage : NativeImage
    {
        public override ImageFormat Format => ImageFormat.Elf;
        public ExceptionImage()
        {
            Arch = CpuArch.Arm64;
            PointerSize = 8;
            Memory = new byte[0x4000];
            Sections.Add(new ImageSection("code", 0x1000, 0x2000, SectionFlags.Read | SectionFlags.Execute));
            Sections.Add(new ImageSection("strings", 0x3000, 0x1000, SectionFlags.Read));
        }
        public void Word(ulong at, uint word) => BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan((int)at, 4), word);
        public void Text(ulong at, string text) => Encoding.UTF8.GetBytes(text + "\0").CopyTo(Memory, (int)at);
    }

    private sealed class ExceptionContext(ExceptionImage image, HelperTable helpers) : ILiftContext
    {
        public NativeImage Image => image;
        public bool IsFunctionStart(ulong address) => address is 0x1000 or 0x1008 or 0x1800 or 0x1810 or 0x2000;
        public ulong NextFunctionStart(ulong address) => new ulong[] { 0x1000, 0x1008, 0x1800, 0x1810, 0x2000 }
            .Where(a => a > address).DefaultIfEmpty(0UL).Min();
        public bool IsNoReturn(ulong target) => helpers.At(target)?.NoReturn == true;
        public CallShape? ShapeOf(ulong target) => null;
    }

    private static HelperInfo? ExceptionStub(ExceptionImage image, HelperTable helpers, ulong start = 0x1000, ulong end = 0x1008)
        => (HelperInfo?)typeof(HelperShapes).GetMethod("Arm64ExceptionStub", All)!.Invoke(null, [image, helpers, start, end]);

    private static ExceptionImage AdjacentExceptionFactory()
    {
        var image = new ExceptionImage();
        // Original PAP shape: FDE 38AA7D4..38AA7DC is STR LR; BL index thrower. The next FDE,
        // 38AA7DC..38AA7E8, loads an overflow message for an unrelated factory. Addresses are relocated.
        image.Word(0x1000, 0xF81F0FFE);
        image.Word(0x1004, VeneerBranch(0x1004, 0x2000, link: true));
        image.Word(0x1008, 0xD0000000); // adrp x0, 0x3000
        image.Word(0x100C, 0x91000000); // add x0, x0, #0
        image.Word(0x1010, VeneerBranch(0x1010, 0x2800));
        image.Text(0x3000, "Arithmetic operation resulted in an overflow.");
        image.FunctionTable.Add(new FunctionRange(0x1000, 0x1008, 0));
        image.FunctionTable.Add(new FunctionRange(0x1008, 0x1014, 0));
        return image;
    }

    private static Exception ExceptionFor(HelperKind kind) => kind switch
    {
        HelperKind.ThrowIndexOutOfRange => new IndexOutOfRangeException(),
        HelperKind.ThrowNullReference => new NullReferenceException(),
        HelperKind.ThrowDivideByZero => new DivideByZeroException(),
        HelperKind.GetOverflowException => new OverflowException(),
        _ => throw new NotSupportedException("no semantic fixture for " + kind)
    };

    // Execute the original wrapper's bytes and the independently supplied callee behavior. In contrast to
    // the matcher this follows control flow; a real throwing callee prevents all following instructions.
    private static void ExecuteExceptionWrapper(ExceptionImage image, Action callee, Action continuation)
    {
        ulong pc = 0x1000;
        for (int step = 0; step < 6; step++)
        {
            A64Instruction ins = A64Decoder.Decode(image.U32(pc), pc);
            pc += 4;
            switch (ins.Op)
            {
                case A64Op.Str or A64Op.Stp when ins.Rn == A64Instruction.Sp:
                    break;
                case A64Op.AddImm when ins.Rd == 29 && ins.Rn == A64Instruction.Sp:
                    break;
                case A64Op.B or A64Op.Bl when ins.Target == 0x2000:
                    callee();
                    if (ins.Op == A64Op.B) return;
                    break;
                default:
                    continuation();
                    return;
            }
        }
        throw new InvalidOperationException("exception fixture did not finish");
    }

    private static Type? Caught(Action action)
    {
        try { action(); return null; }
        catch (Exception e) { return e.GetType(); }
    }

    private static void ExceptionStubs()
    {
        var image = AdjacentExceptionFactory();
        Check(image.TryCString(0x3000) == "Arithmetic operation resulted in an overflow.", "fixture has the misleading adjacent message");
        Check(ExceptionStub(image, new HelperTable()) == null, "an unknown index wrapper never borrows the next function's overflow type");
        Check(ExceptionStub(image, new HelperTable(), end: 0x1040) == null, "an unknown first call is not skipped even when unwind extent is wider");

        foreach (HelperKind kind in new[] { HelperKind.ThrowIndexOutOfRange, HelperKind.ThrowNullReference,
                     HelperKind.ThrowDivideByZero, HelperKind.GetOverflowException })
        foreach (uint[] prologue in new uint[][] { [], [0xF81F0FFE], [0xA9BF7BFD], [0xA9BF7BFD, 0x910003FD] })
        {
            var fixture = new ExceptionImage();
            for (int i = 0; i < prologue.Length; i++) fixture.Word(0x1000UL + (uint)i * 4, prologue[i]);
            ulong call = 0x1000UL + (uint)prologue.Length * 4;
            fixture.Word(call, VeneerBranch(call, 0x2000, link: true));
            fixture.Word(call + 4, 0xD503201F); // a continuation must remain unexecuted
            var helpers = new HelperTable();
            var known = new HelperInfo(kind, 0, true, false, "independently known thrower");
            helpers.Add(0x2000, known);
            HelperInfo? recognized = ExceptionStub(fixture, helpers, end: call + 4);
            Check(recognized?.Kind == kind && recognized.NoReturn && !recognized.ReturnsValue,
                "the first proven no-return callee supplies its own exception kind");
            Check(recognized!.IntArgs == known.IntArgs && recognized.FloatArgs == known.FloatArgs,
                "the wrapper preserves the callee's argument contract");
            int calls = 0, continued = 0;
            Type? native = Caught(() => ExecuteExceptionWrapper(fixture,
                () => { calls++; throw ExceptionFor(kind); }, () => continued++));
            Type? recovered = Caught(() => throw ExceptionFor(recognized.Kind));
            Check(native == recovered && native == ExceptionFor(kind).GetType(), "native and recognized helpers throw the same exception type");
            Check(calls == 1 && continued == 0, "a no-return call executes once and never reaches following bytes");
        }

        var index = new HelperInfo(HelperKind.ThrowIndexOutOfRange, 0, true, false, "index thrower");
        var typed = new HelperTable(); typed.Add(0x2000, index);
        Check(ExceptionStub(image, typed)?.Kind == HelperKind.ThrowIndexOutOfRange,
            "the actual 8-byte wrapper shape stays index-related despite adjacent overflow text");
        image.Word(0x1004, VeneerBranch(0x1004, 0x2000));
        Check(ExceptionStub(image, typed)?.Kind == HelperKind.ThrowIndexOutOfRange,
            "an LR-save wrapper can tail-branch to a proven thrower");
        Cases.Add("ARM64 exception wrappers: actual adjacent-function shape, four typed callees, complete native throw/continuation semantics");

        void Reject(string name, Action<ExceptionImage, HelperTable> change, ulong start = 0x1000, ulong end = 0x1008)
        {
            var fixture = AdjacentExceptionFactory();
            var helpers = new HelperTable(); helpers.Add(0x2000, index);
            change(fixture, helpers);
            Check(ExceptionStub(fixture, helpers, start, end) == null, name);
        }
        Reject("function extent stops before the call", (_, _) => { }, end: 0x1004);
        Reject("truncated instruction at the extent is not decoded", (_, _) => { }, end: 0x1007);
        Reject("unknown function extent gives no wrapper proof", (_, _) => { }, end: 0);
        Reject("empty function extent is rejected", (_, _) => { }, end: 0x1000);
        Reject("reversed function extent is rejected", (_, _) => { }, end: 0xFFC);
        Reject("unaligned entry is rejected", (_, _) => { }, start: 0x1001);
        Reject("unmapped entry is rejected", (_, _) => { }, start: 0x5000, end: 0x5008);
        Reject("non-executable bytes are rejected", (f, _) => f.Sections[0] = f.Sections[0] with { Flags = SectionFlags.Read });
        Reject("executable section end limits the wrapper", (f, _) => f.Sections[0] = f.Sections[0] with { Size = 4 });
        Reject("a returning factory is not a thrower", (_, h) => h.Add(0x2000, index with { NoReturn = false, ReturnsValue = true }));
        Reject("a returning void call is not a thrower", (_, h) => h.Add(0x2000, index with { NoReturn = false }));
        Reject("an inconsistent value-return contract is rejected", (_, h) => h.Add(0x2000, index with { ReturnsValue = true }));
        Reject("integer-argument helper needs a different proof", (_, h) => h.Add(0x2000, index with { IntArgs = 1 }));
        Reject("floating-argument helper needs a different proof", (_, h) => h.Add(0x2000, index with { FloatArgs = 1 }));
        Reject("abort-like no-return is not a managed exception kind", (_, h) => h.Add(0x2000, index with { Kind = HelperKind.StackCheckFail }));
        Reject("a generic throw is not a known exception type", (_, h) => h.Add(0x2000, index with { Kind = HelperKind.Throw }));
        Reject("unknown helper kind is rejected", (_, h) => h.Add(0x2000, index with { Kind = HelperKind.None }));
        Reject("argument mutation before the call is not ignored", (f, _) => f.Word(0x1000, 0xD2800020));
        Reject("non-stack store before the call is not ignored", (f, _) => f.Word(0x1000, 0xF9000020));
        Reject("different-width LR store is not the proved prologue", (f, _) => f.Word(0x1000, 0xB81F0FFE));
        Reject("a prior unknown call is not skipped", (f, _) => f.Word(0x1000, VeneerBranch(0x1000, 0x2800, link: true)));
        Reject("conditional control flow is not a plain wrapper", (f, _) => f.Word(0x1000, 0xB4000040));
        Reject("indirect call lacks a typed target", (f, _) => f.Word(0x1004, 0xD63F0000));
        Reject("return before the helper is not skipped", (f, _) => f.Word(0x1000, 0xD65F03C0));
        Reject("multiple prologue writes are not silently dropped", (f, _) => f.Word(0x1004, 0xF81F0FFE), end: 0x1014);
        Reject("known label inside this function is not an external helper", (f, h) =>
        { f.Word(0x1004, VeneerBranch(0x1004, 0x1000, link: true)); h.Add(0x1000, index); });

        var caller = AdjacentExceptionFactory();
        caller.Word(0x1800, VeneerBranch(0x1800, 0x1000, link: true));
        caller.Word(0x1804, 0x91000400); // add x0, x0, #1
        caller.Word(0x1808, 0xD65F03C0);
        var recognizedHelpers = new HelperTable(); recognizedHelpers.Add(0x2000, index);
        recognizedHelpers.Add(0x1000, ExceptionStub(caller, recognizedHelpers)!);
        A64Cfg cfg = A64Cfg.Build(new ExceptionContext(caller, recognizedHelpers), 0x1800);
        Check(cfg.Blocks.Count == 1 && cfg.Blocks[0].End == BlockEnd.NoReturnCall && cfg.Blocks[0].Instructions.Count == 1,
            "the proven wrapper's no-return contract stops the actual caller CFG at the call");
        A64Cfg unknown = A64Cfg.Build(new ExceptionContext(caller, new HelperTable()), 0x1800);
        Check(unknown.Blocks.SelectMany(b => b.Instructions).Any(i => i.Address == 0x1804),
            "a rejected classification does not invent a no-return contract at callers");
        Cases.Add("ARM64 exception rejection: unwind/entry/section limits, first transfer, side effects, return and argument contracts");
    }
}
