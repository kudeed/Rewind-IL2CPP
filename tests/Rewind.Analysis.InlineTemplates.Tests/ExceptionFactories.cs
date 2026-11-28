using System.Buffers.Binary;
using System.Text;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Runtime;
using Rewind.Analysis.X64;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Runtime;
using HelperTable = Rewind.Analysis.Runtime.RuntimeHelpers;

internal static partial class Program
{
    private sealed class FactoryImage : NativeImage
    {
        public override ImageFormat Format => ImageFormat.Elf;
        public FactoryImage()
        {
            Arch = CpuArch.Arm64; PointerSize = 8; Memory = new byte[0xA000];
            Sections.Add(new ImageSection("code", 0x1000, 0x5000, SectionFlags.Read | SectionFlags.Execute));
            Sections.Add(new ImageSection("strings", 0x8000, 0x1000, SectionFlags.Read));
        }
        public void Word(ulong at, uint word) => BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan((int)at, 4), word);
        public void Text(ulong at, string text) => Encoding.UTF8.GetBytes(text + "\0").CopyTo(Memory, (int)at);
        public void Function(ulong start, params uint[] words)
        {
            for (int i = 0; i < words.Length; i++) Word(start + (uint)i * 4, words[i]);
            FunctionTable.Add(new FunctionRange(start, start + (uint)words.Length * 4, 0));
        }
    }

    private sealed class FactoryContext(FactoryImage image) : ICodeContext
    {
        public NativeImage Image => image;
        public readonly HashSet<ulong> ExtraStarts = [];
        public bool IsFunctionStart(ulong at) => ExtraStarts.Contains(at) || image.FunctionTable.Any(f => f.Start == at);
        public ulong NextFunctionStart(ulong at) => image.FunctionTable.Select(f => f.Start).Concat(ExtraStarts)
            .Where(a => a > at).DefaultIfEmpty(0UL).Min();
        public bool IsNoReturn(ulong target) => false;
    }

    private sealed record FactoryFixture(FactoryImage Image, FactoryContext Context, HelperTable Helpers,
        List<TypeDef> Types, TypeDef Exception, HashSet<ulong> Managed, HashSet<ulong> LandingPads);

    private static uint FactoryAdrp(ulong pc, ulong target, byte register)
    {
        long pages = ((long)(target & ~0xFFFUL) - (long)(pc & ~0xFFFUL)) >> 12;
        uint bits = unchecked((uint)pages) & 0x1FFFFF;
        return 0x90000000U | ((bits & 3) << 29) | ((bits >> 2) << 5) | register;
    }

    private static FactoryFixture Factory(string exceptionName = "IndexOutOfRangeException", ulong factory = 0x1000)
    {
        var image = new FactoryImage();
        var asm = new AssemblyModel { Name = "mscorlib", ImageName = "mscorlib.dll" };
        TypeDef Type(string name, TypeDef? parent)
        {
            var t = new TypeDef { Index = ++index, Name = name, Namespace = "System", Assembly = asm, BaseType = parent?.Sig };
            t.Sig = Sigs.TypeDef(t); asm.Types.Add(t); return t;
        }
        TypeDef obj = Type("Object", null), ex = Type("Exception", obj), sys = Type("SystemException", ex), type = Type(exceptionName, sys);
        type.Methods = [new MethodDef { Name = ".ctor", DeclaringType = type, Flags = 6,
            ReturnType = Sigs.Primitive(Il2CppTypeEnum.Void) }];
        image.Text(0x8000, "System"); image.Text(0x8040, exceptionName);
        image.Function(factory, 0xD10083FF, 0xA900FBFF, 0xF90003FF,
            VeneerBranch(factory + 12, 0x3000, true), FactoryAdrp(factory + 16, 0x8000, 1), 0x91000021,
            FactoryAdrp(factory + 24, 0x8040, 2), 0x91010042, 0x910003E3,
            VeneerBranch(factory + 36, 0x2000, true), 0xF9400BFE, 0x910083FF, 0xD65F03C0);
        image.Function(0x1100, 0xF81F0FFE, VeneerBranch(0x1104, factory, true), 0xAA1F03E1,
            VeneerBranch(0x110C, 0x3400, true));
        image.Function(0x1200, 0xF81F0FFE, VeneerBranch(0x1204, 0x1100, true));
        // Same 72-byte shared factory shape as the native sample, relocated. The two unknown calls in
        // the message-setting arm must not run for the proved zero-length input view.
        image.Function(0x2000, 0xF81E0FFE, 0xA9014FF4, 0xAA0303F3,
            VeneerBranch(0x200C, 0x3100, true), VeneerBranch(0x2010, 0x3200, true), 0xAA0003F4,
            VeneerBranch(0x2018, 0x3300, true), 0xF9400668, 0xB40000C8,
            0xAA1303E0, VeneerBranch(0x2028, 0x3800, true), 0xAA0003E1, 0x91006280,
            VeneerBranch(0x2034, 0x3810, true), 0xAA1403E0, 0xA9414FF4, 0xF84207FE, 0xD65F03C0);
        foreach (ulong at in new ulong[] { 0x3000, 0x3100, 0x3200, 0x3300 }) image.Function(at, 0xD65F03C0);
        image.Function(0x3400, 0xD4200000); // modeled exported raise implementation never returns
        image.Function(0x4000, VeneerBranch(0x4000, 0x3000));
        image.Function(0x4010, VeneerBranch(0x4010, 0x3100));
        image.Function(0x4020, VeneerBranch(0x4020, 0x3300));
        image.Function(0x4030, 0xF81F0FFE, 0xAA1F03E1, VeneerBranch(0x4038, 0x3400, true));
        image.Exports["il2cpp_get_corlib"] = 0x4000;
        image.Exports["il2cpp_class_from_name"] = 0x4010;
        image.Exports["il2cpp_runtime_object_init"] = 0x4020;
        image.Exports["il2cpp_raise_exception"] = 0x4030;
        var helpers = new HelperTable(); helpers.Add(0x3200, new HelperInfo(HelperKind.ObjectNew, 1, false, true, "known allocator"));
        return new FactoryFixture(image, new FactoryContext(image), helpers, [obj, ex, sys, type], type, [], []);
    }

    private static int DiscoverFactories(FactoryFixture f)
    {
        Type t = typeof(HelperShapes).Assembly.GetType("Rewind.Analysis.Runtime.Arm64ExceptionFactories", true)!;
        return (int)t.GetMethod("Identify", All)!.Invoke(null, [f.Context,
            f.Image.FunctionTable.Select(r => r.Start).Order().ToArray(), f.Types, f.Helpers,
            (Func<ulong, bool>)f.Managed.Contains, (Func<ulong, bool>)f.LandingPads.Contains])!;
    }

    // Independent instruction execution of the actual factory, shared constructor path and raise wrapper.
    // Exported APIs and the allocator are the external contract: all caller-saved registers are spoiled
    // after each modeled call, so preserving the view, object and LR is tested rather than assumed.
    private sealed class FactoryMachine(FactoryFixture f)
    {
        private readonly ulong[] registers = new ulong[33];
        private readonly Dictionary<ulong, ulong> stack = [];
        public readonly List<string> Events = [];
        public bool ConstructorFails;
        public Exception? Created;
        public ulong Result;
        private ulong R(byte n) => n == A64Instruction.Zr ? 0 : registers[n];
        private void W(byte n, ulong value) { if (n != A64Instruction.Zr) registers[n] = value; }
        private static Exception New(string name) => name switch
        {
            "IndexOutOfRangeException" => new IndexOutOfRangeException(),
            "NullReferenceException" => new NullReferenceException(),
            "DivideByZeroException" => new DivideByZeroException(),
            "OverflowException" => new OverflowException(),
            "InvalidCastException" => new InvalidCastException(),
            _ => throw new NotSupportedException(name)
        };

        public void Run(ulong entry)
        {
            registers[A64Instruction.Sp] = 0x100000;
            ulong pc = entry;
            for (int step = 0; step < 120; step++)
            {
                A64Instruction i = A64Decoder.Decode(f.Image.U32(pc), pc);
                ulong next = pc + 4; pc = next;
                switch (i.Op)
                {
                    case A64Op.AddImm: W(i.Rd, unchecked(R(i.Rn) + (ulong)i.Imm)); break;
                    case A64Op.SubImm: W(i.Rd, unchecked(R(i.Rn) - (ulong)i.Imm)); break;
                    case A64Op.Adrp: W(i.Rd, i.Target); break;
                    case A64Op.Orr when i.Rn == A64Instruction.Zr: W(i.Rd, R(i.Rm)); break;
                    case A64Op.Str or A64Op.Stp or A64Op.Ldr or A64Op.Ldp:
                    {
                        ulong address = i.Mode == A64Mode.PostIndex ? R(i.Rn) : unchecked(R(i.Rn) + (ulong)i.Imm);
                        if (i.Op is A64Op.Str or A64Op.Stp) stack[address] = R(i.Rd);
                        else W(i.Rd, stack[address]);
                        if (i.Op == A64Op.Stp) stack[address + 8] = R(i.Ra);
                        if (i.Op == A64Op.Ldp) W(i.Ra, stack[address + 8]);
                        if (i.Mode is A64Mode.PreIndex or A64Mode.PostIndex) W(i.Rn, unchecked(R(i.Rn) + (ulong)i.Imm));
                        break;
                    }
                    case A64Op.Cbz: if (R(i.Rd) == 0) pc = i.Target; break;
                    case A64Op.B: pc = i.Target; break;
                    case A64Op.Bl:
                        registers[30] = next;
                        if (!Api(i.Target)) pc = i.Target;
                        break;
                    case A64Op.Ret:
                        pc = R(i.Rn);
                        if (pc == 0) { Result = registers[0]; return; }
                        break;
                    default: throw new NotSupportedException("factory instruction " + i);
                }
            }
            throw new InvalidOperationException("factory fixture did not finish");
        }

        private bool Api(ulong target)
        {
            ulong result;
            switch (target)
            {
                case 0x3000: Events.Add("corelib"); result = 0xCAFE; break;
                case 0x3100:
                    Check(registers[0] == 0xCAFE && f.Image.TryCString(registers[1]) == "System" &&
                        f.Image.TryCString(registers[2]) == f.Exception.Name, "the actual lookup receives corelib and the exact metadata identity");
                    Events.Add("lookup"); result = 0xC1A55; break;
                case 0x3200:
                    Check(registers[0] == 0xC1A55, "the actual allocator receives that looked-up class");
                    Events.Add("allocate"); result = 0x0B1EC7; break;
                case 0x3300:
                    Check(registers[0] == 0x0B1EC7, "the actual constructor initializes the allocated object");
                    Events.Add("construct");
                    if (ConstructorFails) throw new ApplicationException("constructor failed");
                    Created = New(f.Exception.Name); result = 0xBAD; break;
                case 0x3400:
                    Check(registers[0] == 0x0B1EC7 && registers[1] == 0, "the exported raise backend receives the same object and null method");
                    Events.Add("raise"); throw Created ?? new InvalidOperationException("uninitialized exception");
                default: return false;
            }
            for (int n = 0; n <= 18; n++) registers[n] = 0xDEAD0000UL + (uint)n;
            registers[0] = result;
            return true;
        }

        public void Recovered(bool throws)
        {
            Events.Add("construct");
            if (ConstructorFails) throw new ApplicationException("constructor failed");
            Created = New(f.Exception.Name);
            if (throws) { Events.Add("raise"); throw Created; }
        }
    }

    private static void ExceptionFactories()
    {
        foreach (var (name, expected) in new[] {
            ("IndexOutOfRangeException", HelperKind.ThrowIndexOutOfRange),
            ("NullReferenceException", HelperKind.ThrowNullReference),
            ("DivideByZeroException", HelperKind.ThrowDivideByZero),
            ("InvalidCastException", HelperKind.ThrowInvalidCast),
            ("OverflowException", HelperKind.GetOverflowException) })
        {
            var f = Factory(name);
            int count = DiscoverFactories(f);
            Check(count == (name is "IndexOutOfRangeException" or "OverflowException" ? 2 : 1),
                "only supported factory/raise contracts are added");
            Check(f.Helpers.At(0x1100) is { NoReturn: true, ReturnsValue: false, IntArgs: 0 } h && h.Kind == expected,
                "metadata-backed default construction and exported raise determine the throw kind");
            if (name == "IndexOutOfRangeException") Check(f.Helpers.At(0x1000) is
                { Kind: HelperKind.GetIndexOutOfRangeException, ReturnsValue: true, NoReturn: false }, "a factory produces an exception and does not itself throw it");
            var native = new FactoryMachine(f); var recovered = new FactoryMachine(f);
            Type? a = Caught(() => native.Run(0x1100)), b = Caught(() => recovered.Recovered(true));
            Check(a == b && a?.Name == name, "actual native factory/raiser and recovered construction throw the same type");
            Check(native.Events.SequenceEqual(new[] { "corelib", "lookup", "allocate", "construct", "raise" }),
                "native construction occurs once and the nonempty-message arm never executes");
            Check(ReferenceEquals(native.Created?.GetType(), recovered.Created?.GetType()), "the exception's constructed type identity survives the raise");
            var returned = new FactoryMachine(f); returned.Run(0x1000);
            Check(returned.Result == 0x0B1EC7 && returned.Created?.GetType().Name == name && !returned.Events.Contains("raise"),
                "the factory returns the same initialized object without raising");
            foreach (bool original in new[] { true, false })
            {
                var failing = new FactoryMachine(f) { ConstructorFails = true };
                Type? failure = Caught(() => { if (original) failing.Run(0x1100); else failing.Recovered(true); });
                Check(failure == typeof(ApplicationException) && failing.Events.Count(e => e == "construct") == 1 && !failing.Events.Contains("raise"),
                    "constructor exceptions propagate once before the requested exception is raised");
            }
        }
        Cases.Add("ARM64 exception factories: runtime API identities, metadata constructor/ancestry, actual native object and exception flow");

        void Reject(string name, Action<FactoryFixture> mutate, bool factoryMayRemain = false)
        {
            var f = Factory(); mutate(f); DiscoverFactories(f);
            Check(f.Helpers.At(0x1100) == null && (factoryMayRemain || f.Helpers.At(0x1000) == null), name);
        }
        foreach (string export in new[] { "il2cpp_get_corlib", "il2cpp_class_from_name", "il2cpp_runtime_object_init", "il2cpp_raise_exception" })
            Reject("missing export identity: " + export, f => f.Image.Exports.Remove(export));
        Reject("a message/type string alone proves no allocator", f => f.Helpers.Add(0x3200, new HelperInfo(HelperKind.None, 1, false, true, "unknown")));
        Reject("allocator with an incompatible ABI", f => f.Helpers.Add(0x3200, new HelperInfo(HelperKind.ObjectNew, 2, false, true, "wrong arguments")));
        Reject("a no-return allocator is not an object factory", f => f.Helpers.Add(0x3200, new HelperInfo(HelperKind.ObjectNew, 1, true, false, "no result")));
        Reject("unknown core-library image", f => f.Types[0].Assembly.Name = "UserAssembly");
        Reject("mismatched core-library metadata image", f => f.Types[0].Assembly.ImageName = "Other.dll");
        Reject("same-named user type cannot replace the core-library type", f => f.Exception.Assembly = new AssemblyModel { Name = "Game" });
        Reject("same-named ambiguous type is refused before HIR name lookup", f => f.Types.Add(new TypeDef { Name = f.Exception.Name, Namespace = "System", Assembly = new AssemblyModel { Name = "Game" } }));
        Reject("duplicate core Object identity", f => f.Types.Add(f.Types[0]));
        Reject("not derived from the core Exception", f => f.Exception.BaseType = f.Types[0].Sig);
        Reject("cyclic base chain is not proof", f => f.Exception.BaseType = f.Exception.Sig);
        Reject("value type is not an exception object", f => f.Exception.IsValueType = true);
        Reject("abstract exception cannot be instantiated", f => f.Exception.Flags |= TypeDef.Abstract);
        Reject("generic exception is not a closed type identity", f => f.Exception.GenericParameters = [new GenericParam { Name = "T" }]);
        Reject("missing parameterless constructor", f => f.Exception.Methods = []);
        Reject("static constructor is not instance initialization", f => f.Exception.Methods[0].Flags |= MethodDef.Static);
        Reject("non-public constructor is outside the supported contract", f => f.Exception.Methods[0].Flags = 1);
        Reject("constructor parameters are not supplied", f => f.Exception.Methods[0].Parameters = [new ParamDef { Type = Int }]);
        Reject("constructor must return void", f => f.Exception.Methods[0].ReturnType = Int);
        Reject("ambiguous constructors", f => f.Exception.Methods = [f.Exception.Methods[0], f.Exception.Methods[0]]);
        Reject("writable string data is not a constant type argument", f => f.Image.Sections[1] = f.Image.Sections[1] with { Flags = SectionFlags.Read | SectionFlags.Write });
        Reject("unknown namespace does not identify a core type", f => f.Image.Text(0x8000, "Other"));
        Reject("unknown type name does not identify a metadata exception", f => f.Image.Text(0x8040, "NotAnException"));
        Reject("literal destination register is part of the proof", f => f.Image.Word(0x1014, 0x91000020));
        Reject("nonzero view length cannot use the default constructor path", f => f.Image.Word(0x1004, 0xA900FBE0));
        Reject("input arguments cannot replace the proved empty view", f => f.Image.Word(0x1020, 0xAA0003E3));
        Reject("a different corelib call is not sufficient", f => f.Image.Word(0x100C, VeneerBranch(0x100C, 0x3300, true)));
        Reject("a different class lookup is not sufficient", f => f.Image.Word(0x200C, VeneerBranch(0x200C, 0x3000, true)));
        Reject("a different constructor API is not sufficient", f => f.Image.Word(0x2018, VeneerBranch(0x2018, 0x3100, true)));
        Reject("view length must come from the zeroed field", f => f.Image.Word(0x201C, 0xF9400268));
        Reject("wrong empty-view branch target cannot skip arbitrary effects", f => f.Image.Word(0x2020, 0xB40000A8));
        Reject("changed return object is not the initialized exception", f => f.Image.Word(0x2038, 0xAA1303E0));
        Reject("unknown call before class lookup is not ignored", f => f.Image.Word(0x2008, VeneerBranch(0x2008, 0x3800, true)));
        Reject("managed body is not relabeled as a support factory", f => f.Managed.Add(0x1000));
        Reject("factory catches or cleanup need their own proof", f => f.LandingPads.Add(0x1000));
        Reject("shared constructor path with landing pads is refused", f => f.LandingPads.Add(0x2000));
        Reject("exported raise wrapper with a landing pad is refused", f => f.LandingPads.Add(0x4030));
        Reject("missing factory FDE is not replaced by a guessed size", f => f.Image.FunctionTable.RemoveAt(0));
        Reject("a new function entry inside the shape limits the extent", f => f.Context.ExtraStarts.Add(0x1010));
        Reject("shorter unwind extent limits the shape", f => f.Image.FunctionTable[0] = f.Image.FunctionTable[0] with { End = 0x1030 });
        Reject("extra body instructions need a separate proof", f => f.Image.FunctionTable[0] = f.Image.FunctionTable[0] with { End = 0x1038 });
        Reject("executable section boundary limits the shape", f => f.Image.Sections[0] = f.Image.Sections[0] with { Size = 0x30 });
        Reject("cyclic export thunks are not API identities", f => f.Image.Word(0x4000, VeneerBranch(0x4000, 0x4000)));
        Reject("changed thrower object flow is not ignored", f => f.Image.Word(0x1108, 0xAA1F03E0), factoryMayRemain: true);
        Reject("non-null hidden method differs from the exported raise contract", f => f.Image.Word(0x1108, 0xD2800021), factoryMayRemain: true);
        Reject("a different raise target is not the exported API", f => f.Image.Word(0x110C, VeneerBranch(0x110C, 0x3800, true)), factoryMayRemain: true);
        Reject("thrower landing pads must preserve exception behavior explicitly", f => f.LandingPads.Add(0x1100), factoryMayRemain: true);
        var relocated = Factory(factory: 0x1400); DiscoverFactories(relocated);
        Check(relocated.Helpers.At(0x1400)?.Kind == HelperKind.GetIndexOutOfRangeException &&
            relocated.Helpers.At(0x1100)?.Kind == HelperKind.ThrowIndexOutOfRange,
            "relocated forward/backward call relationships do not depend on game RVAs");
        Cases.Add("ARM64 exception factory rejection: literal-only guesses, API/ABI/metadata ambiguity, changed effects, unwind and EH boundaries");
    }
}
