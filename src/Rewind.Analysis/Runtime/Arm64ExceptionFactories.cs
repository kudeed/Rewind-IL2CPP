using Rewind.Analysis.Arm64;
using Rewind.Analysis.X64;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// Empty-message core-library exception factories, proved through exported runtime APIs and metadata.
/// Literal type names are arguments to an identified class lookup, never standalone type evidence.
/// </summary>
internal static class Arm64ExceptionFactories
{
    private sealed record ExceptionType(TypeDef Type, HelperKind? Factory, HelperKind Thrower);

    internal static int Identify(ICodeContext context, IReadOnlyList<ulong> starts, IReadOnlyList<TypeDef> types,
        RuntimeHelpers helpers, Func<ulong, bool> isManaged, Func<ulong, bool> hasLandingPads)
    {
        if (context.Image.Arch != CpuArch.Arm64 || context.Image.Format != ImageFormat.Elf) return 0;
        return new Proof(context, starts, types, helpers, isManaged, hasLandingPads).Run();
    }

    private sealed class Proof(ICodeContext context, IReadOnlyList<ulong> starts, IReadOnlyList<TypeDef> types,
        RuntimeHelpers helpers, Func<ulong, bool> isManaged, Func<ulong, bool> hasLandingPads)
    {
        private readonly NativeImage image = context.Image;
        private readonly Dictionary<ulong, ulong> ends = [];
        private readonly Dictionary<ulong, bool> coreFactories = [];
        private readonly Dictionary<ulong, ExceptionType> factories = [];
        private ulong corlib, classFromName, objectInit, raise;
        private AssemblyModel? coreAssembly;
        private TypeDef? exceptionBase;

        internal int Run()
        {
            foreach (FunctionRange range in image.FunctionTable)
                if (!range.Chained && range.End > range.Start)
                    ends[range.Start] = ends.TryGetValue(range.Start, out ulong previous)
                        ? Math.Min(previous, range.End) : range.End;
            if (!CoreMetadata() || !Export("il2cpp_get_corlib", out corlib) ||
                !Export("il2cpp_class_from_name", out classFromName) ||
                !Export("il2cpp_runtime_object_init", out objectInit) || !RaiseExport()) return 0;

            int added = 0;
            foreach (ulong start in starts)
            {
                if (isManaged(start) || FixedFactory(start) is not { } type) continue;
                factories[start] = type;
                if (type.Factory is { } kind && helpers.At(start) == null)
                {
                    helpers.Add(start, new HelperInfo(kind, 0, false, true,
                        type.Type.ReflectionName + " default factory (runtime API and metadata proof)"));
                    added++;
                }
            }
            foreach (ulong start in starts)
            {
                if (isManaged(start) || helpers.At(start) != null || !Body(start, 16, out var body) ||
                    body[0].Word != 0xF81F0FFE || body[1].Op != A64Op.Bl ||
                    body[2].Word != 0xAA1F03E1 || body[3].Op != A64Op.Bl ||
                    Canonical(body[3].Target) != raise || !factories.TryGetValue(body[1].Target, out var type)) continue;
                helpers.Add(start, new HelperInfo(type.Thrower, 0, true, false,
                    type.Type.ReflectionName + " default factory and raise (runtime API and metadata proof)"));
                added++;
            }
            return added;
        }

        private bool CoreMetadata()
        {
            // HIR's well-known exception lookup is by full name. Refuse an ambiguous name even if one
            // candidate has the right assembly, so a same-named user type cannot be selected later.
            TypeDef[] objects = types.Where(t => t.ReflectionName == "System.Object").ToArray();
            TypeDef[] exceptions = types.Where(t => t.ReflectionName == "System.Exception").ToArray();
            if (objects.Length != 1 || exceptions.Length != 1) return false;
            TypeDef obj = objects[0], ex = exceptions[0];
            if (obj.Assembly.Name is not ("mscorlib" or "System.Private.CoreLib") ||
                obj.Assembly.ImageName != obj.Assembly.Name + ".dll" || obj.BaseType != null ||
                obj.IsValueType || obj.IsInterface || obj.IsNested || obj.IsGenericDefinition || obj.IsAbstract ||
                !ReferenceEquals(ex.Assembly, obj.Assembly) || !ReferenceEquals(ex.BaseType?.Definition, obj) ||
                ex.IsValueType || ex.IsInterface || ex.IsNested || ex.IsGenericDefinition) return false;
            coreAssembly = obj.Assembly;
            exceptionBase = ex;
            return true;
        }

        private ExceptionType? MetadataType(string ns, string name)
        {
            if (ns != "System") return null;
            (HelperKind? Factory, HelperKind Thrower)? kinds = name switch
            {
                "IndexOutOfRangeException" => (HelperKind.GetIndexOutOfRangeException, HelperKind.ThrowIndexOutOfRange),
                "NullReferenceException" => (null, HelperKind.ThrowNullReference),
                "DivideByZeroException" => (null, HelperKind.ThrowDivideByZero),
                "InvalidCastException" => (null, HelperKind.ThrowInvalidCast),
                "OverflowException" => (HelperKind.GetOverflowException, HelperKind.GetOverflowException),
                _ => null
            };
            if (kinds == null) return null;
            TypeDef[] matches = types.Where(t => t.ReflectionName == ns + "." + name).ToArray();
            if (matches.Length != 1) return null;
            TypeDef type = matches[0];
            if (!ReferenceEquals(type.Assembly, coreAssembly) || type.IsValueType || type.IsInterface ||
                type.IsNested || type.IsGenericDefinition || type.IsAbstract ||
                type.Methods.Count(m => m.Name == ".ctor" && ReferenceEquals(m.DeclaringType, type) &&
                    !m.IsStatic && !m.IsAbstract && (m.Flags & MethodDef.AccessMask) == 6 &&
                    m.GenericParameters.Length == 0 && m.Parameters.Length == 0 && m.ReturnType.IsVoid) != 1) return null;
            var seen = new HashSet<TypeDef>();
            for (TypeDef? parent = type; parent != null && seen.Add(parent); parent = parent.BaseType?.Definition)
            {
                if (!ReferenceEquals(parent.Assembly, coreAssembly) || parent.IsValueType || parent.IsInterface ||
                    parent.IsGenericDefinition) return null;
                if (ReferenceEquals(parent, exceptionBase)) return new ExceptionType(type, kinds.Value.Factory, kinds.Value.Thrower);
            }
            return null;
        }

        private ExceptionType? FixedFactory(ulong start)
        {
            // A two-word empty string view and a separately saved LR; its zero length is what proves the
            // shared factory takes only its default-constructor path. The incoming argument registers
            // are never read by this complete function.
            if (!Body(start, 52, out var b) || b[0].Word != 0xD10083FF || b[1].Word != 0xA900FBFF ||
                b[2].Word != 0xF90003FF || b[3].Op != A64Op.Bl || Canonical(b[3].Target) != corlib ||
                !Literal(b[4], b[5], 1, out string ns) || !Literal(b[6], b[7], 2, out string name) ||
                b[8].Word != 0x910003E3 || b[9].Op != A64Op.Bl ||
                b[10].Word != 0xF9400BFE || b[11].Word != 0x910083FF || b[12].Word != 0xD65F03C0 ||
                !CoreFactory(b[9].Target)) return null;
            return MetadataType(ns, name);
        }

        private bool CoreFactory(ulong address)
        {
            if (coreFactories.TryGetValue(address, out bool known)) return known;
            bool proved = CoreFactoryBody(address);
            coreFactories[address] = proved;
            return proved;
        }

        private bool CoreFactoryBody(ulong address)
        {
            // x0/image, x1/namespace and x2/name reach the exported class lookup unchanged. Its result
            // goes directly to the already-identified allocator, then the exported constructor API.
            // x19 preserves the empty view across those ABI calls; its length at +8 is exactly zero.
            // The nonempty-message arm is unreachable for the accepted caller and is not interpreted.
            if (!Body(address, 72, out var b) || b[0].Word != 0xF81E0FFE || b[1].Word != 0xA9014FF4 ||
                b[2].Word != 0xAA0303F3 || b[3].Op != A64Op.Bl || Canonical(b[3].Target) != classFromName ||
                b[4].Op != A64Op.Bl || helpers.At(b[4].Target) is not
                    { Kind: HelperKind.ObjectNew, IntArgs: 1, FloatArgs: 0, NoReturn: false, ReturnsValue: true } ||
                b[5].Word != 0xAA0003F4 || b[6].Op != A64Op.Bl || Canonical(b[6].Target) != objectInit ||
                b[7].Word != 0xF9400668 || b[8].Op != A64Op.Cbz || !b[8].Is64 || b[8].Rd != 8 ||
                b[8].Target != address + 56 || b[14].Word != 0xAA1403E0 ||
                b[15].Word != 0xA9414FF4 || b[16].Word != 0xF84207FE || b[17].Word != 0xD65F03C0)
                return false;
            return true;
        }

        private bool RaiseExport()
        {
            if (!Export("il2cpp_raise_exception", out ulong entry) || !Body(entry, 12, out var b) ||
                b[0].Word != 0xF81F0FFE || b[1].Word != 0xAA1F03E1 || b[2].Op != A64Op.Bl) return false;
            // The exported API and recognized thrower both preserve x0 and explicitly supply null x1.
            // This does not assign semantics to arbitrary functions which happen to call __cxa_throw.
            raise = Canonical(b[2].Target);
            return raise != 0 && raise != entry;
        }

        private bool Export(string name, out ulong address)
        {
            address = image.Exports.TryGetValue(name, out ulong entry) ? Canonical(entry) : 0;
            return address != 0;
        }

        private ulong Canonical(ulong address)
        {
            var seen = new HashSet<ulong>();
            for (int depth = 0; depth < 8; depth++)
            {
                if (!seen.Add(address) || isManaged(address) || !context.IsFunctionStart(address) ||
                    !image.IsCodeAddress(address) || !image.IsMapped(address, 4)) return 0;
                if (!Body(address, 4, out var b) || b[0].Op != A64Op.B) return address;
                address = b[0].Target;
            }
            return 0;
        }

        private bool Body(ulong start, int size, out A64Instruction[] instructions)
        {
            instructions = [];
            if ((start & 3) != 0 || isManaged(start) || !context.IsFunctionStart(start) ||
                !ends.TryGetValue(start, out ulong end) || image.SectionAt(start) is not { IsExecutable: true } section)
                return false;
            ulong next = context.NextFunctionStart(start);
            if (next != 0) end = Math.Min(end, next);
            if (end <= start || end - start != (ulong)size || end > section.End || !image.IsMapped(start, size) || hasLandingPads(start)) return false;
            instructions = new A64Instruction[size / 4];
            for (int i = 0; i < instructions.Length; i++)
                instructions[i] = A64Decoder.Decode(image.U32(start + (uint)i * 4), start + (uint)i * 4);
            return true;
        }

        private bool Literal(A64Instruction page, A64Instruction offset, byte register, out string text)
        {
            text = "";
            if (page.Op != A64Op.Adrp || page.Rd != register || offset.Op != A64Op.AddImm ||
                !offset.Is64 || offset.SetFlags || offset.Rn != register || offset.Rd != register ||
                offset.Imm < 0 || page.Target > ulong.MaxValue - (ulong)offset.Imm) return false;
            ulong address = page.Target + (ulong)offset.Imm;
            if (image.SectionAt(address) is not { IsExecutable: false, IsWritable: false } section ||
                image.TryCString(address, 128) is not { Length: > 0 and <= 96 } value ||
                address + (uint)value.Length + 1 > section.End ||
                value.Any(c => !(char.IsAsciiLetterOrDigit(c) || c is '_' or '.'))) return false;
            text = value;
            return true;
        }
    }
}
