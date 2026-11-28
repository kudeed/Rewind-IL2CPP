using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Analysis.Abi;

/// <summary>
/// IL2CPP's fully shared return ABI is an explicit buffer after the managed arguments and before
/// MethodInfo, not the platform's x8 large-struct return. Select it only from a registered native
/// instantiation at the exact body address. A T[] or reference generic source containing that T
/// can use typed elements or a proved invoker address table. Direct-T parameter conventions remain
/// unsupported and keep their existing diagnostics.
/// </summary>
internal static class FullySharedAbi
{
    private static bool Placeholder(TypeSig type) =>
        type is TypeDefSig { Definition: { Namespace: "Unity.IL2CPP.Metadata",
            Name: "__Il2CppFullySharedGenericType" or "__Il2CppFullySharedGenericStructType" } };

    public static MethodAbi For(ProgramAnalysis program, MethodDef method, TypeSig[] classArguments,
        TypeSig[] methodArguments, ulong address) =>
        Adapt(program.Model.Image.Arch, program.Model.Sigs, method, program.InstsOf(method),
            program.Abi.For(method, classArguments, methodArguments), address);

    private static bool SharedValue(TypeSig type) => Placeholder(type) ||
        type is GenericInstSig { IsValueType: true } value && value.Arguments.Any(SharedValue);

    private static bool ContainsReturnedValue(TypeSig parameter, TypeSig returned) =>
        parameter is SzArraySig array && array.ElementType.Key == returned.Key ||
        parameter is GenericInstSig { IsValueType: false } reference &&
        reference.Arguments.Any(argument => argument.Key == returned.Key);

    internal static MethodAbi Adapt(CpuArch arch, SigFactory sigs, MethodDef method,
        IEnumerable<MethodInst> instances, MethodAbi ordinary, ulong address)
    {
        if (arch == CpuArch.Arm64 && address != 0 && method.IsStatic && method.ReturnType.IsVoid &&
            ordinary.Return == ReturnKind.Void && method.Parameters is [{ Type: SzArraySig { ElementType: GenericParamSig element } }] &&
            ordinary.Params is [{ Role: ParamRole.Argument, ArgumentIndex: 0, Pass: PassKind.Integer, Position: 0 },
                { Role: ParamRole.MethodInfo, Position: 1 }])
        {
            // A void(T[]) body has no additional return argument. Its T scratch locals and element
            // stride still use the fully shared runtime sizes, proved by the registered instantiation.
            bool registered = instances.Any(instance => ReferenceEquals(instance.Method, method) &&
                instance.Address == address && Placeholder(sigs.Substitute(element, instance.ClassArguments, instance.MethodArguments)));
            if (registered)
            {
                var runtime = new MethodAbi
                {
                    Return = ordinary.Return, ReturnType = ordinary.ReturnType, ReturnSize = ordinary.ReturnSize,
                    Known = ordinary.Known, ReturnCount = ordinary.ReturnCount, ReturnIsDouble = ordinary.ReturnIsDouble,
                    UsesFullySharedRuntime = true
                };
                runtime.Params.AddRange(ordinary.Params);
                return runtime;
            }
        }
        if (arch != CpuArch.Arm64 || address == 0 ||
            method.ReturnType is not GenericParamSig || ordinary.Return != ReturnKind.Integer ||
            !method.Parameters.Any(p => ContainsReturnedValue(p.Type, method.ReturnType)))
            return ordinary;

        // Direct-T and value types containing T also change their argument convention under full sharing. Do not partially reinterpret
        // one of those signatures until its argument buffers are supported.
        bool found = false;
        foreach (MethodInst instance in instances)
        {
            if (!ReferenceEquals(instance.Method, method) || instance.Address != address) continue;
            TypeSig nativeReturn = sigs.Substitute(method.ReturnType, instance.ClassArguments, instance.MethodArguments);
            if (!Placeholder(nativeReturn)) continue;
            if (method.Parameters.Any(p => SharedValue(sigs.Substitute(p.Type, instance.ClassArguments, instance.MethodArguments))))
                return ordinary;
            found = true;
        }
        if (!found || ordinary.Params.SingleOrDefault(p => p.Role == ParamRole.MethodInfo) is not { } info ||
            ordinary.Params.Any(p => p.Role == ParamRole.ReturnBuffer) ||
            info.Position is < 0 or > 6) return ordinary;

        // This narrowly supported shape fits entirely in the integer argument bank. There is no
        // stack-argument rebasing and the existing floating arguments keep their independent positions.
        var shared = new MethodAbi
        {
            Return = ReturnKind.Buffer, ReturnType = ordinary.ReturnType, ReturnSize = 0,
            Known = ordinary.Known, UsesFullySharedReturnBuffer = true, UsesFullySharedRuntime = true,
            ReturnCount = ordinary.ReturnCount, ReturnIsDouble = ordinary.ReturnIsDouble
        };
        shared.Params.AddRange(ordinary.Params.Where(p => p.Role != ParamRole.MethodInfo));
        shared.Params.Add(new AbiParam(ParamRole.ReturnBuffer, -1, ordinary.ReturnType, PassKind.Integer, info.Position, false, 8));
        shared.Params.Add(info with { Position = info.Position + 1 });
        return shared;
    }
}
