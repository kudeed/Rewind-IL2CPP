using System.Security.Cryptography;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Output;

/// <summary>Opt-in recovery of the concrete Int32[] instance of a static
/// generic void F&lt;T&gt;(T[]) whose open shared implementation has gaps.
/// Never replaces or marks the open generic definition clean.</summary>
internal static class ClosedArraySpecializations
{
    internal static bool Eligible(MethodDef m)
    {
        return m.IsStatic && !m.IsConstructor && !m.IsVirtual &&
            m.DeclaringType.GenericParameters.Length==0 &&
            m.GenericParameters.Length==1 && m.GenericParameters[0].Constraints.Length==0 && m.GenericParameters[0].Flags==0 && m.ReturnType.IsVoid &&
            m.Parameters.Length==1 &&
            m.Parameters[0].Type is SzArraySig {ElementType:GenericParamSig p} &&
            ReferenceEquals(p.Parameter,m.GenericParameters[0]);
    }

    internal static bool IsConcreteIntArrayCall(Instruction i,MethodDefinition definition)
    {
        return i.OpCode.Code==Code.Call && i.Operand is GenericInstanceMethod g &&
            g.ElementMethod==definition && g.GenericArguments.Count==1 &&
            g.GenericArguments[0].MetadataType==MetadataType.Int32;
    }

    internal static void Run(Il2CppModel model,ProgramAnalysis program,AssemblyEmitter emitter,BodyEmitter bodies,
        IEnumerable<MethodDef> selected,IEnumerable<MethodDef> gaps,DecompileOptions options)
    {
        if(Environment.GetEnvironmentVariable("REWIND_CLOSED_ARRAY_SPECIALIZATIONS")!="1")return;
        var selectedMethods=selected.Where(AssemblyEmitter.HasIlBody).Select(m=>(Original:m,Emitted:emitter[m])).ToArray();
        var pipeline=new MethodPipeline(program);
        var report=new List<object>();
        foreach(var method in gaps.Where(Eligible).OrderBy(m=>m.Index))
        {
            var definition=emitter[method];
            var uses=selectedMethods.Where(c=>c.Emitted.Module==definition.Module&&c.Emitted.HasBody)
                .SelectMany(c=>c.Emitted.Body.Instructions.Where(i=>IsConcreteIntArrayCall(i,definition))
                    .Select(i=>(Caller:c.Original,Instruction:i))).ToArray();
            if(uses.Length==0)continue;
            var instances=program.InstsOf(method).Where(i=>i.Address!=0&&i.ClassArguments.Length==0&&
                i.MethodArguments is [PrimitiveSig{Element:Il2CppTypeEnum.I4}]).ToArray();
            if(instances.Length!=1||program.RangeOf(instances[0].Address) is not {} range||
                range.End<=range.Start||range.End-range.Start>int.MaxValue||
                !model.Image.TrySpan(range.Start,(int)(range.End-range.Start),out var bytes))
                continue;
            var instance=instances[0];
            try
            {
                var h=pipeline.Recover(instance);
                if(h.Problems.Count!=0||h.UnidentifiedNativeCalls.Count!=0||h.TryRegions.Count!=0||
                    h.Locals.Any(v=>v.Type.ContainsGenericParameter)||h.Blocks.Count==0)
                    continue;
                // The concrete HIR uses the original MethodDef for identity;
                // give the writer an independent closed signature instead.
                var array=model.Sigs.Substitute(method.Parameters[0].Type,[],instance.MethodArguments);
                if(array is not SzArraySig {ElementType:PrimitiveSig{Element:Il2CppTypeEnum.I4}})continue;
                string name=$"__RewindClosed_{method.Token:X8}_I4";
                if(definition.DeclaringType.Methods.Any(m=>m.Name==name))
                    throw new InvalidDataException("specialization helper collision "+name);
                var closed=new MethodDef {
                    Name=name,DeclaringType=method.DeclaringType,Flags=(ushort)(MethodDef.Static|MethodDef.HideBySig|3),
                    ReturnType=method.ReturnType,Parameters=[new ParamDef{Name=method.Parameters[0].Name,Position=0,Type=array}]
                };
                var target=new MethodDefinition(name,MethodAttributes.Assembly|MethodAttributes.Static|MethodAttributes.HideBySig,
                    emitter.Import(definition.Module,closed.ReturnType));
                target.Parameters.Add(new ParameterDefinition(closed.Parameters[0].Name,ParameterAttributes.None,emitter.Import(definition.Module,array)));
                definition.DeclaringType.Methods.Add(target);
                string? error;
                try { error=bodies.EmitTo(closed,h,target); }
                catch {definition.DeclaringType.Methods.Remove(target);throw;}
                if(error!=null||!target.HasBody||target.Body.Variables.Any(v=>v.VariableType.ContainsGenericParameter)||
                    target.Body.Instructions.Any(i=>i.Operand is MethodReference mr&&(mr.DeclaringType.Name=="__Rewind"||mr.ContainsGenericParameter)||
                        i.Operand is TypeReference tr&&tr.ContainsGenericParameter||
                        i.Operand is FieldReference fr&&fr.ContainsGenericParameter))
                {definition.DeclaringType.Methods.Remove(target);continue;}
                foreach(var use in uses)use.Instruction.Operand=target;
                report.Add(new {
                    assembly=method.DeclaringType.Assembly.Name,declaring_type=method.DeclaringType.ReflectionName,
                    method_name=method.Name,metadata_token=$"0x{method.Token:X}",instance="System.Int32",
                    native_start=$"0x{range.Start:X}",native_end=$"0x{range.End:X}",native_sha256=Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant(),
                    generated_method=name,call_sites=uses.Select(u=>new {declaring_type=u.Caller.DeclaringType.ReflectionName,
                        method_name=u.Caller.Name,metadata_token=$"0x{u.Caller.Token:X}",parameter_types=u.Caller.Parameters.Select(p=>p.Type.DisplayName).ToArray()}).ToArray(),
                    status="concrete_hir_clean_open_definition_unchanged"
                });
            }
            catch(Exception ex) when(ex is not OutOfMemoryException and not StackOverflowException)
            {options.Log($"closed array specialization refused {method.FullName}: {ex.GetType().Name}: {ex.Message}");}
        }
        Directory.CreateDirectory(options.OutputDirectory);
        File.WriteAllText(Path.Combine(options.OutputDirectory,"closed-specializations.json"),JsonSerializer.Serialize(report,new JsonSerializerOptions{WriteIndented=true}));
        options.Log($"closed Int32[] specializations: {report.Count} emitted; open generic gap ledger unchanged");
    }
}
