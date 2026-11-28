using Mono.Cecil;
using Mono.Cecil.Cil;
using Rewind.Model;
using Rewind.Runtime;
using Rewind.Output;
static void Check(bool ok,string why){if(!ok)throw new Exception(why);}
var sig=new SigFactory();
var asm=new AssemblyModel{Name="Synthetic"};
var owner=new TypeDef{Index=1,Name="Example",Assembly=asm};owner.Sig=sig.TypeDef(owner);
var m=new MethodDef{Name="Swap",DeclaringType=owner,Flags=MethodDef.Static,ReturnType=sig.Primitive(Il2CppTypeEnum.Void)};
var p=new GenericParam{Index=1,Position=0,Name="T",OwnerMethod=m,IsMethodParameter=true};
m.GenericParameters=[p];m.Parameters=[new ParamDef{Type=sig.SzArray(sig.GenericParam(p))}];
Check(ClosedArraySpecializations.Eligible(m),"closed array shape");
m.Flags=0;Check(!ClosedArraySpecializations.Eligible(m),"instance");m.Flags=MethodDef.Static;
p.Flags=GenericParam.ReferenceTypeConstraint;Check(!ClosedArraySpecializations.Eligible(m),"constraint");p.Flags=0;
m.Parameters[0].Type=sig.SzArray(sig.Primitive(Il2CppTypeEnum.I4));Check(!ClosedArraySpecializations.Eligible(m),"not T[]");
using var mod=ModuleDefinition.CreateModule("synthetic",ModuleKind.Dll);
var type=new TypeDefinition("","Synthetic",TypeAttributes.Public,mod.TypeSystem.Object);mod.Types.Add(type);
var def=new MethodDefinition("F",MethodAttributes.Public|MethodAttributes.Static,mod.TypeSystem.Void);type.Methods.Add(def);
var t=new GenericParameter("T",def);def.GenericParameters.Add(t);def.Parameters.Add(new ParameterDefinition(new ArrayType(t)));
GenericInstanceMethod Call(TypeReference arg){var inst=new GenericInstanceMethod(def);inst.GenericArguments.Add(arg);return inst;}
Check(ClosedArraySpecializations.IsConcreteIntArrayCall(Instruction.Create(OpCodes.Call,Call(mod.TypeSystem.Int32)),def),"int call");
Check(!ClosedArraySpecializations.IsConcreteIntArrayCall(Instruction.Create(OpCodes.Call,Call(mod.TypeSystem.String)),def),"string call");
Check(!ClosedArraySpecializations.IsConcreteIntArrayCall(Instruction.Create(OpCodes.Ldftn,Call(mod.TypeSystem.Int32)),def),"delegate pointer");
Check(!ClosedArraySpecializations.IsConcreteIntArrayCall(Instruction.Create(OpCodes.Call,def),def),"open call");
var other=new MethodDefinition("Other",MethodAttributes.Static,mod.TypeSystem.Void);type.Methods.Add(other);
Check(!ClosedArraySpecializations.IsConcreteIntArrayCall(Instruction.Create(OpCodes.Call,Call(mod.TypeSystem.Int32)),other),"wrong identity");
Console.WriteLine("CLOSED_ARRAY_SPECIALIZATION_SMOKE_PASS positive=2 negative=7");
