using Mono.Cecil;
using Mono.Cecil.Cil;
using Rewind.Output;
using Rewind.Analysis.Recover;
using System.Reflection;
using MA=Mono.Cecil.MethodAttributes;
using FA=Mono.Cecil.FieldAttributes;
using TA=Mono.Cecil.TypeAttributes;

void Check(bool ok,string why){if(!ok)throw new Exception(why);}
uint[] native={0xd10243ff,0x6d012beb,0x6d0223e9,0xa9037bfd,0xa9046ffc,0xa90567fa,0xa9065ff8,0xa90757f6,0xa9084ff4,0x1e204068,0x1e204049,0x90017e36,0x1e20402a,0x1e20400b,0xd0016337,0x3944f2c8,0xf940e6f7,0xaa0203f4,0x2a0103f3,0xaa0003f5,0xa9000fe2};
Check(Arm64NullableParameterCopy.CompleteSpill(native,2,out var frame)&&frame==-144,"complete native spill");
int rejected=0;
void Reject(uint[] input,int register,string label){Check(!Arm64NullableParameterCopy.CompleteSpill(input,register,out _),label);rejected++;}
Reject(native,1,"wrong ABI register");
Reject(native.Skip(1).ToArray(),2,"missing frame allocation");
foreach(var replacement in new uint[]{0x94000000,0x14000000,0xb4000002,0xd5033f9f,0xaa0003e2,0xaa0003e3,0x1e260002,0x9e660003,0xffffffff}) {
 var copy=(uint[])native.Clone();copy[10]=replacement;Reject(copy,2,"unknown/control/argument overwrite "+replacement.ToString("X"));
}
foreach(var replacement in new uint[]{0xa9000be3,0xa9000fe1,0x29000fe2,0x6d000fe2,0xa9090fe2,0xa9bf0fe2}) {
 var copy=(uint[])native.Clone();copy[^1]=replacement;Reject(copy,2,"incomplete/reordered/outside spill "+replacement.ToString("X"));
}
var restore=(uint[])native.Clone();restore[10]=0x910243ff;Reject(restore,2,"stack changed before spill");

using var module=ModuleDefinition.CreateModule("ReadOnlyFixture",ModuleKind.Dll);
var value=new TypeDefinition("Fixture","Pair",TA.Public|TA.Sealed|TA.SequentialLayout,module.ImportReference(typeof(ValueType)));
var x=new FieldDefinition("x",FA.Public,module.TypeSystem.Int32);
var y=new FieldDefinition("y",FA.Public,module.TypeSystem.Int32);
value.Fields.Add(x);value.Fields.Add(y);module.Types.Add(value);
var host=new TypeDefinition("Fixture","Holder",TA.Public,module.TypeSystem.Object);module.Types.Add(host);
var held=new FieldDefinition("Held",FA.Public|FA.Static|FA.InitOnly,value);host.Fields.Add(held);
var init=new MethodDefinition(".cctor",MA.Private|MA.Static|MA.SpecialName|MA.RTSpecialName,module.TypeSystem.Void);host.Methods.Add(init);
var temp=new VariableDefinition(value);init.Body.Variables.Add(temp);init.Body.InitLocals=true;
var il=init.Body.GetILProcessor();
il.Emit(OpCodes.Ldloca,temp);il.Emit(OpCodes.Initobj,value);il.Emit(OpCodes.Ldloca,temp);il.Emit(OpCodes.Ldc_I4,0x12345678);il.Emit(OpCodes.Stfld,x);il.Emit(OpCodes.Ldloca,temp);il.Emit(OpCodes.Ldc_I4,unchecked((int)0xdeadbeef));il.Emit(OpCodes.Stfld,y);il.Emit(OpCodes.Ldloc,temp);il.Emit(OpCodes.Stsfld,held);il.Emit(OpCodes.Ret);
MethodDefinition Reader(string name, bool address){
 var m=new MethodDefinition(name,MA.Public|MA.Static,module.TypeSystem.Int32);host.Methods.Add(m);var q=m.Body.GetILProcessor();q.Emit(address?OpCodes.Ldsflda:OpCodes.Ldsfld,held);q.Emit(OpCodes.Ldfld,x);q.Emit(OpCodes.Ret);return m;
}
var fixedRead=Reader("Read",true);Check(ReadOnlyFieldReadIlFolding.Run(fixedRead.Body)==1,"readonly field corrected");Check(ReadOnlyFieldReadIlFolding.Run(fixedRead.Body)==0,"readonly idempotent");
var mutable=new FieldDefinition("Mutable",FA.Public|FA.Static,value);host.Fields.Add(mutable);
var mutableRead=Reader("MutableRead",true);mutableRead.Body.Instructions[0].Operand=mutable;Check(ReadOnlyFieldReadIlFolding.Run(mutableRead.Body)==0,"mutable field not rewritten");
var escape=Reader("AddressEscapes",true);escape.Body.Instructions[1].OpCode=OpCodes.Ldflda;Check(ReadOnlyFieldReadIlFolding.Run(escape.Body)==0,"address escape not rewritten");
var branch=Reader("Branched",true);var jump=Instruction.Create(OpCodes.Br,branch.Body.Instructions[1]);branch.Body.GetILProcessor().InsertBefore(branch.Body.Instructions[0],jump);Check(ReadOnlyFieldReadIlFolding.Run(branch.Body)==0,"foreign entry not rewritten");
var prefix=Reader("Volatile",true);prefix.Body.GetILProcessor().InsertBefore(prefix.Body.Instructions[0],Instruction.Create(OpCodes.Volatile));Check(ReadOnlyFieldReadIlFolding.Run(prefix.Body)==0,"prefix not rewritten");
host.Methods.Remove(escape);host.Methods.Remove(branch);host.Methods.Remove(prefix);
using var stream=new MemoryStream();module.Write(stream);
var loaded=Assembly.Load(stream.ToArray());var method=loaded.GetType("Fixture.Holder")!.GetMethod("Read")!;
for(int n=0;n<32;n++)Check((int)method.Invoke(null,null)! ==0x12345678,"runtime readonly field value");
Console.WriteLine("FIELD_RECOVERY_SMOKE_PASS native_positive=1 native_negative="+rejected+" readonly_positive=1 readonly_negative=4 runtime_value_reads=32");
