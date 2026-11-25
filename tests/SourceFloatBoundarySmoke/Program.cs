using Mono.Cecil;
using Mono.Cecil.Cil;
using System.Security.Cryptography;
using Rewind.Output;

static void Check(bool pass,string why){if(!pass)throw new Exception(why);}
static string Hash(string path)=>Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(path)));
string root=Path.Combine(Path.GetTempPath(),"rewind-source-smoke-"+Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(root);
try{
 string path=Path.Combine(root,"Fixture.dll");
 using(var a=AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("Fixture",new Version(1,0)),"Fixture",ModuleKind.Dll)){
  var mod=a.MainModule;var type=new TypeDefinition("Fixture","Numeric",TypeAttributes.Public|TypeAttributes.Abstract|TypeAttributes.Sealed,mod.TypeSystem.Object);
  mod.Types.Add(type);
  MethodDefinition Make(string name){var m=new MethodDefinition(name,MethodAttributes.Public|MethodAttributes.Static,mod.TypeSystem.Single);m.Parameters.Add(new ParameterDefinition("value",ParameterAttributes.None,mod.TypeSystem.Single));type.Methods.Add(m);return m;}
  var m=Make("Branch");
  var p=m.Body.GetILProcessor();
  var convert=Instruction.Create(OpCodes.Conv_R4);
  var ret=Instruction.Create(OpCodes.Ret);
  // Branch to conversion and to the original successor: no incoming
  // branch is redirected to the synthetic call.
  p.Emit(OpCodes.Ldarg_0);p.Emit(OpCodes.Ldc_I4_0);p.Emit(OpCodes.Brtrue_S,ret);p.Emit(OpCodes.Br_S,convert);p.Append(convert);p.Append(ret);
  var eh=Make("Protected");
  eh.Body.InitLocals=true;eh.Body.Variables.Add(new VariableDefinition(mod.TypeSystem.Single));
  var q=eh.Body.GetILProcessor();
  var start=Instruction.Create(OpCodes.Ldarg_0);
  var last=Instruction.Create(OpCodes.Ldloc_0);
  var fin=Instruction.Create(OpCodes.Endfinally);
  q.Append(start);q.Emit(OpCodes.Conv_R4);q.Emit(OpCodes.Stloc_0);q.Emit(OpCodes.Leave_S,last);q.Append(fin);q.Append(last);q.Emit(OpCodes.Ret);
  eh.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Finally){TryStart=start,TryEnd=fin,HandlerStart=fin,HandlerEnd=last});
  var twice=Make("Twice");
  twice.Body.GetILProcessor().Emit(OpCodes.Ldarg_0);twice.Body.GetILProcessor().Emit(OpCodes.Conv_R4);twice.Body.GetILProcessor().Emit(OpCodes.Conv_R4);twice.Body.GetILProcessor().Emit(OpCodes.Ret);
  a.Write(path);
 }
 string before=Hash(path),copy;
 using(var off=new SourceFloatBoundaries(path,false))Check(off.AssemblyPath==path&&off.Calls==0,"disabled");
 using(var s=new SourceFloatBoundaries(path,true)){
  copy=s.AssemblyPath;Check(copy!=path&&s.Calls==4&&File.Exists(copy),"copy");
  using var a=AssemblyDefinition.ReadAssembly(copy);
  var helper=a.MainModule.Types.Single(t=>t.Name==SourceFloatBoundaries.HelperName).Methods.Single();
  Check((helper.ImplAttributes & MethodImplAttributes.NoInlining) != 0&&helper.Body.Instructions.Select(i=>i.OpCode.Code).SequenceEqual(new[]{Code.Ldarg_0,Code.Conv_R4,Code.Ret}),"helper implementation");
  var t=a.MainModule.Types.Single(t=>t.Name=="Numeric");
  foreach(var m in t.Methods)
   foreach(var i in m.Body.Instructions.Where(i=>i.OpCode.Code==Code.Conv_R4))
    Check(i.Next.OpCode.Code==Code.Call&&i.Next.Operand is MethodReference mr&&mr.FullName==helper.FullName,"boundary missing");
  var branch=t.Methods.Single(m=>m.Name=="Branch").Body;
  Check(branch.Instructions.Where(i=>i.Operand is Instruction).Select(i=>((Instruction)i.Operand).OpCode.Code).SequenceEqual(new[]{Code.Ret,Code.Conv_R4}),"branch retargeted");
  var eh=t.Methods.Single(m=>m.Name=="Protected").Body.ExceptionHandlers.Single();
  Check(eh.TryStart.OpCode.Code==Code.Ldarg_0&&eh.TryEnd.OpCode.Code==Code.Endfinally&&eh.HandlerEnd.OpCode.Code==Code.Ldloc_0,"EH retargeted");
  Check(Hash(path)==before,"input altered");
 }
 Check(!File.Exists(copy)&&Hash(path)==before,"temporary cleanup/input");
 string plain=Path.Combine(root,"Plain.dll");
 using(var a=AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("Plain",new Version(1,0)),"Plain",ModuleKind.Dll))a.Write(plain);
 using(var s=new SourceFloatBoundaries(plain,true))Check(s.AssemblyPath==plain&&s.Calls==0,"no FP32 conversions");
 string collision=Path.Combine(root,"Collision.dll");
 using(var a=AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("Collision",new Version(1,0)),"Collision",ModuleKind.Dll)){
  a.MainModule.Types.Add(new TypeDefinition("",SourceFloatBoundaries.HelperName,TypeAttributes.NotPublic,a.MainModule.TypeSystem.Object));a.Write(collision);
 }
 bool rejected=false;try{using var s=new SourceFloatBoundaries(collision,true);}catch(InvalidDataException){rejected=true;}
 Check(rejected,"helper identity collision accepted");
 Console.WriteLine("SOURCE_FLOAT_BOUNDARY_SMOKE_PASS conversions=4 branches=2 eh=1 cleanup=1 disabled=1 no_conversions=1 collision_rejected=1");
}finally{Directory.Delete(root,true);}
