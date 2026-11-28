using Mono.Cecil;
using Mono.Cecil.Cil;
using Mono.Cecil.Rocks;
using Rewind.Output;
using System.Reflection;
using TypeAttributes=Mono.Cecil.TypeAttributes;
using MethodAttributes=Mono.Cecil.MethodAttributes;
using FieldAttributes=Mono.Cecil.FieldAttributes;
using MethodBody=Mono.Cecil.Cil.MethodBody;
static void Check(bool ok,string why){if(!ok)throw new Exception(why);}
static IEnumerable<TypeDefinition> All(IEnumerable<TypeDefinition> types)=>types.SelectMany(t=>new[]{t}.Concat(All(t.NestedTypes)));
if(args.Length==2)
{
    using var r=new DefaultAssemblyResolver();r.AddSearchDirectory(Path.GetDirectoryName(Path.GetFullPath(args[0]))!);
    using var corpus=AssemblyDefinition.ReadAssembly(args[0],new ReaderParameters{AssemblyResolver=r,InMemory=true});
    int sites=0,methods=0;
    foreach(var m in All(corpus.MainModule.Types).SelectMany(t=>t.Methods).Where(m=>m.HasBody))
    {
        int n=VirtualDelegateDup.Run(m.Body);if(n==0)continue;
        m.Body.OptimizeMacros();sites+=n;methods++;
        Console.WriteLine($"{m.MetadataToken.ToUInt32():X8} {n} {m.FullName}");
    }
    corpus.Write(args[1]);
    Console.WriteLine(System.Text.Json.JsonSerializer.Serialize(new{sites,methods}));return;
}
using var resolver=new DefaultAssemblyResolver();
resolver.AddSearchDirectory(Path.GetDirectoryName(typeof(object).Assembly.Location)!);
using var asm=AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("DelegateFixture",new Version(1,0)),"DelegateFixture",
    new ModuleParameters{Kind=ModuleKind.Dll,AssemblyResolver=resolver});
var mod=asm.MainModule;var obj=mod.ImportReference(typeof(object));var vd=mod.ImportReference(typeof(void));var i32=mod.ImportReference(typeof(int));var action=mod.ImportReference(typeof(Action));
var baseType=new TypeDefinition("Fixture","Receiver",TypeAttributes.Public|TypeAttributes.Class,obj);mod.Types.Add(baseType);
var derived=new TypeDefinition("Fixture","Derived",TypeAttributes.Public|TypeAttributes.Class,baseType);mod.Types.Add(derived);
var count=new FieldDefinition("Count",FieldAttributes.Public,i32);baseType.Fields.Add(count);
MethodDefinition Constructor(TypeDefinition t,MethodReference parent)
{
    var m=new MethodDefinition(".ctor",MethodAttributes.Public|MethodAttributes.SpecialName|MethodAttributes.RTSpecialName|MethodAttributes.HideBySig,vd);
    t.Methods.Add(m);m.Body=new MethodBody(m);var il=m.Body.GetILProcessor();
    il.Emit(OpCodes.Ldarg_0);il.Emit(OpCodes.Call,parent);il.Emit(OpCodes.Ret);return m;
}
var bc=Constructor(baseType,mod.ImportReference(typeof(object).GetConstructor(Type.EmptyTypes)!));Constructor(derived,bc);
MethodDefinition Tick(TypeDefinition t,int step,bool fresh)
{
    var m=new MethodDefinition("Tick",MethodAttributes.Public|MethodAttributes.Virtual|MethodAttributes.HideBySig|(fresh?MethodAttributes.NewSlot:0),vd);
    t.Methods.Add(m);m.Body=new MethodBody(m);var il=m.Body.GetILProcessor();il.Emit(OpCodes.Ldarg_0);il.Emit(OpCodes.Dup);il.Emit(OpCodes.Ldfld,count);il.Emit(OpCodes.Ldc_I4,step);il.Emit(OpCodes.Add);il.Emit(OpCodes.Stfld,count);il.Emit(OpCodes.Ret);return m;
}
var tick=Tick(baseType,1,true);Tick(derived,10,false);
var ctor=mod.ImportReference(typeof(Action).GetConstructor(new[]{typeof(object),typeof(IntPtr)})!);
MethodDefinition Make(string name,bool instance=false,bool local=false)
{
    var m=new MethodDefinition(name,MethodAttributes.Public|(instance?0:MethodAttributes.Static),action);baseType.Methods.Add(m);
    if(!instance)m.Parameters.Add(new ParameterDefinition(baseType));
    m.Body=new MethodBody(m){InitLocals=true};var il=m.Body.GetILProcessor();
    var arg=instance?m.Body.ThisParameter:m.Parameters[0];
    if(local){var v=new VariableDefinition(baseType);m.Body.Variables.Add(v);il.Emit(OpCodes.Ldarg,arg);il.Emit(OpCodes.Stloc,v);il.Emit(OpCodes.Ldloc,v);il.Emit(OpCodes.Ldloc,v);}
    else{il.Emit(OpCodes.Ldarg,arg);il.Emit(OpCodes.Ldarg,arg);}
    il.Emit(OpCodes.Ldvirtftn,tick);il.Emit(OpCodes.Newobj,ctor);il.Emit(OpCodes.Ret);return m;
}
var a=Make("Instance",true);var b=Make("Argument");var c=Make("Local",local:true);
foreach(var m in new[]{a,b,c}){Check(VirtualDelegateDup.Run(m.Body)==1,"positive "+m.Name);Check(m.Body.Instructions.Count(i=>i.OpCode.Code==Code.Dup)==1,"canonical dup");m.Body.OptimizeMacros();}
var negatives=new List<MethodDefinition>();
var different=Make("Different");different.Parameters.Add(new ParameterDefinition(baseType));different.Body.Instructions[1].Operand=different.Parameters[1];negatives.Add(different);
var intoMiddle=Make("IntoMiddle");intoMiddle.Body.GetILProcessor().InsertBefore(intoMiddle.Body.Instructions[0],Instruction.Create(OpCodes.Br,intoMiddle.Body.Instructions[1]));negatives.Add(intoMiddle);
var nonDelegate=Make("NonDelegate");nonDelegate.Body.Instructions[3].Operand=bc;negatives.Add(nonDelegate);
var badReceiver=Make("BadReceiver");badReceiver.Parameters[0].ParameterType=i32;negatives.Add(badReceiver);
var noVirtual=Make("NoVirtual");noVirtual.Body.Instructions[2].OpCode=OpCodes.Ldftn;negatives.Add(noVirtual);
var intoCtor=Make("IntoCtor");intoCtor.Body.GetILProcessor().InsertBefore(intoCtor.Body.Instructions[0],Instruction.Create(OpCodes.Br,intoCtor.Body.Instructions[3]));negatives.Add(intoCtor);
static string Shape(MethodDefinition m)=>string.Join("\n",m.Body.Instructions.Select(i=>i.OpCode.Code+":"+i.Operand));
foreach(var m in negatives){var before=Shape(m);Check(VirtualDelegateDup.Run(m.Body)==0&&before==Shape(m),"negative "+m.Name);baseType.Methods.Remove(m);}
using var stream=new MemoryStream();asm.Write(stream);
var loaded=Assembly.Load(stream.ToArray());var rb=loaded.GetType("Fixture.Receiver")!;var rd=loaded.GetType("Fixture.Derived")!;int runs=0;
foreach(var t in new[]{rb,rd})
{
 var target=Activator.CreateInstance(t)!;
 foreach(var name in new[]{"Instance","Argument","Local"})
 {
  var method=rb.GetMethod(name)!;
  var callback=(Action)method.Invoke(method.IsStatic?null:target,method.IsStatic?[target]:null)!;
  Check(ReferenceEquals(callback.Target,target),"delegate target changed");
  for(int n=0;n<100;n++){callback();runs++;}
 }
 Check((int)rb.GetField("Count")!.GetValue(target)! == (t==rd?3000:300),"virtual dispatch");
}
foreach(var name in new[]{"Argument","Local"})
try{rb.GetMethod(name)!.Invoke(null,[null]);throw new Exception("lost null exception");}catch(TargetInvocationException e)when(e.InnerException is NullReferenceException){}
Console.WriteLine($"VIRTUAL_DELEGATE_DUP_SMOKE_PASS runtime_calls={runs} positive=3 negative={negatives.Count} null_cases=2");
