using Mono.Cecil;
using Mono.Cecil.Cil;
using Mono.Cecil.Rocks;
using Rewind.Output;
using System.Reflection;
using System.Numerics;
using TypeAttributes=Mono.Cecil.TypeAttributes;
using FieldAttributes=Mono.Cecil.FieldAttributes;
using MethodAttributes=Mono.Cecil.MethodAttributes;
using MethodBody=Mono.Cecil.Cil.MethodBody;
static void Check(bool b,string why){if(!b)throw new Exception(why);}
static IEnumerable<TypeDefinition> All(IEnumerable<TypeDefinition> types)=>types.SelectMany(t=>new[]{t}.Concat(All(t.NestedTypes)));
if(args.Length==2)
{
    using var r=new DefaultAssemblyResolver();r.AddSearchDirectory(Path.GetDirectoryName(Path.GetFullPath(args[0]))!);
    using var a=AssemblyDefinition.ReadAssembly(args[0],new ReaderParameters{AssemblyResolver=r,InMemory=true});
    int sites=0,methods=0;
    foreach(var m in All(a.MainModule.Types).SelectMany(t=>t.Methods).Where(m=>m.HasBody)){
        int n=ListClearIlFolding.Run(m.Body);if(n==0)continue;
        m.Body.OptimizeMacros();sites+=n;methods++;
        Console.WriteLine($"{m.MetadataToken.ToUInt32():X8} {n} {m.FullName}");
    }
    a.Write(args[1]);
    Console.WriteLine(System.Text.Json.JsonSerializer.Serialize(new{folded_sites=sites,changed_methods=methods}));
    return;
}
using var resolver=new DefaultAssemblyResolver();
resolver.AddSearchDirectory(Path.GetDirectoryName(typeof(List<>).Assembly.Location)!);
resolver.AddSearchDirectory(Path.GetDirectoryName(typeof(Vector2).Assembly.Location)!);
using var asm=AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("ClearFixture",new Version(1,0)), "ClearFixture",
    new ModuleParameters{Kind=ModuleKind.Dll,AssemblyResolver=resolver,Runtime=TargetRuntime.Net_4_0});
var mod=asm.MainModule;
var i32=mod.ImportReference(typeof(int));var vd=mod.ImportReference(typeof(void));var obj=mod.ImportReference(typeof(object));
var open=mod.ImportReference(typeof(List<>));var gp=open.GenericParameters[0];
var host=new TypeDefinition("Fixture","Host",TypeAttributes.Public|TypeAttributes.Abstract|TypeAttributes.Sealed,obj);mod.Types.Add(host);
var holder=new TypeDefinition("Fixture","Holder",TypeAttributes.Public|TypeAttributes.Class,obj);mod.Types.Add(holder);
var valField=new FieldDefinition("Value",FieldAttributes.Public,i32);holder.Fields.Add(valField);
var hc=new MethodDefinition(".ctor",MethodAttributes.Public|MethodAttributes.HideBySig|MethodAttributes.SpecialName|MethodAttributes.RTSpecialName,vd);
holder.Methods.Add(hc);hc.Body=new MethodBody(hc);
hc.Body.GetILProcessor().Emit(OpCodes.Ldarg_0);hc.Body.GetILProcessor().Emit(OpCodes.Call,mod.ImportReference(typeof(object).GetConstructor(Type.EmptyTypes)!));hc.Body.GetILProcessor().Emit(OpCodes.Ret);
var counter=new FieldDefinition("FinallyCount",FieldAttributes.Public|FieldAttributes.Static,i32);host.Fields.Add(counter);
MethodDefinition Fixture(string name,TypeReference element,bool schedule=false,bool refs=false)
{
    var lt=new GenericInstanceType(open);lt.GenericArguments.Add(element);
    var version=new FieldReference("_version",i32,lt);var size=new FieldReference("_size",i32,lt);
    var items=new FieldReference("_items",new ArrayType(gp),lt);
    var getCount=new MethodReference("get_Count",i32,lt){HasThis=true};
    var clearArray=mod.ImportReference(typeof(Array).GetMethod("Clear",new[]{typeof(Array),typeof(int),typeof(int)})!);
    var m=new MethodDefinition(name,MethodAttributes.Public|MethodAttributes.Static,vd);host.Methods.Add(m);
    m.Parameters.Add(new ParameterDefinition(lt));if(schedule)m.Parameters.Add(new ParameterDefinition(holder));
    m.Body=new MethodBody(m){InitLocals=true};var il=m.Body.GetILProcessor();
    VariableDefinition L(TypeReference t){var v=new VariableDefinition(t);m.Body.Variables.Add(v);return v;}
    var list=L(lt);var old=L(i32);var count=L(i32);var destination=L(i32);
    il.Emit(OpCodes.Ldarg,m.Parameters[0]);il.Emit(OpCodes.Stloc,list);
    var entry=Instruction.Create(OpCodes.Nop);il.Append(entry);
    if(refs){il.Emit(OpCodes.Ldloc,list);il.Emit(OpCodes.Callvirt,getCount);il.Emit(OpCodes.Stloc,count);}
    il.Emit(OpCodes.Ldloc,list);il.Emit(OpCodes.Ldfld,version);il.Emit(OpCodes.Stloc,old);
    if(schedule){il.Emit(OpCodes.Ldarg,m.Parameters[1]);il.Emit(OpCodes.Ldfld,valField);il.Emit(OpCodes.Stloc,destination);}
    il.Emit(OpCodes.Ldloc,list);il.Emit(OpCodes.Ldc_I4,0);il.Emit(OpCodes.Stfld,size);
    il.Emit(OpCodes.Ldloc,list);il.Emit(OpCodes.Ldloc,old);il.Emit(OpCodes.Ldc_I4,1);il.Emit(OpCodes.Add);il.Emit(OpCodes.Stfld,version);
    if(!refs){il.Emit(OpCodes.Ret);return m;}
    var join=Instruction.Create(OpCodes.Nop);var nonempty=Instruction.Create(OpCodes.Nop);
    il.Emit(OpCodes.Ldloc,count);il.Emit(OpCodes.Ldc_I4,1);il.Emit(OpCodes.Clt);il.Emit(OpCodes.Brfalse,nonempty);
    il.Emit(OpCodes.Leave,join);il.Append(nonempty);il.Emit(OpCodes.Nop);
    il.Emit(OpCodes.Ldloc,list);il.Emit(OpCodes.Ldfld,items);il.Emit(OpCodes.Ldc_I4,0);il.Emit(OpCodes.Ldloc,count);il.Emit(OpCodes.Call,clearArray);il.Emit(OpCodes.Leave,join);
    var handler=Instruction.Create(OpCodes.Ldsfld,counter);il.Append(handler);il.Emit(OpCodes.Ldc_I4_1);il.Emit(OpCodes.Add);il.Emit(OpCodes.Stsfld,counter);il.Emit(OpCodes.Endfinally);
    il.Append(join);il.Emit(OpCodes.Ret);
    m.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Finally){TryStart=entry,TryEnd=handler,HandlerStart=handler,HandlerEnd=join});
    return m;
}
var f1=Fixture("IntClear",i32);var f2=Fixture("VectorClear",mod.ImportReference(typeof(Vector2)),true);var f3=Fixture("RefClear",obj,false,true);
foreach(var m in new[]{f1,f2,f3}){
    Check(ListClearIlFolding.Run(m.Body)==1,"positive "+m.Name);
    Check(m.Body.Instructions.Count(i=>i.Operand is MethodReference r&&r.Name=="Clear"&&r.DeclaringType is GenericInstanceType)==1,"exact Clear "+m.Name);
    Check(!m.Body.Instructions.Any(i=>i.Operand is FieldReference f&&f.Name is "_items" or "_size" or "_version"),"private removed");
    m.Body.OptimizeMacros();
}
static string Shape(MethodDefinition m)=>string.Join("\n",m.Body.Instructions.Select(i=>i.OpCode.Code+":"+i.Operand));
var badRef=Fixture("BadRef",obj);
var badStep=Fixture("BadStep",i32);
badStep.Body.Instructions.First(i=>i.OpCode.Code==Code.Ldc_I4&&Equals(i.Operand,1)).Operand=2;
var badSize=Fixture("BadSize",i32);badSize.Body.Instructions.First(i=>i.OpCode.Code==Code.Ldc_I4&&Equals(i.Operand,0)).Operand=1;
var badOld=Fixture("BadOld",i32);
var oldLoad=badOld.Body.Instructions.Last(i=>i.OpCode.Code==Code.Ldloc&&i.Operand==badOld.Body.Variables[1]);
oldLoad.Operand=badOld.Body.Variables[2];
var badEntry=Fixture("BadEntry",i32);badEntry.Body.GetILProcessor().InsertBefore(badEntry.Body.Instructions[0],Instruction.Create(OpCodes.Br,badEntry.Body.Instructions.First(i=>i.OpCode.Code==Code.Ldfld)));
var badCount=Fixture("BadCount",obj,false,true);
var oldCountRead=badCount.Body.Instructions.First(i=>i.Operand is MethodReference r&&r.Name=="get_Count");oldCountRead.OpCode=OpCodes.Nop;oldCountRead.Operand=null;
var badJoin=Fixture("BadJoin",obj,false,true);badJoin.Body.Instructions.Last(i=>i.OpCode.Code==Code.Leave).Operand=badJoin.Body.Instructions.Last();
var badRefsStruct=Fixture("BadRefsStruct",mod.ImportReference(typeof(KeyValuePair<int,object>)));
foreach(var m in new[]{badRef,badStep,badSize,badOld,badEntry,badCount,badJoin,badRefsStruct}){
    var before=Shape(m);Check(ListClearIlFolding.Run(m.Body)==0&&Shape(m)==before,"negative "+m.Name);host.Methods.Remove(m);
}
using var memory=new MemoryStream();asm.Write(memory);
var loaded=Assembly.Load(memory.ToArray());var runtime=loaded.GetType("Fixture.Host")!;
var intClear=runtime.GetMethod("IntClear")!.CreateDelegate<Action<List<int>>>();
var vectorClear=runtime.GetMethod("VectorClear")!;var h=Activator.CreateInstance(loaded.GetType("Fixture.Holder")!)!;
var refClear=runtime.GetMethod("RefClear")!.CreateDelegate<Action<List<object>>>();
var finallyCount=runtime.GetField("FinallyCount")!;int runs=0,protectedCalls=0;
foreach(int cap in new[]{0,1,128})
for(int n=0;n<64;n++){
    var ints=new List<int>(cap);var vectors=new List<Vector2>(cap);var refs=new List<object>(cap);
    for(int j=0;j<n;j++){ints.Add(j);vectors.Add(new Vector2(j,-j));refs.Add(new object());}
    var ien=ints.GetEnumerator();var ven=vectors.GetEnumerator();var ren=refs.GetEnumerator();
    int ic=ints.Capacity,vc=vectors.Capacity,rc=refs.Capacity;
    intClear(ints);vectorClear.Invoke(null,[vectors,h]);refClear(refs);runs+=3;protectedCalls++;
    Check(ints.Count==0&&vectors.Count==0&&refs.Count==0,"clear count");
    Check(ints.Capacity==ic&&vectors.Capacity==vc&&refs.Capacity==rc,"capacity preserved");
    Check(((object[])typeof(List<object>).GetField("_items",BindingFlags.Instance|BindingFlags.NonPublic)!.GetValue(refs)!).All(x=>x==null),"reference release");
    bool a=false,b=false,c=false;
    try{ien.MoveNext();}catch(InvalidOperationException){a=true;}
    try{ven.MoveNext();}catch(InvalidOperationException){b=true;}
    try{ren.MoveNext();}catch(InvalidOperationException){c=true;}
    Check(a&&b&&c,"enumerator version invalidation");
    Check((int)finallyCount.GetValue(null)! == protectedCalls,"finally count");
}
try{intClear(null!);throw new Exception("lost null");}catch(NullReferenceException){}
var remaining=new List<Vector2>{new(1,2)};var en=remaining.GetEnumerator();
try{vectorClear.Invoke(null,[remaining,null]);throw new Exception("lost scheduled exception");}catch(TargetInvocationException x)when(x.InnerException is NullReferenceException){}
Check(remaining.Count==1&&en.MoveNext(),"scheduled field exception changed version");
try{refClear(null!);throw new Exception("lost protected null");}catch(NullReferenceException){}
Check((int)finallyCount.GetValue(null)! == protectedCalls+1,"protected null finally");
Console.WriteLine($"LIST_CLEAR_IL_SMOKE_PASS runtime_operations={runs} negative=8 null_cases=3 protected_calls={protectedCalls+1}");
