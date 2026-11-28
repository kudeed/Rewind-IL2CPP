using Mono.Cecil;
using Mono.Cecil.Cil;
using Mono.Cecil.Rocks;
using Rewind.Output;
using System.Reflection;
using Assembly = System.Reflection.Assembly;
using TypeAttributes = Mono.Cecil.TypeAttributes;
using MethodAttributes = Mono.Cecil.MethodAttributes;
using FieldAttributes = Mono.Cecil.FieldAttributes;
using MethodBody = Mono.Cecil.Cil.MethodBody;
static void Check(bool pass,string why){if(!pass)throw new Exception(why);}
using var resolver = new DefaultAssemblyResolver();
resolver.AddSearchDirectory(Path.GetDirectoryName(typeof(List<>).Assembly.Location)!);
using var asm = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("ListAppendFixture",new Version(1,0)), "ListAppendFixture",
    new ModuleParameters{Kind=ModuleKind.Dll,AssemblyResolver=resolver,Runtime=TargetRuntime.Net_4_0});
var mod=asm.MainModule;
var i32=mod.ImportReference(typeof(int));var vd=mod.ImportReference(typeof(void));var obj=mod.ImportReference(typeof(object));
var open=mod.ImportReference(typeof(List<>));
var lt=new GenericInstanceType(open);lt.GenericArguments.Add(i32);
var gp=open.GenericParameters[0];
var itemField=new FieldReference("_items",new ArrayType(gp),lt);
var versionField=new FieldReference("_version",i32,lt);
var sizeField=new FieldReference("_size",i32,lt);
var get=new MethodReference("get_Count",i32,lt){HasThis=true};
var resize=new MethodReference("AddWithResize",vd,lt){HasThis=true};
resize.Parameters.Add(new ParameterDefinition(gp));
var host=new TypeDefinition("Fixture","AppendHost",TypeAttributes.Public|TypeAttributes.Abstract|TypeAttributes.Sealed,obj);mod.Types.Add(host);
var holder=new TypeDefinition("Fixture","Holder",TypeAttributes.Public|TypeAttributes.Class,obj);mod.Types.Add(holder);
var valField=new FieldDefinition("Value",FieldAttributes.Public,i32);holder.Fields.Add(valField);
var hc=new MethodDefinition(".ctor",MethodAttributes.Public|MethodAttributes.HideBySig|MethodAttributes.SpecialName|MethodAttributes.RTSpecialName,vd);
holder.Methods.Add(hc);hc.Body=new MethodBody(hc);
hc.Body.GetILProcessor().Emit(OpCodes.Ldarg_0);hc.Body.GetILProcessor().Emit(OpCodes.Call,mod.ImportReference(typeof(object).GetConstructor(Type.EmptyTypes)!));hc.Body.GetILProcessor().Emit(OpCodes.Ret);

(MethodDefinition M,Instruction[] Region,Instruction Slow,Instruction Join,VariableDefinition Array,VariableDefinition Value) Fixture(string name,bool scheduled,bool separateSlow=false)
{
    var m=new MethodDefinition(name,MethodAttributes.Public|MethodAttributes.Static,vd);
    host.Methods.Add(m);
    m.Parameters.Add(new ParameterDefinition(lt));m.Parameters.Add(new ParameterDefinition(scheduled?holder:i32));
    m.Body=new MethodBody(m){InitLocals=true};
    var il=m.Body.GetILProcessor();
    VariableDefinition Local(TypeReference t){var l=new VariableDefinition(t);m.Body.Variables.Add(l);return l;}
    var list=Local(lt);var array=Local(new ArrayType(i32));var size=Local(i32);var value=Local(i32);var source=Local(holder);
    il.Emit(OpCodes.Ldarg_0);il.Emit(OpCodes.Stloc,list);
    il.Emit(OpCodes.Ldarg_1);il.Emit(OpCodes.Stloc,scheduled?source:value);
    var region=new List<Instruction>();
    void E(Instruction ins){il.Append(ins);region.Add(ins);}
    void V(OpCode op,VariableDefinition x)=>E(Instruction.Create(op,x));
    void F(OpCode op,FieldReference x)=>E(Instruction.Create(op,x));
    void C(OpCode op,MethodReference x)=>E(Instruction.Create(op,x));
    void O(OpCode op)=>E(Instruction.Create(op));
    var slow=Instruction.Create(OpCodes.Nop);var join=Instruction.Create(OpCodes.Nop);
    V(OpCodes.Ldloc,list);F(OpCodes.Ldfld,itemField);V(OpCodes.Stloc,array);
    if(scheduled){V(OpCodes.Ldloc,source);F(OpCodes.Ldfld,valField);V(OpCodes.Stloc,value);}
    V(OpCodes.Ldloc,list);V(OpCodes.Ldloc,list);F(OpCodes.Ldfld,versionField);E(Instruction.Create(OpCodes.Ldc_I4,1));O(OpCodes.Add);F(OpCodes.Stfld,versionField);
    V(OpCodes.Ldloc,list);C(OpCodes.Callvirt,get);V(OpCodes.Stloc,size);
    V(OpCodes.Ldloc,array);O(OpCodes.Ldlen);O(OpCodes.Conv_I4);V(OpCodes.Ldloc,size);O(OpCodes.Cgt_Un);E(Instruction.Create(OpCodes.Ldc_I4,0));O(OpCodes.Ceq);E(Instruction.Create(OpCodes.Brtrue,slow));
    O(OpCodes.Nop);V(OpCodes.Ldloc,list);V(OpCodes.Ldloc,size);E(Instruction.Create(OpCodes.Ldc_I4,1));O(OpCodes.Add);F(OpCodes.Stfld,sizeField);
    V(OpCodes.Ldloc,array);V(OpCodes.Ldloc,size);V(OpCodes.Ldloc,value);E(Instruction.Create(OpCodes.Stelem_Any,i32));E(Instruction.Create(OpCodes.Br,join));
    il.Append(slow);il.Emit(OpCodes.Ldloc,list);il.Emit(OpCodes.Ldloc,value);il.Emit(OpCodes.Callvirt,resize);
    if(separateSlow){il.Emit(OpCodes.Nop);il.Emit(OpCodes.Br,join);}
    il.Append(join);il.Emit(OpCodes.Ret);
    return(m,region.ToArray(),slow,join,array,value);
}
static string Shape(MethodBody b)=>string.Join("\n",b.Instructions.Select(i=>i.OpCode.Code+":"+i.Operand));
var finallyCount=new FieldDefinition("FinallyCount",FieldAttributes.Public|FieldAttributes.Static,i32);
host.Fields.Add(finallyCount);
void Protect(MethodDefinition m,Instruction start)
{
    var il=m.Body.GetILProcessor();var epilogue=Instruction.Create(OpCodes.Ret);
    var exit=m.Body.Instructions.Last();
    exit.OpCode=OpCodes.Leave;exit.Operand=epilogue;
    var handler=Instruction.Create(OpCodes.Ldsfld,finallyCount);
    il.Append(handler);il.Emit(OpCodes.Ldc_I4_1);il.Emit(OpCodes.Add);il.Emit(OpCodes.Stsfld,finallyCount);il.Emit(OpCodes.Endfinally);il.Append(epilogue);
    m.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Finally){TryStart=start,TryEnd=handler,HandlerStart=handler,HandlerEnd=epilogue});
}
var canonical=Fixture("Canonical",false);var scheduled=Fixture("Scheduled",true);
var separated=Fixture("Separated",false,true);
var protectedAppend=Fixture("Protected",false,true);
Protect(protectedAppend.M,protectedAppend.M.Body.Instructions.First());
foreach(var f in new[]{canonical,scheduled,separated,protectedAppend}){
    Check(ListAppendIlFolding.Run(f.M.Body)==1,"complete native capacity diamond "+f.M.Name);
    Check(f.M.Body.Instructions.Count(i=>i.Operand is MethodReference r&&r.Name=="Add")==1,"public Add emitted");
    Check(!f.M.Body.Instructions.Any(i=>i.Operand is FieldReference r&&r.Name is "_items" or "_size" or "_version"),"private fields removed");
    f.M.Body.OptimizeMacros();
}
var negatives=new Action<(MethodDefinition M,Instruction[] Region,Instruction Slow,Instruction Join,VariableDefinition Array,VariableDefinition Value)>[]
{
    f=>f.Region[6].Operand=2,
    f=>f.Region[23].Operand=2,
    f=>f.Region[19].Operand=f.Join,
    f=>f.Region[28].Operand=f.Array,
    f=>f.M.Body.GetILProcessor().InsertBefore(f.M.Body.Instructions[0],Instruction.Create(OpCodes.Br,f.Slow)),
    f=>f.M.Body.GetILProcessor().InsertAfter(f.Join,Instruction.Create(OpCodes.Ldloc,f.Array)),
    f=>f.M.Body.GetILProcessor().InsertBefore(f.M.Body.Instructions[0],Instruction.Create(OpCodes.Ldloca,f.Value)),
    f=>f.Region[16].OpCode=OpCodes.Clt_Un,
};
for(int n=0;n<negatives.Length;n++){
    var f=Fixture("Negative"+n,false);negatives[n](f);var before=Shape(f.M.Body);
    Check(ListAppendIlFolding.Run(f.M.Body)==0,"unsafe mutated pattern "+n);
    Check(Shape(f.M.Body)==before,"rejected body mutated "+n);
    host.Methods.Remove(f.M);
}
var badScheduled=Fixture("BadScheduled",true);
badScheduled.Region[5].Operand=badScheduled.Array;
var badShape=Shape(badScheduled.M.Body);
Check(ListAppendIlFolding.Run(badScheduled.M.Body)==0&&Shape(badScheduled.M.Body)==badShape,"wrong scheduled destination");
host.Methods.Remove(badScheduled.M);
var badBoundary=Fixture("BadBoundary",false,true);
Protect(badBoundary.M,badBoundary.Region[5]);
var boundaryShape=Shape(badBoundary.M.Body);
Check(ListAppendIlFolding.Run(badBoundary.M.Body)==0&&Shape(badBoundary.M.Body)==boundaryShape,"EH boundary moved");
host.Methods.Remove(badBoundary.M);
var badLeave=Fixture("BadLeave",false,true);
badLeave.Slow.Next.Next.Next.Next.Next.OpCode=OpCodes.Leave;
var leaveShape=Shape(badLeave.M.Body);
Check(ListAppendIlFolding.Run(badLeave.M.Body)==0&&Shape(badLeave.M.Body)==leaveShape,"leave accepted as ordinary branch");
host.Methods.Remove(badLeave.M);
using var memory=new MemoryStream();asm.Write(memory);
var assembly=Assembly.Load(memory.ToArray());
var runtimeHost=assembly.GetType("Fixture.AppendHost")!;
var runtimeHolder=assembly.GetType("Fixture.Holder")!;
var append=(Action<List<int>,int>)runtimeHost.GetMethod("Canonical")!.CreateDelegate(typeof(Action<List<int>,int>));
var scheduledCall=runtimeHost.GetMethod("Scheduled")!;
var h=Activator.CreateInstance(runtimeHolder)!;runtimeHolder.GetField("Value")!.SetValue(h,123);
int runs=0;
foreach(int capacity in new[]{0,1,128}){
    var list=new List<int>(capacity);var expected=new List<int>(capacity);
    for(int k=0;k<65;k++){
        var en=list.GetEnumerator();append(list,k);expected.Add(k);runs++;
        try{en.MoveNext();throw new Exception("List version not incremented");}catch(InvalidOperationException){}
        Check(list.SequenceEqual(expected)&&list.Capacity==expected.Capacity,"canonical semantics");
        scheduledCall.Invoke(null,[list,h]);expected.Add(123);runs++;
        Check(list.SequenceEqual(expected)&&list.Capacity==expected.Capacity,"scheduled semantics");
    }
}
try{append(null!,1);throw new Exception("lost list null check");}catch(NullReferenceException){}
var unaffected=new List<int>{1};var originalEnum=unaffected.GetEnumerator();
try{scheduledCall.Invoke(null,[unaffected,null]);throw new Exception("lost field null check");}
catch(TargetInvocationException ex)when(ex.InnerException is NullReferenceException){}
Check(unaffected.Count==1&&originalEnum.MoveNext(),"field exception mutated list or version");
var separatedCall=(Action<List<int>,int>)runtimeHost.GetMethod("Separated")!.CreateDelegate(typeof(Action<List<int>,int>));
var protectedCall=(Action<List<int>,int>)runtimeHost.GetMethod("Protected")!.CreateDelegate(typeof(Action<List<int>,int>));
var counter=runtimeHost.GetField("FinallyCount")!;
int protectedRuns=0;
foreach(int capacity in new[]{0,1,128}){
    var list=new List<int>(capacity);var expected=new List<int>(capacity);
    for(int k=0;k<65;k++){
        separatedCall(list,k);expected.Add(k);runs++;
        var en=list.GetEnumerator();
        protectedCall(list,-k);expected.Add(-k);runs++;protectedRuns++;
        bool invalidated=false;try{en.MoveNext();}catch(InvalidOperationException){invalidated=true;}
        Check(invalidated&&list.SequenceEqual(expected)&&list.Capacity==expected.Capacity,"protected append semantics");
        Check((int)counter.GetValue(null)! == protectedRuns,"finally must execute once");
    }
}
try{protectedCall(null!,1);throw new Exception("lost protected list null check");}catch(NullReferenceException){}
Check((int)counter.GetValue(null)! == protectedRuns+1,"finally must execute after null failure");
Console.WriteLine($"LIST_APPEND_IL_FOLDING_SMOKE_PASS runtime_operations={runs} negative_patterns={negatives.Length+3} null_cases=3 protected_calls={protectedRuns+1}");
