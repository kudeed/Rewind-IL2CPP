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
if(args.Length==2)
{
    using var corpusResolver=new DefaultAssemblyResolver();
    corpusResolver.AddSearchDirectory(Path.GetDirectoryName(Path.GetFullPath(args[0]))!);
    using var corpus=AssemblyDefinition.ReadAssembly(args[0],new ReaderParameters{AssemblyResolver=corpusResolver,InMemory=true});
    static IEnumerable<TypeDefinition> All(IEnumerable<TypeDefinition> t)=>t.SelectMany(x=>new[]{x}.Concat(All(x.NestedTypes)));
    int sites=0,methods=0;
    foreach(var m in All(corpus.MainModule.Types).SelectMany(t=>t.Methods).Where(m=>m.HasBody))
    {
        int n=ListAppendIlFolding.Run(m.Body);
        if(n==0)continue;
        m.Body.OptimizeMacros();sites+=n;methods++;
        Console.WriteLine($"{m.MetadataToken.ToUInt32():X8} {n} {m.FullName}");
    }
    corpus.Write(args[1]);
    Console.WriteLine(System.Text.Json.JsonSerializer.Serialize(new{folded_sites=sites,changed_methods=methods}));
    return;
}
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
// Receiver and item can be stable method arguments rather than locals.
var directArgs=Fixture("DirectArguments",false,true);
foreach(var i in directArgs.M.Body.Instructions)
{
    if(i.OpCode.Code==Code.Ldloc && i.Operand==directArgs.Value)
    {i.OpCode=OpCodes.Ldarg;i.Operand=directArgs.M.Parameters[1];}
    else if(i.OpCode.Code==Code.Ldloc && i.Operand==directArgs.Region[0].Operand)
    { /* Receiver loads are replaced below, after saving the original operand. */ }
}
var listLocal=directArgs.Region[0].Operand;
foreach(var i in directArgs.M.Body.Instructions.Where(i=>i.OpCode.Code==Code.Ldloc&&i.Operand==listLocal))
{i.OpCode=OpCodes.Ldarg;i.Operand=directArgs.M.Parameters[0];}
Check(ListAppendIlFolding.Run(directArgs.M.Body)==1,"stable parameter receiver/item");
directArgs.M.Body.OptimizeMacros();

var argRead=Fixture("ScheduledArgumentRead",true);
argRead.Region[3].OpCode=OpCodes.Ldarg;
argRead.Region[3].Operand=argRead.M.Parameters[1];
Check(ListAppendIlFolding.Run(argRead.M.Body)==1,"scheduled argument field read");
argRead.M.Body.OptimizeMacros();
var badArgRead=Fixture("BadScheduledArgumentRead",true);
badArgRead.Region[3].OpCode=OpCodes.Ldarg;
badArgRead.Region[3].Operand=badArgRead.M.Parameters[0];
var badArgShape=Shape(badArgRead.M.Body);
Check(ListAppendIlFolding.Run(badArgRead.M.Body)==0&&Shape(badArgRead.M.Body)==badArgShape,"wrong scheduled receiver");
host.Methods.Remove(badArgRead.M);

var invalidArgument=Fixture("InvalidArgument",false);
invalidArgument.Region[28].OpCode=OpCodes.Ldarg;invalidArgument.Region[28].Operand=invalidArgument.M.Parameters[1];
var invalidShape=Shape(invalidArgument.M.Body);
Check(ListAppendIlFolding.Run(invalidArgument.M.Body)==0&&Shape(invalidArgument.M.Body)==invalidShape,"different fast/slow value loads");
host.Methods.Remove(invalidArgument.M);
// Real scalar schedule and covariant reference storage (List<object>
// receives string without a box). Construct the exact emitted IL pattern.
MethodDefinition ScalarFixture(string name,TypeReference element,TypeReference input,bool arithmetic)
{
    var listType=new GenericInstanceType(open);listType.GenericArguments.Add(element);
    var items=new FieldReference("_items",new ArrayType(gp),listType);
    var ver=new FieldReference("_version",i32,listType);
    var sz=new FieldReference("_size",i32,listType);
    var count=new MethodReference("get_Count",i32,listType){HasThis=true};
    var slowAdd=new MethodReference("AddWithResize",vd,listType){HasThis=true};
    slowAdd.Parameters.Add(new ParameterDefinition(gp));
    var m=new MethodDefinition(name,MethodAttributes.Public|MethodAttributes.Static,vd);host.Methods.Add(m);
    m.Parameters.Add(new ParameterDefinition(listType));m.Parameters.Add(new ParameterDefinition(input));
    if(arithmetic){m.Parameters.Add(new ParameterDefinition(input));m.Parameters.Add(new ParameterDefinition(input));}
    m.Body=new MethodBody(m){InitLocals=true};
    var il=m.Body.GetILProcessor();
    VariableDefinition Local(TypeReference t){var v=new VariableDefinition(t);m.Body.Variables.Add(v);return v;}
    var list=Local(listType);var array=Local(new ArrayType(element));var size=Local(i32);
    var left=Local(input);var right=Local(input);var factor=Local(input);var value=Local(input);
    il.Emit(OpCodes.Ldarg,m.Parameters[0]);il.Emit(OpCodes.Stloc,list);
    il.Emit(OpCodes.Ldarg,m.Parameters[1]);il.Emit(OpCodes.Stloc,left);
    if(arithmetic)
    {
        il.Emit(OpCodes.Ldarg,m.Parameters[2]);il.Emit(OpCodes.Stloc,right);
        il.Emit(OpCodes.Ldarg,m.Parameters[3]);il.Emit(OpCodes.Stloc,factor);
    }
    else{il.Emit(OpCodes.Ldloc,left);il.Emit(OpCodes.Stloc,value);}
    il.Emit(OpCodes.Ldloc,list);il.Emit(OpCodes.Ldfld,items);il.Emit(OpCodes.Stloc,array);
    il.Emit(OpCodes.Ldloc,list);il.Emit(OpCodes.Ldloc,list);il.Emit(OpCodes.Ldfld,ver);
    il.Emit(OpCodes.Ldc_I4,1);il.Emit(OpCodes.Add);il.Emit(OpCodes.Stfld,ver);
    il.Emit(OpCodes.Ldloc,list);il.Emit(OpCodes.Callvirt,count);il.Emit(OpCodes.Stloc,size);
    if(arithmetic)
    {
        il.Emit(OpCodes.Ldloc,left);il.Emit(OpCodes.Ldloc,right);il.Emit(OpCodes.Sub);il.Emit(OpCodes.Conv_R4);
        il.Emit(OpCodes.Ldloc,factor);il.Emit(OpCodes.Mul);il.Emit(OpCodes.Conv_R4);il.Emit(OpCodes.Stloc,value);
    }
    var slow=Instruction.Create(OpCodes.Nop);var join=Instruction.Create(OpCodes.Nop);
    il.Emit(OpCodes.Ldloc,array);il.Emit(OpCodes.Ldlen);il.Emit(OpCodes.Conv_I4);il.Emit(OpCodes.Ldloc,size);
    il.Emit(OpCodes.Cgt_Un);il.Emit(OpCodes.Ldc_I4,0);il.Emit(OpCodes.Ceq);il.Emit(OpCodes.Brtrue,slow);
    il.Emit(OpCodes.Nop);il.Emit(OpCodes.Ldloc,list);il.Emit(OpCodes.Ldloc,size);il.Emit(OpCodes.Ldc_I4,1);
    il.Emit(OpCodes.Add);il.Emit(OpCodes.Stfld,sz);
    il.Emit(OpCodes.Ldloc,array);il.Emit(OpCodes.Ldloc,size);il.Emit(OpCodes.Ldloc,value);
    il.Emit(OpCodes.Stelem_Any,element);il.Emit(OpCodes.Br,join);
    il.Append(slow);il.Emit(OpCodes.Ldloc,list);il.Emit(OpCodes.Ldloc,value);il.Emit(OpCodes.Callvirt,slowAdd);
    il.Append(join);il.Emit(OpCodes.Ret);
    return m;
}
var fp=mod.ImportReference(typeof(float));
var scheduledFp=ScalarFixture("ScheduledFloat",fp,fp,true);
var objectAppend=ScalarFixture("ObjectAppend",obj,mod.ImportReference(typeof(string)),false);
foreach(var m in new[]{scheduledFp,objectAppend})
{
    Check(ListAppendIlFolding.Run(m.Body)==1,"extended scalar/reference "+m.Name);
    m.Body.OptimizeMacros();
}
var badBox=ScalarFixture("BadBox",obj,i32,false);
var badBoxShape=Shape(badBox.Body);
Check(ListAppendIlFolding.Run(badBox.Body)==0&&Shape(badBox.Body)==badBoxShape,"reject unboxed value type");
host.Methods.Remove(badBox);
var badFp=ScalarFixture("BadFloatSchedule",fp,fp,true);
badFp.Body.Instructions.First(x=>x.OpCode.Code==Code.Mul).OpCode=OpCodes.Div;
var badFpShape=Shape(badFp.Body);
Check(ListAppendIlFolding.Run(badFp.Body)==0&&Shape(badFp.Body)==badFpShape,"reject unproven scheduled op");
host.Methods.Remove(badFp);
// Test branch-local default construction without merging temporary writes.
// The slow-copy local is observable after the join, so collapsing both
// arms to one assignment would change the result.
var defaultBranch=Fixture("DefaultBranch",false);
var bm=defaultBranch.M;var bi=bm.Body.GetILProcessor();
var fastTmp=new VariableDefinition(i32);var slowTmp=new VariableDefinition(i32);
bm.Body.Variables.Add(fastTmp);bm.Body.Variables.Add(slowTmp);
var observable=new FieldDefinition("BranchLocal",FieldAttributes.Public|FieldAttributes.Static,i32);host.Fields.Add(observable);
var val=defaultBranch.Value;
var fl=defaultBranch.Region[28];
bi.InsertBefore(fl,Instruction.Create(OpCodes.Ldloca,fastTmp));
bi.InsertBefore(fl,Instruction.Create(OpCodes.Initobj,i32));fl.Operand=fastTmp;
var sl=defaultBranch.Slow.Next; // before slow receiver
bi.InsertBefore(sl,Instruction.Create(OpCodes.Ldloca,slowTmp));
bi.InsertBefore(sl,Instruction.Create(OpCodes.Initobj,i32));
bi.InsertBefore(sl,Instruction.Create(OpCodes.Ldloc,slowTmp));
bi.InsertBefore(sl,Instruction.Create(OpCodes.Stloc,val));
bi.InsertAfter(defaultBranch.Join,Instruction.Create(OpCodes.Stsfld,observable));
bi.InsertAfter(defaultBranch.Join,Instruction.Create(OpCodes.Ldloc,val));
Check(ListAppendIlFolding.Run(bm.Body)==1,"branch-local default shape");
Check(bm.Body.Instructions.Count(i=>i.Operand is MethodReference r&&r.Name=="Add")==2,"both original arms kept");
bm.Body.OptimizeMacros();

// A scheduled array value read must retain its bounds/null exceptions
// before changing the list version. A pure continuation remains unchanged.
var arrayRead=Fixture("ArrayReadSchedule",false);
var am=arrayRead.M;var ai=am.Body.GetILProcessor();var ap=new ParameterDefinition(new ArrayType(i32));am.Parameters.Add(ap);
var beforeVersion=arrayRead.Region[3];
foreach(var i in new[]{Instruction.Create(OpCodes.Ldarg,ap),Instruction.Create(OpCodes.Ldarg,am.Parameters[1]),
    Instruction.Create(OpCodes.Ldelem_Any,i32),Instruction.Create(OpCodes.Stloc,arrayRead.Value)})ai.InsertBefore(beforeVersion,i);
Check(ListAppendIlFolding.Run(am.Body)==1,"array schedule branch proof");
am.Body.OptimizeMacros();

var badScheduledBranch=Fixture("BadScheduledBranch",false);
var badIl=badScheduledBranch.M.Body.GetILProcessor();
badIl.InsertBefore(badScheduledBranch.Region[3],Instruction.Create(OpCodes.Ldarg,badScheduledBranch.M.Parameters[0]));
badIl.InsertBefore(badScheduledBranch.Region[3],Instruction.Create(OpCodes.Callvirt,resize));
badIl.InsertBefore(badScheduledBranch.Region[3],Instruction.Create(OpCodes.Stloc,badScheduledBranch.Value));
var badScheduledBranchShape=Shape(badScheduledBranch.M.Body);
Check(ListAppendIlFolding.Run(badScheduledBranch.M.Body)==0&&Shape(badScheduledBranch.M.Body)==badScheduledBranchShape,
    "reject scheduled unproven mutating call");
host.Methods.Remove(badScheduledBranch.M);
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
var direct=(Action<List<int>,int>)runtimeHost.GetMethod("DirectArguments")!.CreateDelegate(typeof(Action<List<int>,int>));
var argField=runtimeHost.GetMethod("ScheduledArgumentRead")!;
var extList=new List<int>(1);var extExpected=new List<int>(1);
for(int n=0;n<100;n++)
{
    direct(extList,n);extExpected.Add(n);
    argField.Invoke(null,[extList,h]);extExpected.Add(123);runs+=2;
    Check(extList.SequenceEqual(extExpected)&&extList.Capacity==extExpected.Capacity,"extended argument list semantics");
}
try{direct(null!,1);throw new Exception("lost direct receiver null check");}catch(NullReferenceException){}
var enumBefore=extList.GetEnumerator();
try{argField.Invoke(null,[extList,null]);throw new Exception("lost scheduled argument exception");}
catch(TargetInvocationException ex)when(ex.InnerException is NullReferenceException){}
Check(enumBefore.MoveNext()&&extList.SequenceEqual(extExpected),"pre-version scheduled field exception mutated list");
var appendFp=runtimeHost.GetMethod("ScheduledFloat")!.CreateDelegate<Action<List<float>,float,float,float>>();
var appendObject=runtimeHost.GetMethod("ObjectAppend")!.CreateDelegate<Action<List<object>,string>>();
foreach(int capacity in new[]{0,1,128})
{
    var list=new List<float>(capacity);var expected=new List<float>(capacity);
    var refs=new List<object>(capacity);var strings=new List<object>(capacity);
    for(int n=0;n<100;n++)
    {
        float a=n*.125f,b=n*.01f,c=n*.375f;
        appendFp(list,a,b,c);expected.Add((a-b)*c);
        var str=n%17==0?null!:n.ToString();appendObject(refs,str);strings.Add(str);
        runs+=2;
        Check(list.Select(BitConverter.SingleToInt32Bits).SequenceEqual(expected.Select(BitConverter.SingleToInt32Bits))
            &&list.Capacity==expected.Capacity,"bit-exact scheduled FP");
        Check(refs.SequenceEqual(strings)&&refs.Capacity==strings.Capacity,"reference value storage");
    }
}
try{appendFp(null!,1f,2f,3f);throw new Exception("lost scheduled FP null check");}catch(NullReferenceException){}
var appendDefault=runtimeHost.GetMethod("DefaultBranch")!.CreateDelegate<Action<List<int>,int>>();
var readArray=runtimeHost.GetMethod("ArrayReadSchedule")!.CreateDelegate<Action<List<int>,int,int[]>>();
var observed=runtimeHost.GetField("BranchLocal")!;
int branchRuns=0;
foreach(int capacity in new[]{0,1,128})
{
    var ints=new List<int>(capacity);var expected=new List<int>(capacity);
    for(int n=0;n<100;n++)
    {
        bool expands=ints.Count==ints.Capacity;
        appendDefault(ints,7);expected.Add(0);
        Check((int)observed.GetValue(null)! == (expands?0:7),"branch-local value changed");
        Check(ints.SequenceEqual(expected)&&ints.Capacity==expected.Capacity,"default branch append");
        readArray(ints,1,[10,20,30]);expected.Add(20);
        Check(ints.SequenceEqual(expected)&&ints.Capacity==expected.Capacity,"scheduled array append");
        runs+=2;branchRuns+=2;
    }
    var old=ints.GetEnumerator();
    try{readArray(ints,8,[1]);throw new Exception("missing array bounds check");}catch(IndexOutOfRangeException){}
    Check(old.MoveNext()&&ints.SequenceEqual(expected),"array exception changed list version");
}
try{readArray(null!,99,[1]);throw new Exception("missing receiver null check");}catch(NullReferenceException){}
Console.WriteLine($"BRANCH_PRESERVING_APPEND_SMOKE_PASS operations={branchRuns} negative=1 exception_order=4");
Console.WriteLine($"LIST_APPEND_IL_FOLDING_SMOKE_PASS runtime_operations={runs} negative_patterns={negatives.Length+7} null_cases=6 protected_calls={protectedRuns+1}");
