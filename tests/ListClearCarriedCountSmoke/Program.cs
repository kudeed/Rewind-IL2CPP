using System.Reflection;
using System.Numerics;
using Mono.Cecil;
using Mono.Cecil.Cil;
using Rewind.Output;
using TypeAttributes = Mono.Cecil.TypeAttributes;
using FieldAttributes = Mono.Cecil.FieldAttributes;
using MethodAttributes = Mono.Cecil.MethodAttributes;
using ParameterAttributes = Mono.Cecil.ParameterAttributes;

using var fixture = new ClearFixtures();
int positives=0, negatives=0, operations=0, exceptions=0;
string Shape(MethodDefinition method)=>string.Join("\n",method.Body.Instructions.Select(i=>i.OpCode.Code+":"+i.Operand));
void Good(MethodDefinition method)
{
    if(ListClearIlFolding.Run(method.Body)!=1)throw new Exception(method.Name+": no complete Clear recovery");
    if(method.Body.Instructions.Any(i=>i.Operand is FieldReference f&&f.DeclaringType.FullName.StartsWith("System.Collections.Generic.List",StringComparison.Ordinal)))
        throw new Exception(method.Name+": private List fields remain");
    if(ListClearIlFolding.Run(method.Body)!=0)throw new Exception(method.Name+": not idempotent");
    positives++;
}
void Bad(string name,bool loop,Action<ReferenceCase> change)
{
    var c=fixture.Reference(name,loop);change(c);string before=Shape(c.Method);int locals=c.Method.Body.Variables.Count;
    if(ListClearIlFolding.Run(c.Method.Body)!=0||Shape(c.Method)!=before||locals!=c.Method.Body.Variables.Count)
        throw new Exception(name+": unproved count changed");
    fixture.Host.Methods.Remove(c.Method);negatives++;
}
void BadValue(string name,Action<ValueCase> change)
{
    var c=fixture.Value(name);change(c);string before=Shape(c.Method);int locals=c.Method.Body.Variables.Count;
    if(ListClearIlFolding.Run(c.Method.Body)!=0||Shape(c.Method)!=before||locals!=c.Method.Body.Variables.Count)
        throw new Exception(name+": unproved schedule changed");
    fixture.Host.Methods.Remove(c.Method);negatives++;
}
Good(fixture.Reference("LoopCountClear",true).Method);
Good(fixture.Reference("PhiCountClear",false).Method);
Good(fixture.Value("ConditionalValueClear").Method);
Bad("InterveningCallback",false,c=>c.Method.Body.GetILProcessor().InsertBefore(c.Entry,Instruction.Create(OpCodes.Call,fixture.Observe)));
Bad("FreshAndStalePhi",false,c=>{c.CopyB!.OpCode=OpCodes.Ldc_I4;c.CopyB.Operand=0;});
Bad("WrongListCount",false,c=>{c.FirstCall.Previous!.OpCode=OpCodes.Ldarg;c.FirstCall.Previous.Operand=c.Method.Parameters[2];});
Bad("CountOverwritten",false,c=>
{
    var il=c.Method.Body.GetILProcessor();il.InsertBefore(c.Entry,Instruction.Create(OpCodes.Ldc_I4,0));il.InsertBefore(c.Entry,Instruction.Create(OpCodes.Stloc,c.Count));
});
Bad("ReceiverOverwritten",false,c=>
{
    var il=c.Method.Body.GetILProcessor();il.InsertBefore(c.Entry,Instruction.Create(OpCodes.Ldarg,c.Method.Parameters[2]));il.InsertBefore(c.Entry,Instruction.Create(OpCodes.Stloc,c.List));
});
Bad("CountAliasAddressEscapes",false,c=>c.Method.Body.GetILProcessor().InsertBefore(c.Join.Next!,Instruction.Create(OpCodes.Ldloca,c.First)));
Bad("ReceiverAddressEscapes",false,c=>c.Method.Body.GetILProcessor().InsertBefore(c.Join.Next!,Instruction.Create(OpCodes.Ldloca,c.List)));
Bad("ThirdEntryIntoCountStore",false,c=>
{
    var il=c.Method.Body.GetILProcessor();Instruction first=c.Method.Body.Instructions[0];
    il.InsertBefore(first,Instruction.Create(OpCodes.Ldc_I4,0));il.InsertBefore(first,Instruction.Create(OpCodes.Br,c.FirstStore));
});
Bad("CopyBackedgeWithoutFreshRead",false,c=>
{
    var il=c.Method.Body.GetILProcessor();var stale=Instruction.Create(OpCodes.Nop);il.Append(stale);
    il.Append(Instruction.Create(OpCodes.Ldloc,c.Count));il.Append(Instruction.Create(OpCodes.Stloc,c.First));
    il.Append(Instruction.Create(OpCodes.Br,c.CopyB!));
    il.InsertBefore(c.FirstCall.Previous!,Instruction.Create(OpCodes.Br,stale));
});
Bad("HandlerEntryBypassesCount",false,c=>c.Method.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
    {TryStart=c.Method.Body.Instructions[0],TryEnd=c.Entry,HandlerStart=c.Entry,HandlerEnd=c.Join,CatchType=fixture.Module.ImportReference(typeof(Exception))}));
Bad("MissingLoopRefresh",true,c=>{c.FirstCall.OpCode=OpCodes.Nop;c.FirstCall.Operand=null;});
Bad("StaleLoopExitCallback",true,c=>c.Method.Body.GetILProcessor().InsertBefore(c.Entry,Instruction.Create(OpCodes.Call,fixture.Observe)));
Bad("InteriorEntryPastVersionLoad",false,c=>c.Method.Body.GetILProcessor().InsertBefore(c.Method.Body.Instructions[0],Instruction.Create(OpCodes.Br,c.Entry.Next!)));
Bad("WrongArrayClearLength",false,c=>c.ArrayCall.Previous!.Operand=c.Second);
Bad("SkipBridgeSideEffect",false,c=>c.Method.Body.GetILProcessor().InsertAfter(c.Skip!,Instruction.Create(OpCodes.Call,fixture.Observe)));
Bad("GenericCountSpecification",false,c=>
{
    var generic=new GenericInstanceMethod((MethodReference)c.FirstCall.Operand);generic.GenericArguments.Add(fixture.Int);c.FirstCall.Operand=generic;
});
Bad("WrongProtectedLeave",true,c=>c.Method.Body.Instructions.Last(i=>i.OpCode.Code==Code.Leave).Operand=c.Method.Body.Instructions[^1]);
BadValue("DifferentClampConstant",c=>c.Schedule[8].Operand=3);
BadValue("WrongClampPhi",c=>c.Schedule[4].Operand=c.Schedule[9]);
BadValue("ClampReadsCapturedVersion",c=>{c.Schedule[2].OpCode=OpCodes.Ldloc;c.Schedule[2].Operand=c.Version;c.Schedule[5].OpCode=OpCodes.Ldloc;c.Schedule[5].Operand=c.Version;});
BadValue("ClampCallback",c=>c.Method.Body.GetILProcessor().InsertBefore(c.Schedule[10],Instruction.Create(OpCodes.Call,fixture.Observe)));
BadValue("OutsideClampEntry",c=>c.Method.Body.GetILProcessor().InsertBefore(c.Method.Body.Instructions[0],Instruction.Create(OpCodes.Br,c.Schedule[7])));

using var stream=new MemoryStream();fixture.Assembly.Write(stream);
var assembly=System.Reflection.Assembly.Load(stream.ToArray());Type host=assembly.GetType("Fixture.ClearHost",true)!,holderType=assembly.GetType("Fixture.Holder",true)!;
var version=typeof(List<object>).GetField("_version",BindingFlags.Instance|BindingFlags.NonPublic)!;
var vectorVersion=typeof(List<Vector2>).GetField("_version",BindingFlags.Instance|BindingFlags.NonPublic)!;
var finallyCount=host.GetField("FinallyCount")!;var stepsField=holderType.GetField("Steps")!;
foreach(string name in new[]{"LoopCountClear","PhiCountClear"})
{
    var clear=host.GetMethod(name)!.CreateDelegate<Action<List<object>?,bool,List<object>?,Action<List<object>>?>>();
    foreach(int capacity in new[]{0,1,16,64})
    foreach(int length in new[]{0,1,2,3,8,15})
    foreach(bool choose in new[]{false,true})
    {
        var actual=new List<object>(capacity);var expected=new List<object>(capacity);
        for(int n=0;n<length;n++){var item=new object();actual.Add(item);expected.Add(item);}
        if(length==3){version.SetValue(actual,int.MaxValue);version.SetValue(expected,int.MaxValue);}
        var old=actual.GetEnumerator();int beforeFinally=(int)finallyCount.GetValue(null)!;
        var actualTrace=new List<int>();var expectedTrace=new List<int>();
        void Mutate(List<object> list,List<int> trace){trace.Add(list.Count);if(list.Count>2)list.RemoveAt(list.Count-1);}
        clear(actual,choose,new List<object>{new object()},list=>Mutate(list,actualTrace));
        if(name=="LoopCountClear")
        {
            int index=0;while(expected.Count>index){Mutate(expected,expectedTrace);index++;}
            if((int)finallyCount.GetValue(null)! !=beforeFinally+1)throw new Exception("loop finally changed");
        }
        expected.Clear();
        if(actual.Count!=0||actual.Capacity!=expected.Capacity||(int)version.GetValue(actual)! != (int)version.GetValue(expected)! ||
            !actualTrace.SequenceEqual(expectedTrace))throw new Exception(name+": count/capacity/version/callback sequence changed");
        var backing=(object[])typeof(List<object>).GetField("_items",BindingFlags.Instance|BindingFlags.NonPublic)!.GetValue(actual)!;
        if(backing.Any(x=>x!=null))throw new Exception(name+": references retained");
        bool invalidated=false;try{old.MoveNext();}catch(InvalidOperationException){invalidated=true;}
        if(!invalidated)throw new Exception(name+": stale enumerator survived");
        operations++;
    }
    var sample=new List<object>{new object(),new object()};int previous=(int)version.GetValue(sample)!;var prior=sample.GetEnumerator();
    int startFinally=(int)finallyCount.GetValue(null)!;
    try
    {
        clear(sample,true,name=="PhiCountClear"?null:new List<object>(),null);
        throw new Exception("Expected original pre-Clear null exception");
    }
    catch(NullReferenceException){exceptions++;}
    if(sample.Count!=2||(int)version.GetValue(sample)! != previous||!prior.MoveNext())throw new Exception("pre-Clear failure changed list");
    if(name=="LoopCountClear"&&(int)finallyCount.GetValue(null)! !=startFinally+1)throw new Exception("callback failure lost finally");
    startFinally=(int)finallyCount.GetValue(null)!;
    try{clear(null,false,new List<object>(),_=>{});throw new Exception("Expected receiver null");}
    catch(NullReferenceException){exceptions++;}
    if(name=="LoopCountClear"&&(int)finallyCount.GetValue(null)! !=startFinally+1)throw new Exception("receiver failure lost finally");
}
MethodInfo conditional=host.GetMethod("ConditionalValueClear")!;
foreach(int capacity in new[]{0,1,16})
foreach(int length in new[]{0,1,8})
foreach(int value in new[]{int.MinValue,-1,2,3,int.MaxValue})
{
    var actual=new List<Vector2>(capacity);var expected=new List<Vector2>(capacity);
    for(int n=0;n<length;n++){actual.Add(new Vector2(n+.25f,-n));expected.Add(new Vector2(n+.25f,-n));}
    object holder=Activator.CreateInstance(holderType)!;stepsField.SetValue(holder,73);var old=actual.GetEnumerator();
    var backing=(Vector2[])typeof(List<Vector2>).GetField("_items",BindingFlags.Instance|BindingFlags.NonPublic)!.GetValue(actual)!;
    var bits=backing.Select(v=>(BitConverter.SingleToInt32Bits(v.X),BitConverter.SingleToInt32Bits(v.Y))).ToArray();
    conditional.Invoke(null,new object?[]{actual,holder,value});expected.Clear();
    if((int)stepsField.GetValue(holder)! != Math.Max(2,value)||actual.Count!=0||actual.Capacity!=expected.Capacity||
        (int)vectorVersion.GetValue(actual)! != (int)vectorVersion.GetValue(expected)!||
        !bits.SequenceEqual(backing.Select(v=>(BitConverter.SingleToInt32Bits(v.X),BitConverter.SingleToInt32Bits(v.Y)))))
        throw new Exception("conditional store/count/capacity/version/backing values changed");
    bool invalidated=false;try{old.MoveNext();}catch(InvalidOperationException){invalidated=true;}if(!invalidated)throw new Exception("conditional stale enumerator");
    operations++;
}
var intact=new List<Vector2>{new(4,5)};int originalVersion=(int)vectorVersion.GetValue(intact)!;var intactEnum=intact.GetEnumerator();
try{conditional.Invoke(null,new object?[]{intact,null,9});throw new Exception("Expected holder null");}
catch(TargetInvocationException e)when(e.InnerException is NullReferenceException){exceptions++;}
if(intact.Count!=1||(int)vectorVersion.GetValue(intact)! != originalVersion||!intactEnum.MoveNext())throw new Exception("field failure cleared list");
object untouched=Activator.CreateInstance(holderType)!;stepsField.SetValue(untouched,73);
try{conditional.Invoke(null,new object?[]{null,untouched,9});throw new Exception("Expected early list null");}
catch(TargetInvocationException e)when(e.InnerException is NullReferenceException){exceptions++;}
if((int)stepsField.GetValue(untouched)! != 73)throw new Exception("list null happened after field write");
Console.WriteLine($"LIST_CLEAR_CARRIED_SMOKE_PASS positive={positives} negative={negatives} runtime_operations={operations} exception_cases={exceptions} fresh_loop_after_mutation=true phi_paths=true reference_release=true capacity=true version_and_wrap=true enum_invalidated=true finally_and_original_exception_order=true");

sealed record ReferenceCase(MethodDefinition Method,VariableDefinition List,VariableDefinition Version,VariableDefinition Count,VariableDefinition First,VariableDefinition Second,
    Instruction Entry,Instruction FirstCall,Instruction FirstStore,Instruction? CopyB,Instruction ArrayCall,Instruction? Skip,Instruction Join);
sealed record ValueCase(MethodDefinition Method,VariableDefinition List,VariableDefinition Version,Instruction[] Schedule);
sealed class ClearFixtures:IDisposable
{
    public readonly DefaultAssemblyResolver Resolver=new();
    public readonly AssemblyDefinition Assembly;
    public ModuleDefinition Module=>Assembly.MainModule;
    public readonly TypeDefinition Host,Holder;
    public readonly TypeReference Int,Object,Void;
    public readonly FieldDefinition Steps,Finally;
    public readonly MethodDefinition Observe;
    public ClearFixtures()
    {
        Resolver.AddSearchDirectory(Path.GetDirectoryName(typeof(List<>).Assembly.Location)!);
        Resolver.AddSearchDirectory(Path.GetDirectoryName(typeof(Vector2).Assembly.Location)!);
        Assembly=AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("ClearCarriedFixtures",new Version(1,0)),"ClearCarriedFixtures",
            new ModuleParameters{Kind=ModuleKind.Dll,AssemblyResolver=Resolver,Runtime=TargetRuntime.Net_4_0});
        var m=Module;Int=m.ImportReference(typeof(int));Object=m.ImportReference(typeof(object));Void=m.ImportReference(typeof(void));
        Host=new TypeDefinition("Fixture","ClearHost",TypeAttributes.Public|TypeAttributes.Abstract|TypeAttributes.Sealed,Object);m.Types.Add(Host);
        Holder=new TypeDefinition("Fixture","Holder",TypeAttributes.Public|TypeAttributes.Class,Object);m.Types.Add(Holder);
        Steps=new FieldDefinition("Steps",FieldAttributes.Public,Int);Holder.Fields.Add(Steps);
        var ctor=new MethodDefinition(".ctor",MethodAttributes.Public|MethodAttributes.SpecialName|MethodAttributes.RTSpecialName,Void);Holder.Methods.Add(ctor);
        var il=ctor.Body.GetILProcessor();il.Emit(OpCodes.Ldarg_0);il.Emit(OpCodes.Call,m.ImportReference(typeof(object).GetConstructor(Type.EmptyTypes)!));il.Emit(OpCodes.Ret);
        Finally=new FieldDefinition("FinallyCount",FieldAttributes.Public|FieldAttributes.Static,Int);Host.Fields.Add(Finally);
        Observe=new MethodDefinition("Observe",MethodAttributes.Public|MethodAttributes.Static,Void);Host.Methods.Add(Observe);Observe.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
    }
    GenericInstanceType List(TypeReference element){var t=new GenericInstanceType(Module.ImportReference(typeof(List<>)));t.GenericArguments.Add(element);return t;}
    MethodDefinition Method(string name){var m=new MethodDefinition(name,MethodAttributes.Public|MethodAttributes.Static,Void);Host.Methods.Add(m);m.Body.InitLocals=true;return m;}
    ParameterDefinition Param(MethodDefinition m,string name,TypeReference type){var p=new ParameterDefinition(name,ParameterAttributes.None,type);m.Parameters.Add(p);return p;}
    VariableDefinition Local(MethodDefinition m,TypeReference type){var v=new VariableDefinition(type);m.Body.Variables.Add(v);return v;}
    public ReferenceCase Reference(string name,bool loop)
    {
        var m=Method(name);var type=List(Object);var listArg=Param(m,"list",type);var choose=Param(m,"choose",Module.ImportReference(typeof(bool)));
        var other=Param(m,"other",type);var callback=Param(m,"callback",Module.ImportReference(typeof(Action<List<object>>)));
        var list=Local(m,type);var version=Local(m,Int);var count=Local(m,Int);var first=loop?count:Local(m,Int);var second=Local(m,Int);var index=Local(m,Int);
        var vf=new FieldReference("_version",Int,type);var sf=new FieldReference("_size",Int,type);
        var items=new FieldReference("_items",new ArrayType(type.ElementType.GenericParameters[0]),type);
        var getCount=new MethodReference("get_Count",Int,type){HasThis=true};
        var clearArray=Module.ImportReference(typeof(Array).GetMethod("Clear",new[]{typeof(Array),typeof(int),typeof(int)})!);
        var il=m.Body.GetILProcessor();void Add(params Instruction[] code){foreach(var i in code)il.Append(i);}
        Instruction L(VariableDefinition v)=>Instruction.Create(OpCodes.Ldloc,v);Instruction A(ParameterDefinition p)=>Instruction.Create(OpCodes.Ldarg,p);
        var clearLabel=Instruction.Create(OpCodes.Nop);var join=Instruction.Create(OpCodes.Nop);var skip=Instruction.Create(OpCodes.Nop);
        Instruction firstCall=Instruction.Create(OpCodes.Callvirt,getCount),firstStore=Instruction.Create(OpCodes.Stloc,first);Instruction? copyB=null,tryStart=null;
        Add(A(listArg),Instruction.Create(OpCodes.Stloc,list));
        if(loop)
        {
            var header=Instruction.Create(OpCodes.Nop);tryStart=header;
            Add(Instruction.Create(OpCodes.Ldc_I4,0),Instruction.Create(OpCodes.Stloc,index),header,L(list),firstCall,firstStore,
                L(count),L(index),Instruction.Create(OpCodes.Cgt),Instruction.Create(OpCodes.Ldc_I4,0),Instruction.Create(OpCodes.Ceq),Instruction.Create(OpCodes.Brtrue,clearLabel));
            Add(A(callback),L(list),Instruction.Create(OpCodes.Callvirt,Module.ImportReference(typeof(Action<List<object>>).GetMethod("Invoke")!)),
                L(index),Instruction.Create(OpCodes.Ldc_I4,1),Instruction.Create(OpCodes.Add),Instruction.Create(OpCodes.Stloc,index),Instruction.Create(OpCodes.Br,header));
        }
        else
        {
            var branchB=Instruction.Create(OpCodes.Nop);
            Add(A(choose),Instruction.Create(OpCodes.Brfalse,branchB),L(list),firstCall,firstStore,
                A(other),Instruction.Create(OpCodes.Callvirt,getCount),Instruction.Create(OpCodes.Pop),L(first),Instruction.Create(OpCodes.Stloc,count),Instruction.Create(OpCodes.Br,clearLabel),branchB,
                L(list),Instruction.Create(OpCodes.Callvirt,getCount),Instruction.Create(OpCodes.Stloc,second));
            copyB=L(second);Add(copyB,Instruction.Create(OpCodes.Stloc,count),Instruction.Create(OpCodes.Br,clearLabel));
        }
        Add(clearLabel);var entry=L(list);Add(entry,Instruction.Create(OpCodes.Ldfld,vf),Instruction.Create(OpCodes.Stloc,version),
            L(list),Instruction.Create(OpCodes.Ldc_I4,0),Instruction.Create(OpCodes.Stfld,sf),L(list),L(version),Instruction.Create(OpCodes.Ldc_I4,1),
            Instruction.Create(OpCodes.Add),Instruction.Create(OpCodes.Stfld,vf),L(count),Instruction.Create(OpCodes.Ldc_I4,1),Instruction.Create(OpCodes.Clt));
        var nonempty=Instruction.Create(OpCodes.Nop);
        if(loop)Add(Instruction.Create(OpCodes.Brfalse,nonempty),Instruction.Create(OpCodes.Leave,join),nonempty,Instruction.Create(OpCodes.Nop));
        else Add(Instruction.Create(OpCodes.Brtrue,skip),nonempty);
        var arrayCall=Instruction.Create(OpCodes.Call,clearArray);
        Add(L(list),Instruction.Create(OpCodes.Ldfld,items),Instruction.Create(OpCodes.Ldc_I4,0),L(count),arrayCall);
        if(loop)
        {
            Add(Instruction.Create(OpCodes.Leave,join));var handler=Instruction.Create(OpCodes.Ldsfld,Finally);
            Add(handler,Instruction.Create(OpCodes.Ldc_I4,1),Instruction.Create(OpCodes.Add),Instruction.Create(OpCodes.Stsfld,Finally),Instruction.Create(OpCodes.Endfinally));
            m.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Finally){TryStart=tryStart,TryEnd=handler,HandlerStart=handler,HandlerEnd=join});
        }
        Add(join,Instruction.Create(OpCodes.Ret));if(!loop)Add(skip,Instruction.Create(OpCodes.Br,join));
        return new ReferenceCase(m,list,version,count,first,second,entry,firstCall,firstStore,copyB,arrayCall,loop?null:skip,join);
    }
    public ValueCase Value(string name)
    {
        var m=Method(name);var type=List(Module.ImportReference(typeof(Vector2)));var arg=Param(m,"list",type);
        var holder=Param(m,"holder",Holder);var steps=Param(m,"steps",Int);var list=Local(m,type);var version=Local(m,Int);
        var vf=new FieldReference("_version",Int,type);var sf=new FieldReference("_size",Int,type);var il=m.Body.GetILProcessor();
        void Add(params Instruction[] code){foreach(var i in code)il.Append(i);}
        var alternate=Instruction.Create(OpCodes.Nop);var merge=Instruction.Create(OpCodes.Nop);
        Add(Instruction.Create(OpCodes.Ldarg,arg),Instruction.Create(OpCodes.Stloc,list),Instruction.Create(OpCodes.Ldloc,list),
            Instruction.Create(OpCodes.Ldfld,vf),Instruction.Create(OpCodes.Stloc,version));
        Instruction[] schedule=[Instruction.Create(OpCodes.Ldarg,holder),Instruction.Create(OpCodes.Ldc_I4,2),Instruction.Create(OpCodes.Ldarg,steps),
            Instruction.Create(OpCodes.Clt),Instruction.Create(OpCodes.Brfalse,alternate),Instruction.Create(OpCodes.Ldarg,steps),Instruction.Create(OpCodes.Br,merge),
            alternate,Instruction.Create(OpCodes.Ldc_I4,2),merge,Instruction.Create(OpCodes.Stfld,Steps)];
        Add(schedule);Add(Instruction.Create(OpCodes.Ldloc,list),Instruction.Create(OpCodes.Ldc_I4,0),Instruction.Create(OpCodes.Stfld,sf),
            Instruction.Create(OpCodes.Ldloc,list),Instruction.Create(OpCodes.Ldloc,version),Instruction.Create(OpCodes.Ldc_I4,1),
            Instruction.Create(OpCodes.Add),Instruction.Create(OpCodes.Stfld,vf),Instruction.Create(OpCodes.Ret));
        return new ValueCase(m,list,version,schedule);
    }
    public void Dispose(){Assembly.Dispose();Resolver.Dispose();}
}
