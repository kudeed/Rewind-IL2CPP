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

(MethodDefinition M,Instruction[] Region,Instruction Slow,Instruction Join,VariableDefinition Array,VariableDefinition Value) Fixture(string name,bool scheduled)
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
    il.Append(slow);il.Emit(OpCodes.Ldloc,list);il.Emit(OpCodes.Ldloc,value);il.Emit(OpCodes.Callvirt,resize);il.Append(join);il.Emit(OpCodes.Ret);
    return(m,region.ToArray(),slow,join,array,value);
}
static string Shape(MethodBody b)=>string.Join("\n",b.Instructions.Select(i=>i.OpCode.Code+":"+i.Operand));
var canonical=Fixture("Canonical",false);var scheduled=Fixture("Scheduled",true);
foreach(var f in new[]{canonical,scheduled}){
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
Console.WriteLine($"LIST_APPEND_IL_FOLDING_SMOKE_PASS runtime_operations={runs} negative_patterns={negatives.Length+1} null_cases=2");
