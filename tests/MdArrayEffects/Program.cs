using System.Reflection;
using System.Security.Cryptography;
using System.Text.Json;
using System.Text.Json.Nodes;
using Mono.Cecil;
using Mono.Cecil.Cil;
using Mono.Cecil.Rocks;
using MA=Mono.Cecil.MethodAttributes;using TA=Mono.Cecil.TypeAttributes;using PA=Mono.Cecil.ParameterAttributes;using MB=Mono.Cecil.Cil.MethodBody;
static void Check(bool b,string n){if(!b)throw new Exception(n);}
string input=args[0],oracle=args[1],output=args[2];Directory.CreateDirectory(output);
using var bindings=AssemblyDefinition.ReadAssembly(typeof(Manager).Assembly.Location);
TypeDefinition B(string name)=>bindings.MainModule.Types.Single(t=>t.Name==name);
using var result=AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("MdEffectsRecovered",new Version(1,0)),"MdEffectsRecovered",ModuleKind.Dll);
var mod=result.MainModule;var holder=new TypeDefinition("Fixture","Recovered",TA.Public|TA.Abstract|TA.Sealed,mod.TypeSystem.Object);mod.Types.Add(holder);
using var manifest=JsonDocument.Parse(File.ReadAllText(Path.Combine(input,"effects-manifest.json")));
TypeReference TypeMap(TypeReference t)=>t switch{
 ArrayType a=>new ArrayType(TypeMap(a.ElementType),a.Rank),
 _=>t.FullName switch{
 "Unicorn.MazeManager"=>mod.ImportReference(B("Manager")),"Unicorn.MazeFloor"=>mod.ImportReference(B("Item")),
 "System.Int32"=>mod.TypeSystem.Int32,"System.Int64"=>mod.TypeSystem.Int64,"System.UInt64"=>mod.TypeSystem.UInt64,
 "System.Object"=>mod.TypeSystem.Object,_=>throw new Exception("type "+t.FullName)}};
MethodReference MethodMap(MethodReference m){
 if(m.Name=="get_Maze")return mod.ImportReference(B("Manager").Methods.Single(x=>x.Name=="Produce"));
 if(m.DeclaringType.FullName=="UnityEngine.Random"&&m.Name=="Range")return mod.ImportReference(B("Hook").Methods.Single(x=>x.Name=="Index"));
 Check(m.DeclaringType.FullName=="System.Array","unexpected method "+m.FullName);
 return mod.ImportReference(typeof(Array).GetMethods().Single(x=>x.Name==m.Name&&x.GetParameters().Select(p=>p.ParameterType.FullName).SequenceEqual(m.Parameters.Select(p=>p.ParameterType.FullName))));
}
foreach(var row in manifest.RootElement.EnumerateArray()){
 string mode=row.GetProperty("mode").GetString()!;using var src=AssemblyDefinition.ReadAssembly(Path.Combine(input,mode+".dll"));
 var method=(MethodDefinition)src.MainModule.LookupToken(row.GetProperty("token").GetInt32());method.Body.SimplifyMacros();
 foreach(bool mutant in new[]{false,true}){
  var f=new MethodDefinition(mode+(mutant?"Uncaptured":""),MA.Public|MA.Static,mod.ImportReference(B("Item")));holder.Methods.Add(f);
  f.Parameters.Add(new ParameterDefinition("owner",PA.None,mod.ImportReference(B("Manager"))));f.Body=new MB(f){InitLocals=true};
  foreach(var v in method.Body.Variables)f.Body.Variables.Add(new VariableDefinition(TypeMap(v.VariableType)));
  foreach(var old in method.Body.Instructions){
   var n=Instruction.Create(OpCodes.Nop);n.OpCode=old.OpCode;n.Operand=old.Operand switch{
    null=>null,VariableDefinition v=>f.Body.Variables[v.Index],ParameterDefinition p when p.Index==-1=>f.Parameters[0],
    TypeReference t=>TypeMap(t),MethodReference m=>MethodMap(m),FieldReference=>mod.ImportReference(B("Manager").Fields.Single(x=>x.Name=="Current")),var x=>x};
   f.Body.Instructions.Add(n);
  }
  if(mutant){
   // Deliberately remove only receiver capture to prove the runtime check detects repeated evaluation.
   var ins=f.Body.Instructions;
   var first=ins.Where(i=>i.OpCode!=OpCodes.Nop).Take(3).ToArray();
   Check(first.Length==3&&first[0].OpCode==OpCodes.Ldarg&&first[2].OpCode==OpCodes.Stloc,"array capture prefix");
   var captured=(VariableDefinition)first[2].Operand;
   var prefix=new[]{first[0],first[1]};foreach(var i in first)ins.Remove(i);
   foreach(var at in ins.Where(i=>i.OpCode==OpCodes.Ldloc&&ReferenceEquals(i.Operand,captured)).ToArray()){
    int n=ins.IndexOf(at);ins.RemoveAt(n);
    foreach(var p in prefix){var copy=Instruction.Create(OpCodes.Nop);copy.OpCode=p.OpCode;copy.Operand=p.Operand;ins.Insert(n++,copy);}
   }
  }
  f.Body.OptimizeMacros();
 }
}
string fixture=Path.Combine(output,"MdEffectsRecovered.dll");result.Write(fixture);
var runtime=System.Reflection.Assembly.Load(File.ReadAllBytes(fixture)).GetType("Fixture.Recovered")!;
using var cd=JsonDocument.Parse(File.ReadAllText(Path.Combine(oracle,"cases.json")));
using var nd=JsonDocument.Parse(File.ReadAllText(Path.Combine(oracle,"oracle.json")));
var expected=nd.RootElement.GetProperty("cases").EnumerateArray().ToDictionary(c=>c.GetProperty("id").GetString()!);
int failed=0,positive=0;var mutantDetected=new Dictionary<string,int>{{"call",0},{"field",0}};var rows=new List<object>();
foreach(var c in cd.RootElement.GetProperty("cases").EnumerateArray()){
 string id=c.GetProperty("id").GetString()!,mode=c.GetProperty("mode").GetString()!;
 foreach(bool mutant in new[]{false,true}){
  Hook.Arrays.Clear();Hook.Names.Clear();Hook.Events.Clear();Hook.Case=c;Hook.ArrayCalls=0;
  foreach(var a in cd.RootElement.GetProperty("arrays").EnumerateObject()){
   int[] lengths=a.Value.GetProperty("lengths").EnumerateArray().Select(x=>x.GetInt32()).ToArray(),lower=a.Value.GetProperty("lower").EnumerateArray().Select(x=>x.GetInt32()).ToArray();
   var arr=(Item[,])Array.CreateInstance(typeof(Item),lengths,lower);int n=0;
   foreach(var item in a.Value.GetProperty("items").EnumerateArray()){arr[lower[0]+n/lengths[1],lower[1]+n%lengths[1]]=new Item(item.GetInt32());n++;}
   Hook.Arrays.Add(a.Name,arr);Hook.Names.Add(arr,a.Name);
  }
  string? initial=c.GetProperty("array").GetString();var owner=new Manager{Current=initial==null?null:Hook.Arrays[initial]};Hook.Owner=owner;
  int? returned=null;string? exception=null;
  try{returned=((Item?)runtime.GetMethod(mode+(mutant?"Uncaptured":""))!.Invoke(null,[owner]))?.Id;}
  catch(TargetInvocationException ex){exception=ex.InnerException!.GetType().Name;}
  var actual=new{id,returned,exception,events=Hook.Events.ToArray(),current=owner.Current==null?null:Hook.Names[owner.Current]};
  bool same=JsonNode.DeepEquals(JsonNode.Parse(JsonSerializer.Serialize(actual)),JsonNode.Parse(expected[id].GetRawText()));
  if(mutant){if(!same)mutantDetected[mode]++;}else{positive++;if(!same)failed++;}
  rows.Add(new{id,mutant,match=same,actual,expected=expected[id]});
 }
}
string Sha(string f)=>Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(f))).ToLowerInvariant();
bool pass=failed==0&&mutantDetected.Values.All(n=>n>0);
File.WriteAllText(Path.Combine(output,"effects-differential.json"),JsonSerializer.Serialize(new{pass,cases=positive,mismatches=failed,mutant_detected=mutantDetected,fixture_sha256=Sha(fixture),manifest_sha256=Sha(Path.Combine(input,"effects-manifest.json")),oracle_sha256=Sha(Path.Combine(oracle,"oracle.json")),results=rows},new JsonSerializerOptions{WriteIndented=true}));
Console.WriteLine($"MD_EFFECT_BOUNDARY cases={positive} mismatches={failed} mutants={string.Join(",",mutantDetected.Values)}");
Check(pass,"effect-boundary regression");
public sealed class Item(int id){public int Id=id;}
public sealed class Manager{
 public Item[,]? Current;
 public Item[,]? Produce(){
  int call=Hook.ArrayCalls++;string? first=Hook.Case.GetProperty("array").GetString();string? name=call==0?first:call==1?"B":null;
  Hook.Events.Add(["array",name]);Hook.MaybeThrow("array");return name==null?null:Hook.Arrays[name];
 }
}
public static class Hook{
 public static readonly Dictionary<string,Item[,]> Arrays=[];
 public static readonly Dictionary<Array,string> Names=new(ReferenceEqualityComparer.Instance);
 public static readonly List<object?[]> Events=[];public static Manager Owner=null!;public static JsonElement Case;public static int ArrayCalls;
 public static void MaybeThrow(string stage){if(Case.GetProperty("throw_on").GetString()==stage)throw new InvalidOperationException();}
 public static int Index(int marker,int unused){
  string stage=marker==10?"row":marker==20?"col":throw new Exception("marker");int value=Case.GetProperty(stage).GetInt32();
  Events.Add([stage,value]);MaybeThrow(stage);
  if(Case.TryGetProperty("swap_after",out var swap)&&swap.GetString()==stage)Owner.Current=Arrays["B"];
  return value;
 }
}
