using System.Reflection;
using System.Security.Cryptography;
using System.Text.Json;
using System.Text.Json.Nodes;
using Mono.Cecil;
using Mono.Cecil.Cil;
using Mono.Cecil.Rocks;
using MA=Mono.Cecil.MethodAttributes;
using TA=Mono.Cecil.TypeAttributes;
using PA=Mono.Cecil.ParameterAttributes;
using MethodBody=Mono.Cecil.Cil.MethodBody;
static void Check(bool v,string s){if(!v)throw new Exception(s);}
string source=args[0],dest=args[1],proof=args.Length>2?args[2]:"/data/workspace/rewind-null-proof-v175/mdarray-proof";
Directory.CreateDirectory(dest);
using var original=AssemblyDefinition.ReadAssembly(source);
using var fixture=AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("MdRecovered",new Version(1,0)),"MdRecovered",ModuleKind.Dll);
var mod=fixture.MainModule;
using var runner=AssemblyDefinition.ReadAssembly(typeof(Manager).Assembly.Location);
TypeDefinition BoundType(string name)=>runner.MainModule.Types.Single(t=>t.Name==name);
MethodReference BoundMethod(string type,string name)=>mod.ImportReference(BoundType(type).Methods.Single(m=>m.Name==name));
var holder=new TypeDefinition("Fixture","Recovered",TA.Public|TA.Abstract|TA.Sealed,mod.TypeSystem.Object);mod.Types.Add(holder);
var receipt=new List<object>();
TypeReference MapType(TypeReference t){
 if(t is ArrayType a)return new ArrayType(MapType(a.ElementType),a.Rank);
 return t.FullName switch{
  "Unicorn.MazeFloor" or "Floor"=>mod.ImportReference(BoundType("Item")),
  "Unicorn.MazeManager"=>mod.ImportReference(BoundType("Manager")),
  "Unicorn.LobbyManager"=>mod.ImportReference(BoundType("Controller")),
  "Unicorn.LobbyManager/<MazeCameraIntroduceMap>d__144"=>mod.ImportReference(BoundType("CameraState")),
  "UnityEngine.Vector3"=>mod.ImportReference(BoundType("Vec3")),
  "System.Int32"=>mod.TypeSystem.Int32,"System.Int64"=>mod.TypeSystem.Int64,
  "System.UInt64"=>mod.TypeSystem.UInt64,"System.Single"=>mod.TypeSystem.Single,
  "System.Boolean"=>mod.TypeSystem.Boolean,"System.Void"=>mod.TypeSystem.Void,
  "System.Object"=>mod.TypeSystem.Object,
  _=>throw new Exception("unexpected type "+t.FullName)};
}
FieldReference MapField(FieldReference f){
 Check(f.DeclaringType.FullName=="Unicorn.LobbyManager/<MazeCameraIntroduceMap>d__144","unexpected field "+f.FullName);
 string name=f.Name switch{"<>1__state"=>"State","<>4__this"=>"Controller","<Maze>5__2"=>"Maze",_=>throw new Exception("unexpected state field "+f.FullName)};
 return mod.ImportReference(BoundType("CameraState").Fields.Single(f=>f.Name==name));
}
MethodReference MapCall(MethodReference c,bool nativeLength){
 if(c.DeclaringType.FullName=="System.Array"){
  if(nativeLength)return mod.ImportReference(typeof(Hook).GetMethod(nameof(Hook.NativeLength))!);
  var found=typeof(Array).GetMethods().Single(x=>x.Name==c.Name&&x.ReturnType.FullName==c.ReturnType.FullName&&x.GetParameters().Select(p=>p.ParameterType.FullName).SequenceEqual(c.Parameters.Select(p=>p.ParameterType.FullName)));
  return mod.ImportReference(found);
 }
 if(c.Name==".ctor"&&c.Parameters.Count==0&&c.DeclaringType.FullName=="System.IndexOutOfRangeException")return mod.ImportReference(typeof(IndexOutOfRangeException).GetConstructor(Type.EmptyTypes)!);
 if(c.Name==".ctor"&&c.Parameters.Count==0&&c.DeclaringType.FullName=="System.NullReferenceException")return mod.ImportReference(typeof(NullReferenceException).GetConstructor(Type.EmptyTypes)!);
 if(c.Name=="get_Maze"&&c.DeclaringType.FullName=="Unicorn.MazeManager")return BoundMethod("Manager","GetMaze");
 if(c.Name=="RefreshTextColorInFloor"&&c.DeclaringType.FullName=="Floor")return BoundMethod("Item","Refresh");
 if(c.Name=="CalculateCamIntroducePos"&&c.DeclaringType.FullName=="Unicorn.LobbyManager")return BoundMethod("Controller","Position");
 throw new Exception("unexpected call "+c.FullName);
}
MethodDefinition NewMethod(string name,TypeReference result,params (string,TypeReference)[] parameters){
 var f=new MethodDefinition(name,MA.Public|MA.Static,result);holder.Methods.Add(f);
 foreach(var (n,t) in parameters)f.Parameters.Add(new ParameterDefinition(n,PA.None,t));
 f.Body=new MethodBody(f){InitLocals=true};return f;
}
var scan=(MethodDefinition)original.MainModule.LookupToken(0x060018F5);
var corners=(MethodDefinition)original.MainModule.LookupToken(0x06001BB0);
scan.Body.SimplifyMacros();corners.Body.SimplifyMacros();
void Clone(MethodDefinition src,string name,List<Instruction> ins,HashSet<int> originalLengths,Instruction? cut,VariableDefinition? seeded){
 var f=NewMethod(name,mod.TypeSystem.Void,("instance",MapType(src.DeclaringType)));
 var vars=ins.Where(i=>i.Operand is VariableDefinition).Select(i=>(VariableDefinition)i.Operand).Distinct().OrderBy(v=>v.Index).ToList();
 if(seeded!=null&&!vars.Contains(seeded))vars.Add(seeded);
 var vm=new Dictionary<VariableDefinition,VariableDefinition>();
 foreach(var v in vars){var n=new VariableDefinition(MapType(v.VariableType));f.Body.Variables.Add(n);vm[v]=n;}
 if(seeded!=null){
  f.Body.Instructions.Add(Instruction.Create(OpCodes.Ldarg,f.Parameters[0]));
  f.Body.Instructions.Add(Instruction.Create(OpCodes.Ldfld,mod.ImportReference(BoundType("CameraState").Fields.Single(f=>f.Name==nameof(CameraState.Controller)))));
  f.Body.Instructions.Add(Instruction.Create(OpCodes.Stloc,vm[seeded]));
 }
 var im=new Dictionary<Instruction,Instruction>();
 foreach(var i in ins){
  var n=Instruction.Create(OpCodes.Nop);n.OpCode=i.OpCode;f.Body.Instructions.Add(n);im[i]=n;
  if(i==cut){f.Body.Instructions.Add(Instruction.Create(OpCodes.Pop));f.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));}
 }
 int lengthOrdinal=0,nativeCount=0;
 foreach(var i in ins){
  bool nl=false;
  if(i.Operand is MethodReference c&&c.DeclaringType.FullName=="System.Array"&&c.Name=="GetLength"){nl=originalLengths.Contains(lengthOrdinal++);if(nl)nativeCount++;}
  im[i].Operand=i.Operand switch{
   null=>null,Instruction b=>im[b],Instruction[] bs=>bs.Select(b=>im[b]).ToArray(),
   VariableDefinition v=>vm[v],ParameterDefinition p when p.Index==-1=>f.Parameters[0],
   ParameterDefinition p=>f.Parameters[p.Index+1],TypeReference t=>MapType(t),
   FieldReference field=>MapField(field),MethodReference call=>MapCall(call,nl),var x=>x
  };
  if(nl)im[i].OpCode=OpCodes.Call;
 }
 Check(lengthOrdinal==(name=="Scan"?3:10),"GetLength site count "+name+" "+lengthOrdinal);
 Check(nativeCount==originalLengths.Count,"native call count");f.Body.OptimizeMacros();
 receipt.Add(new{name,source_token=src.MetadataToken.ToInt32(),instructions=ins.Count,length_sites=lengthOrdinal,original_length_ordinals=originalLengths.Order().ToArray(),cut_after_source_offset=cut?.Offset,entry_offset=ins[0].Offset,seeded_local=seeded?.Index});
}
Clone(scan,"Scan",scan.Body.Instructions.ToList(),[0,1],null,null);
var entry=(Instruction)corners.Body.Instructions.First(i=>i.OpCode==OpCodes.Brtrue).Operand;
var cameraCalls=corners.Body.Instructions.SkipWhile(i=>i!=entry).Where(i=>i.Operand is MethodReference m&&m.Name=="CalculateCamIntroducePos").Take(4).ToArray();
Check(cameraCalls.Length==4,"camera 4 calls");
var last=cameraCalls[3];var selected=corners.Body.Instructions.SkipWhile(i=>i!=entry).TakeWhile(i=>i!=last).Append(last).ToHashSet();
foreach(var target in selected.SelectMany(i=>i.Operand switch{Instruction t=>new[]{t},Instruction[] t=>t,_=>Array.Empty<Instruction>()}).ToArray()){
 if(selected.Contains(target))continue;
 var chain=new List<Instruction>();var n=target;
 while(n!=null&&chain.Count<8){chain.Add(n);if(n.OpCode==OpCodes.Throw)break;n=n.Next;}
 Check(chain.Last().OpCode==OpCodes.Throw&&chain.All(i=>i.OpCode==OpCodes.Nop||i.OpCode==OpCodes.Throw||i.OpCode==OpCodes.Newobj&&i.Operand is MethodReference c&&c.DeclaringType.FullName=="System.IndexOutOfRangeException"),"external prefix edge not an original throw");
 foreach(var i in chain)selected.Add(i);
}
var seed=corners.Body.Variables.Single(v=>v.VariableType.FullName=="Unicorn.LobbyManager");
Clone(corners,"Corners",corners.Body.Instructions.Where(selected.Contains).ToList(),[2,4,7,8],last,seed);
// Extract actual emitted expressions; retain all arithmetic, conversions, lower-bound calls and casts.
void ExtractGet(MethodDefinition src,int ordinal,string name){
 src.Body.SimplifyMacros();
 var cast=src.Body.Instructions.Where(i=>i.OpCode==OpCodes.Castclass&&i.Operand is TypeReference t&&t.FullName=="Unicorn.MazeFloor").ElementAt(ordinal);
 int need=1;var slice=new List<Instruction>();
 for(var i=cast;i!=null;i=i.Previous){
  int pop,push;
  if(i.Operand is MethodReference m){pop=m.Parameters.Count+(m.HasThis?1:0);push=m.ReturnType.MetadataType==MetadataType.Void?0:1;}
  else if(i.OpCode==OpCodes.Ldloc||i.OpCode==OpCodes.Ldc_I4){pop=0;push=1;}
  else if(i.OpCode==OpCodes.Conv_I4||i.OpCode==OpCodes.Conv_I8||i.OpCode==OpCodes.Conv_U8||i.OpCode==OpCodes.Castclass){pop=1;push=1;}
  else if(i.OpCode==OpCodes.Add){pop=2;push=1;}
  else if(i.OpCode==OpCodes.Nop){pop=0;push=0;}
  else throw new Exception("unexpected slice opcode "+i);
  need=need-push+pop;slice.Add(i);if(need==0)break;
 }
 Check(need==0,"slice stack balance");slice.Reverse();
 var live=slice.Where(i=>i.OpCode==OpCodes.Ldloc).Select(i=>(VariableDefinition)i.Operand).Distinct().ToArray();
 Check(live.Length==3&&live[0].VariableType is ArrayType{Rank:2}&&live.Skip(1).All(v=>v.VariableType.MetadataType is MetadataType.Int64 or MetadataType.Int32 or MetadataType.UInt64),"slice input types "+name+" "+string.Join(",",live.Select(v=>v.VariableType.FullName)));
 var getter=NewMethod(name,mod.ImportReference(BoundType("Item")),("array",MapType(live[0].VariableType)),("row",MapType(live[1].VariableType)),("col",MapType(live[2].VariableType)));
 foreach(var i in slice){
  var n=Instruction.Create(OpCodes.Nop);n.OpCode=i.OpCode;
  if(i.Operand is VariableDefinition v){n.OpCode=OpCodes.Ldarg;n.Operand=getter.Parameters[Array.IndexOf(live,v)];}
  else n.Operand=i.Operand switch{MethodReference c=>MapCall(c,false),TypeReference t=>MapType(t),var x=>x};
  getter.Body.Instructions.Add(n);
 }
 getter.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));getter.Body.OptimizeMacros();
 receipt.Add(new{name,source_token=src.MetadataToken.ToInt32(),cast_ordinal=ordinal,entry_offset=slice[0].Offset,end_offset=cast.Offset,instructions=slice.Count,live_locals=live.Select(v=>new{v.Index,type=v.VariableType.FullName}).ToArray(),scope="Actual emitted expression; only its array and index live-ins are rebound."});
}
ExtractGet(scan,0,"Get");
var occupy=(MethodDefinition)original.MainModule.LookupToken(0x060018FA);
ExtractGet(occupy,2,"HelperGet");
var fp=Path.Combine(dest,"MdRecovered.dll");fixture.Write(fp);
File.WriteAllText(Path.Combine(dest,"fixture-bindings.json"),JsonSerializer.Serialize(receipt,new JsonSerializerOptions{WriteIndented=true}));
var loaded=System.Reflection.Assembly.Load(File.ReadAllBytes(fp)).GetType("Fixture.Recovered")!;
using var cs=JsonDocument.Parse(File.ReadAllText(Path.Combine(proof,"cases.json")));
using var ns=JsonDocument.Parse(File.ReadAllText(Path.Combine(proof,"native-oracle.json")));
var expected=ns.RootElement.GetProperty("cases").EnumerateArray().ToDictionary(x=>x.GetProperty("id").GetString()!);
var results=new List<object>();int failed=0;
foreach(var c in cs.RootElement.EnumerateArray()){
 var id=c.GetProperty("id").GetString()!;var mode=c.GetProperty("mode").GetString()!;
 foreach(var fixtureName in mode=="get"?new[]{"Get","HelperGet"}:new[]{mode=="scan"?"Scan":"Corners"}){
 Hook.Reset(c);
 var arrays=new Dictionary<string,Item?[,]>();
 foreach(var a in c.GetProperty("arrays").EnumerateArray()){
  int[] lengths=a.GetProperty("lengths").EnumerateArray().Select(x=>x.GetInt32()).ToArray(),lower=a.GetProperty("lower").EnumerateArray().Select(x=>x.GetInt32()).ToArray();
  var arr=(Item?[,])Array.CreateInstance(typeof(Item),lengths,lower);
  int p=0;foreach(var item in a.GetProperty("items").EnumerateArray()){arr[p/lengths[1]+lower[0],p%lengths[1]+lower[1]]=item.ValueKind==JsonValueKind.Null?null:new Item(item.GetInt32());p++;}
  var name=a.GetProperty("id").GetString()!;arrays.Add(name,arr);Hook.Names.Add(arr,name);
 }
 Hook.Arrays=arrays;
 var initial=c.GetProperty("initial").GetString();var current=initial==null?null:arrays[initial];
 var manager=new Manager{Maze=current};var state=new CameraState{Maze=current,State=1,Controller=c.TryGetProperty("null_controller",out var nc)&&nc.GetBoolean()?null:new Controller()};
 Hook.Manager=manager;Hook.State=state;
 string? exception=null;int? returned=null;bool completed=false;
 try{
  var method=loaded.GetMethod(fixtureName)!;
  if(mode=="get"){
   var ps=method.GetParameters();object Index(string name,Type t){long value=c.GetProperty(name).GetInt64();return t==typeof(ulong)?(object)(ulong)unchecked((uint)value):Convert.ChangeType(value,t);}
   object ri=Index("row",ps[1].ParameterType),ci=Index("col",ps[2].ParameterType);
   returned=((Item?)method.Invoke(null,[current,ri,ci]))?.Id;
  }else method.Invoke(null,[mode=="scan"?(object)manager:state]);
  completed=true;
 }catch(TargetInvocationException ex){exception=ex.InnerException!.GetType().Name;if(exception=="MissingMethodException"&&id.EndsWith("0x0-0-0"))Console.WriteLine(ex.InnerException.ToString());}
 var cur=mode=="corners"?state.Maze:manager.Maze;
 var actual=new{id,returned,exception,completed,events=Hook.Events.ToArray(),current=cur==null?null:Hook.Names[cur],state=mode=="corners"?(int?)state.State:null};
 var aj=JsonSerializer.Serialize(actual);bool pass=JsonNode.DeepEquals(JsonNode.Parse(aj),JsonNode.Parse(expected[id].GetRawText()));
 if(!pass)failed++;results.Add(new{id,fixture=fixtureName,pass,actual,expected=expected[id]});
 }
}
string Sha(string p)=>Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(p))).ToLowerInvariant();
var output=new{pass=failed==0,cases=results.Count,mismatches=failed,source_sha256=Sha(source),fixture_sha256=Sha(fp),oracle_sha256=Sha(Path.Combine(proof,"native-oracle.json")),bindings_sha256=Sha(Path.Combine(dest,"fixture-bindings.json")),results};
File.WriteAllText(Path.Combine(dest,"native-il-differential.json"),JsonSerializer.Serialize(output,new JsonSerializerOptions{WriteIndented=true}));
Console.WriteLine($"MD_NATIVE_IL_DIFFERENTIAL cases={results.Count} mismatches={failed}");
Check(failed==0,"native/IL mismatch");
public sealed class Item(int id){public int Id=id;public void Refresh()=>Hook.Callback("refresh",this);}
public sealed class Manager{public Item?[,]? Maze;public Item?[,]? GetMaze()=>Maze;}
public sealed class CameraState{public int State;public Controller? Controller;public Item?[,]? Maze;}
public readonly record struct Vec3(float X,float Y,float Z);
public sealed class Controller{public Vec3 Position(Item? item){Hook.Callback("position",item);return new Vec3(1,2,3);}}
public static class Hook{
 public static Dictionary<string,Item?[,]> Arrays=[];
 public static Dictionary<Array,string> Names=new(ReferenceEqualityComparer.Instance);
 public static readonly List<object?[]> Events=[];
 public static Manager Manager=null!;public static CameraState State=null!;
 static JsonElement Case;static int CallbackCount,LengthCount;
 public static void Reset(JsonElement c){Case=c;CallbackCount=LengthCount=0;Events.Clear();Names.Clear();}
 static void Replace(string kind,int at){
  if(Case.TryGetProperty("replacements",out var swaps))foreach(var swap in swaps.EnumerateArray())
   if(swap.GetProperty("kind").GetString()==kind&&swap.GetProperty("at").GetInt32()==at){
    string? name=swap.GetProperty("to").GetString();var value=name==null?null:Arrays[name];Manager.Maze=value;State.Maze=value;
   }
 }
 public static int NativeLength(Array array,int dimension){
  int length=array.GetLength(dimension);Events.Add(["length",Names[array],dimension,length]);
  Replace("length",LengthCount++);return length;
 }
 public static void Callback(string kind,Item? item){
  Events.Add([kind,item?.Id]);int n=CallbackCount++;
  if(Case.TryGetProperty("throw_callback",out var t)&&t.GetInt32()==n)throw new InvalidOperationException();
  Replace("callback",n);
 }
}
