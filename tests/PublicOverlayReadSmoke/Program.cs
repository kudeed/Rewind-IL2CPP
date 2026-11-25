using Mono.Cecil;
using Mono.Cecil.Cil;
using Rewind.Model;
using Rewind.Runtime;
using Rewind.Output;
using System.Reflection;

static void Check(bool pass,string why){if(!pass)throw new Exception(why);}
var sf=new SigFactory();
(TypeDef T,FieldDef Rgba) Fixture(){
 var a=new AssemblyModel{Name="UnityEngine.CoreModule"};
 var t=new TypeDef{Index=1,Name="Color32",Namespace="UnityEngine",Assembly=a,IsValueType=true,Flags=TypeDef.ExplicitLayout,Sizes=new RawTypeSizes(20,4,0,0)};
 t.Sig=sf.TypeDef(t);
 var rgba=new FieldDef{DeclaringType=t,Name="rgba",Type=sf.Primitive(Il2CppTypeEnum.I4),Offset=16,Attrs=1};
 var fields=new List<FieldDef>{rgba};
 for(int i=0;i<4;i++)fields.Add(new FieldDef{DeclaringType=t,Name="rgba"[i].ToString(),Type=sf.Primitive(Il2CppTypeEnum.U1),Offset=16+i,Attrs=6});
 t.Fields=fields.ToArray();return(t,rgba);
}
var valid=Fixture();
Check(PublicOverlayRead.TryColor32(valid.Rgba,valid.T.Sig,16,out var f)&&f.Select(x=>x.Name).SequenceEqual(new[]{"r","g","b","a"}),"valid layout");
var tests=new (string Name,Action<TypeDef,FieldDef> Change)[]{
 ("wrong assembly",(t,p)=>t.Assembly.Name="Other"),
 ("wrong type",(t,p)=>t.Name="Other"),
 ("not explicit",(t,p)=>t.Flags=TypeDef.SequentialLayout),
 ("not value type",(t,p)=>t.IsValueType=false),
 ("wrong size",(t,p)=>t.Sizes=new RawTypeSizes(24,8,0,0)),
 ("wrong packed offset",(t,p)=>p.Offset=20),
 ("wrong packed type",(t,p)=>p.Type=sf.Primitive(Il2CppTypeEnum.U4)),
 ("packed public",(t,p)=>p.Attrs=6),
 ("wrong channel offset",(t,p)=>t.Fields[2].Offset=18),
 ("private channel",(t,p)=>t.Fields[3].Attrs=1),
 ("wrong channel type",(t,p)=>t.Fields[4].Type=sf.Primitive(Il2CppTypeEnum.I1)),
 ("missing field",(t,p)=>t.Fields=t.Fields[..4]),
 ("duplicate field",(t,p)=>t.Fields[3].Name="g"),
 ("static channel",(t,p)=>t.Fields[1].Attrs=6|FieldDef.Static)
};
foreach(var (name,change) in tests){
 var x=Fixture();change(x.T,x.Rgba);
 // Rebuild the signature: the fixture's SigFactory is interned by type index.
 var own=new SigFactory().TypeDef(x.T);
 Check(!PublicOverlayRead.TryColor32(x.Rgba,own,16,out _),"accepted "+name);
}
Check(!PublicOverlayRead.TryColor32(valid.Rgba,null,16,out _),"null owner");
Check(!PublicOverlayRead.TryColor32(valid.Rgba,valid.T.Sig,8,out _),"wrong header");
Console.WriteLine("PUBLIC_OVERLAY_LAYOUT_PASS positive=1 negative="+(tests.Length+2));
// Exercise the actual emitter using an independent synthetic value-type
// provider that counts calls, plus every byte in each position and random values.
using var a=AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("SyntheticOverlay",new Version(1,0)),"SyntheticOverlay",ModuleKind.Dll);
var mod=a.MainModule;
var color=new TypeDefinition("Synthetic","Color",Mono.Cecil.TypeAttributes.Public|Mono.Cecil.TypeAttributes.Sealed|Mono.Cecil.TypeAttributes.ExplicitLayout,mod.ImportReference(typeof(ValueType))){ClassSize=4,PackingSize=1};
mod.Types.Add(color);
var channels=Enumerable.Range(0,4).Select(i=>new FieldDefinition("rgba"[i].ToString(),Mono.Cecil.FieldAttributes.Public,mod.TypeSystem.Byte){Offset=i}).ToArray();
foreach(var c in channels)color.Fields.Add(c);
var holder=new TypeDefinition("Synthetic","Probe",Mono.Cecil.TypeAttributes.Public|Mono.Cecil.TypeAttributes.Abstract|Mono.Cecil.TypeAttributes.Sealed,mod.TypeSystem.Object);
mod.Types.Add(holder);
var calls=new FieldDefinition("Calls",Mono.Cecil.FieldAttributes.Public|Mono.Cecil.FieldAttributes.Static,mod.TypeSystem.Int32);holder.Fields.Add(calls);
MethodDefinition Make(string name,TypeReference ret){
 var m=new MethodDefinition(name,Mono.Cecil.MethodAttributes.Public|Mono.Cecil.MethodAttributes.Static,ret);
 for(int i=0;i<4;i++)m.Parameters.Add(new ParameterDefinition("p"+i,Mono.Cecil.ParameterAttributes.None,mod.TypeSystem.Byte));
 holder.Methods.Add(m);return m;
}
var provider=Make("GetColor",color);
provider.Body.InitLocals=true;
var obj=new VariableDefinition(color);provider.Body.Variables.Add(obj);
var p=provider.Body.GetILProcessor();
p.Emit(OpCodes.Ldsfld,calls);p.Emit(OpCodes.Ldc_I4_1);p.Emit(OpCodes.Add);p.Emit(OpCodes.Stsfld,calls);
p.Emit(OpCodes.Ldloca,obj);p.Emit(OpCodes.Initobj,color);
for(int i=0;i<4;i++){p.Emit(OpCodes.Ldloca,obj);p.Emit(OpCodes.Ldarg,provider.Parameters[i]);p.Emit(OpCodes.Stfld,channels[i]);}
p.Emit(OpCodes.Ldloc,obj);p.Emit(OpCodes.Ret);
var pack=Make("Pack",mod.TypeSystem.Int32);
var snapshot=new VariableDefinition(color);pack.Body.Variables.Add(snapshot);
var il=pack.Body.GetILProcessor();
for(int i=0;i<4;i++)il.Emit(OpCodes.Ldarg,pack.Parameters[i]);
il.Emit(OpCodes.Call,provider);
PublicOverlayRead.Emit(il,snapshot,channels);
il.Emit(OpCodes.Ret);
using var stream=new MemoryStream();a.Write(stream);
var rt=Assembly.Load(stream.ToArray()).GetType("Synthetic.Probe",true)!;
var invoke=rt.GetMethod("Pack")!.CreateDelegate<Func<byte,byte,byte,byte,int>>();
var random=new Random(602616);int n=0;
void Run(byte r,byte g,byte b,byte alpha){
 uint expected=(uint)r|((uint)g<<8)|((uint)b<<16)|((uint)alpha<<24);
 Check(unchecked((uint)invoke(r,g,b,alpha))==expected,"packing result");
 n++;
}
for(int c=0;c<4;c++)for(int i=0;i<256;i++){byte[] v=[17,114,195,238];v[c]=(byte)i;Run(v[0],v[1],v[2],v[3]);}
for(int i=0;i<1024;i++)Run((byte)random.Next(256),(byte)random.Next(256),(byte)random.Next(256),(byte)random.Next(256));
Check((int)rt.GetField("Calls")!.GetValue(null)! == n,"provider evaluation count");
Console.WriteLine("PUBLIC_OVERLAY_IL_PASS cases="+n+" provider_calls="+n);
