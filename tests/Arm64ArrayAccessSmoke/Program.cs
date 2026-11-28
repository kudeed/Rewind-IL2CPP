using System.Buffers.Binary;
using System.Text.Json;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Runtime;
static void Check(bool ok,string name){if(!ok)throw new Exception(name);}
byte[] actual=Convert.FromHexString("081840B93F00086B82000054080C018B021100F9C0035FD6FE0F1FF8028B0B94");
const ulong start=0x2072A44,thrower=0x2355668;
int positive=0,negative=0;
var match=Arm64ArrayAccessShape.Match(actual,start,a=>a==thrower);
Check(match is {Kind:HelperKind.ArraySetAt,IntArgs:3,NoReturn:false,ReturnsValue:false,ArrayAccessFreshObjectStore:true},"original native contract");positive++;
for(int word=0;word<7;word++)for(int bit=0;bit<32;bit++){byte[] b=[..actual];b[word*4+bit/8]^=(byte)(1<<(bit%8));Check(Arm64ArrayAccessShape.Match(b,start,a=>a==thrower)==null,"mutant "+word+"/"+bit);negative++;}
Check(Arm64ArrayAccessShape.Match(actual,start,_=>false)==null,"unproved thrower");negative++;
Check(Arm64ArrayAccessShape.Match(actual,start+2,_=>true)==null,"unaligned function");negative++;
Check(Arm64ArrayAccessShape.Match(actual[..28],start,_=>true)==null,"missing throw edge");negative++;
Check(Arm64ArrayAccessShape.Match([..actual,0,0,0,0],start,_=>true)==null,"neighbor bytes");negative++;
byte[] branch=[..actual];BinaryPrimitives.WriteUInt32LittleEndian(branch.AsSpan(28),0x140B8B02);Check(Arm64ArrayAccessShape.Match(branch,start,_=>true)==null,"tail branch not proven layout");negative++;
Node I32()=>new(){Op=Op.Param,Type=VT.I32};
Node K(long value)=>new(){Op=Op.Const,Type=VT.I64,Imm=value};
void Index(Node n,bool expected,string name){Check(Arm64ArrayAccessShape.CanonicalIndex(n)==expected,name);if(expected)positive++;else negative++;}
Index(I32(),true,"32bit parameter");
foreach(var op in new[]{Op.ZExt,Op.SExt})Index(new(){Op=op,Type=VT.I64,In=[I32()]},true,"canonical extension "+op);
foreach(long x in new long[]{0,1,int.MaxValue,uint.MaxValue,-1,int.MinValue})Index(K(x),true,"canonical literal "+x);
foreach(long x in new long[]{0x100000000L,0x100000001L,-0x100000000L,int.MinValue-1L})Index(K(x),false,"noncanonical high bits "+x);
Index(new(){Op=Op.Param,Type=VT.I64},false,"unproved register upper bits");
Index(new(){Op=Op.ZExt,Type=VT.I64,In=[new(){Op=Op.Param,Type=VT.I16}]},false,"narrow extension");
Index(new(){Op=Op.SExt,Type=VT.I64,In=[]},false,"missing operand");
Index(new(){Op=Op.Const,Type=VT.I64,Imm=0,Dead=true},false,"dead index");
Node Allocation()=>new(){Op=Op.Proj,Type=VT.I64,Imm=0,In=[new(){Op=Op.Call,Aux=new CallInfo{Target=0x2000,Indirect=false}}]};
var allocation=Allocation();
Check(Arm64ArrayAccessShape.FreshAllocation(allocation,_=>HelperKind.SzArrayNew),"exact fresh array result");positive++;
Check(!Arm64ArrayAccessShape.FreshAllocation(allocation,_=>HelperKind.ObjectNew),"wrong allocator");negative++;
foreach(var change in new Action<Node>[]{
 n=>n.Op=Op.Phi,n=>n.Imm=1,n=>n.Type=VT.I32,n=>n.Dead=true,n=>n.In=[],
 n=>n.In[0].Dead=true,n=>n.In[0].Op=Op.TailCall,n=>n.In[0].Aux=new CallInfo{Target=0x2000,Indirect=true}})
{var n=Allocation();change(n);Check(!Arm64ArrayAccessShape.FreshAllocation(n,_=>HelperKind.SzArrayNew),"fresh allocation rejection");negative++;}
int cases=0;
if(args.Length==1){
 using var json=JsonDocument.Parse(File.ReadAllText(args[0]));
 object?[] values=[null,new object(),new object()];
 foreach(var c in json.RootElement.GetProperty("cases").EnumerateArray()){
  object?[]? array=c.GetProperty("null_array").GetBoolean()?null:c.GetProperty("before").EnumerateArray().Select(x=>values[x.GetInt32()]).ToArray();
  string exception="";try{array![c.GetProperty("index").GetInt32()]=values[c.GetProperty("value").GetInt32()];}catch(Exception e){exception=e.GetType().Name;}
  Check(exception==c.GetProperty("exception").GetString(),"native exception "+cases);
  if(array!=null){int[] ids=array.Select(x=>Array.FindIndex(values,v=>ReferenceEquals(v,x))).ToArray();Check(ids.SequenceEqual(c.GetProperty("after").EnumerateArray().Select(x=>x.GetInt32())),"native array state "+cases);}
  cases++;
 }
 Check(cases>100,"complete original native matrix");
}
Console.WriteLine($"ARM64_OBJECT_ARRAY_STORE_PASS positive={positive} negative={negative} native_clr_cases={cases}");
