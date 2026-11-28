using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;

static void Check(bool ok,string name){if(!ok)throw new Exception(name);}
static uint Evaluate(HExpr e,Dictionary<FieldDef,byte> bytes)=>e switch
{
 HConst c=>Convert.ToUInt32(c.Value),
 HField f=>bytes[f.Field],
 HConv {Kind:HConvKind.U4} c=>Evaluate(c.Operand,bytes),
 HConv {Kind:HConvKind.U2} c=>Evaluate(c.Operand,bytes)&0xFFFF,
 HBinary {Op:HBinaryOp.Or} b=>Evaluate(b.Left,bytes)|Evaluate(b.Right,bytes),
 HBinary {Op:HBinaryOp.Shl} b=>Evaluate(b.Left,bytes)<<(int)Evaluate(b.Right,bytes),
 _=>throw new Exception("Unexpected expression "+e.GetType().Name),
};
int negative=0;void Reject(string name,Action<Fixture> mutate,int offset=0,int size=2)
{var f=new Fixture();mutate(f);Check(ScalarByteSlice.Read(f.Value,f.Layout,offset,size,f.Sigs)==null,name);negative++;}
var exact=new Fixture();HExpr expr=ScalarByteSlice.Read(exact.Value,exact.Layout,0,2,exact.Sigs)??throw new Exception("read two bytes");
for(uint bits=0;bits<65536;bits++){exact.Bytes[exact.Fields[0]]=(byte)bits;exact.Bytes[exact.Fields[1]]=(byte)(bits>>8);Check(Evaluate(expr,exact.Bytes)==bits,"16bit exhaustive "+bits);}
var four=new Fixture();four.Layout.Size=8;four.Layout.DataSize=8;HExpr full=ScalarByteSlice.Read(four.Value,four.Layout,0,4,four.Sigs)??throw new Exception("read four bytes");
uint[] examples=[0,1,0xFF,0xFFFF,0x80000000,0xFFFFFFFF,0x01020304,0x89ABCDEF];
foreach(uint bits in examples){for(int i=0;i<4;i++)four.Bytes[four.Fields[i]]=(byte)(bits>>(i*8));Check(Evaluate(full,four.Bytes)==bits,"packed unsigned32");}
var high=new Fixture();high.Bytes[high.Fields[2]]=0xAB;high.Bytes[high.Fields[3]]=0xCD;Check(Evaluate(ScalarByteSlice.Read(high.Value,high.Layout,2,2,high.Sigs)!,high.Bytes)==0xCDAB,"shifted byte window");
var plain=new Fixture();plain.Value.Type=null;Check(ScalarByteSlice.Read(plain.Value,plain.Layout,0,2,plain.Sigs)!=null,"declared local type");
Reject("unknown layout",f=>f.Layout.Known=false);
Reject("padding",f=>f.Layout.Fields=f.Layout.Fields.Where(s=>!ReferenceEquals(s.Field,f.Fields[1])).ToArray());
Reject("ambiguous public byte",f=>{var d=new FieldDef{Name="alias",DeclaringType=f.Owner,Type=f.Byte,Attrs=6};f.Layout.Fields=[..f.Layout.Fields,new FieldSlot(d,f.Byte,0,1)];});
Reject("private selected byte",f=>f.Fields[1].Attrs=1);
Reject("signed byte",f=>{f.Fields[1].Type=f.Sigs.Primitive(Il2CppTypeEnum.I1);f.Layout.Fields[2]=new FieldSlot(f.Fields[1],f.Fields[1].Type,1,1);});
Reject("float overlay",f=>{var t=f.Sigs.Primitive(Il2CppTypeEnum.R4);f.Packed.Type=t;f.Layout.Fields[0]=new FieldSlot(f.Packed,t,0,4);});
Reject("reference overlay",f=>{var t=f.Sigs.Primitive(Il2CppTypeEnum.Object);f.Packed.Type=t;f.Layout.Fields[0]=new FieldSlot(f.Packed,t,0,4);});
Reject("static layout field",f=>f.Fields[0].Attrs|=FieldDef.Static);
Reject("foreign field owner",f=>f.Fields[0].DeclaringType=new TypeDef());
Reject("contradictory view",f=>f.Value.Type=f.Byte);
Reject("aliased local",f=>((HLocal)f.Value).Variable.AddressTaken=true);
Reject("side effect owner",f=>f.Value=new HCall{Type=f.Owner.Sig,Method=new MethodDef{DeclaringType=f.Owner,ReturnType=f.Owner.Sig}});
Reject("enum",f=>f.Owner.IsEnum=true);
Reject("oversized struct",f=>f.Layout.Size=16);
Reject("malformed outside slot",f=>f.Layout.Fields[0]=new FieldSlot(f.Packed,f.Packed.Type,2,4));
Reject("wrong declared field type",f=>f.Fields[0].Type=f.Sigs.Primitive(Il2CppTypeEnum.I4));
Reject("malformed overlay width",f=>f.Layout.Fields[0]=new FieldSlot(f.Packed,f.Packed.Type,0,2));
Reject("contradictory overlay type",f=>f.Packed.Type=f.Sigs.Primitive(Il2CppTypeEnum.I4));
Reject("negative offset",_=>{},-1,2);
Reject("outside window",_=>{},3,2);
Reject("offset overflow",_=>{},int.MaxValue,2);
Reject("unsupported bit width",_=>{},0,3);
Reject("whole-width four-byte struct",_=>{},0,4);
Reject("whole-width two-byte struct",f=>{f.Layout.Size=f.Layout.DataSize=2;f.Packed.Type=f.Sigs.Primitive(Il2CppTypeEnum.U2);f.Layout.Fields=[new FieldSlot(f.Packed,f.Packed.Type,0,2),new FieldSlot(f.Fields[0],f.Byte,0,1),new FieldSlot(f.Fields[1],f.Byte,1,1)];},0,2);
Console.WriteLine($"ScalarByteSliceSmoke passed: all65536 ushort patterns, 8 uint patterns, shifted and unannotated cases; {negative} negative guards");

sealed class Fixture
{
 public SigFactory Sigs=new();public TypeDef Owner;public TypeSig Byte;public FieldDef Packed;public FieldDef[] Fields;public TypeLayout Layout;public HExpr Value;public Dictionary<FieldDef,byte> Bytes=[];
 public Fixture()
 {
  var asm=new AssemblyModel{Name="Test"};Owner=new TypeDef{Index=1,Name="Packed",Assembly=asm,IsValueType=true};Owner.Sig=Sigs.TypeDef(Owner);Byte=Sigs.Primitive(Il2CppTypeEnum.U1);
  Packed=new FieldDef{Name="whole",DeclaringType=Owner,Type=Sigs.Primitive(Il2CppTypeEnum.U4),Attrs=1};
  Fields=Enumerable.Range(0,4).Select(i=>new FieldDef{Name="b"+i,DeclaringType=Owner,Type=Byte,Attrs=6}).ToArray();
  Layout=new TypeLayout{Size=4,DataSize=4,Align=1,Fields=[new FieldSlot(Packed,Packed.Type,0,4),..Fields.Select((f,i)=>new FieldSlot(f,Byte,i,1))]};
  Value=new HLocal(new HVar{Name="packed",Type=Owner.Sig}){Type=Owner.Sig};foreach(var f in Fields)Bytes[f]=0;
 }
}
