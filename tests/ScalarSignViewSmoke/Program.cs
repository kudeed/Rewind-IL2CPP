using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;

static void Check(bool ok,string name){if(!ok)throw new Exception(name);}
int negative=0,positive=0;long comparisons=0;
void Accept(string name,Fixture f)
{
 var result=ScalarSignView.Compare(f.Op,f.Register,f.Zero,f.Value,f.Layout,f.Sigs);
 Check(result is HCompare{Op:HCompareOp.Lt,Left:HField,Right:HConst{Value:0}},name+" typed sign field");
 var field=(HField)((HCompare)result!).Left;Check(ReferenceEquals(field.Field,f.Top)&&ReferenceEquals(((HLocal)field.Object!).Variable,((HLocal)f.Value).Variable),name+" original local and exact top");
 int bits=f.Layout.Size*8,topBits=f.Layout.Fields.Single(s=>ReferenceEquals(s.Field,f.Top)).Size*8;
 ulong[] low=[0,1,0x7FFFFFFF,0x80000000,0xFFFFFFFF,0x0123456789ABCDEF,0xFEDCBA9876543210,ulong.MaxValue];
 for(ulong high=0;high<65536;high++)foreach(ulong lower in low)
 {
  ulong raw=(lower&0x0000FFFFFFFFFFFFUL)|(high<<48);
  if(bits==32)raw=(raw>>32)&0xFFFFFFFF;
  ulong top=raw>>(bits-topBits);
  long signedTop=unchecked((long)(top<<(64-topBits)))>>(64-topBits);
  long signedWhole=bits==64?unchecked((long)raw):unchecked((int)raw);
  Check((signedTop<0)==(signedWhole<0),name+" original sign-bit semantics");comparisons++;
 }
 Check(!((HLocal)f.Value).Variable.AddressTaken,name+" no state mutation");positive++;
}
void Reject(string name,Action<Fixture> mutate){var f=new Fixture();mutate(f);Check(ScalarSignView.Compare(f.Op,f.Register,f.Zero,f.Value,f.Layout,f.Sigs)==null,name);negative++;}
Accept("two int32 fields in native64",new());
var unannotated=new Fixture();unannotated.Value.Type=null;Accept("declared local type",unannotated);
Accept("native64 high int16",new(8,2));Accept("native64 high int8",new(8,1));
Accept("native32 high int16",new(4,2));Accept("native32 high int8",new(4,1));
Reject("unsigned comparison",f=>f.Op=Op.CmpLtU);
Reject("less or equal uses low bits",f=>f.Op=Op.CmpLeS);
Reject("equality uses low bits",f=>f.Op=Op.CmpEq);
Reject("nonzero boundary",f=>f.Zero.Imm=1);
Reject("negative boundary",f=>f.Zero.Imm=-1);
Reject("nonconstant boundary",f=>f.Zero.Op=Op.Param);
Reject("dead boundary",f=>f.Zero.Dead=true);
Reject("annotated boundary",f=>f.Zero.Aux=new object());
Reject("malformed boundary",f=>f.Zero.In=[new Node{Op=Op.Const}]);
Reject("boundary width",f=>f.Zero.Type=VT.I32);
Reject("narrow register",f=>f.Register=VT.I16);
Reject("unknown layout",f=>f.Layout.Known=false);
Reject("partial register",f=>{f.Register=VT.I32;f.Zero.Type=VT.I32;});
Reject("oversized native register",f=>{f.Layout.Size=f.Layout.DataSize=4;});
Reject("trailing padding",f=>f.Layout.DataSize=7);
Reject("top padding",f=>f.Layout.Fields=f.Layout.Fields.Where(s=>!ReferenceEquals(s.Field,f.Top)).ToArray());
Reject("private sign field",f=>f.Top.Attrs=1);
Reject("static sign field",f=>f.Top.Attrs|=FieldDef.Static);
Reject("unsigned sign field",f=>f.RetypeTop(Il2CppTypeEnum.U4));
Reject("float sign field",f=>f.RetypeTop(Il2CppTypeEnum.R4));
Reject("reference sign field",f=>f.RetypeTop(Il2CppTypeEnum.Object));
Reject("boolean sign field",f=>f.RetypeTop(Il2CppTypeEnum.Boolean));
Reject("foreign owner",f=>f.Top.DeclaringType=new TypeDef());
Reject("declared field mismatch",f=>f.Top.Type=f.Sigs.Primitive(Il2CppTypeEnum.I8));
Reject("overlap",f=>f.Layout.Fields=[..f.Layout.Fields,new FieldSlot(f.Top,f.Top.Type,4,4)]);
Reject("offset overflow",f=>f.Layout.Fields[^1]=new FieldSlot(f.Top,f.Top.Type,int.MaxValue,4));
Reject("size overflow",f=>f.Layout.Fields[^1]=new FieldSlot(f.Top,f.Top.Type,4,int.MaxValue));
Reject("negative offset",f=>f.Layout.Fields[^1]=new FieldSlot(f.Top,f.Top.Type,-1,4));
Reject("wrong width",f=>f.Layout.Fields[^1]=new FieldSlot(f.Top,f.Top.Type,4,2));
Reject("effectful source",f=>f.Value=new HCall{Type=f.Owner.Sig,Method=new MethodDef{DeclaringType=f.Owner,ReturnType=f.Owner.Sig}});
Reject("aliased source",f=>((HLocal)f.Value).Variable.AddressTaken=true);
Reject("contradictory source view",f=>f.Value.Type=f.Sigs.Primitive(Il2CppTypeEnum.I8));
Reject("enum whole value",f=>f.Owner.IsEnum=true);
Reject("class whole value",f=>f.Owner.IsValueType=false);
Console.WriteLine($"ScalarSignViewSmoke passed: {positive} positive, {negative} negative, {comparisons} sign-bit differential cases");

sealed class Fixture
{
 public SigFactory Sigs=new();public TypeDef Owner;public FieldDef Top;public TypeLayout Layout;public HExpr Value;public Node Zero;public VT Register;public Op Op=Op.CmpLtS;
 public Fixture(int size=8,int topSize=4)
 {
  Owner=new TypeDef{Index=1,Name="Coordinates",Assembly=new AssemblyModel{Name="Test"},IsValueType=true};Owner.Sig=Sigs.TypeDef(Owner);
  TypeSig topType=Sigs.Primitive(topSize==4?Il2CppTypeEnum.I4:topSize==2?Il2CppTypeEnum.I2:Il2CppTypeEnum.I1);
  Top=new FieldDef{Name="high",DeclaringType=Owner,Type=topType,Attrs=6};var slots=new List<FieldSlot>();
  if(size-topSize==4){var type=Sigs.Primitive(Il2CppTypeEnum.I4);var low=new FieldDef{Name="low",DeclaringType=Owner,Type=type,Attrs=6};slots.Add(new FieldSlot(low,type,0,4));}
  else for(int i=0;i<size-topSize;i++){var type=Sigs.Primitive(Il2CppTypeEnum.U1);var f=new FieldDef{Name="b"+i,DeclaringType=Owner,Type=type,Attrs=6};slots.Add(new FieldSlot(f,type,i,1));}
  slots.Add(new FieldSlot(Top,topType,size-topSize,topSize));Layout=new TypeLayout{Size=size,DataSize=size,Align=1,Fields=slots.ToArray()};
  Value=new HLocal(new HVar{Name="value",Type=Owner.Sig}){Type=Owner.Sig};Register=size==8?VT.I64:VT.I32;Zero=new Node{Op=Op.Const,Type=Register};
 }
 public void RetypeTop(Il2CppTypeEnum kind){Top.Type=Sigs.Primitive(kind);int i=Array.FindIndex(Layout.Fields,s=>ReferenceEquals(s.Field,Top));Layout.Fields[i]=new FieldSlot(Top,Top.Type,Layout.Fields[i].Offset,Layout.Fields[i].Size);}
}
