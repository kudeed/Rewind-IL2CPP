using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;
static void Check(bool ok,string name){if(!ok)throw new Exception(name);}
int positive=0,negative=0;
void Accept(string name,Fixture f){var old=f.Block.Nodes.ToArray();var p=f.Match();Check(p!=null&&p.Offset==f.Offset&&ReferenceEquals(p.Header,f.Header)&&ReferenceEquals(p.Type,f.Enum.Sig)&&ReferenceEquals(p.Consumer,f.Consumer),name);Check(old.SequenceEqual(f.Block.Nodes)&&old.All(n=>!n.Dead),name+" pure proof");positive++;}
void Reject(string name,Action<Fixture> mutate){var f=new Fixture();mutate(f);Check(f.Match()==null,name);negative++;}
Accept("int32 enum exact stack box",new());Accept("int64 enum",new(VT.I64,Il2CppTypeEnum.I8));Accept("uint16 enum",new(VT.I16,Il2CppTypeEnum.U2));Accept("sbyte enum",new(VT.I8,Il2CppTypeEnum.I1));
Reject("unknown initializer",f=>f.KnownInit=false);
Reject("unknown enum slot",f=>f.KnownSlot=false);
Reject("unknown consumer",f=>f.KnownConsumer=false);
Reject("not enum",f=>f.Enum.IsEnum=false);
Reject("reference class",f=>f.Enum.IsValueType=false);
Reject("bad underlying",f=>f.Enum.EnumUnderlyingType=f.Sigs.Primitive(Il2CppTypeEnum.R4));
Reject("nonzero methodinfo",f=>f.Consumer.In[1].Imm=1);
Reject("indirect init",f=>((CallInfo)f.Init.Aux!).Indirect=true);
Reject("noreturn init",f=>((CallInfo)f.Init.Aux!).NoReturn=true);
Reject("intrinsic init",f=>((CallInfo)f.Init.Aux!).Intrinsic="unknown");
Reject("indirect consumer",f=>((CallInfo)f.Consumer.Aux!).Indirect=true);
Reject("noreturn consumer",f=>((CallInfo)f.Consumer.Aux!).NoReturn=true);
Reject("tail consumer",f=>f.Consumer.Op=Op.TailCall);
Reject("narrow projection",f=>f.Projection.Type=VT.I32);
Reject("wrong return projection",f=>f.Projection.Imm=1);
Reject("projection annotation",f=>f.Projection.Aux=new object());
Reject("dead projection",f=>f.Projection.Dead=true);
Reject("foreign projection block",f=>f.Projection.Block=new Block());
Reject("foreign initializer block",f=>f.Init.Block=new Block());
Reject("cross-block header",f=>f.Header.Block=new Block());
Reject("protected block",f=>f.Block.Scope=0);
Reject("handler block",f=>f.Block.Scope=1);
Reject("header annotation",f=>f.Header.Aux=new object());
Reject("no payload",f=>f.Block.Nodes.Remove(f.Payload));
Reject("payload too wide",f=>f.Payload.In[1].Type=VT.I64);
Reject("float bits are not enum payload",f=>f.Payload.In[1].Type=VT.F32);
Reject("partial payload",f=>f.Payload.In[1].Type=VT.I16);
Reject("wrong payload offset",f=>f.Payload.In[0]=f.Address(f.Offset+24));
Reject("wrong marker offset",f=>f.Mark.In[0]=f.Address(f.Offset+16));
Reject("ordinary object mark",f=>f.Mark.In[1].Imm=0);
Reject("narrow mark",f=>f.Mark.In[1].Type=VT.I32);
Reject("wrong receiver",f=>f.Consumer.In[0]=f.Address(f.Offset+8));
Reject("slot not constant",f=>f.Init.In[0].Op=Op.Load);
Reject("slot narrow",f=>f.Init.In[0].Type=VT.I32);
Reject("slot unaligned",f=>f.Init.In[0].Imm++);
Reject("slot zero",f=>f.Init.In[0].Imm=0);
Reject("slot annotation",f=>f.Init.In[0].Aux=new object());
Reject("wrong stores order",f=>{int a=f.Block.Nodes.IndexOf(f.Payload),b=f.Block.Nodes.IndexOf(f.Header);(f.Block.Nodes[a],f.Block.Nodes[b])=(f.Block.Nodes[b],f.Block.Nodes[a]);});
Reject("intervening load",f=>f.BeforeConsumer(new Node{Op=Op.Load,Type=VT.I64,In=[f.Address(f.Offset)]}));
Reject("intervening branch",f=>f.BeforeConsumer(new Node{Op=Op.Branch,In=[Fixture.C(1)]}));
Reject("extra store",f=>f.BeforeConsumer(new Node{Op=Op.Store,In=[f.Address(f.Offset+24),Fixture.C(0)]}));
Reject("escaping address",f=>f.BeforeConsumer(new Node{Op=Op.Store,In=[f.Address(f.Offset+24),f.Address(f.Offset)]}));
Reject("extra call",f=>f.BeforeConsumer(new Node{Op=Op.Call,Aux=new CallInfo{Target=3}}));
Reject("arithmetic instead of address",f=>f.BeforeConsumer(new Node{Op=Op.Add,Type=VT.I64,In=[Fixture.C(1),Fixture.C(2)]}));
Reject("duplicate init ABI slot",f=>{f.Init.In=[f.Init.In[0],f.Init.In[0]];((CallInfo)f.Init.Aux!).Slots.Add(new(ArgSlotKind.IntReg,0));});
Reject("consumer ABI length mismatch",f=>((CallInfo)f.Consumer.Aux!).Slots.RemoveAt(1));
Reject("oversized window",f=>{for(int i=0;i<130;i++)f.BeforeConsumer(Fixture.C(i));});
Console.WriteLine($"ProjectedEnumBoxSmoke passed: {positive} positive, {negative} negative");
sealed class Fixture
{
 public SigFactory Sigs=new();public TypeDef Enum;public Block Block=new();public int Offset=-104;public Node Stack=new(){Op=Op.Param,Type=VT.I64,Imm=31};public Node Init,Projection,Payload,Header,Mark,Consumer;public bool KnownInit=true,KnownSlot=true,KnownConsumer=true;
 public Fixture(VT payload=VT.I32,Il2CppTypeEnum underlying=Il2CppTypeEnum.I4){Enum=new TypeDef{Index=1,Name="Choice",Assembly=new AssemblyModel{Name="Test"},IsValueType=true,IsEnum=true,EnumUnderlyingType=Sigs.Primitive(underlying)};Enum.Sig=Sigs.TypeDef(Enum);Init=new Node{Op=Op.Call,Aux=new CallInfo{Target=1,Slots=[new(ArgSlotKind.IntReg,0)]},In=[C(0x1000)]};Projection=new Node{Op=Op.Proj,Type=VT.I64,In=[Init]};Payload=new Node{Op=Op.Store,In=[Address(Offset+16),new Node{Op=Op.Param,Type=payload}]};Header=new Node{Op=Op.Store,In=[Address(Offset),Projection]};Mark=new Node{Op=Op.Store,In=[Address(Offset+8),C(-1)]};Consumer=new Node{Op=Op.Call,Aux=new CallInfo{Target=2,Slots=[new(ArgSlotKind.IntReg,0),new(ArgSlotKind.IntReg,1)]},In=[Address(Offset),C(0)]};Block.Nodes=[Init,Projection,Payload.In[0],Payload,Header.In[0],Header,Mark.In[0],Mark,Consumer.In[0],Consumer];foreach(var n in Block.Nodes)n.Block=Block;}
 public static Node C(long n)=>new(){Op=Op.Const,Type=VT.I64,Imm=n};
 public Node Address(int at)=>new(){Op=Op.Add,Type=VT.I64,In=[Stack,C(at)],Block=Block};
 public void BeforeConsumer(Node n){n.Block=Block;Block.Nodes.Insert(Block.Nodes.IndexOf(Consumer),n);}
 public ProjectedEnumBox? Match()=>ProjectedEnumBoxes.Match(Block,Header,Frame,t=>KnownInit&&t==1,s=>KnownSlot&&s==0x1000?Enum.Sig:null,t=>KnownConsumer&&t==2);
 private int? Frame(Node n)=>n.Op==Op.Add&&n.In.Length==2&&ReferenceEquals(n.In[0],Stack)&&n.In[1] is {Op:Op.Const,Type:VT.I64} c&&c.Imm is >=int.MinValue and <=int.MaxValue?(int)c.Imm:null;
}
