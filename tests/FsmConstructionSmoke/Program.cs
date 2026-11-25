using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;
using Rewind.Analysis.Ir;
using Rewind.Binary;
using System.Buffers.Binary;
static void Check(bool pass,string why){if(!pass)throw new Exception(why);}
var sf=new SigFactory();
var asm=new AssemblyModel{Name="Synthetic"};
var i=sf.Primitive(Il2CppTypeEnum.I4);
var o=sf.Primitive(Il2CppTypeEnum.Object);
var v=sf.Primitive(Il2CppTypeEnum.Void);
var bo=sf.Primitive(Il2CppTypeEnum.Boolean);
var owner=new TypeDef{Index=1,Name="Caller",Assembly=asm};owner.Sig=sf.TypeDef(owner);
var made=new TypeDef{Index=2,Name="Action",Assembly=asm};made.Sig=sf.TypeDef(made);
var f=new FieldDef{Name="state",DeclaringType=owner,Type=o};
var field=new FieldDef{Name="manager",DeclaringType=made,Type=o};
var caller=new MethodDef{Name=".ctor",DeclaringType=owner,ReturnType=v};
var ctor=new MethodDef{Name=".ctor",DeclaringType=made,ReturnType=v};
HLocal L(HVar x)=>new(x){Type=x.Type};
HField F(FieldDef d,HExpr x)=>new(){Field=d,Object=x,Type=d.Type};
var fresh=new HVar{Type=made.Sig};
var tmp=new HVar{Type=o};
List<HStmt> Site()=>[
 new HAssign(L(fresh),new HTypeExpr(HTypeOp.Allocate,made.Sig,null){Type=made.Sig}),
 new HAssign(F(field,L(fresh)),new HConst(null,o)),
 new HEval(new HCall{Method=ctor,This=L(fresh),Type=v}),
 new HAssign(L(tmp),F(f,new HArg(-1){Type=owner.Sig})),
 new HAssign(F(field,L(fresh)),new HArg(0){Type=o}),
 new HReturn(null)
];
Check(ScheduledConstructorReads.TryGather(caller,Site(),0,fresh,3,out var picked)&&picked.SequenceEqual(new[]{1,2,4}),"valid scheduled read");
var ctorTests=new (string,Action<List<HStmt>>)[]{
 ("before base",s=>{var a=s[3];s.RemoveAt(3);s.Insert(2,a);}),
 ("read fresh object",s=>((HField)((HAssign)s[3]).Value).Object=L(fresh)),
 ("different receiver",s=>((HField)((HAssign)s[3]).Value).Object=new HArg(0){Type=owner.Sig}),
 ("read used by store",s=>((HAssign)s[4]).Value=L(tmp)),
 ("call after read",s=>s[4]=new HEval(new HCall{Method=ctor,This=L(fresh)})),
 ("different object store",s=>((HField)((HAssign)s[4]).Target).Object=new HArg(-1){Type=owner.Sig}),
 ("address taken",s=>((HLocal)((HAssign)s[3]).Target).Variable=new HVar{Type=o,AddressTaken=true}),
 ("duplicate moved temp",s=>s.Insert(4,s[3])),
 ("missing constructor",s=>s[2]=new HAssign(F(field,L(fresh)),new HConst(null,o)))
};
foreach(var (name,mut) in ctorTests){var s=Site();mut(s);Check(!ScheduledConstructorReads.TryGather(caller,s,0,fresh,3,out _),"accepted "+name);}
Console.WriteLine("SCHEDULED_CTOR_READ_SMOKE_PASS positive=1 negative="+ctorTests.Length);
var core=new AssemblyModel{Name="mscorlib"};
var listDef=new TypeDef{Index=3,Name="List`1",Namespace="System.Collections.Generic",Assembly=core};
var gp=new GenericParam{Index=10,Position=0,OwnerType=listDef,Name="T"};listDef.GenericParameters=[gp];listDef.Sig=sf.TypeDef(listDef);
var tp=sf.GenericParam(gp);
var listType=sf.GenericInst(listDef,[o]);
var arrayType=sf.SzArray(o);
var items=new FieldDef{Name="_items",DeclaringType=listDef,Type=sf.SzArray(tp)};
var version=new FieldDef{Name="_version",DeclaringType=listDef,Type=i};
var sz=new FieldDef{Name="_size",DeclaringType=listDef,Type=i};
MethodDef Method(string name,TypeSig ret,params TypeSig[] args)=>new(){Name=name,DeclaringType=listDef,ReturnType=ret,Parameters=args.Select(x=>new ParamDef{Type=x}).ToArray()};
var add=Method("Add",v,tp);var resize=Method("AddWithResize",v,tp);var count=Method("get_Count",i);
listDef.Methods=[add,resize,count];
(HMethod h,HBlock block,HBlock fast,HBlock slow,HVar arr,HVar n) Fixture(bool ints=false,TypeSig? custom=null){
 var element=custom??(ints?i:o);
 var listType=sf.GenericInst(listDef,[element]);
 var arrayType=sf.SzArray(element);
 var h=new HMethod{Method=new MethodDef{Name="Caller",DeclaringType=owner,ReturnType=v}};
 var l=h.NewLocal(listType);var arr=h.NewLocal(arrayType);var n=h.NewLocal(i);
 HField LF(FieldDef fd)=>new(){Field=fd,Object=L(l),DeclaringType=listType,Type=fd==items?arrayType:i};
 var item=new HArg(0){Type=element};var block=new HBlock{Id=0};var fast=new HBlock{Id=1};var slow=new HBlock{Id=2};
 HBinary Inc(HExpr x)=>new(HBinaryOp.Add,x,new HConst(1,i)){Type=i};
 block.Statements=[new HAssign(L(l),new HArg(1){Type=listType}),
 new HAssign(L(arr),LF(items)),new HAssign(LF(version),Inc(LF(version))),
 new HAssign(L(n),new HCall{Method=count,This=L(l),DeclaringType=listType,Type=i}),
 new HBranch(new HCompare(HCompareOp.LeUn,new HArrayLength(L(arr)){Type=i},L(n)){Type=bo},slow,fast)];
 fast.Statements=[new HAssign(LF(sz),Inc(L(n))),new HAssign(new HElement{Array=L(arr),Index=L(n),Type=element},item),new HReturn(null)];
 slow.Statements=[new HEval(new HCall{Method=resize,This=L(l),DeclaringType=listType,Arguments=[item],Type=v}),new HReturn(null)];
 h.Blocks=[block,fast,slow];return(h,block,fast,slow,arr,n);
}
var yes=Fixture();Check(ListAppendFolding.TryFold(yes.h,sf,yes.block)&&yes.h.Blocks.Count==1&&yes.block.Statements[1] is HEval{Expression:HCall c}&&ReferenceEquals(c.Method,add),"valid list diamond");
var listTests=new (string,Action<(HMethod h,HBlock block,HBlock fast,HBlock slow,HVar arr,HVar n)> )[]{
 ("wrong version",x=>((HBinary)((HAssign)x.block.Statements[2]).Value).Right=new HConst(2,i)),
 ("wrong increment",x=>((HBinary)((HAssign)x.fast.Statements[0]).Value).Right=new HConst(2,i)),
 ("wrong item",x=>((HAssign)x.fast.Statements[1]).Value=new HArg(3){Type=o}),
 ("wrong branch",x=>((HCompare)((HBranch)x.block.Statements[4]).Condition).Op=HCompareOp.LtUn),
 ("extra array use",x=>x.block.Statements.Insert(0,new HEval(L(x.arr)))),
 ("extra incoming edge",x=>x.h.Blocks.Add(new HBlock{Id=3,Statements=[new HJump(x.fast)]})),
 ("extra slow effect",x=>x.slow.Statements.Insert(0,new HEval(new HConst(0,i)))),
 ("address taken",x=>x.n.AddressTaken=true),
 ("exception scope",x=>x.fast.Scope=0),
 ("wrong resize call",x=>((HCall)((HEval)x.slow.Statements[0]).Expression).Method=add)
};
foreach(var (name,mut) in listTests){var x=Fixture();mut(x);Check(!ListAppendFolding.TryFold(x.h,sf,x.block),"accepted "+name);}
Console.WriteLine("LIST_APPEND_SMOKE_PASS positive=1 negative="+listTests.Length);

var ints=Fixture(true);
Check(ListAppendFolding.TryFold(ints.h,sf,ints.block),"int list append");
var joined=Fixture(true);
joined.h.Method.ReturnType=i;
var join=new HBlock{Id=3,Statements=[new HReturn(new HConst(3,i))]};
joined.h.Blocks.Add(join);
joined.fast.Statements[2]=new HJump(join);joined.slow.Statements[1]=new HJump(join);
Check(ListAppendFolding.TryFold(joined.h,sf,joined.block)&&joined.h.Blocks.Count==2&&joined.block.Statements.Last() is HJump j&&j.Target==join,"common successor");
var computed=Fixture(true);
var cvar=computed.h.NewLocal(i);
var calculation=new HAssign(L(cvar),new HBinary(HBinaryOp.Add,new HArg(0){Type=i},new HConst(-1,i)){Type=i});
computed.block.Statements.Insert(4,calculation);
((HAssign)computed.fast.Statements[1]).Value=L(cvar);
((HCall)((HEval)computed.slow.Statements[0]).Expression).Arguments[0]=L(cvar);
Check(ListAppendFolding.TryFold(computed.h,sf,computed.block)&&computed.block.Statements[1]==calculation,"scheduled integer computation");
var mixed=Fixture(true);
var exit=new HBlock{Id=3,Statements=[new HReturn(null)]};
mixed.h.Blocks.Add(exit);mixed.fast.Statements[2]=new HJump(exit);
Check(ListAppendFolding.TryFold(mixed.h,sf,mixed.block),"mixed terminal exit");
var badJoin=Fixture(true);
var b1=new HBlock{Id=3,Statements=[new HReturn(new HConst(1,i))]};
var b2=new HBlock{Id=4,Statements=[new HReturn(new HConst(2,i))]};
badJoin.h.Method.ReturnType=i;badJoin.h.Blocks.Add(b1);badJoin.h.Blocks.Add(b2);
badJoin.fast.Statements[2]=new HJump(b1);badJoin.slow.Statements[1]=new HJump(b2);
Check(!ListAppendFolding.TryFold(badJoin.h,sf,badJoin.block),"different continuations accepted");
var badCompute=Fixture(true);
var cv=badCompute.h.NewLocal(i);
badCompute.block.Statements.Insert(4,new HAssign(L(cv),new HCall{Method=count,This=new HArg(1){Type=listType},Type=i}));
Check(!ListAppendFolding.TryFold(badCompute.h,sf,badCompute.block),"side effect calculation accepted");
var badDependency=Fixture(true);
var dep=badDependency.h.NewLocal(i);
badDependency.block.Statements.Insert(4,new HAssign(L(dep),L(badDependency.n)));
Check(!ListAppendFolding.TryFold(badDependency.h,sf,badDependency.block),"private count use accepted");
Console.WriteLine("LIST_APPEND_EXTENDED_SMOKE_PASS positive=4 negative=3");

var phi=Fixture(true);
var input=phi.h.NewLocal(i);var result=phi.h.NewLocal(i);
var phiRead=new HLocal(input); // authoritative declared type, no expression annotation
var phiMath=new HAssign(L(result),new HBinary(HBinaryOp.Add,phiRead,new HConst(-1,i)){Type=i});
phi.block.Statements.Insert(4,phiMath);
var phiItem=new HLocal(result);
((HAssign)phi.fast.Statements[1]).Value=phiItem;
((HCall)((HEval)phi.slow.Statements[0]).Expression).Arguments[0]=phiItem;
Check(ListAppendFolding.TryFold(phi.h,sf,phi.block),"typed merge local");
var conflict=Fixture(true);var local=conflict.h.NewLocal(i);var output=conflict.h.NewLocal(i);
conflict.block.Statements.Insert(4,new HAssign(L(output),new HBinary(HBinaryOp.Add,new HLocal(local){Type=o},new HConst(-1,i)){Type=i}));
Check(!ListAppendFolding.TryFold(conflict.h,sf,conflict.block),"conflicting annotation accepted");
Console.WriteLine("LIST_APPEND_MERGE_TYPE_SMOKE_PASS positive=1 negative=1");

// The declared Unity value layout and actual ARM64 constructor are both
// required before allowing struct computations inside a list diamond.
var unity=new AssemblyModel{Name="UnityEngine.CoreModule"};
var ft=sf.Primitive(Il2CppTypeEnum.R4);
var vec=new TypeDef{Index=100,Name="Vector2",Namespace="UnityEngine",Assembly=unity,IsValueType=true,
 Flags=TypeDef.SequentialLayout,Sizes=new RawTypeSizes(24,8,0,0)};
vec.Sig=sf.TypeDef(vec);
vec.Fields=[new FieldDef{Name="x",DeclaringType=vec,Type=ft,Offset=16,Attrs=6},new FieldDef{Name="y",DeclaringType=vec,Type=ft,Offset=20,Attrs=6}];
var vc=new MethodDef{Name=".ctor",DeclaringType=vec,ReturnType=v,Address=0x1000,Flags=6,Parameters=[new ParamDef{Type=ft},new ParamDef{Type=ft}]};
var native=new VectorImage(0x2D000400u,0xD65F03C0u);
Check(VectorListValue.Dimension(vec.Sig,16)==2&&VectorListValue.ConstructorShape(native,vc,vec.Sig),"vector layout/constructor proof");
var vectorCopy=Fixture(custom:vec.Sig);
Check(ListAppendFolding.TryFold(vectorCopy.h,sf,vectorCopy.block,native),"vector argument append");
HNewObject NewVector(float x,float y)=>new(){Constructor=vc,Type=vec.Sig,Arguments=[new HConst(x,ft),new HConst(y,ft)]};
var vectorCtor=Fixture(custom:vec.Sig);
((HAssign)vectorCtor.fast.Statements[1]).Value=NewVector(1.25f,-2.5f);
((HCall)((HEval)vectorCtor.slow.Statements[0]).Expression).Arguments[0]=NewVector(1.25f,-2.5f);
Check(ListAppendFolding.TryFold(vectorCtor.h,sf,vectorCtor.block,native),"same proven vector constructor");
var vectorMismatch=Fixture(custom:vec.Sig);
((HAssign)vectorMismatch.fast.Statements[1]).Value=NewVector(1,2);
((HCall)((HEval)vectorMismatch.slow.Statements[0]).Expression).Arguments[0]=NewVector(1,3);
Check(!ListAppendFolding.TryFold(vectorMismatch.h,sf,vectorMismatch.block,native),"different constructor arguments");
var vectorBadCtor=Fixture(custom:vec.Sig);
((HAssign)vectorBadCtor.fast.Statements[1]).Value=NewVector(1,2);
((HCall)((HEval)vectorBadCtor.slow.Statements[0]).Expression).Arguments[0]=NewVector(1,2);
Check(!ListAppendFolding.TryFold(vectorBadCtor.h,sf,vectorBadCtor.block,new VectorImage(0x2D000401u,0xD65F03C0u)),"wrong native constructor");
vec.Fields[1].Offset=24;
var badLayout=Fixture(custom:vec.Sig);
Check(!ListAppendFolding.TryFold(badLayout.h,sf,badLayout.block,native),"wrong field offset");
vec.Fields[1].Offset=20;
vec.Fields[0].Attrs=1;
Check(VectorListValue.Dimension(vec.Sig,16)==0,"private channel");
vec.Fields[0].Attrs=6;
Check(VectorListValue.Dimension(vec.Sig,8)==0,"wrong ABI header");
var signZero=Fixture(custom:vec.Sig);
((HAssign)signZero.fast.Statements[1]).Value=NewVector(0f,1);
((HCall)((HEval)signZero.slow.Statements[0]).Expression).Arguments[0]=NewVector(BitConverter.UInt32BitsToSingle(0x80000000),1);
Check(!ListAppendFolding.TryFold(signZero.h,sf,signZero.block,native),"different signed zero accepted");
var nan=Fixture(custom:vec.Sig);
((HAssign)nan.fast.Statements[1]).Value=NewVector(BitConverter.UInt32BitsToSingle(0x7fc00001),1);
((HCall)((HEval)nan.slow.Statements[0]).Expression).Arguments[0]=NewVector(BitConverter.UInt32BitsToSingle(0x7fc00002),1);
Check(!ListAppendFolding.TryFold(nan.h,sf,nan.block,native),"different NaN payload accepted");
Console.WriteLine("VECTOR_LIST_SMOKE_PASS positive=3 negative=7");

// A value local may carry a stale address-taken marker, but not any
// remaining actual pointer or byref use. Validate the whole HIR use proof.
static void SetCopy24((HMethod h,HBlock block,HBlock fast,HBlock slow,HVar arr,HVar n) f,HVar v)
{
 var item=new HLocal(v){Type=v.Type};
 ((HAssign)f.fast.Statements[1]).Value=item;
 ((HCall)((HEval)f.slow.Statements[0]).Expression).Arguments[0]=item;
}
var cp24=Fixture(custom:vec.Sig);var vv24=cp24.h.NewLocal(vec.Sig);vv24.AddressTaken=true;SetCopy24(cp24,vv24);
cp24.block.Statements.Insert(0,new HAssign(L(vv24),new HArg(0){Type=vec.Sig}));
Check(VectorListValue.ValueOnlyLocal(cp24.h,sf,vv24)&&ListAppendFolding.TryFold(cp24.h,sf,cp24.block,native),"value-only vector copy");
var copyNeg24=new Action<(HMethod h,HBlock block,HBlock fast,HBlock slow,HVar arr,HVar n),HVar>[]{
 (f,x)=>f.block.Statements.Insert(0,new HEval(new HAddressOf(L(x)))),
 (f,x)=>f.block.Statements.Insert(0,new HEval(new HConv(HConvKind.I8,L(x)))),
 (f,x)=>f.h.Problems.Add("opaque native operation"),
 (f,x)=>f.block.Statements.Insert(0,new HEval(new HCall{Method=vc,This=L(x),Arguments=[new HConst(1f,ft),new HConst(2f,ft)]})),
 (f,x)=>f.block.Statements.Insert(0,new HEval(new HCall{Method=new MethodDef{Name="Escape",DeclaringType=owner,ReturnType=v,Parameters=[new ParamDef{Type=sf.ByRef(vec.Sig)}]},Arguments=[L(x)]}))
};
foreach(var mut24 in copyNeg24){var f24=Fixture(custom:vec.Sig);var x24=f24.h.NewLocal(vec.Sig);x24.AddressTaken=true;SetCopy24(f24,x24);mut24(f24,x24);Check(!ListAppendFolding.TryFold(f24.h,sf,f24.block,native),"unsafe vector copy accepted");}
Console.WriteLine("VECTOR_VALUE_COPY_SMOKE_PASS positive=1 negative="+copyNeg24.Length);

// Independent branch/edge shape checks used before a native null guard is
// discarded. These tests do not substitute for the full metadata/callee proof.
var pointer=new Node{Op=Op.Load,Type=VT.I64};
var zero=new Node{Op=Op.Const,Type=VT.I64,Imm=0};
var equal=new Node{Op=Op.CmpEq,Type=VT.I1,In=[pointer,zero]};
var notEqual=new Node{Op=Op.CmpNe,Type=VT.I1,In=[zero,pointer]};
Check(Normalizer.NullGuardValue(equal,0)==pointer&&Normalizer.NullGuardValue(notEqual,1)==pointer,"null guard polarity");
Check(Normalizer.NullGuardValue(equal,1)==null&&Normalizer.NullGuardValue(notEqual,0)==null,"inverted guard rejected");
var narrow=new Node{Op=Op.Load,Type=VT.I32};
Check(Normalizer.NullGuardValue(new Node{Op=Op.CmpEq,In=[narrow,zero]},0)==null,"narrow guard");
var guard=new Block();var next=new Block();var direct=new Node{Op=Op.Call,Aux=new CallInfo{Target=0x1000}};
next.Preds=[guard];next.Nodes=[new Node{Op=Op.Add},direct];
Check(Normalizer.FirstDirectCall(guard,next)==direct,"unique continuation");
next.Preds.Add(new Block());Check(Normalizer.FirstDirectCall(guard,next)==null,"alternate entry");next.Preds.RemoveAt(1);
next.Nodes.Insert(0,new Node{Op=Op.Store});Check(Normalizer.FirstDirectCall(guard,next)==null,"effect before call");next.Nodes.RemoveAt(0);
((CallInfo)direct.Aux!).Indirect=true;Check(Normalizer.FirstDirectCall(guard,next)==null,"indirect call");((CallInfo)direct.Aux!).Indirect=false;
next.Scope=0;Check(Normalizer.FirstDirectCall(guard,next)==null,"exception scope");
Console.WriteLine("GUARDED_RECEIVER_SHAPE_PASS positive=3 negative=7");

// Receiver proof checks: no arbitrary heap reads, writes or unaligned stack locations.
var sp=new Node{Op=Op.Param,Type=VT.I64};
Node Const19(long n)=>new(){Op=Op.Const,Type=VT.I64,Imm=n};
Node Add19(Node a,Node b)=>new(){Op=Op.Add,Type=VT.I64,In=[a,b]};
Node Load19(Node a,VT t=VT.I64)=>new(){Op=Op.Load,Type=t,In=[a]};
var restore=Load19(Add19(sp,Const19(-16)));
var guard19=new Block();var tail19=new Block{Preds=[guard19]};
var tailCall19=new Node{Op=Op.TailCall,Aux=new CallInfo{Target=0x1000}};
tail19.Nodes=[restore,tailCall19];
Check(Normalizer.FirstDirectCall(guard19,tail19,sp)==tailCall19,"tail restore");
tail19.Nodes[0]=Load19(Add19(sp,Const19(-9)));
Check(Normalizer.FirstDirectCall(guard19,tail19,sp)==null,"unaligned stack read");
tail19.Nodes[0]=Load19(Add19(pointer,Const19(-16)));
Check(Normalizer.FirstDirectCall(guard19,tail19,sp)==null,"heap load");
tail19.Nodes[0]=restore;tail19.Nodes[1]=direct;
Check(Normalizer.FirstDirectCall(guard19,tail19,sp)==null,"non-tail restore");
var own19=Load19(Add19(pointer,Const19(32)));
var arr19=Load19(Add19(own19,Const19(120)));
var index19=new Node{Op=Op.Shl,Type=VT.I64,In=[zero,Const19(2)]};
var element19=Load19(Add19(Add19(arr19,index19),Const19(32)),VT.I32);
Check(Normalizer.ArrayArgumentOwner(element19,32,out var ar19,out var off19)==own19&&ar19==arr19&&off19==120,"array origin");
Check(Normalizer.IsThisFieldValue(own19,pointer,32),"owner field");
Check(!Normalizer.IsThisFieldValue(own19,pointer,40),"wrong owner offset");
Check(Normalizer.ArrayArgumentOwner(element19,24,out _,out _)==null,"wrong array header");
index19.In[1]=Const19(3);
Check(Normalizer.ArrayArgumentOwner(element19,32,out _,out _)==null,"wrong element scale");
Console.WriteLine("V19_RECEIVER_SHAPE_PASS positive=3 negative=6");
uint[] getter19=[0xf9401808,0xb4000068,0xb9402100,0xd65f03c0,0xf81f0ffe,0x94000002];
Check(Arm64ChainedGetter.Matches(getter19,48,32,0x1000,a=>a==0x101c),"chain getter");
Check(!Arm64ChainedGetter.Matches(getter19,40,32,0x1000,_=>true),"wrong first offset");
Check(!Arm64ChainedGetter.Matches(getter19,48,36,0x1000,_=>true),"wrong second offset");
Check(!Arm64ChainedGetter.Matches(getter19,48,32,0x1000,_=>false),"wrong helper");
getter19[1]^=1;
Check(!Arm64ChainedGetter.Matches(getter19,48,32,0x1000,_=>true),"wrong guard register");
Console.WriteLine("V19_CHAIN_GETTER_SHAPE_PASS positive=1 negative=4");

// Own MethodInfo klass offset and exact TBZ/TBNZ bit-zero shape.
var mi22=new Node{Op=Op.Param,Type=VT.I64};
var other22=new Node{Op=Op.Param,Type=VT.I64};
Node C22(long x)=>new(){Op=Op.Const,Type=VT.I64,Imm=x};
Node N22(Op op,params Node[] xs)=>new(){Op=op,Type=VT.I64,In=xs};
Check(Normalizer.OwnMethodKlassLoad(N22(Op.Load,N22(Op.Add,mi22,C22(32))),mi22),"klass positive");
Check(!Normalizer.OwnMethodKlassLoad(N22(Op.Load,N22(Op.Add,other22,C22(32))),mi22),"wrong info");
Check(!Normalizer.OwnMethodKlassLoad(N22(Op.Load,N22(Op.Add,mi22,C22(40))),mi22),"wrong offset");
Check(Normalizer.TryClassInitBranch(0x37000048,0x1000,out var slow22)&&slow22==0x1004,"tbnz");
Check(Normalizer.TryClassInitBranch(0x36000048,0x1000,out slow22)&&slow22==0x1008,"tbz");
Check(!Normalizer.TryClassInitBranch(0x36080048,0x1000,out slow22),"wrong bit");
Check(!Normalizer.TryClassInitBranch(0xb4000048,0x1000,out slow22),"cbz rejected");
Console.WriteLine("METHOD_KLASS_SHAPE_SMOKE_PASS positive=3 negative=4");

// Exact same-base indexed-address merge: no other effect or pointer uses.
static (Block B,Node Phi,Node Load,Node Shift,Dictionary<Node,List<Node>> Uses) IndexedFixture22(){
 Node C(long n)=>new(){Op=Op.Const,Type=VT.I64,Imm=n};
 Node N(Op op,params Node[] xs)=>new(){Op=op,Type=VT.I64,In=xs};
 var b=new Block();b.Preds=[new Block(),new Block()];
 var root=N(Op.Param);var sh=N(Op.Shl,N(Op.Param),C(3));var add=N(Op.Add,root,sh);
 var phi=N(Op.Phi,root,add);phi.Block=b;b.Phis=[phi];
 var addr=N(Op.Add,phi,C(32));addr.Block=b;var load=N(Op.Load,addr);load.Block=b;
 b.Nodes=[addr,load,N(Op.Jump)];
 return(b,phi,load,sh,new(){[phi]=[addr],[addr]=[load]});
}
var ix22=IndexedFixture22();Check(Rewind.Analysis.Passes.IndexedBaseMerges.Candidate(ix22.B,ix22.Phi,ix22.Uses),"indexed positive");
var neg22=new Action<(Block B,Node Phi,Node Load,Node Shift,Dictionary<Node,List<Node>> Uses)>[]{
 f=>f.Phi.In[0]=new Node{Op=Op.Param,Type=VT.I64},
 f=>f.Shift.In[1].Imm=2,
 f=>f.Uses[f.Phi].Add(new Node{Op=Op.Load,Type=VT.I64}),
 f=>f.Load.Type=VT.I32,
 f=>f.B.Scope=1,
 f=>f.B.Nodes.Insert(0,new Node{Op=Op.Store,Type=VT.I64}),
 f=>f.B.Preds.Add(new Block()),
 f=>f.Load.In[0].In[1].Imm=24
};
foreach(var mutation in neg22){var fixture22=IndexedFixture22();mutation(fixture22);Check(!Rewind.Analysis.Passes.IndexedBaseMerges.Candidate(fixture22.B,fixture22.Phi,fixture22.Uses),"unsafe indexed merge accepted");}
Console.WriteLine("INDEXED_BASE_SMOKE_PASS positive=1 negative="+neg22.Length);

// Different loaded arrays merge with indexed elements from other arrays.
static (Block B,Node Phi,Node Load,Node Shift,Dictionary<Node,List<Node>> Uses) MixedIndexedFixture28(){
 var f=IndexedFixture22();
 Node C(long n)=>new(){Op=Op.Const,Type=VT.I64,Imm=n};
 Node N(Op op,params Node[] xs)=>new(){Op=op,Type=VT.I64,In=xs};
 Node Loaded()=>N(Op.Load,N(Op.Param));
 var ix=N(Op.SExt,new Node{Op=Op.Param,Type=VT.I32});
 var joined=N(Op.Phi,Enumerable.Range(0,7).Select(_=>Loaded()).ToArray());
 var a=N(Op.Add,joined,N(Op.Shl,ix,C(3)));
 var c=N(Op.Add,Loaded(),N(Op.Shl,ix,C(3)));
 f.B.Preds.Add(new Block());f.Phi.In=[a,Loaded(),c];
 return f;
}
var mix28=MixedIndexedFixture28();Check(Rewind.Analysis.Passes.IndexedBaseMerges.Candidate(mix28.B,mix28.Phi,mix28.Uses),"mixed indexed positive");
var neg28=new Action<(Block B,Node Phi,Node Load,Node Shift,Dictionary<Node,List<Node>> Uses)>[]{
 f=>f.Phi.In[0].In[0].In[0]=new Node{Op=Op.Param,Type=VT.I64},
 f=>f.Phi.In[0].In[1].In[1].Imm=2,
 f=>f.Phi.In[2].In[1].In[0].In[0].Type=VT.I64,
 f=>f.Phi.In[1]=f.Phi.In[0],
 f=>f.Uses[f.Phi].Add(new Node{Op=Op.Load,Type=VT.I64}),
 f=>f.Load.In[0].In[1].Imm=24,
 f=>f.B.Nodes.Insert(0,new Node{Op=Op.Store,Type=VT.I64}),
};
foreach(var mutation in neg28){var mix=MixedIndexedFixture28();mutation(mix);Check(!Rewind.Analysis.Passes.IndexedBaseMerges.Candidate(mix.B,mix.Phi,mix.Uses),"unsafe mixed indexed merge accepted");}
Console.WriteLine("MIXED_INDEXED_BASE_SMOKE_PASS positive=1 negative="+neg28.Length);

// Explicit LSDA no-pad evidence is required, not merely a missing entry.
static (Function Fn,Block Gate,Block Body,Node Call,Node Park,List<CallSite> Sites) TryPrefix23()
{
 var fn=new Function{Regs=RegisterModel.Arm64,Address=0x1000,End=0x1100};
 var sp=fn.NewNode(Op.Param,VT.I64,null);fn.Params[fn.Regs.StackPointer]=sp;
 var gate=new Block{Scope=-1};var handler=new Block{Scope=1};var body=new Block{Scope=0};
 fn.TryRegions.Add(new TryRegionInfo{Index=0,Outer=-1});
 gate.Succs=[handler,body];handler.Preds=[gate];body.Preds=[gate];fn.Blocks=[gate,body,handler];
 var raised=fn.NewNode(Op.Idiom,VT.I1,gate);raised.Imm=(long)IdiomKind.TryEntry;raised.Aux=0;
 gate.Nodes=[raised,fn.NewNode(Op.Branch,VT.None,gate,raised)];
 Node Const(long k){var n=fn.NewNode(Op.Const,VT.I64,null);n.Imm=k;return n;}
 Node At(int off)=>fn.NewNode(Op.Add,VT.I64,body,sp,Const(off));
 var call=fn.NewNode(Op.Call,VT.None,body);call.Aux=new CallInfo{Target=0x2000};call.Addr=0x1000;
 var proj=fn.NewNode(Op.Proj,VT.I64,body,call);proj.Imm=0;
 var local=At(-32);var slot=At(-48);
 var init=fn.NewNode(Op.Store,VT.None,body,local,proj);init.Addr=0x1004;
 var park=fn.NewNode(Op.Store,VT.None,body,slot,local);park.Addr=0x1008;
 var protectedCall=fn.NewNode(Op.Call,VT.None,body);protectedCall.Aux=new CallInfo{Target=0x3000};protectedCall.Addr=0x100c;
 body.Nodes=[call,proj,local,init,slot,park,protectedCall,fn.NewNode(Op.Return,VT.None,body)];
 handler.Nodes=[fn.NewNode(Op.Return,VT.None,handler)];
 return(fn,gate,body,call,park,[new CallSite(0x1000,0x100c,0,0),new CallSite(0x100c,0x1010,0x1080,1,1)]);
}
var good23=TryPrefix23();
Check(Rewind.Analysis.Passes.NativeTryPrefix.Run(good23.Fn,good23.Sites)==6,"LSDA prefix positive");
Check(good23.Gate.Nodes.Contains(good23.Call)&&good23.Call.Block==good23.Gate&&good23.Park.Block==good23.Gate&&
 good23.Body.Nodes.Count==2&&good23.Body.Nodes[0].Addr==0x100c&&good23.Gate.Terminator?.Op==Op.Branch,"LSDA prefix ordering and ownership");
var neg23=new Action<(Function Fn,Block Gate,Block Body,Node Call,Node Park,List<CallSite> Sites)>[]{
 x=>x.Sites.RemoveAt(0),
 x=>x.Sites[0]=new CallSite(0x1000,0x100c,0x1080,1,1),
 x=>x.Sites[0]=new CallSite(0x1000,0x100c,0x1080,0),
 x=>x.Sites.Add(new CallSite(0x1000,0x1004,0,0)),
 x=>((CallInfo)x.Call.Aux!).Indirect=true,
 x=>((CallInfo)x.Call.Aux!).NoReturn=true,
 x=>x.Call.Addr=0,
 x=>x.Park.Addr=0x100c,
 x=>x.Park.In[1]=new Node{Op=Op.Const,Type=VT.I64},
 x=>x.Body.Preds.Add(new Block()),
 x=>x.Fn.TryRegions.Add(new TryRegionInfo{Index=1}),
 x=>x.Gate.Scope=1,
 x=>x.Body.Phis.Add(new Node{Op=Op.Phi,Type=VT.I64}),
 x=>x.Body.Nodes.Insert(1,new Node{Op=Op.Store,Type=VT.None,Addr=0x1004,In=[new Node{Op=Op.Param,Type=VT.I64},new Node{Op=Op.Const,Type=VT.I64}]})
};
foreach(var mutate23 in neg23){var fixture23=TryPrefix23();mutate23(fixture23);var before23=fixture23.Body.Nodes.ToArray();Check(Rewind.Analysis.Passes.NativeTryPrefix.Run(fixture23.Fn,fixture23.Sites)==0&&fixture23.Body.Nodes.SequenceEqual(before23),"unsafe prefix accepted");}
Console.WriteLine("NATIVE_TRY_PREFIX_SMOKE_PASS positive=1 negative="+neg23.Length);

Check(HirBuilder.NullableFlagGetterCode(new VectorImage(0x39400000,0xd65f03c0),0x1000),"nullable getter");
Check(!HirBuilder.NullableFlagGetterCode(new VectorImage(0x39400400,0xd65f03c0),0x1000),"wrong flag offset");
Check(!HirBuilder.NullableFlagGetterCode(new VectorImage(0xb9400000,0xd65f03c0),0x1000),"wrong flag width");
Check(!HirBuilder.NullableFlagGetterCode(new VectorImage(0x39400000,0xd61f0020),0x1000),"wrong getter exit");
Check(!HirBuilder.NullableFlagGetterCode(new VectorImage(0x39400000),0x1000),"truncated getter");
Console.WriteLine("NULLABLE_FLAG_GETTER_SMOKE_PASS positive=1 negative=4");

// Delayed constant folding may leave page+offset and trunc(1) in SSA.
var flag25=N22(Op.Load,N22(Op.Add,C22(0x5502000),C22(0xa6d)));flag25.Type=VT.I8;
var z25=N22(Op.ZExt,flag25);z25.Type=VT.I32;
var cond25=N22(Op.CmpNe,z25,C22(0));cond25.Type=VT.I1;
var one25=N22(Op.Trunc,C22(1));one25.Type=VT.I8;
var store25=N22(Op.Store,N22(Op.Add,C22(0x5502000),C22(0xa6d)),one25);
Check(Normalizer.FlagCondition(cond25,out var load25,out var truth25)&&load25==flag25&&truth25,"exact metadata branch");
Check(Normalizer.FlagStore(store25,0x5502a6d),"late constant byte store");
cond25.Op=Op.CmpEq;
Check(Normalizer.FlagCondition(cond25,out load25,out truth25)&&load25==flag25&&!truth25,"inverted metadata branch");
cond25.Op=Op.CmpLtU;Check(!Normalizer.FlagCondition(cond25,out _,out _),"nonzero test only");
cond25.Op=Op.CmpNe;cond25.In[1]=C22(1);Check(!Normalizer.FlagCondition(cond25,out _,out _),"wrong comparison constant");
cond25.In[1]=C22(0);flag25.Type=VT.I32;Check(!Normalizer.FlagCondition(cond25,out _,out _),"not byte");
flag25.Type=VT.I8;Check(!Normalizer.FlagStore(store25,0x5502a6c),"different flag");
one25.In[0]=C22(2);Check(!Normalizer.FlagStore(store25,0x5502a6d),"wrong store value");
one25.In[0]=C22(1);one25.Type=VT.I32;Check(!Normalizer.FlagStore(store25,0x5502a6d),"wrong store width");
one25.Type=VT.I8;store25.In[0]=N22(Op.Add,mi22,C22(0xa6d));Check(!Normalizer.FlagStore(store25,0x5502a6d),"unknown base");
store25.In[0]=N22(Op.Mul,C22(2),C22(0x5502a6d));Check(!Normalizer.FlagStore(store25,0x5502a6d),"unsupported arithmetic");
Console.WriteLine("LATE_METADATA_FLAG_SMOKE_PASS positive=3 negative=8");

// Packed signed indexing must match an exact full-word shift/add/ASR
// pattern, preserve 32-bit wrap, and not accept a differently scaled access.
var x25=N22(Op.Param);x25.Type=VT.I32;
var ext25=N22(Op.ZExt,x25);var sh25=N22(Op.Shl,ext25,C22(32));
var add25=N22(Op.Add,C22(-4294967296),sh25);
var asr25=N22(Op.ShrS,add25,C22(29));
Check(HirBuilder.TryPackedSignedIndex(asr25,1,8,out var val25,out var delta25)&&val25==x25&&delta25==-1,"packed index");
Check(!HirBuilder.TryPackedSignedIndex(asr25,2,8,out _,out _),"wrong scale");
Check(!HirBuilder.TryPackedSignedIndex(asr25,1,4,out _,out _),"wrong size");
asr25.Op=Op.ShrU;Check(!HirBuilder.TryPackedSignedIndex(asr25,1,8,out _,out _),"unsigned shift");
asr25.Op=Op.ShrS;add25.In[0]=C22(-4294967295);Check(!HirBuilder.TryPackedSignedIndex(asr25,1,8,out _,out _),"low bits nonzero");
add25.In[0]=C22(-4294967296);sh25.In[1]=C22(31);Check(!HirBuilder.TryPackedSignedIndex(asr25,1,8,out _,out _),"wrong upper shift");
sh25.In[1]=C22(32);x25.Type=VT.I64;Check(!HirBuilder.TryPackedSignedIndex(asr25,1,8,out _,out _),"unproven width");
Console.WriteLine("PACKED_INDEX_SMOKE_PASS positive=1 negative=6");

uint[] target27=[0xa9bf4ffe,0xf9002801,0xb4000101,0xaa0003f3,0xaa0103e0,0xaa1f03e1,0x9400000a,0xbd005a62,0xa8c14ffe,0xd65f03c0,0x9400000a];
bool Target27(uint[] a,int first=80,int second=88,ulong get=0x1040,bool helper=true)=>Arm64TargetPositionSetter.Matches(a,first,second,0x1000,get,x=>helper&&x==0x1050);
Check(Target27(target27),"compound target");
Check(!Target27(target27,72),"wrong reference offset");
Check(!Target27(target27,80,92),"wrong scalar offset");
Check(!Target27(target27,get:0x1044),"wrong position call");
Check(!Target27(target27,helper:false),"wrong exception call");
foreach(int ix in new[]{0,2,3,4,5,7,8,9}){var bad27=target27.ToArray();bad27[ix]^=1;Check(!Target27(bad27),"unsafe target shape "+ix);}
Check(!Target27(target27[..^1]),"truncated target");
Console.WriteLine("COMPOUND_TARGET_SETTER_SMOKE_PASS positive=1 negative=13");

sealed class VectorImage:NativeImage{
 public override ImageFormat Format=>ImageFormat.Elf;
 public VectorImage(params uint[] words){
  Arch=CpuArch.Arm64;PointerSize=8;MemoryBase=0x1000;Memory=new byte[4*words.Length];
  for(int i=0;i<words.Length;i++)BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan(4*i),words[i]);
  Sections.Add(new ImageSection(".text",MemoryBase,(ulong)Memory.Length,SectionFlags.Read|SectionFlags.Execute));
 }
}
