using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;
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
(HMethod h,HBlock block,HBlock fast,HBlock slow,HVar arr,HVar n) Fixture(bool ints=false){
 var element=ints?i:o;
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
