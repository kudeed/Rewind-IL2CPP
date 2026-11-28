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
var capacityMethod=Method("get_Capacity",i);capacityMethod.Flags=6;add.Flags=6|MethodDef.Virtual|MethodDef.Final;
listDef.Methods=[add,resize,count,capacityMethod];
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

// Native key snapshots may sit wholly inside a foreach try/finally. Keep
// region entries, handlers and scope transitions intact while folding Add.
var scopedAppend52=Fixture();
var scopedJoin52=new HBlock{Id=3,Scope=0,Statements=[new HReturn(null)]};
var scopedHandler52=new HBlock{Id=4,Scope=1,Statements=[new HEndFinally()]};
scopedAppend52.block.Scope=scopedAppend52.fast.Scope=scopedAppend52.slow.Scope=0;
scopedAppend52.fast.Statements[2]=new HJump(scopedJoin52);
scopedAppend52.slow.Statements[1]=new HJump(scopedJoin52);
scopedAppend52.h.Blocks.AddRange([scopedJoin52,scopedHandler52]);
var scopedRegion52=new HTryRegion{Index=0,Entry=scopedAppend52.block,HandlerEntry=scopedHandler52,Finally=true,
    Exception=scopedAppend52.h.NewLocal(o)};
scopedAppend52.h.TryRegions.Add(0,scopedRegion52);
Check(ListAppendFolding.TryFold(scopedAppend52.h,sf,scopedAppend52.block)&&
    scopedAppend52.h.TryRegions[0]==scopedRegion52&&scopedRegion52.Entry==scopedAppend52.block&&
    scopedRegion52.HandlerEntry==scopedHandler52&&scopedAppend52.block.Scope==0&&
    scopedAppend52.block.Statements.Last() is HJump {Target:var target52}&&target52==scopedJoin52,
    "same-scope foreach finally append");
foreach(string failure52 in new[]{"region-entry","handler-entry","cross-scope","unknown-scope"})
{
    var x52=Fixture(); var join52=new HBlock{Id=3,Statements=[new HReturn(null)]};
    x52.h.Blocks.Add(join52);x52.fast.Statements[2]=new HJump(join52);x52.slow.Statements[1]=new HJump(join52);
    var region52=new HTryRegion{Index=0,Entry=x52.block,HandlerEntry=join52,Exception=x52.h.NewLocal(o)};
    x52.h.TryRegions.Add(0,region52);
    switch(failure52)
    {
        case "region-entry":region52.Entry=x52.fast;break;
        case "handler-entry":region52.HandlerEntry=x52.slow;break;
        case "cross-scope":x52.slow.Scope=0;break;
        case "unknown-scope":x52.block.Scope=x52.fast.Scope=x52.slow.Scope=4;break;
    }
    Check(!ListAppendFolding.TryFold(x52.h,sf,x52.block),"unsafe exception fold "+failure52);
}
var string52=sf.Primitive(Il2CppTypeEnum.String);
foreach(string shape52 in new[]{"pure","addressed","annotation","effect"})
{
    var x52=Fixture(custom:string52);var from52=x52.h.NewLocal(string52);var copy52=x52.h.NewLocal(string52);
    x52.block.Statements.Insert(1,new HAssign(L(from52),new HArg(0){Type=string52}));
    var copyStatement52=new HAssign(L(copy52),L(from52));
    x52.block.Statements.Insert(3,copyStatement52);
    ((HAssign)x52.fast.Statements[1]).Value=L(copy52);
    ((HCall)((HEval)x52.slow.Statements[0]).Expression).Arguments[0]=L(copy52);
    if(shape52=="addressed")copy52.AddressTaken=true;
    if(shape52=="annotation")copyStatement52.Value.Type=o;
    if(shape52=="effect")copyStatement52.Value=new HCall{Method=new MethodDef{Name="Read",DeclaringType=owner,ReturnType=string52},Type=string52};
    bool folded52=ListAppendFolding.TryFold(x52.h,sf,x52.block);
    Check(folded52==(shape52=="pure"),"reference-copy contract "+shape52);
    if(folded52)Check(x52.block.Statements.Contains(copyStatement52),"reference copy was dropped");
}
Console.WriteLine("LIST_APPEND_SCOPE_COPY_SMOKE_PASS positive=2 negative=7");

// Actual foreach recovery routes the resize arm through an empty jump block.
foreach(string shape53 in new[]{"pure","effect","cycle","scope","region-entry","handler-entry"})
{
    var x53=Fixture();var join53=new HBlock{Id=3,Statements=[new HReturn(null)]};
    var bridge53=new HBlock{Id=4,Statements=[new HJump(join53)]};
    x53.h.Blocks.AddRange([join53,bridge53]);
    x53.fast.Statements[2]=new HJump(join53);x53.slow.Statements[1]=new HJump(bridge53);
    if(shape53=="effect")bridge53.Statements.Insert(0,new HAssign(L(x53.n),new HConst(9,i)));
    if(shape53=="cycle")bridge53.Statements[0]=new HJump(bridge53);
    if(shape53=="scope")bridge53.Scope=0;
    if(shape53 is "region-entry" or "handler-entry")
        x53.h.TryRegions.Add(0,new HTryRegion{Index=0,Entry=shape53=="region-entry"?bridge53:x53.block,
            HandlerEntry=shape53=="handler-entry"?bridge53:join53,Exception=x53.h.NewLocal(o)});
    Check(ListAppendFolding.TryFold(x53.h,sf,x53.block)==(shape53=="pure"),"jump continuation "+shape53);
    if(shape53=="pure")Check(x53.block.Statements.Last() is HJump j53&&j53.Target==join53,"lost common continuation");
}
Console.WriteLine("LIST_APPEND_JUMP_SMOKE_PASS positive=1 negative=5");

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

// Preserve the identity difference between an original receiver copy and
// a field reload after AddWithResize. Neither assignment may be moved.
(HMethod h,HBlock block,HBlock fast,HBlock slow,HVar arr,HVar n) ReloadFixture()
{
 var x=Fixture(true);var receiver=((HLocal)((HField)((HAssign)x.block.Statements[1]).Value).Object!).Variable;
 var phi=x.h.NewLocal(receiver.Type);
 var field=new FieldDef{Name="all",DeclaringType=owner,Type=receiver.Type};
 var reload=new HField{Field=field,Object=new HArg(2){Type=owner.Sig},Type=receiver.Type};
 x.fast.Statements.Insert(2,new HAssign(L(phi),L(receiver)));
 x.slow.Statements.Insert(1,new HAssign(L(phi),reload));
 return x;
}
var reloadPositive=ReloadFixture();
var originalFastTail=reloadPositive.fast.Statements[2];var originalSlowTail=reloadPositive.slow.Statements[1];
var originalDecision=(HBranch)reloadPositive.block.Statements[^1];
Check(ListAppendFolding.TryFold(reloadPositive.h,sf,reloadPositive.block)&&reloadPositive.h.Blocks.Count==3&&
 ReferenceEquals(reloadPositive.block.Statements[^1],originalDecision)&&
 ReferenceEquals(reloadPositive.fast.Statements[1],originalFastTail)&&ReferenceEquals(reloadPositive.slow.Statements[1],originalSlowTail)&&
 reloadPositive.fast.Statements[0] is HEval{Expression:HCall reloadFastCall}&&ReferenceEquals(reloadFastCall.Method,add)&&
 reloadPositive.slow.Statements[0] is HEval{Expression:HCall reloadSlowCall}&&ReferenceEquals(reloadSlowCall.Method,add)&&
 reloadPositive.block.Statements[1] is HAssign{Value:HCall reloadCapacityCall}&&ReferenceEquals(reloadCapacityCall.Method,capacityMethod)&&
 reloadPositive.h.Locals.Contains(reloadPositive.arr)&&reloadPositive.arr.Type.Key==i.Key&&reloadPositive.h.Locals.Contains(reloadPositive.n),"branch receiver reload preservation");
var tailCases=new (string,Action<(HMethod h,HBlock block,HBlock fast,HBlock slow,HVar arr,HVar n)> mutate)[]{
 ("mismatched receiver phi",x=>((HLocal)((HAssign)x.slow.Statements[1]).Target).Variable=x.h.NewLocal(((HAssign)x.slow.Statements[1]).Target.Type!)),
 ("address-taken receiver phi",x=>((HLocal)((HAssign)x.fast.Statements[2]).Target).Variable.AddressTaken=true),
 ("array tail escape",x=>((HAssign)x.slow.Statements[1]).Value=L(x.arr)),
 ("count tail escape",x=>((HAssign)x.slow.Statements[1]).Value=L(x.n)),
 ("extra tail effect",x=>x.slow.Statements.Insert(2,new HEval(new HConst(0,i)))),
 ("wrong fast receiver",x=>((HAssign)x.fast.Statements[2]).Value=new HArg(7){Type=((HAssign)x.fast.Statements[2]).Value.Type}),
 ("wrong element",x=>((HCall)((HEval)x.slow.Statements[0]).Expression).Arguments[0]=new HArg(7){Type=i}),
 ("extra array use",x=>x.h.Blocks.Add(new HBlock{Id=3,Statements=[new HEval(L(x.arr)),new HReturn(null)]})),
 ("other incoming edge",x=>x.h.Blocks.Add(new HBlock{Id=3,Statements=[new HJump(x.slow)]})),
 ("wrong scope",x=>x.slow.Scope=0)
};
foreach(var tailCase in tailCases){var x=ReloadFixture();tailCase.mutate(x);Check(!ListAppendFolding.TryFold(x.h,sf,x.block),"unsafe reload tail accepted: "+tailCase.Item1);}
foreach(string badGetter in new[]{"missing","private","static","virtual","wrong return","argument","duplicate"})
{
 var x=ReloadFixture();var savedMethods=listDef.Methods;ushort savedFlags=capacityMethod.Flags;var savedReturn=capacityMethod.ReturnType;var savedParameters=capacityMethod.Parameters;
 if(badGetter=="missing")listDef.Methods=[add,resize,count];
 if(badGetter=="private")capacityMethod.Flags=1;
 if(badGetter=="static")capacityMethod.Flags=6|MethodDef.Static;
 if(badGetter=="virtual")capacityMethod.Flags=6|MethodDef.Virtual;
 if(badGetter=="wrong return")capacityMethod.ReturnType=o;
 if(badGetter=="argument")capacityMethod.Parameters=[new ParamDef{Type=i}];
 if(badGetter=="duplicate")listDef.Methods=[add,resize,count,capacityMethod,capacityMethod];
 Check(!ListAppendFolding.TryFold(x.h,sf,x.block),"unsafe capacity metadata accepted: "+badGetter);
 listDef.Methods=savedMethods;capacityMethod.Flags=savedFlags;capacityMethod.ReturnType=savedReturn;capacityMethod.Parameters=savedParameters;
}
// Holes in the local inventory occur after an earlier diamond fold.
// Converting the dead array snapshot must preserve every local identity.
foreach(int localHoles in new[]{1,3})
{
 var x=ReloadFixture();var unusedHoles=Enumerable.Range(0,localHoles).Select(_=>x.h.NewLocal(i)).ToArray();
 var liveSentinel=x.h.NewLocal(i);foreach(var hole in unusedHoles)x.h.Locals.Remove(hole);
 x.block.Statements.Insert(0,new HEval(L(liveSentinel)));
 var originalLocals=x.h.Locals.ToArray();
 Check(ListAppendFolding.TryFold(x.h,sf,x.block)&&x.h.Locals.SequenceEqual(originalLocals)&&
  x.h.Locals.Select(a=>a.Index).Distinct().Count()==x.h.Locals.Count&&
  x.h.Locals.Select(a=>a.Name).Distinct().Count()==x.h.Locals.Count&&x.arr.Type.Key==i.Key,
  "receiver reload fold duplicated or removed a local across inventory holes");
}
Console.WriteLine("LIST_APPEND_RECEIVER_RELOAD_SMOKE_PASS positive=3 negative=17");


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

// Four public float components require both original layout and all three
// original native constructor instructions; size alone never qualifies.
int fourPositive=0,fourNegative=0;
foreach(string fourName in new[]{"Vector4","Color"})
{
 var fourAssembly=new AssemblyModel{Name="UnityEngine.CoreModule"};
 string channels=fourName=="Color"?"rgba":"xyzw";
 var fourType=new TypeDef{Index=fourName=="Color"?501:500,Name=fourName,Namespace="UnityEngine",Assembly=fourAssembly,IsValueType=true,
  Flags=TypeDef.SequentialLayout,Sizes=new RawTypeSizes(32,16,0,0)};
 fourType.Sig=sf.TypeDef(fourType);
 fourType.Fields=Enumerable.Range(0,4).Select(channelIndex4=>new FieldDef{Name=channels[channelIndex4].ToString(),DeclaringType=fourType,Type=ft,Offset=16+4*channelIndex4,Attrs=6}).ToArray();
 var fourCtor=new MethodDef{Name=".ctor",DeclaringType=fourType,ReturnType=v,Address=0x1000,Flags=6,
  Parameters=Enumerable.Range(0,4).Select(_=>new ParamDef{Type=ft}).ToArray()};
 var fourImage=new VectorImage(0x2D000400u,0x2D010C02u,0xD65F03C0u);
 void FourCheck(bool condition4,string reason4){Check(condition4,fourName+": "+reason4);}
 FourCheck(VectorListValue.Dimension(fourType.Sig,16)==4&&VectorListValue.ConstructorShape(fourImage,fourCtor,fourType.Sig),"exact layout and original constructor");fourPositive++;
 var fourArgument=Fixture(custom:fourType.Sig);
 FourCheck(ListAppendFolding.TryFold(fourArgument.h,sf,fourArgument.block,fourImage),"four-float value argument append");fourPositive++;
 HNewObject FourValue(uint fourLastBits)=>new(){Constructor=fourCtor,Type=fourType.Sig,Arguments=[new HConst(1.25f,ft),new HConst(-2.5f,ft),new HConst(BitConverter.UInt32BitsToSingle(0x80000000),ft),new HConst(BitConverter.UInt32BitsToSingle(fourLastBits),ft)]};
 var fourConstructed=Fixture(custom:fourType.Sig);
 ((HAssign)fourConstructed.fast.Statements[1]).Value=FourValue(0x7fc01234);
 ((HCall)((HEval)fourConstructed.slow.Statements[0]).Expression).Arguments[0]=FourValue(0x7fc01234);
 FourCheck(ListAppendFolding.TryFold(fourConstructed.h,sf,fourConstructed.block,fourImage),"same four-float constructor bits");fourPositive++;
 foreach(uint altered in new uint[]{0,0x80000000,0x7fc01235})
 {
  var mismatch=Fixture(custom:fourType.Sig);
  ((HAssign)mismatch.fast.Statements[1]).Value=FourValue(0x7fc01234);
  ((HCall)((HEval)mismatch.slow.Statements[0]).Expression).Arguments[0]=FourValue(altered);
  FourCheck(!ListAppendFolding.TryFold(mismatch.h,sf,mismatch.block,fourImage),"different fourth component bits accepted");fourNegative++;
 }
 foreach(var bad in new[]{new VectorImage(0x2D000401u,0x2D010C02u,0xD65F03C0u),new VectorImage(0x2D000400u,0x2D010C03u,0xD65F03C0u),new VectorImage(0x2D000400u,0x2D010C02u,0),new VectorImage(0x2D000400u,0x2D010C02u)})
 {FourCheck(!VectorListValue.ConstructorShape(bad,fourCtor,fourType.Sig),"mutated/truncated constructor accepted");fourNegative++;}
 fourType.Fields[3].Offset=32;FourCheck(VectorListValue.Dimension(fourType.Sig,16)==0,"wrong last offset accepted");fourNegative++;fourType.Fields[3].Offset=28;
 fourType.Fields[3].Attrs=1;FourCheck(VectorListValue.Dimension(fourType.Sig,16)==0,"private last channel accepted");fourNegative++;fourType.Fields[3].Attrs=6;
 fourType.Fields[3].Type=i;FourCheck(VectorListValue.Dimension(fourType.Sig,16)==0,"integer last channel accepted");fourNegative++;fourType.Fields[3].Type=ft;
 string originalChannel=fourType.Fields[3].Name;fourType.Fields[3].Name=channels[2].ToString();FourCheck(VectorListValue.Dimension(fourType.Sig,16)==0,"duplicate channel accepted");fourNegative++;fourType.Fields[3].Name=originalChannel;
 fourAssembly.Name="Synthetic";FourCheck(VectorListValue.Dimension(fourType.Sig,16)==0,"wrong assembly accepted");fourNegative++;fourAssembly.Name="UnityEngine.CoreModule";
 fourType.Name="UnprovenFourFloats";FourCheck(VectorListValue.Dimension(fourType.Sig,16)==0,"arbitrary equal-size struct accepted");fourNegative++;fourType.Name=fourName;
 fourType.Sizes=new RawTypeSizes(36,20,0,0);FourCheck(VectorListValue.Dimension(fourType.Sig,16)==0,"padded struct accepted");fourNegative++;fourType.Sizes=new RawTypeSizes(32,16,0,0);
 FourCheck(VectorListValue.Dimension(fourType.Sig,8)==0,"wrong object header accepted");fourNegative++;
}
Console.WriteLine("FOUR_COMPONENT_LIST_SMOKE_PASS positive="+fourPositive+" negative="+fourNegative);


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

// Retain the capacity decision and value stores instead of inferring an ABI
// or moving field reads. These fixtures also require rejection to be atomic.
var byteTypeR=new TypeDef{Index=610,Name="Color32",Namespace="UnityEngine",Assembly=new AssemblyModel{Name="UnityEngine.CoreModule"},IsValueType=true,Flags=16,Sizes=new RawTypeSizes(20,4,0,0)};
byteTypeR.Sig=sf.TypeDef(byteTypeR);var byteSigR=sf.Primitive(Il2CppTypeEnum.U1);
byteTypeR.Fields=Enumerable.Range(0,4).Select(k=>new FieldDef{Name="rgba"[k].ToString(),DeclaringType=byteTypeR,Type=byteSigR,Offset=16+k,Attrs=6}).ToArray();
(HMethod h,HBlock block,HBlock fast,HBlock slow,HVar arr,HVar n) ByteFixtureR()
{
 var x=Fixture(custom:byteTypeR.Sig);var a=x.h.NewLocal(byteTypeR.Sig);var b=x.h.NewLocal(byteTypeR.Sig);a.AddressTaken=true;b.AddressTaken=true;
 var packed=x.h.NewLocal(i);
 x.block.Statements.InsertRange(0,new HStmt[]{new HAssign(L(a),new HTypeExpr(HTypeOp.Default,byteTypeR.Sig,null){Type=byteTypeR.Sig}),new HAssign(L(b),new HTypeExpr(HTypeOp.Default,byteTypeR.Sig,null){Type=byteTypeR.Sig})});
 int at=x.block.Statements.FindIndex(s=>s is HAssign{Value:HField{Field.Name:"_items"}});
 x.block.Statements.Insert(at+1,new HAssign(L(packed),new HSelect(new HArg(0){Type=bo},new HConst(-16776961,i),new HConst(-16777216,i)){Type=i}));
 HStmt[] Stores(HVar value)=>byteTypeR.Fields.Select((f,k)=>(HStmt)new HAssign(F(f,L(value)),new HConv(HConvKind.U1,k==0?L(packed):new HBinary(HBinaryOp.ShrUn,L(packed),new HConst(k*8,i)){Type=i}){Type=byteSigR})).ToArray();
 ((HAssign)x.fast.Statements[1]).Value=L(a);((HCall)((HEval)x.slow.Statements[0]).Expression).Arguments[0]=L(b);
 x.fast.Statements.InsertRange(1,Stores(a));x.slow.Statements.InsertRange(0,Stores(b));return x;
}
var bytePositiveR=ByteFixtureR();var byteLocalsR=bytePositiveR.h.Locals.ToArray();var byteFastR=bytePositiveR.fast.Statements.Skip(1).Take(4).ToArray();var byteSlowR=bytePositiveR.slow.Statements.Take(4).ToArray();
Check(ListAppendFolding.TryFoldRetainedDiamond(bytePositiveR.h,sf,bytePositiveR.block,native)&&bytePositiveR.h.Blocks.Count==3&&
 bytePositiveR.fast.Statements.Take(4).SequenceEqual(byteFastR)&&bytePositiveR.slow.Statements.Take(4).SequenceEqual(byteSlowR)&&
 bytePositiveR.fast.Statements[^2]is HEval{Expression:HCall{Method.Name:"Add"}}&&bytePositiveR.slow.Statements[^2]is HEval{Expression:HCall{Method.Name:"Add"}}&&
 bytePositiveR.h.Locals.SequenceEqual(byteLocalsR)&&bytePositiveR.arr.Type.Key==i.Key,"retained byte stores/arms/identities");
var byteNegativeR=new (string,Action<(HMethod h,HBlock block,HBlock fast,HBlock slow,HVar arr,HVar n)> )[]{
 ("wrong capacity condition",x=>((HCompare)((HBranch)x.block.Statements[^1]).Condition).Op=HCompareOp.LtUn),
 ("different receiver",x=>((HCall)((HEval)x.slow.Statements[^2]).Expression).This=new HArg(5){Type=sf.GenericInst(listDef,[byteTypeR.Sig])}),
 ("version increment",x=>((HBinary)((HAssign)x.block.Statements[^3]).Value).Right=new HConst(2,i)),
 ("size increment",x=>((HBinary)((HAssign)x.fast.Statements[0]).Value).Right=new HConst(2,i)),
 ("different array index",x=>((HElement)((HAssign)x.fast.Statements[^2]).Target).Index=new HConst(0,i)),
 ("extra array use",x=>x.block.Statements.Insert(0,new HEval(L(x.arr)))),
 ("extra incoming edge",x=>x.h.Blocks.Add(new HBlock{Id=99,Statements=[new HJump(x.fast)]})),
 ("exception region",x=>x.fast.Scope=0),
 ("side effect in prelude",x=>x.block.Statements.Insert(x.block.Statements.Count-3,new HEval(new HCall{Method=ctor,This=new HArg(0){Type=made.Sig}}))),
 ("side effect in arm",x=>x.fast.Statements.Insert(1,new HEval(new HCall{Method=ctor,This=new HArg(0){Type=made.Sig}}))),
 ("value address escape",x=>x.block.Statements.Insert(0,new HEval(new HAddressOf(((HAssign)x.fast.Statements[1]).Target)))),
 ("duplicate component",x=>((HField)((HAssign)x.fast.Statements[2]).Target).Field=byteTypeR.Fields[0]),
 ("field read after size update",x=>((HAssign)x.fast.Statements[1]).Value=new HField{Field=new FieldDef{Name="channel",DeclaringType=made,Type=byteSigR,Attrs=6},Object=new HArg(4){Type=made.Sig},Type=byteSigR}),
 ("checked component conversion",x=>((HConv)((HAssign)x.fast.Statements[1]).Value).Kind=HConvKind.OvfU1),
 ("private temp in payload",x=>((HConv)((HAssign)x.fast.Statements[1]).Value).Operand=L(x.arr)),
 ("different continuation",x=>{var end=new HBlock{Id=98,Statements=[new HReturn(null)]};x.h.Blocks.Add(end);x.slow.Statements[^1]=new HJump(end);}),
 ("unknown native data",x=>x.h.Problems.Add("unmodeled native instruction"))
};
foreach(var (name,mutate)in byteNegativeR){var x=ByteFixtureR();mutate(x);string before=HirPrinter.Print(x.h);Check(!ListAppendFolding.TryFoldRetainedDiamond(x.h,sf,x.block,native)&&HirPrinter.Print(x.h)==before,"retained unsafe mutation accepted/edited: "+name);}
var closureR=new TypeDef{Index=611,Name="Closure",Assembly=asm,IsValueType=true};closureR.Sig=sf.TypeDef(closureR);var scalarR=new FieldDef{Name="value",DeclaringType=closureR,Type=ft,Attrs=6};
(HMethod h,HBlock block,HBlock fast,HBlock slow,HVar arr,HVar n) ReadFixtureR()
{
 var x=Fixture(custom:vec.Sig);var temp=x.h.NewLocal(ft);
 int at=x.block.Statements.FindIndex(s=>s is HAssign{Value:HField{Field.Name:"_items"}});
 x.block.Statements.Insert(at+1,new HAssign(L(temp),F(scalarR,new HDeref(new HArg(3){Type=sf.ByRef(closureR.Sig)}){Type=closureR.Sig})));
 HNewObject Value()=>new(){Constructor=vc,Type=vec.Sig,Arguments=[L(temp),new HConst(1f,ft)]};
 ((HAssign)x.fast.Statements[^2]).Value=Value();((HCall)((HEval)x.slow.Statements[^2]).Expression).Arguments[0]=Value();return x;
}
var readPositiveR=ReadFixtureR();var readStatementR=readPositiveR.block.Statements[2];
Check(ListAppendFolding.TryFoldRetainedDiamond(readPositiveR.h,sf,readPositiveR.block,native)&&readPositiveR.h.Blocks.Count==3&&
 ReferenceEquals(readPositiveR.block.Statements[2],readStatementR)&&readPositiveR.fast.Statements[^2]is HEval{Expression:HCall{Method.Name:"Add"}},"interleaved scalar read was moved");
var badReadR=ReadFixtureR();((HAssign)badReadR.block.Statements[2]).Value=new HCall{Method=vc,This=new HArg(0){Type=vec.Sig},Type=ft};
Check(!ListAppendFolding.TryFoldRetainedDiamond(badReadR.h,sf,badReadR.block,native),"scheduled call accepted");
var oldGetterFlagsR=capacityMethod.Flags;capacityMethod.Flags=1;var badGetterR=ByteFixtureR();string getterBeforeR=HirPrinter.Print(badGetterR.h);
Check(!ListAppendFolding.TryFoldRetainedDiamond(badGetterR.h,sf,badGetterR.block,native)&&HirPrinter.Print(badGetterR.h)==getterBeforeR,"private Capacity accepted or partially mutated");capacityMethod.Flags=oldGetterFlagsR;
Console.WriteLine("LIST_APPEND_RETAINED_VALUES_SMOKE_PASS positive=2 negative="+(byteNegativeR.Length+2));

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


// Exact bounded two-phi cursor loop. The type proof is a separate callback;
// this tests the machine shape, use restrictions and rewritten SSA.
(Function fn,Block head,Block body,Node index,Node cursor,Node inc,Node call,Node len,Node array) Cursor30()
{
 var fn=new Function();
 var entry=new Block{Id=0};var pre=new Block{Id=1};var head=new Block{Id=2};var body=new Block{Id=3};var fail=new Block{Id=4};var exit=new Block{Id=5};
 fn.Blocks=[entry,pre,head,body,fail,exit];
 entry.Succs=[pre];pre.Preds=[entry];pre.Succs=[head];head.Preds=[pre,body];head.Succs=[fail,body];body.Preds=[head];body.Succs=[head,exit];fail.Preds=[head];exit.Preds=[body];
 Node C(long v){var n=fn.NewNode(Op.Const,VT.I64,null);n.Imm=v;return n;}
 Node N(Block b,Op op,VT t,params Node[] x){var n=fn.NewNode(op,t,b,x);b.Nodes.Add(n);return n;}
 var array=N(entry,Op.Proj,VT.I64);var n0=N(entry,Op.Load,VT.I64,N(entry,Op.Add,VT.I64,array,C(24)));
 N(entry,Op.Jump,VT.None);
 var p0=N(pre,Op.Add,VT.I64,array,C(32));var l0=N(pre,Op.Trunc,VT.I32,n0);N(pre,Op.Jump,VT.None);
 var index=fn.NewNode(Op.Phi,VT.I64,head);var cursor=fn.NewNode(Op.Phi,VT.I64,head);var len=fn.NewNode(Op.Phi,VT.I32,head);head.Phis=[index,cursor,len];
 var cmp=N(head,Op.CmpLeU,VT.I1,N(head,Op.ZExt,VT.I64,len),index);N(head,Op.Branch,VT.None,cmp);
 var call=N(body,Op.Call,VT.None,cursor);call.Aux=new CallInfo{Target=0x1000,Slots=[new ArgSlot(ArgSlotKind.IntReg,0)]};
 var l1=N(body,Op.Load,VT.I32,N(body,Op.Add,VT.I64,array,C(24)));
 var i1=N(body,Op.Add,VT.I64,index,C(1));var inc=N(body,Op.Add,VT.I64,cursor,C(44));
 N(body,Op.Branch,VT.None,N(body,Op.CmpLtS,VT.I1,i1,N(body,Op.SExt,VT.I64,l1)));
 index.In=[C(0),i1];cursor.In=[p0,inc];len.In=[l0,l1];
 N(fail,Op.Unreachable,VT.None);N(exit,Op.Return,VT.None);
 return(fn,head,body,index,cursor,inc,call,len,array);
}
var pos30=Cursor30();
Check(ArrayCursorRecovery.Run(pos30.fn,32,(a,c)=>a==pos30.array&&c==pos30.call?44:null)==1,"bounded cursor positive");
Check(pos30.cursor.Dead&&pos30.inc.Dead&&pos30.call.In[0] is {Op:Op.Add} newAddress&&
 newAddress.In[1].IsConstValue(32)&&newAddress.In[0].In[0]==pos30.array&&
 newAddress.In[0].In[1].In[0]==pos30.index&&newAddress.In[0].In[1].In[1].IsConstValue(44),"cursor rewrites to captured array/index");
var neg30=new Action<(Function fn,Block head,Block body,Node index,Node cursor,Node inc,Node call,Node len,Node array)>[]{
 x=>x.inc.In[1].Imm=40,
 x=>x.index.In[0].Imm=1,
 x=>x.index.In[1].In[1].Imm=2,
 x=>x.body.Terminator!.In[0].Op=Op.CmpLtU,
 x=>x.head.Terminator!.In[0].Op=Op.CmpLtU,
 x=>x.head.Succs.Reverse(),
 x=>x.body.Succs.Reverse(),
 x=>x.len.In[1].In[0].In[1].Imm=16,
 x=>x.len.In[1].In[0].In[0]=new Node{Op=Op.Param,Type=VT.I64},
 x=>x.body.Nodes.Insert(0,x.fn.NewNode(Op.Store,VT.None,x.body,x.cursor,x.array)),
 x=>x.body.Nodes.Insert(0,x.fn.NewNode(Op.Store,VT.None,x.body,x.inc,x.array)),
 x=>((CallInfo)x.call.Aux!).Indirect=true,
 x=>((CallInfo)x.call.Aux!).Slots[0]=new ArgSlot(ArgSlotKind.IntReg,1),
 x=>x.fn.TryRegions.Add(new TryRegionInfo{Index=0}),
 x=>x.head.Preds.Add(new Block()),
};
foreach(var mutate30 in neg30){var x=Cursor30();mutate30(x);Check(ArrayCursorRecovery.Run(x.fn,32,(_,_)=>44)==0&&!x.cursor.Dead,"unsafe cursor accepted");}
var noProof30=Cursor30();
Check(ArrayCursorRecovery.Run(noProof30.fn,32,(_,_)=>null)==0,"unknown array type accepted");
var wrongHeader30=Cursor30();
Check(ArrayCursorRecovery.Run(wrongHeader30.fn,16,(_,_)=>44)==0,"wrong header accepted");
Console.WriteLine("ARRAY_CURSOR_SMOKE_PASS positive=1 negative="+(neg30.Length+2));


// Reference-element inlined List.Clear tail with a same-receiver count snapshot.
var array31=new TypeDef{Index=311,Name="Array",Namespace="System",Assembly=core};array31.Sig=sf.TypeDef(array31);
var arrayClear31=new MethodDef{Name="Clear",DeclaringType=array31,ReturnType=v,Flags=MethodDef.Static|6,Parameters=[new ParamDef{Type=array31.Sig},new ParamDef{Type=i},new ParamDef{Type=i}]};
var listClear31=Method("Clear",v);listClear31.Flags=6;
listDef.Methods=[add,resize,count,listClear31];
(HMethod h,HBlock pre,HBlock b,HBlock clear,HBlock empty,HVar list,HVar n,HVar ver) Clear31()
{
 var h=new HMethod{Method=new MethodDef{Name="Caller",DeclaringType=owner,ReturnType=v}};
 var list=h.NewLocal(listType);var n=h.NewLocal(i);var ver=h.NewLocal(i);
 HField LF(FieldDef f)=>new(){Field=f,Object=L(list),DeclaringType=listType,Type=f==items?arrayType:i};
 var pre=new HBlock{Id=0};var b=new HBlock{Id=1};var clear=new HBlock{Id=2};var empty=new HBlock{Id=3};
 pre.Statements=[new HAssign(L(list),new HArg(0){Type=listType}),new HAssign(L(n),new HCall{Method=count,This=L(list),DeclaringType=listType,Type=i}),new HJump(b)];
 b.Statements=[new HAssign(L(ver),LF(version)),new HAssign(LF(sz),new HConst(0,i)),new HAssign(LF(version),new HBinary(HBinaryOp.Add,L(ver),new HConst(1,i)){Type=i}),new HBranch(new HCompare(HCompareOp.Lt,L(n),new HConst(1,i)){Type=bo},empty,clear)];
 clear.Statements=[new HEval(new HCall{Method=arrayClear31,Arguments=[LF(items),new HConst(0,i),L(n)],Type=v}),new HReturn(null)];
 empty.Statements=[new HReturn(null)];h.Blocks=[pre,b,clear,empty];
 return(h,pre,b,clear,empty,list,n,ver);
}
var good31=Clear31();
Check(ListClearFolding.TryFold(good31.h,sf,good31.b)&&good31.h.Blocks.Count==3&&good31.b.Statements[0] is HEval{Expression:HCall clear31}&&clear31.Method==listClear31,"reference list clear");
var conditional31=Clear31();
conditional31.pre.Statements[^1]=new HBranch(new HCompare(HCompareOp.Le,L(conditional31.n),new HConst(0,i)),conditional31.b,conditional31.empty);
Check(ListClearFolding.TryFold(conditional31.h,sf,conditional31.b),"pure count branch");
var negatives31=new Action<(HMethod h,HBlock pre,HBlock b,HBlock clear,HBlock empty,HVar list,HVar n,HVar ver)>[]{
 x=>((HAssign)x.b.Statements[1]).Value=new HConst(1,i),
 x=>((HBinary)((HAssign)x.b.Statements[2]).Value).Right=new HConst(2,i),
 x=>((HCompare)((HBranch)x.b.Statements[3]).Condition).Right=new HConst(0,i),
 x=>((HCompare)((HBranch)x.b.Statements[3]).Condition).Op=HCompareOp.Gt,
 x=>((HCall)((HEval)x.clear.Statements[0]).Expression).Arguments[1]=new HConst(1,i),
 x=>((HCall)((HEval)x.clear.Statements[0]).Expression).Arguments[2]=new HConst(2,i),
 x=>((HField)((HCall)((HEval)x.clear.Statements[0]).Expression).Arguments[0]).Object=new HArg(1){Type=listType},
 x=>x.pre.Statements.Insert(x.pre.Statements.Count-1,new HEval(new HConst(1,i))),
 x=>x.h.Blocks.Add(new HBlock{Id=4,Statements=[new HJump(x.b)]}),
 x=>x.h.Blocks.Add(new HBlock{Id=4,Statements=[new HJump(x.clear)]}),
 x=>x.empty.Statements.Insert(0,new HEval(L(x.ver))),
 x=>x.n.AddressTaken=true,
 x=>x.clear.Scope=0,
 x=>((HCall)((HAssign)x.pre.Statements[1]).Value).This=new HArg(2){Type=listType},
 x=>x.pre.Statements[^1]=new HBranch(new HCompare(HCompareOp.Lt,new HCall{Method=count,This=L(x.list),Type=i},new HConst(0,i)),x.b,x.empty),
};
foreach(var mutate31 in negatives31){var x=Clear31();mutate31(x);Check(!ListClearFolding.TryFold(x.h,sf,x.b),"unsafe list clear accepted");}
Console.WriteLine("LIST_CLEAR_SMOKE_PASS positive=2 negative="+negatives31.Length);


// Synthetic v39 own-MethodInfo RGCTX warm/cold paths with equivalent
// argument-null tests and one exact identified runtime initializer.
uint CB31(uint op,int reg,int from,int to)=>op|((uint)((to-from)/4)&0x7ffffu)<<5|(uint)reg;
uint[] rgctx31=[
 0xf9401c28,0xaa0103f4,0xaa0003f3,CB31(0xb4000000,8,12,32),
 CB31(0xb4000000,19,16,44),0xd503201f,0xd503201f,0xd503201f,
 0xaa1403e0,0x94000007,CB31(0xb5000000,19,40,20),0xd65f03c0];
bool Guard31(uint[] w,int mi=1,int arg=0,bool helper=true)=>Normalizer.OwnRgctxGuardCode(new VectorImage(w),0x100c,mi,arg,x=>helper&&x==0x1040);
Check(Guard31(rgctx31),"own rgctx metadata guard");
foreach(int at in new[]{0,1,2,3,4,8,9,10}){var bad=rgctx31.ToArray();bad[at]^=1;Check(!Guard31(bad),"wrong rgctx instruction "+at);}
Check(!Guard31(rgctx31,mi:2)&&!Guard31(rgctx31,arg:3)&&!Guard31(rgctx31,helper:false)&&!Guard31(rgctx31[..10]),"wrong rgctx arguments/helper/range");
Console.WriteLine("OWN_RGCTX_GUARD_SMOKE_PASS positive=1 negative=12");

// AAPCS64: a struct word holding one reference must remain a typed pointer
// for indexed loads and also survive forwarding into another struct argument.
var wordMethod=typeof(HirBuilder).GetMethod("StructWord",System.Reflection.BindingFlags.Static|System.Reflection.BindingFlags.NonPublic)!;
var partsMethod=typeof(HirBuilder).GetMethod("PartsOf",System.Reflection.BindingFlags.Static|System.Reflection.BindingFlags.NonPublic)!;
Sem Word(List<Part>? parts,int size=8)=>(Sem)wordMethod.Invoke(null,[parts,size])!;
List<Part>? Parts(Sem sem)=>(List<Part>?)partsMethod.Invoke(null,[sem]);
var pointerTypes=new TypeSig[]{o,sf.Primitive(Il2CppTypeEnum.String),sf.SzArray(i),owner.Sig,sf.Pointer(i),sf.ByRef(i)};
foreach(var type in pointerTypes){
 var value=new HArg(0){Type=type};var leaves=new List<Part>{new(0,8,value)};
 Check(Word(leaves) is SVal sv&&ReferenceEquals(sv.Expr,value),"reference word lost pointer type: "+type.Key);
 var forwarded=Parts(Word(leaves));
 Check(forwarded is [{Offset:0,Size:8,Value:var exact}]&&ReferenceEquals(exact,value),"reference word lost while forwarding: "+type.Key);
}
var numberWord=new HArg(0){Type=sf.Primitive(Il2CppTypeEnum.I8)};
var pointerWord=new HArg(0){Type=o};
var nonPointerParts=new List<Part>[] {
 [new(0,8,numberWord)], [new(0,8,new HArg(0){Type=sf.Primitive(Il2CppTypeEnum.R8)})],
 [new(0,4,pointerWord)], [new(1,8,pointerWord)],
 [new(0,4,new HArg(0){Type=i}),new(4,4,new HArg(1){Type=i})], [],
 [new(0,8,new HArg(0))]
};
foreach(var leaves in nonPointerParts)
 Check(Word(leaves) is SParts packed&&packed.Size==8&&ReferenceEquals(packed.Parts,leaves),"partial/numeric word changed representation");
Check(Word(null) is SJunk,"missing word must remain missing");
Check(Parts(new SVal(numberWord))==null,"numeric word treated as reference");
var split=new SParts(nonPointerParts[4],8);
Check(ReferenceEquals(Parts(split),split.Parts),"split fields lost while forwarding");
Console.WriteLine("REFERENCE_STRUCT_WORD_SMOKE_PASS pointer-types=6 forward=6 negative=9 split=1");

// Both words of a live aggregate are arguments, including when forwarded.
var leftoversMethod=typeof(MethodPipeline).GetMethod("Leftovers",System.Reflection.BindingFlags.Static|System.Reflection.BindingFlags.NonPublic)!;
for(int position=0;position<=6;position++){
 var fn=new Function{Regs=RegisterModel.Arm64};
 for(int reg=0;reg<=31;reg++)fn.Params[reg]=fn.NewNode(Op.Param,VT.I64,null);
 var abi=new Rewind.Analysis.Abi.MethodAbi();
 abi.Params.Add(new(Rewind.Analysis.Abi.ParamRole.Argument,0,o,Rewind.Analysis.Abi.PassKind.IntegerPair,position,false,16,2));
 var leftover=(Func<Node,bool>)leftoversMethod.Invoke(null,[fn,abi])!;
 for(int reg=0;reg<8;reg++)Check(leftover(fn.Params[reg])==(reg!=position&&reg!=position+1),"aggregate argument word incorrectly discarded at "+position+" register "+reg);
 Check(leftover(fn.Params[9])&&leftover(fn.Params[30]),"scratch/link register became a live argument");
}
Console.WriteLine("PAIR_ARGUMENT_LIVENESS_SMOKE_PASS positions=7 registers=56 scratch=14");

// A landing prefix's complete address/load chain, not an intermediate word.
Rewind.Analysis.Arm64.A64Instruction Page52(ulong target=0x9000)=>new(){Op=Rewind.Analysis.Arm64.A64Op.Adrp,Rd=24,Target=target,Is64=true};
Rewind.Analysis.Arm64.A64Instruction Load52()=>new(){Op=Rewind.Analysis.Arm64.A64Op.Ldr,Rd=24,Rn=24,Imm=40,Size=8,Is64=true,Mode=Rewind.Analysis.Arm64.A64Mode.Offset};
Rewind.Analysis.Arm64.A64Instruction Copy52(byte to,byte from)=>new(){Op=Rewind.Analysis.Arm64.A64Op.Orr,Rd=to,Rn=31,Rm=from,Is64=true};
var padMain52=new[]{Page52(),Load52()};
var padOther52=new[]{Page52(),Copy52(19,1),Copy52(26,0),Load52()};
bool Equal52(Rewind.Analysis.Arm64.A64Instruction[] a,Rewind.Analysis.Arm64.A64Instruction[] b,int reg=24)=>Rewind.Analysis.Arm64.A64LandingPadSetup.EquivalentRegister(a,b,reg);
Check(Equal52(padMain52,padOther52),"equivalent complete GOT load prefixes rejected");
var extra52=padOther52.Append(new Rewind.Analysis.Arm64.A64Instruction{Op=Rewind.Analysis.Arm64.A64Op.Ldr,Rd=28,Rn=32,Imm=8,Size=8,Is64=true,Mode=Rewind.Analysis.Arm64.A64Mode.Offset}).ToArray();
Check(Equal52(padMain52,extra52),"independent frame reload changed GOT value");
Check(Equal52([Copy52(24,0)],[Copy52(24,0)])&&Equal52([Copy52(24,1)],[Copy52(24,1)]),"exception/selector copies rejected");
var mutations52=new Action<Rewind.Analysis.Arm64.A64Instruction[]>[]{
 a=>a[0].Target+=0x1000,a=>a[1].Imm++,a=>a[1].Size=4,a=>a[1].Signed=true,a=>a[1].Is64=false,
 a=>a[1].Vector=true,a=>a[1].SetFlags=true,a=>a[1].Mode=Rewind.Analysis.Arm64.A64Mode.PreIndex,
 a=>a[1].Op=Rewind.Analysis.Arm64.A64Op.Str,a=>a[1].Op=Rewind.Analysis.Arm64.A64Op.Bl,
 a=>a[1].Op=Rewind.Analysis.Arm64.A64Op.Unknown,a=>a[1].Rn=2,a=>a[1].Rd=32
};
foreach(var mutate52 in mutations52){var bad=padMain52.ToArray();mutate52(bad);Check(!Equal52(padMain52,bad),"unsafe landing prefix accepted");}
Check(!Equal52([Copy52(24,2)],[Copy52(24,2)])&&!Equal52(padMain52,[Page52()])&&!Equal52(padMain52,[]),"unknown/missing setup accepted");
Console.WriteLine("LANDING_PAD_SETUP_SMOKE_PASS positive=4 negative=16");

sealed class VectorImage:NativeImage{
 public override ImageFormat Format=>ImageFormat.Elf;
 public VectorImage(params uint[] words){
  Arch=CpuArch.Arm64;PointerSize=8;MemoryBase=0x1000;Memory=new byte[4*words.Length];
  for(int i=0;i<words.Length;i++)BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan(4*i),words[i]);
  Sections.Add(new ImageSection(".text",MemoryBase,(ulong)Memory.Length,SectionFlags.Read|SectionFlags.Execute));
 }
}
