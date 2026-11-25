using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;

static void Check(bool pass,string why){if(!pass)throw new Exception(why);}
static (HMethod H, HBlock Left,HBlock Right,HBlock Join,HVar Pointer,MethodDef Target) Fixture(){
 var sigs=new SigFactory();
 var i=sigs.Primitive(Il2CppTypeEnum.I4);var f=sigs.Primitive(Il2CppTypeEnum.R4);
 var ni=sigs.Primitive(Il2CppTypeEnum.I);var o=sigs.Primitive(Il2CppTypeEnum.Object);
 var v=sigs.Primitive(Il2CppTypeEnum.Void);var bl=sigs.Primitive(Il2CppTypeEnum.Boolean);
 var asm=new AssemblyModel{Name="Synthetic"};
 var d=new TypeDef{Index=1,Name="D",Assembly=asm,IsDelegate=true};d.Sig=sigs.TypeDef(d);
 var owner=new TypeDef{Index=2,Name="Factory",Assembly=asm};owner.Sig=sigs.TypeDef(owner);
 ParamDef[] P(params TypeSig[] ts)=>ts.Select(t=>new ParamDef{Type=t}).ToArray();
 var ctor=new MethodDef{DeclaringType=d,Name=".ctor",ReturnType=v,Parameters=P(o,ni)};
 var invoke=new MethodDef{DeclaringType=d,Name="Invoke",ReturnType=f,Parameters=P(f)};
 d.Methods=[ctor,invoke];
 var a=new MethodDef{DeclaringType=owner,Name="First",Flags=0x10,Address=0x1000,ReturnType=f,Parameters=P(f)};
 var b=new MethodDef{DeclaringType=owner,Name="Second",Flags=0x10,Address=0x2000,ReturnType=f,Parameters=P(f)};
 var h=new HMethod{Method=new MethodDef{DeclaringType=owner,Name="Get",Flags=0x10,ReturnType=d.Sig,Parameters=P(i)}};
 var local=h.NewLocal(ni);var obj=h.NewLocal(d.Sig);
 HLocal L(HVar x)=>new(x){Type=x.Type};
 HMethodPointer Ptr(MethodDef m)=>new(){Method=m,Type=ni};
 var root=new HBlock{Id=0};var left=new HBlock{Id=1};var right=new HBlock{Id=2};var join=new HBlock{Id=3};
 var condition=new HCompare(HCompareOp.LtUn,new HArg(0){Type=i},new HConst(1,i)){Type=bl};
 root.Statements=[new HBranch(condition,left,right)];
 left.Statements=[new HAssign(L(local),new HSelect(condition,Ptr(a),Ptr(b)){Type=ni}),new HJump(join)];
 right.Statements=[new HAssign(L(local),Ptr(a)),new HJump(join)];
 join.Statements=[new HAssign(L(obj),new HNewObject{Constructor=ctor,Type=d.Sig,Arguments=[new HConst(null,o),L(local)]}),new HReturn(L(obj))];
 h.Blocks=[root,left,right,join];
 return(h,left,right,join,local,b);
}
var good=Fixture();DelegateChoiceFolding.Run(good.H);
Check(good.H.Blocks.Count==3&&good.H.Locals.Count==0&&good.Left.Statements is [HReturn{Value:HSelect{WhenTrue:HNewObject,WhenFalse:HNewObject}}]&&good.Right.Statements is [HReturn{Value:HNewObject}],"valid factory not transformed");
var cases=new (string Name,Action<(HMethod H,HBlock Left,HBlock Right,HBlock Join,HVar Pointer,MethodDef Target)> Mutate)[]{
 ("wrong signature",f=>f.Target.ReturnType=f.H.Method.ReturnType),
 ("instance target",f=>f.Target.Flags=0),
 ("address taken",f=>f.Pointer.AddressTaken=true),
 ("extra pointer use",f=>f.H.Blocks[0].Statements.Insert(0,new HEval(new HLocal(f.Pointer)))),
 ("side effect in choice",f=>((HSelect)((HAssign)f.Left.Statements[0]).Value).Condition=new HCall{Method=f.Target}),
 ("extra statement before jump",f=>f.Left.Statements.Insert(1,new HEval(new HConst(0,null)))),
 ("non-null receiver",f=>((HNewObject)((HAssign)f.Join.Statements[0]).Value).Arguments[0]=new HConst(1,null)),
 ("exception scope",f=>f.Left.Scope=0),
 ("unknown pointer",f=>((HAssign)f.Right.Statements[0]).Value=new HConst(0,null)),
 ("branch directly into join",f=>((HBranch)f.H.Blocks[0].Statements[0]).WhenTrue=f.Join),
 ("no code target",f=>f.Target.Address=0),
 ("constructor target",f=>f.Target.Name=".ctor"),
 ("entry join",f=>{f.H.Blocks.Remove(f.Join);f.H.Blocks.Insert(0,f.Join);})
};
foreach(var c in cases){
 var f=Fixture();c.Mutate(f);var before=HirPrinter.Print(f.H);
 DelegateChoiceFolding.Run(f.H);
 Check(HirPrinter.Print(f.H)==before,"unsafe mutation accepted: "+c.Name);
}
Console.WriteLine($"DELEGATE_CHOICE_SMOKE_PASS positive=1 negative={cases.Length}");
