using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;
static void Check(bool value,string name){if(!value)throw new Exception(name);}
int positive=0,negative=0;
void Accept(string name,Fixture f){Check(EquivalentBranches.TryTarget(f.Method,f.Entry,out var target)&&target!=null,name);positive++;}
void Reject(string name,Action<Fixture> mutate){var f=new Fixture();mutate(f);Check(!EquivalentBranches.TryTarget(f.Method,f.Entry,out _),name);negative++;}
Accept("pure unknown register with identical successors",new Fixture());
var rgctx=new Fixture();rgctx.Branch.Condition=new HCompare(HCompareOp.Ne,new HOpaque("rgctx"),new HConst(0,rgctx.Int)){Type=rgctx.Bool};Accept("metadata context null check with identical successors",rgctx);
var klass=new Fixture();klass.Branch.Condition=new HCompare(HCompareOp.Ne,new HOpaque("klass"),new HConst(0,klass.Int)){Type=klass.Bool};Accept("class metadata check with identical successors",klass);
var direct=new Fixture();direct.Branch.WhenTrue=direct.Join;Accept("one direct successor",direct);
var copied=new Fixture();copied.Copies(new HLocal(copied.Input){Type=copied.Int},new HLocal(copied.Input){Type=copied.Int});Accept("same whole-local copies",copied);
var constant=new Fixture();constant.Copies(new HConst(1,constant.Int),new HConst(1,constant.Int));Accept("same constants",constant);
var argument=new Fixture();argument.Copies(new HArg(0){Type=argument.Int},new HArg(0){Type=argument.Int});Accept("same caller argument",argument);
Reject("effectful condition",f=>f.Branch.Condition=f.Call());
Reject("possibly throwing field condition",f=>f.Branch.Condition=new HField{Field=f.Field,Object=new HArg(-1),Type=f.Bool});
Reject("possibly throwing array condition",f=>f.Branch.Condition=new HElement{Array=new HArg(0),Index=new HConst(0,f.Int),Type=f.Bool});
Reject("native memory read condition",f=>f.Branch.Condition=new HDeref(new HArg(0)){Type=f.Int});
Reject("unknown native call condition",f=>f.Branch.Condition=new HOpaque("call_indirect"));
Reject("unknown load condition",f=>f.Branch.Condition=new HOpaque("load8"));
Reject("metadata value with operands",f=>f.Branch.Condition=new HOpaque("rgctx",f.Call()));
Reject("integer division condition",f=>f.Branch.Condition=new HBinary(HBinaryOp.Div,new HConst(1,f.Int),new HConst(0,f.Int)){Type=f.Int});
Reject("checked arithmetic condition",f=>f.Branch.Condition=new HBinary(HBinaryOp.AddOvf,new HConst(int.MaxValue,f.Int),new HConst(1,f.Int)){Type=f.Int});
Reject("checked conversion condition",f=>f.Branch.Condition=new HConv(HConvKind.OvfI4,new HConst(1d,f.Double)){Type=f.Int});
Reject("one arm has side effect",f=>f.Yes.Statements.Insert(0,new HEval(f.Call())));
Reject("both arms call",f=>{f.Yes.Statements.Insert(0,new HEval(f.Call()));f.No.Statements.Insert(0,new HEval(f.Call()));});
Reject("different constants",f=>f.Copies(new HConst(1,f.Int),new HConst(2,f.Int)));
Reject("different locals",f=>f.Copies(new HLocal(f.Input){Type=f.Int},new HLocal(f.Output){Type=f.Int}));
Reject("different arguments",f=>f.Copies(new HArg(0){Type=f.Int},new HArg(1){Type=f.Int}));
Reject("different target variables",f=>{f.Copies(new HConst(1,f.Int),new HConst(1,f.Int));((HAssign)f.No.Statements[0]).Target=new HLocal(f.Input){Type=f.Int};});
Reject("field copies can throw",f=>f.Copies(new HField{Field=f.Field,Object=new HArg(-1),Type=f.Int},new HField{Field=f.Field,Object=new HArg(-1),Type=f.Int}));
Reject("different successor",f=>{var other=new HBlock{Id=4,Statements=[new HReturn(new HConst(2,f.Int))]};f.Method.Blocks.Add(other);((HJump)f.No.Statements[^1]).Target=other;});
Reject("exception region",f=>f.Method.TryRegions[0]=new HTryRegion());
Reject("exception scope",f=>f.Yes.Scope=0);
Reject("unknown source scope",f=>f.Entry.Scope=0);
Reject("branch successor outside method",f=>f.Branch.WhenTrue=new HBlock{Statements=[new HReturn(null)]});
Reject("jump cycle",f=>((HJump)f.Yes.Statements[0]).Target=f.Yes);
Reject("back edge through source",f=>((HJump)f.Yes.Statements[0]).Target=f.Entry);
Reject("different signed zeros",f=>f.Copies(new HConst(0f,f.Single),new HConst(-0f,f.Single)));
Reject("different nan payloads",f=>f.Copies(new HConst(BitConverter.Int32BitsToSingle(0x7fc00001),f.Single),new HConst(BitConverter.Int32BitsToSingle(0x7fc00002),f.Single)));
var cleanup=new Fixture();var deadA=new HVar{Type=cleanup.Int};var deadB=new HVar{Type=cleanup.Int};cleanup.Yes.Statements.Insert(0,new HAssign(new HLocal(deadA),new HConst(10,cleanup.Int)));cleanup.No.Statements.Insert(0,new HAssign(new HLocal(deadB),new HConst(11,cleanup.Int)));HirCleanup.Run(cleanup.Method);Check(cleanup.Entry.Statements[^1] is HJump,"dead copies followed by equivalent successor removal");Check(cleanup.Method.Blocks.Count==2,"unreachable empty arm removal");positive++;
Console.WriteLine($"EQUIVALENT_BRANCHES_PASS positive={positive} negative={negative}");
sealed class Fixture
{
 public TypeSig Int,Bool,Single,Double;public MethodDef Called;public FieldDef Field;public HVar Input,Output;public HBlock Entry,Yes,No,Join;public HBranch Branch;public HMethod Method;
 public Fixture(){var sf=new SigFactory();Int=sf.Primitive(Il2CppTypeEnum.I4);Bool=sf.Primitive(Il2CppTypeEnum.Boolean);Single=sf.Primitive(Il2CppTypeEnum.R4);Double=sf.Primitive(Il2CppTypeEnum.R8);var owner=new TypeDef{Name="Owner",Assembly=new AssemblyModel{Name="Test"}};owner.Sig=sf.TypeDef(owner);Called=new MethodDef{Name="Effect",DeclaringType=owner,ReturnType=Int};Field=new FieldDef{Name="Field",DeclaringType=owner,Type=Int};Input=new HVar{Type=Int};Output=new HVar{Type=Int};Join=new HBlock{Id=3,Statements=[new HReturn(new HLocal(Output){Type=Int})]};Yes=new HBlock{Id=1,Statements=[new HJump(Join)]};No=new HBlock{Id=2,Statements=[new HJump(Join)]};Branch=new HBranch(new HCompare(HCompareOp.Ne,new HBinary(HBinaryOp.And,new HOpaque("undefined"){Type=Int},new HConst(1,Int)){Type=Int},new HConst(0,Int)){Type=Bool},Yes,No);Entry=new HBlock{Id=0,Statements=[Branch]};Method=new HMethod{Method=Called,Blocks=[Entry,Yes,No,Join]};}
 public HCall Call()=>new(){Method=Called,This=new HArg(-1),Type=Int};
 public void Copies(HExpr a,HExpr b){Yes.Statements.Insert(0,new HAssign(new HLocal(Output){Type=Int},a));No.Statements.Insert(0,new HAssign(new HLocal(Output){Type=Int},b));}
}
