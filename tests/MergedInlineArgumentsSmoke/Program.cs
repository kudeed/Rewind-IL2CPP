using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;

static void Check(bool ok,string name) { if(!ok) throw new Exception(name); }
int positive=0,negative=0;
void Accept(string name,Fixture f)
{
 string[] problems=f.Method.Problems.ToArray();
 Check(MergedInlineArguments.Run(f.Method),name);
 Check(f.Join.Statements.Count==1 && f.Join.Statements[0] is HReturn,name+" join");
 Check(f.Method.Problems.SequenceEqual(problems),name+" diagnostics preserved");
 foreach(var arm in new[]{f.Left,f.Right})
 {
  Check(arm.Statements[^2] is HEval or HAssign,name+" consumer at former tail");
  int references=0;FinallyFolding.Visit(arm.Statements[^2],e=>{if(e is HLocal l && f.Merge.Contains(l.Variable)) references++;});
  Check(references==0,name+" all merge arguments substituted");
 }
 Check(!MergedInlineArguments.Run(f.Method),name+" idempotent");positive++;
}
void Reject(string name,Action<Fixture> change,bool ctor=false)
{
 var f=new Fixture(ctor);change(f);string before=HirPrinter.Print(f.Method);
 Check(!MergedInlineArguments.Run(f.Method),name);
 Check(HirPrinter.Print(f.Method)==before,name+" atomic rejection");negative++;
}
Accept("two method paths",new Fixture());
Accept("four scalar aggregate",new Fixture(true));
foreach(bool ctor in new[]{false,true})
{
 var f=new Fixture(ctor);
 foreach(var block in f.Method.Blocks) foreach(var statement in block.Statements)
  FinallyFolding.Visit(statement,e=>{if(e is HLocal)e.Type=null;});
 Accept(ctor?"unannotated aggregate phi views":"unannotated scalar phi views",f);
}

var effects=new Fixture();effects.Left.Statements.Insert(0,new HEval(new HOpaque("kept effect")));Accept("effect before full tail stays",effects);
var gaps=new Fixture(true);gaps.Method.Problems.Add("unrelated retained gap");Accept("unrelated diagnostic retained",gaps);
var staticCall=new Fixture();staticCall.Call!.This=null;staticCall.Consumer.Flags|=MethodDef.Static;Accept("static consumer",staticCall);
var bits=new Fixture(true);((HAssign)bits.Right.Statements[0]).Value=new HConst(BitConverter.Int32BitsToSingle(unchecked((int)0x80000000)),bits.Number);((HAssign)bits.Right.Statements[1]).Value=new HConst(BitConverter.Int32BitsToSingle(unchecked((int)0x7FC00001)),bits.Number);Accept("signed zero and NaN payload",bits);
var values=((HNewObject)((HAssign)bits.Right.Statements[0]).Value).Arguments;
Check(BitConverter.SingleToInt32Bits((float)((HConst)values[0]).Value!)==unchecked((int)0x80000000),"negative zero exact");
Check(BitConverter.SingleToInt32Bits((float)((HConst)values[1]).Value!)==unchecked((int)0x7FC00001),"NaN payload exact");
Reject("EH",f=>f.Method.TryRegions[0]=new HTryRegion{Entry=f.Left,HandlerEntry=f.Right,Exception=f.Receiver});
Reject("unknown scope",f=>f.Left.Scope=0);
Reject("loop back edge",f=>f.Join.Statements[^1]=new HJump(f.Left));
Reject("foreign edge",f=>f.Entry.Statements.Add(new HJump(new HBlock())));
Reject("branch predecessor",f=>f.Left.Statements[^1]=new HBranch(new HConst(true,f.Bool),f.Join,f.Right));
Reject("missing predecessor definition",f=>f.Right.Statements.RemoveAt(0));
Reject("effect after arguments",f=>f.Left.Statements.Insert(1,new HEval(new HOpaque("effect"))));
Reject("unknown earlier incoming edge",f=>f.Method.Blocks.Add(new HBlock{Id=4,Statements=[new HJump(f.Join)]}));
Reject("extra merge read",f=>f.Join.Statements.Insert(1,new HEval(Fixture.Local(f.Merge[0]))));
Reject("extra merge definition",f=>f.Entry.Statements.Insert(0,new HAssign(Fixture.Local(f.Merge[0]),new HConst(0,f.Number))));
Reject("merge has address",f=>f.Merge[0].AddressTaken=true);
Reject("actual merge address without flag",f=>f.Entry.Statements.Insert(0,new HEval(new HAddressOf(Fixture.Local(f.Merge[0])))));
Reject("actual receiver address without flag",f=>f.Entry.Statements.Insert(0,new HEval(new HAddressOf(Fixture.Local(f.Receiver)))));
Reject("receiver marked alias",f=>f.Receiver.AddressTaken=true);
Reject("wrong receiver type",f=>f.Call!.This!.Type=f.Number);
Reject("virtual consumer flag",f=>f.Call!.Virtual=true);
Reject("virtual consumer definition",f=>f.Consumer.Flags|=MethodDef.Virtual);
Reject("constrained consumer",f=>f.Call!.Constrained=f.Owner.Sig);
Reject("ambiguous consumer",f=>f.Call!.Alternatives.Add(f.Consumer));
Reject("wrong parameter type",f=>f.Consumer.Parameters[0].Type=f.Bool);
Reject("wrong value type",f=>((HAssign)f.Left.Statements[0]).Value=new HConst(0f,f.Float));
Reject("hidden call argument",f=>((HAssign)f.Left.Statements[0]).Value=new HCall{Method=f.Consumer,Type=f.Number});
Reject("checked arithmetic",f=>((HAssign)f.Left.Statements[0]).Value=new HBinary(HBinaryOp.AddOvf,new HConst(1,f.Number),f.FieldRead(0)){Type=f.Number});
Reject("integer division",f=>((HAssign)f.Left.Statements[0]).Value=new HBinary(HBinaryOp.Div,f.FieldRead(0),new HConst(0,f.Number)){Type=f.Number});
Reject("native load",f=>((HAssign)f.Left.Statements[0]).Value=new HOpaque("load"){Type=f.Number});
Reject("static field",f=>f.Fields[0].Attrs|=FieldDef.Static);
Reject("reads merged value",f=>((HAssign)f.Left.Statements[0]).Value=Fixture.Local(f.Merge[0]));
Reject("already public only",f=>{f.Consumer.Flags=6;f.Fields[0].Attrs=6;});
Reject("consumer not first",f=>f.Join.Statements.Insert(0,new HEval(new HConst(0,f.Number))));
Reject("different argument order",f=>(f.Left.Statements[0],f.Left.Statements[1])=(f.Left.Statements[1],f.Left.Statements[0]),true);
Reject("duplicate constructor argument",f=>f.Creation!.Arguments[1]=Fixture.Local(f.Merge[0]),true);
Reject("constructor reads field target",f=>((HAssign)f.Join.Statements[0]).Target=f.FieldRead(0),true);
var formerlyAddressed=new Fixture(true);formerlyAddressed.Output.AddressTaken=true;Accept("constructor former frame local",formerlyAddressed);
Reject("actual output address",f=>f.Entry.Statements.Insert(0,new HEval(new HAddressOf(Fixture.Local(f.Output)))),true);
Reject("reference constructor",f=>f.ValueType.IsValueType=false,true);
Reject("partial merge set",f=>f.Right.Statements.RemoveAt(2),true);
Reject("null numeric value",f=>((HAssign)f.Right.Statements[0]).Value=new HConst(null,f.Number),true);
HCall Nest(Fixture f)
{
 var call=new HCall { Method=new MethodDef { Name="Convert",DeclaringType=f.ValueType,
  Flags=(ushort)(6|MethodDef.Static),ReturnType=f.ValueType.Sig,Parameters=[new ParamDef{Type=f.ValueType.Sig}] },
  Type=f.ValueType.Sig,Arguments=[f.Creation!] };
 f.Join.Statements[0]=new HAssign(Fixture.Local(f.Output),call){Address=0x100};return call;
}
void RejectNested(string name,Action<Fixture,HCall> change)
{
 var f=new Fixture(true);var call=Nest(f);change(f,call);string before=HirPrinter.Print(f.Method);int locals=f.Method.Locals.Count;
 Check(!MergedInlineArguments.Run(f.Method),name);Check(HirPrinter.Print(f.Method)==before && f.Method.Locals.Count==locals,name+" atomic rejection");negative++;
}
var nested=new Fixture(true);var enclosing=Nest(nested);int previousLocals=nested.Method.Locals.Count;
Check(MergedInlineArguments.Run(nested.Method),"nested struct constructor");
Check(nested.Join.Statements.Count==2 && nested.Join.Statements[0] is HAssign {Value:HCall} && nested.Join.Statements[1] is HReturn,"outer call remains in join");
var kept=(HCall)((HAssign)nested.Join.Statements[0]).Value;
Check(kept.Method==enclosing.Method && nested.Join.Statements[0].Address==0x100,"same enclosing operation and source site");
Check(kept.Arguments[0] is HLocal && nested.Method.Locals.Count==previousLocals+1,"one committed struct merge");
var temp=((HLocal)kept.Arguments[0]).Variable;
foreach(var arm in new[]{nested.Left,nested.Right})
{
 Check(arm.Statements[^2] is HAssign {Target:HLocal,Value:HNewObject},"only construction distributed");
 Check(((HLocal)((HAssign)arm.Statements[^2]).Target).Variable==temp,"both arms initialize same temporary");
 int calls=0;FinallyFolding.Visit(arm.Statements[^2],e=>{if(e is HCall)calls++;});Check(calls==0,"outer effect not duplicated");
}
Check(!MergedInlineArguments.Run(nested.Method),"nested idempotent");positive++;
RejectNested("nested instance receiver",(f,c)=>{c.Method.Flags=6;c.This=Fixture.Local(f.Receiver);});
RejectNested("nested earlier argument",(f,c)=>{c.Arguments=[new HConst(1,f.Number),f.Creation!];c.Method.Parameters=[new ParamDef{Type=f.Number},new ParamDef{Type=f.ValueType.Sig}];});
RejectNested("nested virtual call",(f,c)=>c.Virtual=true);
RejectNested("nested constrained call",(f,c)=>c.Constrained=f.ValueType.Sig);
RejectNested("nested alternative",(f,c)=>c.Alternatives.Add(c.Method));
RejectNested("nested parameter mismatch",(f,c)=>c.Method.Parameters[0].Type=f.Number);
RejectNested("nested return mismatch",(f,c)=>c.Method.ReturnType=f.Number);
RejectNested("nested aliased target",(f,c)=>f.Output.AddressTaken=true);
RejectNested("nested output field",(f,c)=>((HAssign)f.Join.Statements[0]).Target=f.FieldRead(0));
RejectNested("nested public inputs only",(f,c)=>{foreach(var field in f.Fields)field.Attrs=6;});
RejectNested("nested actual input address",(f,c)=>f.Entry.Statements.Insert(0,new HEval(new HAddressOf(Fixture.Local(f.Merge[0])))));
Console.WriteLine($"MergedInlineArgumentsSmoke passed: {positive} positive, {negative} negative");

sealed class Fixture
{
 public SigFactory Sigs=new();public TypeSig Number,Float,Bool,Void;
 public TypeDef Owner,User,ValueType;public HVar Receiver,Output;public HVar[] Merge;public FieldDef[] Fields;
 public HBlock Entry,Left,Right,Join;public HMethod Method;public MethodDef Consumer;public HCall? Call;public HNewObject? Creation;
 public static HLocal Local(HVar v)=>new(v){Type=v.Type};
 public HField FieldRead(int i)=>new(){Object=Local(Receiver),Field=Fields[i],Type=Number};
 public Fixture(bool ctor=false)
 {
  var asm=new AssemblyModel{Name="Test"};TypeDef Make(int index,string name,bool value=false){var t=new TypeDef{Index=index,Name=name,Assembly=asm,IsValueType=value};t.Sig=Sigs.TypeDef(t);return t;}
  Owner=Make(1,"Owner");User=Make(2,"Caller");ValueType=Make(3,"Value",true);
  Float=Sigs.Primitive(Il2CppTypeEnum.R4);Number=ctor?Float:Sigs.Primitive(Il2CppTypeEnum.I4);Bool=Sigs.Primitive(Il2CppTypeEnum.Boolean);Void=Sigs.Primitive(Il2CppTypeEnum.Void);
  int n=ctor?4:1;Receiver=new HVar{Name="receiver",Type=Owner.Sig};Output=new HVar{Name="output",Type=ValueType.Sig};
  Merge=Enumerable.Range(0,n).Select(i=>new HVar{Name="m"+i,Type=Number}).ToArray();
  Fields=Enumerable.Range(0,n).Select(i=>new FieldDef{Name="f"+i,Type=Number,DeclaringType=Owner,Attrs=1}).ToArray();
  Consumer=new MethodDef{Name=ctor?".ctor":"Step",DeclaringType=ctor?ValueType:Owner,Flags=(ushort)(ctor?6:1),ReturnType=Void,Parameters=Enumerable.Range(0,n).Select(i=>new ParamDef{Type=Number}).ToArray()};
  HStmt use;
  if(ctor){Creation=new HNewObject{Constructor=Consumer,Type=ValueType.Sig,Arguments=Merge.Select(v=>(HExpr)Local(v)).ToArray()};use=new HAssign(Local(Output),Creation);}
  else {Call=new HCall{Method=Consumer,This=Local(Receiver),Type=Void,Arguments=[Local(Merge[0])]};use=new HEval(Call);}
  Join=new HBlock{Id=3,Statements=[use,new HReturn(null)]};
  Left=new HBlock{Id=1};Right=new HBlock{Id=2};
  for(int i=0;i<n;i++)
  {
   HExpr value=FieldRead(i);if(!ctor)value=new HUnary(HUnaryOp.Neg,value){Type=Number};
   Left.Statements.Add(new HAssign(Local(Merge[i]),value));
   Right.Statements.Add(new HAssign(Local(Merge[i]),ctor?new HConst(i==3?1f:0f,Number):FieldRead(i)));
  }
  Left.Statements.Add(new HJump(Join));Right.Statements.Add(new HJump(Join));
  Entry=new HBlock{Id=0,Statements=[new HBranch(new HArg(0){Type=Bool},Left,Right)]};
  Method=new HMethod{Method=new MethodDef{Name="Run",DeclaringType=User,ReturnType=Void},Locals=[Receiver,Output,..Merge],Blocks=[Entry,Left,Right,Join]};
 }
}
