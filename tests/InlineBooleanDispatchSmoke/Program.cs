using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;

static void Check(bool value,string name) { if(!value) throw new Exception(name); }
int positive=0,negative=0;
void Accept(string name,Fixture f,bool expected)
{
 Check(InlineBooleanDispatch.TryFold(f.Caller,f.Body,f.Site,out var call),name);
 Check(call is { Virtual:false, Arguments:[HConst { Value:bool actual }] } && actual==expected && ReferenceEquals(call.Method,f.Wrapper),name+" result");
 Check(call!.This is HLocal receiver && ReferenceEquals(receiver.Variable,f.Receiver),name+" receiver");
 positive++;
}
void Reject(string name,Action<Fixture> mutate)
{
 var f=new Fixture();mutate(f);
 Check(!InlineBooleanDispatch.TryFold(f.Caller,f.Body,f.Site,out _),name);negative++;
}
Accept("true producer",new Fixture(),true);
var no=new Fixture();no.ActualProducer.Method=no.FalseProducer;Accept("false producer",no,false);
var negated=new Fixture();var branch=(HBranch)negated.Entry.Statements[0];branch.Condition=new HUnary(HUnaryOp.LogicalNot,branch.Condition){Type=negated.Bool};(branch.WhenTrue,branch.WhenFalse)=(branch.WhenFalse,branch.WhenTrue);Accept("native inverted branch",negated,true);
var direct=new Fixture();foreach(var arm in new[]{direct.TrueArm,direct.FalseArm}){((HAssign)arm.Statements[0]).Target=Fixture.Local(direct.Merge);arm.Statements.RemoveAt(1);}Accept("direct merge stores",direct,true);
Reject("body gap",f=>f.Body.Problems.Add("unknown"));
Reject("exception region",f=>f.Body.TryRegions[0]=new HTryRegion());
Reject("unknown scope",f=>f.Join.Scope=0);
Reject("extra block",f=>f.Body.Blocks.Add(new HBlock()));
Reject("missing block",f=>f.Body.Blocks.Remove(f.FalseArm));
Reject("extra entry effect",f=>f.Entry.Statements.Insert(0,new HEval(f.ActualProducer)));
Reject("not boolean condition",f=>((HBranch)f.Entry.Statements[0]).Condition=new HConst(true,f.Bool));
Reject("wrong parameter index",f=>((HBranch)f.Entry.Statements[0]).Condition=new HArg(1){Type=f.Bool});
Reject("nonboolean parameter",f=>f.Wrapper.Parameters[0].Type=f.Item.Sig);
Reject("additional parameter",f=>f.Wrapper.Parameters=[new ParamDef{Type=f.Bool},new ParamDef{Type=f.Bool}]);
Reject("private wrapper",f=>f.Wrapper.Flags=1);
Reject("static wrapper",f=>f.Wrapper.Flags=6|MethodDef.Static);
Reject("virtual wrapper",f=>f.Wrapper.Flags=6|0x40);
Reject("value receiver wrapper",f=>f.Owner.IsValueType=true);
Reject("nonvoid wrapper",f=>f.Wrapper.ReturnType=f.Item.Sig);
Reject("extra producer effect",f=>f.TrueArm.Statements.Insert(1,new HEval(f.ActualProducer)));
Reject("missing join",f=>((HJump)f.TrueArm.Statements[^1]).Target=f.FalseArm);
Reject("different merges",f=>((HAssign)f.TrueArm.Statements[1]).Target=Fixture.Local(new HVar{Type=f.Item.Sig}));
Reject("producer receiver differs",f=>f.TemplateProducer.This=new HArg(0){Type=f.Owner.Sig});
Reject("static producer",f=>f.TrueProducer.Flags=1|MethodDef.Static);
Reject("virtual producer",f=>f.TrueProducer.Flags=1|0x40);
Reject("producer belongs elsewhere",f=>f.TrueProducer.DeclaringType=f.Base);
Reject("producer argument",f=>f.TrueProducer.Parameters=[new ParamDef{Type=f.Bool}]);
Reject("producer result mismatch",f=>f.TrueProducer.ReturnType=f.Bool);
Reject("ambiguous producers",f=>((HCall)((HAssign)f.FalseArm.Statements[0]).Value).Method=f.TrueProducer);
Reject("escaped merge",f=>f.Merge.AddressTaken=true);
Reject("tail receiver differs",f=>f.TemplateConsumer.This=new HArg(0){Type=f.Owner.Sig});
Reject("tail argument differs",f=>f.TemplateConsumer.Arguments=[Fixture.Local(new HVar{Type=f.Item.Sig})]);
Reject("tail extra effect",f=>f.Join.Statements.Insert(1,new HEval(f.ActualProducer)));
Reject("tail returned value",f=>f.Join.Statements[1]=new HReturn(Fixture.Local(f.Merge)));
Reject("static consumer",f=>f.Consumer.Flags=6|MethodDef.Static);
Reject("virtual consumer",f=>f.Consumer.Flags=6|0x40);
Reject("consumer parameter mismatch",f=>f.Consumer.Parameters[0].Type=f.Bool);
Reject("actual foreign method",f=>f.ActualProducer.Method=f.Consumer);
Reject("different actual receiver",f=>f.ActualProducer.This=Fixture.Local(new HVar{Type=f.Owner.Sig}));
Reject("effectful actual receiver",f=>f.ActualConsumer.This=f.ActualProducer);
Reject("escaped actual receiver flag",f=>f.Receiver.AddressTaken=true);
Reject("escaped actual receiver expression",f=>f.Caller.Blocks.Add(new HBlock{Statements=[new HEval(new HAddressOf(Fixture.Local(f.Receiver)))]}));
Reject("receiver wrong type",f=>f.Receiver.Type=f.Item.Sig);
Reject("receiver expression wrong type",f=>f.ActualConsumer.This!.Type=f.Item.Sig);
Reject("actual virtual dispatch",f=>f.ActualConsumer.Virtual=true);
Reject("actual constrained dispatch",f=>f.ActualConsumer.Constrained=f.Owner.Sig);
Reject("actual generic dispatch",f=>f.ActualProducer.MethodArguments=[f.Bool]);
Reject("actual alternative dispatch",f=>f.ActualProducer.Alternatives.Add(f.TrueProducer));
Reject("actual extra argument",f=>f.ActualProducer.Arguments=[new HConst(true,f.Bool)]);
Reject("actual wrong call type",f=>f.ActualProducer.Type=f.Bool);
Console.WriteLine($"INLINE_BOOLEAN_DISPATCH_PASS positive={positive} negative={negative}");

sealed class Fixture
{
 public TypeSig Bool,Void;public TypeDef Owner,Item,Base;
 public MethodDef Wrapper,TrueProducer,FalseProducer,Consumer;
 public HVar Merge,Receiver;public HBlock Entry,TrueArm,FalseArm,Join;
 public HCall ActualConsumer,ActualProducer,TemplateConsumer,TemplateProducer;
 public HMethod Caller,Body;public HStmt Site;
 public static HLocal Local(HVar v)=>new(v){Type=v.Type};
 public Fixture()
 {
  var sf=new SigFactory();var asm=new AssemblyModel{Name="Test"};Bool=sf.Primitive(Il2CppTypeEnum.Boolean);Void=sf.Primitive(Il2CppTypeEnum.Void);
  TypeDef Type(int index,string name){var t=new TypeDef{Index=index,Name=name,Assembly=asm};t.Sig=sf.TypeDef(t);return t;}
  Base=Type(1,"Base");Owner=Type(2,"Wrapper");Owner.BaseType=Base.Sig;Item=Type(3,"Item");
  Wrapper=new MethodDef{Name="Dispatch",DeclaringType=Owner,Flags=6,ReturnType=Void,Parameters=[new ParamDef{Type=Bool}]};
  TrueProducer=new MethodDef{Name="GetTrue",DeclaringType=Owner,Flags=1,ReturnType=Item.Sig};
  FalseProducer=new MethodDef{Name="GetFalse",DeclaringType=Owner,Flags=1,ReturnType=Item.Sig};
  Consumer=new MethodDef{Name="Consume",DeclaringType=Base,Flags=6,ReturnType=Item.Sig,Parameters=[new ParamDef{Type=Item.Sig}]};
  Merge=new HVar{Name="merged",Type=Item.Sig};Receiver=new HVar{Name="receiver",Type=Owner.Sig};
  HCall Producer(MethodDef method,HExpr receiver)=>new(){Method=method,This=receiver,Type=Item.Sig};
  HCall Consume(HExpr receiver,HExpr arg)=>new(){Method=Consumer,This=receiver,Type=Item.Sig,Arguments=[arg]};
  TemplateProducer=Producer(TrueProducer,new HArg(-1){Type=Owner.Sig});
  var otherProducer=Producer(FalseProducer,new HArg(-1){Type=Owner.Sig});
  TemplateConsumer=Consume(new HArg(-1){Type=Owner.Sig},Local(Merge));
  Join=new HBlock{Id=3,Statements=[new HEval(TemplateConsumer),new HReturn(null)]};
  HBlock Arm(int id,HCall producer){var temp=new HVar{Name="temp"+id,Type=Item.Sig};return new HBlock{Id=id,Statements=[new HAssign(Local(temp),producer),new HAssign(Local(Merge),Local(temp)),new HJump(Join)]};}
  TrueArm=Arm(1,TemplateProducer);FalseArm=Arm(2,otherProducer);Entry=new HBlock{Id=0,Statements=[new HBranch(new HArg(0){Type=Bool},TrueArm,FalseArm)]};
  Body=new HMethod{Method=Wrapper,Blocks=[Entry,TrueArm,FalseArm,Join]};
  ActualProducer=Producer(TrueProducer,Local(Receiver));ActualConsumer=Consume(Local(Receiver),ActualProducer);Site=new HEval(ActualConsumer);
  Caller=new HMethod{Method=new MethodDef{Name="Caller",DeclaringType=Owner,ReturnType=Void},Blocks=[new HBlock{Statements=[Site,new HReturn(null)]}]};
 }
}
