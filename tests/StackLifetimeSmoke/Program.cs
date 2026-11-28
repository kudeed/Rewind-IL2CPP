using Rewind.Analysis.Ir;
using Rewind.Analysis.Passes;
static void Check(bool pass,string message){if(!pass)throw new InvalidOperationException(message);}
static (Function Fn,Block Body,Node Park,Node Load,Node Call,Node Source) ParkFixture(int callAt=-40,bool overwrite=false)
{
    var fn=new Function{Regs=RegisterModel.Arm64};var body=new Block{Id=0,Scope=-1};fn.Blocks=[body];
    var sp=fn.NewNode(Op.Param,VT.I64,null);fn.Params[fn.Regs.StackPointer]=sp;
    Node Constant(long value){var n=fn.NewNode(Op.Const,VT.I64,null);n.Imm=value;return n;}
    Node Address(int offset){var n=fn.NewNode(Op.Add,VT.I64,body,sp,Constant(offset));body.Nodes.Add(n);return n;}
    var source=Address(-96);var slot=Address(-32);
    var park=fn.NewNode(Op.Store,VT.None,body,slot,source);body.Nodes.Add(park);
    var arg=Address(callAt);var call=fn.NewNode(Op.Call,VT.None,body,arg);call.Aux=new CallInfo{Target=0x2000,Slots=[new(ArgSlotKind.IntReg,0)]};body.Nodes.Add(call);
    if(overwrite){var at=Address(-28);var value=fn.NewNode(Op.Const,VT.I32,null);value.Imm=17;body.Nodes.Add(fn.NewNode(Op.Store,VT.None,body,at,value));}
    var load=fn.NewNode(Op.Load,VT.I64,body,slot);body.Nodes.Add(load);body.Nodes.Add(fn.NewNode(Op.Return,VT.None,body,load));
    return(fn,body,park,load,call,source);
}
foreach(var extent in new[]{StackPromotion.NotTaken,8})
{
    var x=ParkFixture();Check(ParkedAddresses.Run(x.Fn,(_,_)=>extent),"Valid parked pointer was not resolved for extent="+extent);
    Check(x.Load.Dead && x.Park.Dead,"Resolved pointer kept memory side effects");
    var returned=x.Body.Nodes[^1].In[0];Check(returned.Op==Op.Add && returned.In[1].Imm==-96,"Wrong parked pointer target");
}
var negative=new (int At,int Extent,bool Partial)[]{(-40,16,false),(-32,8,false),(-40,-1,false),(-40,StackPromotion.NotTaken,true)};
foreach(var test in negative)
{
    var x=ParkFixture(test.At,test.Partial);var before=x.Body.Nodes.ToArray();
    Check(!ParkedAddresses.Run(x.Fn,(_,_)=>test.Extent),"Unsafe parked pointer was resolved");
    Check(x.Body.Nodes.SequenceEqual(before)&&!x.Load.Dead&&!x.Park.Dead,"Rejected alias case was mutated");
}
Console.WriteLine("PARKED_UNTAKEN_SMOKE_PASS positive2 negative4 exact-target effects-preserved");
static (Function Fn,Block Gate,Block Body,Block Handler,Node Store,Node Call) PrologueFixture(int scope=-1)
{
    var fn=new Function{Regs=RegisterModel.Arm64};var gate=new Block{Id=0,Scope=scope};var body=new Block{Id=1,Scope=2*(scope+1)};var handler=new Block{Id=2,Scope=2*(scope+1)+1};
    int region=scope+1;for(int j=0;j<=region;j++)fn.TryRegions.Add(new TryRegionInfo{Index=j,Outer=j==region?scope:-1});
    var sp=fn.NewNode(Op.Param,VT.I64,null);fn.Params[fn.Regs.StackPointer]=sp;fn.Blocks=[gate,body,handler];
    var entry=fn.NewNode(Op.Idiom,VT.I1,gate);entry.Imm=(long)IdiomKind.TryEntry;entry.Aux=region;
    gate.Nodes=[entry,fn.NewNode(Op.Branch,VT.None,gate,entry)];gate.Succs=[handler,body];body.Preds=[gate];handler.Preds=[gate];
    var offset=fn.NewNode(Op.Const,VT.I64,null);offset.Imm=-32;
    var address=fn.NewNode(Op.Add,VT.I64,body,sp,offset);
    var value=fn.NewNode(Op.Const,VT.I64,null);value.Imm=123;
    var store=fn.NewNode(Op.Store,VT.None,body,address,value);
    var call=fn.NewNode(Op.Call,VT.None,body);call.Aux=new CallInfo{Target=0x3000};
    body.Nodes=[address,store,call,fn.NewNode(Op.Return,VT.None,body)];handler.Nodes=[fn.NewNode(Op.Return,VT.None,handler)];
    return(fn,gate,body,handler,store,call);
}
foreach(int scope in new[]{-1,0,2})
{
    var x=PrologueFixture(scope);Check(TryPrologues.Run(x.Fn),"Valid nonthrowing stack prefix did not move");
    Check(x.Gate.Nodes[^2]==x.Store && x.Store.Block==x.Gate && x.Body.Nodes[0]==x.Call,"Prologue ordering or first throwing call changed");
    Check(!TryPrologues.Run(x.Fn),"Prologue pass was not idempotent");
}
var mutations=new Action<(Function Fn,Block Gate,Block Body,Block Handler,Node Store,Node Call)>[]{
    x=>x.Body.Preds.Add(new Block()),
    x=>x.Body.Phis.Add(new Node{Op=Op.Phi,Type=VT.I64}),
    x=>{x.Body.Nodes.Remove(x.Call);x.Body.Nodes.Insert(0,x.Call);},
    x=>x.Body.Nodes.Insert(0,new Node{Op=Op.Load,Type=VT.I64,In=[new Node{Op=Op.Param,Type=VT.I64}]}),
    x=>x.Body.Nodes.Insert(0,new Node{Op=Op.DivU,Type=VT.I64}),
    x=>{x.Store.In[0]=new Node{Op=Op.Param,Type=VT.I64};},
};
foreach(var mutate in mutations)
{
    var x=PrologueFixture();mutate(x);var before=x.Body.Nodes.ToArray();Check(!TryPrologues.Run(x.Fn),"Unsafe try prefix moved");
    Check(x.Body.Nodes.SequenceEqual(before),"Rejected try prefix was mutated");
}
Console.WriteLine("LATE_TRY_PROLOGUE_SMOKE_PASS outer-and-nested3 negative6 idempotent first-throw-boundary");
var factory=new Rewind.Model.SigFactory();var scalar=factory.Primitive(Rewind.Runtime.Il2CppTypeEnum.I4);
var fieldDef=new Rewind.Model.FieldDef{Name="array",Type=scalar};
Rewind.Model.TypeLayout Layout(int at=8,int size=16)=>new(){Known=true,Size=24,Fields=[new(fieldDef,scalar,at,size)]};
var selector=typeof(Rewind.Analysis.Recover.HirBuilder).GetMethod("LeadingPaddingField",System.Reflection.BindingFlags.Static|System.Reflection.BindingFlags.NonPublic)!;
Rewind.Model.FieldSlot? Pick(Rewind.Model.TypeLayout layout,int offset=6,int size=18,int pointer=8)=>(Rewind.Model.FieldSlot?)selector.Invoke(null,[layout,offset,size,pointer]);
Check(Pick(Layout()) is {Offset:8,Size:16},"Original two-byte padding copy not recognized");
Check(Pick(Layout(8,16),4,20) is {Offset:8,Size:16},"Four-byte padding copy not recognized");
var badPadding=new Action<Rewind.Model.TypeLayout>[]{
    x=>x.Known=false,x=>x.Size=23,x=>x.Fields=[x.Fields[0],new(new Rewind.Model.FieldDef{Name="observed"},scalar,6,2)],
    x=>x.Fields=[x.Fields[0],new(new Rewind.Model.FieldDef{Name="overlap"},scalar,8,4)],
    x=>x.Fields=[x.Fields[0],x.Fields[0]],x=>x.Fields[0]=x.Fields[0] with {Size=15},
};
foreach(var mutate in badPadding){var layout=Layout();mutate(layout);Check(Pick(layout)==null,"Unsafe padded field view accepted");}
Check(Pick(Layout(),8,16)==null&&Pick(Layout(),-1,25)==null&&Pick(Layout(),6,17)==null&&Pick(Layout(),0,24)==null&&Pick(Layout(),6,18,16)==null&&Pick(Layout(),int.MaxValue,18)==null,"Invalid padded copy bounds accepted");
Console.WriteLine("LEADING_PADDING_COPY_SMOKE_PASS positive2 negative12 complete-field-only no-overlap exact-bounds");

var guardFold=typeof(Rewind.Analysis.Arm64.A64Lifter).GetMethod("FoldResolvedStackGuardReads",System.Reflection.BindingFlags.Static|System.Reflection.BindingFlags.NonPublic)!;
(Function Fn,Node Load,Node Base,Node Offset) GuardFixture()
{
    var fn=new Function{Regs=RegisterModel.Arm64};var block=new Block{Id=0};fn.Blocks=[block];
    var pointer=fn.NewNode(Op.Param,VT.I64,null);pointer.Imm=33;
    var offset=fn.NewNode(Op.Const,VT.I64,null);offset.Imm=40;
    var address=fn.NewNode(Op.Add,VT.I64,block,pointer,offset);var load=fn.NewNode(Op.Load,VT.I64,block,address);
    block.Nodes=[address,load,fn.NewNode(Op.Return,VT.None,block,load)];return(fn,load,pointer,offset);
}
var guard=GuardFixture();Check((int)guardFold.Invoke(null,[guard.Fn])! ==1 && guard.Load.Op==Op.Const && guard.Load.Imm==0x5354414B47554152,"Resolved bionic TLS guard not folded");
var guardNegatives=new Action<(Function Fn,Node Load,Node Base,Node Offset)>[]{
    x=>x.Base.Imm=32,x=>x.Base.Op=Op.Undef,x=>x.Offset.Imm=39,x=>x.Offset.Imm=48,
    x=>x.Load.Type=VT.I32,x=>x.Load.Op=Op.Store,x=>x.Load.Dead=true,
    x=>x.Load.In[0].Op=Op.Sub,x=>x.Offset.Op=Op.Param,
};
foreach(var mutate in guardNegatives){var fixture=GuardFixture();mutate(fixture);var original=fixture.Load.Op;Check((int)guardFold.Invoke(null,[fixture.Fn])! ==0 && fixture.Load.Op==original,"Unsafe TLS load folded");}
Console.WriteLine("RESOLVED_STACK_GUARD_SMOKE_PASS positive1 negative9 exact-existing-guard-contract");
