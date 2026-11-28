using Rewind.Analysis.Ir;
using Rewind.Analysis.Passes;
using Rewind.Analysis.Recover;
using Rewind.Analysis.Runtime;

int positive=0,negative=0;
foreach(var registers in new[]{RegisterModel.Arm64,RegisterModel.Win64})
foreach(bool wide in new[]{false,true})
foreach(var kind in new[]{HelperKind.Modf,HelperKind.SinCos})
{
    var helper=new HelperInfo(kind,2,false,kind==HelperKind.Modf,"fixture"){FloatArgs=1,IsDouble=wide};
    int first=registers.SharedPositions?1:0,count=kind==HelperKind.SinCos?2:1;
    for(int i=0;i<count;i++)
    {
        int n=ScalarMathWriteExtent.Of(helper,new(ArgSlotKind.IntReg,first+i),registers);
        if(n!=(wide?8:4))throw new Exception("wrong output extent/ABI position");
        positive++;
    }
    foreach(var slot in new ArgSlot[]{new(ArgSlotKind.FloatReg,0),new(ArgSlotKind.Stack,0),new(ArgSlotKind.Target,0),
        new(ArgSlotKind.IntReg,-1),new(ArgSlotKind.IntReg,first-1),new(ArgSlotKind.IntReg,first+count),new(ArgSlotKind.IntReg,8)})
    {
        if(ScalarMathWriteExtent.Of(helper,slot,registers)!=-1)throw new Exception("nonoutput accepted");
        negative++;
    }
}
foreach(var helper in new[]{
 new HelperInfo(HelperKind.MathFunction,1,false,true,"sin"){FloatArgs=1},
 new HelperInfo(HelperKind.SinCos,2,false,false,"missing signature"){FloatArgs=0},
 new HelperInfo(HelperKind.Modf,2,true,false,"noreturn"){FloatArgs=1}})
{
 if(ScalarMathWriteExtent.Of(helper,new(ArgSlotKind.IntReg,0),RegisterModel.Arm64)!=-1)throw new Exception("unproved helper accepted");
 negative++;
}
var before=Fixture();var after=Fixture();
int baseline=Split(before,false),fixedGroups=Split(after,true);
if(baseline!=0||fixedGroups<1)throw new Exception($"lifetime proof failed: unknown={baseline} precise={fixedGroups}");
int calls=after.Blocks.SelectMany(b=>b.Nodes).Count(n=>!n.Dead&&n.Op==Op.Call);
if(calls!=3)throw new Exception("native call was removed");
Console.WriteLine($"SCALAR_MATH_WRITE_SMOKE_PASS positive={positive} negative={negative} unknown_split={baseline} precise_split={fixedGroups} preserved_calls={calls}");

static int Split(Function fn,bool precise)
{
 var helper=new HelperInfo(HelperKind.SinCos,2,false,false,"sincosf"){FloatArgs=1};
 int Extent(Node call,int input)
 {
  var info=(CallInfo)call.Aux!;
  if(info.Target==1)return 32;
  if(info.Target==2)return 12;
  return precise?ScalarMathWriteExtent.Of(helper,info.Slots[input],fn.Regs):-1;
 }
 bool Writes(Node call,int input)=>((CallInfo)call.Aux!).Target==1||precise&&((CallInfo)call.Aux!).Target==3;
 bool Reads(Node call,int input)=>((CallInfo)call.Aux!).Target==2;
 return StackSplitting.Run(fn,[-64],Extent,Writes,Reads);
}

static Function Fixture()
{
 var fn=new Function{Address=0x1000,Regs=RegisterModel.Arm64};
 Block entry=new(){Id=0},loop=new(){Id=1},sin=new(){Id=2},vector=new(){Id=3};
 fn.Blocks.AddRange([entry,loop,sin,vector]);
 var sp=fn.NewNode(Op.Param,VT.I64,null);sp.Imm=fn.Regs.StackPointer;fn.Params[fn.Regs.StackPointer]=sp;
 Node C(Block block,VT type,long value){var n=fn.NewNode(Op.Const,type,block);n.Imm=value;block.Nodes.Add(n);return n;}
 Node A(Block block,int offset){var n=fn.NewNode(Op.Add,VT.I64,block,sp,C(block,VT.I64,offset));block.Nodes.Add(n);return n;}
 Node N(Block block,Op op,VT type,params Node[] input){var n=fn.NewNode(op,type,block,input);block.Nodes.Add(n);return n;}
 void Link(Block from,params Block[] to){foreach(var b in to){from.Succs.Add(b);b.Preds.Add(from);}}
 var curve=N(entry,Op.Call,VT.None,A(entry,-64));curve.Aux=new CallInfo{Target=1,Slots=[new(ArgSlotKind.IntReg,8)]};
 N(entry,Op.Load,VT.I64,A(entry,-64));N(entry,Op.Jump,VT.None);Link(entry,loop);
 N(loop,Op.Branch,VT.None,C(loop,VT.I1,1));Link(loop,sin,vector);
 var sc=N(sin,Op.Call,VT.None,C(sin,VT.F32,BitConverter.SingleToInt32Bits(0.5f)),A(sin,-72),A(sin,-68));
 sc.Aux=new CallInfo{Target=3,Slots=[new(ArgSlotKind.FloatReg,0),new(ArgSlotKind.IntReg,0),new(ArgSlotKind.IntReg,1)]};
 N(sin,Op.Jump,VT.None);Link(sin,loop);
 for(int i=0;i<3;i++)N(vector,Op.Store,VT.None,A(vector,-64+i*4),C(vector,VT.F32,BitConverter.SingleToInt32Bits(i+1f)));
 var read=N(vector,Op.Call,VT.None,A(vector,-64));read.Aux=new CallInfo{Target=2,Slots=[new(ArgSlotKind.IntReg,0)]};
 N(vector,Op.Jump,VT.None);Link(vector,loop);
 return fn;
}
