using System.Buffers.Binary;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Binary;

int checks=0;
void Run(string name,bool expected,bool spill=false,bool reload=false,bool phi=false,Action<Fixture>? change=null)
{
    var f=new Fixture(spill,reload,phi);change?.Invoke(f);
    bool got=MetadataFlagRegionProof.TryProve(f.Fn,f.Guard,f.Image,a=>a==0x3000,a=>a==0x2080,0xb8,out var flag,out var store,out ulong address);
    if(got!=expected || got && (flag!=f.Flag || store!=f.Mark || address!=0x2020))throw new InvalidDataException(name+": proof="+got+" expected="+expected);
    checks++;
}
Run("literal metadata-only arm",true);
Run("FP register spills",true,spill:true);
Run("same-class static pointer reload",true,reload:true);
Run("identical slot phi",true,phi:true);
Run("all compiler bookkeeping",true,spill:true,reload:true,phi:true);
Run("unknown metadata target",false,change:f=>((CallInfo)f.Call.Aux!).Target=0x3004);
Run("indirect metadata call",false,change:f=>((CallInfo)f.Call.Aux!).Indirect=true);
Run("intrinsic call",false,change:f=>((CallInfo)f.Call.Aux!).Intrinsic="unknown");
Run("nonreturning call",false,change:f=>((CallInfo)f.Call.Aux!).NoReturn=true);
Run("missing slot identity",false,change:f=>f.Call.In[0]=f.Const(VT.I64,0x2088));
Run("ambiguous phi slot",false,phi:true,change:f=>f.Call.In[0].In[1]=f.Const(VT.I64,0x2088));
Run("cyclic phi slot",false,phi:true,change:f=>f.Call.In[0].In[0]=f.Call.In[0]);
Run("heap read",false,change:f=>f.Insert(f.Node(Op.Load,VT.I64,f.Const(VT.I64,0x2100))));
Run("heap write",false,change:f=>f.Insert(f.Node(Op.Store,VT.None,f.Const(VT.I64,0x2100),f.Const(VT.I64,5))));
Run("second proven metadata initializer",true,change:f=>{var n=f.Node(Op.Call,VT.None,f.Const(VT.I64,0x2080));n.Aux=new CallInfo{Target=0x3000,Slots=[new(ArgSlotKind.IntReg,0)]};f.Cold.Nodes.Insert(f.Cold.Nodes.IndexOf(f.Mark),n);});
Run("observable arithmetic",false,change:f=>f.Insert(f.Node(Op.FAdd,VT.F32,f.Const(VT.F32,0),f.Const(VT.F32,0))));
Run("extra integer arithmetic",false,change:f=>f.Insert(f.Node(Op.Mul,VT.I64,f.Const(VT.I64,2),f.Const(VT.I64,3))));
Run("positive stack offset",false,change:f=>f.Insert(f.Node(Op.Store,VT.None,f.Node(Op.Add,VT.I64,f.Sp,f.Const(VT.I64,16)),f.Const(VT.I64,7))));
Run("out-of-frame offset",false,change:f=>f.Insert(f.Node(Op.Load,VT.I64,f.Node(Op.Add,VT.I64,f.Sp,f.Const(VT.I64,-65544)))));
Run("wrong static pointer offset",false,reload:true,change:f=>f.StaticAddress!.In[1]=f.Const(VT.I64,0xc0));
Run("flag marked before initialization",false,change:f=>{f.Cold.Nodes.Remove(f.Mark);f.Cold.Nodes.Insert(0,f.Mark);});
Run("flag writes zero",false,change:f=>f.Mark.In[1]=f.Const(VT.I8,0));
Run("flag is metadata storage",false,change:f=>{f.Flag.In[0]=f.Const(VT.I64,0x2080);f.Mark.In[0]=f.Const(VT.I64,0x2080);});
Run("extra predecessor",false,change:f=>f.Cold.Preds.Add(f.Warm));
Run("protected scope",false,change:f=>f.Cold.Scope=0);
Run("entry cold arm",false,change:f=>{f.Fn.Blocks.Remove(f.Cold);f.Fn.Blocks.Insert(0,f.Cold);});
Run("not native LDRB",false,change:f=>f.Image.Word(0x1000,0xd503201f));
Run("not native STRB",false,change:f=>f.Image.Word(0x1040,0xd503201f));
Console.WriteLine("ORIGINAL_METADATA_FLAG_REGION_FIXTURE_PASS checks="+checks);
int positive=6,negative=22;
Node C(VT type,long value)=>new(){Op=Op.Const,Type=type,Imm=value};
Node P(VT type,params Node[] inputs)=>new(){Op=Op.Phi,Type=type,In=inputs};
void Constant(string name,Node node,bool expected,ulong value=0)
{
    bool got=Normalizer.FlagConstant(node,out ulong actual);
    if(got!=expected||got&&actual!=value)
        throw new InvalidDataException(name+": constant proof="+got+" expected="+expected+" value="+actual);
    checks++;if(expected)positive++;else negative++;
}
var page=P(VT.I64,C(VT.I64,0x2000),C(VT.I64,0x2000));
Constant("identical constant page phi",page,true,0x2000);
Constant("nested identical page phi",P(VT.I64,page,C(VT.I64,0x2000)),true,0x2000);
Constant("page phi plus flag offset",new(){Op=Op.Add,Type=VT.I64,In=[page,C(VT.I64,0x20)]},true,0x2020);
Constant("truncate identical phi",new(){Op=Op.Trunc,Type=VT.I8,In=[P(VT.I64,C(VT.I64,0x120),C(VT.I64,0x120))]},true,0x20);
Constant("extend identical phi",new(){Op=Op.ZExt,Type=VT.I64,In=[P(VT.I8,C(VT.I8,0xff),C(VT.I8,0xff))]},true,0xff);
Constant("all integer bits preserved",P(VT.I64,C(VT.I64,-1),C(VT.I64,-1)),true,ulong.MaxValue);
Constant("empty phi",P(VT.I64),false);
Constant("different page values",P(VT.I64,C(VT.I64,0x2000),C(VT.I64,0x3000)),false);
Constant("different integer widths",P(VT.I64,C(VT.I64,1),C(VT.I32,1)),false);
Constant("unknown parameter arm",P(VT.I64,C(VT.I64,1),new(){Op=Op.Param,Type=VT.I64}),false);
Constant("undefined arm",P(VT.I64,C(VT.I64,1),new(){Op=Op.Undef,Type=VT.I64}),false);
Constant("nested ambiguous arm",P(VT.I64,C(VT.I64,1),P(VT.I64,C(VT.I64,1),C(VT.I64,2))),false);
var self=P(VT.I64,C(VT.I64,1));self.In=[C(VT.I64,1),self];
Constant("self cycle",self,false);
var cycle1=P(VT.I64);var cycle2=P(VT.I64);cycle1.In=[C(VT.I64,1),cycle2];cycle2.In=[C(VT.I64,1),cycle1];
Constant("mutual cycle",cycle1,false);
Node deep=C(VT.I64,1);for(int i=0;i<10;i++)deep=P(VT.I64,C(VT.I64,1),deep);
Constant("depth bound",deep,false);
Constant("floating phi",P(VT.F32,C(VT.F32,0x3f800000),C(VT.F32,0x3f800000)),false);
Constant("untyped phi",P(VT.None,C(VT.None,0),C(VT.None,0)),false);
Constant("select is not an unconditional merge",new(){Op=Op.Select,Type=VT.I64,In=[C(VT.I1,1),C(VT.I64,1),C(VT.I64,2)]},false);
void PagePhi(Fixture f)
{
    var merge=f.Fn.NewNode(Op.Phi,VT.I64,f.Guard,f.Const(VT.I64,0x2000),f.Const(VT.I64,0x2000));
    f.Guard.Phis.Add(merge);
    var address=f.Fn.NewNode(Op.Add,VT.I64,f.Guard,merge,f.Const(VT.I64,0x20));
    f.Flag.In[0]=address;f.Mark.In[0]=address;
}
void Region(string name,bool expected,Action<Fixture>? change=null)
{
    Run(name,expected,spill:true,reload:true,phi:true,change:f=>{PagePhi(f);change?.Invoke(f);});
    if(expected)positive++;else negative++;
}
Region("page phi with proven metadata cold arm",true);
Region("different flag pages remain unproven",false,f=>f.Flag.In[0].In[0].In[1]=f.Const(VT.I64,0x3000));
Region("different flag page widths remain unproven",false,f=>f.Flag.In[0].In[0].In[1]=f.Const(VT.I32,0x2000));
Region("cyclic flag page remains unproven",false,f=>f.Flag.In[0].In[0].In[1]=f.Flag.In[0].In[0]);
Region("unknown initializer still rejected",false,f=>((CallInfo)f.Call.Aux!).Target=0x3004);
Region("heap write still rejected",false,f=>f.Insert(f.Node(Op.Store,VT.None,f.Const(VT.I64,0x2100),f.Const(VT.I8,1))));
Region("unrelated heap read still rejected",false,f=>f.Insert(f.Node(Op.Load,VT.I64,f.Const(VT.I64,0x2100))));
Region("non-LDRB still rejected",false,f=>f.Image.Word(0x1000,0xd503201f));
Region("non-STRB still rejected",false,f=>f.Image.Word(0x1040,0xd503201f));
Region("ambiguous metadata slot still rejected",false,f=>f.Call.In[0].In[1]=f.Const(VT.I64,0x2088));
Region("nonmatching mark address still rejected",false,f=>f.Mark.In[0]=f.Const(VT.I64,0x2028));
Console.WriteLine("EXACT_PHI_AND_ORIGINAL_REGION_FIXTURE_PASS checks="+checks);
void UnrelatedTryRegion(Fixture f,bool observable=false)
{
    var gate=new Block{Id=3};var protectedBlock=new Block{Id=4,Scope=0};var handler=new Block{Id=5,Scope=1};
    f.Fn.TryRegions.Add(new TryRegionInfo{Index=0,Outer=-1,Funclet=0x1080});
    var test=f.Fn.NewNode(Op.Idiom,VT.I1,gate);test.Imm=(long)IdiomKind.TryEntry;test.Aux=0;
    gate.Nodes.Add(test);gate.Nodes.Add(f.Fn.NewNode(Op.Branch,VT.None,gate,test));gate.Succs.AddRange([handler,protectedBlock]);
    foreach(var block in new[]{protectedBlock,handler})
    {
        block.Preds.Add(gate);block.Succs.Add(f.Guard);f.Guard.Preds.Add(block);
        if(observable)block.Nodes.Add(f.Fn.NewNode(Op.Store,VT.None,block,f.Const(VT.I64,0x2100),f.Const(VT.I64,7)));
        block.Nodes.Add(f.Fn.NewNode(Op.Jump,VT.None,block));
    }
    f.Fn.Blocks.InsertRange(0,[gate,protectedBlock,handler]);
}
Region("outside unrelated try region",true,f=>UnrelatedTryRegion(f));
Region("unrelated protected state remains outside proof",true,f=>UnrelatedTryRegion(f,observable:true));
Region("protected guard is rejected",false,f=>{UnrelatedTryRegion(f);f.Guard.Scope=0;});
Region("handler guard is rejected",false,f=>{UnrelatedTryRegion(f);f.Guard.Scope=1;});
Region("protected cold arm is rejected",false,f=>{UnrelatedTryRegion(f);f.Cold.Scope=0;});
Region("handler cold arm is rejected",false,f=>{UnrelatedTryRegion(f);f.Cold.Scope=1;});
Region("protected warm join is rejected",false,f=>{UnrelatedTryRegion(f);f.Warm.Scope=0;});
Region("handler warm join is rejected",false,f=>{UnrelatedTryRegion(f);f.Warm.Scope=1;});
void Protected(Fixture f,int scope=0)
{
    f.Fn.TryRegions.Add(new TryRegionInfo{Index=0,Outer=-1,Funclet=0x1080});
    f.Guard.Scope=f.Cold.Scope=f.Warm.Scope=scope;
}
void Split(Fixture f)
{
    var tail=new Block{Id=6,Scope=f.Cold.Scope};
    int index=f.Cold.Nodes.IndexOf(f.Mark);var rest=f.Cold.Nodes.Skip(index).ToArray();f.Cold.Nodes.RemoveRange(index,f.Cold.Nodes.Count-index);
    foreach(var n in rest){n.Block=tail;tail.Nodes.Add(n);}
    f.Cold.Nodes.Add(f.Fn.NewNode(Op.Jump,VT.None,f.Cold));
    f.Cold.Succs.Clear();f.Cold.Succs.Add(tail);tail.Preds.Add(f.Cold);tail.Succs.Add(f.Warm);
    f.Warm.Preds.Remove(f.Cold);f.Warm.Preds.Add(tail);f.Fn.Blocks.Add(tail);
}
Region("uniform real try body",true,f=>Protected(f));
Region("split metadata mark block",true,f=>Split(f));
Region("split arm inside real try body",true,f=>{Protected(f);Split(f);});
Region("uniform handler remains rejected",false,f=>Protected(f,1));
Region("unknown uniform try index",false,f=>{f.Guard.Scope=f.Cold.Scope=f.Warm.Scope=2;});
Region("split arm changes EH scope",false,f=>{Protected(f);Split(f);f.Mark.Block!.Scope=1;});
Region("split arm gains external predecessor",false,f=>{Split(f);f.Mark.Block!.Preds.Add(f.Guard);});
Region("split arm calls unknown service",false,f=>{Split(f);var c=f.Fn.NewNode(Op.Call,VT.None,f.Mark.Block!,f.Const(VT.I64,0x2080));c.Aux=new CallInfo{Target=0x3004,Slots=[new(ArgSlotKind.IntReg,0)]};f.Mark.Block!.Nodes.Insert(0,c);});
Region("split arm writes game memory",false,f=>{Split(f);var b=f.Mark.Block!;b.Nodes.Insert(0,f.Fn.NewNode(Op.Store,VT.None,b,f.Const(VT.I64,0x2100),f.Const(VT.I64,7)));});
Region("metadata call after mark",false,f=>{f.Cold.Nodes.Remove(f.Call);f.Cold.Nodes.Insert(f.Cold.Nodes.Count-1,f.Call);});
Region("second unknown metadata target",false,f=>{var n=f.Node(Op.Call,VT.None,f.Const(VT.I64,0x2080));n.Aux=new CallInfo{Target=0x3004,Slots=[new(ArgSlotKind.IntReg,0)]};f.Insert(n);});
Node Carry(Fixture f,long value)
{
    var entry=f.Fn.Blocks.FirstOrDefault(b=>b.Id==10);
    Block loop;
    if(entry==null)
    {
        entry=new Block{Id=10};loop=new Block{Id=11};
        entry.Succs.Add(loop);loop.Preds.AddRange([entry,loop]);loop.Succs.AddRange([f.Guard,loop]);f.Guard.Preds.Add(loop);
        entry.Nodes.Add(f.Fn.NewNode(Op.Jump,VT.None,entry));
        var condition=f.Fn.NewNode(Op.Param,VT.I1,null);loop.Nodes.Add(f.Fn.NewNode(Op.Branch,VT.None,loop,condition));
        f.Fn.Blocks.InsertRange(0,[entry,loop]);
    }
    else loop=f.Fn.Blocks.Single(b=>b.Id==11);
    var phi=f.Fn.NewNode(Op.Phi,VT.I64,loop);phi.In=[f.Const(VT.I64,value),phi];loop.Phis.Add(phi);return phi;
}
Region("loop-carried exact initialization mark",true,f=>f.Mark.In[1]=f.Node(Op.Trunc,VT.I8,Carry(f,1)));
Region("loop-carried exact metadata slot",true,f=>f.Call.In[0]=Carry(f,0x2080));
Region("both slot and mark carried in real try body",true,f=>{Protected(f);f.Mark.In[1]=f.Node(Op.Trunc,VT.I8,Carry(f,1));f.Call.In[0]=Carry(f,0x2080);});
Region("changing loop mark",false,f=>{var p=Carry(f,1);p.In[1]=f.Const(VT.I64,2);f.Mark.In[1]=f.Node(Op.Trunc,VT.I8,p);});
Region("unknown loop mark",false,f=>{var p=Carry(f,1);p.In[1]=f.Fn.NewNode(Op.Undef,VT.I64,null);f.Mark.In[1]=f.Node(Op.Trunc,VT.I8,p);});
Region("unseeded loop mark",false,f=>{var p=Carry(f,1);p.In=[p,p];f.Mark.In[1]=f.Node(Op.Trunc,VT.I8,p);});
Region("changing metadata slot",false,f=>{var p=Carry(f,0x2080);p.In[1]=f.Const(VT.I64,0x2088);f.Call.In[0]=p;});
Region("unknown loop slot",false,f=>{var p=Carry(f,0x2080);p.In[1]=f.Fn.NewNode(Op.Param,VT.I64,null);f.Call.In[0]=p;});
Region("loop mark needs all CFG predecessors",false,f=>{var p=Carry(f,1);p.In=[f.Const(VT.I64,1),p,p];f.Mark.In[1]=f.Node(Op.Trunc,VT.I8,p);});
Region("loop constant cannot come from function entry",false,f=>{var p=Carry(f,1);f.Fn.Blocks.Remove(p.Block!);f.Fn.Blocks.Insert(0,p.Block!);f.Mark.In[1]=f.Node(Op.Trunc,VT.I8,p);});
Region("seeded arm cannot hide an unseeded component",false,f=>{var p=Carry(f,1);var bad=f.Fn.NewNode(Op.Phi,VT.I64,p.Block!);bad.In=[bad,bad];p.Block!.Phis.Add(bad);p.In[1]=bad;f.Mark.In[1]=f.Node(Op.Trunc,VT.I8,p);});
Console.WriteLine("METADATA_FLAG_EH_FIXTURE_PASS positive="+positive+" negative="+negative+" checks="+checks+" failures=0");

sealed class Fixture
{
    public readonly Function Fn=new(){Regs=RegisterModel.Arm64};
    public readonly Block Guard=new(){Id=0},Cold=new(){Id=1},Warm=new(){Id=2};
    public readonly FixtureImage Image=new();
    public readonly Node Sp,Flag,Mark,Call;
    public Node? StaticAddress;
    public Node Const(VT type,long value){var n=Fn.NewNode(Op.Const,type,null);n.Imm=value;return n;}
    public Node Node(Op op,VT type,params Node[] inputs)=>Fn.NewNode(op,type,Cold,inputs);
    public void Insert(Node n)=>Cold.Nodes.Insert(Cold.Nodes.Count-1,n);
    public Fixture(bool spill,bool reload,bool phi)
    {
        Fn.Blocks.AddRange([Guard,Cold,Warm]);Guard.Succs.AddRange([Warm,Cold]);Cold.Preds.Add(Guard);Cold.Succs.Add(Warm);Warm.Preds.AddRange([Guard,Cold]);
        Sp=Fn.NewNode(Op.Param,VT.I64,null);Sp.Imm=31;Fn.Params[Fn.Regs.StackPointer]=Sp;
        Node address=Node(Op.Add,VT.I64,Const(VT.I64,0x2000),Const(VT.I64,0x20));
        Flag=Fn.NewNode(Op.Load,VT.I8,Guard,address);Flag.Addr=0x1000;Guard.Nodes.Add(Flag);
        var test=Fn.NewNode(Op.CmpNe,VT.I1,Guard,Flag,Const(VT.I8,0));Guard.Nodes.Add(test);Guard.Nodes.Add(Fn.NewNode(Op.Branch,VT.None,Guard,test));
        var slot=Const(VT.I64,0x2080);
        if(phi){var merge=Fn.NewNode(Op.Phi,VT.I64,Guard,slot,Const(VT.I64,0x2080));Guard.Phis.Add(merge);slot=merge;}
        if(spill){var stack=Node(Op.Add,VT.I64,Sp,Const(VT.I64,-32));Cold.Nodes.Add(stack);Cold.Nodes.Add(Node(Op.Store,VT.None,stack,Const(VT.I64,0x3f800000)));}
        Call=Node(Op.Call,VT.None,slot);Call.Addr=0x1020;Call.Aux=new CallInfo{Target=0x3000,Slots=[new(ArgSlotKind.IntReg,0)]};Cold.Nodes.Add(Call);
        if(spill){var stack=Node(Op.Add,VT.I64,Sp,Const(VT.I64,-32));Cold.Nodes.Add(stack);Cold.Nodes.Add(Node(Op.Load,VT.I64,stack));}
        Mark=Node(Op.Store,VT.None,address,Const(VT.I8,1));Mark.Addr=0x1040;Cold.Nodes.Add(Mark);
        if(reload){var klass=Node(Op.Load,VT.I64,slot);Cold.Nodes.Add(klass);StaticAddress=Node(Op.Add,VT.I64,klass,Const(VT.I64,0xb8));Cold.Nodes.Add(StaticAddress);Cold.Nodes.Add(Node(Op.Load,VT.I64,StaticAddress));}
        Cold.Nodes.Add(Node(Op.Jump,VT.None));Warm.Nodes.Add(Fn.NewNode(Op.Return,VT.None,Warm));
    }
}
sealed class FixtureImage:NativeImage
{
    public override ImageFormat Format=>ImageFormat.Elf;
    public FixtureImage(){Arch=CpuArch.Arm64;PointerSize=8;MemoryBase=0x1000;Memory=new byte[0x2000];Sections.Add(new ImageSection(".text",0x1000,0x100,SectionFlags.Read|SectionFlags.Execute));Sections.Add(new ImageSection(".data",0x2000,0x100,SectionFlags.Read|SectionFlags.Write));Word(0x1000,0x39400000);Word(0x1040,0x39000000);}
    public void Word(ulong address,uint value)=>BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan((int)(address-MemoryBase)),value);
}
