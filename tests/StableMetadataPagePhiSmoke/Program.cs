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
Run("second native call",false,change:f=>{var n=f.Node(Op.Call,VT.None,f.Const(VT.I64,0x2080));n.Aux=new CallInfo{Target=0x3000,Slots=[new(ArgSlotKind.IntReg,0)]};f.Insert(n);});
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
Console.WriteLine("METADATA_FLAG_REGION_FIXTURE positive=5 negative=23 checks="+checks+" failures=0");

int loopPositive=0,loopNegative=0;
void Loop(string name,bool expected,Action<Fixture>? change=null)
{
    Run(name,expected,spill:true,reload:true,phi:true,change:f=>
    {
        var entry=new Block{Id=10};var head=new Block{Id=11};var latch=new Block{Id=12};
        f.Fn.Blocks.InsertRange(0,[entry,head,latch]);
        entry.Succs.AddRange([head,latch]);head.Preds.AddRange([entry,latch]);
        head.Succs.Add(f.Guard);f.Guard.Preds.Add(head);
        latch.Preds.AddRange([f.Warm,entry]);latch.Succs.Add(head);
        f.Warm.Succs.Add(latch);f.Warm.Nodes.Clear();f.Warm.Nodes.Add(f.Fn.NewNode(Op.Jump,VT.None,f.Warm));
        entry.Nodes.Add(f.Fn.NewNode(Op.Branch,VT.None,entry,f.Const(VT.I1,1)));
        head.Nodes.Add(f.Fn.NewNode(Op.Jump,VT.None,head));latch.Nodes.Add(f.Fn.NewNode(Op.Jump,VT.None,latch));
        var a=f.Fn.NewNode(Op.Phi,VT.I64,head);var b=f.Fn.NewNode(Op.Phi,VT.I64,latch);
        a.In=[f.Const(VT.I64,0x2000),b];b.In=[a,f.Const(VT.I64,0x2000)];
        head.Phis.Add(a);latch.Phis.Add(b);
        var address=f.Fn.NewNode(Op.Add,VT.I64,f.Cold,a,f.Const(VT.I64,0x20));
        f.Cold.Nodes.Insert(f.Cold.Nodes.IndexOf(f.Mark),address);
        f.Flag.In[0]=address;f.Mark.In[0]=address;
        change?.Invoke(f);
    });
    if(expected)loopPositive++;else loopNegative++;
}
Loop("native nested loop page SCC",true);
Loop("seeded self page",true,f=>f.Flag.In[0].In[0].In[1]=f.Flag.In[0].In[0]);
Loop("literal mark with cyclic page read",true,f=>f.Mark.In[0]=f.Const(VT.I64,0x2020));
Loop("byte truncate mark preserved",true,f=>f.Mark.In[1]=f.Fn.NewNode(Op.Trunc,VT.I8,f.Cold,f.Const(VT.I32,1)));
Loop("different loop page seed",false,f=>f.Flag.In[0].In[0].In[1].In[1]=f.Const(VT.I64,0x3000));
Loop("unknown loop seed",false,f=>f.Flag.In[0].In[0].In[0]=f.Fn.NewNode(Op.Param,VT.I64,null));
Loop("undefined loop seed",false,f=>f.Flag.In[0].In[0].In[0]=f.Fn.NewNode(Op.Undef,VT.I64,null));
Loop("changing loop induction",false,f=>f.Flag.In[0].In[0].In[1].In[1]=f.Fn.NewNode(Op.Add,VT.I64,null,f.Flag.In[0].In[0],f.Const(VT.I64,0x1000)));
Loop("unseeded SCC",false,f=>{var a=f.Flag.In[0].In[0];var b=a.In[1];a.In=[b,b];b.In=[a,a];});
Loop("different phi width",false,f=>f.Flag.In[0].In[0].In[1].Type=VT.I32);
Loop("unaligned page seed",false,f=>f.Flag.In[0].In[0].In[0]=f.Const(VT.I64,0x2001));
Loop("zero page seed",false,f=>f.Flag.In[0].In[0].In[0]=f.Const(VT.I64,0));
Loop("offset outside one page",false,f=>f.Flag.In[0].In[1]=f.Const(VT.I64,4096));
Loop("different offset width",false,f=>f.Flag.In[0].In[1]=f.Const(VT.I32,0x20));
Loop("unreachable page definitions",false,f=>f.Fn.Entry.Succs.Clear());
Loop("phi not registered with block",false,f=>f.Flag.In[0].In[0].Block!.Phis.Clear());
Loop("phi predecessor count mismatch",false,f=>f.Flag.In[0].In[0].Block!.Preds.Clear());
Loop("phi predecessor edge mismatch",false,f=>f.Fn.Entry.Succs.Remove(f.Flag.In[0].In[0].Block!));
Loop("protected cold arm remains rejected",false,f=>f.Cold.Scope=0);
Loop("unknown native metadata helper",false,f=>((CallInfo)f.Call.Aux!).Target=0x3004);
Loop("second native call remains rejected",false,f=>{var n=f.Node(Op.Call,VT.None,f.Const(VT.I64,0x2080));n.Aux=new CallInfo{Target=0x3000,Slots=[new(ArgSlotKind.IntReg,0)]};f.Insert(n);});
Loop("non-LDRB remains rejected",false,f=>f.Image.Word(0x1000,0xd503201f));
Loop("non-STRB remains rejected",false,f=>f.Image.Word(0x1040,0xd503201f));
Loop("unrelated heap read remains rejected",false,f=>f.Insert(f.Node(Op.Load,VT.I64,f.Const(VT.I64,0x2100))));
Loop("unrelated heap write remains rejected",false,f=>f.Insert(f.Node(Op.Store,VT.None,f.Const(VT.I64,0x2100),f.Const(VT.I64,1))));
Loop("metadata slot remains rejected as flag",false,f=>f.Flag.In[0].In[1]=f.Const(VT.I64,0x80));
Loop("mark address differs",false,f=>f.Mark.In[0]=f.Const(VT.I64,0x2028));
Loop("mark before helper remains rejected",false,f=>{f.Cold.Nodes.Remove(f.Mark);f.Cold.Nodes.Insert(0,f.Mark);});
Loop("mark zero remains rejected",false,f=>f.Mark.In[1]=f.Const(VT.I8,0));
Console.WriteLine("STABLE_METADATA_PAGE_PHI_PASS positive="+loopPositive+" negative="+loopNegative+" checks="+checks+" failures=0");


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
