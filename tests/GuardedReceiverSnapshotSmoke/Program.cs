using System.Buffers.Binary;
using System.Reflection;
using System.Runtime.CompilerServices;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Passes;
using Rewind.Analysis.Recover;
using Rewind.Binary;

// All bytes, addresses, graphs and runtime objects in this test are synthetic.
// No application metadata, native snippets or application-specific names.
int assertions=0;
void Check(bool pass,string why){assertions++;if(!pass)throw new Exception(why);}
const uint Ret=0xd65f03c0u,Kill=0xd2800000u,Nop=0xd503201fu;
bool Proves(uint[] words)=>Arm64ReceiverProof.IsUnused(new CodeImage(words,0x1000),0x1000,0x1000+(ulong)words.Length*4);
// Independently constructed forward diamond: both arms overwrite x0.
Check(Proves([0xb4000061u,Kill,Ret,0x52800000u,Ret]),"both synthetic entry paths kill receiver");
Check(!Proves([0xb4000061u,Kill,Ret,0xaa0003e2u,Ret]),"one arm reads receiver");
Check(!Proves([0xb4000061u,Kill,Ret,Ret]),"one arm returns receiver");
Check(!Proves([0x94000002u,Kill,Ret]),"unknown call before kill");
Check(!Proves([0x14000000u,Kill,Ret]),"cycle before kill");
Check(!Proves([Nop]),"truncated before kill");
var direct=new CodeImage([0x94000002u,Nop,Kill,Ret],0x2000);
Check(Arm64ReceiverProof.ExactDirectTransfer(direct,0x2000,0x2008,false),"exact synthetic BL");
Check(!Arm64ReceiverProof.ExactDirectTransfer(direct,0x2000,0x200c,false),"wrong target");
Check(!Arm64ReceiverProof.ExactDirectTransfer(direct,0x2000,0x2008,true),"wrong transfer kind");
Check(!Arm64ReceiverProof.ExactDirectTransfer(new CodeImage([0xd63f0020u,Nop,Kill,Ret],0x2000),0x2000,0x2008,false),"indirect transfer");
int nativeAssertions=assertions;

// Invoke the existing internal shape predicates without changing the public
// API or adding application fixtures to the tool. A missing predicate fails.
MethodInfo Predicate(string name)=>typeof(Normalizer).GetMethod(name,BindingFlags.Static|BindingFlags.NonPublic)??throw new Exception("missing predicate "+name);
Node? GuardValue(Node condition,int side)=>(Node?)Predicate("NullGuardValue").Invoke(null,[condition,side]);
Node? First(Block guard,Block next)=>(Node?)Predicate("FirstDirectCall").Invoke(null,[guard,next,null]);
var pointer=new Node{Op=Op.Load,Type=VT.I64};var zero=new Node{Op=Op.Const,Type=VT.I64};
var condition=new Node{Op=Op.CmpEq,Type=VT.I1,In=[pointer,zero]};
Check(GuardValue(condition,0)==pointer,"exact checked value identity");
Check(GuardValue(condition,1)==null,"wrong guard polarity");
Check(GuardValue(new Node{Op=Op.CmpEq,Type=VT.I1,In=[new Node{Op=Op.Load,Type=VT.I32},zero]},0)==null,"narrow value");
(Block Guard,Block Next,Node Call) GuardFixture()
{
    var g=new Block();var n=new Block{Preds=[g]};
    var prior=new Node{Op=Op.Call,Aux=new CallInfo{Target=0x3000},Block=g};
    var call=new Node{Op=Op.Call,Aux=new CallInfo{Target=0x4000},Block=n};
    g.Nodes=[pointer,prior,new Node{Op=Op.Branch,In=[condition],Block=g}];
    n.Nodes=[new Node{Op=Op.Add,Type=VT.I64,Block=n},call];return(g,n,call);
}
var accepted=GuardFixture();
Check(First(accepted.Guard,accepted.Next)==accepted.Call,"prior producer does not move the null check");
foreach(var (name,change) in new (string,Action<Block,Block,Node>)[]{
    ("alternate entry",(g,n,c)=>n.Preds.Add(new Block())),
    ("protected guard",(g,n,c)=>g.Scope=0),
    ("protected continuation",(g,n,c)=>n.Scope=0),
    ("heap read after guard",(g,n,c)=>n.Nodes.Insert(0,new Node{Op=Op.Load,Type=VT.I64})),
    ("write after guard",(g,n,c)=>n.Nodes.Insert(0,new Node{Op=Op.Store})),
    ("indirect callee",(g,n,c)=>((CallInfo)c.Aux!).Indirect=true),
    ("intrinsic callee",(g,n,c)=>((CallInfo)c.Aux!).Intrinsic="opaque"),
    ("nonreturning callee",(g,n,c)=>((CallInfo)c.Aux!).NoReturn=true),
})
{
    var f=GuardFixture();change(f.Guard,f.Next,f.Call);Check(First(f.Guard,f.Next)==null,name);
}
int guardAssertions=assertions-nativeAssertions;

// Exercise the production materialization planner on synthetic SSA. This
// calculation needs no model/metadata. Only its four working fields are set;
// it cannot silently fall back to a duplicate test implementation.
HashSet<Node> Plan(Function function)
{
    var builder=(HirBuilder)RuntimeHelpers.GetUninitializedObject(typeof(HirBuilder));
    void Set(string name,object value)=>(typeof(HirBuilder).GetField(name,BindingFlags.NonPublic|BindingFlags.Instance)??throw new Exception("missing planner field "+name)).SetValue(builder,value);
    var positions=new Dictionary<Node,int>();
    foreach(var b in function.Blocks)for(int i=0;i<b.Nodes.Count;i++)positions[b.Nodes[i]]=i;
    var plan=new HashSet<Node>();Set("_fn",function);Set("_uses",DeadCode.Uses(function));Set("_position",positions);Set("_materialize",plan);
    (typeof(HirBuilder).GetMethod("DecideMaterialization",BindingFlags.NonPublic|BindingFlags.Instance)??throw new Exception("missing planner")).Invoke(builder,null);
    return plan;
}
(Function Function,Node Snapshot,Node Producer,Node Consumer) SnapshotFixture(Op effect=Op.Call,bool split=false)
{
    var block=new Block{Id=0};var next=split?new Block{Id=1,Preds=[block]}:block;
    var address=new Node{Op=Op.Param,Type=VT.I64};
    var load=new Node{Op=Op.Load,Type=VT.I64,In=[address],Block=block};
    var producer=new Node{Op=effect,Type=VT.None,Aux=new CallInfo{Target=0x3000},Block=block};
    var consume=new Node{Op=Op.Call,Type=VT.None,In=[load],Aux=new CallInfo{Target=0x4000},Block=next};
    block.Nodes=[load,producer];
    if(split){block.Nodes.Add(new Node{Op=Op.Jump,Block=block});block.Succs=[next];}
    next.Nodes.Add(consume);next.Nodes.Add(new Node{Op=Op.Return,Block=next});
    return(new Function{Blocks=split?[block,next]:[block]},load,producer,consume);
}
foreach(var effect in new[]{Op.Call,Op.Store})
{
    var f=SnapshotFixture(effect);Check(Plan(f.Function).Contains(f.Snapshot),"capture before "+effect);
}
var cross=SnapshotFixture(split:true);Check(Plan(cross.Function).Contains(cross.Snapshot),"capture across block boundary");
var pure=SnapshotFixture(Op.Add);Check(!Plan(pure.Function).Contains(pure.Snapshot),"no unnecessary capture without intervening effect");
var unusedReturn=SnapshotFixture();
var projection=new Node{Op=Op.Proj,Type=VT.I64,In=[unusedReturn.Producer],Block=unusedReturn.Producer.Block};
unusedReturn.Producer.Block!.Nodes.Insert(2,projection);
unusedReturn.Consumer.In=[projection];
// A proven receiver rewrite must preserve an effectful producer even if its
// return value was used only as the stale receiver.
unusedReturn.Consumer.In=[unusedReturn.Snapshot];DeadCode.Run(unusedReturn.Function);
Check(!unusedReturn.Producer.Dead&&unusedReturn.Producer.Block.Nodes.Contains(unusedReturn.Producer)&&projection.Dead,"unused scalar return does not drop producer effect");

(string Trace,Type? Error) Execute(HashSet<Node> plan,Node snapshot,string mutation,bool oldNull=false)
{
    var trace=new List<string>();object original=new();object replacement=new();object? current=oldNull?null:original;
    // A materialized value is read at its original node, before the producer.
    object? saved=plan.Contains(snapshot)?current:null;
    try
    {
        trace.Add("producer");
        if(mutation=="throw")throw new ProducerException();
        current=mutation=="replace"?replacement:mutation=="clear"?null:current;
        object? receiver=plan.Contains(snapshot)?saved:current;
        if(receiver==null)throw new NullReferenceException();
        trace.Add(ReferenceEquals(receiver,original)?"consume:original":"consume:replacement");
        return(string.Join('|',trace),null);
    }
    catch(Exception e){return(string.Join('|',trace),e.GetType());}
}
int semantics=0;
foreach(var effect in new[]{Op.Call,Op.Store})
{
    var fixture=SnapshotFixture(effect);var plan=Plan(fixture.Function);
    foreach(var (mutation,oldNull,trace,error) in new (string,bool,string,Type?)[]{
        ("replace",false,"producer|consume:original",null),
        ("clear",false,"producer|consume:original",null),
        ("replace",true,"producer",typeof(NullReferenceException)),
        ("clear",true,"producer",typeof(NullReferenceException)),
        ("throw",false,"producer",typeof(ProducerException)),
        ("throw",true,"producer",typeof(ProducerException)),
    })
    {
        Check(Execute(plan,fixture.Snapshot,mutation,oldNull)==(trace,error),"snapshot effect/exception order "+effect+" "+mutation);semantics++;
    }
    var broken=new HashSet<Node>(plan);broken.Remove(fixture.Snapshot);
    Check(Execute(broken,fixture.Snapshot,"replace")!=("producer|consume:original",null),"detect synthetic reload mutant");
    Check(Execute(broken,fixture.Snapshot,"replace",true)!=("producer",typeof(NullReferenceException)),"detect lost original null check");
}
Console.WriteLine($"GUARDED_RECEIVER_SYNTHETIC_PASS native_assertions={nativeAssertions} guard_assertions={guardAssertions} semantic_cases={semantics} total_assertions={assertions} original_game_data=none");

sealed class ProducerException:Exception;
sealed class CodeImage:NativeImage
{
    public override ImageFormat Format=>ImageFormat.Elf;
    public CodeImage(uint[] words,ulong start)
    {
        Arch=CpuArch.Arm64;PointerSize=8;MemoryBase=start;Memory=new byte[words.Length*4];
        for(int i=0;i<words.Length;i++)BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan(i*4),words[i]);
        Sections.Add(new ImageSection(".text",MemoryBase,(ulong)Memory.Length,SectionFlags.Read|SectionFlags.Execute));
    }
}
