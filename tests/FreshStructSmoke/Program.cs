using System.Reflection;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

var analysis=typeof(ProgramAnalysis).Assembly;
var run=analysis.GetType("Rewind.Analysis.Recover.FreshStructNullInitialization",true)!.GetMethods(BindingFlags.Static|BindingFlags.NonPublic)
    .Single(m=>m.Name=="Run"&&m.GetParameters().Length==3&&m.GetParameters()[1].ParameterType==typeof(Func<HVar,FieldDef,bool>));
int positive=0,negative=0;
int Apply(Fixture f,bool layout=true,bool setters=true)
{
    Func<HVar,FieldDef,bool> valid=(_,_)=>layout;
    Func<HCall,FieldDef?> pure=c=>setters&&c.Method==f.Setter?f.Flag:null;
    return (int)run.Invoke(null,[f.H,valid,pure])!;
}
void Check(string name,Fixture f,int expected,bool layout=true,bool setters=true)
{
    int before=f.H.Blocks.Sum(b=>b.Statements.Count);
    string[] calls=Calls(f.H);
    int actual=Apply(f,layout,setters);
    if(actual!=expected||before-f.H.Blocks.Sum(b=>b.Statements.Count)!=expected||
        !calls.SequenceEqual(Calls(f.H))||Apply(f,layout,setters)!=0)
        throw new Exception(name+": wrong fold/count/call-preservation/idempotence "+actual+" expected "+expected);
    if(expected>0)positive++;else negative++;
}
Fixture Straight(params string[] operations)
{
    var f=new Fixture();f.Entry.Statements.Add(f.Default());
    foreach(var op in operations) f.Entry.Statements.Add(op switch {
        "nullA"=>f.Store(f.A,null),"nullB"=>f.Store(f.B,null),"liveA"=>f.Store(f.A,"live"),
        "setter"=>new HEval(f.Set()),"mutator"=>new HEval(f.Unknown()),"escape"=>new HEval(f.Escape()),
        "reset"=>f.Default(),_=>throw new Exception(op)});
    f.Entry.Statements.Add(new HReturn(null));return f;
}
Check("one fresh reference",Straight("nullA"),1);
Check("two fresh references and public setter",Straight("setter","nullA","nullB"),2);
Check("duplicate null writes",Straight("nullA","nullA"),2);
var diamond=Straight();
var left=new HBlock{Id=1};var right=new HBlock{Id=2};var join=new HBlock{Id=3};
diamond.Entry.Statements[^1]=new HBranch(new HArg(0){Type=diamond.Bool},left,right);
left.Statements.Add(new HEval(diamond.Set()));left.Statements.Add(new HJump(join));
right.Statements.Add(new HJump(join));join.Statements.Add(diamond.Store(diamond.A,null));join.Statements.Add(new HReturn(null));
diamond.H.Blocks.AddRange([left,right,join]);
Check("all paths preserve fresh field",diamond,1);
Check("earlier non-null value",Straight("liveA","nullA"),0);
Check("unknown struct mutator",Straight("mutator","nullA"),0);
Check("address escapes",Straight("escape","nullA"),0);
Check("escape followed by reset remains unsafe",Straight("escape","reset","nullA"),0);
Check("overlapping or unknown layout",Straight("nullA"),0,layout:false);
Check("unproven setter",Straight("setter","nullA"),0,setters:false);
var missing=Straight("nullA");missing.Entry.Statements.RemoveAt(0);Check("no dominating default",missing,0);
var wrong=Straight("nullA");((HTypeExpr)((HAssign)wrong.Entry.Statements[0]).Value).Target=wrong.Ref;Check("default has another type",wrong,0);
var after=Straight("nullA");(after.Entry.Statements[0],after.Entry.Statements[1])=(after.Entry.Statements[1],after.Entry.Statements[0]);Check("default after candidate",after,0);
var problem=Straight("nullA");problem.H.Problems.Add("unrecovered input");Check("pending problem",problem,0);
var scope=Straight("nullA");scope.Entry.Scope=0;Check("exception scope",scope,0);
var pub=Straight("nullA");pub.A.Attrs=6;Check("public field outside scope",pub,0);
var readonlyField=Straight("nullA");readonlyField.A.Attrs|=FieldDef.InitOnly;Check("initonly outside scope",readonlyField,0);
var reassigned=Straight("nullA");reassigned.Entry.Statements.Insert(1,new HAssign(reassigned.Local(),new HArg(0){Type=reassigned.Struct.Sig}));Check("whole struct reassigned",reassigned,0);
var onePath=Straight();left=new HBlock{Id=1};right=new HBlock{Id=2};join=new HBlock{Id=3};
onePath.Entry.Statements[^1]=new HBranch(new HArg(0){Type=onePath.Bool},left,right);
left.Statements.Add(onePath.Store(onePath.A,"live"));left.Statements.Add(new HJump(join));
right.Statements.Add(new HJump(join));join.Statements.Add(onePath.Store(onePath.A,null));join.Statements.Add(new HReturn(null));
onePath.H.Blocks.AddRange([left,right,join]);Check("one path writes a live value",onePath,0);
var cycle=Straight();var loop=new HBlock{Id=1};join=new HBlock{Id=2};
cycle.Entry.Statements[^1]=new HJump(loop);loop.Statements.Add(new HBranch(new HArg(0){Type=cycle.Bool},loop,join));join.Statements.Add(cycle.Store(cycle.A,null));join.Statements.Add(new HReturn(null));cycle.H.Blocks.AddRange([loop,join]);Check("cycle in proof region",cycle,0);
var beforeDefault=Straight("nullA");beforeDefault.Entry.Statements.Insert(0,new HEval(beforeDefault.Escape()));Check("alias before initialization",beforeDefault,0);
var ownSetter=Straight("setter","nullA");ownSetter.SetterTarget=ownSetter.A;
// The test policy itself must also reject a setter of the field under proof.
Func<HVar,FieldDef,bool> goodLayout=(_,_)=>true;Func<HCall,FieldDef?> targetSetter=_=>ownSetter.A;
if((int)run.Invoke(null,[ownSetter.H,goodLayout,targetSetter])! !=0)throw new Exception("setter of target field accepted");
negative++;

var match=analysis.GetType("Rewind.Analysis.Recover.Arm64ChainedGetter",true)!.GetMethods(BindingFlags.Static|BindingFlags.NonPublic)
    .Single(m=>m.Name=="Matches"&&m.GetParameters().Length==6);
uint[] reference=[0xf9401008,0xb4000068,0xf9401900,0xd65f03c0,0xf81f0ffe,0x97fbe98d];
ulong address=0x245B018;
long delta=((long)(int)(reference[5]<<6)>>6)*4;
ulong target=unchecked((ulong)((long)address+20+delta));
bool Match(uint[] words,int width=8,int first=32,int second=48,bool nullHelper=true)
{
    Func<ulong,bool> helper=a=>nullHelper&&a==target;
    return (bool)match.Invoke(null,[words,first,second,address,helper,width])!;
}
if(!Match(reference))throw new Exception("original 64-bit reference getter rejected");
uint[] scalar=(uint[])reference.Clone();scalar[2]=0xb9403100;
if(!Match(scalar,4))throw new Exception("existing 32-bit getter rejected");
int nativeNegative=0;
void Reject(uint[] words,int width=8,int first=32,int second=48,bool helper=true)
{if(Match(words,width,first,second,helper))throw new Exception("negative native sequence accepted");nativeNegative++;}
foreach(var (at,value) in new (int,uint)[]{(0,0xf9401000),(0,0xf940101f),(0,0xb9401008),(1,0xb5000068),(1,0xb4000048),(1,0xb4000069),(2,0xb9403100),(2,0xf9401901),(2,0xf9401920),(3,0xd65f0000),(4,0xf9000ffe),(5,0x14000000),(5,reference[5]+1)})
{var words=(uint[])reference.Clone();words[at]=value;Reject(words);}
Reject(reference[..5]);Reject([..reference,0xd503201f]);Reject(reference,width:16);
Reject(reference,first:31);Reject(reference,second:52);Reject(reference,first:32768);Reject(reference,second:32768);Reject(reference,helper:false);
Console.WriteLine($"FRESH_STRUCT_SMOKE_PASS positive={positive} negative={negative} native_positive=2 native_negative={nativeNegative}");

static string[] Calls(HMethod h)=>h.Blocks.SelectMany(b=>b.Statements).OfType<HEval>()
    .Where(s=>s.Expression is HCall).Select(s=>((HCall)s.Expression).Method.FullName).ToArray();

sealed class Fixture
{
    public readonly SigFactory Sigs=new();
    public readonly TypeSig Bool;
    public readonly TypeSig Void;
    public readonly TypeSig Ref;
    public readonly TypeDef Struct;
    public readonly HMethod H;
    public readonly HBlock Entry=new(){Id=0};
    public readonly HVar V;
    public readonly FieldDef A,B,Flag;
    public readonly MethodDef Setter,Mutator,ByRefCall;
    public FieldDef? SetterTarget;
    public Fixture()
    {
        Bool=Sigs.Primitive(Il2CppTypeEnum.Boolean);Void=Sigs.Primitive(Il2CppTypeEnum.Void);
        var image=new AssemblyModel{Name="Fixture"};
        var r=new TypeDef{Index=1,Name="Reference",Assembly=image};r.Sig=Sigs.TypeDef(r);Ref=r.Sig;
        Struct=new TypeDef{Index=2,Name="State",Assembly=image,IsValueType=true,Flags=TypeDef.SequentialLayout};Struct.Sig=Sigs.TypeDef(Struct);
        A=new FieldDef{Name="a",DeclaringType=Struct,Type=Ref,Attrs=1,Offset=0};
        B=new FieldDef{Name="b",DeclaringType=Struct,Type=Ref,Attrs=1,Offset=8};
        Flag=new FieldDef{Name="flag",DeclaringType=Struct,Type=Bool,Attrs=1,Offset=16};
        Struct.Fields=[A,B,Flag];
        Setter=new MethodDef{Name="set_flag",DeclaringType=Struct,ReturnType=Void,Flags=6,Parameters=[new ParamDef{Type=Bool}]};
        Mutator=new MethodDef{Name="Mutate",DeclaringType=Struct,ReturnType=Void,Flags=6};
        ByRefCall=new MethodDef{Name="Escape",DeclaringType=Struct,ReturnType=Void,Flags=MethodDef.Static|6,Parameters=[new ParamDef{Type=Sigs.ByRef(Struct.Sig)}]};
        var caller=new TypeDef{Index=3,Name="Caller",Assembly=image};caller.Sig=Sigs.TypeDef(caller);
        H=new HMethod{Method=new MethodDef{Name="Run",DeclaringType=caller,ReturnType=Void,Parameters=[new ParamDef{Type=Bool}]}};
        V=H.NewLocal(Struct.Sig);H.Blocks.Add(Entry);
    }
    public HLocal Local()=>new(V){Type=Struct.Sig};
    public HAssign Default()=>new(Local(),new HTypeExpr(HTypeOp.Default,Struct.Sig,null){Type=Struct.Sig});
    public HAssign Store(FieldDef f,object? value)=>new(new HField{Field=f,Object=Local(),Type=f.Type},new HConst(value,f.Type));
    public HCall Set()=>new(){Method=Setter,This=Local(),Arguments=[new HConst(false,Bool)],Type=Void};
    public HCall Unknown()=>new(){Method=Mutator,This=Local(),Arguments=[],Type=Void};
    public HCall Escape()=>new(){Method=ByRefCall,Arguments=[new HAddressOf(Local()){Type=Sigs.ByRef(Struct.Sig)}],Type=Void};
}
