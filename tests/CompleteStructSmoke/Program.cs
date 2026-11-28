using System.Reflection;
using System.Security.Cryptography;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

var assembly=typeof(ProgramAnalysis).Assembly;
string sha=Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(assembly.Location)));
if(args.Length!=1||sha!=args[0])throw new Exception("Analysis SHA gate failed: "+sha);
var run=assembly.GetType("Rewind.Analysis.Recover.CompleteStructInitialization",true)!
    .GetMethods(BindingFlags.Static|BindingFlags.NonPublic).Single(m=>m.Name=="Run"&&
        m.GetParameters()[1].ParameterType==typeof(Func<TypeSig,bool>));
int positive=0,negative=0;
void Check(string name,Fixture f,int expected=0,bool layout=true,bool setters=true)
{
    string before=HirPrinter.Print(f.H);
    var original=f.Block.Statements.ToArray();
    var nativeKept=original.OfType<HEval>().Where(x=>x.Expression is HCall c&&
        c.Method.Flags==6&&c.Arguments.Length==1&&c.Arguments[0] is not HTypeExpr).ToArray();
    string? expectedState=expected>0?f.State():null;
    Func<TypeSig,bool> valid=_=>layout;
    Func<HCall,FieldDef?> writes=c=>setters&&f.Setters.TryGetValue(c.Method,out var field)?field:null;
    int Apply()=>(int)run.Invoke(null,[f.H,valid,writes])!;
    int actual=Apply();
    if(actual!=expected)throw new Exception(name+": got "+actual+" expected "+expected);
    if(expected==0)
    {
        if(HirPrinter.Print(f.H)!=before||!original.SequenceEqual(f.Block.Statements))
            throw new Exception(name+": rejected input was modified");
        negative++;
    }
    else
    {
        if(f.State()!=expectedState)throw new Exception(name+": complete struct value changed");
        var kept=f.Block.Statements.OfType<HEval>().ToArray();
        if(!kept.SequenceEqual(nativeKept))throw new Exception(name+": retained write order changed");
        if(f.Block.Statements.OfType<HAssign>().Count(a=>a.Value is HTypeExpr {Op:HTypeOp.Default} d&&d.Target==f.Struct.Sig)!=1)
            throw new Exception(name+": expected one whole default initialization");
        if(Apply()!=0)throw new Exception(name+": not idempotent");
        positive++;
    }
}
Check("local initialized over nonzero old value",new Fixture(),1);
Check("instance field initialized over nonzero old value",new Fixture(field:true),1);
var reordered=new Fixture();reordered.Block.Statements.Reverse();Check("independent writes in another order",reordered,1);
var fields=new Fixture();fields.Name.Attrs=6;fields.Block.Statements[0]=fields.Store(fields.Name,new HLocal(fields.Input){Type=fields.Ref});Check("public field remains direct write",fields,1);
var zeros=new Fixture();zeros.Call(0).Arguments[0]=zeros.Zero(zeros.Ref);zeros.Call(1).Arguments[0]=zeros.Zero(zeros.Int);Check("all fields explicitly zero",zeros,1);
var missing=new Fixture();missing.Block.Statements.RemoveAt(4);Check("partial write set",missing);
var duplicate=new Fixture();duplicate.Block.Statements[4]=duplicate.Store(duplicate.Flag,duplicate.Zero(duplicate.Bool));Check("duplicate field and missing field",duplicate);
var unknown=new Fixture();unknown.Block.Statements.Insert(2,new HEval(new HCall{Method=new MethodDef{Name="Observe",DeclaringType=unknown.Caller,ReturnType=unknown.Void,Flags=6},This=new HArg(-1){Type=unknown.Caller.Sig},Type=unknown.Void}));Check("observable call between stores",unknown);
var nonzero=new Fixture();nonzero.Block.Statements[3]=nonzero.Store(nonzero.Payload,new HLocal(nonzero.H.NewLocal(nonzero.Inner.Sig)){Type=nonzero.Inner.Sig});Check("private nonzero field remains inaccessible",nonzero);
var internalValue=new Fixture();internalValue.Call(2).Arguments[0]=new HConst(true,internalValue.Bool);Check("internal nonzero setter",internalValue);
Check("unknown layout",new Fixture(),layout:false);
Check("unproven native setter",new Fixture(),setters:false);
var explicitLayout=new Fixture();explicitLayout.Struct.Flags=TypeDef.ExplicitLayout;Check("explicit union layout",explicitLayout);
var readOnly=new Fixture();readOnly.Payload.Attrs|=FieldDef.InitOnly;Check("readonly struct member",readOnly);
var staticField=new Fixture();staticField.Payload.Attrs|=FieldDef.Static;Check("static member is not a struct component",staticField);
var generic=new Fixture();generic.Struct.GenericParameters=[new GenericParam{Name="T"}];Check("generic owner",generic);
var enumOwner=new Fixture();enumOwner.Struct.IsEnum=true;Check("enum owner",enumOwner);
var classOwner=new Fixture();classOwner.Struct.IsValueType=false;Check("reference owner",classOwner);
var badReceiver=new Fixture();badReceiver.Call(1).This=new HLocal(badReceiver.H.NewLocal(badReceiver.Struct.Sig)){Type=badReceiver.Struct.Sig};Check("another destination",badReceiver);
var addressed=new Fixture();addressed.Call(0).This=new HAddressOf(addressed.Place()){Type=addressed.Sigs.ByRef(addressed.Struct.Sig)};Check("address expression destination",addressed);
var wrongSetter=new Fixture();wrongSetter.Setters[wrongSetter.Call(1).Method]=wrongSetter.Flag;Check("native setter field has wrong type",wrongSetter);
var virtualCall=new Fixture();virtualCall.Call(1).Virtual=true;Check("virtual call",virtualCall);
var virtualMethod=new Fixture();virtualMethod.Call(1).Method.Flags|=MethodDef.Virtual;Check("virtual method definition",virtualMethod);
var extra=new Fixture();extra.Call(1).Arguments=[extra.Call(1).Arguments[0],extra.Zero(extra.Int)];Check("extra argument",extra);
var result=new Fixture();result.Call(1).Method.ReturnType=result.Int;Check("nonvoid setter",result);
var changedSignature=new Fixture();changedSignature.Call(1).Method.Parameters[0].Type=changedSignature.Bool;Check("setter signature mismatch",changedSignature);
var wrongZero=new Fixture();((HTypeExpr)((HAssign)wrongZero.Block.Statements[3]).Value).Target=wrongZero.Struct.Sig;Check("default of another type",wrongZero);
var wrongType=new Fixture();wrongType.Call(0).Arguments[0].Type=wrongType.Int;Check("argument type mismatch",wrongType);
var readsOld=new Fixture();readsOld.Call(0).Arguments[0]=new HField{Object=readsOld.Place(),Field=readsOld.Name,Type=readsOld.Ref};Check("value reads old destination",readsOld);
var effectValue=new Fixture();effectValue.Call(0).Arguments[0]=new HCall{Method=new MethodDef{Name="Produce",DeclaringType=effectValue.Caller,ReturnType=effectValue.Ref,Flags=MethodDef.Static|6},Type=effectValue.Ref};Check("effectful value",effectValue);
var problem=new Fixture();problem.H.Problems.Add("unknown prior semantics");Check("existing blocker",problem);
var scope=new Fixture();scope.Block.Scope=0;Check("exception scope",scope);
var readonlyRoot=new Fixture(field:true);readonlyRoot.Outer.Attrs|=FieldDef.InitOnly;Check("readonly destination field",readonlyRoot);
var staticCaller=new Fixture(field:true);staticCaller.H.Method.Flags|=MethodDef.Static;Check("static caller with instance field",staticCaller);
Check("field on unrelated receiver",new Fixture(field:true,receiver:0));
var publicOnly=new Fixture();publicOnly.Flag.Attrs=6;publicOnly.Payload.Attrs=6;publicOnly.Pattern.Attrs=6;publicOnly.Call(2).Method.Flags=6;Check("no inaccessible zero outside repair scope",publicOnly);
Console.WriteLine($"COMPLETE_STRUCT_SMOKE_PASS positive={positive} negative={negative} exact_final_values=true original_nonzero_write_order=true idempotent=true analysis_sha256={sha}");

sealed class Fixture
{
    public readonly SigFactory Sigs=new();
    public readonly TypeSig Ref,Bool,Int,Void;
    public readonly TypeDef Struct,Inner,Caller;
    public readonly HMethod H;
    public readonly HBlock Block=new(){Id=0};
    public readonly HVar V,Input;
    public readonly FieldDef Name,Count,Flag,Payload,Pattern,Outer;
    public readonly Dictionary<MethodDef,FieldDef> Setters=[];
    private readonly bool field;
    private readonly int receiver;
    public Fixture(bool field=false,int receiver=-1)
    {
        this.field=field;this.receiver=receiver;
        Ref=Sigs.Primitive(Il2CppTypeEnum.String);Bool=Sigs.Primitive(Il2CppTypeEnum.Boolean);
        Int=Sigs.Primitive(Il2CppTypeEnum.I4);Void=Sigs.Primitive(Il2CppTypeEnum.Void);
        var image=new AssemblyModel{Name="Fixture"};
        Caller=new TypeDef{Index=1,Name="Caller",Assembly=image};Caller.Sig=Sigs.TypeDef(Caller);
        Inner=new TypeDef{Index=2,Name="Inner",Assembly=image,IsValueType=true,Flags=TypeDef.SequentialLayout};Inner.Sig=Sigs.TypeDef(Inner);
        Struct=new TypeDef{Index=3,Name="State",Assembly=image,IsValueType=true,Flags=TypeDef.SequentialLayout};Struct.Sig=Sigs.TypeDef(Struct);
        FieldDef F(string name,TypeSig type)=>new(){Name=name,Type=type,DeclaringType=Struct,Attrs=1};
        Name=F("name",Ref);Count=F("count",Int);Flag=F("flag",Bool);Payload=F("payload",Inner.Sig);Pattern=F("pattern",Sigs.SzArray(Sigs.Primitive(Il2CppTypeEnum.I8)));
        Struct.Fields=[Name,Count,Flag,Payload,Pattern];
        Outer=new FieldDef{Name="state",Type=Struct.Sig,DeclaringType=Caller,Attrs=1};Caller.Fields=[Outer];
        H=new HMethod{Method=new MethodDef{Name="Run",DeclaringType=Caller,ReturnType=Void,Parameters=[new ParamDef{Type=Int}]}};
        H.Blocks.Add(Block);V=H.NewLocal(Struct.Sig);Input=H.NewLocal(Ref);
        Block.Statements.Add(Set(Name,new HLocal(Input){Type=Ref},6));
        Block.Statements.Add(Set(Count,new HArg(0){Type=Int},6));
        Block.Statements.Add(Set(Flag,Zero(Bool),3));
        Block.Statements.Add(Store(Payload,Zero(Inner.Sig)));
        Block.Statements.Add(Store(Pattern,new HConst(null,Pattern.Type)));
    }
    public HExpr Place()=>field?new HField{Object=new HArg(receiver){Type=Caller.Sig},Field=Outer,Type=Struct.Sig}:new HLocal(V){Type=Struct.Sig};
    public HTypeExpr Zero(TypeSig type)=>new(HTypeOp.Default,type,null){Type=type};
    public HAssign Store(FieldDef f,HExpr value)=>new(new HField{Object=Place(),Field=f,Type=f.Type},value);
    private HEval Set(FieldDef f,HExpr value,ushort flags)
    {
        var m=new MethodDef{Name="set_"+f.Name,DeclaringType=Struct,ReturnType=Void,Flags=flags,Parameters=[new ParamDef{Type=f.Type}]};
        Setters[m]=f;
        return new HEval(new HCall{Method=m,This=Place(),Arguments=[value],Type=Void});
    }
    public HCall Call(int index)=>(HCall)((HEval)Block.Statements[index]).Expression;
    public string State()
    {
        var values=Struct.Fields.ToDictionary(f=>f,_=>(object?)"old-nonzero");
        object? Default(TypeSig type)=>!type.IsValueType?null:type.Key==Bool.Key?false:type.Key==Int.Key?0:"zero:"+type.Key;
        object? Value(HExpr value)=>value switch {
            HConst c=>c.Value,HTypeExpr {Op:HTypeOp.Default} d=>Default(d.Target),
            HLocal l when l.Variable==Input=>"after",HArg{Index:0}=>17,
            _=>throw new Exception("unexpected interpreter value")};
        foreach(var s in Block.Statements)
        {
            if(s is HAssign {Value:HTypeExpr {Op:HTypeOp.Default} d} &&d.Target==Struct.Sig)
                values=Struct.Fields.ToDictionary(f=>f,f=>Default(f.Type));
            else if(s is HAssign {Target:HField f,Value:var v})values[f.Field]=Value(v);
            else if(s is HEval {Expression:HCall c})values[Setters[c.Method]]=Value(c.Arguments[0]);
            else throw new Exception("unexpected interpreter statement");
        }
        return string.Join("|",Struct.Fields.Select(f=>f.Name+"="+(values[f]?.ToString()??"null")));
    }
}
