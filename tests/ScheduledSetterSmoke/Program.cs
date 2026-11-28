using System.Reflection;
using System.Security.Cryptography;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

var assembly=typeof(ProgramAnalysis).Assembly;
string sha=Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(assembly.Location)));
if(args.Length!=1||args[0]!=sha)throw new Exception("Analysis SHA mismatch: "+sha);
var run=assembly.GetType("Rewind.Analysis.Recover.ScheduledSetterWrites",true)!
    .GetMethods(BindingFlags.Static|BindingFlags.NonPublic).Single(m=>m.Name=="Run"&&m.GetParameters().Length==2);
int positive=0,negative=0;
void Check(string name,Fixture f,int expected=0,bool template=true)
{
    string before=HirPrinter.Print(f.H);
    var original=f.B.Statements.ToArray();
    var reads=original.OfType<HAssign>().Where(s=>s.Value is HField).ToArray();
    string? state=expected>0?f.Execute():null;
    Func<FieldDef,(MethodDef Setter,HCall Prelude)[]> models=field=>template&&field==f.Written?[(f.Setter,f.Model)]:[];
    int Apply()=>(int)run.Invoke(null,[f.H,models])!;
    int count=Apply();
    if(count!=expected)throw new Exception(name+": got "+count+" expected "+expected);
    if(expected>0)
    {
        if(f.Execute()!=state)throw new Exception(name+": callback/read/write semantics changed");
        if(!reads.SequenceEqual(f.B.Statements.OfType<HAssign>().Where(s=>s.Value is HField)))
            throw new Exception(name+": original caller field reads changed order");
        var remainingCalls=f.B.Statements.OfType<HEval>().Select(e=>e.Expression).OfType<HCall>().ToArray();
        if(remainingCalls.Count(c=>c.Method==f.Setter)!=1 || remainingCalls.Length!=original.OfType<HEval>().Count())
            throw new Exception(name+": expected one public setter and all other calls preserved");
        if(Apply()!=0)throw new Exception(name+": not idempotent");
        positive++;
    }
    else
    {
        if(before!=HirPrinter.Print(f.H)||!original.SequenceEqual(f.B.Statements))throw new Exception(name+": rejected input modified");
        negative++;
    }
}
Check("two independent caller reads",new Fixture(),1);
var one=new Fixture();one.B.Statements.RemoveAt(4);Check("one independent caller read",one,1);
var none=new Fixture();none.B.Statements.RemoveRange(3,2);Check("adjacent call and store",none,1);
var argument=new Fixture();argument.Store.Value=new HArg(0){Type=argument.Float};Check("value argument already available",argument,1);
var constant=new Fixture();constant.Store.Value=new HConst(-0.0f,constant.Float);Check("negative zero bit pattern preserved",constant,1);
var twice=new Fixture();twice.B.Statements.Insert(3,new HEval(new HCall{Method=twice.Dirty,This=twice.Local(twice.Target),Type=twice.Void}));Check("earlier identical dirty call retained",twice,1);
var explicitOwner=new Fixture();((HField)explicitOwner.Store.Target).DeclaringType=explicitOwner.Effect.Sig;
foreach(var read in explicitOwner.B.Statements.OfType<HAssign>().Select(a=>a.Value).OfType<HField>())read.DeclaringType=explicitOwner.Caller.Sig;
Check("exact explicit declaring types from native HIR",explicitOwner,1);
var wrongStoreOwner=new Fixture();((HField)wrongStoreOwner.Store.Target).DeclaringType=wrongStoreOwner.Caller.Sig;Check("wrong explicit store declaring type",wrongStoreOwner);
var wrongReadOwner=new Fixture();((HField)((HAssign)wrongReadOwner.B.Statements[3]).Value).DeclaringType=wrongReadOwner.Effect.Sig;Check("wrong explicit read declaring type",wrongReadOwner);
Check("unproven public setter template",new Fixture(),template:false);
var late=new Fixture();var assign=late.B.Statements[1];late.B.Statements.RemoveAt(1);late.B.Statements.Insert(3,assign);Check("argument computed after call",late);
var changed=new Fixture();changed.B.Statements[3]=new HAssign(changed.Local(changed.Arg),changed.Read(changed.CallerRead));Check("argument overwritten between call and store",changed);
var receiver=new Fixture();receiver.B.Statements[4]=new HAssign(receiver.Local(receiver.Target),receiver.Read(receiver.CallerReceiver));Check("receiver overwritten between call and store",receiver);
var addressArg=new Fixture();addressArg.Arg.AddressTaken=true;Check("address-taken argument can be changed by callback",addressArg);
var addressReceiver=new Fixture();addressReceiver.Target.AddressTaken=true;Check("address-taken receiver",addressReceiver);
var addressTemp=new Fixture();addressTemp.ReadValue.AddressTaken=true;Check("address-taken skipped destination",addressTemp);
var aliased=new Fixture();((HAssign)aliased.B.Statements[3]).Value=new HField{Object=aliased.Local(aliased.Target),Field=aliased.Written,Type=aliased.Float};Check("intermediate read observes target field",aliased);
var baseCaller=new Fixture();baseCaller.Caller.BaseType=baseCaller.Effect.Sig;Check("caller can alias setter receiver",baseCaller);
var derivedEffect=new Fixture();derivedEffect.Effect.BaseType=derivedEffect.Caller.Sig;Check("setter receiver can alias caller",derivedEffect);
var unknownBase=new Fixture();unknownBase.Caller.BaseType=unknownBase.Ref;Check("unresolved inheritance",unknownBase);
var explicitLayout=new Fixture();explicitLayout.Effect.Flags=TypeDef.ExplicitLayout;Check("explicit layout",explicitLayout);
var wrongCall=new Fixture();wrongCall.Before.Method=new MethodDef{Name="Other",DeclaringType=wrongCall.Effect,ReturnType=wrongCall.Void};Check("different prelude call",wrongCall);
var dispatch=new Fixture();dispatch.Before.Virtual=true;Check("different virtual dispatch",dispatch);
var callArgs=new Fixture();callArgs.Before.Arguments=[new HConst(1f,callArgs.Float)];Check("extra prelude arguments",callArgs);
var callGenerics=new Fixture();callGenerics.Before.MethodArguments=[callGenerics.Float];Check("generic prelude instance",callGenerics);
var constrained=new Fixture();constrained.Before.Constrained=constrained.Effect.Sig;Check("constrained prelude",constrained);
var observable=new Fixture();observable.B.Statements.Insert(3,new HEval(new HCall{Method=new MethodDef{Name="OtherEffect",DeclaringType=observable.Effect,ReturnType=observable.Void,Flags=6},This=observable.Local(observable.Target),Type=observable.Void}));Check("intervening observable call",observable);
var computed=new Fixture();((HAssign)computed.B.Statements[3]).Value=new HCall{Method=new MethodDef{Name="Read",DeclaringType=computed.Caller,ReturnType=computed.Float,Flags=MethodDef.Static|6},Type=computed.Float};Check("intervening effectful read",computed);
var readType=new Fixture();((HAssign)readType.B.Statements[3]).Value.Type=readType.Ref;Check("intermediate read type mismatch",readType);
var badType=new Fixture();badType.Store.Value.Type=badType.Ref;Check("setter argument type mismatch",badType);
var readOnly=new Fixture();readOnly.Written.Attrs|=FieldDef.InitOnly;Check("readonly target",readOnly);
var pub=new Fixture();pub.Written.Attrs=6;Check("public store outside repair scope",pub);
var stat=new Fixture();stat.Written.Attrs|=FieldDef.Static;Check("static field",stat);
var currentStatic=new Fixture();currentStatic.H.Method.Flags|=MethodDef.Static;Check("static caller",currentStatic);
var currentValue=new Fixture();currentValue.Caller.IsValueType=true;Check("value-type caller",currentValue);
var generic=new Fixture();generic.Caller.GenericParameters=[new GenericParam{Name="T"}];Check("generic caller",generic);
var problem=new Fixture();problem.H.Problems.Add("unknown semantics");Check("existing problem",problem);
var scope=new Fixture();scope.B.Scope=0;Check("exception scope",scope);
var noNullProof=new Fixture();noNullProof.H.Method.Parameters=[new ParamDef{Type=noNullProof.Float},new ParamDef{Type=noNullProof.Effect.Sig}];
((HAssign)noNullProof.B.Statements[0]).Value=new HArg(1){Type=noNullProof.Effect.Sig};
noNullProof.B.Statements.RemoveAt(1);noNullProof.Store.Value=new HArg(0){Type=noNullProof.Float};Check("caller could still be null before skipped reads",noNullProof);
var absentReceiver=new Fixture();absentReceiver.B.Statements.RemoveAt(0);Check("receiver not defined before call",absentReceiver);
Console.WriteLine($"SCHEDULED_SETTER_SMOKE_PASS positive={positive} negative={negative} callback_effects_preserved=true caller_reads_preserved=true original_argument_value=true negative_zero_preserved=true idempotent=true analysis_sha256={sha}");

sealed class Fixture
{
    public readonly SigFactory Sigs=new();
    public readonly TypeSig Float,Void,Ref;
    public readonly TypeDef Caller,Effect;
    public readonly FieldDef Written,CallerReceiver,CallerInput,CallerRead;
    public readonly HMethod H;
    public readonly HBlock B=new(){Id=0};
    public readonly HVar Target,Arg,ReadValue,ReadReceiver;
    public readonly MethodDef Setter,Dirty;
    public readonly HCall Model,Before;
    public readonly HAssign Store;
    public Fixture()
    {
        Float=Sigs.Primitive(Il2CppTypeEnum.R4);Void=Sigs.Primitive(Il2CppTypeEnum.Void);Ref=Sigs.Primitive(Il2CppTypeEnum.Object);
        var image=new AssemblyModel{Name="Fixture"};
        Caller=new TypeDef{Index=1,Name="Caller",Assembly=image};Caller.Sig=Sigs.TypeDef(Caller);
        Effect=new TypeDef{Index=2,Name="Effect",Assembly=image};Effect.Sig=Sigs.TypeDef(Effect);
        Written=new FieldDef{Name="value",Type=Float,DeclaringType=Effect,Attrs=1};Effect.Fields=[Written];
        CallerReceiver=new FieldDef{Name="effect",Type=Effect.Sig,DeclaringType=Caller,Attrs=1};
        CallerInput=new FieldDef{Name="input",Type=Float,DeclaringType=Caller,Attrs=1};
        CallerRead=new FieldDef{Name="observed",Type=Float,DeclaringType=Caller,Attrs=1};
        Caller.Fields=[CallerReceiver,CallerInput,CallerRead];
        H=new HMethod{Method=new MethodDef{Name="Run",DeclaringType=Caller,ReturnType=Void,Parameters=[new ParamDef{Type=Float}]}};H.Blocks.Add(B);
        Target=H.NewLocal(Effect.Sig);Arg=H.NewLocal(Float);ReadValue=H.NewLocal(Float);ReadReceiver=H.NewLocal(Effect.Sig);
        Dirty=new MethodDef{Name="Dirty",DeclaringType=Effect,ReturnType=Void,Flags=6};
        Setter=new MethodDef{Name="set_Value",DeclaringType=Effect,ReturnType=Void,Flags=6,Parameters=[new ParamDef{Type=Float}]};
        Model=new HCall{Method=Dirty,This=new HArg(-1){Type=Effect.Sig},Type=Void};
        Before=new HCall{Method=Dirty,This=Local(Target),Type=Void};
        Store=new HAssign(new HField{Object=Local(Target),Field=Written,Type=Float},Local(Arg));
        B.Statements.AddRange([new HAssign(Local(Target),Read(CallerReceiver)),new HAssign(Local(Arg),Read(CallerInput)),
            new HEval(Before),new HAssign(Local(ReadValue),Read(CallerRead)),new HAssign(Local(ReadReceiver),Read(CallerReceiver)),Store,new HReturn(null)]);
    }
    public HLocal Local(HVar v)=>new(v){Type=v.Type};
    public HField Read(FieldDef f)=>new(){Object=new HArg(-1){Type=Caller.Sig},Field=f,Type=f.Type};
    public string Execute()
    {
        var a=new Box{Value=2f,Name="A"};var b=new Box{Value=9f,Name="B"};
        var caller=new Dictionary<FieldDef,object>{{CallerReceiver,a},{CallerInput,3f},{CallerRead,0f}};
        var vars=new Dictionary<HVar,object>();var trace=new List<string>();
        object Value(HExpr e)=>e switch {HConst c=>c.Value!,HArg{Index:0}=>5f,HLocal l=>vars[l.Variable],
            HField f when f.Object is HArg{Index:-1}=>caller[f.Field],_=>throw new Exception("unexpected expression")};
        void Call(HCall c)
        {
            var target=(Box)Value(c.This!);object? argument=c.Arguments.Length==1?Value(c.Arguments[0]):null;
            trace.Add("dirty:"+target.Name+":"+BitConverter.SingleToInt32Bits(target.Value));
            // A dirty callback is allowed to mutate the caller. The original reads must still see it.
            target.Value+=10f;caller[CallerReceiver]=b;caller[CallerInput]=11f;caller[CallerRead]=17f;
            if(c.Method==Setter)target.Value=(float)argument!;
            else if(c.Method!=Dirty)throw new Exception("unexpected call");
        }
        foreach(var statement in B.Statements)
        {
            if(statement is HAssign {Target:HLocal l,Value:var v})vars[l.Variable]=Value(v);
            else if(statement is HAssign {Target:HField f,Value:var fieldValue})((Box)Value(f.Object!)).Value=(float)Value(fieldValue);
            else if(statement is HEval {Expression:HCall c})Call(c);
            else if(statement is not HReturn)throw new Exception("unexpected statement");
        }
        string Format(object? o)=>o is Box box?box.Name:o is float f?BitConverter.SingleToInt32Bits(f).ToString():o?.ToString()??"unset";
        return string.Join("|",trace)+"|A="+Format(a.Value)+"|B="+Format(b.Value)+"|read="+Format(vars.GetValueOrDefault(ReadValue))+"|receiver="+Format(vars.GetValueOrDefault(ReadReceiver))+"|input="+Format(caller[CallerInput]);
    }
    private sealed class Box {public string Name="";public float Value;}
}
