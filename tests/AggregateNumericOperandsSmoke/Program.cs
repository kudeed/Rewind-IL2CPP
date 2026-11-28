using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Output;
using Rewind.Runtime;

static TypeSig Struct(string ns, string name, bool isEnum = false)
{
    var d = new TypeDef { Namespace=ns, Name=name, IsValueType=true, IsEnum=isEnum };
    var sig = new TypeDefSig(d); d.Sig=sig; return sig;
}
static void Check(bool shouldReject, string operation, HExpr operand, TypeSig? declared = null)
{
    var error=AggregateNumericOperands.Error(operation,operand,declared);
    if((error!=null)!=shouldReject || (error!=null&&!error.Contains("recover typed field/lane")))
        throw new Exception($"{operation}: expected rejection {shouldReject}, got {error ?? "accepted"}");
}
var i4 = new PrimitiveSig(Il2CppTypeEnum.I4,null);
var i8 = new PrimitiveSig(Il2CppTypeEnum.I8,null);
var f4 = new PrimitiveSig(Il2CppTypeEnum.R4,null);
var native = new PrimitiveSig(Il2CppTypeEnum.I,null);
var position=Struct("Unicorn","MatrixPosition");
var vector=Struct("UnityEngine","Vector2");
var enumeration=Struct("Fixture","Mode",true);
var genericDef=new TypeDef { Namespace="Fixture",Name="Pair`1",IsValueType=true };
var closed=new GenericInstSig(genericDef,[i4]);
HExpr Local(TypeSig actual,TypeSig? annotated=null)=>new HLocal(new HVar{Type=actual}){Type=annotated??actual};
// The original failures are compare(MatrixPosition, Int64) and shift(Vector2, int).
Check(true,"Lt",Local(position));
Check(true,"ShrUn",Local(vector));
Check(true,"ShrUn",Local(vector,i8));
Check(true,"I4",Local(position,i8));
Check(true,"Eq",Local(closed));
Check(true,"Lt",new HArg(0){Type=i8},position);
Check(true,"ShrUn",new HField{Field=new FieldDef{Name="uvCenter",Type=vector},Type=i8});
Check(true,"Neg",Local(vector));
// Explicit field/lane extraction is scalar, not a struct operation.
Check(false,"Lt",new HField{Field=new FieldDef{Name="x",Type=i4},Type=i4});
Check(false,"ShrUn",Local(i8));
Check(false,"Lt",Local(i4));
Check(false,"Add",Local(f4));
Check(false,"Eq",Local(enumeration));
Check(false,"Add",Local(native));
Check(false,"Eq",new HConst(null,new PrimitiveSig(Il2CppTypeEnum.Object,null)));
Check(false,"Add",new HArg(0));
// StickHero DOTweenPro native aggregate recovery: Reset must carry the
// entire Nullable<Color>; its constructor must carry complete Keyframes.
// These checks exercise the scalar-annotation gate only. The separate
// real emitted-IL regression in DotweenPathNativeV110 catches incorrect
// ldloca Int64 receivers and Int64 constructor arguments.
var color=Struct("UnityEngine","Color");
var keyframe=Struct("UnityEngine","Keyframe");
var nullableDef=new TypeDef { Namespace="System",Name="Nullable`1",IsValueType=true };
var nullableColor=new GenericInstSig(nullableDef,[color]);
Check(true,"ShrUn",Local(nullableColor,i8));
Check(true,"I4",Local(keyframe,i8));
Check(true,"ShrUn",new HField{Field=new FieldDef{Name="pathColor",Type=color},Type=i8});
Check(true,"Add",new HArg(1){Type=i8},nullableColor);
Check(false,"Add",new HField{Field=new FieldDef{Name="time",Type=f4},Type=f4});
Check(false,"ShrUn",Local(i8));
Console.WriteLine("AGGREGATE_NUMERIC_OPERANDS_SMOKE_PASS rejected=12 accepted=10 (packed MatrixPosition, Vector2, Nullable<Color>, Keyframe, typed fields, enum, native integer)");

// Generic typed packed snapshots: the exact metadata offsets select the
// field, even with arbitrary names and metadata array order.
var bc=new TypeDef { Namespace="System",Name="BitConverter",Assembly=new AssemblyModel{Name="mscorlib"} };
var bitCall=new MethodDef { DeclaringType=bc,Name="Int32BitsToSingle",Flags=MethodDef.Static|6,
    ReturnType=f4,Parameters=[new ParamDef{Type=i4}] };
var pair=new TypeDef { Namespace="Fixture",Name="TwoFloat",IsValueType=true,
    Flags=TypeDef.SequentialLayout,Sizes=new RawTypeSizes(24,8,0,0) };
var pairSig=new TypeDefSig(pair);pair.Sig=pairSig;
var low=new FieldDef{DeclaringType=pair,Name="first",Type=f4,Attrs=6,Offset=16};
var high=new FieldDef{DeclaringType=pair,Name="second",Type=f4,Attrs=6,Offset=20};
pair.Fields=[high,low];
var u8=new PrimitiveSig(Il2CppTypeEnum.U8,null);
HLocal snapshot=new(new HVar{Type=pairSig}){Type=pairSig};
HCall Packed(HExpr operand)=>new(){Method=bitCall,Type=f4,Arguments=[new HConv(HConvKind.I4,operand){Type=i4}]};
HExpr Shift(HExpr operand,int count,HBinaryOp op=HBinaryOp.ShrUn)=>new HBinary(op,operand,new HConst(count,i4)){Type=u8};
void Lane(HCall c,FieldDef? expected,bool arm64=true,int header=16)
{
    var got=PackedFloatLane.Resolve(c,arm64,header);
    if (!ReferenceEquals(got?.Field,expected) || got!=null && (!ReferenceEquals(got.Object,snapshot) || !ReferenceEquals(got.Type,f4)))
        throw new Exception("unexpected packed lane result");
}
Lane(Packed(snapshot),low);
Lane(Packed(Shift(snapshot,32)),high);
Lane(Packed(Shift(snapshot,16)),null);
Lane(Packed(Shift(snapshot,64)),null);
Lane(Packed(Shift(snapshot,32,HBinaryOp.Shr)),null);
Lane(Packed(snapshot),null,false);
Lane(Packed(snapshot),null,true,8);
Lane(Packed(Local(i8)),null);
Lane(Packed(Local(pairSig,i8)),null);
var altered=Packed(snapshot);altered.Arguments=[new HConv(HConvKind.U4,snapshot){Type=i4}];Lane(altered,null);
high.Offset=16;Lane(Packed(snapshot),null);high.Offset=20;
high.Attrs=1;Lane(Packed(snapshot),null);high.Attrs=6;
high.Type=i4;Lane(Packed(snapshot),null);high.Type=f4;
pair.Flags=TypeDef.ExplicitLayout;Lane(Packed(snapshot),null);pair.Flags=TypeDef.SequentialLayout;
pair.Sizes=new RawTypeSizes(28,12,0,0);Lane(Packed(snapshot),null);pair.Sizes=new RawTypeSizes(24,8,0,0);
pair.Fields=[low,high,new FieldDef{DeclaringType=pair,Name="other",Attrs=6,Offset=16,Type=f4}];Lane(Packed(snapshot),null);pair.Fields=[high,low];
bc.Assembly.Name="Untrusted";Lane(Packed(snapshot),null);bc.Assembly.Name="mscorlib";
bitCall.Name="ToSingle";Lane(Packed(snapshot),null);bitCall.Name="Int32BitsToSingle";
Lane(Packed(snapshot),low);
Check(true,"I4",snapshot); // original guard must still reject naked aggregate casts.
Console.WriteLine("PACKED_FLOAT_LANE_SMOKE_PASS positive=3 negative=15 original_guard_retained=1");
