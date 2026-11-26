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
Console.WriteLine("AGGREGATE_NUMERIC_OPERANDS_SMOKE_PASS rejected=8 accepted=8 (packed MatrixPosition, Vector2, typed fields, enum, native integer)");
