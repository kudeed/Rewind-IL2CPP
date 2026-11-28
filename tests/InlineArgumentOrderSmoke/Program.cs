using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;

static void Check(bool value, string name) { if (!value) throw new Exception(name); }
var sf = new SigFactory();
var integer = sf.Primitive(Il2CppTypeEnum.I4);
var single = sf.Primitive(Il2CppTypeEnum.R4);
var boolean = sf.Primitive(Il2CppTypeEnum.Boolean);
var obj = sf.Primitive(Il2CppTypeEnum.Object);
var owner = new TypeDef { Name = "Owner", Assembly = new AssemblyModel { Name = "Test" } };
owner.Sig = sf.TypeDef(owner);
var caller = new MethodDef { Name = "Caller", DeclaringType = owner, ReturnType = integer };
var getter = new MethodDef { Name = "GetValue", DeclaringType = owner, ReturnType = single, Flags = MethodDef.Static };
var x = new HVar { Name = "x", Type = single };
var y = new HVar { Name = "y", Type = single };
var result = new HVar { Name = "result", Type = single };
HLocal Local(HVar variable) => new(variable) { Type = variable.Type };
HCall Call() => new() { Method = getter, Type = single };
HExpr Angle() => new HBinary(HBinaryOp.Sub, Local(x), Local(y)) { Type = single };
HMethod Body() => new() { Method = caller, Blocks = [new HBlock { Statements = [new HEval(Call()), new HAssign(Local(result), Call())] }] };
bool Match(int[] order, HExpr?[] arguments, HMethod? body = null)
{
    body ??= Body();
    return InlineArgumentOrder.Preserves(order, arguments, body, body.Blocks[0].Statements, 0, 1);
}
int positive = 0, negative = 0;
void Accept(string name, int[] order, HExpr?[] arguments) { Check(Match(order, arguments), name); positive++; }
void Reject(string name, HExpr? scalar)
{
    Check(!Match([1, 0], [scalar, Call()]), name);
    negative++;
}
Accept("AngleAxis getter followed by stable angle", [1, 0], [Angle(), Call()]);
Accept("original call order", [0, 1], [Call(), Call()]);
Accept("constant across call", [1, 0], [new HConst(7, integer), Call()]);
Accept("three effects in their original order", [1, 0, 2], [Angle(), Call(), Call()]);
Accept("stable value moves later", [1, 0], [Call(), Angle()]);
Accept("floating division cannot throw", [1, 0], [new HBinary(HBinaryOp.Div, Local(x), Local(y)) { Type = single }, Call()]);
Accept("comparison and unchecked conversion", [1, 0], [new HConv(HConvKind.I4, new HCompare(HCompareOp.Gt, Local(x), Local(y)) { Type = boolean }) { Type = integer }, Call()]);
Check(!Match([2, 1, 0], [Call(), Angle(), Call()]), "pure argument does not hide two reordered calls"); negative++;
Reject("two calls", Call());
Reject("reference field", new HField { Field = new FieldDef { Name = "field", DeclaringType = owner, Type = single }, Object = new HArg(0) { Type = owner.Sig }, Type = single });
Reject("static field", new HField { Field = new FieldDef { Name = "field", DeclaringType = owner, Type = single, Attrs = 0x10 }, Type = single });
Reject("array element", new HElement { Array = new HArg(0), Index = new HConst(0, integer), Type = single });
Reject("argument may be aliased", new HArg(0) { Type = single });
Reject("reference local", Local(new HVar { Type = obj }));
Reject("byref local", Local(new HVar { Type = sf.ByRef(single) }));
Reject("pointer local", Local(new HVar { Type = sf.Pointer(single) }));
Reject("escaped scalar local", Local(new HVar { Type = single, AddressTaken = true }));
Reject("unknown type local", new HLocal(new HVar()));
Reject("inconsistent local type", new HLocal(x) { Type = integer });
Reject("unknown expression type", new HBinary(HBinaryOp.Sub, Local(x), Local(y)));
Reject("null constant", new HConst(null, single));
Reject("string constant with wrong scalar type", new HConst("bad", single));
Reject("checked addition", new HBinary(HBinaryOp.AddOvf, new HConst(int.MaxValue, integer), new HConst(1, integer)) { Type = integer });
Reject("integer division", new HBinary(HBinaryOp.Div, new HConst(1, integer), new HConst(0, integer)) { Type = integer });
Reject("integer remainder", new HBinary(HBinaryOp.Rem, new HConst(1, integer), new HConst(0, integer)) { Type = integer });
Reject("checked conversion", new HConv(HConvKind.OvfI4, Local(x)) { Type = integer });
var changed = Body(); changed.Blocks[0].Statements[0] = new HAssign(Local(x), new HConst(1f, single));
Check(!Match([1, 0], [Angle(), Call()], changed), "scalar assigned inside folded interval"); negative++;
var aliased = Body(); aliased.Blocks.Add(new HBlock { Statements = [new HEval(new HAddressOf(Local(x)) { Type = sf.ByRef(single) })] });
Check(!Match([1, 0], [Angle(), Call()], aliased), "address taken elsewhere despite flag false"); negative++;
Check(!Match([1, 0, 1], [Angle(), Call()]), "duplicate parameter"); negative++;
Check(!Match([2, 0], [Angle(), Call()]), "unknown parameter"); negative++;
Check(!Match([-1, 0], [Angle(), Call()]), "receiver index in argument list"); negative++;
Reject("missing argument", null);
Console.WriteLine($"INLINE_ARGUMENT_ORDER_PASS positive={positive} negative={negative}");
