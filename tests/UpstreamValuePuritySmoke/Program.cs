using System.Text.Json;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;
var sigs = new SigFactory();
var integer = sigs.Primitive(Il2CppTypeEnum.I4);
int assertions = 0;
void Check(bool ok, string reason) { if (!ok) throw new InvalidDataException(reason); assertions++; }
HMethod Method(HExpr value, bool read)
{
    var m = new HMethod();
    var local = m.NewLocal(integer);
    m.Blocks.Add(new HBlock { Id = 0, Statements = [new HAssign(new HLocal(local), value), new HReturn(read ? new HLocal(local) : null)] });
    return m;
}
foreach (string name in new[] { "reference_arithmetic", "struct_bits", "struct_from_value" })
{
    var marker = new HOpaque(name, new HConst(123, integer)) { Problem = "explicit-gap" };
    Check(HirBuilder.IsPure(marker), name + " value was not recognized as pure");
    var dead = Method(marker, false); HirCleanup.Run(dead);
    Check(dead.Blocks[0].Statements is [HReturn], "Dead value not removed: " + name);
    var used = Method(marker, true); HirCleanup.Run(used);
    Check(used.Blocks[0].Statements is [HAssign { Value: HOpaque { Problem: "explicit-gap" } }, HReturn], "Used gap disappeared: " + name);
    foreach (HExpr operand in new HExpr[] {
        new HCall { Method = new MethodDef { Name = "Effect", ReturnType = integer }, Type = integer },
        new HBinary(HBinaryOp.Div, new HConst(1, integer), new HConst(0, integer)) { Type = integer },
        new HConv(HConvKind.OvfI1, new HConst(1000, integer)) { Type = integer },
        new HOpaque("unsupported_operation") })
    {
        var impure = new HOpaque(name, operand) { Problem = "explicit-gap" };
        Check(!HirBuilder.IsPure(impure), "Effect or possible exception marked pure: " + name);
        var retained = Method(impure, false); HirCleanup.Run(retained);
        Check(retained.Blocks[0].Statements is [HEval { Expression: HOpaque { Problem: "explicit-gap" } }, HReturn], "Effect or exception dropped: " + name);
    }
}
foreach (string name in new[] { "raw_constructor", "address", "untyped_load", "unsupported_operation" })
    Check(!HirBuilder.IsPure(new HOpaque(name, new HConst(1, integer))), "Unrelated marker incorrectly silenced: " + name);
Console.WriteLine(JsonSerializer.Serialize(new { complete = true, assertions, deadMarkersRemoved = 3, usedMarkersRetained = 3, effectAndExceptionCasesRetained = 12, unrelatedMarkersRetained = 4 }));
