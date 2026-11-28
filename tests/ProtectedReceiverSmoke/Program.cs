using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;

var assembly = new AssemblyModel { Name = "FamilyCases" };
var otherAssembly = new AssemblyModel { Name = "OtherCases" };
TypeDef T(string name, TypeDef? parent = null, TypeDef? enclosing = null, AssemblyModel? image = null)
{
    var t = new TypeDef { Name = name, Assembly = image ?? assembly, BaseType = parent?.Sig, DeclaringType = enclosing };
    t.Sig = new TypeDefSig(t);
    return t;
}
var root = T("Base");
var a = T("DerivedA", root);
var aChild = T("DerivedAChild", a);
var b = T("DerivedB", root);
var unrelated = T("Unrelated");
var nestedOwner = T("NestedOwner", enclosing: root);
var nestedA = T("NestedA", enclosing: a);
var crossA = T("CrossA", root, image: otherAssembly);
var crossSibling = T("CrossSibling", root, image: otherAssembly);
var unknown = new HArg(0);
int accepted = 0, rejected = 0;
void Check(string name, ushort access, TypeDef fromType, HExpr? receiver, bool expected, bool isStatic = false, bool staticCaller = false)
{
    var field = new FieldDef { DeclaringType = root, Name = "field", Type = root.Sig, Attrs = (ushort)(access | (isStatic ? FieldDef.Static : 0)) };
    var from = new MethodDef { DeclaringType = fromType, Name = "Read", Flags = (ushort)(staticCaller ? MethodDef.Static : 0) };
    bool actual = AccessorFolding.IsAccessible(field, from) && ProtectedFieldReceiver.Allows(field, from, receiver);
    if (actual != expected) throw new Exception(name + ": " + actual + " != " + expected);
    if (actual) accepted++; else rejected++;
}
HExpr On(TypeDef type) => new HArg(0) { Type = type.Sig };
Check("owner may use base", 4, root, On(root), true);
Check("owner may use either derived", 4, root, On(b), true);
Check("nested owner may use base", 4, nestedOwner, On(root), true);
Check("derived this", 4, a, new HArg(-1), true);
Check("derived this preserves caller type", 4, a, new HArg(-1) { Type = root.Sig }, true);
Check("derived its own receiver", 4, a, On(a), true);
Check("derived receiver subclass", 4, a, On(aChild), true);
Check("derived sibling receiver", 4, a, On(b), false);
Check("derived base receiver", 4, a, On(root), false);
Check("derived unrelated receiver", 4, a, On(unrelated), false);
Check("unknown receiver", 4, a, unknown, false);
Check("missing instance receiver", 4, a, null, false);
Check("nested derived outer receiver", 4, nestedA, On(a), true);
Check("nested derived sibling receiver", 4, nestedA, On(b), false);
Check("nested this is not outer this", 4, nestedA, new HArg(-1), false);
Check("unrelated caller", 4, unrelated, On(a), false);
Check("static protected has no receiver limit", 4, a, null, true, isStatic: true);
Check("static unrelated still denied", 4, unrelated, null, false, isStatic: true);
Check("static method explicit derived receiver", 4, a, On(a), true, staticCaller: true);
Check("static method no implicit this", 4, a, new HArg(-1), false, staticCaller: true);
Check("family-or-assembly sibling in assembly", 5, a, On(b), true);
Check("family-or-assembly unrelated in assembly", 5, unrelated, On(root), true);
Check("family-or-assembly cross own", 5, crossA, On(crossA), true);
Check("family-or-assembly cross sibling", 5, crossA, On(crossSibling), false);
Check("family-and-assembly own", 2, a, On(a), true);
Check("family-and-assembly sibling", 2, a, On(b), false);
Check("family-and-assembly cross own", 2, crossA, On(crossA), false);
Check("public is unaffected", 6, unrelated, On(root), true);
Check("assembly is unaffected", 3, unrelated, On(root), true);
Check("cross assembly remains denied", 3, crossA, On(root), false);
Check("private owner", 1, root, On(root), true);
Check("private nested owner", 1, nestedOwner, On(root), true);
Check("private derived remains denied", 1, a, On(a), false);
Console.WriteLine($"PROTECTED_RECEIVER_SMOKE_PASS accepted={accepted} rejected={rejected} total={accepted+rejected}");
