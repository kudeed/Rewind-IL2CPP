using System.Security.Cryptography;
using System.Text.Json;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Analysis.Runtime;
using Rewind.Binary;
using Rewind.Metadata;
using Rewind.Model;
using Rewind.Output;
using Rewind.Runtime;
if (args.Length != 4 || args.Any(string.IsNullOrWhiteSpace)) throw new ArgumentException("Required: original-library original-metadata signatures-directory fresh-output-directory");
var sigs = new SigFactory(); var assembly = new AssemblyModel { Name = "Fixture" };
TypeDef Type(int index, string name, TypeDef? parent = null)
{
    var t = new TypeDef { Index = index, Name = name, Assembly = assembly, BaseType = parent?.Sig }; t.Sig = sigs.TypeDef(t); return t;
}
var source = Type(-1, "Source"); var derived = Type(-2, "Derived", source); var other = Type(-3, "Other");
var caller = new MethodDef { Name = "Caller", DeclaringType = source, Flags = MethodDef.Static, ReturnType = sigs.Primitive(Il2CppTypeEnum.Void), Parameters = [new ParamDef { Type = source.Sig }] };
var callee = new MethodDef { Name = "Read", DeclaringType = derived, ReturnType = sigs.Primitive(Il2CppTypeEnum.I4) };
int positive = 0, negative = 0;
(HMethod Method, HBlock Guard, HBlock Success, HBlock Failure, HBlock Entry, HCall Call) Fixture()
{
    var call = new HCall { Method = callee, This = new HArg(0) { Type = source.Sig }, Type = callee.ReturnType };
    var success = new HBlock { Id = 1, Statements = [new HEval(call), new HReturn(null)] };
    var failure = new HBlock { Id = 2, Statements = [new HReturn(null)] };
    var guard = new HBlock { Id = 0, Statements = [new HBranch(new HCompare(HCompareOp.Ne, new HTypeExpr(HTypeOp.IsInst, derived.Sig, new HArg(0) { Type = source.Sig }) { Type = derived.Sig }, new HConst(null, derived.Sig)), success, failure)] };
    var entry = new HBlock { Id = 3, Statements = [new HJump(guard)] };
    return (new HMethod { Method = caller, Blocks = [entry, guard, success, failure] }, guard, success, failure, entry, call);
}
foreach (bool equal in new[] { false, true }) foreach (bool reverse in new[] { false, true })
{
    var f = Fixture(); var b = (HBranch)f.Guard.Statements[0]; var c = (HCompare)b.Condition;
    if (equal) { c.Op = HCompareOp.Eq; (b.WhenTrue, b.WhenFalse) = (b.WhenFalse, b.WhenTrue); }
    if (reverse) (c.Left, c.Right) = (c.Right, c.Left);
    if (TypeTestReceiverCasts.Run(f.Method) != 1 || f.Call.This is not HTypeExpr { Op: HTypeOp.CastClass } || TypeTestReceiverCasts.Run(f.Method) != 0) throw new InvalidDataException("Successful type-test proof or idempotence failed");
    positive++;
}
void Reject(string why, Action<HMethod, HBlock, HBlock, HBlock, HBlock, HCall> change)
{
    var f = Fixture(); change(f.Method, f.Guard, f.Success, f.Failure, f.Entry, f.Call);
    if (TypeTestReceiverCasts.Run(f.Method) != 0 || f.Call.This is HTypeExpr { Op: HTypeOp.CastClass }) throw new InvalidDataException("Unproved receiver accepted: " + why);
    negative++;
}
Reject("bypass", (m,g,s,f,e,c) => e.Statements[0] = new HBranch(new HConst(true, null), g, s));
Reject("merge after failed test", (m,g,s,f,e,c) => f.Statements[0] = new HJump(s));
Reject("failed edge", (m,g,s,f,e,c) => { s.Statements = [new HReturn(null)]; f.Statements = [new HEval(c), new HReturn(null)]; });
Reject("before test", (m,g,s,f,e,c) => { s.Statements = [new HReturn(null)]; g.Statements.Insert(0, new HEval(c)); });
Reject("argument reassignment", (m,g,s,f,e,c) => s.Statements.Insert(0, new HAssign(new HArg(0), new HConst(null, source.Sig))));
Reject("argument address escapes", (m,g,s,f,e,c) => e.Statements.Insert(0, new HEval(new HAddressOf(new HArg(0)))));
Reject("local receiver", (m,g,s,f,e,c) => c.This = new HLocal(new HVar { Type = source.Sig }));
Reject("different argument", (m,g,s,f,e,c) => c.This = new HArg(1) { Type = source.Sig });
Reject("receiver type annotation differs", (m,g,s,f,e,c) => c.This = new HArg(0) { Type = other.Sig });
Reject("unrelated callee", (m,g,s,f,e,c) => c.Method = new MethodDef { DeclaringType = other });
Reject("generic method arguments", (m,g,s,f,e,c) => c.MethodArguments = [source.Sig]);
Reject("instantiated declaring type", (m,g,s,f,e,c) => c.DeclaringType = derived.Sig);
Reject("scoped block", (m,g,s,f,e,c) => s.Scope = 0);
Reject("exception region", (m,g,s,f,e,c) => m.TryRegions.Add(0, new HTryRegion()));
Reject("non-type test", (m,g,s,f,e,c) => ((HCompare)((HBranch)g.Statements[0]).Condition).Left = new HArg(0) { Type = source.Sig });
Console.WriteLine($"TYPE_TEST_RECEIVER_SYNTHETIC_PASS positive={positive} negative={negative}");
string Sha(byte[] b) => Convert.ToHexString(SHA256.HashData(b)).ToLowerInvariant();
var native = File.ReadAllBytes(args[0]); var metadata = File.ReadAllBytes(args[1]);
if (Sha(native) != "031b3c7a09bb67f6f6c1c8c89b400848f75d023a8cdbe69f392872f72e787eae" || Sha(metadata) != "6b2c40f77fc5ac40c2e75be3cba0655a7d4bf9464fc694f6336f65c911383465") throw new InvalidDataException("Original input differs");
if (!UnityVersion.TryParse("6000.3.11f1", out var version)) throw new InvalidDataException("Unity version");
var model = Il2CppModel.Load(NativeImage.Load(native, "original"), metadata, version);
var discovery = HelperDiscovery.Discover(model, Directory.GetFiles(args[2], "*.sig"), Console.WriteLine);
var program = new ProgramAnalysis(model, discovery.Helpers, discovery.Context); var pipeline = new MethodPipeline(program);
var original = model.Methods.Single(m => m.Index == 24864); var recovered = pipeline.Recover(original);
var calls = new List<HCall>(); foreach (var b in recovered.Blocks) foreach (var s in b.Statements) FinallyFolding.Visit(s, e => { if (e is HCall c) calls.Add(c); });
var casts = calls.Where(c => c.This is HTypeExpr { Op: HTypeOp.CastClass }).ToArray();
if (recovered.Problems.Count != 0 || casts.Length != 11) throw new InvalidDataException("Original collision branch proof differs: casts=" + casts.Length + " gaps=" + string.Join(";", recovered.Problems));
var emitter = new AssemblyEmitter(model); emitter.Build(); var writer = new BodyEmitter(emitter, model) { RawAllocator = program.RawAllocator, TypeFromHandle = program.TypeFromHandle };
if (writer.Emit(original, recovered) is { } error) throw new InvalidDataException("Original collider emit failed: " + error);
var output = args[3];
if (Directory.Exists(output)) throw new IOException("Refuse previous original receiver proof"); Directory.CreateDirectory(output);
File.WriteAllText(output + "/24864.hir.txt", HirPrinter.Print(recovered));
File.WriteAllText(output + "/result.json", JsonSerializer.Serialize(new { complete = true, positive, negative, originalMethod = 24864, originalReceiverCasts = casts.Length, originalCalls = calls.Count, problems = recovered.Problems, emitted = true }));
Console.WriteLine("ORIGINAL_COLLIDER_TYPE_TEST_RECEIVER_PASS casts=" + casts.Length);
