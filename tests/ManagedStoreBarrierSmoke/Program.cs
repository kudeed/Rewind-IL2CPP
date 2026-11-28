using System.Security.Cryptography;
using System.Text.Json;
using System.Buffers.Binary;
using System.Reflection;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Analysis.Runtime;
using Rewind.Analysis.X64;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Runtime;

int positive = 0, negative = 0;
void Check(bool ok, string label, bool accepted = false)
{
    if (!ok) throw new Exception(label);
    if (accepted) positive++; else negative++;
}
using var json = JsonDocument.Parse(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "native-bodies.json")));
var native = new Dictionary<ulong, A64Instruction[]>();
var sizes = new Dictionary<ulong, int>();
foreach (JsonElement f in json.RootElement.GetProperty("functions").EnumerateArray())
{
    ulong at = f.GetProperty("address").GetUInt64();
    byte[] bytes = Convert.FromHexString(f.GetProperty("bytes").GetString()!);
    Check(bytes.Length == f.GetProperty("length").GetInt32() &&
        Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant() == f.GetProperty("sha256").GetString(), "native fixture hash/extent", true);
    native[at] = Enumerable.Range(0, bytes.Length / 4).Select(i =>
        A64Decoder.Decode(BitConverter.ToUInt32(bytes, i * 4), at + (ulong)i * 4)).ToArray();
    sizes[at] = bytes.Length;
}
var exports = json.RootElement.GetProperty("exports").EnumerateObject().ToDictionary(p => p.Name, p => p.Value.GetUInt64());
A64Instruction[] Body(ulong at) => native.GetValueOrDefault(at) ?? [];
Dictionary<ulong, HelperInfo> Identify() => Arm64ExportHelperShapes.Identify(exports, sizes, Body, _ => null, _ => null);
var found = Identify();
Check(found.GetValueOrDefault(0x1F2D6F8UL) is { Kind: HelperKind.WriteBarrier, IntArgs: 1, NoReturn: false,
    ReturnsValue: false, ManagedStoreBarrierOnly: true }, "native one-argument mark-only alias", true);
Check(!found.ContainsKey(0x1F34D40), "STR wrapper is never a no-op");
Check(!found.ContainsKey(0x1F02C74), "public three-argument setter is never a no-op");
Check(Arm64MarkOnlyWriteBarrierShape.HasCompleteAliasExtent([new FunctionRange(0x1000, 0x1004, 0)], 0x1000), "complete four-byte alias extent", true);
Check(!Arm64MarkOnlyWriteBarrierShape.HasCompleteAliasExtent([new FunctionRange(0x1000, 0x1008, 0)], 0x1000), "branch prefix is not a whole alias");
Check(!Arm64MarkOnlyWriteBarrierShape.HasCompleteAliasExtent([new FunctionRange(0x1000, 0x1004, 0), new FunctionRange(0x1000, 0x1008, 0)], 0x1000), "conflicting extents rejected");
Check(!Arm64MarkOnlyWriteBarrierShape.HasCompleteAliasExtent([new FunctionRange(0x1000, 0x1004, 0, true)], 0x1000), "chained region is not an independent alias");
var dirty = Body(0x1EC2A68);
for (int i = 0; i < dirty.Length; i++)
{
    var mutant = (A64Instruction[])dirty.Clone();
    mutant[i] = A64Decoder.Decode(0, dirty[i].Address);
    Check(!Arm64MarkOnlyWriteBarrierShape.Matches(mutant), "dirty body instruction mutant " + i);
}
Check(!Arm64MarkOnlyWriteBarrierShape.Matches(dirty[..^1]), "partial mark body rejected");
Check(!Arm64MarkOnlyWriteBarrierShape.Matches(dirty.Append(A64Decoder.Decode(0xD65F03C0, dirty[^1].NextAddress)).ToArray()),
    "neighbor instructions rejected");
var genericStore = Body(0x1F34D40);
native[0x1F34D40] = [A64Decoder.Decode(0xD503201F, 0x1F34D40), genericStore[1]];
Check(!Identify().ContainsKey(0x1F2D6F8), "public store-to-dirty anchor must contain real store");
native[0x1F34D40] = genericStore;

void Accept(string label, Fixture f)
{
    HStmt[] statements = f.Hir.Statements.ToArray(); Node[] nodes = f.Block.Nodes.ToArray();
    HExpr producer = f.Assignment.Value;
    Check(f.Match(), label, true);
    Check(statements.SequenceEqual(f.Hir.Statements) && nodes.SequenceEqual(f.Block.Nodes) &&
        ReferenceEquals(producer, f.Assignment.Value), label + " proof preserves producer and all existing operations", true);
}
void Reject(string label, Action<Fixture> change)
{
    var f = new Fixture(); change(f); Check(!f.Match(), label);
}
Accept("field reference store", new());
var array = new Fixture(); array.Element(); Accept("array reference store", array);
var statics = new Fixture(); statics.StaticField(); Accept("static reference store", statics);
var effects = new Fixture(); effects.Assignment.Value = new HCall { Method = new MethodDef(), Type = effects.ObjectType };
effects.Witness = ManagedStoreBarrierProof.Record(effects.Store, effects.Assignment); Accept("effectful value producer retained once", effects);
var tail = new Fixture(); tail.Call.Op = Op.TailCall; Accept("void tail after reference store", tail);

Reject("missing typed witness", f => f.Witness = null);
Reject("different SSA destination", f => { var address = new Node { Op = Op.Param, Type = VT.I64 }; f.Call.In[0] = address; });
Reject("store SSA destination rewritten after witness", f => { var address = new Node { Op = Op.Param, Type = VT.I64 }; f.Store.In[0] = address; f.Call.In[0] = address; });
Reject("store SSA value rewritten after witness", f => f.Store.In[1] = new Node { Op = Op.Param, Type = VT.I64 });
Reject("store width rewritten after witness", f => f.Value.Type = VT.I32);
Reject("wrong ABI slot", f => ((CallInfo)f.Call.Aux!).Slots[0] = new(ArgSlotKind.Stack, 0));
Reject("extra argument", f => { f.Call.In = [f.Address, f.Address]; ((CallInfo)f.Call.Aux!).Slots.Add(new(ArgSlotKind.IntReg, 1)); });
Reject("live result", f => f.Used.Add(f.Projection));
Reject("live non-x0 projection", f => { f.Projection.Imm = CallResult.IntReturn2; f.Used.Add(f.Projection); });
Reject("live float projection", f => { f.Projection.Imm = CallResult.FloatLane0; f.Projection.Type = VT.I32; f.Used.Add(f.Projection); });
Reject("nonvoid tail", f => { f.Call.Op = Op.TailCall; f.ManagedVoid = false; });
Reject("cross-block witness", f => f.Store.Block = new Block());
Reject("removed original store", f => f.Block.Nodes.Remove(f.Store));
Reject("dead original store", f => f.Store.Dead = true);
Reject("intervening call", f => f.Insert(new Node { Op = Op.Call, Aux = new CallInfo() }));
Reject("intervening write", f => f.Insert(new Node { Op = Op.Store, In = [f.Address, f.Value] }));
Reject("intervening read", f => f.Insert(new Node { Op = Op.Load, Type = VT.I64, In = [f.Address] }));
Reject("intervening HIR statement", f => f.Hir.Statements.Add(new HEval(new HOpaque("effect"))));
Reject("rewritten assignment value", f => f.Assignment.Value = new HConst(null, f.ObjectType));
Reject("rewritten assignment destination", f => f.Assignment.Target = new HOpaque("raw") { Type = f.ObjectType });
Reject("raw pointer store", f => f.Location(new HDeref(new HArg(1)) { Type = f.ObjectType }));
Reject("metadata/opaque store", f => f.Location(new HOpaque("metadata") { Type = f.ObjectType }));
Reject("scalar field with reference annotation", f => { ((HField)f.Assignment.Target).Field.Type = f.IntType;
    f.Witness = ManagedStoreBarrierProof.Record(f.Store, f.Assignment); });
Reject("different declared reference field type", f => { ((HField)f.Assignment.Target).Field.Type = f.Sigs.Primitive(Il2CppTypeEnum.String);
    f.Witness = ManagedStoreBarrierProof.Record(f.Store, f.Assignment); });
Reject("scalar receiver local with reference annotation", f => { ((HField)f.Assignment.Target).Object =
    new HLocal(new HVar { Type = f.IntType }) { Type = f.Owner.Sig };
    f.Witness = ManagedStoreBarrierProof.Record(f.Store, f.Assignment); });
Reject("array local actual scalar type", f => { f.Element(); ((HElement)f.Assignment.Target).Array =
    new HLocal(new HVar { Type = f.IntType }) { Type = f.ArrayType };
    f.Witness = ManagedStoreBarrierProof.Record(f.Store, f.Assignment); });
Reject("array element reference annotation differs from declaration", f => { f.Element(); f.Assignment.Target.Type = f.Sigs.Primitive(Il2CppTypeEnum.String);
    f.Witness = ManagedStoreBarrierProof.Record(f.Store, f.Assignment); });
Reject("index local actual int64 type", f => { f.Element(); ((HElement)f.Assignment.Target).Index =
    new HLocal(new HVar { Type = f.Sigs.Primitive(Il2CppTypeEnum.I8) }) { Type = f.IntType };
    f.Witness = ManagedStoreBarrierProof.Record(f.Store, f.Assignment); });
Reject("whole struct copy", f => { f.Owner.IsValueType = true; f.Location(new HArg(0) { Type = f.Owner.Sig }); });
Reject("field on a raw/struct receiver", f => { f.Owner.IsValueType = true; f.Witness = ManagedStoreBarrierProof.Record(f.Store, f.Assignment); });
Reject("effectful field receiver", f => { ((HField)f.Assignment.Target).Object = new HCall { Type = f.Owner.Sig }; f.Witness = ManagedStoreBarrierProof.Record(f.Store, f.Assignment); });
Reject("effectful array getter", f => { f.Element(); ((HElement)f.Assignment.Target).Array = new HCall { Type = f.ArrayType }; f.Witness = ManagedStoreBarrierProof.Record(f.Store, f.Assignment); });
Reject("effectful array index", f => { f.Element(); ((HElement)f.Assignment.Target).Index = new HCall { Type = f.IntType }; f.Witness = ManagedStoreBarrierProof.Record(f.Store, f.Assignment); });
Reject("narrow reference store", f => { f.Value.Type = VT.I32; f.Witness = ManagedStoreBarrierProof.Record(f.Store, f.Assignment); });
Reject("indirect barrier", f => ((CallInfo)f.Call.Aux!).Indirect = true);
Reject("intrinsic barrier", f => ((CallInfo)f.Call.Aux!).Intrinsic = "unknown");
Reject("noreturn barrier", f => ((CallInfo)f.Call.Aux!).NoReturn = true);

// Actual ARM64 BL followed by a double store: both v0 lanes remain physical projections. Run the
// production unsupported-return binder, then the same HalfBits consumer that previously erased SJunk.
var machine = new BarrierReturnImage();
var lifter = new A64Lifter(new BarrierReturnContext(machine));
Function lifted = lifter.Lift(0x1000);
Check(lifted.Problems.Count == 0 && lifter.UnsupportedCounts.Count == 0, "ARM64 double consumer lifts", true);
Node nativeCall = lifted.Blocks.SelectMany(b => b.Nodes).Single(n => n.Op == Op.Call);
Node doubleStore = lifted.Blocks.SelectMany(b => b.Nodes).Single(n => n.Op == Op.Store && n.Addr == 0x1008);
Node doubleBits = doubleStore.In[1];
Check(doubleBits.Op == Op.Concat && doubleBits.In.Length == 2, "STR d0 consumes both lanes", true);
Node low = doubleBits.In[1], high = doubleBits.In[0];
Check(low.Op == Op.Proj && low.Imm == CallResult.FloatLane0 && high.Op == Op.Proj && high.Imm == CallResult.FloatLane1 &&
    ReferenceEquals(low.In.Single(), nativeCall) && ReferenceEquals(high.In.Single(), nativeCall), "live double projections were not Undef", true);
var recovery = (HirBuilder)System.Runtime.CompilerServices.RuntimeHelpers.GetUninitializedObject(typeof(HirBuilder));
var method = new HMethod(); var block = new HBlock(); var sem = new Dictionary<Node, Sem>();
var signatures = new SigFactory();
void Set(string field, object value) => typeof(HirBuilder).GetField(field, BindingFlags.NonPublic | BindingFlags.Instance)!.SetValue(recovery, value);
Set("_h", method); Set("_cur", block); Set("_sem", sem);
Set("_fn", lifted);
// Match the normally constructed builder's empty deferred-evidence state on Eval's cached path.
Set("_heldProblems", new Dictionary<Node, List<string>>());
Set("_heldUnder", new Dictionary<Node, List<Node>>());
Set("_heldPhiReads", new Dictionary<Node, List<Node>>());
Set("_uses", new Dictionary<Node, List<Node>> { [low] = [doubleBits], [high] = [doubleBits] });
Set("_int", signatures.Primitive(Il2CppTypeEnum.I4)); Set("_long", signatures.Primitive(Il2CppTypeEnum.I8));
block.Statements.Add(new HEval(new HOpaque("WriteBarrier"))); // the single effect already emitted by FinishCall
typeof(HirBuilder).GetMethod("PreserveManagedBarrierReturns", BindingFlags.NonPublic | BindingFlags.Instance)!
    .Invoke(recovery, [nativeCall, new Dictionary<int, Node> { [CallResult.FloatLane0] = low, [CallResult.FloatLane1] = high }]);
Check(block.Statements.Count(s => s is HEval) == 1 && block.Statements.OfType<HAssign>().Count() == 2 && method.Problems.Count == 2,
    "one helper effect plus explicit physical-lane markers", true);
var halfBits = typeof(HirBuilder).GetMethod("HalfBits", BindingFlags.NonPublic | BindingFlags.Instance)!;
Check(halfBits.Invoke(recovery, [low]) is HLocal && halfBits.Invoke(recovery, [high]) is HLocal &&
    sem[low] is SVal && sem[high] is SVal && block.Statements.OfType<HAssign>().All(s => s.Value is HOpaque { Problem: not null }),
    "double consumer retains typed markers instead of folding unknown lanes to zero", true);
Console.WriteLine(JsonSerializer.Serialize(new { pass = true, positive, negative,
    native_sha256 = json.RootElement.GetProperty("native_sha256").GetString() }));

sealed class Fixture
{
    public SigFactory Sigs = new();
    public TypeDef Owner;
    public TypeSig ObjectType, IntType, ArrayType;
    public Block Block = new();
    public HBlock Hir = new();
    public Node Address = new() { Op = Op.Param, Type = VT.I64 }, Value = new() { Op = Op.Param, Type = VT.I64 };
    public Node Store, Call, Projection;
    public HAssign Assignment;
    public ManagedStoreBarrierProof.Witness? Witness;
    public HashSet<Node> Used = [];
    public bool ManagedVoid = true;
    public Fixture()
    {
        ObjectType = Sigs.Primitive(Il2CppTypeEnum.Object); IntType = Sigs.Primitive(Il2CppTypeEnum.I4);
        ArrayType = Sigs.SzArray(ObjectType);
        Owner = new TypeDef { Name = "Owner", Assembly = new AssemblyModel { Name = "BarrierProof" } };
        Owner.Sig = Sigs.TypeDef(Owner);
        Store = new Node { Op = Op.Store, In = [Address, Value], Block = Block };
        var info = new CallInfo { Target = 0x1F2D6F8 }; info.Slots.Add(new(ArgSlotKind.IntReg, 0));
        Call = new Node { Op = Op.Call, In = [Address], Aux = info, Block = Block };
        Projection = new Node { Op = Op.Proj, Imm = CallResult.IntReturn, Type = VT.I64, In = [Call], Block = Block };
        Block.Nodes.AddRange([Store, Call, Projection]);
        Assignment = new HAssign(new HField { Field = new FieldDef { Name = "value", DeclaringType = Owner, Type = ObjectType },
            Object = new HArg(-1) { Type = Owner.Sig }, Type = ObjectType }, new HArg(0) { Type = ObjectType });
        Hir.Statements.Add(Assignment); Witness = ManagedStoreBarrierProof.Record(Store, Assignment);
    }
    public void Insert(Node n) { n.Block = Block; Block.Nodes.Insert(Block.Nodes.IndexOf(Call), n); }
    public void Location(HExpr location) { Assignment.Target = location; Witness = ManagedStoreBarrierProof.Record(Store, Assignment); }
    public void Element() => Location(new HElement { Array = new HArg(1) { Type = ArrayType },
        Index = new HConst(0, IntType), Type = ObjectType });
    public void StaticField() => Location(new HField { Field = new FieldDef { Name = "cache", DeclaringType = Owner,
        Type = ObjectType, Attrs = FieldDef.Static, Offset = 0 }, Object = null, Type = ObjectType });
    public bool Match() => ManagedStoreBarrierProof.CanElide(Witness, Call, Call.In[0], Hir, ManagedVoid, n => Used.Contains(n));
}

sealed class BarrierReturnImage : NativeImage
{
    public override ImageFormat Format => ImageFormat.Elf;
    public BarrierReturnImage()
    {
        // stp x29,x30,[sp,#-16]!; bl 0x2000; str d0,[x19]; ldp x29,x30,[sp],#16; ret
        uint[] words = [0xA9BF7BFD, 0x940003FF, 0xFD000260, 0xA8C17BFD, 0xD65F03C0];
        Arch = CpuArch.Arm64; PointerSize = 8; MemoryBase = 0x1000; Memory = new byte[words.Length * 4];
        for (int i = 0; i < words.Length; i++) BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan(i * 4), words[i]);
        Sections.Add(new ImageSection(".text", MemoryBase, (ulong)Memory.Length, SectionFlags.Read | SectionFlags.Execute));
    }
}

sealed class BarrierReturnContext(NativeImage image) : ILiftContext
{
    public NativeImage Image => image;
    public bool IsFunctionStart(ulong at) => at is 0x1000 or 0x2000;
    public ulong NextFunctionStart(ulong at) => 0x1014;
    public bool IsNoReturn(ulong target) => false;
    public CallShape? ShapeOf(ulong target) => target == 0x2000 ? new CallShape
        { Count = 1, IsFloat = new bool[4], IsDouble = new bool[4], Returns = CallReturn.Unknown } : null;
    public CallReturn ReturnOf(ulong target) => CallReturn.Unknown;
}
