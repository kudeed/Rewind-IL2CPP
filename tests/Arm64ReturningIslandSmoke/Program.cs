using System.Buffers.Binary;
using System.Text.Json;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.X64;
using Rewind.Binary;

static uint Branch(ulong from, ulong to) => 0x14000000U | (uint)(((long)to - (long)from) >> 2) & 0x03ffffffU;
static void Check(bool ok, string message) { if (!ok) throw new Exception(message); }
static Fixture New(uint load = 0xF9430AB5) => new(load);
int positive = 0, negative = 0;
void AssertIsland(Fixture f, string label) {
    var cfg = A64Cfg.Build(f, 0x1000);
    Check(cfg.Problems.Count == 0, label + ": CFG problems");
    Check(cfg.Blocks.Count == 3 && cfg.Blocks[0].Start == 0x1000, label + ": exact block count/entry");
    var entry = cfg.Blocks.Single(b => b.Start == 0x1000);
    var island = cfg.Blocks.Single(b => b.Start == 0x2000);
    var continuation = cfg.Blocks.Single(b => b.Start == 0x1008);
    Check(entry.End == BlockEnd.Jump && entry.Successors.SequenceEqual(new ulong[] { 0x2000 }), label + ": entry edge");
    Check(island.End == BlockEnd.Jump && island.Successors.SequenceEqual(new ulong[] { 0x1008 }), label + ": resume edge");
    Check(continuation.End == BlockEnd.Return, label + ": real continuation");
    Check(island.Instructions.Count == 2 && island.Instructions[0].Address == 0x2000 && island.Instructions[0].Word == f.Image.U32(0x2000) &&
          island.Instructions[1].Address == 0x2004 && island.Instructions[1].Word == f.Image.U32(0x2004), label + ": original bytes and addresses");
    Check(entry.Instructions.Count == 2 && entry.Instructions[1].Address == 0x1004 && entry.Instructions[1].Word == Branch(0x1004,0x2000), label + ": original source branch");
    Check(cfg.Limit == 0x1010, label + ": original extent");
    positive++;
}
void Reject(Action<Fixture> mutate, string label, bool protectedRoots = false, bool protectedLeaders = false, bool protectedCalls = false) {
    var f = New(); mutate(f);
    var cfg = A64Cfg.Build(f, 0x1000, protectedRoots ? new ulong[] { 0x100c } : null,
        protectedLeaders ? new ulong[] { 0x1008 } : null, protectedCalls ? _ => false : null);
    Check(!cfg.Blocks.Any(b => b.Start == 0x2000), label + ": unsafe island admitted");
    negative++;
}
foreach (uint word in new uint[] { 0xF9430AB5, 0xF94476D6, 0xF94666B5, 0xF9440129, 0xF945BED6, 0xF946C694, 0xF94582B5, 0x3DC01920 })
    AssertIsland(New(word), "original native load " + word.ToString("X8"));
AssertIsland(New(0xB9400040), "word load");
AssertIsland(New(0x39400040), "byte load");
AssertIsland(New(0x79400040), "halfword load");
Reject(f => f.Put(0x2004, Branch(0x2004,0x100c)), "skips continuation");
Reject(f => f.Put(0x2004, Branch(0x2004,0x1004)), "returns to source loop");
Reject(f => f.Put(0x2004, Branch(0x2004,0x1010)), "returns to next function");
Reject(f => f.Put(0x2004, 0xD65F03C0), "ret instead of branch");
Reject(f => f.Put(0x2004, 0xD61F0000), "indirect branch");
Reject(f => f.Put(0x2004, 0x94000000 | (Branch(0x2004,0x1008) & 0x03ffffff)), "return uses BL");
Reject(f => f.Put(0x2004, 0xD503201F), "no return branch");
Reject(f => f.Put(0x2000, 0x58000000), "PC-relative literal load");
Reject(f => f.Put(0x2000, 0xF9000040), "store");
Reject(f => f.Put(0x2000, 0x91000400), "arithmetic");
Reject(f => f.Put(0x2000, 0xF8408C40), "pre-index writeback");
Reject(f => f.Put(0x2000, 0xF8408440), "post-index writeback");
Reject(f => f.Put(0x2000, 0xF8626840), "register offset");
Reject(f => f.Put(0x2000, 0xF94003E0), "stack-relative load");
Reject(f => f.Put(0x2000, 0xD4200000), "trap");
Reject(f => f.Put(0x2000, 0), "invalid");
Reject(f => f.Put(0x1004, 0x94000000 | (Branch(0x1004,0x2000) & 0x03ffffff)), "entry uses BL");
Reject(f => f.Put(0x1004, Branch(0x1004,0x5000)), "unmapped target");
Reject(f => f.Native.Sections[1] = new("island",0x2000,8,SectionFlags.Read), "nonexecuting section");
Reject(f => f.Native.Sections[1] = new("island",0x2000,4,SectionFlags.Read|SectionFlags.Execute), "second instruction past section");
Reject(f => f.Limit = 0x1008, "continuation past function");
Reject(f => f.Starts.Add(0x1008), "continuation is another function");
Reject(f => f.NoReturn.Add(0x2000), "known nonreturn target");
Reject(_ => {}, "protected landing roots", protectedRoots:true);
Reject(_ => {}, "protected boundary leaders", protectedLeaders:true);
Reject(_ => {}, "protected split calls", protectedCalls:true);
var result = new { pass = true, positive, negative };
Console.WriteLine("RETURNING_LOAD_ISLAND_PASS " + JsonSerializer.Serialize(result));
File.WriteAllText(Path.Combine(AppContext.BaseDirectory,"result.json"),JsonSerializer.Serialize(result,new JsonSerializerOptions{WriteIndented=true}));

sealed class Fixture : ICodeContext {
    public FakeImage Native = new();
    public NativeImage Image => Native;
    public ulong Limit = 0x1010;
    public HashSet<ulong> Starts = [0x1000];
    public HashSet<ulong> NoReturn = [];
    public Fixture(uint load) {
        Put(0x1000,0xD503201F); Put(0x1004,0x140003FF); Put(0x1008,0xD65F03C0); Put(0x100c,0xD65F03C0);
        Put(0x2000,load); Put(0x2004,0x17FFFC01);
    }
    public void Put(ulong at,uint word)=>Native.Put(at,word);
    public bool IsFunctionStart(ulong address)=>address==Limit||Starts.Contains(address);
    public ulong NextFunctionStart(ulong address)=>address==0x1000?Limit:0;
    public bool IsNoReturn(ulong target)=>NoReturn.Contains(target);
}
sealed class FakeImage : NativeImage {
    public override ImageFormat Format=>ImageFormat.Elf;
    public FakeImage() {
        MemoryBase=0x1000; Memory=new byte[0x1008]; Arch=CpuArch.Arm64; PointerSize=8;
        Sections.Add(new("main",0x1000,0x10,SectionFlags.Read|SectionFlags.Execute));
        Sections.Add(new("island",0x2000,8,SectionFlags.Read|SectionFlags.Execute));
    }
    public void Put(ulong at,uint word)=>BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan((int)(at-MemoryBase),4),word);
}
