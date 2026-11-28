using System.Buffers.Binary;
using System.Text.Json;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Ir;
using Rewind.Analysis.X64;
using Rewind.Binary;

if (args.Length != 1) throw new ArgumentException("Expected native oracle cases JSON");
var cases = JsonSerializer.Deserialize<Case[]>(File.ReadAllText(args[0]))!;
int passed = 0;
foreach (var test in cases)
{
    var image = new CodeImage(test.Functions);
    var context = new Context(image, test.Functions);
    var fn = new A64Lifter(context).Lift(0x1000);
    if (fn.Problems.Count != 0) throw new Exception(test.Name + ": " + string.Join(";", fn.Problems));
    if (fn.Blocks.SelectMany(b => b.Nodes).Any(n => n.Op == Op.Call && n.Aux is CallInfo { Target: 0x2000 }))
        throw new Exception(test.Name + ": returning branch trampoline was treated as a tail call");
    var memory = new Dictionary<ulong, byte>();
    void Write(ulong address, ulong value, int size) { for (int j = 0; j < size; j++) memory[address + (ulong)j] = (byte)(value >> (j * 8)); }
    ulong Read(ulong address, int size)
    {
        if (address < 0x8000 || address + (ulong)size > 0x10000) throw new Exception("IR memory out of bounds");
        ulong value = 0;
        for (int j = 0; j < size; j++) value |= (ulong)memory.GetValueOrDefault(address + (ulong)j) << (j * 8);
        return value;
    }
    foreach (var (address, value) in test.Memory) Write(ulong.Parse(address), value, 8);
    var values = new Dictionary<Node, ulong>();
    var results = new Dictionary<Node, ulong>();
    ulong Param(int reg) => reg switch { 0 => test.Args[0], 1 => test.Args[1], 2 => test.Args[2], 29 => 0xbad0, 30 => 0x8000, 31 => 0xf000, _ => 0 };
    ulong Eval(Node n)
    {
        if (values.TryGetValue(n, out ulong result)) return result;
        ulong A(int j) => Eval(n.In[j]);
        result = n.Op switch {
            Op.Const => n.UImm, Op.Param => Param((int)n.Imm),
            Op.Add => unchecked(A(0) + A(1)), Op.Sub => unchecked(A(0) - A(1)),
            Op.And => A(0) & A(1), Op.Or => A(0) | A(1), Op.Xor => A(0) ^ A(1),
            Op.Shl => A(0) << (int)A(1), Op.ShrU => A(0) >> (int)A(1),
            Op.CmpEq => A(0) == A(1) ? 1UL : 0UL, Op.CmpNe => A(0) != A(1) ? 1UL : 0UL,
            Op.CmpLtU => A(0) < A(1) ? 1UL : 0UL, Op.CmpLeU => A(0) <= A(1) ? 1UL : 0UL,
            Op.Trunc or Op.ZExt => A(0), Op.Concat => (A(0) << 32) | A(1),
            Op.Load => Read(A(0), n.Type.Bytes()),
            Op.Proj when n.Imm == CallResult.IntReturn => results[n.In[0]],
            _ => throw new Exception("Unsupported oracle IR operation: " + n.Op)
        };
        result &= n.Type.Mask(); values[n] = result; return result;
    }
    Block block = fn.Entry;
    Block? previous = null;
    ulong? returned = null;
    for (int steps = 0; steps < 10000 && returned == null; steps++)
    {
        int incoming = previous == null ? -1 : block.Preds.IndexOf(previous);
        var phis = block.Phis.Where(p => !p.Dead).Select(p => (p, value: Eval(p.In[incoming]))).ToArray();
        foreach (var (phi, value) in phis) values[phi] = value;
        foreach (var node in block.Nodes) values.Remove(node);
        Block? next = null;
        foreach (var n in block.Nodes.Where(n => !n.Dead))
        {
            switch (n.Op)
            {
                case Op.Call:
                    if (n.Aux is not CallInfo { Target: 0x3000 } info) throw new Exception("Unexpected external call");
                    int argument = info.Slots.FindIndex(s => s.Kind == ArgSlotKind.IntReg && s.Index == 0);
                    if (argument < 0) throw new Exception("Missing external scalar argument");
                    results[n] = unchecked(Eval(n.In[argument]) + 7);
                    break;
                case Op.Store: Write(Eval(n.In[0]), Eval(n.In[1]), n.In[1].Type.Bytes()); break;
                case Op.Jump: next = block.Succs.Single(); break;
                case Op.Branch: next = block.Succs[Eval(n.In[0]) != 0 ? 0 : 1]; break;
                case Op.Return: returned = Eval(n.In[0]); break;
                // Loads execute in program order. Other pure SSA expressions
                // are evaluated when consumed; unknown consumed values fail.
                case Op.Load: Eval(n); break;
            }
        }
        if (returned == null) { previous = block; block = next ?? throw new Exception("IR block did not transfer control"); }
    }
    if (returned != test.Expected) throw new Exception(test.Name + ": returned " + returned + " expected " + test.Expected);
    foreach (var (address, value) in test.ExpectedMemory)
        if (Read(ulong.Parse(address), 8) != value) throw new Exception(test.Name + ": memory mismatch at " + address);
    passed++;
}
var refusals = new (string Name, uint[] Body, bool Boundary)[] {
    ("return", [0xd65f03c0], false),
    ("call", [0x94000400, 0x17fffbff], false),
    ("indirect", [0xd61f0120], false),
    ("conditional", [0xb4000040, 0x17fffbff], false),
    ("invalid", [0xffffffff, 0x17fffbff], false),
    ("trap", [0xd4200000, 0x17fffbff], false),
    ("outside-return", [0x14000400], false),
    ("too-long", [0xd503201f,0xd503201f,0xd503201f,0xd503201f,0x17fffbfc], false),
    ("next-function", [0xd503201f,0x17fffbff], true),
};
foreach (var test in refusals)
{
    var functions = new Dictionary<string, uint[]> { ["4096"] = [0x14000400,0xd65f03c0], ["8192"] = test.Body };
    if (test.Boundary) functions["8196"] = [0x17fffbff];
    var cfg = A64Cfg.Build(new Context(new CodeImage(functions), functions), 0x1000);
    if (cfg.Blocks.Single(b => b.Start == 0x1000).End != BlockEnd.TailCall || cfg.Blocks.Any(b => b.Start == 0x2000))
        throw new Exception("External branch misclassified: " + test.Name);
}
Console.WriteLine($"ARM64_BRANCH_RETURN_DIFFERENTIAL_PASS native-cases={passed} refusal-cases={refusals.Length}");

sealed record Case(string Name, Dictionary<string, uint[]> Functions, ulong[] Args, Dictionary<string, ulong> Memory, ulong Expected, Dictionary<string, ulong> ExpectedMemory);
sealed class CodeImage : NativeImage
{
    public override ImageFormat Format => ImageFormat.Elf;
    public CodeImage(Dictionary<string, uint[]> functions)
    {
        Arch = CpuArch.Arm64; PointerSize = 8; MemoryBase = 0x1000; Memory = new byte[0x4000];
        foreach (var (address, words) in functions)
            for (int j = 0; j < words.Length; j++) BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan((int)(ulong.Parse(address) - MemoryBase) + j * 4), words[j]);
        Sections.Add(new ImageSection("il2cpp", MemoryBase, (ulong)Memory.Length, SectionFlags.Read | SectionFlags.Execute));
    }
}
sealed class Context(NativeImage image, Dictionary<string, uint[]> functions) : ILiftContext
{
    public NativeImage Image => image;
    public bool IsFunctionStart(ulong address) => functions.ContainsKey(address.ToString());
    public ulong NextFunctionStart(ulong address) => functions.Keys.Select(ulong.Parse).Where(a => a > address).DefaultIfEmpty(0x3000UL).Min();
    public bool IsNoReturn(ulong address) => false;
    public CallShape? ShapeOf(ulong address) => null;
    public bool ShouldInline(ulong address) => false;
}
