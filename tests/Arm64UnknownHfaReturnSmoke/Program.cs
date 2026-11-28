using System.Buffers.Binary;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Ir;
using Rewind.Analysis.X64;
using Rewind.Binary;

int cases = 0, laneChecks = 0;
void Check(bool value, string why) { if (!value) throw new Exception(why); }
void Run(string name, bool indirect, CallShape? shape, CallReturn fallback, int results, bool wide)
{
    var image = new TestImage(indirect);
    var lifter = new A64Lifter(new TestContext(image, shape, fallback));
    Function fn = lifter.Lift(0x1000);
    Check(fn.Problems.Count == 0 && lifter.UnsupportedCounts.Count == 0, name + " lift");
    Node call = fn.Blocks.SelectMany(b => b.Nodes).Single(n => n.Op == Op.Call);
    var stores = fn.Blocks.SelectMany(b => b.Nodes).Where(n => n.Op == Op.Store).ToArray();
    Check(stores.Length == 64, name + " all q0-q31 stores");
    int[] low = [CallResult.FloatLane0, CallResult.Float1Lane0, CallResult.Float2Lane0, CallResult.Float3Lane0];
    int[] high = [CallResult.FloatLane1, CallResult.Float1Lane1, CallResult.Float2Lane1, CallResult.Float3Lane1];
    for (int v = 0; v < 32; v++)
    {
        Node[] lanes = Parts(stores[v * 2].In[1]).Concat(Parts(stores[v * 2 + 1].In[1])).ToArray();
        for (int lane = 0; lane < 4; lane++)
        {
            Node n = lanes[lane];
            bool returned = v < results && (lane == 0 || lane == 1 && wide);
            bool preserved = v is >= 8 and < 16 && lane < 2;
            string where = $"{name} v{v}.{lane}: {n.Op} {n.Imm}";
            if (returned)
                Check(n.Op == Op.Proj && n.Type == VT.I32 && n.Imm == (lane == 0 ? low[v] : high[v]) && ReferenceEquals(n.In.Single(), call), where);
            else if (preserved)
                Check(n.Op == Op.Param && n.Type == VT.I32 && n.Imm == A64Lifter.VarV + v * 4 + lane, where);
            else Check(n.Op == Op.Undef && n.Type == VT.I32, where);
            laneChecks++;
        }
    }
    cases++;
}
Run("unknown indirect", true, null, CallReturn.Unknown, 4, true);
Run("unknown direct", false, null, CallReturn.Unknown, 4, true);
Run("unknown shape default is not a one-lane proof", false, new CallShape { Returns = CallReturn.Unknown, Slots = [] }, CallReturn.Unknown, 4, true);
foreach (int count in new[] { 1, 2, 3, 4 })
{
    Run("known float HFA " + count, false, new CallShape { Returns = CallReturn.Float, FloatResults = count, Slots = [] }, CallReturn.Unknown, count, false);
    Run("known double HFA " + count, false, new CallShape { Returns = CallReturn.Double, FloatResults = count, Slots = [] }, CallReturn.Unknown, count, true);
}
Run("known void", false, new CallShape { Returns = CallReturn.Void, Slots = [] }, CallReturn.Unknown, 0, false);
Run("known integer", false, new CallShape { Returns = CallReturn.Integer, Slots = [] }, CallReturn.Unknown, 0, false);
Run("scalar float fallback", false, null, CallReturn.Float, 1, false);
Run("scalar double fallback", false, null, CallReturn.Double, 1, true);
Console.WriteLine($"Arm64UnknownHfaReturnSmoke passed: {cases} machine-code cases, {laneChecks} lane assertions");

static Node[] Parts(Node n)
{
    if (n.Op != Op.Concat || n.Type != VT.I64 || n.In.Length != 2) throw new Exception("expected paired 32-bit lanes in qword store: " + n.Op);
    return [n.In[1], n.In[0]];
}
sealed class TestImage : NativeImage
{
    public override ImageFormat Format => ImageFormat.Elf;
    public TestImage(bool indirect)
    {
        Arch = CpuArch.Arm64; PointerSize = 8; MemoryBase = 0x1000; Memory = new byte[(1 + 32 + 1) * 4];
        BinaryPrimitives.WriteUInt32LittleEndian(Memory, indirect ? 0xD63F0200u : 0x94000400u); // blr x16 / bl 0x2000
        for (int v = 0; v < 32; v++)
            BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan((v + 1) * 4), 0x3D800000u | ((uint)v << 10) | (19u << 5) | (uint)v); // str qV,[x19,#16*V]
        BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan((1 + 32) * 4), 0xD65F03C0u);
        Sections.Add(new ImageSection(".text", MemoryBase, (ulong)Memory.Length, SectionFlags.Read | SectionFlags.Execute));
    }
}
sealed class TestContext(NativeImage image, CallShape? shape, CallReturn fallback) : ILiftContext
{
    public NativeImage Image => image;
    public bool IsFunctionStart(ulong a) => a == 0x1000 || a == 0x2000;
    public ulong NextFunctionStart(ulong a) => 0x1088;
    public bool IsNoReturn(ulong target) => false;
    public CallShape? ShapeOf(ulong target) => target == 0x2000 ? shape : null;
    public CallReturn ReturnOf(ulong target) => target == 0x2000 ? fallback : CallReturn.Unknown;
}
