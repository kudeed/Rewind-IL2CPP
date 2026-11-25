using System.Buffers.Binary;
using System.Text.Json;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Ir;
using Rewind.Analysis.X64;
using Rewind.Binary;

if(args.Length!=1){Console.Error.WriteLine("usage: Arm64LaneSmoke cases.json (generate with oracle.py)");return 2;}
var cases=JsonSerializer.Deserialize<TestCase[]>(File.ReadAllText(args[0]))!;
int failures=0;
var counts=new Dictionary<string,int>();
foreach(var test in cases){
 try{
  var image=new TestImage(test.Word,test.Destination,test.Vector);
  var lifter=new A64Lifter(new TestContext(image));
  Function f=lifter.Lift(0x1000);
  if(f.Problems.Count!=0)throw new Exception(string.Join("; ",f.Problems));
  var stores=f.Blocks.SelectMany(b=>b.Nodes).Where(n=>n.Op==Op.Store).ToArray();
  if(stores.Length!=(test.Vector?2:1))throw new Exception("store count "+stores.Length);
  var cache=new Dictionary<Node,ulong>();
  ulong Eval(Node n){
   if(cache.TryGetValue(n,out var prior))return prior;
   ulong A(int i)=>Eval(n.In[i]);
   long Signed(Node x){ulong v=Eval(x);int bits=x.Type.Bits();return bits==64?unchecked((long)v):unchecked((long)((v^(1UL<<(bits-1)))-(1UL<<(bits-1))));}
   double Float(Node x)=>x.Type==VT.F32?BitConverter.Int32BitsToSingle(unchecked((int)Eval(x))):BitConverter.Int64BitsToDouble(unchecked((long)Eval(x)));
   ulong Bits(double x)=>n.Type==VT.F32?unchecked((uint)BitConverter.SingleToInt32Bits((float)x)):unchecked((ulong)BitConverter.DoubleToInt64Bits(x));
   ulong Param(int i)=>i<A64Lifter.VarV?test.Gp[i]:(test.Vectors[(i-A64Lifter.VarV)/2]>>(((i-A64Lifter.VarV)%2)*32))&0xffffffffUL;
   ulong value=n.Op switch{
    Op.Const=>n.UImm, Op.Param=>Param((int)n.Imm), Op.Trunc or Op.ZExt or Op.BitsToF or Op.FToBits=>A(0),
    Op.SExt=>unchecked((ulong)Signed(n.In[0])), Op.Concat=>(A(0)<<32)|A(1),
    Op.Add=>unchecked(A(0)+A(1)),Op.Sub=>unchecked(A(0)-A(1)),Op.Neg=>unchecked(0UL-A(0)),Op.And=>A(0)&A(1),Op.Or=>A(0)|A(1),Op.Xor=>A(0)^A(1),Op.Not=>~A(0),
    Op.Shl=>A(0)<<(int)(A(1)&(n.Type.Bits()==64?63UL:31UL)),
    Op.ShrU=>A(0)>>(int)(A(1)&(n.Type.Bits()==64?63UL:31UL)),
    Op.ShrS=>unchecked((ulong)(Signed(n.In[0])>>(int)(A(1)&(n.Type.Bits()==64?63UL:31UL)))),
    Op.CmpLtS=>Signed(n.In[0])<Signed(n.In[1])?1UL:0UL,Op.CmpLeS=>Signed(n.In[0])<=Signed(n.In[1])?1UL:0UL,
    Op.CmpLtU=>A(0)<A(1)?1UL:0UL,Op.CmpLeU=>A(0)<=A(1)?1UL:0UL,Op.CmpEq=>A(0)==A(1)?1UL:0UL,Op.CmpNe=>A(0)!=A(1)?1UL:0UL,
    Op.Select=>A(0)!=0?A(1):A(2),Op.FCmpLt=>Float(n.In[0])<Float(n.In[1])?1UL:0UL,
    Op.SIntToF=>n.Type==VT.F32?unchecked((uint)BitConverter.SingleToInt32Bits((float)Signed(n.In[0]))):Bits(Signed(n.In[0])),
    Op.UIntToF=>n.Type==VT.F32?unchecked((uint)BitConverter.SingleToInt32Bits((float)A(0))):Bits(A(0)),
    Op.FMul=>Bits(Float(n.In[0])*Float(n.In[1])),
    _=>throw new Exception("unhandled oracle IR op "+n.Op)
   };
   value&=n.Type.Mask();cache[n]=value;return value;
  }
  var actual=stores.Select(n=>Eval(n.In[1])).ToArray();
  if(!actual.SequenceEqual(test.Expected))throw new Exception("actual "+string.Join(",",actual.Select(v=>v.ToString("X16")))+" expected "+string.Join(",",test.Expected.Select(v=>v.ToString("X16"))));
  counts[test.Kind]=counts.GetValueOrDefault(test.Kind)+1;
 }catch(Exception e){failures++;if(failures<=20)Console.Error.WriteLine($"{test.Kind} {test.Word:X8}: {e.Message}");}
}
foreach(var (k,n) in counts.OrderBy(kv=>kv.Key))Console.WriteLine($"{k}: {n}");
Console.WriteLine($"ARM64_LANE_DIFFERENTIAL total={cases.Length} passed={cases.Length-failures} failed={failures}");
return failures==0?0:1;
sealed record TestCase(string Kind,uint Word,int Destination,bool Vector,ulong[] Gp,ulong[] Vectors,ulong[] Expected);
sealed class TestImage:NativeImage{
 public override ImageFormat Format=>ImageFormat.Elf;
 public TestImage(uint word,int dest,bool vector){
  Arch=CpuArch.Arm64;PointerSize=8;MemoryBase=0x1000;Memory=new byte[12];
  BinaryPrimitives.WriteUInt32LittleEndian(Memory,word);
  BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan(4),(vector?0x3D800000u:0xF9000000u)|(27u<<5)|(uint)dest);
  BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan(8),0xD65F03C0);
  Sections.Add(new ImageSection(".text",0x1000,12,SectionFlags.Read|SectionFlags.Execute));
 }
}
sealed class TestContext(NativeImage image):ILiftContext{
 public NativeImage Image=>image;public bool IsFunctionStart(ulong a)=>a==0x1000;public ulong NextFunctionStart(ulong a)=>0x100c;
 public bool IsNoReturn(ulong target)=>false;public CallShape? ShapeOf(ulong target)=>null;
}
