using System.Buffers.Binary;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Binary;

int positive=0,negative=0;
Node C(long address,VT type=VT.I64)=>new(){Op=Op.Const,Type=type,Imm=address};
Node P(params Node[] inputs)=>new(){Op=Op.Phi,Type=VT.I64,In=inputs};
Node Load(VT type,Node address)=>new(){Op=Op.Load,Type=type,In=[address]};
void Check(string name,NativeImage image,Node load,bool expected,ulong expectedBits=0)
{
 bool got=ImmutableImageLoad.TryRead(image,load,out long bits);
 if(got!=expected||got&&unchecked((ulong)bits)!=expectedBits||!got&&bits!=0)
  throw new InvalidDataException(name+": got="+got+" expected="+expected+" bits=0x"+unchecked((ulong)bits).ToString("x"));
 if(expected)positive++;else negative++;
}
var image=new FixtureImage();
foreach(var (type,mask)in new[]{(VT.I8,0xffUL),(VT.I16,0xffffUL),(VT.I32,0xffffffffUL),(VT.I64,ulong.MaxValue),(VT.F32,0xffffffffUL),(VT.F64,ulong.MaxValue)})
{
 image.Word(0x1010,0xfedcba9876543210);Check("exact scalar width "+type,image,Load(type,C(0x1010)),true,0xfedcba9876543210&mask);
}
foreach(uint value in new uint[]{0,0x80000000,0x3f800000,1,0x7f800000,0xff800000,0x7fc12345,0x7fa12345,0xffc98765})
{
 image.Word(0x1010,value);Check("float32 exact bits "+value.ToString("x"),image,Load(VT.F32,C(0x1010)),true,value);
}
foreach(ulong value in new ulong[]{0,0x8000000000000000,0x3ff0000000000000,1,0x7ff0000000000000,0xfff0000000000000,0x7ff8123456789abc,0x7ff0123456789abc,0xfff89876543210ab})
{
 image.Word(0x1010,value);Check("float64 exact bits "+value.ToString("x"),image,Load(VT.F64,C(0x1010)),true,value);
}
image.Word(0x1010,0x38d1b717);
Check("identical page phi plus offset",image,Load(VT.I32,new(){Op=Op.Add,Type=VT.I64,In=[P(C(0x1000),C(0x1000)),C(0x10)]}),true,0x38d1b717);
Check("nested exact address phi",image,Load(VT.I32,P(C(0x1010),P(C(0x1010),C(0x1010)))),true,0x38d1b717);
Check("last complete scalar in section",image,Load(VT.I64,C(0x1058)),true,0);
Check("writable data",image,Load(VT.I32,C(0x1060)),false);
Check("relro pointer slot stays with metadata proof",new FixtureImage(relro:true),Load(VT.I64,C(0x1060)),false);
Check("executable code",image,Load(VT.I32,C(0x1080)),false);
Check("missing section",image,Load(VT.I32,C(0x10a0)),false);
Check("not readable",new FixtureImage(readable:false),Load(VT.I32,C(0x1010)),false);
Check("cross data sections",image,Load(VT.I64,C(0x105c)),false);
Check("partly unmapped data",new FixtureImage(shortMemory:true),Load(VT.I64,C(0x1058)),false);
Check("unmapped address",image,Load(VT.I32,C(0x2000)),false);
Check("address-end overflow",image,Load(VT.I64,C(-4)),false);
Check("wrong architecture",new FixtureImage(arch:CpuArch.X64),Load(VT.I32,C(0x1010)),false);
Check("wrong image format",new FixtureImage(format:ImageFormat.PE),Load(VT.I32,C(0x1010)),false);
Check("wrong pointer width",new FixtureImage(pointerSize:4),Load(VT.I32,C(0x1010)),false);
Check("non-address scalar width",image,Load(VT.I32,C(0x1010,VT.I32)),false);
Check("ambiguous address phi",image,Load(VT.I32,P(C(0x1010),C(0x1020))),false);
Check("unknown address phi",image,Load(VT.I32,P(C(0x1010),new(){Op=Op.Param,Type=VT.I64})),false);
Check("empty address phi",image,Load(VT.I32,P()),false);
var cycle=P(C(0x1010));cycle.In=[C(0x1010),cycle];Check("cyclic address phi",image,Load(VT.I32,cycle),false);
Check("unknown address load",image,Load(VT.I32,Load(VT.I64,C(0x1010))),false);
Check("not a load",image,new(){Op=Op.Store,Type=VT.None,In=[C(0x1010),C(1)]},false);
Check("missing address",image,new(){Op=Op.Load,Type=VT.I32},false);
Check("extra address inputs",image,new(){Op=Op.Load,Type=VT.I32,In=[C(0x1010),C(0x1010)]},false);
Check("non-native boolean load",image,Load(VT.I1,C(0x1010)),false);
Check("non-scalar load",image,Load(VT.None,C(0x1010)),false);
Console.WriteLine("IMMUTABLE_IMAGE_LOAD_SMOKE_PASS positive="+positive+" negative="+negative+" checks="+(positive+negative)+" failures=0");

sealed class FixtureImage:NativeImage
{
 private readonly ImageFormat format;
 private readonly bool relro;
 public override ImageFormat Format=>format;
 public FixtureImage(CpuArch arch=CpuArch.Arm64,ImageFormat format=ImageFormat.Elf,int pointerSize=8,bool readable=true,bool shortMemory=false,bool relro=false)
 {
  Arch=arch;PointerSize=pointerSize;this.format=format;this.relro=relro;MemoryBase=0x1000;Memory=new byte[shortMemory?0x5c:0x100];
  Sections.Add(new ImageSection(".rodata",0x1000,0x60,readable?SectionFlags.Read:SectionFlags.None));
  Sections.Add(new ImageSection(".data",0x1060,0x20,SectionFlags.Read|SectionFlags.Write));
  Sections.Add(new ImageSection(".text",0x1080,0x20,SectionFlags.Read|SectionFlags.Execute));
 }
 public override bool IsReadOnlyAfterLoad(ulong address)=>relro&&address>=0x1060&&address<0x1080;
 public void Word(ulong address,ulong value)=>BinaryPrimitives.WriteUInt64LittleEndian(Memory.AsSpan((int)(address-MemoryBase)),value);
}
