using System.Buffers.Binary;
using Rewind.Analysis.Recover;
using Rewind.Binary;
static void Check(bool pass,string why) { if(!pass)throw new Exception(why); }
bool Known(ulong a)=>a==0x1080;
var image=new FixtureImage();
Check(MetadataGotLoad.TryResolve(image,0x1008,Known,out ulong slot)&&slot==0x1080,"relocated metadata pointer");
Check(!MetadataGotLoad.TryResolve(image,0x1009,Known,out _),"unaligned");
Check(!MetadataGotLoad.TryResolve(image,0x1080,Known,out _),"mutable slot");
Check(!MetadataGotLoad.TryResolve(image,0x1010,Known,out _),"unknown target");
Check(!MetadataGotLoad.TryResolve(image,0x1018,Known,out _),"import slot");
Check(!MetadataGotLoad.TryResolve(image,0x1020,Known,out _),"partial RELRO");
Check(!MetadataGotLoad.TryResolve(image,0x1030,Known,out _),"executable section");
Check(!MetadataGotLoad.TryResolve(image,0x1038,Known,out _),"cross-section read");
Check(!MetadataGotLoad.TryResolve(image,ulong.MaxValue-7,Known,out _),"unmapped");
Check(!MetadataGotLoad.TryResolve(new FixtureImage(CpuArch.X64),0x1008,Known,out _),"unsupported architecture");
Console.WriteLine("METADATA_GOT_LOAD_PASS positive=1 negative=9");
sealed class FixtureImage:NativeImage
{
    public override ImageFormat Format=>ImageFormat.Elf;
    public FixtureImage(CpuArch arch=CpuArch.Arm64) {
        Arch=arch;PointerSize=8;MemoryBase=0x1000;Memory=new byte[0x100];
        Sections.Add(new ImageSection(".got",0x1000,0x2c,SectionFlags.Read|SectionFlags.Write));
        Sections.Add(new ImageSection(".text",0x1030,8,SectionFlags.Read|SectionFlags.Execute));
        Sections.Add(new ImageSection(".split",0x1038,4,SectionFlags.Read|SectionFlags.Write));
        Sections.Add(new ImageSection(".data",0x1080,0x80,SectionFlags.Read|SectionFlags.Write));
        foreach(int at in new[]{8,24,32,48,56,128})BinaryPrimitives.WriteUInt64LittleEndian(Memory.AsSpan(at),0x1080);
        BinaryPrimitives.WriteUInt64LittleEndian(Memory.AsSpan(16),0x10c0);
    }
    public override bool IsReadOnlyAfterLoad(ulong a)=>a>=0x1000&&a<0x1040&&a!=0x1018&&a!=0x1027;
}
