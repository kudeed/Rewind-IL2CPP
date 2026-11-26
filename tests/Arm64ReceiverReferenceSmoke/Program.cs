using System.Buffers.Binary;
using System.Security.Cryptography;
using Rewind.Analysis.Arm64;
using Rewind.Binary;

// Native receiver-erased Boolean predicate: x1 retains the explicit reference
// argument; every normal entry path overwrites x0 before observing it.
// The null-argument path requires the independently identified argless throw.
const ulong Start=0x256a688, End=0x256a728, Throw=0x2355660;
uint[] code=[0xf81d0ffeu,0xa90157f6u,0xa9024ff4u,0xb0017cd4u,0xaa0103f3u,0x394a8288u,0x37000128u,0x900161e0u,0xf9400c00u,0x97f7ab54u,0x900161e0u,0xf9401400u,0x97f7ab51u,0x52800028u,0x390a8288u,0xb4000253u,0xf9401260u,0xb4000200u,0x900161f5u,0x2a1f03f4u,0xf94016b5u,0xb9401816u,0x6b16029fu,0x5400016au,0xf94002a2u,0x2a1403e1u,0x945c0164u,0xb40000c0u,0x39439008u,0x340000a8u,0xf9401260u,0x11000694u,0xb5fffea0u,0x97f7abd5u,0x6b16029fu,0xa9424ff4u,0xa94157f6u,0x1a9fb7e0u,0xf84307feu,0xd65f03c0u];
bool Prove(uint[] words,bool known=true)=>Arm64ReceiverProof.IsUnused(new CodeImage(words),Start,End,arglessThrow:t=>known&&t==Throw);
var native=new CodeImage(code);
if(native.Sha!="0e92f619cf43b53eeecf1f2b45dfd538d1d304502bb07172013a0f61e19fcaeb")throw new Exception("fixture hash");
var checks=new List<(string Name,bool Expected,bool Actual)>{("native cold/warm reference predicate",true,Prove(code)),("unidentified null throw",false,Prove(code,false))};
void Change(string name,int index,uint word){var m=code.ToArray();m[index]=word;checks.Add((name,false,Prove(m)));}
Change("incoming receiver copied instead of argument",4,0xaa0003f3u);
Change("cold path forwards stale receiver",7,0xd503201fu);
Change("warm path dereferences stale receiver",16,0xf9400000u);
Change("warm path calls unknown target before kill",16,0x94000000u);
Change("warm path returns stale receiver",16,0xd65f03c0u);
int bad=0;foreach(var c in checks){Console.WriteLine($"{c.Name}: {c.Actual} expected {c.Expected}");if(c.Actual!=c.Expected)bad++;}
Console.WriteLine($"REFERENCE_PREDICATE_RECEIVER_SMOKE checks={checks.Count} failed={bad}");
return bad==0?0:1;
sealed class CodeImage:NativeImage{
 public override ImageFormat Format=>ImageFormat.Elf;
 public string Sha=>Convert.ToHexString(SHA256.HashData(Memory)).ToLowerInvariant();
 public CodeImage(uint[] words){
  Arch=CpuArch.Arm64;PointerSize=8;MemoryBase=0x256a688;Memory=new byte[words.Length*4];
  for(int i=0;i<words.Length;i++)BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan(i*4),words[i]);
  Sections.Add(new ImageSection(".text",MemoryBase,(ulong)Memory.Length,SectionFlags.Read|SectionFlags.Execute));
 }
}
