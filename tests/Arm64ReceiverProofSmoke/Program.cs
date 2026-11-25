using System.Buffers.Binary;
using Rewind.Analysis.Arm64;
using Rewind.Binary;

const uint Ret=0xD65F03C0, Kill=0xD2800000, Nop=0xD503201F;
var cases=new (string Name,bool Expected,uint[] Words)[]{
 ("movz x0",true,new[]{Kill,Ret}),
 ("movz w0",true,new[]{0x52800000u,Ret}),
 ("adrp x0",true,new[]{0x90000000u,Ret}),
 ("load from x1",true,new[]{0xF9400020u,Ret}),
 ("forward merge, both paths kill",true,new[]{0xB4000061u,Kill,Ret,Kill,Ret}),
 ("copy another register",true,new[]{0xAA0103E0u,Ret}),
 ("read through incoming x0",false,new[]{0xF9400000u,Ret}),
 ("store incoming x0",false,new[]{0xF9000020u,Kill,Ret}),
 ("copy incoming x0",false,new[]{0xAA0003E1u,Kill,Ret}),
 ("arithmetic reads x0",false,new[]{0x91000400u,Ret}),
 ("movk preserves x0",false,new[]{0xF2800020u,Kill,Ret}),
 ("test incoming x0",false,new[]{0xB4000040u,Kill,Kill,Ret}),
 ("one branch escapes without kill",false,new[]{0xB4000061u,Kill,Ret,Ret}),
 ("call before kill",false,new[]{0x94000002u,Kill,Ret}),
 ("tail transfer before kill",false,new[]{0x14000004u,Kill,Ret}),
 ("entry loop",false,new[]{0x14000000u,Kill,Ret}),
 ("return before kill",false,new[]{Ret}),
 ("no complete kill",false,new[]{Nop}),
 ("unsupported operation",false,new[]{0xFFFFFFFFu,Kill,Ret}),
};
int failed=0;
foreach(var c in cases){
 var i=new CodeImage(c.Words);
 bool actual=Arm64ReceiverProof.IsUnused(i,0x1000,0x1000+(ulong)c.Words.Length*4);
 if(actual!=c.Expected){Console.Error.WriteLine(c.Name+": "+actual+" expected "+c.Expected);failed++;}
}
var x=new CodeImage(new[]{Kill,Ret});
if(Arm64ReceiverProof.IsUnused(x,0x1001,0x1008)||Arm64ReceiverProof.IsUnused(x,0x1000,0x1010)||Arm64ReceiverProof.IsUnused(x,0x1000,0x1000))failed++;
Console.WriteLine($"RECEIVER_PROOF_SMOKE positive={cases.Count(c=>c.Expected)} negative={cases.Count(c=>!c.Expected)+3} failed={failed}");
return failed==0?0:1;
sealed class CodeImage:NativeImage{
 public override ImageFormat Format=>ImageFormat.Elf;
 public CodeImage(uint[] words){
  Arch=CpuArch.Arm64;PointerSize=8;MemoryBase=0x1000;Memory=new byte[words.Length*4];
  for(int i=0;i<words.Length;i++)BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan(i*4),words[i]);
  Sections.Add(new ImageSection(".text",MemoryBase,(ulong)Memory.Length,SectionFlags.Read|SectionFlags.Execute));
 }
}
