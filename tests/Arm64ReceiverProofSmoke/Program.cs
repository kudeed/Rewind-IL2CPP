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
var warmCold=new (string Name,bool Expected,uint[] Words)[]{
 ("incoming scalar ignored in cold/warm metadata paths",true,new[]{0xD10043FFu,0xAA0203F3u,0xB4000068u,0x90000000u,Ret,0x910003E0u,Ret}),
 ("cold path observes x0 before overwrite",false,new[]{0xD10043FFu,0xAA0203F3u,0xB4000068u,0x90000000u,Ret,0xAA0003E1u,0x910003E0u,Ret}),
 ("warm path observes x0 before overwrite",false,new[]{0xD10043FFu,0xAA0203F3u,0xB4000088u,0xF90003E0u,0x90000000u,Ret,0x910003E0u,Ret}),
 ("callee forwards stale x0 to call",false,new[]{0xAA0203F3u,0x94000002u,0x910003E0u,Ret}),
};
foreach(var c in warmCold){
 var im=new CodeImage(c.Words);bool actual=Arm64ReceiverProof.IsUnused(im,0x1000,0x1000+(ulong)c.Words.Length*4);
 if(actual!=c.Expected){Console.Error.WriteLine(c.Name+": "+actual+" expected "+c.Expected);failed++;}
}
Console.WriteLine($"INT32_RECEIVER_ENTRY_SMOKE positive={warmCold.Count(c=>c.Expected)} negative={warmCold.Count(c=>!c.Expected)} failed={failed}");
var throwCases=new (string Name,bool Expected,uint[] Words,bool KnownThrow)[]{
 ("argless throw or explicit overwrite",true,new[]{0xB4000061u,Kill,Ret,0x94000002u},true),
 ("unknown call or explicit overwrite",false,new[]{0xB4000061u,Kill,Ret,0x94000002u},false),
 ("observed receiver before throw",false,new[]{0xAA0003E1u,0x94000004u},true),
 ("normal return without overwrite",false,new[]{0xB4000061u,Kill,Ret,Ret},true),
};
foreach(var c in throwCases){
 var im=new CodeImage(c.Words);bool actual=Arm64ReceiverProof.IsUnused(im,0x1000,0x1000+(ulong)c.Words.Length*4,arglessThrow:a=>c.KnownThrow&&a==0x1014);
 if(actual!=c.Expected){Console.Error.WriteLine(c.Name+": "+actual+" expected "+c.Expected);failed++;}
}
Console.WriteLine($"BOOL_RECEIVER_THROW_SMOKE positive={throwCases.Count(c=>c.Expected)} negative={throwCases.Count(c=>!c.Expected)} failed={failed}");
uint[] repeatBool=[0x94000006u,0x36000040u,0x94000004u,Ret,Ret,Ret,Kill,Ret];
var repeated=new CodeImage(repeatBool);
if(!Arm64ReceiverProof.RepeatedBooleanCall(repeated,0x1008,0x1018))failed++;
foreach(int index in new[]{0,1,2}){
 var wrong=repeatBool.ToArray();wrong[index]^=1;
 if(Arm64ReceiverProof.RepeatedBooleanCall(new CodeImage(wrong),0x1008,0x1018))failed++;
}
if(Arm64ReceiverProof.RepeatedBooleanCall(repeated,0x1008,0x101c)||
   Arm64ReceiverProof.RepeatedBooleanCall(repeated,0x1004,0x1018))failed++;
Console.WriteLine($"BOOL_REPEAT_CALL_SMOKE positive=1 negative=5 failed={failed}");
var argCases=new (string Name,bool Expected,uint[] Words,bool KnownCall)[]{
 ("x2 direct kill",true,new[]{0xAA1F03E2u,Ret},false),
 ("x2 kill after proven unary metadata helper",true,new[]{0x94000004u,0xAA1F03E2u,Ret},true),
 ("unknown helper",false,new[]{0x94000004u,0xAA1F03E2u,Ret},false),
 ("incoming x2 read",false,new[]{0xAA0203E1u,0xAA1F03E2u,Ret},false),
 ("incoming x2 stored",false,new[]{0xF9000022u,0xAA1F03E2u,Ret},false),
 ("incoming x2 dereferenced",false,new[]{0xF9400043u,0xAA1F03E2u,Ret},false),
 ("known call without subsequent kill",false,new[]{0x94000004u,Ret},true),
 ("known call then stale read",false,new[]{0x94000004u,0xAA0203E1u,0xAA1F03E2u,Ret},true),
 ("wrong register kill",false,new[]{Kill,Ret},false),
};
foreach(var c in argCases){
 var im=new CodeImage(c.Words);
 bool actual=Arm64ReceiverProof.IsUnused(im,0x1000,0x1000+(ulong)c.Words.Length*4,2,a=>c.KnownCall&&a==0x1010);
 if(actual!=c.Expected){Console.Error.WriteLine(c.Name+": "+actual+" expected "+c.Expected);failed++;}
}
Console.WriteLine($"UNUSED_METADATA_ARG_SMOKE positive={argCases.Count(c=>c.Expected)} negative={argCases.Count(c=>!c.Expected)} failed={failed}");
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
