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
// Void return leaves x0 unconstrained; a scalar-return method cannot use
// this proof. Preserve rejection of arbitrary RET-register and read paths.
var voidCases=new (string Name,bool Expected,bool Void,uint[] Words)[]{
 ("void receiver-independent return",true,true,new[]{Ret}),
 ("nonvoid stale return",false,false,new[]{Ret}),
 ("void read then return",false,true,new[]{0xAA0003E1u,Ret}),
 ("void branch to return or kill",true,true,new[]{0xB4000041u,Kill,Ret}),
 ("void indirect return register x0",false,true,new[]{0xD65F0000u}),
 ("void forwards stale receiver",false,true,new[]{0x94000002u,Ret}),
};
foreach(var c in voidCases){
 var im=new CodeImage(c.Words);
 bool actual=Arm64ReceiverProof.IsUnused(im,0x1000,0x1000+(ulong)c.Words.Length*4,allowVoidReturn:c.Void);
 if(actual!=c.Expected){Console.Error.WriteLine(c.Name+": "+actual+" expected "+c.Expected);failed++;}
}
Console.WriteLine($"VOID_RECEIVER_EXIT_SMOKE positive={voidCases.Count(c=>c.Expected)} negative={voidCases.Count(c=>!c.Expected)} failed={failed}");
var indirectCases=new (string Name,bool Expected,uint[] Words)[]{
 ("AAPCS64 indirect UIVertex result leaves x0 unused",true,new[]{Ret}),
 ("indirect result still rejects x0 read",false,new[]{0xAA0003E1u,Ret}),
 ("indirect result still rejects unknown call",false,new[]{0x94000002u,Ret}),
 ("indirect result accepts x0 overwritten before return",true,new[]{Kill,Ret}),
 ("ordinary scalar return still rejects stale x0",false,new[]{Ret}),
};
foreach(var c in indirectCases){
 var im=new CodeImage(c.Words);
 bool actual=Arm64ReceiverProof.IsUnused(im,0x1000,0x1000+(ulong)c.Words.Length*4,
     allowIndirectStructReturn:c.Name.StartsWith("AAPCS64")||c.Name.StartsWith("indirect result"));
 if(actual!=c.Expected){Console.Error.WriteLine(c.Name+": "+actual+" expected "+c.Expected);failed++;}
}
Console.WriteLine($"INDIRECT_STRUCT_RECEIVER_EXIT_SMOKE positive={indirectCases.Count(c=>c.Expected)} negative={indirectCases.Count(c=>!c.Expected)} failed={failed}");
var sretCases=new (string Name,bool Expected,uint[] Words)[]{
 ("x8 copied to callee-saved sret pointer",true,new[]{0xAA0803F3u,Ret}), // mov x19,x8
 ("ordinary x7 copied to callee-saved register",false,new[]{0xAA0703F3u,Ret}),
 ("x8 scratch after first call is not an sret proof",false,new[]{0x94000001u,0xAA0803F3u,Ret}),
};
foreach(var c in sretCases){
 var im=new CodeImage(c.Words);
 bool actual=Arm64ReceiverProof.HasIndirectReturnBuffer(im,0x1000,0x1000+(ulong)c.Words.Length*4);
 if(actual!=c.Expected){Console.Error.WriteLine(c.Name+": "+actual+" expected "+c.Expected);failed++;}
}
Console.WriteLine($"AAPCS64_SRET_BUFFER_SMOKE positive={sretCases.Count(c=>c.Expected)} negative={sretCases.Count(c=>!c.Expected)} failed={failed}");

// Original CUIGraphic.uiVertexLerp entry (RVA 0x24e56b8), through mov x0,xzr.
// SIMD/GP register numbers are not interchangeable: the receiver survives
// until the explicit GP kill, while the native interpolation loads vertex data.
uint[] vertexEntry=[0xD10143FFu, 0xFD0013EAu, 0x6D0323E9u, 0xA9044FFEu, 0xB9402829u, 0xD0FF462Au, 0xBD402025u, 0xFD412142u, 0xAD404047u, 0x0E040D21u, 0x1E270123u, 0x53087D2Bu, 0xB9402849u, 0xFC42C031u, 0xFC42C052u, 0xFC43C033u, 0xFC43C054u, 0xAA1F03E0u,Ret];
if(!Arm64ReceiverProof.IsUnused(new CodeImage(vertexEntry),0x1000,0x1000+(ulong)vertexEntry.Length*4,allowIndirectStructReturn:true))failed++;
var gpRead=vertexEntry.ToArray();
// DUP V1.2S,W9 -> DUP V1.2S,W0. The explicit overwrite later is not enough.
gpRead[9]&=~(31u<<5);
if(Arm64ReceiverProof.IsUnused(new CodeImage(gpRead),0x1000,0x1000+(ulong)gpRead.Length*4,allowIndirectStructReturn:true))failed++;
var fpRead=vertexEntry.ToArray();
// FMOV S3,W9 -> FMOV S3,W0.
fpRead[10]&=~(31u<<5);
if(Arm64ReceiverProof.IsUnused(new CodeImage(fpRead),0x1000,0x1000+(ulong)fpRead.Length*4,allowIndirectStructReturn:true))failed++;
// GP register 0 is not killed by a SIMD-register-0 destination.
uint[] vectorZero=[(vertexEntry[9]&~31u),0xAA0003E1u,Ret];
if(Arm64ReceiverProof.IsUnused(new CodeImage(vectorZero),0x1000,0x100c,allowIndirectStructReturn:true))failed++;
Console.WriteLine($"NATIVE_UIVERTEX_RECEIVER_PROOF positive=1 negative=3 failed={failed}");

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
uint[] guardedArg=[0xf81e0ffeu,0xa9014ff4u,0xb4000061u,0xaa0103e0u,Ret,0x94000002u,Ret,Ret];
bool ArgGuard(uint[] words,bool known=true)=>Arm64ReceiverProof.GuardedFirstArgument(new CodeImage(words),0x1000,0x1020,a=>known&&a==0x101c);
if(!ArgGuard(guardedArg))failed++;
foreach(int ix in new[]{0,1,2,3,5}){
 var wrong=guardedArg.ToArray();wrong[ix]^=1;
 if(ArgGuard(wrong))failed++;
}
if(ArgGuard(guardedArg,false))failed++;
Console.WriteLine($"GUARDED_ARGUMENT_RECEIVER_SMOKE positive=1 negative=6 failed={failed}");
uint[] restoredTail=[0xa9414ff4u,0xf9400101u,0xa8c257feu,0x14000001u,Kill,Ret];
bool Tail(uint[] words,ulong target=0x1010)=>Arm64ReceiverProof.DirectRestoredTail(new CodeImage(words),0x100c,target);
if(!Tail(restoredTail))failed++;
foreach(int ix in new[]{0,1,2,3}){
 var wrong=restoredTail.ToArray();wrong[ix]^=1;
 if(Tail(wrong))failed++;
}
if(Tail(restoredTail,0x1014)||Arm64ReceiverProof.DirectRestoredTail(new CodeImage(restoredTail),0x1008,0x1010))failed++;
Console.WriteLine($"RESTORED_TAIL_RECEIVER_SMOKE positive=1 negative=6 failed={failed}");
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
// Exact call-site proof: indirect transfer, wrong destination, wrong
// branch kind and unaligned/unmapped sites cannot justify a receiver.
var directSite=new CodeImage(new[]{0x94000002u,Ret,Kill,Ret});
if(!Arm64ReceiverProof.ExactDirectTransfer(directSite,0x1000,0x1008,false))failed++;
var tailSite=new CodeImage(new[]{0x14000002u,Ret,Kill,Ret});
if(!Arm64ReceiverProof.ExactDirectTransfer(tailSite,0x1000,0x1008,true))failed++;
foreach(var wrong in new[]{0xd63f0000u,0xd61f0000u,0x94000001u,0x14000002u})
    if(Arm64ReceiverProof.ExactDirectTransfer(new CodeImage(new[]{wrong,Ret,Kill,Ret}),0x1000,0x1008,false))failed++;
if(Arm64ReceiverProof.ExactDirectTransfer(directSite,0x1001,0x1008,false)||
   Arm64ReceiverProof.ExactDirectTransfer(directSite,0x1000,0x1010,false)||
   Arm64ReceiverProof.ExactDirectTransfer(directSite,0x1000,0x1008,true))failed++;
Console.WriteLine($"EXACT_DIRECT_RECEIVER_SITE_SMOKE positive=2 negative=7 failed={failed}");
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
