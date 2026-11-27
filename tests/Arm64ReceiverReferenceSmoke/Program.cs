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
// v69 real receiver fixtures: APK ARM64 bytes; exact null throw target only.
Actual("GetTimeAddGold",0x245a290,[0xd100c3ffu,0xa90157feu,0xa9024ff4u,0x90018555u,0xd0016a33u,0xb0016a34u,0x39656ea8u,0xf9420a73u,0xf9467294u,0x37000188u,0xd0016a20u,0xf941fc00u,0x97fbec4fu,0xd0016a20u,0xf9420800u,0x97fbec4cu,0xb0016a20u,0xf9467000u,0x97fbec49u,0x52800028u,0x39256ea8u,0xf9400260u,0xf9400281u,0xaa1f03e2u,0xf90007ffu,0x949a0a62u,0xb40003a0u,0xd0016a28u,0xaa0003f3u,0xf941fd08u,0xb9401269u,0xf9400100u,0xb940e408u,0x34000129u,0x35000048u,0x97fbec86u,0xaa1303e0u,0xa9424ff4u,0xa94157feu,0xaa1f03e1u,0x9100c3ffu,0x146de626u,0x35000048u,0x97fbec7eu,0xaa1f03e0u,0x946de567u,0x1e731000u,0xf90007e0u,0x910023e0u,0xaa1f03e1u,0x946ddf97u,0xa9424ff4u,0xa94157feu,0x9100c3ffu,0xd65f03c0u,0x97fbecbdu],"a32b4b978314628669103e38b9b862e1ee7bbb58bc400a3246b6c001d9a5c67d",21);
Actual("SetTimeAddGold",0x245aa18,[0xf81e0ffeu,0xa9014ff4u,0x90018554u,0xd0016a33u,0x39657288u,0xf941fe73u,0xf90007e1u,0x37000128u,0xd0016a20u,0xf941fc00u,0x97fbea6fu,0xd0016a20u,0xf9420800u,0x97fbea6cu,0x52800028u,0x39257288u,0xf9400260u,0xd0016a33u,0xb940e408u,0xf9420a73u,0x35000048u,0x97fbeab2u,0x910023e0u,0xaa1f03e1u,0x946de729u,0xf9400268u,0xaa0003e1u,0xaa1f03e2u,0xaa0803e0u,0x949a0866u,0xa9414ff4u,0xf84207feu,0xd65f03c0u],"6d60c7156ebe11714245425fa44ff8f976ca20a7249e965e74d9888969a2fff5",6);
Actual("EnableHoleCollider",0x2468150,[0xf81e0ffeu,0xa9014ff4u,0xd00184d4u,0xaa0103f3u,0x3967ea88u,0x370000c8u,0x900169c0u,0xf9461400u,0x97fbb4a3u,0x52800028u,0x3927ea88u,0xb4000193u,0x900169c8u,0xaa1303e0u,0xf9461508u,0xf9400101u,0x94163d9eu,0xb40000c0u,0xa9414ff4u,0x52800021u,0xaa1f03e2u,0xf84207feu,0x149c5cceu,0x97fbb52du],"caca041f52de6ca136371c0660a641d69e7e979c82ecbbc4257846159a7bfb29",3);
Actual("DisableHoleCollider",0x24681b0,[0xf81e0ffeu,0xa9014ff4u,0xd00184d4u,0xaa0103f3u,0x3967e688u,0x370000c8u,0x900169c0u,0xf9461400u,0x97fbb48bu,0x52800028u,0x3927e688u,0xb4000193u,0x900169c8u,0xaa1303e0u,0xf9461508u,0xf9400101u,0x94163d86u,0xb40000c0u,0xa9414ff4u,0x52800021u,0xaa1f03e2u,0xf84207feu,0x149c5cb6u,0x97fbb515u],"fc050cb13341d59a38472d9d0364bb23c7f242e8b2ec07567b59452fd4c4665f",3);
Actual("RectTransformDistance",0x24f6aa8,[0xfc1c0fecu,0x6d012bebu,0x6d0223e9u,0xa9034ffeu,0xb4000481u,0xaa0103f3u,0xaa0103e0u,0xaa1f03e1u,0x9497fd87u,0xaa1303e0u,0xaa1f03e1u,0x1e204008u,0x9497fde4u,0xaa1303e0u,0xaa1f03e1u,0x1e204009u,0x9497fe41u,0xaa1303e0u,0xaa1f03e1u,0x1e20400au,0x9497fd7bu,0xaa1303e0u,0xaa1f03e1u,0x1e20402bu,0x9497fdd8u,0xaa1303e0u,0xaa1f03e1u,0x1e20402cu,0x9497fe35u,0x1e2e1000u,0xa9434ffeu,0x1e213800u,0x1e2a0921u,0x1e200982u,0x1e213900u,0x6d4223e9u,0x1e222961u,0x6d412bebu,0xfc4407ecu,0xd65f03c0u,0x97f97ac6u],"8fc3d5491c68803759b1f0a8f269d4d4cebadc2e521c79e5f5970ce431ac655d",6);
Actual("LuckyWheelToggleInteractable",0x25becc4,[0xf81e0ffeu,0xa9014ff4u,0xb4000241u,0xaa0103e0u,0xaa1f03e1u,0x2a0303f3u,0xaa0203f4u,0x94948df2u,0xb4000180u,0x12000261u,0xaa1f03e2u,0x94949f0au,0xb4000114u,0x52800028u,0xaa1403e0u,0xaa1f03e2u,0x0a330101u,0xa9414ff4u,0xf84207feu,0x14949f02u,0x97f65a53u],"d0afe0919317e965fbf9c09d61387ceb10748eb373cc7a8b977708b25125475a",3);
Actual("PlayerDataGetUnlockSkin",0x25a0bd4,[0xd10143ffu,0xf90013feu,0xa90357f6u,0xa9044ff4u,0xf0017b15u,0xd0016036u,0xf0016034u,0x39550ea8u,0xf94312d6u,0xf9401294u,0x2a0103f3u,0xb9002fe2u,0x37000128u,0xd0016020u,0xf9431000u,0x97f6d1fbu,0xf0016020u,0xf9401000u,0x97f6d1f8u,0x52800028u,0x39150ea8u,0xf94002c8u,0x92800009u,0x910023e0u,0xaa1f03e1u,0xb9001bf3u,0xa900a7e8u,0x946a1fb6u,0xaa0003f3u,0x9100b3e0u,0xaa1f03e1u,0x94693c8au,0xf9400288u,0xaa0003e2u,0xaa1303e1u,0xaa1f03e3u,0xaa0803e0u,0x9463e0e5u,0x2a1f03e1u,0xaa1f03e2u,0x9494eef1u,0xa9444ff4u,0x7100001fu,0xa94357f6u,0x1a9f07e0u,0xf94013feu,0x910143ffu,0xd65f03c0u],"904c1b01bec672f416a7c5aa1f65e17cf43ed99706004ee963793cef50659c51",10);
void Actual(string name,ulong start,uint[] words,string hash,int mutate){
 var image=new CodeImage(words,start);
 if(image.Sha!=hash)throw new Exception(name+" fixture hash");
 bool Check(uint[] w,bool known)=>Arm64ReceiverProof.IsUnused(new CodeImage(w,start),start,start+(ulong)w.Length*4,arglessThrow:t=>known&&t==Throw);
 checks.Add((name+" native receiver independent",true,Check(words,true)));
 if(name.EndsWith("HoleCollider")||name=="RectTransformDistance"||name=="LuckyWheelToggleInteractable")checks.Add((name+" unknown null throw",false,Check(words,false)));
 var m=words.ToArray();m[mutate]=0xaa0003f3u;
 checks.Add((name+" injected incoming receiver read",false,Check(m,true)));
}
int bad=0;foreach(var c in checks){Console.WriteLine($"{c.Name}: {c.Actual} expected {c.Expected}");if(c.Actual!=c.Expected)bad++;}
Console.WriteLine($"REFERENCE_PREDICATE_RECEIVER_SMOKE checks={checks.Count} failed={bad}");
return bad==0?0:1;
sealed class CodeImage:NativeImage{
 public override ImageFormat Format=>ImageFormat.Elf;
 public string Sha=>Convert.ToHexString(SHA256.HashData(Memory)).ToLowerInvariant();
 public CodeImage(uint[] words,ulong start=0x256a688){
  Arch=CpuArch.Arm64;PointerSize=8;MemoryBase=start;Memory=new byte[words.Length*4];
  for(int i=0;i<words.Length;i++)BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan(i*4),words[i]);
  Sections.Add(new ImageSection(".text",MemoryBase,(ulong)Memory.Length,SectionFlags.Read|SectionFlags.Execute));
 }
}
