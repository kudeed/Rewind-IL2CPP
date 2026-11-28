using System.Buffers.Binary;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Binary;

static void Check(bool pass,string why){if(!pass)throw new Exception(why);}
var image=new FixtureImage();
static bool Known(ulong slot)=>slot>=0x2000&&slot<0x2400&&(slot&7)==0;
int comparisons=0,maxDepth=0;
for(int count=1;count<=128;count++){
 Check(LiteralLookupTable.TryRead(image,0x1000,count,Known,out ulong[] entries)&&entries.Length==count,"read "+count);
 var fn=new Function();var block=new Block();fn.Blocks.Add(block);
 var index=fn.NewNode(Op.Param,VT.I32,null);int pos=0;
 Node root=LiteralLookupTable.BuildChoice(fn,block,ref pos,index,entries,0x9000);
 int Depth(Node n)=>n.IsConst?0:1+Math.Max(Depth(n.In[1]),Depth(n.In[2]));
 int depth=Depth(root);maxDepth=Math.Max(depth,maxDepth);
 Check(depth<=(int)Math.Ceiling(Math.Log2(count)),"unbalanced table");
 // Verify dataflow and topological placement (not just the final tree).
 var seen=new HashSet<Node>();
 foreach(Node n in block.Nodes){
  Check(n.Addr==0x9000&&ReferenceEquals(n.Block,block),"source location lost");
  Check(n.In.All(x=>x.IsConst||ReferenceEquals(x,index)||seen.Contains(x)),"use before definition");
  seen.Add(n);
 }
 Check(pos==block.Nodes.Count,"insertion cursor");
 for(uint i=0;i<count;i++){
  Node n=root;
  while(!n.IsConst){
   Check(n.Op==Op.Select&&n.In[0].Op==Op.CmpLtU&&ReferenceEquals(n.In[0].In[0],index),"unexpected IR");
   n=n.In[i<n.In[0].In[1].UImm?1:2];
  }
  Check(n.UImm==entries[i],"lookup value mismatch");
  comparisons++;
 }
}
var cases=new (string Name,FixtureImage Image,ulong Address,int Count,Func<ulong,bool> IsString)[]{
 ("zero entries",image,0x1000,0,Known),
 ("too many entries",image,0x1000,129,Known),
 ("unaligned table",image,0x1001,1,Known),
 ("address overflow",image,ulong.MaxValue-7,2,Known),
 ("unmapped table",image,0x4000,1,Known),
 ("cross-section read",image,0x13f8,2,Known),
 ("mutable table",new FixtureImage(readOnlyEnd:0x1000),0x1000,1,Known),
 ("partial RELRO pointer",new FixtureImage(readOnlyEnd:0x1007),0x1000,1,Known),
 ("import slot",new FixtureImage(importSlot:0x1008),0x1000,2,Known),
 ("unknown slot",image,0x1000,4,s=>Known(s)&&s!=0x2018),
 ("unaligned slot",new FixtureImage(first:0x2001),0x1000,1,_=>true),
 ("unmapped target",new FixtureImage(first:0x4000),0x1000,1,_=>true),
 ("executable target",new FixtureImage(first:0x2800),0x1000,1,_=>true),
 ("cross-section target",new FixtureImage(first:0x23f8,targetSize:0x3fc),0x1000,1,_=>true),
 ("unsupported architecture",new FixtureImage(arch:CpuArch.X64),0x1000,1,Known)
};
foreach(var c in cases)
 Check(!LiteralLookupTable.TryRead(c.Image,c.Address,c.Count,c.IsString,out ulong[] r)&&r.Length==0,"accepted "+c.Name);
Console.WriteLine($"LITERAL_TABLE_SMOKE sizes=128 comparisons={comparisons} max_depth={maxDepth} negative={cases.Length} failed=0");
sealed class FixtureImage:NativeImage
{
 readonly ulong readOnlyEnd,importSlot;
 public override ImageFormat Format=>ImageFormat.Elf;
 public FixtureImage(CpuArch arch=CpuArch.Arm64,ulong readOnlyEnd=0x1400,ulong importSlot=0,ulong first=0x2000,ulong targetSize=0x400){
  Arch=arch;PointerSize=8;MemoryBase=0x1000;Memory=new byte[0x2000];this.readOnlyEnd=readOnlyEnd;this.importSlot=importSlot;
  Sections.Add(new ImageSection(".got",0x1000,0x400,SectionFlags.Read|SectionFlags.Write));
  Sections.Add(new ImageSection(".data",0x2000,targetSize,SectionFlags.Read|SectionFlags.Write));
  Sections.Add(new ImageSection(".text",0x2800,0x100,SectionFlags.Read|SectionFlags.Execute));
  for(int i=0;i<128;i++)BinaryPrimitives.WriteUInt64LittleEndian(Memory.AsSpan(i*8),i==0?first:0x2000+(ulong)(i*8));
 }
 public override bool IsReadOnlyAfterLoad(ulong va)=>va>=0x1000&&va<readOnlyEnd&&va!=importSlot;
}
