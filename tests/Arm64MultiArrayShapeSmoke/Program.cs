using System.Buffers.Binary;
using System.Text.Json;
using Rewind.Analysis.Runtime;
uint[] words=[0xF81F0FFE,0xF9400808,0xB9400109,0x6B09003F,0x54000122,0xF9400908,0x6B08005F,0x540000C2,0x9B010908,0x8B080C08,0xF9401100,0xF84107FE,0xD65F03C0,0x940B8765];
byte[] body=new byte[56];for(int i=0;i<words.Length;i++)BinaryPrimitives.WriteUInt32LittleEndian(body.AsSpan(i*4),words[i]);
int positive=0,negative=0;
void Require(bool v,string n){if(!v)throw new Exception(n);}
bool Match(byte[] b,ulong start,ulong target){
 var h=Arm64MultiArrayAccessShape.Match(b,start,a=>a==target);
 if(h!=null)Require(h.Kind==HelperKind.RectangularArrayGetAt&&h.IntArgs==3&&!h.NoReturn&&h.ReturnsValue,"helper contract");
 return h!=null;
}
Require(Match(body,0x20738A0,0x2355668),"original helper");positive++;
foreach(var (start,target) in new (ulong,ulong)[]{(0x1000,0x2000),(0x3000,0x2000)}){
 var b=(byte[])body.Clone();long d=(long)target-(long)(start+52);
 BinaryPrimitives.WriteUInt32LittleEndian(b.AsSpan(52),0x94000000|((uint)(d>>2)&0x03ffffff));
 Require(Match(b,start,target),"relocated");positive++;
}
for(int bit=0;bit<448;bit++){var b=(byte[])body.Clone();b[bit/8]^=(byte)(1<<(bit%8));Require(!Match(b,0x20738A0,0x2355668),"mutated bit "+bit);negative++;}
for(int length=0;length<56;length++){Require(!Match(body[..length],0x20738A0,0x2355668),"truncated "+length);negative++;}
Require(!Match([..body,0,0,0,0],0x20738A0,0x2355668),"trailing body");negative++;
Require(!Match(body,0x20738A0,0x2355660),"wrong exception helper");negative++;
Require(Arm64MultiArrayAccessShape.Match(body,ulong.MaxValue-30,_=>true)==null,"address overflow");negative++;
var result=new{pass=true,positive,negative};
Console.WriteLine(JsonSerializer.Serialize(result));
if(args.Length!=0)File.WriteAllText(args[0],JsonSerializer.Serialize(result,new JsonSerializerOptions{WriteIndented=true}));
