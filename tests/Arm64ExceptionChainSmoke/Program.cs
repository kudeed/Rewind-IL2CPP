// Fixtures: Unity 6000.3.12f1 ARM64 original libil2cpp.so SHA256 f0808ccac104a950c6b99a3f4a148c21ae0daed078105714b14ac2b58f1dd583.
using System.Text.Json;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Runtime;
static void Check(bool value,string name){if(!value)throw new Exception(name);}
string root=AppContext.BaseDirectory;
using var doc=JsonDocument.Parse(File.ReadAllText(root+"/native-bodies.json"));
var bodies=new Dictionary<ulong,A64Instruction[]>();foreach(var r in doc.RootElement.EnumerateArray()){ulong at=r.GetProperty("address").GetUInt64();byte[] bytes=Convert.FromHexString(r.GetProperty("bytes").GetString()!);bodies[at]=Enumerable.Range(0,bytes.Length/4).Select(i=>A64Decoder.Decode(BitConverter.ToUInt32(bytes,i*4),at+(ulong)i*4)).ToArray();}
var texts=new Dictionary<ulong,string>{{0xDBF635,"System"},{0xDC234A,"NullReferenceException"},{0xDD0687,"IndexOutOfRangeException"}};
A64Instruction[] Body(ulong at)=>bodies.GetValueOrDefault(at)??[];string? Text(ulong at)=>texts.GetValueOrDefault(at);
int positive=0,negative=0;
var known=Arm64ExceptionChain.FromNullThrower(0x2355660,Body,Text);Check(known!=null&&known.ImageGetter==0x23ABF20&&known.Factory==0x239D8D8&&known.Raise==0x239CF44,"native anchored runtime contract");positive++;
var factory=Body(0x239D038);Check(Arm64ExceptionChain.IsIndexFactory(factory,known!,Text),"native index factory");positive++;
Check(Arm64ExceptionChain.Raise(Body(0x239D028)) is {} raised&&raised.Factory==0x239D038&&raised.Raiser==known!.Raise,"native typed raiser");positive++;
Check(Arm64ExceptionChain.CallOnly(Body(0x2355668))==0x239D028,"native complete no-return call wrapper");positive++;
for(int i=0;i<factory.Length;i++){var bad=(A64Instruction[])factory.Clone();bad[i]=A64Decoder.Decode(0,bad[i].Address);Check(!Arm64ExceptionChain.IsIndexFactory(bad,known!,Text),"factory instruction mutant "+i);negative++;}
for(int i=0;i<Body(0x239D000).Length;i++){var save=bodies[0x239D000];var bad=(A64Instruction[])save.Clone();bad[i]=A64Decoder.Decode(0,bad[i].Address);bodies[0x239D000]=bad;Check(Arm64ExceptionChain.FromNullThrower(0x2355660,Body,Text)==null,"anchor factory mutant "+i);bodies[0x239D000]=save;negative++;}
Check(!Arm64ExceptionChain.IsIndexFactory(factory,known! with{Factory=known!.Factory+4},Text),"different factory target");negative++;
Check(!Arm64ExceptionChain.IsIndexFactory(factory,known! with{ImageGetter=known!.ImageGetter+4},Text),"different image getter target");negative++;
texts[0xDBF635]="Game";Check(!Arm64ExceptionChain.IsIndexFactory(factory,known!,Text),"wrong namespace");negative++;texts[0xDBF635]="System";
texts[0xDD0687]="OverflowException";Check(!Arm64ExceptionChain.IsIndexFactory(factory,known!,Text),"wrong exception overload");negative++;texts[0xDD0687]="IndexOutOfRangeException";
Check(!Arm64ExceptionChain.IsIndexFactory(factory.Append(factory[0]).ToArray(),known!,Text),"extra instruction after return");negative++;
Check(!Arm64ExceptionChain.IsIndexFactory(factory[..^1],known!,Text),"truncated function");negative++;
Check(Arm64ExceptionChain.CallOnly(Body(0x2355668).Concat(Body(0x239D028)).ToArray())==null,"adjacent function must not be scanned");negative++;
Check(Arm64ExceptionChain.Raise(Body(0x239D028).Append(A64Decoder.Decode(0xD65F03C0,0)).ToArray())==null,"returning wrapper rejected");negative++;
Check(Arm64ExceptionChain.FromNullThrower(0x2355668,Body,Text)==null,"untrusted bounds root cannot anchor itself");negative++;
var result=new{pass=true,positive,negative};File.WriteAllText(root+"/result.json",JsonSerializer.Serialize(result,new JsonSerializerOptions{WriteIndented=true}));Console.WriteLine($"EXCEPTION_CHAIN_PASS positive={positive} negative={negative}");
