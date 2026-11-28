using System.Reflection;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;

static void Check(bool ok,string label){if(!ok)throw new Exception(label);}
var flag=typeof(MethodPipeline).GetMethod("FlagMarkers",BindingFlags.NonPublic|BindingFlags.Static)!;
void Run(HMethod method)=>flag.Invoke(null,[method]);
string Marker(string name)=>$"native operation left in the code ({name})";
HMethod Body(params HExpr[] expressions)=>new(){Blocks=[new HBlock{Statements=expressions.Select(e=>(HStmt)new HEval(e)).ToList()}]};
int checks=0;
var existing=Body(new HOpaque("undefined"));existing.Problems.Add("unrelated existing failure");Run(existing);
Check(existing.Problems.SequenceEqual(new[]{"unrelated existing failure",Marker("undefined")}),"existing problem cannot hide undefined");checks++;
var repeated=Body(new HOpaque("undefined"),new HOpaque("undefined"),new HOpaque("Box",new HOpaque("klass")));Run(repeated);var once=repeated.Problems.ToArray();Run(repeated);
Check(repeated.Problems.SequenceEqual(once)&&repeated.Problems.Count==3,"marker kind deduplication and idempotence");checks++;
var many=Body(Enumerable.Range(0,180).Select(i=>(HExpr)new HOpaque("marker"+i)).ToArray());many.Problems.AddRange(Enumerable.Range(0,120).Select(i=>"original"+i));Run(many);
Check(many.Problems.Count==300&&Enumerable.Range(0,180).All(i=>many.Problems.Contains(Marker("marker"+i))),"all markers beyond old caps");checks++;
var linked=Body(new HOpaque("kept"){Problem="kept site"});linked.Problems.AddRange(Enumerable.Range(0,80).Select(i=>"other"+i));linked.Problems.AddRange(["gone site","kept site"]);linked.SiteProblems.UnionWith(["gone site","kept site"]);Run(linked);
Check(!linked.Problems.Contains("gone site")&&linked.Problems.Contains("kept site")&&linked.Problems.Contains(Marker("kept"))&&linked.Problems.Count==82,"site evidence is complete beyond64");checks++;
var unlinked=Body();unlinked.Problems.Add("existing nonsited issue");Run(unlinked);Check(unlinked.Problems.SequenceEqual(new[]{"existing nonsited issue"}),"nonsited diagnostic retained");checks++;
var unreachable=Body(new HOpaque("unreachable"));Run(unreachable);Check(unreachable.Problems.Count==0,"unreachable filler exemption unchanged");checks++;
var sf=new SigFactory();var asm=new AssemblyModel{Name="Test"};var t=new TypeDef{Index=1,Name="D",Assembly=asm};t.Sig=sf.TypeDef(t);
var ctor=new MethodDef{Name=".ctor",DeclaringType=t,ReturnType=sf.Primitive(Il2CppTypeEnum.Void)};
var cached=Body(new HCachedDelegate(new HField{Field=new FieldDef{Name="cache",DeclaringType=t,Type=t.Sig,Attrs=FieldDef.Static},Object=new HOpaque("cache owner")},new HNewObject{Constructor=ctor,Arguments=[new HOpaque("captured native")]}));Run(cached);
Check(cached.Problems.Contains(Marker("cache owner"))&&cached.Problems.Contains(Marker("captured native")),"cached delegate child coverage");checks++;
var marked=Body(new HOpaque("native remark"){Remark=true});marked.Problems.Add("other");Run(marked);Check(marked.Problems.Contains(Marker("native remark")),"remark does not conceal native gaps");checks++;
var retained=new HOpaque("opaque",new HConst(7,sf.Primitive(Il2CppTypeEnum.I4)));var unchanged=Body(retained);var statement=unchanged.Blocks[0].Statements[0];Run(unchanged);Check(ReferenceEquals(unchanged.Blocks[0].Statements[0],statement)&&ReferenceEquals(((HEval)statement).Expression,retained)&&retained.Operands.Length==1,"body is not rewritten");checks++;
Console.WriteLine($"RecoveryMarkerCompletenessSmoke passed: {checks} checks, 180 markers plus 120 original problems retained");
