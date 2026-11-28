using System.Security.Cryptography;
using System.Text.Json;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Analysis.Runtime;
using Rewind.Binary;
using Rewind.Metadata;
using Rewind.Model;
using Rewind.Output;
if(args.Length!=4)throw new ArgumentException("Required: ORIGINAL_SO ORIGINAL_METADATA SIGNATURE_DIRECTORY FRESH_OUTPUT_DIRECTORY");
Node N(Op op,VT type,params Node[] inputs)=>new(){Op=op,Type=type,In=inputs};
Node C(long v,VT type=VT.I32)=>new(){Op=Op.Const,Type=type,Imm=v};
var p=N(Op.Param,VT.I32);var test=N(Op.CmpLtU,VT.I1,p,C(9));var widened=N(Op.ZExt,VT.I64,test);
int positive=0,negative=0;
void BoundCheck(string name,Block use,Node index,Node compared,long? expected){var got=Normalizer.Bound(use,index,compared);if(got!=expected)throw new InvalidDataException(name+": "+got+" != "+expected);if(expected==null)negative++;else positive++;}
BoundCheck("zero extended predicate",new(),widened,test,1);
BoundCheck("sign extended predicate",new(),N(Op.SExt,VT.I64,test),test,null);
BoundCheck("integer is not boolean",new(),N(Op.ZExt,VT.I64,p),p,null);
foreach(var (mask,zeroEdge,expect) in new[]{(0xfffffffcL,true,(long?)3),(0xfffffffcL,false,null),(0xfffffff5L,true,null),(0xfffffe00L,true,null)})
{
 var pred=new Block();var use=new Block();var other=new Block();use.Preds.Add(pred);pred.Succs.AddRange(zeroEdge?[use,other]:[other,use]);pred.Nodes.Add(N(Op.Branch,VT.None,N(Op.CmpEq,VT.I1,N(Op.And,VT.I32,p,C(mask)),C(0))));BoundCheck("masked domain "+mask+zeroEdge,use,N(Op.ZExt,VT.I64,p),p,expect);
}
Function Loop(long step=1,long end=4,bool reversed=false)
{
 var entry=new Block{Id=0};var head=new Block{Id=1};var tail=new Block{Id=2};var exit=new Block{Id=3};entry.Succs.Add(head);head.Preds.AddRange([entry,tail]);head.Succs.Add(tail);tail.Preds.Add(head);tail.Succs.AddRange(reversed?[exit,head]:[head,exit]);exit.Preds.Add(tail);
 var phi=N(Op.Phi,VT.I64);phi.Block=head;var next=N(Op.Add,VT.I64,phi,C(step,VT.I64));next.Block=tail;phi.In=[C(0,VT.I64),next];head.Phis.Add(phi);tail.Nodes.Add(next);tail.Nodes.Add(N(Op.Branch,VT.None,N(Op.CmpNe,VT.I1,next,C(end,VT.I64))));return new Function{Blocks=[entry,head,tail,exit]};
}
foreach(var (fn,expected) in new[]{(Loop(),(long?)3),(Loop(step:2),null),(Loop(end:0),null),(Loop(end:257),null),(Loop(reversed:true),null)})
{var got=Normalizer.InductionTableBound(fn,fn.Blocks[1],fn.Blocks[1].Phis[0]);if(got!=expected)throw new InvalidDataException("Induction bound "+got+" != "+expected);if(expected==null)negative++;else positive++;}
Console.WriteLine($"TABLE_DOMAIN_PASS positive={positive} negative={negative}");
var sf=new SigFactory();var single=sf.Primitive(Rewind.Runtime.Il2CppTypeEnum.R4);var layoutOwner=new TypeDef{Index=-9,Name="Layout",IsValueType=true};
Rewind.Model.FieldSlot Slot(int offset,int size=4,ushort attrs=6)=>new(new FieldDef{DeclaringType=layoutOwner,Name="f"+offset,Type=single,Attrs=attrs},single,offset,size);
Rewind.Model.TypeLayout Layout(params Rewind.Model.FieldSlot[] fields)=>new(){Known=true,Size=16,Fields=fields};
if(HirBuilder.WholePublicFieldRange(Layout(Slot(0),Slot(4),Slot(8),Slot(12)),4,12)is not{Length:3})throw new InvalidDataException("Complete struct tail rejected");
foreach(var c in new[]{(Layout(Slot(0),Slot(8),Slot(12)),4,12),(Layout(Slot(0),Slot(4,8),Slot(8),Slot(12)),4,12),(Layout(Slot(4,4,1),Slot(8),Slot(12)),4,12),(Layout(Slot(4,4,38),Slot(8),Slot(12)),4,12),(Layout(Slot(0),Slot(4),Slot(8),Slot(12)),5,11),(Layout(Slot(0),Slot(4),Slot(8),Slot(12)),4,13),(Layout(Slot(0),Slot(4),Slot(8),Slot(12)),-4,12),(Layout(Slot(0),Slot(4),Slot(8),Slot(12)),4,0),(Layout(Slot(0),Slot(4),Slot(8),Slot(12)),4,4)})
 if(HirBuilder.WholePublicFieldRange(c.Item1,c.Item2,c.Item3)!=null)throw new InvalidDataException("Invalid struct range accepted");
var unknown=Layout(Slot(0),Slot(4),Slot(8),Slot(12));unknown.Known=false;if(HirBuilder.WholePublicFieldRange(unknown,4,12)!=null)throw new InvalidDataException("Unknown layout accepted");
Console.WriteLine("PARTIAL_FIELD_RANGE_PASS positive=1 negative=10");
if(!UnityVersion.TryParse("6000.3.11f1",out var unity))throw new InvalidDataException("Unity version");
var native=File.ReadAllBytes(args[0]);var metadata=File.ReadAllBytes(args[1]);
string Sha(byte[] b)=>Convert.ToHexString(SHA256.HashData(b)).ToLowerInvariant();
if(Sha(native)!="031b3c7a09bb67f6f6c1c8c89b400848f75d023a8cdbe69f392872f72e787eae" || Sha(metadata)!="6b2c40f77fc5ac40c2e75be3cba0655a7d4bf9464fc694f6336f65c911383465")throw new InvalidDataException("Original input hashes differ");
var model=Il2CppModel.Load(NativeImage.Load(native,"original"),metadata,unity);
foreach(var (name,slots,expected) in new[]{("eleven original strings",new long[]{87643744,87641016,87604616,87650136,87673136,87662848,87647088,87651096,87641008,87649208,87668944},true),("one invalid slot",new long[]{87643744,0},false),("over budget",Enumerable.Repeat(87643744L,33).ToArray(),false)})
{
 var block=new Block{Id=0};var phi=N(Op.Phi,VT.I32,slots.Select(v=>C(v)).ToArray());phi.Block=block;block.Phis.Add(phi);
 for(int i=0;i<slots.Length;i++)block.Preds.Add(new Block{Id=i+1});
 var address=N(Op.ZExt,VT.I64,phi);address.Block=block;var load=N(Op.Load,VT.I64,address);load.Block=block;block.Nodes.AddRange([address,load]);var fn=new Function{Blocks=[block]};
 var norm=new Normalizer(new ProgramAnalysis(model,new Rewind.Analysis.Runtime.RuntimeHelpers(),new ModelCodeContext(model)));norm.CanonicalizeSlots(fn);
 if(load.Dead!=expected)throw new InvalidDataException("Metadata phi proof: "+name);
}
Console.WriteLine("METADATA_CHOICE_PASS positive=1 negative=2");
var discovery=HelperDiscovery.Discover(model,Directory.GetFiles(args[2],"*.sig"),Console.WriteLine);var program=new ProgramAnalysis(model,discovery.Helpers,discovery.Context);var pipeline=new MethodPipeline(program);var emitter=new AssemblyEmitter(model);emitter.Build();var writer=new BodyEmitter(emitter,model){RawAllocator=program.RawAllocator,TypeFromHandle=program.TypeFromHandle};
string root=args[3];if(Directory.Exists(root))throw new IOException("Previous bulk recovery evidence");Directory.CreateDirectory(root);var rows=new List<object>();
foreach(int index in new[]{24872,27995,27161,26696,26693,26587,26690})
{
 var method=model.Methods.Single(m=>m.Index==index);var body=pipeline.Recover(method);var error=writer.Emit(method,body);File.WriteAllText(root+"/"+index+".hir.txt",HirPrinter.Print(body));rows.Add(new{index,method=method.FullName,problems=body.Problems,notes=body.Notes,emitError=error});File.WriteAllText(root+"/methods.json",JsonSerializer.Serialize(rows,new JsonSerializerOptions{WriteIndented=true}));Console.WriteLine("ORIGINAL_BULK "+index+" gaps="+body.Problems.Count+" emit="+(error??"OK"));
 if(error!=null || index!=26690 && body.Problems.Count!=0)throw new InvalidDataException("Bulk method rejected "+index+": "+error+" "+string.Join(";",body.Problems));
}
File.WriteAllText(root+"/result.json",JsonSerializer.Serialize(new{complete=true,positive,negative,originalMethods=7}));Console.WriteLine("BULK_RULES_TARGETED_COMPLETE");
