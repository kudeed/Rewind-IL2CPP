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
Node obj=N(Op.Param,VT.I64);Node actual=N(Op.Load,VT.I64,obj);Node slot=new(){Op=Op.SlotValue,Type=VT.I64,Imm=0x1000};
int positive=0,negative=0;
foreach(var (condition,expected)in new[]{(N(Op.CmpEq,VT.I1,actual,slot),true),(N(Op.CmpNe,VT.I1,slot,actual),true),(N(Op.CmpLtU,VT.I1,actual,slot),false),(N(Op.CmpEq,VT.I1,obj,slot),false),(N(Op.CmpEq,VT.I1,actual,new Node{Op=Op.Const,Type=VT.I64,Imm=0x1000}),false),(N(Op.CmpEq,VT.I1,N(Op.Load,VT.I32,obj),slot),false),(N(Op.CmpEq,VT.I1,N(Op.Load,VT.I64,N(Op.Param,VT.I32)),slot),false),(N(Op.CmpEq,VT.I1,actual,new Node{Op=Op.SlotValue,Type=VT.I64,Imm=0x2000}),false),(N(Op.CmpEq,VT.I1,actual),false)})
{if(Normalizer.IsNativeClassCheck(condition,a=>a==0x1000)!=expected)throw new InvalidDataException("Class guard classifier differs");if(expected)positive++;else negative++;}
Console.WriteLine($"CLASS_GUARD_PASS positive={positive} negative={negative}");
(Function Fn,Node Index,Node Offset,Node Seed,Node Return) Loop(long step=1,long delta=108,long seedValue=32,bool parameter=false,bool unknown=false,bool wrongBase=false)
{
 var fn=new Function();var entry=new Block{Id=0};var head=new Block{Id=1};var tail=new Block{Id=2};var exit=new Block{Id=3};fn.Blocks.AddRange([entry,head,tail,exit]);entry.Succs.Add(head);head.Preds.AddRange([entry,tail]);head.Succs.Add(tail);tail.Preds.Add(head);tail.Succs.AddRange([head,exit]);exit.Preds.Add(tail);
 Node C(long v){var n=fn.NewNode(Op.Const,VT.I64,null);n.Imm=v;return n;}
 var index=fn.NewNode(Op.Phi,VT.I64,head);var offset=fn.NewNode(Op.Phi,VT.I64,head);head.Phis.AddRange([index,offset]);
 var seed=unknown?fn.NewNode(Op.Undef,VT.I64,null):parameter?fn.NewNode(Op.Param,VT.I64,null):C(seedValue);if(parameter)fn.Params[0]=seed;
 var next=fn.NewNode(Op.Add,VT.I64,tail,index,C(step));var advance=fn.NewNode(Op.Add,VT.I64,tail,wrongBase?index:offset,C(delta));index.In=[C(0),next];offset.In=[seed,advance];tail.Nodes.AddRange([next,advance]);var cmp=fn.NewNode(Op.CmpNe,VT.I1,tail,next,C(100));tail.Nodes.Add(cmp);tail.Nodes.Add(fn.NewNode(Op.Branch,VT.None,tail,cmp));var ret=fn.NewNode(Op.Return,VT.None,exit,offset);exit.Nodes.Add(ret);return(fn,index,offset,seed,ret);
}
positive=0;negative=0;
foreach(var (step,delta,seedValue,parameter)in new[]{(1L,108L,32L,false),(-1L,-12L,64L,false),(1L,12L,long.MaxValue,true),(-1L,108L,long.MinValue,true)})
{
 var x=Loop(step,delta,seedValue,parameter);if(AffineLoopOffsets.Run(x.Fn)!=1)throw new InvalidDataException("Proven paired induction rejected");long old=seedValue,index=0;
 long Eval(Node n)=>n==x.Index?index:n==x.Seed?seedValue:n.Op switch{Op.Const=>n.Imm,Op.Add=>unchecked(Eval(n.In[0])+Eval(n.In[1])),Op.Mul=>unchecked(Eval(n.In[0])*Eval(n.In[1])),_=>throw new InvalidDataException("Unexpected affine expression "+n.Op)};
 for(int i=0;i<100;i++){if(Eval(x.Return.In[0])!=old)throw new InvalidDataException("Original modular recurrence changed");old=unchecked(old+delta);index=unchecked(index+step);}positive++;
}
foreach(var x in new[]{Loop(step:2),Loop(delta:0),Loop(delta:4097),Loop(unknown:true),Loop(wrongBase:true)})
{if(AffineLoopOffsets.Run(x.Fn)!=0)throw new InvalidDataException("Unsupported recurrence accepted");negative++;}
var eh=Loop();eh.Fn.TryRegions.Add(new TryRegionInfo());if(AffineLoopOffsets.Run(eh.Fn)!=0)throw new InvalidDataException("Exception scope accepted");negative++;
Console.WriteLine($"AFFINE_OFFSET_PASS positive={positive} negative={negative} recurrenceSamples={positive*100}");
if(!UnityVersion.TryParse("6000.3.11f1",out var unity))throw new InvalidDataException("Unity version");
var native=File.ReadAllBytes(args[0]);var metadata=File.ReadAllBytes(args[1]);
string Sha(byte[] bytes)=>Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant();
if(Sha(native)!="031b3c7a09bb67f6f6c1c8c89b400848f75d023a8cdbe69f392872f72e787eae" || Sha(metadata)!="6b2c40f77fc5ac40c2e75be3cba0655a7d4bf9464fc694f6336f65c911383465")throw new InvalidDataException("Original input hashes differ");
var model=Il2CppModel.Load(NativeImage.Load(native,"original"),metadata,unity);
var discovery=HelperDiscovery.Discover(model,Directory.GetFiles(args[2],"*.sig"),Console.WriteLine);var program=new ProgramAnalysis(model,discovery.Helpers,discovery.Context);var pipeline=new MethodPipeline(program);var emitter=new AssemblyEmitter(model);emitter.Build();var writer=new BodyEmitter(emitter,model){RawAllocator=program.RawAllocator,TypeFromHandle=program.TypeFromHandle};
string root=args[3];if(Directory.Exists(root))throw new IOException("Previous bulk recovery evidence");Directory.CreateDirectory(root);var rows=new List<object>();
foreach(int index in new[]{27758,26690,28006,28614,28637})
{
 var method=model.Methods.Single(m=>m.Index==index);var body=pipeline.Recover(method);var error=writer.Emit(method,body);File.WriteAllText(root+"/"+index+".hir.txt",HirPrinter.Print(body));rows.Add(new{index,method=method.FullName,problems=body.Problems,notes=body.Notes,emitError=error});File.WriteAllText(root+"/methods.json",JsonSerializer.Serialize(rows,new JsonSerializerOptions{WriteIndented=true}));Console.WriteLine("ORIGINAL_CLASS_GUARD "+index+" gaps="+body.Problems.Count+" emit="+(error??"OK"));
 if(error!=null)throw new InvalidDataException("Class guard emit failed "+index+": "+error);
 if((index is 27758 or 26690 or 28006) && (body.Problems.Count!=0 || index==27758 && !HirPrinter.Print(body).Contains("NullReferenceException",StringComparison.Ordinal)))throw new InvalidDataException("Original class check/exception missing or unresolved");
}
File.WriteAllText(root+"/result.json",JsonSerializer.Serialize(new{complete=true,positive,negative,originalMethods=5}));Console.WriteLine("BULK_RULES_TARGETED_COMPLETE");
