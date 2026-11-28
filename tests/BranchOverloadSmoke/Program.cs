using System.Text.Json;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Analysis.Runtime;
using Rewind.Binary;
using Rewind.Metadata;
using Rewind.Model;
using Rewind.Output;
using Rewind.Runtime;
if(args.Length!=4||args.Any(string.IsNullOrWhiteSpace))throw new ArgumentException("Required: original-library original-metadata signatures-directory fresh-output-directory");
var sigs=new SigFactory();var asm=new AssemblyModel{Name="Fixture"};
var obj=new TypeDef{Index=-1,Name="Object",Namespace="System",Assembly=asm};obj.Sig=sigs.TypeDef(obj);
var owner=new TypeDef{Index=-2,Name="Constructed",Assembly=asm,BaseType=obj.Sig};owner.Sig=sigs.TypeDef(owner);
var i4=sigs.Primitive(Il2CppTypeEnum.I4);var boolean=sigs.Primitive(Il2CppTypeEnum.Boolean);var nothing=sigs.Primitive(Il2CppTypeEnum.Void);
var seeded=new MethodDef{Name=".ctor",DeclaringType=owner,ReturnType=nothing,Parameters=[new ParamDef{Type=i4}]};var empty=new MethodDef{Name=".ctor",DeclaringType=owner,ReturnType=nothing};owner.Methods=[seeded,empty];
(HMethod M,HBlock B,HBlock Y,HBlock N,HVar V) Fixture()
{
 var m=new HMethod{Method=new MethodDef{Name="Caller",DeclaringType=owner,ReturnType=owner.Sig,Parameters=[new ParamDef{Type=i4}]}};var v=m.NewLocal(owner.Sig);HLocal Read()=>new(v){Type=owner.Sig};
 var join=new HBlock{Id=3,Statements=[new HReturn(Read())]};
 var y=new HBlock{Id=1,Statements=[new HEval(new HCall{Method=seeded,This=Read(),Arguments=[new HArg(0){Type=i4}],Type=nothing}),new HJump(join)]};
 var n=new HBlock{Id=2,Statements=[new HEval(new HCall{Method=empty,This=Read(),Type=nothing}),new HJump(join)]};
 var b=new HBlock{Id=0,Statements=[new HAssign(Read(),new HTypeExpr(HTypeOp.Allocate,owner.Sig,null){Type=owner.Sig}),new HBranch(new HCompare(HCompareOp.Eq,new HArg(0){Type=i4},new HConst(0,i4)){Type=boolean},y,n)]};m.Blocks=[b,y,n,join];return(m,b,y,n,v);
}
var p=Fixture();if(!BranchConstructorFolding.TryFold(p.M,p.B,0,sigs)||p.B.Statements[1]is not HAssign{Value:HSelect{WhenTrue:HNewObject{Arguments.Length:1},WhenFalse:HNewObject{Arguments.Length:0}}}||p.Y.Statements.Count!=1||p.N.Statements.Count!=1)throw new InvalidDataException("Overload construction did not preserve the selected signatures");
owner.Methods=[seeded,empty,new MethodDef{Name=".cctor",DeclaringType=owner,Flags=MethodDef.Static,ReturnType=nothing}];
var initialized=Fixture();if(!BranchConstructorFolding.TryFold(initialized.M,initialized.B,0,sigs))throw new InvalidDataException("Stable scalar condition incorrectly observes a type initializer");
owner.Methods=[seeded,empty];
int negative=0;
void Reject(string reason,Action<HMethod,HBlock,HBlock,HBlock,HVar> mutate)
{
 var f=Fixture();mutate(f.M,f.B,f.Y,f.N,f.V);if(BranchConstructorFolding.TryFold(f.M,f.B,0,sigs))throw new InvalidDataException("Unsafe overload construction accepted: "+reason);negative++;
}
Reject("address escape",(m,b,y,n,v)=>v.AddressTaken=true);
Reject("effect before constructor",(m,b,y,n,v)=>y.Statements.Insert(0,new HEval(new HCall{Method=empty})));
Reject("effectful condition",(m,b,y,n,v)=>((HBranch)b.Statements[1]).Condition=new HCall{Method=empty,Type=boolean});
Reject("extra constructor predecessor",(m,b,y,n,v)=>m.Blocks.Add(new HBlock{Id=4,Statements=[new HJump(y)]}));
Reject("early publication",(m,b,y,n,v)=>b.Statements.Insert(1,new HEval(new HLocal(v){Type=owner.Sig})));
Reject("local alias",(m,b,y,n,v)=>m.Blocks[3].Statements.Insert(0,new HAssign(new HLocal(m.NewLocal(owner.Sig)){Type=owner.Sig},new HLocal(v){Type=owner.Sig})));
Reject("exception scope",(m,b,y,n,v)=>y.Scope=0);
Reject("exception region",(m,b,y,n,v)=>m.TryRegions.Add(0,new HTryRegion()));
Console.WriteLine($"BRANCH_OVERLOAD_SYNTHETIC_PASS positive=2 negative={negative}");
if(!UnityVersion.TryParse("6000.3.11f1",out var unity))throw new InvalidDataException("Unity version");
var model=Il2CppModel.Load(NativeImage.Load(File.ReadAllBytes(args[0]),"original"),File.ReadAllBytes(args[1]),unity);
var discovered=HelperDiscovery.Discover(model,Directory.GetFiles(args[2],"*.sig"),Console.WriteLine);var program=new ProgramAnalysis(model,discovered.Helpers,discovered.Context);
var original=model.Methods.Single(m=>m.Index==26620);var random=model.FindType("System.Random")??throw new InvalidDataException("Random metadata missing");
Console.WriteLine("ORIGINAL_RANDOM_HIERARCHY "+JsonSerializer.Serialize(new{random.HasStaticConstructor,methods=random.Methods.Where(m=>m.Name is ".cctor" or "Finalize").Select(m=>m.FullName)}));
var body=new MethodPipeline(program).Recover(original);var output=args[3];if(Directory.Exists(output))throw new IOException("Previous overload original evidence");Directory.CreateDirectory(output);File.WriteAllText(output+"/26620.hir.txt",HirPrinter.Print(body));
if(body.Problems.Count!=0)throw new InvalidDataException("Original constructor recovery remains explicit: "+string.Join(";",body.Problems));
int choices=0,raw=0;foreach(var b in body.Blocks)foreach(var s in b.Statements)FinallyFolding.Visit(s,e=>{if(e is HSelect{WhenTrue:HNewObject,WhenFalse:HNewObject})choices++;if(e is HTypeExpr{Op:HTypeOp.Allocate})raw++;});
if(choices!=1||raw!=0)throw new InvalidDataException("Original overload allocation counts differ");
var emitter=new AssemblyEmitter(model);emitter.Build();var writer=new BodyEmitter(emitter,model){RawAllocator=program.RawAllocator,TypeFromHandle=program.TypeFromHandle};if(writer.Emit(original,body)is{}error)throw new InvalidDataException(error);
File.WriteAllText(output+"/result.json",JsonSerializer.Serialize(new{complete=true,positive=2,negative,originalMethod=26620,constructorChoices=choices,rawAllocations=raw}));Console.WriteLine("ORIGINAL_RANDOM_OVERLOAD_PASS");
