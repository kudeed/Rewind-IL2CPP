using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;
using Rewind.Analysis.Recover;
static void Check(bool value, string message) { if (!value) throw new Exception(message); }
var sf = new SigFactory();
var asm = new AssemblyModel { Name = "Game" };
var core = new AssemblyModel { Name = "mscorlib" };
var objectType = new TypeDef { Index = 0, Name = "Object", Namespace = "System", Assembly = core }; objectType.Sig = sf.TypeDef(objectType);
var owner = new TypeDef { Index = 1, Name = "Owner", Assembly = asm }; owner.Sig = sf.TypeDef(owner);
var made = new TypeDef { Index = 2, Name = "Fresh", Assembly = asm }; made.Sig = sf.TypeDef(made);
var v = sf.Primitive(Il2CppTypeEnum.Void); var o = sf.Primitive(Il2CppTypeEnum.Object); var n = sf.Primitive(Il2CppTypeEnum.I4);
var field = new FieldDef { Name = "list", DeclaringType = owner, Type = o };
var freshField = new FieldDef { Name = "position", DeclaringType = made, Type = n };
var baseCtor = new MethodDef { Name = ".ctor", DeclaringType = objectType, ReturnType = v };
var caller = new MethodDef { Name = "Init", DeclaringType = owner, ReturnType = v };
var getter = new MethodDef { Name = "get_List", DeclaringType = owner, ReturnType = o };
HLocal L(HVar x) => new(x) { Type = x.Type };
HField F(FieldDef f,HExpr obj) => new() { Field = f, Object = obj, Type = f.Type };
var fresh = new HVar { Type = made.Sig }; var temp = new HVar { Type = o };
HMethod GetterBody() => new() { Method = getter, Blocks = [new HBlock { Statements = [new HReturn(F(field,new HArg(-1) { Type = owner.Sig }))] }] };
HMethod? body = GetterBody();
HMethod? Recover(MethodDef method) => ReferenceEquals(method,getter) ? body : null;
HCall Getter() => new() { Method = getter, This = new HArg(-1) { Type = owner.Sig }, Type = o };
List<HStmt> Site() => [
 new HAssign(L(fresh),new HTypeExpr(HTypeOp.Allocate,made.Sig,null) { Type = made.Sig }),
 new HEval(new HCall { Method = baseCtor, This = L(fresh), Type = v }),
 new HAssign(L(temp),Getter()),
 new HAssign(F(freshField,L(fresh)),new HArg(0) { Type = n }),
 new HReturn(null)
];
bool Gather(List<HStmt> site) => ScheduledConstructorReads.TryGatherGetters(caller,site,0,fresh,2,objectType,Recover,out var picked) && picked.SequenceEqual(new[]{1,3});
Check(Gather(Site()),"valid field getter in ordinary instance method");
Check(!ScheduledConstructorReads.TryGather(caller,Site(),0,fresh,2,out _),"old constructor-only match unexpectedly allowed method");
int negative = 0;
void Reject(string name,Action mutate,Action restore) { mutate(); Check(!Gather(Site()),name); restore(); negative++; }
Reject("virtual getter",()=>getter.Flags=MethodDef.Virtual,()=>getter.Flags=0);
Reject("static getter",()=>getter.Flags=MethodDef.Static,()=>getter.Flags=0);
Reject("getter parameter",()=>getter.Parameters=[new ParamDef { Type = n }],()=>getter.Parameters=[]);
Reject("wrong declaring type",()=>getter.DeclaringType=made,()=>getter.DeclaringType=owner);
Reject("wrong field declaring type",()=>field.DeclaringType=made,()=>field.DeclaringType=owner);
Reject("static field",()=>field.Attrs=0x10,()=>field.Attrs=0);
Reject("body unavailable",()=>body=null,()=>body=GetterBody());
Reject("body has gap",()=>body!.Problems.Add("gap"),()=>body=GetterBody());
Reject("body effect",()=>body!.Blocks[0].Statements.Insert(0,new HEval(new HCall { Method = baseCtor })),()=>body=GetterBody());
Reject("body wrong receiver",()=>((HField)((HReturn)body!.Blocks[0].Statements[0]).Value!).Object=new HArg(0),()=>body=GetterBody());
Reject("non-object base constructor",()=>baseCtor.DeclaringType=made,()=>baseCtor.DeclaringType=objectType);
Reject("base constructor arguments",()=>baseCtor.Parameters=[new ParamDef { Type = n }],()=>baseCtor.Parameters=[]);
Reject("fresh address escape",()=>fresh.AddressTaken=true,()=>fresh.AddressTaken=false);
Reject("destination address escape",()=>temp.AddressTaken=true,()=>temp.AddressTaken=false);
Reject("static caller",()=>caller.Flags=MethodDef.Static,()=>caller.Flags=0);
var mutations=new (string,Action<List<HStmt>>)[] {
 ("getter before base",s=>{var r=s[2];s[2]=s[1];s[1]=r;}),
 ("getter result read by constructor",s=>((HAssign)s[3]).Value=L(temp)),
 ("store to foreign object",s=>((HField)((HAssign)s[3]).Target).Object=new HArg(-1)),
 ("extra side effect",s=>s.Insert(3,new HEval(new HCall { Method = getter,This=new HArg(-1) }))),
 ("fresh object passed to getter",s=>((HCall)((HAssign)s[2]).Value).This=L(fresh)),
 ("getter call argument",s=>((HCall)((HAssign)s[2]).Value).Arguments=[L(fresh)]),
 ("getter aliases fresh local",s=>((HAssign)s[2]).Target=L(fresh)),
 ("duplicate moved destination",s=>s.Insert(3,s[2])),
 ("constructor publishes object",s=>s[3]=new HAssign(F(field,new HArg(-1)),L(fresh))),
 ("read after body completed",s=>{var x=s[2];s.RemoveAt(2);s.Insert(3,x);})
};
foreach (var (name,mutate) in mutations) { var site=Site(); mutate(site); Check(!Gather(site),name); negative++; }
var directRead = Site(); ((HAssign)directRead[2]).Value = F(field,new HArg(-1) { Type = owner.Sig });
Check(Gather(directRead),"direct field read before accessor folding");
foreach (var mutation in new Action<List<HStmt>>[] {
 s => ((HField)((HAssign)s[2]).Value).Object = L(fresh),
 s => ((HField)((HAssign)s[2]).Value).Object = new HArg(0),
 s => ((HField)((HAssign)s[2]).Value).Field = freshField,
 s => ((HAssign)s[3]).Value = L(temp)
}) { var site = Site(); ((HAssign)site[2]).Value = F(field,new HArg(-1) { Type = owner.Sig }); mutation(site); Check(!Gather(site),"unsafe direct field read"); negative++; }
Console.WriteLine($"SCHEDULED_GETTER_CTOR_PROOF_PASS positive=2 negative={negative}");

// Regression for evidence silently dropping every problem after the 64th.
var builder = (HirBuilder)System.Runtime.CompilerServices.RuntimeHelpers.GetUninitializedObject(typeof(HirBuilder));
var captured = new HMethod();
typeof(HirBuilder).GetField("_h",System.Reflection.BindingFlags.Instance|System.Reflection.BindingFlags.NonPublic)!.SetValue(builder,captured);
var problemMethod = typeof(HirBuilder).GetMethod("Problem",System.Reflection.BindingFlags.Instance|System.Reflection.BindingFlags.NonPublic)!;
for (int count = 0; count < 80; count++) problemMethod.Invoke(builder,["evidence problem " + count]);
Check(captured.Problems.Count == 80 && captured.Problems[79] == "evidence problem 79","problem evidence truncated");
Console.WriteLine("RECOVERY_PROBLEM_COMPLETENESS_PASS captured=80");
