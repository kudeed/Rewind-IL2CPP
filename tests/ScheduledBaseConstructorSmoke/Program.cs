using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;
using Rewind.Analysis.Recover;
static void Check(bool value,string message) { if (!value) throw new Exception(message); }
var sf=new SigFactory(); var asm=new AssemblyModel { Name="Game" };
var v=sf.Primitive(Il2CppTypeEnum.Void); var n=sf.Primitive(Il2CppTypeEnum.I4); var f=sf.Primitive(Il2CppTypeEnum.R4);
TypeDef Type(int id,string name,TypeDef? parent=null,bool value=false) {var t=new TypeDef {Index=id,Name=name,Assembly=asm,BaseType=parent?.Sig,IsValueType=value};t.Sig=sf.TypeDef(t);return t;}
var ancestor=Type(1,"Ancestor");var parent=Type(2,"Base",ancestor);var child=Type(3,"Child",parent);var color=Type(4,"Color",null,true);
var ancestorCtor=new MethodDef{Name=".ctor",DeclaringType=ancestor,ReturnType=v};
var baseCtor=new MethodDef{Name=".ctor",DeclaringType=parent,ReturnType=v};
var childCtor=new MethodDef{Name=".ctor",DeclaringType=child,ReturnType=v};
var colorCtor=new MethodDef{Name=".ctor",DeclaringType=color,ReturnType=v,Parameters=[new ParamDef{Type=f}]};
var baseField=new FieldDef{Name="baseNumber",DeclaringType=parent,Type=n};
var ownField=new FieldDef{Name="ownNumber",DeclaringType=child,Type=n};
var ownColor=new FieldDef{Name="ownColor",DeclaringType=child,Type=color.Sig};
var colorField=new FieldDef{Name="r",DeclaringType=color,Type=f};
HField Field(FieldDef field)=>new(){Field=field,Object=new HArg(-1),Type=field.Type};
HStmt Store(FieldDef field,HExpr value)=>new HAssign(Field(field),value);
HStmt Call()=>new HEval(new HCall{Method=ancestorCtor,This=new HArg(-1),Type=v});
HMethod ColorBody()=>new(){Method=colorCtor,Blocks=[new HBlock{Statements=[Store(colorField,new HArg(0){Type=f}),new HReturn(null)]}]};
HMethod? body=ColorBody();
HMethod? Recover(MethodDef m)=>ReferenceEquals(m,colorCtor)?body:null;
List<HStmt> Template()=>[Store(baseField,new HConst(10,n)),Call()];
List<HStmt> Site(bool useColor=false)=>[Store(baseField,new HConst(10,n)),useColor?Store(ownColor,new HNewObject{Constructor=colorCtor,Type=color.Sig,Arguments=[new HConst(1f,f)]}):Store(ownField,new HConst(20,n)),Call(),new HReturn(null)];
bool Gather(List<HStmt> site,List<HStmt>? template=null)=>ScheduledBaseConstructorStores.TryGather(childCtor,baseCtor,site,template??Template(),Recover,out var picked)&&picked.SequenceEqual(new[]{0,2});
Check(Gather(Site()),"integer field scheduling");Check(Gather(Site(true)),"value constructor scheduling");int negative=0;
void Reject(string name,Action mutate,Action restore,bool useColor=false){mutate();Check(!Gather(Site(useColor)),name);restore();negative++;}
Reject("wrong direct base",()=>child.BaseType=ancestor.Sig,()=>child.BaseType=parent.Sig);
Reject("not caller constructor",()=>childCtor.Name="Init",()=>childCtor.Name=".ctor");
Reject("static caller",()=>childCtor.Flags=MethodDef.Static,()=>childCtor.Flags=0);
Reject("base has arguments",()=>baseCtor.Parameters=[new ParamDef{Type=n}],()=>baseCtor.Parameters=[]);
Reject("wrong ancestor target",()=>ancestorCtor.DeclaringType=child,()=>ancestorCtor.DeclaringType=ancestor);
Reject("ancestor has arguments",()=>ancestorCtor.Parameters=[new ParamDef{Type=n}],()=>ancestorCtor.Parameters=[]);
Reject("own field is static",()=>ownField.Attrs=0x10,()=>ownField.Attrs=0);
Reject("own field belongs to base",()=>ownField.DeclaringType=parent,()=>ownField.DeclaringType=child);
Reject("base field static",()=>baseField.Attrs=0x10,()=>baseField.Attrs=0);
Reject("value ctor body absent",()=>body=null,()=>body=ColorBody(),true);
Reject("value ctor body gap",()=>body!.Problems.Add("unknown"),()=>body=ColorBody(),true);
Reject("value ctor side effect",()=>body!.Blocks[0].Statements.Insert(0,Call()),()=>body=ColorBody(),true);
Reject("value ctor static field",()=>colorField.Attrs=0x10,()=>colorField.Attrs=0,true);
Reject("value ctor wrong field owner",()=>colorField.DeclaringType=child,()=>colorField.DeclaringType=color,true);
Reject("value type initializer side effect",()=>color.Methods=[new MethodDef{Name=".cctor",DeclaringType=color}],()=>color.Methods=[],true);
Reject("value ctor invalid parameter index",()=>((HAssign)body!.Blocks[0].Statements[0]).Value=new HArg(2){Type=f},()=>body=ColorBody(),true);
var mutations=new (string,Action<List<HStmt>>)[]{
 ("missing last constructor",s=>s[2]=new HReturn(null)),
 ("different last constructor",s=>((HCall)((HEval)s[2]).Expression).Method=baseCtor),
 ("different ancestor receiver",s=>((HCall)((HEval)s[2]).Expression).This=new HArg(0)),
 ("constructor argument",s=>((HCall)((HEval)s[2]).Expression).Arguments=[new HConst(0,n)]),
 ("different base constant",s=>((HAssign)s[0]).Value=new HConst(11,n)),
 ("derived initializer reads base field",s=>((HAssign)s[1]).Value=Field(baseField)),
 ("derived initializer call",s=>((HAssign)s[1]).Value=new HCall{Method=ancestorCtor,Type=n}),
 ("derived initializer wrong value type",s=>((HAssign)s[1]).Value=new HConst(1f,f)),
 ("derived initializer local escaped",s=>((HAssign)s[1]).Value=new HLocal(new HVar{Type=n,AddressTaken=true})),
 ("unmatched observable effect",s=>s.Insert(2,new HEval(new HCall{Method=ancestorCtor,This=new HArg(0)})))
};
foreach(var (name,mutate) in mutations){var site=Site();mutate(site);Check(!Gather(site),name);negative++;}
var ft=Template();((HAssign)ft[0]).Value=new HConst(0f,f);var fs=Site();((HAssign)fs[0]).Value=new HConst(-0f,f);Check(!Gather(fs,ft),"signed zero mismatched");negative++;
((HAssign)ft[0]).Value=new HConst(BitConverter.Int32BitsToSingle(0x7fc00001),f);((HAssign)fs[0]).Value=new HConst(BitConverter.Int32BitsToSingle(0x7fc00002),f);Check(!Gather(fs,ft),"nan payload mismatched");negative++;
Console.WriteLine($"SCHEDULED_BASE_CTOR_PROOF_PASS positive=2 negative={negative}");
