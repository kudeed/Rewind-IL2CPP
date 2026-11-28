using Rewind.Analysis.Abi;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Runtime;
static void Check(bool value,string name){if(!value)throw new Exception(name);}
int positive=0,negative=0;
void Accept(string name,Fixture f){var before=f.Abi.Params.ToArray();var got=f.Adapt();Check(!ReferenceEquals(got,f.Abi)&&got.Return==ReturnKind.Buffer&&got.ReturnType==f.T&&got.UsesFullySharedReturnBuffer&&got.UsesFullySharedRuntime,name);var buffer=got.Params.Single(p=>p.Role==ParamRole.ReturnBuffer);var info=got.Params.Single(p=>p.Role==ParamRole.MethodInfo);Check(buffer.Position==f.InfoPosition&&buffer.Type==f.T&&buffer.Size==8&&info.Position==f.InfoPosition+1,name+" buffer order");Check(f.Abi.Return==ReturnKind.Integer&&f.Abi.Params.SequenceEqual(before),name+" original ABI unchanged");Check(got.Params.Where(p=>p.Role is not (ParamRole.ReturnBuffer or ParamRole.MethodInfo)).SequenceEqual(before.Where(p=>p.Role!=ParamRole.MethodInfo)),name+" managed argument locations");positive++;}
void Reject(string name,Action<Fixture> change){var f=new Fixture();change(f);Check(ReferenceEquals(f.Adapt(),f.Abi),name);negative++;}
Accept("registered fully shared T array return",new Fixture());
var str=new Fixture();str.Placeholder.Name="__Il2CppFullySharedGenericStructType";Accept("registered fully shared struct marker",str);
var instance=new Fixture();instance.Abi.Params.Insert(0,new AbiParam(ParamRole.This,-1,instance.T,PassKind.Integer,0,false,8));instance.InfoPosition=2;instance.Abi.Params[^1]=instance.Abi.Params[^1] with{Position=2};Accept("instance argument remains in place",instance);
var floating=new Fixture();floating.Abi.Params.Insert(0,new AbiParam(ParamRole.Argument,1,floating.Sigs.Primitive(Il2CppTypeEnum.R4),PassKind.Float,0,false,4));Accept("independent float argument bank",floating);
var extra=new Fixture();extra.Method.Parameters=extra.Method.Parameters.Concat([new ParamDef{Type=extra.Sigs.Primitive(Il2CppTypeEnum.I4)}]).ToArray();extra.InfoPosition=2;extra.Abi.Params[^1]=extra.Abi.Params[^1] with{Position=2};extra.Abi.Params.Insert(1,new AbiParam(ParamRole.Argument,1,extra.Sigs.Primitive(Il2CppTypeEnum.I4),PassKind.Integer,1,false,4));Accept("extra integer argument stays before return buffer",extra);
Reject("by-reference-only source requires later support",f=>f.Method.Parameters=[new ParamDef{Type=f.Sigs.ByRef(f.T)}]);
var container=new Fixture();var box=new TypeDef{Index=4,Name="Container`1",Assembly=container.Owner.Assembly};TypeSig sourceType=container.Sigs.GenericInst(box,[container.T]);container.Method.Parameters=[new ParamDef{Type=sourceType}];container.Abi.Params[0]=container.Abi.Params[0] with{Type=sourceType};Accept("generic reference source supports invoker",container);
Reject("source does not contain the returned T",f=>f.Method.Parameters=[new ParamDef{Type=f.Sigs.SzArray(f.Sigs.Primitive(Il2CppTypeEnum.Object))}]);
Reject("SDK-shaped unrelated arguments stay unselected",f=>f.Method.Parameters=[new ParamDef{Type=f.Sigs.Primitive(Il2CppTypeEnum.String)},new ParamDef{Type=f.Sigs.SzArray(f.Sigs.Primitive(Il2CppTypeEnum.Object))}]);
Reject("x64 is not selected",f=>f.Arch=CpuArch.X64);
Reject("zero body address",f=>f.Address=0);
Reject("different registered body",f=>f.Instance.Address++);
Reject("unregistered body",f=>f.Instances=[]);
Reject("other method at same address",f=>f.Instance.Method=new MethodDef());
Reject("same marker name in wrong namespace",f=>f.Placeholder.Namespace="Game");
Reject("different native marker name",f=>f.Placeholder.Name="Object");
Reject("ordinary object instantiation",f=>f.Instance.MethodArguments=[f.Sigs.Primitive(Il2CppTypeEnum.Object)]);
Reject("direct T parameter unsupported",f=>f.Method.Parameters=f.Method.Parameters.Concat([new ParamDef{Type=f.T}]).ToArray());
Reject("generic value type parameter unsupported",f=>{var value=new TypeDef{Index=3,Name="ValueTuple`1",IsValueType=true,Assembly=f.Owner.Assembly};f.Method.Parameters=f.Method.Parameters.Concat([new ParamDef{Type=f.Sigs.GenericInst(value,[f.T])}]).ToArray();});
Reject("nongeneric return",f=>f.Method.ReturnType=f.Sigs.Primitive(Il2CppTypeEnum.Object));
Reject("constructed generic value return",f=>{var value=new TypeDef{Index=3,Name="ValueTuple`1",IsValueType=true,Assembly=f.Owner.Assembly};f.Method.ReturnType=f.Sigs.GenericInst(value,[f.T]);});
Reject("platform buffer return already selected",f=>f.Abi.Return=ReturnKind.Buffer);
Reject("floating return",f=>f.Abi.Return=ReturnKind.Float);
Reject("no trailing MethodInfo",f=>f.Abi.Params.RemoveAll(p=>p.Role==ParamRole.MethodInfo));
Reject("integer register bank full",f=>f.Abi.Params[^1]=f.Abi.Params[^1] with{Position=7});
Reject("negative MethodInfo location",f=>f.Abi.Params[^1]=f.Abi.Params[^1] with{Position=-1});
Reject("existing return buffer",f=>f.Abi.Params.Add(new AbiParam(ParamRole.ReturnBuffer,-1,f.T,PassKind.Integer,8,false,8)));
Fixture VoidArray(){var f=new Fixture();f.Method.ReturnType=f.Sigs.Primitive(Il2CppTypeEnum.Void);f.Abi.Return=ReturnKind.Void;f.Abi.ReturnType=f.Method.ReturnType;f.Abi.ReturnSize=0;return f;}
var voidArray=VoidArray();var originalParameters=voidArray.Abi.Params.ToArray();var voidGot=voidArray.Adapt();
Check(!ReferenceEquals(voidGot,voidArray.Abi)&&voidGot.UsesFullySharedRuntime&&!voidGot.UsesFullySharedReturnBuffer&&voidGot.Return==ReturnKind.Void&&voidGot.Params.SequenceEqual(originalParameters),"void array keeps exact ABI");positive++;
void RejectVoid(string name,Action<Fixture> change){var f=VoidArray();change(f);Check(ReferenceEquals(f.Adapt(),f.Abi),name);negative++;}
RejectVoid("void x64 unsupported",f=>f.Arch=CpuArch.X64);
RejectVoid("void body unregistered",f=>f.Instances=[]);
RejectVoid("void reference source is not array",f=>f.Method.Parameters=[new ParamDef{Type=f.T}]);
RejectVoid("void nongeneric array unchanged",f=>f.Method.Parameters=[new ParamDef{Type=f.Sigs.SzArray(f.Sigs.Primitive(Il2CppTypeEnum.Object))}]);
RejectVoid("void extra argument unsupported",f=>f.Method.Parameters=f.Method.Parameters.Concat([new ParamDef{Type=f.Sigs.Primitive(Il2CppTypeEnum.I4)}]).ToArray());
RejectVoid("void instance shape unsupported",f=>f.Method.Flags=0);
RejectVoid("void missing MethodInfo",f=>f.Abi.Params.RemoveAt(1));
RejectVoid("void wrong MethodInfo register",f=>f.Abi.Params[1]=f.Abi.Params[1] with{Position=2});
Console.WriteLine($"FULLY_SHARED_ABI_PASS positive={positive} negative={negative}");
sealed class Fixture
{
 public SigFactory Sigs=new();public TypeDef Owner,Placeholder;public MethodDef Method;public TypeSig T;public MethodInst Instance;public MethodInst[] Instances;public MethodAbi Abi;public CpuArch Arch=CpuArch.Arm64;public ulong Address=0x1000;public int InfoPosition=1;
 public Fixture(){Owner=new TypeDef{Index=1,Name="Owner",Assembly=new AssemblyModel{Name="Fixture"}};Owner.Sig=Sigs.TypeDef(Owner);Method=new MethodDef{Name="Method",DeclaringType=Owner,Flags=MethodDef.Static};var gp=new GenericParam{Name="T",IsMethodParameter=true,Position=0,OwnerMethod=Method};T=Sigs.GenericParam(gp);Method.GenericParameters=[gp];Method.ReturnType=T;Method.Parameters=[new ParamDef{Type=Sigs.SzArray(T)}];Placeholder=new TypeDef{Index=2,Name="__Il2CppFullySharedGenericType",Namespace="Unity.IL2CPP.Metadata",Assembly=Owner.Assembly};Placeholder.Sig=Sigs.TypeDef(Placeholder);Instance=new MethodInst{Method=Method,MethodArguments=[Placeholder.Sig],Address=Address};Instances=[Instance];Abi=new MethodAbi{Return=ReturnKind.Integer,ReturnType=T,ReturnSize=8,Known=false,Params=[new AbiParam(ParamRole.Argument,0,Method.Parameters[0].Type,PassKind.Integer,0,false,8),new AbiParam(ParamRole.MethodInfo,-1,null,PassKind.Integer,InfoPosition,false,8)]};}
 public MethodAbi Adapt()=>FullySharedAbi.Adapt(Arch,Sigs,Method,Instances,Abi,Address);
}
