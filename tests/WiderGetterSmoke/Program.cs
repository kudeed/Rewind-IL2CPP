using Rewind.Analysis.Recover;
using Rewind.Model;
static void Check(bool ok,string why){if(!ok)throw new Exception(why);}
var sf=new SigFactory();
var asm=new AssemblyModel{Name="Fixture"};
TypeDef Make(string name,int index,uint flags=0){
 var t=new TypeDef{Index=index,Name=name,Namespace="Synthetic",Assembly=asm,Flags=flags};
 t.Sig=sf.TypeDef(t);return t;
}
var parent=Make("IParent",1,TypeDef.Interface);
var middle=Make("IMiddle",2,TypeDef.Interface);middle.Interfaces=[parent.Sig];
var child=Make("IChild",3,TypeDef.Interface);child.Interfaces=[middle.Sig];
var unrelated=Make("IUnrelated",4,TypeDef.Interface);
var host=Make("Host",5);
var field=new FieldDef{Name="data",DeclaringType=host,Type=child.Sig,Offset=0x48};
host.Fields=[field];
var getter=new MethodDef{Name="get_Data",DeclaringType=host,ReturnType=parent.Sig,Address=0x1000};
const uint load=0xf9400000u|(9u<<10),ret=0xd65f03c0;
bool Test(TypeSig? expected=null,uint a=load,uint b=ret,int len=8,bool arm=true,int ptr=8)
 =>WiderGetterResult.ProvesFieldReturn(getter,field,expected??child.Sig,a,b,len,arm,ptr);
Check(Test(),"transitive interface getter");
getter.ReturnType=middle.Sig;Check(Test(),"direct interface getter");getter.ReturnType=parent.Sig;
Check(!Test(unrelated.Sig),"unrelated expected");
Check(!Test(a:load|1),"wrong target register");
Check(!Test(a:load|32),"wrong base register");
Check(!Test(a:load+1024),"wrong offset");
Check(!Test(b:0xd503201f),"not ret");
Check(!Test(len:12),"extra code");
Check(!Test(arm:false),"wrong architecture");
Check(!Test(ptr:4),"wrong pointer width");
getter.Flags=MethodDef.Virtual;Check(!Test(),"virtual getter");getter.Flags=0;
getter.Flags=MethodDef.Static;Check(!Test(),"static getter");getter.Flags=0;
getter.ReturnType=unrelated.Sig;Check(!Test(),"unrelated return");getter.ReturnType=parent.Sig;
getter.ReturnType=child.Sig;Check(!Test(),"not narrower");getter.ReturnType=parent.Sig;
host.Fields=[field,new FieldDef{Name="overlap",DeclaringType=host,Offset=field.Offset,Type=child.Sig}];Check(!Test(),"overlap");host.Fields=[field];
field.Attrs=FieldDef.Static;Check(!Test(),"static field");field.Attrs=0;
field.Offset=0x4c;Check(!Test(),"unaligned field");field.Offset=0x48;
getter.Parameters=[new ParamDef{Type=parent.Sig}];Check(!Test(),"extra argument");getter.Parameters=[];
Check(Test(),"restore valid fixture");
Console.WriteLine("WIDER_GETTER_SMOKE_PASS positive=3 negative=16 native_shape_and_interface_ancestry=1");
