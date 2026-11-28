using Rewind.Analysis.Recover;
using Rewind.Model;

static void Check(bool ok,string message){if(!ok)throw new Exception(message);}
static TypeDef Type(string name,bool value=false)
{
    var t=new TypeDef{Name=name,Namespace="Fixture",IsValueType=value};
    t.Sig=new TypeDefSig(t);return t;
}
static bool Same(TypeSig a,TypeSig b)
{
    if(!ReferenceEquals(a.Definition,b.Definition))return false;
    if(a is GenericInstSig x&&b is GenericInstSig y)
        return x.Arguments.Length==y.Arguments.Length&&x.Arguments.Zip(y.Arguments).All(p=>ReferenceEquals(p.First,p.Second));
    return a is not GenericInstSig&&b is not GenericInstSig;
}
static bool Is(TypeDef expected,TypeSig actual)=>
    InlineReceiverCompatibility.IsAssignable(expected.Sig,actual,Same,(_,parent)=>parent);

var obj=Type("Object");var animal=Type("Animal");var dog=Type("Dog");var cat=Type("Cat");
animal.BaseType=obj.Sig;dog.BaseType=animal.Sig;cat.BaseType=animal.Sig;
var iface=Type("IWalk");var derivedIface=Type("IRun");derivedIface.Interfaces=[iface.Sig];dog.Interfaces=[derivedIface.Sig];
var number=Type("Int32",true);var real=Type("Single",true);var text=Type("String");
text.BaseType=obj.Sig;
Check(Is(animal,dog.Sig),"derived receiver");
Check(Is(obj,dog.Sig),"object base receiver");
Check(Is(iface,dog.Sig),"transitive interface receiver");
Check(Is(derivedIface,dog.Sig),"direct interface receiver");
Check(Is(text,text.Sig),"exact reference receiver");
Check(Is(number,number.Sig),"exact value receiver");
Check(!Is(text,number.Sig),"reject value receiver for reference method");
Check(!Is(number,text.Sig),"reject reference receiver for value method");
Check(!Is(cat,dog.Sig),"reject unrelated reference types");
Check(!Is(iface,number.Sig),"reject value type for interface without constrained call");
Check(!Is(number,real.Sig),"reject different value types");

var iBox=Type("IBox");var box=Type("Box");box.Interfaces=[iBox.Sig];
var generic=Type("GenericBox");generic.Interfaces=[iBox.Sig];
Check(Is(iBox,generic.Sig),"generic interface definition identity");
var iBoxDog=new GenericInstSig(iBox,[dog.Sig]);
var iBoxCat=new GenericInstSig(iBox,[cat.Sig]);
var concrete=new GenericInstSig(box,[dog.Sig]);
TypeSig Substitute(TypeSig current,TypeSig parent)=>ReferenceEquals(current,concrete)&&ReferenceEquals(parent,iBox.Sig)?iBoxDog:parent;
Check(InlineReceiverCompatibility.IsAssignable(iBoxDog,concrete,Same,Substitute),"closed generic interface substitution");
Check(!InlineReceiverCompatibility.IsAssignable(iBoxCat,concrete,Same,Substitute),"different generic argument");
Check(!InlineReceiverCompatibility.IsAssignable(text.Sig,new ByRefSig(text.Sig),Same,(_,p)=>p),"reject reference byref as object receiver");
number.BaseType=real.Sig;
Check(!Is(real,number.Sig),"value receiver must be exact, never through base");
Console.WriteLine("INLINE_RECEIVER_TYPE_SMOKE_PASS positive=8 negative=8 generic_instantiation=1");
