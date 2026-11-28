using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;

static void Check(bool value,string name){if(!value)throw new Exception(name);}
var sf=new SigFactory();var asm=new AssemblyModel{Name="MetadataProof"};
TypeDef Type(int index,string name){var t=new TypeDef{Index=index,Name=name,Assembly=asm};t.Sig=sf.TypeDef(t);return t;}
var a=Type(1,"A");var b=Type(2,"B");var voidType=sf.Primitive(Il2CppTypeEnum.Void);
var first=new MethodDef{Name="First",DeclaringType=a,ReturnType=voidType};
var second=new MethodDef{Name="Second",DeclaringType=a,ReturnType=voidType};
var items=new RgctxItem[]{new(RgctxKind.Class,a.Sig,null)};
var values=new Dictionary<Node,Sem>();
Node Leaf(Sem value,VT type=VT.I64){var n=new Node{Op=Op.SlotValue,Type=type};values[n]=value;return n;}
Node Phi(params Node[] input){var block=new Block();foreach(var _ in input)block.Preds.Add(new Block());var n=new Node{Op=Op.Phi,Type=input.Length==0?VT.I64:input[0].Type,Block=block,In=input};block.Phis.Add(n);return n;}
Sem? Describe(Node n,Func<Node,Sem?> recur)=>n.Op is Op.SlotValue or Op.Param?values.GetValueOrDefault(n):n.Op==Op.Load&&n.In.Length==1?recur(n.In[0]):null;
Sem? Resolve(Node phi,int width=8)=>MetadataPhiJoin.Resolve(phi,width,Describe);
int positive=0,negative=0;
void Accept(string name,Node phi,int width=8){Check(Resolve(phi,width)!=null,name);positive++;}
void Reject(string name,Node phi,int width=8){Check(Resolve(phi,width)==null,name);negative++;}
Accept("same class",Phi(Leaf(new SKlass(a.Sig)),Leaf(new SKlass(a.Sig))));
Accept("same method",Phi(Leaf(new SMethod(first,null)),Leaf(new SMethod(first,null))));
SMethod Inst(MethodDef m,TypeSig[] classes,TypeSig[] methods)=>new(m,new MethodInst{Method=m,ClassArguments=classes,MethodArguments=methods});
Accept("same generic method identity",Phi(Leaf(Inst(first,[a.Sig],[b.Sig])),Leaf(Inst(first,[a.Sig],[b.Sig]))));
Accept("same context and instantiation",Phi(Leaf(new SRgctx(items,[a.Sig],[b.Sig])),Leaf(new SRgctx(items,[a.Sig],[b.Sig]))));
Accept("nested merge",Phi(Phi(Leaf(new SKlass(a.Sig)),Leaf(new SKlass(a.Sig))),Leaf(new SKlass(a.Sig))));
Accept("projected immutable metadata",Phi(new Node{Op=Op.Load,Type=VT.I64,In=[Leaf(new SKlass(a.Sig))]},Leaf(new SKlass(a.Sig))));
Accept("32 bit metadata",Phi(Leaf(new SKlass(a.Sig),VT.I32),Leaf(new SKlass(a.Sig),VT.I32)),4);
Reject("different classes",Phi(Leaf(new SKlass(a.Sig)),Leaf(new SKlass(b.Sig))));
Reject("different methods",Phi(Leaf(new SMethod(first,null)),Leaf(new SMethod(second,null))));
Reject("different generic class args",Phi(Leaf(Inst(first,[a.Sig],[])),Leaf(Inst(first,[b.Sig],[]))));
Reject("different generic method args",Phi(Leaf(Inst(first,[],[a.Sig])),Leaf(Inst(first,[],[b.Sig]))));
Reject("different generic arity",Phi(Leaf(Inst(first,[a.Sig],[])),Leaf(Inst(first,[a.Sig,b.Sig],[]))));
Reject("definition versus instantiated method",Phi(Leaf(new SMethod(first,null)),Leaf(Inst(first,[],[]))));
Reject("inconsistent method record",Phi(Leaf(new SMethod(first,new MethodInst{Method=second})),Leaf(new SMethod(first,new MethodInst{Method=second}))));
Reject("metadata kinds differ",Phi(Leaf(new SKlass(a.Sig)),Leaf(new SMethod(first,null))));
Reject("context source differs",Phi(Leaf(new SRgctx(items,[],[])),Leaf(new SRgctx([new RgctxItem(RgctxKind.Class,a.Sig,null)],[],[]))));
Reject("context class args differ",Phi(Leaf(new SRgctx(items,[a.Sig],[])),Leaf(new SRgctx(items,[b.Sig],[]))));
Reject("context method args differ",Phi(Leaf(new SRgctx(items,[],[a.Sig])),Leaf(new SRgctx(items,[],[b.Sig]))));
Reject("empty unknown context",Phi(Leaf(new SRgctx([],[],[])),Leaf(new SRgctx([],[],[]))));
Reject("one unknown input",Phi(Leaf(new SKlass(a.Sig)),new Node{Op=Op.Undef,Type=VT.I64}));
Reject("call result unavailable",Phi(Leaf(new SKlass(a.Sig)),new Node{Op=Op.Proj,Type=VT.I64}));
Reject("integer is not class metadata",Phi(Leaf(new SKlass(a.Sig)),Leaf(new SVal(new HConst(1,sf.Primitive(Il2CppTypeEnum.I8))))));
Reject("runtime object class is not static metadata",Phi(Leaf(new SObjKlass(new Node())),Leaf(new SObjKlass(new Node()))));
var self=Phi(Leaf(new SKlass(a.Sig)),Leaf(new SKlass(a.Sig)));self.In[1]=self;Reject("self cycle",self);
var x=Phi(Leaf(new SKlass(a.Sig)),Leaf(new SKlass(a.Sig)));var y=Phi(Leaf(new SKlass(a.Sig)),x);x.In[1]=y;Reject("mutual cycle",x);
var malformed=Phi(Leaf(new SKlass(a.Sig)),Leaf(new SKlass(a.Sig)));malformed.Block!.Preds.RemoveAt(0);Reject("predecessor count mismatch",malformed);
var missing=Phi(Leaf(new SKlass(a.Sig)),Leaf(new SKlass(a.Sig)));missing.Block=null;Reject("missing block",missing);
Reject("empty phi",Phi());
Reject("not phi",Leaf(new SKlass(a.Sig)));
Reject("wrong pointer width",Phi(Leaf(new SKlass(a.Sig)),Leaf(new SKlass(a.Sig))),4);
Reject("invalid pointer width",Phi(Leaf(new SKlass(a.Sig)),Leaf(new SKlass(a.Sig))),3);
var typed=Phi(Leaf(new SKlass(a.Sig)),Leaf(new SKlass(a.Sig),VT.I32));Reject("input width mismatch",typed);
Node deep=Leaf(new SKlass(a.Sig));for(int i=0;i<66;i++)deep=Phi(Leaf(new SKlass(a.Sig)),deep);Reject("depth limit",deep);
Node Wide(int level)=>level==0?Leaf(new SKlass(a.Sig)):Phi(Wide(level-1),Wide(level-1));Reject("work limit",Wide(8));
Console.WriteLine($"METADATA_PHI_JOIN_PASS positive={positive} negative={negative}");
