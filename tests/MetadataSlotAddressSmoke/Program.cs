using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;

static void Check(bool ok,string name){if(!ok)throw new Exception(name);}
static Node Constant(ulong n)=>new(){Op=Op.Const,Type=VT.I64,Imm=unchecked((long)n)};
static Node Add(ulong a=0x1000,ulong b=0x48)=>new(){Op=Op.Add,Type=VT.I64,In=[Constant(a),Constant(b)]};
var known=new HashSet<ulong>{0x1048,0x1068,0x1008};int positive=0,negative=0;
void Accept(string name,Node n,ulong expected){Check(MetadataSlotAddress.TryConstantAdd(n,known.Contains,out var slot)&&slot==expected,name);Check(n.Op==Op.Add&&!n.Dead&&n.In.All(x=>x.Op==Op.Const&&!x.Dead),name+" pure matcher");positive++;}
void Reject(string name,Action<Node> mutate,Func<ulong,bool>? predicate=null){var n=Add();mutate(n);Check(!MetadataSlotAddress.TryConstantAdd(n,predicate??known.Contains,out var slot)&&slot==0,name);negative++;}
Accept("constant table offset",Add(),0x1048);
Accept("second exact slot",Add(0x1000,0x68),0x1068);
Accept("commuted constant inputs",Add(0x48,0x1000),0x1048);
Accept("negative native displacement",Add(0x1068,unchecked((ulong)-32L)),0x1048);
Accept("native 64-bit wrap",Add(ulong.MaxValue-7,0x1010),0x1008);
Reject("unproved writable global",n=>n.In[1]=Constant(0x50));
Reject("same final value through register",n=>n.In[0].Op=Op.Param);
Reject("same final value through load",n=>n.In[0].Op=Op.Load);
Reject("phi operand",n=>n.In[0]=new Node{Op=Op.Phi,Type=VT.I64,In=[Constant(0x1000),Constant(0x1000)]});
Reject("nested arithmetic",n=>n.In[0]=Add(0x1000,0));
Reject("cycle",n=>n.In[0]=n);
Reject("non-add",n=>n.Op=Op.Sub);
Reject("multiplication",n=>n.Op=Op.Mul);
Reject("narrow address",n=>n.Type=VT.I32);
Reject("narrow left operand",n=>n.In[0].Type=VT.I32);
Reject("narrow right operand",n=>n.In[1].Type=VT.I32);
Reject("dead address",n=>n.Dead=true);
Reject("dead left",n=>n.In[0].Dead=true);
Reject("dead right",n=>n.In[1].Dead=true);
Reject("unknown operation annotation",n=>n.Aux=new object());
Reject("unknown constant annotation",n=>n.In[0].Aux=new object());
Reject("malformed zero inputs",n=>n.In=[]);
Reject("malformed one input",n=>n.In=[Constant(0x1048)]);
Reject("malformed extra input",n=>n.In=[Constant(0x1000),Constant(0x48),Constant(0)]);
Reject("malformed constant input",n=>n.In[0].In=[Constant(0)]);
Reject("unaligned known address",n=>n.In[1]=Constant(0x49),_=>true);
Reject("null address",n=>n.In=[Constant(0),Constant(0)],_=>true);
var repeated=Add();Check(MetadataSlotAddress.TryConstantAdd(repeated,known.Contains,out _),"first known table");known.Remove(0x1048);Check(!MetadataSlotAddress.TryConstantAdd(repeated,known.Contains,out _),"unknown table not cached as known");negative++;
Console.WriteLine($"MetadataSlotAddressSmoke passed: {positive} positive, {negative} negative");
