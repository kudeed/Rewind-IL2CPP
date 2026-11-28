using System.Reflection;
using System.Security.Cryptography;
using System.Text.Json;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Model;

internal static class MdMutationProbe
{
    private static Node At(Function fn, ulong address, Op op) =>
        fn.Blocks.SelectMany(b => b.Nodes).Single(n => !n.Dead && n.Addr == address && n.Op == op);
    private static Node Constant(Function fn, long value, VT type = VT.I64)
    {
        Node node = fn.NewNode(Op.Const, type, null); node.Imm = value; return node;
    }
    private static void RemoveGuard(Function fn, ulong address)
    {
        Node branch = At(fn, address, Op.Branch); Block block = branch.Block!;
        block.Succs[0].Preds.Remove(block); block.Succs.RemoveAt(0); branch.Op = Op.Jump; branch.In = [];
    }
    private static void Argument(Node call, int register, Node value)
    {
        var info = (CallInfo)call.Aux!;
        int i = info.Slots.FindIndex(s => s.Kind == ArgSlotKind.IntReg && s.Index == register);
        if (i < 0) throw new Exception("missing register"); call.In[i] = value;
    }
    public static void Run(Il2CppModel model, ProgramAnalysis program, MethodPipeline pipeline, string dest)
    {
        Directory.CreateDirectory(dest);
        var tests = new List<(string Name, uint Token, Action<Function>? Change, string Required)>
        {
            ("positive-scan",0x60018F5,null,""),
            ("positive-corners",0x6001BB0,null,""),
            ("positive-occupy",0x60018FA,null,""),
            ("corner-row-bounds-removed",0x6001BB0,fn=>RemoveGuard(fn,0x259A5AC),"[,]"),
            ("corner-row-bounds-reversed",0x6001BB0,fn=>At(fn,0x259A5AC,Op.Branch).In[0].Op=Op.CmpNe,"[,]"),
            ("corner-bounds-width-mismatch",0x6001BB0,fn=>At(fn,0x259A5AC,Op.Branch).In[0].In[1]=Constant(fn,0,VT.I64),"[,]"),
            ("corner-column-bounds-removed",0x6001BB0,fn=>RemoveGuard(fn,0x259A5B4),"[,]"),
            ("corner-column-bounds-reversed",0x6001BB0,fn=>At(fn,0x259A5B4,Op.Branch).In[0].Op=Op.CmpNe,"[,]"),
            ("corner-stride-from-different-array",0x6001BB0,fn=>{
                Node read=At(fn,0x259A600,Op.Load),oldBounds=At(fn,0x259A5A4,Op.Load);
                Node address=fn.NewNode(Op.Add,VT.I64,read.Block,oldBounds,Constant(fn,16));
                read.Block!.Nodes.Insert(read.Block.Nodes.IndexOf(read),address);read.In[0]=address;
            },"[,]"),
            ("corner-reference-stride-four",0x6001BB0,fn=>{
                Node read=At(fn,0x259A670,Op.Load);
                Node shifted=read.Block!.Nodes.Single(n=>n.Op==Op.Shl&&n.In[1].IsConstValue(3));
                shifted.In[1]=Constant(fn,2);
            },"[,]"),
            ("corner-row-unchecked-high-word",0x6001BB0,fn=>{
                Node read=At(fn,0x259A618,Op.Load),mul=read.Block!.Nodes.Single(n=>n.Op==Op.Mul);
                Node wide=fn.NewNode(Op.Add,VT.I64,read.Block,mul.In[1],Constant(fn,0x100000000));
                read.Block.Nodes.Insert(read.Block.Nodes.IndexOf(mul),wide);mul.In[1]=wide;
            },"[,]"),
            ("corner-null-check-delayed-past-call",0x6001BB0,fn=>{
                Node bounds=At(fn,0x259A5A4,Op.Load);Block block=bounds.Block!;
                Node call=fn.NewNode(Op.Call,VT.None,block);call.Aux=new CallInfo{Target=0x12345678};
                block.Nodes.Insert(block.Nodes.IndexOf(bounds)+1,call);
            },"[,]"),
            ("scan-counter-start-high-word",0x60018F5,fn=>{
                Node phi=fn.Blocks.Single(b=>b.Start==0x257D8E4).Phis.Single(n=>n.Type==VT.I64&&n.In.Any(v=>v.IsConstValue(0)));
                phi.In[Array.FindIndex(phi.In,n=>n.IsConstValue(0))]=Constant(fn,0x100000000);
            },"[,]"),
            ("scan-counter-step-high-word",0x60018F5,fn=>{
                Node phi=fn.Blocks.Single(b=>b.Start==0x257D8E4).Phis.Single(n=>n.Type==VT.I64&&n.In.Any(v=>v.IsConstValue(0)));
                Node increment=phi.In.Single(n=>n.Op==Op.Add);increment.In[1]=Constant(fn,0x100000001);
            },"[,]"),
            ("getter-row-unchecked-high-word",0x60018FA,fn=>{
                Node call=At(fn,0x257C9FC,Op.Call);var info=(CallInfo)call.Aux!;Node row=call.In[info.Slots.FindIndex(s=>s.Kind==ArgSlotKind.IntReg&&s.Index==1)];
                Node wide=fn.NewNode(Op.Add,VT.I64,call.Block,row,Constant(fn,0x100000000));
                call.Block!.Nodes.Insert(call.Block.Nodes.IndexOf(call),wide);Argument(call,1,wide);
            },"RectangularArrayGetAt"),
            ("getter-column-shift-only31",0x60018FA,fn=>{
                Node shift=fn.Blocks.SelectMany(b=>b.Nodes).Single(n=>n.Op==Op.ShrU&&n.In[1].IsConstValue(32));
                shift.In[1]=Constant(fn,31);
            },"RectangularArrayGetAt")
        };
        var build=typeof(MethodPipeline).GetMethod("Build",BindingFlags.Instance|BindingFlags.NonPublic)!;
        var forget=typeof(MethodPipeline).GetMethod("ForgetOpen",BindingFlags.Instance|BindingFlags.NonPublic)!;
        var rows=new List<object>();int positive=0,negative=0;
        foreach(var test in tests)
        {
            var method=model.Methods.Single(m=>m.DeclaringType.Assembly.Name=="Assembly-CSharp"&&m.Token==test.Token);
            forget.Invoke(pipeline,null);
            var lifted=pipeline.Lift(method,[],[],method.Address);string original=lifted.Function.Dump();test.Change?.Invoke(lifted.Function);
            string changed=lifted.Function.Dump();var h=(HMethod)build.Invoke(pipeline,[lifted])!;
            bool pass=test.Change==null?h.Problems.Count==0&&!HirPrinter.Print(h).Contains("__undefined"):
                h.Problems.Count>0&&h.Problems.Any(p=>p.Contains(test.Required,StringComparison.Ordinal));
            rows.Add(new{name=test.Name,token="0x"+test.Token.ToString("X"),pass,positive=test.Change==null,problems=h.Problems.Distinct().ToArray(),
                before_sha256=Convert.ToHexString(SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(original))).ToLowerInvariant(),
                after_sha256=Convert.ToHexString(SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(changed))).ToLowerInvariant()});
            File.WriteAllText(dest+"/"+test.Name+".hir.txt",HirPrinter.Print(h));Console.WriteLine(test.Name+" pass="+pass);
            if(test.Change==null)positive++;else negative++;
            if(!pass){File.WriteAllText(dest+"/mutation-proof.json",JsonSerializer.Serialize(rows,new JsonSerializerOptions{WriteIndented=true}));throw new Exception("MD mutation failed "+test.Name);}
        }
        forget.Invoke(pipeline,null);
        File.WriteAllText(dest+"/mutation-proof.json",JsonSerializer.Serialize(new{pass=true,positive,negative,tests=rows},new JsonSerializerOptions{WriteIndented=true}));
        Console.WriteLine($"MD_MUTATION_PASS positive={positive} negative={negative}");
    }
}
