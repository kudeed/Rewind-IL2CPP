using System.Reflection;
using System.Security.Cryptography;
using System.Text.Json;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Model;

internal static class ListMutationProbe
{
    private static Node At(Function fn, ulong address, Op op, int which = 0) =>
        fn.Blocks.SelectMany(b => b.Nodes).Where(n => !n.Dead && n.Addr == address && n.Op == op).ElementAt(which);
    private static Node Constant(Function fn, long value, VT type = VT.I64)
    {
        Node node = fn.NewNode(Op.Const, type, null);
        node.Imm = value;
        return node;
    }
    private static void Argument(Node call, int position, Node value)
    {
        var info = (CallInfo)call.Aux!;
        int input = info.Slots.FindIndex(s => s.Kind == ArgSlotKind.IntReg && s.Index == position);
        if (input < 0) throw new Exception("missing argument");
        call.In[input] = value;
    }
    private static void InsertWrite(Function fn, ulong readAddress, int bytes)
    {
        Node load = At(fn, readAddress, Op.Load);
        Block block = load.Block!;
        Node store = fn.NewNode(Op.Store, VT.None, block, load.In[0], Constant(fn, 0, bytes == 8 ? VT.I64 : VT.I32));
        block.Nodes.Insert(block.Nodes.IndexOf(load), store);
    }

    private static void RemoveGuard(Function fn, ulong address)
    {
        Node branch=At(fn,address,Op.Branch);Block block=branch.Block!;
        block.Succs[0].Preds.Remove(block);block.Succs.RemoveAt(0);
        branch.Op=Op.Jump;branch.In=[];
    }

    public static void Run(Il2CppModel model, ProgramAnalysis program, MethodPipeline pipeline, string dest)
    {
        Directory.CreateDirectory(dest);
        var tests = new List<(string Name, uint Token, Action<Function>? Change, string Required)>
        {
            ("positive-list", 0x60007F3, null, ""),
            ("positive-remove", 0x60007F2, null, ""),
            ("positive-array", 0x60007F4, null, ""),
            ("positive-shuffle", 0x60007F6, null, ""),
            ("different-invoker-code", 0x60007F3, fn => Argument(At(fn, 0x2BBE4B0, Op.Call), 0, At(fn, 0x2BBE470, Op.Load)), "indirect call"),
            ("different-method-info", 0x60007F3, fn => Argument(At(fn, 0x2BBE4B0, Op.Call), 1, At(fn, 0x2BBE468, Op.Load)), "indirect call"),
            ("wrong-invoker-field", 0x60007F3, fn => At(fn, 0x2BBE4A8, Op.Load).In[0].In[1] = Constant(fn, 24), "indirect call"),
            ("nonframe-argument-table", 0x60007F3, fn => Argument(At(fn, 0x2BBE4B0, Op.Call), 3, Constant(fn, 0)), "indirect call"),
            ("partial-table-cell", 0x60007F3, fn => {
                Node store=At(fn,0x2BBE4AC,Op.Store);Node narrow=fn.NewNode(Op.Trunc,VT.I32,store.Block,store.In[1]);
                store.Block!.Nodes.Insert(store.Block.Nodes.IndexOf(store),narrow);store.In[1]=narrow;
            }, "indirect call"),
            ("return-cell-mismatch", 0x60007F3, fn => At(fn,0x2BBE4AC,Op.Store,1).In[1]=Constant(fn,0), "indirect call"),
            ("argument-cell-missing", 0x60007F3, fn => At(fn,0x2BBE48C,Op.Store).Dead=true, "indirect call"),
            ("rounded-allocation-size-wrong", 0x60007F3, fn => fn.Blocks.SelectMany(b=>b.Nodes).Single(n=>n.Op==Op.And&&n.In[1].IsConstValue(0x1FFFFFFF0)).In[1]=Constant(fn,0x1FFFFFFE0), ""),
            ("rounding-bias-wrong", 0x60007F3, fn => fn.Blocks.SelectMany(b=>b.Nodes).Single(n=>n.Op==Op.Add&&n.In[1].IsConstValue(15)).In[1]=Constant(fn,14), ""),
            ("partial-runtime-copy", 0x60007F3, fn => Argument(At(fn,0x2BBE4C0,Op.Call),2,Constant(fn,1)), ""),
            ("different-size-field", 0x60007F3, fn => At(fn,0x2BBE44C,Op.Load).In[0].In[1]=Constant(fn,0x104), ""),
            ("marshal-wrong-predicate", 0x60007F2, fn => fn.Blocks.SelectMany(b=>b.Nodes).Single(n=>n.Op==Op.CmpLtS).Op=Op.CmpLeS, "indirect call"),
            ("marshal-wrong-class-flag", 0x60007F2, fn => At(fn,0x2BBE710,Op.Load).In[0].In[1]=Constant(fn,0x2C), "indirect call"),
            ("marshal-partial-reference", 0x60007F2, fn => At(fn,0x2BBE71C,Op.Load).Type=VT.I32, "indirect call"),
            ("marshal-effectful-reference-branch", 0x60007F2, fn => {
                Node load=At(fn,0x2BBE71C,Op.Load);Node call=fn.NewNode(Op.Call,VT.None,load.Block);call.Aux=new CallInfo{Target=0x12345678};
                load.Block!.Nodes.Insert(load.Block.Nodes.IndexOf(load),call);
            }, "indirect call"),
            ("canary-initial-value-changed", 0x60007F3, fn => At(fn,0x2BBE430,Op.Store).In[1]=Constant(fn,0x5354414B47554153), "StackCheckFail"),
            ("canary-initial-write-missing", 0x60007F3, fn => At(fn,0x2BBE430,Op.Store).Dead=true, "StackCheckFail"),
            ("canary-overwrite", 0x60007F3, fn => InsertWrite(fn,0x2BBE4F0,8), "StackCheckFail"),
            ("canary-partial-overwrite", 0x60007F3, fn => InsertWrite(fn,0x2BBE4F0,4), "StackCheckFail"),
            ("canary-unknown-call", 0x60007F3, fn => {
                Node load=At(fn,0x2BBE4F0,Op.Load);Node call=fn.NewNode(Op.Call,VT.None,load.Block);call.Aux=new CallInfo{Target=0x12345678};
                load.Block!.Nodes.Insert(load.Block.Nodes.IndexOf(load),call);
            }, "StackCheckFail"),
            ("canary-unproven-dynamic-write", 0x60007F2, fn => Argument(At(fn,0x2BBE60C,Op.Call),2,Constant(fn,64)), "StackCheckFail"),
            ("shuffle-loop-canary-overwrite", 0x60007F6, fn => {
                Node saved=At(fn,0x2BBEC54,Op.Store),call=At(fn,0x2BBECD4,Op.Call);
                Node store=fn.NewNode(Op.Store,VT.None,call.Block,saved.In[0],Constant(fn,0));
                call.Block!.Nodes.Insert(call.Block.Nodes.IndexOf(call),store);
            }, "StackCheckFail"),
            ("shuffle-loop-partial-canary", 0x60007F6, fn => {
                Node saved=At(fn,0x2BBEC54,Op.Store),call=At(fn,0x2BBECD4,Op.Call);
                Node store=fn.NewNode(Op.Store,VT.None,call.Block,saved.In[0],Constant(fn,0,VT.I32));
                call.Block!.Nodes.Insert(call.Block.Nodes.IndexOf(call),store);
            }, "StackCheckFail"),
            ("shuffle-unknown-rng-call", 0x60007F6, fn => ((CallInfo)At(fn,0x2BBECE4,Op.Call).Aux!).Target=0x12345678, "StackCheckFail"),
            ("shuffle-frame-passed-as-scalar", 0x60007F6, fn => Argument(At(fn,0x2BBECE4,Op.Call),0,fn.Params[fn.Regs.StackPointer]), "StackCheckFail"),
            ("shuffle-wrong-array-stride", 0x60007F6, fn => At(fn,0x2BBED0C,Op.Load).In[0].In[1]=Constant(fn,0x100), "StackCheckFail"),
            ("shuffle-oversized-array-write", 0x60007F6, fn => Argument(At(fn,0x2BBED64,Op.Call),2,Constant(fn,64)), "StackCheckFail"),
            ("shuffle-first-write-bounds-removed", 0x60007F6, fn => RemoveGuard(fn,0x2BBECFC), "StackCheckFail"),
            ("shuffle-first-write-bounds-reversed", 0x60007F6, fn => {Node cmp=At(fn,0x2BBECFC,Op.Branch).In[0];cmp.Op=Op.CmpLtU;(cmp.In[0],cmp.In[1])=(cmp.In[1],cmp.In[0]);}, "StackCheckFail"),
            ("shuffle-last-write-bounds-removed", 0x60007F6, fn => RemoveGuard(fn,0x2BBED48), "StackCheckFail"),
            ("shuffle-last-write-bounds-reversed", 0x60007F6, fn => {Node cmp=At(fn,0x2BBED48,Op.Branch).In[0];cmp.Op=Op.CmpLtU;(cmp.In[0],cmp.In[1])=(cmp.In[1],cmp.In[0]);}, "StackCheckFail"),
            ("shuffle-frame-escape-before-canary-call", 0x60007F6, fn => {
                Node saved=At(fn,0x2BBEC54,Op.Store);Block block=saved.Block!;
                Node call=fn.NewNode(Op.Call,VT.None,block,saved.In[0]);
                call.Aux=new CallInfo{Target=0x12345678,Slots=[new ArgSlot(ArgSlotKind.IntReg,0)]};
                block.Nodes.Insert(block.Nodes.IndexOf(saved),call);
            }, "StackCheckFail"),
            ("shuffle-frame-escape-before-canary-store", 0x60007F6, fn => {
                Node saved=At(fn,0x2BBEC54,Op.Store);Block block=saved.Block!;
                Node store=fn.NewNode(Op.Store,VT.None,block,Constant(fn,0x10000000),saved.In[0]);
                block.Nodes.Insert(block.Nodes.IndexOf(saved),store);
            }, "StackCheckFail"),
            ("shuffle-canary-read-backedge", 0x60007F6, fn => {
                Node read=At(fn,0x2BBEDCC,Op.Load);Block block=read.Block!;
                Node store=fn.NewNode(Op.Store,VT.None,block,read.In[0],Constant(fn,0));
                block.Nodes.Insert(block.Nodes.IndexOf(read)+1,store);
                block.Succs[1].Preds.Remove(block);block.Succs[1]=block;block.Preds.Add(block);
            }, "StackCheckFail")
        };
        var ownField=typeof(HirBuilder).GetField("OwnParameters",BindingFlags.Static|BindingFlags.NonPublic)!;
        var build=typeof(MethodPipeline).GetMethod("Build",BindingFlags.Instance|BindingFlags.NonPublic)!;
        var forget=typeof(MethodPipeline).GetMethod("ForgetOpen",BindingFlags.Instance|BindingFlags.NonPublic)!;
        var rows=new List<object>();int positive=0,negative=0;
        foreach(var test in tests)
        {
            var method=model.Methods.Single(m=>m.DeclaringType.Assembly.Name=="Assembly-CSharp"&&m.Token==test.Token);
            ulong address=test.Token==0x60007F2?0x2BBE588UL:test.Token==0x60007F3?0x2BBE404UL:test.Token==0x60007F6?0x2BBEC28UL:0x2BBE504UL;
            TypeSig[] ma=method.GenericParameters.Select(g=>(TypeSig)model.Sigs.GenericParam(g)).ToArray();
            var own=method.GenericParameters.ToHashSet();ownField.SetValue(null,own);program.Layouts.ReferenceParameters=own;forget.Invoke(pipeline,null);
            var lifted=pipeline.Lift(method,[],ma,address);string original=lifted.Function.Dump();test.Change?.Invoke(lifted.Function);
            string mutated=lifted.Function.Dump();
            HMethod h=(HMethod)build.Invoke(pipeline,[lifted])!;
            bool ok=test.Change==null?h.Problems.Count==0&&!HirPrinter.Print(h).Contains("__undefined"):h.Problems.Count>0&&(test.Required.Length==0||h.Problems.Any(p=>p.Contains(test.Required,StringComparison.Ordinal)));
            rows.Add(new{name=test.Name,token="0x"+test.Token.ToString("X"),pass=ok,positive=test.Change==null,required=test.Required,problems=h.Problems.Distinct().ToArray(),notes=h.Notes,
                before_sha256=Convert.ToHexString(SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(original))).ToLowerInvariant(),
                after_sha256=Convert.ToHexString(SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(mutated))).ToLowerInvariant()});
            File.WriteAllText(dest+"/"+test.Name+".hir.txt",HirPrinter.Print(h));
            Console.WriteLine(test.Name+" pass="+ok+" problems="+h.Problems.Distinct().Count());
            if(test.Change==null)positive++;else negative++;
            if(!ok){File.WriteAllText(dest+"/mutation-proof.json",JsonSerializer.Serialize(rows,new JsonSerializerOptions{WriteIndented=true}));throw new Exception("mutation gate failed "+test.Name);}
        }
        ownField.SetValue(null,null);program.Layouts.ReferenceParameters=null;forget.Invoke(pipeline,null);
        File.WriteAllText(dest+"/mutation-proof.json",JsonSerializer.Serialize(new{pass=true,positive,negative,tests=rows},new JsonSerializerOptions{WriteIndented=true}));
        Console.WriteLine($"LIST_MUTATION_PASS positive={positive} negative={negative}");
    }
}
