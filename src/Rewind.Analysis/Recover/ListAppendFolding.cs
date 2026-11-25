using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>Restore the public List&lt;T&gt;.Add call from the exact inlined
/// version/update/capacity/resize diamond. A terminal void diamond only.
/// Never leave an inaccessible BCL private field in this matched pattern.</summary>
internal static class ListAppendFolding
{
    internal static bool TryFold(HMethod method, SigFactory sigs, HBlock block)
    {
        if (method.Method.ReturnType.IsVoid == false || method.TryRegions.Count != 0 ||
            method.Blocks.Any(b => b.Scope != -1) || block.Statements.Count < 4) return false;
        var ss = block.Statements;
        int start = ss.Count - 4;
        if (ss[start] is not HAssign { Target: HLocal array,
                Value: HField { Object: HLocal list, Field.Name: "_items" } items } ||
            list.Variable.Type is not GenericInstSig g || g.Definition.FullName != "System.Collections.Generic.List" ||
            g.Definition.Assembly.Name is not ("mscorlib" or "System.Private.CoreLib") ||
            g.Arguments.Length != 1 || g.Arguments[0].IsValueType || g.Arguments[0].ContainsGenericParameter ||
            array.Variable.AddressTaken || list.Variable.AddressTaken ||
            array.Variable.Type is not SzArraySig arr || arr.ElementType.Key != g.Arguments[0].Key ||
            ss[start+1] is not HAssign {Target:HField version,Value:HBinary {Op:HBinaryOp.Add,Left:HField previous,Right:HConst one}} ||
            ss[start+2] is not HAssign {Target:HLocal count,Value:var readCount} ||
            count.Variable.AddressTaken ||
            ss[start+3] is not HBranch {Condition:HCompare {Op:HCompareOp.LeUn,Left:HArrayLength len,Right:HLocal compareCount}} branch)
            return false;
        bool Local(HExpr? e,HVar v)=>e is HLocal l&&ReferenceEquals(l.Variable,v);
        bool Field(HField field,string name)=>field.Field.Name==name && !field.Field.IsStatic &&
            ReferenceEquals(field.Field.DeclaringType,g.Definition)&&Local(field.Object,list.Variable);
        bool One(HConst c)=>c.Value is int x&&x==1 || c.Value is long y&&y==1;
        if (!Field(items,"_items") || !Field(version,"_version") || !Field(previous,"_version") ||
            !ReferenceEquals(version.Field,previous.Field) || !One(one) ||
            !Local(len.Array,array.Variable)||!ReferenceEquals(compareCount.Variable,count.Variable))return false;
        bool CountRead(HExpr e)=> e is HField f&&Field(f,"_size") ||
            e is HCall c&&c.Method.Name=="get_Count"&&ReferenceEquals(c.Method.DeclaringType,g.Definition)&&
            Local(c.This,list.Variable)&&c.Arguments.Length==0;
        if(!CountRead(readCount))return false;
        HBlock slow=branch.WhenTrue,fast=branch.WhenFalse;
        if(slow==fast||slow==block||fast==block||slow==method.Blocks[0]||fast==method.Blocks[0]||
            !method.Blocks.Contains(slow)||!method.Blocks.Contains(fast))return false;
        if(fast.Statements is not [HAssign {Target:HField size,Value:HBinary {Op:HBinaryOp.Add,Left:HLocal sz,Right:HConst increment}},
                HAssign {Target:HElement dest,Value:var item},HReturn {Value:null}] ||
            !Field(size,"_size")||!ReferenceEquals(sz.Variable,count.Variable)||!One(increment)||
            !Local(dest.Array,array.Variable)||!Local(dest.Index,count.Variable)||
            slow.Statements is not [HEval {Expression:HCall resize},HReturn {Value:null}] ||
            resize.Method.Name!="AddWithResize"||!ReferenceEquals(resize.Method.DeclaringType,g.Definition)||
            resize.Method.IsStatic||!Local(resize.This,list.Variable)||resize.Arguments.Length!=1||
            !HirCleanup.Same(item,resize.Arguments[0])||
            item is not (HArg or HLocal or HConst)||item.Type?.Key!=g.Arguments[0].Key||
            ConstructorFolding.Mentions(item,array.Variable)||ConstructorFolding.Mentions(item,count.Variable))
            return false;
        // No other edge or use of the private-array/count temps is allowed.
        foreach(var b in method.Blocks)
        foreach(var s in b.Statements)
        {
            if(ReferenceEquals(b,block)&&ReferenceEquals(s,branch))continue;
            if(s is HJump j&&(j.Target==slow||j.Target==fast)||
               s is HBranch br&&(br.WhenTrue==slow||br.WhenFalse==slow||br.WhenTrue==fast||br.WhenFalse==fast)||
               s is HSwitch sw&&(sw.Default==slow||sw.Default==fast||sw.Targets.Contains(slow)||sw.Targets.Contains(fast)))return false;
            if(b==slow||b==fast||b==block&&ss.IndexOf(s)>=start)continue;
            if(ConstructorFolding.Mentions(s,array.Variable)||ConstructorFolding.Mentions(s,count.Variable))return false;
        }
        var add=g.Definition.Methods.Where(m=>m.Name=="Add"&&!m.IsStatic&&m.GenericParameters.Length==0&&m.ReturnType.IsVoid&&m.Parameters.Length==1&&
            sigs.Substitute(m.Parameters[0].Type,g.Arguments,[]).Key==g.Arguments[0].Key).ToArray();
        if(add.Length!=1)return false;
        ss.RemoveRange(start,4);
        ss.Add(new HEval(new HCall{Method=add[0],DeclaringType=g,This=list,Arguments=[item],Type=add[0].ReturnType}){Address=branch.Address});
        ss.Add(new HReturn(null){Address=branch.Address});
        method.Blocks.Remove(fast);method.Blocks.Remove(slow);
        method.Locals.Remove(array.Variable);method.Locals.Remove(count.Variable);
        method.Notes.Add("public List.Add restored from complete inlined terminal capacity diamond");
        return true;
    }
    public static void Run(HMethod method,SigFactory sigs)
    {
        if(Environment.GetEnvironmentVariable("REWIND_NO_LIST_APPEND_FOLDING")!=null)return;
        foreach(var b in method.Blocks.ToArray())
            if(method.Blocks.Contains(b))TryFold(method,sigs,b);
    }
}
