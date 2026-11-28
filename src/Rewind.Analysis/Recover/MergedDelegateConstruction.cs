using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>Native compiler tail-merged a delegate constructor after several
/// raw allocations and pointer choices. Put construction on each predecessor
/// at its allocation site; do not construct on an already allocated object.</summary>
internal static class MergedDelegateConstruction
{
    internal static bool TryFold(HMethod method,HBlock join)
    {
        if(method.TryRegions.Count!=0||method.Blocks.Any(b=>b.Scope!=-1)||
           method.Method.IsStatic||method.Method.DeclaringType.IsValueType||
           method.Method.DeclaringType.GenericParameters.Length!=0||
           method.Blocks[0]==join||
           join.Statements.Count<2||
           join.Statements[0] is not HEval{Expression:HCall{This:HLocal obj,Arguments:[HArg{Index:-1} receiver,HLocal ptr]} ctor}||
           ctor.Method.Name!=".ctor"||ctor.Method.IsStatic||ctor.Virtual||
           ctor.DeclaringType!=null||ctor.MethodArguments.Length!=0||
           obj.Variable.AddressTaken||ptr.Variable.AddressTaken||
           obj.Variable.Type is not TypeDefSig d||!d.Definition.IsDelegate||
           d.Definition.GenericParameters.Length!=0||ctor.Method.DeclaringType!=d.Definition||
           ctor.Method.Parameters.Length!=2||ctor.Method.Parameters[0].Type is not PrimitiveSig{Element:Il2CppTypeEnum.Object}||
           ctor.Method.Parameters[1].Type is not PrimitiveSig{Element:Il2CppTypeEnum.I}||
           receiver.Type?.Definition!=method.Method.DeclaringType||
           ptr.Variable.Type is not PrimitiveSig{Element:Il2CppTypeEnum.I})return false;
        var invoke=d.Definition.Methods.Where(m=>m.Name=="Invoke"&&!m.IsStatic).ToArray();
        if(invoke.Length!=1)return false;
        var incoming=new List<HBlock>();
        foreach(var b in method.Blocks)
        foreach(var s in b.Statements)
        {
            if(s is HJump j&&j.Target==join){if(b==join||s!=b.Statements.Last())return false;incoming.Add(b);}
            if(s is HBranch br&&(br.WhenTrue==join||br.WhenFalse==join)||s is HSwitch sw&&(sw.Default==join||sw.Targets.Contains(join)))return false;
        }
        if(incoming.Count is <2 or >16||incoming.Distinct().Count()!=incoming.Count)return false;
        var sites=new List<(HBlock Block,int Index,HAssign Allocation,HAssign Copy,HAssign Pointer,HVar Local,HMethodPointer Function)>();
        var allowed=new HashSet<HStmt>{join.Statements[0]};
        foreach(var b in incoming)
        {
            var s=b.Statements;int n=s.Count;
            if(n<5||s[n-5] is not HAssign{Target:HLocal local,Value:HTypeExpr{Op:HTypeOp.Allocate} allocation} a||
               s[n-4] is not HAssign{Target:HLocal copy,Value:HLocal from} c||
               s[n-3] is not HAssign{Target:HLocal middle,Value:HLocal middleValue}||
               s[n-2] is not HAssign{Target:HLocal pointer,Value:HMethodPointer f} p||
               copy.Variable!=obj.Variable||from.Variable!=local.Variable||pointer.Variable!=ptr.Variable||
               local.Variable.AddressTaken||local.Variable.Type.Key!=d.Key||allocation.Target.Key!=d.Key||
               local.Variable==obj.Variable||local.Variable==ptr.Variable||
               middle.Variable==obj.Variable||middle.Variable==ptr.Variable||middle.Variable==local.Variable||
               middleValue.Variable==obj.Variable||middleValue.Variable==ptr.Variable||middleValue.Variable==local.Variable||
               f.VirtualOn!=null||f.DeclaringType!=null||f.MethodArguments.Length!=0||
               f.Method.IsStatic||f.Method.IsVirtual||f.Method.IsAbstract||f.Method.IsConstructor||f.Method.Address==0||
               f.Method.IsGenericDefinition||f.Method.DeclaringType!=method.Method.DeclaringType||
               f.Method.ReturnType.Key!=invoke[0].ReturnType.Key||f.Method.Parameters.Length!=invoke[0].Parameters.Length||
               !f.Method.Parameters.Zip(invoke[0].Parameters).All(z=>z.First.Type.Key==z.Second.Type.Key))return false;
            sites.Add((b,n-5,a,c,p,local.Variable,f));allowed.Add(a);allowed.Add(c);allowed.Add(p);
        }
        if(sites.Select(v=>v.Local).Distinct().Count()!=sites.Count)return false;
        // No observations/escapes of the raw objects or of the merged pointer.
        // The object merge may be consumed only in the join after its ctor.
        foreach(var b in method.Blocks)
        foreach(var s in b.Statements)
        {
            if(allowed.Contains(s))continue;
            if(ConstructorFolding.Mentions(s,ptr.Variable)||sites.Any(v=>ConstructorFolding.Mentions(s,v.Local)))return false;
            if(b!=join&&ConstructorFolding.Mentions(s,obj.Variable))return false;
            if(b==join&&s is HAssign{Target:HLocal l}&&l.Variable==obj.Variable)return false;
        }
        foreach(var v in sites)
        {
            v.Block.Statements[v.Index]=new HAssign(new HLocal(obj.Variable){Type=d},new HNewObject{
                Constructor=ctor.Method,Type=d,Arguments=[new HArg(-1){Type=receiver.Type},v.Function]}){Address=v.Allocation.Address};
            v.Block.Statements.Remove(v.Copy);v.Block.Statements.Remove(v.Pointer);
            method.Locals.Remove(v.Local);
        }
        join.Statements.RemoveAt(0);method.Locals.Remove(ptr.Variable);
        string note=$"the constructor of {d.ShortName} was inlined here; the object is allocated raw and its statements follow";
        if(!method.Blocks.SelectMany(b=>b.Statements).Any(s=>s is HAssign{Value:HTypeExpr{Op:HTypeOp.Allocate} a}&&a.Target.Key==d.Key))method.Notes.RemoveAll(n=>n==note);
        method.Notes.Add($"merged delegate construction: {sites.Count} exact instance method leaves");
        return true;
    }
    public static void Run(HMethod method)
    {
        if(Environment.GetEnvironmentVariable("REWIND_NO_MERGED_DELEGATE_CONSTRUCTION")!=null)return;
        foreach(var b in method.Blocks.ToArray())TryFold(method,b);
    }
}
