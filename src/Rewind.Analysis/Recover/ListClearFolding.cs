using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>Recover the reference-element BCL List.Clear inlined tail.
/// The pre-mutation count, receiver and array must belong to the same closed
/// List, and the fast empty and Array.Clear branches must have the same exit.</summary>
internal static class ListClearFolding
{
    private static bool Local(HExpr? e,HVar v)=>e is HLocal l&&l.Variable==v;
    private static bool Number(HExpr? e,int n)=>e is HConst c&&(c.Value is int i&&i==n||c.Value is long l&&l==n);
    private static bool Int(TypeSig? t)=>t is PrimitiveSig{Element:Il2CppTypeEnum.I4};
    private static bool PlainInt(HExpr e)=>e is HLocal l&&Int(l.Variable.Type)&&!l.Variable.AddressTaken||e is HConst{Value:int};
    private static bool Edge(HStmt s,HBlock b)=>s switch
    {
        HJump j=>j.Target==b,
        HBranch c=>c.WhenTrue==b||c.WhenFalse==b,
        HSwitch sw=>sw.Default==b||sw.Targets.Contains(b),
        _=>false
    };

    internal static bool TryFold(HMethod h,SigFactory sigs,HBlock b)
    {
        if(h.TryRegions.Count!=0||h.Blocks.Any(x=>x.Scope!=-1)||b.Statements.Count!=4||
           b.Statements[0] is not HAssign{Target:HLocal versionLocal,Value:HField{Object:HLocal list} prior}||
           b.Statements[1] is not HAssign{Target:HField size,Value:var zero}||
           b.Statements[2] is not HAssign{Target:HField version,Value:HBinary{Op:HBinaryOp.Add,Left:HLocal oldVersion,Right:var one}}||
           b.Statements[3] is not HBranch{Condition:HCompare{Op:HCompareOp.Lt,Left:HLocal count,Right:var threshold}} branch||
           list.Variable.Type is not GenericInstSig g||g.Definition.FullName!="System.Collections.Generic.List"||
           g.Definition.Assembly.Name is not ("mscorlib" or "System.Private.CoreLib")||g.Arguments.Length!=1||
           g.Arguments[0].IsValueType||g.Arguments[0].ContainsGenericParameter||
           g.Arguments[0] is not (TypeDefSig or SzArraySig or GenericInstSig or PrimitiveSig{Element:Il2CppTypeEnum.Object or Il2CppTypeEnum.String})||
           list.Variable.AddressTaken||versionLocal.Variable.AddressTaken||count.Variable.AddressTaken||
           !Int(versionLocal.Variable.Type)||!Int(count.Variable.Type)||
           count.Variable==versionLocal.Variable||!Local(oldVersion,versionLocal.Variable)||
           !Number(zero,0)||!Number(one,1)||!Number(threshold,1))return false;
        bool Field(HField f,string name)=>f.Field.Name==name&&!f.Field.IsStatic&&
            f.Field.DeclaringType==g.Definition&&Local(f.Object,list.Variable)&&f.DeclaringType?.Key==g.Key;
        if(!Field(prior,"_version")||!Field(version,"_version")||prior.Field!=version.Field||
           !Field(size,"_size")||!Int(size.Field.Type)||!Int(prior.Field.Type))return false;
        HBlock empty=branch.WhenTrue,clear=branch.WhenFalse;
        if(empty==b||clear==b||empty==clear||clear==h.Blocks[0]||
           !h.Blocks.Contains(clear)||!h.Blocks.Contains(empty)||
           clear.Statements is not [HEval{Expression:HCall call},var exit]||
           call.Method.Name!="Clear"||call.Method.DeclaringType.FullName!="System.Array"||
           call.Method.DeclaringType.Assembly.Name!=g.Definition.Assembly.Name||
           !call.Method.IsStatic||call.This!=null||call.Method.GenericParameters.Length!=0||
           !call.Method.ReturnType.IsVoid||call.Method.Parameters.Length!=3||
           call.Method.Parameters[0].Type.Definition!=call.Method.DeclaringType||
           !Int(call.Method.Parameters[1].Type)||!Int(call.Method.Parameters[2].Type)||
           call.Arguments is not [HField items,var start,HLocal len]||
           !Field(items,"_items")||items.Field.Type is not SzArraySig||
           sigs.Substitute(items.Field.Type,g.Arguments,[]).Key!=sigs.SzArray(g.Arguments[0]).Key||
           !Number(start,0)||!Local(len,count.Variable))return false;
        if(!(exit is HJump j&&j.Target==empty)&&!(exit is HReturn{Value:null}&&h.Method.ReturnType.IsVoid&&empty.Statements is [HReturn{Value:null}]))return false;
        // The saved count must have been read immediately before the sole
        // predecessor's pure branch/jump. No other incoming edge, field write
        // or callback may invalidate the snapshot before the inlined clear.
        var predecessors=h.Blocks.Where(x=>x.Statements.Any(s=>Edge(s,b))).ToArray();
        if(b==h.Blocks[0]||predecessors.Length!=1)return false;
        var p=predecessors[0];
        if(p.Statements.Count<2||p.Statements[^2] is not HAssign{Target:HLocal read,Value:var value}||
           read.Variable!=count.Variable||!Edge(p.Statements[^1],b))return false;
        bool CountRead(HExpr v)=>v is HField f&&Field(f,"_size")||v is HCall c&&
          c.Method.Name=="get_Count"&&c.Method.DeclaringType==g.Definition&&!c.Method.IsStatic&&
          c.DeclaringType?.Key==g.Key&&Local(c.This,list.Variable)&&c.Arguments.Length==0&&Int(c.Method.ReturnType);
        if(!CountRead(value))return false;
        if(p.Statements[^1] is HBranch pb)
        {
            if(pb.WhenTrue==b&&pb.WhenFalse==b||pb.Condition is not HCompare cmp||!PlainInt(cmp.Left)||!PlainInt(cmp.Right))return false;
        }
        else if(p.Statements[^1] is not HJump)return false;
        foreach(var x in h.Blocks)
        foreach(var s in x.Statements)
        {
            if(x!=b&&Edge(s,clear))return false;
            if(x!=b&&ConstructorFolding.Mentions(s,versionLocal.Variable))return false;
        }
        var methods=g.Definition.Methods.Where(m=>m.Name=="Clear"&&!m.IsStatic&&m.GenericParameters.Length==0&&
            m.ReturnType.IsVoid&&m.Parameters.Length==0&&(m.Flags&MethodDef.AccessMask)==6).ToArray();
        if(methods.Length!=1)return false;
        b.Statements=[new HEval(new HCall{Method=methods[0],DeclaringType=g,This=list,Type=methods[0].ReturnType}){Address=branch.Address},
            new HJump(empty){Address=branch.Address}];
        h.Blocks.Remove(clear);h.Locals.Remove(versionLocal.Variable);
        h.Notes.Add($"public List.Clear restored from exact reference-element clear tail at 0x{branch.Address:X}");
        return true;
    }

    internal static void Run(HMethod h,SigFactory sigs)
    {
        if(Environment.GetEnvironmentVariable("REWIND_NO_LIST_CLEAR_FOLDING")!=null)return;
        foreach(var b in h.Blocks.ToArray())if(h.Blocks.Contains(b))TryFold(h,sigs,b);
    }
}
