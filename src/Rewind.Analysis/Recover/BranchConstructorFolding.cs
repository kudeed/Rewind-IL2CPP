using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// One allocation immediately followed by a pure scalar test, with the same constructor first in both
/// successor blocks. Capture that test once and construct at the original allocation with selected arguments.
/// No exception region, type initializer, finalizer, early publication or alias is accepted.
/// </summary>
internal static class BranchConstructorFolding
{
    internal static bool TryFold(HMethod method,HBlock block,int at,SigFactory sigs)
    {
        if(method.TryRegions.Count!=0||method.Blocks.Any(b=>b.Scope!=-1)||block.Scope!=-1||at<0||at+2!=block.Statements.Count||
           block.Statements[at] is not HAssign {Target:HLocal target,Value:HTypeExpr {Op:HTypeOp.Allocate,Operand:null} allocation} assign||
           block.Statements[^1] is not HBranch branch||target.Variable.AddressTaken||
           allocation.Target is not TypeDefSig {Definition:{IsValueType:false} definition}||
           target.Variable.Type.Key!=allocation.Target.Key||target.Type?.Key!=allocation.Target.Key||
           allocation.Type?.Key!=allocation.Target.Key||!PlainHierarchy(definition)||(definition.Flags&(TypeDef.Abstract|TypeDef.Interface))!=0)return false;
        HVar created=target.Variable;
        if(method.Blocks.SelectMany(b=>b.Statements).Distinct().Count()!=method.Blocks.Sum(b=>b.Statements.Count))return false;
        HBlock yes=branch.WhenTrue,no=branch.WhenFalse;
        if(ReferenceEquals(yes,no)||ReferenceEquals(yes,block)||ReferenceEquals(no,block)||
           yes.Scope!=-1||no.Scope!=-1||!method.Blocks.Contains(block)||!method.Blocks.Contains(yes)||!method.Blocks.Contains(no)||
           method.Blocks.Count==0||ReferenceEquals(method.Blocks[0],yes)||ReferenceEquals(method.Blocks[0],no)||
           yes.Statements.Count<2||no.Statements.Count<2||
           yes.Statements[0] is not HEval {Expression:HCall yc}||no.Statements[0] is not HEval {Expression:HCall nc}||
           !Constructor(yc)||!Constructor(nc)||!ReferenceEquals(yc.Method,nc.Method)||
           !ReferenceEquals(yc.Method.DeclaringType,definition)||yc.DeclaringType?.Key!=nc.DeclaringType?.Key||
           yc.DeclaringType!=null&&yc.DeclaringType.Key!=allocation.Target.Key||
           yc.Arguments.Length!=yc.Method.Parameters.Length||nc.Arguments.Length!=yc.Arguments.Length||
           !ScalarTest(branch.Condition,method))return false;
        for(int i=0;i<yc.Arguments.Length;i++)
            if(!ScalarValue(yc.Arguments[i],method,yc.Method.Parameters[i].Type)||
               !ScalarValue(nc.Arguments[i],method,yc.Method.Parameters[i].Type))return false;

        var predecessors=method.Blocks.ToDictionary(b=>b,_=>new HashSet<HBlock>());
        foreach(HBlock b in method.Blocks)
        {
            if(b.Statements.Count==0)return false;
            IEnumerable<HBlock> successors=b.Statements[^1] switch
            {
                HJump j=>[j.Target],HBranch br=>[br.WhenTrue,br.WhenFalse],
                HSwitch sw=>[..sw.Targets,sw.Default],HReturn or HThrow=>[],_=>[],
            };
            if(b.Statements.Take(b.Statements.Count-1).Any(s=>s is HJump or HBranch or HSwitch or HReturn or HThrow or HEndFinally))return false;
            if(b.Statements[^1] is not (HJump or HBranch or HSwitch or HReturn or HThrow))return false;
            foreach(HBlock next in successors)
            {
                if(!predecessors.TryGetValue(next,out var incoming))return false;
                incoming.Add(b);
            }
        }
        if(!predecessors[yes].SetEquals([block])||!predecessors[no].SetEquals([block]))return false;
        var reachable=new HashSet<HBlock>{method.Blocks[0]};
        for(bool changed=true;changed;)
        {
            changed=false;
            foreach(var pair in predecessors)
                if(pair.Value.Any(reachable.Contains)&&reachable.Add(pair.Key))changed=true;
        }
        if(!reachable.Contains(block))return false;
        // Reachability with the allocation block removed proves that it dominates every publication.
        var without=new HashSet<HBlock>();
        if(!ReferenceEquals(method.Blocks[0],block))without.Add(method.Blocks[0]);
        for(bool changed=true;changed;)
        {
            changed=false;
            foreach(var pair in predecessors)
                if(!ReferenceEquals(pair.Key,block)&&pair.Value.Any(without.Contains)&&without.Add(pair.Key))changed=true;
        }
        foreach(HBlock b in method.Blocks)
        foreach(HStmt statement in b.Statements)
        {
            if(ReferenceEquals(statement,assign)||ReferenceEquals(statement,yes.Statements[0])||ReferenceEquals(statement,no.Statements[0]))continue;
            if(!Mentions(statement,created))continue;
            // A direct field publication or return after construction creates no hidden local alias.
            bool publication=statement is HAssign {Target:HField {Field.IsStatic:false,Object:not null} field,Value:HLocal value}&&
                ReferenceEquals(value.Variable,created)&&!Mentions(field.Object,created);
            bool returned=statement is HReturn {Value:HLocal held}&&ReferenceEquals(held.Variable,created);
            if((!publication&&!returned)||ReferenceEquals(b,block)||!reachable.Contains(b)||without.Contains(b))return false;
        }

        var boolean=sigs.Primitive(Il2CppTypeEnum.Boolean);
        HVar selected=method.NewLocal(boolean,"ctorChoice");
        HLocal ReadChoice()=>new(selected){Type=boolean};
        var arguments=new HExpr[yc.Arguments.Length];
        for(int i=0;i<arguments.Length;i++)arguments[i]=new HSelect(ReadChoice(),HirCopy.Of(yc.Arguments[i]),HirCopy.Of(nc.Arguments[i])){Type=yc.Method.Parameters[i].Type};
        var capture=new HAssign(ReadChoice(),HirCopy.Of(branch.Condition)){Address=branch.Address};
        assign.Value=new HNewObject{Constructor=yc.Method,DeclaringType=yc.DeclaringType,Arguments=arguments,Type=allocation.Target};
        block.Statements.Insert(at,capture);branch.Condition=ReadChoice();
        yes.Statements.RemoveAt(0);no.Statements.RemoveAt(0);
        method.Notes.Add("one raw allocation and two branch constructors restored with one captured pure scalar condition");
        return true;

        bool Constructor(HCall call)=>call.Method.Name==".ctor"&&!call.Method.IsStatic&&!call.Method.IsVirtual&&!call.Method.IsAbstract&&!call.Virtual&&call.Constrained==null&&
            call.MethodArguments.Length==0&&call.Method.GenericParameters.Length==0&&call.Alternatives.Count==0&&
            call.Method.ReturnType is PrimitiveSig {Element:Il2CppTypeEnum.Void}&&
            call.This is HLocal receiver&&ReferenceEquals(receiver.Variable,created)&&receiver.Type?.Key==allocation.Target.Key;
    }

    private static bool PlainHierarchy(TypeDef definition)
    {
        var seen=new HashSet<TypeDef>();
        for(TypeDef? current=definition;current!=null;)
        {
            bool systemObject=current.ReflectionName=="System.Object";
            if(!seen.Add(current)||current.GenericParameters.Length!=0||current.IsValueType||
               current.Methods.Any(m=>m.Name==".cctor"||m.Name=="Finalize"&&!systemObject))return false;
            if(current.BaseType==null)return current.ReflectionName=="System.Object";
            // System.Object is normally encoded as ELEMENT_TYPE_OBJECT in loaded metadata.
            // Accept that signature only when it resolves to the exact terminal Object definition.
            if(current.BaseType is TypeDefSig parent)current=parent.Definition;
            else if(current.BaseType is PrimitiveSig {Element:Il2CppTypeEnum.Object,Definition:{ReflectionName:"System.Object",BaseType:null} root})current=root;
            else return false;
        }
        return false;
    }

    private static bool ScalarTest(HExpr e,HMethod method)
    {
        if(e is HCompare compare)return (compare.Op is HCompareOp.Eq or HCompareOp.Ne or HCompareOp.Lt or HCompareOp.Le or HCompareOp.Gt or HCompareOp.Ge or HCompareOp.LtUn or HCompareOp.LeUn or HCompareOp.GtUn or HCompareOp.GeUn)&& Integral(compare.Left,method)&&Integral(compare.Right,method)&&
            ActualType(compare.Left,method)?.Key==ActualType(compare.Right,method)?.Key&&
            (ActualType(compare.Left,method) is not PrimitiveSig {Element:Il2CppTypeEnum.Boolean}||compare.Op is HCompareOp.Eq or HCompareOp.Ne)&&
            e.Type is PrimitiveSig {Element:Il2CppTypeEnum.Boolean};
        if(e is HUnary {Op:HUnaryOp.LogicalNot} unary)return ScalarTest(unary.Operand,method)&&e.Type is PrimitiveSig {Element:Il2CppTypeEnum.Boolean};
        return ActualType(e,method) is PrimitiveSig {Element:Il2CppTypeEnum.Boolean}&&Atom(e,method);
    }

    private static bool Integral(HExpr e,HMethod method)
    {
        if(ActualType(e,method) is not PrimitiveSig {Element:Il2CppTypeEnum.Boolean or Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 or Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8})return false;
        if(Atom(e,method))return true;
        if(ActualType(e,method) is PrimitiveSig {Element:Il2CppTypeEnum.Boolean})return false;
        return e is HBinary {Op:HBinaryOp.Add or HBinaryOp.Sub or HBinaryOp.Mul or HBinaryOp.And or HBinaryOp.Or or HBinaryOp.Xor} binary&&
            Integral(binary.Left,method)&&Integral(binary.Right,method)&&ActualType(binary.Left,method)?.Key==e.Type?.Key&&ActualType(binary.Right,method)?.Key==e.Type?.Key;
    }

    private static bool ScalarValue(HExpr e,HMethod method,TypeSig required)=>
        required is PrimitiveSig {Element:Il2CppTypeEnum.Boolean or Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 or Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 or Il2CppTypeEnum.R4 or Il2CppTypeEnum.R8}&&
        ActualType(e,method)?.Key==required.Key&&Atom(e,method);

    private static bool Atom(HExpr e,HMethod method)=>e switch
    {
        HLocal l=>!l.Variable.AddressTaken&&e.Type?.Key==l.Variable.Type.Key,
        HArg a=>a.Index>=0&&a.Index<method.Method.Parameters.Length&&e.Type?.Key==method.Method.Parameters[a.Index].Type.Key,
        HConst c when c.Type is PrimitiveSig p=>c.Value switch
        {
            bool=>p.Element==Il2CppTypeEnum.Boolean,int=>p.Element==Il2CppTypeEnum.I4,uint=>p.Element==Il2CppTypeEnum.U4,
            long=>p.Element==Il2CppTypeEnum.I8,ulong=>p.Element==Il2CppTypeEnum.U8,float=>p.Element==Il2CppTypeEnum.R4,double=>p.Element==Il2CppTypeEnum.R8,_=>false,
        },
        _=>false,
    };

    private static TypeSig? ActualType(HExpr e,HMethod method)=>e switch
    {
        HLocal l when e.Type?.Key==l.Variable.Type.Key=>l.Variable.Type,
        HArg a when a.Index>=0&&a.Index<method.Method.Parameters.Length&&e.Type?.Key==method.Method.Parameters[a.Index].Type.Key=>method.Method.Parameters[a.Index].Type,
        HLocal or HArg=>null,_=>e.Type,
    };

    private static bool Mentions(HExpr? e,HVar variable)
    {
        bool found=false;FinallyFolding.Visit(e,node=>found|=node is HLocal local&&ReferenceEquals(local.Variable,variable));return found;
    }
    private static bool Mentions(HStmt statement,HVar variable)
    {
        bool found=false;FinallyFolding.Visit(statement,node=>found|=node is HLocal local&&ReferenceEquals(local.Variable,variable));return found;
    }
}
