using Rewind.Analysis.Hir;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>Restore the public List&lt;T&gt;.Add call from the exact inlined
/// version/update/capacity/resize diamond. Both paths must converge or return.
/// Never leave an inaccessible BCL private field in this matched pattern.</summary>
internal static class ListAppendFolding
{
    internal static bool TryFold(HMethod method, SigFactory sigs, HBlock block, NativeImage? image=null)
    {
        if (block.Statements.Count < 4 || block.Scope >= 0 && !method.TryRegions.ContainsKey(block.Scope >> 1)) return false;
        var ss = block.Statements;
        if (ss[^1] is not HBranch {Condition:HCompare {Op:HCompareOp.LeUn,Left:HArrayLength len,Right:HLocal compareCount}} branch)
            return false;
        // Optional integer local calculations scheduled between count and
        // capacity test. They neither access memory nor throw, and must not
        // use or overwrite any of the private implementation temporaries.
        int start = ss.Count - 4;
        while (start > 0 && ss.Count - start < 8 &&
            ss[start] is not HAssign {Value:HField {Field.Name:"_items"}}) start--;
        if (ss[start] is not HAssign { Target: HLocal array,
                Value: HField { Object: HLocal list, Field.Name: "_items" } items } ||
            list.Variable.Type is not GenericInstSig g || g.Definition.FullName != "System.Collections.Generic.List" ||
            g.Definition.Assembly.Name is not ("mscorlib" or "System.Private.CoreLib") ||
            g.Arguments.Length != 1 || g.Arguments[0].ContainsGenericParameter ||
            (g.Arguments[0].IsValueType && g.Arguments[0] is not PrimitiveSig {Element:Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4} &&
                (image==null||image.Arch!=CpuArch.Arm64||Environment.GetEnvironmentVariable("REWIND_NO_VECTOR_LIST_APPEND")!=null||
                 VectorListValue.Dimension(g.Arguments[0],2*image.PointerSize)==0)) ||
            array.Variable.AddressTaken || list.Variable.AddressTaken ||
            array.Variable.Type is not SzArraySig arr || arr.ElementType.Key != g.Arguments[0].Key)
            return false;
        // Only an identically typed, non-escaping local reference copy may be
        // moved past the private version update. Reads/calls/conversions stay put.
        int versionIndex=start+1;
        HAssign? itemCopy=null;
        if (ss[versionIndex] is HAssign {Target:HLocal copy,Value:HLocal source} copied &&
            !g.Arguments[0].IsValueType && !copy.Variable.AddressTaken && !source.Variable.AddressTaken &&
            copy.Variable.Type.Key==g.Arguments[0].Key && source.Variable.Type.Key==g.Arguments[0].Key &&
            (copy.Type==null||copy.Type.Key==copy.Variable.Type.Key) &&
            (source.Type==null||source.Type.Key==source.Variable.Type.Key))
        { itemCopy=copied; versionIndex++; }
        if (versionIndex+1>=ss.Count-1 ||
            ss[versionIndex] is not HAssign {Target:HField version,Value:HBinary {Op:HBinaryOp.Add,Left:HField previous,Right:HConst one}} ||
            ss[versionIndex+1] is not HAssign {Target:HLocal count,Value:var readCount} || count.Variable.AddressTaken)
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
        // A phi/merge local can lack its expression annotation after HIR
        // cleanup. Its declared HVar type is authoritative; conflicting
        // annotations are not accepted.
        TypeSig? EffectiveType(HExpr e)=>e is HLocal l
            ? (e.Type == null || e.Type.Key==l.Variable.Type.Key ? l.Variable.Type : null)
            : e.Type;
        bool Integer(TypeSig? t)=>t is PrimitiveSig {Element:Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4};
        bool Vector(TypeSig? t)=>image!=null&&image.Arch==CpuArch.Arm64&&
            VectorListValue.Dimension(t,2*image.PointerSize)!=0;
        bool vectorElement=Vector(g.Arguments[0]);
        bool Float(TypeSig? t)=>t is PrimitiveSig{Element:Il2CppTypeEnum.R4};
        bool Independent(HVar v)=>!v.AddressTaken&&!ReferenceEquals(v,array.Variable)&&
            !ReferenceEquals(v,count.Variable)&&!ReferenceEquals(v,list.Variable);
        // A vector kept in a typed local may retain the old stack object's
        // AddressTaken bit after the ABI reads were recovered as value
        // operations. Only relax that bit for a direct vector copy, if all
        // remaining uses are proven value uses (not a byref/address escape).
        var copyProofs=new Dictionary<HVar,bool>();
        bool CopyLocal(HVar v)
        {
            if(Independent(v))return true;
            if(!vectorElement||!Vector(v.Type)||v==array.Variable||v==count.Variable||v==list.Variable||
                Environment.GetEnvironmentVariable("REWIND_NO_VECTOR_VALUE_COPY")!=null)return false;
            if(!copyProofs.TryGetValue(v,out bool safe))
            {
                safe=VectorListValue.ValueOnlyLocal(method,sigs,v);
                copyProofs[v]=safe;
            }
            return safe;
        }
        bool PlainVector(HExpr e,int depth=0)
        {
            if(!vectorElement||depth>16)return false;
            TypeSig? t=EffectiveType(e);
            if(!Vector(t)&&!Float(t))return false;
            return e switch
            {
                HArg {Index:>=0}=>true,
                HLocal l=>CopyLocal(l.Variable),
                HConst {Value:float}=>Float(t),
                HField {Object:HLocal l} f=>Float(t)&&Independent(l.Variable)&&Vector(l.Variable.Type)&&
                    ReferenceEquals(f.Field.DeclaringType,l.Variable.Type.Definition)&&!f.Field.IsStatic&&
                    (f.Field.Attrs&FieldDef.AccessMask)==6&&f.Field.Type.Key==t!.Key,
                HBinary {Op:HBinaryOp.Add or HBinaryOp.Sub or HBinaryOp.Mul or HBinaryOp.Div} b=>
                    Float(t)&&Float(EffectiveType(b.Left))&&Float(EffectiveType(b.Right))&&
                    PlainVector(b.Left,depth+1)&&PlainVector(b.Right,depth+1),
                HNewObject n=>Vector(t)&&VectorListValue.ConstructorShape(image!,n.Constructor,t)&&
                    n.Arguments.Length==n.Constructor.Parameters.Length&&
                    n.Arguments.All(a=>Float(EffectiveType(a))&&PlainVector(a,depth+1)),
                _=>false
            };
        }
        bool SameVector(HExpr a,HExpr b,int depth=0)
        {
            if(depth>16||EffectiveType(a)?.Key!=EffectiveType(b)?.Key||a.GetType()!=b.GetType())return false;
            return (a,b) switch
            {
                (HConst {Value:float x},HConst {Value:float y})=>BitConverter.SingleToUInt32Bits(x)==BitConverter.SingleToUInt32Bits(y),
                (HBinary x,HBinary y)=>x.Op==y.Op&&SameVector(x.Left,y.Left,depth+1)&&SameVector(x.Right,y.Right,depth+1),
                (HNewObject x,HNewObject y)=>ReferenceEquals(x.Constructor,y.Constructor)&&x.Arguments.Length==y.Arguments.Length&&
                    PlainVector(x)&&PlainVector(y)&&x.Arguments.Zip(y.Arguments).All(z=>SameVector(z.First,z.Second,depth+1)),
                _=>HirCleanup.Same(a,b)
            };
        }
        bool SameItem(HExpr a,HExpr b)=>vectorElement?SameVector(a,b):HirCleanup.Same(a,b);

        bool Plain(HExpr e)=>Integer(EffectiveType(e)) && (e switch
        {
            HConst {Value:int or long}=>true,
            HArg {Index:>=0}=>true,
            HLocal l=>!l.Variable.AddressTaken &&
                !ReferenceEquals(l.Variable,array.Variable)&&!ReferenceEquals(l.Variable,count.Variable)&&!ReferenceEquals(l.Variable,list.Variable),
            HBinary {Op:HBinaryOp.Add or HBinaryOp.Sub or HBinaryOp.And or HBinaryOp.Or or HBinaryOp.Xor} b=>Plain(b.Left)&&Plain(b.Right),
            _=>false
        });
        var computations=ss.Skip(versionIndex+2).Take(ss.Count-versionIndex-3).ToArray();
        if(computations.Length>4||computations.Any(s=>s is not HAssign {Target:HLocal dest,Value:var value} ||
            !Independent(dest.Variable)||
            !((Integer(dest.Variable.Type)&&Plain(value))||
                ((Vector(dest.Variable.Type)||Float(dest.Variable.Type))&&
                 EffectiveType(value)?.Key==dest.Variable.Type.Key&&PlainVector(value)))))return false;
        HBlock slow=branch.WhenTrue,fast=branch.WhenFalse;
        if(slow==fast||slow==block||fast==block||slow==method.Blocks[0]||fast==method.Blocks[0]||
            !method.Blocks.Contains(slow)||!method.Blocks.Contains(fast)||
            slow.Scope!=block.Scope||fast.Scope!=block.Scope||
            method.TryRegions.Values.Any(r=>r.Entry==slow||r.Entry==fast||r.HandlerEntry==slow||r.HandlerEntry==fast))return false;
        if(fast.Statements.Count<3 || slow.Statements.Count<2 ||
            fast.Statements[0] is not HAssign {Target:HField size,Value:HBinary {Op:HBinaryOp.Add,Left:HLocal sz,Right:HConst increment}} ||
            fast.Statements[1] is not HAssign {Target:HElement dest,Value:var item} ||
            !Field(size,"_size")||!ReferenceEquals(sz.Variable,count.Variable)||!One(increment)||
            !Local(dest.Array,array.Variable)||!Local(dest.Index,count.Variable)||
            slow.Statements[0] is not HEval {Expression:HCall resize} ||
            resize.Method.Name!="AddWithResize"||!ReferenceEquals(resize.Method.DeclaringType,g.Definition)||
            resize.Method.IsStatic||!Local(resize.This,list.Variable)||resize.Arguments.Length!=1||
            !SameItem(item,resize.Arguments[0])||
            (!(item is HArg or HLocal or HConst)&&!PlainVector(item))||
            (vectorElement&&(!PlainVector(item)||!PlainVector(resize.Arguments[0])))||EffectiveType(item)?.Key!=g.Arguments[0].Key||
            (vectorElement&&EffectiveType(resize.Arguments[0])?.Key!=g.Arguments[0].Key)||
            ConstructorFolding.Mentions(item,array.Variable)||ConstructorFolding.Mentions(item,count.Variable))
            return false;
        var fastEnd=fast.Statements[^1];var slowEnd=slow.Statements[^1];
        bool preserveArms=fast.Statements.Count!=3||slow.Statements.Count!=2;
        MethodDef? capacityGetter=null;
        if(preserveArms)
        {
            // A branch-local receiver copy and a post-resize reload need not
            // denote the same list. Keep both arms, their assignments, and
            // the capacity decision; only replace the proven BCL mutation.
            // Restrict this form to an int append and one typed reference
            // assignment per arm. No private temporary may survive in a tail.
            if(g.Arguments[0] is not PrimitiveSig {Element:Il2CppTypeEnum.I4} ||
                count.Variable.Type is not PrimitiveSig {Element:Il2CppTypeEnum.I4} ||
                fast.Statements.Count!=4||slow.Statements.Count!=3 ||
                fast.Statements[2] is not HAssign {Target:HLocal fastPhi,Value:var fastReference} ||
                slow.Statements[1] is not HAssign {Target:HLocal slowPhi,Value:var slowReference} ||
                !ReferenceEquals(fastPhi.Variable,slowPhi.Variable)||fastPhi.Variable.AddressTaken||
                fastPhi.Variable.Type.Key!=g.Key||EffectiveType(fastReference)?.Key!=g.Key||
                EffectiveType(slowReference)?.Key!=g.Key||!Local(fastReference,list.Variable)||
                ConstructorFolding.Mentions(slowReference,array.Variable)||
                ConstructorFolding.Mentions(slowReference,count.Variable))return false;
            var getters=g.Definition.Methods.Where(m=>m.Name=="get_Capacity"&&
                ReferenceEquals(m.DeclaringType,g.Definition)&&!m.IsStatic&&!m.IsVirtual&&
                (m.Flags&MethodDef.AccessMask)==6&&m.GenericParameters.Length==0&&
                m.Parameters.Length==0&&m.ReturnType is PrimitiveSig {Element:Il2CppTypeEnum.I4}).ToArray();
            if(getters.Length!=1)return false;
            capacityGetter=getters[0];
        }
        HStmt continuation;
        // IL2CPP can route one arm through an empty jump block. Follow only
        // same-scope jumps with no effects, never an exception-region entry.
        HBlock? JumpTarget(HBlock target)
        {
            var visited=new HashSet<HBlock>();
            while(true)
            {
                if(!method.Blocks.Contains(target)||target==fast||target==slow||target==block||!visited.Add(target))return null;
                if(target.Scope!=block.Scope||
                    method.TryRegions.Values.Any(r=>r.Entry==target||r.HandlerEntry==target)||
                    target.Statements is not [HJump next])return target;
                target=next.Target;
            }
        }
        if(fastEnd is HJump fj&&slowEnd is HJump sj&&JumpTarget(fj.Target) is { } join&&JumpTarget(sj.Target)==join)
        {
            if(block.Scope>=0&&!method.Encloses(join.Scope,block.Scope))return false;
            continuation=new HJump(join){Address=branch.Address};
        }
        else if(block.Scope<0&&method.Method.ReturnType.IsVoid && IsVoidExit(fastEnd)&&IsVoidExit(slowEnd))
            continuation=new HReturn(null){Address=branch.Address};
        else return false;
        bool IsVoidExit(HStmt end)=>end is HReturn {Value:null} ||
            end is HJump j&&j.Target!=fast&&j.Target!=slow&&j.Target!=block&&j.Target.Statements is [HReturn{Value:null}];
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
        if(preserveArms)
        {
            if((add[0].Flags&MethodDef.AccessMask)!=6||(add[0].IsVirtual&&(add[0].Flags&MethodDef.Final)==0))return false;
            // List.Capacity is exactly _items.Length in the BCL. Its snapshot
            // replaces the inaccessible array snapshot at the same site.
            // Add performs the already-proven version/size/payload mutation;
            // the original branch-specific receiver reload remains after it.
            // The private array has no surviving uses. Reuse its identity
            // instead of allocating by Locals.Count after previous folds
            // removed locals; that could duplicate another HVar's index/name.
            var capacity=array.Variable;
            capacity.Type=sigs.Primitive(Il2CppTypeEnum.I4);
            ss[start]=new HAssign(new HLocal(capacity){Type=capacity.Type},new HCall{
                Method=capacityGetter!,DeclaringType=g,This=list,Type=capacity.Type}){Address=ss[start].Address};
            ss.RemoveAt(versionIndex);
            ((HCompare)branch.Condition).Left=new HLocal(capacity){Type=capacity.Type};
            HEval PublicAdd(HExpr value,ulong address)=>new(new HCall{
                Method=add[0],DeclaringType=g,This=list,Arguments=[value],Type=add[0].ReturnType}){Address=address};
            fast.Statements[0]=PublicAdd(item,fast.Statements[0].Address);
            fast.Statements.RemoveAt(1);
            slow.Statements[0]=PublicAdd(resize.Arguments[0],slow.Statements[0].Address);
            method.Notes.Add($"public List.Add restored with branch-specific receiver reload preserved at 0x{branch.Address:X}");
            return true;
        }
        ss.RemoveRange(start,ss.Count-start);
        if(itemCopy!=null)ss.Add(itemCopy);
        ss.AddRange(computations);
        ss.Add(new HEval(new HCall{Method=add[0],DeclaringType=g,This=list,Arguments=[item],Type=add[0].ReturnType}){Address=branch.Address});
        ss.Add(continuation);
        method.Blocks.Remove(fast);method.Blocks.Remove(slow);
        method.Locals.Remove(array.Variable);method.Locals.Remove(count.Variable);
        method.Notes.Add($"public List.Add restored from complete inlined capacity diamond at 0x{branch.Address:X}");
        return true;
    }
    /// <summary>Keep both original capacity arms and all value construction.
    /// Only the BCL implementation mutations become public Add calls. The
    /// capacity read stays at the original array-read site, so interleaved
    /// reads and their exception order are never moved across that site.</summary>
    internal static bool TryFoldRetainedDiamond(HMethod method,SigFactory sigs,HBlock block,NativeImage image)
    {
        if(image.Arch!=CpuArch.Arm64||block.Scope>=0||method.TryRegions.Count!=0||
            method.Problems.Count!=0||block.Statements.Count<4)return false;
        var ss=block.Statements;
        if(ss[^1] is not HBranch {Condition:HCompare {Op:HCompareOp.LeUn,
            Left:HArrayLength length,Right:HLocal compareCount}} branch)return false;
        int start=ss.Count-4;
        while(start>0&&ss.Count-start<9&&ss[start] is not HAssign {Value:HField {Field.Name:"_items"}})start--;
        if(ss[start] is not HAssign {Target:HLocal array,Value:HField {Object:HLocal list} items}||
            list.Variable.Type is not GenericInstSig g||g.Definition.FullName!="System.Collections.Generic.List"||
            g.Definition.Assembly.Name is not("mscorlib" or "System.Private.CoreLib")||g.Arguments.Length!=1||
            g.Arguments[0] is not TypeDefSig {Definition:{IsValueType:true,IsEnum:false,IsGenericDefinition:false}}||
            array.Variable.Type is not SzArraySig arr||arr.ElementType.Key!=g.Arguments[0].Key||
            list.Variable.AddressTaken||array.Variable.AddressTaken)return false;
        bool Local(HExpr? e,HVar v)=>e is HLocal l&&ReferenceEquals(l.Variable,v);
        TypeSig? Type(HExpr e)=>e is HLocal l?(e.Type==null||e.Type.Key==l.Variable.Type.Key?l.Variable.Type:null):e.Type;
        bool Int(TypeSig? t)=>t is PrimitiveSig {Element:Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4};
        bool One(HConst c)=>c.Value is int x&&x==1||c.Value is long y&&y==1;
        bool Field(HField f,string name)=>f.Field.Name==name&&!f.Field.IsStatic&&
            ReferenceEquals(f.Field.DeclaringType,g.Definition)&&Local(f.Object,list.Variable);
        if(!Field(items,"_items")||sigs.Substitute(items.Field.Type,g.Arguments,[]) is not SzArraySig backing||
            backing.ElementType.Key!=g.Arguments[0].Key)return false;
        int vi=start+1;
        while(vi<ss.Count-3&&ss[vi] is not HAssign {Target:HField {Field.Name:"_version"}})vi++;
        if(vi+3!=ss.Count||ss[vi] is not HAssign {Target:HField version,
            Value:HBinary {Op:HBinaryOp.Add,Left:HField previous,Right:HConst one}}||
            !Field(version,"_version")||!Field(previous,"_version")||!ReferenceEquals(version.Field,previous.Field)||
            !Int(version.Field.Type)||!One(one)||
            ss[vi+1] is not HAssign {Target:HLocal count,Value:var countRead}||
            count.Variable.AddressTaken||!Int(count.Variable.Type)||!Local(compareCount,count.Variable)||
            !Local(length.Array,array.Variable))return false;
        bool Count(HExpr e)=>e is HField f&&Field(f,"_size")||
            e is HCall c&&c.Method.Name=="get_Count"&&!c.Method.IsStatic&&
            ReferenceEquals(c.Method.DeclaringType,g.Definition)&&Local(c.This,list.Variable)&&
            c.Arguments.Length==0&&Int(c.Method.ReturnType);
        if(!Count(countRead))return false;
        bool Independent(HVar v)=>v!=array.Variable&&v!=count.Variable&&v!=list.Variable&&!v.AddressTaken;
        // These operations remain at the same position before the version
        // increment. No calls, stores, allocation, checked math or escapes.
        bool Read(HExpr e,int depth=0)
        {
            if(depth>12)return false;
            return e switch
            {
                HLocal l=>Independent(l.Variable),
                HArg {Index:>=0}=>true,
                HConst {Value:int or long or float or bool}=>true,
                HDeref d=>Read(d.Pointer,depth+1),
                HField f=>!f.Field.IsStatic&&f.Object!=null&&Read(f.Object,depth+1),
                HBinary b when b.Op is HBinaryOp.Add or HBinaryOp.Sub or HBinaryOp.And or HBinaryOp.Or or HBinaryOp.Xor or HBinaryOp.Shl or HBinaryOp.Shr or HBinaryOp.ShrUn=>Read(b.Left,depth+1)&&Read(b.Right,depth+1),
                HConv c when c.Kind is HConvKind.U1 or HConvKind.I4 or HConvKind.U4=>Read(c.Operand,depth+1),
                HCompare c=>Read(c.Left,depth+1)&&Read(c.Right,depth+1),
                HSelect c=>Read(c.Condition,depth+1)&&Read(c.WhenTrue,depth+1)&&Read(c.WhenFalse,depth+1),
                _=>false
            };
        }
        bool PureValue(HExpr e,int depth=0)
        {
            if(depth>12||Type(e) is not PrimitiveSig)return false;
            return e switch
            {
                HLocal l=>Independent(l.Variable),
                HArg {Index:>=0}=>true,
                HConst {Value:int or long or float or bool}=>true,
                HBinary b when b.Op is HBinaryOp.Add or HBinaryOp.Sub or HBinaryOp.And or HBinaryOp.Or or HBinaryOp.Xor or HBinaryOp.Shl or HBinaryOp.Shr or HBinaryOp.ShrUn=>PureValue(b.Left,depth+1)&&PureValue(b.Right,depth+1),
                HConv c when c.Kind is HConvKind.U1 or HConvKind.I4 or HConvKind.U4=>PureValue(c.Operand,depth+1),
                HCompare c=>PureValue(c.Left,depth+1)&&PureValue(c.Right,depth+1),
                HSelect c=>PureValue(c.Condition,depth+1)&&PureValue(c.WhenTrue,depth+1)&&PureValue(c.WhenFalse,depth+1),
                _=>false
            };
        }
        var prelude=ss.Skip(start+1).Take(vi-start-1).ToArray();
        if(prelude.Length>4||prelude.Any(s=>s is not HAssign {Target:HLocal l,Value:var e}||
            !Independent(l.Variable)||l.Variable.Type is not PrimitiveSig||!Read(e)))return false;
        var fast=branch.WhenFalse;var slow=branch.WhenTrue;
        if(fast==slow||fast==block||slow==block||fast==method.Blocks[0]||slow==method.Blocks[0]||
            !method.Blocks.Contains(fast)||!method.Blocks.Contains(slow)||fast.Scope!=block.Scope||slow.Scope!=block.Scope||
            fast.Statements.Count<3||slow.Statements.Count<2)return false;
        var fs=fast.Statements;var sl=slow.Statements;
        if(fs[0] is not HAssign {Target:HField size,Value:HBinary {Op:HBinaryOp.Add,Left:HLocal n,Right:HConst increment}}||
            !Field(size,"_size")||!Int(size.Field.Type)||!Local(n,count.Variable)||!One(increment)||
            fs[^2] is not HAssign {Target:HElement target,Value:var fastItem}||
            !Local(target.Array,array.Variable)||!Local(target.Index,count.Variable)||
            sl[^2] is not HEval {Expression:HCall resize}||resize.Method.Name!="AddWithResize"||
            resize.Method.IsStatic||!resize.Method.ReturnType.IsVoid||
            !ReferenceEquals(resize.Method.DeclaringType,g.Definition)||!Local(resize.This,list.Variable)||
            resize.Method.Parameters.Length!=1||
            sigs.Substitute(resize.Method.Parameters[0].Type,g.Arguments,[]).Key!=g.Arguments[0].Key||
            resize.Arguments.Length!=1||Type(fastItem)?.Key!=g.Arguments[0].Key||
            Type(resize.Arguments[0])?.Key!=g.Arguments[0].Key)return false;
        if(!(fs[^1] is HReturn {Value:null}&&sl[^1] is HReturn {Value:null}&&method.Method.ReturnType.IsVoid)&&
            !(fs[^1] is HJump fj&&sl[^1] is HJump sj&&fj.Target==sj.Target&&fj.Target!=fast&&fj.Target!=slow&&fj.Target!=block))return false;
        var valueStores=fs.Skip(1).Take(fs.Count-3).Concat(sl.Take(sl.Count-2)).ToArray();
        // A distinct receiver-reload tail is handled by the earlier matcher.
        // This form is only for interleaved reads or retained value stores.
        if(prelude.Length==0&&valueStores.Length==0)return false;
        var permittedValueUses=new HashSet<HStmt>();
        bool ValueArm(HExpr item,IEnumerable<HStmt> stores,HStmt append)
        {
            var writes=stores.ToArray();
            if(writes.Length==0)return item is HNewObject creation&&
                VectorListValue.ConstructorShape(image,creation.Constructor,g.Arguments[0])&&
                creation.Arguments.Length==creation.Constructor.Parameters.Length&&creation.Arguments.All(a=>
                    Type(a) is PrimitiveSig {Element:Il2CppTypeEnum.R4}&&PureValue(a));
            if(item is not HLocal value||writes.Length is <2 or >4)return false;
            var seen=new HashSet<FieldDef>();
            foreach(var s in writes)
            {
                if(s is not HAssign {Target:HField {Object:HLocal receiver} field,Value:var rhs}||
                    receiver.Variable!=value.Variable||field.Field.IsStatic||
                    !ReferenceEquals(field.Field.DeclaringType,g.Arguments[0].Definition)||
                    (field.Field.Attrs&FieldDef.AccessMask)!=6||
                    field.Field.Type is not PrimitiveSig {Element:Il2CppTypeEnum.U1 or Il2CppTypeEnum.R4}||
                    !seen.Add(field.Field)||!PureValue(rhs)||ConstructorFolding.Mentions(rhs,value.Variable))return false;
                permittedValueUses.Add(s);
            }
            permittedValueUses.Add(append);
            foreach(var b in method.Blocks)foreach(var s in b.Statements)
            {
                if(!ConstructorFolding.Mentions(s,value.Variable)||permittedValueUses.Contains(s))continue;
                if(s is not HAssign {Target:HLocal l,Value:HTypeExpr {Op:HTypeOp.Default} d}||
                    l.Variable!=value.Variable||d.Target.Key!=value.Variable.Type.Key)return false;
            }
            return true;
        }
        if(!ValueArm(fastItem,fs.Skip(1).Take(fs.Count-3),fs[^2])||
            !ValueArm(resize.Arguments[0],sl.Take(sl.Count-2),sl[^2]))return false;
        foreach(var b in method.Blocks)foreach(var s in b.Statements)
        {
            if(b==block&&ReferenceEquals(s,branch))continue;
            if(s is HJump j&&(j.Target==fast||j.Target==slow)||
                s is HBranch br&&(br.WhenTrue==fast||br.WhenTrue==slow||br.WhenFalse==fast||br.WhenFalse==slow)||
                s is HSwitch sw&&(sw.Default==fast||sw.Default==slow||sw.Targets.Contains(fast)||sw.Targets.Contains(slow)))return false;
            if(ConstructorFolding.Mentions(s,array.Variable)&&
                !(b==block&&ReferenceEquals(s,ss[start]))&&!(b==fast&&ReferenceEquals(s,fs[^2])))return false;
        }
        var capacities=g.Definition.Methods.Where(m=>m.Name=="get_Capacity"&&!m.IsStatic&&!m.IsVirtual&&
            (m.Flags&MethodDef.AccessMask)==6&&m.GenericParameters.Length==0&&m.Parameters.Length==0&&Int(m.ReturnType)).ToArray();
        var adds=g.Definition.Methods.Where(m=>m.Name=="Add"&&!m.IsStatic&&
            (m.Flags&MethodDef.AccessMask)==6&&(!m.IsVirtual||(m.Flags&MethodDef.Final)!=0)&&
            m.GenericParameters.Length==0&&m.ReturnType.IsVoid&&m.Parameters.Length==1&&
            sigs.Substitute(m.Parameters[0].Type,g.Arguments,[]).Key==g.Arguments[0].Key).ToArray();
        var countGetters=g.Definition.Methods.Where(m=>m.Name=="get_Count"&&!m.IsStatic&&m.Parameters.Length==0&&
            m.GenericParameters.Length==0&&(m.Flags&MethodDef.AccessMask)==6&&Int(m.ReturnType)).ToArray();
        if(capacities.Length!=1||adds.Length!=1||countRead is HField&&countGetters.Length!=1)return false;
        // Commit only after every proof succeeds; use the existing dead array
        // identity to avoid duplicate HVar indices after earlier folds.
        array.Variable.Type=sigs.Primitive(Il2CppTypeEnum.I4);
        ss[start]=new HAssign(new HLocal(array.Variable){Type=array.Variable.Type},new HCall{
            Method=capacities[0],DeclaringType=g,This=list,Type=array.Variable.Type}){Address=ss[start].Address};
        ss.RemoveAt(vi);
        ((HCompare)branch.Condition).Left=new HLocal(array.Variable){Type=array.Variable.Type};
        if(countRead is HField)
        {
            ((HAssign)ss[vi]).Value=new HCall{Method=countGetters[0],DeclaringType=g,This=list,Type=count.Variable.Type};
        }
        HEval Add(HExpr item,ulong address)=>new(new HCall{Method=adds[0],DeclaringType=g,This=list,
            Arguments=[item],Type=adds[0].ReturnType}){Address=address};
        fs[^2]=Add(fastItem,fs[^2].Address);fs.RemoveAt(0);
        sl[^2]=Add(resize.Arguments[0],sl[^2].Address);
        method.Notes.Add($"public List.Add restored with capacity arms and value-construction order retained at 0x{branch.Address:X}");
        return true;
    }
    public static void Run(HMethod method,SigFactory sigs,NativeImage image)
    {
        if(Environment.GetEnvironmentVariable("REWIND_NO_LIST_APPEND_FOLDING")!=null)return;
        // Exact method selection keeps diagnostics useful under parallel recovery.
        bool trace=Environment.GetEnvironmentVariable("REWIND_LIST_APPEND_TRACE")==method.Method.FullName;
        if(trace)
        {
            Console.Error.WriteLine("[list-append] before\n"+HirPrinter.Print(method));
            foreach(var v in method.Locals)
                Console.Error.WriteLine($"[list-append] {v.Name}: {v.Type.Key}, address taken={v.AddressTaken}");
        }
        foreach(var b in method.Blocks.ToArray())
            if(method.Blocks.Contains(b))
            {
                TryFoldRetainedDiamond(method,sigs,b,image);
                TryFold(method,sigs,b,image);
            }
        if(trace)Console.Error.WriteLine("[list-append] after\n"+HirPrinter.Print(method));
    }
}
