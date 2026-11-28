using Mono.Cecil;
using Mono.Cecil.Cil;
using Mono.Cecil.Rocks;

namespace Rewind.Output;

/// <summary>
/// Last, strict managed-IL normalization of the complete inlined BCL List.Add
/// diamond when the earlier HIR folding could not express it. Never fold a
/// partial private field access or an unproven capacity branch.
/// </summary>
internal static class ListAppendIlFolding
{
    private static readonly Code[] Shape =
    [
        Code.Ldloc, Code.Ldfld, Code.Stloc,
        Code.Ldloc, Code.Ldloc, Code.Ldfld, Code.Ldc_I4, Code.Add, Code.Stfld,
        Code.Ldloc, Code.Callvirt, Code.Stloc,
        Code.Ldloc, Code.Ldlen, Code.Conv_I4, Code.Ldloc, Code.Cgt_Un, Code.Ldc_I4, Code.Ceq, Code.Brtrue,
        Code.Nop, Code.Ldloc, Code.Ldloc, Code.Ldc_I4, Code.Add, Code.Stfld,
        Code.Ldloc, Code.Ldloc, Code.Ldloc, Code.Stelem_Any, Code.Br
    ];

    private static bool List(TypeReference t) => t is GenericInstanceType g &&
        g.ElementType.FullName == "System.Collections.Generic.List`1" &&
        g.ElementType.Scope.Name is "mscorlib" or "System.Private.CoreLib" &&
        g.GenericArguments.Count == 1 && !g.ContainsGenericParameter;

    private static string? AssemblyIdentity(TypeReference t) => t.Scope switch
    {
        AssemblyNameReference a => a.FullName,
        ModuleDefinition m => m.Assembly?.Name.FullName,
        _ => null
    };

    private static bool Same(TypeReference a, TypeReference b) =>
        a.FullName == b.FullName && AssemblyIdentity(a) is { } id && id == AssemblyIdentity(b) &&
        (a is not GenericInstanceType ga || b is GenericInstanceType gb &&
         ga.GenericArguments.Count == gb.GenericArguments.Count &&
         ga.GenericArguments.Zip(gb.GenericArguments).All(x => Same(x.First, x.Second)));

    private static bool ElementParameter(TypeReference t, GenericInstanceType list) =>
        t is GenericParameter p && p.Type == GenericParameterType.Type && p.Position == 0 &&
        p.Owner is TypeReference owner && Same(owner, list.ElementType);

    private static bool Constant(Instruction i, int n) => i.OpCode.Code == Code.Ldc_I4 && i.Operand is int k && k == n;

    // Preserve the native array-indexed item read at its original position.
    // It may throw on a null/short source array, so it is not moved across the
    // List receiver null-check or the original version increment.
    private static bool SafeArrayAppendSchedule(Instruction[] code, object list,
        VariableDefinition array, VariableDefinition size, object value, TypeReference element)
    {
        if (code.Length != 8 || code[0].OpCode.Code != Code.Ldloc ||
            code[0].Operand is not VariableDefinition source ||
            source.VariableType is not ArrayType { IsVector: true } sourceArray ||
            !Same(sourceArray.ElementType, element) ||
            code[1].OpCode.Code != Code.Ldloc || code[1].Operand is not VariableDefinition index ||
            index.VariableType.MetadataType != MetadataType.Int64 ||
            code[2].OpCode.Code != Code.Ldc_I4 ||
            code[3].OpCode.Code != Code.Conv_I8 || code[4].OpCode.Code != Code.Add ||
            code[5].OpCode.Code != Code.Conv_I4 || code[6].OpCode.Code != Code.Ldelem_Any ||
            code[6].Operand is not TypeReference readType || !Same(readType, element) ||
            code[7].OpCode.Code != Code.Stloc || code[7].Operand != value ||
            value is not VariableDefinition destination || !Same(destination.VariableType, element) ||
            new object[] { list, array, size, value }.Contains(source) ||
            new object[] { list, array, size, value }.Contains(index)) return false;
        return true;
    }

    private static TypeReference? LoadedValueType(Instruction i) => i.OpCode.Code switch
    {
        Code.Ldloc or Code.Ldloc_S when i.Operand is VariableDefinition v => v.VariableType,
        Code.Ldarg or Code.Ldarg_S when i.Operand is ParameterDefinition p => p.ParameterType,
        _ => null
    };

    private static bool Scalar(TypeReference t) => t.MetadataType is MetadataType.Single or MetadataType.Double or
        MetadataType.Int32 or MetadataType.UInt32 or MetadataType.Int64 or MetadataType.UInt64 or
        MetadataType.SByte or MetadataType.Byte or MetadataType.Int16 or MetadataType.UInt16;
    private static bool Floating(TypeReference t) => t.MetadataType is MetadataType.Single or MetadataType.Double;
    private static int StackKind(TypeReference t) => t.MetadataType switch
    {
        MetadataType.Single or MetadataType.Double => 1,
        MetadataType.Int64 or MetadataType.UInt64 => 2,
        MetadataType.Int32 or MetadataType.UInt32 or MetadataType.SByte or MetadataType.Byte or MetadataType.Int16 or MetadataType.UInt16 => 3,
        _ => 0
    };
    private static bool StackSame(TypeReference a, TypeReference b) => Same(a,b) ||
        StackKind(a) != 0 && StackKind(a) == StackKind(b);

    private static bool ReadOnlyValueField(Instruction address, Instruction read)
    {
        TypeReference? owner = address.OpCode.Code switch
        {
            Code.Ldarga or Code.Ldarga_S when address.Operand is ParameterDefinition p => p.ParameterType,
            Code.Ldloca or Code.Ldloca_S when address.Operand is VariableDefinition v => v.VariableType,
            _ => null
        };
        if (owner is not { IsValueType: true, ContainsGenericParameter: false } ||
            read.OpCode.Code != Code.Ldfld || read.Operand is not FieldReference field ||
            !Same(field.DeclaringType,owner) || !Scalar(field.FieldType)) return false;
        try
        {
            return field.Resolve() is { IsStatic: false, IsPublic: true } resolved &&
                Same(resolved.DeclaringType,owner) && Same(resolved.FieldType,field.FieldType);
        }
        catch (AssemblyResolutionException) { return false; }
        catch (ResolutionException) { return false; }
    }

    // Only the scalar field constructors of the engine's vector values (or
    // their System.Numerics fixture equivalents). These write their own value;
    // they cannot call game code or allocate a managed object.
    private static bool ScalarValueConstructor(MethodReference call)
    {
        if (call.Name != ".ctor" || !call.HasThis || !call.DeclaringType.IsValueType ||
            call.HasGenericParameters || call is GenericInstanceMethod ||
            call.ReturnType.MetadataType != MetadataType.Void || call.Parameters.Any(p=>p.ParameterType.MetadataType!=MetadataType.Single)) return false;
        string type=call.DeclaringType.FullName;
        int count=type is "UnityEngine.Vector2" or "System.Numerics.Vector2" ? 2 :
            type is "UnityEngine.Vector3" or "System.Numerics.Vector3" ? 3 :
            type is "UnityEngine.Vector4" or "System.Numerics.Vector4" ? 4 : 0;
        if(count==0 || call.Parameters.Count!=count ||
            (type.StartsWith("UnityEngine.",StringComparison.Ordinal) ?
                call.DeclaringType.Scope.Name is not ("UnityEngine.CoreModule" or "UnityEngine") :
                call.DeclaringType.Scope.Name is not ("System.Private.CoreLib" or "System.Numerics.Vectors")))return false;
        try
        {
            return call.Resolve() is { IsPublic:true, IsStatic:false, IsConstructor:true, HasGenericParameters:false } resolved &&
                Same(resolved.DeclaringType,call.DeclaringType) && resolved.Parameters.Count==count &&
                resolved.Parameters.All(p=>p.ParameterType.MetadataType==MetadataType.Single);
        }
        catch(AssemblyResolutionException){return false;}
        catch(ResolutionException){return false;}
    }

    private static bool ScalarIntrinsic(MethodReference call, TypeDefinition listDefinition)
    {
        if(call.HasThis || call.HasGenericParameters || call is GenericInstanceMethod || call.Parameters.Count!=1 ||
            AssemblyIdentity(call.DeclaringType)!=AssemblyIdentity(listDefinition))return false;
        var input=call.Parameters[0].ParameterType.MetadataType;var output=call.ReturnType.MetadataType;
        bool signature=call.DeclaringType.FullName=="System.BitConverter" &&
            ((call.Name=="SingleToInt32Bits"&&input==MetadataType.Single&&output==MetadataType.Int32)||
             (call.Name=="Int32BitsToSingle"&&input==MetadataType.Int32&&output==MetadataType.Single)) ||
            call.DeclaringType.FullName=="System.Math"&&call.Name=="Sqrt"&&input==MetadataType.Double&&output==MetadataType.Double;
        if(!signature)return false;
        try
        {
            return call.Resolve() is {IsStatic:true,IsPublic:true,HasGenericParameters:false} resolved &&
                Same(resolved.DeclaringType,call.DeclaringType)&&resolved.Parameters.Count==1&&
                Same(resolved.Parameters[0].ParameterType,call.Parameters[0].ParameterType)&&Same(resolved.ReturnType,call.ReturnType);
        }
        catch(AssemblyResolutionException){return false;}
        catch(ResolutionException){return false;}
    }

    // A bounded typed interpreter proves that a scheduled scalar calculation
    // cannot throw, escape an address or mutate the receiver. Instructions stay
    // in place and retain their exact rounding, bitcasts and local stores.
    private static bool SafePostVersionSchedule(Instruction[] code, TypeDefinition listDefinition, TypeSystem types, params object[] protectedLocals)
    {
        var stack=new Stack<TypeReference>();
        TypeReference? Pop()=>stack.TryPop(out var t)?t:null;
        var ts=types;
        for(int i=0;i<code.Length;i++)
        {
            var op=code[i];
            if(op.Operand!=null&&protectedLocals.Contains(op.Operand))return false;
            if(LoadedValueType(op) is {} loaded)
            {
                if(!loaded.IsValueType||loaded.ContainsGenericParameter)return false;
                stack.Push(loaded);continue;
            }
            if(i+1<code.Length&&ReadOnlyValueField(op,code[i+1]))
            {stack.Push(((FieldReference)code[++i].Operand).FieldType);continue;}
            switch(op.OpCode.Code)
            {
                case Code.Ldc_I4:stack.Push(ts.Int32);break;
                case Code.Ldc_I8:stack.Push(ts.Int64);break;
                case Code.Ldc_R4:stack.Push(ts.Single);break;
                case Code.Ldc_R8:stack.Push(ts.Double);break;
                case Code.Conv_R4:case Code.Conv_R8:case Code.Conv_I4:case Code.Conv_U4:case Code.Conv_I8:case Code.Conv_U8:
                    if(Pop() is not {} cv||!Scalar(cv))return false;
                    stack.Push(op.OpCode.Code switch{Code.Conv_R4=>ts.Single,Code.Conv_R8=>ts.Double,
                        Code.Conv_I4=>ts.Int32,Code.Conv_U4=>ts.UInt32,Code.Conv_I8=>ts.Int64,_=>ts.UInt64});break;
                case Code.Add:case Code.Sub:case Code.Mul:case Code.Div:case Code.And:case Code.Or:case Code.Xor:
                    if(Pop() is not {} rhs||Pop() is not {} lhs||!Scalar(lhs)||!StackSame(lhs,rhs)||
                        op.OpCode.Code==Code.Div&&!Floating(lhs)||
                        op.OpCode.Code is Code.And or Code.Or or Code.Xor&&Floating(lhs))return false;
                    stack.Push(lhs);break;
                case Code.Shl:case Code.Shr:case Code.Shr_Un:
                    if(Pop() is not {} shift||StackKind(shift)!=3||Pop() is not {} number||StackKind(number) is not (2 or 3))return false;
                    stack.Push(number);break;
                case Code.Neg:
                    if(Pop() is not {} neg||!Scalar(neg))return false;stack.Push(neg);break;
                case Code.Newobj:
                    if(op.Operand is not MethodReference ctor||!ScalarValueConstructor(ctor))return false;
                    for(int j=ctor.Parameters.Count-1;j>=0;j--)if(Pop() is not {} item||!StackSame(item,ctor.Parameters[j].ParameterType))return false;
                    stack.Push(ctor.DeclaringType);break;
                case Code.Call:
                    if(op.Operand is not MethodReference call||!ScalarIntrinsic(call,listDefinition)||
                        Pop() is not {} arg||!StackSame(arg,call.Parameters[0].ParameterType))return false;
                    stack.Push(call.ReturnType);break;
                case Code.Stloc:case Code.Stloc_S:
                    if(op.Operand is not VariableDefinition dest||Pop() is not {} value||!StackSame(value,dest.VariableType)||stack.Count!=0)return false;
                    break;
                default:return false;
            }
        }
        return stack.Count==0;
    }

    private static bool Candidate(Instruction i) => i.OpCode.Code == Code.Ldfld &&
        i.Operand is FieldReference f && f.Name == "_items" && List(f.DeclaringType);

    internal static int Run(MethodBody body)
    {
        // Complete diamonds inside a protected region are permitted only
        // after proving every instruction and continuation share its scope.
        if (!body.Instructions.Any(Candidate)) return 0;
        var original = body.Instructions.Select(i => (i, i.OpCode, i.Operand)).ToArray();
        body.SimplifyMacros();
        int count = 0;
        foreach (Instruction candidate in body.Instructions.Where(Candidate).ToArray())
            if (TryFold(body, candidate) || TryFold(body, candidate, extended: true) || TryPreserveBranches(body, candidate)) count++;
        if (count == 0)
            foreach (var (i, opcode, operand) in original) { i.OpCode = opcode; i.Operand = operand; }
        return count;
    }

    private static bool TryFold(MethodBody body, Instruction candidate, bool extended = false)
    {
        var a = body.Instructions.ToArray();
        var ix = a.Select((i, n) => (i, n)).ToDictionary(x => x.i, x => x.n);
        int k = ix[candidate] - 1;
        if (k < 0 || k + Shape.Length > a.Length) return false;
        // The native scheduler may load the value from a typed public
        // instance field between loading _items and incrementing _version.
        // Keep this exact read and its original list-null-check ordering.
        static TypeReference? LoadType(Instruction i) => i.OpCode.Code switch
        {
            Code.Ldloc when i.Operand is VariableDefinition v => v.VariableType,
            Code.Ldarg when i.Operand is ParameterDefinition p => p.ParameterType,
            _ => null
        };
        bool Load(Instruction i) => i.OpCode.Code == Code.Ldloc || extended && i.OpCode.Code == Code.Ldarg;
        bool SameLoad(Instruction x, Instruction y) =>
            x.OpCode.Code == y.OpCode.Code && x.Operand == y.Operand;
        static bool FloatLocal(Instruction i) => i.Operand is VariableDefinition v &&
            v.VariableType.MetadataType == MetadataType.Single;
        bool ValueCompatible(TypeReference actual, TypeReference expected)
        {
            if (Same(actual, expected)) return true;
            // Object accepts an actual managed reference without boxing.
            // No guessed interface casts, array covariance or value-type conversion.
            if (!extended || expected.MetadataType != MetadataType.Object ||
                expected.Scope.Name is not ("mscorlib" or "System.Private.CoreLib") ||
                actual.IsValueType || actual.ContainsGenericParameter ||
                actual is ByReferenceType or PointerType or FunctionPointerType) return false;
            try { return actual.Resolve() is { IsValueType: false }; }
            catch (AssemblyResolutionException) { return false; }
        }

        int scheduled = k + Shape.Length + 3 <= a.Length &&
            Load(a[k+3]) &&
            (a[k+4].OpCode.Code == Code.Ldfld || extended && a[k+4].OpCode.Code == Code.Callvirt) &&
            a[k+5].OpCode.Code == Code.Stloc ? 3 : 0;
        if (scheduled == 0 && extended && k + 17 < a.Length &&
            a[k+3].OpCode.Code == Code.Ldloc && a[k+4].OpCode.Code == Code.Ldloc &&
            a[k+5].OpCode.Code == Code.Ldc_I4 &&
            a[k+6].OpCode.Code == Code.Conv_I8 && a[k+7].OpCode.Code == Code.Add &&
            a[k+8].OpCode.Code == Code.Conv_I4 && a[k+9].OpCode.Code == Code.Ldelem_Any &&
            a[k+10].OpCode.Code == Code.Stloc && SameLoad(a[k],a[k+11]) && SameLoad(a[k],a[k+12]) &&
            a[k+13].OpCode.Code == Code.Ldfld && a[k+13].Operand is FieldReference versionField && versionField.Name == "_version" &&
            Constant(a[k+14],1) && a[k+15].OpCode.Code == Code.Add &&
            a[k+16].OpCode.Code == Code.Stfld && a[k+16].Operand is FieldReference versionStore && versionStore.Name == "_version")
            scheduled = 8;
        int post = k+12+scheduled;
        // One proven nonthrowing, stack-balanced FP calculation. No calls,
        // field access, integer division, overflow checks, or address writes.
        int arithmetic = extended && post+8 <= a.Length &&
            a.Skip(post).Take(8).Select(i=>i.OpCode.Code).SequenceEqual(
                new[]{Code.Ldloc,Code.Ldloc,Code.Sub,Code.Conv_R4,Code.Ldloc,Code.Mul,Code.Conv_R4,Code.Stloc}) &&
            new[]{0,1,4,7}.All(n=>FloatLocal(a[post+n])) ? 8 : 0;
        var physical = a.Skip(k).Take(Shape.Length + scheduled + arithmetic).ToArray();
        var moved = physical.Skip(3).Take(scheduled).ToArray();
        var computed = physical.Skip(12+scheduled).Take(arithmetic).ToArray();
        var b = physical.Take(3).Concat(physical.Skip(3+scheduled).Take(9))
            .Concat(physical.Skip(12+scheduled+arithmetic)).ToArray();
        var listPositions = new[]{0,3,4,9,21};
        if (b.Length != Shape.Length ||
            !b.Select((i,n)=>i.OpCode.Code==Shape[n] ||
                extended && (listPositions.Contains(n)||n==28) && i.OpCode.Code==Code.Ldarg).All(x=>x) ||
            !Load(b[0]) || !Load(b[28]) ||
            LoadType(b[0]) is not GenericInstanceType gt || !List(gt) ||
            b[2].Operand is not VariableDefinition array ||
            b[11].Operand is not VariableDefinition size ||
            LoadType(b[28]) is not TypeReference valueType ||
            b[0].Operand == b[28].Operand || array == size ||
            b[0].Operand == array || b[0].Operand == size ||
            b[28].Operand == array || b[28].Operand == size ||
            array.VariableType is not ArrayType { IsVector: true } at ||
            !Same(at.ElementType, gt.GenericArguments[0]) ||
            size.VariableType.MetadataType != MetadataType.Int32 ||
            !ValueCompatible(valueType, gt.GenericArguments[0]) ||
            b[29].Operand is not TypeReference stored || !Same(stored, at.ElementType)) return false;
        object list=b[0].Operand, value=b[28].Operand;
        if (body.Method.DeclaringType.FullName == gt.ElementType.FullName &&
            body.Method.DeclaringType.Scope.Name == gt.ElementType.Scope.Name) return false;
        bool Local(VariableDefinition v, params int[] positions) => positions.All(n => b[n].Operand == v);
        if (!listPositions.All(n=>SameLoad(b[0],b[n])) || !Local(array, 12, 26) || !Local(size, 15, 22, 27) ||
            !Constant(b[6], 1) || !Constant(b[17], 0) || !Constant(b[23], 1) ||
            b[19].Operand is not Instruction slow || b[30].Operand is not Instruction join ||
            !ix.TryGetValue(slow, out int f) || f + 4 >= a.Length) return false;

        TypeDefinition? def;
        try { def = gt.ElementType.Resolve(); }
        catch (AssemblyResolutionException) { return false; }
        if (def == null || def.FullName != gt.ElementType.FullName ||
            def.Module.Assembly.Name.Name != gt.ElementType.Scope.Name ||
            def.GenericParameters.Count != 1) return false;

        // Resolve the exact original framework metadata. A same-named
        // user type or overloaded/altered method is not proof of List.Add.
        bool Field(Instruction i, string name, bool items = false)
        {
            if (i.Operand is not FieldReference field || field.Name != name || !Same(field.DeclaringType, gt)) return false;
            FieldDefinition? d;
            try { d = field.Resolve(); }
            catch (AssemblyResolutionException) { return false; }
            return d != null && d.DeclaringType == def && !d.IsStatic && (d.IsPrivate || d.IsAssembly) &&
                (items ? d.FieldType is ArrayType { IsVector: true } t && ElementParameter(t.ElementType, gt)
                       : d.FieldType.MetadataType == MetadataType.Int32);
        }
        if (!Field(b[1], "_items", true) || !Field(b[5], "_version") ||
            !Field(b[8], "_version") || !Field(b[25], "_size")) return false;
        MethodDefinition? Resolve(MethodReference m)
        {
            try { return m.Resolve(); }
            catch (AssemblyResolutionException) { return null; }
        }
        if (b[10].Operand is not MethodReference get || get.Name != "get_Count" ||
            !Same(get.DeclaringType, gt) || !get.HasThis || get.Parameters.Count != 0 ||
            get.ReturnType.MetadataType != MetadataType.Int32 ||
            Resolve(get) is not { IsPublic: true, IsStatic: false } countMethod || countMethod.DeclaringType != def) return false;

        if (scheduled == 3)
        {
            if (LoadType(moved[0]) is not TypeReference sourceType || moved[2].Operand is not VariableDefinition destination ||
                (!extended && moved[2].Operand != value) || new[]{list,(object)array,size}.Contains(destination) ||
                new[]{list,(object)array,size,value}.Contains(moved[0].Operand) ||
                sourceType.IsValueType || sourceType is ByReferenceType or PointerType) return false;
            if(moved[1].Operand is FieldReference field && moved[1].OpCode.Code==Code.Ldfld)
            {
                if (!Same(sourceType,field.DeclaringType) || !Same(field.FieldType,destination.VariableType)) return false;
                FieldDefinition? d;
                try { d = field.Resolve(); }
                catch (AssemblyResolutionException) { return false; }
                // Nested types share the containing type's private access.
                // Require that exact owner definition on the declaring-type
                // chain; a name match or unrelated enclosing type is not proof.
                bool inOwnerScope = false;
                for (TypeDefinition? context = body.Method.DeclaringType; context != null; context = context.DeclaringType)
                    if (context == d?.DeclaringType) { inOwnerScope = true; break; }
                if(d==null || d.IsStatic || (!d.IsPublic && !(extended && inOwnerScope)) ||
                    !Same(d.FieldType,destination.VariableType)) return false;
            }
            else if(extended && moved[1].OpCode.Code==Code.Callvirt &&
                moved[1].Operand is MethodReference countRead && List(sourceType) &&
                Same(countRead.DeclaringType,sourceType) && countRead.Name=="get_Count" &&
                countRead.HasThis && countRead.Parameters.Count==0 && countRead.ReturnType.MetadataType==MetadataType.Int32 &&
                destination.VariableType.MetadataType==MetadataType.Int32 &&
                Resolve(countRead) is {IsPublic:true,IsStatic:false} sourceCount &&
                sourceCount.DeclaringType.FullName==((GenericInstanceType)sourceType).ElementType.FullName &&
                AssemblyIdentity(sourceCount.DeclaringType)==AssemblyIdentity(sourceType))
            { /* Non-mutating exact List.Count; preserve its original exception order. */ }
            else return false;
        }
        else if (scheduled == 8)
        {
            if (!extended || arithmetic != 0 || !SafeArrayAppendSchedule(moved,list,array,size,value,gt.GenericArguments[0])) return false;
        }
        if (computed.Any(i=>i.Operand==list || i.Operand==array || i.Operand==size)) return false;
        var fb = a.Skip(f).Take(4).ToArray();
        if (fb[0].OpCode.Code != Code.Nop || !SameLoad(fb[1],b[0]) ||
            !SameLoad(fb[2],b[28]) ||
            fb[3].OpCode.Code != Code.Callvirt || fb[3].Operand is not MethodReference resize ||
            resize.Name != "AddWithResize" || !Same(resize.DeclaringType, gt) || !resize.HasThis ||
            resize.ReturnType.MetadataType != MetadataType.Void || resize.Parameters.Count != 1 ||
            !ElementParameter(resize.Parameters[0].ParameterType, gt) ||
            Resolve(resize) is not { IsPrivate: true, IsStatic: false } slowMethod ||
            slowMethod.DeclaringType != def) return false;

        // The emitter can lay out the slow arm as a fall-through or as
        // a separate basic block ending in a branch to the SAME join.
        // Do not consume arbitrary trailing computations or a leave.
        var slowTail = new System.Collections.Generic.List<Instruction>();
        if (a[f + 4] != join)
        {
            int end = f + 4;
            if (a[end].OpCode.Code == Code.Nop)
            {
                slowTail.Add(a[end++]);
                if (end >= a.Length) return false;
            }
            if (a[end].OpCode.Code != Code.Br || a[end].Operand != join) return false;
            slowTail.Add(a[end]);
        }
        var add = def.Methods.Where(m => m.Name == "Add" && m.IsPublic && !m.IsStatic &&
            !m.HasGenericParameters && m.ReturnType.MetadataType == MetadataType.Void &&
            m.Parameters.Count == 1 && ElementParameter(m.Parameters[0].ParameterType, gt)).ToArray();
        if (add.Length != 1) return false;
        var addRef = new MethodReference("Add", resize.ReturnType, resize.DeclaringType)
            { HasThis = true, CallingConvention = resize.CallingConvention };
        addRef.Parameters.Add(new ParameterDefinition(resize.Parameters[0].ParameterType));
        if (Resolve(addRef) != add[0]) return false;

        var region = physical.Concat(fb).Concat(slowTail).ToHashSet();
        if (region.Count != Shape.Length + scheduled + arithmetic + 4 + slowTail.Count || region.Contains(join) || !ix.ContainsKey(join) || region.Contains(a[0]) && a[0] != b[0]) return false;
        // No exception-region boundary may be moved or erased. Compare
        // each region's complete try/handler/filter membership against
        // the original entry, including the common continuation.
        foreach (var h in body.ExceptionHandlers)
        {
            var boundaries = new[] { h.TryStart,h.TryEnd,h.HandlerStart,h.HandlerEnd,h.FilterStart };
            if (boundaries.Any(t=>t!=null&&region.Contains(t))) return false;
            bool Inside(Instruction i, Instruction? start, Instruction? end) =>
                start != null && ix[i]>=ix[start] && (end==null || ix[i]<ix[end]);
            int Scope(Instruction i) =>
                (Inside(i,h.TryStart,h.TryEnd)?1:0) |
                (Inside(i,h.HandlerStart,h.HandlerEnd)?2:0) |
                (Inside(i,h.FilterStart,h.HandlerStart)?4:0);
            int expected = Scope(b[0]);
            if ((expected & 4)!=0 || region.Any(i=>Scope(i)!=expected) || Scope(join)!=expected) return false;
        }
        // Do not admit implicit entry to the slow arm by fall-through
        // from an unrelated instruction, or an outside jump into either arm.
        if (f == 0 || (a[f - 1].OpCode.FlowControl is not (FlowControl.Branch or FlowControl.Return or FlowControl.Throw))) return false;
        foreach (var i in a)
        {
            if ((i.OpCode.Code is Code.Ldloca or Code.Ldarga) && new object[] { list, array, size, value }.Contains(i.Operand)) return false;
            if (i.OpCode.Code==Code.Starg && (i.Operand==list || i.Operand==value)) return false;
            if (region.Contains(i)) continue;
            if (i.Operand == array || i.Operand == size) return false;
            if (i.Operand is Instruction target && target != b[0] && region.Contains(target)) return false;
            if (i.Operand is Instruction[] targets && targets.Any(t => t != b[0] && region.Contains(t))) return false;
        }
        // Both original paths do exactly one version increment, then
        // append at old size or call the framework resize helper. The
        // public Add(T) implements that same operation, on the same locals.
        object? savedSource=scheduled!=0?moved[0].Operand:null;
        object? savedField=scheduled!=0?moved[1].Operand:null;
        if (extended)
        {
            // Keep both scheduled regions at their original positions.
            // Before any potentially throwing pre-version read, reproduce
            // the list null check with the proven nonmutating Count getter.
            // The only post-version schedule accepted above is pure FP
            // arithmetic, so moving the single Add after it cannot expose
            // an exception or callback between the original mutations.
            var listOp=b[0].OpCode;var valueOp=b[28].OpCode;
            var keep=moved.Concat(computed).ToHashSet();
            foreach(var i in region) if(!keep.Contains(i)){i.OpCode=OpCodes.Nop;i.Operand=null;}
            if(scheduled!=0 || arithmetic!=0)
            {
                b[0].OpCode=listOp;b[0].Operand=list;
                b[1].OpCode=OpCodes.Callvirt;b[1].Operand=get;
                b[2].OpCode=OpCodes.Pop;
            }
            b[12].OpCode=listOp;b[12].Operand=list;
            b[13].OpCode=valueOp;b[13].Operand=value;
            b[14].OpCode=OpCodes.Callvirt;b[14].Operand=addRef;
            b[15].OpCode=OpCodes.Br;b[15].Operand=join;
            return true;
        }
        foreach (var i in region) { i.OpCode = OpCodes.Nop; i.Operand = null; }
        int w = 0;
        void Put(OpCode op, object? operand = null)
        {
            physical[w].OpCode = op;
            physical[w++].Operand = operand;
        }
        if (scheduled != 0)
        {
            Put(OpCodes.Ldloc, list);
            Put(OpCodes.Callvirt, get);
            Put(OpCodes.Pop);
            // Preserve old canonical emitted form (the legacy matcher
            // already proved this source field and destination local).
            Put(OpCodes.Ldloc, savedSource);
            Put(OpCodes.Ldfld, savedField);
            Put(OpCodes.Stloc, value);
        }
        Put(OpCodes.Ldloc, list);
        Put(OpCodes.Ldloc, value);
        Put(OpCodes.Callvirt, addRef);
        Put(OpCodes.Br, join);
        return true;
    }

    // A fallback for complete diamonds whose branches have their own
    // initialized element temporaries or different continuation loads.
    // Preserve the capacity decision and both original arms. Only replace
    // the framework internals with public Capacity, Count and Add.
    private static bool TryPreserveBranches(MethodBody body,Instruction candidate)
    {
        // Protected regions require a separate proof of exceptional exits.
        if(body.HasExceptionHandlers)return false;
        var a=body.Instructions.ToArray();
        var ix=a.Select((i,n)=>(i,n)).ToDictionary(x=>x.i,x=>x.n);
        int k=ix[candidate]-1;
        if(k<0||k+30>=a.Length)return false;
        static TypeReference? LoadType(Instruction i)=>i.OpCode.Code switch
        {
            Code.Ldloc or Code.Ldloc_S when i.Operand is VariableDefinition v=>v.VariableType,
            Code.Ldarg or Code.Ldarg_S when i.Operand is ParameterDefinition p=>p.ParameterType,
            _=>null
        };
        var receiver=a[k];
        if(LoadType(receiver) is not GenericInstanceType gt||!List(gt)||
           a[k+2].OpCode.Code is not (Code.Stloc or Code.Stloc_S)||a[k+2].Operand is not VariableDefinition array||
           array.VariableType is not ArrayType{IsVector:true} at||!Same(at.ElementType,gt.GenericArguments[0]))return false;
        var element=gt.GenericArguments[0];
        bool Receiver(Instruction i)=>i.Operand==receiver.Operand&&
            (receiver.OpCode.Code is Code.Ldloc or Code.Ldloc_S ? i.OpCode.Code is Code.Ldloc or Code.Ldloc_S :
             receiver.OpCode.Code is Code.Ldarg or Code.Ldarg_S ? i.OpCode.Code is Code.Ldarg or Code.Ldarg_S :
             i.OpCode.Code==receiver.OpCode.Code);
        bool Local(Instruction i,Code c,VariableDefinition v)=>i.Operand==v&&
            (c==Code.Ldloc ? i.OpCode.Code is Code.Ldloc or Code.Ldloc_S :
             c==Code.Stloc ? i.OpCode.Code is Code.Stloc or Code.Stloc_S : i.OpCode.Code==c);
        TypeDefinition? def;
        try{def=gt.ElementType.Resolve();}catch(AssemblyResolutionException){return false;}
        if(def==null||!Same(def,gt.ElementType)||def.GenericParameters.Count!=1||
           Same(body.Method.DeclaringType,def))return false;
        bool Field(Instruction i,Code op,string name,bool items=false)
        {
            if(i.OpCode.Code!=op||i.Operand is not FieldReference f||f.Name!=name||!Same(f.DeclaringType,gt))return false;
            FieldDefinition? d;try{d=f.Resolve();}catch(AssemblyResolutionException){return false;}
            return d!=null&&d.DeclaringType==def&&!d.IsStatic&&(d.IsPrivate||d.IsAssembly)&&
                (items?d.FieldType is ArrayType{IsVector:true} t&&ElementParameter(t.ElementType,gt):d.FieldType.MetadataType==MetadataType.Int32);
        }
        MethodDefinition? Resolve(MethodReference m){try{return m.Resolve();}catch(AssemblyResolutionException){return null;}}
        if(!Field(candidate,Code.Ldfld,"_items",true))return false;

        // The optional schedule before the version increment may contain
        // a complete, typed array read or a field read. Keep it in place,
        // including its original exceptions. Only the exact BCL List getters
        // or the separately proven nonthrowing scalar schedule are allowed.
        int n=k+3;
        while(n+6<a.Length&&n-k<=256&&!(Receiver(a[n])&&Receiver(a[n+1])&&Field(a[n+2],Code.Ldfld,"_version")))
            n++;
        if(n-k>256||n+30>=a.Length||!Receiver(a[n])||!Receiver(a[n+1])||!Field(a[n+2],Code.Ldfld,"_version")||
           !Constant(a[n+3],1)||a[n+4].OpCode.Code!=Code.Add||!Field(a[n+5],Code.Stfld,"_version"))return false;
        var scheduled=a.Skip(k+3).Take(n-k-3).ToArray();

        // A bounded stack/type interpreter for read-only pre-version
        // schedules. Integer arithmetic is unchecked, array accesses
        // preserve their exceptions; the list's original null check
        // occurs first. All stores are to unrelated locals.
        var stack=new Stack<TypeReference>();
        TypeReference? Pop()=>stack.TryPop(out var v)?v:null;
        bool IsInt(TypeReference t)=>t.MetadataType is MetadataType.Int32 or MetadataType.Int64 or MetadataType.UInt32 or MetadataType.UInt64;
        bool RefAssignable(TypeReference source,TypeReference target)
        {
            if(Same(source,target))return true;
            if(source.IsValueType||target.IsValueType||source is TypeSpecification||target is TypeSpecification)return false;
            try
            {
                var seen=new HashSet<string>();TypeDefinition? d=source.Resolve();
                while(d!=null&&seen.Add(d.FullName))
                {if(Same(d,target))return true;d=d.BaseType?.Resolve();}
            }
            catch(AssemblyResolutionException){}
            return false;
        }
        foreach(var ins in SafePostVersionSchedule(scheduled,def,body.Method.Module.TypeSystem,receiver.Operand,array)?Array.Empty<Instruction>():scheduled)
        {
            if(ins.Operand==receiver.Operand||ins.Operand==array)return false;
            if(LoadType(ins) is {} load){stack.Push(load);continue;}
            switch(ins.OpCode.Code)
            {
                case Code.Ldc_I4:stack.Push(body.Method.Module.TypeSystem.Int32);break;
                case Code.Ldc_I8:stack.Push(body.Method.Module.TypeSystem.Int64);break;
                case Code.Conv_I4:case Code.Conv_I8:
                    if(Pop() is not {} converted||!IsInt(converted))return false;
                    stack.Push(ins.OpCode.Code==Code.Conv_I4?body.Method.Module.TypeSystem.Int32:body.Method.Module.TypeSystem.Int64);break;
                case Code.Add:case Code.Sub:
                    if(Pop() is not {} right||Pop() is not {} left||!IsInt(left)||!IsInt(right)||!Same(left,right))return false;
                    stack.Push(left);break;
                case Code.Ldlen:
                    if(Pop() is not ArrayType{IsVector:true})return false;
                    // The immediately following Conv_I4 in emitted shapes
                    // restores the original array length to int.
                    stack.Push(body.Method.Module.TypeSystem.Int64);break;
                case Code.Ldelem_Any:
                    if(Pop() is not {} index||index.MetadataType!=MetadataType.Int32||
                       Pop() is not ArrayType{IsVector:true} arr||ins.Operand is not TypeReference et||!Same(et,arr.ElementType))return false;
                    stack.Push(et);break;
                case Code.Ldfld:
                    if(Pop() is not {} owner||ins.Operand is not FieldReference fr||
                       !RefAssignable(owner,fr.DeclaringType))return false;
                    FieldDefinition? fd;try{fd=fr.Resolve();}catch(AssemblyResolutionException){return false;}
                    if(fd==null||fd.IsStatic||(!fd.IsPublic&&fd.DeclaringType!=body.Method.DeclaringType)||
                       fr.FieldType.ContainsGenericParameter)return false;
                    stack.Push(fr.FieldType);break;
                case Code.Callvirt:
                    if(ins.Operand is not MethodReference cr||!cr.HasThis||cr.HasGenericParameters||cr is GenericInstanceMethod)return false;
                    bool item=cr.Name=="get_Item"&&cr.Parameters.Count==1&&
                        cr.Parameters[0].ParameterType.MetadataType==MetadataType.Int32;
                    if(item)
                    {if(Pop() is not {} indexValue||indexValue.MetadataType!=MetadataType.Int32)return false;}
                    else if(cr.Name!="get_Count"||cr.Parameters.Count!=0||cr.ReturnType.MetadataType!=MetadataType.Int32)return false;
                    if(Pop() is not GenericInstanceType cg||!List(cg)||!Same(cr.DeclaringType,cg)||
                       Resolve(cr) is not {IsPublic:true,IsStatic:false} cm||
                       (cm.IsVirtual&&!cm.IsFinal)||!Same(cm.DeclaringType,cg.ElementType)||item&&!ElementParameter(cr.ReturnType,cg))return false;
                    stack.Push(item?cg.GenericArguments[0]:cr.ReturnType);break;
                case Code.Stloc:
                    if(ins.Operand is not VariableDefinition dest||Pop() is not {} val||
                       !Same(val,dest.VariableType)||stack.Count!=0)return false;
                    break;
                default:return false;
            }
        }
        if(stack.Count!=0)return false;
        bool CountAt(int c)=>c+2<a.Length&&Receiver(a[c])&&a[c+1].OpCode.Code==Code.Callvirt&&
              a[c+1].Operand is MethodReference countCandidate&&
              Same(countCandidate.DeclaringType,gt)&&countCandidate.Name=="get_Count"&&countCandidate.HasThis&&
              !countCandidate.HasGenericParameters&&countCandidate is not GenericInstanceMethod&&
              countCandidate.Parameters.Count==0&&countCandidate.ReturnType.MetadataType==MetadataType.Int32&&
              a[c+2].OpCode.Code is Code.Stloc or Code.Stloc_S;
        int c=n+6;
        while(c+2<a.Length&&c-(n+6)<=256&&!CountAt(c))c++;
        if(c-(n+6)>256||!CountAt(c)||a[c+1].Operand is not MethodReference get||
           Resolve(get) is not {IsPublic:true,IsStatic:false} countMethod||countMethod.DeclaringType!=def||
           a[c+2].Operand is not VariableDefinition size||size.VariableType.MetadataType!=MetadataType.Int32||
           scheduled.Any(i=>i.Operand==size))return false;
        var afterVersionSchedule=a.Skip(n+6).Take(c-(n+6)).ToArray();
        if(!SafePostVersionSchedule(afterVersionSchedule,def,body.Method.Module.TypeSystem,receiver.Operand,array,size))return false;
        bool CapacityBranchAt(int b)=>b+7<a.Length&&Local(a[b],Code.Ldloc,array)&&
              a[b+1].OpCode.Code==Code.Ldlen&&a[b+2].OpCode.Code==Code.Conv_I4&&
              Local(a[b+3],Code.Ldloc,size)&&a[b+4].OpCode.Code==Code.Cgt_Un&&Constant(a[b+5],0)&&
              a[b+6].OpCode.Code==Code.Ceq&&a[b+7].OpCode.Code==Code.Brtrue;
        int b=c+3;
        while(b+7<a.Length&&b-(c+3)<=256&&!CapacityBranchAt(b))b++;
        var afterCountSchedule=a.Skip(c+3).Take(b-(c+3)).ToArray();
        if(b-(c+3)>256||!CapacityBranchAt(b)||!SafePostVersionSchedule(afterCountSchedule,def,body.Method.Module.TypeSystem,receiver.Operand,array,size)||
           a[b+7].Operand is not Instruction slow||!ix.TryGetValue(slow,out int f)||f<=b+16||f>=a.Length-4)return false;
        int fast=b+8;
        if(a[fast].OpCode.Code!=Code.Nop||!Receiver(a[fast+1])||!Local(a[fast+2],Code.Ldloc,size)||
           !Constant(a[fast+3],1)||a[fast+4].OpCode.Code!=Code.Add||!Field(a[fast+5],Code.Stfld,"_size")||
           !Local(a[fast+6],Code.Ldloc,array)||!Local(a[fast+7],Code.Ldloc,size))return false;
        int v=fast+8,store;
        VariableDefinition? fastTemp=null,slowTemp=null,slowCopy=null;
        Instruction? fastValue=null;
        Instruction[]? constructedValue=null;
        bool ConstructedAt(int at,out Instruction[]? expression)
        {
            expression=null;
            int q=at;
            while(q<a.Length&&q-at<4&&LoadedValueType(a[q]) is {} t&&t.MetadataType==MetadataType.Single)q++;
            if(q>=a.Length||a[q].OpCode.Code!=Code.Newobj||a[q].Operand is not MethodReference ctor||
               !Same(ctor.DeclaringType,element)||!ScalarValueConstructor(ctor)||ctor.Parameters.Count!=q-at)return false;
            expression=a.Skip(at).Take(q-at+1).ToArray();return true;
        }
        bool SameValueExpression(Instruction[] left,int right)
        {
            if(right+left.Length>a.Length)return false;
            for(int q=0;q<left.Length;q++)
            {
                var x=left[q];var y=a[right+q];
                if(x.OpCode.Code!=y.OpCode.Code)return false;
                if(x.Operand==y.Operand)continue;
                if(x.Operand is not MethodReference xm||y.Operand is not MethodReference ym||
                   !Same(xm.DeclaringType,ym.DeclaringType)||xm.FullName!=ym.FullName||Resolve(xm)!=Resolve(ym))return false;
            }
            return true;
        }
        bool DefaultAt(int i,out VariableDefinition? local)
        {
            local=null;
            if(i+2>=a.Length||a[i].OpCode.Code!=Code.Ldloca||a[i].Operand is not VariableDefinition t||
               !element.IsValueType||!Same(t.VariableType,element)||a[i+1].OpCode.Code!=Code.Initobj||
               a[i+1].Operand is not TypeReference ty||!Same(ty,element)||!Local(a[i+2],Code.Ldloc,t))return false;
            local=t;return true;
        }
        if(DefaultAt(v,out fastTemp))store=v+3;
        else if(LoadType(a[v]) is {} vt&&Same(vt,element)){fastValue=a[v];store=v+1;}
        else if(ConstructedAt(v,out constructedValue))store=v+constructedValue!.Length;
        else return false;
        if(store>=f||a[store].OpCode.Code!=Code.Stelem_Any||a[store].Operand is not TypeReference st||!Same(st,element))return false;
        // Preserve only straight-line continuation loads/stores in the
        // fast arm before its original unconditional join.
        int end=store+1;
        while(end+1<f&&LoadType(a[end]) is {} type&&a[end+1].OpCode.Code==Code.Stloc&&
              a[end+1].Operand is VariableDefinition dst&&Same(type,dst.VariableType)&&dst!=size&&dst!=array&&dst!=receiver.Operand)end+=2;
        if(end>=a.Length||a[end].OpCode.Code!=Code.Br||a[end].Operand is not Instruction join||
           !ix.TryGetValue(join,out int j)||end>=f||j<=f||a[f].OpCode.Code!=Code.Nop)return false;
        int si=f+1;
        if(fastTemp!=null)
        {
            if(si+3>=a.Length||!DefaultAt(si,out slowTemp)||slowTemp==fastTemp||a[si+3].OpCode.Code!=Code.Stloc||
               a[si+3].Operand is not VariableDefinition copy||!Same(copy.VariableType,element)||
               copy==slowTemp||copy==fastTemp||copy==array||copy==size)return false;
            slowCopy=copy;si+=4;
        }
        int resizeAt=si+1+(constructedValue?.Length??1);
        bool sameValue=constructedValue!=null?SameValueExpression(constructedValue,si+1):
            si+1<a.Length&&LoadType(a[si+1]) is {} sv&&Same(sv,element)&&
            (fastTemp!=null?Local(a[si+1],Code.Ldloc,slowCopy!):
             a[si+1].OpCode.Code==fastValue!.OpCode.Code&&a[si+1].Operand==fastValue.Operand);
        if(resizeAt>=j||!Receiver(a[si])||!sameValue||
           a[resizeAt].OpCode.Code!=Code.Callvirt||a[resizeAt].Operand is not MethodReference resize||
           resize.Name!="AddWithResize"||!Same(resize.DeclaringType,gt)||!resize.HasThis||
           resize.ReturnType.MetadataType!=MetadataType.Void||resize.Parameters.Count!=1||
           !ElementParameter(resize.Parameters[0].ParameterType,gt)||
           Resolve(resize) is not {IsPrivate:true,IsStatic:false} rm||rm.DeclaringType!=def)return false;
        // Slow tail may read a field of the exact receiver's owning class
        // and store a local. Both continuations stay as originally emitted.
        // No unknown call or control flow in the matched region.
        int e=resizeAt+1;
        while(e<j)
        {
            if(a[e].OpCode.Code==Code.Nop){e++;continue;}
            if(e+2<j&&LoadType(a[e]) is {} own&&a[e+1].OpCode.Code==Code.Ldfld&&
               a[e+1].Operand is FieldReference rf&&Same(own,rf.DeclaringType)&&
               a[e+2].OpCode.Code==Code.Stloc&&a[e+2].Operand is VariableDefinition rd&&
               Same(rd.VariableType,rf.FieldType)&&rd!=array&&rd!=size&&rd!=receiver.Operand){e+=3;continue;}
            if(e+1<j&&LoadType(a[e]) is {} ot&&a[e+1].OpCode.Code==Code.Stloc&&
               a[e+1].Operand is VariableDefinition od&&Same(od.VariableType,ot)&&od!=array&&od!=size&&od!=receiver.Operand){e+=2;continue;}
            if(e==j-1&&a[e].OpCode.Code==Code.Br&&a[e].Operand==join){e++;continue;}
            return false;
        }
        var region=a.Skip(k).Take(end-k+1).Concat(a.Skip(f).Take(j-f)).ToHashSet();
        foreach(var i in a)
        {
            if((i.OpCode.Code is Code.Ldloca or Code.Ldloca_S or Code.Ldarga or Code.Ldarga_S)&&
                (i.Operand==array||i.Operand==size||i.Operand==receiver.Operand||
                 (i.Operand==fastValue?.Operand&&
                    (i.Next==null||!ReadOnlyValueField(i,i.Next)||
                     (region.Contains(i)&&!scheduled.Contains(i)&&!afterCountSchedule.Contains(i)&&!afterVersionSchedule.Contains(i))))||
                 (i.Operand==fastTemp||i.Operand==slowTemp)&&i!=a[v]&&i!=a[f+1])){return false;}
            if(!region.Contains(i)&&(i.Operand==array||i.Operand==size)){return false;}
            if(i.OpCode.Code==Code.Starg&&(i.Operand==receiver.Operand||i.Operand==fastValue?.Operand)){return false;}
            if(!region.Contains(i)&&i.Operand is Instruction target&&target!=receiver&&region.Contains(target)){return false;}
            if(!region.Contains(i)&&i.Operand is Instruction[] ts&&ts.Any(t=>t!=receiver&&region.Contains(t))){return false;}
            // The only interior branch targets are the original capacity
            // decision's slow arm and the common join.
            if(region.Contains(i)&&i.Operand is Instruction target2&&region.Contains(target2)&&
               !(i==a[b+7]&&target2==slow)){return false;}
        }
        var adds=def.Methods.Where(m=>m.Name=="Add"&&m.IsPublic&&!m.IsStatic&&!m.HasGenericParameters&&
            m.ReturnType.MetadataType==MetadataType.Void&&m.Parameters.Count==1&&ElementParameter(m.Parameters[0].ParameterType,gt)).ToArray();
        var caps=def.Methods.Where(m=>m.Name=="get_Capacity"&&m.IsPublic&&!m.IsStatic&&!m.HasGenericParameters&&
            m.ReturnType.MetadataType==MetadataType.Int32&&m.Parameters.Count==0).ToArray();
        if(adds.Length!=1||caps.Length!=1)return false;
        var addRef=new MethodReference("Add",resize.ReturnType,gt){HasThis=true,CallingConvention=resize.CallingConvention};
        addRef.Parameters.Add(new ParameterDefinition(resize.Parameters[0].ParameterType));
        var capRef=new MethodReference("get_Capacity",caps[0].ReturnType,gt){HasThis=true,CallingConvention=caps[0].CallingConvention};
        if(Resolve(addRef)!=adds[0]||Resolve(capRef)!=caps[0])return false;
        // Keep the original array local for metadata stability, but never
        // read or write it after this transformation. Capture Capacity
        // before any scheduled read, preserving the original null check.
        var cap=new VariableDefinition(body.Method.Module.TypeSystem.Int32);
        body.Variables.Add(cap);
        void Nop(Instruction i){i.OpCode=OpCodes.Nop;i.Operand=null;}
        candidate.OpCode=OpCodes.Callvirt;candidate.Operand=capRef;a[k+2].Operand=cap;
        foreach(var i in a.Skip(n).Take(6))Nop(i);
        a[b].Operand=cap;Nop(a[b+1]);Nop(a[b+2]);
        foreach(var i in a.Skip(fast+1).Take(5))Nop(i);
        a[fast+6].OpCode=receiver.OpCode;a[fast+6].Operand=receiver.Operand;Nop(a[fast+7]);
        a[store].OpCode=OpCodes.Callvirt;a[store].Operand=addRef;
        a[resizeAt].Operand=addRef; return true;
    }
}
