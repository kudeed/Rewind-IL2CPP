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
            if (TryFold(body, candidate)) count++;
        if (count == 0)
            foreach (var (i, opcode, operand) in original) { i.OpCode = opcode; i.Operand = operand; }
        return count;
    }

    private static bool TryFold(MethodBody body, Instruction candidate)
    {
        var a = body.Instructions.ToArray();
        var ix = a.Select((i, n) => (i, n)).ToDictionary(x => x.i, x => x.n);
        int k = ix[candidate] - 1;
        if (k < 0 || k + Shape.Length > a.Length) return false;
        // The native scheduler may load the value from a typed public
        // instance field between loading _items and incrementing _version.
        // Keep this exact read and its original list-null-check ordering.
        int scheduled = k + Shape.Length + 3 <= a.Length &&
            a[k+3].OpCode.Code == Code.Ldloc &&
            a[k+4].OpCode.Code == Code.Ldfld &&
            a[k+5].OpCode.Code == Code.Stloc ? 3 : 0;
        var physical = a.Skip(k).Take(Shape.Length + scheduled).ToArray();
        var moved = physical.Skip(3).Take(scheduled).ToArray();
        var b = physical.Take(3).Concat(physical.Skip(3 + scheduled)).ToArray();
        if (!b.Select(i => i.OpCode.Code).SequenceEqual(Shape) ||
            b[0].Operand is not VariableDefinition list ||
            b[2].Operand is not VariableDefinition array ||
            b[11].Operand is not VariableDefinition size ||
            b[28].Operand is not VariableDefinition value ||
            new[] { list, array, size, value }.Distinct().Count() != 4 ||
            list.VariableType is not GenericInstanceType gt || !List(gt) ||
            array.VariableType is not ArrayType { IsVector: true } at ||
            !Same(at.ElementType, gt.GenericArguments[0]) ||
            size.VariableType.MetadataType != MetadataType.Int32 ||
            !Same(value.VariableType, gt.GenericArguments[0]) ||
            b[29].Operand is not TypeReference stored || !Same(stored, at.ElementType)) return false;
        if (body.Method.DeclaringType.FullName == gt.ElementType.FullName &&
            body.Method.DeclaringType.Scope.Name == gt.ElementType.Scope.Name) return false;
        bool Local(VariableDefinition v, params int[] positions) => positions.All(n => b[n].Operand == v);
        if (!Local(list, 3, 4, 9, 21) || !Local(array, 12, 26) || !Local(size, 15, 22, 27) ||
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

        VariableDefinition? readFrom = null;
        FieldReference? readField = null;
        if (scheduled != 0)
        {
            if (moved[0].Operand is not VariableDefinition source ||
                moved[1].Operand is not FieldReference field ||
                moved[2].Operand != value || new[] { list, array, size, value }.Contains(source) ||
                source.VariableType.IsValueType || source.VariableType is ByReferenceType or PointerType ||
                !Same(source.VariableType, field.DeclaringType) ||
                !Same(field.FieldType, value.VariableType)) return false;
            FieldDefinition? d;
            try { d = field.Resolve(); }
            catch (AssemblyResolutionException) { return false; }
            if (d == null || !d.IsPublic || d.IsStatic || !Same(d.FieldType, value.VariableType)) return false;
            readFrom = source; readField = field;
        }
        var fb = a.Skip(f).Take(4).ToArray();
        if (fb[0].OpCode.Code != Code.Nop || fb[1].OpCode.Code != Code.Ldloc || fb[1].Operand != list ||
            fb[2].OpCode.Code != Code.Ldloc || fb[2].Operand != value ||
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
        if (region.Count != Shape.Length + scheduled + 4 + slowTail.Count || region.Contains(join) || !ix.ContainsKey(join) || region.Contains(a[0]) && a[0] != b[0]) return false;
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
            if (i.OpCode.Code == Code.Ldloca && new object[] { list, array, size, value }.Contains(i.Operand)) return false;
            if (region.Contains(i)) continue;
            if (i.Operand == array || i.Operand == size) return false;
            if (i.Operand is Instruction target && target != b[0] && region.Contains(target)) return false;
            if (i.Operand is Instruction[] targets && targets.Any(t => t != b[0] && region.Contains(t))) return false;
        }
        // Both original paths do exactly one version increment, then
        // append at old size or call the framework resize helper. The
        // public Add(T) implements that same operation, on the same locals.
        foreach (var i in region) { i.OpCode = OpCodes.Nop; i.Operand = null; }
        int w = 0;
        void Put(OpCode op, object? operand = null)
        {
            physical[w].OpCode = op;
            physical[w++].Operand = operand;
        }
        if (scheduled != 0)
        {
            // Count is the exact public, non-mutating framework accessor.
            // Preserve the original list-null check before the field read;
            // _items is otherwise a private implementation detail.
            Put(OpCodes.Ldloc, list);
            Put(OpCodes.Callvirt, get);
            Put(OpCodes.Pop);
            Put(OpCodes.Ldloc, readFrom);
            Put(OpCodes.Ldfld, readField);
            Put(OpCodes.Stloc, value);
        }
        Put(OpCodes.Ldloc, list);
        Put(OpCodes.Ldloc, value);
        Put(OpCodes.Callvirt, addRef);
        Put(OpCodes.Br, join);
        return true;
    }
}
