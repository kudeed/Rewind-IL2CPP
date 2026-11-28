using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Rewind.Output;

internal static partial class ListAppendIlFolding
{
    private sealed record CopyValue(TypeReference Type, object? Root = null, FieldDefinition[]? Path = null)
    {
        internal bool Address => Root != null;
    }

    // Value-copy coverage is by the resolved CLR fields, never names or guessed byte sizes. A whole typed
    // field copy covers that value, including a possible explicit-layout payload. Partial coverage must
    // descend only through non-overlapping value definitions. No value may contain a managed reference.
    private static bool CopyData(TypeReference type, HashSet<string>? visiting = null, int depth = 0)
    {
        if (Scalar(type) || type.MetadataType is MetadataType.Boolean or MetadataType.Char) return true;
        if (!type.IsValueType || type.ContainsGenericParameter || type is TypeSpecification || depth > 12) return false;
        TypeDefinition? definition;
        try { definition = type.Resolve(); }
        catch (AssemblyResolutionException) { return false; }
        catch (ResolutionException) { return false; }
        if (definition == null || !Same(definition, type)) return false;
        var fields = definition.Fields.Where(f => !f.IsStatic).ToArray();
        if (fields.Length is 0 or > 64) return false;
        visiting ??= [];
        string key = AssemblyIdentity(type) + ":" + type.FullName;
        if (!visiting.Add(key)) return false;
        bool valid = fields.All(f => CopyData(f.FieldType, visiting, depth + 1));
        visiting.Remove(key);
        return valid;
    }

    private static bool CopyField(FieldReference field, TypeReference owner, out FieldDefinition definition)
    {
        definition = null!;
        if (!Same(field.DeclaringType, owner) || !CopyData(field.FieldType)) return false;
        FieldDefinition? found;
        try { found = field.Resolve(); }
        catch (AssemblyResolutionException) { return false; }
        catch (ResolutionException) { return false; }
        if (found is not { IsStatic: false, IsPublic: true, IsInitOnly: false } ||
            !Same(found.DeclaringType, owner) || !Same(found.FieldType, field.FieldType)) return false;
        definition = found;
        return true;
    }

    private static bool CompleteCopy(TypeReference type, List<FieldDefinition[]> written,
        FieldDefinition[]? path = null, int depth = 0)
    {
        path ??= [];
        if (written.Any(p => p.SequenceEqual(path))) return true;
        if (depth > 12 || !type.IsValueType || type is TypeSpecification || type.ContainsGenericParameter ||
            Scalar(type) || type.MetadataType is MetadataType.Boolean or MetadataType.Char) return false;
        TypeDefinition? definition;
        try { definition = type.Resolve(); }
        catch (AssemblyResolutionException) { return false; }
        catch (ResolutionException) { return false; }
        if (definition == null || definition.IsExplicitLayout || !Same(definition, type)) return false;
        var fields = definition.Fields.Where(f => !f.IsStatic).ToArray();
        return fields.Length is > 0 and <= 64 && fields.All(f => f.IsPublic && !f.IsInitOnly &&
            CompleteCopy(f.FieldType, written, [.. path, f], depth + 1));
    }

    // Interpret only nonthrowing, typed value computations. Managed addresses can name an unrelated value
    // local or this append's exact array element. They are consumed by value-field operations or initobj;
    // they cannot be stored, returned, passed to a call, used arithmetically, or read from the append target.
    private static bool ValueCopySchedule(Instruction[] a, int first, int end, TypeDefinition listDefinition,
        TypeSystem types, TypeReference element, VariableDefinition array, VariableDefinition size,
        object receiver, bool destination, out List<int> roots, out List<FieldDefinition[]> written)
    {
        roots = []; written = [];
        object target = new();
        var stack = new Stack<CopyValue>();
        CopyValue? Pop() => stack.TryPop(out var value) ? value : null;
        bool Protected(object? operand) => operand == receiver || operand == array || operand == size;
        bool Local(Instruction instruction, Code code, VariableDefinition variable) =>
            instruction.OpCode.Code == code && instruction.Operand == variable;
        if (first < 0 || end < first || end > a.Length || end - first > 1024) return false;
        for (int i = first; i < end; i++)
        {
            Instruction instruction = a[i];
            if (destination && i + 2 < end && Local(instruction, Code.Ldloc, array) &&
                Local(a[i + 1], Code.Ldloc, size) && a[i + 2].OpCode.Code == Code.Ldelema &&
                a[i + 2].Operand is TypeReference addressed && Same(addressed, element))
            {
                stack.Push(new CopyValue(element, target, []));
                roots.Add(i); i += 2; continue;
            }
            if (instruction.Operand != null && Protected(instruction.Operand)) return false;
            if (LoadedValueType(instruction) is { } loaded)
            {
                if (!CopyData(loaded)) return false;
                stack.Push(new CopyValue(loaded)); continue;
            }
            switch (instruction.OpCode.Code)
            {
                case Code.Nop: break;
                case Code.Ldloca:
                    if (instruction.Operand is not VariableDefinition local || !CopyData(local.VariableType)) return false;
                    stack.Push(new CopyValue(local.VariableType, local, [])); break;
                case Code.Ldflda:
                    if (instruction.Operand is not FieldReference addressField || Pop() is not { Address: true } parent ||
                        !CopyField(addressField, parent.Type, out var addressDefinition)) return false;
                    stack.Push(new CopyValue(addressField.FieldType, parent.Root, [.. parent.Path!, addressDefinition])); break;
                case Code.Ldfld:
                    if (instruction.Operand is not FieldReference readField || Pop() is not { } source ||
                        source.Root == target || !CopyField(readField, source.Type, out _)) return false;
                    stack.Push(new CopyValue(readField.FieldType)); break;
                case Code.Stfld:
                    if (instruction.Operand is not FieldReference storeField || Pop() is not { Address: false } value ||
                        Pop() is not { Address: true } place || !CopyField(storeField, place.Type, out var storeDefinition) ||
                        !StackSame(value.Type, storeField.FieldType)) return false;
                    if (place.Root == target) written.Add([.. place.Path!, storeDefinition]);
                    else if (place.Root is not VariableDefinition) return false;
                    break;
                case Code.Initobj:
                    if (instruction.Operand is not TypeReference initialized || Pop() is not { Address: true } initializedPlace ||
                        !Same(initialized, initializedPlace.Type) || !CopyData(initialized)) return false;
                    if (initializedPlace.Root == target) written.Add(initializedPlace.Path!);
                    else if (initializedPlace.Root is not VariableDefinition) return false;
                    break;
                case Code.Ldc_I4: stack.Push(new CopyValue(types.Int32)); break;
                case Code.Ldc_I8: stack.Push(new CopyValue(types.Int64)); break;
                case Code.Ldc_R4: stack.Push(new CopyValue(types.Single)); break;
                case Code.Ldc_R8: stack.Push(new CopyValue(types.Double)); break;
                case Code.Conv_I1: case Code.Conv_U1: case Code.Conv_I2: case Code.Conv_U2:
                case Code.Conv_I4: case Code.Conv_U4: case Code.Conv_I8: case Code.Conv_U8:
                case Code.Conv_R4: case Code.Conv_R8:
                    if (Pop() is not { Address: false } converted || !Scalar(converted.Type)) return false;
                    TypeReference convertedType = instruction.OpCode.Code switch
                    {
                        Code.Conv_I1 => types.SByte, Code.Conv_U1 => types.Byte, Code.Conv_I2 => types.Int16,
                        Code.Conv_U2 => types.UInt16, Code.Conv_I4 => types.Int32, Code.Conv_U4 => types.UInt32,
                        Code.Conv_I8 => types.Int64, Code.Conv_U8 => types.UInt64,
                        Code.Conv_R4 => types.Single, _ => types.Double
                    };
                    stack.Push(new CopyValue(convertedType)); break;
                case Code.Add: case Code.Sub: case Code.Mul: case Code.Div: case Code.And: case Code.Or: case Code.Xor:
                    if (Pop() is not { Address: false } right || Pop() is not { Address: false } left ||
                        !Scalar(left.Type) || !StackSame(left.Type, right.Type) ||
                        instruction.OpCode.Code == Code.Div && !Floating(left.Type) ||
                        instruction.OpCode.Code is Code.And or Code.Or or Code.Xor && Floating(left.Type)) return false;
                    stack.Push(new CopyValue(left.Type)); break;
                case Code.Shl: case Code.Shr: case Code.Shr_Un:
                    if (Pop() is not { Address: false } shift || StackKind(shift.Type) != 3 ||
                        Pop() is not { Address: false } shifted || StackKind(shifted.Type) is not (2 or 3)) return false;
                    stack.Push(new CopyValue(shifted.Type)); break;
                case Code.Neg:
                    if (Pop() is not { Address: false } negated || !Scalar(negated.Type)) return false;
                    stack.Push(new CopyValue(negated.Type)); break;
                case Code.Newobj:
                    if (instruction.Operand is not MethodReference ctor || !ScalarValueConstructor(ctor)) return false;
                    for (int argument = ctor.Parameters.Count - 1; argument >= 0; argument--)
                        if (Pop() is not { Address: false } argumentValue || !StackSame(argumentValue.Type, ctor.Parameters[argument].ParameterType)) return false;
                    stack.Push(new CopyValue(ctor.DeclaringType)); break;
                case Code.Call:
                    if (instruction.Operand is not MethodReference call || !ScalarIntrinsic(call, listDefinition) ||
                        Pop() is not { Address: false } input || !StackSame(input.Type, call.Parameters[0].ParameterType)) return false;
                    stack.Push(new CopyValue(call.ReturnType)); break;
                case Code.Stloc:
                    if (instruction.Operand is not VariableDefinition output || !CopyData(output.VariableType) ||
                        Pop() is not { Address: false } outputValue || !StackSame(output.VariableType, outputValue.Type)) return false;
                    // Scalar-byte extraction may capture a whole value while its final destination address
                    // remains on the stack. Keep only that one proven address; neither it nor its root may
                    // be stored over. All instructions and the eventual field store retain their order.
                    if (stack.Count != 0 && (stack.Count != 1 || stack.Peek() is not { Address: true } pending ||
                        pending.Root != target && pending.Root is not VariableDefinition || pending.Root == output)) return false;
                    break;
                default: return false;
            }
        }
        return stack.Count == 0;
    }

    private static bool TryFieldwiseAppend(MethodBody body, Instruction[] a, Dictionary<Instruction, int> ix,
        int k, int versionAt, int capacityAt, int fast, int slow, GenericInstanceType list, TypeDefinition definition,
        Instruction receiver, VariableDefinition array, VariableDefinition size)
    {
        TypeReference element = list.GenericArguments[0];
        TypeDefinition? elementDefinition;
        try { elementDefinition = element.Resolve(); }
        catch (AssemblyResolutionException) { return false; }
        catch (ResolutionException) { return false; }
        if (body.HasExceptionHandlers || !body.InitLocals || !CopyData(element) || elementDefinition == null || elementDefinition.IsExplicitLayout) return false;
        int end = fast + 6;
        while (end < slow && end - fast <= 1024 && a[end].OpCode.Code != Code.Br) end++;
        if (end >= slow || end - fast > 1024 || a[end].Operand is not Instruction join ||
            !ix.TryGetValue(join, out int joinAt) || joinAt <= slow || a[slow].OpCode.Code != Code.Nop) return false;
        if (!ValueCopySchedule(a, fast + 6, end, definition, body.Method.Module.TypeSystem, element, array, size,
                receiver.Operand, true, out var roots, out var written) || roots.Count == 0 || !CompleteCopy(element, written)) return false;
        int resizeAt = slow + 1;
        while (resizeAt < joinAt && resizeAt - slow <= 1024 && a[resizeAt].OpCode.Code != Code.Callvirt) resizeAt++;
        bool Receiver(Instruction instruction) => instruction.OpCode.Code == receiver.OpCode.Code && instruction.Operand == receiver.Operand;
        if (resizeAt >= joinAt || resizeAt - slow > 1024 || resizeAt < slow + 3 || !Receiver(a[resizeAt - 2]) ||
            a[resizeAt - 1].OpCode.Code != Code.Ldloc || a[resizeAt - 1].Operand is not VariableDefinition slowValue ||
            !Same(slowValue.VariableType, element) || a[resizeAt].Operand is not MethodReference resize ||
            resize.Name != "AddWithResize" || !Same(resize.DeclaringType, list) || !resize.HasThis ||
            resize.ReturnType.MetadataType != MetadataType.Void || resize.Parameters.Count != 1 ||
            !ElementParameter(resize.Parameters[0].ParameterType, list)) return false;
        MethodDefinition? Resolve(MethodReference method)
        {
            try { return method.Resolve(); }
            catch (AssemblyResolutionException) { return null; }
            catch (ResolutionException) { return null; }
        }
        if (Resolve(resize) is not { IsPrivate: true, IsStatic: false } resizeDefinition || resizeDefinition.DeclaringType != definition ||
            !ValueCopySchedule(a, slow + 1, resizeAt - 2, definition, body.Method.Module.TypeSystem, element, array, size,
                receiver.Operand, false, out _, out _)) return false;
        // Continuation copies are unchanged. No extra control edge or call is admitted to the append diamond.
        for (int tail = resizeAt + 1; tail < joinAt;)
        {
            if (a[tail].OpCode.Code == Code.Nop) { tail++; continue; }
            if (tail == joinAt - 1 && a[tail].OpCode.Code == Code.Br && a[tail].Operand == join) { tail++; continue; }
            if (tail + 1 < joinAt && LoadedValueType(a[tail]) is { } type && a[tail + 1].OpCode.Code == Code.Stloc &&
                a[tail + 1].Operand is VariableDefinition local && Same(type, local.VariableType) &&
                local != array && local != size && local != receiver.Operand) { tail += 2; continue; }
            return false;
        }
        var region = a.Skip(k).Take(end - k + 1).Concat(a.Skip(slow).Take(joinAt - slow)).ToHashSet();
        if (slow == 0 || a[slow - 1].OpCode.FlowControl is not (FlowControl.Branch or FlowControl.Return or FlowControl.Throw)) return false;
        foreach (Instruction instruction in a)
        {
            if (instruction.OpCode.Code is Code.Ldloca or Code.Ldarga &&
                (instruction.Operand == receiver.Operand || instruction.Operand == array || instruction.Operand == size)) return false;
            if (!region.Contains(instruction) && (instruction.Operand == array || instruction.Operand == size)) return false;
            if (!region.Contains(instruction) && instruction.Operand is Instruction entry && entry != receiver && region.Contains(entry)) return false;
            if (!region.Contains(instruction) && instruction.Operand is Instruction[] entries && entries.Any(e => e != receiver && region.Contains(e))) return false;
            if (region.Contains(instruction) && instruction.Operand is Instruction interior && region.Contains(interior) &&
                !(instruction == a[capacityAt + 7] && interior == a[slow])) return false;
        }
        var adds = definition.Methods.Where(m => m.Name == "Add" && m.IsPublic && !m.IsStatic && !m.HasGenericParameters &&
            m.ReturnType.MetadataType == MetadataType.Void && m.Parameters.Count == 1 && ElementParameter(m.Parameters[0].ParameterType, list)).ToArray();
        var capacities = definition.Methods.Where(m => m.Name == "get_Capacity" && m.IsPublic && !m.IsStatic && !m.HasGenericParameters &&
            m.ReturnType.MetadataType == MetadataType.Int32 && m.Parameters.Count == 0).ToArray();
        if (adds.Length != 1 || capacities.Length != 1) return false;
        var add = new MethodReference("Add", resize.ReturnType, list) { HasThis = true, CallingConvention = resize.CallingConvention };
        add.Parameters.Add(new ParameterDefinition(resize.Parameters[0].ParameterType));
        var capacity = new MethodReference("get_Capacity", capacities[0].ReturnType, list)
            { HasThis = true, CallingConvention = capacities[0].CallingConvention };
        if (Resolve(add) != adds[0] || Resolve(capacity) != capacities[0]) return false;

        var valueLocal = new VariableDefinition(element);
        var capacityLocal = new VariableDefinition(body.Method.Module.TypeSystem.Int32);
        body.Variables.Add(valueLocal); body.Variables.Add(capacityLocal);
        void Nop(Instruction instruction) { instruction.OpCode = OpCodes.Nop; instruction.Operand = null; }
        a[k + 1].OpCode = OpCodes.Callvirt; a[k + 1].Operand = capacity; a[k + 2].Operand = capacityLocal;
        foreach (Instruction instruction in a.Skip(versionAt).Take(6)) Nop(instruction);
        a[capacityAt].Operand = capacityLocal; Nop(a[capacityAt + 1]); Nop(a[capacityAt + 2]);
        foreach (Instruction instruction in a.Skip(fast + 1).Take(5)) Nop(instruction);
        foreach (int root in roots)
        {
            a[root].OpCode = OpCodes.Ldloca; a[root].Operand = valueLocal;
            Nop(a[root + 1]); Nop(a[root + 2]);
        }
        var loadReceiver = Instruction.Create(OpCodes.Nop);
        loadReceiver.OpCode = receiver.OpCode; loadReceiver.Operand = receiver.Operand;
        var il = body.GetILProcessor();
        il.InsertBefore(a[end], loadReceiver);
        il.InsertBefore(a[end], Instruction.Create(OpCodes.Ldloc, valueLocal));
        il.InsertBefore(a[end], Instruction.Create(OpCodes.Callvirt, add));
        a[resizeAt].Operand = add;
        return true;
    }
}
