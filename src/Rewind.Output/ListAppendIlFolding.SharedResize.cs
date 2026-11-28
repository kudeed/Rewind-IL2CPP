using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Rewind.Output;

internal static partial class ListAppendIlFolding
{
    private sealed record SharedAppend(Instruction Receiver, GenericInstanceType List, TypeDefinition Definition,
        VariableDefinition Array, VariableDefinition Size, VariableDefinition Phi, VariableDefinition? Read,
        int Start, int Version, int Capacity, int Fast, int Store, int End, int Slow, int SlowEnd,
        int Shared, int Resize, int Join, int ComputationStart);

    // Two native append diamonds may share a resize block through one scalar phi. Restore the pair together:
    // the shared call must have exactly these two proved predecessors, each carrying its own version increment.
    private static int FoldSharedResize(MethodBody body)
    {
        if (body.HasExceptionHandlers) return 0;
        int changed = 0;
        foreach (Instruction seed in body.Instructions.Where(Candidate).ToArray())
        {
            if (!Candidate(seed)) continue;
            Instruction[] a = body.Instructions.ToArray();
            var ix = a.Select((i, n) => (i, n)).ToDictionary(p => p.i, p => p.n);
            var first = SharedShape(body, a, ix, seed);
            if (first == null) continue;
            var group = body.Instructions.Where(Candidate).Select(i => SharedShape(body, a, ix, i))
                .Where(m => m != null && m.Shared == first.Shared && m.Resize == first.Resize).Select(m => m!).ToArray();
            if (group.Length != 2 || group.Any(m => m.Receiver.OpCode.Code != first.Receiver.OpCode.Code ||
                m.Receiver.Operand != first.Receiver.Operand || !Same(m.List, first.List) ||
                m.Definition != first.Definition || m.Phi != first.Phi || m.Join != first.Join) ||
                group.Select(m => m.Start).Distinct().Count() != 2 || group.Select(m => m.Slow).Distinct().Count() != 2 ||
                group.SelectMany(m => new[] { m.Array, m.Size }).Distinct().Count() != 4) continue;
            object[] protectedValues = group.SelectMany(m => new object[] { m.Array, m.Size })
                .Concat(new[] { first.Receiver.Operand, (object)first.Phi }).ToArray();
            if (group.Any(m => m.Read != null && protectedValues.Contains(m.Read) ||
                !SafePostVersionSchedule(a.Skip(m.ComputationStart).Take(m.Capacity - m.ComputationStart).ToArray(),
                    m.Definition, body.Method.Module.TypeSystem, protectedValues))) continue;
            var region = new HashSet<Instruction>();
            foreach (var match in group)
            {
                foreach (var instruction in a.Skip(match.Start).Take(match.End - match.Start + 1)) region.Add(instruction);
                foreach (var instruction in a.Skip(match.Slow).Take(match.SlowEnd - match.Slow + 1)) region.Add(instruction);
            }
            foreach (var instruction in a.Skip(first.Shared).Take(first.Resize - first.Shared + 1)) region.Add(instruction);
            var entries = group.Select(m => a[m.Start]).ToHashSet();
            bool safe = true;
            foreach (Instruction instruction in a)
            {
                if (instruction.OpCode.Code is Code.Ldloca or Code.Ldarga && protectedValues.Contains(instruction.Operand)) { safe = false; break; }
                if (!region.Contains(instruction) && group.Any(m => instruction.Operand == m.Array || instruction.Operand == m.Size)) { safe = false; break; }
                IEnumerable<Instruction> targets = instruction.Operand is Instruction one ? [one] : instruction.Operand as Instruction[] ?? [];
                foreach (Instruction target in targets.Where(region.Contains))
                {
                    if (!region.Contains(instruction))
                    { if (!entries.Contains(target)) safe = false; }
                    else if (!group.Any(m => instruction == a[m.Capacity + 7] && target == a[m.Slow] ||
                        instruction == a[m.SlowEnd] && instruction.OpCode.Code == Code.Br && target == a[m.Shared])) safe = false;
                }
                // A physical fall-through is an incoming edge too. Only the original header entries may
                // be reached from outside; no third path may enter either slow assignment or the shared call.
                if (!region.Contains(instruction) && instruction.Next is { } next && region.Contains(next) && !entries.Contains(next) &&
                    instruction.OpCode.FlowControl is not (FlowControl.Branch or FlowControl.Return or FlowControl.Throw)) safe = false;
                if (!safe) break;
            }
            if (!safe) continue;
            MethodDefinition? Resolve(MethodReference method)
            {
                try { return method.Resolve(); }
                catch (AssemblyResolutionException) { return null; }
                catch (ResolutionException) { return null; }
            }
            var adds = first.Definition.Methods.Where(m => m.Name == "Add" && m.IsPublic && !m.IsStatic && !m.HasGenericParameters &&
                m.ReturnType.MetadataType == MetadataType.Void && m.Parameters.Count == 1 && ElementParameter(m.Parameters[0].ParameterType, first.List)).ToArray();
            var capacities = first.Definition.Methods.Where(m => m.Name == "get_Capacity" && m.IsPublic && !m.IsStatic && !m.HasGenericParameters &&
                m.ReturnType.MetadataType == MetadataType.Int32 && m.Parameters.Count == 0).ToArray();
            if (adds.Length != 1 || capacities.Length != 1 || a[first.Resize].Operand is not MethodReference resize) continue;
            var add = new MethodReference("Add", resize.ReturnType, first.List) { HasThis = true, CallingConvention = resize.CallingConvention };
            add.Parameters.Add(new ParameterDefinition(resize.Parameters[0].ParameterType));
            var capacity = new MethodReference("get_Capacity", capacities[0].ReturnType, first.List)
                { HasThis = true, CallingConvention = capacities[0].CallingConvention };
            if (Resolve(add) != adds[0] || Resolve(capacity) != capacities[0]) continue;
            void Nop(Instruction instruction) { instruction.OpCode = OpCodes.Nop; instruction.Operand = null; }
            foreach (var match in group)
            {
                var captured = new VariableDefinition(body.Method.Module.TypeSystem.Int32); body.Variables.Add(captured);
                a[match.Start + 1].OpCode = OpCodes.Callvirt; a[match.Start + 1].Operand = capacity; a[match.Start + 2].Operand = captured;
                foreach (var instruction in a.Skip(match.Version).Take(6)) Nop(instruction);
                a[match.Capacity].Operand = captured; Nop(a[match.Capacity + 1]); Nop(a[match.Capacity + 2]);
                foreach (var instruction in a.Skip(match.Fast + 1).Take(5)) Nop(instruction);
                a[match.Fast + 6].OpCode = match.Receiver.OpCode; a[match.Fast + 6].Operand = match.Receiver.Operand;
                Nop(a[match.Fast + 7]); a[match.Store].OpCode = OpCodes.Callvirt; a[match.Store].Operand = add;
            }
            a[first.Resize].Operand = add;
            changed += group.Length;
        }
        return changed;
    }

    private static SharedAppend? SharedShape(MethodBody body, Instruction[] a, Dictionary<Instruction, int> ix, Instruction candidate)
    {
        int k = ix[candidate] - 1;
        if (k < 0 || k + 31 >= a.Length || LoadedValueType(a[k]) is not GenericInstanceType list || !List(list) ||
            list.GenericArguments[0].MetadataType != MetadataType.Int32 || a[k + 2].OpCode.Code != Code.Stloc ||
            a[k + 2].Operand is not VariableDefinition array || array.VariableType is not ArrayType { IsVector: true } at ||
            !Same(at.ElementType, list.GenericArguments[0])) return null;
        TypeDefinition? definition;
        try { definition = list.ElementType.Resolve(); }
        catch (AssemblyResolutionException) { return null; }
        catch (ResolutionException) { return null; }
        if (definition == null || !Same(definition, list.ElementType) || definition.GenericParameters.Count != 1 ||
            Same(body.Method.DeclaringType, definition)) return null;
        Instruction receiver = a[k];
        bool Receiver(Instruction instruction) => instruction.OpCode.Code == receiver.OpCode.Code && instruction.Operand == receiver.Operand;
        bool Local(Instruction instruction, Code code, VariableDefinition local) => instruction.OpCode.Code == code && instruction.Operand == local;
        bool Field(Instruction instruction, Code code, string name, bool items = false)
        {
            if (instruction.OpCode.Code != code || instruction.Operand is not FieldReference field || field.Name != name || !Same(field.DeclaringType, list)) return false;
            FieldDefinition? found;
            try { found = field.Resolve(); }
            catch (AssemblyResolutionException) { return false; }
            catch (ResolutionException) { return false; }
            return found != null && found.DeclaringType == definition && !found.IsStatic && (found.IsPrivate || found.IsAssembly) &&
                (items ? found.FieldType is ArrayType { IsVector: true } arrayType && ElementParameter(arrayType.ElementType, list) : found.FieldType.MetadataType == MetadataType.Int32);
        }
        MethodDefinition? Resolve(MethodReference method)
        {
            try { return method.Resolve(); }
            catch (AssemblyResolutionException) { return null; }
            catch (ResolutionException) { return null; }
        }
        bool Version(int i) => i + 5 < a.Length && Receiver(a[i]) && Receiver(a[i + 1]) && Field(a[i + 2], Code.Ldfld, "_version") &&
            Constant(a[i + 3], 1) && a[i + 4].OpCode.Code == Code.Add && Field(a[i + 5], Code.Stfld, "_version");
        if (!Field(candidate, Code.Ldfld, "_items", true)) return null;
        int version = k + 3; VariableDefinition? read = null;
        if (!Version(version))
        {
            if (version + 3 >= a.Length || LoadedValueType(a[version]) is not { IsValueType: false } source || source is TypeSpecification ||
                a[version + 1].OpCode.Code != Code.Ldfld || a[version + 1].Operand is not FieldReference field ||
                !Same(source, field.DeclaringType) || field.FieldType.MetadataType != MetadataType.Int32 ||
                a[version + 2].OpCode.Code != Code.Stloc || a[version + 2].Operand is not VariableDefinition readLocal ||
                !Same(readLocal.VariableType, field.FieldType) || readLocal == array || readLocal == receiver.Operand) return null;
            FieldDefinition? found;
            try { found = field.Resolve(); }
            catch (AssemblyResolutionException) { return null; }
            catch (ResolutionException) { return null; }
            bool inside = false;
            for (TypeDefinition? owner = body.Method.DeclaringType; owner != null; owner = owner.DeclaringType)
                if (owner == found?.DeclaringType) inside = true;
            if (found == null || found.IsStatic || !found.IsPublic && !inside || !Same(found.FieldType, field.FieldType)) return null;
            read = readLocal; version += 3;
        }
        if (!Version(version)) return null;
        int count = version + 6;
        if (count + 2 >= a.Length || !Receiver(a[count]) || a[count + 1].OpCode.Code != Code.Callvirt ||
            a[count + 1].Operand is not MethodReference getter || getter.Name != "get_Count" || !Same(getter.DeclaringType, list) ||
            !getter.HasThis || getter.HasGenericParameters || getter is GenericInstanceMethod || getter.Parameters.Count != 0 || getter.ReturnType.MetadataType != MetadataType.Int32 ||
            Resolve(getter) is not { IsPublic: true, IsStatic: false } countDefinition || countDefinition.DeclaringType != definition ||
            a[count + 2].OpCode.Code != Code.Stloc || a[count + 2].Operand is not VariableDefinition size ||
            size.VariableType.MetadataType != MetadataType.Int32 || size == array || size == receiver.Operand || size == read) return null;
        bool Capacity(int i) => i + 7 < a.Length && Local(a[i], Code.Ldloc, array) && a[i + 1].OpCode.Code == Code.Ldlen &&
            a[i + 2].OpCode.Code == Code.Conv_I4 && Local(a[i + 3], Code.Ldloc, size) && a[i + 4].OpCode.Code == Code.Cgt_Un &&
            Constant(a[i + 5], 0) && a[i + 6].OpCode.Code == Code.Ceq && a[i + 7].OpCode.Code == Code.Brtrue;
        int capacity = count + 3;
        while (capacity + 7 < a.Length && capacity - count <= 35 && !Capacity(capacity)) capacity++;
        if (capacity - count > 35 || !Capacity(capacity) || a[capacity + 7].Operand is not Instruction slowTarget || !ix.TryGetValue(slowTarget, out int slow)) return null;
        int fast = capacity + 8;
        if (fast + 10 >= a.Length || a[fast].OpCode.Code != Code.Nop || !Receiver(a[fast + 1]) || !Local(a[fast + 2], Code.Ldloc, size) ||
            !Constant(a[fast + 3], 1) || a[fast + 4].OpCode.Code != Code.Add || !Field(a[fast + 5], Code.Stfld, "_size") ||
            !Local(a[fast + 6], Code.Ldloc, array) || !Local(a[fast + 7], Code.Ldloc, size) ||
            a[fast + 9].OpCode.Code != Code.Stelem_Any || a[fast + 9].Operand is not TypeReference stored || !Same(stored, list.GenericArguments[0]) ||
            a[fast + 10].OpCode.Code != Code.Br || a[fast + 10].Operand is not Instruction joinTarget || !ix.TryGetValue(joinTarget, out int join)) return null;
        bool ScalarValue(Instruction instruction) => instruction.OpCode.Code == Code.Ldc_I4 && instruction.Operand is int ||
            LoadedValueType(instruction) is { } value && Same(value, list.GenericArguments[0]);
        if (!ScalarValue(a[fast + 8]) || a[fast + 8].Operand == size || a[fast + 8].Operand == array ||
            slow < 0 || slow + 3 >= a.Length || a[slow].OpCode.Code != Code.Nop ||
            a[slow + 1].OpCode.Code != a[fast + 8].OpCode.Code || !Equals(a[slow + 1].Operand, a[fast + 8].Operand) ||
            a[slow + 2].OpCode.Code != Code.Stloc || a[slow + 2].Operand is not VariableDefinition phi ||
            !Same(phi.VariableType, list.GenericArguments[0]) || phi == size || phi == array || phi == receiver.Operand ||
            phi == a[fast + 8].Operand || phi == read) return null;
        int shared = slow + 3, slowEnd = slow + 2;
        if (a[shared].OpCode.Code == Code.Br)
        {
            slowEnd = shared;
            if (a[shared].Operand is not Instruction sharedTarget || !ix.TryGetValue(sharedTarget, out shared)) return null;
        }
        if (shared + 4 >= a.Length || a[shared].OpCode.Code != Code.Nop || !Receiver(a[shared + 1]) ||
            !Local(a[shared + 2], Code.Ldloc, phi) || a[shared + 3].OpCode.Code != Code.Callvirt ||
            a[shared + 3].Operand is not MethodReference resize || resize.Name != "AddWithResize" || !Same(resize.DeclaringType, list) ||
            !resize.HasThis || resize.HasGenericParameters || resize is GenericInstanceMethod || resize.ReturnType.MetadataType != MetadataType.Void || resize.Parameters.Count != 1 ||
            !ElementParameter(resize.Parameters[0].ParameterType, list) || Resolve(resize) is not { IsPrivate: true, IsStatic: false } resizeDefinition ||
            resizeDefinition.DeclaringType != definition || a[shared + 4] != joinTarget) return null;
        return new SharedAppend(receiver, list, definition, array, size, phi, read, k, version, capacity, fast, fast + 9,
            fast + 10, slow, slowEnd, shared, shared + 3, join, count + 3);
    }
}
