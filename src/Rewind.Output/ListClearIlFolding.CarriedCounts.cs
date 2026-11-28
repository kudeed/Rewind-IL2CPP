using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Rewind.Output;

internal static partial class ListClearIlFolding
{
    // Keep the complete native max/min-style field assignment in place. Only the
    // early List null check is replaced by Count; the Clear still follows the store.
    private static bool ConditionalFieldStore(MethodBody body, Instruction[] a, int s,
        VariableDefinition list, VariableDefinition version)
    {
        if (s < 0 || s + 10 >= a.Length) return false;
        static TypeReference? Loaded(Instruction i) => i.Operand switch
        {
            VariableDefinition v when i.OpCode.Code == Code.Ldloc => v.VariableType,
            ParameterDefinition p when i.OpCode.Code == Code.Ldarg => p.ParameterType,
            _ => null
        };
        TypeReference? owner = Loaded(a[s]), value = Loaded(a[s + 2]);
        if (owner == null || owner.IsValueType || owner is TypeSpecification || owner.ContainsGenericParameter ||
            value == null || !Int(value) || a[s + 1].OpCode.Code != Code.Ldc_I4 || a[s + 1].Operand is not int bound ||
            a[s + 3].OpCode.Code != Code.Clt || a[s + 4].OpCode.Code != Code.Brfalse || a[s + 4].Operand != a[s + 7] ||
            a[s + 5].OpCode.Code != a[s + 2].OpCode.Code || a[s + 5].Operand != a[s + 2].Operand ||
            a[s + 6].OpCode.Code != Code.Br || a[s + 6].Operand != a[s + 9] || a[s + 7].OpCode.Code != Code.Nop ||
            !Number(a[s + 8], bound) || a[s + 9].OpCode.Code != Code.Nop ||
            a[s + 10].OpCode.Code != Code.Stfld || a[s + 10].Operand is not FieldReference field ||
            !Int(field.FieldType) || !Same(field.DeclaringType, owner) ||
            a.Skip(s).Take(11).Any(i => i.Operand == list || i.Operand == version)) return false;
        try
        {
            // This exact store remains in place with its original member/visibility. A pre-existing
            // private-field diagnostic is retained; this proof only establishes Clear's ordering.
            return field.Resolve() is { IsStatic: false, IsInitOnly: false } resolved &&
                Same(resolved.FieldType, field.FieldType) && Same(resolved.DeclaringType, owner) &&
                !resolved.DeclaringType.IsExplicitLayout && !resolved.DeclaringType.IsValueType;
        }
        catch (AssemblyResolutionException) { return false; }
        catch (ResolutionException) { return false; }
    }

    // Prove every reaching count definition, including scalar copy phis. Stop at
    // the most recent exact Count read: an earlier loop/callback is irrelevant,
    // while any intervening call or write that could stale that count is rejected.
    private static bool FreshCountSnapshot(MethodBody body, Instruction[] a, Dictionary<Instruction, int> ix,
        int entry, VariableDefinition list, GenericInstanceType listType, MethodDefinition getCount,
        VariableDefinition savedCount, VariableDefinition version, out HashSet<VariableDefinition> aliases)
    {
        aliases = [savedCount]; var trackedAliases = aliases;
        if (!Int(savedCount.VariableType) || savedCount == list || savedCount == version) return false;
        foreach (var handler in body.ExceptionHandlers)
            if (new[] { handler.TryStart, handler.TryEnd, handler.HandlerStart, handler.HandlerEnd, handler.FilterStart }
                .Any(i => i != null && !ix.ContainsKey(i))) return false;
        int ScopeAt(int n, ExceptionHandler handler)
        {
            bool Inside(Instruction? start, Instruction? end) => start != null && n >= ix[start] && (end == null || n < ix[end]);
            return (Inside(handler.TryStart, handler.TryEnd) ? 1 : 0) |
                (Inside(handler.HandlerStart, handler.HandlerEnd) ? 2 : 0) |
                (Inside(handler.FilterStart, handler.HandlerStart) ? 4 : 0);
        }
        bool SameRegion(int n) => body.ExceptionHandlers.All(h => ScopeAt(n, h) == ScopeAt(entry, h) && (ScopeAt(n, h) & 4) == 0);
        var predecessors = Enumerable.Range(0, a.Length).Select(_ => new List<int>()).ToArray();
        for (int n = 0; n < a.Length; n++)
        {
            void Edge(Instruction target)
            {
                if (ix.TryGetValue(target, out int at)) predecessors[at].Add(n);
            }
            if (a[n].Operand is Instruction target) Edge(target);
            else if (a[n].Operand is Instruction[] targets) foreach (Instruction destination in targets) Edge(destination);
            if (n + 1 < a.Length && a[n].OpCode.FlowControl is not (FlowControl.Branch or FlowControl.Return or FlowControl.Throw))
                predecessors[n + 1].Add(n);
        }
        MethodDefinition? Resolve(MethodReference method)
        {
            try { return method.Resolve(); }
            catch (AssemblyResolutionException) { return null; }
            catch (ResolutionException) { return null; }
        }
        bool IsCount(Instruction instruction, bool sameReceiver)
        {
            if (instruction.OpCode.Code != Code.Callvirt || instruction.Operand is not MethodReference method ||
                method.Name != "get_Count" || !method.HasThis || method.HasGenericParameters || method is GenericInstanceMethod ||
                method.Parameters.Count != 0 || !Int(method.ReturnType) || !List(method.DeclaringType) ||
                Resolve(method) is not { IsPublic: true, IsStatic: false, HasGenericParameters: false } definition ||
                definition.IsVirtual && !definition.IsFinal || !Same(definition.DeclaringType, ((GenericInstanceType)method.DeclaringType).ElementType)) return false;
            return !sameReceiver || Same(method.DeclaringType, listType) && definition == getCount;
        }
        bool ReadField(Instruction instruction)
        {
            if (instruction.Operand is not FieldReference field || field.FieldType is ByReferenceType or PointerType or FunctionPointerType ||
                field.FieldType.ContainsGenericParameter) return false;
            try
            {
                return field.Resolve() is { IsStatic: false } definition &&
                    (definition.IsPublic || definition.DeclaringType == body.Method.DeclaringType) &&
                    Same(definition.FieldType, field.FieldType) && Same(definition.DeclaringType, field.DeclaringType);
            }
            catch (AssemblyResolutionException) { return false; }
            catch (ResolutionException) { return false; }
        }
        bool PlainValue(TypeReference type) => type is not (ByReferenceType or PointerType or FunctionPointerType) && !type.ContainsGenericParameter;
        var marks = new Dictionary<(int Index, VariableDefinition Value), byte>();
        bool Before(int n, VariableDefinition value) => predecessors[n].Count != 0 && predecessors[n].All(p => Visit(p, value));
        bool Visit(int n, VariableDefinition value)
        {
            if (!SameRegion(n) || marks.Count > 4096) return false;
            var key = (n, value);
            if (marks.TryGetValue(key, out byte mark)) return mark == 2;
            marks[key] = 1;
            bool Prove()
            {
                Instruction instruction = a[n];
                if (instruction.OpCode.Code == Code.Stloc && instruction.Operand == value)
                {
                    // The stored value must be produced by this exact read/copy, not another stack predecessor.
                    if (n < 1 || predecessors[n].Count != 1 || predecessors[n][0] != n - 1 || !SameRegion(n - 1)) return false;
                    if (n >= 2 && IsCount(a[n - 1], true) && Local(a[n - 2], Code.Ldloc, list) &&
                        predecessors[n - 1].Count == 1 && predecessors[n - 1][0] == n - 2 && SameRegion(n - 2)) return true;
                    if (a[n - 1].OpCode.Code != Code.Ldloc || a[n - 1].Operand is not VariableDefinition copied ||
                        !Int(copied.VariableType) || copied == list || copied == version || copied == value) return false;
                    trackedAliases.Add(copied); return Before(n - 1, copied);
                }
                if (body.ExceptionHandlers.Any(h => instruction == h.HandlerStart || instruction == h.FilterStart)) return false;
                bool allowed = instruction.OpCode.Code switch
                {
                    Code.Nop or Code.Ldc_I4 or Code.Ldc_I8 or Code.Ldc_R4 or Code.Ldc_R8 or Code.Ldnull or
                    Code.Add or Code.Sub or Code.Mul or Code.And or Code.Or or Code.Xor or Code.Neg or
                    Code.Clt or Code.Clt_Un or Code.Cgt or Code.Cgt_Un or Code.Ceq or
                    Code.Conv_I4 or Code.Conv_U4 or Code.Conv_I8 or Code.Conv_U8 or
                    Code.Br or Code.Brtrue or Code.Brfalse or Code.Switch or Code.Pop => true,
                    Code.Ldloc => instruction.Operand is VariableDefinition local && PlainValue(local.VariableType),
                    Code.Ldarg => instruction.Operand is ParameterDefinition argument && PlainValue(argument.ParameterType),
                    Code.Stloc => instruction.Operand is VariableDefinition local && Int(local.VariableType) && local != list && local != version,
                    Code.Ldfld => ReadField(instruction),
                    Code.Callvirt => IsCount(instruction, false),
                    _ => false
                };
                return allowed && Before(n, value);
            }
            bool proved = Prove(); marks[key] = proved ? (byte)2 : (byte)3; return proved;
        }
        bool result = Before(entry, savedCount);
        return result && !a.Any(i => i.OpCode.Code == Code.Ldloca && i.Operand is VariableDefinition variable &&
            (variable == list || trackedAliases.Contains(variable)));
    }
}
