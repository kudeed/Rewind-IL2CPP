using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Rewind.Output;

/// <summary>
/// A readonly struct field used only by the next scalar field read needs its
/// value, never a writable managed address. Preserve exactly the same reads,
/// null checks and evaluation count without producing an illegal initonly
/// address outside the declaring constructor.
/// </summary>
internal static class ReadOnlyFieldReadIlFolding
{
    internal static int Run(MethodBody body)
    {
        var instructions = body.Instructions;
        var entries = new HashSet<Instruction>();
        foreach (var i in instructions)
        {
            if (i.Operand is Instruction one) entries.Add(one);
            if (i.Operand is Instruction[] many) foreach (var target in many) entries.Add(target);
        }
        foreach (var e in body.ExceptionHandlers)
        {
            if (e.TryStart != null) entries.Add(e.TryStart);
            if (e.TryEnd != null) entries.Add(e.TryEnd);
            if (e.HandlerStart != null) entries.Add(e.HandlerStart);
            if (e.HandlerEnd != null) entries.Add(e.HandlerEnd);
            if (e.FilterStart != null) entries.Add(e.FilterStart);
        }
        int count = 0;
        for (int n = 0; n + 1 < instructions.Count; n++)
        {
            var load = instructions[n]; var read = instructions[n + 1];
            if (load.OpCode.Code is not (Code.Ldflda or Code.Ldsflda) ||
                load.Operand is not FieldReference outer || read.OpCode.Code != Code.Ldfld ||
                read.Operand is not FieldReference inner || entries.Contains(read) ||
                n > 0 && instructions[n - 1].OpCode.OpCodeType == OpCodeType.Prefix) continue;
            FieldDefinition? field; FieldDefinition? member; TypeDefinition? value;
            try { field = outer.Resolve(); member = inner.Resolve(); value = outer.FieldType.Resolve(); }
            catch (AssemblyResolutionException) { continue; }
            catch (ResolutionException) { continue; }
            if (field == null || member == null || value == null || !field.IsInitOnly ||
                !outer.FieldType.IsValueType || value.IsEnum || member.IsStatic ||
                member.DeclaringType != value || !member.IsPublic ||
                field.IsStatic != (load.OpCode.Code == Code.Ldsflda) ||
                outer.FieldType is GenericInstanceType || inner.DeclaringType.FullName != outer.FieldType.FullName ||
                body.Method.IsConstructor && body.Method.DeclaringType == field.DeclaringType) continue;
            load.OpCode = field.IsStatic ? OpCodes.Ldsfld : OpCodes.Ldfld;
            count++;
        }
        return count;
    }
}
