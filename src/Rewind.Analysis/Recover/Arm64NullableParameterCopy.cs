using Rewind.Analysis.Abi;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Hir;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// An AAPCS64 16-byte nullable argument spilled by a single STP is a complete
/// copy. Some split-field recoveries retained only its first eight bytes.
/// Recover the whole copy only when both the native store and the exact
/// entry HIR stores identify the same untouched incoming argument.
/// </summary>
internal static class Arm64NullableParameterCopy
{
    internal static bool CompleteSpill(uint[] prefix, int firstRegister, out int stackOffset)
    {
        stackOffset = 0;
        if (prefix.Length is < 2 or > 64 || firstRegister is < 0 or > 6) return false;
        bool Pair(int r) => r == firstRegister || r == firstRegister + 1;
        long allocation = 0;
        for (int n = 0; n < prefix.Length; n++)
        {
            var i = A64Decoder.Decode(prefix[n], (ulong)n * 4);
            if (n == prefix.Length - 1)
            {
                if (i.Op != A64Op.Stp || i.Vector || i.Size != 8 || i.Rn != A64Instruction.Sp ||
                    i.Mode != A64Mode.Offset || i.Rd != firstRegister || i.Ra != firstRegister + 1 ||
                    i.Imm < 0 || i.Imm % 8 != 0 || i.Imm + 16 > allocation) return false;
                stackOffset = checked((int)(i.Imm - allocation));
                return true;
            }
            switch (i.Op)
            {
                case A64Op.Nop:
                case A64Op.FMov:
                    break;
                case A64Op.SubImm:
                    if (allocation != 0 || !i.Is64 || i.SetFlags ||
                        i.Rd != A64Instruction.Sp || i.Rn != A64Instruction.Sp || i.Imm <= 0) return false;
                    allocation = i.Imm;
                    break;
                case A64Op.Adr:
                case A64Op.Adrp:
                case A64Op.Orr:
                    if (Pair(i.Rd)) return false;
                    break;
                case A64Op.Ldr:
                    if (i.Mode != A64Mode.Offset || !i.Vector && Pair(i.Rd)) return false;
                    break;
                case A64Op.Stp:
                case A64Op.Str:
                    if (i.Rn != A64Instruction.Sp || i.Mode != A64Mode.Offset ||
                        i.Imm < 0 || allocation == 0 ||
                        i.Imm + i.Size * (i.Op == A64Op.Stp ? 2 : 1) > allocation) return false;
                    break;
                default:
                    // No call, branch, unknown instruction or hidden GP write
                    // may precede the spill on this deliberately narrow proof.
                    return false;
            }
        }
        return false;
    }

    internal static int Run(HMethod h, ProgramAnalysis p)
    {
        if (Environment.GetEnvironmentVariable("REWIND_NO_NULLABLE_ENTRY_COPY") != null ||
            p.Model.Image.Arch != CpuArch.Arm64 || h.Method.Address == 0 ||
            h.Method.DeclaringType.IsGenericDefinition || h.Method.IsGenericDefinition ||
            h.Problems.Count != 0 || h.TryRegions.Count != 0 || h.Blocks.Count == 0 ||
            h.Blocks.Any(b => b.Scope != -1)) return 0;
        var entry = h.Blocks[0];
        if (h.Blocks.SelectMany(b => b.Statements).Any(s => s switch
            {
                HJump j => j.Target == entry,
                HBranch b => b.WhenTrue == entry || b.WhenFalse == entry,
                HSwitch sw => sw.Default == entry || sw.Targets.Contains(entry),
                _ => false,
            })) return 0;
        var s = h.Blocks[0].Statements;
        if (s.Count < 3 ||
            s[0] is not HAssign { Target: HLocal local, Value: HTypeExpr { Op: HTypeOp.Default } zero } initial ||
            s[1] is not HAssign { Target: HField { Object: HLocal flagLocal } flag, Value: HCall flagGet } flagStore ||
            s[2] is not HAssign { Target: HField { Object: HField { Object: HLocal payloadLocal } payload } lane,
                Value: HField { Object: HCall valueGet } sourceLane } laneStore ||
            local.Variable != flagLocal.Variable || local.Variable != payloadLocal.Variable ||
            local.Variable.Type is not GenericInstSig nullable ||
            nullable.Definition.ReflectionName != "System.Nullable`1" || nullable.Definition.Assembly.Name != "mscorlib" ||
            nullable.Arguments is not [TypeDefSig vector] ||
            vector.Definition.ReflectionName != "UnityEngine.Vector3" || vector.Definition.Assembly.Name != "UnityEngine.CoreModule" ||
            zero.Target.Key != nullable.Key || flag.Field.DeclaringType != nullable.Definition || flag.Field.Name != "hasValue" ||
            payload.Field.DeclaringType != nullable.Definition || payload.Field.Name != "value" ||
            lane.Field != sourceLane.Field || lane.Field.DeclaringType != vector.Definition || lane.Field.Name != "x" ||
            flagGet.This is not HArg { Index: >= 0 } argument || valueGet.This is not HArg other ||
            argument.Index != other.Index || argument.Type?.Key != nullable.Key || other.Type?.Key != nullable.Key ||
            flagGet.Method.Name != "get_HasValue" || valueGet.Method.Name != "GetValueOrDefault" ||
            flagGet.Method.DeclaringType != nullable.Definition || valueGet.Method.DeclaringType != nullable.Definition ||
            flagGet.Method.IsStatic || valueGet.Method.IsStatic || flagGet.Virtual || valueGet.Virtual ||
            flagGet.Arguments.Length != 0 || valueGet.Arguments.Length != 0 ||
            flagGet.MethodArguments.Length != 0 || valueGet.MethodArguments.Length != 0 ||
            flagGet.DeclaringType?.Key != nullable.Key || valueGet.DeclaringType?.Key != nullable.Key ||
            initial.Address != flagStore.Address || initial.Address != laneStore.Address) return 0;
        var layout = p.Layouts.Of(nullable);
        var vectorLayout = p.Layouts.Of(vector);
        if (!layout.Known || layout.Size != 16 || layout.Fields.Length != 2 ||
            !layout.Fields.Any(f => f.Field == flag.Field && f.Offset == 0 && f.Size == 1 &&
                f.Type is PrimitiveSig { Element: Il2CppTypeEnum.Boolean }) ||
            !layout.Fields.Any(f => f.Field == payload.Field && f.Offset == 4 && f.Size == 12 && f.Type.Key == vector.Key) ||
            !vectorLayout.Known || vectorLayout.Size != 12 || vectorLayout.Fields.Length != 3 ||
            !vectorLayout.Fields.Select((f, n) => f.Offset == 4 * n && f.Size == 4 &&
                f.Field.Name == new[] { "x", "y", "z" }[n] && f.Type is PrimitiveSig { Element: Il2CppTypeEnum.R4 }).All(v => v))
            return 0;
        var abi = p.Abi.For(h.Method, [], []);
        var parts = abi.Params.Where(a => a.Role == ParamRole.Argument && a.ArgumentIndex == argument.Index).ToArray();
        if (!abi.Known || parts is not [{ Pass: PassKind.IntegerPair, Size: 16, Count: 2 } parameter] ||
            p.Abi.Regs.IsStackPosition(parameter.Position) ||
            p.RangeOf(h.Method.Address) is not { } range || initial.Address < range.Start ||
            initial.Address >= range.End || (initial.Address - range.Start) % 4 != 0 ||
            initial.Address - range.Start > 252) return 0;
        int firstRegister = p.Abi.Regs.IntRegisterOf(parameter.Position);
        var image = p.Model.Image;
        if (image.SectionAt(range.Start) is not { IsExecutable: true } section ||
            initial.Address + 4 > section.End || !image.IsMapped(range.Start, (int)(initial.Address - range.Start + 4))) return 0;
        var prefix = Enumerable.Range(0, (int)((initial.Address - range.Start) / 4 + 1))
            .Select(n => image.U32(range.Start + (ulong)n * 4)).ToArray();
        if (!CompleteSpill(prefix, firstRegister, out int frameOffset) ||
            !h.FrameTypes.TryGetValue(frameOffset, out var frameType) || frameType.Key != nullable.Key) return 0;
        s[0] = new HAssign(new HLocal(local.Variable) { Type = nullable },
            new HArg(argument.Index) { Type = nullable }) { Address = initial.Address };
        s.RemoveRange(1, 2);
        h.Notes.Add("restored complete 16-byte nullable parameter spill from original ARM64 STP");
        return 1;
    }
}
