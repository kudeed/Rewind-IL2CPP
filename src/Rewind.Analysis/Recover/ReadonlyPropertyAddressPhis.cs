using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// An inlined value property can leave a scalar read behind a phi of addresses into its returned struct.
/// Restore a scalar phi only when every path to its single read defines it once, all intervening operations
/// are read-only, and each address is a field chain rooted in a reference argument. A whole struct address
/// means its first scalar field only when the recorded, non-overlapping layout proves that exact interval.
/// </summary>
internal static class ReadonlyPropertyAddressPhis
{
    internal static int Run(HMethod h, ProgramAnalysis program, MethodPipeline pipeline)
    {
        if (Environment.GetEnvironmentVariable("REWIND_NO_READONLY_PROPERTY_ADDRESS_PHIS") != null) return 0;
        var cache = new Dictionary<FieldDef, MethodDef?>();
        MethodDef? Getter(FieldDef field)
        {
            if (cache.TryGetValue(field, out var known)) return known;
            MethodDef? found = null;
            if (AccessorIndex.IsBackingField(field) && program.Accessors.GetterOf(field) is { } method &&
                GetterMatches(method, field) && method.Address != 0 &&
                program.Code.Get(method.Address) is { Instructions: <= 16 } &&
                pipeline.CoreBody(method) is { Problems.Count: 0, TryRegions.Count: 0, Blocks:
                    [{ Scope: -1, Statements: [HReturn { Value: HField { Object: HArg { Index: -1 } } read }] }] } &&
                read.Field == field && SameType(read.Type, field.Type) &&
                SameOwner(read.DeclaringType, field.DeclaringType)) found = method;
            return cache[field] = found;
        }
        return Run(h, Getter, program.Layouts.Of);
    }

    internal static int Run(HMethod h, Func<FieldDef, MethodDef?> getter, Func<TypeSig, TypeLayout> layout)
    {
        if (h.Problems.Count != 0 || h.TryRegions.Count != 0 || h.Blocks.Count is 0 or > 256 ||
            h.Blocks.Any(b => b.Scope != -1) || !Graph(h, out var edges)) return 0;
        int changed = 0;
        foreach (HVar variable in h.Locals.ToArray())
        {
            if (variable.AddressTaken || variable.Type is not ByRefSig { ElementType: PrimitiveSig scalar } ||
                scalar.Element is not (Il2CppTypeEnum.R4 or Il2CppTypeEnum.R8)) continue;
            var definitions = new List<(HBlock Block, int Index, HAssign Assign, HExpr Value)>();
            (HBlock Block, int Index, HAssign Assign)? read = null;
            bool valid = true, property = false;
            foreach (HBlock block in h.Blocks)
            for (int i = 0; i < block.Statements.Count; i++)
            {
                HStmt statement = block.Statements[i];
                int uses = 0;
                if (!Visit(statement, e => { if (e is HLocal l && l.Variable == variable) uses++; }))
                { valid = false; break; }
                if (uses == 0) continue;
                if (uses != 1) { valid = false; break; }
                if (statement is HAssign { Target: HLocal target, Value: HAddressOf address } assign &&
                    target.Variable == variable && SameType(target.Type, variable.Type) &&
                    address.Type is ByRefSig addressType &&
                    (SameType(addressType.ElementType, scalar) || SameType(addressType.ElementType, address.Target.Type)) &&
                    Source(address.Target, h.Method, getter, layout, out bool fromProperty))
                {
                    HExpr value;
                    if (SameType(address.Target.Type, scalar)) value = HirCopy.Of(address.Target);
                    else if (LeadingScalar(address.Target.Type, scalar, layout) is { } first)
                        value = new HField { Object = HirCopy.Of(address.Target), Field = first,
                            DeclaringType = first.DeclaringType.Sig, Type = scalar };
                    else { valid = false; break; }
                    definitions.Add((block, i, assign, value));
                    property |= fromProperty;
                }
                else if (statement is HAssign { Target: HLocal destination,
                    Value: HDeref { Pointer: HLocal pointer } dereference } use &&
                    pointer.Variable == variable && SameType(pointer.Type, variable.Type) &&
                    SameType(dereference.Type, scalar) && SameType(destination.Type, scalar) &&
                    SameType(destination.Variable.Type, scalar) && read == null)
                    read = (block, i, use);
                else { valid = false; break; }
            }
            if (!valid || !property || definitions.Count is < 2 or > 4 || read is not { } useSite ||
                !ReadonlyPaths(h, edges, definitions.Select(d => (d.Block, d.Index)).ToArray(),
                    useSite.Block, useSite.Index)) continue;
            variable.Type = scalar;
            foreach (var definition in definitions)
            {
                definition.Assign.Target.Type = scalar;
                definition.Assign.Value = definition.Value;
            }
            useSite.Assign.Value = new HLocal(variable) { Type = scalar };
            h.Notes.Add($"restored read-only property scalar phi: {variable.Name}, {definitions.Count} address definition(s)");
            changed++;
        }
        return changed;
    }

    private static bool GetterMatches(MethodDef method, FieldDef field) =>
        method.DeclaringType == field.DeclaringType && !method.IsStatic && !method.IsVirtual &&
        !method.IsAbstract && !method.IsGenericDefinition && !method.DeclaringType.IsGenericDefinition &&
        (method.Flags & MethodDef.AccessMask) == 6 && method.Parameters.Length == 0 &&
        SameType(method.ReturnType, field.Type) && method.Name.StartsWith("get_", StringComparison.Ordinal);

    private static bool SameType(TypeSig? a, TypeSig? b) => a != null && b != null &&
        a.Key.Length != 0 && a.Key == b.Key;

    private static bool SameOwner(TypeSig? type, TypeDef owner) => type == null ||
        type is TypeDefSig definition && definition.Definition == owner && SameType(type, owner.Sig);

    private static bool PlainDefinition(TypeDef owner) => !owner.IsGenericDefinition && !owner.IsEnum &&
        (owner.Flags & TypeDef.LayoutMask) != TypeDef.ExplicitLayout;

    private static bool Source(HExpr expression, MethodDef caller, Func<FieldDef, MethodDef?> getter,
        Func<TypeSig, TypeLayout> layout, out bool property)
    {
        property = false;
        if (expression is HArg argument)
        {
            TypeSig? type = argument.Index == -1 ? caller.IsStatic ? null : caller.DeclaringType.Sig :
                argument.Index >= 0 && argument.Index < caller.Parameters.Length ? caller.Parameters[argument.Index].Type : null;
            return type is TypeDefSig { Definition: { IsValueType: false } owner } &&
                PlainDefinition(owner) && SameType(argument.Type, type);
        }
        if (expression is not HField { Object: { } on } field || field.Field.IsStatic ||
            !PlainDefinition(field.Field.DeclaringType) || !field.Field.DeclaringType.Fields.Contains(field.Field) ||
            !SameOwner(field.DeclaringType, field.Field.DeclaringType) || !SameType(field.Type, field.Field.Type) ||
            !SameType(on.Type, field.Field.DeclaringType.Sig) ||
            on is not HArg && on.Type is not TypeDefSig { Definition: { IsValueType: true } } ||
            field.Field.DeclaringType.IsValueType && !KnownLayout(field.Field.DeclaringType.Sig, layout, out _) ||
            !Source(on, caller, getter, layout, out property)) return false;
        if (!AccessorFolding.IsAccessible(field.Field, caller) || AccessorIndex.IsBackingField(field.Field))
        {
            if (!AccessorIndex.IsBackingField(field.Field) || getter(field.Field) is not { } method ||
                !GetterMatches(method, field.Field)) return false;
            property = true;
        }
        return true;
    }

    private static bool KnownLayout(TypeSig type, Func<TypeSig, TypeLayout> layout, out TypeLayout result)
    {
        result = null!;
        if (type is not TypeDefSig { Definition: { IsValueType: true } owner } || !PlainDefinition(owner)) return false;
        TypeLayout found = layout(type);
        FieldDef[] fields = owner.Fields.Where(f => !f.IsStatic).ToArray();
        if (!found.Known || found.Size <= 0 || fields.Length == 0 || found.Fields.Length != fields.Length ||
            found.Fields.Select(s => s.Field).Distinct().Count() != fields.Length) return false;
        for (int i = 0; i < found.Fields.Length; i++)
        {
            FieldSlot slot = found.Fields[i];
            if (!fields.Contains(slot.Field) || !SameType(slot.Type, slot.Field.Type) ||
                slot.Offset < 0 || slot.Size <= 0 || slot.Size > found.Size ||
                slot.Offset > found.Size - slot.Size) return false;
            for (int j = 0; j < i; j++)
                if (slot.Offset < found.Fields[j].Offset + found.Fields[j].Size &&
                    found.Fields[j].Offset < slot.Offset + slot.Size) return false;
        }
        result = found;
        return true;
    }

    private static FieldDef? LeadingScalar(TypeSig? type, PrimitiveSig scalar, Func<TypeSig, TypeLayout> layout)
    {
        if (type == null || !KnownLayout(type, layout, out var found)) return null;
        int size = scalar.Element == Il2CppTypeEnum.R4 ? 4 : 8;
        var first = found.Fields.Where(f => f.Offset == 0 && f.Size == size && SameType(f.Type, scalar) &&
            (f.Field.Attrs & FieldDef.AccessMask) == 6).ToArray();
        return first.Length == 1 ? first[0].Field : null;
    }

    private static bool Graph(HMethod h, out Dictionary<HBlock, HBlock[]> edges)
    {
        edges = [];
        var blocks = h.Blocks.ToHashSet();
        foreach (HBlock b in h.Blocks)
        {
            if (b.Statements.Count == 0 || b.Statements.Take(b.Statements.Count - 1)
                .Any(s => s is HBranch or HJump or HSwitch or HReturn or HThrow or HEndFinally)) return false;
            HBlock[]? next = b.Statements[^1] switch
            {
                HJump jump => [jump.Target],
                HBranch branch => [branch.WhenTrue, branch.WhenFalse],
                HSwitch select => [.. select.Targets, select.Default],
                HReturn or HThrow => [],
                _ => null
            };
            if (next == null || next.Any(n => !blocks.Contains(n))) return false;
            edges[b] = next.Distinct().ToArray();
        }
        return true;
    }

    private static bool ReadonlyPaths(HMethod h, Dictionary<HBlock, HBlock[]> edges,
        (HBlock Block, int Index)[] definitions, HBlock readBlock, int readIndex)
    {
        var ancestors = new HashSet<HBlock> { readBlock };
        var pending = new Queue<HBlock>();
        pending.Enqueue(readBlock);
        while (pending.TryDequeue(out var next))
            foreach (var edge in edges)
                if (edge.Value.Contains(next) && ancestors.Add(edge.Key)) pending.Enqueue(edge.Key);
        if (!ancestors.Contains(h.Blocks[0]) || definitions.Any(d => !ancestors.Contains(d.Block) ||
            d.Block == readBlock && d.Index >= readIndex)) return false;
        var indegree = ancestors.ToDictionary(b => b, _ => 0);
        foreach (var edge in edges.Where(e => ancestors.Contains(e.Key)))
            foreach (var target in edge.Value.Where(ancestors.Contains)) indegree[target]++;
        var ready = new Queue<HBlock>(ancestors.Where(b => indegree[b] == 0));
        var order = new List<HBlock>();
        while (ready.TryDequeue(out var block))
        {
            order.Add(block);
            foreach (var target in edges[block].Where(ancestors.Contains))
                if (--indegree[target] == 0) ready.Enqueue(target);
        }
        if (order.Count != ancestors.Count) return false; // no repeated reads or definitions through a loop
        var state = ancestors.ToDictionary(b => b, _ => 0);
        state[h.Blocks[0]] = 1; // bit 0: no definition; bit 1: exactly one definition
        int reachedDefinitions = 0;
        bool reachedRead = false;
        foreach (HBlock block in order)
        {
            int current = state[block];
            if (current == 0) continue;
            int end = block == readBlock ? readIndex : block.Statements.Count;
            for (int i = 0; i < end; i++)
            {
                if (definitions.Contains((block, i)))
                {
                    if ((current & 2) != 0) return false;
                    current = 2;
                    reachedDefinitions++;
                }
                else if ((current & 2) != 0 && !Readonly(block.Statements[i])) return false;
            }
            if (block == readBlock)
            {
                if (current != 2) return false;
                reachedRead = true;
            }
            foreach (var target in edges[block].Where(ancestors.Contains)) state[target] |= current;
        }
        return reachedRead && reachedDefinitions == definitions.Length;
    }

    private static bool Readonly(HStmt statement) => statement switch
    {
        HAssign { Target: HLocal local, Value: var value } => !local.Variable.AddressTaken &&
            SameType(local.Type, local.Variable.Type) && Pure(value),
        HJump => true,
        HBranch branch => Pure(branch.Condition),
        HSwitch select => Pure(select.Value),
        _ => false
    };

    private static bool Pure(HExpr expression) => expression switch
    {
        HConst or HLocal or HArg => true,
        HField { Object: { } on, Field: { IsStatic: false } } => Pure(on),
        HAddressOf address => address.Target is HField or HLocal && Pure(address.Target),
        HUnary unary => Pure(unary.Operand),
        HBinary binary => Pure(binary.Left) && Pure(binary.Right),
        HCompare compare => Pure(compare.Left) && Pure(compare.Right),
        HConv convert => Pure(convert.Operand),
        HSelect select => Pure(select.Condition) && Pure(select.WhenTrue) && Pure(select.WhenFalse),
        HTypeExpr { Op: HTypeOp.Default, Operand: null } => true,
        _ => false
    };

    private static bool Visit(HStmt statement, Action<HExpr> visit) => statement switch
    {
        HAssign assign => Visit(assign.Target, visit) && Visit(assign.Value, visit),
        HEval eval => Visit(eval.Expression, visit),
        HBranch branch => Visit(branch.Condition, visit),
        HSwitch select => Visit(select.Value, visit),
        HReturn ret => ret.Value == null || Visit(ret.Value, visit),
        HThrow thr => thr.Exception == null || Visit(thr.Exception, visit),
        HJump => true,
        _ => false
    };

    private static bool Visit(HExpr expression, Action<HExpr> visit)
    {
        visit(expression);
        bool V(HExpr? e) => e == null || Visit(e, visit);
        return expression switch
        {
            HConst or HLocal or HArg or HMemberToken or HMethodPointer => true,
            HField field => V(field.Object),
            HElement element => V(element.Array) && V(element.Index),
            HArrayLength length => V(length.Array),
            HAddressOf address => V(address.Target),
            HDeref dereference => V(dereference.Pointer),
            HUnary unary => V(unary.Operand),
            HBinary binary => V(binary.Left) && V(binary.Right),
            HCompare compare => V(compare.Left) && V(compare.Right),
            HConv convert => V(convert.Operand),
            HCall call => V(call.This) && call.Arguments.All(V),
            HNewObject obj => obj.Arguments.All(V),
            HNewArray array => V(array.Length),
            HTypeExpr type => V(type.Operand),
            HCachedDelegate cached => V(cached.Cache) && V(cached.Creation),
            HSelect select => V(select.Condition) && V(select.WhenTrue) && V(select.WhenFalse),
            HOpaque opaque => opaque.Operands.All(V),
            _ => false
        };
    }
}
