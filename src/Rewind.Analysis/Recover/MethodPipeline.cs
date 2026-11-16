using Rewind.Analysis.Abi;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Passes;
using Rewind.Analysis.Runtime;
using Rewind.Analysis.X64;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>One method after lifting and cleanup, ready for translation into managed terms.</summary>
public sealed class LiftedMethod
{
    public MethodDef Method = null!;
    public TypeSig[] ClassArguments = [];
    public TypeSig[] MethodArguments = [];
    public MethodAbi Abi = null!;
    public Function Function = null!;
    public NormalizeResult Normalization = null!;
    public List<FrameObject> Frame = [];
}

/// <summary>Runs the per-method stages in order: lift, apply the calling convention, normalize, promote the stack.</summary>
public sealed class MethodPipeline
{
    private readonly ProgramAnalysis _program;
    private readonly X64Lifter _lifter;
    private readonly Normalizer _normalizer;

    public MethodPipeline(ProgramAnalysis program)
    {
        _program = program;
        _lifter = program.NewLifter();
        _normalizer = new Normalizer(program);
    }

    /// <summary>
    /// What a recovered body uses, whatever the order and the temporaries: the methods it calls, the fields it
    /// touches, the types it makes and tests for, the numbers and texts in it, the kinds of arithmetic.
    /// </summary>
    internal static string Uses(HMethod h)
    {
        var used = new SortedSet<string>(StringComparer.Ordinal);
        void Note(HExpr e)
        {
            switch (e)
            {
                case HCall call: used.Add("call " + call.Method.FullName + "/" + call.Method.Parameters.Length); break;
                case HNewObject made: used.Add("new " + made.Constructor.DeclaringType.FullName + "/" + made.Constructor.Parameters.Length); break;
                case HNewArray array: used.Add("array of " + array.ElementType.Key); break;
                case HField field: used.Add("field " + field.Field.DeclaringType.FullName + "::" + field.Field.Name); break;
                case HTypeExpr type: used.Add("type " + type.Op + " " + type.Target.Key); break;
                case HMethodPointer pointer: used.Add("pointer to " + pointer.Method.FullName); break;
                case HMemberToken token: used.Add("token " + (token.Method?.FullName ?? token.Field?.Name)); break;
                case HOpaque native: used.Add("native " + native.Text); break;
                case HElement: used.Add("element"); break;
                case HArrayLength: used.Add("length"); break;
                case HBinary { Op: var op }: used.Add("op " + op); break;
                case HConst { Value: string text }: used.Add("text " + text); break;
                case HConst { Value: float or double } real: used.Add("real " + Convert.ToDouble(real.Value).ToString("R", System.Globalization.CultureInfo.InvariantCulture)); break;
                case HConst { Value: int or long or uint or ulong or short or ushort or byte or sbyte } number:
                {
                    long value = number.Value is ulong u ? unchecked((long)u) : Convert.ToInt64(number.Value);
                    if (value is < -1 or > 1) used.Add("number " + value);
                    break;
                }
            }
        }
        foreach (HBlock block in h.Blocks)
            foreach (HStmt s in block.Statements)
            {
                if (s is HThrow) used.Add("throw");
                if (s is HSwitch) used.Add("switch");
                FinallyFolding.Visit(s, Note);
            }
        return string.Join("\n", used);
    }

    /// <summary>
    /// The check for a function its caller names (it hands it a method's descriptor where that method takes its
    /// own): the caller says what the function is; what remains to be told is that it is not some other
    /// function that happens to take a descriptor there. A copy made for one source file is compiled apart
    /// from the original, so the two need not come out statement for statement alike. Read as the method - both
    /// completely - they must use the same things (<see cref="Uses"/>), and something at all.
    /// </summary>
    private bool VerifyNamed(ulong address, ulong[] originals)
    {
        foreach (ulong original in originals)
        {
            MethodDef? method = null;
            TypeSig[] classArgs = [], methodArgs = [];
            if (_program.Model.MethodsByAddress.TryGetValue(original, out List<MethodDef>? defs))
                method = defs.FirstOrDefault(m => m.DeclaringType.GenericParameters.Length == 0 && m.GenericParameters.Length == 0);
            if (method == null && _program.Model.InstsByAddress.TryGetValue(original, out List<MethodInst>? insts) && insts.Count != 0)
                (method, classArgs, methodArgs) = (insts[0].Method, insts[0].ClassArguments, insts[0].MethodArguments);
            if (method == null) continue;
            try
            {
                if (!_program.OwnUses.TryGetValue(original, out string? own))
                {
                    HMethod recovered = RecoverAt(method, classArgs, methodArgs, original);
                    _program.OwnUses[original] = own = recovered.Problems.Count == 0 ? Uses(recovered) : null;
                }
                if (string.IsNullOrEmpty(own)) return false;
                HMethod copy = RecoverAt(method, classArgs, methodArgs, address);
                return copy.Problems.Count == 0 && Uses(copy) == own;
            }
            catch (Exception e) when (e is not OutOfMemoryException and not StackOverflowException)
            {
                return false;
            }
        }
        return false;
    }

    /// <summary>For inspection: the listed method at <paramref name="original"/> recovered from its own code and from the code at <paramref name="address"/>.</summary>
    public (MethodDef? Method, HMethod? Own, HMethod? Copy, string? Error) RecoverBoth(ulong address, ulong original)
    {
        MethodDef? method = null;
        TypeSig[] classArgs = [], methodArgs = [];
        if (_program.Model.MethodsByAddress.TryGetValue(original, out List<MethodDef>? defs))
            method = defs.FirstOrDefault(m => m.DeclaringType.GenericParameters.Length == 0 && m.GenericParameters.Length == 0);
        if (method == null && _program.Model.InstsByAddress.TryGetValue(original, out List<MethodInst>? insts) && insts.Count != 0)
            (method, classArgs, methodArgs) = (insts[0].Method, insts[0].ClassArguments, insts[0].MethodArguments);
        if (method == null) return (null, null, null, "no listed method at that address");
        try
        {
            HMethod own = Build(Lift(method, classArgs, methodArgs, original));
            HMethod copy = Build(Lift(method, classArgs, methodArgs, address));
            return (method, own, copy, null);
        }
        catch (Exception e)
        {
            return (method, null, null, e.GetType().Name + ": " + e.Message + " @ " + e.StackTrace?.Split('\n').FirstOrDefault()?.Trim());
        }
    }

    /// <summary>Lifts and builds the method from the code at <paramref name="address"/>.</summary>
    private HMethod RecoverAt(MethodDef method, TypeSig[]? classArgs, TypeSig[]? methodArgs, ulong address)
    {
        // A definition's own type parameters as the arguments: the body its reference-type instantiations share
        // is being read, and there each of them stands for a reference type.
        HashSet<GenericParam>? own = null;
        foreach (TypeSig argument in (classArgs ?? []).Concat(methodArgs ?? []))
            if (argument is GenericParamSig parameter)
                (own ??= []).Add(parameter.Parameter);
        // (None of its own: none at all - also where this recovery was started from within such a one.)
        (HashSet<GenericParam>? builder, HashSet<GenericParam>? layouts) = (HirBuilder.OwnParameters, _program.Layouts.ReferenceParameters);
        (HirBuilder.OwnParameters, _program.Layouts.ReferenceParameters) = (own, own);
        try
        {
            return Build(Lift(method, classArgs, methodArgs, address));
        }
        finally
        {
            (HirBuilder.OwnParameters, _program.Layouts.ReferenceParameters) = (builder, layouts);
        }
    }

    public LiftedMethod Lift(MethodDef method, TypeSig[]? classArgs = null, TypeSig[]? methodArgs = null, ulong address = 0)
    {
        classArgs ??= [];
        methodArgs ??= [];
        MethodAbi abi = _program.Abi.For(method, classArgs, methodArgs);
        Function fn = _lifter.Lift(address != 0 ? address : method.Address);
        CheckShape(fn, "lifting");
        MathCalls.Run(fn, _program.Helpers);
        TrimReturns(fn, abi);
        NormalizeResult normalization = _normalizer.Run(fn);
        CheckShape(fn, "normalizing");
        if (Environment.GetEnvironmentVariable("REWIND_NO_ARG_TRIM") == null && TrimCallArguments(fn))
        {
            DeadCode.Run(fn);
            _normalizer.Cleanup(fn);
        }
        if (Environment.GetEnvironmentVariable("REWIND_NO_LEFTOVERS") == null && UndefinedValues.Run(fn, Leftovers(fn, abi)))
        {
            DeadCode.Run(fn);
            _normalizer.Cleanup(fn);
        }
        if (Environment.GetEnvironmentVariable("REWIND_NO_BLOCK_COPIES") == null)
        {
            if (BlockCopies.CollapseLoops(fn)) _normalizer.Cleanup(fn);
            if (BlockCopies.Extend(fn)) DeadCode.Run(fn);
            CheckShape(fn, "block copies");
        }
        if (Environment.GetEnvironmentVariable("REWIND_NO_EXCEPTION_STACKS") == null && ExceptionStacks.Run(fn, _program.Helpers)) _normalizer.Cleanup(fn);
        CheckShape(fn, "exception stacks");
        Dictionary<int, int> boxes = InPlaceBoxes(fn);
        if (Environment.GetEnvironmentVariable("REWIND_NO_PARKED") == null && ParkedAddresses.Run(fn, (call, input) => EscapeExtent(call, input, fn, boxes)))
        {
            DeadCode.Run(fn);
            _normalizer.Cleanup(fn);
        }
        CheckShape(fn, "parked addresses");
        ParkedAddresses.Canonicalize(fn);
        List<FrameObject> frame = StackPromotion.Run(fn, (call, input) => EscapeExtent(call, input, fn, boxes));
        DeadCode.Run(fn);
        // A promoted slot that held a stack address turns what was read through it into direct stack accesses:
        // with those in view, more can be promoted.
        for (int again = 0; again < 2 && ParkedAddresses.Canonicalize(fn); again++)
        {
            frame = StackPromotion.Run(fn, (call, input) => EscapeExtent(call, input, fn, boxes));
            DeadCode.Run(fn);
        }
        _normalizer.Cleanup(fn);
        CheckShape(fn, "stack promotion");
        if (LoopValues.Run(fn, ArgumentBits)) _normalizer.Cleanup(fn);
        CheckShape(fn, "loop values");
        if (Environment.GetEnvironmentVariable("REWIND_NO_CLASS_SPLIT") == null && ClassMerges.Run(fn, IsClassOrMethodSlot)) _normalizer.Cleanup(fn);
        CheckShape(fn, "class merges");
        return new LiftedMethod
        {
            Method = method,
            ClassArguments = classArgs,
            MethodArguments = methodArgs,
            Abi = abi,
            Function = fn,
            Normalization = normalization,
            Frame = frame,
        };
    }

    private static readonly bool CheckShapes = Environment.GetEnvironmentVariable("REWIND_CHECK_SHAPE") != null;

    /// <summary>
    /// Debugging aid (REWIND_CHECK_SHAPE): after each stage, every merged value must have one input per way into
    /// its block, and edges must be recorded at both ends. Reports the first stage that breaks this.
    /// </summary>
    private static void CheckShape(Function fn, string stage)
    {
        if (!CheckShapes || fn.Problems.Any(p => p.StartsWith("shape broken", StringComparison.Ordinal))) return;
        foreach (Block b in fn.Blocks)
        {
            foreach (Node phi in b.Phis)
                if (!phi.Dead && phi.In.Length != b.Preds.Count)
                {
                    fn.Problems.Add($"shape broken after {stage}: {phi} in {b} has {phi.In.Length} inputs for {b.Preds.Count} predecessors");
                    return;
                }
            foreach (Block s in b.Succs)
                if (!s.Preds.Contains(b) || !fn.Blocks.Contains(s))
                {
                    fn.Problems.Add($"shape broken after {stage}: edge {b} -> {s} is not recorded at its target");
                    return;
                }
            foreach (Block p in b.Preds)
                if (!p.Succs.Contains(b) || !fn.Blocks.Contains(p))
                {
                    fn.Problems.Add($"shape broken after {stage}: edge {p} -> {b} is not recorded at its source");
                    return;
                }
        }
    }

    public HMethod Recover(MethodDef method) => RecoverAt(method, null, null, 0);

    /// <summary>Recovers the body compiled for one instantiation of a generic method (or method of a generic type).</summary>
    public HMethod Recover(MethodInst inst) => RecoverAt(inst.Method, inst.ClassArguments, inst.MethodArguments, inst.Address);

    private GuardedAccessorFolding? _guardedAccessors;
    private InlineFolding? _inlineFolding;
    private static readonly bool NoStructsAgain = Environment.GetEnvironmentVariable("REWIND_NO_STRUCTS_AFTER_GUARDS") != null;

    private HMethod Build(LiftedMethod lifted)
    {
        _program.Building++;
        try
        {
            return BuildAll(lifted);
        }
        finally
        {
            _program.Building--;
        }
    }

    private HMethod BuildAll(LiftedMethod lifted)
    {
        // The method asked for: nothing else is being built around it.
        bool before = _program.OwnTranslation;
        Func<ulong, ulong[], bool>? verifier = _program.NamedVerifier;
        _program.OwnTranslation = _program.Building == 1;
        _program.NamedVerifier = VerifyNamed; // asked while this pipeline translates (it is not lifting then): it can do the reading
        HMethod result;
        try
        {
            result = BuildCore(lifted);
        }
        finally
        {
            _program.OwnTranslation = before;
            _program.NamedVerifier = verifier;
        }
        // A networked property read in the middle of a struct being filled kept the stores apart (its check is a
        // branch): with the read put back they are one run, which may be one struct made in one go.
        if ((_guardedAccessors ??= new GuardedAccessorFolding(this)).Run(result) && !NoStructsAgain) StructFolding.Run(result, _program, this);
        (_inlineFolding ??= new InlineFolding(this, _program)).Run(result);
        if (WrapperFolding.Lift(result, this))
        {
            StructFolding.Run(result, _program, this);
            _inlineFolding.Run(result);
        }
        AccessorFolding.Run(result, _program);
        LibraryInternals.Run(result, _program);
        InitializerOrder.Run(result);
        UnsetLocals.Run(result);
        FlagMarkers(result);
        return result;
    }

    /// <summary>
    /// Whatever is still expressed as a native operation in the finished method is a gap, whether or not the
    /// step that left it there said so: the rebuilt code stops when it gets there. Only the filler after a
    /// call that never returns is exempt, since nothing reaches it.
    /// </summary>
    private static void FlagMarkers(HMethod method)
    {
        HashSet<string>? found = null;
        void Visit(HExpr? e)
        {
            switch (e)
            {
                case null: return;
                case HOpaque o:
                    if (o.Text != "unreachable") (found ??= []).Add(o.Text);
                    foreach (HExpr a in o.Operands) Visit(a);
                    return;
                case HField f: Visit(f.Object); return;
                case HElement el: Visit(el.Array); Visit(el.Index); return;
                case HArrayLength len: Visit(len.Array); return;
                case HAddressOf a: Visit(a.Target); return;
                case HDeref d: Visit(d.Pointer); return;
                case HUnary u: Visit(u.Operand); return;
                case HBinary b: Visit(b.Left); Visit(b.Right); return;
                case HCompare c: Visit(c.Left); Visit(c.Right); return;
                case HConv c: Visit(c.Operand); return;
                case HCall call: Visit(call.This); foreach (HExpr a in call.Arguments) Visit(a); return;
                case HNewObject n: foreach (HExpr a in n.Arguments) Visit(a); return;
                case HNewArray na: Visit(na.Length); return;
                case HTypeExpr t: Visit(t.Operand); return;
                case HSelect s: Visit(s.Condition); Visit(s.WhenTrue); Visit(s.WhenFalse); return;
            }
        }
        foreach (HBlock block in method.Blocks)
        {
            foreach (HStmt s in block.Statements)
            {
                switch (s)
                {
                    case HAssign a: Visit(a.Target); Visit(a.Value); break;
                    case HEval e: Visit(e.Expression); break;
                    case HReturn r: Visit(r.Value); break;
                    case HThrow t: Visit(t.Exception); break;
                    case HBranch b: Visit(b.Condition); break;
                    case HSwitch sw: Visit(sw.Value); break;
                }
            }
        }
        if (found == null || method.Problems.Count != 0) return;
        // Nothing reported this method as incomplete, yet it is.
        foreach (string text in found) method.Problems.Add($"native operation left in the code ({text})");
    }

    private static readonly bool NoSharedConstructors = Environment.GetEnvironmentVariable("REWIND_NO_SHARED_CONSTRUCTORS") != null;

    /// <summary>The type argument whose code a type argument's code is shared with: "object" for a reference type (in a struct's arguments too).</summary>
    private TypeSig Shared(TypeSig type)
    {
        if (type is PointerSig or ByRefSig or GenericParamSig or OpaqueSig) return type;
        if (!type.IsValueType) return _program.Model.Sigs.Primitive(Rewind.Runtime.Il2CppTypeEnum.Object);
        if (type is GenericInstSig g)
        {
            TypeSig[] arguments = g.Arguments.Select(Shared).ToArray();
            return arguments.SequenceEqual(g.Arguments) ? type : _program.Model.Sigs.GenericInst(g.Definition, arguments);
        }
        return type;
    }

    private readonly Dictionary<(MethodDef, string), HMethod?> _constructorBodies = [];
    internal static readonly bool NoConstructorFlows = Environment.GetEnvironmentVariable("REWIND_NO_CONSTRUCTOR_FLOWS") != null;
    private readonly HashSet<MethodDef> _recovering = [];

    /// <summary>
    /// The recovered statements of a constructor, when they are complete and a plain run without branches:
    /// what a creation site is compared with to put an inlined constructor back.
    /// </summary>
    internal HMethod? ConstructorBody(MethodDef constructor, TypeSig[] classArguments) =>
        ConstructorFlow(constructor, classArguments) is { Blocks: [{ Statements: [.., HReturn { Value: null }] }] } body ? body : null;

    /// <summary>
    /// The recovered statements of a constructor, when they are complete, branches and all: what a creation site
    /// is compared with along every way through it (ConstructorFolding).
    /// </summary>
    internal HMethod? ConstructorFlow(MethodDef constructor, TypeSig[] classArguments)
    {
        string key = classArguments.Length == 0 ? "" : string.Join(",", classArguments.Select(a => a.Key));
        if (_constructorBodies.TryGetValue((constructor, key), out HMethod? known)) return known;
        if (!_recovering.Add(constructor)) return null; // being recovered right now, further up
        HMethod? body = null;
        try
        {
            LiftedMethod? lifted = null;
            if (constructor.DeclaringType.GenericParameters.Length == 0)
            {
                if (constructor.Address != 0) lifted = Lift(constructor);
            }
            else
            {
                // The instantiation's own code - or, for reference types among the type arguments, the code
                // they share (every class runs what was made for "object").
                for (int form = 0; form < (NoSharedConstructors ? 1 : 2) && lifted == null; form++)
                {
                    TypeSig[] wanted = form == 0 ? classArguments : classArguments.Select(Shared).ToArray();
                    if (form == 1 && wanted.SequenceEqual(classArguments)) break;
                    foreach (MethodInst inst in _program.InstsOf(constructor))
                    {
                        if (inst.Address == 0 || inst.MethodArguments.Length != 0 || inst.ClassArguments.Length != wanted.Length) continue;
                        bool same = true;
                        for (int i = 0; i < wanted.Length && same; i++) same = ReferenceEquals(inst.ClassArguments[i], wanted[i]);
                        if (!same) continue;
                        lifted = Lift(inst.Method, inst.ClassArguments, inst.MethodArguments, inst.Address);
                        break;
                    }
                }
            }
            if (lifted != null)
            {
                HMethod h = BuildCore(lifted);
                if (h.Problems.Count == 0 && h.Blocks.Count != 0 && h.TryRegions.Count == 0 &&
                    (h.Blocks.Count == 1 ? h.Blocks[0].Statements is [.., HReturn { Value: null }] : !NoConstructorFlows))
                    body = h;
            }
        }
        catch (Exception)
        {
            body = null;
        }
        finally
        {
            _recovering.Remove(constructor);
        }
        return _constructorBodies[(constructor, key)] = body;
    }

    private readonly Dictionary<MethodDef, HMethod?> _coreBodies = [];

    /// <summary>
    /// The recovered statements of a method as they stand before accessors are put back into them - what code
    /// pasted from that method into another looks like there. Null when the method has no code of its own or
    /// was not recovered completely.
    /// </summary>
    internal HMethod? CoreBody(MethodDef method)
    {
        if (_coreBodies.TryGetValue(method, out HMethod? known)) return known;
        if (method.Address == 0 || method.DeclaringType.GenericParameters.Length != 0 || method.GenericParameters.Length != 0) return null;
        if (!_recovering.Add(method)) return null; // being recovered right now, further up
        HMethod? body = null;
        try
        {
            HMethod h = BuildCore(Lift(method));
            if (h.Problems.Count == 0) body = h;
        }
        catch (Exception)
        {
            body = null;
        }
        finally
        {
            _recovering.Remove(method);
        }
        return _coreBodies[method] = body;
    }

    private readonly Dictionary<MethodInst, HMethod?> _instanceBodies = [];
    private readonly HashSet<ulong> _recoveringAt = [];

    /// <summary>
    /// CoreBody for one instantiation of a method of a generic class: the statements the code compiled for those
    /// type arguments gives. Null when it was not recovered completely.
    /// </summary>
    internal HMethod? CoreBody(MethodInst inst)
    {
        if (_instanceBodies.TryGetValue(inst, out HMethod? known)) return known;
        if (inst.Address == 0 || !_recoveringAt.Add(inst.Address)) return null;
        HMethod? body = null;
        try
        {
            HMethod h = BuildCore(Lift(inst.Method, inst.ClassArguments, inst.MethodArguments, inst.Address));
            if (h.Problems.Count == 0) body = h;
        }
        catch (Exception)
        {
            body = null;
        }
        finally
        {
            _recoveringAt.Remove(inst.Address);
        }
        return _instanceBodies[inst] = body;
    }

    /// <summary>The same statements as CoreBody gives, made anew: the caller's own, to change as it likes.</summary>
    internal HMethod? FreshCoreBody(MethodDef method)
    {
        if (method.Address == 0 || method.DeclaringType.GenericParameters.Length != 0 || method.GenericParameters.Length != 0) return null;
        if (!_recovering.Add(method)) return null;
        try
        {
            HMethod h = BuildCore(Lift(method));
            return h.Problems.Count == 0 ? h : null;
        }
        catch (Exception)
        {
            return null;
        }
        finally
        {
            _recovering.Remove(method);
        }
    }

    /// <summary>Everything up to, but not including, the rewriting of private field accesses into accessor calls.</summary>
    private HMethod BuildCore(LiftedMethod lifted)
    {
        _program.Translations++;
        try
        {
            return BuildCoreOf(lifted);
        }
        finally
        {
            _program.Translations--;
        }
    }

    private HMethod BuildCoreOf(LiftedMethod lifted)
    {
        (HirBuilder builder, HMethod result) = BuildRounds(lifted);
        // Code for two classes merged because their fields sit at the same offsets: un-merge and build again.
        for (int round = 0; round < 2 && builder.MergedObjects.Count != 0; round++)
        {
            if (!ClassMerges.SplitAt(lifted.Function, builder.MergedObjects)) break;
            _normalizer.Cleanup(lifted.Function);
            (builder, result) = BuildRounds(lifted);
        }
        // Stack memory that reads as two different things is usually a slot the compiler reused: give each
        // lifetime its own memory and build again.
        // (Separating one pair of lifetimes can show the next - a temporary that serves as the result of one
        // call and then of another - so this repeats a few times.)
        Function fn = lifted.Function;
        for (int round = 0; round < 3 && builder.FrameConflicts.Count != 0; round++)
        {
            ParkedAddresses.Canonicalize(fn);
            Dictionary<int, int> boxes = InPlaceBoxes(fn);
            HirBuilder current = builder;
            if (StackSplitting.Run(fn, current.FrameConflicts, (call, input) => EscapeExtent(call, input, fn, boxes, current),
                    (call, input) => WritesOnly(call, input, current), ReadsOnly, WritesAndNothingElse, current.ReachThrough) <= 0)
                break;
            Dictionary<int, int> after = InPlaceBoxes(fn);
            ParkedAddresses.Canonicalize(fn);
            lifted.Frame = StackPromotion.Run(fn, (call, input) => EscapeExtent(call, input, fn, after, current));
            DeadCode.Run(fn);
            _normalizer.Cleanup(fn);
            (builder, result) = BuildRounds(lifted);
        }
        FieldOwners.Run(result, _program.Model);
        ConstantTyping.Run(result, _program);
        AddressMerges.Run(result);
        FusionWeaving.Run(result);
        FinallyFolding.Run(result, _program);
        WrapperFolding.Retype(result, _program);
        StructFolding.Run(result, _program, this);
        StructConstruction.Run(result);
        ConstructorFolding.Run(result, _program, this);
        DelegateFolding.Run(result, _program);
        // A constructor that hands a lambda to its base class reads as one run of statements only now, and
        // so does the place it was pasted into.
        if (LambdaCacheFolding.Run(result)) ConstructorFolding.Run(result, _program, this, again: true);
        DeadStores.Run(result);
        EnumeratorLoops.Run(result, _program);
        if (LateMoves.Run(result)) StructConstruction.Run(result);
        return result;
    }

    private (HirBuilder Builder, HMethod Result) BuildRounds(LiftedMethod lifted)
    {
        var builder = new HirBuilder(_program, lifted, null, _program.FrameHints?.Invoke(lifted.Function.Address));
        HMethod result = builder.Build();
        // Types of merged values and of stack objects are discovered while building; when any was, build
        // again knowing them.
        for (int round = 0; round < 4 && (builder.PhiTypesRefined || builder.FrameTypesRefined); round++)
        {
            builder = new HirBuilder(_program, lifted, builder.PhiTypes, builder.RefinedFrameTypes);
            result = builder.Build();
        }
        // Each build may learn types the next one starts from. Still learning after the last one means this
        // result was translated with types that have since changed: it cannot be trusted as it is.
        if (builder.FrameTypesRefined && result.Problems.Count < 64) result.Problems.Add("types of stack objects did not settle");
        return (builder, result);
    }

    /// <summary>
    /// A return captures rax and xmm0; keep only what this method's return type actually uses. A value narrower
    /// than the register is cut to its size, which also discards whatever the upper register bits held.
    /// </summary>
    private static void TrimReturns(Function fn, MethodAbi abi)
    {
        var builder = new IrBuilder(fn) { InsertBeforeTerminator = true };
        foreach (Block b in fn.Blocks)
        {
            Node? ret = b.Terminator;
            if (ret?.Op != Op.Return || ret.In.Length != 3) continue;
            switch (abi.Return)
            {
                case ReturnKind.Void:
                    ret.In = [];
                    break;
                case ReturnKind.Float:
                    ret.In = [ret.In[1]];
                    break;
                case ReturnKind.Double:
                    ret.In = [ret.In[1], ret.In[2]];
                    break;
                default:
                {
                    Node value = ret.In[0];
                    if (abi.ReturnSize is 1 or 2 or 4)
                    {
                        builder.Current = b;
                        builder.CurrentAddr = ret.Addr;
                        value = builder.Trunc(value, VTExtensions.IntOfBytes(abi.ReturnSize));
                    }
                    ret.In = [value];
                    break;
                }
            }
        }
    }

    /// <summary>
    /// How many low bits of <paramref name="value"/> a call looks at, given the parameters it is passed as:
    /// a bool or byte parameter is read as 8 bits no matter what else the register holds.
    /// </summary>
    private int ArgumentBits(Node call, Node value)
    {
        if (call.Aux is not CallInfo info || info.Indirect || info.Intrinsic != null) return 64;
        CallTarget target = _program.Resolve(info.Target);
        if (target.Helper != null || !target.IsManaged) return 64;
        int bits = 0;
        for (int i = 0; i < call.In.Length && i < info.Slots.Count; i++)
        {
            if (!ReferenceEquals(call.In[i], value)) continue;
            ArgSlot slot = info.Slots[i];
            int position = slot.Kind == ArgSlotKind.IntReg ? slot.Index : slot.Kind == ArgSlotKind.Stack ? slot.Index + 4 : -1;
            if (position < 0) return 64;
            void Consider(MethodAbi abi)
            {
                if (!abi.Known)
                {
                    bits = 64;
                    return;
                }
                foreach (AbiParam p in abi.Params)
                {
                    if (p.Position != position) continue;
                    bool small = p.Role == ParamRole.Argument && p.Pass == PassKind.Integer && p.Size is 1 or 2 or 4 && p.Type is not ByRefSig;
                    bits = Math.Max(bits, small ? p.Size * 8 : 64);
                    return;
                }
                bits = 64; // not a parameter of this candidate at all
            }
            foreach (MethodDef m in target.Methods) Consider(_program.Abi.For(m, [], []));
            foreach (MethodInst inst in target.Insts) Consider(_program.Abi.For(inst));
        }
        return bits == 0 ? 64 : bits;
    }

    /// <summary>
    /// How many bytes a callee may touch through a stack address passed as an argument: the size of the struct
    /// for by-reference struct parameters and return buffers, unknown otherwise.
    /// </summary>
    /// <summary>
    /// True when the callee only writes the memory a pointer argument points to before anything reads it: the
    /// return buffer, or an "out" parameter (C# requires the callee to assign it first).
    /// </summary>
    private bool WritesOnly(Node call, int inputIndex)
    {
        if (BlockCopies.Access(call, inputIndex, _program.Helpers, out _, out bool blockReads, out _)) return !blockReads;
        if (call.Aux is not CallInfo info || info.Indirect || info.Intrinsic != null || inputIndex >= info.Slots.Count) return false;
        ArgSlot slot = info.Slots[inputIndex];
        int position = slot.Kind == ArgSlotKind.IntReg ? slot.Index : slot.Kind == ArgSlotKind.Stack ? slot.Index + 4 : -1;
        if (position < 0) return false;
        CallTarget target = _program.Resolve(info.Target);
        if (target.Helper != null || !target.IsManaged) return false;
        bool all = true, any = false;
        void Consider(MethodDef method, MethodAbi abi)
        {
            foreach (AbiParam p in abi.Params)
            {
                if (p.Position != position) continue;
                any = true;
                bool writes = p.Role == ParamRole.ReturnBuffer ||
                              (p.Role == ParamRole.Argument && p.ArgumentIndex >= 0 && p.ArgumentIndex < method.Parameters.Length && method.Parameters[p.ArgumentIndex].IsOut);
                all &= writes;
            }
        }
        foreach (MethodDef m in target.Methods) Consider(m, _program.Abi.For(m, [], []));
        foreach (MethodInst inst in target.Insts) Consider(inst.Method, _program.Abi.For(inst));
        return any && all;
    }

    /// <summary>True for a fill, or a copy seen from its destination: without that memory being read, the call does nothing.</summary>
    private bool WritesAndNothingElse(Node call, int inputIndex) =>
        BlockCopies.Access(call, inputIndex, _program.Helpers, out _, out bool blockReads, out bool blockWrites) && blockWrites && !blockReads;

    /// <summary>True when the callee only reads the memory a pointer argument points to (the source of a copy, a value being boxed).</summary>
    private bool ReadsOnly(Node call, int inputIndex)
    {
        if (BlockCopies.Access(call, inputIndex, _program.Helpers, out _, out _, out bool blockWrites)) return !blockWrites;
        if (call.Aux is not CallInfo { Indirect: false, Intrinsic: null } info || inputIndex >= info.Slots.Count ||
            info.Slots[inputIndex] is not { Kind: ArgSlotKind.IntReg } slot || _program.Resolve(info.Target).Helper is not { } helper)
            return false;
        return HelperReads(call, info, helper.Kind, slot.Index) > 0;
    }

    /// <summary>
    /// How many bytes a runtime helper reads through the stack address in argument <paramref name="position"/>, and
    /// does nothing else with: Box(klass, &amp;value) one value of the class, a C++ throw the wrapper of the exception
    /// (one pointer). -1 when that is not known (the unbox helpers write a value whose size is not the class's).
    /// </summary>
    private int HelperReads(Node call, CallInfo info, HelperKind kind, int position)
    {
        if (NoHelperExtents) return -1;
        if (kind == HelperKind.CxxThrow && position == 0) return _program.Model.Image.PointerSize;
        if (kind != HelperKind.Box || position != 1) return -1;
        for (int i = 0; i < info.Slots.Count && i < call.In.Length; i++)
        {
            if (info.Slots[i] is not { Kind: ArgSlotKind.IntReg, Index: 0 }) continue;
            if (SlotClass(call.In[i]) is not { IsValueType: true } type || type.ContainsGenericParameter) return -1;
            var (size, _, known) = _program.Layouts.SizeOf(type);
            return known && size > 0 ? size : -1;
        }
        return -1;
    }

    private static readonly bool NoHelperExtents = Environment.GetEnvironmentVariable("REWIND_NO_HELPER_EXTENTS") != null;

    /// <summary>The class a metadata slot value names, when it names one.</summary>
    private TypeSig? SlotClass(Node value)
    {
        if (value.Op != Op.SlotValue) return null;
        ulong slot = (ulong)value.Imm;
        return _program.Defaults.Slots.TryGetValue(slot, out TypeDef? def) ? def.Sig
            : _program.Model.ResolveUsageSlot(slot) is { Kind: UsageKind.TypeInfo, Type: { } usage } ? usage : null;
    }

    /// <summary>
    /// Values boxed in place: generated code writes an object header (the class, then a mark) on the stack in
    /// front of a copy of the value and passes that address where an object is expected. Stack offset of each
    /// such header -> the size of the whole (header and the largest value given that header there).
    /// </summary>
    private Dictionary<int, int> InPlaceBoxes(Function fn)
    {
        var boxes = new Dictionary<int, int>();
        if (!fn.Params.TryGetValue(X64Lifter.VarRsp, out Node? sp0)) return boxes;
        int header = 2 * _program.Model.Image.PointerSize;
        foreach (Block b in fn.Blocks)
            foreach (Node n in b.Nodes)
            {
                if (n.Dead || n.Op != Op.Store || n.In[1].Op != Op.SlotValue || StackOffset(sp0, n.In[0]) is not int at) continue;
                TypeSig? type = SlotClass(n.In[1]);
                if (type is not { IsValueType: true } || type.ContainsGenericParameter) continue;
                var (size, _, known) = _program.Layouts.SizeOf(type);
                if (!known) continue;
                boxes[at] = Math.Max(boxes.GetValueOrDefault(at), header + Math.Max(1, size));
            }
        return boxes;
    }

    /// <summary>
    /// A call is lifted with whatever the argument registers and the first stack slots held: the callee's
    /// signature is not known at that point. What no method the target can be takes as a parameter is not an
    /// argument but a leftover of earlier code - and as long as the call "uses" it, that leftover (a class
    /// pointer, a stack address, a merge of unrelated values) has to be explained for nothing.
    /// </summary>
    private bool TrimCallArguments(Function fn)
    {
        bool changed = false;
        foreach (Block b in fn.Blocks)
            foreach (Node call in b.Nodes)
            {
                if (call.Dead || call.Op is not (Op.Call or Op.TailCall) || call.Aux is not CallInfo { Indirect: false, Intrinsic: null } info) continue;
                if (info.Slots.Count != call.In.Length || call.In.Length == 0) continue;
                CallTarget target = _program.Resolve(info.Target);
                if (!target.IsManaged || target.Helper != null || target.Forwarded) continue;
                var integer = new HashSet<int>();
                var floating = new HashSet<int>();
                bool unknown = false;
                void Consider(MethodAbi abi)
                {
                    if (!abi.Known)
                    {
                        unknown = true;
                        return;
                    }
                    foreach (AbiParam p in abi.Params) (p.Pass == PassKind.Float ? floating : integer).Add(p.Position);
                }
                foreach (MethodDef m in target.Methods) Consider(_program.Abi.For(m, [], []));
                foreach (MethodInst inst in target.Insts) Consider(_program.Abi.For(inst));
                if (unknown) continue;

                var inputs = new List<Node>(call.In.Length);
                var slots = new List<ArgSlot>(call.In.Length);
                for (int i = 0; i < call.In.Length; i++)
                {
                    ArgSlot slot = info.Slots[i];
                    bool taken = slot.Kind switch
                    {
                        ArgSlotKind.IntReg => integer.Contains(slot.Index),
                        ArgSlotKind.Stack => integer.Contains(slot.Index + 4) || floating.Contains(slot.Index + 4),
                        ArgSlotKind.FloatReg => floating.Contains(slot.Index / 4),
                        _ => true,
                    };
                    if (!taken) continue;
                    inputs.Add(call.In[i]);
                    slots.Add(slot);
                }
                if (inputs.Count == call.In.Length) continue;
                call.In = inputs.ToArray();
                info.Slots = slots;
                changed = true;
            }
        return changed;
    }

    /// <summary>
    /// The entry values the calling convention gives no meaning: the scratch registers, and the argument
    /// registers this method has no parameter for.
    /// </summary>
    private static readonly bool NoSavedLeftovers = Environment.GetEnvironmentVariable("REWIND_NO_SAVED_LEFTOVERS") != null;

    private static Func<Node, bool> Leftovers(Function fn, MethodAbi abi)
    {
        var leftovers = new HashSet<Node>();
        void Add(int variable)
        {
            if (fn.Params.TryGetValue(variable, out Node? entry)) leftovers.Add(entry);
        }
        Add(0);   // rax
        Add(10);  // r10
        Add(11);  // r11
        // What the caller left in a register this method must preserve means nothing to the method itself: it
        // is only saved and put back. Writing one byte of such a register ("mov bl, [isOn]") keeps the caller's
        // other seven, which no one reads.
        if (!NoSavedLeftovers)
            foreach (int saved in X64Lifter.CalleeSaved)
                if (saved != X64Lifter.VarRsp)
                    Add(saved);
        if (abi.Known)
        {
            var taken = new HashSet<int>();
            foreach (AbiParam p in abi.Params)
                if (p.Pass != PassKind.Float) taken.Add(p.Position);
            for (int position = 0; position < X64Lifter.IntArgRegs.Length; position++)
                if (!taken.Contains(position)) Add(X64Lifter.IntArgRegs[position]);
        }
        return leftovers.Contains;
    }

    private bool IsClassOrMethodSlot(ulong slot) =>
        _program.Defaults.Slots.ContainsKey(slot) ||
        _program.Model.ResolveUsageSlot(slot) is { Kind: UsageKind.TypeInfo or UsageKind.MethodDef or UsageKind.MethodRef };

    private static int? StackOffset(Node sp0, Node n)
    {
        if (ReferenceEquals(n, sp0)) return 0;
        if (n.Op == Op.Add && ReferenceEquals(n.In[0], sp0) && n.In[1].IsConst && IrBuilder.SImm(n.In[1]) is > -0x4000000 and < 0x4000000)
            return (int)IrBuilder.SImm(n.In[1]);
        return null;
    }

    private int EscapeExtent(Node call, int inputIndex, Function fn, Dictionary<int, int> boxes)
    {
        int extent = EscapeExtent(call, inputIndex, out bool asObject);
        if (extent > 0 || !asObject || boxes.Count == 0 || !fn.Params.TryGetValue(X64Lifter.VarRsp, out Node? sp0)) return extent;
        // A stack address where an object is expected: the value boxed in place there.
        return StackOffset(sp0, call.In[inputIndex]) is int at && boxes.TryGetValue(at, out int box) ? box : -1;
    }

    private int EscapeExtent(Node call, int inputIndex) => EscapeExtent(call, inputIndex, out _);

    /// <summary>
    /// The parameter a call input is, by the method the call was found to mean when the function was built:
    /// exact where the call's target alone names several methods sharing one body. False when the call was not
    /// resolved that way; a null parameter means the method takes nothing in that position.
    /// </summary>
    private static bool Chosen(HirBuilder built, Node call, int inputIndex, out MethodDef method, out MethodAbi abi, out AbiParam? parameter)
    {
        method = null!;
        abi = null!;
        parameter = null;
        if (!built.ChosenCalls.TryGetValue(call, out var chosen) || call.Aux is not CallInfo info || inputIndex >= info.Slots.Count) return false;
        ArgSlot slot = info.Slots[inputIndex];
        int position = slot.Kind == ArgSlotKind.IntReg ? slot.Index : slot.Kind == ArgSlotKind.Stack ? slot.Index + 4 : -1;
        if (position < 0) return false;
        method = chosen.Method;
        abi = chosen.Abi;
        foreach (AbiParam p in abi.Params)
            if (p.Position + chosen.Shift == position)
            {
                parameter = p;
                break;
            }
        return true;
    }

    private int EscapeExtent(Node call, int inputIndex, Function fn, Dictionary<int, int> boxes, HirBuilder built)
    {
        if (!Chosen(built, call, inputIndex, out _, out MethodAbi abi, out AbiParam? p) || p == null) return EscapeExtent(call, inputIndex, fn, boxes);
        int size = -1;
        if (p.Role == ParamRole.ReturnBuffer) size = abi.ReturnSize;
        else if (p.Pass == PassKind.Indirect) size = p.Size;
        else if (p.Type is ByRefSig byRef) size = _program.Layouts.SizeOf(byRef.ElementType).Size;
        else if (p.Role == ParamRole.This && p.Type?.Definition is { IsValueType: true }) size = _program.Layouts.SizeOf(p.Type).Size;
        if (size > 0) return size;
        bool asObject = p.Role is ParamRole.This or ParamRole.Argument && p.Pass == PassKind.Integer &&
                        p.Type is { IsValueType: false } and not ByRefSig and not PointerSig && !p.Type.ContainsGenericParameter;
        if (asObject && fn.Params.TryGetValue(X64Lifter.VarRsp, out Node? sp0) && StackOffset(sp0, call.In[inputIndex]) is int at &&
            boxes.TryGetValue(at, out int box))
            return box;
        return -1;
    }

    private bool WritesOnly(Node call, int inputIndex, HirBuilder built)
    {
        if (!Chosen(built, call, inputIndex, out MethodDef method, out _, out AbiParam? p) || p == null) return WritesOnly(call, inputIndex);
        return p.Role == ParamRole.ReturnBuffer ||
               (p.Role == ParamRole.Argument && p.ArgumentIndex >= 0 && p.ArgumentIndex < method.Parameters.Length && method.Parameters[p.ArgumentIndex].IsOut);
    }

    /// <param name="asObject">Set when every method the call may reach takes an object reference in that position.</param>
    private int EscapeExtent(Node call, int inputIndex, out bool asObject)
    {
        asObject = false;
        if (BlockCopies.Access(call, inputIndex, _program.Helpers, out int blockBytes, out _, out _)) return blockBytes;
        if (call.Aux is not CallInfo info || info.Indirect || info.Intrinsic != null) return -1;
        if (inputIndex >= info.Slots.Count) return -1;
        ArgSlot slot = info.Slots[inputIndex];
        int position = slot.Kind == ArgSlotKind.IntReg ? slot.Index : slot.Kind == ArgSlotKind.Stack ? slot.Index + 4 : -1;
        if (position < 0) return -1;

        CallTarget target = _program.Resolve(info.Target);
        if (target.Helper != null) return HelperReads(call, info, target.Helper.Kind, position);

        int extent = -1, objects = 0, others = 0;
        void Consider(MethodAbi abi)
        {
            foreach (AbiParam p in abi.Params)
            {
                if (p.Position != position) continue;
                int size = -1;
                if (p.Role == ParamRole.ReturnBuffer) size = abi.ReturnSize;
                else if (p.Pass == PassKind.Indirect) size = p.Size;
                else if (p.Type is ByRefSig byRef) size = _program.Layouts.SizeOf(byRef.ElementType).Size;
                else if (p.Role == ParamRole.This && p.Type?.Definition is { IsValueType: true }) size = _program.Layouts.SizeOf(p.Type).Size;
                if (size > 0)
                {
                    extent = Math.Max(extent, size);
                    others++;
                }
                else
                {
                    extent = int.MinValue; // some candidate gives no bound
                    if (p.Role is ParamRole.This or ParamRole.Argument && p.Pass == PassKind.Integer &&
                        p.Type is { IsValueType: false } and not ByRefSig and not PointerSig && !p.Type.ContainsGenericParameter)
                        objects++;
                    else others++;
                }
            }
        }
        foreach (MethodDef m in target.Methods) Consider(_program.Abi.For(m, [], []));
        foreach (MethodInst inst in target.Insts) Consider(_program.Abi.For(inst));
        asObject = objects > 0 && others == 0;
        return extent > 0 ? extent : -1;
    }
}
