using Rewind.Analysis.Abi;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Runtime;
using Rewind.Analysis.X64;
using Rewind.Model;

namespace Rewind.Analysis;

/// <summary>What a direct call target is, in program terms.</summary>
public sealed class CallTarget
{
    public HelperInfo? Helper;
    public List<MethodDef> Methods = [];
    public List<MethodInst> Insts = [];
    /// <summary>The address is the native implementation of these "extern" methods, not their generated wrapper.</summary>
    public bool Forwarded;
    public bool IsManaged => Methods.Count != 0 || Insts.Count != 0;
}

/// <summary>Everything about one loaded program that per-function analysis needs.</summary>
public sealed class ProgramAnalysis
{
    public Il2CppModel Model { get; }
    public ModelCodeContext Context { get; }
    public RuntimeHelpers Helpers { get; }
    public LayoutCalculator Layouts { get; }
    /// <summary>What lies where in the replicated memory of networked objects (Photon Fusion).</summary>
    public ReplicatedLayout Replicated { get; }
    public Win64Abi Abi { get; }
    public DefaultsTable Defaults { get; }
    public KlassLayout Klass { get; }

    private readonly Dictionary<ulong, CallShape?> _shapes = [];

    /// <summary>
    /// Native functions that implement managed "extern" methods, found from the binary itself: the wrapper
    /// IL2CPP generates for an internal call does nothing but hand its arguments to the implementation, so
    /// whatever such a wrapper jumps to is that method. Callers usually call the implementation directly.
    /// </summary>
    public Dictionary<ulong, List<MethodDef>> ForwardedMethods { get; } = [];
    public Dictionary<ulong, List<MethodInst>> ForwardedInsts { get; } = [];

    /// <summary>Unlisted functions whose code equals that of listed methods exactly (see <see cref="CopyMatcher"/>).</summary>
    public CopyMatcher.Result ExactCopies { get; private set; } = new();
    private readonly Dictionary<ulong, CallTarget> _copyTargets = [];

    /// <summary>Unlisted functions identified as private copies of managed methods (see <see cref="InlineCopyFinder"/>).</summary>
    public Dictionary<ulong, InlineCopy> InlineCopies { get; private set; } = [];

    private Recover.AccessorIndex? _accessors;
    /// <summary>Which method of a class is the plain accessor of which field (computed on demand).</summary>
    public Recover.AccessorIndex Accessors => _accessors ??= new Recover.AccessorIndex(this);

    private Dictionary<MethodDef, List<MethodInst>>? _instsOf;

    /// <summary>The compiled instantiations of a generic method or of a method of a generic type.</summary>
    public IReadOnlyList<MethodInst> InstsOf(MethodDef method) =>
        InstTable().TryGetValue(method, out List<MethodInst>? found) ? found : [];

    private Dictionary<MethodDef, List<MethodInst>> InstTable()
    {
        if (_instsOf != null) return _instsOf;
        var table = new Dictionary<MethodDef, List<MethodInst>>();
        foreach (MethodInst inst in Model.MethodInsts)
        {
            if (inst.Address == 0) continue;
            if (!table.TryGetValue(inst.Method, out List<MethodInst>? list)) table[inst.Method] = list = [];
            list.Add(inst);
        }
        return _instsOf = table;
    }

    private Dictionary<ulong, Rewind.Binary.FunctionRange>? _ranges;
    private readonly Dictionary<ulong, CxxFunctionInfo?> _cxx = [];

    /// <summary>The unwind-table entry of the function starting at <paramref name="address"/>, if it has one.</summary>
    public Rewind.Binary.FunctionRange? RangeOf(ulong address) =>
        RangeTable().TryGetValue(address, out Rewind.Binary.FunctionRange found) ? found : null;

    private Dictionary<ulong, Rewind.Binary.FunctionRange> RangeTable()
    {
        if (_ranges != null) return _ranges;
        var table = new Dictionary<ulong, Rewind.Binary.FunctionRange>();
        foreach (Rewind.Binary.FunctionRange f in Model.Image.FunctionTable)
            if (!f.Chained)
                table.TryAdd(f.Start, f);
        return _ranges = table;
    }

    // (One table for the program and every fork of it, made by whoever asks first.)
    private readonly Lazy<(Dictionary<ulong, PInvokeImport> BySlot, Dictionary<MethodDef, PInvokeImport> ByMethod)> _pinvoke;

    private (Dictionary<ulong, PInvokeImport> BySlot, Dictionary<MethodDef, PInvokeImport> ByMethod) PInvoke => _pinvoke.Value;

    private (Dictionary<ulong, PInvokeImport>, Dictionary<MethodDef, PInvokeImport>) ScanPInvoke()
    {
        var bySlot = new Dictionary<ulong, PInvokeImport>();
        var byMethod = new Dictionary<MethodDef, PInvokeImport>();
        var shared = new HashSet<ulong>();
        foreach (PInvokeImport import in PInvokeImports.Scan(Model, Helpers))
        {
            byMethod[import.Method] = import;
            if (!bySlot.TryAdd(import.CacheSlot, import)) shared.Add(import.CacheSlot);
        }
        foreach (ulong slot in shared) bySlot.Remove(slot); // two declarations, one cache: not a usable key
        return (bySlot, byMethod);
    }

    /// <summary>
    /// Set by the method pipeline: the check for a function that its caller names (it is handed a method's
    /// descriptor): whether, read as the listed method at the given address, it uses what that method uses.
    /// </summary>
    public Func<ulong, ulong[], bool>? NamedVerifier { get; set; }

    /// <summary>What listed methods use (see MethodPipeline.Uses; null: not recovered completely), by address.</summary>
    public Dictionary<ulong, string?> OwnUses { get; } = [];

    /// <summary>
    /// Whether what is being translated right now is the method a recovery was asked for (and not one recovered
    /// on the way), and how many translations are under way inside one another.
    /// </summary>
    /// <summary>How many functions that a caller named were checked, how many were copies, and the time it took.</summary>
    public int NamedChecks, NamedCopies;
    public long NamedCheckTime;
    private static readonly bool CopyTrace = Environment.GetEnvironmentVariable("REWIND_COPY_TRACE") != null;

    /// <summary>
    /// The functions being checked right now as copies of a method: there, the function is read as that method -
    /// in the two readings the check compares, not in what those ask for in turn (the statements of another
    /// method are the same whether or not a check is under way).
    /// </summary>
    private readonly HashSet<(ulong, MethodDef)> _assumed = [];
    private int _assumedAt;
    public bool CheckingCopies => _assumed.Count != 0 && Auxiliary == _assumedAt;
    public bool AssumedCopy(ulong address, MethodDef method) => Auxiliary == _assumedAt && _assumed.Contains((address, method));

    public bool OwnTranslation;
    public int Translations, Building;
    /// <summary>How many recoveries for the use of another recovery are under way inside one another (see MethodPipeline.Ask).</summary>
    public int Auxiliary;

    /// <summary>
    /// What recoveries ask each other for: one for the program and all its forks. And the same for the
    /// recoveries that look for a field's accessor (AccessorIndex): while one of those runs, a field has no
    /// accessor to ask for, so what is recovered on the way may read differently and is kept apart.
    /// </summary>
    internal Recover.RecoveryCache Kept { get; } = new();
    internal Recover.RecoveryCache KeptForAccessors { get; } = new();

    /// <summary>For REWIND_CHECK_KEPT: how many bodies are kept, and which of them were changed after they were kept (none should be).</summary>
    public (int Kept, List<string> Changed) CheckKept()
    {
        List<string> changed = Kept.Changed();
        changed.AddRange(KeptForAccessors.Changed());
        return (Kept.Count + KeptForAccessors.Count, changed);
    }

    private readonly Dictionary<(ulong, string), bool> _copiesOf = [];

    /// <summary>
    /// Whether the unlisted function at <paramref name="address"/> does what a listed method does, as far as
    /// the recovery of both can tell (<see cref="NamedVerifier"/>). Asked where a caller names the method, and of
    /// the code that the instantiation it names has: its own where that is listed, otherwise the code it shares
    /// with every instantiation that differs from it in reference types only. Two functions of very different
    /// sizes are not copies of each other; that much is told without reading them.
    /// </summary>
    public bool IsCopyOf(ulong address, MethodDef method, MethodInst? named)
    {
        if (NamedVerifier == null) return false;
        TypeSig Shared(TypeSig t) => t switch
        {
            GenericParamSig => Model.Sigs.Primitive(Rewind.Runtime.Il2CppTypeEnum.Object),
            GenericInstSig { IsValueType: true } g => Model.Sigs.GenericInst(g.Definition!, g.Arguments.Select(Shared).ToArray()),
            _ => t.IsValueType || t is PointerSig or ByRefSig ? t : Model.Sigs.Primitive(Rewind.Runtime.Il2CppTypeEnum.Object),
        };
        static string KeyOf(IEnumerable<TypeSig> classArguments, IEnumerable<TypeSig> methodArguments) =>
            string.Join(",", classArguments.Select(a => a.Key)) + "|" + string.Join(",", methodArguments.Select(a => a.Key));

        var originals = new List<ulong>();
        string asked = "";
        if (named == null)
        {
            if (method.Address != 0) originals.Add(method.Address);
        }
        else
        {
            string exact = KeyOf(named.ClassArguments, named.MethodArguments);
            asked = KeyOf(named.ClassArguments.Select(Shared), named.MethodArguments.Select(Shared));
            IReadOnlyList<MethodInst> insts = InstsOf(method);
            foreach (MethodInst inst in insts)
                if (KeyOf(inst.ClassArguments, inst.MethodArguments) == exact && !originals.Contains(inst.Address))
                    originals.Add(inst.Address);
            if (originals.Count == 0)
                foreach (MethodInst inst in insts)
                    if (KeyOf(inst.ClassArguments, inst.MethodArguments) == asked && !originals.Contains(inst.Address))
                        originals.Add(inst.Address);
        }
        if (_copiesOf.TryGetValue((address, method.Index + ":" + asked), out bool known)) return known;
        _copiesOf[(address, method.Index + ":" + asked)] = false; // while it is being checked (the check may come back here)
        bool same = false;
        ulong size = SizeBound(address);
        NamedChecks++;
        var watch = System.Diagnostics.Stopwatch.StartNew();
        _assumed.Add((address, method));
        int assumedAt = _assumedAt;
        _assumedAt = Auxiliary;
        try
        {
        foreach (ulong original in originals)
        {
            ulong listed = SizeBound(original);
            if (size != ulong.MaxValue && listed != ulong.MaxValue && (size > 2 * listed + 32 || listed > 2 * size + 32)) continue;
            if (!NamedVerifier(address, [original])) continue;
            same = true;
            break;
        }
        }
        finally
        {
            _assumed.Remove((address, method));
            _assumedAt = assumedAt;
        }
        if (same) NamedCopies++;
        NamedCheckTime += watch.ElapsedMilliseconds;
        if (CopyTrace) Console.Error.WriteLine($"[copy] 0x{address:X} named {method.FullName} ({originals.Count} listed): {(same ? "a copy" : "not one")}, {watch.ElapsedMilliseconds} ms");
        return _copiesOf[(address, method.Index + ":" + asked)] = same;
    }

    private readonly Dictionary<ulong, bool> _inlinable = [];

    /// <summary>
    /// Whether a call target is code generated for one method's own use rather than a method: a C++ lambda (a
    /// finally block's body the compiler did not inline) or a private helper. Such code is lifted in place; it
    /// has no managed meaning of its own. Only small functions of the generated-code section that nothing names.
    /// </summary>
    /// <summary>
    /// An upper bound on the size of the function at <paramref name="target"/>: its unwind-table entry, or - for
    /// a leaf function, which has none - the distance to the next known function.
    /// </summary>
    private ulong SizeBound(ulong target)
    {
        if (RangeOf(target) is { } range) return range.End - range.Start;
        if (!Context.IsFunctionStart(target)) return ulong.MaxValue;
        ulong next = Context.NextFunctionStart(target);
        return next > target ? next - target : ulong.MaxValue;
    }

    public bool ShouldInline(ulong target)
    {
        lock (_inlinable)
        {
            if (_inlinable.TryGetValue(target, out bool known)) return known;
            if (Environment.GetEnvironmentVariable("REWIND_NO_INLINE") == "1") return _inlinable[target] = false;
            bool result = Model.Image.SectionAt(target) is { Name: "il2cpp", IsExecutable: true } &&
                          !Context.NoReturn.Contains(target) && Helpers.At(target) == null &&
                          SizeBound(target) <= 2048 &&
                          ExceptionInfo(target) == null && Resolve(target) is { IsManaged: false, Helper: null };
            return _inlinable[target] = result;
        }
    }

    /// <summary>
    /// Optional: types of stack memory known before recovery, by function address (offset from the entry stack
    /// pointer -> type). Fed by a type predictor, or by the compiler's records when measuring.
    /// </summary>
    public Func<ulong, IReadOnlyDictionary<int, TypeSig>?>? FrameHints { get; set; }

    /// <summary>The P/Invoke declaration whose resolved function pointer is cached at <paramref name="slot"/>.</summary>
    public PInvokeImport? PInvokeAtSlot(ulong slot) => PInvoke.BySlot.GetValueOrDefault(slot);

    /// <summary>What a P/Invoke declaration imports (library, entry point, ...), when its wrapper could be read.</summary>
    public PInvokeImport? PInvokeOf(MethodDef method) => PInvoke.ByMethod.GetValueOrDefault(method);

    /// <summary>All P/Invoke declarations whose wrapper could be read.</summary>
    public IEnumerable<PInvokeImport> PInvokeDeclarations => PInvoke.ByMethod.Values;

    /// <summary>The C++ exception tables of a function (try blocks, handlers, states), or null when it has none.</summary>
    public CxxFunctionInfo? ExceptionInfo(ulong address)
    {
        if (_cxx.TryGetValue(address, out CxxFunctionInfo? known)) return known;
        CxxFunctionInfo? info = null;
        if (RangeOf(address) is { } range && UnwindData.TryGetHandler(Model.Image, range, out _, out ulong data))
        {
            info = UnwindData.ReadFh4(Model.Image, address, data);
            if (info is { HasRegions: false }) info = null;
        }
        return _cxx[address] = info;
    }

    private bool _allocatorSearched;
    private MethodDef? _rawAllocator, _typeFromHandle;

    private void FindAllocator()
    {
        if (_allocatorSearched) return;
        _allocatorSearched = true;
        MethodDef? Find(string type, string name) => Model.FindType(type)?.Methods.FirstOrDefault(m =>
            m.Name == name && m.IsStatic && m.Parameters.Length == 1 && m.GenericParameters.Length == 0);
        _typeFromHandle = Find("System.Type", "GetTypeFromHandle");
        _rawAllocator = Find("System.Runtime.Serialization.FormatterServices", "GetUninitializedObject")
                        ?? Find("System.Runtime.CompilerServices.RuntimeHelpers", "GetUninitializedObject");
        if (_typeFromHandle == null) _rawAllocator = null;
    }

    /// <summary>
    /// The class library's own way of making an object without running a constructor (what the machine code
    /// does when a constructor was inlined); null when this build's library does not have one.
    /// </summary>
    public MethodDef? RawAllocator
    {
        get
        {
            FindAllocator();
            return _rawAllocator;
        }
    }

    /// <summary>Type.GetTypeFromHandle, which turns a type token into the Type the allocator takes.</summary>
    public MethodDef? TypeFromHandle
    {
        get
        {
            FindAllocator();
            return _typeFromHandle;
        }
    }

    private readonly Dictionary<ulong, MethodDef?> _internalCalls = [];

    /// <summary>
    /// The "extern" method an internal-call name denotes. Generated code looks such a method up the first time
    /// it is called, by a name of the form "Namespace.Type::Method(ParameterTypes)".
    /// </summary>
    public MethodDef? InternalCallNamed(ulong nameAddress, out string name)
    {
        name = Model.Image.TryCString(nameAddress) ?? "";
        if (_internalCalls.TryGetValue(nameAddress, out MethodDef? known)) return known;
        return _internalCalls[nameAddress] = FindInternalCall(name);
    }

    private static string SignatureName(TypeSig type) => type switch
    {
        ByRefSig r => SignatureName(r.ElementType) + "&",
        PointerSig p => SignatureName(p.ElementType) + "*",
        SzArraySig a => SignatureName(a.ElementType) + "[]",
        ArraySig a => SignatureName(a.ElementType) + "[" + new string(',', Math.Max(0, a.Rank - 1)) + "]",
        GenericInstSig g => g.Definition.ReflectionName + "<" + string.Join(",", g.Arguments.Select(SignatureName)) + ">",
        GenericParamSig g => g.Parameter.Name,
        PrimitiveSig { Definition: null } p => "System." + p.Element switch
        {
            Rewind.Runtime.Il2CppTypeEnum.I => "IntPtr",
            Rewind.Runtime.Il2CppTypeEnum.U => "UIntPtr",
            Rewind.Runtime.Il2CppTypeEnum.TypedByRef => "TypedReference",
            _ => p.Element.ToString(),
        },
        _ => type.Definition?.ReflectionName ?? type.DisplayName,
    };

    private static int ParameterCount(string list)
    {
        if (list.Length == 0) return 0;
        int depth = 0, count = 1;
        foreach (char c in list)
        {
            if (c is '<' or '[') depth++;
            else if (c is '>' or ']') depth--;
            else if (c == ',' && depth == 0) count++;
        }
        return count;
    }

    private MethodDef? FindInternalCall(string name)
    {
        int split = name.IndexOf("::", StringComparison.Ordinal);
        if (split <= 0) return null;
        string rest = name[(split + 2)..];
        int open = rest.IndexOf('(');
        string methodName = open < 0 ? rest : rest[..open];
        string? parameters = open < 0 ? null : rest[(open + 1)..].TrimEnd(')').Replace(" ", "").Replace("0...", "");
        TypeDef? type = Model.FindType(name[..split]);
        if (type == null) return null;

        const ushort InternalCall = 0x1000;
        List<MethodDef> candidates = type.Methods.Where(m => m.Name == methodName && (m.ImplFlags & InternalCall) != 0).ToList();
        if (candidates.Count > 1 && parameters != null)
        {
            List<MethodDef> exact = candidates.Where(m => string.Join(",", m.Parameters.Select(p => SignatureName(p.Type))) == parameters).ToList();
            if (exact.Count == 0)
            {
                int count = ParameterCount(parameters);
                exact = candidates.Where(m => m.Parameters.Length == count).ToList();
            }
            candidates = exact;
        }
        return candidates.Count == 1 ? candidates[0] : null;
    }

    private CodeIndex? _code;
    /// <summary>Position-independent descriptions of the image's functions (computed on demand).</summary>
    public CodeIndex Code => _code ??= new CodeIndex(Context);

    public ProgramAnalysis(Il2CppModel model, RuntimeHelpers helpers, ModelCodeContext? context = null)
    {
        Model = model;
        Helpers = helpers;
        _pinvoke = new(ScanPInvoke, LazyThreadSafetyMode.ExecutionAndPublication);
        Context = context ?? new ModelCodeContext(model);
        Context.ShapeProvider = ShapeOf;
        Context.ExceptionProvider = ExceptionInfo;
        Context.InlineProvider = ShouldInline;
        Layouts = new LayoutCalculator(model);
        Replicated = new ReplicatedLayout(model);
        Abi = new Win64Abi(model, Layouts);
        Defaults = DefaultsTable.Locate(model);
        Klass = KlassLayout.For(model.Version, model.Image.PointerSize);
        foreach (var (address, info) in helpers.ByAddress)
            if (info.NoReturn)
                Context.NoReturn.Add(address);
        FindForwarders();
        ExactCopies = CopyMatcher.Find(this);
        InlineCopies = InlineCopyFinder.Find(this);
        _shapes.Clear();
    }

    /// <summary>
    /// The same program for another thread to recover methods with. What was found out about the program when
    /// it was loaded is shared and no longer changes: the model, the support functions, the copies, the tables
    /// of the image. Everything that is filled in or set while methods are recovered is the fork's own - what
    /// was computed so far, what is being recovered right now and inside what, the accessors found - so that no
    /// thread sees another's unfinished work. A thread uses one fork, and one fork is used by one thread.
    /// </summary>
    public ProgramAnalysis Fork() => new(this);

    private ProgramAnalysis(ProgramAnalysis source)
    {
        Model = source.Model;
        Helpers = source.Helpers;
        Kept = source.Kept;
        KeptForAccessors = source.KeptForAccessors;
        _pinvoke = source._pinvoke;
        Context = source.Context.Fork();
        Context.ShapeProvider = ShapeOf;
        Context.ExceptionProvider = ExceptionInfo;
        Context.InlineProvider = ShouldInline;
        Layouts = new LayoutCalculator(Model);
        Replicated = new ReplicatedLayout(Model);
        Abi = new Win64Abi(Model, Layouts);
        Defaults = source.Defaults;
        Klass = source.Klass;
        ForwardedMethods = source.ForwardedMethods;
        ForwardedInsts = source.ForwardedInsts;
        ExactCopies = source.ExactCopies;
        InlineCopies = source.InlineCopies;
        FrameHints = source.FrameHints;
        // (Tables made on first use: made now, by the one thread that forks, and then only read.)
        _instsOf = source.InstTable();
        _ranges = source.RangeTable();
        source.FindAllocator();
        (_allocatorSearched, _rawAllocator, _typeFromHandle) = (true, source._rawAllocator, source._typeFromHandle);
    }

    private void FindForwarders()
    {
        if (Model.Image.Arch != Rewind.Binary.CpuArch.X64) return;
        const ushort InternalCall = 0x1000;
        CodeIndex index = Code;

        ulong ImplementationOf(ulong wrapper)
        {
            FunctionCode? code = index.Get(wrapper);
            if (code == null || code.Instructions > 24) return 0;
            ulong found = 0;
            foreach (ulong callee in code.Callees)
            {
                if (Context.IsManaged(callee) || Helpers.At(callee) != null) continue;
                if (found != 0 && found != callee) return 0; // more than one candidate: not a plain forwarder
                found = callee;
            }
            return found;
        }

        foreach (MethodDef m in Model.Methods)
        {
            if (m.Address == 0 || (m.ImplFlags & InternalCall) == 0) continue;
            ulong target = ImplementationOf(m.Address);
            if (target == 0) continue;
            if (!ForwardedMethods.TryGetValue(target, out List<MethodDef>? list)) ForwardedMethods[target] = list = [];
            if (!list.Contains(m)) list.Add(m);
        }
        foreach (var (address, insts) in Model.InstsByAddress)
        {
            if (!insts.Any(i => (i.Method.ImplFlags & InternalCall) != 0)) continue;
            ulong target = ImplementationOf(address);
            if (target == 0) continue;
            if (!ForwardedInsts.TryGetValue(target, out List<MethodInst>? list)) ForwardedInsts[target] = list = [];
            foreach (MethodInst inst in insts)
                if ((inst.Method.ImplFlags & InternalCall) != 0 && !list.Contains(inst))
                    list.Add(inst);
        }
    }

    public X64Lifter NewLifter() => new(Context);

    public CallTarget Resolve(ulong address)
    {
        var target = new CallTarget { Helper = Helpers.At(address) };
        if (Model.MethodsByAddress.TryGetValue(address, out List<MethodDef>? methods)) target.Methods = methods;
        if (Model.InstsByAddress.TryGetValue(address, out List<MethodInst>? insts)) target.Insts = insts;
        if (!target.IsManaged && target.Helper == null && ExactCopies.Copies.TryGetValue(address, out ulong[]? originals))
        {
            // The same code as these listed methods: a call to it is a call to one of them.
            if (!_copyTargets.TryGetValue(address, out CallTarget? copy))
            {
                copy = new CallTarget();
                foreach (ulong original in originals)
                {
                    if (Model.MethodsByAddress.TryGetValue(original, out List<MethodDef>? ms))
                        foreach (MethodDef m in ms)
                            if (!copy.Methods.Contains(m))
                                copy.Methods.Add(m);
                    if (Model.InstsByAddress.TryGetValue(original, out List<MethodInst>? instances))
                        foreach (MethodInst i in instances)
                            if (!copy.Insts.Contains(i))
                                copy.Insts.Add(i);
                }
                _copyTargets[address] = copy;
            }
            return copy;
        }
        if (!target.IsManaged && target.Helper == null)
        {
            if (ForwardedMethods.TryGetValue(address, out List<MethodDef>? forwarded)) target.Methods = forwarded;
            if (ForwardedInsts.TryGetValue(address, out List<MethodInst>? forwardedInsts)) target.Insts = forwardedInsts;
            target.Forwarded = target.IsManaged;
            if (!target.IsManaged && InlineCopies.TryGetValue(address, out InlineCopy? copy))
            {
                if (copy.Insts.Count != 0) target.Insts = copy.Insts;
                else target.Methods = [copy.Method];
            }
            // A function that only jumps on to another (the linker makes these where a call cannot reach
            // what it calls directly): a call to it is a call to that one.
            if (!target.IsManaged && !NoThunkCalls && Code.ThunkTarget(address) is var onward && onward != address && onward != 0)
            {
                CallTarget beyond = Resolve(onward);
                if (beyond.IsManaged || beyond.Helper != null) return beyond;
            }
        }
        return target;
    }

    private static readonly bool NoThunkCalls = Environment.GetEnvironmentVariable("REWIND_NO_THUNK_CALLS") != null;

    private static CallShape ShapeFrom(MethodAbi abi)
    {
        int count = abi.Params.Count;
        var shape = new CallShape
        {
            Count = count, IsFloat = new bool[Math.Max(4, count)], IsDouble = new bool[Math.Max(4, count)],
            Returns = ReturnFrom(abi),
        };
        foreach (AbiParam p in abi.Params)
        {
            if (p.Position >= shape.IsFloat.Length) continue;
            shape.IsFloat[p.Position] = p.Pass == PassKind.Float;
            shape.IsDouble[p.Position] = p.Pass == PassKind.Float && p.IsDouble;
        }
        return shape;
    }

    private static CallReturn ReturnFrom(MethodAbi abi) => abi.Return switch
    {
        ReturnKind.Void => CallReturn.Void,
        ReturnKind.Float => CallReturn.Float,
        ReturnKind.Double => CallReturn.Double,
        _ => CallReturn.Integer,
    };

    private static bool SameShape(CallShape a, CallShape b)
    {
        if (a.Count != b.Count) return false;
        for (int i = 0; i < Math.Min(4, a.Count); i++)
            if (a.IsFloat[i] != b.IsFloat[i] || a.IsDouble[i] != b.IsDouble[i])
                return false;
        return true;
    }

    /// <summary>
    /// Argument layout for a call target. When several methods share the address (identical code folding) the
    /// layout is used only if they all agree; otherwise the lifter captures every argument register.
    /// </summary>
    public CallShape? ShapeOf(ulong address)
    {
        if (_shapes.TryGetValue(address, out CallShape? cached)) return cached;
        CallShape? shape = null;
        HelperInfo? helper = Helpers.At(address);
        if (helper is { Kind: HelperKind.MathFunction })
        {
            int n = helper.FloatArgs;
            shape = new CallShape
            {
                Count = n, IsFloat = new bool[4], IsDouble = new bool[4],
                Returns = helper.IsDouble ? CallReturn.Double : CallReturn.Float,
            };
            for (int i = 0; i < n; i++)
            {
                shape.IsFloat[i] = true;
                shape.IsDouble[i] = helper.IsDouble;
            }
        }
        else if (helper is { Kind: HelperKind.Modf })
        {
            // modf(x, &whole): a floating point value, then a pointer; the fraction comes back as floating point.
            shape = new CallShape
            {
                Count = 2, IsFloat = [true, false, false, false], IsDouble = [helper.IsDouble, false, false, false],
                Returns = helper.IsDouble ? CallReturn.Double : CallReturn.Float,
            };
        }
        else if (helper != null && helper.Kind is not (HelperKind.InterfaceInvoker or HelperKind.VirtualInvoker
                or HelperKind.GenericInterfaceInvoker or HelperKind.GenericVirtualInvoker or HelperKind.ConstrainedInvoker
                or HelperKind.ArrayGetAt or HelperKind.ArraySetAt or HelperKind.ArrayGetAddressAt))
        {
            int n = helper.IntArgs;
            shape = new CallShape
            {
                Count = n, IsFloat = new bool[Math.Max(4, n)], IsDouble = new bool[Math.Max(4, n)],
                Returns = helper.ReturnsValue ? CallReturn.Integer : CallReturn.Void,
            };
        }
        else
        {
            bool conflict = false;
            void Merge(MethodAbi abi)
            {
                if (!abi.Known)
                {
                    conflict = true;
                    return;
                }
                CallShape s = ShapeFrom(abi);
                if (shape == null) shape = s;
                else if (!SameShape(shape, s)) conflict = true;
                else if (shape.Returns != s.Returns) shape.Returns = CallReturn.Unknown;
            }
            CallTarget target = Resolve(address);
            foreach (MethodDef m in target.Methods) Merge(Abi.For(m, [], []));
            foreach (MethodInst inst in target.Insts) Merge(Abi.For(inst));
            if (conflict) shape = null;
            // The implementation of an internal call takes no trailing MethodInfo.
            else if (shape != null && target.Forwarded && shape.Count > 0)
                shape = new CallShape { Count = shape.Count - 1, IsFloat = shape.IsFloat, IsDouble = shape.IsDouble, Returns = shape.Returns };
        }
        _shapes[address] = shape;
        return shape;
    }
}
