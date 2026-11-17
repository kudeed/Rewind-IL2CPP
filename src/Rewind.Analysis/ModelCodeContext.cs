using Iced.Intel;
using Rewind.Analysis.X64;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Analysis;

/// <summary>Answers the lifter's questions about the program from the IL2CPP model and the image's own tables.</summary>
public sealed class ModelCodeContext : ILiftContext
{
    private ulong[] _starts;
    private readonly HashSet<ulong> _startSet;

    public Il2CppModel Model { get; }
    public NativeImage Image => Model.Image;

    /// <summary>Addresses of functions known never to return (filled in by helper discovery).</summary>
    public HashSet<ulong> NoReturn { get; } = [];
    // (An auto-property with an initializer may still be given another value in a constructor: Fork's.)

    /// <summary>Optional: argument layout per call target.</summary>
    public Func<ulong, CallShape?>? ShapeProvider { get; set; }

    /// <summary>Every known function start, ascending.</summary>
    public IReadOnlyList<ulong> FunctionStarts => _starts;

    public ModelCodeContext(Il2CppModel model)
    {
        Model = model;
        var starts = new HashSet<ulong>();
        foreach (ulong a in model.MethodsByAddress.Keys) starts.Add(a);
        foreach (ulong a in model.InstsByAddress.Keys) starts.Add(a);
        foreach (FunctionRange f in model.Image.FunctionTable)
            if (!f.Chained)
                starts.Add(f.Start);
        foreach (ulong a in model.Image.Exports.Values) starts.Add(a);
        foreach (ulong a in model.Binary.InvokerPointers) if (a != 0) starts.Add(a);
        foreach (ulong a in model.Binary.GenericAdjustorThunks) if (a != 0) starts.Add(a);
        foreach (ulong a in model.Binary.ReversePInvokeWrappers) if (a != 0) starts.Add(a);
        _startSet = starts;
        _starts = starts.ToArray();
        Array.Sort(_starts);
    }

    /// <summary>
    /// The same tables for another thread's analysis to ask through (see ProgramAnalysis.Fork): what is known of
    /// the image is shared and no longer changes; whom the questions about call targets go to is each one's own.
    /// </summary>
    private ModelCodeContext(ModelCodeContext source)
    {
        Model = source.Model;
        _starts = source._starts;
        _startSet = source._startSet;
        NoReturn = source.NoReturn;
    }

    public ModelCodeContext Fork() => new(this);

    public bool IsManaged(ulong address) => Model.MethodsByAddress.ContainsKey(address) || Model.InstsByAddress.ContainsKey(address);

    /// <summary>
    /// Small leaf functions have no entry in the unwind tables, so the tables alone do not list every function.
    /// Whatever a call instruction targets is a function too. Returns how many starts were added.
    /// </summary>
    public int DiscoverCallTargets()
    {
        NativeImage image = Image;
        if (image.Arch != CpuArch.X64) return 0;
        var found = new HashSet<ulong>();
        foreach (FunctionRange f in image.FunctionTable)
        {
            int length = (int)(f.End - f.Start);
            if (length <= 0 || !image.TrySpan(f.Start, length, out ReadOnlySpan<byte> code)) continue;
            var decoder = Decoder.Create(64, new ByteArrayCodeReader(code.ToArray()), f.Start);
            while (decoder.IP < f.End)
            {
                decoder.Decode(out Instruction ins);
                if (ins.IsInvalid) break;
                if (ins.FlowControl != FlowControl.Call || ins.Op0Kind != OpKind.NearBranch64) continue;
                ulong target = ins.NearBranchTarget;
                if (_startSet.Contains(target) || !image.IsCodeAddress(target)) continue;
                found.Add(target);
            }
        }
        if (found.Count == 0) return 0;
        // A target that lies inside a function the unwind tables describe is not a separate function.
        var ranges = image.FunctionTable.OrderBy(f => f.Start).ToArray();
        var starts = ranges.Select(f => f.Start).ToArray();
        int added = 0;
        foreach (ulong target in found)
        {
            int index = Array.BinarySearch(starts, target);
            if (index < 0) index = ~index - 1;
            if (index >= 0 && target > ranges[index].Start && target < ranges[index].End) continue;
            if (_startSet.Add(target)) added++;
        }
        _starts = _startSet.ToArray();
        Array.Sort(_starts);
        return added;
    }

    public bool IsFunctionStart(ulong address) => _startSet.Contains(address);

    public ulong NextFunctionStart(ulong address)
    {
        int index = Array.BinarySearch(_starts, address);
        index = index >= 0 ? index + 1 : ~index;
        return index < _starts.Length ? _starts[index] : 0;
    }

    public bool IsNoReturn(ulong target) => NoReturn.Contains(target);

    public CallShape? ShapeOf(ulong target) => ShapeProvider?.Invoke(target);

    /// <summary>Optional: the C++ exception tables of a function.</summary>
    public Func<ulong, CxxFunctionInfo?>? ExceptionProvider { get; set; }

    public CxxFunctionInfo? ExceptionInfo(ulong start) => ExceptionProvider?.Invoke(start);

    /// <summary>Optional: which call targets to lift in place.</summary>
    public Func<ulong, bool>? InlineProvider { get; set; }

    public bool ShouldInline(ulong target) => InlineProvider?.Invoke(target) ?? false;
}
