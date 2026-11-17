using System.Diagnostics;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Where the time of a recovery goes, for REWIND_RECOVERY_STATS: how long the methods asked for take, and how
/// much of that is spent on what they ask for in turn - the bodies of other methods to compare pasted code
/// with, the lists of those a class has, its accessors. Counted over all threads; a piece of work inside
/// another of the same or another kind is counted with the outer one only.
/// </summary>
public static class RecoveryStats
{
    public static readonly bool On = Environment.GetEnvironmentVariable("REWIND_RECOVERY_STATS") != null;

    public enum Kind { Method, Body, Constructor, Fresh, Templates, Accessor, Passing, Count }

    private static readonly long[] Ticks = new long[(int)Kind.Count], Calls = new long[(int)Kind.Count], Inner = new long[(int)Kind.Count];
    [ThreadStatic] private static int _depth;

    /// <summary>Starts a piece of work; hand what it returns to <see cref="End"/>.</summary>
    public static long Begin()
    {
        if (!On) return 0;
        _depth++;
        return Stopwatch.GetTimestamp();
    }

    public static void End(Kind kind, long started)
    {
        if (!On) return;
        _depth--;
        Interlocked.Increment(ref Calls[(int)kind]);
        // (The method asked for is the outermost; everything else is counted where it is not inside another.)
        if (_depth == (kind == Kind.Method ? 0 : 1)) Interlocked.Add(ref Ticks[(int)kind], Stopwatch.GetTimestamp() - started);
        else Interlocked.Increment(ref Inner[(int)kind]);
    }

    private static long _notKept;

    /// <summary>Something was made where it could not be kept for others (see InlineFolding.Keep): counted, on or off.</summary>
    public static void NotKept() => Interlocked.Increment(ref _notKept);

    public static string Report()
    {
        var parts = new List<string>();
        for (int k = 0; k < (int)Kind.Count; k++)
            parts.Add($"{(Kind)k} {Calls[k]} ({Inner[k]} inside another) {Ticks[k] / (double)Stopwatch.Frequency:F1} s");
        parts.Add($"made but not kept {_notKept}");
        return string.Join("; ", parts);
    }
}
