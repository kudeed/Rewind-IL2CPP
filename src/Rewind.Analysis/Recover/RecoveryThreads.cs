namespace Rewind.Analysis.Recover;

/// <summary>
/// Recovers many methods on several threads and hands the results back in the order they were asked for.
///
/// Each thread has a pipeline of its own over a fork of the program (<see cref="ProgramAnalysis.Fork"/>): what was
/// found out about the program when it was loaded is shared, everything that is filled in while methods are
/// recovered is the thread's own. What a method is recovered as does not depend on which methods were recovered
/// before it, so it does not depend on which thread got it either: the results are those of one thread, sooner.
/// What is done with a result (writing it into an assembly, counting, reporting) happens on the calling thread,
/// one result at a time, in order.
/// </summary>
public static class RecoveryThreads
{
    /// <summary>How many threads to use when nothing else is said: REWIND_THREADS, else one per processor.</summary>
    public static int Default { get; } =
        int.TryParse(Environment.GetEnvironmentVariable("REWIND_THREADS"), out int asked) && asked > 0 ? asked : Environment.ProcessorCount;

    /// <summary>Methods a thread takes at a time: neighbours ask for the same bodies (their class's accessors and constructors).</summary>
    private const int Chunk = 8;

    /// <summary>How far the threads may be ahead of what was handed back: results wait in memory until it is their turn.</summary>
    private static readonly int Window =
        int.TryParse(Environment.GetEnvironmentVariable("REWIND_RECOVERY_WINDOW"), out int window) && window > 0 ? window : 4096;

    /// <summary>For REWIND_RECOVERY_STATS: how long the threads stood still because they were that far ahead, all of them together.</summary>
    public static double Waited => _waited / (double)System.Diagnostics.Stopwatch.Frequency;
    private static long _waited;

    /// <summary>Recovery goes deep (a method inside a method inside a constructor): the stack the single thread has.</summary>
    private const int StackSize = 1 << 30;

    /// <summary>
    /// Calls <paramref name="recover"/> for 0 .. <paramref name="count"/> - 1, on <paramref name="threads"/> threads
    /// (zero or less: <see cref="Default"/>), and <paramref name="consume"/> for each result on this thread, in
    /// order. With one thread everything happens here, with one pipeline over the program itself.
    /// <paramref name="recover"/> must not let an exception out.
    /// </summary>
    public static void Run<T>(ProgramAnalysis program, int count, int threads, Func<MethodPipeline, int, T> recover, Action<int, T> consume)
    {
        if (threads <= 0) threads = Default;
        threads = Math.Min(threads, Math.Max(1, (count + Chunk - 1) / Chunk));
        if (threads <= 1)
        {
            var pipeline = new MethodPipeline(program);
            for (int i = 0; i < count; i++) consume(i, recover(pipeline, i));
            return;
        }

        var results = new T[count];
        var ready = new bool[count];
        object gate = new();
        int next = 0, consumed = 0;
        Exception? fatal = null;

        void Work(ProgramAnalysis fork)
        {
            try
            {
                var pipeline = new MethodPipeline(fork);
                while (true)
                {
                    int start, end;
                    lock (gate)
                    {
                        if (fatal == null && next < count && next - consumed >= Window)
                        {
                            long began = System.Diagnostics.Stopwatch.GetTimestamp();
                            while (fatal == null && next < count && next - consumed >= Window) Monitor.Wait(gate);
                            Interlocked.Add(ref _waited, System.Diagnostics.Stopwatch.GetTimestamp() - began);
                        }
                        if (fatal != null || next >= count) return;
                        start = next;
                        end = next = Math.Min(count, next + Chunk);
                    }
                    for (int i = start; i < end; i++)
                    {
                        T result = recover(pipeline, i);
                        lock (gate)
                        {
                            results[i] = result;
                            ready[i] = true;
                            if (i == consumed) Monitor.PulseAll(gate);
                        }
                    }
                }
            }
            catch (Exception e)
            {
                lock (gate)
                {
                    fatal ??= e;
                    Monitor.PulseAll(gate);
                }
            }
        }

        // (The forks are made here, one after the other: making one reads tables of the program that are built on
        // first use.)
        var workers = new Thread[threads];
        for (int t = 0; t < threads; t++)
        {
            ProgramAnalysis fork = program.Fork();
            workers[t] = new Thread(() => Work(fork), StackSize) { IsBackground = true, Name = "recover " + t };
        }
        foreach (Thread worker in workers) worker.Start();
        try
        {
            for (int i = 0; i < count; i++)
            {
                T result;
                lock (gate)
                {
                    while (!ready[i] && fatal == null) Monitor.Wait(gate);
                    if (fatal != null) throw new InvalidOperationException("a recovery thread failed: " + fatal.Message, fatal);
                    result = results[i];
                    results[i] = default!;
                    bool full = next - consumed >= Window;
                    consumed = i + 1;
                    if (full) Monitor.PulseAll(gate);
                }
                consume(i, result);
            }
        }
        finally
        {
            lock (gate)
            {
                fatal ??= consumed < count ? new OperationCanceledException() : null;
                Monitor.PulseAll(gate);
            }
            foreach (Thread worker in workers) worker.Join();
        }
    }
}
