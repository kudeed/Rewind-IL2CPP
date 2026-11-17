using System.Collections.Concurrent;
using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// What recoveries ask each other for, kept for all of them and for every thread: the recovered statements of
/// other methods (to compare pasted code with, to read an accessor from, to put a constructor back), and what
/// was made of them. One for a program and all its forks (<see cref="ProgramAnalysis.Fork"/>).
///
/// Everything in here is what it would be whoever had asked for it first, and on whatever thread: that is
/// what lets several threads share it and still give the output of one. What is kept is never changed again;
/// whoever wants to change a method's statements gets its own (MethodPipeline.FreshCoreBody).
/// </summary>
internal sealed class RecoveryCache
{
    /// <summary>
    /// The statements a method was recovered as (null: not completely), how deep the recoveries went that it
    /// asked for in turn, and whether one of them was refused something because the depth was used up (see
    /// MethodPipeline.Ask).
    /// </summary>
    internal sealed class Body(HMethod? statements, int used, bool cut)
    {
        public readonly HMethod? Statements = statements;
        public readonly int Used = used;
        public readonly bool Cut = cut;
        /// <summary>With REWIND_CHECK_KEPT: the statements as they were when they were kept.</summary>
        public string? Text;
    }

    /// <summary>
    /// In place of the depth left, for a body that nothing was refused to: it is the same at every depth that
    /// is at least what it used. The others are kept for the depth they were recovered at.
    /// </summary>
    public const int Whole = -1;

    public readonly ConcurrentDictionary<(MethodDef Key, int Left), Body> Methods = new();
    public readonly ConcurrentDictionary<(MethodInst Key, int Left), Body> Instances = new();
    public readonly ConcurrentDictionary<((MethodDef Constructor, string Arguments) Key, int Left), Body> Constructors = new();

    /// <summary>
    /// What pasted code is compared with (InlineFolding): the methods of a class made ready for it - as they
    /// read, and with what they have pasted in themselves put back - of an instantiation of a generic class,
    /// and single constructors.
    /// </summary>
    public readonly ConcurrentDictionary<object, object?> Templates = new();

    /// <summary>The method of a field's class that does nothing but read it, or write it (AccessorIndex); null: none.</summary>
    public readonly ConcurrentDictionary<FieldDef, MethodDef?> Getters = new(), Setters = new();

    /// <summary>REWIND_CHECK_KEPT: remember what is kept as text, to find out afterwards whether anything changed it.</summary>
    public static readonly bool Check = Environment.GetEnvironmentVariable("REWIND_CHECK_KEPT") != null;

    /// <summary>The kept bodies that no longer read as they did when they were kept (for REWIND_CHECK_KEPT).</summary>
    public List<string> Changed()
    {
        var changed = new List<string>();
        void Look(string name, Body body)
        {
            if (body.Statements != null && body.Text != null && HirPrinter.Print(body.Statements) != body.Text) changed.Add(name);
        }
        foreach (var (at, body) in Methods) Look(at.Key.FullName, body);
        foreach (var (at, body) in Instances) Look(at.Key.ToString() ?? at.Key.Method.FullName, body);
        foreach (var (at, body) in Constructors) Look(at.Key.Constructor.FullName + " <" + at.Key.Arguments + ">", body);
        changed.Sort(StringComparer.Ordinal);
        return changed;
    }

    public int Count => Methods.Count + Instances.Count + Constructors.Count;
}
