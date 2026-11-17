using System.Globalization;
using Rewind.Binary;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// One runtime support function as it can be recognized in a binary without symbols: its fingerprint at
/// increasing depths (depth 0 is the function alone, depth n folds in what it calls to n levels), a similarity
/// sketch, and the exported API names that lead to it.
/// </summary>
public sealed record HelperSignature(HelperInfo Info, Fingerprint[] Depths)
{
    public int Instructions { get; init; }
    public uint[] Sketch { get; init; } = [];
    public bool IsThunk { get; init; }
    /// <summary>Exported functions that are this function or jump straight to it.</summary>
    public string[] Exports { get; init; } = [];
}

public enum MatchStage { Exact, Export, Similar, Thunk, Callees, Use }

public sealed class HelperMatchReport
{
    public int Entries, Found, Conflicts;
    /// <summary>How many entries were settled at each fingerprint depth.</summary>
    public int[] SettledAtDepth = new int[CodeIndex.DefaultDepth + 1];
    public List<HelperSignature> Missing = [];
    /// <summary>How each identified address was found.</summary>
    public Dictionary<ulong, MatchStage> Stage = [];

    public override string ToString()
    {
        int Count(MatchStage s) => Stage.Values.Count(v => v == s);
        return $"{Found}/{Entries} library functions found; {Stage.Count} addresses identified " +
               $"(exact {Count(MatchStage.Exact)} [depth 0..{CodeIndex.DefaultDepth}: {string.Join("/", SettledAtDepth)}], " +
               $"with changed callees {Count(MatchStage.Callees)}, by use {Count(MatchStage.Use)}, by export {Count(MatchStage.Export)}, by similarity {Count(MatchStage.Similar)}, as thunks {Count(MatchStage.Thunk)}); " +
               $"{Missing.Count} not found, {Conflicts} conflicting";
    }
}

/// <summary>
/// Fingerprints of the runtime support functions of one Unity version and platform, taken from builds of ours
/// that have symbols. Shipping games have no symbols; their support functions are found by looking these
/// fingerprints up among the game's own functions.
///
/// Identification proceeds from the most certain evidence to the least:
/// 1. identical code (position-independent fingerprint, deepened only as far as needed to be unique);
/// 2. the binary's own exported API names, for helpers that are (or jump to) an exported function;
/// 3. near-identical code (similarity sketch) for functions the game's build options changed slightly;
/// 4. any function that merely jumps to an identified helper is that helper.
/// </summary>
public sealed class HelperLibrary
{
    public string Unity = "", Platform = "", Arch = "";
    public List<HelperSignature> Entries = [];

    /// <summary>Functions this short are only trusted when what they call matches too.</summary>
    private const int MinimumAloneLength = 32;

    /// <summary>Similarity matching needs enough instructions to be meaningful, a high score and a clear winner.</summary>
    private const int MinimumSimilarInstructions = 12;
    private const double MinimumSimilarity = 0.70, MinimumMargin = 0.12;
    /// <summary>
    /// A large function whose best match leaves every other candidate far behind is that function even when a share
    /// of its instructions differs, for example struct field offsets that moved between builds (Class::IsAssignableFrom
    /// of a build scored 0.688 against its signature, and 0.17 against the next function).
    /// </summary>
    private const int LooseMinimumInstructions = 200;
    private const double LooseSimilarity = 0.60, LooseMargin = 0.30;

    public static HelperLibrary Build(RuntimeHelpers named, CodeIndex index, NativeImage image, Func<ulong, bool> isManaged,
        string unity, string platform, string arch)
    {
        var library = new HelperLibrary { Unity = unity, Platform = platform, Arch = arch };

        var exportsByTarget = new Dictionary<ulong, List<string>>();
        foreach (var (name, address) in image.Exports)
        {
            ulong target = index.ThunkTarget(address);
            if (!exportsByTarget.TryGetValue(target, out List<string>? list)) exportsByTarget[target] = list = [];
            list.Add(name);
        }

        // A helper that only jumps elsewhere stands for its destination: record the destination too.
        var functions = new Dictionary<ulong, HelperInfo>();
        foreach (var (address, info) in named.ByAddress)
        {
            functions.TryAdd(address, info);
            ulong target = index.ThunkTarget(address);
            if (target != address && !isManaged(target)) functions.TryAdd(target, info);
        }

        var seen = new HashSet<(HelperKind, Fingerprint)>();
        foreach (var (address, info) in functions.OrderBy(kv => kv.Key))
        {
            FunctionCode? code = index.Get(address);
            if (code == null) continue;
            var depths = new Fingerprint[CodeIndex.DefaultDepth + 1];
            for (int d = 0; d < depths.Length; d++) depths[d] = index.Deep(address, d) ?? default;
            if (!seen.Add((info.Kind, depths[^1]))) continue;
            exportsByTarget.TryGetValue(index.ThunkTarget(address), out List<string>? exports);
            library.Entries.Add(new HelperSignature(info, depths)
            {
                Instructions = code.Instructions,
                Sketch = code.Sketch,
                IsThunk = code.IsThunk,
                Exports = exports?.Order(StringComparer.Ordinal).ToArray() ?? [],
            });
        }
        return library;
    }

    /// <summary>Adds the entries of another library (another build configuration of the same Unity version).</summary>
    public void Merge(HelperLibrary other)
    {
        var seen = new HashSet<(HelperKind, Fingerprint)>(Entries.Select(e => (e.Info.Kind, e.Depths[^1])));
        foreach (HelperSignature e in other.Entries)
            if (seen.Add((e.Info.Kind, e.Depths[^1])))
                Entries.Add(e);
    }

    private static readonly bool NoChangedCallees = Environment.GetEnvironmentVariable("REWIND_NO_CHANGED_CALLEES") != null;
    /// <summary>How many functions with the same code are looked through, how many calls a function may make, and how many entries are tried for one changed callee.</summary>
    private const int MostLookAlikes = 256, MostCallees = 4, MostStandIns = 6;

    /// <summary>
    /// Whether the function's first-level fingerprint becomes the entry's when, for one or more of the functions
    /// it calls, a library entry stands in that is near-identical to that function (see Match, stage 1b).
    /// </summary>
    private bool CallsChangedCopies(CodeIndex target, ulong address, HelperSignature entry)
    {
        FunctionCode? code = target.Get(address);
        if (code == null || code.Callees.Count is 0 or > MostCallees) return false;
        var choices = new List<Fingerprint>[code.Callees.Count];
        for (int i = 0; i < choices.Length; i++)
        {
            // (As it is first; then what it may be a changed copy of, the closest first.)
            choices[i] = [target.Deep(code.Callees[i], 0) ?? default];
            if (target.Get(code.Callees[i]) is not { Instructions: >= MinimumSimilarInstructions } callee) continue;
            int low = callee.Instructions * 3 / 4, high = callee.Instructions * 4 / 3 + 1;
            choices[i].AddRange(Entries
                .Where(e => !e.IsThunk && e.Instructions >= low && e.Instructions <= high)
                .Select(e => (Entry: e, Score: CodeIndex.Similarity(e.Sketch, callee.Sketch)))
                .Where(x => x.Score >= MinimumSimilarity)
                .OrderByDescending(x => x.Score)
                .Select(x => x.Entry.Depths[0])
                .Where(f => f != choices[i][0])
                .Distinct()
                .Take(MostStandIns));
        }
        var chosen = new Fingerprint[choices.Length];
        bool Try(int at, bool changed)
        {
            if (at == chosen.Length) return changed && target.WithCallees(address, chosen) == entry.Depths[1];
            for (int k = 0; k < choices[at].Count; k++)
            {
                chosen[at] = choices[at][k];
                if (Try(at + 1, changed || k > 0)) return true;
            }
            return false;
        }
        return Try(0, false);
    }

    private static readonly bool NoUse = Environment.GetEnvironmentVariable("REWIND_NO_HELPER_USE") != null;
    /// <summary>From how many methods a function must be called to be told by that, and how many times as many as all its look-alikes together.</summary>
    private const int MinimumUse = 1000, UseMargin = 20;
    /// <summary>Fewer instructions than this are what any small function may consist of: being called a lot then says nothing.</summary>
    private const int MinimumUseInstructions = 6;

    /// <summary>From how many of the given functions each function is called (through functions that only jump on, too).</summary>
    private static Dictionary<ulong, int> Callers(CodeIndex target, IEnumerable<ulong> from)
    {
        var callers = new Dictionary<ulong, int>();
        foreach (ulong start in from)
        {
            if (target.Get(start) is not { } code) continue;
            foreach (ulong callee in code.Callees.Select(target.ThunkTarget).Distinct())
                callers[callee] = callers.GetValueOrDefault(callee) + 1;
        }
        return callers;
    }

    /// <param name="managed">The functions that are compiled methods (the code that calls the support functions), when known.</param>
    public RuntimeHelpers Match(CodeIndex target, NativeImage image, IEnumerable<ulong> candidates, out HelperMatchReport report, IEnumerable<ulong>? managed = null)
    {
        ulong[] all = candidates.ToArray();
        int levels = CodeIndex.DefaultDepth + 1;
        var byDepth = new Dictionary<Fingerprint, List<ulong>>[levels];
        Dictionary<Fingerprint, List<ulong>> Level(int depth)
        {
            if (byDepth[depth] is { } ready) return ready;
            var map = new Dictionary<Fingerprint, List<ulong>>();
            foreach (ulong address in all)
            {
                if (target.Deep(address, depth) is not { } fp) continue;
                if (!map.TryGetValue(fp, out List<ulong>? list)) map[fp] = list = [];
                list.Add(address);
            }
            return byDepth[depth] = map;
        }

        var result = new HelperMatchReport { Entries = Entries.Count };
        var claims = new Dictionary<ulong, HelperInfo>();
        var conflicted = new HashSet<ulong>();
        var settledEntries = new HashSet<HelperSignature>();

        void Claim(ulong address, HelperSignature entry, MatchStage stage)
        {
            if (claims.TryGetValue(address, out HelperInfo? other))
            {
                // Two different helpers cannot be the same function: trust neither.
                if (other.Kind != entry.Info.Kind && stage == MatchStage.Exact && result.Stage[address] == MatchStage.Exact) conflicted.Add(address);
                return;
            }
            claims[address] = entry.Info;
            result.Stage[address] = stage;
        }

        // 1. Identical code. Accepted at the shallowest depth at which exactly one candidate has the entry's
        //    fingerprint; deeper levels only tell look-alikes apart. (Requiring the deepest level outright
        //    would reject a function because of an unrelated difference several calls down.)
        foreach (HelperSignature entry in Entries)
        {
            for (int d = 0; d < levels && d < entry.Depths.Length; d++)
            {
                if (!Level(d).TryGetValue(entry.Depths[d], out List<ulong>? hits)) break;
                bool trusted = d > 0 || entry.Depths[0].Length >= MinimumAloneLength;
                // Copies that stay identical all the way down are the same function several times.
                if ((hits.Count == 1 && trusted) || d == levels - 1)
                {
                    foreach (ulong address in hits) Claim(address, entry, MatchStage.Exact);
                    result.SettledAtDepth[d]++;
                    settledEntries.Add(entry);
                    break;
                }
            }
        }

        // 1b. Identical code that calls a function which is not identical any more. The build's own options
        //     change some functions slightly (a field offset that moved); every function that calls one of those
        //     then has another fingerprint from the first level down, and a short one is not trusted by its own
        //     code alone (the image has many functions with the same few instructions, each calling something
        //     else). Among those look-alikes it is the one that calls near-identical copies of what the entry
        //     calls. What the entry calls is not recorded, but it is told by the fingerprints: the entry's
        //     first-level fingerprint comes out again when the right entries stand in for the changed callees.
        if (!NoChangedCallees)
            foreach (HelperSignature entry in Entries)
            {
                if (settledEntries.Contains(entry) || entry.IsThunk || entry.Depths.Length < 2) continue;
                if (!Level(0).TryGetValue(entry.Depths[0], out List<ulong>? alike) || alike.Count > MostLookAlikes) continue;
                ulong found = 0;
                int fitting = 0;
                foreach (ulong address in alike)
                    if (!claims.ContainsKey(address) && CallsChangedCopies(target, address, entry))
                    {
                        found = address;
                        fitting++;
                    }
                if (fitting != 1) continue;
                Claim(found, entry, MatchStage.Callees);
                settledEntries.Add(entry);
            }

        // 2. The binary's own export table.
        foreach (HelperSignature entry in Entries)
        {
            if (settledEntries.Contains(entry) || entry.IsThunk) continue;
            foreach (string export in entry.Exports)
            {
                if (!image.Exports.TryGetValue(export, out ulong exported)) continue;
                ulong address = target.ThunkTarget(exported);
                if (claims.ContainsKey(address)) continue;
                Claim(address, entry, MatchStage.Export);
                settledEntries.Add(entry);
                break;
            }
        }

        // 3. Near-identical code.
        var pool = new List<(ulong Address, FunctionCode Code)>();
        foreach (ulong address in all)
            if (!claims.ContainsKey(address) && target.Get(address) is { Instructions: >= MinimumSimilarInstructions } code)
                pool.Add((address, code));
        foreach (HelperSignature entry in Entries)
        {
            if (settledEntries.Contains(entry) || entry.IsThunk || entry.Instructions < MinimumSimilarInstructions) continue;
            double best = 0, second = 0;
            ulong bestAddress = 0;
            int low = entry.Instructions * 3 / 4, high = entry.Instructions * 4 / 3 + 1;
            foreach (var (address, code) in pool)
            {
                if (code.Instructions < low || code.Instructions > high || claims.ContainsKey(address)) continue;
                double similarity = CodeIndex.Similarity(entry.Sketch, code.Sketch);
                if (similarity > best)
                {
                    second = best;
                    best = similarity;
                    bestAddress = address;
                }
                else if (similarity > second) second = similarity;
            }
            bool clear = best >= MinimumSimilarity && best - second >= MinimumMargin;
            bool dominant = entry.Instructions >= LooseMinimumInstructions && best >= LooseSimilarity && best - second >= LooseMargin;
            if (clear || dominant)
            {
                Claim(bestAddress, entry, MatchStage.Similar);
                settledEntries.Add(entry);
            }
        }

        // 3b. Identical code again (as in 1b), where what the entry calls is no function of the library and
        //     nothing can stand in for it.
        //     The entry is a function the compiled methods call. Where they call one of the functions with its
        //     code from a thousand places and all the others together from next to none, that one is the
        //     support function among them. (Not where the library has that code for two kinds of helper: then
        //     the code does not say which. And only for a kind the decompiler acts on that was found in no other
        //     way: it is the last evidence there is, taken where nothing else is.)
        if (!NoUse && managed != null)
        {
            Dictionary<ulong, int>? callers = null;
            var settledKinds = new HashSet<HelperKind>(claims.Values.Select(i => i.Kind));
            var kindsWithCode = Entries.Where(e => !e.IsThunk).GroupBy(e => e.Depths[0]).ToDictionary(g => g.Key, g => g.Select(e => e.Info.Kind).Distinct().Count());
            foreach (HelperSignature entry in Entries)
            {
                if (settledEntries.Contains(entry) || entry.IsThunk || entry.Info.Kind == HelperKind.None || entry.Depths.Length < 2) continue;
                if (entry.Instructions < MinimumUseInstructions || settledKinds.Contains(entry.Info.Kind) || kindsWithCode[entry.Depths[0]] != 1) continue;
                if (!Level(0).TryGetValue(entry.Depths[0], out List<ulong>? alike) || alike.Count > MostLookAlikes || Level(1).ContainsKey(entry.Depths[1])) continue;
                callers ??= Callers(target, managed);
                ulong most = 0;
                int mostCalls = 0, otherCalls = 0;
                foreach (ulong address in alike)
                {
                    int calls = callers.GetValueOrDefault(address);
                    if (calls > mostCalls)
                    {
                        otherCalls += mostCalls;
                        (most, mostCalls) = (address, calls);
                    }
                    else otherCalls += calls;
                }
                if (mostCalls < MinimumUse || mostCalls < UseMargin * Math.Max(1, otherCalls) || claims.ContainsKey(most)) continue;
                Claim(most, entry, MatchStage.Use);
                settledEntries.Add(entry);
                settledKinds.Add(entry.Info.Kind);
            }
        }

        // 4. A function that only jumps to an identified helper is that helper.
        foreach (ulong address in all)
        {
            if (claims.ContainsKey(address) || target.Get(address) is not { IsThunk: true }) continue;
            ulong destination = target.ThunkTarget(address);
            if (destination != address && claims.TryGetValue(destination, out HelperInfo? info) && !conflicted.Contains(destination))
            {
                claims[address] = info;
                result.Stage[address] = MatchStage.Thunk;
            }
        }

        var helpers = new RuntimeHelpers();
        foreach (var (address, info) in claims)
        {
            if (conflicted.Contains(address))
            {
                result.Stage.Remove(address);
                continue;
            }
            helpers.Add(address, info);
        }
        // A thunk entry counts as found when some thunk in the target was identified as its helper.
        var foundKinds = new HashSet<HelperKind>(helpers.ByAddress.Values.Select(i => i.Kind));
        foreach (HelperSignature entry in Entries)
        {
            bool found = settledEntries.Contains(entry) || (entry.IsThunk && foundKinds.Contains(entry.Info.Kind));
            if (found) result.Found++;
            else result.Missing.Add(entry);
        }
        result.Conflicts = conflicted.Count;
        report = result;
        return helpers;
    }

    // ---- file format: one tab-separated line per function ---------------------------------------------------

    public void Save(string path)
    {
        using var writer = new StreamWriter(path);
        writer.WriteLine($"# rewind helper signatures\t{Unity}\t{Platform}\t{Arch}");
        foreach (HelperSignature e in Entries)
        {
            HelperInfo i = e.Info;
            writer.WriteLine(string.Join('\t', i.Kind, i.IntArgs.ToString(CultureInfo.InvariantCulture), i.NoReturn ? "1" : "0",
                i.ReturnsValue ? "1" : "0", i.FloatArgs.ToString(CultureInfo.InvariantCulture), i.IsDouble ? "1" : "0",
                i.MathName.Length == 0 ? "-" : i.MathName, string.Join(',', e.Depths),
                e.Instructions.ToString(CultureInfo.InvariantCulture), e.IsThunk ? "1" : "0",
                e.Exports.Length == 0 ? "-" : string.Join(',', e.Exports),
                e.Sketch.Length == 0 ? "-" : string.Join(',', e.Sketch.Select(v => v.ToString("X", CultureInfo.InvariantCulture))),
                i.Name));
        }
    }

    public static HelperLibrary Load(string path)
    {
        var library = new HelperLibrary();
        foreach (string line in File.ReadLines(path))
        {
            string[] p = line.Split('\t');
            if (line.StartsWith('#'))
            {
                if (p.Length >= 4) (library.Unity, library.Platform, library.Arch) = (p[1], p[2], p[3]);
                continue;
            }
            if (p.Length < 13 || !Enum.TryParse(p[0], out HelperKind kind)) continue;
            var info = new HelperInfo(kind, int.Parse(p[1], CultureInfo.InvariantCulture), p[2] == "1", p[3] == "1", p[12])
            {
                FloatArgs = int.Parse(p[4], CultureInfo.InvariantCulture),
                IsDouble = p[5] == "1",
                MathName = p[6] == "-" ? "" : p[6],
            };
            library.Entries.Add(new HelperSignature(info, p[7].Split(',').Select(Fingerprint.Parse).ToArray())
            {
                Instructions = int.Parse(p[8], CultureInfo.InvariantCulture),
                IsThunk = p[9] == "1",
                Exports = p[10] == "-" ? [] : p[10].Split(','),
                Sketch = p[11] == "-" ? [] : p[11].Split(',').Select(v => uint.Parse(v, NumberStyles.HexNumber, CultureInfo.InvariantCulture)).ToArray(),
            });
        }
        return library;
    }
}
