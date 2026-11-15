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

public enum MatchStage { Exact, Export, Similar, Thunk }

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
               $"by export {Count(MatchStage.Export)}, by similarity {Count(MatchStage.Similar)}, as thunks {Count(MatchStage.Thunk)}); " +
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

    public RuntimeHelpers Match(CodeIndex target, NativeImage image, IEnumerable<ulong> candidates, out HelperMatchReport report)
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
            if (best >= MinimumSimilarity && best - second >= MinimumMargin)
            {
                Claim(bestAddress, entry, MatchStage.Similar);
                settledEntries.Add(entry);
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
