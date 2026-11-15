using System.Globalization;

namespace Rewind.Analysis.Runtime;

/// <summary>One function the identification model recognized (see the model project's rewind_nn.identify).</summary>
public sealed class ModelIdentification
{
    public ulong Address;
    /// <summary>True: a private copy of the game's own listed methods. False: a known runtime function.</summary>
    public bool IsCopy;
    public float Score, Margin;
    /// <summary>Copies: addresses of the listed methods whose code it is. Runtime: names of the runtime function.</summary>
    public List<ulong> Originals = [];
    public List<string> Names = [];
    /// <summary>
    /// True when the model only proposed this and the decompiler confirmed it: the code recovered from the
    /// function, read as the proposed method, is the same as the code recovered from the method itself.
    /// </summary>
    public bool Verified;
}

/// <summary>
/// Answers of the identification model for one game, as written by <c>python -m rewind_nn.identify run</c>.
/// Only answers that passed the model's calibrated gate are in the file; each one names a group of candidates
/// with identical code, among which the decompiler chooses from the call site.
/// </summary>
public sealed class ModelIdentifications
{
    public Dictionary<ulong, ModelIdentification> ByAddress { get; } = [];
    /// <summary>
    /// Functions the model would not vouch for, with its best candidates (each a group of listed methods with
    /// identical code), best first. A candidate counts only once the decompiler has checked it.
    /// </summary>
    public Dictionary<ulong, List<(float Score, ulong[] Group)>> Proposals { get; } = [];
    public string Source { get; private set; } = "";

    public static ModelIdentifications Load(string path)
    {
        var result = new ModelIdentifications { Source = File.ReadLines(path).FirstOrDefault(l => l.StartsWith("# model", StringComparison.Ordinal)) ?? path };
        foreach (string line in File.ReadLines(path))
        {
            if (line.Length == 0 || line[0] == '#') continue;
            string[] parts = line.Split('\t');
            if (parts.Length < 5) continue;
            if (parts[1] == "propose")
            {
                var candidates = new List<(float, ulong[])>();
                foreach (string item in parts[4].Split(";;", StringSplitOptions.RemoveEmptyEntries))
                {
                    int colon = item.IndexOf(':');
                    if (colon <= 0) continue;
                    candidates.Add((float.Parse(item[..colon], CultureInfo.InvariantCulture),
                        item[(colon + 1)..].Split(',', StringSplitOptions.RemoveEmptyEntries)
                            .Select(a => ulong.Parse(a, NumberStyles.HexNumber, CultureInfo.InvariantCulture)).ToArray()));
                }
                if (candidates.Count != 0) result.Proposals[ulong.Parse(parts[0], NumberStyles.HexNumber, CultureInfo.InvariantCulture)] = candidates;
                continue;
            }
            var id = new ModelIdentification
            {
                Address = ulong.Parse(parts[0], NumberStyles.HexNumber, CultureInfo.InvariantCulture),
                IsCopy = parts[1] == "copy",
                Score = float.Parse(parts[2], CultureInfo.InvariantCulture),
                Margin = float.Parse(parts[3], CultureInfo.InvariantCulture),
            };
            foreach (string target in parts[4].Split(";;", StringSplitOptions.RemoveEmptyEntries))
            {
                if (id.IsCopy) id.Originals.Add(ulong.Parse(target, NumberStyles.HexNumber, CultureInfo.InvariantCulture));
                else id.Names.Add(target);
            }
            result.ByAddress[id.Address] = id;
        }
        return result;
    }

    /// <summary>The path given by the REWIND_IDENTIFICATIONS environment variable, when set (lab and test runs).</summary>
    public static ModelIdentifications? FromEnvironment() =>
        Environment.GetEnvironmentVariable("REWIND_IDENTIFICATIONS") is { Length: > 0 } path && File.Exists(path) ? Load(path) : null;
}
