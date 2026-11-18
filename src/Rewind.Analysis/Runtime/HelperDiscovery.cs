using Rewind.Binary;
using Rewind.Metadata;
using Rewind.Model;

namespace Rewind.Analysis.Runtime;

/// <summary>What is known about a game's runtime support functions, and how it was found out.</summary>
public sealed record DiscoveredHelpers(RuntimeHelpers Helpers, ModelCodeContext Context, string Source, int Kinds, bool ExactVersion);

/// <summary>
/// Finds the runtime support functions of a game that ships without symbols by trying the signature
/// libraries on hand: the one made for the game's Unity version first, any other of the same platform after.
/// </summary>
public static class HelperDiscovery
{
    public static IEnumerable<string> DefaultSignatureFiles()
    {
        var seen = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        foreach (string root in new[] { AppContext.BaseDirectory, Directory.GetCurrentDirectory() })
        {
            string directory = Path.Combine(root, "signatures");
            if (!Directory.Exists(directory)) continue;
            foreach (string file in Directory.EnumerateFiles(directory, "*.sig"))
                if (seen.Add(Path.GetFileName(file)))
                    yield return file;
        }
    }

    /// <summary>
    /// How far apart two Unity versions are: by release line first (2023.2 and 6000.0 are neighbours, Unity 6 being
    /// what would have been 2023.3), then by patch number.
    /// </summary>
    internal static long Distance(UnityVersion a, UnityVersion b)
    {
        static long Line(UnityVersion v) => (v.Major >= 6000 ? 2024 + (v.Major - 6000) : v.Major) * 10L + Math.Min(v.Minor, 9);
        return Math.Abs(Line(a) - Line(b)) * 1000 + Math.Abs(a.Build - b.Build);
    }

    public static DiscoveredHelpers Discover(Il2CppModel model, IEnumerable<string> signatureFiles, Action<string> log)
    {
        var context = new ModelCodeContext(model);
        NativeImage image = model.Image;
        if (image.Arch is not (CpuArch.X64 or CpuArch.Arm64))
            return new DiscoveredHelpers(new RuntimeHelpers(), context, "none (machine code analysis supports x64 and ARM64 only so far)", 0, false);

        context.DiscoverCallTargets();
        var index = new CodeIndex(context);
        ulong[] candidates = context.FunctionStarts.Where(a => !context.IsManaged(a)).ToArray();
        string unity = model.UnityVersion?.ToString() ?? "";

        var libraries = new List<(string File, HelperLibrary Library, bool Exact)>();
        foreach (string file in signatureFiles)
        {
            HelperLibrary library;
            try
            {
                library = HelperLibrary.Load(file);
            }
            catch (Exception e) when (e is IOException or FormatException)
            {
                log($"warning: signature file {Path.GetFileName(file)} could not be read: {e.Message}");
                continue;
            }
            if (!string.Equals(library.Arch, image.Arch.ToString(), StringComparison.OrdinalIgnoreCase)) continue;
            if (!string.Equals(library.Platform, image.Os.ToString(), StringComparison.OrdinalIgnoreCase)) continue;
            libraries.Add((file, library, unity.Length != 0 && library.Unity == unity));
        }

        // The library of the game's own version first, then the others from the nearest version to the farthest:
        // of two libraries that recognize equally much, the one made from the closer runtime is taken.
        long DistanceTo(HelperLibrary library) =>
            model.UnityVersion is { } game && UnityVersion.TryParse(library.Unity, out UnityVersion made) ? Distance(game, made) : long.MaxValue;
        DiscoveredHelpers? best = null;
        foreach (var (file, library, exact) in libraries.OrderByDescending(l => l.Exact).ThenBy(l => DistanceTo(l.Library)))
        {
            RuntimeHelpers helpers = library.Match(index, image, candidates, out HelperMatchReport report, context.FunctionStarts.Where(context.IsManaged));
            int kinds = helpers.ByAddress.Values.Select(i => i.Kind).Distinct().Count();
            log($"signatures {Path.GetFileName(file)} (Unity {library.Unity}): {kinds} kinds of support function identified at {helpers.ByAddress.Count} addresses");
            if (best == null || kinds > best.Kinds)
                best = new DiscoveredHelpers(helpers, context, Path.GetFileName(file), kinds, exact);
            // The library made for this very version settles it when it recognizes the runtime at all.
            if (exact && kinds >= 20) break;
        }
        if (best == null) return new DiscoveredHelpers(new RuntimeHelpers(), context, "none (no signature library for this platform)", 0, false);
        // Imported C library functions (memcpy, sinf, ...) are called through stubs that name them.
        if (image is ElfImage elf)
        {
            foreach (var (stub, name) in elf.ImportStubs)
                if (best.Helpers.At(stub) == null && RuntimeHelpers.Classify(name) is { } imported)
                    best.Helpers.Add(stub, imported);
            best = best with { Kinds = best.Helpers.ByAddress.Values.Select(i => i.Kind).Distinct().Count() };
        }
        // What no library recognized, the compiled methods may show by the way they call it.
        if (HelperRoles.Identify(model, context, index, best.Helpers) is { } found)
        {
            log(found);
            best = best with { Kinds = best.Helpers.ByAddress.Values.Select(i => i.Kind).Distinct().Count() };
        }
        return best;
    }
}
