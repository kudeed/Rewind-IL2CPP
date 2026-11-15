using System.IO.Compression;
using System.Text;
using Rewind.Metadata;

namespace Rewind.Input;

public sealed class InputException(string message) : Exception(message);

/// <summary>The two files that make up an IL2CPP build, loaded into memory, plus what we learned on the way.</summary>
public sealed class GameInput
{
    public required byte[] Binary { get; init; }
    public required string BinaryName { get; init; }
    public required byte[] Metadata { get; init; }
    public required string MetadataName { get; init; }
    public UnityVersion? UnityVersion { get; init; }
    public string Kind { get; init; } = "";
    public List<string> Notes { get; } = [];
}

/// <summary>
/// Locates the native binary and global-metadata.dat for whatever the user points at: a game folder, the game
/// executable, an Android package (APK, split-APK bundles, AAB), an iOS IPA, or the files themselves.
/// </summary>
public static class InputResolver
{
    private static readonly string[] BinaryFileNames =
        ["GameAssembly.dll", "libil2cpp.so", "GameAssembly.so", "GameAssembly.dylib", "UnityFramework"];

    private static readonly string[] AbiPreference = ["arm64-v8a", "armeabi-v7a", "x86_64", "x86"];

    private static readonly string[] VersionCarriers =
    [
        "globalgamemanagers", "data.unity3d", "mainData", "level0", "unity default resources",
        "unity_builtin_extra", "globalgamemanagers.assets",
    ];

    public static GameInput Resolve(string path, string? metadataOverride = null, string? binaryOverride = null,
        string? abi = null)
    {
        path = Path.GetFullPath(path);
        GameInput input;
        if (Directory.Exists(path))
        {
            input = FromDirectory(path, abi);
        }
        else if (File.Exists(path))
        {
            if (IsZip(path)) input = FromArchive(path, abi);
            else
            {
                string name = Path.GetFileName(path);
                bool isMetadata = HasMetadataMagic(path) || name.Equals("global-metadata.dat", StringComparison.OrdinalIgnoreCase);
                bool isLauncher = name.EndsWith(".exe", StringComparison.OrdinalIgnoreCase) ||
                                  name.EndsWith(".x86_64", StringComparison.OrdinalIgnoreCase);
                if (isLauncher && binaryOverride == null && metadataOverride == null)
                    input = FromDirectory(Path.GetDirectoryName(path)!, abi);
                else if (isMetadata)
                    input = FromLooseFiles(binaryOverride ?? FindBinaryNear(path, abi), path);
                else
                    input = FromLooseFiles(path, metadataOverride ?? FindMetadataNear(path));
                return input;
            }
        }
        else
        {
            throw new InputException($"'{path}' does not exist.");
        }

        if (metadataOverride == null && binaryOverride == null) return input;
        return new GameInput
        {
            Binary = binaryOverride != null ? File.ReadAllBytes(binaryOverride) : input.Binary,
            BinaryName = binaryOverride ?? input.BinaryName,
            Metadata = metadataOverride != null ? File.ReadAllBytes(metadataOverride) : input.Metadata,
            MetadataName = metadataOverride ?? input.MetadataName,
            UnityVersion = input.UnityVersion,
            Kind = input.Kind,
        };
    }

    private static bool IsZip(string file)
    {
        using FileStream fs = File.OpenRead(file);
        Span<byte> head = stackalloc byte[4];
        return fs.Read(head) == 4 && head[0] == 'P' && head[1] == 'K' && head[2] is 3 or 5 && head[3] is 4 or 6;
    }

    private static bool HasMetadataMagic(string file)
    {
        using FileStream fs = File.OpenRead(file);
        Span<byte> head = stackalloc byte[8];
        return fs.Read(head) == 8 && MetadataFile.HasMagic(head);
    }

    // ---- loose files and folders -------------------------------------------------------------------------------

    private static GameInput FromLooseFiles(string binary, string metadata)
    {
        string dir = Path.GetDirectoryName(binary) ?? ".";
        return new GameInput
        {
            Binary = File.ReadAllBytes(binary),
            BinaryName = binary,
            Metadata = File.ReadAllBytes(metadata),
            MetadataName = metadata,
            UnityVersion = FindUnityVersionInDirectory(dir) ?? FindUnityVersionInDirectory(Path.GetDirectoryName(metadata) ?? "."),
            Kind = "files",
        };
    }

    private static IEnumerable<string> EnumerateFilesSafe(string root, int maxDepth)
    {
        var pending = new Stack<(string Dir, int Depth)>();
        pending.Push((root, 0));
        while (pending.Count > 0)
        {
            var (dir, depth) = pending.Pop();
            string[] files, dirs;
            try
            {
                files = Directory.GetFiles(dir);
                dirs = depth < maxDepth ? Directory.GetDirectories(dir) : [];
            }
            catch (Exception e) when (e is UnauthorizedAccessException or IOException)
            {
                continue;
            }
            foreach (string f in files) yield return f;
            foreach (string d in dirs) pending.Push((d, depth + 1));
        }
    }

    private static int AbiRank(string path, string? preferred)
    {
        string normalized = path.Replace('\\', '/');
        if (preferred != null && normalized.Contains("/" + preferred + "/", StringComparison.OrdinalIgnoreCase)) return -1;
        for (int i = 0; i < AbiPreference.Length; i++)
            if (normalized.Contains("/" + AbiPreference[i] + "/", StringComparison.OrdinalIgnoreCase))
                return i;
        return AbiPreference.Length;
    }

    private static GameInput FromDirectory(string dir, string? abi)
    {
        var binaries = new List<string>();
        var metadatas = new List<string>();
        foreach (string file in EnumerateFilesSafe(dir, maxDepth: 9))
        {
            string name = Path.GetFileName(file);
            if (name.Equals("global-metadata.dat", StringComparison.OrdinalIgnoreCase)) metadatas.Add(file);
            else if (BinaryFileNames.Contains(name, StringComparer.OrdinalIgnoreCase)) binaries.Add(file);
        }
        if (binaries.Count == 0)
            throw new InputException(
                $"No IL2CPP binary (GameAssembly.dll, libil2cpp.so, GameAssembly.so/.dylib or UnityFramework) was found under '{dir}'. " +
                "If this is a Mono build (it has a Managed folder full of .dll files), its code is already IL and an ordinary .NET decompiler handles it.");
        if (metadatas.Count == 0)
            throw new InputException($"Found the IL2CPP binary but no global-metadata.dat under '{dir}'.");

        string binary = binaries.OrderBy(b => AbiRank(b, abi)).ThenBy(b => b.Length).First();
        string metadata = metadatas.OrderBy(m => m.Length).First();
        var input = new GameInput
        {
            Binary = File.ReadAllBytes(binary),
            BinaryName = binary,
            Metadata = File.ReadAllBytes(metadata),
            MetadataName = metadata,
            UnityVersion = FindUnityVersionInDirectory(dir),
            Kind = "folder",
        };
        if (binaries.Count > 1) input.Notes.Add($"{binaries.Count} binaries found; using {binary}");
        return input;
    }

    private static string FindMetadataNear(string binary)
    {
        string? dir = Path.GetDirectoryName(binary);
        for (int up = 0; up < 5 && dir != null; up++, dir = Path.GetDirectoryName(dir))
        {
            foreach (string file in EnumerateFilesSafe(dir, maxDepth: 6))
                if (Path.GetFileName(file).Equals("global-metadata.dat", StringComparison.OrdinalIgnoreCase))
                    return file;
        }
        throw new InputException($"Could not find global-metadata.dat near '{binary}'. Pass it with --metadata.");
    }

    private static string FindBinaryNear(string metadata, string? abi)
    {
        string? dir = Path.GetDirectoryName(metadata);
        for (int up = 0; up < 7 && dir != null; up++, dir = Path.GetDirectoryName(dir))
        {
            var found = new List<string>();
            foreach (string file in EnumerateFilesSafe(dir, maxDepth: 4))
                if (BinaryFileNames.Contains(Path.GetFileName(file), StringComparer.OrdinalIgnoreCase))
                    found.Add(file);
            if (found.Count > 0) return found.OrderBy(b => AbiRank(b, abi)).First();
        }
        throw new InputException($"Could not find the IL2CPP binary near '{metadata}'. Pass it with --binary.");
    }

    private static int CarrierRank(string fileName)
    {
        for (int i = 0; i < VersionCarriers.Length; i++)
            if (VersionCarriers[i].Equals(fileName, StringComparison.OrdinalIgnoreCase))
                return i;
        return -1;
    }

    private static UnityVersion? FindUnityVersionInDirectory(string dir)
    {
        // Built-in resource files can carry an older engine stamp than the player itself, so the game's own
        // manager files (earlier in VersionCarriers) win over them.
        UnityVersion? best = null;
        int bestRank = int.MaxValue;
        foreach (string file in EnumerateFilesSafe(dir, maxDepth: 6))
        {
            int rank = CarrierRank(Path.GetFileName(file));
            if (rank < 0 || rank >= bestRank) continue;
            try
            {
                using FileStream fs = File.OpenRead(file);
                var buffer = new byte[4096];
                int n = fs.Read(buffer);
                if (ScanForUnityVersion(buffer.AsSpan(0, n)) is { } v)
                {
                    best = v;
                    bestRank = rank;
                }
            }
            catch (IOException)
            {
            }
        }
        return best;
    }

    /// <summary>Unity asset files and bundles carry the engine version as plain text near the start.</summary>
    public static UnityVersion? ScanForUnityVersion(ReadOnlySpan<byte> head)
    {
        string text = Encoding.Latin1.GetString(head);
        for (int i = 0; i < text.Length - 5; i++)
        {
            if (!char.IsAsciiDigit(text[i]) || (i > 0 && (char.IsAsciiDigit(text[i - 1]) || text[i - 1] == '.'))) continue;
            int end = i;
            while (end < text.Length && end - i < 24 && (char.IsAsciiLetterOrDigit(text[end]) || text[end] == '.')) end++;
            string candidate = text[i..end];
            // Require the release-type letter so file format numbers like "5.x.x" are not mistaken for a version.
            if (candidate.IndexOfAny(['f', 'b', 'a', 'p']) < 0) continue;
            if (UnityVersion.TryParse(candidate, out UnityVersion v)) return v;
        }
        return null;
    }

    // ---- archives ----------------------------------------------------------------------------------------------

    private sealed class ArchiveScan
    {
        public byte[]? Metadata, Binary;
        public string MetadataName = "", BinaryName = "";
        public int BinaryRank = int.MaxValue;
        public UnityVersion? Unity;
        public int UnityRank = int.MaxValue;
    }

    private static GameInput FromArchive(string file, string? abi)
    {
        var scan = new ArchiveScan();
        using (FileStream fs = File.OpenRead(file))
            ScanArchive(fs, Path.GetFileName(file), abi, scan, depth: 0);

        if (scan.Binary == null)
            throw new InputException(
                $"'{file}' contains no IL2CPP binary (lib/<abi>/libil2cpp.so or UnityFramework). It may be a Mono build or not a Unity game.");
        if (scan.Metadata == null)
            throw new InputException($"'{file}' contains an IL2CPP binary but no global-metadata.dat.");

        return new GameInput
        {
            Binary = scan.Binary,
            BinaryName = scan.BinaryName,
            Metadata = scan.Metadata,
            MetadataName = scan.MetadataName,
            UnityVersion = scan.Unity,
            Kind = "archive",
        };
    }

    private static byte[] ReadEntry(ZipArchiveEntry entry)
    {
        using Stream s = entry.Open();
        using var ms = new MemoryStream(entry.Length > 0 && entry.Length < int.MaxValue ? (int)entry.Length : 0);
        s.CopyTo(ms);
        return ms.ToArray();
    }

    private static void ScanArchive(Stream stream, string label, string? abi, ArchiveScan scan, int depth)
    {
        using var zip = new ZipArchive(stream, ZipArchiveMode.Read, leaveOpen: true);
        var nested = new List<ZipArchiveEntry>();
        foreach (ZipArchiveEntry entry in zip.Entries)
        {
            string full = entry.FullName.Replace('\\', '/');
            string name = Path.GetFileName(full);
            if (name.Length == 0) continue;

            if (name.Equals("global-metadata.dat", StringComparison.OrdinalIgnoreCase))
            {
                scan.Metadata ??= ReadEntry(entry);
                if (scan.MetadataName.Length == 0) scan.MetadataName = label + "!" + full;
            }
            else if (BinaryFileNames.Contains(name, StringComparer.OrdinalIgnoreCase))
            {
                int rank = AbiRank("/" + full, abi);
                if (rank < scan.BinaryRank)
                {
                    scan.BinaryRank = rank;
                    scan.Binary = ReadEntry(entry);
                    scan.BinaryName = label + "!" + full;
                }
            }
            else if (CarrierRank(name) is var carrier && carrier >= 0 && carrier < scan.UnityRank)
            {
                using Stream s = entry.Open();
                var buffer = new byte[4096];
                int n = s.ReadAtLeast(buffer, buffer.Length, throwOnEndOfStream: false);
                if (ScanForUnityVersion(buffer.AsSpan(0, n)) is { } found)
                {
                    scan.Unity = found;
                    scan.UnityRank = carrier;
                }
            }
            else if (depth == 0 && name.EndsWith(".apk", StringComparison.OrdinalIgnoreCase))
            {
                nested.Add(entry); // XAPK / APKS / APKM: a zip of split APKs
            }
        }

        foreach (ZipArchiveEntry entry in nested)
        {
            using var inner = new MemoryStream(ReadEntry(entry));
            try
            {
                ScanArchive(inner, label + "!" + entry.FullName, abi, scan, depth + 1);
            }
            catch (InvalidDataException)
            {
                // Not a readable zip; ignore and keep looking in the other splits.
            }
        }
    }
}
