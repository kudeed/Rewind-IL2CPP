using System.ComponentModel;
using System.Diagnostics;
using System.IO;
using System.Text;

namespace Rewind.Gui.Services;

/// <summary>Finds the command-line decompiler this window runs.</summary>
public static class CliLocator
{
    public const string ExeName = "rewind.exe";

    /// <summary>
    /// In order: the path chosen in the settings; the rewind.exe installed next to this app; in a clone of the
    /// repository, the newest build of src/Rewind.Cli; a rewind.exe on the PATH.
    /// </summary>
    public static string? Find(string? chosen)
    {
        if (!string.IsNullOrWhiteSpace(chosen))
            return File.Exists(chosen) ? Path.GetFullPath(chosen) : null;

        string beside = Path.Combine(AppContext.BaseDirectory, ExeName);
        if (File.Exists(beside)) return beside;

        for (DirectoryInfo? dir = new(AppContext.BaseDirectory); dir != null; dir = dir.Parent)
        {
            if (!File.Exists(Path.Combine(dir.FullName, "Rewind.slnx"))) continue;
            string? built = new[] { "Release", "Debug" }
                .Select(c => Path.Combine(dir.FullName, "src", "Rewind.Cli", "bin", c, "net10.0", ExeName))
                .Where(File.Exists)
                .OrderByDescending(File.GetLastWriteTimeUtc)
                .FirstOrDefault();
            if (built != null) return built;
            break;
        }

        foreach (string entry in (Environment.GetEnvironmentVariable("PATH") ?? "").Split(Path.PathSeparator,
                     StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries))
        {
            try
            {
                string candidate = Path.Combine(Environment.ExpandEnvironmentVariables(entry.Trim('"')), ExeName);
                if (File.Exists(candidate)) return candidate;
            }
            catch (ArgumentException)
            {
                // A malformed PATH entry.
            }
        }
        return null;
    }
}

/// <summary>Runs rewind.exe and hands over each line it prints.</summary>
public static class CliRunner
{
    /// <summary>
    /// Runs the tool to the end, or until <paramref name="cancel"/> fires (then the tool and anything it started are
    /// ended). Returns its exit code: 0 done, 1 error, 2 options it did not accept, 3 the input is not standard
    /// IL2CPP. Every line has been passed to <paramref name="onLine"/> (true: printed as an error) when this returns.
    /// </summary>
    public static async Task<int> RunAsync(string exe, IReadOnlyList<string> arguments, Action<string, bool> onLine,
        bool lowerPriority, CancellationToken cancel)
    {
        var start = new ProcessStartInfo(exe)
        {
            UseShellExecute = false,
            CreateNoWindow = true,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            StandardOutputEncoding = new UTF8Encoding(false),
            StandardErrorEncoding = new UTF8Encoding(false),
            WorkingDirectory = Path.GetDirectoryName(exe) ?? AppContext.BaseDirectory,
        };
        foreach (string argument in arguments) start.ArgumentList.Add(argument);
        // Asks the tool to print UTF-8, so paths outside the console's code page come through intact.
        start.Environment["REWIND_UTF8_OUTPUT"] = "1";

        using var process = new Process { StartInfo = start, EnableRaisingEvents = true };
        process.OutputDataReceived += (_, e) => { if (e.Data != null) onLine(e.Data, false); };
        process.ErrorDataReceived += (_, e) => { if (e.Data != null) onLine(e.Data, true); };
        process.Start();
        if (lowerPriority)
        {
            try
            {
                process.PriorityClass = ProcessPriorityClass.BelowNormal;
            }
            catch (Exception e) when (e is Win32Exception or InvalidOperationException)
            {
                // It ended already, or the priority cannot be changed; neither matters for the output.
            }
        }
        process.BeginOutputReadLine();
        process.BeginErrorReadLine();

        using (cancel.Register(() =>
               {
                   try
                   {
                       process.Kill(entireProcessTree: true);
                   }
                   catch (Exception e) when (e is InvalidOperationException or Win32Exception)
                   {
                       // Already ended.
                   }
               }))
        {
            await process.WaitForExitAsync(CancellationToken.None);
        }
        // Waits for the last redirected lines as well.
        process.WaitForExit();
        return process.ExitCode;
    }

    /// <summary>The arguments as they would be typed in a terminal.</summary>
    public static string Display(IEnumerable<string> arguments) => string.Join(" ", arguments.Select(Quote));

    private static string Quote(string argument) =>
        argument.Length > 0 && !argument.Any(c => char.IsWhiteSpace(c) || c == '"')
            ? argument
            : "\"" + argument.Replace("\"", "\\\"") + "\"";
}
