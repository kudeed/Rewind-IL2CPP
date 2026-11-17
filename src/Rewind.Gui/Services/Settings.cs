using System.IO;
using System.Text.Json;
using System.Text.Json.Serialization;

namespace Rewind.Gui.Services;

public enum AppTheme { System, Light, Dark }

/// <summary>What the window remembers between runs. Kept in %AppData%\Rewind\gui-settings.json.</summary>
public sealed class GuiSettings
{
    public AppTheme Theme { get; set; } = AppTheme.System;
    public string Accent { get; set; } = "Purple";

    /// <summary>Look for a new build at start and every few hours, download it, install it at the next start.</summary>
    public bool AutoUpdate { get; set; } = true;
    /// <summary>The branch whose builds this copy updates to ("main" or "experimental"); null: the one it was installed from.</summary>
    public string? UpdateChannel { get; set; }

    public bool OpenOutputWhenDone { get; set; } = true;
    public bool LowerPriority { get; set; } = true;
    /// <summary>Where each game's output folder goes; null means Documents\Rewind.</summary>
    public string? OutputRoot { get; set; }
    /// <summary>A rewind.exe to use instead of the one installed with the app.</summary>
    public string? CliPath { get; set; }

    public List<string> RecentInputs { get; set; } = [];

    // The choices of the last run.
    public string Command { get; set; } = "decompile";
    public bool WriteSource { get; set; } = true;
    public string CSharp { get; set; } = "latest";
    public bool StateMachines { get; set; }
    public int Threads { get; set; }
    public bool Verbose { get; set; }
}

public static class SettingsStore
{
    public static string Folder { get; } =
        Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData), "Rewind");

    private static string FilePath => Path.Combine(Folder, "gui-settings.json");

    private static readonly JsonSerializerOptions Json = new()
    {
        WriteIndented = true,
        Converters = { new JsonStringEnumConverter() },
    };

    public static GuiSettings Load()
    {
        try
        {
            if (File.Exists(FilePath))
                return JsonSerializer.Deserialize<GuiSettings>(File.ReadAllText(FilePath), Json) ?? new GuiSettings();
        }
        catch (Exception e) when (e is IOException or UnauthorizedAccessException or JsonException)
        {
            // Unreadable settings are replaced by the defaults the next time they are saved.
        }
        return new GuiSettings();
    }

    public static void Save(GuiSettings settings)
    {
        try
        {
            Directory.CreateDirectory(Folder);
            string temporary = FilePath + ".tmp";
            File.WriteAllText(temporary, JsonSerializer.Serialize(settings, Json));
            File.Move(temporary, FilePath, overwrite: true);
        }
        catch (Exception e) when (e is IOException or UnauthorizedAccessException)
        {
            // Not being able to remember settings is no reason to stop working.
        }
    }
}
