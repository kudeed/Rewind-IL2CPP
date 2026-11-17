using System.IO;
using System.Runtime.InteropServices;
using Microsoft.Win32;

namespace Rewind.Gui.Services;

/// <summary>
/// Puts the folder this app is installed in, which also holds rewind.exe, on the current user's PATH, or takes it
/// off. Only the user's own PATH is changed (HKCU\Environment), never the machine's.
/// </summary>
public static class CommandLinePath
{
    private const string Key = "Environment";
    private const string Name = "Path";

    public static string Folder { get; } = Path.TrimEndingDirectorySeparator(AppContext.BaseDirectory);

    /// <summary>Whether this folder has a rewind.exe to put on the PATH at all.</summary>
    public static bool Available => File.Exists(Path.Combine(Folder, CliLocator.ExeName));

    public static bool IsOn()
    {
        using RegistryKey? key = Registry.CurrentUser.OpenSubKey(Key);
        return Entries(Read(key)).Any(Same);
    }

    public static void Add()
    {
        using RegistryKey key = Registry.CurrentUser.CreateSubKey(Key, writable: true);
        string current = Read(key);
        if (Entries(current).Any(Same)) return;
        string trimmed = current.TrimEnd(';');
        Write(key, trimmed.Length == 0 ? Folder : trimmed + ";" + Folder);
    }

    public static void Remove()
    {
        using RegistryKey key = Registry.CurrentUser.CreateSubKey(Key, writable: true);
        string current = Read(key);
        if (!Entries(current).Any(Same)) return;
        Write(key, string.Join(";", Entries(current).Where(e => !Same(e))));
    }

    /// <summary>For the installer's steps, which must not fail over this.</summary>
    public static void TryAdd()
    {
        try
        {
            if (Available) Add();
        }
        catch (Exception e) when (e is IOException or UnauthorizedAccessException or System.Security.SecurityException)
        {
        }
    }

    public static void TryRemove()
    {
        try
        {
            Remove();
        }
        catch (Exception e) when (e is IOException or UnauthorizedAccessException or System.Security.SecurityException)
        {
        }
    }

    // Read as stored, so entries written with %VARIABLES% keep them.
    private static string Read(RegistryKey? key) =>
        key?.GetValue(Name, "", RegistryValueOptions.DoNotExpandEnvironmentNames) as string ?? "";

    private static void Write(RegistryKey key, string value)
    {
        key.SetValue(Name, value, RegistryValueKind.ExpandString);
        // Tells Explorer, and the terminals it starts from now on, that the environment changed.
        SendMessageTimeout(new IntPtr(0xFFFF), 0x001A, UIntPtr.Zero, "Environment", 0x0002, 2000, out _);
    }

    private static IEnumerable<string> Entries(string value) =>
        value.Split(';', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries);

    private static bool Same(string entry)
    {
        try
        {
            string expanded = Environment.ExpandEnvironmentVariables(entry.Trim('"'));
            return string.Equals(Path.TrimEndingDirectorySeparator(Path.GetFullPath(expanded)), Folder, StringComparison.OrdinalIgnoreCase);
        }
        catch (Exception e) when (e is ArgumentException or NotSupportedException or PathTooLongException)
        {
            return false;
        }
    }

    [DllImport("user32.dll", CharSet = CharSet.Unicode, SetLastError = true)]
    private static extern IntPtr SendMessageTimeout(IntPtr window, uint message, UIntPtr wParam, string lParam,
        uint flags, uint timeout, out UIntPtr result);
}
