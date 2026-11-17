using System.ComponentModel;
using System.Diagnostics;
using System.IO;
using System.Runtime.InteropServices;
using System.Windows;
using Microsoft.Win32;

namespace Rewind.Gui.Services;

/// <summary>File pickers, Explorer, the browser and the clipboard.</summary>
public static class Shell
{
    public const string GameFilter =
        "Games and IL2CPP files|*.exe;*.apk;*.xapk;*.apks;*.aab;*.ipa;GameAssembly.dll;libil2cpp.so;UnityFramework|All files|*.*";

    public static string? PickFile(string title, string filter, string? near = null)
    {
        var dialog = new OpenFileDialog { Title = title, Filter = filter, CheckFileExists = true };
        string? folder = ExistingFolder(near);
        if (folder != null) dialog.InitialDirectory = folder;
        return dialog.ShowDialog(Application.Current.MainWindow) == true ? dialog.FileName : null;
    }

    public static string? PickFolder(string title, string? near = null)
    {
        var dialog = new OpenFolderDialog { Title = title };
        string? folder = ExistingFolder(near);
        if (folder != null) dialog.InitialDirectory = folder;
        return dialog.ShowDialog(Application.Current.MainWindow) == true ? dialog.FolderName : null;
    }

    /// <summary>Opens a folder in Explorer; false when it does not exist.</summary>
    public static bool OpenFolder(string? path)
    {
        if (string.IsNullOrWhiteSpace(path) || !Directory.Exists(path)) return false;
        return Start(new ProcessStartInfo("explorer.exe") { ArgumentList = { path } });
    }

    /// <summary>Opens a file with the program Windows has for it.</summary>
    public static bool OpenFile(string? path) =>
        !string.IsNullOrWhiteSpace(path) && File.Exists(path) && Start(new ProcessStartInfo(path) { UseShellExecute = true });

    public static void OpenUrl(string url) => Start(new ProcessStartInfo(url) { UseShellExecute = true });

    public static bool CopyText(string text)
    {
        try
        {
            Clipboard.SetText(text);
            return true;
        }
        catch (COMException)
        {
            // Another program holds the clipboard.
            return false;
        }
    }

    private static bool Start(ProcessStartInfo start)
    {
        try
        {
            using Process? _ = Process.Start(start);
            return true;
        }
        catch (Exception e) when (e is Win32Exception or InvalidOperationException or FileNotFoundException)
        {
            return false;
        }
    }

    private static string? ExistingFolder(string? near)
    {
        if (string.IsNullOrWhiteSpace(near)) return null;
        try
        {
            string full = Path.GetFullPath(near);
            if (Directory.Exists(full)) return full;
            string? parent = Path.GetDirectoryName(full);
            return parent != null && Directory.Exists(parent) ? parent : null;
        }
        catch (Exception e) when (e is ArgumentException or NotSupportedException or PathTooLongException)
        {
            return null;
        }
    }
}
