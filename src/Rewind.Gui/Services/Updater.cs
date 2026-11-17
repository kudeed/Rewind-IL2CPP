using System.Reflection;
using System.Text.Json;
using Velopack;
using Velopack.Sources;

namespace Rewind.Gui.Services;

public static class AppInfo
{
    public const string RepositoryUrl = "https://github.com/ratman-bit/Rewind-IL2CPP-Decompiler";
    public const string ReleasesUrl = RepositoryUrl + "/releases";
    public const string LicenseUrl = RepositoryUrl + "/blob/main/LICENSE";
    public const string ReadmeUrl = RepositoryUrl + "#readme";

    /// <summary>The installed version, or the version this copy was built as.</summary>
    public static string Version { get; } =
        Updater.InstalledVersion
        ?? (typeof(AppInfo).Assembly.GetCustomAttribute<AssemblyInformationalVersionAttribute>()?.InformationalVersion
            ?? typeof(AppInfo).Assembly.GetName().Version?.ToString(3) ?? "0.0.0").Split('+')[0];
}

/// <summary>
/// Updates from the GitHub releases of the repository, through Velopack. Each of the two branches has a channel of
/// its own: "main" (work that passed the full test pass) and "experimental" (everything new). Only an installed copy
/// can update itself; one run from a build folder only says so.
/// </summary>
public sealed class Updater
{
    public const string Main = "main";
    public const string Experimental = "experimental";

    private Manager? _manager;
    private string? _managerChannel;

    public static bool IsInstalled => Probe() is { IsInstalled: true };

    public static string? InstalledVersion => Probe() is { IsInstalled: true } m ? m.CurrentVersion?.ToString() : null;

    /// <summary>The branch the installed copy came from, when it is one of the two.</summary>
    public static string? InstalledChannel =>
        Probe() is { IsInstalled: true } m && m.InstalledChannel is Main or Experimental ? m.InstalledChannel : null;

    /// <summary>An update downloaded earlier and not yet installed.</summary>
    public static VelopackAsset? Pending
    {
        get
        {
            try
            {
                return Probe() is { IsInstalled: true } m ? m.UpdatePendingRestart : null;
            }
            catch (Exception)
            {
                return null;
            }
        }
    }

    /// <summary>
    /// The newest build on <paramref name="channel"/>, or null when this copy has it. A build on the other branch
    /// than the one installed may be older; it is offered all the same (UpdateInfo.IsDowngrade), as that is a switch.
    /// </summary>
    public Task<UpdateInfo?> CheckAsync(string channel) => ManagerFor(channel).CheckForUpdatesAsync();

    public Task DownloadAsync(UpdateInfo update, string channel, Action<int> progress) =>
        ManagerFor(channel).DownloadUpdatesAsync(update, progress);

    /// <summary>Ends this process, installs the build and starts it.</summary>
    public void ApplyAndRestart(VelopackAsset build, string channel) => ManagerFor(channel).ApplyUpdatesAndRestart(build);

    private Manager ManagerFor(string channel)
    {
        if (_manager == null || _managerChannel != channel)
        {
            _manager = new Manager(new ChannelSource(AppInfo.RepositoryUrl, channel), new UpdateOptions
            {
                ExplicitChannel = channel,
                AllowVersionDowngrade = channel != InstalledChannel,
            });
            _managerChannel = channel;
        }
        return _manager;
    }

    private static Manager? _probe;
    private static bool _probed;

    private static Manager? Probe()
    {
        if (_probed) return _probe;
        _probed = true;
        try
        {
            _probe = new Manager(new ChannelSource(AppInfo.RepositoryUrl, Main), null);
        }
        catch (Exception)
        {
            // Not installed by Velopack, and it says so by throwing on some setups.
            _probe = null;
        }
        return _probe;
    }
}

/// <summary>Velopack's update manager, also saying which channel the installed copy came from.</summary>
internal sealed class Manager(IUpdateSource source, UpdateOptions? options) : UpdateManager(source, options, null)
{
    public string? InstalledChannel => Locator?.Channel;
}

/// <summary>
/// The GitHub releases of one channel. Velopack's own GitHub source reads only the ten newest releases of the
/// repository, and with a build per push on two branches, those can all be the other branch's. This one reads the
/// newest hundred and keeps the few that carry this channel's release index.
/// </summary>
internal sealed class ChannelSource(string repository, string channel) : GithubSource(repository, null, prerelease: true)
{
    private const int Kept = 5;

    protected override async Task<GithubRelease[]> GetReleases(bool includePrereleases)
    {
        string index = $"releases.{channel}.json";
        var uri = new Uri(GetApiBaseUrl(RepoUri), $"repos{RepoUri.AbsolutePath}/releases?per_page=100&page=1");
        string json = await Downloader.DownloadString(uri.ToString(), GetRequestHeaders("application/vnd.github.v3+json")).ConfigureAwait(false);
        List<GithubRelease>? releases = JsonSerializer.Deserialize<List<GithubRelease>>(json);
        if (releases == null) return [];
        return releases
            .Where(r => r.Assets.Any(a => string.Equals(a.Name, index, StringComparison.OrdinalIgnoreCase)))
            .OrderByDescending(r => r.PublishedAt)
            .Take(Kept)
            .ToArray();
    }
}
