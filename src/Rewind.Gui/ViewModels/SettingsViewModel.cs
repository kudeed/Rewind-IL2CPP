using System.Runtime.CompilerServices;
using System.Windows;
using System.Windows.Threading;
using CommunityToolkit.Mvvm.ComponentModel;
using CommunityToolkit.Mvvm.Input;
using MaterialDesignThemes.Wpf;
using Rewind.Gui.Services;
using Velopack;

namespace Rewind.Gui.ViewModels;

public sealed partial class SettingsViewModel : ObservableObject
{
    private static readonly TimeSpan CheckEvery = TimeSpan.FromHours(4);

    private readonly GuiSettings _s;
    private readonly SnackbarMessageQueue _messages;
    private readonly MainViewModel _main;
    private readonly Updater _updater = new();
    private readonly DispatcherTimer _checkTimer;
    private UpdateInfo? _found;
    private VelopackAsset? _downloaded;
    private string? _foundChannel;
    private Accent _accent;

    public SettingsViewModel(GuiSettings settings, SnackbarMessageQueue messages, MainViewModel main)
    {
        _s = settings;
        _messages = messages;
        _main = main;
        _accent = Accent.Named(settings.Accent);
        _onPath = CommandLinePath.Available && CommandLinePath.IsOn();
        _updateStatus = IsInstalled
            ? $"Updates come from the {Channel} branch's releases."
            : "This copy was not installed with the Rewind installer, so it does not update itself. " +
              "Install Rewind from the releases page to get updates.";
        _checkTimer = new DispatcherTimer { Interval = CheckEvery };
        _checkTimer.Tick += async (_, _) => await CheckAsync(automatic: true);
    }

    // ---- Appearance

    public IReadOnlyList<Accent> Accents => Accent.All;

    public Accent SelectedAccent
    {
        get => _accent;
        set
        {
            if (value == null || value == _accent) return;
            _accent = value;
            _s.Accent = value.Name;
            SaveAndApply();
            OnPropertyChanged();
        }
    }

    public bool IsSystemTheme { get => _s.Theme == AppTheme.System; set { if (value) SetTheme(AppTheme.System); } }
    public bool IsLightTheme { get => _s.Theme == AppTheme.Light; set { if (value) SetTheme(AppTheme.Light); } }
    public bool IsDarkTheme { get => _s.Theme == AppTheme.Dark; set { if (value) SetTheme(AppTheme.Dark); } }

    private void SetTheme(AppTheme theme)
    {
        if (_s.Theme == theme) return;
        _s.Theme = theme;
        SaveAndApply();
        OnPropertyChanged(nameof(IsSystemTheme));
        OnPropertyChanged(nameof(IsLightTheme));
        OnPropertyChanged(nameof(IsDarkTheme));
    }

    private void SaveAndApply()
    {
        SettingsStore.Save(_s);
        ThemeService.Apply(_s);
    }

    // ---- Running

    public bool OpenOutputWhenDone { get => _s.OpenOutputWhenDone; set => Store(_s.OpenOutputWhenDone, value, v => _s.OpenOutputWhenDone = v); }

    public bool LowerPriority { get => _s.LowerPriority; set => Store(_s.LowerPriority, value, v => _s.LowerPriority = v); }

    public string OutputRoot
    {
        get => _s.OutputRoot ?? "";
        set
        {
            if (Store(_s.OutputRoot ?? "", value ?? "", v => _s.OutputRoot = string.IsNullOrWhiteSpace(v) ? null : v.Trim()))
                _main.Decompile.OutputRootChanged();
        }
    }

    public string DefaultOutputRoot => DecompileViewModel.DefaultOutputRoot;

    [RelayCommand]
    private void BrowseOutputRoot()
    {
        string? folder = Shell.PickFolder("Where should each game's output folder go?", OutputRoot.Length > 0 ? OutputRoot : DefaultOutputRoot);
        if (folder != null) OutputRoot = folder;
    }

    // ---- Command line

    public string CliPath
    {
        get => _s.CliPath ?? "";
        set
        {
            if (Store(_s.CliPath ?? "", value ?? "", v => _s.CliPath = string.IsNullOrWhiteSpace(v) ? null : v.Trim()))
                OnPropertyChanged(nameof(CliInUse));
        }
    }

    public string CliInUse => CliLocator.Find(_s.CliPath) is { } exe
        ? "Runs " + exe
        : _s.CliPath != null
            ? "There is no file at the path below."
            : "The command-line tool (rewind.exe) was not found. Install Rewind, or build src/Rewind.Cli.";

    [RelayCommand]
    private void BrowseCli()
    {
        string? file = Shell.PickFile("Choose rewind.exe", "rewind.exe|rewind.exe|Programs|*.exe", CliPath);
        if (file != null) CliPath = file;
    }

    public bool CanChangePath => CommandLinePath.Available;

    public string PathFolder => CommandLinePath.Folder;

    private bool _onPath;

    public bool OnPath
    {
        get => _onPath;
        set
        {
            if (value == _onPath) return;
            try
            {
                if (value) CommandLinePath.Add();
                else CommandLinePath.Remove();
                _onPath = CommandLinePath.IsOn();
                _messages.Enqueue(_onPath
                    ? "rewind is on your PATH. Terminals opened from now on can run it."
                    : "rewind is no longer on your PATH.");
            }
            catch (Exception e) when (e is UnauthorizedAccessException or System.IO.IOException or System.Security.SecurityException)
            {
                _messages.Enqueue("Your PATH could not be changed: " + e.Message);
            }
            OnPropertyChanged();
        }
    }

    // ---- Updates

    public string Version => AppInfo.Version;

    public bool IsInstalled => Updater.IsInstalled;

    public string InstalledFrom => Updater.InstalledChannel is { } channel
        ? $"Version {AppInfo.Version}, installed from the {channel} branch"
        : $"Version {AppInfo.Version}";

    public bool AutoUpdate
    {
        get => _s.AutoUpdate;
        set
        {
            if (!Store(_s.AutoUpdate, value, v => _s.AutoUpdate = v)) return;
            if (value)
            {
                _checkTimer.Start();
                _ = CheckAsync(automatic: true);
            }
            else
            {
                _checkTimer.Stop();
            }
        }
    }

    /// <summary>The branch updates come from.</summary>
    public string Channel => _s.UpdateChannel is Updater.Main or Updater.Experimental
        ? _s.UpdateChannel
        : Updater.InstalledChannel ?? Updater.Main;

    public bool IsMainChannel { get => Channel == Updater.Main; set { if (value) SetChannel(Updater.Main); } }

    public bool IsExperimentalChannel { get => Channel == Updater.Experimental; set { if (value) SetChannel(Updater.Experimental); } }

    [RelayCommand]
    private void ChooseChannel(string channel) => SetChannel(channel);

    public string VersionTitle => "Rewind " + AppInfo.Version;

    private void SetChannel(string channel)
    {
        if (Channel == channel) return;
        _s.UpdateChannel = channel;
        SettingsStore.Save(_s);
        OnPropertyChanged(nameof(Channel));
        OnPropertyChanged(nameof(IsMainChannel));
        OnPropertyChanged(nameof(IsExperimentalChannel));
        _found = null;
        _downloaded = null;
        CanDownload = false;
        ReadyToRestart = false;
        if (IsInstalled) _ = CheckAsync(automatic: AutoUpdate);
    }

    [ObservableProperty]
    private string _updateStatus;

    [ObservableProperty]
    private bool _isBusy;

    [ObservableProperty]
    private bool _isDownloading;

    [ObservableProperty]
    private int _downloadProgress;

    /// <summary>A build was found and is not downloaded yet (updates are not automatic).</summary>
    [ObservableProperty]
    private bool _canDownload;

    /// <summary>A build is downloaded and goes in at the next start, or now with a restart.</summary>
    [ObservableProperty]
    private bool _readyToRestart;

    internal void Started()
    {
        if (!IsInstalled) return;
        if (Updater.Pending is { } pending)
        {
            _downloaded = pending;
            _foundChannel = Channel;
            ReadyToRestart = true;
            UpdateStatus = $"Rewind {pending.Version} is downloaded and is installed when Rewind restarts.";
        }
        if (AutoUpdate)
        {
            _checkTimer.Start();
            _ = CheckAsync(automatic: true);
        }
    }

    [RelayCommand]
    private Task CheckNow() => CheckAsync(automatic: false);

    private async Task CheckAsync(bool automatic)
    {
        if (!IsInstalled || IsBusy) return;
        string channel = Channel;
        IsBusy = true;
        UpdateStatus = $"Looking for a newer build on {channel}…";
        try
        {
            UpdateInfo? found = await _updater.CheckAsync(channel);
            if (channel != Channel) return;
            if (found == null)
            {
                _found = null;
                CanDownload = false;
                UpdateStatus = ReadyToRestart && _downloaded != null
                    ? $"Rewind {_downloaded.Version} is downloaded and is installed when Rewind restarts."
                    : $"This is the newest build on {channel} (checked {DateTime.Now:t}).";
                return;
            }
            _found = found;
            _foundChannel = channel;
            string version = found.TargetFullRelease.Version.ToString();
            UpdateStatus = found.IsDowngrade
                ? $"The newest build on {channel} is {version}, older than this one. Download it to switch."
                : $"Rewind {version} is available on {channel}.";
            if (automatic && !found.IsDowngrade)
            {
                await DownloadAsync(found, channel, announce: true);
            }
            else
            {
                CanDownload = true;
                if (automatic) _messages.Enqueue($"Rewind {version} is available on {channel}.", "SHOW", () => _main.ShowSettings());
            }
        }
        catch (Exception e)
        {
            UpdateStatus = "Could not look for updates: " + e.Message;
        }
        finally
        {
            IsBusy = false;
        }
    }

    [RelayCommand]
    private async Task DownloadAndRestart()
    {
        if (_found == null || _foundChannel == null || IsBusy) return;
        IsBusy = true;
        try
        {
            if (await DownloadAsync(_found, _foundChannel, announce: false)) RestartNow();
        }
        finally
        {
            IsBusy = false;
        }
    }

    private async Task<bool> DownloadAsync(UpdateInfo update, string channel, bool announce)
    {
        string version = update.TargetFullRelease.Version.ToString();
        IsDownloading = true;
        DownloadProgress = 0;
        UpdateStatus = $"Downloading Rewind {version}…";
        try
        {
            Dispatcher ui = Application.Current.Dispatcher;
            await _updater.DownloadAsync(update, channel, p => ui.BeginInvoke(() => DownloadProgress = p));
            _downloaded = update.TargetFullRelease;
            CanDownload = false;
            ReadyToRestart = true;
            UpdateStatus = update.IsDowngrade
                ? $"Rewind {version} from {channel} is downloaded. Restart to switch to it."
                : $"Rewind {version} is downloaded and is installed when Rewind restarts.";
            if (announce) _messages.Enqueue($"Rewind {version} is ready.", "RESTART NOW", RestartNow);
            return true;
        }
        catch (Exception e)
        {
            UpdateStatus = $"Rewind {version} could not be downloaded: {e.Message}";
            return false;
        }
        finally
        {
            IsDownloading = false;
        }
    }

    [RelayCommand]
    private void RestartNow()
    {
        if (_downloaded == null) return;
        if (_main.Decompile.IsRunning)
        {
            _messages.Enqueue("Rewind is still running. Restart when it has finished, or stop it first.");
            return;
        }
        SettingsStore.Save(_s);
        try
        {
            _updater.ApplyAndRestart(_downloaded, _foundChannel ?? Channel);
        }
        catch (Exception e)
        {
            UpdateStatus = "The update could not be installed: " + e.Message;
        }
    }

    // ---- About

    [RelayCommand]
    private static void OpenLink(string url) => Shell.OpenUrl(url);

    public string RepositoryUrl => AppInfo.RepositoryUrl;
    public string ReleasesUrl => AppInfo.ReleasesUrl;
    public string LicenseUrl => AppInfo.LicenseUrl;
    public string ReadmeUrl => AppInfo.ReadmeUrl;

    private bool Store<T>(T current, T value, Action<T> store, [CallerMemberName] string? name = null)
    {
        if (EqualityComparer<T>.Default.Equals(current, value)) return false;
        store(value);
        SettingsStore.Save(_s);
        OnPropertyChanged(name);
        return true;
    }
}
