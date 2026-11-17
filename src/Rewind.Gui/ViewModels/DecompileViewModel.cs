using System.Collections.Concurrent;
using System.Collections.ObjectModel;
using System.ComponentModel;
using System.Diagnostics;
using System.Globalization;
using System.IO;
using System.Text.RegularExpressions;
using System.Windows.Data;
using System.Windows.Threading;
using CommunityToolkit.Mvvm.ComponentModel;
using CommunityToolkit.Mvvm.Input;
using MaterialDesignThemes.Wpf;
using Rewind.Gui.Services;

namespace Rewind.Gui.ViewModels;

public enum RewindCommand { Info, Dump, Decompile }

public enum LineKind { Plain, Command, Note, Warning, Error, Done }

public sealed record LogLine(string Text, LineKind Kind);

public sealed record Choice<T>(string Label, T Value);

public sealed partial class AssemblyChoice(string name, int types) : ObservableObject
{
    public string Name { get; } = name;
    public string Types { get; } = types == 1 ? "1 type" : $"{types:N0} types";

    [ObservableProperty]
    private bool _isChecked;
}

public enum Outcome { None, Done, Protected, Refused, Failed, Stopped }

/// <summary>The decompile page: what to read, what to do with it, the options, and running rewind.exe.</summary>
public sealed partial class DecompileViewModel : ObservableObject
{
    public static string DefaultOutputRoot { get; } =
        Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments), "Rewind");

    private static readonly Regex AssemblyLine = new(@"^\s{2}(\S.*?)\s+(\d+) types$", RegexOptions.CultureInvariant);
    private static readonly Regex Bodies = new(@"^method bodies: (\d+) with native code, (\d+) recovered completely, (\d+) with gaps", RegexOptions.CultureInvariant);
    private static readonly Regex Source = new(@"^C# source: (\d+) types written to .*?, (\d+) with parts", RegexOptions.CultureInvariant);

    private readonly GuiSettings _s;
    private readonly SnackbarMessageQueue _messages;
    private readonly ConcurrentQueue<(string Text, bool Error)> _incoming = new();
    private readonly DispatcherTimer _flush;
    private readonly Stopwatch _clock = new();
    private CancellationTokenSource? _cancel;
    private bool _outputIsAuto = true;
    private bool _settingOutput;

    // What the run in progress reported, for the summary at its end.
    private RewindCommand _runCommand;
    private string _runOutput = "";
    private bool _runWritesSource;
    private string? _target, _content, _bodies, _source, _wrote, _lastError;
    private bool _readingAssemblies;
    private readonly List<(string Name, int Types)> _assembliesSeen = [];

    public DecompileViewModel(GuiSettings settings, SnackbarMessageQueue messages)
    {
        _s = settings;
        _messages = messages;
        foreach (string recent in settings.RecentInputs) RecentInputs.Add(recent);

        _command = settings.Command switch
        {
            "info" => RewindCommand.Info,
            "dump" => RewindCommand.Dump,
            _ => RewindCommand.Decompile,
        };
        _writeSource = settings.WriteSource;
        _stateMachines = settings.StateMachines;
        _verbose = settings.Verbose;

        CSharpChoices =
        [
            new("Latest", "latest"),
            new("C# 12", "12"),
            new("C# 11", "11"),
            new("C# 10", "10"),
            new("C# 9 (Unity 2021.2 and later)", "9"),
            new("C# 8 (Unity 2020.2 to 2021.1)", "8"),
            new("C# 7.3 (Unity 2020.1 and earlier)", "7.3"),
        ];
        _cSharp = CSharpChoices.FirstOrDefault(c => c.Value == settings.CSharp) ?? CSharpChoices[0];

        var threads = new List<Choice<int>> { new($"One per processor ({Environment.ProcessorCount})", 0) };
        for (int n = 1; n <= Environment.ProcessorCount; n++) threads.Add(new(n == 1 ? "1 thread" : $"{n} threads", n));
        ThreadChoices = threads;
        _threads = ThreadChoices.FirstOrDefault(t => t.Value == settings.Threads) ?? ThreadChoices[0];

        AbiChoices =
        [
            new("Choose automatically", ""),
            new("arm64-v8a", "arm64-v8a"),
            new("armeabi-v7a", "armeabi-v7a"),
            new("x86_64", "x86_64"),
            new("x86", "x86"),
        ];
        _abi = AbiChoices[0];

        AssemblyView = CollectionViewSource.GetDefaultView(Assemblies);
        AssemblyView.Filter = item => item is AssemblyChoice a &&
            (AssemblyFilter.Length == 0 || a.Name.Contains(AssemblyFilter, StringComparison.OrdinalIgnoreCase));

        _flush = new DispatcherTimer(DispatcherPriority.Background) { Interval = TimeSpan.FromMilliseconds(120) };
        _flush.Tick += (_, _) => Flush();
    }

    // ---- The game

    public ObservableCollection<string> RecentInputs { get; } = [];

    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(CommandLine))]
    private string _input = "";

    partial void OnInputChanged(string value)
    {
        SuggestOutput();
        if (Assemblies.Count != 0)
        {
            Assemblies.Clear();
            OnPropertyChanged(nameof(AssemblySummary));
        }
    }

    [RelayCommand]
    private void UseRecent(string path) => Input = path;

    [RelayCommand]
    private void BrowseInputFile()
    {
        string? file = Shell.PickFile("Choose the game", Shell.GameFilter, Input);
        if (file != null) Input = file;
    }

    [RelayCommand]
    private void BrowseInputFolder()
    {
        string? folder = Shell.PickFolder("Choose the game's folder", Input);
        if (folder != null) Input = folder;
    }

    // ---- What to do

    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(IsInfo), nameof(IsDump), nameof(IsDecompile), nameof(NeedsOutput), nameof(CommandDescription), nameof(CommandLine), nameof(RunLabel))]
    private RewindCommand _command;

    public bool IsInfo { get => Command == RewindCommand.Info; set { if (value) Command = RewindCommand.Info; } }
    public bool IsDump { get => Command == RewindCommand.Dump; set { if (value) Command = RewindCommand.Dump; } }
    public bool IsDecompile { get => Command == RewindCommand.Decompile; set { if (value) Command = RewindCommand.Decompile; } }

    public bool NeedsOutput => Command != RewindCommand.Info;

    /// <summary>What the run button says.</summary>
    public string RunLabel => Command switch
    {
        RewindCommand.Info => "Read info",
        RewindCommand.Dump => "Write dump.cs",
        _ => "Decompile",
    };

    public string CommandDescription => Command switch
    {
        RewindCommand.Info => "Shows what the input is, which Unity version and metadata version it uses, its assemblies, and whether Rewind can read it. Writes nothing.",
        RewindCommand.Dump => "Writes dump.cs: every type and member, with addresses and offsets.",
        _ => "Rebuilds the game's .NET assemblies with the method bodies Rewind recovers, writes C# source, and lists in recovery-report.tsv every method that was not fully recovered.",
    };

    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(CommandLine))]
    private string _outputDir = "";

    partial void OnOutputDirChanged(string value)
    {
        if (!_settingOutput) _outputIsAuto = string.IsNullOrWhiteSpace(value);
    }

    [RelayCommand]
    private void BrowseOutput()
    {
        string? folder = Shell.PickFolder("Where should the output go?", OutputDir.Length > 0 ? OutputDir : OutputRoot);
        if (folder != null) OutputDir = folder;
    }

    private string OutputRoot => string.IsNullOrWhiteSpace(_s.OutputRoot) ? DefaultOutputRoot : _s.OutputRoot;

    internal void OutputRootChanged()
    {
        if (_outputIsAuto) SuggestOutput();
    }

    /// <summary>Unless a folder was chosen by hand: a folder named after the game in the output location.</summary>
    private void SuggestOutput()
    {
        if (!_outputIsAuto) return;
        string name = GameName(Input);
        _settingOutput = true;
        OutputDir = name.Length == 0 ? "" : Path.Combine(OutputRoot, name);
        _settingOutput = false;
    }

    private static string GameName(string input)
    {
        string path = input.Trim().Trim('"').TrimEnd('\\', '/');
        if (path.Length == 0) return "";
        string name;
        try
        {
            string extension = Path.GetExtension(path).ToLowerInvariant();
            name = Directory.Exists(path) || extension is "" ? Path.GetFileName(path)
                : extension is ".exe" or ".apk" or ".xapk" or ".apks" or ".aab" or ".ipa" ? Path.GetFileNameWithoutExtension(path)
                : Path.GetFileName(Path.GetDirectoryName(path) ?? "");
        }
        catch (ArgumentException)
        {
            return "";
        }
        foreach (char c in Path.GetInvalidFileNameChars()) name = name.Replace(c, '_');
        return name.Trim();
    }

    // ---- Decompile options

    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(CommandLine))]
    private bool _writeSource;

    public IReadOnlyList<Choice<string>> CSharpChoices { get; }

    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(CommandLine))]
    private Choice<string> _cSharp;

    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(CommandLine))]
    private bool _stateMachines;

    public IReadOnlyList<Choice<int>> ThreadChoices { get; }

    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(CommandLine))]
    private Choice<int> _threads;

    // ---- Assemblies

    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(CommandLine))]
    private bool _allAssemblies = true;

    public ObservableCollection<AssemblyChoice> Assemblies { get; } = [];

    public ICollectionView AssemblyView { get; }

    [ObservableProperty]
    private string _assemblyFilter = "";

    partial void OnAssemblyFilterChanged(string value) => AssemblyView.Refresh();

    /// <summary>Assembly names typed in, separated by commas or spaces.</summary>
    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(CommandLine))]
    private string _typedAssemblies = "";

    [ObservableProperty]
    private bool _isReadingAssemblies;

    public string AssemblySummary => Assemblies.Count == 0
        ? "Read the list from the game to choose from it, or type the names below."
        : $"{Assemblies.Count(a => a.IsChecked)} of {Assemblies.Count} chosen";

    private IEnumerable<string> ChosenAssemblies() =>
        Assemblies.Where(a => a.IsChecked).Select(a => a.Name)
            .Concat(TypedAssemblies.Split([',', ';', ' '], StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries))
            .Distinct(StringComparer.OrdinalIgnoreCase);

    [RelayCommand]
    private async Task ReadAssemblies()
    {
        string? exe = CliLocator.Find(_s.CliPath);
        if (exe == null)
        {
            _messages.Enqueue("The command-line tool (rewind.exe) was not found. See Settings.");
            return;
        }
        if (!InputExists(out string input))
        {
            _messages.Enqueue("Choose a game first.");
            return;
        }
        IsReadingAssemblies = true;
        var lines = new ConcurrentQueue<(string Text, bool Error)>();
        try
        {
            int exit = await CliRunner.RunAsync(exe, CommonArguments(RewindCommand.Info, input), (t, e) => lines.Enqueue((t, e)), _s.LowerPriority, CancellationToken.None);
            var found = new List<(string Name, int Types)>();
            bool inList = false;
            string? error = null;
            foreach ((string text, bool isError) in lines)
            {
                if (isError && text.StartsWith("error:", StringComparison.Ordinal)) error = text[6..].Trim();
                if (text == "assemblies:") inList = true;
                else if (inList && AssemblyLine.Match(text) is { Success: true } m) found.Add((m.Groups[1].Value, int.Parse(m.Groups[2].Value, CultureInfo.InvariantCulture)));
            }
            if (exit == 0) ShowAssemblies(found);
            else _messages.Enqueue("The assembly list could not be read: " + (error ?? $"rewind ended with code {exit}"));
        }
        catch (Exception e) when (e is Win32Exception or InvalidOperationException or IOException)
        {
            _messages.Enqueue("rewind.exe could not be started: " + e.Message);
        }
        finally
        {
            IsReadingAssemblies = false;
        }
    }

    private void ShowAssemblies(IReadOnlyList<(string Name, int Types)> found)
    {
        var chosen = new HashSet<string>(ChosenAssemblies(), StringComparer.OrdinalIgnoreCase);
        foreach (AssemblyChoice a in Assemblies) a.PropertyChanged -= OnAssemblyChecked;
        Assemblies.Clear();
        foreach ((string name, int types) in found.OrderBy(a => a.Name, StringComparer.OrdinalIgnoreCase))
        {
            var choice = new AssemblyChoice(name, types) { IsChecked = chosen.Contains(name) };
            choice.PropertyChanged += OnAssemblyChecked;
            Assemblies.Add(choice);
        }
        // What was typed and is now in the list is ticked there instead.
        TypedAssemblies = string.Join(", ", TypedAssemblies
            .Split([',', ';', ' '], StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries)
            .Where(t => !Assemblies.Any(a => string.Equals(a.Name, t, StringComparison.OrdinalIgnoreCase))));
        OnPropertyChanged(nameof(AssemblySummary));
        OnPropertyChanged(nameof(CommandLine));
    }

    private void OnAssemblyChecked(object? sender, PropertyChangedEventArgs e)
    {
        OnPropertyChanged(nameof(AssemblySummary));
        OnPropertyChanged(nameof(CommandLine));
    }

    [RelayCommand]
    private void ChooseNoAssemblies()
    {
        foreach (AssemblyChoice a in Assemblies) a.IsChecked = false;
    }

    // ---- Advanced

    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(CommandLine))]
    private string _metadata = "";

    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(CommandLine))]
    private string _binary = "";

    public IReadOnlyList<Choice<string>> AbiChoices { get; }

    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(CommandLine))]
    private Choice<string> _abi;

    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(CommandLine))]
    private string _unity = "";

    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(CommandLine))]
    private string _signatures = "";

    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(CommandLine))]
    private bool _verbose;

    [RelayCommand]
    private void BrowseMetadata()
    {
        string? file = Shell.PickFile("Choose global-metadata.dat", "IL2CPP metadata|global-metadata.dat;*.dat|All files|*.*", Metadata.Length > 0 ? Metadata : Input);
        if (file != null) Metadata = file;
    }

    [RelayCommand]
    private void BrowseBinary()
    {
        string? file = Shell.PickFile("Choose the IL2CPP binary", "IL2CPP binaries|GameAssembly.dll;libil2cpp.so;UnityFramework;*.dll;*.so|All files|*.*", Binary.Length > 0 ? Binary : Input);
        if (file != null) Binary = file;
    }

    [RelayCommand]
    private void BrowseSignatureFile()
    {
        string? file = Shell.PickFile("Choose a signature library", "Signature libraries|*.sig|All files|*.*", Signatures);
        if (file != null) Signatures = file;
    }

    [RelayCommand]
    private void BrowseSignatureFolder()
    {
        string? folder = Shell.PickFolder("Choose a folder of signature libraries", Signatures);
        if (folder != null) Signatures = folder;
    }

    [RelayCommand]
    private void ResetAdvanced()
    {
        Metadata = "";
        Binary = "";
        Abi = AbiChoices[0];
        Unity = "";
        Signatures = "";
        Verbose = false;
    }

    // ---- The command

    /// <summary>The command this runs, as it would be typed in a terminal.</summary>
    public string CommandLine
    {
        get
        {
            string input = Input.Trim().Trim('"');
            return "rewind " + CliRunner.Display(Arguments(input.Length == 0 ? "<game>" : Full(input), Command));
        }
    }

    /// <summary>True for a moment after the command was copied: its button shows a check.</summary>
    [ObservableProperty]
    private bool _commandCopied;

    /// <summary>True for a moment after the output was copied.</summary>
    [ObservableProperty]
    private bool _logCopied;

    [RelayCommand]
    private async Task CopyCommandLine()
    {
        if (!Shell.CopyText(CommandLine)) return;
        CommandCopied = true;
        await Task.Delay(1600);
        CommandCopied = false;
    }

    private List<string> Arguments(string input, RewindCommand command)
    {
        List<string> arguments = CommonArguments(command, input);
        if (command != RewindCommand.Info && OutputDir.Trim().Length > 0) arguments.AddRange(["-o", Full(OutputDir.Trim().Trim('"'))]);
        if (command == RewindCommand.Decompile)
        {
            if (!AllAssemblies)
                foreach (string name in ChosenAssemblies()) arguments.AddRange(["--assembly", name]);
            if (!WriteSource) arguments.Add("--no-source");
            else if (CSharp.Value != "latest") arguments.AddRange(["--csharp", CSharp.Value]);
            if (StateMachines && WriteSource) arguments.Add("--state-machines");
            if (Threads.Value > 0) arguments.AddRange(["--threads", Threads.Value.ToString(CultureInfo.InvariantCulture)]);
            if (Signatures.Trim().Length > 0) arguments.AddRange(["--signatures", Full(Signatures.Trim().Trim('"'))]);
        }
        return arguments;
    }

    /// <summary>The arguments every command takes: what to read and how to find its files.</summary>
    private List<string> CommonArguments(RewindCommand command, string input)
    {
        var arguments = new List<string>
        {
            command switch { RewindCommand.Info => "info", RewindCommand.Dump => "dump", _ => "decompile" },
            input,
        };
        if (Metadata.Trim().Length > 0) arguments.AddRange(["--metadata", Full(Metadata.Trim().Trim('"'))]);
        if (Binary.Trim().Length > 0) arguments.AddRange(["--binary", Full(Binary.Trim().Trim('"'))]);
        if (Abi.Value.Length > 0) arguments.AddRange(["--abi", Abi.Value]);
        if (Unity.Trim().Length > 0) arguments.AddRange(["--unity", Unity.Trim()]);
        if (Verbose) arguments.Add("-v");
        return arguments;
    }

    private static string Full(string path)
    {
        try
        {
            return Path.GetFullPath(path);
        }
        catch (Exception e) when (e is ArgumentException or NotSupportedException or PathTooLongException)
        {
            return path;
        }
    }

    private bool InputExists(out string input)
    {
        input = Full(Input.Trim().Trim('"'));
        return input.Length > 0 && (File.Exists(input) || Directory.Exists(input));
    }

    // ---- Running

    [ObservableProperty]
    private bool _isRunning;

    [ObservableProperty]
    private string _phase = "";

    [ObservableProperty]
    private string _elapsed = "";

    public ObservableCollection<LogLine> Lines { get; } = [];

    [ObservableProperty]
    private Outcome _outcome;

    [ObservableProperty]
    private PackIconKind _outcomeIcon = PackIconKind.CheckCircleOutline;

    /// <summary>A large figure above the title (the share of bodies recovered), or empty.</summary>
    [ObservableProperty]
    private string _outcomeBig = "";

    /// <summary>That share as a number, which the view counts up to; NaN when there is none.</summary>
    [ObservableProperty]
    private double _outcomePercent = double.NaN;

    [ObservableProperty]
    private string _outcomeTitle = "";

    [ObservableProperty]
    private string _outcomeDetail = "";

    [ObservableProperty]
    private bool _hasOutcome;

    [ObservableProperty]
    private bool _canOpenOutput;

    [ObservableProperty]
    private bool _canOpenSource;

    [ObservableProperty]
    private bool _canOpenReport;

    [ObservableProperty]
    private string _lastOutput = "";

    [RelayCommand]
    private async Task Run()
    {
        if (IsRunning) return;
        string? exe = CliLocator.Find(_s.CliPath);
        if (exe == null)
        {
            _messages.Enqueue("The command-line tool (rewind.exe) was not found. See Settings.");
            return;
        }
        if (!InputExists(out string input))
        {
            _messages.Enqueue(Input.Trim().Length == 0 ? "Choose a game first: a folder, an .exe, an APK or IPA, or the IL2CPP binary." : "There is no file or folder at " + input);
            return;
        }
        if (Command != RewindCommand.Info && OutputDir.Trim().Length == 0)
        {
            _messages.Enqueue("Choose where the output should go.");
            return;
        }
        if (Command == RewindCommand.Decompile && !AllAssemblies && !ChosenAssemblies().Any())
        {
            _messages.Enqueue("Choose at least one assembly, or switch back to all of them.");
            return;
        }

        Remember(input);
        List<string> arguments = Arguments(input, Command);
        _runCommand = Command;
        _runOutput = Command == RewindCommand.Info ? "" : Full(OutputDir.Trim().Trim('"'));
        _runWritesSource = WriteSource;
        _target = _content = _bodies = _source = _wrote = _lastError = null;
        _readingAssemblies = false;
        _assembliesSeen.Clear();
        while (_incoming.TryDequeue(out _)) { }

        Lines.Clear();
        Lines.Add(new LogLine("> rewind " + CliRunner.Display(arguments), LineKind.Command));
        HasOutcome = false;
        Outcome = Outcome.None;
        Phase = "Starting";
        Elapsed = "";
        IsRunning = true;
        _clock.Restart();
        _flush.Start();
        _cancel = new CancellationTokenSource();

        int exit;
        try
        {
            exit = await CliRunner.RunAsync(exe, arguments, (text, error) => _incoming.Enqueue((text, error)), _s.LowerPriority, _cancel.Token);
        }
        catch (Exception e) when (e is Win32Exception or InvalidOperationException or IOException)
        {
            exit = -1;
            _incoming.Enqueue(("error: rewind.exe could not be started: " + e.Message, true));
        }
        _clock.Stop();
        _flush.Stop();
        Flush();
        bool stopped = _cancel.IsCancellationRequested;
        _cancel.Dispose();
        _cancel = null;
        IsRunning = false;
        Finish(exit, stopped);
    }

    [RelayCommand]
    private void Stop() => _cancel?.Cancel();

    private void Remember(string input)
    {
        _s.Command = Command switch { RewindCommand.Info => "info", RewindCommand.Dump => "dump", _ => "decompile" };
        _s.WriteSource = WriteSource;
        _s.CSharp = CSharp.Value;
        _s.StateMachines = StateMachines;
        _s.Threads = Threads.Value;
        _s.Verbose = Verbose;
        _s.RecentInputs.RemoveAll(r => string.Equals(r, input, StringComparison.OrdinalIgnoreCase));
        _s.RecentInputs.Insert(0, input);
        if (_s.RecentInputs.Count > 12) _s.RecentInputs.RemoveRange(12, _s.RecentInputs.Count - 12);
        SettingsStore.Save(_s);

        // Changing the list under the editable box can clear its text; it is put back.
        string typed = Input;
        RecentInputs.Clear();
        foreach (string recent in _s.RecentInputs) RecentInputs.Add(recent);
        Input = typed;
    }

    private void Flush()
    {
        bool any = false;
        while (_incoming.TryDequeue(out (string Text, bool Error) line))
        {
            any = true;
            Lines.Add(new LogLine(line.Text, Kind(line.Text, line.Error)));
            Observe(line.Text, line.Error);
        }
        if (IsRunning) Elapsed = Duration(_clock.Elapsed);
        if (any) LineAdded?.Invoke();
    }

    /// <summary>Raised after lines were added, so the view can keep the newest in sight.</summary>
    public event Action? LineAdded;

    private static LineKind Kind(string text, bool error) =>
        text.StartsWith("error:", StringComparison.Ordinal) || error ? LineKind.Error
        : text.StartsWith("warning:", StringComparison.Ordinal) ? LineKind.Warning
        : text.StartsWith("note:", StringComparison.Ordinal) ? LineKind.Note
        : text.StartsWith("done:", StringComparison.Ordinal) ? LineKind.Done
        : LineKind.Plain;

    /// <summary>Follows the tool's progress lines (see src/Rewind.Cli/Program.cs and Rewind.Output's Decompiler).</summary>
    private void Observe(string text, bool error)
    {
        if (text.StartsWith("error:", StringComparison.Ordinal)) _lastError = text[6..].Trim();
        else if (error && text.Trim().Length > 0) _lastError ??= text.Trim();

        if (text.StartsWith("binary:", StringComparison.Ordinal)) Phase = "Reading the game's files";
        else if (text.StartsWith("target:", StringComparison.Ordinal)) _target = text[7..].Trim();
        else if (text.StartsWith("content:", StringComparison.Ordinal))
        {
            _content = text[8..].Trim();
            Phase = _runCommand switch
            {
                RewindCommand.Decompile => "Recognizing the runtime's functions",
                RewindCommand.Dump => "Writing dump.cs",
                _ => "Listing the assemblies",
            };
        }
        else if (text.StartsWith("runtime:", StringComparison.Ordinal)) Phase = "Rebuilding the assemblies";
        else if (text.StartsWith("rebuilt ", StringComparison.Ordinal)) Phase = "Recovering method bodies";
        else if (text.StartsWith("method bodies:", StringComparison.Ordinal))
        {
            _bodies = text;
            Phase = "Writing the assemblies";
        }
        else if (text.StartsWith("wrote ", StringComparison.Ordinal) && text.Contains(" assemblies to ", StringComparison.Ordinal))
        {
            Phase = _runWritesSource ? "Writing C# source" : "Finishing";
        }
        else if (text.StartsWith("wrote ", StringComparison.Ordinal)) _wrote = text[6..].Trim();
        else if (text.StartsWith("C# source:", StringComparison.Ordinal)) _source = text;
        else if (text == "assemblies:") _readingAssemblies = true;
        else if (_readingAssemblies && AssemblyLine.Match(text) is { Success: true } m)
            _assembliesSeen.Add((m.Groups[1].Value, int.Parse(m.Groups[2].Value, CultureInfo.InvariantCulture)));
    }

    private void Finish(int exit, bool stopped)
    {
        string took = Duration(_clock.Elapsed);
        Phase = "";
        CanOpenOutput = CanOpenSource = CanOpenReport = false;
        LastOutput = _runOutput;

        if (stopped)
        {
            Show(Outcome.Stopped, PackIconKind.StopCircleOutline, "Stopped",
                _runOutput.Length > 0 ? "The output folder may hold part of a result." : "");
            CanOpenOutput = Directory.Exists(_runOutput);
            return;
        }

        switch (exit)
        {
            case 0:
                Lines.Add(new LogLine($"finished in {took}", LineKind.Done));
                FinishDone(took);
                break;
            case 3:
                Show(Outcome.Protected, PackIconKind.ShieldLockOutline, "Not a standard IL2CPP build",
                    (_lastError ?? "The game's metadata is not in the standard format.") +
                    "\n\nRewind reads standard IL2CPP builds only. It has no decryption, memory dumping or other way around protection, so it stops here.");
                break;
            case 2:
                Show(Outcome.Refused, PackIconKind.AlertCircleOutline, "rewind did not accept these options",
                    _lastError ?? "See the output below.");
                break;
            default:
                Show(Outcome.Failed, PackIconKind.AlertCircleOutline, "Rewind stopped with an error",
                    _lastError ?? (exit == -1 ? "rewind.exe could not be started." : $"It ended with code {exit}. See the output below."));
                break;
        }
    }

    private void FinishDone(string took)
    {
        switch (_runCommand)
        {
            case RewindCommand.Info:
                Show(Outcome.Done, PackIconKind.CheckCircleOutline, "Rewind can read this game",
                    string.Join("\n", new[] { _target, _content }.Where(s => s != null)));
                if (_assembliesSeen.Count != 0) ShowAssemblies(_assembliesSeen);
                break;
            case RewindCommand.Dump:
                Show(Outcome.Done, PackIconKind.CheckCircleOutline, $"dump.cs written in {took}", _wrote ?? "");
                CanOpenOutput = Directory.Exists(_runOutput);
                break;
            default:
            {
                string title = $"Decompiled in {took}";
                string big = "";
                var detail = new List<string>();
                if (_bodies != null && Bodies.Match(_bodies) is { Success: true } b)
                {
                    long total = long.Parse(b.Groups[1].Value, CultureInfo.InvariantCulture);
                    long complete = long.Parse(b.Groups[2].Value, CultureInfo.InvariantCulture);
                    long gaps = long.Parse(b.Groups[3].Value, CultureInfo.InvariantCulture);
                    if (total != 0)
                    {
                        OutcomePercent = double.NaN;
                        OutcomePercent = Math.Round(100.0 * complete / total, 1);
                        big = (100.0 * complete / total).ToString("F1", CultureInfo.CurrentCulture) + "%";
                        title = $"{complete:N0} of {total:N0} method bodies recovered completely";
                    }
                    if (gaps != 0)
                        detail.Add($"{gaps:N0} have gaps, marked in the code with __Rewind.Opaque, __Rewind.Effect and __Rewind.Note; recovery-report.tsv lists them with the reasons.");
                }
                if (_source != null && Source.Match(_source) is { Success: true } s)
                    detail.Add($"C# source for {long.Parse(s.Groups[1].Value, CultureInfo.InvariantCulture):N0} types.");
                detail.Add($"Done in {took}.");
                Show(Outcome.Done, PackIconKind.CheckCircleOutline, title, string.Join("\n", detail), big);
                CanOpenOutput = Directory.Exists(_runOutput);
                CanOpenSource = Directory.Exists(Path.Combine(_runOutput, "src"));
                CanOpenReport = File.Exists(Path.Combine(_runOutput, "recovery-report.tsv"));
                break;
            }
        }
        if (_s.OpenOutputWhenDone && _runCommand != RewindCommand.Info) Shell.OpenFolder(_runOutput);
    }

    private void Show(Outcome outcome, PackIconKind icon, string title, string detail, string big = "")
    {
        OutcomeBig = big;
        Outcome = outcome;
        OutcomeIcon = icon;
        OutcomeTitle = title;
        OutcomeDetail = detail;
        HasOutcome = true;
    }

    [RelayCommand]
    private void OpenOutput()
    {
        if (!Shell.OpenFolder(LastOutput)) _messages.Enqueue("The output folder is not there any more.");
    }

    [RelayCommand]
    private void OpenSource() => Shell.OpenFolder(Path.Combine(LastOutput, "src"));

    [RelayCommand]
    private void OpenReport() => Shell.OpenFile(Path.Combine(LastOutput, "recovery-report.tsv"));

    [RelayCommand]
    private async Task CopyLog()
    {
        if (!Shell.CopyText(string.Join(Environment.NewLine, Lines.Select(l => l.Text)))) return;
        LogCopied = true;
        await Task.Delay(1600);
        LogCopied = false;
    }

    [RelayCommand]
    private void ClearLog()
    {
        if (!IsRunning) Lines.Clear();
    }

    private static string Duration(TimeSpan t) =>
        t.TotalHours >= 1 ? $"{(int)t.TotalHours} h {t.Minutes} min"
        : t.TotalMinutes >= 1 ? $"{(int)t.TotalMinutes} min {t.Seconds} s"
        : $"{t.Seconds} s";
}
