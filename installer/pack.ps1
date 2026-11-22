<#
.SYNOPSIS
  Builds Rewind's installer: the desktop app and the rewind command in one package that keeps itself up to date.

.DESCRIPTION
  Publishes src/Rewind.Cli (rewind.exe, with the signature libraries) and src/Rewind.Gui (Rewind.Gui.exe) for
  win-x64 into one folder, self-contained so no .NET install is needed, and packs that folder with Velopack's vpk:

    Rewind-<channel>-Setup.exe      the installer: installs both, adds a Start menu and desktop shortcut, and puts
                                    rewind on the user's PATH
    Rewind-<channel>-Portable.zip   the same, without installing
    releases.<channel>.json, *.nupkg   the update feed installed copies read

  The channel is the branch the build comes from: main or experimental. Installed copies update from their channel
  and can switch to the other one in Settings.

  The version is <installer/version.txt>.<number of commits up to HEAD>, with "-experimental" on that channel, so
  every push gives a higher version than the one before it on the same branch.

.PARAMETER Channel
  main or experimental. Default: main when HEAD is the main branch, experimental otherwise.

.PARAMETER Version
  A SemVer 2 version to use instead of the computed one.

.PARAMETER Output
  Where publish/ and releases-<channel>/ go. Default: artifacts/installer in the repository (ignored by git).

.PARAMETER Download
  First fetch the channel's newest release from GitHub, so that vpk can also make a small delta update.

.PARAMETER Upload
  Publish the result as a GitHub release of the repository (needs GITHUB_TOKEN). The release workflow
  (.github/workflows/release.yml) does this on every push to main or experimental.

.EXAMPLE
  powershell -ExecutionPolicy Bypass -File installer/pack.ps1
  Builds an installer for the current branch into artifacts/installer.
#>
param(
    [string] $Channel = '',
    [string] $Version = '',
    [string] $Output = '',
    [switch] $Download,
    [switch] $Upload
)

$ErrorActionPreference = 'Stop'
$root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
# Publish to the repository the build runs in: a fork's token can only write to the fork. GITHUB_REPOSITORY is set
# by Actions; outside CI, fall back to origin so a local build from a fork does not try to publish upstream.
$repo = if ($env:GITHUB_REPOSITORY) { $env:GITHUB_REPOSITORY } else {
    $origin = (git -C $root remote get-url origin 2>$null)
    if ($origin -match 'github\.com[:/](.+?)(?:\.git)?$') { $Matches[1] } else { 'ratman-bit/Rewind-IL2CPP-Decompiler' }
}
$repoUrl = "https://github.com/$repo"

function Run([string] $what, [scriptblock] $command) {
    Write-Host "== $what"
    & $command
    if ($LASTEXITCODE -ne 0) { throw "$what failed (exit code $LASTEXITCODE)" }
}

if (-not $Channel) {
    $branch = (git -C $root rev-parse --abbrev-ref HEAD).Trim()
    $Channel = if ($branch -eq 'main') { 'main' } else { 'experimental' }
}
if ($Channel -notin @('main', 'experimental')) { throw "The channel is main or experimental, not '$Channel'." }

if (-not $Version) {
    $base = (Get-Content (Join-Path $PSScriptRoot 'version.txt') -Raw).Trim()
    $count = (git -C $root rev-list --count HEAD).Trim()
    $Version = "$base.$count"
    if ($Channel -eq 'experimental') { $Version += '-experimental' }
}
if ($Version -notmatch '^\d+\.\d+\.\d+(-[0-9A-Za-z.-]+)?$') { throw "'$Version' is not a SemVer 2 version." }

if (-not $Output) { $Output = Join-Path $root 'artifacts\installer' }
$publish = Join-Path $Output 'publish'
$releases = Join-Path $Output "releases-$Channel"
New-Item -ItemType Directory -Force -Path $Output, $releases | Out-Null
if (Test-Path $publish) { Remove-Item $publish -Recurse -Force }

$vpk = (Get-Command vpk -ErrorAction SilentlyContinue).Source
if (-not $vpk) { $vpk = Join-Path $env:USERPROFILE '.dotnet\tools\vpk.exe' }
if (-not (Test-Path $vpk)) { throw 'vpk was not found. Install it with: dotnet tool install -g vpk --version 1.2.161' }

Write-Host "Rewind $Version, channel $Channel"

if ($Download) {
    Write-Host '== Fetching the newest release of the channel (for a delta update)'
    $arguments = @('download', 'github', '--repoUrl', $repoUrl, '--channel', $Channel, '--outputDir', $releases)
    if ($env:GITHUB_TOKEN) { $arguments += @('--token', $env:GITHUB_TOKEN) }
    if ($Channel -eq 'experimental') { $arguments += '--pre' }
    & $vpk @arguments
    if ($LASTEXITCODE -ne 0) { Write-Host 'No earlier release to make a delta from; the full package is enough.' }
}

# Both apps go into one folder; built with the same SDK, the runtime files they share are the same files.
foreach ($project in @('src\Rewind.Cli\Rewind.Cli.csproj', 'src\Rewind.Gui\Rewind.Gui.csproj')) {
    Run "Publishing $project" {
        dotnet publish (Join-Path $root $project) -c Release -r win-x64 --self-contained true -o $publish "-p:Version=$Version" --nologo
    }
}
foreach ($file in @('rewind.exe', 'Rewind.Gui.exe', 'signatures', 'licenses')) {
    if (-not (Test-Path (Join-Path $publish $file))) { throw "The published folder has no $file." }
}

# Release notes: the commits since the channel's previous release.
$tags = @(git -C $root tag --list 'v*' --sort=-v:refname | Where-Object { ($_ -like '*-experimental') -eq ($Channel -eq 'experimental') })
$range = if ($tags.Count -gt 0) { "$($tags[0])..HEAD" } else { 'HEAD' }
$log = if ($Channel -eq 'main') { git -C $root log --first-parent --format='- %s' -n 40 $range } else { git -C $root log --no-merges --format='- %s' -n 40 $range }
$notes = Join-Path $Output "notes-$Channel.md"
$heading = if ($Channel -eq 'main') { 'Built from main: work that passed the full test pass.' } else { 'Built from experimental: every change first, tested or not.' }
Set-Content -Path $notes -Encoding utf8 -Value (@($heading, '', 'Changes:', '') + @($log))

Run 'Packing with Velopack' {
    & $vpk pack --packId Rewind --packVersion $Version --packDir $publish --mainExe Rewind.Gui.exe `
        --packTitle Rewind --packAuthors ratman-bit --icon (Join-Path $root 'assets\rewind.ico') `
        --runtime win-x64 --channel $Channel --outputDir $releases --releaseNotes $notes
}

if ($Upload) {
    if (-not $env:GITHUB_TOKEN) { throw 'Uploading needs a GitHub token in GITHUB_TOKEN.' }
    # Both branches publish normal releases (a pre-release never shows as the repository's latest release).
    $arguments = @('upload', 'github', '--repoUrl', $repoUrl, '--token', $env:GITHUB_TOKEN, '--channel', $Channel,
        '--outputDir', $releases, '--publish', '--releaseName', "Rewind $Version", '--tag', "v$Version",
        '--targetCommitish', (git -C $root rev-parse HEAD).Trim())
    Run 'Publishing the GitHub release' { & $vpk @arguments }

    # A new release becomes the "Latest release". Once main has one, that badge stays on main's newest build.
    $env:GH_TOKEN = $env:GITHUB_TOKEN
    $mainTags = @(gh release list -R $repo --limit 100 --json tagName --jq '.[].tagName' | Where-Object { $_ -notlike '*-experimental' })
    if ($mainTags.Count -gt 0) {
        $newestMain = $mainTags | Sort-Object { [version]($_.TrimStart('v')) } -Descending | Select-Object -First 1
        Run "Marking $newestMain as the latest release" { gh release edit $newestMain -R $repo --latest }
    }
}

Write-Host "Done: $(Join-Path $releases "Rewind-$Channel-Setup.exe")"
