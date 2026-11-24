#!/usr/bin/env bash
#
# Publishes the rewind command for Linux x64 and, with UPLOAD=1, attaches it to the channel's release.
#
# The desktop app is WPF, so it is Windows-only; on Linux the command-line decompiler is the whole product.
# The version is computed the same way as installer/pack.ps1: <installer/version.txt>.<commits up to HEAD>.
#
#   CHANNEL   main or experimental. Default: main when HEAD is the main branch, experimental otherwise.
#   VERSION   A version to use instead of the computed one.
#   RID       The runtime to build for. Default: linux-x64.
#   OUTPUT    Where the archive goes. Default: artifacts/linux in the repository (ignored by git).
#   UPLOAD    1 to attach the archive to the existing GitHub release for the version (needs GITHUB_TOKEN).
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

channel="${CHANNEL:-}"
if [ -z "$channel" ]; then
    branch="$(git -C "$root" rev-parse --abbrev-ref HEAD)"
    if [ "$branch" = "main" ]; then channel="main"; else channel="experimental"; fi
fi
case "$channel" in
    main|experimental) ;;
    *) echo "The channel is main or experimental, not '$channel'." >&2; exit 1 ;;
esac

version="${VERSION:-}"
if [ -z "$version" ]; then
    base="$(tr -d '[:space:]' < "$root/installer/version.txt")"
    count="$(git -C "$root" rev-list --count HEAD)"
    version="$base.$count"
    if [ "$channel" = "experimental" ]; then version="$version-experimental"; fi
fi

rid="${RID:-linux-x64}"
out="${OUTPUT:-$root/artifacts/linux}"
publish="$out/publish-$rid"
rm -rf "$publish"
mkdir -p "$publish"

echo "Rewind $version, channel $channel, $rid"
"${DOTNET:-dotnet}" publish "$root/src/Rewind.Cli/Rewind.Cli.csproj" -c Release -r "$rid" --self-contained true \
    -o "$publish" "-p:Version=$version" --nologo

for file in rewind signatures licenses; do
    if [ ! -e "$publish/$file" ]; then
        echo "The published folder has no $file." >&2
        exit 1
    fi
done

archive="$out/Rewind-$channel-$rid.tar.gz"
tar -C "$publish" -czf "$archive" .
echo "Built $archive"

if [ "${UPLOAD:-0}" = "1" ]; then
    : "${GITHUB_TOKEN:?Uploading needs a GitHub token in GITHUB_TOKEN.}"
    repo="${GITHUB_REPOSITORY:-}"
    if [ -z "$repo" ]; then
        repo="$(git -C "$root" remote get-url origin | sed -E 's#.*github\.com[:/](.+)(\.git)?$#\1#')"
    fi
    GH_TOKEN="$GITHUB_TOKEN" gh release upload "v$version" "$archive" -R "$repo" --clobber
    echo "Attached $archive to v$version"
fi
