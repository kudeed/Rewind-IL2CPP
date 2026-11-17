<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="assets/rewind-banner-dark.svg">
    <img alt="Rewind: Unity IL2CPP decompiler" src="assets/rewind-banner.svg" width="100%">
  </picture>
</p>

A decompiler for Unity games built with IL2CPP.

When Unity builds a game with IL2CPP, it converts the C# to C++, compiles that to native code, and throws the
original .NET assemblies away. All that ships is a native binary and a metadata file. Rewind works backwards
from those two files and gives you .NET assemblies with real method bodies, plus C# source you can read.

Plenty of tools can recover the types and method signatures. Rewind's goal is to recover what the methods
actually do as well.

## Before you start

Rewind only reads standard IL2CPP builds. If a game's metadata is encrypted or modified, or the game is
protected in some other way, Rewind tells you so and stops. It has no decryption, memory dumping or anti-cheat
bypass features, and that's on purpose.

## Building

You need the .NET 10 SDK.

```
dotnet build Rewind.slnx -c Release
```

The command-line tool ends up in `src/Rewind.Cli/bin/Release/net10.0/rewind.dll`, and you run it with
`dotnet`:

```
dotnet src/Rewind.Cli/bin/Release/net10.0/rewind.dll info path/to/game
```

Run it from the repo folder so it finds the signature libraries in `signatures/`, or point at a library or a
folder of them with `--signatures`.

## Using it

There are three commands:

```
rewind info <input>                   what the input is and whether Rewind can read it
rewind dump <input> [-o <dir>]        writes dump.cs: every type and member, with addresses and offsets
rewind decompile <input> [-o <dir>]   rebuilds the assemblies and writes C# source
```

`<input>` can be the game folder, the game's `.exe`, an APK, XAPK, APKS or AAB, an IPA, or the IL2CPP binary
itself (`GameAssembly.dll`, `libil2cpp.so` or `UnityFramework`). Rewind finds the metadata and the binary on
its own.

Options:

| Option | What it does |
| --- | --- |
| `-o`, `--out <dir>` | where to write the output (default `./rewind-out`) |
| `--assembly <name>` | only decompile this assembly; repeat it for more than one |
| `--no-source` | write the rebuilt assemblies only, skip the C# |
| `--csharp <version>` | write source for an older C# version, for example `9` for a Unity 2021.2+ project |
| `--state-machines` | show iterators and async methods as the classes the compiler made of them, instead of `yield return` and `await` |
| `--signatures <path>` | the signature file or folder to use for recognizing runtime functions |
| `--metadata <file>`, `--binary <file>` | use these files instead of searching for them |
| `--abi <name>` | which Android ABI to use from a package (`arm64-v8a`, `armeabi-v7a`, `x86_64`, `x86`) |
| `--unity <version>` | the Unity version, if Rewind can't work it out (for example `2022.3.33f1`) |
| `-v`, `--verbose` | print more progress details |

Running `rewind` with no arguments prints the same list.

## What you get

`decompile` writes:

| Path | What's in it |
| --- | --- |
| `assemblies/` | one .NET assembly per original assembly, with every type, member and attribute, and the method bodies Rewind recovered |
| `src/<Assembly>/` | C# source, one file per top-level type |
| `recovery-report.tsv` | every method that wasn't fully recovered, and the reason |

When Rewind can't fully work out part of a method, it doesn't guess. That part shows up as a call to
`__Rewind.Opaque<T>("...")` or `__Rewind.Effect("...")`, and the method starts with a `__Rewind.Note("...")`
that says what's missing. That way the gaps are easy to spot.

## How it works

Roughly, in order:

1. **Reading the files.** Rewind parses the native binary (PE, ELF or Mach-O) and `global-metadata.dat`
   (metadata versions 24 to 39). It finds IL2CPP's registration tables by their structure, because shipped
   builds have no symbols to look them up by.
2. **Rebuilding the types.** The whole type system is rebuilt as real .NET assemblies with Mono.Cecil.
3. **Recognizing runtime functions.** Game code calls into the IL2CPP runtime all the time, and none of those
   functions have names in a shipped build. Rewind identifies them with a signature library. It uses
   position-independent fingerprints (which follow calls into other functions only as far as needed to be
   unique), the binary's own exported API names, a similarity sketch for builds that differ slightly, and
   jump thunks.
4. **Lifting and cleaning up.** Each method's x64 machine code is lifted to SSA form. Then Rewind removes the
   things IL2CPP added that weren't in the C#: metadata and class initialization, write barriers, and the
   null, bounds and cast checks that IL does implicitly. It also undoes some of the compiler's work on loops,
   like 64-bit copies of 32-bit variables, duplicated counters and pointers walking over arrays.
5. **Translating.** What's left becomes typed managed operations (fields, array elements, calls, allocations)
   checked against the type model. When several methods share one compiled body, Rewind picks the right one
   from the argument and receiver types.
6. **Writing C#.** The result is emitted as IL into the rebuilt assemblies, and ICSharpCode.Decompiler turns
   it into C#.

## How well it works

All of these numbers come from test games built specifically for checking Rewind. With those, the original C#
source, the IL, the generated C++ and the debug symbols are all there to compare against.

| What was checked | Result |
| --- | --- |
| Method addresses against debug symbols | 39,257 of 39,257 (Windows x64, v39), 34,680 of 34,680 (Android ARM64, v39), 10,229 of 10,229 (Android, v31.1) |
| Rebuilt assemblies against the originals | identical type, field and method tokens and signatures; 43,141 of 43,141 overrides; 133,358 of 133,358 attributes |
| Runtime function identification | no wrong identifications in 5 build configurations, including 2 the library wasn't built from |
| Behavior of recovered code | 176 of 187 comparable test methods behave exactly like the original on up to 60 inputs each |

The behavior check is `rewind-lab diff-exec`. It loads the original assembly and the rebuilt one side by side,
calls the same static methods with the same inputs, and compares the results, any exceptions and any changes
to the arguments.

### Unity versions

One test project was built for Windows x64 with six Unity versions, and each Release build was decompiled
with the signature library for its version. A body counts as complete when all of it was recovered, with no
gap marked.

| Unity version | Metadata | Method addresses against debug symbols | Complete bodies, the project's own assembly | Complete bodies, whole game |
| --- | --- | --- | --- | --- |
| 2020.3.49f1 | v27.1 | 106,376 of 106,376 | 506 of 514 (98.4%) | 90,716 of 95,857 (94.6%) |
| 2021.3.45f2 | v31 | 117,312 of 117,312 | 502 of 514 (97.7%) | 99,038 of 105,241 (94.1%) |
| 2022.3.62f3 | v31.1 | 125,112 of 125,112 | 504 of 516 (97.7%) | 106,162 of 112,687 (94.2%) |
| 6000.0.85f2 | v31.1 | 136,870 of 136,870 | 502 of 514 (97.7%) | 116,200 of 123,449 (94.1%) |
| 6000.2.9f1 | v31.1 | 138,340 of 138,340 | 504 of 516 (97.7%) | 117,521 of 124,794 (94.2%) |
| 6000.3.12f1 | v39 | 146,603 of 146,603 | 504 of 516 (97.7%) | 124,606 of 132,027 (94.4%) |

The whole game includes Unity's and .NET's own class libraries, which is most of the code.

The libraries for 2020.3 to 6000.2 were each built from the project's Release build, Master build and
Release build without incremental garbage collection, and, from 2021.3 on, a Release build optimized for
size. One more configuration of each version was kept out of its library and used to check it against the
debug symbols (a Master build optimized for size; for 2020.3, a Master build without incremental garbage
collection). The 6000.3.12f1 library is an earlier one, built from another project, so both of this
project's builds were new to it. None of the six libraries made a wrong identification on a build it wasn't
built from.

Bodies in those held-out builds are a different matter: Master builds recover far fewer. 60.9% to 63.6% of
the whole game is complete in the five Master builds optimized for size, and 75.7% in the 2020.3 one.

The behavior check gives the same picture on every version. On 6000.3.12f1, 156 of the project's 179
comparable methods behave exactly like the original, and the other versions are within three methods of
that (155 to 159 of 178 or 179). The methods that differ are mostly the same ones on every version. Some
return objects that are never equal between two runs (iterators, delegates) and some run into the time
limit. The rest are real differences: exception handling, generic code, async methods and a few array and
string methods.

Without a library for its own version, a game is read with whichever other library recognizes most of its
runtime. Taking each game's own library away left 68.9% of the 2020.3.49f1 game complete instead of 94.6%,
90.9% instead of 94.1% for 2021.3.45f2 and 92.7% instead of 94.2% for 2022.3.62f3. For the three Unity 6
versions it made no difference beyond one method.

## What it can't do yet

- Method bodies are only recovered for x64 Windows builds. ARM64, which covers most Android games, gets
  complete types and signatures but placeholder bodies.
- Generic methods, and methods of generic types, still get placeholder bodies.
- `try`/`catch`/`finally` blocks aren't rebuilt yet. Methods that use them are flagged.
- Structs copied in 8- or 16-byte pieces, and structs kept on the stack, often aren't resolved to their
  fields yet. In real games this is the most common kind of gap.
- Inlined code mostly isn't folded back into a call. Simple field accessors and trivial constructors are, but
  other code that was inlined from another class uses that class's private members directly.
- Signature libraries come with Rewind for the six Unity versions in the table above, for Windows x64 only.
  A game built with another version is read with whichever library recognizes most of its runtime, and
  fewer bodies come out complete the further apart the versions are (the numbers are under the table). The
  best result needs a library built for the game's exact version (see below).
- A library used on another Unity version than its own can also get a function wrong. Each of the six
  libraries was tried on the other five versions' test games: 29 of the 30 pairings had no wrong
  identification, and one had a single wrong one (the 6000.3.12f1 library on the 2020.3.49f1 game).
- Builds made with the Master compiler configuration come out far worse than Release builds. Of the
  6000.2.9f1 test game's bodies, 62.3% are complete for a Master build, against 94.2% for a Release build
  and 91.7% for a Release build optimized for size.
- Code generated by Unity 2020.3 leaves a `finally` block by a number it keeps on the stack. In large
  methods with several `try` blocks Rewind often can't follow that, and those methods are marked as gaps.
- Metadata versions other than 27.1, 31, 31.1 and 39 are written from the format's history but haven't been
  tested. Unity 6.5 and later (metadata v104 and up) isn't supported. Mach-O input hasn't been tested either.

## Supporting another Unity version

Rewind works best with a signature library for the exact Unity version a game was built with. It comes with
libraries for 2020.3.49f1, 2021.3.45f2, 2022.3.62f3, 6000.0.85f2, 6000.2.9f1 and 6000.3.12f1 (Windows x64).
For any other version it tries every library it has, nearest version first, and uses the one that recognizes
the most kinds of runtime function. To make a library for another version:

1. Install that Unity version and build any project with IL2CPP for Windows x64. Keep the
   `<Game>_BackUpThisFolder_ButDontShipItWithYourGame` folder the build creates, because `GameAssembly.pdb`
   is in it.
2. Dump the PDB's public symbols to a `symbols.tsv`, one per line: the RVA in hex, `1` if it's a function or
   `0` if not, and the name, separated by tabs. (The script used for this, `pdbsyms.py`, isn't in this repo
   yet.)
3. Build the library:

```
rewind-lab sig-build signatures/unity-<version>-windows-x64.sig <build folder> symbols.tsv [<build2> <symbols2> ...]
```

You can put several build configurations of the same version into one library. The more you include, the
more games built with that version Rewind recognizes exactly.

`rewind-lab` is the development tool in `src/Rewind.Lab`. After building, it's at
`src/Rewind.Lab/bin/Release/net10.0/rewind-lab.dll`.

## What's in the repo

| Path | What's in it |
| --- | --- |
| `src/Rewind.Core` | binary and metadata readers, and the type model |
| `src/Rewind.Analysis` | the lifter, IR, cleanup passes, recovery to typed operations and signature matching |
| `src/Rewind.Output` | assembly rebuilding, IL emission, C# output and `dump.cs` |
| `src/Rewind.Cli` | the `rewind` command |
| `src/Rewind.Lab` | `rewind-lab`, commands for measuring things during development (`hir-stats`, `diff-exec`, `sig-apply` and more) |
| `signatures/` | signature libraries |
| `assets/` | the logo and banner, in light and dark versions (SVG and PNG), and the app icon |

The test games and their ground truth are kept separately and aren't included.

## License

Rewind is licensed under the [Apache License 2.0](LICENSE). You're free to use it, fork it and change it. If
you share it or a modified version, keep the [NOTICE](NOTICE) file so the original project gets credit, and
mark the files you changed.
