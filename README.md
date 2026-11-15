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

Run it from the repo folder so it finds the signature library in `signatures/`, or point at the library with
`--signatures`.

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
| `--identifications <file>` | answers from the separate function identification model, which isn't part of this repo |
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
| Behavior of recovered code | 145 of 187 comparable test methods behave exactly like the original on up to 60 inputs each |

The behavior check is `rewind-lab diff-exec`. It loads the original assembly and the rebuilt one side by side,
calls the same static methods with the same inputs, and compares the results, any exceptions and any changes
to the arguments.

## What it can't do yet

- Method bodies are only recovered for x64 Windows builds. ARM64, which covers most Android games, gets
  complete types and signatures but placeholder bodies.
- Generic methods, and methods of generic types, still get placeholder bodies.
- `try`/`catch`/`finally` blocks aren't rebuilt yet. Methods that use them are flagged.
- Structs copied in 8- or 16-byte pieces, and structs kept on the stack, often aren't resolved to their
  fields yet. In real games this is the most common kind of gap.
- Inlined code mostly isn't folded back into a call. Simple field accessors and trivial constructors are, but
  other code that was inlined from another class uses that class's private members directly.
- Only one signature library comes with Rewind: Unity 6000.3.12f1 on Windows x64, covering five build
  configurations. Other Unity versions need a library you build yourself (see below). Without one, most
  method bodies come out as gaps.
- Metadata versions other than 39 and 31.1 are written from the format's history but haven't been tested.
  Unity 6.5 and later (metadata v104 and up) isn't supported. Mach-O input hasn't been tested either.
- When more than one candidate fits, Rewind chooses with hand-written rules. A learned ranking model isn't
  hooked up yet.

## Supporting another Unity version

Rewind needs a signature library for the Unity version a game was built with. To make one:

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
