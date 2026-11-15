# Rewind — Unity IL2CPP decompiler

Rewind takes a Unity game built with IL2CPP and rebuilds what the build threw away: .NET assemblies with
real method bodies, and C# source.

It handles **standard-format IL2CPP only**. If a game's metadata is encrypted or otherwise non-standard,
Rewind says so and stops; it contains no decryption, dumping or anti-cheat features.

## Usage

```
dotnet build Rewind.slnx -c Release

rewind info <input>                      what the input is, Unity version, assemblies
rewind dump <input> -o <dir>             dump.cs: every type and member with addresses and offsets
rewind decompile <input> -o <dir>        rebuilt assemblies + C# source
        --assembly <name>                only this assembly (repeatable)
        --no-source                      assemblies only
        --signatures <file|dir>          signature library to use (default: ./signatures)
```

`<input>` is a game folder, the game's `.exe`, an APK / XAPK / APKS / AAB, an IPA, or the IL2CPP binary
itself. The CLI is `src/Rewind.Cli/bin/Release/net10.0/rewind.dll` (run with `dotnet`).

`decompile` writes:

| Path | Content |
| --- | --- |
| `assemblies/` | One .NET assembly per original assembly: all types, members, attributes, and recovered IL bodies |
| `src/<Assembly>/` | C# source, one file per top-level type |
| `recovery-report.tsv` | Every method that is not a complete recovery, with the reason |

A method the recovery could not express completely is never silently wrong on purpose: the missing piece
appears in the code as a call to `__Rewind.Opaque<T>("…")` / `__Rewind.Effect("…")`, and the method starts
with `__Rewind.Note("…")` listing what is missing.

## How it works

1. **Read** the binary (PE, ELF, Mach-O) and `global-metadata.dat` (layouts v24–v39), and locate the
   registration tables by structure, not by symbol.
2. **Rebuild** the type system as real assemblies (Mono.Cecil).
3. **Identify the runtime's support functions** without symbols, using a signature library: position-
   independent fingerprints (deepened through callees only as far as needed to be unique), the binary's own
   exported API names, a similarity sketch for slightly different builds, and jump-thunk propagation.
4. **Lift** each method's x64 machine code to SSA, **normalize** away what IL2CPP added (metadata and class
   initialization, write barriers, null/bounds/cast checks that IL performs implicitly), and undo compiler
   work on loops (64-bit copies of 32-bit variables, duplicated counters, pointer walks over arrays).
5. **Translate** to typed managed operations (fields, array elements, calls, allocations) against the type
   model, choosing among methods that share one compiled body by argument and receiver types.
6. **Emit IL** into the rebuilt assemblies and let ICSharpCode.Decompiler structure it into C#.

## What is verified, and how

Everything is measured against games we build ourselves (the corpus game, kept outside this repository), where the original C#,
IL, generated C++ and symbols are known.

| Check | Result |
| --- | --- |
| Method addresses vs. symbols | 39,257/39,257 (Windows x64, v39), 34,680/34,680 (Android ARM64, v39), 10,229/10,229 (Android, v31.1) |
| Rebuilt assemblies vs. originals | identical type/field/method tokens and signatures; 43,141/43,141 overrides; 133,358/133,358 attributes |
| Support-function identification | 0 wrong identifications in 5 build configurations, including 2 the library was not built from |
| Behaviour of recovered code | 145 of 187 comparable corpus methods behave identically to the original on up to 60 inputs each |

The behaviour check (`rewind-lab diff-exec`) loads the original assembly and the rebuilt one side by side
and calls the same static methods with the same inputs, comparing results, exceptions and argument changes.

## Current limits

- Method bodies are recovered for **x64 Windows** code. ARM64 (most APKs) gets complete types and
  signatures, with placeholder bodies.
- Methods of generic types and generic methods keep placeholder bodies.
- `try`/`catch`/`finally` regions are not reconstructed yet; such methods are flagged.
- Struct values copied in 8- or 16-byte pieces and structs kept on the stack are often not resolved to their
  fields yet; this is the most common kind of marked gap in real games.
- Inlined callees are not folded back in general (plain field accessors and trivial constructors are); other
  code inlined from another class shows that class's private members directly.
- One signature library ships: Unity 6000.3.12f1, Windows x64 (five build configurations). Other versions
  need a library built from a build of yours that has symbols (below); without one, bodies are mostly gaps.
- Metadata layouts other than v39 and v31.1 are implemented from the format's history but untested.
  Unity 6.5+ (v104+) is not supported. Mach-O input is untested.
- Choices among candidates use rules; the learned ranking model is not integrated yet.

## Adding a signature library for another Unity version

Build any IL2CPP player with that editor (keep the `*_BackUpThisFolder_ButDontShipItWithYourGame` folder),
then:

```
python pdbsyms.py <backup>/GameAssembly.pdb symbols.tsv
rewind-lab sig-build signatures/unity-<version>-windows-x64.sig <build folder> symbols.tsv [<build2> <symbols2> ...]
```

Several build configurations of the same version can go into one library; more configurations mean more
games of that version are recognized exactly.

## Layout

| Path | Content |
| --- | --- |
| `src/Rewind.Core` | binary and metadata readers, type model |
| `src/Rewind.Analysis` | lifter, IR, normalization, recovery to typed operations, signature matching |
| `src/Rewind.Output` | assembly rebuilding, IL emission, C# output, `dump.cs` |
| `src/Rewind.Cli` | the `rewind` command |
| `src/Rewind.Lab` | measurement commands used during development (`hir-stats`, `diff-exec`, `sig-apply`, …) |
| `signatures/` | signature libraries |
| (sibling folder `IL2CPP Decompiler tools n stuff`) | not source: the corpus game and its ground truth, reference game, outputs, helper scripts (`tools/pdbsyms.py`, `tools/measure.sh`) |
| (sibling folder `IL2CPP Neural Model`) | the learned function-identification model: training code, exported data, runs |

## License

Rewind is licensed under the [Apache License 2.0](LICENSE). You are free to use, fork and modify it; if you
redistribute it or a modified version, keep the [NOTICE](NOTICE) file, which credits the original project,
and mark the files you changed.
