# SurfaceEffects Artifact Guide

This file is the reviewer-facing guide for checking the mechanized results.
It avoids the long proof narrative in `REPORT.md` and focuses on how to build
the artifact and where the paper theorems live.

## Entry Point

Start here:

```text
theories/PaperTheorems.v
```

This facade exports:

- runtime safety and determinism wrappers from
  `theories/Runtime/SmallStepPaperTheorems.v`;
- structured surface-correctness from
  `theories/Soundness/SmallStepPaperSoundness.v`.

## Known-Good Toolchain

Checked locally with:

```text
The Rocq Prover, version 9.1.1
compiled with OCaml 4.14.2
```

Known-good opam switch:

```text
switch                surfaceeffects
ocaml-base-compiler   4.14.2
coq                   9.1.1
coq-core              9.1.1
rocq-core             9.1.1
rocq-runtime          9.1.1
rocq-stdlib           9.0.0
coq-stdlib            9.0.0
coq-stdpp             1.12.0
dune                  3.23.1
zarith                1.14
```

Fresh-switch setup:

```sh
opam switch create surfaceeffects ocaml-base-compiler.4.14.2
eval $(opam env --switch=surfaceeffects)
opam install coq.9.1.1 coq-stdpp.1.12.0
```

Then check:

```sh
rocq --version
coqc --version
```

Both should report Rocq 9.1.1.

## Build

From the repository root:

```sh
eval $(opam env --switch=surfaceeffects)
make
```

Expected result: `_CoqProject` compiles.

Expected warnings:

- old `From Coq` imports are deprecated in Rocq 9;
- a few notation prefixes are reported as incompatible.

These warnings do not block the build.

To rebuild the paper:

```sh
cd paper
pdflatex -interaction=nonstopmode -halt-on-error main_revised.tex
pdflatex -interaction=nonstopmode -halt-on-error main_revised.tex
```

Generated Rocq, LaTeX, and make-dependency files are ignored by `.gitignore`
when they are not already tracked.

## Review Path

Recommended reading order:

1. `theories/PaperTheorems.v`
2. `theories/Runtime/SmallStepPaperTheorems.v`
3. `theories/Soundness/SmallStepPaperSoundness.v`
4. `theories/Runtime/SmallStepStructuredTrace.v`
5. `theories/Soundness/SmallStepCorrectnessPairPar.v`

For the full proof-development story, use `REPORT.md`.

## Theorem Map

The paper uses mathematical theorem statements. These are the corresponding
mechanized names.

Runtime safety:

- `PaperSmallStepFinitePrefixSafety`
- `PaperSmallStepTerminalSoundness`

Checked `Pair_Par` safety:

- `PaperPairParCheckedOrBlockedTraceSafety`
- `PaperPairParCheckedOrBlockedTerminalSoundness`
- `PaperPairParCheckedPackedTerminalSoundness`

Scheduled terminal trace soundness:

- `PaperScheduledSmallStepTerminalTraceSoundness`
- `PaperScheduledExpressionTerminalTraceSoundness`

Scheduler independence:

- `PaperScheduledSmallStepTerminalDeterminism`
- `PaperScheduledExpressionTerminalDeterminism`

Surface-effect correctness:

- `PaperPairParCheckedStructuredTerminalCorrectness`

All of these are exported by `theories/PaperTheorems.v`.

Value-only scheduled wrappers also exist in
`theories/Runtime/SmallStepPaperTheorems.v`. They are support lemmas; the public
artifact map uses the trace-strengthened scheduled statements above.

## Source Navigation

- `Runtime/SmallStep.v`: continuation-machine semantics.
- `Runtime/SmallStepPairParDispatch.v`: staged dynamic check for `Pair_Par`.
- `Runtime/SmallStepStructuredTrace.v`: structured traces and scheduled runs.
- `Runtime/SmallStepPaperTheorems.v`: runtime paper wrappers.
- `Soundness/SmallStepBackTriangle.v`: small-step summary relation.
- `Soundness/SmallStepCorrectnessBase.v`: base terminal-run utilities.
- `Soundness/SmallStepCorrectnessApps.v`: application correctness.
- `Soundness/SmallStepCorrectnessPairPar.v`: checked `Pair_Par` correctness.
- `Soundness/SmallStepPaperSoundness.v`: surface-correctness wrapper.

## Scope

The artifact proves the small-step continuation-machine results listed above.

It does not currently prove:

- terminal small-step/big-step adequacy;
- equivalence with a separate sequential tuple constructor;
- termination or cost bounds for summary evaluation;
- summary inference or synthesis.

The old matched-trace bridge to the terminating evaluator is archived under
`theories/Archive/`. It is not part of `_CoqProject`.

## Git Hygiene

Normal review status:

```sh
git status --short
```

Ignored build products:

```sh
git status --short --ignored
```

The `.gitignore` file excludes Rocq objects, LaTeX byproducts, make dependency
files, and local scratch exports.
