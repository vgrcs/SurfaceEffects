# SurfaceEffects Artifact Guide

Purpose:

- build the artifact;
- find the public theorem statements;
- check the paper-to-Rocq theorem map.

For the long proof narrative, use `REPORT.md`.

## Entry Point

Public facade:

```text
theories/PaperTheorems.v
```

Exports:

- runtime safety and determinism wrappers from
  `theories/Runtime/SmallStepPaperTheorems.v`;
- structured surface-correctness from
  `theories/Soundness/SmallStepPaperSoundness.v`.

## Known-Good Toolchain

Version checked locally:

```text
The Rocq Prover, version 9.1.1
compiled with OCaml 4.14.2
```

Known-good opam packages:

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

Fresh switch:

```sh
opam switch create surfaceeffects ocaml-base-compiler.4.14.2
eval $(opam env --switch=surfaceeffects)
opam install coq.9.1.1 coq-stdpp.1.12.0
```

Version check:

```sh
rocq --version
coqc --version
```

Expected result: both commands report Rocq 9.1.1.

## Build

Project build:

```sh
eval $(opam env --switch=surfaceeffects)
make
```

Expected result:

- `_CoqProject` compiles.

Expected warnings:

- old `From Coq` imports are deprecated in Rocq 9;
- a few notation prefixes are reported as incompatible.

These warnings are non-blocking.

Paper build:

```sh
cd paper
pdflatex -interaction=nonstopmode -halt-on-error main_revised.tex
pdflatex -interaction=nonstopmode -halt-on-error main_revised.tex
```

Generated files:

- Rocq objects;
- LaTeX byproducts;
- make dependencies.

These are ignored by `.gitignore` when they are not already tracked.

## Review Path

Read in this order:

1. `theories/PaperTheorems.v`
2. `theories/Runtime/SmallStepPaperTheorems.v`
3. `theories/Soundness/SmallStepPaperSoundness.v`
4. `theories/Runtime/SmallStepStructuredTrace.v`
5. `theories/Soundness/SmallStepCorrectnessPairPar.v`

Details: `REPORT.md`.

## Theorem Map

The paper uses mathematical theorem statements.

Mechanized names:

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

Exported by:

```text
theories/PaperTheorems.v
```

Support-only wrappers:

- value-only scheduled wrappers in
  `theories/Runtime/SmallStepPaperTheorems.v`.

Public map:

- the trace-strengthened scheduled statements above.

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

Proved:

- the small-step continuation-machine results listed above.

Not proved:

- terminal small-step/big-step adequacy;
- equivalence with a separate sequential tuple constructor;
- termination or cost bounds for summary evaluation;
- summary inference or synthesis.

Archived:

- old matched-trace bridge to the terminating evaluator;
- location: `theories/Archive/`;
- not part of `_CoqProject`.

## Git Hygiene

Review status:

```sh
git status --short
```

Ignored files:

```sh
git status --short --ignored
```

Ignored categories:

- Rocq objects;
- LaTeX byproducts;
- make dependency files;
- local scratch exports.
