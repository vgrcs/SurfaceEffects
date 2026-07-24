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

- the checked-pair-free ordinary syntax `NExpr`;
- the checked-pair-free ordinary typing judgment `NTcExp`;
- progress, preservation, terminal determinism, and terminal correctness
  wrappers from `theories/NewSmallStep/PaperTheorems.v`.

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

- a few notation prefixes are reported as incompatible;
- one fixpoint is reported as not truly recursive.

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

Paper source split:

- `main_revised.tex`: main narrative and theorem statements;
- `operational_semantics.tex`: paper-facing continuation-machine rules.

## Review Path

Read in this order:

1. `theories/PaperTheorems.v`
2. `theories/NewSmallStep/PaperTheorems.v`
3. `theories/NewSmallStep/Core/Syntax.v`
4. `theories/NewSmallStep/Typing/Judgments.v`
5. `theories/NewSmallStep/Runtime/Machine.v`
6. `theories/NewSmallStep/Soundness/Correctness.v`

Details: `REPORT.md`.

## Theorem Map

The paper uses mathematical theorem statements.

Main mechanized names:

Ordinary small-step safety:

- `PaperOrdinarySmallStepProgress`
- `PaperOrdinarySmallStepEvalPreservation`
- `PaperOrdinarySmallStepReturnPreservation`

Terminal determinism:

- `PaperOrdinarySmallStepTerminalTraceDeterminism`
- `PaperOrdinarySmallStepTerminalDeterminism`

Surface-effect correctness:

- `PaperOrdinarySurfaceEffectCorrectnessFromBelow`
- `PaperOrdinaryStructuredSurfaceEffectCorrectnessFromBelow`

All of these quantify over the ordinary `NExpr` language. Since `NExpr` has no
checked-pair constructor, the public theorem map excludes checked pairs by
construction.

Exported by:

```text
theories/PaperTheorems.v
```

The older checked-pair wrappers are not exported by the public facade.

## Source Navigation

Use `README.md` for the compact source-layout overview.
Use `REPORT.md` for the detailed proof narrative.

For artifact checking, the shortest path is still the review path above:

1. public facade;
2. checked-pair-free syntax and typing;
3. ordinary machine;
4. terminal correctness and determinism wrappers.

## Scope

This artifact proves the small-step continuation-machine results listed in the
theorem map.

It does not prove:

- terminal small-step/big-step adequacy;
- equivalence with a separate sequential pair constructor;
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
