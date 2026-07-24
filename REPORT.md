# SurfaceEffects Mechanization Report

This report records the current public proof surface.

The paper-facing theorem facade is checked-pair-free:

```text
theories/PaperTheorems.v
```

It exports the ordinary `NewSmallStep` syntax and theorem wrappers directly.
The ordinary syntax is `NExpr`, and the ordinary typing judgment is `NTcExp`.
Neither inductive definition contains a checked-pair constructor/rule.

## Build And Trust Status

Current local toolchain:

```text
The Rocq Prover, version 9.1.1
compiled with OCaml 4.14.2
```

Verification command:

```sh
make
```

Current trust status:

- no `Admitted` declarations in `theories/`;
- no source-level `Axiom` declarations in `theories/`;
- `Definitions/Axioms.v` is no longer part of `_CoqProject`;
- known Rocq 9 notation-prefix and non-recursive-fixpoint warnings remain
  non-blocking.

## Public Source Path

Read these files first:

1. `theories/PaperTheorems.v`
2. `theories/NewSmallStep/Core/Syntax.v`
3. `theories/NewSmallStep/Typing/Judgments.v`
4. `theories/NewSmallStep/Runtime/Machine.v`
5. `theories/NewSmallStep/Soundness/Correctness.v`
6. `theories/NewSmallStep/Determinism/Terminal.v`

The older experimental checked-pair files remain in the repository for
comparison, but they are not exported by the public theorem facade.

## Public Theorem Map

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

All theorem statements quantify over `NExpr` states/evaluations. Since `NExpr`
has no checked-pair constructor, these statements exclude checked pairs by
construction.

## Current Boundary

The current public calculus contains:

- regions;
- mutable references;
- dynamic traces;
- executable surface-effect summaries;
- a continuation-machine small-step semantics;
- terminal determinism;
- terminal surface-effect correctness from the counted-run induction package.

Current non-goals:

- terminal small-step/big-step adequacy;
- termination or cost bounds for summary evaluation;
- summary inference or synthesis;
- any public theorem whose ordinary syntax includes checked pairs.

## Paper Notes

The paper should state the public theorems in mathematical notation rather than
using Coq theorem names in prose. The Coq names above are stable artifact-entry
points for reviewers.
