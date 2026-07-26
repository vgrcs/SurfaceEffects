# SurfaceEffects Mechanization Report

This report records the current public proof surface.

The paper-facing theorem facade re-exports the active `NewSmallStep`
development:

```text
theories/PaperTheorems.v
```

It exports the `NewSmallStep` syntax and theorem stack directly. The syntax is
`NExpr`, which now includes `EPairPar`; the checked typing and correctness
surface uses `NCheckedTcExp` and `NCheckedBackTriangle`.

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

The older proof experiments remain in the repository for comparison, but the
public theorem facade is the `NewSmallStep` stack exported through
`PaperTheorems.v`.

## Public Theorem Map

Runtime safety:

- `NStep_progress`
- `NStep_store_resolved_state_preservation`
- `NSteps_store_resolved_state_preservation`
- `NStepsN_store_resolved_state_preservation`

Static-effect soundness:

- `checked_store_computation_trace_soundness`

Terminal determinism:

- `NSteps_terminal_trace_deterministic`
- `NSteps_terminal_deterministic`

Surface-effect correctness:

- `checked_context_terminal_correctness_from_store_dispatch`
- `checked_context_structured_terminal_correctness_from_store_dispatch`

Pair-parallel dispatcher case:

- `EPairPar_checked_store_context_case_from_below`

## Current Boundary

The current public calculus contains:

- regions;
- mutable references;
- dynamic traces;
- executable surface effects;
- checked pair-parallel expressions;
- a continuation-machine small-step semantics;
- static-effect trace soundness;
- terminal determinism;
- closed terminal surface-effect correctness.

Current non-goals:

- terminal small-step/big-step adequacy;
- termination or cost bounds for surface-effect evaluation;
- surface-effect inference or synthesis;
- scheduler determinism for a nondeterministic/interleaving scheduler.

## Paper Notes

The paper should state the public theorems in mathematical notation rather than
using Coq theorem names in prose. The Coq names above are stable artifact-entry
points for reviewers.
