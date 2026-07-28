# SurfaceEffects Mechanization Report

This report records the current public proof surface.

The paper-facing theorem facade re-exports the active `SmallStep`
development:

```text
theories/PaperTheorems.v
```

It exports the `SmallStep` syntax and theorem stack directly. The syntax is
`NExpr`, which now includes `EPairPar`; the checked typing and correctness
surface uses `NCheckedTcExp` and `NCheckedBackTriangle`.

## Build And Trust Status

Current local toolchain:

```text
The Rocq Prover, version 9.1.1
compiled with OCaml 4.14.2
```

Verification commands:

```sh
make build-smallstep
make build-bigstep
make -C theories/SmallStep
make -C theories/BigStep
```

Current trust status:

- no `Admitted` declarations in `theories/`;
- no source-level `Axiom` declarations in `theories/`;
- known Rocq 9 notation-prefix and non-recursive-fixpoint warnings remain
  non-blocking.

## Public Source Path

Read these files first:

1. `theories/PaperTheorems.v`
2. `theories/SmallStep/Core/Syntax.v`
3. `theories/SmallStep/Typing/Judgments.v`
4. `theories/SmallStep/Runtime/Machine.v`
5. `theories/SmallStep/Soundness/Correctness.v`
6. `theories/SmallStep/Determinism/Terminal.v`

The old SmallStep proof tree has been removed. The public theorem facade is the
current `SmallStep` stack exported through `PaperTheorems.v`; the BigStep
artifact remains available through the separate BigStep build.

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

Checked pair-parallel scheduler determinism:

- `NScheduledPairParRun_checked_pairpar_left_then_right_embeds`
- `NScheduledPairParRun_checked_pairpar_success_join_deterministic`
- `NScheduledPairParRun_checked_pairpar_success_continuation_deterministic`
- `NScheduledPairParRun_checked_pairpar_error_classifies`
- `NScheduledPairParRun_checked_pairpar_error_same_cause`
- `NScheduledPairParRun_checked_pairpar_terminal_outcomes_deterministic`

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
- checked scheduler determinism for pair-parallel run phases;
- closed terminal surface-effect correctness.

Current non-goals:

- terminal small-step/big-step adequacy;
- termination or cost bounds for surface-effect evaluation;
- surface-effect inference or synthesis.

## Paper Notes

The paper should state the public theorems in mathematical notation rather than
using Coq theorem names in prose. The Coq names above are stable artifact-entry
points for reviewers.
