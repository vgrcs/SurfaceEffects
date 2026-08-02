# SurfaceEffects Mechanization Report

This report records the current public proof surface.

The paper-facing theorem facade re-exports the curated active `SmallStep`
theorem surface:

```text
theories/PaperTheorems.v
```

That file re-exports `theories/SmallStep/Public.v`. The detailed proof
libraries remain importable directly from `theories/SmallStep`. The syntax is
`Expr`, which includes `EPairPar`; the checked typing and correctness surface
uses `CheckedTcExp` and `CheckedBackTriangle`.

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
2. `theories/SmallStep/Public.v`
3. `theories/SmallStep/Core/Syntax.v`
4. `theories/SmallStep/Typing/Judgments.v`
5. `theories/SmallStep/Runtime/Machine.v`
6. `theories/SmallStep/Runtime/PreservationPublic.v`
7. `theories/SmallStep/Soundness/Correctness.v`
8. `theories/SmallStep/Determinism/SchedulerPublic.v`

The old SmallStep proof tree has been removed. The public theorem facade is the
curated `SmallStep` stack exported through `PaperTheorems.v`; the BigStep
artifact remains available through the separate BigStep build.

## Public Theorem Map

Runtime safety:

- `Step_progress`
- `Runtime_step_store_preservation`
- `Runtime_steps_store_preservation`
- `Runtime_stepsN_store_preservation`
- `Runtime_steps_view_store_preservation`

Static-effect soundness:

- `SmallStep_static_effect_soundness`

Terminal determinism:

- `SmallStep_terminal_trace_deterministic`
- `SmallStep_terminal_deterministic`

Surface-effect correctness:

- `SmallStep_checked_terminal_correctness`

Pair-parallel dispatcher case:

- `SmallStep_pairpar_dispatcher_case`

Pair-parallel fallback and static branch facts:

- `SmallStep_pairpar_fallback_run`
- `SmallStep_pairpar_checked_reject_run`
- `SmallStep_pairpar_checked_pass_fallback_embeds_steps`
- `SmallStep_pairpar_precheck_rejection_falls_back_sequentially`
- `SmallStep_pairpar_checked_components_fallback`
- `SmallStep_pairpar_static_summary_noalloc`
- `SmallStep_pairpar_static_summary_readonly`

Checked pair-parallel scheduler determinism:

- `SmallStep_scheduler_checked_left_then_right_embeds`
- `SmallStep_scheduler_checked_nsteps_embeds`
- `SmallStep_scheduler_checked_success_join_deterministic`
- `SmallStep_scheduler_checked_success_continuation_deterministic`
- `SmallStep_scheduler_checked_error_classifies`
- `SmallStep_scheduler_checked_error_same_cause`
- `SmallStep_scheduler_checked_success_error_disjoint`
- `SmallStep_scheduler_checked_terminal_outcomes_deterministic`

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
