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

`PaperTheorems.v` re-exports the curated small-step surface from:

```text
theories/SmallStep/Public.v
```

Exports include:

- the `SmallStep` syntax `Expr`, including `EPairPar`;
- the ordinary and checked typing judgments, including `TcExp`,
  `CheckedTcExp`, and `CheckedBackTriangle`;
- progress, preservation, static-effect soundness, terminal determinism,
  terminal surface-effect correctness, and pair-parallel fallback facts;
- checked pair-parallel scheduler determinism through
  `theories/SmallStep/Determinism/SchedulerPublic.v`.

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
make build-smallstep
make build-bigstep
```

Equivalently:

```sh
make -C theories/SmallStep
make -C theories/BigStep
```

Expected result:

- the SmallStep and BigStep project files compile.

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
2. `theories/SmallStep/Public.v`
3. `theories/SmallStep/Core/Syntax.v`
4. `theories/SmallStep/Typing/Judgments.v`
5. `theories/SmallStep/Runtime/Machine.v`
6. `theories/SmallStep/Runtime/PreservationPublic.v`
7. `theories/SmallStep/Soundness/Correctness.v`
8. `theories/SmallStep/Determinism/SchedulerPublic.v`

Details: `REPORT.md`.

## Theorem Map

The paper uses mathematical theorem statements.

Main mechanized names:

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

Exported by:

```text
theories/PaperTheorems.v
```

## Source Navigation

Use `README.md` for the compact source-layout overview.
Use `REPORT.md` for the detailed proof narrative.

For artifact checking, the shortest path is still the review path above:

1. public facade;
2. curated small-step theorem facade;
3. `SmallStep` syntax and checked typing;
4. continuation machine, progress, and preservation facade;
5. static-effect soundness and dispatcher terminal correctness;
6. checked pair-parallel scheduler determinism.

## Scope

This artifact proves the small-step continuation-machine and checked
pair-parallel scheduler results listed in the theorem map.

It does not prove:

- terminal small-step/big-step adequacy;
- equivalence with a separate sequential pair constructor;
- termination or cost bounds for surface-effect evaluation;
- surface-effect inference or synthesis.

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
