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

- the `SmallStep` syntax `Expr`, including `EPairPar`;
- the ordinary and checked typing judgments, including `TcExp`,
  `CheckedTcExp`, and `CheckedBackTriangle`;
- progress, preservation, static-effect soundness, terminal determinism, and
  terminal surface-effect correctness from `theories/SmallStep`;
- checked pair-parallel scheduler determinism from
  `theories/SmallStep/Determinism/Scheduler.v`.

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
2. `theories/SmallStep/Core/Syntax.v`
3. `theories/SmallStep/Typing/Judgments.v`
4. `theories/SmallStep/Runtime/Machine.v`
5. `theories/SmallStep/Soundness/Correctness.v`

Details: `REPORT.md`.

## Theorem Map

The paper uses mathematical theorem statements.

Main mechanized names:

Runtime safety:

- `Step_progress`
- `Step_store_resolved_state_preservation`
- `Steps_store_resolved_state_preservation`
- `StepsN_store_resolved_state_preservation`

Static-effect soundness:

- `checked_store_computation_trace_soundness`

Terminal determinism:

- `Steps_terminal_trace_deterministic`
- `Steps_terminal_deterministic`

Surface-effect correctness:

- `checked_context_terminal_correctness_from_store_dispatch`
- `checked_context_structured_terminal_correctness_from_store_dispatch`

Pair-parallel dispatcher case:

- `EPairPar_checked_store_context_case_from_below`

Pair-parallel fallback relation:

- `PairParFallbackRun`
- `PairParFallbackRun_checked_pass_to_Steps`
- `PairParFallbackRun_check_fail_sequential`
- `PairParFallbackRun_from_component_evaluations`
- `PairParFallbackRun_checked_components`

Checked pair-parallel scheduler determinism:

- `ScheduledPairParRun_checked_pairpar_left_then_right_embeds`
- `ScheduledPairParRun_checked_pairpar_success_join_deterministic`
- `ScheduledPairParRun_checked_pairpar_success_continuation_deterministic`
- `ScheduledPairParRun_checked_pairpar_error_classifies`
- `ScheduledPairParRun_checked_pairpar_error_same_cause`
- `ScheduledPairParRun_checked_pairpar_terminal_outcomes_deterministic`

Exported by:

```text
theories/PaperTheorems.v
```

## Source Navigation

Use `README.md` for the compact source-layout overview.
Use `REPORT.md` for the detailed proof narrative.

For artifact checking, the shortest path is still the review path above:

1. public facade;
2. `SmallStep` syntax and checked typing;
3. continuation machine, progress, and preservation;
4. static-effect soundness and dispatcher terminal correctness;
5. checked pair-parallel scheduler determinism.

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
