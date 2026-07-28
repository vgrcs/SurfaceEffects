# SurfaceEffects

SurfaceEffects is a Rocq mechanization of a language with regions, mutable
references, dynamic traces, and executable surface effects.

The current paper-facing semantics is a small-step continuation machine. The
public theorem facade is:

```text
theories/PaperTheorems.v
```

## Where To Look

- [ARTIFACT.md](ARTIFACT.md): reproducibility instructions, theorem map, and
  artifact-review path.
- [REPORT.md](REPORT.md): detailed proof status and engineering notes.
- [paper/main_revised.tex](paper/main_revised.tex): current paper draft.
- [paper/operational_semantics.tex](paper/operational_semantics.tex):
  paper-facing continuation-machine rules.
- [theories/PaperTheorems.v](theories/PaperTheorems.v): public theorem exports.

## Quick Build

Known-good local toolchain:

```text
The Rocq Prover, version 9.1.1
compiled with OCaml 4.14.2
```

Build from the repository root:

```sh
opam switch surfaceeffects
eval $(opam env)
rocq --version
make build-smallstep
make build-bigstep
```

Equivalent per-semantics wrappers are available:

```sh
make -C theories/SmallStep
make -C theories/BigStep
```

Expected result: the active SmallStep build and the separate BigStep build both
compile. Rocq 9 may emit non-blocking warnings about notation prefixes and one
non-recursive fixpoint.

## Active Source Layout

```text
theories/
  PaperTheorems.v
  SmallStep/     active continuation-machine semantics and proofs
  BigStep/       terminating-evaluator calculus, runtime, meta facts, and theorem facade
```

The paper-facing calculus is the active `SmallStep` development:

- `SmallStep/Core/Syntax.v`: `NExpr`, including `EPairPar`.
- `SmallStep/Typing/Judgments.v`: ordinary and checked typing judgments.
- `SmallStep/Runtime/Machine.v`: continuation-machine semantics.
- `SmallStep/Runtime/Trace.v`: finite executions and traces.
- `SmallStep/Runtime/Progress.v`: progress for well-typed states.
- `SmallStep/Runtime/RegularPreservation.v`: store-resolved preservation.
- `SmallStep/Soundness/BackTriangle.v`: checked surface-effect relation.
- `SmallStep/Soundness/Dispatcher.v`: static-effect soundness and terminal
  correctness dispatcher.
- `SmallStep/Determinism/Terminal.v`: terminal determinism.
- `SmallStep/Determinism/Scheduler.v`: checked pair-parallel scheduler
  determinism.
- `PaperTheorems.v`: paper-facing theorem exports.

The old SmallStep proof tree has been removed. The public theorem facade is the
current `SmallStep` stack exported through `PaperTheorems.v`.

## Current Status

The active theorem stack proves:

- progress for the `SmallStep` continuation machine;
- store-resolved preservation for machine steps and finite executions;
- static-effect trace soundness;
- terminal trace determinism;
- terminal value/heap determinism;
- closed terminal surface-effect correctness;
- structured terminal correctness as a corollary of terminal trace correctness;
- checked pair-parallel scheduler determinism.

There are no source-level `Axiom` or `Admitted` declarations in `theories/`.

Current non-goals:

- terminal small-step/big-step adequacy;
- termination or cost bounds for surface-effect evaluation;
- surface-effect inference or synthesis.

For the exact theorem names and build environment, see
[ARTIFACT.md](ARTIFACT.md).
