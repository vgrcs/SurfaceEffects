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
make
```

Expected result: `_CoqProject` compiles. Rocq 9 may emit non-blocking warnings
about notation prefixes and one non-recursive fixpoint.

## Active Source Layout

```text
theories/
  PaperTheorems.v
  Core/          syntax, actions, values, regions
  Runtime/       heap model and small-step continuation machine
  Typing/        types and typing judgments
  Meta/          reusable proof facts
  Soundness/     type/effect/correctness proofs
  Determinism/   terminal determinism proofs
  Archive/       inactive proof experiments
```

The paper-facing calculus is the active `NewSmallStep` development:

- `NewSmallStep/Core/Syntax.v`: `NExpr`, including `EPairPar`.
- `NewSmallStep/Typing/Judgments.v`: ordinary and checked typing judgments.
- `NewSmallStep/Runtime/Machine.v`: continuation-machine semantics.
- `NewSmallStep/Runtime/Trace.v`: finite executions and traces.
- `NewSmallStep/Runtime/Progress.v`: progress for well-typed states.
- `NewSmallStep/Runtime/RegularPreservation.v`: store-resolved preservation.
- `NewSmallStep/Soundness/BackTriangle.v`: checked surface-effect relation.
- `NewSmallStep/Soundness/Dispatcher.v`: static-effect soundness and terminal
  correctness dispatcher.
- `NewSmallStep/Determinism/Terminal.v`: terminal determinism.
- `PaperTheorems.v`: paper-facing theorem exports.

Older proof experiments remain in the repository for comparison and future
work, but the public theorem facade is the `NewSmallStep` stack exported through
`PaperTheorems.v`.

## Current Status

The active theorem stack proves:

- progress for the `NewSmallStep` continuation machine;
- store-resolved preservation for machine steps and finite executions;
- static-effect trace soundness;
- terminal trace determinism;
- terminal value/heap determinism;
- closed terminal surface-effect correctness;
- structured terminal correctness as a corollary of terminal trace correctness.

There are no source-level `Axiom` or `Admitted` declarations in `theories/`.

Current non-goals:

- terminal small-step/big-step adequacy;
- termination or cost bounds for surface-effect evaluation;
- surface-effect inference or synthesis;
- scheduler determinism for a nondeterministic/interleaving scheduler.

For the exact theorem names and build environment, see
[ARTIFACT.md](ARTIFACT.md).
