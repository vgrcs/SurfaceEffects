# SurfaceEffects

SurfaceEffects is a Rocq mechanization of a language with regions, mutable
references, dynamic traces, and executable effect summaries.

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

The paper-facing ordinary calculus is the checked-pair-free `NewSmallStep`
development:

- `NewSmallStep/Core/Syntax.v`: `NExpr`, with no checked-pair constructor.
- `NewSmallStep/Typing/Judgments.v`: `NTcExp`, with no checked-pair rule.
- `NewSmallStep/Runtime/Machine.v`: continuation-machine semantics.
- `NewSmallStep/Runtime/Trace.v`: finite executions and traces.
- `NewSmallStep/Runtime/Progress.v`: progress for well-typed states.
- `NewSmallStep/Runtime/Preservation.v`: preservation lemmas.
- `NewSmallStep/Soundness/BackTriangle.v`: ordinary summary relation.
- `NewSmallStep/Soundness/Correctness.v`: terminal correctness shape.
- `NewSmallStep/Determinism/Terminal.v`: terminal determinism.
- `PaperTheorems.v`: paper-facing theorem wrappers.

Older checked-pair files remain in the repository for comparison and future
experiments, but they are not exported by the public theorem facade.

## Current Status

The active theorem stack proves:

- progress for the checked-pair-free ordinary small-step machine;
- preservation for evaluation and return steps;
- terminal trace determinism;
- terminal value/heap determinism;
- terminal surface-effect correctness from the counted-run induction package;
- structured terminal correctness as a corollary of raw trace correctness.

There are no source-level `Axiom` or `Admitted` declarations in `theories/`.

Current non-goals:

- terminal small-step/big-step adequacy;
- termination or cost bounds for summary evaluation;
- summary inference or synthesis.

For the exact theorem names and build environment, see
[ARTIFACT.md](ARTIFACT.md).
