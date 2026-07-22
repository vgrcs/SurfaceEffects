# SurfaceEffects

SurfaceEffects is a Rocq mechanization of a language with regions, mutable
references, dynamic traces, executable effect summaries, and checked implicit
parallel pairs.

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

Expected result: `_CoqProject` compiles. Rocq 9 may emit compatibility warnings
about old `From Coq` imports and notation prefixes; these warnings do not block
the build.

## Active Source Layout

```text
theories/
  PaperTheorems.v
  Core/          syntax, actions, values, regions
  Runtime/       heap model and small-step continuation machine
  Typing/        types and typing judgments
  Meta/          reusable proof facts
  Soundness/     type/effect/correctness proofs
  Determinism/   determinism and scheduler-independence proofs
  Archive/       inactive proof experiments
```

The main small-step files are:

- `Runtime/SmallStep.v`: continuation-machine semantics.
- `Runtime/SmallStepPairParDispatch.v`: checked/blocked `Pair_Par` dispatch.
- `Runtime/SmallStepParallel.v`: branch-scheduled proof view for
  `StPairParRun`, bridged back to the ordinary `Step` relation.
- `Runtime/SmallStepStructuredTrace.v`: structured traces and scheduled runs.
- `Runtime/SmallStepPaperTheorems.v`: runtime theorem wrappers.
- `Soundness/SmallStepBackTriangle.v`: small-step summary relation.
- `Soundness/SmallStepCorrectnessBase.v`: base correctness utilities.
- `Soundness/SmallStepCorrectnessApps.v`: application correctness.
- `Soundness/SmallStepCorrectnessPairPar.v`: checked `Pair_Par` correctness.
- `Soundness/SmallStepPaperSoundness.v`: scheduled source-level
  surface-correctness wrapper.

## Current Status

The active theorem stack proves:

- finite-prefix type and trace safety;
- terminal type and trace soundness;
- checked-or-blocked safety for `Pair_Par`;
- scheduled source-level surface-effect correctness for checked `Pair_Par`;
- terminal scheduler independence for scheduled small-step runs.

There are no source-level `Axiom` or `Admitted` declarations in `theories/`.

Current non-goals:

- terminal small-step/big-step adequacy;
- equivalence with a separate sequential pair constructor;
- termination or cost bounds for summary evaluation;
- summary inference or synthesis.

For the exact theorem names and build environment, see
[ARTIFACT.md](ARTIFACT.md).
