# SurfaceEffects Artifact Guide

This guide is for researchers who want to check the mechanized results
corresponding to the paper.

## Entry Point

The public theorem map is exported by:

```text
theories/PaperTheorems.v
```

That facade re-exports the runtime safety/determinism theorems from
`theories/Runtime/SmallStepPaperTheorems.v` and the structured
surface-correctness theorem from
`theories/Soundness/SmallStepPaperSoundness.v`.

## Known-Good Toolchain

The current local artifact was checked with:

```text
The Rocq Prover, version 9.1.1
compiled with OCaml 4.14.2
```

The current opam switch is `surfaceeffects`. The relevant installed packages
are:

```text
ocaml-base-compiler   4.14.2
coq                   9.1.1
coq-core              9.1.1
coqide-server         9.1.1
rocq-core             9.1.1
rocq-runtime          9.1.1
rocq-stdlib           9.0.0
coq-stdlib            9.0.0
coq-stdpp             1.12.0
dune                  3.23.1
zarith                1.14
```

A fresh switch can be prepared with commands of this shape:

```sh
opam switch create surfaceeffects ocaml-base-compiler.4.14.2
eval $(opam env --switch=surfaceeffects)
opam install coq.9.1.1 coq-stdpp.1.12.0
```

If opam resolves Rocq packages directly rather than through Coq compatibility
packages, the important version check is:

```sh
rocq --version
coqc --version
```

Both should report Rocq 9.1.1.

## Build

From the repository root:

```sh
eval $(opam env --switch=surfaceeffects)
make
```

Expected result: the whole `_CoqProject` compiles. Rocq 9 currently emits
compatibility warnings about old `From Coq` imports and notation prefixes; these
warnings are expected and do not block the build.

The revised paper can be rebuilt separately:

```sh
cd paper
pdflatex -interaction=nonstopmode -halt-on-error main_revised.tex
pdflatex -interaction=nonstopmode -halt-on-error main_revised.tex
```

Generated `.vo`, `.vos`, `.vok`, `.glob`, `.aux`, `.out`, `.log`, `.toc`, and
make dependency files are intentionally ignored by `.gitignore` when they are
not already tracked.

## Theorem Map

The paper states the theorems in mathematical notation. The corresponding
mechanized names are:

| Paper role | Mechanized theorem | File |
| --- | --- | --- |
| Finite-prefix type/trace safety | `PaperSmallStepFinitePrefixSafety` | `theories/Runtime/SmallStepPaperTheorems.v` |
| Terminal type/trace soundness for ordinary runs | `PaperSmallStepTerminalSoundness` | `theories/Runtime/SmallStepPaperTheorems.v` |
| Checked-or-blocked `Pair_Par` finite-prefix safety | `PaperPairParCheckedOrBlockedTraceSafety` | `theories/Runtime/SmallStepPaperTheorems.v` |
| Checked-or-blocked `Pair_Par` terminal soundness | `PaperPairParCheckedOrBlockedTerminalSoundness` | `theories/Runtime/SmallStepPaperTheorems.v` |
| Successful checked packed `Pair_Par` terminal soundness | `PaperPairParCheckedPackedTerminalSoundness` | `theories/Runtime/SmallStepPaperTheorems.v` |
| Scheduled terminal heap/value/full-trace soundness | `PaperScheduledSmallStepTerminalTraceSoundness` | `theories/Runtime/SmallStepPaperTheorems.v` |
| Initial-expression scheduled terminal trace soundness | `PaperScheduledExpressionTerminalTraceSoundness` | `theories/Runtime/SmallStepPaperTheorems.v` |
| Scheduled terminal determinism | `PaperScheduledSmallStepTerminalDeterminism` | `theories/Runtime/SmallStepPaperTheorems.v` |
| Initial-expression scheduled terminal determinism | `PaperScheduledExpressionTerminalDeterminism` | `theories/Runtime/SmallStepPaperTheorems.v` |
| Structured surface-effect correctness for checked `Pair_Par` | `PaperPairParCheckedStructuredTerminalCorrectness` | `theories/Soundness/SmallStepPaperSoundness.v` |

Additional value-only scheduled wrappers remain in
`theories/Runtime/SmallStepPaperTheorems.v` as derived support lemmas, but the
paper-facing theorem map uses the trace-strengthened scheduled statements.

## Source Navigation

- `theories/Runtime/SmallStep.v`: continuation-machine operational semantics.
- `theories/Runtime/SmallStepPairParDispatch.v`: staged dynamic check for
  `Pair_Par`, including checked/blocked safety facts.
- `theories/Runtime/SmallStepStructuredTrace.v`: structured `Phi` traces and
  scheduled executions.
- `theories/Runtime/SmallStepPaperTheorems.v`: runtime paper-facing theorem
  wrappers.
- `theories/Soundness/SmallStepBackTriangle.v`: small-step summary relation
  used by the direct correctness stack.
- `theories/Soundness/SmallStepCorrectnessBase.v`: shared terminal-run
  decompositions and base correctness cases.
- `theories/Soundness/SmallStepCorrectnessApps.v`: application and
  effect-application correctness cases.
- `theories/Soundness/SmallStepCorrectnessPairPar.v`: checked structured
  `Pair_Par` correctness.
- `theories/Soundness/SmallStepPaperSoundness.v`: paper-facing structured
  correctness wrapper.

## Scope And Non-Goals

The artifact proves the small-step continuation-machine safety, correctness,
determinism, and scheduler-independence results listed above.

The artifact does not currently prove:

- terminal small-step/big-step adequacy;
- observational equivalence with a separate sequential tuple constructor;
- termination or cost bounds for summary evaluation;
- summary inference or synthesis.

The old matched-trace bridge to the terminating evaluator is archived under
`theories/Archive/` for comparison, but it is not part of `_CoqProject` or the
paper-facing theorem spine.

## Git Hygiene For Artifact Review

Before packaging or sharing the artifact, the normal git status should show
only intentional source/documentation changes:

```sh
git status --short
```

Ignored build products can be inspected with:

```sh
git status --short --ignored
```

The repository `.gitignore` excludes Rocq, LaTeX, and local scratch outputs so
reviewers do not see generated proof objects or cache files as source changes.
