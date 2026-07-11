# SurfaceEffects

SurfaceEffects is a Rocq mechanization of a language with regions, heap
effects, dynamic traces, parallel pairs, and effect soundness.

## Current Build

Known local toolchain:

```sh
opam switch surfaceeffects
eval $(opam env)
rocq -v
make
```

The current workspace builds with:

```text
The Rocq Prover, version 9.1.1
compiled with OCaml 4.14.2
```

Both `rocq` and `coqc` report this Rocq version in the current switch.

Expected build result:

```sh
make
```

The full project currently compiles. There are no source-level `Axiom` or
`Admitted` declarations in `theories/`.

Rocq 9 emits some compatibility warnings:

- `From Coq` imports are deprecated in favor of `From Stdlib`.
- A few notation declarations have incompatible prefixes.

These warnings do not currently block the build.

## Current Source Layout

The source tree is organized by dependency layer:

```text
theories/
  Core/
    Regions.v
    Expressions.v
    Values.v
    ComputedActions.v
    DynamicActions.v
    StaticActions.v

  Runtime/
    Heap.v
    TraceSemantics.v
    HeapTyping.v
    Semantics.v
    SmallStep.v
    SmallStepFacts.v
    SmallStepParallel.v
    SmallStepTyping.v
    SmallStepSafetyFacts.v
    SmallStepProgress.v
    SmallStepPreservation.v
    SmallStepParallelPreservation.v

  Typing/
    TypeSyntax.v
    TypingJudgments.v

  Meta/
    Tactics.v
    LocallyNameless.v
    MapFacts.v
    RegionSubstitutionFacts.v
    RegionFacts.v
    TypeSubstitutionFacts.v
    EffectFreeVarsFacts.v
    EffectFacts.v
    TypingWeakeningFacts.v
    TypeFacts.v
    StoreFacts.v
    TraceFacts.v
    HeapFacts.v
    TraceTypingFacts.v

  Soundness/
    TypeSystem.v
    EffectSystem.v
    Correctness.v

  Determinism/
    ReadOnlyDeterminism.v
    Determinism.v
    DeterminismExt.v
```

`Definitions/Axioms.v` is no longer part of the source tree or `_CoqProject`.
The old `Definitions/` and `Proofs/` directories may still contain generated
build artifacts after local compilation, but they no longer contain source files
listed by `_CoqProject`.

## Proof Status

The main type soundness theorem is now stratified internally:

- `ty_sound_strong` proves type soundness together with a trace typing
  invariant.
- `ty_sound` preserves the older public interface by projecting away that
  extra invariant.
- `TcHeap_Extended_2` is proved without an admission.
- The `BS_Set_Ref` semantics includes the side condition that assignment only
  writes to an existing location after evaluating the assigned value.
- Concrete read/write and write/write computed-action disjointness is based on
  concrete address inequality `(region, location) <> (region, location)`, so
  same-region accesses to distinct locations can be accepted by the parallel
  disjointness check.

The trace typing invariant records that dynamic allocation and write actions
are justified by the final store typing. This is what makes the parallel heap
extension proof go through without an axiom.

A preliminary small-step runtime layer has been added alongside the existing
big-step semantics. `SmallStep.v` defines a continuation machine with silent
steps and dynamic-action labels for the sequential/effect constructs. `Pair_Par`
now has a staged small-step path that evaluates the two surface-effect
applications first, checks `Disjointness theta1 theta2` and absence of
`Conflictness theta1 theta2`, and then either enters the checked computational
path or falls back to the sequential computational path. `SmallStepFacts.v`
contains the first reusable facts about terminal states and multi-step
composition, including one-step determinism for this staging machine.
`SmallStepParallel.v` adds a separate nondeterministic interleaving relation for
the successful checked branch: either computational branch may step, heap
updates are synchronized into the other branch state, and two finished branches
return a pair to the outer continuation. It also proves the first operational
facts for that relation: heap agreement is preserved by one step and finite
traces, interleaving traces compose, and the checked initial state can start by
stepping either branch. `SmallStepParallelPreservation.v` introduces the first
typed invariant for interleaving configurations,
`WTPairParStateRuntimeHeapShape`, plus explicit-store state and pair-state
invariants `WTStateRuntimeHeapShapeAt` and
`WTPairParStateRuntimeHeapShapeAt`. It proves checked-initial typing, retyping
of an idle branch under a heap/store extension, forgetful bridges back to the
hidden-store invariants, preservation for wrapped ordinary small-step states,
preservation for the completed-branches return step, and conditional left/right
branch preservation lemmas. `SmallStepTyping.v` introduces the first lightweight
`WTKont` and `WTState` invariants plus indexed
`WTKontTyped`/`WTStateTyped` relations for the preservation proof to build on.
`SmallStepSafetyFacts.v` records the initial not-stuck facts for terminal
well-typed states. `SmallStepProgress.v` proves the first eval-state progress
lemma for supported sequential heads whose abstract-effect regions are resolved,
plus return-frame progress for explicitly ready frames. It also introduces a
stricter `RuntimeValShape` predicate with canonical-shape lemmas and progress
corollaries for arithmetic, boolean, closure, effect, and concrete-reference
frames. `WTKontTyped` now records the concrete-region restriction for reference
frames that the source typing rules already require. `WTStateRuntimeShape`
packages typed states together with runtime value shape and proves a conditional
not-stuck theorem for sequential/resolved eval states, return states, and done
states. Closure cases of `RuntimeValShape` now remember the captured
runtime-shaped environment and expose inversion lemmas for recursive and
region-polymorphic closures. `SmallStepPreservation.v` adds two preservation
layers. The first records why eval continuations must be indexed by
`subst_rho rho t`. The second
introduces `WTKontRuntime`, a runtime-substituted continuation relation, and
`WTStateRuntimeKontShape`, which carries the `TcInc` premise needed for closure
values. It now proves preservation for pure head steps, frame-introducing eval
steps, conditionals, arithmetic frames, concrete read/write summary frames,
concat frames, `KDone`, application/effect-application eval-argument frames,
application/effect-application body-entry frames, region-application body-entry
frames, assignment eval-value, and assignment write completion. A stronger
`WTStateRuntimeHeapShape` layer adds a runtime heap-shape invariant, lifts the
same-heap preservation cases, proves the heap-sensitive completion steps for
allocation, dereference, assignment, and the staged `Pair_Par` frames, and
assembles them into the general one-step theorem
`WTStateRuntimeHeapShape_step_preservation`; it also lifts this to finite traces
with `WTStateRuntimeHeapShape_steps_preservation` and the initial-state
corollary `WTStateRuntimeHeapShape_initial_steps_preservation`. These theorems
are intentionally stated at the heap-shaped layer, because dereference
preservation needs runtime-shape evidence for values read from the heap.
The same layer now also exposes and handles the dynamic-check boundary for
staged `Pair_Par`: `PairParCheckState` identifies the frame where both computed
summaries have been evaluated, `pairpar_check_state_ready` shows that a
successful `Disjointness`/`Conflictness` check can step into the checked
computational path, and `pairpar_check_state_fallback_ready` shows that a failed
check falls back to the sequential computational path. Because computed
summaries are still represented as `Ensemble`s, the total progress theorem
`WTStateRuntimeHeapShape_not_stuck` takes the explicit premise
`PairParCheckDecidable`; without that premise,
`WTStateRuntimeHeapShape_not_stuck_or_pairpar_check` keeps the exact check
boundary visible.

## Remaining Stratification Work

The source files have been moved into strata. The former `GTypes.v` content has
been split into type syntax and typing judgments, and the former `GHeap.v`
content has been split into heap operations, trace semantics, and heap typing.
The small-step migration has started with a continuation machine in
`SmallStep.v`, basic reusable facts in `SmallStepFacts.v`, and a lightweight
typed-state layer plus indexed continuation typing in
`SmallStepTyping.v`/`SmallStepSafetyFacts.v`/`SmallStepProgress.v`, followed by
the first preservation-shaped invariant and preservation lemmas in
`SmallStepPreservation.v`; the existing big-step semantics remains the
terminating reference semantics. Application and effect-application body entry
now re-establish both `TcEnv` and `RuntimeEnvShape` by extending the captured
closure environment with the recursive closure and argument value.
Region-application body entry re-establishes those invariants by extending the
captured region environment and using the open/close substitution bridge now
located in `TypeSubstitutionFacts.v`. The heap-shaped cases are now assembled
into the general one-step preservation theorem, including the staged `Pair_Par`
control frames, and lifted to arbitrary finite `Steps` traces. The current
small-step machine takes a successful check into the checked computational path
and a failed check into the sequential fallback path; both paths are currently
implemented with the same sequential continuation frames in the staging
machine, while `SmallStepParallel.v` provides the separate interleaving target
relation for the checked branch. `SmallStepParallelPreservation.v` now packages
the first typed preservation facts for that target relation, including a
common-store invariant for the two running branches. The next proof step is
extracting the concrete heap/store-extension evidence produced by each active
branch step, and then assembling the conditional left/right branch lemmas into a
full preservation theorem for `PairParStep`.
Trace replay and read-only trace/evaluation lemmas have been moved from
`HeapFacts.v` into `TraceFacts.v`, and downstream files now import the trace
facts explicitly when they need them. The old compatibility wrappers have also
been removed from `_CoqProject`. Store-extension facts now live in
`StoreFacts.v`, and the trace typing invariant plus its heap-replay lemmas live
in `TraceTypingFacts.v`. Generic finite-map lookup/update lemmas live in
`MapFacts.v`, store-weakening facts live in `TypingWeakeningFacts.v`, and
low-level region substitution/fold lemmas live in `RegionSubstitutionFacts.v`.
`RegionFacts.v` now keeps the higher-level `TcRho` no-free-vars theorem family.
Type-level substitution commutation and rho-extension fold lemmas live in
`TypeSubstitutionFacts.v`, while `TypeFacts.v` keeps typing closure and
environment-extension facts. Effect free-variable/inclusion support lives in
`EffectFreeVarsFacts.v`, leaving `EffectFacts.v` focused on effect unions,
conflict/disjointness facts, soundness, and read-only preservation. The next
cleanup is to make the remaining large fact files match the strata more
precisely. Dependencies should continue to flow in one direction. In
particular, core/read-only determinism supports soundness, while extended
determinism sits after correctness:

```text
Core < Runtime < Typing < Meta < Core Determinism < Soundness < Extended Determinism
```

A more refined target after splitting large files:

```text
theories/
  Core/
    Names.v              # identifiers, regions, shared finite-map utilities
    Syntax.v             # expressions and values
    StaticActions.v      # static actions and static effects
    DynamicActions.v     # dynamic actions and traces
    ComputedActions.v    # computed effects

  Runtime/
    Heap.v               # heaps and heap operations
    Semantics.v          # big-step semantics
    TraceSemantics.v     # trace replay relation and trace execution facts

  Typing/
    Types.v              # Tau, Gamma, Sigma, Omega
    Contexts.v           # typing contexts, store typings, environments
    ExprTyping.v         # TcExp, TcVal, TcEnv, TcRho, TcInc
    EffectTyping.v       # static/dynamic effect typing judgments

  Meta/
    Tactics.v
    LocallyNameless.v
    MapFacts.v
    RegionSubstitutionFacts.v
    RegionFacts.v
    TypeSubstitutionFacts.v
    EffectFreeVarsFacts.v
    TypingWeakeningFacts.v
    StoreFacts.v
    HeapFacts.v
    TraceFacts.v
    TraceTypingFacts.v
    TypeFacts.v
    EffectFacts.v

  Soundness/
    TypeSoundness.v
    EffectSoundness.v
    Correctness.v

  Determinism/
    CoreDeterminism.v
    ReadOnlyDeterminism.v
    ExtendedDeterminism.v
```

Suggested next migration order:

1. Split the remaining large fact files by subject: region facts, type facts,
   effect facts, and any residual heap/trace facts.
2. Trim direct imports after each split so files mention only the layer they use.
3. Rename theorem files once the contents are stable: `TypeSystem.v` to
   `TypeSoundness.v`, `EffectSystem.v` to `EffectSoundness.v`, and
   `DeterminismExt.v` to `ExtendedDeterminism.v`.

The important rule is that lower layers should never import higher layers. For
example, `Runtime/Semantics.v` should not import typing proofs, and `Meta/`
facts should not import final soundness theorems.
