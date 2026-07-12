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
`WTPairParStateRuntimeHeapShapeAt`. It also defines the stronger
`WTPairParStateRuntimeHeapShapeAtStrong` invariant, which records the outer
continuation as `WTKontRuntime stty (Ty_Pair tleft tright) tout k` and derives
the completed-branches return case from that continuation typing. It proves
checked-initial typing, retyping of an idle branch under a heap/store extension,
forgetful bridges back to the hidden-store invariants, preservation for wrapped
ordinary small-step states, preservation for the completed-branches return step,
conditional left/right branch preservation lemmas, and a parametric full
`PairParStep` preservation theorem
`WTPairParStateRuntimeHeapShapeAtStrong_step_preservation_with_active` assuming
the active-branch interface `WTStateRuntimeHeapShapeAtStepPreservation`, and
lifts it to finite interleaving traces with
`WTPairParStateRuntimeHeapShapeAtStrong_steps_preservation_with_active`. The
abstract-effect typing rules now require `TcRgn` for `AllocAbs`, `ReadAbs`, and
`WriteAbs`, which lets typed states derive eval-head region readiness. The same
file defines state- and pair-level terminal, not-stuck, and eval-head readiness
predicates, proves that heap synchronization preserves idle-branch readiness,
and proves not-stuck theorems for hidden-store and strong explicit-store
interleaving states. These progress results require preserved branch heap
agreement and the same `PairParCheckDecidable` premise used by the ordinary
small-step progress theorem. The checked-initial corollary
`pairpar_checked_initial_never_stuck_typed` packages those premises for the
successful checked branch, and `pairpar_checked_initial_steps_safety` combines
finite-trace preservation, store extension, preserved branch heap agreement, and
not-stuckness for each reached checked interleaving state. If such a trace
terminates, `pairpar_checked_initial_terminal_value` extracts the final value's
type and runtime shape. The `KDone` corollaries
`pairpar_checked_initial_kdone_steps_safety` and
`pairpar_checked_initial_kdone_terminal_value` specialize these endpoints to the
checked pair expression itself, and
`pairpar_checked_initial_kdone_terminal_pair` decomposes a terminal result into
typed/runtime-shaped pair components. `TraceTypingFacts.v` now bridges linear
small-step traces to sequential `Phi` summaries via `trace_as_phi`; using that
bridge, `SmallStepParallelPreservation.v` proves
`WTStateRuntimeHeapShapeAt_steps_trace_typed` for ordinary finite `Steps` traces
and the initial-state wrappers `initial_state_steps_trace_typed` and
`initial_state_terminal_value_with_trace`. The ordinary safety wrappers
`WTStateRuntimeHeapShapeAt_steps_safety_with_trace` and
`initial_state_steps_safety_with_trace` add not-stuckness to the same
preservation, store-extension, and trace-typing package. The ordinary
finite-prefix safety statements `WTStateRuntimeHeapShapeAt_never_stuck_typed`
and `initial_state_never_stuck_typed` expose the same nonterminating-program
safety idea without requiring a terminal state. The compact predicate
`StateTraceSafeAt` and wrappers `WTStateRuntimeHeapShapeAt_trace_safe_typed` and
`initial_state_trace_safe_typed` package ordinary finite-prefix preservation,
store extension, not-stuckness, and trace typing under one name. It also proves
`WTPairParStateRuntimeHeapShapeAtStrong_steps_trace_typed` plus the checked
corollary `pairpar_checked_initial_steps_trace_typed`, so every finite checked
interleaving trace is accompanied by a `TcPhi` proof at the reached store. The
packaged safety corollaries `pairpar_checked_initial_steps_safety_with_trace`
and `pairpar_checked_initial_kdone_steps_safety_with_trace` combine that trace
typing evidence with preservation, store extension, branch heap agreement, and
not-stuckness. The pair-level predicate `PairParTraceSafeAt` and wrappers
`WTPairParStateRuntimeHeapShapeAtStrong_trace_safe_typed`,
`pairpar_checked_initial_trace_safe_typed`, and
`pairpar_checked_initial_kdone_trace_safe_typed` give the same compact
finite-prefix safety package for checked interleavings. Terminal wrappers
`pairpar_checked_initial_terminal_value_with_trace`,
`pairpar_checked_initial_kdone_terminal_value_with_trace`, and
`pairpar_checked_initial_kdone_terminal_pair_with_trace` carry the same trace
typing evidence through final-value and final-pair extraction.
`SmallStepTyping.v` introduces the first lightweight
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
typed preservation facts for that target relation, including weak and strong
common-store invariants for the two running branches. The active-branch interface
returns the new store typing, `StoreExtends` evidence, and runtime heap shape
produced by each branch step. The heap-sensitive completion cases now have
explicit-store lemmas:
dereference preserves the current store, assignment preserves the current store
while updating an existing heap cell, and reference allocation returns the
freshly extended store typing. A reusable same-store packager handles the common
result shape, and explicit-store same-store lemmas now cover the pure heads,
eval/control frames, staged `Pair_Par` frames, and application/region/effect
body-entry frames. These lemmas are assembled into
`WTStateRuntimeHeapShapeAt_step_preservation`, closing the active-branch
interface `WTStateRuntimeHeapShapeAtStepPreservation`. The checked
non-parametric theorems
`WTPairParStateRuntimeHeapShapeAtStrong_step_preservation` and
`WTPairParStateRuntimeHeapShapeAtStrong_steps_preservation` now give strong
explicit-store preservation for one-step and finite `PairParStep` executions.
The same file now proves pair-level not-stuck theorems
`WTPairParStateRuntimeHeapShape_not_stuck`,
`WTPairParStateRuntimeHeapShapeAtStrong_not_stuck`, and
`WTPairParStateRuntimeHeapShapeAtStrong_steps_not_stuck`, under branch
heap-agreement and eval-head readiness assumptions. The stricter abstract-effect
typing rules support `TcExp_eval_head_regions_resolved` and the finite-trace
readiness theorem `WTPairParStateRuntimeHeapShapeAtStrong_steps_eval_heads_resolved`,
which in turn give the scheduler-facing theorem
`WTPairParStateRuntimeHeapShapeAtStrong_never_stuck_typed` without a separate
run-level readiness premise. The endpoint corollary
`pairpar_checked_initial_never_stuck_typed` applies this result directly to the
checked initial interleaving state built after a successful dynamic effect check.
The companion theorem `pairpar_checked_initial_steps_safety` returns both the
preserved strong pair invariant, store-extension evidence, preserved branch
heap agreement, and not-stuckness for any finite checked interleaving trace.
The terminal corollary `pairpar_checked_initial_terminal_value` says that any
terminal checked interleaving result is typed at the expected output type and has
the corresponding runtime value shape. The no-continuation corollaries
`pairpar_checked_initial_kdone_steps_safety` and
`pairpar_checked_initial_kdone_terminal_value` specialize the safety and terminal
statements to output type `subst_rho rho (Ty_Pair ty1 ty2)`.
`pairpar_checked_initial_kdone_terminal_pair` further exposes the terminal value
as `Pair (v1, v2)` with components typed and runtime-shaped at
`subst_rho rho ty1` and `subst_rho rho ty2`. The generic trace bridge
`trace_as_phi` lives in `TraceTypingFacts.v` and turns emitted dynamic-action
lists into sequential `Phi` summaries; `phi_as_list_trace_as_phi` proves that
converting the summary back with `phi_as_list` recovers the original trace.
Using it,
`WTStateRuntimeHeapShapeAt_steps_trace_typed` proves that ordinary finite
`Steps` traces preserve explicit typing and produce `TcPhi` evidence at the
final store. The wrappers `WTStateRuntimeHeapShapeAt_steps_safety_with_trace`
and `initial_state_steps_safety_with_trace` add not-stuckness, while
`WTStateRuntimeHeapShapeAt_never_stuck_typed` and
`initial_state_never_stuck_typed` expose finite-prefix safety for potentially
diverging ordinary executions. `StateTraceSafeAt` packages these ordinary
finite-prefix conclusions into a reusable predicate.
`initial_state_terminal_value_with_trace` specializes the result to terminating
initial states.
`WTPairParStateRuntimeHeapShapeAtStrong_steps_trace_typed` proves that finite
checked interleavings produce traces satisfying `TcPhi` at the final store. The
checked-initial wrapper `pairpar_checked_initial_steps_trace_typed` packages the
same result for the surface-effect checked branch, and the safety wrappers
`pairpar_checked_initial_steps_safety_with_trace` and
`pairpar_checked_initial_kdone_steps_safety_with_trace` expose trace typing
alongside the existing not-stuck and preservation conclusions. The terminal
variants ending in `_with_trace` similarly expose `TcPhi` evidence for final
values and decomposed final pairs.
`PairParTraceSafeAt` packages the checked-interleaving finite-prefix conclusions
under one predicate.
Trace replay and read-only trace/evaluation lemmas have been moved from
`HeapFacts.v` into `TraceFacts.v`, and downstream files now import the trace
facts explicitly when they need them. The old compatibility wrappers have also
been removed from `_CoqProject`. The `StoreExtends` relation and its basic
reflexivity, transitivity, and fresh-update facts now live in `StoreFacts.v`,
and the trace typing invariant plus its heap-replay lemmas live in
`TraceTypingFacts.v`. Generic finite-map lookup/update lemmas live in
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
