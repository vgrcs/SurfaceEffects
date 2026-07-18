# SurfaceEffects

SurfaceEffects is a Rocq mechanization of a language with regions, heap
effects, dynamic traces, parallel pairs, and effect soundness.

For a paper-facing summary of the current mechanized proof state, theorem map,
and remaining limitations, see [REPORT.md](REPORT.md).

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
    SmallStepProgressBase.v
    SmallStepReturnProgress.v
    SmallStepEvalProgress.v
    SmallStepRuntimeProgress.v
    SmallStepProgress.v
    SmallStepRuntimeSubstShape.v
    SmallStepRuntimeHeapShape.v
    SmallStepRuntimeKontTyping.v
    SmallStepRuntimeStateShape.v
    SmallStepPreservationBase.v
    SmallStepPreservationHeapShapeEvalCases.v
    SmallStepPreservationHeapShapeHeadCases.v
    SmallStepPreservationHeapShapeReturnCases.v
    SmallStepPreservationHeapShapeCases.v
    SmallStepPreservationKontShapeEvalCases.v
    SmallStepPreservationKontShapeHeadCases.v
    SmallStepPreservationKontShapeReturnCases.v
    SmallStepPreservationKontShapeCases.v
    SmallStepPreservationHeapSensitiveCases.v
    SmallStepPreservationTheorems.v
    SmallStepPreservation.v
    SmallStepExplicitStoreBase.v
    SmallStepExplicitStoreHeap.v
    SmallStepExplicitStoreHeadCases.v
    SmallStepExplicitStoreEvalCases.v
    SmallStepExplicitStoreReturnCases.v
    SmallStepExplicitStoreBodyCases.v
    SmallStepExplicitStoreCases.v
    SmallStepExplicitStoreTheorems.v
    SmallStepExplicitStore.v
    SmallStepTraceSafety.v
    SmallStepParallelPreservationBase.v
    SmallStepParallelTyping.v
    SmallStepParallelStepPreservation.v
    SmallStepParallelProgress.v
    SmallStepParallelSafety.v
    SmallStepParallelPreservation.v
    SmallStepParallelTraceTyping.v
    SmallStepParallelTraceSafe.v
    SmallStepParallelCheckedTraceSafety.v
    SmallStepParallelCheckedTerminal.v
    SmallStepParallelTraceSafety.v
    SmallStepSequentialSoundness.v
    SmallStepStructuredTrace.v
    SmallStepEffectSoundness.v
    SmallStepCorrectness.v
    SmallStepPaperTheorems.v

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
    SmallStepCorrectnessBridge.v
    SmallStepBackTriangle.v
    SmallStepCorrectnessDirect.v
    SmallStepPaperSoundness.v

  Determinism/
    ReadOnlyDeterminism.v
    Determinism.v
    SmallStepStructuredReplay.v
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
facts for that relation: the branch heap-synchronization invariant is preserved
by one step and finite traces, interleaving traces compose, and the checked
initial state can start by stepping either branch. The explicit-store ordinary
preservation layer is split
by dependency. `SmallStepExplicitStoreBase.v` introduces
`WTStateRuntimeHeapShapeAt` and the forget/re-heap lemmas under `StoreExtends`.
`SmallStepExplicitStoreHeap.v` handles the heap-sensitive dereference,
assignment, and allocation completion cases and defines the active-branch
interface `WTStateRuntimeHeapShapeAtStepPreservation`.
The same-store case library is split into
`SmallStepExplicitStoreHeadCases.v`, `SmallStepExplicitStoreEvalCases.v`,
`SmallStepExplicitStoreReturnCases.v`, and
`SmallStepExplicitStoreBodyCases.v`, with `SmallStepExplicitStoreCases.v` kept
as a re-export facade. `SmallStepExplicitStoreTheorems.v` assembles
`WTStateRuntimeHeapShapeAt_step_preservation`, and
`SmallStepExplicitStore.v` re-exports the explicit-store layer.

`TraceTypingFacts.v` bridges linear small-step traces to sequential `Phi`
summaries via `trace_as_phi`. `SmallStepTraceSafety.v` uses that bridge to prove
ordinary finite-prefix trace safety: `WTStateRuntimeHeapShapeAt_steps_trace_typed`,
the initial-state wrappers, the compact `StateTraceSafeAt` predicate, never-stuck
wrappers for potentially diverging executions, and terminal extractors such as
`StateTraceSafeAt_terminal_value` and
`initial_state_terminal_value_with_trace`.

The checked interleaving proof is split similarly.
`SmallStepParallelPreservationBase.v` introduces the shared re-heap and
done-continuation interfaces. `SmallStepParallelTyping.v` owns the weak,
strong, and erased pair-level typing predicates, including
`WTPairParStateRuntimeHeapShapeAtStrong`. `SmallStepParallelStepPreservation.v`
proves one-step and finite-trace `PairParStep` preservation.
`SmallStepParallelProgress.v` owns pair-level terminal, not-stuck, eval-head
readiness, and never-stuck theorems. `SmallStepParallelSafety.v` packages the
checked-initial non-trace safety and terminal-value corollaries.
`SmallStepParallelPreservation.v` is the re-export facade for those layers.

The checked trace layer is split into four files.
`SmallStepParallelTraceTyping.v` proves
`WTPairParStateRuntimeHeapShapeAtStrong_steps_trace_typed`.
`SmallStepParallelTraceSafe.v` packages finite-prefix checked interleaving
safety as `PairParTraceSafeAt` and gives the generic terminal extractors.
`SmallStepParallelCheckedTraceSafety.v` provides the checked-initial trace
safety wrappers, while `SmallStepParallelCheckedTerminal.v` owns the
checked-initial terminal extractors ending in `_with_trace`, including
`pairpar_checked_initial_kdone_terminal_pair_with_trace`.
`SmallStepParallelTraceSafety.v` is the re-export facade for those trace layers.
`SmallStepSequentialSoundness.v` packages the reviewer-facing staged
`Pair_Par` dispatch facts: a successful check exposes the checked interleaving
start state while the ordinary continuation path begins with the first
computational application, and a failed check steps directly into that same
sequential fallback path. It also provides typed wrappers for fallback
preservation, checked-interleaving trace safety, and terminal-value extraction
after the decidable check split.
`SmallStepStructuredTrace.v` adds an instrumented `Phi`-trace layer for future
adequacy work. It keeps ordinary finite-prefix traces available as structured
`StepsPhi`, records checked computation steps with separate left/right branch
traces, and gives `Pair_Par` trace shapes whose effect-summary phase is
`Phi_Par`-structured before either checked computation branches or sequential
fallback. It also proves the structured checked/fallback split
`pairpar_check_decidable_phi_trace_safe` and terminal extractor
`pairpar_check_decidable_phi_terminal_value`, plus terminal component
extractors for successful checked runs and sequential fallback runs.
`SmallStepPaperTheorems.v` provides stable paper-facing theorem names:
`PaperSmallStepFinitePrefixSafety`, `PaperSmallStepTerminalSoundness`,
`PaperPairParCheckedOrBlockedTraceSafety`, and
`PaperPairParCheckedOrBlockedTerminalSoundness`. These four are the current
theorem map cited by the revised paper. The file also exposes
`PaperSmallStepTerminalDeterminism`, which says two terminal ordinary
small-step runs from the same state have the same emitted trace, final heap,
and final value. The structured counterparts
`PaperSmallStepStructuredTerminalDeterminism` and
`PaperSmallStepStructuredEffectTerminalDeterminism` give the same result for
terminal `StepsPhi` runs, with equality stated for `phi_as_list` rather than
syntactic `Phi` equality.
`PaperPairParCheckedArbitraryScheduleTerminalDeterminism` is the checked
parallel counterpart: two terminal checked `Pair_Par` runs from the same start,
whose left/right branch traces are sound under the same successful check,
finish with the same heap and value without requiring the two schedules to use
the same branch projection. `theories/Determinism/SmallStepDeterminismExt.v`
adds the full small-step replacements for the old terminating big-step
determinism statements: `SmallStepDynamicDeterminism_ext`,
`SmallStepStructuredDynamicDeterminism_ext`, `SmallStepDeterminism`, and
`SmallStepStructuredDeterminism`. The file also exposes
`PaperPairParSummaryPassSmallStepSoundPrefix` and
`PaperPairParSummaryFailSmallStepSoundPrefix`, which package the checked
`Pair_Par` source-prefix result using the small-step effect-summary soundness
proof rather than a raw `Epsilon_Phi_Soundness` premise.
`SmallStepTyping.v` introduces the first lightweight
`WTKont` and `WTState` invariants plus indexed
`WTKontTyped`/`WTStateTyped` relations for the preservation proof to build on.
`SmallStepSafetyFacts.v` records the initial not-stuck facts for terminal
well-typed states. The progress layer is split into four modules.
`SmallStepProgressBase.v` defines `SequentialHead`,
`EvalHeadRegionsResolved`, the stricter `RuntimeValShape` and
`RuntimeEnvShape` predicates, and their canonical-shape, environment, and store
extension lemmas. `SmallStepReturnProgress.v` defines `ReturnFrameReady` and
proves return-frame progress from typing plus runtime shape. `SmallStepEvalProgress.v`
proves eval-state progress for supported sequential heads whose abstract-effect
regions are resolved. `SmallStepRuntimeProgress.v` packages those facts into
the runtime-shaped state predicates and conditional not-stuck theorems, while
`SmallStepProgress.v` re-exports the layer. `WTKontTyped` now records the
concrete-region restriction for reference frames that the source typing rules
already require. Closure cases of `RuntimeValShape` now remember the captured
runtime-shaped environment and expose inversion lemmas for recursive and
region-polymorphic closures. The hidden-store preservation stack is now split
into smaller runtime files. `SmallStepRuntimeSubstShape.v` records the first
substitution-indexed state shape and the head preservation facts that justify
indexing eval continuations by `subst_rho rho t`. `SmallStepRuntimeHeapShape.v`
introduces `RuntimeHeapShape` and its update lemmas.
`SmallStepRuntimeKontTyping.v` owns `WTKontRuntime` plus the store-extension and
environment/substitution helpers. `SmallStepRuntimeStateShape.v` introduces
`WTStateRuntimeKontShape` and `WTStateRuntimeHeapShape`, and
`SmallStepPreservationBase.v` re-exports these foundational layers.
The same-heap heap-shaped cases are grouped by role in
`SmallStepPreservationHeapShapeEvalCases.v`,
`SmallStepPreservationHeapShapeHeadCases.v`, and
`SmallStepPreservationHeapShapeReturnCases.v`; the matching continuation-shaped
cases live in `SmallStepPreservationKontShapeEvalCases.v`,
`SmallStepPreservationKontShapeHeadCases.v`, and
`SmallStepPreservationKontShapeReturnCases.v`. The shorter
`SmallStepPreservationHeapShapeCases.v` and
`SmallStepPreservationKontShapeCases.v` files re-export those clusters.
`SmallStepPreservationHeapSensitiveCases.v` handles allocation, dereference,
assignment, body-entry cases, and staged `Pair_Par` frames.
`SmallStepPreservationTheorems.v` assembles the general
one-step theorem `WTStateRuntimeHeapShape_step_preservation`, lifts it to finite
traces with `WTStateRuntimeHeapShape_steps_preservation`, and contains the
dynamic-check progress boundary. `SmallStepPreservation.v` is now the re-export
facade for those layers. These theorems are intentionally stated at the
heap-shaped layer, because dereference preservation needs runtime-shape evidence
for values read from the heap. The final theorem layer also exposes and handles
the dynamic-check boundary for
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
`SmallStepTyping.v`/`SmallStepSafetyFacts.v`, followed by the progress stack in
`SmallStepProgressBase.v`, `SmallStepReturnProgress.v`,
`SmallStepEvalProgress.v`, and `SmallStepRuntimeProgress.v`, then the
hidden-store preservation base in `SmallStepRuntimeSubstShape.v`,
`SmallStepRuntimeHeapShape.v`, `SmallStepRuntimeKontTyping.v`,
`SmallStepRuntimeStateShape.v`, and the `SmallStepPreservationBase.v` facade,
the heap-shaped and continuation-shaped eval/head/return case clusters,
`SmallStepPreservationHeapSensitiveCases.v`, and
`SmallStepPreservationTheorems.v`; the existing big-step semantics remains the
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
relation for the checked branch.

The explicit-store active-branch preservation layer is now factored into small
runtime strata. `SmallStepExplicitStoreBase.v` owns
`WTStateRuntimeHeapShapeAt`, the bridge back to `WTStateRuntimeHeapShape`, and
the re-heap lemmas used when an idle branch is synchronized to a newer heap.
`SmallStepExplicitStoreHeap.v` proves the heap-sensitive completion cases:
dereference preserves the current store, assignment preserves the current store
while updating an existing heap cell, and reference allocation returns the
freshly extended store typing. It also defines the active-branch interface
`WTStateRuntimeHeapShapeAtStepPreservation` and the reusable same-store
packager. `SmallStepExplicitStoreCases.v` contains the pure head,
eval/control-frame, staged `Pair_Par`, and application/region/effect body-entry
cases through four smaller files: `SmallStepExplicitStoreHeadCases.v`,
`SmallStepExplicitStoreEvalCases.v`,
`SmallStepExplicitStoreReturnCases.v`, and
`SmallStepExplicitStoreBodyCases.v`. `SmallStepExplicitStoreCases.v` re-exports
those case clusters. `SmallStepExplicitStoreTheorems.v` assembles
`WTStateRuntimeHeapShapeAt_step_preservation`, closing the active-branch
interface, and `SmallStepExplicitStore.v` is the facade that re-exports the
whole explicit-store layer.

The checked-interleaving preservation stack is now split into base, typing,
step-preservation, progress, and safety layers.
`SmallStepParallelPreservationBase.v` packages the common-store retyping
helpers and done-continuation interface for the two running branches.
`SmallStepParallelTyping.v` owns the weak, strong, and erased pair-level
typing predicates and their checked-initial constructors. The checked
non-parametric theorems
`WTPairParStateRuntimeHeapShapeAtStrong_step_preservation` and
`WTPairParStateRuntimeHeapShapeAtStrong_steps_preservation` now give strong
explicit-store preservation for one-step and finite `PairParStep` executions
from `SmallStepParallelStepPreservation.v`.
`SmallStepParallelProgress.v` proves pair-level not-stuck theorems
`WTPairParStateRuntimeHeapShape_not_stuck`,
`WTPairParStateRuntimeHeapShapeAtStrong_not_stuck`, and
`WTPairParStateRuntimeHeapShapeAtStrong_steps_not_stuck`, under branch
heap-synchronization and eval-head readiness assumptions. The stricter abstract-effect
typing rules support `TcExp_eval_head_regions_resolved` and the finite-trace
readiness theorem `WTPairParStateRuntimeHeapShapeAtStrong_steps_eval_heads_resolved`,
which in turn give the scheduler-facing theorem
`WTPairParStateRuntimeHeapShapeAtStrong_never_stuck_typed` without a separate
run-level readiness premise. The endpoint corollary
`pairpar_checked_initial_never_stuck_typed` applies this result directly to the
checked initial interleaving state built after a successful dynamic effect check.
`SmallStepParallelSafety.v` owns the non-trace endpoint theorems. The companion
theorem `pairpar_checked_initial_steps_safety` returns both the
preserved strong pair invariant, store-extension evidence, preserved branch
heap synchronization, and not-stuckness for any finite checked interleaving trace.
The terminal corollary `pairpar_checked_initial_terminal_value` says that any
terminal checked interleaving result is typed at the expected output type and has
the corresponding runtime value shape. The no-continuation corollaries
`pairpar_checked_initial_kdone_steps_safety` and
`pairpar_checked_initial_kdone_terminal_value` specialize the safety and terminal
statements to output type `subst_rho rho (Ty_Pair ty1 ty2)`.
`pairpar_checked_initial_kdone_terminal_pair` further exposes the terminal value
as `Pair (v1, v2)` with components typed and runtime-shaped at
`subst_rho rho ty1` and `subst_rho rho ty2`. `SmallStepParallelPreservation.v`
re-exports these three layers for downstream files. The generic trace bridge
`trace_as_phi` lives in `TraceTypingFacts.v` and turns emitted dynamic-action
lists into sequential `Phi` summaries; `phi_as_list_trace_as_phi` proves that
converting the summary back with `phi_as_list` recovers the original trace.
`SmallStepTraceSafety.v` uses it to prove that ordinary finite `Steps` traces
preserve explicit typing and produce `TcPhi` evidence at the final store. It
also packages ordinary finite-prefix safety as `StateTraceSafeAt`, exposes
never-stuck wrappers for potentially diverging ordinary executions, and provides
terminal-value extraction with trace evidence.

The checked trace layer is factored similarly.
`SmallStepParallelTraceTyping.v` proves that finite checked interleavings
produce traces satisfying `TcPhi` at the final store.
`SmallStepParallelTraceSafe.v` defines `PairParTraceSafeAt` and proves the
generic terminal extractors `PairParTraceSafeAt_terminal_value` and
`PairParTraceSafeAt_kdone_terminal_pair`. `SmallStepParallelCheckedTraceSafety.v`
exposes checked-initial trace typing alongside preservation, store extension,
branch heap synchronization, and not-stuckness. `SmallStepParallelCheckedTerminal.v`
owns the checked-initial terminal variants ending in `_with_trace`, recovering
typed final values, decomposed final pairs, and trace evidence.
`SmallStepParallelTraceSafety.v` re-exports the full checked trace layer.
`SmallStepSequentialSoundness.v` makes the staged check/fallback story explicit:
`pairpar_check_decidable_dispatch` splits on the dynamic effect check,
`pairpar_check_fail_sequential_preservation` proves the failed-check sequential
target preserves explicit runtime typing,
`pairpar_check_fail_sequential_trace_safe` lifts the failed branch to ordinary
finite-prefix trace safety, `pairpar_check_pass_checked_trace_safe` connects a
successful check to the safe checked interleaving theorem, and
`pairpar_check_decidable_trace_safe` packages the success/failure trace-safety
split in one theorem. `pairpar_check_decidable_terminal_value` adds the matching
terminal-value extractor for both checked and fallback outcomes.
`SmallStepPaperTheorems.v` re-exposes these results through the stable names
`PaperSmallStepFinitePrefixSafety`, `PaperSmallStepTerminalSoundness`,
`PaperPairParCheckedOrBlockedTraceSafety`, and
`PaperPairParCheckedOrBlockedTerminalSoundness`, plus
`PaperPairParCheckedArbitraryScheduleTerminalDeterminism` for terminal
checked-parallel schedule independence.
`SmallStepStructuredTrace.v` is the first adequacy-oriented trace layer: it
does not replace the paper-facing list-trace theorems, but it records the
branch structure needed to align future small-step terminal runs with the
big-step trace shape
`Phi_Seq (Phi_Par acts_eff1 acts_eff2) (Phi_Par acts_mu1 acts_mu2)`. Its
structured checked-trace predicate `PairParPhiTraceSafeAt` preserves heap
agreement, not-stuckness, and typed `Phi` evidence for each branch component.
The component extractors keep independent effect-summary store typings visible,
while `StepsPhi_replays_heap` supplies heap replay for ordinary structured
small-step traces. `PairParStepsPhi_run_split_replays_heap` and
`PairParStepsPhi_checked_replays_heap` now replay the successful checked
computation as a branch-parallel `Phi_Par` phase followed by the continuation
trace. `PairParBranchReplayWitness` records the independent branch replay
premises needed for heap joining, and
`PairParStepsPhi_checked_branch_replay_join` combines those premises with the
checked run to invoke `TcHeap_Extended_PhiPar`.
`SmallStepStructuredReplay.v` derives the trace-disjointness side from
`phi ⋞ theta` plus `Disjointness`, and exposes
`PairParStepsPhi_checked_pass_sound_branch_steps_join` for independent branch
`StepsPhi` runs. The structured layer also exposes
`pairpar_check_pass_steps_phi_to_sequential`,
`pairpar_check_fail_steps_phi_to_fallback`,
`PairParCheckedStructuredStepsPhi_source_check_dispatch`, and
`PairParFallbackStructuredStepsPhi_erases_from_check_state`, which pin down the
ordinary source check-state prefix for successful and failed checks.
`StepsPhi_initial_terminal_continue` and
`PairParSequentialEffectSummaryStepsPhi_source_pass_prefix`/
`PairParSequentialEffectSummaryStepsPhi_source_fail_prefix` now connect the
source-initial `Pair_Par` effect-summary phase to the ordinary sequential start,
using a sequential-summary relation whose second summary starts from the first
summary's heap. `Phi_Static_Effect` and `Phi_Static_Effect_sound`, defined in
`EffectFacts.v`, compute a precise static-action envelope for any structured
dynamic trace and prove that the trace is sound with respect to that envelope.
`Phi_Static_Effect_least` and
`Epsilon_Phi_Soundness_iff_phi_static_included` show that this envelope is the
least static effect that can justify the trace. `StepsPhi_trace_static_sound`
exposes that fact at the small-step run level. `fold_subst_rgn_mk_rgn_type_find_R`
and the `Epsilon_Phi_Soundness_*_find_R` lemmas connect concrete runtime
region lookup to the folded singleton allocation/read/write effects emitted by
the dynamic frames. `SmallStepEffectSoundness.v` now introduces
`WTKontEffect` and `WTStateEffectAt`, an effect-budgeted refinement of the
existing runtime typing, plus forget/initial lemmas, dynamic-label budget
lemmas for allocation/read/write continuation frames, and
`WTStateEffectAt_*_step_budget` lemmas for all ordinary `Step` constructors,
including closure-entry/body cases and `Pair_Par` checked/fallback frames.
`WTStateEffectAt_step_budget` assembles the one-step theorem, and
`WTStateEffectAt_steps_budget` lifts it to finite `Steps` prefixes by bounding
`Phi_Static_Effect (trace_as_phi trace)` plus the residual state budget by the
original declared budget. `WTStateEffectAt_initial_steps_budget`,
`WTStateEffectAt_initial_terminal_trace_budget`, and
`WTStateEffectAt_initial_effect_terminal_trace_budget` specialize this to
initial states, terminal runs, and terminating effect-summary expressions.
`small_step_eff_sound` gives the old-style `Epsilon_Phi_Soundness` conclusion
for terminal small-step runs, and `small_step_effect_summary_eff_sound`
specializes it to effect-summary expressions.
`SmallStepCorrectness.v` composes that theorem with the structured replay
layer. Its normalization lemmas relate branch-shaped `Phi` traces to
`trace_as_phi (phi_as_list phi)`, and
`Phi_Theta_Soundness_of_trace_as_phi_phi_as_list` transports computed-summary
soundness back from the normalized list trace to the branch-shaped trace.
`ReadOnlyPhi_trace_as_phi_phi_as_list` transports read-only evidence in the
other direction when a normalized trace is needed.
`PairParSequentialEffectSummaryStepsPhi_first_small_step_sound` derives the
first summary trace's `Epsilon_Phi_Soundness` directly from typing plus the
small-step run. `StepsPhi_effect_summary_readonly_from_small_step_sound` and
`StepsPhi_effect_summary_heap_neutral_from_small_step_sound` prove the
read-only/heap-neutrality bridge for terminating typed effect-summary runs.
The pass/fail wrappers
`PairParSequentialEffectSummaryStepsPhi_source_pass_small_step_sound_prefix`
and
`PairParSequentialEffectSummaryStepsPhi_source_fail_small_step_sound_prefix`
then recover the source-prefix/independent-summary bridge without assuming the
old big-step soundness premise.
`Soundness/SmallStepCorrectnessBridge.v` records the current correctness
boundary explicitly: `small_step_structured_correctness_from_big_step_traces`
and `small_step_list_correctness_from_big_step_traces` transfer the old
`BackTriangle` correctness theorem to terminal small-step runs once matching
big-step traces are supplied. These are bridge theorems, not adequacy theorems.
`small_step_structured_correctness_from_big_step_normalized_traces` additionally
handles the common case where the supplied big-step trace is
`trace_as_phi (phi_as_list phi)` for the structured small-step trace `phi`.
`Soundness/SmallStepCorrectnessDirect.v` starts the direct small-step port of
`Correctness_soundness_ext`: it proves the reusable empty-trace soundness fact
and the direct pure terminal cases for constants, booleans, variables, function
values, and region lambdas over `StepsPhi`. It also proves the direct `Top`
summary case corresponding to `BT_Top_Approx`, without appealing to big-step
adequacy. `StepsPhi_terminal_inv_step` is the first terminal-run inversion
helper: it peels a deterministic first step from a terminal structured run and
recovers the tail run plus trace equation.
`StepsPhi_append_kont_terminal_decompose` and
`StepsPhi_initial_with_kont_terminal_decompose` are the converse of the
continuation replay lemmas: a terminal run under an appended continuation
contains a terminal run of the focused `KDone` computation plus the remaining
continuation run. These lemmas are the main bridge for eliminating the old
second computation evaluation from the direct small-step induction. The same
file now contains the first
conditional composition lemmas:
terminal guard and selected-branch `StepsPhi` runs can be replayed as a
terminal `Cond` run, and the empty-guard plus branch-soundness premises compose
to soundness for the condition trace. The summary-terminal true/false wrappers
use determinism to identify the final theta of `Cond e efft efff` with the
selected branch-summary theta before proving the computational condition trace
sound. The strict binary operators `Plus`,
`Minus`, `Times`, and `Eq` now have the analogous replay and composed
soundness packages, including union-shaped variants where the left trace is
sound for `theta1`, the right trace is sound for `theta2`, and the whole
operator trace is sound for `Union_Theta theta1 theta2`. The projection lemmas
`StepsPhi_{plus,minus,times,eq}_terminal_decompose` recover the two numeric
operand runs from a single terminal binary-operator run, which is the
computation-side counterpart to the no-second-evaluation plan.
`StepsPhi_concat_summary_terminal_theta` identifies the theta produced by an
actual terminal `Concat` summary run. `StepsPhi_concat_terminal_decompose` and
`StepsPhi_concat_effect_terminal_decompose` now also recover the two component
summary runs from a terminal `Concat` run. The
`Correctness_soundness_ext_small_step_{plus,minus,times,eq}_summary_terminal_case`
wrappers state the four binary computational cases directly against that
terminal summary theta. The stronger
`Correctness_soundness_ext_small_step_{plus,minus,times,eq}_summary_terminal_direct_case`
theorems now take only the whole binary computation run and whole `Concat`
summary run, decompose both internally, use read-only heap neutrality for the
left operand, and pass the recovered branch runs to the recursive premises.
`StepsPhi_cond_terminal_decompose` and
`Correctness_soundness_ext_small_step_cond_summary_terminal_direct_case` provide
the same no-second-evaluation shape for conditionals: both terminal `Cond`
runs are decomposed, mismatched guard branches are ruled out by terminal
determinism, and read-only guard execution aligns the selected branch heaps.
The effect-summary
primitives `AllocAbs`, `ReadAbs`,
`WriteAbs`, `ReadConc`, `WriteConc`, and `Concat` now have terminal replay
facts, singleton dynamic-action soundness lemmas, and a composed `Concat`
soundness package. `StepsPhi_readconc_terminal_from_arg` and
`StepsPhi_writeconc_terminal_from_arg` extract the concrete singleton summary
computed by terminal `ReadConc`/`WriteConc` runs. The abstract reference
wrappers also consume terminal `AllocAbs`/`ReadAbs`/`WriteAbs` summaries via
the existing primitive terminal facts. The computational reference
forms `Ref`, `DeRef`, and
`Assign` now have labelled continuation replay lemmas and composed direct
soundness packages for abstract and concrete reference summaries, including
summary-terminal cases that use the extracted singleton theta.
`StepsPhi_right_nested_concat_summary_terminal_theta` plus the
`Correctness_soundness_ext_small_step_{ref_abs,deref_abs,assign_abs}_bt_summary_terminal_case`
wrappers now cover the actual abstract-reference `BackTriangle` summary shapes
`eff ⊕ AllocAbs`, `eff ⊕ ReadAbs`, and `eff1 ⊕ (eff2 ⊕ WriteAbs)` against
the terminal theta of the full summary expression. The concrete assignment
shape `eff1 ⊕ (eff2 ⊕ WriteConc ea)` is covered by
`Correctness_soundness_ext_small_step_assign_conc_bt_summary_readonly_terminal_case`;
its two preceding summary components are required to be `ReadOnlyPhi`, so their
small-step summary runs are heap-neutral before the final concrete write
summary is matched.
`StepsPhi_ref_terminal_decompose` and `StepsPhi_deref_terminal_decompose`
recover the argument run, heap/action witnesses, final value, and emitted
singleton action from terminal `Ref` and `DeRef` runs.
`Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_direct_case`,
`Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_direct_case`,
and `Correctness_soundness_ext_small_step_deref_conc_summary_terminal_direct_case`
use those decomposers to remove externally supplied argument runs from the
allocation/read cases.
`Correctness_soundness_ext_small_step_terminal_transfer` uses structured
terminal determinism to transport soundness from those canonical replay runs to
any terminal run from the same starting state. The conditional, strict binary,
summary-concat, binary summary-terminal, and reference cases now have corresponding `_terminal_case`
theorems that expose this arbitrary-terminal form directly. `Mu_App`,
`Eff_App`, and `Rgn_App` now also have structured replay lemmas, composed
soundness wrappers, arbitrary-terminal wrappers, and summary-terminal bridges:
`Correctness_soundness_ext_small_step_mu_app_summary_terminal_case` consumes an
actual terminal `Eff_App` summary run, while
`Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_case`
consumes the terminal `Empty` summary for region application. These application
lemmas still take component-run soundness as premises; the remaining work is to
connect those premises to the full `BackTriangle` induction and
typing/read-only obligations. The staged ordinary `Pair_Par` path now has the
same treatment:
`StepsPhi_pair_par_from_components` replays the two effect-summary runs and two
computation runs through the single check/fallback transition, while the
pass/fallback composed and `_terminal_case` theorems join the four component
soundness premises under
`Union_Theta (Union_Theta theta1 theta2) (Union_Theta theta_mu1 theta_mu2)`.
`Correctness_soundness_ext_small_step_pair_par_checked_composed_case` and
`Correctness_soundness_ext_small_step_pair_par_checked_terminal_case` package
the two branches behind the existing `PairParCheckDecidable` assumption. The
derived `Correctness_soundness_ext_small_step_pair_par_same_summary_*` theorems
cover the closer paper-facing shape where both computation branches are sound
against the same two thetas computed by the effect-summary phase, yielding the
smaller summary `Union_Theta theta1 theta2`. The
`Correctness_soundness_ext_small_step_pair_par_same_summary_readonly_terminal_case`
and
`Correctness_soundness_ext_small_step_pair_par_same_summary_static_readonly_terminal_case`
variants use read-only summary traces, or static read-only evidence plus
`Epsilon_Phi_Soundness`, to rewrite the staged summary heaps back to the source
heap before applying the checked terminal theorem.
`Correctness_soundness_ext_small_step_pair_par_same_summary_sequential_readonly_terminal_case`
is the same result phrased over the structured
`PairParSequentialEffectSummaryStepsPhi` summary witness.
`Correctness_soundness_ext_small_step_pair_par_same_summary_typed_readonly_terminal_case`
removes the explicit `Epsilon_Phi_Soundness` premises by deriving both
summary-trace read-only facts from typed small-step effect soundness.
`StepsPhi_nested_concat_summary_terminal_theta` and
`Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_case` cover
the actual four-part `BT_Pair_Par` summary shape
`(eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)`, identifying the terminal theta of that nested
summary expression before applying the checked `Pair_Par` terminal machinery.
`theories/Soundness/SmallStepBackTriangle.v` defines the small-step
paper-facing summary relation `SmallStepBackTriangle`. It has constructors for
all expression forms and canonicalizes the `Pair_Par` summary to use the two
checked `Eff_App` summaries for the computation branches. The erasure theorem
`SmallStepBackTriangle_as_BackTriangle` keeps compatibility with the archived
relation.
`theories/Soundness/SmallStepPaperSoundness.v` exports the closed paper-facing
correctness statement `PaperPairParCheckedStructuredTerminalCorrectness`. This
statement has the ordinary typing and terminal-run hypotheses, but it no longer
exports a bounded induction package or any auxiliary heap-agreement premise.

The lower-level files still keep diagnostic lemmas for individual constructors,
summary replay, counted decompositions, and the old unaugmented application
summary path. Those lemmas are implementation support for the direct induction,
not the public story. `SmallStepFallback.v` is intentionally focused on
fallback occurrence and no-fallback conversion lemmas, while
`SmallStepCorrectnessDirect.v` contains the large canonical correctness
dispatcher. What remains postponed is terminal small-step/terminating-evaluator
adequacy.
The direct application-summary port now includes
`Correctness_soundness_ext_small_step_mu_app_summary_terminal_direct_case`,
which decomposes the
terminal `Mu_App ef ea` and `Eff_App ef ea` runs, uses terminal determinism to
align the shared function and argument evaluations, and delegates only the body
summary to the recursive correctness premise. The direct region-application
case
`Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_direct_case`
decomposes a terminal `Rgn_App er w` run and matches it against the terminal
`Empty` summary. `StepsPhi_pair_par_after_check_terminal_decompose` and
`StepsPhi_pair_par_terminal_decompose` are now the corresponding terminal
decomposition tools for `Pair_Par`: they recover the two effect-summary runs,
the check/fallback boundary, both computation runs, the final pair value, and
the four-part trace equation from one terminal `Pair_Par` execution.
`Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_direct_case`
uses those decompositions plus the nested-summary decomposition to prove the
four-part `BT_Pair_Par` summary theorem directly over the actual terminal
`Pair_Par` and nested-summary runs; unlike the older premise-driven alias, it
does not need `PairParCheckDecidable`.
The public paper-facing layer now points at the closed structured terminal
theorem. The direct correctness file keeps the implementation support local:
terminal decompositions, read-only trace stability, and constructor-specific
facts used to assemble the exported statement.
`StepsPhi_readonly_preserves_heap`,
`StepsPhi_readonly_static_effect_preserves_heap`, and
`pairpar_effect_summary_steps_phi_heap_neutral` prove the expected read-only
heap-neutrality bridge. `PairParSequentialEffectSummaryStepsPhi_readonly_heap_neutral`
packages the same fact for the two-stage sequential `Pair_Par` summary phase,
showing both summary heaps are the original source heap when both summary traces
are read-only.
`PairParSequentialEffectSummaryStepsPhi_readonly_from_small_step_sound` and
`PairParSequentialEffectSummaryStepsPhi_readonly_heap_neutral_from_small_step_sound`
are the corresponding typed runtime wrappers, while
`PairParSequentialEffectSummaryStepsPhi_source_pass_independent_prefix` and
`PairParSequentialEffectSummaryStepsPhi_source_fail_independent_prefix` combine
the source prefix with the independent summary witness when the first summary
trace is read-only. The old big-step proof pattern is now exposed through
`effect_summary_trace_readonly_from_static_soundness`,
`pairpar_effect_summary_steps_phi_readonly_from_static_soundness`, and the
`PairParSequentialEffectSummaryStepsPhi_source_*_static_sound_prefix` theorems:
static read-only plus `Epsilon_Phi_Soundness` yields the read-only premise. The
`PairPar_source_static_summary_checked_branch_join_exists` theorem then packages
that source summary prefix with the checked computation branch replay/join.
`PairParSequentialEffectSummaryStepsPhi_source_*_trace_static_prefix` and
`PairPar_source_trace_static_summary_checked_branch_join_exists` give the same
staging result using `ReadOnlyStatic (Phi_Static_Effect phi_eff1)`.
`PairParSequentialEffectSummaryStepsPhi_source_*_static_included_prefix` and
`PairPar_source_static_included_summary_checked_branch_join_exists` give the
declared-effect-inclusion version. The next adequacy-side gap is proving
`Included StaticAction (Phi_Static_Effect phi) (fold_subst_eps rho static_eff)`
from static typing. `WTStateEffectAt_steps_budget` now provides the ordinary
finite-prefix budget skeleton that this future theorem should feed.
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
