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
facts for that relation: heap agreement is preserved by one step and finite
traces, interleaving traces compose, and the checked initial state can start by
stepping either branch. The explicit-store ordinary preservation layer is split
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
`PaperPairParCheckedOrFallbackTraceSafety`, and
`PaperPairParCheckedOrFallbackTerminalSoundness`.
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
heap-agreement and eval-head readiness assumptions. The stricter abstract-effect
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
heap agreement, and not-stuckness for any finite checked interleaving trace.
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
branch heap agreement, and not-stuckness. `SmallStepParallelCheckedTerminal.v`
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
`PaperPairParCheckedOrFallbackTraceSafety`, and
`PaperPairParCheckedOrFallbackTerminalSoundness`.
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
original declared budget.
`StepsPhi_readonly_preserves_heap`,
`StepsPhi_readonly_static_effect_preserves_heap`, and
`pairpar_effect_summary_steps_phi_heap_neutral` prove the expected read-only
heap-neutrality bridge, while
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
