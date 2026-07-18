# SurfaceEffects Mechanization Report

This report summarizes the current mechanized proof state, with emphasis on the
recent removal of admitted/axiomatic gaps, the small-step runtime layer, and the
reviewer-facing `Pair_Par` check/fallback story.

## Executive Summary

The project now builds under Rocq 9.1.1 with no source-level `Axiom` or
`Admitted` declarations in `theories/`.

The paper-facing semantics is now the small-step continuation machine. It
supports finite-prefix reasoning for both terminating and diverging executions,
plus terminal theorems for completed runs. The archived big-step files remain
in the repository for comparison and future adequacy work, but they are no
longer presented as the paper semantics.

The most important reviewer-facing addition is
`theories/Runtime/SmallStepPaperTheorems.v`, which gives stable theorem names
for the paper. The underlying staged-check development lives in
`theories/Runtime/SmallStepSequentialSoundness.v` and exposes the dynamic
effect check explicitly:

- if the check succeeds, the checked interleaving semantics is available and is
  trace-safe;
- if the check fails, the ordinary sequential fallback path is taken and is
  trace-safe;
- `pairpar_check_decidable_trace_safe` packages this success/failure split in a
  single theorem;
- `pairpar_check_decidable_terminal_value` adds the terminal-value extractor for
  both checked and fallback outcomes.

The paper-facing wrappers are:

- `PaperSmallStepFinitePrefixSafety`;
- `PaperSmallStepTerminalSoundness`;
- `PaperPairParCheckedOrFallbackTraceSafety`;
- `PaperPairParCheckedOrFallbackTerminalSoundness`.

These are stable theorem-map names for the mechanization notes. The revised
paper states the corresponding results only in mathematical notation, without
using Coq theorem names in the prose.

This is intentionally not a full observational-equivalence theorem between two
distinct syntactic tuple rules. The mechanized language still has only
`Pair_Par`, not separate `[E-PAR]` and `[E-SEQ]` tuple constructors. The current
result is therefore the right statement for the present calculus: one staged
construct dispatches to a checked interleaving target or to the sequential
fallback path.

## Build And Trust Status

Current local toolchain:

```text
The Rocq Prover, version 9.1.1
compiled with OCaml 4.14.2
```

Current verification command:

```sh
make
```

Current trust status:

- no `Admitted` in `theories/*.v`;
- no source-level `Axiom` in `theories/*.v`;
- `Definitions/Axioms.v` is no longer part of `_CoqProject`;
- known Rocq 9 notation/import warnings remain, but do not block compilation.

## Source Organization

The runtime proof stack is now stratified into explicit dependency layers:

- `SmallStep.v`: sequential continuation machine with labels.
- `SmallStepFacts.v`: generic state/step facts.
- `SmallStepParallel.v`: checked interleaving target relation.
- `SmallStepProgressBase.v`, `SmallStepReturnProgress.v`,
  `SmallStepEvalProgress.v`, `SmallStepRuntimeProgress.v`: progress and
  runtime-shape foundations.
- `SmallStepRuntimeSubstShape.v`, `SmallStepRuntimeHeapShape.v`,
  `SmallStepRuntimeKontTyping.v`, `SmallStepRuntimeStateShape.v`: runtime
  preservation foundations.
- `SmallStepPreservation*.v`: ordinary hidden-store preservation.
- `SmallStepExplicitStore*.v`: explicit-store preservation indexed by final
  store typings.
- `SmallStepTraceSafety.v`: ordinary finite-prefix trace safety.
- `SmallStepParallel*.v`: checked interleaving preservation, progress, safety,
  trace safety, and terminal extraction.
- `SmallStepSequentialSoundness.v`: staged `Pair_Par` dispatch and
  success/failure trace-safety theorem surface.
- `SmallStepStructuredTrace.v`: adequacy-oriented `Phi` trace instrumentation,
  including branch-structured effect-summary traces.
- `SmallStepEffectSoundness.v`: effect-budgeted continuation/state invariant
  for the future small-step static-effect soundness theorem.
- `SmallStepCorrectness.v`: composition layer that derives structured
  checked `Pair_Par` source-prefix correctness from the small-step
  effect-summary soundness theorem.
- `SmallStepPaperTheorems.v`: stable theorem names for paper citations.
- `Determinism/SmallStepStructuredReplay.v`: theta-soundness bridge from
  checked-disjoint surface summaries to branch replay/join witnesses.
- `Soundness/SmallStepCorrectnessBridge.v`: explicit bridge from matched
  terminal small-step traces plus corresponding big-step traces to the old
  `BackTriangle` correctness theorem.
- `Soundness/SmallStepCorrectnessDirect.v`: beginning of the direct small-step
  port of `Correctness_soundness_ext`. It now includes direct terminal cases
  for pure expressions, conditionals, arithmetic, reference/read/write
- summaries, application summaries, and canonical `Pair_Par` summaries. The
  current paper-facing summary relation is `SmallStepBackTriangle`, defined in
  `Soundness/SmallStepBackTriangle.v`; it has constructors for every expression
  form and canonicalizes the `Pair_Par` branch summaries to the corresponding
  `Eff_App` expressions. The bridge lemma
  `SmallStepBackTriangle_as_BackTriangle` shows compatibility with the archived
  relation.
  The first native coverage lemmas over this relation are now in place for
  `Concat`, `ReadConc`, `WriteConc`, abstract allocation/read summaries,
  abstract assignment summaries, and concrete assignment summaries:
  `Correctness_soundness_ext_small_step_concat_summary_coverage_runtime_canonical_nofallback_below_case`,
  `Correctness_soundness_ext_small_step_readconc_summary_coverage_runtime_canonical_nofallback_below_case`,
  `Correctness_soundness_ext_small_step_writeconc_summary_coverage_runtime_canonical_nofallback_below_case`,
  `Correctness_soundness_ext_small_step_ref_abs_summary_coverage_runtime_canonical_nofallback_below_case`,
  `Correctness_soundness_ext_small_step_deref_abs_summary_coverage_runtime_canonical_nofallback_below_case`,
  `Correctness_soundness_ext_small_step_assign_abs_summary_coverage_runtime_canonical_nofallback_below_case`,
  and
  `Correctness_soundness_ext_small_step_assign_conc_summary_coverage_runtime_canonical_nofallback_below_case`.
  The concrete-assignment proof uses the previously computed `eff1` summary to
  cover the internal `e1` trace that is re-run by `WriteConc e1`.
  The older premise-oriented checkpoints remain as internal implementation
  support. The paper-facing layer now exports the closed
  `PaperPairParCheckedStructuredTerminalCorrectness` theorem, while
  `SmallStepBackTriangle` records the canonical all-constructor summary
  relation used for the small-step proof story.
  The helper
  `NoPairParFallback_initial_child_from_step` is the first porting lemma for
  that induction: after a parent step enters a child expression under a
  continuation, parent-level no-fallback implies no-fallback for the child's
  initial terminal run. The bounded companion
  `StepsPhiN_child_from_initial_step_terminal_decompose_no_fallback` packages
  the smaller child count together with the inherited no-fallback fact. The
  direct Pair_Par checkpoint
  `Correctness_soundness_ext_small_step_pair_par_canonical_eff_app_backtriangle_no_fallback_structured_below_case`
  eliminates the failed-check branch using an actual fallback occurrence,
  rather than assuming branch-summary replay.
- `Soundness/SmallStepFallback.v`: connects a failed `Pair_Par` check witness
  to an actual sequential fallback transition occurring inside the terminal
  small-step run.

The facade modules remain for stable imports, but non-facade runtime files now
avoid importing the broad facades directly.

## Current Boundary

The older big-step semantics proves properties only for evaluations that
terminate. That is expected: a big-step judgment relates an initial
configuration directly to a final value/heap/trace, so there is no finite
intermediate state to inspect for a diverging run.

The small-step layer fixes that proof-shape limitation. Its main safety
statements are finite-prefix properties: for every finite sequence of steps, the
reached state remains well typed, not stuck, and its emitted trace is well typed
against the final store typing. This is the form needed to discuss executions
that may continue forever.

## Operational Structure Of `Pair_Par`

The small-step rule for `Pair_Par ef1 ea1 ef2 ea2` is staged.

1. Evaluate `Eff_App ef1 ea1` to a first surface-effect summary `theta1`.
2. Evaluate `Eff_App ef2 ea2` to a second summary `theta2`.
3. Check:

   ```coq
   Disjointness theta1 theta2 /\ ~ Conflictness theta1 theta2
   ```

4. If the check succeeds, the ordinary continuation machine steps into the
   first computational application:

   ```coq
   Mu_App ef1 ea1
   ```

   The separate checked interleaving target is represented by
   `pairpar_checked_initial`, which runs the two computational applications as
   independent branch states under `PairParStep`.

5. If the check fails, the ordinary continuation machine steps into the same
   first computational application, but this is interpreted as the sequential
   fallback path. The second computational application is evaluated afterward
   through the `KPairParMu1`/`KPairParMu2` continuation frames.

This matches the current calculus: there is one staged `Pair_Par` construct,
not two separate source constructs.

## Main Theorem Map

### Ordinary Small-Step Preservation

File: `theories/Runtime/SmallStepPreservationTheorems.v`

- `WTStateRuntimeHeapShape_step_preservation`
  proves one-step preservation for the hidden-store runtime shape.

- `WTStateRuntimeHeapShape_steps_preservation`
  lifts preservation to finite ordinary `Steps`.

- `WTStateRuntimeHeapShape_not_stuck`
  proves not-stuckness for runtime-shaped states, assuming the dynamic
  pair-check decision principle `PairParCheckDecidable`.

### Explicit-Store Preservation

File: `theories/Runtime/SmallStepExplicitStoreTheorems.v`

- `WTStateRuntimeHeapShapeAt_step_preservation`
  proves explicit-store one-step preservation. The result produces a new store
  typing `stty'`, proves `StoreExtends stty stty'`, and re-establishes heap
  typing/heap shape at the reached state.

This theorem is the bridge needed for trace typing, because allocation can
extend the store and writes depend on final heap/store consistency.

### Ordinary Trace Safety

File: `theories/Runtime/SmallStepTraceSafety.v`

- `WTStateRuntimeHeapShapeAt_steps_trace_typed`
  proves that finite ordinary `Steps` preserve explicit runtime typing and
  produce a trace satisfying `TcPhi` at the final store typing.

- `StateTraceSafeAt`
  packages finite-prefix safety as a reusable predicate.

- `WTStateRuntimeHeapShapeAt_trace_safe_typed`
  proves `StateTraceSafeAt` for any explicitly well-typed state.

- `StateTraceSafeAt_terminal_value`
  extracts final heap typing, value typing, runtime value shape, and trace
  typing from a terminal ordinary execution.

### Checked Interleaving Preservation

Files:

- `theories/Runtime/SmallStepParallelTyping.v`
- `theories/Runtime/SmallStepParallelStepPreservation.v`

Key predicates and theorems:

- `WTPairParStateRuntimeHeapShapeAtStrong`
  is the strong typed invariant for checked interleaving states.

- `WTPairParStateRuntimeHeapShapeAtStrong_step_preservation`
  proves one checked-interleaving step preserves the strong invariant.

- `WTPairParStateRuntimeHeapShapeAtStrong_steps_preservation`
  lifts that result to finite checked-interleaving traces.

The checked interleaving semantics synchronizes branch heaps after each branch
step using `with_state_heap`, and the preservation proof retypes the idle
branch under the active branch's new heap/store.

### Checked Interleaving Progress And Safety

Files:

- `theories/Runtime/SmallStepParallelProgress.v`
- `theories/Runtime/SmallStepParallelSafety.v`

Important theorems:

- `WTPairParStateRuntimeHeapShapeAtStrong_never_stuck_typed`
  proves never-stuckness for finite prefixes of checked interleavings.

- `pairpar_checked_initial_steps_safety`
  packages preservation, store extension, branch heap synchronization, and
  not-stuckness for any finite checked-interleaving execution.

- `pairpar_checked_initial_kdone_terminal_pair`
  extracts the final pair value and component typing for `KDone`.

### Checked Interleaving Trace Safety

Files:

- `theories/Runtime/SmallStepParallelTraceTyping.v`
- `theories/Runtime/SmallStepParallelTraceSafe.v`
- `theories/Runtime/SmallStepParallelCheckedTraceSafety.v`
- `theories/Runtime/SmallStepParallelCheckedTerminal.v`

Important theorems:

- `WTPairParStateRuntimeHeapShapeAtStrong_steps_trace_typed`
  proves checked-interleaving finite traces satisfy `TcPhi` at the final store.

- `PairParTraceSafeAt`
  packages checked finite-prefix trace safety.

- `pairpar_checked_initial_steps_safety_with_trace`
  combines checked preservation, store extension, branch heap synchronization,
  not-stuckness, and trace typing.

- `pairpar_checked_initial_kdone_terminal_pair_with_trace`
  extracts a terminal pair value with component typing and trace evidence.

### Staged Check And Sequential Fallback

File: `theories/Runtime/SmallStepSequentialSoundness.v`

Definitions:

- `PairParCheckPass theta1 theta2`
  abbreviates `Disjointness theta1 theta2 /\ ~ Conflictness theta1 theta2`.

- `PairParCheckFail theta1 theta2`
  is the negation of `PairParCheckPass theta1 theta2`.

- `pairpar_check_state`
  names the ordinary machine state immediately after the second effect summary
  has been computed.

- `pairpar_sequential_start`
  names the ordinary sequential fallback target.

- `pairpar_checked_start`
  names the separate checked interleaving target.

Important theorems:

- `pairpar_check_pass_dispatch`
  proves that a successful check has the ordinary step into the first
  computational application and exposes the checked interleaving start.

- `pairpar_check_fail_dispatch`
  proves that a failed check steps to the sequential fallback start.

- `pairpar_check_decidable_dispatch`
  splits on the check result and exposes the corresponding dispatch fact.

- `pairpar_check_state_typed`
  proves that the check state is explicitly well typed from the source typing
  assumptions.

- `pairpar_check_fail_sequential_preservation`
  proves the failed-check sequential target preserves explicit runtime typing.

- `pairpar_check_fail_sequential_trace_safe`
  proves that the failed-check sequential fallback is ordinary finite-prefix
  trace-safe.

- `pairpar_check_pass_checked_trace_safe`
  proves that the successful checked branch is checked-interleaving trace-safe.

- `pairpar_check_decidable_trace_safe`
  packages the final reviewer-facing split:

  - pass case: `PairParTraceSafeAt` for the checked interleaving target;
  - fail case: `StateTraceSafeAt` for the sequential fallback target.

- `pairpar_check_decidable_terminal_value`
  strengthens the split for terminating runs:

  - pass case: every terminal checked interleaving result has an extended store
    typing, typed final heap, runtime heap shape, typed final value, runtime
    value shape, and typed trace;
  - fail case: every terminal ordinary fallback result has the same final heap,
    value, and trace evidence, with store extension composed through the
    failed-check step.

### Paper-Facing Small-Step Theorems

File: `theories/Runtime/SmallStepPaperTheorems.v`

These are thin wrappers around the theorem stack above. They introduce no new
semantic commitments; their purpose is to give the paper stable names that do
not depend on internal proof-stratification filenames.

- `PaperSmallStepFinitePrefixSafety`
  wraps `initial_state_steps_safety_with_trace`.

- `PaperSmallStepTerminalSoundness`
  wraps `initial_state_terminal_value_with_trace`.

- `PaperPairParCheckedOrFallbackTraceSafety`
  wraps `pairpar_check_decidable_trace_safe`.

- `PaperPairParCheckedOrFallbackTerminalSoundness`
  wraps `pairpar_check_decidable_terminal_value`.

## Proof Explanation: `pairpar_check_decidable_trace_safe`

The theorem assumes source typing for the two computational applications:

```coq
TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1)
TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2)
```

It also assumes a typed heap, runtime heap shape, typed environment, runtime
environment shape, and a typed outer continuation.

The proof proceeds by destructing `PairParCheckDecidable theta1 theta2`.

In the pass case:

1. The hypothesis is `PairParCheckPass theta1 theta2`.
2. The theorem calls `pairpar_check_pass_checked_trace_safe`.
3. That theorem builds the strong checked interleaving invariant with
   `WTPairParStateRuntimeHeapShapeAtStrong_checked_initial`.
4. Heap agreement follows from `pairpar_checked_initial_heaps_agree`.
5. Checked finite-prefix trace safety follows from
   `WTPairParStateRuntimeHeapShapeAtStrong_trace_safe_typed`.

In the fail case:

1. The hypothesis is `PairParCheckFail theta1 theta2`.
2. `pairpar_check_state_typed` proves the ordinary check state is explicitly
   well typed.
3. `pairpar_check_fails_to_sequential_start` gives the concrete small-step rule
   to the sequential fallback target.
4. `WTStateRuntimeHeapShapeAt_step_preservation` preserves explicit typing for
   that one failed-check step.
5. `WTStateRuntimeHeapShapeAt_trace_safe_typed` gives ordinary finite-prefix
   trace safety from the sequential fallback target.

Thus the result does not merely say that the staged machine is deterministic or
that two evaluations agree. It states the actual dispatch behavior of the
current syntax.

The companion theorem `pairpar_check_decidable_terminal_value` reuses this
trace-safety split and applies the generic terminal extractors. In the
successful branch it calls `PairParTraceSafeAt_terminal_value`; in the failed
branch it calls `StateTraceSafeAt_terminal_value` and composes the store
extension produced by the failed-check step with the store extension produced by
the fallback run.

### Structured Traces For Future Adequacy

File: `theories/Runtime/SmallStepStructuredTrace.v`

This layer is additive. It does not replace the current list-trace safety stack
and it does not prove small-step/big-step adequacy. Its purpose is to give the
small-step development a trace vocabulary with the same shape needed by the
big-step `Pair_Par` rule.

Important definitions and theorems:

- `StepsPhi`
  is the ordinary small-step finite-prefix relation indexed directly by a
  structured `Phi` trace rather than by `list DynamicAction`.

- `Phi_Static_Effect` and `Phi_Static_Effect_sound`
  live in `theories/Meta/EffectFacts.v`. They compute a precise static-action
  envelope for any structured dynamic trace and prove that the trace is sound
  with respect to that envelope.

- `Phi_Static_Effect_least` and
  `Epsilon_Phi_Soundness_iff_phi_static_included`
  prove that this envelope is the least static effect that can justify the
  trace. Consequently, the remaining declared-effect goal can be stated as an
  inclusion:
  `Included StaticAction (Phi_Static_Effect phi) (fold_subst_eps rho static_eff)`.

- `fold_dist_union`, `fold_subst_rgn_mk_rgn_type_find_R`, and the
  `Epsilon_Phi_Soundness_*_find_R` lemmas live in
  `theories/Meta/EffectFacts.v`. They connect a runtime region lookup
  `find_R w rho = Some r` to the folded singleton static effects for
  allocation, read, and write labels. These are the per-frame facts needed by
  the `WTKontEffect` continuation budget invariant.

- `label_phi_static_sound` and `StepsPhi_trace_static_sound`
  expose the same self-soundness property at the small-step label and
  structured-run levels.

- `WTKontEffect` and `WTStateEffectAt`
  live in `theories/Runtime/SmallStepEffectSoundness.v`. They refine the
  existing runtime continuation/state typing with an explicit static-effect
  budget.

- `terminal_steps_refl`, `steps_terminal_state_deterministic`, and
  `Steps_terminal_deterministic`
  live in `theories/Runtime/SmallStepFacts.v`. They lift one-step determinism
  of `Step` to terminal ordinary `Steps` runs: if two runs from the same state
  both terminate, their traces, final heaps, and final values coincide.
  `PaperSmallStepTerminalDeterminism` is the stable paper-facing alias.

- `SmallStepDynamicDeterminism_ext` and `SmallStepDeterminism`
  live in `theories/Determinism/SmallStepDeterminismExt.v`. They are the
  small-step analogues of `DynamicDeterminism_ext` and `Determinism`: two
  terminating small-step evaluations of the same well-typed expression, from
  equivalent starting heaps, finish with equivalent heaps, equal values, and
  equal emitted traces. `SmallStepStructuredDynamicDeterminism_ext` and
  `SmallStepStructuredDeterminism` give the corresponding `StepsPhi` versions,
  with trace equality stated through `phi_as_list`.

- `StepsPhi_terminal_deterministic` and
  `StepsPhi_effect_terminal_deterministic`
  live in `theories/Runtime/SmallStepStructuredTrace.v`. They lift ordinary
  terminal determinism to structured `StepsPhi` runs. The trace equality is
  stated as equality of `phi_as_list`, not syntactic equality of `Phi`, because
  silent transitions may create different `Phi_Nil`/`Phi_Seq` shapes with the
  same emitted dynamic actions. The paper-facing aliases are
  `PaperSmallStepStructuredTerminalDeterminism` and
  `PaperSmallStepStructuredEffectTerminalDeterminism`.

- `WTKontEffect_forget`, `WTStateEffectAt_forget`, and
  `WTStateEffectAt_initial`
  prove that the effect-budgeted invariant is conservative over the existing
  explicit-store runtime typing and is available for initially typed states.

- `WTKontEffect_ref_done_label_included`,
  `WTKontEffect_deref_done_label_included`, and
  `WTKontEffect_assign_done_label_included`
  prove the first dynamic-label budget cases: allocation, read, and write
  labels emitted by continuation frames are included in the frame's static
  budget.

- `WTStateEffectAt_*_step_budget` lemmas cover all ordinary `Step`
  constructors, including closure-entry/body cases and `Pair_Par`
  checked/fallback frames. `WTStateEffectAt_step_budget` assembles the case
  library into a one-step static-effect budget theorem, and
  `WTStateEffectAt_steps_budget` lifts it to finite `Steps` prefixes:
  the static effect computed from `trace_as_phi trace` plus the residual
  state budget is included in the original declared budget.
  `WTStateEffectAt_initial_steps_budget` specializes this to initially typed
  expressions. `WTStateEffectAt_initial_terminal_trace_budget` removes the
  residual budget for terminal runs, and
  `WTStateEffectAt_initial_effect_terminal_trace_budget` specializes the result
  to terminating effect-summary expressions. `small_step_eff_sound` packages
  the inclusion result as the old-style `Epsilon_Phi_Soundness` conclusion for
  terminal small-step runs. `small_step_effect_summary_eff_sound` is the
  effect-summary-specific specialization.

- `SmallStepCorrectness.v`
  composes the effect-budget theorem with the branch-structured trace layer.
  `Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list` bridges the normalized
  list trace used by ordinary `Steps` and the branch-shaped `Phi` trace used by
  `StepsPhi`. `Phi_Theta_Soundness_of_trace_as_phi_phi_as_list` gives the
  analogous bridge for computed-summary soundness, and
  `ReadOnlyPhi_trace_as_phi_phi_as_list` carries read-only evidence to the
  normalized list trace when the old big-step theorem needs that shape.
  `PairParSequentialEffectSummaryStepsPhi_first_small_step_sound`
  derives the first effect-summary branch's `Epsilon_Phi_Soundness` from its
  typed terminating small-step execution.
  `StepsPhi_effect_summary_readonly_from_small_step_sound` and
  `StepsPhi_effect_summary_heap_neutral_from_small_step_sound` derive
  read-only traces and heap neutrality for typed terminating effect summaries
  from small-step soundness. The pass/fail wrappers
  `PairParSequentialEffectSummaryStepsPhi_source_pass_small_step_sound_prefix`
  and
  `PairParSequentialEffectSummaryStepsPhi_source_fail_small_step_sound_prefix`
  reuse the existing structured replay theorems without assuming a separate
  big-step soundness premise.

- `Soundness/SmallStepCorrectnessBridge.v`
  makes the remaining adequacy boundary explicit. The theorems
  `small_step_structured_correctness_from_big_step_traces` and
  `small_step_list_correctness_from_big_step_traces` prove that, if a terminal
  small-step run is accompanied by the corresponding big-step evaluation with
  the same trace, the existing `Correctness_soundness_ext` theorem yields
  `phi ⋞ theta`.
  `small_step_structured_correctness_from_big_step_normalized_traces` covers
  the more realistic structured case where the supplied big-step trace is
  `trace_as_phi (phi_as_list phi)` for the structured small-step trace `phi`.
  These theorems do not prove that every terminal small-step run has such a
  big-step counterpart.

- `Soundness/SmallStepCorrectnessDirect.v`
  starts the direct terminal small-step port of `Correctness_soundness_ext`.
  `StepsPhi_terminal_trace_nil_from_nil_steps` uses terminal determinism to
  show that a structured terminal run has an empty action list whenever a
  canonical empty-trace terminal run exists.
  `Correctness_soundness_ext_small_step_empty_trace` packages the reusable
  empty-trace soundness fact, and
  `StepsPhi_terminal_inv_step` gives the first decomposition helper for
  terminal structured runs: a deterministic first step can be peeled off while
  preserving the tail run and emitted trace equation.
  `StepsPhi_append_kont_terminal_decompose` and
  `StepsPhi_initial_with_kont_terminal_decompose` provide the converse
  direction for continuation replay: any terminal run under an appended
  continuation contains a terminal run of the focused `KDone` computation and
  the residual continuation run. This is the key new tool for the small-step
  correctness theorem without a second computation evaluation.
  `Correctness_soundness_ext_small_step_num_case`,
  `Correctness_soundness_ext_small_step_bool_case`,
  `Correctness_soundness_ext_small_step_var_case`,
  `Correctness_soundness_ext_small_step_var_typed_case`,
  `Correctness_soundness_ext_small_step_mu_abs_case`, and
  `Correctness_soundness_ext_small_step_rgn_abs_case` discharge the pure base
  cases directly over terminal `StepsPhi` runs.
  `Correctness_soundness_ext_small_step_top_summary_case` handles the
  `BT_Top_Approx` shape directly: a terminal `Top` summary run computes
  `Theta_Top`, so any structured body trace is sound.
  `StepsPhi_cond_true_from_guard_branch` and
  `StepsPhi_cond_false_from_guard_branch` compose terminal guard and selected
  branch runs into terminal `Cond` runs while preserving the concatenated
  action-list shape.
  `Correctness_soundness_ext_small_step_cond_join_case` is the corresponding
  soundness combinator: an empty-sound guard trace plus a branch trace sound
  for `theta` yields a condition trace sound for `theta`. The true/false
  composed variants package this replay plus soundness step, and the true/false
  terminal variants use structured terminal determinism to transfer that
  package to any terminal run from the same condition state.
  `StepsPhi_cond_true_summary_terminal_theta` and
  `StepsPhi_cond_false_summary_terminal_theta` identify the final theta of a
  terminal summary `Cond e efft efff` run with the selected branch-summary
  theta. The true/false summary-terminal wrappers then state the computational
  condition cases against that actual terminal summary theta.
  `StepsPhi_mu_app_from_fun_arg_body`,
  `StepsPhi_eff_app_from_fun_arg_body`, and
  `StepsPhi_rgn_app_from_fun_body` now provide the same branch-shaped replay
  spine for applications. The corresponding composed and terminal
  `Correctness_soundness_ext_small_step_*_app_*_case` theorems join component
  soundness premises and use terminal determinism to cover arbitrary terminal
  application executions.
  `Correctness_soundness_ext_small_step_mu_app_summary_terminal_case` bridges a
  terminal `Eff_App` summary run to the matching computational `Mu_App` trace,
  and
  `Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_case`
  does the analogous region-application case against an actual terminal
  `Empty` summary. These are intentionally premise-driven stepping stones; the
  full direct induction still has to derive the component premises from typing,
  read-only evidence, and recursive `BackTriangle` hypotheses.
  `StepsPhi_pair_par_from_components` replays the staged ordinary `Pair_Par`
  path through effect summary 1, effect summary 2, computation 1, computation
  2, and the final pair return. The pass/fallback replay wrappers instantiate
  the single generic check step with either `Step_PairPar_EvalMu1` or
  `Step_PairPar_FallbackMu1`. The composed and terminal pair-par theorems join
  the four component soundness premises into
  `Union_Theta (Union_Theta theta1 theta2) (Union_Theta theta_mu1 theta_mu2)`
  and then use terminal determinism to cover arbitrary terminal `Pair_Par`
  executions. `Correctness_soundness_ext_small_step_pair_par_checked_composed_case`
  and
  `Correctness_soundness_ext_small_step_pair_par_checked_terminal_case` package
  those two branches behind the existing `PairParCheckDecidable` assumption.
  The derived
  `Correctness_soundness_ext_small_step_pair_par_same_summary_*` theorem family
  covers the closer paper-facing invariant where the computation branches are
  already known sound against the two thetas computed by the effect-summary
  phase, so the full staged `Pair_Par` trace is sound against
  `Union_Theta theta1 theta2`. The
  `Correctness_soundness_ext_small_step_pair_par_same_summary_readonly_terminal_case`
  and
  `Correctness_soundness_ext_small_step_pair_par_same_summary_static_readonly_terminal_case`
  variants use summary-trace read-only evidence, or static read-only evidence
  plus `Epsilon_Phi_Soundness`, to show that the sequentially staged summary
  heaps are definitionally equal to the source heap before applying the checked
  terminal theorem.
  `Correctness_soundness_ext_small_step_pair_par_same_summary_sequential_readonly_terminal_case`
  phrases the same result over the structured
  `PairParSequentialEffectSummaryStepsPhi` summary witness, which is the cleaner
  hook for later direct-induction cases.
  `Correctness_soundness_ext_small_step_pair_par_same_summary_typed_readonly_terminal_case`
  removes those explicit `Epsilon_Phi_Soundness` premises by deriving both
  summary-trace read-only facts from typed small-step effect soundness.
  `StepsPhi_nested_concat_summary_terminal_theta` and
  `Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_case`
  cover the actual four-part `BT_Pair_Par` summary shape
  `(eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)`: they identify the terminal theta of the
  nested summary expression and then apply the general checked/fallback
  `Pair_Par` terminal theorem.
  `PairParSequentialEffectSummaryStepsPhi_readonly_heap_neutral` records the
  reusable runtime version of that heap-neutrality fact for the whole
  two-summary staging phase, while
  `PairParSequentialEffectSummaryStepsPhi_readonly_from_small_step_sound` and
  `PairParSequentialEffectSummaryStepsPhi_readonly_heap_neutral_from_small_step_sound`
  are the corresponding typed runtime wrappers.
  `StepsPhi_binary_from_left_right` factors the same continuation-replay
  pattern for strict left-to-right binary operators. Its specializations cover
  `Plus`, `Minus`, `Times`, and `Eq`, and
  `Correctness_soundness_ext_small_step_binary_join_case` plus the four
  composed variants package the corresponding direct soundness steps. The four
  binary terminal variants again use deterministic terminal equality to make
  the result independent of the particular terminal derivation.
  `StepsPhi_{plus,minus,times,eq}_terminal_decompose` go in the reverse
  direction: from one terminal binary-operator run they recover the two
  terminal numeric operand runs and the final result equation.
  `Correctness_soundness_ext_small_step_binary_union_join_case` and the
  `_union_composed_case`/`_union_terminal_case` variants for `Plus`, `Minus`,
  `Times`, and `Eq` match the `BackTriangle` shape more directly: the left
  component may be sound for `theta1`, the right component for `theta2`, and
  the whole operator trace is sound for `Union_Theta theta1 theta2`.
  `StepsPhi_concat_summary_terminal_theta` then identifies the theta produced
  by an actual terminal `Concat` summary run.
  `StepsPhi_concat_terminal_decompose` and
  `StepsPhi_concat_effect_terminal_decompose` recover the two component
  summary runs from a terminal `Concat` run. The four
  `Correctness_soundness_ext_small_step_*_summary_terminal_case` wrappers for
  `Plus`, `Minus`, `Times`, and `Eq` state the binary computational cases
  directly against that terminal summary theta.
  `Correctness_soundness_ext_small_step_*_summary_terminal_direct_case` for
  `Plus`, `Minus`, `Times`, and `Eq` strengthen this interface: they take the
  whole terminal computation run and whole terminal `Concat` summary run,
  recover both branch runs internally, use typed read-only heap neutrality for
  the left operand, and then invoke the recursive branch-soundness premises.
  `StepsPhi_cond_terminal_decompose` and
  `Correctness_soundness_ext_small_step_cond_summary_terminal_direct_case`
  provide the analogous direct conditional shape, including deterministic
  exclusion of mismatched summary/computation guard branches.
  The same file now includes terminal summary facts for `AllocAbs`, `ReadAbs`,
  `WriteAbs`, `ReadConc`, `WriteConc`, and `Concat`. The singleton lemmas
  `Phi_Theta_Soundness_*_singleton` connect dynamic heap actions to the
  computed-action summaries they require, while
  `Correctness_soundness_ext_small_step_concat_composed_case` and
  `Correctness_soundness_ext_small_step_concat_terminal_case` package the
  direct soundness step for summary concatenation.
  `StepsPhi_readconc_terminal_from_arg` and
  `StepsPhi_writeconc_terminal_from_arg` use terminal determinism to extract
  the concrete singleton theta from terminal `ReadConc`/`WriteConc` summary
  runs. The abstract summary-terminal wrappers for `Ref`, `DeRef`, and
  `Assign` similarly consume terminal `AllocAbs`, `ReadAbs`, and `WriteAbs`
  summary runs through the existing primitive terminal facts.
  `Correctness_soundness_ext_small_step_deref_conc_summary_terminal_case`
  and
  `Correctness_soundness_ext_small_step_assign_conc_summary_terminal_case`
  then use those extracted summaries to state the concrete read/write cases
  against the actual terminal summary theta.
  `StepsPhi_right_nested_concat_summary_terminal_theta` and the
  `Correctness_soundness_ext_small_step_{ref_abs,deref_abs,assign_abs}_bt_summary_terminal_case`
  wrappers cover the actual abstract-reference `BackTriangle` summary shapes
  `eff ⊕ AllocAbs`, `eff ⊕ ReadAbs`, and `eff1 ⊕ (eff2 ⊕ WriteAbs)`, using
  terminal determinism to identify the theta produced by the full summary
  expression before applying the computational reference theorem. The concrete
  assignment shape `eff1 ⊕ (eff2 ⊕ WriteConc ea)` is covered by
  `Correctness_soundness_ext_small_step_assign_conc_bt_summary_readonly_terminal_case`,
  with `ReadOnlyPhi` premises on the two preceding summary phases to recover
  heap neutrality before matching the final concrete write summary.
  The computational reference side now has labelled continuation replay for
  `Ref`, `DeRef`, and `Assign`, plus composed direct soundness cases for
  abstract allocation/read/write and concrete read/write summaries. The
  new `StepsPhi_ref_terminal_decompose` and
  `StepsPhi_deref_terminal_decompose` lemmas recover the argument run and
  heap/action witnesses from the whole terminal computation run.
  `Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_direct_case`,
  `Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_direct_case`,
  and
  `Correctness_soundness_ext_small_step_deref_conc_summary_terminal_direct_case`
  use those decomposers to remove externally supplied argument runs from the
  corresponding allocation/read correctness steps. The
  corresponding `_terminal_case` theorems expose the same facts for arbitrary
  terminal executions by applying
  `Correctness_soundness_ext_small_step_terminal_transfer`.
  `theories/Soundness/SmallStepPaperSoundness.v` now exports the closed
  paper-facing terminal theorem
  `PaperPairParCheckedStructuredTerminalCorrectness`. The statement keeps the
  ordinary typing and terminal-run hypotheses, but it does not expose a bounded
  induction package or an auxiliary heap-agreement premise.

  The lower-level constructor lemmas, replay facts, counted decompositions, and
  unaugmented application-summary diagnostics remain in the proof tree as
  implementation support for the direct induction. They are no longer presented
  as part of the public theorem map. `SmallStepFallback.v` is kept focused on
  fallback occurrence and no-fallback conversion lemmas; the canonical
  dispatcher lives in `SmallStepCorrectnessDirect.v`. Terminal
  small-step/terminating-evaluator adequacy remains postponed.
  The application-summary port now has
  `Correctness_soundness_ext_small_step_mu_app_summary_terminal_direct_case`,
  exposed under that paper-facing name. This theorem
  recovers the function, argument, and body runs from terminal `Mu_App` and
  `Eff_App` executions, aligns the shared function/argument phases by
  small-step determinism, and applies the body correctness premise to the
  summary body trace directly. The region-application port now has
  `Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_direct_case`,
  exposed as `PaperSmallStepRgnAppEmptySummaryDirectCorrectness`; it recovers
  the function/body runs from the terminal `Rgn_App` execution and matches them
  against the terminal `Empty` summary.
  `StepsPhi_pair_par_after_check_terminal_decompose` and
  `StepsPhi_pair_par_terminal_decompose` are the next direct `Pair_Par`
  decomposition tools: they recover both effect-summary runs, both computation
  runs, the final pair value, and the four-part trace equation from a single
  terminal `Pair_Par` execution.
  `Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_direct_case`
  combines that
  runtime decomposition with decomposition of the nested summary expression.
  It proves the four-part `BT_Pair_Par` summary theorem directly over the
  actual terminal `Pair_Par` and nested-summary runs, and it no longer needs
  `PairParCheckDecidable`.
  The public paper-facing layer intentionally stops at the no-fallback bounded
  principles. The direct correctness file now keeps the remaining
  implementation support local: terminal decompositions, read-only trace
  stability, and the constructor-specific facts needed by the no-fallback
  induction.

- `WTStateRuntimeHeapShapeAt_steps_phi_trace_typed`
  proves that explicitly typed ordinary states remain explicitly typed and
  emit a well-typed structured trace.

- `PairParStepsPhi`
  records checked interleaving prefixes with three structured components:
  continuation/state trace, left computation branch trace, and right
  computation branch trace.

- `WTPairParStateRuntimeHeapShapeAtStrong_steps_phi_trace_typed`
  proves explicit typing and `TcPhi` evidence for all three checked
  interleaving trace components.

- `PairParPhiTraceSafeAt`
  packages branch-structured checked finite-prefix safety. It preserves the
  strong checked-interleaving invariant, store extension, branch heap synchronization,
  not-stuckness, and typed `Phi` evidence for the continuation, left-branch,
  and right-branch trace components.

- `PairParStepsPhi_as_pairpar_steps_exists`
  proves that every branch-structured checked run has some erased ordinary
  checked-interleaving run. The theorem is intentionally existential: the
  branch-structured trace records branch membership, not a unique linear
  interleaving order.

- `StepsPhi_replays_heap`
  proves that every ordinary structured small-step run replays its `Phi` trace
  over the heap components of the initial and final states.

- `PairParStepsPhi_run_split_replays_heap`
  decomposes a checked `PPS_Run` execution into a replay of the branch-parallel
  computation trace `Phi_Par phi_left phi_right`, followed by a replay of the
  continuation/state trace `phi_state`.

- `PairParStepsPhi_checked_replays_heap`
  specializes the split replay theorem to `pairpar_checked_start`, giving heap
  replay for the whole checked computation trace
  `Phi_Seq (Phi_Par phi_left phi_right) phi_state`.

- `PairParBranchReplayWitness`
  packages the independent branch replay premises needed by the factored heap
  join theorem: left replay, right replay, disjoint heap deltas, and replay of
  the combined `Phi_Par` trace.

- `PairParBranchReplayWitness_tc_heap_join`
  applies `TcHeap_Extended_PhiPar` to a branch replay witness and the two
  branch heap typings, producing the joined heap typing for the parallel phase.

- `PairParStepsPhi_checked_branch_replay_join`
  combines a checked structured run with independent branch replay witnesses:
  the checked run supplies the `Phi_Par` replay and the continuation replay,
  while the branch witnesses supply the per-branch replay/typing hypotheses
  needed for the heap/store join.

- `PairParStepsPhi_checked_pass_sound_branch_steps_join`
  lives in `theories/Determinism/SmallStepStructuredReplay.v`. It derives trace
  disjointness from `phi_left ⋞ theta_left`, `phi_right ⋞ theta_right`, and
  `PairParCheckPass theta_left theta_right`, then combines independent branch
  `StepsPhi` runs with the checked interleaving run to produce the replay
  witness and joined heap typing.

- `pairpar_check_pass_steps_phi_to_sequential`
  prefixes any ordinary sequential continuation run with the successful
  check-state step. This records that the source `Pair_Par` machine still steps
  to the ordinary sequential tuple continuation after a successful check.

- `pairpar_check_fail_steps_phi_to_fallback`
  prefixes any ordinary fallback run with the failed check-state step.

- `PairParCheckedStructuredStepsPhi_source_check_dispatch`
  decomposes a successful structured checked run into its effect-summary traces,
  pass evidence, the ordinary source check-state step, and the separate checked
  interleaving run.

- `PairParFallbackStructuredStepsPhi_erases_from_check_state`
  proves that a structured fallback run erases to an ordinary `StepsPhi` prefix
  from the source check state to the fallback result.

- `StepsPhi_initial_terminal_continue`
  is the generic continuation-lifting bridge: a terminal `KDone` run can be
  replayed under another continuation by replacing the final `Step_Done` with
  the continuation's next silent step.

- `StepsPhi_readonly_preserves_heap`
  reuses `ReadOnlyPhi_Heap_Steps_preserves_heap` through `StepsPhi_replays_heap`
  to show that any read-only structured small-step trace leaves the heap
  unchanged.

- `StepsPhi_readonly_static_effect_preserves_heap`
  derives the same heap-neutrality result from
  `ReadOnlyStatic (Phi_Static_Effect phi)` plus the generic trace
  self-soundness theorem.

- `PairParSequentialEffectSummaryStepsPhi`
  records the ordinary source order for the effect-summary phase. The first
  summary starts from the original heap; the second starts from the heap
  produced by the first summary.

- `pairpar_effect_summary_steps_phi_heap_neutral`
  specializes read-only heap preservation to one terminating effect-summary
  evaluation.

- `effect_summary_trace_readonly_from_static_soundness`
  ports the old big-step proof pattern: static read-only plus
  `Epsilon_Phi_Soundness` gives `ReadOnlyPhi`.

- `pairpar_effect_summary_steps_phi_readonly_from_static_soundness`
  specializes that wrapper to one terminating structured small-step
  effect-summary run.

- `PairParEffectSummaryStepsPhi_sequential_when_first_heap_unchanged`
  turns independent summary witnesses into source-sequential summary witnesses
  when the first summary leaves the heap unchanged.

- `PairParSequentialEffectSummaryStepsPhi_independent_when_first_heap_unchanged`
  turns source-sequential summary witnesses back into independent summary
  witnesses under the same heap-neutrality assumption.

- `PairParSequentialEffectSummaryStepsPhi_source_pass_prefix`
  proves that a source-initial `Pair_Par` expression reaches the ordinary
  sequential tuple start after a successful check, with an erased dynamic trace
  equal to the two sequential summary traces.

- `PairParSequentialEffectSummaryStepsPhi_source_fail_prefix`
  proves the same source-prefix result for failed checks and fallback.

- `PairParSequentialEffectSummaryStepsPhi_source_pass_independent_prefix`
  combines the source pass prefix with the independent summary witness when the
  first effect-summary trace is read-only.

- `PairParSequentialEffectSummaryStepsPhi_source_fail_independent_prefix`
  gives the analogous combined bridge for failed checks.

- `PairParSequentialEffectSummaryStepsPhi_source_pass_static_sound_prefix`
  replaces the raw `ReadOnlyPhi` premise with the old static-read-only plus
  `Epsilon_Phi_Soundness` pattern in the pass case.

- `PairParSequentialEffectSummaryStepsPhi_source_fail_static_sound_prefix`
  gives the analogous static-soundness wrapper for failed checks.

- `PaperPairParSummaryPassSmallStepSoundPrefix` and
  `PaperPairParSummaryFailSmallStepSoundPrefix`
  are the stable paper-facing aliases for the corresponding small-step-derived
  pass/fail source-prefix wrappers in `SmallStepCorrectness.v`.

- `PairParSequentialEffectSummaryStepsPhi_source_pass_static_included_prefix`
  and `PairParSequentialEffectSummaryStepsPhi_source_fail_static_included_prefix`
  are the inclusion-shaped versions of the previous two theorems. They replace
  the `Epsilon_Phi_Soundness` premise with
  `Included StaticAction (Phi_Static_Effect phi_eff1)
     (fold_subst_eps rho static_eff1)`.

- `PairParSequentialEffectSummaryStepsPhi_source_pass_trace_static_prefix`
  and `PairParSequentialEffectSummaryStepsPhi_source_fail_trace_static_prefix`
  use the trace's own computed static envelope instead of a declared source
  effect. These are staging theorems for adequacy work: they prove the
  source-prefix/independent-summary bridge whenever the first summary trace's
  computed static envelope is read-only.

- `PairPar_source_static_summary_checked_branch_join_exists`
  lives in `theories/Determinism/SmallStepStructuredReplay.v`. It packages the
  source summary prefix, the independent summary witness, and the checked
  computation branch replay/join into one theorem under the static-read-only
  plus `Epsilon_Phi_Soundness` assumptions for the first summary.

- `PairPar_source_trace_static_summary_checked_branch_join_exists`
  is the corresponding staging theorem under
  `ReadOnlyStatic (Phi_Static_Effect phi_eff1)`. It avoids any new semantic
  commitment about declared source effects while preserving the same source
  prefix and checked branch replay/join conclusion.

- `PairPar_source_static_included_summary_checked_branch_join_exists`
  packages the same replay/join conclusion under the declared-effect inclusion
  premise. This is the theorem the future small-step static-effect soundness
  proof should feed directly.

- `pairpar_check_decidable_phi_trace_safe`
  is the structured-trace counterpart of
  `pairpar_check_decidable_trace_safe`: successful checks get
  `PairParPhiTraceSafeAt`; failed checks get `StatePhiTraceSafeAt` for the
  sequential fallback.

- `pairpar_check_decidable_phi_terminal_value`
  gives the matching terminal-value extractor for structured checked traces
  and structured fallback traces.

- `PairParEffectSummaryStepsPhi`
  runs the two surface-effect summary applications as separate structured
  branches, producing `theta1` and `theta2`.

- `pairpar_effect_summary_steps_phi_trace_typed`
  proves typed structured traces for both effect-summary branches, producing
  one final store typing per branch.

- `pairpar_effect_summary_steps_phi_replay`
  gives the heap replay facts for both effect-summary branches.

- `pairpar_checked_structured_trace`
  records the successful-check shape:

  ```coq
  Phi_Seq
    (Phi_Par phi_eff1 phi_eff2)
    (Phi_Seq (Phi_Par phi_mu1 phi_mu2) phi_mu_state)
  ```

- `pairpar_fallback_structured_trace`
  records the failed-check shape:

  ```coq
  Phi_Seq (Phi_Par phi_eff1 phi_eff2) phi_seq
  ```

Thus, yes: in the adequacy-oriented instrumentation, the effect-summary phase
is itself branch-structured. That is the shape needed to line up later with the
big-step trace
`Phi_Seq (Phi_Par acts_eff1 acts_eff2) (Phi_Par acts_mu1 acts_mu2)`. The
remaining future work is to connect these instrumented structured runs to the
ordinary `Pair_Par` machine and then to the big-step judgment.

Two terminal component extractors now expose the proof obligations that a later
adequacy theorem must reconcile:

- `PairParCheckedStructuredStepsPhi_terminal_components_typed`
  extracts `phi_eff1`, `phi_eff2`, `phi_mu_state`, `phi_mu1`, and `phi_mu2`
  from a terminating successful structured run, together with typed trace
  evidence for each component and typed final value/heap evidence for the
  checked computation.

- `PairParFallbackStructuredStepsPhi_terminal_components_typed`
  extracts `phi_eff1`, `phi_eff2`, and `phi_seq` from a terminating fallback
  structured run, together with typed trace evidence for each component and
  typed final value/heap evidence for the sequential fallback.

The old heap/store join machinery has now been factored into
`TcHeap_Extended_PhiPar` in `theories/Meta/TraceTypingFacts.v`. The original
big-step theorem `TcHeap_Extended_2` is now a thin wrapper around it, using
`BigStep_replays_trace` to discharge the branch replay premises. For the
structured small-step path, `StepsPhi_replays_heap` already supplies replay for
ordinary structured runs such as effect-summary branches and fallback runs, and
`PairParStepsPhi_checked_replays_heap` supplies replay for the whole checked
computation trace. The new `PairParBranchReplayWitness` and
`PairParStepsPhi_checked_branch_replay_join` bridge the replay facts to
`TcHeap_Extended_PhiPar` once independent branch witnesses are available.
`SmallStepStructuredReplay.v` now derives the trace-disjointness part from
checked-disjointness plus trace soundness and packages the result for
independent branch `StepsPhi` runs. The meta layer also gives a computed static
envelope for any structured trace (`Phi_Static_Effect`), proves that every
trace is sound with respect to that envelope, and proves that the envelope is
least among all sound static effects for the trace. The check-state bridge is now explicit:
successful checks expose both the ordinary source step to the sequential tuple
continuation and the separate structured checked interleaving relation, while
failed structured runs erase to an ordinary fallback `StepsPhi` prefix. The
source-initial effect-summary prefix is also explicit for the sequential source
order, and the source-sequential and independent summary relations coincide
when the first summary is heap-neutral. Read-only traces are now proved
heap-neutral, and the source-prefix bridge packages the independent summary
witness under a `ReadOnlyPhi` premise. The old big-step read-only pattern is
also exposed as a small wrapper: `ReadOnlyStatic` plus
`Epsilon_Phi_Soundness` gives `ReadOnlyPhi`. The replay layer now packages this
source summary prefix together with the checked computation branch replay/join.
The replay layer also exposes a trace-static staging version using
`ReadOnlyStatic (Phi_Static_Effect phi_eff1)`. The remaining independence gap is
to prove the inclusion from the computed envelope to the declared
`fold_subst_eps rho static_eff` obtained from static typing.

## Addressing The Reviewer Comment

The earlier concern was that the final theorem only proved determinism of
repeated evaluations from equivalent heaps, rather than a direct relationship
between a parallel tuple and a separately defined sequential tuple rule.

The current mechanization answers the part that is expressible in the current
syntax:

- `Pair_Par` has one staged small-step rule sequence.
- After summaries are evaluated, the dynamic check is explicit.
- If the check succeeds, the checked interleaving semantics is trace-safe.
- If the check fails, the ordinary sequential fallback path is trace-safe.

The mechanization still does not prove equivalence against a separate
syntactic `[E-SEQ]` rule, because no such rule exists in the mechanized syntax.
Adding that theorem would require first adding a distinct sequential tuple
construct or relation, then proving a simulation or observational equivalence
between that construct and the failed-check path.

The accurate paper claim is therefore:

> The mechanization proves finite-prefix trace safety for the staged `Pair_Par`
> semantics. A successful dynamic effect check is connected to a checked
> interleaving relation, while a failed check is connected to the ordinary
> sequential fallback path. The current calculus does not include a distinct
> sequential tuple constructor, so the mechanized result is a dispatch/safety
> theorem for the existing staged construct, not an equivalence theorem between
> two source constructs.

## Computed-Action Disjointness

The computed-action disjointness definition has been adjusted so concrete
read/write and write/write actions are disjoint when their concrete addresses
are different:

```text
(r1, l1) <> (r2, l2)
```

This means same-region, different-location accesses can be accepted by the
parallel disjointness check. That matches the motivating `incr` intuition:
surface-effect summaries can distinguish concrete locations even when the
static region is the same.

## BS_Set_Ref Gap

The assignment semantics now includes the side condition that a write targets an
existing heap location after the assigned value has been evaluated. This closes
the previous preservation gap around `BS_Set_Ref`/assignment by ensuring the
store typing does not need to invent a type for an unallocated cell during a
write.

In the small-step layer, the corresponding rule is:

```coq
Step_Assign_Done :
  find_R w rho = Some r ->
  find_H (r, l) heap <> None ->
  ...
```

The explicit-store preservation theorem for assignment uses
`RuntimeHeapShape_update_existing`, not fresh allocation reasoning.

## Remaining Limitations And Next Work

The mechanization is now substantially cleaner, but some limits remain:

- The big-step theorem stack is still the reference for terminating runs.
- The small-step theorem stack proves finite-prefix safety, not full
  observational equivalence.
- The checked interleaving target is a separate relation reached after a
  successful check; the ordinary machine itself still steps through the
  continuation frames sequentially.
- `SmallStepStructuredTrace.v` records the adequacy-oriented trace shape and
  now replays ordinary `StepsPhi` plus successful checked computation traces.
  It also connects checked/fallback structured runs to the ordinary source
  check-state prefix and connects source-initial `Pair_Par` executions through
  the sequential effect-summary phase. It bridges sequential and independent
  summaries for first-summary traces that are read-only or are statically
  sound with respect to a read-only static effect. It now also computes a
  precise static envelope for each structured trace, proves trace
  self-soundness, and proves that the envelope is least among static effects
  sound for that trace. The small-step theorem that includes this computed
  envelope in the declared static effect from typing is not yet proved.
- A true equivalence theorem with a separately defined sequential tuple rule
  would require adding that rule or relation first.

Useful next theorem targets:

1. A small-step static-effect soundness theorem for effect-summary
   evaluations, proving
   `Included StaticAction (Phi_Static_Effect phi) (fold_subst_eps rho static_eff)`.
   The `WTStateEffectAt_steps_budget` theorem now provides the finite-prefix
   budget skeleton for ordinary small-step traces; the next internal step is
   connecting it to the paper-facing terminal/static-summary statements.
2. A terminal small-step/big-step adequacy theorem using the structured trace
   shape.
3. A separate sequential tuple relation, if the paper wants a direct
   `[E-PAR]` versus `[E-SEQ]` theorem.
