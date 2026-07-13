# SurfaceEffects Mechanization Report

This report summarizes the current mechanized proof state, with emphasis on the
recent removal of admitted/axiomatic gaps, the small-step runtime layer, and the
reviewer-facing `Pair_Par` check/fallback story.

## Executive Summary

The project now builds under Rocq 9.1.1 with no source-level `Axiom` or
`Admitted` declarations in `theories/`.

The original big-step development remains as the terminating reference
semantics. A new small-step continuation-machine layer has been added to reason
about finite prefixes of both terminating and diverging executions. This layer
does not replace every older theorem; instead, it gives a new proof stack for
runtime preservation, progress, trace safety, checked interleaving safety, and
the staged `Pair_Par` check/fallback behavior.

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
- `SmallStepPaperTheorems.v`: stable theorem names for paper citations.

The facade modules remain for stable imports, but non-facade runtime files now
avoid importing the broad facades directly.

## Big-Step Versus Small-Step

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
  packages preservation, store extension, branch heap agreement, and
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
  combines checked preservation, store extension, heap agreement,
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
  strong checked-interleaving invariant, store extension, heap agreement,
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
`TcHeap_Extended_PhiPar` once independent branch witnesses are available. The
remaining independence gap is to derive those witnesses from checked
disjointness plus trace soundness, rather than assuming them as premises.

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
  now replays ordinary `StepsPhi` plus successful checked computation traces,
  but it is not yet connected to all ordinary source-level `Pair_Par` runs or
  to the big-step judgment.
- A true equivalence theorem with a separately defined sequential tuple rule
  would require adding that rule or relation first.

Useful next theorem targets:

1. Derive `PairParBranchReplayWitness` from checked-disjointness and trace
   soundness.
2. A bridge from ordinary source-level `Pair_Par` executions to the structured
   checked/fallback instrumentation.
3. A terminal small-step/big-step adequacy theorem using the structured trace
   shape.
4. A separate sequential tuple relation, if the paper wants a direct
   `[E-PAR]` versus `[E-SEQ]` theorem.
