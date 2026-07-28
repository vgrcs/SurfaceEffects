From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Program.Equality.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Core.Values.
Require Import theories.SmallStep.Runtime.Continuation.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Runtime.Trace.
Require Import theories.SmallStep.Soundness.Correctness.
Require Import theories.SmallStep.Soundness.StaticEffect.
Require Import theories.SmallStep.Soundness.Summary.
Require Import theories.SmallStep.Determinism.Terminal.
Require Import theories.SmallStep.Typing.Judgments.
Require Import theories.SmallStep.Typing.Regularity.
Require Import theories.SmallStep.Typing.Types.

Import ListNotations.

Lemma CBT_Cond_components :
  forall gamma omega e et ef efft efff,
    CheckedBackTriangle gamma omega
      (ECond e et ef) (ECond e efft efff) ->
    exists (eff_e : StaticEffect) (ty ty_t ty_f : Ty)
      (eff_et eff_ef : StaticEffect),
      CheckedTcExp gamma omega e TyBool eff_e /\
      CheckedTcExp gamma omega et ty_t eff_et /\
      CheckedTcExp gamma omega ef ty_f eff_ef /\
      static_heap_neutral eff_e /\
      CheckedBackTriangle gamma omega e EEmpty /\
      CheckedBackTriangle gamma omega et efft /\
      CheckedBackTriangle gamma omega ef efff.
Proof.
  intros gamma omega e et ef efft efff HBack.
  dependent destruction HBack.
  exists eff_e, ty, ty_t, ty_f, eff_et, eff_ef.
  split; [exact H |].
  split; [exact H0 |].
  split; [exact H1 |].
  split; [exact H3 |].
  split; [exact HBack1 |].
  split; assumption.
Qed.

Lemma ECond_terminal_first_step :
  forall heap env rho e et ef phi heap_final v_final,
    Steps
      (InitialState heap env rho (ECond e et ef))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      Steps
        (StEval heap env rho e (KCond et ef env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap env rho e et ef phi heap_final v_final HSteps.
  remember (InitialState heap env rho (ECond e et ef))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (Step_deterministic
        (StEval heap env rho (ECond e et ef) KDone)
        LSilent
        (StEval heap env rho e (KCond et ef env rho KDone))
        label state'
        (StepCond heap env rho e et ef KDone)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma ECond_terminal_first_step_N :
  forall n heap env rho e et ef phi heap_final v_final,
    StepsN n
      (InitialState heap env rho (ECond e et ef))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      StepsN n_tail
        (StEval heap env rho e (KCond et ef env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap env rho e et ef phi heap_final v_final HSteps.
  destruct
    (StepsN_known_first_step_terminal_inv
      n
      (InitialState heap env rho (ECond e et ef))
      LSilent
      (StEval heap env rho e (KCond et ef env rho KDone))
      phi heap_final v_final
      (StepCond heap env rho e et ef KDone)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
Qed.

Lemma KCond_terminal_value_is_bool :
  forall heap v et ef env rho k phi heap_final v_final,
    Steps
      (StReturn heap v (KCond et ef env rho k))
      phi
      (StDone heap_final v_final) ->
    exists b,
      v = VBool b.
Proof.
  intros heap v et ef env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap v (KCond et ef env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst; eexists; reflexivity.
Qed.

Lemma KCond_bool_terminal_first_step :
  forall heap b et ef env rho k phi heap_final v_final,
    Steps
      (StReturn heap (VBool b) (KCond et ef env rho k))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      Steps
        (StEval heap env rho (if b then et else ef) k)
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap b et ef env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap (VBool b) (KCond et ef env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct b.
    + destruct
        (Step_deterministic
          (StReturn heap (VBool true) (KCond et ef env rho k))
          LSilent
          (StEval heap env rho et k)
          label state'
          (StepCondTrue heap et ef env rho k)
          HStep)
        as [HLabel HState].
      subst label state'.
      exists phi0.
      split; [assumption | reflexivity].
    + destruct
        (Step_deterministic
          (StReturn heap (VBool false) (KCond et ef env rho k))
          LSilent
          (StEval heap env rho ef k)
          label state'
          (StepCondFalse heap et ef env rho k)
          HStep)
        as [HLabel HState].
      subst label state'.
      exists phi0.
        split; [assumption | reflexivity].
Qed.

Lemma KCond_bool_terminal_first_step_N :
  forall n heap b et ef env rho k phi heap_final v_final,
    StepsN n
      (StReturn heap (VBool b) (KCond et ef env rho k))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      StepsN n_tail
        (StEval heap env rho (if b then et else ef) k)
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap b et ef env rho k phi heap_final v_final HSteps.
  destruct b.
  - destruct
      (StepsN_known_first_step_terminal_inv
        n
        (StReturn heap (VBool true) (KCond et ef env rho k))
        LSilent
        (StEval heap env rho et k)
        phi heap_final v_final
        (StepCondTrue heap et ef env rho k)
        HSteps)
      as (n_tail & phi_tail & Hn & HTail & HTrace).
    simpl in HTrace.
    exists n_tail, phi_tail.
    repeat split; assumption.
  - destruct
      (StepsN_known_first_step_terminal_inv
        n
        (StReturn heap (VBool false) (KCond et ef env rho k))
        LSilent
        (StEval heap env rho ef k)
        phi heap_final v_final
        (StepCondFalse heap et ef env rho k)
        HSteps)
      as (n_tail & phi_tail & Hn & HTail & HTrace).
    simpl in HTrace.
    exists n_tail, phi_tail.
    repeat split; assumption.
Qed.

Definition ECondDecompositionGoal : Prop :=
  forall heap env rho e et ef phi heap_final v_final,
    Steps
      (InitialState heap env rho (ECond e et ef))
      phi
      (StDone heap_final v_final) ->
    exists phi_cond b heap_cond phi_branch,
      Steps
        (InitialState heap env rho e)
        phi_cond
        (StDone heap_cond (VBool b)) /\
      Steps
        (InitialState heap_cond env rho (if b then et else ef))
        phi_branch
        (StDone heap_final v_final) /\
      phi = phi_cond ++ phi_branch.

Definition ECondCountedDecompositionGoal : Prop :=
  forall n heap env rho e et ef phi heap_final v_final,
    StepsN n
      (InitialState heap env rho (ECond e et ef))
      phi
      (StDone heap_final v_final) ->
    exists n_cond n_branch phi_cond b heap_cond phi_branch,
      StepsN n_cond
        (InitialState heap env rho e)
        phi_cond
        (StDone heap_cond (VBool b)) /\
      StepsN n_branch
        (InitialState heap_cond env rho (if b then et else ef))
        phi_branch
        (StDone heap_final v_final) /\
      phi = phi_cond ++ phi_branch /\
      n_cond < n /\
      n_branch < n.

Theorem ECond_counted_decomposition :
  ECondCountedDecompositionGoal.
Proof.
  unfold ECondCountedDecompositionGoal.
  intros n heap env rho e et ef phi heap_final v_final HSteps.
  destruct
    (ECond_terminal_first_step_N
      n heap env rho e et ef phi heap_final v_final HSteps)
    as (n_cond_tail & phi_cond_tail & HnStart &
      HCondWithKont & HTraceStart).
  destruct
    (StepsN_append_kont_terminal_split_counted
      n_cond_tail
      (StEval heap env rho e (KCond et ef env rho KDone))
      phi_cond_tail
      heap_final
      v_final
      HCondWithKont
      (InitialState heap env rho e)
      (KCond et ef env rho KDone)
      eq_refl)
    as (n_cond & n_after_cond & phi_cond & heap_cond & v_cond &
      phi_after_cond & HCond & HAfterCond & HCountCond &
      HTraceCond).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KCond_terminal_value_is_bool
        heap_cond v_cond et ef env rho KDone
        phi_after_cond heap_final v_final
        (StepsN_to_Steps
          n_after_cond
          (StReturn heap_cond v_cond (KCond et ef env rho KDone))
          phi_after_cond
          (StDone heap_final v_final)
          HAfterCond))
      as (b & HBool).
    subst v_cond.
    destruct
      (KCond_bool_terminal_first_step_N
        n_after_cond heap_cond b et ef env rho KDone
        phi_after_cond heap_final v_final HAfterCond)
      as (n_branch & phi_branch & HCountAfterCond &
        HBranch & HTraceAfterCond).
    exists n_cond, n_branch, phi_cond, b, heap_cond, phi_branch.
    repeat split; try assumption.
    + rewrite HTraceStart, HTraceCond, HTraceAfterCond.
      reflexivity.
    + lia.
    + lia.
Qed.

Theorem ECond_decomposition :
  ECondDecompositionGoal.
Proof.
  unfold ECondDecompositionGoal.
  intros heap env rho e et ef phi heap_final v_final HSteps.
  destruct
    (ECond_terminal_first_step
      heap env rho e et ef phi heap_final v_final HSteps)
    as (phi_tail & HCondWithKont & HTraceStart).
  destruct
    (Steps_to_StepsN
      (StEval heap env rho e (KCond et ef env rho KDone))
      phi_tail
      (StDone heap_final v_final)
      HCondWithKont)
    as (n_cond & HCondWithKontN).
  destruct
    (StepsN_append_kont_terminal_split
      n_cond
      (StEval heap env rho e (KCond et ef env rho KDone))
      phi_tail
      heap_final
      v_final
      HCondWithKontN
      (InitialState heap env rho e)
      (KCond et ef env rho KDone)
      eq_refl)
    as (phi_cond & heap_cond & v_cond & phi_after_cond &
      HCond & HAfterCond & HTraceCond).
  destruct
    (KCond_terminal_value_is_bool
      heap_cond v_cond et ef env rho KDone
      phi_after_cond heap_final v_final HAfterCond)
    as (b & HBool).
  subst v_cond.
  destruct
    (KCond_bool_terminal_first_step
      heap_cond b et ef env rho KDone
      phi_after_cond heap_final v_final HAfterCond)
    as (phi_branch & HBranch & HTraceAfterCond).
  exists phi_cond, b, heap_cond, phi_branch.
  repeat split; try assumption.
  rewrite HTraceStart, HTraceCond, HTraceAfterCond.
  reflexivity.
Qed.

Theorem ECond_counted_checked_store_context_trace_covered_from_below :
  forall n_bound n_eval gamma omega heap env rho
    e et ef efft efff phi heap_final v_final
    phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n_bound ->
    n_eval < n_bound ->
    CheckedBackTriangle gamma omega
      (ECond e et ef) (ECond e efft efff) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CountedComputationEvaluation n_eval heap env rho
      (ECond e et ef) phi heap_final v_final ->
    SummaryEvaluation heap env rho
      (ECond e efft efff) phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n_bound n_eval gamma omega heap env rho
    e et ef efft efff phi heap_final v_final
    phi_summary heap_summary theta
    HBelow HCountEval HBack HContext HComp HSummary.
  destruct
    (CBT_Cond_components
      gamma omega e et ef efft efff HBack)
    as (eff_e & ty & ty_t & ty_f & eff_et & eff_ef &
      HCheckedCond & _ & _ & _ & HBackCond & HBackThen & HBackElse).
  unfold CountedComputationEvaluation in HComp.
  destruct
    (ECond_counted_decomposition
      n_eval heap env rho e et ef phi heap_final v_final HComp)
    as (n_cond & n_branch & phi_cond & b & heap_cond &
      phi_branch & HCond & HBranch & HTrace & HCountCond &
      HCountBranch).
  unfold SummaryEvaluation in HSummary.
  destruct
    (ECond_decomposition
      heap env rho e efft efff phi_summary heap_summary
      (VSummary theta) HSummary)
    as (phi_cond_summary & b_summary & heap_cond_summary &
      phi_branch_summary & HCondSummary & HBranchSummary &
      _HTraceSummary).
  destruct
    (Steps_terminal_trace_deterministic
      (InitialState heap env rho e)
      phi_cond heap_cond (VBool b)
      phi_cond_summary heap_cond_summary (VBool b_summary))
    as (HTraceCond & HHeapCond & HValCond).
  - eapply StepsN_to_Steps; eauto.
  - exact HCondSummary.
  - inversion HValCond; subst b_summary.
    subst phi_cond_summary heap_cond_summary.
    assert
      (TraceCoveredBySummary phi_cond
        (SummarySet ([] : list ComputedAction))) as HCoverCond.
    { eapply
        (HBelow n_cond gamma omega heap env rho e EEmpty
          phi_cond heap_cond (VBool b)
          ([] : Trace) heap (SummarySet ([] : list ComputedAction)));
        eauto.
      - lia.
      - apply EEmpty_summary_evaluation. }
    pose proof
      (trace_covered_empty_summary_nil phi_cond HCoverCond)
      as HCondNil.
    assert
      (CheckedStoreRuntimeContext gamma omega heap_cond env rho)
      as HContextBranch.
    { eapply
        (checked_store_counted_computation_store_runtime_context
          n_cond gamma omega heap env rho e TyBool eff_e
          phi_cond heap_cond (VBool b)); eauto. }
    subst phi.
    rewrite HCondNil.
    simpl.
    destruct b.
    + eapply
        (HBelow n_branch gamma omega heap_cond env rho et efft
          phi_branch heap_final v_final phi_branch_summary
          heap_summary theta); eauto.
      all: try (unfold SummaryEvaluation; exact HBranchSummary).
      all: lia.
    + eapply
        (HBelow n_branch gamma omega heap_cond env rho ef efff
          phi_branch heap_final v_final phi_branch_summary
          heap_summary theta); eauto.
      all: try (unfold SummaryEvaluation; exact HBranchSummary).
      all: lia.
Qed.

Theorem ECond_checked_store_context_case_from_below :
  forall n gamma omega heap env rho
    e et ef efft efff phi heap_final v_final
    phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    CheckedBackTriangle gamma omega
      (ECond e et ef) (ECond e efft efff) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (ECond e et ef) phi heap_final v_final ->
    SummaryEvaluation heap env rho
      (ECond e efft efff) phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho
    e et ef efft efff phi heap_final v_final
    phi_summary heap_summary theta
    HBelow HBack HContext HComp HSummary.
  destruct
    (CBT_Cond_components
      gamma omega e et ef efft efff HBack)
    as (eff_e & ty & ty_t & ty_f & eff_et & eff_ef &
      HCheckedCond & _ & _ & _ & HBackCond & HBackThen & HBackElse).
  unfold CountedComputationEvaluation in HComp.
  destruct
    (ECond_counted_decomposition
      n heap env rho e et ef phi heap_final v_final HComp)
    as (n_cond & n_branch & phi_cond & b & heap_cond &
      phi_branch & HCond & HBranch & HTrace & HCountCond &
      HCountBranch).
  unfold SummaryEvaluation in HSummary.
  destruct
    (ECond_decomposition
      heap env rho e efft efff phi_summary heap_summary
      (VSummary theta) HSummary)
    as (phi_cond_summary & b_summary & heap_cond_summary &
      phi_branch_summary & HCondSummary & HBranchSummary &
      _HTraceSummary).
  destruct
    (Steps_terminal_trace_deterministic
      (InitialState heap env rho e)
      phi_cond heap_cond (VBool b)
      phi_cond_summary heap_cond_summary (VBool b_summary))
    as (HTraceCond & HHeapCond & HValCond).
  - eapply StepsN_to_Steps; eauto.
  - exact HCondSummary.
  - inversion HValCond; subst b_summary.
    subst phi_cond_summary heap_cond_summary.
    assert
      (TraceCoveredBySummary phi_cond
        (SummarySet ([] : list ComputedAction))) as HCoverCond.
    { eapply
        (HBelow n_cond gamma omega heap env rho e EEmpty
          phi_cond heap_cond (VBool b)
          ([] : Trace) heap (SummarySet ([] : list ComputedAction))).
      - exact HCountCond.
      - exact HBackCond.
      - exact HContext.
      - unfold CountedComputationEvaluation. exact HCond.
      - apply EEmpty_summary_evaluation. }
    pose proof
      (trace_covered_empty_summary_nil phi_cond HCoverCond)
      as HCondNil.
    assert
      (CheckedStoreRuntimeContext gamma omega heap_cond env rho)
      as HContextBranch.
    { eapply
        (checked_store_counted_computation_store_runtime_context
          n_cond gamma omega heap env rho e TyBool eff_e
          phi_cond heap_cond (VBool b)); eauto. }
    subst phi.
    rewrite HCondNil.
    simpl.
    destruct b.
    + simpl in HBranch, HBranchSummary.
      eapply
        (HBelow n_branch gamma omega heap_cond env rho et efft
          phi_branch heap_final v_final phi_branch_summary
          heap_summary theta);
        [ exact HCountBranch
        | exact HBackThen
        | exact HContextBranch
        | unfold CountedComputationEvaluation; exact HBranch
        | unfold SummaryEvaluation; exact HBranchSummary ].
    + simpl in HBranch, HBranchSummary.
      eapply
        (HBelow n_branch gamma omega heap_cond env rho ef efff
          phi_branch heap_final v_final phi_branch_summary
          heap_summary theta);
        [ exact HCountBranch
        | exact HBackElse
        | exact HContextBranch
        | unfold CountedComputationEvaluation; exact HBranch
        | unfold SummaryEvaluation; exact HBranchSummary ].
Qed.
