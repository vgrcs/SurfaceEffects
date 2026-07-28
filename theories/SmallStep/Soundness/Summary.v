From Stdlib Require Import Lia.
From Stdlib Require Import List.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Core.Values.
Require Import theories.SmallStep.Runtime.Continuation.
Require Import theories.SmallStep.Runtime.HeapNeutral.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Runtime.Trace.
Require Import theories.SmallStep.Soundness.Correctness.
Require Import theories.SmallStep.Typing.Judgments.
Require Import theories.SmallStep.Typing.Regularity.
Require Import theories.SmallStep.Typing.Types.
Require Import theories.SmallStep.Determinism.Terminal.

Import ListNotations.

Definition SummaryHeapNeutral (summary_expr : NExpr) : Prop :=
  forall heap env rho phi heap_final theta,
    NSteps
      (NInitialState heap env rho summary_expr)
      phi
      (StDone heap_final (VSummary theta)) ->
    heap_final = heap /\ HeapNeutralTrace phi.

Definition SummaryTraceHeapNeutral (summary_expr : NExpr) : Prop :=
  forall heap env rho phi heap_final theta,
    NSteps
      (NInitialState heap env rho summary_expr)
      phi
      (StDone heap_final (VSummary theta)) ->
    HeapNeutralTrace phi.

Lemma EEmpty_summary_evaluation :
  forall heap env rho,
    SummaryEvaluation heap env rho EEmpty
      ([] : Trace) heap (SummarySet ([] : list ComputedAction)).
Proof.
  intros heap env rho.
  unfold SummaryEvaluation, NInitialState.
  eapply StepsStep
    with
      (label := LSilent)
      (state' := StReturn heap
        (VSummary (SummarySet ([] : list ComputedAction))) KDone).
  - apply StepEmpty.
  - eapply StepsStep
      with
        (label := LSilent)
        (state' := StDone heap
          (VSummary (SummarySet ([] : list ComputedAction)))).
    + apply StepReturnDone.
    + constructor.
Qed.

Lemma SummaryHeapNeutral_from_trace_heap_neutral :
  forall summary_expr,
    SummaryTraceHeapNeutral summary_expr ->
    SummaryHeapNeutral summary_expr.
Proof.
  unfold SummaryTraceHeapNeutral, SummaryHeapNeutral.
  intros summary_expr HTraceNeutral
    heap env rho phi heap_final theta HSteps.
  pose proof
    (HTraceNeutral heap env rho phi heap_final theta HSteps)
    as HNeutral.
  split.
  - eapply NSteps_heap_neutral_initial_heap; eauto.
  - exact HNeutral.
Qed.

Lemma EEmpty_terminal_summary :
  forall heap env rho phi heap_final theta,
    NSteps
      (NInitialState heap env rho EEmpty)
      phi
      (StDone heap_final (VSummary theta)) ->
    heap_final = heap /\
    theta = SummarySet [] /\
    phi = [].
Proof.
  intros heap env rho phi heap_final theta HSteps.
  remember (NInitialState heap env rho EEmpty) as start eqn:HStart.
  remember (StDone heap_final (VSummary theta)) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (NSteps_return_done_inv
        heap
        (VSummary (SummarySet []))
        phi0 heap_final (VSummary theta)
        HTail)
      as (HHeap & HVal & HTrace).
    simpl in *.
    inversion HVal; subst.
    repeat split; assumption || reflexivity.
Qed.

Lemma EEmpty_summary_heap_neutral :
  SummaryHeapNeutral EEmpty.
Proof.
  unfold SummaryHeapNeutral.
  intros heap env rho phi heap_final theta HSteps.
  destruct (EEmpty_terminal_summary heap env rho phi heap_final theta HSteps)
    as (HHeap & _ & HTrace).
  subst.
  split; [reflexivity | apply heap_neutral_trace_nil].
Qed.

Lemma ETop_terminal_summary :
  forall heap env rho phi heap_final theta,
    NSteps
      (NInitialState heap env rho ETop)
      phi
      (StDone heap_final (VSummary theta)) ->
    heap_final = heap /\
    theta = SummaryTop /\
    phi = [].
Proof.
  intros heap env rho phi heap_final theta HSteps.
  remember (NInitialState heap env rho ETop) as start eqn:HStart.
  remember (StDone heap_final (VSummary theta)) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (NSteps_return_done_inv
        heap
        (VSummary SummaryTop)
        phi0 heap_final (VSummary theta)
        HTail)
      as (HHeap & HVal & HTrace).
    simpl in *.
    inversion HVal; subst.
    repeat split; assumption || reflexivity.
Qed.

Lemma ETop_summary_heap_neutral :
  SummaryHeapNeutral ETop.
Proof.
  unfold SummaryHeapNeutral.
  intros heap env rho phi heap_final theta HSteps.
  destruct (ETop_terminal_summary heap env rho phi heap_final theta HSteps)
    as (HHeap & _ & HTrace).
  subst.
  split; [reflexivity | apply heap_neutral_trace_nil].
Qed.

Lemma EAllocAbs_terminal_summary :
  forall heap env rho r phi heap_final theta,
    NSteps
      (NInitialState heap env rho (EAllocAbs r))
      phi
      (StDone heap_final (VSummary theta)) ->
    exists r_val,
      eval_region rho r = Some r_val /\
      heap_final = heap /\
      theta = SummarySet [CAllocAbs r_val] /\
      phi = [].
Proof.
  intros heap env rho r phi heap_final theta HSteps.
  remember (NInitialState heap env rho (EAllocAbs r)) as start
    eqn:HStart.
  remember (StDone heap_final (VSummary theta)) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (NSteps_return_done_inv
        heap
        (VSummary (SummarySet [CAllocAbs r_val]))
        phi0 heap_final (VSummary theta)
        HTail)
      as (HHeap & HVal & HTrace).
    simpl in *.
    inversion HVal; subst.
    exists r_val.
    repeat split; assumption || reflexivity.
Qed.

Lemma EAllocAbs_summary_heap_neutral :
  forall r,
    SummaryHeapNeutral (EAllocAbs r).
Proof.
  unfold SummaryHeapNeutral.
  intros r heap env rho phi heap_final theta HSteps.
  destruct
    (EAllocAbs_terminal_summary
      heap env rho r phi heap_final theta HSteps)
    as (_ & _ & HHeap & _ & HTrace).
  subst.
  split; [reflexivity | apply heap_neutral_trace_nil].
Qed.

Lemma EReadAbs_terminal_summary :
  forall heap env rho r phi heap_final theta,
    NSteps
      (NInitialState heap env rho (EReadAbs r))
      phi
      (StDone heap_final (VSummary theta)) ->
    exists r_val,
      eval_region rho r = Some r_val /\
      heap_final = heap /\
      theta = SummarySet [CReadAbs r_val] /\
      phi = [].
Proof.
  intros heap env rho r phi heap_final theta HSteps.
  remember (NInitialState heap env rho (EReadAbs r)) as start
    eqn:HStart.
  remember (StDone heap_final (VSummary theta)) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (NSteps_return_done_inv
        heap
        (VSummary (SummarySet [CReadAbs r_val]))
        phi0 heap_final (VSummary theta)
        HTail)
      as (HHeap & HVal & HTrace).
    simpl in *.
    inversion HVal; subst.
    exists r_val.
    repeat split; assumption || reflexivity.
Qed.

Lemma EReadAbs_summary_heap_neutral :
  forall r,
    SummaryHeapNeutral (EReadAbs r).
Proof.
  unfold SummaryHeapNeutral.
  intros r heap env rho phi heap_final theta HSteps.
  destruct
    (EReadAbs_terminal_summary
      heap env rho r phi heap_final theta HSteps)
    as (_ & _ & HHeap & _ & HTrace).
  subst.
  split; [reflexivity | apply heap_neutral_trace_nil].
Qed.

Lemma EWriteAbs_terminal_summary :
  forall heap env rho r phi heap_final theta,
    NSteps
      (NInitialState heap env rho (EWriteAbs r))
      phi
      (StDone heap_final (VSummary theta)) ->
    exists r_val,
      eval_region rho r = Some r_val /\
      heap_final = heap /\
      theta = SummarySet [CWriteAbs r_val] /\
      phi = [].
Proof.
  intros heap env rho r phi heap_final theta HSteps.
  remember (NInitialState heap env rho (EWriteAbs r)) as start
    eqn:HStart.
  remember (StDone heap_final (VSummary theta)) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (NSteps_return_done_inv
        heap
        (VSummary (SummarySet [CWriteAbs r_val]))
        phi0 heap_final (VSummary theta)
        HTail)
      as (HHeap & HVal & HTrace).
    simpl in *.
    inversion HVal; subst.
    exists r_val.
    repeat split; assumption || reflexivity.
Qed.

Lemma EWriteAbs_summary_heap_neutral :
  forall r,
    SummaryHeapNeutral (EWriteAbs r).
Proof.
  unfold SummaryHeapNeutral.
  intros r heap env rho phi heap_final theta HSteps.
  destruct
    (EWriteAbs_terminal_summary
      heap env rho r phi heap_final theta HSteps)
    as (_ & _ & HHeap & _ & HTrace).
  subst.
  split; [reflexivity | apply heap_neutral_trace_nil].
Qed.

Lemma EConcat_terminal_first_step :
  forall heap env rho e1 e2 phi heap_final v_final,
    NSteps
      (NInitialState heap env rho (EConcat e1 e2))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho e1 (KConcatL e2 env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap env rho e1 e2 phi heap_final v_final HSteps.
  remember (NInitialState heap env rho (EConcat e1 e2))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StEval heap env rho (EConcat e1 e2) KDone)
        LSilent
        (StEval heap env rho e1 (KConcatL e2 env rho KDone))
        label state'
        (StepConcat heap env rho e1 e2 KDone)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma EConcat_terminal_first_step_N :
  forall n heap env rho e1 e2 phi heap_final v_final,
    NStepsN n
      (NInitialState heap env rho (EConcat e1 e2))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho e1 (KConcatL e2 env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap env rho e1 e2 phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (NInitialState heap env rho (EConcat e1 e2))
      LSilent
      (StEval heap env rho e1 (KConcatL e2 env rho KDone))
      phi heap_final v_final
      (StepConcat heap env rho e1 e2 KDone)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
Qed.

Lemma KConcatL_terminal_value_is_summary :
  forall heap v e2 env rho k phi heap_final v_final,
    NSteps
      (StReturn heap v (KConcatL e2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists theta,
      v = VSummary theta.
Proof.
  intros heap v e2 env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap v (KConcatL e2 env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    eexists. reflexivity.
Qed.

Lemma KConcatL_summary_terminal_first_step :
  forall heap theta1 e2 env rho k phi heap_final v_final,
    NSteps
      (StReturn heap (VSummary theta1) (KConcatL e2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho e2 (KConcatR theta1 k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap theta1 e2 env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap (VSummary theta1) (KConcatL e2 env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StReturn heap (VSummary theta1) (KConcatL e2 env rho k))
        LSilent
        (StEval heap env rho e2 (KConcatR theta1 k))
        label state'
        (StepConcatL heap theta1 e2 env rho k)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KConcatL_summary_terminal_first_step_N :
  forall n heap theta1 e2 env rho k phi heap_final v_final,
    NStepsN n
      (StReturn heap (VSummary theta1) (KConcatL e2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho e2 (KConcatR theta1 k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap theta1 e2 env rho k phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (StReturn heap (VSummary theta1) (KConcatL e2 env rho k))
      LSilent
      (StEval heap env rho e2 (KConcatR theta1 k))
      phi heap_final v_final
      (StepConcatL heap theta1 e2 env rho k)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
Qed.

Lemma KConcatR_terminal_summary_result :
  forall heap theta1 v phi heap_final theta_final,
    NSteps
      (StReturn heap v (KConcatR theta1 KDone))
      phi
      (StDone heap_final (VSummary theta_final)) ->
    exists theta2,
      v = VSummary theta2 /\
      theta_final = summary_union theta1 theta2 /\
      heap_final = heap /\
      phi = [].
Proof.
  intros heap theta1 v phi heap_final theta_final HSteps.
  remember
    (StReturn heap v (KConcatR theta1 KDone))
    as start eqn:HStart.
  remember
    (StDone heap_final (VSummary theta_final))
    as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (NSteps_known_first_step_terminal_inv
        (StReturn heap (VSummary (summary_union theta1 theta2)) KDone)
        LSilent
        (StDone heap (VSummary (summary_union theta1 theta2)))
        phi0
        heap_final
        (VSummary theta_final)
        (StepReturnDone heap
          (VSummary (summary_union theta1 theta2)))
        HTail)
      as (phi_done & HDone & HTraceTail).
    destruct
      (NSteps_done_inv
        heap
        (VSummary (summary_union theta1 theta2))
        phi_done
        (StDone heap_final (VSummary theta_final))
        HDone)
      as (HTraceDone & HFinalState).
    simpl in *.
    subst phi_done phi0.
    inversion HFinalState; subst.
    exists theta2.
    repeat split; reflexivity.
Qed.

Definition EConcatDecompositionGoal : Prop :=
  forall heap env rho e1 e2 phi heap_final theta,
    NSteps
      (NInitialState heap env rho (EConcat e1 e2))
      phi
      (StDone heap_final (VSummary theta)) ->
    exists phi1 phi2 theta1 theta2 heap1 heap2,
      NSteps
        (NInitialState heap env rho e1)
        phi1
        (StDone heap1 (VSummary theta1)) /\
      NSteps
        (NInitialState heap1 env rho e2)
        phi2
        (StDone heap2 (VSummary theta2)) /\
      theta = summary_union theta1 theta2 /\
      heap_final = heap2 /\
      phi = phi1 ++ phi2.

Definition EConcatCountedDecompositionGoal : Prop :=
  forall n heap env rho e1 e2 phi heap_final theta,
    NStepsN n
      (NInitialState heap env rho (EConcat e1 e2))
      phi
      (StDone heap_final (VSummary theta)) ->
    exists n1 n2 phi1 phi2 theta1 theta2 heap1 heap2,
      NStepsN n1
        (NInitialState heap env rho e1)
        phi1
        (StDone heap1 (VSummary theta1)) /\
      NStepsN n2
        (NInitialState heap1 env rho e2)
        phi2
        (StDone heap2 (VSummary theta2)) /\
      theta = summary_union theta1 theta2 /\
      heap_final = heap2 /\
      phi = phi1 ++ phi2 /\
      n1 < n /\
      n2 < n.

Theorem EConcat_counted_decomposition :
  EConcatCountedDecompositionGoal.
Proof.
  unfold EConcatCountedDecompositionGoal.
  intros n heap env rho e1 e2 phi heap_final theta HSteps.
  destruct
    (EConcat_terminal_first_step_N
      n heap env rho e1 e2 phi heap_final (VSummary theta) HSteps)
    as (n_left_tail & phi_left_tail & HnStart &
      HLeftWithKont & HTraceStart).
  destruct
    (NStepsN_append_kont_terminal_split_counted
      n_left_tail
      (StEval heap env rho e1 (KConcatL e2 env rho KDone))
      phi_left_tail
      heap_final
      (VSummary theta)
      HLeftWithKont
      (NInitialState heap env rho e1)
      (KConcatL e2 env rho KDone)
      eq_refl)
    as (n1 & n_after_left & phi1 & heap1 & v1 &
      phi_after_left & HLeft & HAfterLeft & HCountLeft & HTraceLeft).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KConcatL_terminal_value_is_summary
        heap1 v1 e2 env rho KDone
        phi_after_left heap_final (VSummary theta)
        (NStepsN_to_NSteps
          n_after_left
          (StReturn heap1 v1 (KConcatL e2 env rho KDone))
          phi_after_left
          (StDone heap_final (VSummary theta))
          HAfterLeft))
      as (theta1 & HTheta1).
    subst v1.
    destruct
      (KConcatL_summary_terminal_first_step_N
        n_after_left heap1 theta1 e2 env rho KDone
        phi_after_left heap_final (VSummary theta) HAfterLeft)
      as (n_right_tail & phi_right_tail & HCountAfterLeft &
        HRightWithKont & HTraceAfterLeft).
    destruct
      (NStepsN_append_kont_terminal_split_counted
        n_right_tail
        (StEval heap1 env rho e2 (KConcatR theta1 KDone))
        phi_right_tail
        heap_final
        (VSummary theta)
        HRightWithKont
        (NInitialState heap1 env rho e2)
        (KConcatR theta1 KDone)
        eq_refl)
      as (n2 & n_after_right & phi2 & heap2 & v2 &
        phi_after_right & HRight & HAfterRight & HCountRight &
        HTraceRight).
    + intros heap_done v_done HDone. inversion HDone.
    + destruct
        (KConcatR_terminal_summary_result
          heap2 theta1 v2 phi_after_right heap_final theta
          (NStepsN_to_NSteps
            n_after_right
            (StReturn heap2 v2 (KConcatR theta1 KDone))
            phi_after_right
            (StDone heap_final (VSummary theta))
            HAfterRight))
        as (theta2 & HTheta2 & HTheta & HHeap & HTraceAfterRight).
      subst v2 theta heap_final phi_after_right.
      assert (HAfterRightPositive : 0 < n_after_right).
      { destruct n_after_right; [inversion HAfterRight | lia]. }
      exists n1, n2, phi1, phi2, theta1, theta2, heap1, heap2.
      repeat split; try assumption.
      * rewrite HTraceStart, HTraceLeft, HTraceAfterLeft, HTraceRight.
        rewrite app_nil_r.
        reflexivity.
      * lia.
      * lia.
Qed.

Lemma NCheckedTcExp_EConcat_inv :
  forall gamma omega e1 e2 eff,
    NCheckedTcExp gamma omega (EConcat e1 e2) TyEffect eff ->
    exists eff1 eff2,
      NCheckedTcExp gamma omega e1 TyEffect eff1 /\
      NCheckedTcExp gamma omega e2 TyEffect eff2 /\
      eff = static_union eff1 eff2.
Proof.
  intros gamma omega e1 e2 eff HChecked.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HShape; subst; eauto.
Qed.

Theorem EConcat_decomposition :
  EConcatDecompositionGoal.
Proof.
  unfold EConcatDecompositionGoal.
  intros heap env rho e1 e2 phi heap_final theta HSteps.
  destruct
    (EConcat_terminal_first_step
      heap env rho e1 e2 phi heap_final (VSummary theta) HSteps)
    as (phi_tail & HLeftWithKont & HTraceStart).
  destruct
    (NSteps_to_NStepsN
      (StEval heap env rho e1 (KConcatL e2 env rho KDone))
      phi_tail
      (StDone heap_final (VSummary theta))
      HLeftWithKont)
    as (n_left & HLeftWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_left
      (StEval heap env rho e1 (KConcatL e2 env rho KDone))
      phi_tail
      heap_final
      (VSummary theta)
      HLeftWithKontN
      (NInitialState heap env rho e1)
      (KConcatL e2 env rho KDone)
      eq_refl)
    as (phi1 & heap1 & v1 & phi_after_left &
      HLeft & HAfterLeft & HTraceLeft).
  destruct
    (KConcatL_terminal_value_is_summary
      heap1 v1 e2 env rho KDone
      phi_after_left heap_final (VSummary theta) HAfterLeft)
    as (theta1 & HTheta1).
  subst v1.
  destruct
    (KConcatL_summary_terminal_first_step
      heap1 theta1 e2 env rho KDone
      phi_after_left heap_final (VSummary theta) HAfterLeft)
    as (phi_right_tail & HRightWithKont & HTraceAfterLeft).
  destruct
    (NSteps_to_NStepsN
      (StEval heap1 env rho e2 (KConcatR theta1 KDone))
      phi_right_tail
      (StDone heap_final (VSummary theta))
      HRightWithKont)
    as (n_right & HRightWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_right
      (StEval heap1 env rho e2 (KConcatR theta1 KDone))
      phi_right_tail
      heap_final
      (VSummary theta)
      HRightWithKontN
      (NInitialState heap1 env rho e2)
      (KConcatR theta1 KDone)
      eq_refl)
    as (phi2 & heap2 & v2 & phi_after_right &
      HRight & HAfterRight & HTraceRight).
  destruct
    (KConcatR_terminal_summary_result
      heap2 theta1 v2 phi_after_right heap_final theta HAfterRight)
    as (theta2 & HTheta2 & HTheta & HHeap & HTraceAfterRight).
  subst v2 theta heap_final phi_after_right.
  exists phi1, phi2, theta1, theta2, heap1, heap2.
  repeat split; try assumption.
  rewrite HTraceStart, HTraceLeft, HTraceAfterLeft, HTraceRight.
  rewrite app_nil_r.
  reflexivity.
Qed.

Theorem EConcat_summary_deterministic_from_components :
  forall heap env rho e1 e2
    phi1 heap1 theta1 phi2 heap2 theta2
    phi heap_final theta,
    NSteps
      (NInitialState heap env rho e1)
      phi1
      (StDone heap1 (VSummary theta1)) ->
    NSteps
      (NInitialState heap1 env rho e2)
      phi2
      (StDone heap2 (VSummary theta2)) ->
    NSteps
      (NInitialState heap env rho (EConcat e1 e2))
      phi
      (StDone heap_final (VSummary theta)) ->
    theta = summary_union theta1 theta2 /\
    heap_final = heap2 /\
    phi = phi1 ++ phi2.
Proof.
  intros heap env rho e1 e2
    phi1 heap1 theta1 phi2 heap2 theta2
    phi heap_final theta HLeft HRight HConcat.
  destruct
    (EConcat_decomposition
      heap env rho e1 e2 phi heap_final theta HConcat)
    as (phi1' & phi2' & theta1' & theta2' & heap1' & heap2' &
      HLeft' & HRight' & HTheta & HHeap & HTrace).
  destruct
    (NSteps_terminal_trace_deterministic
      (NInitialState heap env rho e1)
      phi1 heap1 (VSummary theta1)
      phi1' heap1' (VSummary theta1')
      HLeft HLeft')
    as (HTrace1 & HHeap1 & HVal1).
  inversion HVal1; subst theta1'.
  subst phi1' heap1'.
  destruct
    (NSteps_terminal_trace_deterministic
      (NInitialState heap1 env rho e2)
      phi2 heap2 (VSummary theta2)
      phi2' heap2' (VSummary theta2')
      HRight HRight')
    as (HTrace2 & HHeap2 & HVal2).
  inversion HVal2; subst theta2'.
  subst phi2' heap2'.
  split; [exact HTheta |].
  split; [symmetry; exact HHeap2 |].
  exact HTrace.
Qed.

Lemma EConcat_summary_heap_neutral :
  forall e1 e2,
    SummaryHeapNeutral e1 ->
    SummaryHeapNeutral e2 ->
    SummaryHeapNeutral (EConcat e1 e2).
Proof.
  unfold SummaryHeapNeutral.
  intros e1 e2 HNeutral1 HNeutral2
    heap env rho phi heap_final theta HSteps.
  destruct
    (EConcat_decomposition
      heap env rho e1 e2 phi heap_final theta HSteps)
    as (phi1 & phi2 & theta1 & theta2 & heap1 & heap2 &
      HSteps1 & HSteps2 & _ & HHeapFinal & HTrace).
  destruct
    (HNeutral1 heap env rho phi1 heap1 theta1 HSteps1)
    as (HHeap1 & HNeutralTrace1).
  subst heap1.
  destruct
    (HNeutral2 heap env rho phi2 heap2 theta2 HSteps2)
    as (HHeap2 & HNeutralTrace2).
  subst heap2 heap_final phi.
  split.
  - reflexivity.
  - apply heap_neutral_trace_app; assumption.
Qed.

Inductive NAbstractSummaryExpr : NExpr -> Prop :=
| NASE_Empty :
    NAbstractSummaryExpr EEmpty
| NASE_Top :
    NAbstractSummaryExpr ETop
| NASE_AllocAbs :
    forall r,
      NAbstractSummaryExpr (EAllocAbs r)
| NASE_ReadAbs :
    forall r,
      NAbstractSummaryExpr (EReadAbs r)
| NASE_WriteAbs :
    forall r,
      NAbstractSummaryExpr (EWriteAbs r)
| NASE_Concat :
    forall e1 e2,
      NAbstractSummaryExpr e1 ->
      NAbstractSummaryExpr e2 ->
      NAbstractSummaryExpr (EConcat e1 e2).

Theorem NAbstractSummaryExpr_heap_neutral :
  forall e,
    NAbstractSummaryExpr e ->
    SummaryHeapNeutral e.
Proof.
  intros e HAbstract.
  induction HAbstract.
  - apply EEmpty_summary_heap_neutral.
  - apply ETop_summary_heap_neutral.
  - apply EAllocAbs_summary_heap_neutral.
  - apply EReadAbs_summary_heap_neutral.
  - apply EWriteAbs_summary_heap_neutral.
  - eapply EConcat_summary_heap_neutral; eauto.
Qed.

Corollary NAbstractSummaryExpr_trace_heap_neutral :
  forall e,
    NAbstractSummaryExpr e ->
    SummaryTraceHeapNeutral e.
Proof.
  unfold SummaryTraceHeapNeutral.
  intros e HAbstract heap env rho phi heap_final theta HSteps.
  destruct
    (NAbstractSummaryExpr_heap_neutral e HAbstract
      heap env rho phi heap_final theta HSteps)
    as (_ & HNeutral).
  exact HNeutral.
Qed.

Theorem NAbstractSummaryExpr_typed_static_heap_neutral :
  forall gamma omega e eff,
    NAbstractSummaryExpr e ->
    NTcExp gamma omega e TyEffect eff ->
    static_heap_neutral eff.
Proof.
  intros gamma omega e eff HAbstract.
  revert gamma omega eff.
  induction HAbstract; intros gamma omega eff HTyped;
    inversion HTyped; subst; try apply static_heap_neutral_nil.
  eapply static_heap_neutral_app; eauto.
Qed.

Corollary NAbstractSummaryExpr_typed_static_noalloc :
  forall gamma omega e eff,
    NAbstractSummaryExpr e ->
    NTcExp gamma omega e TyEffect eff ->
    static_noalloc eff.
Proof.
  intros gamma omega e eff HAbstract HTyped.
  destruct
    (NAbstractSummaryExpr_typed_static_heap_neutral
      gamma omega e eff HAbstract HTyped)
    as (HNoAlloc & _).
  exact HNoAlloc.
Qed.

Corollary NAbstractSummaryExpr_typed_static_readonly :
  forall gamma omega e eff,
    NAbstractSummaryExpr e ->
    NTcExp gamma omega e TyEffect eff ->
    static_readonly eff.
Proof.
  intros gamma omega e eff HAbstract HTyped.
  destruct
    (NAbstractSummaryExpr_typed_static_heap_neutral
      gamma omega e eff HAbstract HTyped)
    as (_ & HReadOnly).
  exact HReadOnly.
Qed.

Corollary NAbstractSummaryExpr_trace_no_alloc :
  forall e,
    NAbstractSummaryExpr e ->
    forall heap env rho phi heap_final theta,
      NSteps
        (NInitialState heap env rho e)
        phi
        (StDone heap_final (VSummary theta)) ->
      NoAllocTrace phi.
Proof.
  intros e HAbstract heap env rho phi heap_final theta HSteps.
  destruct
    (NAbstractSummaryExpr_trace_heap_neutral
      e HAbstract heap env rho phi heap_final theta HSteps)
    as (HNoAlloc & _).
  exact HNoAlloc.
Qed.

Corollary NAbstractSummaryExpr_trace_read_only :
  forall e,
    NAbstractSummaryExpr e ->
    forall heap env rho phi heap_final theta,
      NSteps
        (NInitialState heap env rho e)
        phi
        (StDone heap_final (VSummary theta)) ->
      ReadOnlyTrace phi.
Proof.
  intros e HAbstract heap env rho phi heap_final theta HSteps.
  destruct
    (NAbstractSummaryExpr_trace_heap_neutral
      e HAbstract heap env rho phi heap_final theta HSteps)
    as (_ & HReadOnly).
  exact HReadOnly.
Qed.

Lemma EReadConc_terminal_first_step :
  forall heap env rho e phi heap_final v_final,
    NSteps
      (NInitialState heap env rho (EReadConc e))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho e (KReadConc KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap env rho e phi heap_final v_final HSteps.
  remember (NInitialState heap env rho (EReadConc e)) as start
    eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StEval heap env rho (EReadConc e) KDone)
        LSilent
        (StEval heap env rho e (KReadConc KDone))
        label state'
        (StepReadConc heap env rho e KDone)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KReadConc_terminal_value_is_loc :
  forall heap v k phi heap_final v_final,
    NSteps
      (StReturn heap v (KReadConc k))
      phi
      (StDone heap_final v_final) ->
    exists r l,
      v = VLoc r l.
Proof.
  intros heap v k phi heap_final v_final HSteps.
  remember (StReturn heap v (KReadConc k)) as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    repeat eexists.
Qed.

Lemma KReadConc_loc_terminal_summary :
  forall heap r l phi heap_final theta,
    NSteps
      (StReturn heap (VLoc r l) (KReadConc KDone))
      phi
      (StDone heap_final (VSummary theta)) ->
    heap_final = heap /\
    theta = SummarySet [CReadConc r l] /\
    phi = [].
Proof.
  intros heap r l phi heap_final theta HSteps.
  remember
    (StReturn heap (VLoc r l) (KReadConc KDone))
    as start eqn:HStart.
  remember (StDone heap_final (VSummary theta)) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (NSteps_return_done_inv
        heap
        (VSummary (SummarySet [CReadConc r l]))
        phi0 heap_final (VSummary theta)
        HTail)
      as (HHeap & HVal & HTrace).
    simpl in *.
    inversion HVal; subst.
    repeat split; assumption || reflexivity.
Qed.

Definition EReadConcDecompositionGoal : Prop :=
  forall heap env rho e phi heap_final theta,
    NSteps
      (NInitialState heap env rho (EReadConc e))
      phi
      (StDone heap_final (VSummary theta)) ->
    exists phi_e heap_e r l,
      NSteps
        (NInitialState heap env rho e)
        phi_e
        (StDone heap_e (VLoc r l)) /\
      heap_final = heap_e /\
      theta = SummarySet [CReadConc r l] /\
      phi = phi_e.

Theorem EReadConc_decomposition :
  EReadConcDecompositionGoal.
Proof.
  unfold EReadConcDecompositionGoal.
  intros heap env rho e phi heap_final theta HSteps.
  destruct
    (EReadConc_terminal_first_step
      heap env rho e phi heap_final (VSummary theta) HSteps)
    as (phi_tail & HExprWithKont & HTraceStart).
  destruct
    (NSteps_to_NStepsN
      (StEval heap env rho e (KReadConc KDone))
      phi_tail
      (StDone heap_final (VSummary theta))
      HExprWithKont)
    as (n_expr & HExprWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_expr
      (StEval heap env rho e (KReadConc KDone))
      phi_tail
      heap_final
      (VSummary theta)
      HExprWithKontN
      (NInitialState heap env rho e)
      (KReadConc KDone)
      eq_refl)
    as (phi_e & heap_e & v_loc & phi_after_expr &
      HExpr & HAfterExpr & HTraceExpr).
  destruct
    (KReadConc_terminal_value_is_loc
      heap_e v_loc KDone
      phi_after_expr heap_final (VSummary theta) HAfterExpr)
    as (r & l & HLoc).
  subst v_loc.
  destruct
    (KReadConc_loc_terminal_summary
      heap_e r l phi_after_expr heap_final theta HAfterExpr)
    as (HHeap & HTheta & HTraceAfterExpr).
  subst heap_final theta phi_after_expr.
  exists phi_e, heap_e, r, l.
  repeat split; try assumption.
  rewrite HTraceStart, HTraceExpr.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma EWriteConc_terminal_first_step :
  forall heap env rho e phi heap_final v_final,
    NSteps
      (NInitialState heap env rho (EWriteConc e))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho e (KWriteConc KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap env rho e phi heap_final v_final HSteps.
  remember (NInitialState heap env rho (EWriteConc e)) as start
    eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StEval heap env rho (EWriteConc e) KDone)
        LSilent
        (StEval heap env rho e (KWriteConc KDone))
        label state'
        (StepWriteConc heap env rho e KDone)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KWriteConc_terminal_value_is_loc :
  forall heap v k phi heap_final v_final,
    NSteps
      (StReturn heap v (KWriteConc k))
      phi
      (StDone heap_final v_final) ->
    exists r l,
      v = VLoc r l.
Proof.
  intros heap v k phi heap_final v_final HSteps.
  remember (StReturn heap v (KWriteConc k)) as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    repeat eexists.
Qed.

Lemma KWriteConc_loc_terminal_summary :
  forall heap r l phi heap_final theta,
    NSteps
      (StReturn heap (VLoc r l) (KWriteConc KDone))
      phi
      (StDone heap_final (VSummary theta)) ->
    heap_final = heap /\
    theta = SummarySet [CWriteConc r l] /\
    phi = [].
Proof.
  intros heap r l phi heap_final theta HSteps.
  remember
    (StReturn heap (VLoc r l) (KWriteConc KDone))
    as start eqn:HStart.
  remember (StDone heap_final (VSummary theta)) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (NSteps_return_done_inv
        heap
        (VSummary (SummarySet [CWriteConc r l]))
        phi0 heap_final (VSummary theta)
        HTail)
      as (HHeap & HVal & HTrace).
    simpl in *.
    inversion HVal; subst.
    repeat split; assumption || reflexivity.
Qed.

Definition EWriteConcDecompositionGoal : Prop :=
  forall heap env rho e phi heap_final theta,
    NSteps
      (NInitialState heap env rho (EWriteConc e))
      phi
      (StDone heap_final (VSummary theta)) ->
    exists phi_e heap_e r l,
      NSteps
        (NInitialState heap env rho e)
        phi_e
        (StDone heap_e (VLoc r l)) /\
      heap_final = heap_e /\
      theta = SummarySet [CWriteConc r l] /\
      phi = phi_e.

Theorem EWriteConc_decomposition :
  EWriteConcDecompositionGoal.
Proof.
  unfold EWriteConcDecompositionGoal.
  intros heap env rho e phi heap_final theta HSteps.
  destruct
    (EWriteConc_terminal_first_step
      heap env rho e phi heap_final (VSummary theta) HSteps)
    as (phi_tail & HExprWithKont & HTraceStart).
  destruct
    (NSteps_to_NStepsN
      (StEval heap env rho e (KWriteConc KDone))
      phi_tail
      (StDone heap_final (VSummary theta))
      HExprWithKont)
    as (n_expr & HExprWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_expr
      (StEval heap env rho e (KWriteConc KDone))
      phi_tail
      heap_final
      (VSummary theta)
      HExprWithKontN
      (NInitialState heap env rho e)
      (KWriteConc KDone)
      eq_refl)
    as (phi_e & heap_e & v_loc & phi_after_expr &
      HExpr & HAfterExpr & HTraceExpr).
  destruct
    (KWriteConc_terminal_value_is_loc
      heap_e v_loc KDone
      phi_after_expr heap_final (VSummary theta) HAfterExpr)
    as (r & l & HLoc).
  subst v_loc.
  destruct
    (KWriteConc_loc_terminal_summary
      heap_e r l phi_after_expr heap_final theta HAfterExpr)
    as (HHeap & HTheta & HTraceAfterExpr).
  subst heap_final theta phi_after_expr.
  exists phi_e, heap_e, r, l.
  repeat split; try assumption.
  rewrite HTraceStart, HTraceExpr.
  rewrite app_nil_r.
  reflexivity.
Qed.
