From Stdlib Require Import List.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.Continuation.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.Trace.
Require Import theories.NewSmallStep.Determinism.Terminal.

Import ListNotations.

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
