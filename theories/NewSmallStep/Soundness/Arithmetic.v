From Stdlib Require Import List.

Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.Continuation.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.Trace.
Require Import theories.NewSmallStep.Determinism.Terminal.

Import ListNotations.

Lemma EPlus_terminal_first_step :
  forall heap env rho e1 e2 phi heap_final v_final,
    NSteps
      (NInitialState heap env rho (EPlus e1 e2))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho e1 (KPlusL e2 env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap env rho e1 e2 phi heap_final v_final HSteps.
  remember (NInitialState heap env rho (EPlus e1 e2))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StEval heap env rho (EPlus e1 e2) KDone)
        LSilent
        (StEval heap env rho e1 (KPlusL e2 env rho KDone))
        label state'
        (StepPlus heap env rho e1 e2 KDone)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KPlusL_terminal_value_is_nat :
  forall heap v e2 env rho k phi heap_final v_final,
    NSteps
      (StReturn heap v (KPlusL e2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists n,
      v = VNat n.
Proof.
  intros heap v e2 env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap v (KPlusL e2 env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    eexists. reflexivity.
Qed.

Lemma KPlusL_nat_terminal_first_step :
  forall heap n e2 env rho k phi heap_final v_final,
    NSteps
      (StReturn heap (VNat n) (KPlusL e2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho e2 (KPlusR n k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap n e2 env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap (VNat n) (KPlusL e2 env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StReturn heap (VNat n) (KPlusL e2 env rho k))
        LSilent
        (StEval heap env rho e2 (KPlusR n k))
        label state'
        (StepPlusL heap n e2 env rho k)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KPlusR_terminal_nat_result :
  forall heap n1 v phi heap_final n_final,
    NSteps
      (StReturn heap v (KPlusR n1 KDone))
      phi
      (StDone heap_final (VNat n_final)) ->
    exists n2,
      v = VNat n2 /\
      n_final = n1 + n2 /\
      heap_final = heap /\
      phi = [].
Proof.
  intros heap n1 v phi heap_final n_final HSteps.
  remember
    (StReturn heap v (KPlusR n1 KDone))
    as start eqn:HStart.
  remember (StDone heap_final (VNat n_final)) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (NSteps_known_first_step_terminal_inv
        (StReturn heap (VNat (n1 + n2)) KDone)
        LSilent
        (StDone heap (VNat (n1 + n2)))
        phi0
        heap_final
        (VNat n_final)
        (StepReturnDone heap (VNat (n1 + n2)))
        HTail)
      as (phi_done & HDone & HTraceTail).
    destruct
      (NSteps_done_inv
        heap
        (VNat (n1 + n2))
        phi_done
        (StDone heap_final (VNat n_final))
        HDone)
      as (HTraceDone & HFinalState).
    simpl in *.
    subst phi_done phi0.
    inversion HFinalState; subst.
    exists n2.
    repeat split; reflexivity.
Qed.

Definition EPlusDecompositionGoal : Prop :=
  forall heap env rho e1 e2 phi heap_final n_final,
    NSteps
      (NInitialState heap env rho (EPlus e1 e2))
      phi
      (StDone heap_final (VNat n_final)) ->
    exists phi1 phi2 n1 n2 heap1 heap2,
      NSteps
        (NInitialState heap env rho e1)
        phi1
        (StDone heap1 (VNat n1)) /\
      NSteps
        (NInitialState heap1 env rho e2)
        phi2
        (StDone heap2 (VNat n2)) /\
      n_final = n1 + n2 /\
      heap_final = heap2 /\
      phi = phi1 ++ phi2.

Theorem EPlus_decomposition :
  EPlusDecompositionGoal.
Proof.
  unfold EPlusDecompositionGoal.
  intros heap env rho e1 e2 phi heap_final n_final HSteps.
  destruct
    (EPlus_terminal_first_step
      heap env rho e1 e2 phi heap_final (VNat n_final) HSteps)
    as (phi_tail & HLeftWithKont & HTraceStart).
  destruct
    (NSteps_to_NStepsN
      (StEval heap env rho e1 (KPlusL e2 env rho KDone))
      phi_tail
      (StDone heap_final (VNat n_final))
      HLeftWithKont)
    as (n_left & HLeftWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_left
      (StEval heap env rho e1 (KPlusL e2 env rho KDone))
      phi_tail
      heap_final
      (VNat n_final)
      HLeftWithKontN
      (NInitialState heap env rho e1)
      (KPlusL e2 env rho KDone)
      eq_refl)
    as (phi1 & heap1 & v1 & phi_after_left &
      HLeft & HAfterLeft & HTraceLeft).
  destruct
    (KPlusL_terminal_value_is_nat
      heap1 v1 e2 env rho KDone
      phi_after_left heap_final (VNat n_final) HAfterLeft)
    as (n1 & HNat1).
  subst v1.
  destruct
    (KPlusL_nat_terminal_first_step
      heap1 n1 e2 env rho KDone
      phi_after_left heap_final (VNat n_final) HAfterLeft)
    as (phi_right_tail & HRightWithKont & HTraceAfterLeft).
  destruct
    (NSteps_to_NStepsN
      (StEval heap1 env rho e2 (KPlusR n1 KDone))
      phi_right_tail
      (StDone heap_final (VNat n_final))
      HRightWithKont)
    as (n_right & HRightWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_right
      (StEval heap1 env rho e2 (KPlusR n1 KDone))
      phi_right_tail
      heap_final
      (VNat n_final)
      HRightWithKontN
      (NInitialState heap1 env rho e2)
      (KPlusR n1 KDone)
      eq_refl)
    as (phi2 & heap2 & v2 & phi_after_right &
      HRight & HAfterRight & HTraceRight).
  destruct
    (KPlusR_terminal_nat_result
      heap2 n1 v2 phi_after_right heap_final n_final HAfterRight)
    as (n2 & HNat2 & HResult & HHeap & HTraceAfterRight).
  subst v2 n_final heap_final phi_after_right.
  exists phi1, phi2, n1, n2, heap1, heap2.
  repeat split; try assumption.
  rewrite HTraceStart, HTraceLeft, HTraceAfterLeft, HTraceRight.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma EMinus_terminal_first_step :
  forall heap env rho e1 e2 phi heap_final v_final,
    NSteps
      (NInitialState heap env rho (EMinus e1 e2))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho e1 (KMinusL e2 env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap env rho e1 e2 phi heap_final v_final HSteps.
  remember (NInitialState heap env rho (EMinus e1 e2))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StEval heap env rho (EMinus e1 e2) KDone)
        LSilent
        (StEval heap env rho e1 (KMinusL e2 env rho KDone))
        label state'
        (StepMinus heap env rho e1 e2 KDone)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KMinusL_terminal_value_is_nat :
  forall heap v e2 env rho k phi heap_final v_final,
    NSteps
      (StReturn heap v (KMinusL e2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists n,
      v = VNat n.
Proof.
  intros heap v e2 env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap v (KMinusL e2 env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    eexists. reflexivity.
Qed.

Lemma KMinusL_nat_terminal_first_step :
  forall heap n e2 env rho k phi heap_final v_final,
    NSteps
      (StReturn heap (VNat n) (KMinusL e2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho e2 (KMinusR n k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap n e2 env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap (VNat n) (KMinusL e2 env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StReturn heap (VNat n) (KMinusL e2 env rho k))
        LSilent
        (StEval heap env rho e2 (KMinusR n k))
        label state'
        (StepMinusL heap n e2 env rho k)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KMinusR_terminal_nat_result :
  forall heap n1 v phi heap_final n_final,
    NSteps
      (StReturn heap v (KMinusR n1 KDone))
      phi
      (StDone heap_final (VNat n_final)) ->
    exists n2,
      v = VNat n2 /\
      n_final = n1 - n2 /\
      heap_final = heap /\
      phi = [].
Proof.
  intros heap n1 v phi heap_final n_final HSteps.
  remember
    (StReturn heap v (KMinusR n1 KDone))
    as start eqn:HStart.
  remember (StDone heap_final (VNat n_final)) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (NSteps_known_first_step_terminal_inv
        (StReturn heap (VNat (n1 - n2)) KDone)
        LSilent
        (StDone heap (VNat (n1 - n2)))
        phi0
        heap_final
        (VNat n_final)
        (StepReturnDone heap (VNat (n1 - n2)))
        HTail)
      as (phi_done & HDone & HTraceTail).
    destruct
      (NSteps_done_inv
        heap
        (VNat (n1 - n2))
        phi_done
        (StDone heap_final (VNat n_final))
        HDone)
      as (HTraceDone & HFinalState).
    simpl in *.
    subst phi_done phi0.
    inversion HFinalState; subst.
    exists n2.
    repeat split; reflexivity.
Qed.

Definition EMinusDecompositionGoal : Prop :=
  forall heap env rho e1 e2 phi heap_final n_final,
    NSteps
      (NInitialState heap env rho (EMinus e1 e2))
      phi
      (StDone heap_final (VNat n_final)) ->
    exists phi1 phi2 n1 n2 heap1 heap2,
      NSteps
        (NInitialState heap env rho e1)
        phi1
        (StDone heap1 (VNat n1)) /\
      NSteps
        (NInitialState heap1 env rho e2)
        phi2
        (StDone heap2 (VNat n2)) /\
      n_final = n1 - n2 /\
      heap_final = heap2 /\
      phi = phi1 ++ phi2.

Theorem EMinus_decomposition :
  EMinusDecompositionGoal.
Proof.
  unfold EMinusDecompositionGoal.
  intros heap env rho e1 e2 phi heap_final n_final HSteps.
  destruct
    (EMinus_terminal_first_step
      heap env rho e1 e2 phi heap_final (VNat n_final) HSteps)
    as (phi_tail & HLeftWithKont & HTraceStart).
  destruct
    (NSteps_to_NStepsN
      (StEval heap env rho e1 (KMinusL e2 env rho KDone))
      phi_tail
      (StDone heap_final (VNat n_final))
      HLeftWithKont)
    as (n_left & HLeftWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_left
      (StEval heap env rho e1 (KMinusL e2 env rho KDone))
      phi_tail
      heap_final
      (VNat n_final)
      HLeftWithKontN
      (NInitialState heap env rho e1)
      (KMinusL e2 env rho KDone)
      eq_refl)
    as (phi1 & heap1 & v1 & phi_after_left &
      HLeft & HAfterLeft & HTraceLeft).
  destruct
    (KMinusL_terminal_value_is_nat
      heap1 v1 e2 env rho KDone
      phi_after_left heap_final (VNat n_final) HAfterLeft)
    as (n1 & HNat1).
  subst v1.
  destruct
    (KMinusL_nat_terminal_first_step
      heap1 n1 e2 env rho KDone
      phi_after_left heap_final (VNat n_final) HAfterLeft)
    as (phi_right_tail & HRightWithKont & HTraceAfterLeft).
  destruct
    (NSteps_to_NStepsN
      (StEval heap1 env rho e2 (KMinusR n1 KDone))
      phi_right_tail
      (StDone heap_final (VNat n_final))
      HRightWithKont)
    as (n_right & HRightWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_right
      (StEval heap1 env rho e2 (KMinusR n1 KDone))
      phi_right_tail
      heap_final
      (VNat n_final)
      HRightWithKontN
      (NInitialState heap1 env rho e2)
      (KMinusR n1 KDone)
      eq_refl)
    as (phi2 & heap2 & v2 & phi_after_right &
      HRight & HAfterRight & HTraceRight).
  destruct
    (KMinusR_terminal_nat_result
      heap2 n1 v2 phi_after_right heap_final n_final HAfterRight)
    as (n2 & HNat2 & HResult & HHeap & HTraceAfterRight).
  subst v2 n_final heap_final phi_after_right.
  exists phi1, phi2, n1, n2, heap1, heap2.
  repeat split; try assumption.
  rewrite HTraceStart, HTraceLeft, HTraceAfterLeft, HTraceRight.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma ETimes_terminal_first_step :
  forall heap env rho e1 e2 phi heap_final v_final,
    NSteps
      (NInitialState heap env rho (ETimes e1 e2))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho e1 (KTimesL e2 env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap env rho e1 e2 phi heap_final v_final HSteps.
  remember (NInitialState heap env rho (ETimes e1 e2))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StEval heap env rho (ETimes e1 e2) KDone)
        LSilent
        (StEval heap env rho e1 (KTimesL e2 env rho KDone))
        label state'
        (StepTimes heap env rho e1 e2 KDone)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KTimesL_terminal_value_is_nat :
  forall heap v e2 env rho k phi heap_final v_final,
    NSteps
      (StReturn heap v (KTimesL e2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists n,
      v = VNat n.
Proof.
  intros heap v e2 env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap v (KTimesL e2 env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    eexists. reflexivity.
Qed.

Lemma KTimesL_nat_terminal_first_step :
  forall heap n e2 env rho k phi heap_final v_final,
    NSteps
      (StReturn heap (VNat n) (KTimesL e2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho e2 (KTimesR n k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap n e2 env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap (VNat n) (KTimesL e2 env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StReturn heap (VNat n) (KTimesL e2 env rho k))
        LSilent
        (StEval heap env rho e2 (KTimesR n k))
        label state'
        (StepTimesL heap n e2 env rho k)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KTimesR_terminal_nat_result :
  forall heap n1 v phi heap_final n_final,
    NSteps
      (StReturn heap v (KTimesR n1 KDone))
      phi
      (StDone heap_final (VNat n_final)) ->
    exists n2,
      v = VNat n2 /\
      n_final = n1 * n2 /\
      heap_final = heap /\
      phi = [].
Proof.
  intros heap n1 v phi heap_final n_final HSteps.
  remember
    (StReturn heap v (KTimesR n1 KDone))
    as start eqn:HStart.
  remember (StDone heap_final (VNat n_final)) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (NSteps_known_first_step_terminal_inv
        (StReturn heap (VNat (n1 * n2)) KDone)
        LSilent
        (StDone heap (VNat (n1 * n2)))
        phi0
        heap_final
        (VNat n_final)
        (StepReturnDone heap (VNat (n1 * n2)))
        HTail)
      as (phi_done & HDone & HTraceTail).
    destruct
      (NSteps_done_inv
        heap
        (VNat (n1 * n2))
        phi_done
        (StDone heap_final (VNat n_final))
        HDone)
      as (HTraceDone & HFinalState).
    simpl in *.
    subst phi_done phi0.
    inversion HFinalState; subst.
    exists n2.
    repeat split; reflexivity.
Qed.

Definition ETimesDecompositionGoal : Prop :=
  forall heap env rho e1 e2 phi heap_final n_final,
    NSteps
      (NInitialState heap env rho (ETimes e1 e2))
      phi
      (StDone heap_final (VNat n_final)) ->
    exists phi1 phi2 n1 n2 heap1 heap2,
      NSteps
        (NInitialState heap env rho e1)
        phi1
        (StDone heap1 (VNat n1)) /\
      NSteps
        (NInitialState heap1 env rho e2)
        phi2
        (StDone heap2 (VNat n2)) /\
      n_final = n1 * n2 /\
      heap_final = heap2 /\
      phi = phi1 ++ phi2.

Theorem ETimes_decomposition :
  ETimesDecompositionGoal.
Proof.
  unfold ETimesDecompositionGoal.
  intros heap env rho e1 e2 phi heap_final n_final HSteps.
  destruct
    (ETimes_terminal_first_step
      heap env rho e1 e2 phi heap_final (VNat n_final) HSteps)
    as (phi_tail & HLeftWithKont & HTraceStart).
  destruct
    (NSteps_to_NStepsN
      (StEval heap env rho e1 (KTimesL e2 env rho KDone))
      phi_tail
      (StDone heap_final (VNat n_final))
      HLeftWithKont)
    as (n_left & HLeftWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_left
      (StEval heap env rho e1 (KTimesL e2 env rho KDone))
      phi_tail
      heap_final
      (VNat n_final)
      HLeftWithKontN
      (NInitialState heap env rho e1)
      (KTimesL e2 env rho KDone)
      eq_refl)
    as (phi1 & heap1 & v1 & phi_after_left &
      HLeft & HAfterLeft & HTraceLeft).
  destruct
    (KTimesL_terminal_value_is_nat
      heap1 v1 e2 env rho KDone
      phi_after_left heap_final (VNat n_final) HAfterLeft)
    as (n1 & HNat1).
  subst v1.
  destruct
    (KTimesL_nat_terminal_first_step
      heap1 n1 e2 env rho KDone
      phi_after_left heap_final (VNat n_final) HAfterLeft)
    as (phi_right_tail & HRightWithKont & HTraceAfterLeft).
  destruct
    (NSteps_to_NStepsN
      (StEval heap1 env rho e2 (KTimesR n1 KDone))
      phi_right_tail
      (StDone heap_final (VNat n_final))
      HRightWithKont)
    as (n_right & HRightWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_right
      (StEval heap1 env rho e2 (KTimesR n1 KDone))
      phi_right_tail
      heap_final
      (VNat n_final)
      HRightWithKontN
      (NInitialState heap1 env rho e2)
      (KTimesR n1 KDone)
      eq_refl)
    as (phi2 & heap2 & v2 & phi_after_right &
      HRight & HAfterRight & HTraceRight).
  destruct
    (KTimesR_terminal_nat_result
      heap2 n1 v2 phi_after_right heap_final n_final HAfterRight)
    as (n2 & HNat2 & HResult & HHeap & HTraceAfterRight).
  subst v2 n_final heap_final phi_after_right.
  exists phi1, phi2, n1, n2, heap1, heap2.
  repeat split; try assumption.
  rewrite HTraceStart, HTraceLeft, HTraceAfterLeft, HTraceRight.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma EEq_terminal_first_step :
  forall heap env rho e1 e2 phi heap_final v_final,
    NSteps
      (NInitialState heap env rho (EEq e1 e2))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho e1 (KEqL e2 env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap env rho e1 e2 phi heap_final v_final HSteps.
  remember (NInitialState heap env rho (EEq e1 e2))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StEval heap env rho (EEq e1 e2) KDone)
        LSilent
        (StEval heap env rho e1 (KEqL e2 env rho KDone))
        label state'
        (StepEq heap env rho e1 e2 KDone)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KEqL_terminal_value_is_nat :
  forall heap v e2 env rho k phi heap_final v_final,
    NSteps
      (StReturn heap v (KEqL e2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists n,
      v = VNat n.
Proof.
  intros heap v e2 env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap v (KEqL e2 env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    eexists. reflexivity.
Qed.

Lemma KEqL_nat_terminal_first_step :
  forall heap n e2 env rho k phi heap_final v_final,
    NSteps
      (StReturn heap (VNat n) (KEqL e2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho e2 (KEqR n k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap n e2 env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap (VNat n) (KEqL e2 env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StReturn heap (VNat n) (KEqL e2 env rho k))
        LSilent
        (StEval heap env rho e2 (KEqR n k))
        label state'
        (StepEqL heap n e2 env rho k)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KEqR_terminal_bool_result :
  forall heap n1 v phi heap_final b_final,
    NSteps
      (StReturn heap v (KEqR n1 KDone))
      phi
      (StDone heap_final (VBool b_final)) ->
    exists n2,
      v = VNat n2 /\
      b_final = Nat.eqb n1 n2 /\
      heap_final = heap /\
      phi = [].
Proof.
  intros heap n1 v phi heap_final b_final HSteps.
  remember
    (StReturn heap v (KEqR n1 KDone))
    as start eqn:HStart.
  remember (StDone heap_final (VBool b_final)) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (NSteps_known_first_step_terminal_inv
        (StReturn heap (VBool (Nat.eqb n1 n2)) KDone)
        LSilent
        (StDone heap (VBool (Nat.eqb n1 n2)))
        phi0
        heap_final
        (VBool b_final)
        (StepReturnDone heap (VBool (Nat.eqb n1 n2)))
        HTail)
      as (phi_done & HDone & HTraceTail).
    destruct
      (NSteps_done_inv
        heap
        (VBool (Nat.eqb n1 n2))
        phi_done
        (StDone heap_final (VBool b_final))
        HDone)
      as (HTraceDone & HFinalState).
    simpl in *.
    subst phi_done phi0.
    inversion HFinalState; subst.
    exists n2.
    repeat split; reflexivity.
Qed.

Definition EEqDecompositionGoal : Prop :=
  forall heap env rho e1 e2 phi heap_final b_final,
    NSteps
      (NInitialState heap env rho (EEq e1 e2))
      phi
      (StDone heap_final (VBool b_final)) ->
    exists phi1 phi2 n1 n2 heap1 heap2,
      NSteps
        (NInitialState heap env rho e1)
        phi1
        (StDone heap1 (VNat n1)) /\
      NSteps
        (NInitialState heap1 env rho e2)
        phi2
        (StDone heap2 (VNat n2)) /\
      b_final = Nat.eqb n1 n2 /\
      heap_final = heap2 /\
      phi = phi1 ++ phi2.

Theorem EEq_decomposition :
  EEqDecompositionGoal.
Proof.
  unfold EEqDecompositionGoal.
  intros heap env rho e1 e2 phi heap_final b_final HSteps.
  destruct
    (EEq_terminal_first_step
      heap env rho e1 e2 phi heap_final (VBool b_final) HSteps)
    as (phi_tail & HLeftWithKont & HTraceStart).
  destruct
    (NSteps_to_NStepsN
      (StEval heap env rho e1 (KEqL e2 env rho KDone))
      phi_tail
      (StDone heap_final (VBool b_final))
      HLeftWithKont)
    as (n_left & HLeftWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_left
      (StEval heap env rho e1 (KEqL e2 env rho KDone))
      phi_tail
      heap_final
      (VBool b_final)
      HLeftWithKontN
      (NInitialState heap env rho e1)
      (KEqL e2 env rho KDone)
      eq_refl)
    as (phi1 & heap1 & v1 & phi_after_left &
      HLeft & HAfterLeft & HTraceLeft).
  destruct
    (KEqL_terminal_value_is_nat
      heap1 v1 e2 env rho KDone
      phi_after_left heap_final (VBool b_final) HAfterLeft)
    as (n1 & HNat1).
  subst v1.
  destruct
    (KEqL_nat_terminal_first_step
      heap1 n1 e2 env rho KDone
      phi_after_left heap_final (VBool b_final) HAfterLeft)
    as (phi_right_tail & HRightWithKont & HTraceAfterLeft).
  destruct
    (NSteps_to_NStepsN
      (StEval heap1 env rho e2 (KEqR n1 KDone))
      phi_right_tail
      (StDone heap_final (VBool b_final))
      HRightWithKont)
    as (n_right & HRightWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_right
      (StEval heap1 env rho e2 (KEqR n1 KDone))
      phi_right_tail
      heap_final
      (VBool b_final)
      HRightWithKontN
      (NInitialState heap1 env rho e2)
      (KEqR n1 KDone)
      eq_refl)
    as (phi2 & heap2 & v2 & phi_after_right &
      HRight & HAfterRight & HTraceRight).
  destruct
    (KEqR_terminal_bool_result
      heap2 n1 v2 phi_after_right heap_final b_final HAfterRight)
    as (n2 & HNat2 & HResult & HHeap & HTraceAfterRight).
  subst v2 b_final heap_final phi_after_right.
  exists phi1, phi2, n1, n2, heap1, heap2.
  repeat split; try assumption.
  rewrite HTraceStart, HTraceLeft, HTraceAfterLeft, HTraceRight.
  rewrite app_nil_r.
  reflexivity.
Qed.
