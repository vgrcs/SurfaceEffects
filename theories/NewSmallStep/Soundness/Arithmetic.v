From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Program.Equality.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.Continuation.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.Trace.
Require Import theories.NewSmallStep.Soundness.BackTriangle.
Require Import theories.NewSmallStep.Soundness.Correctness.
Require Import theories.NewSmallStep.Soundness.Summary.
Require Import theories.NewSmallStep.Typing.Judgments.
Require Import theories.NewSmallStep.Typing.Regularity.
Require Import theories.NewSmallStep.Typing.Resolve.
Require Import theories.NewSmallStep.Typing.Types.
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

Lemma EPlus_terminal_first_step_N :
  forall n heap env rho e1 e2 phi heap_final v_final,
    NStepsN n
      (NInitialState heap env rho (EPlus e1 e2))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho e1 (KPlusL e2 env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap env rho e1 e2 phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (NInitialState heap env rho (EPlus e1 e2))
      LSilent
      (StEval heap env rho e1 (KPlusL e2 env rho KDone))
      phi heap_final v_final
      (StepPlus heap env rho e1 e2 KDone)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
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

Lemma KPlusL_nat_terminal_first_step_N :
  forall n_steps heap n e2 env rho k phi heap_final v_final,
    NStepsN n_steps
      (StReturn heap (VNat n) (KPlusL e2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n_steps = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho e2 (KPlusR n k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n_steps heap n e2 env rho k phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n_steps
      (StReturn heap (VNat n) (KPlusL e2 env rho k))
      LSilent
      (StEval heap env rho e2 (KPlusR n k))
      phi heap_final v_final
      (StepPlusL heap n e2 env rho k)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
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

Definition EPlusCountedDecompositionGoal : Prop :=
  forall n heap env rho e1 e2 phi heap_final n_final,
    NStepsN n
      (NInitialState heap env rho (EPlus e1 e2))
      phi
      (StDone heap_final (VNat n_final)) ->
    exists n1_steps n2_steps phi1 phi2 n1 n2 heap1 heap2,
      NStepsN n1_steps
        (NInitialState heap env rho e1)
        phi1
        (StDone heap1 (VNat n1)) /\
      NStepsN n2_steps
        (NInitialState heap1 env rho e2)
        phi2
        (StDone heap2 (VNat n2)) /\
      n_final = n1 + n2 /\
      heap_final = heap2 /\
      phi = phi1 ++ phi2 /\
      n1_steps < n /\
      n2_steps < n.

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

Theorem EPlus_counted_decomposition :
  EPlusCountedDecompositionGoal.
Proof.
  unfold EPlusCountedDecompositionGoal.
  intros n heap env rho e1 e2 phi heap_final n_final HSteps.
  destruct
    (EPlus_terminal_first_step_N
      n heap env rho e1 e2 phi heap_final (VNat n_final) HSteps)
    as (n_left_tail & phi_left_tail & HnStart &
      HLeftWithKont & HTraceStart).
  destruct
    (NStepsN_append_kont_terminal_split_counted
      n_left_tail
      (StEval heap env rho e1 (KPlusL e2 env rho KDone))
      phi_left_tail
      heap_final
      (VNat n_final)
      HLeftWithKont
      (NInitialState heap env rho e1)
      (KPlusL e2 env rho KDone)
      eq_refl)
    as (n1_steps & n_after_left & phi1 & heap1 & v1 &
      phi_after_left & HLeft & HAfterLeft & HCountLeft &
      HTraceLeft).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KPlusL_terminal_value_is_nat
        heap1 v1 e2 env rho KDone
        phi_after_left heap_final (VNat n_final)
        (NStepsN_to_NSteps
          n_after_left
          (StReturn heap1 v1 (KPlusL e2 env rho KDone))
          phi_after_left
          (StDone heap_final (VNat n_final))
          HAfterLeft))
      as (n1 & HNat1).
    subst v1.
    destruct
      (KPlusL_nat_terminal_first_step_N
        n_after_left heap1 n1 e2 env rho KDone
        phi_after_left heap_final (VNat n_final) HAfterLeft)
      as (n_right_tail & phi_right_tail & HCountAfterLeft &
        HRightWithKont & HTraceAfterLeft).
    destruct
      (NStepsN_append_kont_terminal_split_counted
        n_right_tail
        (StEval heap1 env rho e2 (KPlusR n1 KDone))
        phi_right_tail
        heap_final
        (VNat n_final)
        HRightWithKont
        (NInitialState heap1 env rho e2)
        (KPlusR n1 KDone)
        eq_refl)
      as (n2_steps & n_after_right & phi2 & heap2 & v2 &
        phi_after_right & HRight & HAfterRight & HCountRight &
        HTraceRight).
    + intros heap_done v_done HDone. inversion HDone.
    + destruct
        (KPlusR_terminal_nat_result
          heap2 n1 v2 phi_after_right heap_final n_final
          (NStepsN_to_NSteps
            n_after_right
            (StReturn heap2 v2 (KPlusR n1 KDone))
            phi_after_right
            (StDone heap_final (VNat n_final))
            HAfterRight))
        as (n2 & HNat2 & HResult & HHeap & HTraceAfterRight).
      subst v2 n_final heap_final phi_after_right.
      assert (HAfterRightPositive : 0 < n_after_right).
      { destruct n_after_right; [inversion HAfterRight | lia]. }
      exists n1_steps, n2_steps, phi1, phi2, n1, n2, heap1, heap2.
      repeat split; try assumption.
      * rewrite HTraceStart, HTraceLeft, HTraceAfterLeft, HTraceRight.
        rewrite app_nil_r.
        reflexivity.
      * lia.
      * lia.
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

Lemma EMinus_terminal_first_step_N :
  forall n heap env rho e1 e2 phi heap_final v_final,
    NStepsN n
      (NInitialState heap env rho (EMinus e1 e2))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho e1 (KMinusL e2 env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap env rho e1 e2 phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (NInitialState heap env rho (EMinus e1 e2))
      LSilent
      (StEval heap env rho e1 (KMinusL e2 env rho KDone))
      phi heap_final v_final
      (StepMinus heap env rho e1 e2 KDone)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
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

Lemma KMinusL_nat_terminal_first_step_N :
  forall n_steps heap n e2 env rho k phi heap_final v_final,
    NStepsN n_steps
      (StReturn heap (VNat n) (KMinusL e2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n_steps = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho e2 (KMinusR n k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n_steps heap n e2 env rho k phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n_steps
      (StReturn heap (VNat n) (KMinusL e2 env rho k))
      LSilent
      (StEval heap env rho e2 (KMinusR n k))
      phi heap_final v_final
      (StepMinusL heap n e2 env rho k)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
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

Definition EMinusCountedDecompositionGoal : Prop :=
  forall n heap env rho e1 e2 phi heap_final n_final,
    NStepsN n
      (NInitialState heap env rho (EMinus e1 e2))
      phi
      (StDone heap_final (VNat n_final)) ->
    exists n1_steps n2_steps phi1 phi2 n1 n2 heap1 heap2,
      NStepsN n1_steps
        (NInitialState heap env rho e1)
        phi1
        (StDone heap1 (VNat n1)) /\
      NStepsN n2_steps
        (NInitialState heap1 env rho e2)
        phi2
        (StDone heap2 (VNat n2)) /\
      n_final = n1 - n2 /\
      heap_final = heap2 /\
      phi = phi1 ++ phi2 /\
      n1_steps < n /\
      n2_steps < n.

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

Theorem EMinus_counted_decomposition :
  EMinusCountedDecompositionGoal.
Proof.
  unfold EMinusCountedDecompositionGoal.
  intros n heap env rho e1 e2 phi heap_final n_final HSteps.
  destruct
    (EMinus_terminal_first_step_N
      n heap env rho e1 e2 phi heap_final (VNat n_final) HSteps)
    as (n_left_tail & phi_left_tail & HnStart &
      HLeftWithKont & HTraceStart).
  destruct
    (NStepsN_append_kont_terminal_split_counted
      n_left_tail
      (StEval heap env rho e1 (KMinusL e2 env rho KDone))
      phi_left_tail
      heap_final
      (VNat n_final)
      HLeftWithKont
      (NInitialState heap env rho e1)
      (KMinusL e2 env rho KDone)
      eq_refl)
    as (n1_steps & n_after_left & phi1 & heap1 & v1 &
      phi_after_left & HLeft & HAfterLeft & HCountLeft &
      HTraceLeft).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KMinusL_terminal_value_is_nat
        heap1 v1 e2 env rho KDone
        phi_after_left heap_final (VNat n_final)
        (NStepsN_to_NSteps
          n_after_left
          (StReturn heap1 v1 (KMinusL e2 env rho KDone))
          phi_after_left
          (StDone heap_final (VNat n_final))
          HAfterLeft))
      as (n1 & HNat1).
    subst v1.
    destruct
      (KMinusL_nat_terminal_first_step_N
        n_after_left heap1 n1 e2 env rho KDone
        phi_after_left heap_final (VNat n_final) HAfterLeft)
      as (n_right_tail & phi_right_tail & HCountAfterLeft &
        HRightWithKont & HTraceAfterLeft).
    destruct
      (NStepsN_append_kont_terminal_split_counted
        n_right_tail
        (StEval heap1 env rho e2 (KMinusR n1 KDone))
        phi_right_tail
        heap_final
        (VNat n_final)
        HRightWithKont
        (NInitialState heap1 env rho e2)
        (KMinusR n1 KDone)
        eq_refl)
      as (n2_steps & n_after_right & phi2 & heap2 & v2 &
        phi_after_right & HRight & HAfterRight & HCountRight &
        HTraceRight).
    + intros heap_done v_done HDone. inversion HDone.
    + destruct
        (KMinusR_terminal_nat_result
          heap2 n1 v2 phi_after_right heap_final n_final
          (NStepsN_to_NSteps
            n_after_right
            (StReturn heap2 v2 (KMinusR n1 KDone))
            phi_after_right
            (StDone heap_final (VNat n_final))
            HAfterRight))
        as (n2 & HNat2 & HResult & HHeap & HTraceAfterRight).
      subst v2 n_final heap_final phi_after_right.
      assert (HAfterRightPositive : 0 < n_after_right).
      { destruct n_after_right; [inversion HAfterRight | lia]. }
      exists n1_steps, n2_steps, phi1, phi2, n1, n2, heap1, heap2.
      repeat split; try assumption.
      * rewrite HTraceStart, HTraceLeft, HTraceAfterLeft, HTraceRight.
        rewrite app_nil_r.
        reflexivity.
      * lia.
      * lia.
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

Lemma ETimes_terminal_first_step_N :
  forall n heap env rho e1 e2 phi heap_final v_final,
    NStepsN n
      (NInitialState heap env rho (ETimes e1 e2))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho e1 (KTimesL e2 env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap env rho e1 e2 phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (NInitialState heap env rho (ETimes e1 e2))
      LSilent
      (StEval heap env rho e1 (KTimesL e2 env rho KDone))
      phi heap_final v_final
      (StepTimes heap env rho e1 e2 KDone)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
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

Lemma KTimesL_nat_terminal_first_step_N :
  forall n_steps heap n e2 env rho k phi heap_final v_final,
    NStepsN n_steps
      (StReturn heap (VNat n) (KTimesL e2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n_steps = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho e2 (KTimesR n k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n_steps heap n e2 env rho k phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n_steps
      (StReturn heap (VNat n) (KTimesL e2 env rho k))
      LSilent
      (StEval heap env rho e2 (KTimesR n k))
      phi heap_final v_final
      (StepTimesL heap n e2 env rho k)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
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

Definition ETimesCountedDecompositionGoal : Prop :=
  forall n heap env rho e1 e2 phi heap_final n_final,
    NStepsN n
      (NInitialState heap env rho (ETimes e1 e2))
      phi
      (StDone heap_final (VNat n_final)) ->
    exists n1_steps n2_steps phi1 phi2 n1 n2 heap1 heap2,
      NStepsN n1_steps
        (NInitialState heap env rho e1)
        phi1
        (StDone heap1 (VNat n1)) /\
      NStepsN n2_steps
        (NInitialState heap1 env rho e2)
        phi2
        (StDone heap2 (VNat n2)) /\
      n_final = n1 * n2 /\
      heap_final = heap2 /\
      phi = phi1 ++ phi2 /\
      n1_steps < n /\
      n2_steps < n.

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

Theorem ETimes_counted_decomposition :
  ETimesCountedDecompositionGoal.
Proof.
  unfold ETimesCountedDecompositionGoal.
  intros n heap env rho e1 e2 phi heap_final n_final HSteps.
  destruct
    (ETimes_terminal_first_step_N
      n heap env rho e1 e2 phi heap_final (VNat n_final) HSteps)
    as (n_left_tail & phi_left_tail & HnStart &
      HLeftWithKont & HTraceStart).
  destruct
    (NStepsN_append_kont_terminal_split_counted
      n_left_tail
      (StEval heap env rho e1 (KTimesL e2 env rho KDone))
      phi_left_tail
      heap_final
      (VNat n_final)
      HLeftWithKont
      (NInitialState heap env rho e1)
      (KTimesL e2 env rho KDone)
      eq_refl)
    as (n1_steps & n_after_left & phi1 & heap1 & v1 &
      phi_after_left & HLeft & HAfterLeft & HCountLeft &
      HTraceLeft).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KTimesL_terminal_value_is_nat
        heap1 v1 e2 env rho KDone
        phi_after_left heap_final (VNat n_final)
        (NStepsN_to_NSteps
          n_after_left
          (StReturn heap1 v1 (KTimesL e2 env rho KDone))
          phi_after_left
          (StDone heap_final (VNat n_final))
          HAfterLeft))
      as (n1 & HNat1).
    subst v1.
    destruct
      (KTimesL_nat_terminal_first_step_N
        n_after_left heap1 n1 e2 env rho KDone
        phi_after_left heap_final (VNat n_final) HAfterLeft)
      as (n_right_tail & phi_right_tail & HCountAfterLeft &
        HRightWithKont & HTraceAfterLeft).
    destruct
      (NStepsN_append_kont_terminal_split_counted
        n_right_tail
        (StEval heap1 env rho e2 (KTimesR n1 KDone))
        phi_right_tail
        heap_final
        (VNat n_final)
        HRightWithKont
        (NInitialState heap1 env rho e2)
        (KTimesR n1 KDone)
        eq_refl)
      as (n2_steps & n_after_right & phi2 & heap2 & v2 &
        phi_after_right & HRight & HAfterRight & HCountRight &
        HTraceRight).
    + intros heap_done v_done HDone. inversion HDone.
    + destruct
        (KTimesR_terminal_nat_result
          heap2 n1 v2 phi_after_right heap_final n_final
          (NStepsN_to_NSteps
            n_after_right
            (StReturn heap2 v2 (KTimesR n1 KDone))
            phi_after_right
            (StDone heap_final (VNat n_final))
            HAfterRight))
        as (n2 & HNat2 & HResult & HHeap & HTraceAfterRight).
      subst v2 n_final heap_final phi_after_right.
      assert (HAfterRightPositive : 0 < n_after_right).
      { destruct n_after_right; [inversion HAfterRight | lia]. }
      exists n1_steps, n2_steps, phi1, phi2, n1, n2, heap1, heap2.
      repeat split; try assumption.
      * rewrite HTraceStart, HTraceLeft, HTraceAfterLeft, HTraceRight.
        rewrite app_nil_r.
        reflexivity.
      * lia.
      * lia.
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

Lemma EEq_terminal_first_step_N :
  forall n heap env rho e1 e2 phi heap_final v_final,
    NStepsN n
      (NInitialState heap env rho (EEq e1 e2))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho e1 (KEqL e2 env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap env rho e1 e2 phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (NInitialState heap env rho (EEq e1 e2))
      LSilent
      (StEval heap env rho e1 (KEqL e2 env rho KDone))
      phi heap_final v_final
      (StepEq heap env rho e1 e2 KDone)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
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

Lemma KEqL_nat_terminal_first_step_N :
  forall n_steps heap n e2 env rho k phi heap_final v_final,
    NStepsN n_steps
      (StReturn heap (VNat n) (KEqL e2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n_steps = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho e2 (KEqR n k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n_steps heap n e2 env rho k phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n_steps
      (StReturn heap (VNat n) (KEqL e2 env rho k))
      LSilent
      (StEval heap env rho e2 (KEqR n k))
      phi heap_final v_final
      (StepEqL heap n e2 env rho k)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
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

Definition EEqCountedDecompositionGoal : Prop :=
  forall n heap env rho e1 e2 phi heap_final b_final,
    NStepsN n
      (NInitialState heap env rho (EEq e1 e2))
      phi
      (StDone heap_final (VBool b_final)) ->
    exists n1_steps n2_steps phi1 phi2 n1 n2 heap1 heap2,
      NStepsN n1_steps
        (NInitialState heap env rho e1)
        phi1
        (StDone heap1 (VNat n1)) /\
      NStepsN n2_steps
        (NInitialState heap1 env rho e2)
        phi2
        (StDone heap2 (VNat n2)) /\
      b_final = Nat.eqb n1 n2 /\
      heap_final = heap2 /\
      phi = phi1 ++ phi2 /\
      n1_steps < n /\
      n2_steps < n.

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

Theorem EEq_counted_decomposition :
  EEqCountedDecompositionGoal.
Proof.
  unfold EEqCountedDecompositionGoal.
  intros n heap env rho e1 e2 phi heap_final b_final HSteps.
  destruct
    (EEq_terminal_first_step_N
      n heap env rho e1 e2 phi heap_final (VBool b_final) HSteps)
    as (n_left_tail & phi_left_tail & HnStart &
      HLeftWithKont & HTraceStart).
  destruct
    (NStepsN_append_kont_terminal_split_counted
      n_left_tail
      (StEval heap env rho e1 (KEqL e2 env rho KDone))
      phi_left_tail
      heap_final
      (VBool b_final)
      HLeftWithKont
      (NInitialState heap env rho e1)
      (KEqL e2 env rho KDone)
      eq_refl)
    as (n1_steps & n_after_left & phi1 & heap1 & v1 &
      phi_after_left & HLeft & HAfterLeft & HCountLeft &
      HTraceLeft).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KEqL_terminal_value_is_nat
        heap1 v1 e2 env rho KDone
        phi_after_left heap_final (VBool b_final)
        (NStepsN_to_NSteps
          n_after_left
          (StReturn heap1 v1 (KEqL e2 env rho KDone))
          phi_after_left
          (StDone heap_final (VBool b_final))
          HAfterLeft))
      as (n1 & HNat1).
    subst v1.
    destruct
      (KEqL_nat_terminal_first_step_N
        n_after_left heap1 n1 e2 env rho KDone
        phi_after_left heap_final (VBool b_final) HAfterLeft)
      as (n_right_tail & phi_right_tail & HCountAfterLeft &
        HRightWithKont & HTraceAfterLeft).
    destruct
      (NStepsN_append_kont_terminal_split_counted
        n_right_tail
        (StEval heap1 env rho e2 (KEqR n1 KDone))
        phi_right_tail
        heap_final
        (VBool b_final)
        HRightWithKont
        (NInitialState heap1 env rho e2)
        (KEqR n1 KDone)
        eq_refl)
      as (n2_steps & n_after_right & phi2 & heap2 & v2 &
        phi_after_right & HRight & HAfterRight & HCountRight &
        HTraceRight).
    + intros heap_done v_done HDone. inversion HDone.
    + destruct
        (KEqR_terminal_bool_result
          heap2 n1 v2 phi_after_right heap_final b_final
          (NStepsN_to_NSteps
            n_after_right
            (StReturn heap2 v2 (KEqR n1 KDone))
            phi_after_right
            (StDone heap_final (VBool b_final))
            HAfterRight))
        as (n2 & HNat2 & HResult & HHeap & HTraceAfterRight).
      subst v2 b_final heap_final phi_after_right.
      assert (HAfterRightPositive : 0 < n_after_right).
      { destruct n_after_right; [inversion HAfterRight | lia]. }
      exists n1_steps, n2_steps, phi1, phi2, n1, n2, heap1, heap2.
      repeat split; try assumption.
      * rewrite HTraceStart, HTraceLeft, HTraceAfterLeft, HTraceRight.
        rewrite app_nil_r.
        reflexivity.
	      * lia.
	      * lia.
Qed.

Lemma NCBT_Plus_components :
  forall gamma omega e1 e2 eff1 eff2,
    NCheckedBackTriangle gamma omega
      (EPlus e1 e2) (EConcat eff1 eff2) ->
    exists eff_static eff_e1,
      NCheckedTcExp gamma omega (EPlus e1 e2) TyNat eff_static /\
      NCheckedTcExp gamma omega e1 TyNat eff_e1 /\
      static_heap_neutral eff_e1 /\
      NCheckedBackTriangle gamma omega e1 eff1 /\
      NCheckedBackTriangle gamma omega e2 eff2.
Proof.
  intros gamma omega e1 e2 eff1 eff2 HBack.
  inversion HBack; subst; try discriminate.
  exists eff_static, eff_e1.
  split; [exact H3 |].
  split; [exact H6 |].
  split; [exact H7 |].
  split; assumption.
Qed.

Theorem EPlus_checked_store_context_case_from_below :
  forall n gamma omega heap env rho e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EPlus e1 e2) (EConcat eff1 eff2) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EPlus e1 e2) phi heap_final v_final ->
    SummaryEvaluation heap env rho (EConcat eff1 eff2)
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext HComputationTraceSound HComp HSummary.
  destruct
    (NCBT_Plus_components gamma omega e1 e2 eff1 eff2 HBack)
    as (eff_static & eff_e1 & HCheckedPlus & HCheckedLeft &
      HNeutralLeft & HBackLeft & HBackRight).
  assert (HCompForShape := HComp).
  destruct
    (checked_store_counted_computation_store_value_shape_resolved
      n gamma omega heap env rho (EPlus e1 e2) TyNat eff_static
      phi heap_final v_final HContext HCheckedPlus HCompForShape)
    as (store_final & ty_res & HResolveTy & _HBoundedFinal &
      _HHeapFinal & HValFinal).
  assert (ty_res = TyNat) as HTyRes.
  {
    eapply NResolveTy_deterministic.
    - exact HResolveTy.
    - constructor.
  }
  subst ty_res.
  inversion HValFinal; subst v_final.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (EPlus_counted_decomposition
      n heap env rho e1 e2 phi heap_final n0 HComp)
    as (n1_steps & n2_steps & phi1 & phi2 & n1 & n2 &
      heap1 & heap2 & HLeft & HRight & _HResult & HHeapFinal &
      HTrace & HCountLeft & HCountRight).
  subst heap_final.
  unfold SummaryEvaluation in HSummary.
  destruct
    (EConcat_decomposition
      heap env rho eff1 eff2 phi_summary heap_summary theta HSummary)
    as (phi_summary1 & phi_summary2 & theta1 & theta2 &
      heap_summary1 & heap_summary2 & HSummary1 & HSummary2 &
      HTheta & _HHeapSummary & _HTraceSummary).
  destruct
    (NCheckedBackTriangle_summary_checked_heap_neutral
      gamma omega e1 eff1 HBackLeft)
    as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
  destruct
    (NSteps_to_NStepsN
      (NInitialState heap env rho eff1)
      phi_summary1
      (StDone heap_summary1 (VSummary theta1))
      HSummary1)
    as (n_summary1 & HSummary1N).
  destruct
    (checked_store_counted_computation_heap_neutral
      n_summary1 gamma omega heap env rho eff1 TyEffect eff_summary1
      phi_summary1 heap_summary1 (VSummary theta1)
      HContext HComputationTraceSound HCheckedSummary1 HNeutralSummary1)
    as (HHeapSummary1 & _).
  {
    unfold CountedComputationEvaluation.
    exact HSummary1N.
  }
  subst heap_summary1.
  destruct
    (checked_store_counted_computation_heap_neutral
      n1_steps gamma omega heap env rho e1 TyNat eff_e1
      phi1 heap1 (VNat n1)
      HContext HComputationTraceSound HCheckedLeft HNeutralLeft)
    as (HHeap1 & _).
  {
    unfold CountedComputationEvaluation.
    exact HLeft.
  }
  subst heap1.
  assert (HCoveredLeft : TraceCoveredBySummary phi1 theta1).
  {
    eapply
      (HBelow n1_steps gamma omega heap env rho e1 eff1
        phi1 heap (VNat n1) phi_summary1 heap theta1).
    - exact HCountLeft.
    - exact HBackLeft.
    - exact HContext.
    - unfold CountedComputationEvaluation. exact HLeft.
    - unfold SummaryEvaluation. exact HSummary1.
  }
  assert (HCoveredRight : TraceCoveredBySummary phi2 theta2).
  {
    eapply
      (HBelow n2_steps gamma omega heap env rho e2 eff2
        phi2 heap2 (VNat n2) phi_summary2 heap_summary2 theta2).
    - exact HCountRight.
    - exact HBackRight.
    - exact HContext.
    - unfold CountedComputationEvaluation. exact HRight.
    - unfold SummaryEvaluation. exact HSummary2.
  }
  subst phi theta.
  eapply trace_covered_app_summary_union; eauto.
Qed.

Lemma NCBT_Minus_components :
  forall gamma omega e1 e2 eff1 eff2,
    NCheckedBackTriangle gamma omega
      (EMinus e1 e2) (EConcat eff1 eff2) ->
    exists eff_static eff_e1,
      NCheckedTcExp gamma omega (EMinus e1 e2) TyNat eff_static /\
      NCheckedTcExp gamma omega e1 TyNat eff_e1 /\
      static_heap_neutral eff_e1 /\
      NCheckedBackTriangle gamma omega e1 eff1 /\
      NCheckedBackTriangle gamma omega e2 eff2.
Proof.
  intros gamma omega e1 e2 eff1 eff2 HBack.
  inversion HBack; subst; try discriminate.
  exists eff_static, eff_e1.
  split; [exact H3 |].
  split; [exact H6 |].
  split; [exact H7 |].
  split; assumption.
Qed.

Theorem EMinus_checked_store_context_case_from_below :
  forall n gamma omega heap env rho e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EMinus e1 e2) (EConcat eff1 eff2) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EMinus e1 e2) phi heap_final v_final ->
    SummaryEvaluation heap env rho (EConcat eff1 eff2)
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext HComputationTraceSound HComp HSummary.
  destruct
    (NCBT_Minus_components gamma omega e1 e2 eff1 eff2 HBack)
    as (eff_static & eff_e1 & HCheckedMinus & HCheckedLeft &
      HNeutralLeft & HBackLeft & HBackRight).
  assert (HCompForShape := HComp).
  destruct
    (checked_store_counted_computation_store_value_shape_resolved
      n gamma omega heap env rho (EMinus e1 e2) TyNat eff_static
      phi heap_final v_final HContext HCheckedMinus HCompForShape)
    as (store_final & ty_res & HResolveTy & _HBoundedFinal &
      _HHeapFinal & HValFinal).
  assert (ty_res = TyNat) as HTyRes.
  {
    eapply NResolveTy_deterministic.
    - exact HResolveTy.
    - constructor.
  }
  subst ty_res.
  inversion HValFinal; subst v_final.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (EMinus_counted_decomposition
      n heap env rho e1 e2 phi heap_final n0 HComp)
    as (n1_steps & n2_steps & phi1 & phi2 & n1 & n2 &
      heap1 & heap2 & HLeft & HRight & _HResult & HHeapFinal &
      HTrace & HCountLeft & HCountRight).
  subst heap_final.
  unfold SummaryEvaluation in HSummary.
  destruct
    (EConcat_decomposition
      heap env rho eff1 eff2 phi_summary heap_summary theta HSummary)
    as (phi_summary1 & phi_summary2 & theta1 & theta2 &
      heap_summary1 & heap_summary2 & HSummary1 & HSummary2 &
      HTheta & _HHeapSummary & _HTraceSummary).
  destruct
    (NCheckedBackTriangle_summary_checked_heap_neutral
      gamma omega e1 eff1 HBackLeft)
    as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
  destruct
    (NSteps_to_NStepsN
      (NInitialState heap env rho eff1)
      phi_summary1
      (StDone heap_summary1 (VSummary theta1))
      HSummary1)
    as (n_summary1 & HSummary1N).
  destruct
    (checked_store_counted_computation_heap_neutral
      n_summary1 gamma omega heap env rho eff1 TyEffect eff_summary1
      phi_summary1 heap_summary1 (VSummary theta1)
      HContext HComputationTraceSound HCheckedSummary1 HNeutralSummary1)
    as (HHeapSummary1 & _).
  {
    unfold CountedComputationEvaluation.
    exact HSummary1N.
  }
  subst heap_summary1.
  destruct
    (checked_store_counted_computation_heap_neutral
      n1_steps gamma omega heap env rho e1 TyNat eff_e1
      phi1 heap1 (VNat n1)
      HContext HComputationTraceSound HCheckedLeft HNeutralLeft)
    as (HHeap1 & _).
  {
    unfold CountedComputationEvaluation.
    exact HLeft.
  }
  subst heap1.
  assert (HCoveredLeft : TraceCoveredBySummary phi1 theta1).
  {
    eapply
      (HBelow n1_steps gamma omega heap env rho e1 eff1
        phi1 heap (VNat n1) phi_summary1 heap theta1).
    - exact HCountLeft.
    - exact HBackLeft.
    - exact HContext.
    - unfold CountedComputationEvaluation. exact HLeft.
    - unfold SummaryEvaluation. exact HSummary1.
  }
  assert (HCoveredRight : TraceCoveredBySummary phi2 theta2).
  {
    eapply
      (HBelow n2_steps gamma omega heap env rho e2 eff2
        phi2 heap2 (VNat n2) phi_summary2 heap_summary2 theta2).
    - exact HCountRight.
    - exact HBackRight.
    - exact HContext.
    - unfold CountedComputationEvaluation. exact HRight.
    - unfold SummaryEvaluation. exact HSummary2.
  }
  subst phi theta.
  eapply trace_covered_app_summary_union; eauto.
Qed.

Lemma NCBT_Times_components :
  forall gamma omega e1 e2 eff1 eff2,
    NCheckedBackTriangle gamma omega
      (ETimes e1 e2) (EConcat eff1 eff2) ->
    exists eff_static eff_e1,
      NCheckedTcExp gamma omega (ETimes e1 e2) TyNat eff_static /\
      NCheckedTcExp gamma omega e1 TyNat eff_e1 /\
      static_heap_neutral eff_e1 /\
      NCheckedBackTriangle gamma omega e1 eff1 /\
      NCheckedBackTriangle gamma omega e2 eff2.
Proof.
  intros gamma omega e1 e2 eff1 eff2 HBack.
  inversion HBack; subst; try discriminate.
  exists eff_static, eff_e1.
  split; [exact H3 |].
  split; [exact H6 |].
  split; [exact H7 |].
  split; assumption.
Qed.

Theorem ETimes_checked_store_context_case_from_below :
  forall n gamma omega heap env rho e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega
      (ETimes e1 e2) (EConcat eff1 eff2) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (ETimes e1 e2) phi heap_final v_final ->
    SummaryEvaluation heap env rho (EConcat eff1 eff2)
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext HComputationTraceSound HComp HSummary.
  destruct
    (NCBT_Times_components gamma omega e1 e2 eff1 eff2 HBack)
    as (eff_static & eff_e1 & HCheckedTimes & HCheckedLeft &
      HNeutralLeft & HBackLeft & HBackRight).
  assert (HCompForShape := HComp).
  destruct
    (checked_store_counted_computation_store_value_shape_resolved
      n gamma omega heap env rho (ETimes e1 e2) TyNat eff_static
      phi heap_final v_final HContext HCheckedTimes HCompForShape)
    as (store_final & ty_res & HResolveTy & _HBoundedFinal &
      _HHeapFinal & HValFinal).
  assert (ty_res = TyNat) as HTyRes.
  {
    eapply NResolveTy_deterministic.
    - exact HResolveTy.
    - constructor.
  }
  subst ty_res.
  inversion HValFinal; subst v_final.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (ETimes_counted_decomposition
      n heap env rho e1 e2 phi heap_final n0 HComp)
    as (n1_steps & n2_steps & phi1 & phi2 & n1 & n2 &
      heap1 & heap2 & HLeft & HRight & _HResult & HHeapFinal &
      HTrace & HCountLeft & HCountRight).
  subst heap_final.
  unfold SummaryEvaluation in HSummary.
  destruct
    (EConcat_decomposition
      heap env rho eff1 eff2 phi_summary heap_summary theta HSummary)
    as (phi_summary1 & phi_summary2 & theta1 & theta2 &
      heap_summary1 & heap_summary2 & HSummary1 & HSummary2 &
      HTheta & _HHeapSummary & _HTraceSummary).
  destruct
    (NCheckedBackTriangle_summary_checked_heap_neutral
      gamma omega e1 eff1 HBackLeft)
    as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
  destruct
    (NSteps_to_NStepsN
      (NInitialState heap env rho eff1)
      phi_summary1
      (StDone heap_summary1 (VSummary theta1))
      HSummary1)
    as (n_summary1 & HSummary1N).
  destruct
    (checked_store_counted_computation_heap_neutral
      n_summary1 gamma omega heap env rho eff1 TyEffect eff_summary1
      phi_summary1 heap_summary1 (VSummary theta1)
      HContext HComputationTraceSound HCheckedSummary1 HNeutralSummary1)
    as (HHeapSummary1 & _).
  {
    unfold CountedComputationEvaluation.
    exact HSummary1N.
  }
  subst heap_summary1.
  destruct
    (checked_store_counted_computation_heap_neutral
      n1_steps gamma omega heap env rho e1 TyNat eff_e1
      phi1 heap1 (VNat n1)
      HContext HComputationTraceSound HCheckedLeft HNeutralLeft)
    as (HHeap1 & _).
  {
    unfold CountedComputationEvaluation.
    exact HLeft.
  }
  subst heap1.
  assert (HCoveredLeft : TraceCoveredBySummary phi1 theta1).
  {
    eapply
      (HBelow n1_steps gamma omega heap env rho e1 eff1
        phi1 heap (VNat n1) phi_summary1 heap theta1).
    - exact HCountLeft.
    - exact HBackLeft.
    - exact HContext.
    - unfold CountedComputationEvaluation. exact HLeft.
    - unfold SummaryEvaluation. exact HSummary1.
  }
  assert (HCoveredRight : TraceCoveredBySummary phi2 theta2).
  {
    eapply
      (HBelow n2_steps gamma omega heap env rho e2 eff2
        phi2 heap2 (VNat n2) phi_summary2 heap_summary2 theta2).
    - exact HCountRight.
    - exact HBackRight.
    - exact HContext.
    - unfold CountedComputationEvaluation. exact HRight.
    - unfold SummaryEvaluation. exact HSummary2.
  }
  subst phi theta.
  eapply trace_covered_app_summary_union; eauto.
Qed.

Lemma NCBT_Eq_components :
  forall gamma omega e1 e2 eff1 eff2,
    NCheckedBackTriangle gamma omega
      (EEq e1 e2) (EConcat eff1 eff2) ->
    exists eff_static eff_e1,
      NCheckedTcExp gamma omega (EEq e1 e2) TyBool eff_static /\
      NCheckedTcExp gamma omega e1 TyNat eff_e1 /\
      static_heap_neutral eff_e1 /\
      NCheckedBackTriangle gamma omega e1 eff1 /\
      NCheckedBackTriangle gamma omega e2 eff2.
Proof.
  intros gamma omega e1 e2 eff1 eff2 HBack.
  inversion HBack; subst; try discriminate.
  exists eff_static, eff_e1.
  split; [exact H3 |].
  split; [exact H6 |].
  split; [exact H7 |].
  split; assumption.
Qed.

Theorem EEq_checked_store_context_case_from_below :
  forall n gamma omega heap env rho e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EEq e1 e2) (EConcat eff1 eff2) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EEq e1 e2) phi heap_final v_final ->
    SummaryEvaluation heap env rho (EConcat eff1 eff2)
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext HComputationTraceSound HComp HSummary.
  destruct
    (NCBT_Eq_components gamma omega e1 e2 eff1 eff2 HBack)
    as (eff_static & eff_e1 & HCheckedEq & HCheckedLeft &
      HNeutralLeft & HBackLeft & HBackRight).
  assert (HCompForShape := HComp).
  destruct
    (checked_store_counted_computation_store_value_shape_resolved
      n gamma omega heap env rho (EEq e1 e2) TyBool eff_static
      phi heap_final v_final HContext HCheckedEq HCompForShape)
    as (store_final & ty_res & HResolveTy & _HBoundedFinal &
      _HHeapFinal & HValFinal).
  assert (ty_res = TyBool) as HTyRes.
  {
    eapply NResolveTy_deterministic.
    - exact HResolveTy.
    - constructor.
  }
  subst ty_res.
  inversion HValFinal; subst v_final.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (EEq_counted_decomposition
      n heap env rho e1 e2 phi heap_final b HComp)
    as (n1_steps & n2_steps & phi1 & phi2 & n1 & n2 &
      heap1 & heap2 & HLeft & HRight & _HResult & HHeapFinal &
      HTrace & HCountLeft & HCountRight).
  subst heap_final.
  unfold SummaryEvaluation in HSummary.
  destruct
    (EConcat_decomposition
      heap env rho eff1 eff2 phi_summary heap_summary theta HSummary)
    as (phi_summary1 & phi_summary2 & theta1 & theta2 &
      heap_summary1 & heap_summary2 & HSummary1 & HSummary2 &
      HTheta & _HHeapSummary & _HTraceSummary).
  destruct
    (NCheckedBackTriangle_summary_checked_heap_neutral
      gamma omega e1 eff1 HBackLeft)
    as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
  destruct
    (NSteps_to_NStepsN
      (NInitialState heap env rho eff1)
      phi_summary1
      (StDone heap_summary1 (VSummary theta1))
      HSummary1)
    as (n_summary1 & HSummary1N).
  destruct
    (checked_store_counted_computation_heap_neutral
      n_summary1 gamma omega heap env rho eff1 TyEffect eff_summary1
      phi_summary1 heap_summary1 (VSummary theta1)
      HContext HComputationTraceSound HCheckedSummary1 HNeutralSummary1)
    as (HHeapSummary1 & _).
  {
    unfold CountedComputationEvaluation.
    exact HSummary1N.
  }
  subst heap_summary1.
  destruct
    (checked_store_counted_computation_heap_neutral
      n1_steps gamma omega heap env rho e1 TyNat eff_e1
      phi1 heap1 (VNat n1)
      HContext HComputationTraceSound HCheckedLeft HNeutralLeft)
    as (HHeap1 & _).
  {
    unfold CountedComputationEvaluation.
    exact HLeft.
  }
  subst heap1.
  assert (HCoveredLeft : TraceCoveredBySummary phi1 theta1).
  {
    eapply
      (HBelow n1_steps gamma omega heap env rho e1 eff1
        phi1 heap (VNat n1) phi_summary1 heap theta1).
    - exact HCountLeft.
    - exact HBackLeft.
    - exact HContext.
    - unfold CountedComputationEvaluation. exact HLeft.
    - unfold SummaryEvaluation. exact HSummary1.
  }
  assert (HCoveredRight : TraceCoveredBySummary phi2 theta2).
  {
    eapply
      (HBelow n2_steps gamma omega heap env rho e2 eff2
        phi2 heap2 (VNat n2) phi_summary2 heap_summary2 theta2).
    - exact HCountRight.
    - exact HBackRight.
    - exact HContext.
    - unfold CountedComputationEvaluation. exact HRight.
    - unfold SummaryEvaluation. exact HSummary2.
  }
  subst phi theta.
  eapply trace_covered_app_summary_union; eauto.
Qed.
