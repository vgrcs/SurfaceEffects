From Stdlib Require Import Lia.
From Stdlib Require Import List.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.Continuation.
Require Import theories.NewSmallStep.Runtime.HeapNeutral.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.RegularStateShape.
Require Import theories.NewSmallStep.Runtime.Trace.
Require Import theories.NewSmallStep.Soundness.App.
Require Import theories.NewSmallStep.Soundness.Correctness.
Require Import theories.NewSmallStep.Soundness.Summary.
Require Import theories.NewSmallStep.Determinism.Terminal.
Require Import theories.NewSmallStep.Typing.Judgments.
Require Import theories.NewSmallStep.Typing.Regularity.
Require Import theories.NewSmallStep.Typing.Resolve.
Require Import theories.NewSmallStep.Typing.Types.

Import ListNotations.

Lemma StError_no_done :
  forall heap_error phi heap v,
    ~ NSteps (StError heap_error) phi (StDone heap v).
Proof.
  intros heap_error phi heap v HSteps.
  remember (StError heap_error) as start eqn:HStart.
  remember (StDone heap v) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep.
Qed.

Lemma StError_no_done_N :
  forall n heap_error phi heap v,
    ~ NStepsN n (StError heap_error) phi (StDone heap v).
Proof.
  intros n heap_error phi heap v HSteps.
  eapply StError_no_done.
  eapply NStepsN_to_NSteps; eauto.
Qed.

Lemma with_state_heap_idempotent :
  forall heap1 heap2 state,
    with_state_heap heap1 (with_state_heap heap2 state) =
    with_state_heap heap1 state.
Proof.
  intros heap1 heap2 state.
  induction state as
    [heap env rho e k | heap v k | heap v
    | left_state IHLeft right_state IHRight phi_left phi_right k
    | heap];
    simpl; try reflexivity.
  rewrite IHLeft, IHRight.
  reflexivity.
Qed.

Lemma NCBT_PairPar_summary_static_heap_neutral :
  forall gamma omega ef1 ea1 ef2 ea2,
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    exists ty1 ty2 eff1 eff2 eff_summary1 eff_summary2,
      NCheckedTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 /\
      NCheckedTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 /\
      NCheckedTcExp gamma omega (EEffApp ef1 ea1) TyEffect
        eff_summary1 /\
      NCheckedTcExp gamma omega (EEffApp ef2 ea2) TyEffect
        eff_summary2 /\
      static_heap_neutral eff_summary1 /\
      static_heap_neutral eff_summary2.
Proof.
  intros gamma omega ef1 ea1 ef2 ea2 HBack.
  inversion HBack; subst; try discriminate.
  exists ty1, ty2, eff1, eff2, eff_summary1, eff_summary2.
  split; [exact H3 |].
  split; [exact H4 |].
  split; [exact H5 |].
  split; [exact H6 |].
  split; assumption.
Qed.

Corollary NCBT_PairPar_summary_static_noalloc :
  forall gamma omega ef1 ea1 ef2 ea2,
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    exists eff_summary1 eff_summary2,
      NCheckedTcExp gamma omega (EEffApp ef1 ea1) TyEffect
        eff_summary1 /\
      NCheckedTcExp gamma omega (EEffApp ef2 ea2) TyEffect
        eff_summary2 /\
      static_noalloc eff_summary1 /\
      static_noalloc eff_summary2.
Proof.
  intros gamma omega ef1 ea1 ef2 ea2 HBack.
  destruct
    (NCBT_PairPar_summary_static_heap_neutral
      gamma omega ef1 ea1 ef2 ea2 HBack)
    as (_ & _ & _ & _ & eff_summary1 & eff_summary2 &
      _ & _ & HCheckedSummary1 & HCheckedSummary2 &
      HNeutral1 & HNeutral2).
  exists eff_summary1, eff_summary2.
  split; [exact HCheckedSummary1 |].
  split; [exact HCheckedSummary2 |].
  split.
  - destruct HNeutral1 as (HNoAlloc1 & _).
    exact HNoAlloc1.
  - destruct HNeutral2 as (HNoAlloc2 & _).
    exact HNoAlloc2.
Qed.

Corollary NCBT_PairPar_summary_static_readonly :
  forall gamma omega ef1 ea1 ef2 ea2,
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    exists eff_summary1 eff_summary2,
      NCheckedTcExp gamma omega (EEffApp ef1 ea1) TyEffect
        eff_summary1 /\
      NCheckedTcExp gamma omega (EEffApp ef2 ea2) TyEffect
        eff_summary2 /\
      static_readonly eff_summary1 /\
      static_readonly eff_summary2.
Proof.
  intros gamma omega ef1 ea1 ef2 ea2 HBack.
  destruct
    (NCBT_PairPar_summary_static_heap_neutral
      gamma omega ef1 ea1 ef2 ea2 HBack)
    as (_ & _ & _ & _ & eff_summary1 & eff_summary2 &
      _ & _ & HCheckedSummary1 & HCheckedSummary2 &
      HNeutral1 & HNeutral2).
  exists eff_summary1, eff_summary2.
  split; [exact HCheckedSummary1 |].
  split; [exact HCheckedSummary2 |].
  split.
  - destruct HNeutral1 as (_ & HReadOnly1).
    exact HReadOnly1.
  - destruct HNeutral2 as (_ & HReadOnly2).
    exact HReadOnly2.
Qed.

Lemma NCBT_PairPar_components :
  forall gamma omega ef1 ea1 ef2 ea2,
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    exists ty1 ty2 eff1 eff2 eff_summary1 eff_summary2,
      NCheckedTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 /\
      NCheckedTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 /\
      NCheckedTcExp gamma omega (EEffApp ef1 ea1) TyEffect
        eff_summary1 /\
      NCheckedTcExp gamma omega (EEffApp ef2 ea2) TyEffect
        eff_summary2 /\
      static_heap_neutral eff_summary1 /\
      static_heap_neutral eff_summary2 /\
      NCheckedBackTriangle gamma omega
        (EMuApp ef1 ea1) (EEffApp ef1 ea1) /\
      NCheckedBackTriangle gamma omega
        (EMuApp ef2 ea2) (EEffApp ef2 ea2).
Proof.
  intros gamma omega ef1 ea1 ef2 ea2 HBack.
  inversion HBack; subst; try discriminate.
  exists ty1, ty2, eff1, eff2, eff_summary1, eff_summary2.
  split; [exact H3 |].
  split; [exact H4 |].
  split; [exact H5 |].
  split; [exact H6 |].
  split; [assumption |].
  split; [assumption |].
  split.
  - match goal with
    | H : NCheckedBackTriangle _ _
        (EMuApp ef1 ea1) (EEffApp ef1 ea1) |- _ =>
        exact H
    end.
  - match goal with
    | H : NCheckedBackTriangle _ _
        (EMuApp ef2 ea2) (EEffApp ef2 ea2) |- _ =>
        exact H
    end.
Qed.

Lemma EPairPar_terminal_first_step :
  forall heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final,
    NSteps
      (NInitialState heap env rho
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho (EEffApp ef1 ea1)
          (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps.
  remember
    (NInitialState heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StEval heap env rho
          (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)) KDone)
        LSilent
        (StEval heap env rho (EEffApp ef1 ea1)
          (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))
        label state'
        (StepPairPar heap env rho ef1 ea1 ef2 ea2 KDone)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma EPairPar_terminal_first_step_N :
  forall n heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final,
    NStepsN n
      (NInitialState heap env rho
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho (EEffApp ef1 ea1)
          (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (NInitialState heap env rho
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)))
      LSilent
      (StEval heap env rho (EEffApp ef1 ea1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))
      phi heap_final v_final
      (StepPairPar heap env rho ef1 ea1 ef2 ea2 KDone)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
Qed.

Lemma KPairParEff1_terminal_value_is_summary :
  forall heap v ef1 ea1 ef2 ea2 env rho k phi heap_final v_final,
    NSteps
      (StReturn heap v (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists theta,
      v = VSummary theta.
Proof.
  intros heap v ef1 ea1 ef2 ea2 env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap v (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    eexists. reflexivity.
Qed.

Lemma KPairParEff1_summary_terminal_first_step_N :
  forall n heap theta1 ef1 ea1 ef2 ea2 env rho k phi heap_final
    v_final,
    NStepsN n
      (StReturn heap (VSummary theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho (EEffApp ef2 ea2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap theta1 ef1 ea1 ef2 ea2 env rho k phi heap_final
    v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (StReturn heap (VSummary theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      LSilent
      (StEval heap env rho (EEffApp ef2 ea2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      phi heap_final v_final
      (StepPairParEff1 heap theta1 ef1 ea1 ef2 ea2 env rho k)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
Qed.

Lemma KPairParEff1_summary_terminal_first_step :
  forall heap theta1 ef1 ea1 ef2 ea2 env rho k phi heap_final v_final,
    NSteps
      (StReturn heap (VSummary theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho (EEffApp ef2 ea2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap theta1 ef1 ea1 ef2 ea2 env rho k phi heap_final v_final
    HSteps.
  remember
    (StReturn heap (VSummary theta1)
      (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StReturn heap (VSummary theta1)
          (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
        LSilent
        (StEval heap env rho (EEffApp ef2 ea2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
        label state'
        (StepPairParEff1 heap theta1 ef1 ea1 ef2 ea2 env rho k)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KPairParEff2_terminal_value_is_summary :
  forall heap v ef1 ea1 ef2 ea2 env rho theta1 k
    phi heap_final v_final,
    NSteps
      (StReturn heap v
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      phi
      (StDone heap_final v_final) ->
    exists theta2,
      v = VSummary theta2.
Proof.
  intros heap v ef1 ea1 ef2 ea2 env rho theta1 k
    phi heap_final v_final HSteps.
  remember
    (StReturn heap v
      (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst; eexists; reflexivity.
Qed.

Lemma KPairParEff2_summary_terminal_check_pass :
  forall heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k
    phi heap_final v_final,
    NSteps
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      phi
      (StDone heap_final v_final) ->
    summary_disjointb theta1 theta2 = true /\
    exists phi_tail,
      NSteps
        (StPairParRun
          (StEval heap env rho (EMuApp ef1 ea1) KDone)
          (StEval heap env rho (EMuApp ef2 ea2) KDone)
          [] [] k)
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k
    phi heap_final v_final HSteps.
  destruct (summary_disjointb theta1 theta2) eqn:HCheck.
  - remember
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      as start eqn:HStart.
    remember (StDone heap_final v_final) as final eqn:HFinal.
    destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
    + rewrite HStart in HFinal. inversion HFinal.
    + subst state state''.
      destruct
        (NStep_deterministic
          (StReturn heap (VSummary theta2)
            (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
          LSilent
          (StPairParRun
            (StEval heap env rho (EMuApp ef1 ea1) KDone)
            (StEval heap env rho (EMuApp ef2 ea2) KDone)
            [] [] k)
          label state'
          (StepPairParCheckPass
            heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k HCheck)
          HStep)
        as [HLabel HState].
      subst label state'.
      split; [reflexivity |].
      exists phi0.
      split; [assumption | reflexivity].
  - remember
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      as start eqn:HStart.
    remember (StDone heap_final v_final) as final eqn:HFinal.
    destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
    + rewrite HStart in HFinal. inversion HFinal.
    + subst state state''.
      destruct
        (NStep_deterministic
          (StReturn heap (VSummary theta2)
            (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
          LSilent
          (StError heap)
          label state'
          (StepPairParCheckFail
            heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k HCheck)
          HStep)
        as [HLabel HState].
      subst label state'.
      exfalso.
      eapply StError_no_done; eauto.
Qed.

Lemma KPairParEff2_summary_terminal_check_pass_N :
  forall n heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k
    phi heap_final v_final,
    NStepsN n
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      phi
      (StDone heap_final v_final) ->
    summary_disjointb theta1 theta2 = true /\
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StPairParRun
          (StEval heap env rho (EMuApp ef1 ea1) KDone)
          (StEval heap env rho (EMuApp ef2 ea2) KDone)
          [] [] k)
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k
    phi heap_final v_final HSteps.
  destruct (summary_disjointb theta1 theta2) eqn:HCheck.
  - destruct
      (NStepsN_known_first_step_terminal_inv
        n
        (StReturn heap (VSummary theta2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
        LSilent
        (StPairParRun
          (StEval heap env rho (EMuApp ef1 ea1) KDone)
          (StEval heap env rho (EMuApp ef2 ea2) KDone)
          [] [] k)
        phi heap_final v_final
        (StepPairParCheckPass
          heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k HCheck)
        HSteps)
      as (n_tail & phi_tail & Hn & HTail & HTrace).
    simpl in HTrace.
    split; [reflexivity |].
    exists n_tail, phi_tail.
    repeat split; assumption.
  - destruct
      (NStepsN_known_first_step_terminal_inv
        n
        (StReturn heap (VSummary theta2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
        LSilent
        (StError heap)
        phi heap_final v_final
        (StepPairParCheckFail
          heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k HCheck)
        HSteps)
      as (n_tail & phi_tail & _ & HTail & _).
    exfalso.
    eapply StError_no_done_N; exact HTail.
Qed.

Lemma StPairParRun_right_phase_decomposition_N :
  forall n heap_left v_left right_state phi_left_acc phi_right_acc
    phi heap_final v_final,
    NStepsN n
      (StPairParRun
        (StDone heap_left v_left)
        right_state
        phi_left_acc
        phi_right_acc
        KDone)
      phi
      (StDone heap_final v_final) ->
    exists phi_right heap_right v_right,
      NSteps right_state phi_right (StDone heap_right v_right) /\
      trace_disjointb phi_left_acc (phi_right_acc ++ phi_right) = true /\
      heap_final = heap_right /\
      v_final = VPair v_left v_right /\
      phi = phi_right.
Proof.
  induction n as [| n IH];
    intros heap_left v_left right_state phi_left_acc phi_right_acc
      phi heap_final v_final HRun.
  - inversion HRun.
  - inversion HRun as
      [| n0 state0 label state1 phi0 state2 HStep0 HTail0];
      subst; clear HRun.
    inversion HStep0; subst.
    all: try match goal with
    | H : NStep (StDone _ _) _ _ |- _ => inversion H
    end.
    all: try match goal with
    | H : NStepsN _ (StError _) _ (StDone _ _) |- _ =>
        exfalso; eapply StError_no_done_N; exact H
    end.
    all: try match goal with
    | HRightStep : NStep ?right_state0 ?label ?right_state' |- _ =>
        destruct
          (IH (state_heap right_state') v_left right_state'
            phi_left_acc (phi_right_acc ++ label_trace label)
            phi0 heap_final v_final HTail0)
          as (phi_right_tail & heap_right & v_right &
            HRightTail & HCheck & HHeap & HVal & HTraceTail);
        exists (label_trace label ++ phi_right_tail), heap_right, v_right;
        split;
        [ eapply StepsStep; eauto
        | split;
          [ rewrite <- app_assoc in HCheck; exact HCheck
          | repeat split; try assumption;
            subst phi0; reflexivity ] ]
    end.
    all: try match goal with
    | HTail : NStepsN _ (StReturn ?heap (VPair ?v_left0 ?v2) KDone)
        ?phi_tail (StDone ?heap_final0 ?v_final0) |- _ =>
        destruct
          (NSteps_return_done_inv
            heap
            (VPair v_left0 v2)
            phi_tail
            heap_final0
            v_final0
            (NStepsN_to_NSteps _ _ _ _ HTail))
          as (HHeap & HVal & HTrace);
        subst heap_final0 v_final0 phi_tail;
        exists [], heap, v2;
        split;
        [ constructor
        | split;
          [ rewrite app_nil_r; assumption
          | repeat split; try assumption; reflexivity ] ]
    end.
Qed.

Lemma StPairParRun_right_phase_counted_decomposition_N :
  forall n heap_left v_left right_state phi_left_acc phi_right_acc
    phi heap_final v_final,
    NStepsN n
      (StPairParRun
        (StDone heap_left v_left)
        right_state
        phi_left_acc
        phi_right_acc
        KDone)
      phi
      (StDone heap_final v_final) ->
    exists n_right phi_right heap_right v_right,
      NStepsN n_right right_state phi_right (StDone heap_right v_right) /\
      n_right < n /\
      trace_disjointb phi_left_acc (phi_right_acc ++ phi_right) = true /\
      heap_final = heap_right /\
      v_final = VPair v_left v_right /\
      phi = phi_right.
Proof.
  induction n as [| n IH];
    intros heap_left v_left right_state phi_left_acc phi_right_acc
      phi heap_final v_final HRun.
  - inversion HRun.
  - inversion HRun as
      [| n0 state0 label state1 phi0 state2 HStep0 HTail0];
      subst; clear HRun.
    inversion HStep0; subst.
    all: try match goal with
    | H : NStep (StDone _ _) _ _ |- _ => inversion H
    end.
    all: try match goal with
    | H : NStepsN _ (StError _) _ (StDone _ _) |- _ =>
        exfalso; eapply StError_no_done_N; exact H
    end.
    all: try match goal with
    | HRightStep : NStep ?right_state0 ?label ?right_state' |- _ =>
        destruct
          (IH (state_heap right_state') v_left right_state'
            phi_left_acc (phi_right_acc ++ label_trace label)
            phi0 heap_final v_final HTail0)
          as (n_right_tail & phi_right_tail & heap_right & v_right &
            HRightTail & HRightCount & HCheck & HHeap & HVal &
            HTraceTail);
        exists (S n_right_tail), (label_trace label ++ phi_right_tail),
          heap_right, v_right;
        split;
        [ eapply StepsNStep; eauto
        | split;
          [ lia
          | split;
            [ rewrite <- app_assoc in HCheck; exact HCheck
            | repeat split; try assumption;
              subst phi0; reflexivity ] ] ]
    end.
    all: try match goal with
    | HTail : NStepsN _ (StReturn ?heap (VPair ?v_left0 ?v2) KDone)
        ?phi_tail (StDone ?heap_final0 ?v_final0) |- _ =>
        destruct
          (NSteps_return_done_inv
            heap
            (VPair v_left0 v2)
            phi_tail
            heap_final0
            v_final0
            (NStepsN_to_NSteps _ _ _ _ HTail))
          as (HHeap & HVal & HTrace);
        subst heap_final0 v_final0 phi_tail;
        exists 0, [], heap, v2;
        split;
        [ constructor
        | split;
          [ lia
          | split;
            [ rewrite app_nil_r; assumption
            | repeat split; try assumption; reflexivity ] ] ]
    end.
Qed.

Lemma StPairParRun_left_phase_decomposition_N :
  forall n left_state env rho e_right phi_left_acc phi_right_acc
    phi heap_final v_final,
    NStepsN n
      (StPairParRun
        left_state
        (NInitialState (state_heap left_state) env rho e_right)
        phi_left_acc
        phi_right_acc
        KDone)
      phi
      (StDone heap_final v_final) ->
    exists phi_left heap_left v_left phi_after_left,
      NSteps left_state phi_left (StDone heap_left v_left) /\
      NSteps
        (StPairParRun
          (StDone heap_left v_left)
          (NInitialState heap_left env rho e_right)
          (phi_left_acc ++ phi_left)
          phi_right_acc
          KDone)
        phi_after_left
        (StDone heap_final v_final) /\
      phi = phi_left ++ phi_after_left.
Proof.
  induction n as [| n IH];
    intros left_state env rho e_right phi_left_acc phi_right_acc
      phi heap_final v_final HRun.
  - inversion HRun.
  - inversion HRun as
      [| n0 state0 label state1 phi0 state2 HStep0 HTail0];
      subst; clear HRun.
    inversion HStep0; subst.
    + simpl in *.
      destruct
        (IH left_state' env rho e_right
          (phi_left_acc ++ label_trace label)
          phi_right_acc
          phi0 heap_final v_final HTail0)
        as (phi_left_tail & heap_left & v_left & phi_after_left &
          HLeftTail & HAfterLeft & HTraceTail).
      exists (label_trace label ++ phi_left_tail), heap_left, v_left,
        phi_after_left.
      split.
      * eapply StepsStep.
        -- eassumption.
        -- exact HLeftTail.
      * split.
        -- rewrite app_assoc.
           exact HAfterLeft.
        -- subst phi0.
           rewrite app_assoc.
           reflexivity.
    + exists [], heap, v1, (label_trace label ++ phi0).
      split.
      * constructor.
      * split.
        -- rewrite app_nil_r.
           eapply StepsStep.
           ++ exact HStep0.
           ++ eapply NStepsN_to_NSteps. exact HTail0.
        -- reflexivity.
    + exfalso.
      eapply StError_no_done_N. exact HTail0.
    all: try solve
      [ match goal with
        | H : NStep (StDone _ _) _ _ |- _ => inversion H
        end
      | match goal with
        | H : NStep (StError _) _ _ |- _ => inversion H
        end
      | match goal with
        | H : NStepsN _ (StError _) _ (StDone _ _) |- _ =>
            exfalso; eapply StError_no_done_N; exact H
        end
      | congruence ].
    Unshelve.
    all: try solve
      [ eassumption
      | constructor
      | reflexivity
      | match goal with
        | H : NStep (StDone _ _) _ _ |- _ => inversion H
        end
      | match goal with
        | H : NStepsN _ (StError _) _ (StDone _ _) |- _ =>
            exfalso; eapply StError_no_done_N; exact H
        end ].
Qed.

Lemma StPairParRun_left_phase_counted_decomposition_N :
  forall n left_state env rho e_right phi_left_acc phi_right_acc
    phi heap_final v_final,
    NStepsN n
      (StPairParRun
        left_state
        (NInitialState (state_heap left_state) env rho e_right)
        phi_left_acc
        phi_right_acc
        KDone)
      phi
      (StDone heap_final v_final) ->
    exists n_left n_after_left phi_left heap_left v_left phi_after_left,
      NStepsN n_left left_state phi_left (StDone heap_left v_left) /\
      NStepsN n_after_left
        (StPairParRun
          (StDone heap_left v_left)
          (NInitialState heap_left env rho e_right)
          (phi_left_acc ++ phi_left)
          phi_right_acc
          KDone)
        phi_after_left
        (StDone heap_final v_final) /\
      n_left < n /\
      n = n_left + n_after_left /\
      phi = phi_left ++ phi_after_left.
Proof.
  induction n as [| n IH];
    intros left_state env rho e_right phi_left_acc phi_right_acc
      phi heap_final v_final HRun.
  - inversion HRun.
  - inversion HRun as
      [| n0 state0 label state1 phi0 state2 HStep0 HTail0];
      subst; clear HRun.
    inversion HStep0; subst.
    + simpl in *.
      destruct
        (IH left_state' env rho e_right
          (phi_left_acc ++ label_trace label)
          phi_right_acc
          phi0 heap_final v_final HTail0)
        as (n_left_tail & n_after_left & phi_left_tail & heap_left &
          v_left & phi_after_left &
          HLeftTail & HAfterLeft & HCountLeft & HCountTotal &
          HTraceTail).
      exists (S n_left_tail), n_after_left,
        (label_trace label ++ phi_left_tail), heap_left, v_left,
        phi_after_left.
      split.
      * eapply StepsNStep; eauto.
      * split.
        -- rewrite app_assoc.
           exact HAfterLeft.
        -- split; [lia |].
           split; [lia |].
           subst phi0.
           rewrite app_assoc.
           reflexivity.
    + exists 0, (S n), [], heap, v1, (label_trace label ++ phi0).
      split.
      * constructor.
      * split.
        -- rewrite app_nil_r.
           eapply StepsNStep.
           ++ exact HStep0.
           ++ exact HTail0.
        -- repeat split; try lia.
    + exfalso.
      eapply StError_no_done_N. exact HTail0.
    all: try solve
      [ match goal with
        | H : NStep (StDone _ _) _ _ |- _ => inversion H
        end
      | match goal with
        | H : NStep (StError _) _ _ |- _ => inversion H
        end
      | match goal with
        | H : NStepsN _ (StError _) _ (StDone _ _) |- _ =>
            exfalso; eapply StError_no_done_N; exact H
        end
      | congruence ].
    Unshelve.
    all: try solve
      [ eassumption
      | constructor
      | reflexivity
      | match goal with
        | H : NStep (StDone _ _) _ _ |- _ => inversion H
        end
      | match goal with
        | H : NStepsN _ (StError _) _ (StDone _ _) |- _ =>
            exfalso; eapply StError_no_done_N; exact H
        end ].
Qed.

Lemma StPairParRun_initial_decomposition_N :
  forall n heap env rho e_left e_right phi heap_final v_final,
    NStepsN n
      (StPairParRun
        (NInitialState heap env rho e_left)
        (NInitialState heap env rho e_right)
        [] [] KDone)
      phi
      (StDone heap_final v_final) ->
    exists phi_left phi_right heap_left v_left heap_right v_right,
      NSteps
        (NInitialState heap env rho e_left)
        phi_left
        (StDone heap_left v_left) /\
      NSteps
        (NInitialState heap_left env rho e_right)
        phi_right
        (StDone heap_right v_right) /\
      trace_disjointb phi_left phi_right = true /\
      heap_final = heap_right /\
      v_final = VPair v_left v_right /\
      phi = phi_left ++ phi_right.
Proof.
  intros n heap env rho e_left e_right phi heap_final v_final HRun.
  destruct
    (StPairParRun_left_phase_decomposition_N
      n
      (NInitialState heap env rho e_left)
      env rho e_right [] [] phi heap_final v_final HRun)
    as (phi_left & heap_left & v_left & phi_after_left &
      HLeft & HAfterLeft & HTraceLeft).
  destruct
    (NSteps_to_NStepsN
      (StPairParRun
        (StDone heap_left v_left)
        (NInitialState heap_left env rho e_right)
        ([] ++ phi_left)
        []
        KDone)
      phi_after_left
      (StDone heap_final v_final)
      HAfterLeft)
    as (n_right & HAfterLeftN).
  simpl in HAfterLeftN.
  destruct
    (StPairParRun_right_phase_decomposition_N
      n_right heap_left v_left
      (NInitialState heap_left env rho e_right)
      phi_left [] phi_after_left heap_final v_final HAfterLeftN)
    as (phi_right & heap_right & v_right &
      HRight & HCheck & HHeap & HVal & HTraceRight).
  exists phi_left, phi_right, heap_left, v_left, heap_right, v_right.
  split; [exact HLeft |].
  split; [exact HRight |].
  split; [exact HCheck |].
  split; [exact HHeap |].
  split; [exact HVal |].
  rewrite HTraceLeft, HTraceRight.
  reflexivity.
Qed.

Lemma StPairParRun_initial_counted_decomposition_N :
  forall n heap env rho e_left e_right phi heap_final v_final,
    NStepsN n
      (StPairParRun
        (NInitialState heap env rho e_left)
        (NInitialState heap env rho e_right)
        [] [] KDone)
      phi
      (StDone heap_final v_final) ->
    exists n_left n_right
      phi_left phi_right heap_left v_left heap_right v_right,
      NStepsN n_left
        (NInitialState heap env rho e_left)
        phi_left
        (StDone heap_left v_left) /\
      NStepsN n_right
        (NInitialState heap_left env rho e_right)
        phi_right
        (StDone heap_right v_right) /\
      n_left < n /\
      n_right < n /\
      trace_disjointb phi_left phi_right = true /\
      heap_final = heap_right /\
      v_final = VPair v_left v_right /\
      phi = phi_left ++ phi_right.
Proof.
  intros n heap env rho e_left e_right phi heap_final v_final HRun.
  destruct
    (StPairParRun_left_phase_counted_decomposition_N
      n
      (NInitialState heap env rho e_left)
      env rho e_right [] [] phi heap_final v_final HRun)
    as (n_left & n_after_left & phi_left & heap_left & v_left &
      phi_after_left &
      HLeft & HAfterLeft & HLeftCount & HCountTotal & HTraceLeft).
  simpl in HAfterLeft.
  destruct
    (StPairParRun_right_phase_counted_decomposition_N
      n_after_left heap_left v_left
      (NInitialState heap_left env rho e_right)
      phi_left [] phi_after_left heap_final v_final HAfterLeft)
    as (n_right & phi_right & heap_right & v_right &
      HRight & HRightCount & HCheck & HHeap & HVal & HTraceRight).
  exists n_left, n_right, phi_left, phi_right,
    heap_left, v_left, heap_right, v_right.
  split; [exact HLeft |].
  split; [exact HRight |].
  split; [exact HLeftCount |].
  split; [lia |].
  split; [exact HCheck |].
  split; [exact HHeap |].
  split; [exact HVal |].
  rewrite HTraceLeft, HTraceRight.
  reflexivity.
Qed.

Definition EPairParCountedDecompositionGoal : Prop :=
  forall n heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final,
    NStepsN n
      (NInitialState heap env rho
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)))
      phi
      (StDone heap_final v_final) ->
    exists n_eff1 n_eff2 n_left n_right
      phi_eff1 phi_eff2 phi_left phi_right
      theta1 theta2 heap_eff1 heap_eff2 heap_left heap_right
      v_left v_right,
      NStepsN n_eff1
        (NInitialState heap env rho (EEffApp ef1 ea1))
        phi_eff1
        (StDone heap_eff1 (VSummary theta1)) /\
      NStepsN n_eff2
        (NInitialState heap_eff1 env rho (EEffApp ef2 ea2))
        phi_eff2
        (StDone heap_eff2 (VSummary theta2)) /\
      NStepsN n_left
        (NInitialState heap_eff2 env rho (EMuApp ef1 ea1))
        phi_left
        (StDone heap_left v_left) /\
      NStepsN n_right
        (NInitialState heap_left env rho (EMuApp ef2 ea2))
        phi_right
        (StDone heap_right v_right) /\
      n_eff1 < n /\
      n_eff2 < n /\
      n_left < n /\
      n_right < n /\
      summary_disjointb theta1 theta2 = true /\
      trace_disjointb phi_left phi_right = true /\
      heap_final = heap_right /\
      v_final = VPair v_left v_right /\
      phi = phi_eff1 ++ phi_eff2 ++ phi_left ++ phi_right.

Theorem EPairPar_counted_decomposition :
  EPairParCountedDecompositionGoal.
Proof.
  unfold EPairParCountedDecompositionGoal.
  intros n heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps.
  destruct
    (EPairPar_terminal_first_step_N
      n heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps)
    as (n_eff1_tail & phi_tail & HnStart &
      HSummary1WithKont & HTraceStart).
  destruct
    (NStepsN_append_kont_terminal_split_counted
      n_eff1_tail
      (StEval heap env rho (EEffApp ef1 ea1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))
      phi_tail
      heap_final v_final
      HSummary1WithKont
      (NInitialState heap env rho (EEffApp ef1 ea1))
      (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone)
      eq_refl)
    as (n_eff1 & n_after_eff1 & phi_eff1 & heap_eff1 & v_eff1 &
      phi_after_eff1 & HSummary1 & HAfterEff1 & HCountEff1 &
      HTraceEff1).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KPairParEff1_terminal_value_is_summary
        heap_eff1 v_eff1 ef1 ea1 ef2 ea2 env rho KDone
        phi_after_eff1 heap_final v_final
        (NStepsN_to_NSteps
          n_after_eff1
          (StReturn heap_eff1 v_eff1
            (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))
          phi_after_eff1
          (StDone heap_final v_final)
          HAfterEff1))
      as (theta1 & HTheta1).
    subst v_eff1.
    destruct
      (KPairParEff1_summary_terminal_first_step_N
        n_after_eff1 heap_eff1 theta1 ef1 ea1 ef2 ea2 env rho KDone
        phi_after_eff1 heap_final v_final HAfterEff1)
      as (n_eff2_tail & phi_eff2_tail & HCountAfterEff1 &
        HSummary2WithKont & HTraceAfterEff1).
    destruct
      (NStepsN_append_kont_terminal_split_counted
        n_eff2_tail
        (StEval heap_eff1 env rho (EEffApp ef2 ea2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone))
        phi_eff2_tail
        heap_final v_final
        HSummary2WithKont
        (NInitialState heap_eff1 env rho (EEffApp ef2 ea2))
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone)
        eq_refl)
      as (n_eff2 & n_after_eff2 & phi_eff2 & heap_eff2 & v_eff2 &
        phi_after_eff2 & HSummary2 & HAfterEff2 & HCountEff2 &
        HTraceEff2).
    + intros heap_done v_done HDone. inversion HDone.
    + destruct
        (KPairParEff2_terminal_value_is_summary
          heap_eff2 v_eff2 ef1 ea1 ef2 ea2 env rho theta1 KDone
          phi_after_eff2 heap_final v_final
          (NStepsN_to_NSteps
            n_after_eff2
            (StReturn heap_eff2 v_eff2
              (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone))
            phi_after_eff2
            (StDone heap_final v_final)
            HAfterEff2))
        as (theta2 & HTheta2).
      subst v_eff2.
      destruct
        (KPairParEff2_summary_terminal_check_pass_N
          n_after_eff2 heap_eff2 theta1 theta2 ef1 ea1 ef2 ea2 env rho
          KDone phi_after_eff2 heap_final v_final HAfterEff2)
        as (HCheckSummary & n_pair & phi_pair & HCountAfterEff2 &
          HPairRun & HTraceAfterEff2).
      destruct
        (StPairParRun_initial_counted_decomposition_N
          n_pair heap_eff2 env rho
          (EMuApp ef1 ea1)
          (EMuApp ef2 ea2)
          phi_pair heap_final v_final HPairRun)
        as (n_left & n_right & phi_left & phi_right &
          heap_left & v_left & heap_right & v_right &
          HLeft & HRight & HLeftCount & HRightCount &
          HCheckTrace & HHeap & HVal & HTracePair).
      exists n_eff1, n_eff2, n_left, n_right,
        phi_eff1, phi_eff2, phi_left, phi_right,
        theta1, theta2, heap_eff1, heap_eff2,
        heap_left, heap_right, v_left, v_right.
      repeat split; try assumption; try lia.
      rewrite HTraceStart, HTraceEff1, HTraceAfterEff1, HTraceEff2,
        HTraceAfterEff2, HTracePair.
      repeat rewrite app_assoc.
      reflexivity.
Qed.

Definition EPairParDecompositionGoal : Prop :=
  forall heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final,
    NSteps
      (NInitialState heap env rho
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)))
      phi
      (StDone heap_final v_final) ->
    exists phi_eff1 phi_eff2 phi_left phi_right
      theta1 theta2 heap_eff1 heap_eff2 heap_left heap_right
      v_left v_right,
      SummaryEvaluation
        heap env rho (EEffApp ef1 ea1)
        phi_eff1 heap_eff1 theta1 /\
      SummaryEvaluation
        heap_eff1 env rho (EEffApp ef2 ea2)
        phi_eff2 heap_eff2 theta2 /\
      ComputationEvaluation
        heap_eff2 env rho (EMuApp ef1 ea1)
        phi_left heap_left v_left /\
      ComputationEvaluation
        heap_left env rho (EMuApp ef2 ea2)
        phi_right heap_right v_right /\
      summary_disjointb theta1 theta2 = true /\
      trace_disjointb phi_left phi_right = true /\
      heap_final = heap_right /\
      v_final = VPair v_left v_right /\
      phi = phi_eff1 ++ phi_eff2 ++ phi_left ++ phi_right.

Theorem EPairPar_decomposition :
  EPairParDecompositionGoal.
Proof.
  unfold EPairParDecompositionGoal.
  intros heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps.
  destruct
    (EPairPar_terminal_first_step
      heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps)
    as (phi_tail & HSummary1WithKont & HTraceStart).
  destruct
    (NSteps_to_NStepsN
      (StEval heap env rho (EEffApp ef1 ea1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))
      phi_tail
      (StDone heap_final v_final)
      HSummary1WithKont)
    as (n_eff1 & HSummary1WithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_eff1
      (StEval heap env rho (EEffApp ef1 ea1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))
      phi_tail
      heap_final
      v_final
      HSummary1WithKontN
      (NInitialState heap env rho (EEffApp ef1 ea1))
      (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone)
      eq_refl)
    as (phi_eff1 & heap_eff1 & v_eff1 & phi_after_eff1 &
      HSummary1 & HAfterEff1 & HTraceEff1).
  destruct
    (KPairParEff1_terminal_value_is_summary
      heap_eff1 v_eff1 ef1 ea1 ef2 ea2 env rho KDone
      phi_after_eff1 heap_final v_final HAfterEff1)
    as (theta1 & HTheta1).
  subst v_eff1.
  destruct
    (KPairParEff1_summary_terminal_first_step
      heap_eff1 theta1 ef1 ea1 ef2 ea2 env rho KDone
      phi_after_eff1 heap_final v_final HAfterEff1)
    as (phi_eff2_tail & HSummary2WithKont & HTraceAfterEff1).
  destruct
    (NSteps_to_NStepsN
      (StEval heap_eff1 env rho (EEffApp ef2 ea2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone))
      phi_eff2_tail
      (StDone heap_final v_final)
      HSummary2WithKont)
    as (n_eff2 & HSummary2WithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_eff2
      (StEval heap_eff1 env rho (EEffApp ef2 ea2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone))
      phi_eff2_tail
      heap_final
      v_final
      HSummary2WithKontN
      (NInitialState heap_eff1 env rho (EEffApp ef2 ea2))
      (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone)
      eq_refl)
    as (phi_eff2 & heap_eff2 & v_eff2 & phi_after_eff2 &
      HSummary2 & HAfterEff2 & HTraceEff2).
  destruct
    (KPairParEff2_terminal_value_is_summary
      heap_eff2 v_eff2 ef1 ea1 ef2 ea2 env rho theta1 KDone
      phi_after_eff2 heap_final v_final HAfterEff2)
    as (theta2 & HTheta2).
  subst v_eff2.
  destruct
    (KPairParEff2_summary_terminal_check_pass
      heap_eff2 theta1 theta2 ef1 ea1 ef2 ea2 env rho KDone
      phi_after_eff2 heap_final v_final HAfterEff2)
    as (HCheckSummary & phi_pair & HPairRun & HTraceAfterEff2).
  destruct
    (NSteps_to_NStepsN
      (StPairParRun
        (StEval heap_eff2 env rho (EMuApp ef1 ea1) KDone)
        (StEval heap_eff2 env rho (EMuApp ef2 ea2) KDone)
        [] [] KDone)
      phi_pair
      (StDone heap_final v_final)
      HPairRun)
    as (n_pair & HPairRunN).
  destruct
    (StPairParRun_initial_decomposition_N
      n_pair heap_eff2 env rho
      (EMuApp ef1 ea1)
      (EMuApp ef2 ea2)
      phi_pair heap_final v_final HPairRunN)
    as (phi_left & phi_right & heap_left & v_left &
      heap_right & v_right &
      HLeft & HRight & HCheckTrace & HHeap & HVal & HTracePair).
  exists phi_eff1, phi_eff2, phi_left, phi_right,
    theta1, theta2, heap_eff1, heap_eff2, heap_left, heap_right,
    v_left, v_right.
  unfold SummaryEvaluation, ComputationEvaluation in *.
  split; [exact HSummary1 |].
  split; [exact HSummary2 |].
  split; [exact HLeft |].
  split; [exact HRight |].
  split; [exact HCheckSummary |].
  split; [exact HCheckTrace |].
  split; [exact HHeap |].
  split; [exact HVal |].
  rewrite HTraceStart, HTraceEff1, HTraceAfterEff1, HTraceEff2,
    HTraceAfterEff2, HTracePair.
  repeat rewrite app_assoc.
  reflexivity.
Qed.

Definition EPairParHeapNeutralSummaryDecompositionGoal : Prop :=
  forall heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final,
    SummaryHeapNeutral (EEffApp ef1 ea1) ->
    SummaryHeapNeutral (EEffApp ef2 ea2) ->
    NSteps
      (NInitialState heap env rho
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)))
      phi
      (StDone heap_final v_final) ->
    exists phi_eff1 phi_eff2 phi_left phi_right
      theta1 theta2 heap_left heap_right v_left v_right,
      SummaryEvaluation
        heap env rho (EEffApp ef1 ea1)
        phi_eff1 heap theta1 /\
      SummaryEvaluation
        heap env rho (EEffApp ef2 ea2)
        phi_eff2 heap theta2 /\
      ComputationEvaluation
        heap env rho (EMuApp ef1 ea1)
        phi_left heap_left v_left /\
      ComputationEvaluation
        heap_left env rho (EMuApp ef2 ea2)
        phi_right heap_right v_right /\
      HeapNeutralTrace (phi_eff1 ++ phi_eff2) /\
      summary_disjointb theta1 theta2 = true /\
      trace_disjointb phi_left phi_right = true /\
      heap_final = heap_right /\
      v_final = VPair v_left v_right /\
      phi = phi_eff1 ++ phi_eff2 ++ phi_left ++ phi_right.

Theorem EPairPar_decomposition_with_heap_neutral_summaries :
  EPairParHeapNeutralSummaryDecompositionGoal.
Proof.
  unfold EPairParHeapNeutralSummaryDecompositionGoal.
  intros heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final
    HNeutralSummary1 HNeutralSummary2 HSteps.
  destruct
    (EPairPar_decomposition
      heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps)
    as (phi_eff1 & phi_eff2 & phi_left & phi_right &
      theta1 & theta2 & heap_eff1 & heap_eff2 & heap_left & heap_right &
      v_left & v_right &
      HSummary1 & HSummary2 & HLeft & HRight &
      HCheckSummary & HCheckTrace & HHeap & HVal & HTrace).
  destruct
    (HNeutralSummary1 heap env rho phi_eff1 heap_eff1 theta1 HSummary1)
    as (HHeapEff1 & HNeutralTrace1).
  subst heap_eff1.
  destruct
    (HNeutralSummary2 heap env rho phi_eff2 heap_eff2 theta2 HSummary2)
    as (HHeapEff2 & HNeutralTrace2).
  subst heap_eff2.
  exists phi_eff1, phi_eff2, phi_left, phi_right,
    theta1, theta2, heap_left, heap_right, v_left, v_right.
  split; [exact HSummary1 |].
  split; [exact HSummary2 |].
  split; [exact HLeft |].
  split; [exact HRight |].
  split.
  - apply heap_neutral_trace_app; assumption.
  - split; [exact HCheckSummary |].
    split; [exact HCheckTrace |].
    split; [exact HHeap |].
    split; [exact HVal |].
	    exact HTrace.
Qed.

Definition CheckedEPairParHeapNeutralStoreDecompositionGoal : Prop :=
  forall gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right,
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    SummaryHeapNeutral (EEffApp ef1 ea1) ->
    SummaryHeapNeutral (EEffApp ef2 ea2) ->
    ComputationEvaluation heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final (VPair v_left v_right) ->
    exists phi_eff1 phi_eff2 phi_left phi_right
      theta1 theta2 heap_left heap_right store ty_left ty_right,
      SummaryEvaluation
        heap env rho (EEffApp ef1 ea1)
        phi_eff1 heap theta1 /\
      SummaryEvaluation
        heap env rho (EEffApp ef2 ea2)
        phi_eff2 heap theta2 /\
      ComputationEvaluation
        heap env rho (EMuApp ef1 ea1)
        phi_left heap_left v_left /\
      ComputationEvaluation
        heap_left env rho (EMuApp ef2 ea2)
        phi_right heap_right v_right /\
      HeapNeutralTrace (phi_eff1 ++ phi_eff2) /\
      summary_disjointb theta1 theta2 = true /\
      trace_disjointb phi_left phi_right = true /\
      heap_final = heap_right /\
      NStoreKeysBoundedByHeap heap_final store /\
      NStoreResolvedHeapShape heap_final store /\
      NStoreResolvedValShape store v_left ty_left /\
      NStoreResolvedValShape store v_right ty_right /\
      phi = phi_eff1 ++ phi_eff2 ++ phi_left ++ phi_right.

Theorem EPairPar_checked_decomposition_with_heap_neutral_store :
  CheckedEPairParHeapNeutralStoreDecompositionGoal.
Proof.
  unfold CheckedEPairParHeapNeutralStoreDecompositionGoal.
  intros gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right HBack HContext
    HNeutralSummary1 HNeutralSummary2 HComp.
  unfold ComputationEvaluation in HComp.
  destruct
    (EPairPar_decomposition_with_heap_neutral_summaries
      heap env rho ef1 ea1 ef2 ea2 phi heap_final
      (VPair v_left v_right)
      HNeutralSummary1 HNeutralSummary2 HComp)
    as (phi_eff1 & phi_eff2 & phi_left & phi_right &
      theta1 & theta2 & heap_left & heap_right & v_left_decomp &
      v_right_decomp &
      HSummary1 & HSummary2 & HLeft & HRight & HNeutralTrace &
      HCheckSummary & HCheckTrace & HHeap & HVal & HTrace).
  inversion HVal; subst v_left_decomp v_right_decomp.
  destruct
    (NCBT_PairPar_summary_static_heap_neutral
      gamma omega ef1 ea1 ef2 ea2 HBack)
    as (ty1 & ty2 & eff1 & eff2 & _ & _ &
      HCheckedLeft & HCheckedRight & _ & _ & _ & _).
  subst heap_final.
  destruct
    (checked_sequential_computations_store_value_shapes
      gamma omega heap env rho
      (EMuApp ef1 ea1) ty1 eff1 phi_left heap_left v_left
      (EMuApp ef2 ea2) ty2 eff2 phi_right heap_right v_right
      HContext HCheckedLeft HCheckedRight HLeft HRight)
    as (store & ty_left & ty_right &
      _HResolveLeft & _HResolveRight &
      HStoreBounded & HStoreHeap & HValLeft & HValRight).
  exists phi_eff1, phi_eff2, phi_left, phi_right,
    theta1, theta2, heap_left, heap_right, store, ty_left, ty_right.
  split; [exact HSummary1 |].
  split; [exact HSummary2 |].
  split; [exact HLeft |].
  split; [exact HRight |].
  split; [exact HNeutralTrace |].
  split; [exact HCheckSummary |].
  split; [exact HCheckTrace |].
  split; [reflexivity |].
  split; [exact HStoreBounded |].
  split; [exact HStoreHeap |].
  split; [exact HValLeft |].
  split; [exact HValRight |].
  exact HTrace.
Qed.

Definition CheckedEPairParStaticTraceStoreDecompositionGoal : Prop :=
  forall gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right,
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    ComputationEvaluation heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final (VPair v_left v_right) ->
    exists phi_eff1 phi_eff2 phi_left phi_right
      theta1 theta2 heap_left heap_right store ty_left ty_right,
      SummaryEvaluation
        heap env rho (EEffApp ef1 ea1)
        phi_eff1 heap theta1 /\
      SummaryEvaluation
        heap env rho (EEffApp ef2 ea2)
        phi_eff2 heap theta2 /\
      ComputationEvaluation
        heap env rho (EMuApp ef1 ea1)
        phi_left heap_left v_left /\
      ComputationEvaluation
        heap_left env rho (EMuApp ef2 ea2)
        phi_right heap_right v_right /\
      HeapNeutralTrace (phi_eff1 ++ phi_eff2) /\
      summary_disjointb theta1 theta2 = true /\
      trace_disjointb phi_left phi_right = true /\
      heap_final = heap_right /\
      NStoreKeysBoundedByHeap heap_final store /\
      NStoreResolvedHeapShape heap_final store /\
      NStoreResolvedValShape store v_left ty_left /\
      NStoreResolvedValShape store v_right ty_right /\
      phi = phi_eff1 ++ phi_eff2 ++ phi_left ++ phi_right.

Theorem EPairPar_checked_decomposition_with_static_trace_store :
  CheckedEPairParStaticTraceStoreDecompositionGoal.
Proof.
  unfold CheckedEPairParStaticTraceStoreDecompositionGoal.
  intros gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right HBack HContext
    HSummaryTraceSound HComp.
  pose proof HContext as HContextOriginal.
  unfold ComputationEvaluation in HComp.
  destruct
    (EPairPar_decomposition
      heap env rho ef1 ea1 ef2 ea2 phi heap_final
      (VPair v_left v_right) HComp)
    as (phi_eff1 & phi_eff2 & phi_left & phi_right &
      theta1 & theta2 & heap_eff1 & heap_eff2 & heap_left & heap_right &
      v_left_decomp & v_right_decomp &
      HSummary1 & HSummary2 & HLeft & HRight &
      HCheckSummary & HCheckTrace & HHeap & HVal & HTrace).
  inversion HVal; subst v_left_decomp v_right_decomp.
  destruct
    (NCBT_PairPar_summary_static_heap_neutral
      gamma omega ef1 ea1 ef2 ea2 HBack)
    as (ty1 & ty2 & eff1 & eff2 & eff_summary1 & eff_summary2 &
      HCheckedLeft & HCheckedRight &
      HCheckedSummary1 & HCheckedSummary2 &
      HStaticNeutral1 & HStaticNeutral2).
  destruct HContext as
    (_ & _ & _ & _ & _ & HRho & _).
  pose proof
    (NCheckedTcExp_eff_wf
      gamma omega (EEffApp ef1 ea1) TyEffect eff_summary1
      HCheckedSummary1)
    as HSummaryWF1.
  destruct
    (NResolveStaticEffect_exists
      0 omega rho eff_summary1 HRho HSummaryWF1)
    as (eff_summary1_res & HResolveSummary1).
  pose proof
    (HSummaryTraceSound
      (EEffApp ef1 ea1) eff_summary1
      phi_eff1 heap_eff1 theta1 eff_summary1_res
      HCheckedSummary1 HSummary1 HResolveSummary1)
    as HCoveredSummary1.
  destruct
    (summary_static_heap_neutral
      heap env rho (EEffApp ef1 ea1)
      phi_eff1 heap_eff1 theta1
      eff_summary1 eff_summary1_res
      HSummary1 HResolveSummary1 HCoveredSummary1 HStaticNeutral1)
    as (HHeapEff1 & HNeutralTrace1).
  subst heap_eff1.
  pose proof
    (NCheckedTcExp_eff_wf
      gamma omega (EEffApp ef2 ea2) TyEffect eff_summary2
      HCheckedSummary2)
    as HSummaryWF2.
  destruct
    (NResolveStaticEffect_exists
      0 omega rho eff_summary2 HRho HSummaryWF2)
    as (eff_summary2_res & HResolveSummary2).
  pose proof
    (HSummaryTraceSound
      (EEffApp ef2 ea2) eff_summary2
      phi_eff2 heap_eff2 theta2 eff_summary2_res
      HCheckedSummary2 HSummary2 HResolveSummary2)
    as HCoveredSummary2.
  destruct
    (summary_static_heap_neutral
      heap env rho (EEffApp ef2 ea2)
      phi_eff2 heap_eff2 theta2
      eff_summary2 eff_summary2_res
      HSummary2 HResolveSummary2 HCoveredSummary2 HStaticNeutral2)
    as (HHeapEff2 & HNeutralTrace2).
  subst heap_eff2.
  subst heap_final.
  destruct
    (checked_sequential_computations_store_value_shapes
      gamma omega heap env rho
      (EMuApp ef1 ea1) ty1 eff1 phi_left heap_left v_left
      (EMuApp ef2 ea2) ty2 eff2 phi_right heap_right v_right
      HContextOriginal HCheckedLeft HCheckedRight HLeft HRight)
    as (store & ty_left & ty_right &
      _HResolveLeft & _HResolveRight &
      HStoreBounded & HStoreHeap & HValLeft & HValRight).
  exists phi_eff1, phi_eff2, phi_left, phi_right,
    theta1, theta2, heap_left, heap_right, store, ty_left, ty_right.
  split; [exact HSummary1 |].
  split; [exact HSummary2 |].
  split; [exact HLeft |].
  split; [exact HRight |].
  split.
  - apply heap_neutral_trace_app; assumption.
  - split; [exact HCheckSummary |].
    split; [exact HCheckTrace |].
    split; [reflexivity |].
    split; [exact HStoreBounded |].
    split; [exact HStoreHeap |].
    split; [exact HValLeft |].
    split; [exact HValRight |].
    exact HTrace.
Qed.

Definition CheckedEPairParCountedStaticTraceStoreDecompositionGoal : Prop :=
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right,
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final (VPair v_left v_right) ->
    exists n_eff1 n_eff2 n_left n_right
      phi_eff1 phi_eff2 phi_left phi_right
      theta1 theta2 heap_left heap_right store ty_left ty_right,
      NStepsN n_eff1
        (NInitialState heap env rho (EEffApp ef1 ea1))
        phi_eff1
        (StDone heap (VSummary theta1)) /\
      NStepsN n_eff2
        (NInitialState heap env rho (EEffApp ef2 ea2))
        phi_eff2
        (StDone heap (VSummary theta2)) /\
      NStepsN n_left
        (NInitialState heap env rho (EMuApp ef1 ea1))
        phi_left
        (StDone heap_left v_left) /\
      NStepsN n_right
        (NInitialState heap_left env rho (EMuApp ef2 ea2))
        phi_right
        (StDone heap_right v_right) /\
      n_eff1 < n /\
      n_eff2 < n /\
      n_left < n /\
      n_right < n /\
      HeapNeutralTrace (phi_eff1 ++ phi_eff2) /\
      summary_disjointb theta1 theta2 = true /\
      trace_disjointb phi_left phi_right = true /\
      heap_final = heap_right /\
      NStoreKeysBoundedByHeap heap_final store /\
      NStoreResolvedHeapShape heap_final store /\
      NStoreResolvedValShape store v_left ty_left /\
      NStoreResolvedValShape store v_right ty_right /\
      phi = phi_eff1 ++ phi_eff2 ++ phi_left ++ phi_right.

Theorem EPairPar_counted_checked_decomposition_with_static_trace_store :
  CheckedEPairParCountedStaticTraceStoreDecompositionGoal.
Proof.
  unfold CheckedEPairParCountedStaticTraceStoreDecompositionGoal.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right HBack HContext
    HSummaryTraceSound HComp.
  pose proof HContext as HContextOriginal.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (EPairPar_counted_decomposition
      n heap env rho ef1 ea1 ef2 ea2 phi heap_final
      (VPair v_left v_right) HComp)
    as (n_eff1 & n_eff2 & n_left & n_right &
      phi_eff1 & phi_eff2 & phi_left & phi_right &
      theta1 & theta2 & heap_eff1 & heap_eff2 & heap_left & heap_right &
      v_left_decomp & v_right_decomp &
      HSummary1N & HSummary2N & HLeftN & HRightN &
      HCountEff1 & HCountEff2 & HCountLeft & HCountRight &
      HCheckSummary & HCheckTrace & HHeap & HVal & HTrace).
  inversion HVal; subst v_left_decomp v_right_decomp.
  destruct
    (NCBT_PairPar_summary_static_heap_neutral
      gamma omega ef1 ea1 ef2 ea2 HBack)
    as (ty1 & ty2 & eff1 & eff2 & eff_summary1 & eff_summary2 &
      HCheckedLeft & HCheckedRight &
      HCheckedSummary1 & HCheckedSummary2 &
      HStaticNeutral1 & HStaticNeutral2).
  destruct HContext as
    (_ & _ & _ & _ & _ & HRho & _).
  pose proof
    (NCheckedTcExp_eff_wf
      gamma omega (EEffApp ef1 ea1) TyEffect eff_summary1
      HCheckedSummary1)
    as HSummaryWF1.
  destruct
    (NResolveStaticEffect_exists
      0 omega rho eff_summary1 HRho HSummaryWF1)
    as (eff_summary1_res & HResolveSummary1).
  assert
    (HSummary1 :
      SummaryEvaluation heap env rho (EEffApp ef1 ea1)
        phi_eff1 heap_eff1 theta1).
  {
    unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps.
    exact HSummary1N.
  }
  pose proof
    (HSummaryTraceSound
      (EEffApp ef1 ea1) eff_summary1
      phi_eff1 heap_eff1 theta1 eff_summary1_res
      HCheckedSummary1 HSummary1 HResolveSummary1)
    as HCoveredSummary1.
  destruct
    (summary_static_heap_neutral
      heap env rho (EEffApp ef1 ea1)
      phi_eff1 heap_eff1 theta1
      eff_summary1 eff_summary1_res
      HSummary1 HResolveSummary1 HCoveredSummary1 HStaticNeutral1)
    as (HHeapEff1 & HNeutralTrace1).
  subst heap_eff1.
  pose proof
    (NCheckedTcExp_eff_wf
      gamma omega (EEffApp ef2 ea2) TyEffect eff_summary2
      HCheckedSummary2)
    as HSummaryWF2.
  destruct
    (NResolveStaticEffect_exists
      0 omega rho eff_summary2 HRho HSummaryWF2)
    as (eff_summary2_res & HResolveSummary2).
  assert
    (HSummary2 :
      SummaryEvaluation heap env rho (EEffApp ef2 ea2)
        phi_eff2 heap_eff2 theta2).
  {
    unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps.
    exact HSummary2N.
  }
  pose proof
    (HSummaryTraceSound
      (EEffApp ef2 ea2) eff_summary2
      phi_eff2 heap_eff2 theta2 eff_summary2_res
      HCheckedSummary2 HSummary2 HResolveSummary2)
    as HCoveredSummary2.
  destruct
    (summary_static_heap_neutral
      heap env rho (EEffApp ef2 ea2)
      phi_eff2 heap_eff2 theta2
      eff_summary2 eff_summary2_res
      HSummary2 HResolveSummary2 HCoveredSummary2 HStaticNeutral2)
    as (HHeapEff2 & HNeutralTrace2).
  subst heap_eff2.
  subst heap_final.
  destruct
    (checked_sequential_computations_store_value_shapes
      gamma omega heap env rho
      (EMuApp ef1 ea1) ty1 eff1 phi_left heap_left v_left
      (EMuApp ef2 ea2) ty2 eff2 phi_right heap_right v_right
      HContextOriginal HCheckedLeft HCheckedRight
      (NStepsN_to_NSteps _ _ _ _ HLeftN)
      (NStepsN_to_NSteps _ _ _ _ HRightN))
    as (store & ty_left & ty_right &
      _HResolveLeft & _HResolveRight &
      HStoreBounded & HStoreHeap & HValLeft & HValRight).
  exists n_eff1, n_eff2, n_left, n_right,
    phi_eff1, phi_eff2, phi_left, phi_right,
    theta1, theta2, heap_left, heap_right, store, ty_left, ty_right.
  split; [exact HSummary1N |].
  split; [exact HSummary2N |].
  split; [exact HLeftN |].
  split; [exact HRightN |].
  split; [exact HCountEff1 |].
  split; [exact HCountEff2 |].
  split; [exact HCountLeft |].
  split; [exact HCountRight |].
  split.
  - apply heap_neutral_trace_app; assumption.
  - split; [exact HCheckSummary |].
    split; [exact HCheckTrace |].
    split; [reflexivity |].
    split; [exact HStoreBounded |].
    split; [exact HStoreHeap |].
    split; [exact HValLeft |].
    split; [exact HValRight |].
    exact HTrace.
Qed.

Definition CheckedStoreEPairParCountedStaticTraceStoreDecompositionGoal :
    Prop :=
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right,
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final (VPair v_left v_right) ->
    exists n_eff1 n_eff2 n_left n_right
      phi_eff1 phi_eff2 phi_left phi_right
      theta1 theta2 heap_left heap_right store ty_left ty_right,
      NStepsN n_eff1
        (NInitialState heap env rho (EEffApp ef1 ea1))
        phi_eff1
        (StDone heap (VSummary theta1)) /\
      NStepsN n_eff2
        (NInitialState heap env rho (EEffApp ef2 ea2))
        phi_eff2
        (StDone heap (VSummary theta2)) /\
      NStepsN n_left
        (NInitialState heap env rho (EMuApp ef1 ea1))
        phi_left
        (StDone heap_left v_left) /\
      NStepsN n_right
        (NInitialState heap_left env rho (EMuApp ef2 ea2))
        phi_right
        (StDone heap_right v_right) /\
      n_eff1 < n /\
      n_eff2 < n /\
      n_left < n /\
      n_right < n /\
      HeapNeutralTrace (phi_eff1 ++ phi_eff2) /\
      summary_disjointb theta1 theta2 = true /\
      trace_disjointb phi_left phi_right = true /\
      heap_final = heap_right /\
      NStoreKeysBoundedByHeap heap_final store /\
      NStoreResolvedHeapShape heap_final store /\
      NStoreResolvedValShape store v_left ty_left /\
      NStoreResolvedValShape store v_right ty_right /\
      phi = phi_eff1 ++ phi_eff2 ++ phi_left ++ phi_right.

Theorem EPairPar_counted_checked_store_decomposition_with_static_trace_store :
  CheckedStoreEPairParCountedStaticTraceStoreDecompositionGoal.
Proof.
  unfold CheckedStoreEPairParCountedStaticTraceStoreDecompositionGoal.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right HBack HContext
    HSummaryTraceSound HComp.
  pose proof HContext as HContextOriginal.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (EPairPar_counted_decomposition
      n heap env rho ef1 ea1 ef2 ea2 phi heap_final
      (VPair v_left v_right) HComp)
    as (n_eff1 & n_eff2 & n_left & n_right &
      phi_eff1 & phi_eff2 & phi_left & phi_right &
      theta1 & theta2 & heap_eff1 & heap_eff2 & heap_left & heap_right &
      v_left_decomp & v_right_decomp &
      HSummary1N & HSummary2N & HLeftN & HRightN &
      HCountEff1 & HCountEff2 & HCountLeft & HCountRight &
      HCheckSummary & HCheckTrace & HHeap & HVal & HTrace).
  inversion HVal; subst v_left_decomp v_right_decomp.
  destruct
    (NCBT_PairPar_summary_static_heap_neutral
      gamma omega ef1 ea1 ef2 ea2 HBack)
    as (ty1 & ty2 & eff1 & eff2 & eff_summary1 & eff_summary2 &
      HCheckedLeft & HCheckedRight &
      HCheckedSummary1 & HCheckedSummary2 &
      HStaticNeutral1 & HStaticNeutral2).
  destruct HContext as (_ & HRho).
  pose proof
    (NCheckedTcExp_eff_wf
      gamma omega (EEffApp ef1 ea1) TyEffect eff_summary1
      HCheckedSummary1)
    as HSummaryWF1.
  destruct
    (NResolveStaticEffect_exists
      0 omega rho eff_summary1 HRho HSummaryWF1)
    as (eff_summary1_res & HResolveSummary1).
  assert
    (HSummary1 :
      SummaryEvaluation heap env rho (EEffApp ef1 ea1)
        phi_eff1 heap_eff1 theta1).
  {
    unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps.
    exact HSummary1N.
  }
  pose proof
    (HSummaryTraceSound
      (EEffApp ef1 ea1) eff_summary1
      phi_eff1 heap_eff1 theta1 eff_summary1_res
      HCheckedSummary1 HSummary1 HResolveSummary1)
    as HCoveredSummary1.
  destruct
    (summary_static_heap_neutral
      heap env rho (EEffApp ef1 ea1)
      phi_eff1 heap_eff1 theta1
      eff_summary1 eff_summary1_res
      HSummary1 HResolveSummary1 HCoveredSummary1 HStaticNeutral1)
    as (HHeapEff1 & HNeutralTrace1).
  subst heap_eff1.
  pose proof
    (NCheckedTcExp_eff_wf
      gamma omega (EEffApp ef2 ea2) TyEffect eff_summary2
      HCheckedSummary2)
    as HSummaryWF2.
  destruct
    (NResolveStaticEffect_exists
      0 omega rho eff_summary2 HRho HSummaryWF2)
    as (eff_summary2_res & HResolveSummary2).
  assert
    (HSummary2 :
      SummaryEvaluation heap env rho (EEffApp ef2 ea2)
        phi_eff2 heap_eff2 theta2).
  {
    unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps.
    exact HSummary2N.
  }
  pose proof
    (HSummaryTraceSound
      (EEffApp ef2 ea2) eff_summary2
      phi_eff2 heap_eff2 theta2 eff_summary2_res
      HCheckedSummary2 HSummary2 HResolveSummary2)
    as HCoveredSummary2.
  destruct
    (summary_static_heap_neutral
      heap env rho (EEffApp ef2 ea2)
      phi_eff2 heap_eff2 theta2
      eff_summary2 eff_summary2_res
      HSummary2 HResolveSummary2 HCoveredSummary2 HStaticNeutral2)
    as (HHeapEff2 & HNeutralTrace2).
  subst heap_eff2.
  subst heap_final.
  destruct
    (checked_store_sequential_computations_store_value_shapes
      gamma omega heap env rho
      (EMuApp ef1 ea1) ty1 eff1 phi_left heap_left v_left
      (EMuApp ef2 ea2) ty2 eff2 phi_right heap_right v_right
      HContextOriginal HCheckedLeft HCheckedRight
      (NStepsN_to_NSteps _ _ _ _ HLeftN)
      (NStepsN_to_NSteps _ _ _ _ HRightN))
    as (store & ty_left & ty_right &
      _HResolveLeft & _HResolveRight &
      HStoreBounded & HStoreHeap & HValLeft & HValRight).
  exists n_eff1, n_eff2, n_left, n_right,
    phi_eff1, phi_eff2, phi_left, phi_right,
    theta1, theta2, heap_left, heap_right, store, ty_left, ty_right.
  split; [exact HSummary1N |].
  split; [exact HSummary2N |].
  split; [exact HLeftN |].
  split; [exact HRightN |].
  split; [exact HCountEff1 |].
  split; [exact HCountEff2 |].
  split; [exact HCountLeft |].
  split; [exact HCountRight |].
  split.
  - apply heap_neutral_trace_app; assumption.
  - split; [exact HCheckSummary |].
    split; [exact HCheckTrace |].
    split; [reflexivity |].
    split; [exact HStoreBounded |].
    split; [exact HStoreHeap |].
    split; [exact HValLeft |].
    split; [exact HValRight |].
    exact HTrace.
Qed.

Theorem EPairPar_counted_checked_left_store_context :
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right,
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final (VPair v_left v_right) ->
    exists n_left phi_left heap_left,
      CountedComputationEvaluation n_left heap env rho
        (EMuApp ef1 ea1) phi_left heap_left v_left /\
      n_left < n /\
      CheckedStoreRuntimeContext gamma omega heap_left env rho.
Proof.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right HBack HContext
    HSummaryTraceSound HComp.
  destruct
    (EPairPar_counted_checked_decomposition_with_static_trace_store
      n gamma omega heap env rho ef1 ea1 ef2 ea2
      phi heap_final v_left v_right
      HBack HContext HSummaryTraceSound HComp)
    as (_ & _ & n_left & _ &
      _ & _ & phi_left & _ &
      _ & _ & heap_left & _ &
      _ & _ & _ &
      _ & _ & HLeftN & _ &
      _ & _ & HCountLeft & _ &
      _ & _ & _ & _ & _ & _ & _ & _ & _).
  destruct
    (NCBT_PairPar_components
      gamma omega ef1 ea1 ef2 ea2 HBack)
    as (ty1 & _ & eff1 & _ & _ & _ &
      HCheckedLeft & _ & _ & _ & _ & _ & _ & _).
  assert
    (HLeftComp :
      CountedComputationEvaluation n_left heap env rho
        (EMuApp ef1 ea1) phi_left heap_left v_left).
  {
    unfold CountedComputationEvaluation.
    exact HLeftN.
  }
  pose proof
    (checked_store_counted_computation_store_runtime_context
      n_left gamma omega heap env rho
      (EMuApp ef1 ea1) ty1 eff1 phi_left heap_left v_left
      (CheckedRuntimeContext_to_store_context
        gamma omega heap env rho HContext)
      HCheckedLeft HLeftComp)
    as HStoreContext.
  exists n_left, phi_left, heap_left.
  split; [exact HLeftComp |].
  split; [exact HCountLeft |].
  exact HStoreContext.
Qed.

Lemma EPairPar_component_trace_covered :
  forall phi_eff1 phi_eff2 phi_left phi_right theta1 theta2,
    TraceCoveredBySummary phi_eff1 theta1 ->
    TraceCoveredBySummary phi_eff2 theta2 ->
    TraceCoveredBySummary phi_left theta1 ->
    TraceCoveredBySummary phi_right theta2 ->
    TraceCoveredBySummary
      (phi_eff1 ++ phi_eff2 ++ phi_left ++ phi_right)
      (summary_union theta1 theta2).
Proof.
  intros phi_eff1 phi_eff2 phi_left phi_right theta1 theta2
    HCoveredEff1 HCoveredEff2 HCoveredLeft HCoveredRight.
  replace (phi_eff1 ++ phi_eff2 ++ phi_left ++ phi_right)
    with ((phi_eff1 ++ phi_eff2) ++ (phi_left ++ phi_right))
    by (repeat rewrite app_assoc; reflexivity).
  apply trace_covered_app_same.
  - apply trace_covered_app_summary_union;
      [exact HCoveredEff1 | exact HCoveredEff2].
  - apply trace_covered_app_summary_union;
      [exact HCoveredLeft | exact HCoveredRight].
Qed.

Theorem EPairPar_terminal_trace_covered_from_components :
  forall heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final
    phi_eff1 phi_eff2 phi_left phi_right theta1 theta2
    heap_eff1 heap_eff2 heap_left heap_right v_left v_right,
    NSteps
      (NInitialState heap env rho
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)))
      phi
      (StDone heap_final v_final) ->
    SummaryEvaluation
      heap env rho (EEffApp ef1 ea1)
      phi_eff1 heap_eff1 theta1 ->
    SummaryEvaluation
      heap_eff1 env rho (EEffApp ef2 ea2)
      phi_eff2 heap_eff2 theta2 ->
    ComputationEvaluation
      heap_eff2 env rho (EMuApp ef1 ea1)
      phi_left heap_left v_left ->
    ComputationEvaluation
      heap_left env rho (EMuApp ef2 ea2)
      phi_right heap_right v_right ->
    phi = phi_eff1 ++ phi_eff2 ++ phi_left ++ phi_right ->
    TraceCoveredBySummary phi_eff1 theta1 ->
    TraceCoveredBySummary phi_eff2 theta2 ->
    TraceCoveredBySummary phi_left theta1 ->
    TraceCoveredBySummary phi_right theta2 ->
    TraceCoveredBySummary phi (summary_union theta1 theta2).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final
    phi_eff1 phi_eff2 phi_left phi_right theta1 theta2
    heap_eff1 heap_eff2 heap_left heap_right v_left v_right
    _ _ _ _ _ HTrace HCoveredEff1 HCoveredEff2
    HCoveredLeft HCoveredRight.
  subst phi.
  eapply EPairPar_component_trace_covered; eauto.
Qed.

Theorem EPairPar_terminal_trace_covered_from_sequential_concat_summary :
  forall heap env rho ef1 ea1 ef2 ea2
    phi phi_summary heap_summary theta
    phi_eff1 phi_eff2 phi_left phi_right theta1 theta2
    heap_eff1 heap_eff2,
    SummaryEvaluation
      heap env rho (EEffApp ef1 ea1)
      phi_eff1 heap_eff1 theta1 ->
    SummaryEvaluation
      heap_eff1 env rho (EEffApp ef2 ea2)
      phi_eff2 heap_eff2 theta2 ->
    SummaryEvaluation
      heap env rho
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
      phi_summary heap_summary theta ->
    phi = phi_eff1 ++ phi_eff2 ++ phi_left ++ phi_right ->
    TraceCoveredBySummary phi_eff1 theta1 ->
    TraceCoveredBySummary phi_eff2 theta2 ->
    TraceCoveredBySummary phi_left theta1 ->
    TraceCoveredBySummary phi_right theta2 ->
    TraceCoveredBySummary phi theta.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi phi_summary heap_summary theta
    phi_eff1 phi_eff2 phi_left phi_right theta1 theta2
    heap_eff1 heap_eff2
    HSummary1 HSummary2 HSummaryConcat HTrace
    HCoveredEff1 HCoveredEff2 HCoveredLeft HCoveredRight.
  unfold SummaryEvaluation in HSummary1, HSummary2, HSummaryConcat.
  destruct
    (EConcat_summary_deterministic_from_components
      heap env rho (EEffApp ef1 ea1) (EEffApp ef2 ea2)
      phi_eff1 heap_eff1 theta1
      phi_eff2 heap_eff2 theta2
      phi_summary heap_summary theta
      HSummary1 HSummary2 HSummaryConcat)
    as (HTheta & _ & _).
  subst theta phi.
  eapply EPairPar_component_trace_covered; eauto.
Qed.

Theorem EPairPar_terminal_trace_covered_from_concat_summary :
  forall heap env rho ef1 ea1 ef2 ea2
    phi phi_summary heap_summary theta
    phi_eff1 phi_eff2 phi_left phi_right theta1 theta2,
    SummaryEvaluation
      heap env rho (EEffApp ef1 ea1)
      phi_eff1 heap theta1 ->
    SummaryEvaluation
      heap env rho (EEffApp ef2 ea2)
      phi_eff2 heap theta2 ->
    SummaryEvaluation
      heap env rho
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
      phi_summary heap_summary theta ->
    phi = phi_eff1 ++ phi_eff2 ++ phi_left ++ phi_right ->
    TraceCoveredBySummary phi_eff1 theta1 ->
    TraceCoveredBySummary phi_eff2 theta2 ->
    TraceCoveredBySummary phi_left theta1 ->
    TraceCoveredBySummary phi_right theta2 ->
    TraceCoveredBySummary phi theta.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi phi_summary heap_summary theta
    phi_eff1 phi_eff2 phi_left phi_right theta1 theta2
    HSummary1 HSummary2 HSummaryConcat HTrace
    HCoveredEff1 HCoveredEff2 HCoveredLeft HCoveredRight.
  eapply
    (EPairPar_terminal_trace_covered_from_sequential_concat_summary
      heap env rho ef1 ea1 ef2 ea2
      phi phi_summary heap_summary theta
      phi_eff1 phi_eff2 phi_left phi_right theta1 theta2
      heap heap);
    eauto.
Qed.

Theorem EPairPar_counted_terminal_trace_covered_from_component_coverages :
  forall n heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_final phi_summary heap_summary theta,
    CountedComputationEvaluation n heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final v_final ->
    SummaryEvaluation
      heap env rho
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
      phi_summary heap_summary theta ->
    (forall n_eff1 phi_eff1 heap_eff1 theta1,
      n_eff1 < n ->
      NStepsN n_eff1
        (NInitialState heap env rho (EEffApp ef1 ea1))
        phi_eff1
        (StDone heap_eff1 (VSummary theta1)) ->
      TraceCoveredBySummary phi_eff1 theta1) ->
    (forall n_eff2 heap_eff1 phi_eff2 heap_eff2 theta2,
      n_eff2 < n ->
      NStepsN n_eff2
        (NInitialState heap_eff1 env rho (EEffApp ef2 ea2))
        phi_eff2
        (StDone heap_eff2 (VSummary theta2)) ->
      TraceCoveredBySummary phi_eff2 theta2) ->
    (forall n_left heap_eff2 phi_left heap_left v_left theta1,
      n_left < n ->
      NStepsN n_left
        (NInitialState heap_eff2 env rho (EMuApp ef1 ea1))
        phi_left
        (StDone heap_left v_left) ->
      TraceCoveredBySummary phi_left theta1) ->
    (forall n_right heap_left phi_right heap_right v_right theta2,
      n_right < n ->
      NStepsN n_right
        (NInitialState heap_left env rho (EMuApp ef2 ea2))
        phi_right
        (StDone heap_right v_right) ->
      TraceCoveredBySummary phi_right theta2) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_final phi_summary heap_summary theta
    HComp HSummaryConcat HCoveredEff1 HCoveredEff2
    HCoveredLeft HCoveredRight.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (EPairPar_counted_decomposition
      n heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HComp)
    as (n_eff1 & n_eff2 & n_left & n_right &
      phi_eff1 & phi_eff2 & phi_left & phi_right &
      theta1 & theta2 & heap_eff1 & heap_eff2 &
      heap_left & heap_right & v_left & v_right &
      HSummary1 & HSummary2 & HLeft & HRight &
      HCountEff1 & HCountEff2 & HCountLeft & HCountRight &
      _ & _ & _ & _ & HTrace).
  eapply
    (EPairPar_terminal_trace_covered_from_sequential_concat_summary
      heap env rho ef1 ea1 ef2 ea2
      phi phi_summary heap_summary theta
      phi_eff1 phi_eff2 phi_left phi_right theta1 theta2
      heap_eff1 heap_eff2).
  - unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps; exact HSummary1.
  - unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps; exact HSummary2.
  - exact HSummaryConcat.
  - exact HTrace.
  - eapply (HCoveredEff1 n_eff1 phi_eff1 heap_eff1 theta1);
      eauto.
  - eapply (HCoveredEff2 n_eff2 heap_eff1 phi_eff2 heap_eff2 theta2);
      eauto.
  - eapply (HCoveredLeft n_left heap_eff2 phi_left heap_left v_left
      theta1);
      eauto.
  - eapply (HCoveredRight n_right heap_left phi_right heap_right
      v_right theta2);
      eauto.
Qed.

Theorem EPairPar_checked_context_counted_trace_covered_from_below_left :
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta,
    CheckedContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final (VPair v_left v_right) ->
    SummaryEvaluation
      heap env rho
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
      phi_summary heap_summary theta ->
    (forall n_eff1 phi_eff1 theta1,
      n_eff1 < n ->
      NStepsN n_eff1
        (NInitialState heap env rho (EEffApp ef1 ea1))
        phi_eff1
        (StDone heap (VSummary theta1)) ->
      TraceCoveredBySummary phi_eff1 theta1) ->
    (forall n_eff2 phi_eff2 theta2,
      n_eff2 < n ->
      NStepsN n_eff2
        (NInitialState heap env rho (EEffApp ef2 ea2))
        phi_eff2
        (StDone heap (VSummary theta2)) ->
      TraceCoveredBySummary phi_eff2 theta2) ->
    (forall n_right heap_left phi_right heap_right v_right theta2,
      n_right < n ->
      NStepsN n_right
        (NInitialState heap_left env rho (EMuApp ef2 ea2))
        phi_right
        (StDone heap_right v_right) ->
      TraceCoveredBySummary phi_right theta2) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta
    HBelow HBack HContext HSummaryTraceSound HComp HSummaryConcat
    HCoveredSummary1 HCoveredSummary2 HCoveredRight.
  destruct
    (EPairPar_counted_checked_decomposition_with_static_trace_store
      n gamma omega heap env rho ef1 ea1 ef2 ea2
      phi heap_final v_left v_right
      HBack HContext HSummaryTraceSound HComp)
    as (n_eff1 & n_eff2 & n_left & n_right &
      phi_eff1 & phi_eff2 & phi_left & phi_right &
      theta1 & theta2 & heap_left & heap_right &
      store & ty_left & ty_right &
      HSummary1N & HSummary2N & HLeftN & HRightN &
      HCountEff1 & HCountEff2 & HCountLeft & HCountRight &
      _ & _ & _ & _ & _ & _ & _ & _ & HTrace).
  destruct
    (NCBT_PairPar_components
      gamma omega ef1 ea1 ef2 ea2 HBack)
    as (_ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & HBackLeft & _).
  assert
    (HSummary1 :
      SummaryEvaluation heap env rho (EEffApp ef1 ea1)
        phi_eff1 heap theta1).
  {
    unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps.
    exact HSummary1N.
  }
  assert
    (HSummary2 :
      SummaryEvaluation heap env rho (EEffApp ef2 ea2)
        phi_eff2 heap theta2).
  {
    unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps.
    exact HSummary2N.
  }
  assert
    (HCoveredLeft :
      TraceCoveredBySummary phi_left theta1).
  {
    eapply
      (HBelow
        n_left gamma omega heap env rho
        (EMuApp ef1 ea1) (EEffApp ef1 ea1)
        phi_left heap_left v_left
        phi_eff1 heap theta1);
      eauto.
  }
  eapply
    (EPairPar_terminal_trace_covered_from_sequential_concat_summary
      heap env rho ef1 ea1 ef2 ea2
      phi phi_summary heap_summary theta
      phi_eff1 phi_eff2 phi_left phi_right theta1 theta2
      heap heap).
  - exact HSummary1.
  - exact HSummary2.
  - exact HSummaryConcat.
  - exact HTrace.
  - eapply (HCoveredSummary1 n_eff1 phi_eff1 theta1);
      eauto.
  - eapply (HCoveredSummary2 n_eff2 phi_eff2 theta2);
      eauto.
  - exact HCoveredLeft.
  - eapply (HCoveredRight n_right heap_left phi_right heap_right
      v_right theta2);
      eauto.
Qed.

Theorem EPairPar_checked_store_context_counted_trace_covered_from_below_left :
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final (VPair v_left v_right) ->
    SummaryEvaluation
      heap env rho
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
      phi_summary heap_summary theta ->
    (forall n_eff1 phi_eff1 theta1,
      n_eff1 < n ->
      NStepsN n_eff1
        (NInitialState heap env rho (EEffApp ef1 ea1))
        phi_eff1
        (StDone heap (VSummary theta1)) ->
      TraceCoveredBySummary phi_eff1 theta1) ->
    (forall n_eff2 phi_eff2 theta2,
      n_eff2 < n ->
      NStepsN n_eff2
        (NInitialState heap env rho (EEffApp ef2 ea2))
        phi_eff2
        (StDone heap (VSummary theta2)) ->
      TraceCoveredBySummary phi_eff2 theta2) ->
    (forall n_eff2 phi_eff2 theta2
      n_right heap_left phi_right heap_right v_right,
      n_eff2 < n ->
      NStepsN n_eff2
        (NInitialState heap env rho (EEffApp ef2 ea2))
        phi_eff2
        (StDone heap (VSummary theta2)) ->
      n_right < n ->
      CheckedStoreRuntimeContext gamma omega heap_left env rho ->
      NStepsN n_right
        (NInitialState heap_left env rho (EMuApp ef2 ea2))
        phi_right
        (StDone heap_right v_right) ->
      TraceCoveredBySummary phi_right theta2) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta
    HBelow HBack HContext HSummaryTraceSound HComp HSummaryConcat
    HCoveredSummary1 HCoveredSummary2 HCoveredRight.
  destruct
    (EPairPar_counted_checked_decomposition_with_static_trace_store
      n gamma omega heap env rho ef1 ea1 ef2 ea2
      phi heap_final v_left v_right
      HBack HContext HSummaryTraceSound HComp)
    as (n_eff1 & n_eff2 & n_left & n_right &
      phi_eff1 & phi_eff2 & phi_left & phi_right &
      theta1 & theta2 & heap_left & heap_right &
      store & ty_left & ty_right &
      HSummary1N & HSummary2N & HLeftN & HRightN &
      HCountEff1 & HCountEff2 & HCountLeft & HCountRight &
      _ & _ & _ & _ & _ & _ & _ & _ & HTrace).
  destruct
    (NCBT_PairPar_components
      gamma omega ef1 ea1 ef2 ea2 HBack)
    as (ty1 & _ & eff1 & _ & _ & _ &
      HCheckedLeft & _ & _ & _ & _ & _ & HBackLeft & _).
  assert
    (HSummary1 :
      SummaryEvaluation heap env rho (EEffApp ef1 ea1)
        phi_eff1 heap theta1).
  {
    unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps.
    exact HSummary1N.
  }
  assert
    (HSummary2 :
      SummaryEvaluation heap env rho (EEffApp ef2 ea2)
        phi_eff2 heap theta2).
  {
    unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps.
    exact HSummary2N.
  }
  assert
    (HLeftComp :
      CountedComputationEvaluation n_left heap env rho
        (EMuApp ef1 ea1) phi_left heap_left v_left).
  {
    unfold CountedComputationEvaluation.
    exact HLeftN.
  }
  assert
    (HLeftStoreContext :
      CheckedStoreRuntimeContext gamma omega heap_left env rho).
  {
    eapply
      (checked_store_counted_computation_store_runtime_context
        n_left gamma omega heap env rho
        (EMuApp ef1 ea1) ty1 eff1 phi_left heap_left v_left);
      eauto.
    eapply CheckedRuntimeContext_to_store_context; eauto.
  }
  assert
    (HCoveredLeft :
      TraceCoveredBySummary phi_left theta1).
  {
    eapply
      (HBelow
        n_left gamma omega heap env rho
        (EMuApp ef1 ea1) (EEffApp ef1 ea1)
        phi_left heap_left v_left
        phi_eff1 heap theta1);
      eauto using CheckedRuntimeContext_to_store_context.
  }
  eapply
    (EPairPar_terminal_trace_covered_from_sequential_concat_summary
      heap env rho ef1 ea1 ef2 ea2
      phi phi_summary heap_summary theta
      phi_eff1 phi_eff2 phi_left phi_right theta1 theta2
      heap heap).
  - exact HSummary1.
  - exact HSummary2.
  - exact HSummaryConcat.
  - exact HTrace.
  - eapply (HCoveredSummary1 n_eff1 phi_eff1 theta1);
      eauto.
  - eapply (HCoveredSummary2 n_eff2 phi_eff2 theta2);
      eauto.
  - exact HCoveredLeft.
  - eapply (HCoveredRight n_eff2 phi_eff2 theta2
      n_right heap_left phi_right heap_right v_right);
      eauto.
Qed.

Theorem EPairPar_checked_store_entry_counted_trace_covered_from_below_left :
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final (VPair v_left v_right) ->
    SummaryEvaluation
      heap env rho
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
      phi_summary heap_summary theta ->
    (forall n_eff1 phi_eff1 theta1,
      n_eff1 < n ->
      NStepsN n_eff1
        (NInitialState heap env rho (EEffApp ef1 ea1))
        phi_eff1
        (StDone heap (VSummary theta1)) ->
      TraceCoveredBySummary phi_eff1 theta1) ->
    (forall n_eff2 phi_eff2 theta2,
      n_eff2 < n ->
      NStepsN n_eff2
        (NInitialState heap env rho (EEffApp ef2 ea2))
        phi_eff2
        (StDone heap (VSummary theta2)) ->
      TraceCoveredBySummary phi_eff2 theta2) ->
    (forall n_eff2 phi_eff2 theta2
      n_right heap_left phi_right heap_right v_right,
      n_eff2 < n ->
      NStepsN n_eff2
        (NInitialState heap env rho (EEffApp ef2 ea2))
        phi_eff2
        (StDone heap (VSummary theta2)) ->
      n_right < n ->
      CheckedStoreRuntimeContext gamma omega heap_left env rho ->
      NStepsN n_right
        (NInitialState heap_left env rho (EMuApp ef2 ea2))
        phi_right
        (StDone heap_right v_right) ->
      TraceCoveredBySummary phi_right theta2) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta
    HBelow HBack HContext HSummaryTraceSound HComp HSummaryConcat
    HCoveredSummary1 HCoveredSummary2 HCoveredRight.
  destruct
    (EPairPar_counted_checked_store_decomposition_with_static_trace_store
      n gamma omega heap env rho ef1 ea1 ef2 ea2
      phi heap_final v_left v_right
      HBack HContext HSummaryTraceSound HComp)
    as (n_eff1 & n_eff2 & n_left & n_right &
      phi_eff1 & phi_eff2 & phi_left & phi_right &
      theta1 & theta2 & heap_left & heap_right &
      store & ty_left & ty_right &
      HSummary1N & HSummary2N & HLeftN & HRightN &
      HCountEff1 & HCountEff2 & HCountLeft & HCountRight &
      _ & _ & _ & _ & _ & _ & _ & _ & HTrace).
  destruct
    (NCBT_PairPar_components
      gamma omega ef1 ea1 ef2 ea2 HBack)
    as (ty1 & _ & eff1 & _ & _ & _ &
      HCheckedLeft & _ & _ & _ & _ & _ & HBackLeft & _).
  assert
    (HSummary1 :
      SummaryEvaluation heap env rho (EEffApp ef1 ea1)
        phi_eff1 heap theta1).
  {
    unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps.
    exact HSummary1N.
  }
  assert
    (HSummary2 :
      SummaryEvaluation heap env rho (EEffApp ef2 ea2)
        phi_eff2 heap theta2).
  {
    unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps.
    exact HSummary2N.
  }
  assert
    (HLeftComp :
      CountedComputationEvaluation n_left heap env rho
        (EMuApp ef1 ea1) phi_left heap_left v_left).
  {
    unfold CountedComputationEvaluation.
    exact HLeftN.
  }
  assert
    (HLeftStoreContext :
      CheckedStoreRuntimeContext gamma omega heap_left env rho).
  {
    eapply
      (checked_store_counted_computation_store_runtime_context
        n_left gamma omega heap env rho
        (EMuApp ef1 ea1) ty1 eff1 phi_left heap_left v_left);
      eauto.
  }
  assert
    (HCoveredLeft :
      TraceCoveredBySummary phi_left theta1).
  {
    eapply
      (HBelow
        n_left gamma omega heap env rho
        (EMuApp ef1 ea1) (EEffApp ef1 ea1)
        phi_left heap_left v_left
        phi_eff1 heap theta1);
      eauto.
  }
  eapply
    (EPairPar_terminal_trace_covered_from_sequential_concat_summary
      heap env rho ef1 ea1 ef2 ea2
      phi phi_summary heap_summary theta
      phi_eff1 phi_eff2 phi_left phi_right theta1 theta2
      heap heap).
  - exact HSummary1.
  - exact HSummary2.
  - exact HSummaryConcat.
  - exact HTrace.
  - eapply (HCoveredSummary1 n_eff1 phi_eff1 theta1);
      eauto.
  - eapply (HCoveredSummary2 n_eff2 phi_eff2 theta2);
      eauto.
  - exact HCoveredLeft.
  - eapply (HCoveredRight n_eff2 phi_eff2 theta2
      n_right heap_left phi_right heap_right v_right);
      eauto.
Qed.

Definition EPairParRightSummaryReplayBelow
    (n : nat) (gamma : NCtx) (omega : NRgnCtx)
    (heap : Heap) (env : NEnv) (rho : Rho)
    (ef2 ea2 : NExpr) : Prop :=
  forall n_eff2 phi_eff2 theta2 heap_left,
    n_eff2 < n ->
    NStepsN n_eff2
      (NInitialState heap env rho (EEffApp ef2 ea2))
      phi_eff2
      (StDone heap (VSummary theta2)) ->
    CheckedStoreRuntimeContext gamma omega heap_left env rho ->
    exists phi_summary heap_summary,
      SummaryEvaluation heap_left env rho (EEffApp ef2 ea2)
        phi_summary heap_summary theta2.

Definition EPairParRightSummaryReplayAfterLeftBelow
    (n : nat) (gamma : NCtx) (omega : NRgnCtx)
    (heap : Heap) (env : NEnv) (rho : Rho)
    (ef1 ea1 ef2 ea2 : NExpr) : Prop :=
  forall n_eff2 n_left phi_eff2 phi_left theta1 theta2
    heap_left v_left,
    n_eff2 < n ->
    NStepsN n_eff2
      (NInitialState heap env rho (EEffApp ef2 ea2))
      phi_eff2
      (StDone heap (VSummary theta2)) ->
    n_left < n ->
    NStepsN n_left
      (NInitialState heap env rho (EMuApp ef1 ea1))
      phi_left
      (StDone heap_left v_left) ->
    summary_disjointb theta1 theta2 = true ->
    HeapNeutralTrace phi_eff2 ->
    TraceCoveredBySummary phi_eff2 theta2 ->
    TraceCoveredBySummary phi_left theta1 ->
    CheckedStoreRuntimeContext gamma omega heap_left env rho ->
    exists phi_summary heap_summary,
      SummaryEvaluation heap_left env rho (EEffApp ef2 ea2)
        phi_summary heap_summary theta2.

Definition SummaryReplayUnderReadAgreementBelow
    (n : nat) (gamma : NCtx) (omega : NRgnCtx)
    (heap : Heap) (env : NEnv) (rho : Rho)
    (summary_expr : NExpr) : Prop :=
  forall n_summary phi_summary theta heap_left,
    n_summary < n ->
    NStepsN n_summary
      (NInitialState heap env rho summary_expr)
      phi_summary
      (StDone heap (VSummary theta)) ->
    HeapNeutralTrace phi_summary ->
    TraceReadHeapAgreement phi_summary heap heap_left ->
    CheckedStoreRuntimeContext gamma omega heap_left env rho ->
    exists phi_summary' heap_summary',
      SummaryEvaluation heap_left env rho summary_expr
        phi_summary' heap_summary' theta.

Theorem SummaryReplayUnderReadAgreementBelow_from_heap_neutral_replay :
  forall n gamma omega heap env rho summary_expr,
    SummaryReplayUnderReadAgreementBelow
      n gamma omega heap env rho summary_expr.
Proof.
  unfold SummaryReplayUnderReadAgreementBelow.
  intros n gamma omega heap env rho summary_expr
    n_summary phi_summary theta heap_left
    _HCount HSummary HNeutral HAgreement _HStoreContext.
  exists phi_summary, heap_left.
  unfold SummaryEvaluation.
  replace (StDone heap_left (VSummary theta))
    with (with_state_heap heap_left (StDone heap (VSummary theta)))
    by reflexivity.
  change (NSteps
    (with_state_heap heap_left
      (NInitialState heap env rho summary_expr))
    phi_summary
    (with_state_heap heap_left (StDone heap (VSummary theta)))).
  eapply NStepsN_to_NSteps.
  eapply NStepsN_heap_neutral_read_agreement_replay;
    simpl; eauto.
Qed.

Theorem EPairParRightSummaryReplayAfterLeftBelow_from_read_agreement :
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2,
    CheckedRuntimeContext gamma omega heap env rho ->
    SummaryReplayUnderReadAgreementBelow
      n gamma omega heap env rho (EEffApp ef2 ea2) ->
    EPairParRightSummaryReplayAfterLeftBelow
      n gamma omega heap env rho ef1 ea1 ef2 ea2.
Proof.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    HContext HReplayRead.
  unfold EPairParRightSummaryReplayAfterLeftBelow.
  intros n_eff2 n_left phi_eff2 phi_left theta1 theta2
    heap_left v_left HCountSummary HSummary2N HCountLeft HLeftN
    HSummaryDisjoint HNeutralSummary2 HCoveredSummary2 HCoveredLeft
    HStoreContextLeft.
  destruct HContext as (_ & _ & _ & _ & _ & _ & HHeapBounded).
  eapply HReplayRead.
  - exact HCountSummary.
  - exact HSummary2N.
  - exact HNeutralSummary2.
  - eapply
      (NStepsN_trace_read_heap_agreement_for_summary_disjoint
        n_left
        (NInitialState heap env rho (EMuApp ef1 ea1))
        phi_left
        (StDone heap_left v_left)
        phi_eff2 theta1 theta2);
      simpl; eauto.
  - exact HStoreContextLeft.
Qed.

Theorem EPairParRightSummaryReplayAfterLeftBelow_from_read_agreement_store :
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    SummaryReplayUnderReadAgreementBelow
      n gamma omega heap env rho (EEffApp ef2 ea2) ->
    EPairParRightSummaryReplayAfterLeftBelow
      n gamma omega heap env rho ef1 ea1 ef2 ea2.
Proof.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    HContext HReplayRead.
  unfold EPairParRightSummaryReplayAfterLeftBelow.
  intros n_eff2 n_left phi_eff2 phi_left theta1 theta2
    heap_left v_left HCountSummary HSummary2N HCountLeft HLeftN
    HSummaryDisjoint HNeutralSummary2 HCoveredSummary2 HCoveredLeft
    HStoreContextLeft.
  eapply HReplayRead.
  - exact HCountSummary.
  - exact HSummary2N.
  - exact HNeutralSummary2.
  - eapply
      (NStepsN_trace_read_heap_agreement_for_summary_disjoint
        n_left
        (NInitialState heap env rho (EMuApp ef1 ea1))
        phi_left
        (StDone heap_left v_left)
        phi_eff2 theta1 theta2);
      simpl; eauto using CheckedStoreRuntimeContext_heap_keys_bounded.
  - exact HStoreContextLeft.
Qed.

Theorem EPairPar_right_coverage_from_store_below_replayed_summary :
  forall n gamma omega heap env rho ef2 ea2,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EMuApp ef2 ea2) (EEffApp ef2 ea2) ->
    EPairParRightSummaryReplayBelow
      n gamma omega heap env rho ef2 ea2 ->
    forall n_eff2 phi_eff2 theta2
      n_right heap_left phi_right heap_right v_right,
      n_eff2 < n ->
      NStepsN n_eff2
        (NInitialState heap env rho (EEffApp ef2 ea2))
        phi_eff2
        (StDone heap (VSummary theta2)) ->
      n_right < n ->
      CheckedStoreRuntimeContext gamma omega heap_left env rho ->
      NStepsN n_right
        (NInitialState heap_left env rho (EMuApp ef2 ea2))
        phi_right
        (StDone heap_right v_right) ->
      TraceCoveredBySummary phi_right theta2.
Proof.
  intros n gamma omega heap env rho ef2 ea2
    HBelow HBackRight HReplay
    n_eff2 phi_eff2 theta2 n_right heap_left phi_right heap_right
    v_right HCountSummary HSummary2N HCountRight HContextRight
    HRightN.
  destruct
    (HReplay n_eff2 phi_eff2 theta2 heap_left
      HCountSummary HSummary2N HContextRight)
    as (phi_summary & heap_summary & HSummaryRight).
  eapply
    (HBelow
      n_right gamma omega heap_left env rho
      (EMuApp ef2 ea2) (EEffApp ef2 ea2)
      phi_right heap_right v_right
      phi_summary heap_summary theta2);
	    eauto.
Qed.

Theorem EPairPar_right_coverage_from_store_below_replayed_after_left_summary :
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EMuApp ef2 ea2) (EEffApp ef2 ea2) ->
    EPairParRightSummaryReplayAfterLeftBelow
      n gamma omega heap env rho ef1 ea1 ef2 ea2 ->
    forall n_eff2 n_left phi_eff2 phi_left theta1 theta2
      heap_left v_left n_right phi_right heap_right v_right,
      n_eff2 < n ->
      NStepsN n_eff2
        (NInitialState heap env rho (EEffApp ef2 ea2))
        phi_eff2
        (StDone heap (VSummary theta2)) ->
      n_left < n ->
      NStepsN n_left
        (NInitialState heap env rho (EMuApp ef1 ea1))
        phi_left
        (StDone heap_left v_left) ->
      summary_disjointb theta1 theta2 = true ->
      HeapNeutralTrace phi_eff2 ->
      TraceCoveredBySummary phi_eff2 theta2 ->
      TraceCoveredBySummary phi_left theta1 ->
      n_right < n ->
      CheckedStoreRuntimeContext gamma omega heap_left env rho ->
      NStepsN n_right
        (NInitialState heap_left env rho (EMuApp ef2 ea2))
        phi_right
        (StDone heap_right v_right) ->
      TraceCoveredBySummary phi_right theta2.
Proof.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    HBelow HBackRight HReplay
    n_eff2 n_left phi_eff2 phi_left theta1 theta2
    heap_left v_left n_right phi_right heap_right v_right
    HCountSummary HSummary2N HCountLeft HLeftN
    HSummaryDisjoint HNeutralSummary2 HCoveredSummary2 HCoveredLeft
    HCountRight HContextRight HRightN.
  destruct
    (HReplay n_eff2 n_left phi_eff2 phi_left theta1 theta2
      heap_left v_left
      HCountSummary HSummary2N HCountLeft HLeftN
      HSummaryDisjoint HNeutralSummary2 HCoveredSummary2 HCoveredLeft
      HContextRight)
    as (phi_summary & heap_summary & HSummaryRight).
  eapply
    (HBelow
      n_right gamma omega heap_left env rho
      (EMuApp ef2 ea2) (EEffApp ef2 ea2)
      phi_right heap_right v_right
      phi_summary heap_summary theta2);
	    eauto.
Qed.

Theorem EPairPar_checked_store_context_counted_trace_covered_from_below_left_replayed_after_left :
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final (VPair v_left v_right) ->
    SummaryEvaluation
      heap env rho
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
      phi_summary heap_summary theta ->
    (forall n_eff1 phi_eff1 theta1,
      n_eff1 < n ->
      NStepsN n_eff1
        (NInitialState heap env rho (EEffApp ef1 ea1))
        phi_eff1
        (StDone heap (VSummary theta1)) ->
      TraceCoveredBySummary phi_eff1 theta1) ->
    (forall n_eff2 phi_eff2 theta2,
      n_eff2 < n ->
      NStepsN n_eff2
        (NInitialState heap env rho (EEffApp ef2 ea2))
        phi_eff2
        (StDone heap (VSummary theta2)) ->
      TraceCoveredBySummary phi_eff2 theta2) ->
    EPairParRightSummaryReplayAfterLeftBelow
      n gamma omega heap env rho ef1 ea1 ef2 ea2 ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta
    HBelow HBack HContext HSummaryTraceSound HComp HSummaryConcat
    HCoveredSummary1 HCoveredSummary2 HReplay.
  destruct
    (EPairPar_counted_checked_decomposition_with_static_trace_store
      n gamma omega heap env rho ef1 ea1 ef2 ea2
      phi heap_final v_left v_right
      HBack HContext HSummaryTraceSound HComp)
    as (n_eff1 & n_eff2 & n_left & n_right &
      phi_eff1 & phi_eff2 & phi_left & phi_right &
      theta1 & theta2 & heap_left & heap_right &
      store & ty_left & ty_right &
      HSummary1N & HSummary2N & HLeftN & HRightN &
      HCountEff1 & HCountEff2 & HCountLeft & HCountRight &
      HNeutralSummaries & HSummaryDisjoint & _HTraceDisjoint &
      _HHeap & _HStoreBounded & _HStoreHeap & _HValLeft &
      _HValRight & HTrace).
  destruct
    (NCBT_PairPar_components
      gamma omega ef1 ea1 ef2 ea2 HBack)
    as (ty1 & _ & eff1 & _ & _ & _ &
      HCheckedLeft & _ & _ & _ & _ & _ & HBackLeft & HBackRight).
  assert
    (HSummary1 :
      SummaryEvaluation heap env rho (EEffApp ef1 ea1)
        phi_eff1 heap theta1).
  {
    unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps.
    exact HSummary1N.
  }
  assert
    (HSummary2 :
      SummaryEvaluation heap env rho (EEffApp ef2 ea2)
        phi_eff2 heap theta2).
  {
    unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps.
    exact HSummary2N.
  }
  assert
    (HLeftComp :
      CountedComputationEvaluation n_left heap env rho
        (EMuApp ef1 ea1) phi_left heap_left v_left).
  {
    unfold CountedComputationEvaluation.
    exact HLeftN.
  }
  assert
    (HLeftStoreContext :
      CheckedStoreRuntimeContext gamma omega heap_left env rho).
  {
    eapply
      (checked_store_counted_computation_store_runtime_context
        n_left gamma omega heap env rho
        (EMuApp ef1 ea1) ty1 eff1 phi_left heap_left v_left);
      eauto.
    eapply CheckedRuntimeContext_to_store_context; eauto.
  }
  assert
    (HCoveredLeft :
      TraceCoveredBySummary phi_left theta1).
  {
    eapply
      (HBelow
        n_left gamma omega heap env rho
        (EMuApp ef1 ea1) (EEffApp ef1 ea1)
        phi_left heap_left v_left
        phi_eff1 heap theta1);
      eauto using CheckedRuntimeContext_to_store_context.
  }
  assert
    (HCoveredSummary2Actual :
      TraceCoveredBySummary phi_eff2 theta2).
  {
    eapply HCoveredSummary2.
    - exact HCountEff2.
    - exact HSummary2N.
  }
  assert
    (HNeutralSummary2 :
      HeapNeutralTrace phi_eff2).
  {
    eapply heap_neutral_trace_app_r.
    exact HNeutralSummaries.
  }
  eapply
    (EPairPar_terminal_trace_covered_from_sequential_concat_summary
      heap env rho ef1 ea1 ef2 ea2
      phi phi_summary heap_summary theta
      phi_eff1 phi_eff2 phi_left phi_right theta1 theta2
      heap heap).
  - exact HSummary1.
  - exact HSummary2.
  - exact HSummaryConcat.
  - exact HTrace.
  - eapply HCoveredSummary1.
    + exact HCountEff1.
    + exact HSummary1N.
  - exact HCoveredSummary2Actual.
  - exact HCoveredLeft.
  - eapply
      (EPairPar_right_coverage_from_store_below_replayed_after_left_summary
        n gamma omega heap env rho ef1 ea1 ef2 ea2).
    + exact HBelow.
    + exact HBackRight.
    + exact HReplay.
    + exact HCountEff2.
    + exact HSummary2N.
    + exact HCountLeft.
    + exact HLeftN.
    + exact HSummaryDisjoint.
    + exact HNeutralSummary2.
    + exact HCoveredSummary2Actual.
    + exact HCoveredLeft.
    + exact HCountRight.
    + exact HLeftStoreContext.
    + exact HRightN.
Qed.

Theorem EPairPar_checked_store_entry_counted_trace_covered_from_below_left_replayed_after_left :
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final (VPair v_left v_right) ->
    SummaryEvaluation
      heap env rho
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
      phi_summary heap_summary theta ->
    (forall n_eff1 phi_eff1 theta1,
      n_eff1 < n ->
      NStepsN n_eff1
        (NInitialState heap env rho (EEffApp ef1 ea1))
        phi_eff1
        (StDone heap (VSummary theta1)) ->
      TraceCoveredBySummary phi_eff1 theta1) ->
    (forall n_eff2 phi_eff2 theta2,
      n_eff2 < n ->
      NStepsN n_eff2
        (NInitialState heap env rho (EEffApp ef2 ea2))
        phi_eff2
        (StDone heap (VSummary theta2)) ->
      TraceCoveredBySummary phi_eff2 theta2) ->
    EPairParRightSummaryReplayAfterLeftBelow
      n gamma omega heap env rho ef1 ea1 ef2 ea2 ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta
    HBelow HBack HContext HSummaryTraceSound HComp HSummaryConcat
    HCoveredSummary1 HCoveredSummary2 HReplay.
  destruct
    (EPairPar_counted_checked_store_decomposition_with_static_trace_store
      n gamma omega heap env rho ef1 ea1 ef2 ea2
      phi heap_final v_left v_right
      HBack HContext HSummaryTraceSound HComp)
    as (n_eff1 & n_eff2 & n_left & n_right &
      phi_eff1 & phi_eff2 & phi_left & phi_right &
      theta1 & theta2 & heap_left & heap_right &
      store & ty_left & ty_right &
      HSummary1N & HSummary2N & HLeftN & HRightN &
      HCountEff1 & HCountEff2 & HCountLeft & HCountRight &
      HNeutralSummaries & HSummaryDisjoint & _HTraceDisjoint &
      _HHeap & _HStoreBounded & _HStoreHeap & _HValLeft &
      _HValRight & HTrace).
  destruct
    (NCBT_PairPar_components
      gamma omega ef1 ea1 ef2 ea2 HBack)
    as (ty1 & _ & eff1 & _ & _ & _ &
      HCheckedLeft & _ & _ & _ & _ & _ & HBackLeft & HBackRight).
  assert
    (HSummary1 :
      SummaryEvaluation heap env rho (EEffApp ef1 ea1)
        phi_eff1 heap theta1).
  {
    unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps.
    exact HSummary1N.
  }
  assert
    (HSummary2 :
      SummaryEvaluation heap env rho (EEffApp ef2 ea2)
        phi_eff2 heap theta2).
  {
    unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps.
    exact HSummary2N.
  }
  assert
    (HLeftComp :
      CountedComputationEvaluation n_left heap env rho
        (EMuApp ef1 ea1) phi_left heap_left v_left).
  {
    unfold CountedComputationEvaluation.
    exact HLeftN.
  }
  assert
    (HLeftStoreContext :
      CheckedStoreRuntimeContext gamma omega heap_left env rho).
  {
    eapply
      (checked_store_counted_computation_store_runtime_context
        n_left gamma omega heap env rho
        (EMuApp ef1 ea1) ty1 eff1 phi_left heap_left v_left);
      eauto.
  }
  assert
    (HCoveredLeft :
      TraceCoveredBySummary phi_left theta1).
  {
    eapply
      (HBelow
        n_left gamma omega heap env rho
        (EMuApp ef1 ea1) (EEffApp ef1 ea1)
        phi_left heap_left v_left
        phi_eff1 heap theta1);
      eauto.
  }
  assert
    (HCoveredSummary2Actual :
      TraceCoveredBySummary phi_eff2 theta2).
  {
    eapply HCoveredSummary2.
    - exact HCountEff2.
    - exact HSummary2N.
  }
  assert
    (HNeutralSummary2 :
      HeapNeutralTrace phi_eff2).
  {
    eapply heap_neutral_trace_app_r.
    exact HNeutralSummaries.
  }
  eapply
    (EPairPar_terminal_trace_covered_from_sequential_concat_summary
      heap env rho ef1 ea1 ef2 ea2
      phi phi_summary heap_summary theta
      phi_eff1 phi_eff2 phi_left phi_right theta1 theta2
      heap heap).
  - exact HSummary1.
  - exact HSummary2.
  - exact HSummaryConcat.
  - exact HTrace.
  - eapply HCoveredSummary1.
    + exact HCountEff1.
    + exact HSummary1N.
  - exact HCoveredSummary2Actual.
  - exact HCoveredLeft.
  - eapply
      (EPairPar_right_coverage_from_store_below_replayed_after_left_summary
        n gamma omega heap env rho ef1 ea1 ef2 ea2).
    + exact HBelow.
    + exact HBackRight.
    + exact HReplay.
    + exact HCountEff2.
    + exact HSummary2N.
    + exact HCountLeft.
    + exact HLeftN.
    + exact HSummaryDisjoint.
    + exact HNeutralSummary2.
    + exact HCoveredSummary2Actual.
    + exact HCoveredLeft.
    + exact HCountRight.
    + exact HLeftStoreContext.
    + exact HRightN.
Qed.

Theorem EPairPar_checked_store_context_counted_trace_covered_from_below_bodies :
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final (VPair v_left v_right) ->
    SummaryEvaluation
      heap env rho
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
      phi_summary heap_summary theta ->
    (forall n_summary phi_body
      closure_env closure_rho f x ec ee arg theta_body,
      n_summary < n ->
      NStepsN n_summary
        (NInitialState heap
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ee)
        phi_body
        (StDone heap (VSummary theta_body)) ->
      TraceCoveredBySummary phi_body theta_body) ->
    (forall n_eff2 phi_eff2 theta2
      n_right heap_left phi_right heap_right v_right,
      n_eff2 < n ->
      NStepsN n_eff2
        (NInitialState heap env rho (EEffApp ef2 ea2))
        phi_eff2
        (StDone heap (VSummary theta2)) ->
      n_right < n ->
      CheckedStoreRuntimeContext gamma omega heap_left env rho ->
      NStepsN n_right
        (NInitialState heap_left env rho (EMuApp ef2 ea2))
        phi_right
        (StDone heap_right v_right) ->
      TraceCoveredBySummary phi_right theta2) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta
    HBelow HBack HContext HSummaryTraceSound HComp HSummaryConcat
    HCoveredSummaryBody HCoveredRight.
  destruct
    (NCBT_PairPar_components
      gamma omega ef1 ea1 ef2 ea2 HBack)
    as (_ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & HBackLeft & HBackRight).
  eapply
    (EPairPar_checked_store_context_counted_trace_covered_from_below_left
      n gamma omega heap env rho ef1 ea1 ef2 ea2
      phi heap_final v_left v_right phi_summary heap_summary theta);
    eauto.
  - intros n_eff1 phi_eff1 theta1 HCountEff1 HSummary1N.
    assert
      (HCompSummary1 :
        CountedComputationEvaluation n_eff1 heap env rho
          (EEffApp ef1 ea1) phi_eff1 heap (VSummary theta1)).
    {
      unfold CountedComputationEvaluation.
      exact HSummary1N.
    }
    eapply
      (EEffApp_counted_checked_summary_trace_covered_from_store_below_body
        n n_eff1 gamma omega heap env rho ef1 ea1 phi_eff1 theta1);
      try exact HBelow;
      try exact HCountEff1;
      try exact HBackLeft;
      try exact HContext;
      try exact HSummaryTraceSound;
      try exact HCompSummary1.
    intros n_summary phi_body closure_env closure_rho
      f x ec ee arg HCountSummary HBody.
    eapply HCoveredSummaryBody; eauto.
  - intros n_eff2 phi_eff2 theta2 HCountEff2 HSummary2N.
    assert
      (HCompSummary2 :
        CountedComputationEvaluation n_eff2 heap env rho
          (EEffApp ef2 ea2) phi_eff2 heap (VSummary theta2)).
    {
      unfold CountedComputationEvaluation.
      exact HSummary2N.
    }
    eapply
      (EEffApp_counted_checked_summary_trace_covered_from_store_below_body
        n n_eff2 gamma omega heap env rho ef2 ea2 phi_eff2 theta2);
      try exact HBelow;
      try exact HCountEff2;
      try exact HBackRight;
      try exact HContext;
      try exact HSummaryTraceSound;
      try exact HCompSummary2.
    intros n_summary phi_body closure_env closure_rho
      f x ec ee arg HCountSummary HBody.
    eapply HCoveredSummaryBody; eauto.
Qed.

Theorem EPairPar_checked_store_context_counted_trace_covered_from_below_body_contexts :
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final (VPair v_left v_right) ->
    SummaryEvaluation
      heap env rho
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
      phi_summary heap_summary theta ->
    (forall n_summary phi_body
      closure_env closure_rho f x ec ee arg
      gamma_body omega_body ty_body eff_body eff_summary theta_body,
      n_summary < n ->
      CheckedStoreRuntimeContext gamma_body omega_body
        heap
        (env_extend x arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho ->
      NCheckedTcExp gamma_body omega_body ec ty_body eff_body ->
      NCheckedTcExp gamma_body omega_body ee TyEffect eff_summary ->
      NCheckedBackTriangle gamma_body omega_body ec ee ->
      NStepsN n_summary
        (NInitialState heap
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ee)
        phi_body
        (StDone heap (VSummary theta_body)) ->
      TraceCoveredBySummary phi_body theta_body) ->
    (forall n_eff2 phi_eff2 theta2
      n_right heap_left phi_right heap_right v_right,
      n_eff2 < n ->
      NStepsN n_eff2
        (NInitialState heap env rho (EEffApp ef2 ea2))
        phi_eff2
        (StDone heap (VSummary theta2)) ->
      n_right < n ->
      CheckedStoreRuntimeContext gamma omega heap_left env rho ->
      NStepsN n_right
        (NInitialState heap_left env rho (EMuApp ef2 ea2))
        phi_right
        (StDone heap_right v_right) ->
      TraceCoveredBySummary phi_right theta2) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta
    HBelow HBack HContext HSummaryTraceSound HComp HSummaryConcat
    HCoveredSummaryBody HCoveredRight.
  destruct
    (NCBT_PairPar_components
      gamma omega ef1 ea1 ef2 ea2 HBack)
    as (_ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & HBackLeft & HBackRight).
  eapply
    (EPairPar_checked_store_context_counted_trace_covered_from_below_left
      n gamma omega heap env rho ef1 ea1 ef2 ea2
      phi heap_final v_left v_right phi_summary heap_summary theta);
    eauto.
  - intros n_eff1 phi_eff1 theta1 HCountEff1 HSummary1N.
    assert
      (HCompSummary1 :
        CountedComputationEvaluation n_eff1 heap env rho
          (EEffApp ef1 ea1) phi_eff1 heap (VSummary theta1)).
    {
      unfold CountedComputationEvaluation.
      exact HSummary1N.
    }
    eapply
      (EEffApp_counted_checked_summary_trace_covered_from_store_below_body_context
        n n_eff1 gamma omega heap env rho ef1 ea1 phi_eff1 theta1);
      try exact HBelow;
      try exact HCountEff1;
      try exact HBackLeft;
      try exact HContext;
      try exact HSummaryTraceSound;
      try exact HCompSummary1.
	    intros n_summary phi_body closure_env closure_rho
	      f x ec ee arg gamma_body omega_body
	      ty_body eff_body eff_summary HCountSummary
	      HBodyContext HCheckedBody HCheckedSummary HRawBodyBack HBody.
	    eapply HCoveredSummaryBody; eauto.
  - intros n_eff2 phi_eff2 theta2 HCountEff2 HSummary2N.
    assert
      (HCompSummary2 :
        CountedComputationEvaluation n_eff2 heap env rho
          (EEffApp ef2 ea2) phi_eff2 heap (VSummary theta2)).
    {
      unfold CountedComputationEvaluation.
      exact HSummary2N.
    }
    eapply
      (EEffApp_counted_checked_summary_trace_covered_from_store_below_body_context
        n n_eff2 gamma omega heap env rho ef2 ea2 phi_eff2 theta2);
      try exact HBelow;
      try exact HCountEff2;
      try exact HBackRight;
      try exact HContext;
      try exact HSummaryTraceSound;
      try exact HCompSummary2.
	    intros n_summary phi_body closure_env closure_rho
	      f x ec ee arg gamma_body omega_body
	      ty_body eff_body eff_summary HCountSummary
	      HBodyContext HCheckedBody HCheckedSummary HRawBodyBack HBody.
	    eapply HCoveredSummaryBody; eauto.
Qed.

Theorem EPairPar_checked_store_context_counted_trace_covered_from_below_summary_value :
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    CheckedStoreSummaryValueSoundnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final (VPair v_left v_right) ->
    SummaryEvaluation
      heap env rho
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
      phi_summary heap_summary theta ->
    (forall closure_env closure_rho f x ec ee arg
      gamma_body omega_body ty_body eff_body eff_summary,
      CheckedStoreRuntimeContext gamma_body omega_body
        heap
        (env_extend x arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho ->
      NCheckedTcExp gamma_body omega_body ec ty_body eff_body ->
      NCheckedTcExp gamma_body omega_body ee TyEffect eff_summary ->
      NCheckedBackTriangle gamma_body omega_body ec ee) ->
    (forall n_eff2 phi_eff2 theta2
      n_right heap_left phi_right heap_right v_right,
      n_eff2 < n ->
      NStepsN n_eff2
        (NInitialState heap env rho (EEffApp ef2 ea2))
        phi_eff2
        (StDone heap (VSummary theta2)) ->
      n_right < n ->
      CheckedStoreRuntimeContext gamma omega heap_left env rho ->
      NStepsN n_right
        (NInitialState heap_left env rho (EMuApp ef2 ea2))
        phi_right
        (StDone heap_right v_right) ->
      TraceCoveredBySummary phi_right theta2) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta
    HBelow HSummaryValueBelow HBack HContext HSummaryTraceSound
    HComp HSummaryConcat HBodyBack HCoveredRight.
  eapply
    (EPairPar_checked_store_context_counted_trace_covered_from_below_body_contexts
      n gamma omega heap env rho ef1 ea1 ef2 ea2
      phi heap_final v_left v_right phi_summary heap_summary theta).
  - exact HBelow.
  - exact HBack.
  - exact HContext.
  - exact HSummaryTraceSound.
  - exact HComp.
  - exact HSummaryConcat.
  - intros n_summary phi_body closure_env closure_rho
      f x ec ee arg gamma_body omega_body
      ty_body eff_body eff_summary theta_body HCountSummary
      HBodyContext HCheckedBody HCheckedSummary _HRawBodyBack HBody.
    pose proof
      (HBodyBack closure_env closure_rho f x ec ee arg
        gamma_body omega_body ty_body eff_body eff_summary
        HBodyContext HCheckedBody HCheckedSummary)
      as HBackBody.
    eapply
      (HSummaryValueBelow
        n_summary gamma_body omega_body heap
        (env_extend x arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho ec ee eff_summary phi_body heap theta_body).
    + exact HCountSummary.
    + exact HBackBody.
    + exact HCheckedSummary.
    + exact HBodyContext.
    + unfold CountedComputationEvaluation.
      exact HBody.
  - exact HCoveredRight.
Qed.

Theorem EPairPar_checked_store_entry_counted_trace_covered_from_below_summary_value_replayed_after_left :
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    CheckedStoreSummaryValueSoundnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final (VPair v_left v_right) ->
    SummaryEvaluation
      heap env rho
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
      phi_summary heap_summary theta ->
    EPairParRightSummaryReplayAfterLeftBelow
      n gamma omega heap env rho ef1 ea1 ef2 ea2 ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta
    HBelow HSummaryValueBelow HBack HContext HSummaryTraceSound
    HComp HSummaryConcat HReplay.
  destruct
    (NCBT_PairPar_components
      gamma omega ef1 ea1 ef2 ea2 HBack)
    as (_ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & HBackLeft & HBackRight).
  eapply
    (EPairPar_checked_store_entry_counted_trace_covered_from_below_left_replayed_after_left
      n gamma omega heap env rho ef1 ea1 ef2 ea2
      phi heap_final v_left v_right phi_summary heap_summary theta).
  - exact HBelow.
  - exact HBack.
  - exact HContext.
  - exact HSummaryTraceSound.
  - exact HComp.
  - exact HSummaryConcat.
  - intros n_eff1 phi_eff1 theta1 HCountEff1 HSummary1N.
    assert
      (HCompSummary1 :
        CountedComputationEvaluation n_eff1 heap env rho
          (EEffApp ef1 ea1) phi_eff1 heap (VSummary theta1)).
    {
      unfold CountedComputationEvaluation.
      exact HSummary1N.
    }
    eapply
      (EEffApp_counted_checked_summary_trace_covered_from_store_entry_below_summary_value
        n n_eff1 gamma omega heap env rho ef1 ea1 phi_eff1 theta1);
      eauto.
  - intros n_eff2 phi_eff2 theta2 HCountEff2 HSummary2N.
    assert
      (HCompSummary2 :
        CountedComputationEvaluation n_eff2 heap env rho
          (EEffApp ef2 ea2) phi_eff2 heap (VSummary theta2)).
    {
      unfold CountedComputationEvaluation.
      exact HSummary2N.
    }
    eapply
      (EEffApp_counted_checked_summary_trace_covered_from_store_entry_below_summary_value
        n n_eff2 gamma omega heap env rho ef2 ea2 phi_eff2 theta2);
      eauto.
  - exact HReplay.
Qed.

Theorem EPairPar_checked_store_entry_counted_trace_covered_from_below_summary_value_replayed_by_read_agreement :
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    CheckedStoreSummaryValueSoundnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final (VPair v_left v_right) ->
    SummaryEvaluation
      heap env rho
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
      phi_summary heap_summary theta ->
    SummaryReplayUnderReadAgreementBelow
      n gamma omega heap env rho (EEffApp ef2 ea2) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta
    HBelow HSummaryValueBelow HBack HContext HSummaryTraceSound
    HComp HSummaryConcat HReplayRead.
  eapply
    (EPairPar_checked_store_entry_counted_trace_covered_from_below_summary_value_replayed_after_left
      n gamma omega heap env rho ef1 ea1 ef2 ea2
      phi heap_final v_left v_right phi_summary heap_summary theta);
    eauto.
  eapply EPairParRightSummaryReplayAfterLeftBelow_from_read_agreement_store;
    eauto.
Qed.

Theorem EPairPar_checked_store_entry_counted_trace_covered_from_below_summary_value_closed :
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    CheckedStoreSummaryValueSoundnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final (VPair v_left v_right) ->
    SummaryEvaluation
      heap env rho
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta
    HBelow HSummaryValueBelow HBack HContext HSummaryTraceSound
    HComp HSummaryConcat.
  eapply
    (EPairPar_checked_store_entry_counted_trace_covered_from_below_summary_value_replayed_by_read_agreement
      n gamma omega heap env rho ef1 ea1 ef2 ea2
      phi heap_final v_left v_right phi_summary heap_summary theta);
    eauto.
  apply SummaryReplayUnderReadAgreementBelow_from_heap_neutral_replay.
Qed.

Theorem EPairPar_checked_store_context_case_from_below :
  forall n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    CheckedStoreSummaryValueSoundnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final v_final ->
    SummaryEvaluation
      heap env rho
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HSummaryValueBelow HBack HContext HSummaryTraceSound
    HComp HSummaryConcat.
  destruct
    (EPairPar_counted_decomposition
      n heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HComp)
    as (_n_eff1 & _n_eff2 & _n_left & _n_right &
      _phi_eff1 & _phi_eff2 & _phi_left & _phi_right &
      _theta1 & _theta2 & _heap_eff1 & _heap_eff2 &
      _heap_left & _heap_right & v_left & v_right &
      _HSummary1 & _HSummary2 & _HLeft & _HRight &
      _HLtEff1 & _HLtEff2 & _HLtLeft & _HLtRight &
      _HSummaryDisjoint & _HTraceDisjoint &
      _HHeapFinal & HValueFinal & _HTrace).
  subst v_final.
  eapply
    (EPairPar_checked_store_entry_counted_trace_covered_from_below_summary_value_closed
      n gamma omega heap env rho ef1 ea1 ef2 ea2
      phi heap_final v_left v_right phi_summary heap_summary theta);
    eauto.
Qed.

Theorem EPairPar_checked_terminal_trace_covered_from_component_coverages :
  forall gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta,
    NCheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    ComputationEvaluation heap env rho
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      phi heap_final (VPair v_left v_right) ->
    SummaryEvaluation
      heap env rho
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
      phi_summary heap_summary theta ->
    (forall phi_eff1 theta1,
      SummaryEvaluation
        heap env rho (EEffApp ef1 ea1)
        phi_eff1 heap theta1 ->
      TraceCoveredBySummary phi_eff1 theta1) ->
    (forall phi_eff2 theta2,
      SummaryEvaluation
        heap env rho (EEffApp ef2 ea2)
        phi_eff2 heap theta2 ->
      TraceCoveredBySummary phi_eff2 theta2) ->
    (forall phi_eff1 phi_left heap_left v_left theta1,
      SummaryEvaluation
        heap env rho (EEffApp ef1 ea1)
        phi_eff1 heap theta1 ->
      ComputationEvaluation
        heap env rho (EMuApp ef1 ea1)
        phi_left heap_left v_left ->
      TraceCoveredBySummary phi_left theta1) ->
    (forall phi_eff2 phi_right heap_left heap_right v_right theta2,
      SummaryEvaluation
        heap env rho (EEffApp ef2 ea2)
        phi_eff2 heap theta2 ->
      ComputationEvaluation
        heap_left env rho (EMuApp ef2 ea2)
        phi_right heap_right v_right ->
      TraceCoveredBySummary phi_right theta2) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros gamma omega heap env rho ef1 ea1 ef2 ea2
    phi heap_final v_left v_right phi_summary heap_summary theta
    HBack HContext HSummaryTraceSound HComp HSummaryConcat
    HCoveredSummary1 HCoveredSummary2 HCoveredLeft HCoveredRight.
  destruct
    (EPairPar_checked_decomposition_with_static_trace_store
      gamma omega heap env rho ef1 ea1 ef2 ea2
      phi heap_final v_left v_right
      HBack HContext HSummaryTraceSound HComp)
    as (phi_eff1 & phi_eff2 & phi_left & phi_right &
      theta1 & theta2 & heap_left & heap_right &
      store & ty_left & ty_right &
      HSummary1 & HSummary2 & HLeft & HRight &
      _ & _ & _ & _ & _ & _ & _ & _ & HTrace).
  eapply
    (EPairPar_terminal_trace_covered_from_concat_summary
      heap env rho ef1 ea1 ef2 ea2
      phi phi_summary heap_summary theta
      phi_eff1 phi_eff2 phi_left phi_right theta1 theta2).
  - exact HSummary1.
  - exact HSummary2.
  - exact HSummaryConcat.
  - exact HTrace.
  - eapply HCoveredSummary1; eauto.
  - eapply HCoveredSummary2; eauto.
  - eapply HCoveredLeft; eauto.
  - eapply HCoveredRight; eauto.
Qed.
