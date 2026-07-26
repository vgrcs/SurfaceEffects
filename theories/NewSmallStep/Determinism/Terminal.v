From Stdlib Require Import List.

Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.Trace.

Import ListNotations.

Theorem NStep_deterministic :
  forall state label1 state1 label2 state2,
    NStep state label1 state1 ->
    NStep state label2 state2 ->
    label1 = label2 /\ state1 = state2.
Proof.
  intros state label1 state1 label2 state2 HStep1.
  revert label2 state2.
  induction HStep1; intros label2 state2 HStep2;
    inversion HStep2; subst;
    try solve [split; reflexivity | split; congruence].
  all: try match goal with
  | H : NStep (StDone _ _) _ _ |- _ => inversion H
  | H : NStep (StError _) _ _ |- _ => inversion H
  end.
  all: try match goal with
  | HTrue : ?b = true, HFalse : ?b = false |- _ =>
      rewrite HTrue in HFalse; discriminate
  | HFalse : ?b = false, HTrue : ?b = true |- _ =>
      rewrite HTrue in HFalse; discriminate
  end.
  all: try match goal with
  | IH : forall label2 state2,
      NStep ?state label2 state2 -> ?label1 = label2 /\ ?state' = state2,
    HStep : NStep ?state ?label2 ?state2 |- _ =>
      destruct (IH _ _ HStep) as [HLabel HState];
      subst; split; reflexivity
  end.
Qed.

Lemma StDone_no_step :
  forall heap v label state,
    ~ NStep (StDone heap v) label state.
Proof.
  intros heap v label state HStep.
  inversion HStep.
Qed.

Lemma NSteps_known_first_step_terminal_inv :
  forall state label state' phi heap v,
    NStep state label state' ->
    NSteps state phi (StDone heap v) ->
    exists phi_tail,
      NSteps state' phi_tail (StDone heap v) /\
      phi = label_trace label ++ phi_tail.
Proof.
  intros state label state' phi heap v HStep HRun.
  inversion HRun; subst.
  - exfalso. eapply StDone_no_step; eauto.
  - destruct
      (NStep_deterministic state label state' label0 state'0 HStep H)
      as [HLabel HState].
    subst label0 state'0.
    exists phi0.
    split; reflexivity || assumption.
Qed.

Lemma NStepsN_known_first_step_terminal_inv :
  forall n state label state' phi heap v,
    NStep state label state' ->
    NStepsN n state phi (StDone heap v) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail state' phi_tail (StDone heap v) /\
      phi = label_trace label ++ phi_tail.
Proof.
  intros n state label state' phi heap v HStep HRun.
  inversion HRun; subst.
  - exfalso. eapply StDone_no_step; eauto.
  - destruct
      (NStep_deterministic state label state' label0 state'0 HStep H)
      as [HLabel HState].
    subst label0 state'0.
    exists n0, phi0.
    repeat split; reflexivity || assumption.
Qed.

Definition TerminalDeterminismGoal : Prop :=
  forall state phi1 heap1 v1 phi2 heap2 v2,
    NSteps state phi1 (StDone heap1 v1) ->
    NSteps state phi2 (StDone heap2 v2) ->
    heap1 = heap2 /\ v1 = v2.

Definition TerminalTraceDeterminismGoal : Prop :=
  forall state phi1 heap1 v1 phi2 heap2 v2,
    NSteps state phi1 (StDone heap1 v1) ->
    NSteps state phi2 (StDone heap2 v2) ->
    phi1 = phi2 /\ heap1 = heap2 /\ v1 = v2.

Theorem NSteps_terminal_trace_deterministic :
  TerminalTraceDeterminismGoal.
Proof.
  unfold TerminalTraceDeterminismGoal.
  intros state phi1 heap1 v1 phi2 heap2 v2 HSteps1.
  revert phi2 heap2 v2.
  remember (StDone heap1 v1) as final_state eqn:HFinal.
  induction HSteps1 as
    [state
    | state label state' phi state'' HStep _ IH];
    intros phi2 heap2 v2 HSteps2; subst.
  - destruct
      (NSteps_done_inv heap1 v1 phi2 (StDone heap2 v2) HSteps2)
      as [HPhi HState].
    inversion HState; subst.
    repeat split; assumption || reflexivity.
  - destruct
      (NSteps_known_first_step_terminal_inv
        state label state' phi2 heap2 v2 HStep HSteps2)
      as (phi_tail & HStepsTail & HPhi2).
    destruct (IH eq_refl _ _ _ HStepsTail) as [HPhiTail [HHeap HV]].
    subst.
    repeat split; assumption || reflexivity.
Qed.

Theorem NSteps_terminal_deterministic :
  TerminalDeterminismGoal.
Proof.
  unfold TerminalDeterminismGoal.
  intros state phi1 heap1 v1 phi2 heap2 v2 HSteps1 HSteps2.
  destruct
    (NSteps_terminal_trace_deterministic
      state phi1 heap1 v1 phi2 heap2 v2 HSteps1 HSteps2)
    as [_ HDet].
  exact HDet.
Qed.
