From Stdlib Require Import List.

Require Import theories.SmallStep.Core.Values.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Runtime.Trace.

Import ListNotations.

Theorem Step_deterministic :
  forall state label1 state1 label2 state2,
    Step state label1 state1 ->
    Step state label2 state2 ->
    label1 = label2 /\ state1 = state2.
Proof.
  intros state label1 state1 label2 state2 HStep1.
  revert label2 state2.
  induction HStep1; intros label2 state2 HStep2;
    inversion HStep2; subst;
    try solve [split; reflexivity | split; congruence].
  all: try match goal with
  | H : Step (StDone _ _) _ _ |- _ => inversion H
  | H : Step (StError _) _ _ |- _ => inversion H
  end.
  all: try match goal with
  | HTrue : ?b = true, HFalse : ?b = false |- _ =>
      rewrite HTrue in HFalse; discriminate
  | HFalse : ?b = false, HTrue : ?b = true |- _ =>
      rewrite HTrue in HFalse; discriminate
  end.
  all: try match goal with
  | IH : forall label2 state2,
      Step ?state label2 state2 -> ?label1 = label2 /\ ?state' = state2,
    HStep : Step ?state ?label2 ?state2 |- _ =>
      destruct (IH _ _ HStep) as [HLabel HState];
      subst; split; reflexivity
  end.
Qed.

Lemma StDone_no_step :
  forall heap v label state,
    ~ Step (StDone heap v) label state.
Proof.
  intros heap v label state HStep.
  inversion HStep.
Qed.

Lemma Terminal_no_step :
  forall state label state',
    Terminal state ->
    ~ Step state label state'.
Proof.
  intros state label state' HTerminal HStep.
  inversion HTerminal; subst; inversion HStep.
Qed.

Lemma Steps_terminal_start_inv :
  forall state phi state',
    Terminal state ->
    Steps state phi state' ->
    phi = [] /\ state' = state.
Proof.
  intros state phi state' HTerminal HSteps.
  inversion HSteps; subst.
  - split; reflexivity.
  - exfalso.
    eapply Terminal_no_step; eauto.
Qed.

Lemma Steps_known_first_step_to_terminal_inv :
  forall state label state' phi final_state,
    Step state label state' ->
    Steps state phi final_state ->
    Terminal final_state ->
    exists phi_tail,
      Steps state' phi_tail final_state /\
      phi = label_trace label ++ phi_tail.
Proof.
  intros state label state' phi final_state HStep HRun HTerminal.
  inversion HRun; subst.
  - exfalso.
    eapply Terminal_no_step; eauto.
  - destruct
      (Step_deterministic state label state' label0 state'0 HStep H)
      as [HLabel HState].
    subst label0 state'0.
    exists phi0.
    split; reflexivity || assumption.
Qed.

Lemma Steps_known_first_step_terminal_inv :
  forall state label state' phi heap v,
    Step state label state' ->
    Steps state phi (StDone heap v) ->
    exists phi_tail,
      Steps state' phi_tail (StDone heap v) /\
      phi = label_trace label ++ phi_tail.
Proof.
  intros state label state' phi heap v HStep HRun.
  inversion HRun; subst.
  - exfalso. eapply StDone_no_step; eauto.
  - destruct
      (Step_deterministic state label state' label0 state'0 HStep H)
      as [HLabel HState].
    subst label0 state'0.
    exists phi0.
    split; reflexivity || assumption.
Qed.

Lemma StepsN_known_first_step_terminal_inv :
  forall n state label state' phi heap v,
    Step state label state' ->
    StepsN n state phi (StDone heap v) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      StepsN n_tail state' phi_tail (StDone heap v) /\
      phi = label_trace label ++ phi_tail.
Proof.
  intros n state label state' phi heap v HStep HRun.
  inversion HRun; subst.
  - exfalso. eapply StDone_no_step; eauto.
  - destruct
      (Step_deterministic state label state' label0 state'0 HStep H)
      as [HLabel HState].
    subst label0 state'0.
    exists n0, phi0.
    repeat split; reflexivity || assumption.
Qed.

Definition TerminalStateTraceDeterminismGoal : Prop :=
  forall state phi1 final1 phi2 final2,
    Steps state phi1 final1 ->
    Terminal final1 ->
    Steps state phi2 final2 ->
    Terminal final2 ->
    phi1 = phi2 /\ final1 = final2.

Definition TerminalDeterminismGoal : Prop :=
  forall state phi1 heap1 v1 phi2 heap2 v2,
    Steps state phi1 (StDone heap1 v1) ->
    Steps state phi2 (StDone heap2 v2) ->
    heap1 = heap2 /\ v1 = v2.

Definition TerminalTraceDeterminismGoal : Prop :=
  forall state phi1 heap1 v1 phi2 heap2 v2,
    Steps state phi1 (StDone heap1 v1) ->
    Steps state phi2 (StDone heap2 v2) ->
    phi1 = phi2 /\ heap1 = heap2 /\ v1 = v2.

Theorem Steps_terminal_state_trace_deterministic :
  TerminalStateTraceDeterminismGoal.
Proof.
  unfold TerminalStateTraceDeterminismGoal.
  intros state phi1 final1 phi2 final2 HSteps1.
  revert phi2 final2.
  induction HSteps1 as
    [state
    | state label state' phi state'' HStep _ IH];
    intros phi2 final2 HTerminal1 HSteps2 HTerminal2.
  - destruct
      (Steps_terminal_start_inv state phi2 final2 HTerminal1 HSteps2)
      as [HPhi HState].
    subst.
    split; reflexivity.
  - destruct
      (Steps_known_first_step_to_terminal_inv
        state label state' phi2 final2 HStep HSteps2 HTerminal2)
      as (phi_tail & HStepsTail & HPhi2).
    destruct (IH phi_tail final2 HTerminal1 HStepsTail HTerminal2)
      as [HPhiTail HState].
    subst.
    split; reflexivity.
Qed.

Corollary Steps_error_trace_deterministic :
  forall state phi1 heap1 phi2 heap2,
    Steps state phi1 (StError heap1) ->
    Steps state phi2 (StError heap2) ->
    phi1 = phi2 /\ heap1 = heap2.
Proof.
  intros state phi1 heap1 phi2 heap2 HSteps1 HSteps2.
  destruct
    (Steps_terminal_state_trace_deterministic
      state phi1 (StError heap1) phi2 (StError heap2)
      HSteps1 (TerminalError heap1) HSteps2 (TerminalError heap2))
    as [HPhi HState].
  inversion HState; subst.
  split; reflexivity || assumption.
Qed.

Theorem Steps_terminal_trace_deterministic :
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
      (Steps_done_inv heap1 v1 phi2 (StDone heap2 v2) HSteps2)
      as [HPhi HState].
    inversion HState; subst.
    repeat split; assumption || reflexivity.
  - destruct
      (Steps_known_first_step_terminal_inv
        state label state' phi2 heap2 v2 HStep HSteps2)
      as (phi_tail & HStepsTail & HPhi2).
    destruct (IH eq_refl _ _ _ HStepsTail) as [HPhiTail [HHeap HV]].
    subst.
    repeat split; assumption || reflexivity.
Qed.

Theorem Steps_terminal_deterministic :
  TerminalDeterminismGoal.
Proof.
  unfold TerminalDeterminismGoal.
  intros state phi1 heap1 v1 phi2 heap2 v2 HSteps1 HSteps2.
  destruct
    (Steps_terminal_trace_deterministic
      state phi1 heap1 v1 phi2 heap2 v2 HSteps1 HSteps2)
    as [_ HDet].
  exact HDet.
Qed.
