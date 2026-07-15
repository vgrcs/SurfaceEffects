From Stdlib Require Import List.

Require Import theories.Runtime.Heap.
Require Import theories.Core.Regions.
Require Import theories.Core.Values.
Require Import theories.Runtime.SmallStep.

Definition state_heap (state : State) : Heap :=
  match state with
  | StEval heap _ _ _ _ => heap
  | StReturn heap _ _ => heap
  | StDone heap _ => heap
  end.

Definition with_state_heap (heap : Heap) (state : State) : State :=
  match state with
  | StEval _ env rho e k => StEval heap env rho e k
  | StReturn _ v k => StReturn heap v k
  | StDone _ v => StDone heap v
  end.

Lemma state_heap_with_state_heap :
  forall heap state,
    state_heap (with_state_heap heap state) = heap.
Proof.
  intros heap state.
  destruct state; reflexivity.
Qed.

Lemma with_state_heap_state_heap :
  forall state,
    with_state_heap (state_heap state) state = state.
Proof.
  intros state.
  destruct state; reflexivity.
Qed.

Definition CanStep (state : State) : Prop :=
  exists label state', Step state label state'.

Definition NotStuck (state : State) : Prop :=
  Terminal state \/ CanStep state.

Lemma terminal_not_stuck :
  forall state,
    Terminal state ->
    NotStuck state.
Proof.
  intros state HTerminal.
  left. assumption.
Qed.

Lemma done_no_step :
  forall heap v label state',
    ~ Step (StDone heap v) label state'.
Proof.
  intros heap v label state' HStep.
  inversion HStep.
Qed.

Lemma terminal_no_step :
  forall state label state',
    Terminal state ->
    ~ Step state label state'.
Proof.
  intros state label state' HTerminal HStep.
  inversion HTerminal; subst.
  eapply done_no_step; eauto.
Qed.

Lemma step_not_terminal :
  forall state label state',
    Step state label state' ->
    ~ Terminal state.
Proof.
  intros state label state' HStep HTerminal.
  eapply terminal_no_step; eauto.
Qed.

Lemma step_silent_steps :
  forall state state',
    Step state Silent state' ->
    Steps state nil state'.
Proof.
  intros state state' HStep.
  replace nil with (label_trace Silent ++ nil) by reflexivity.
  econstructor; eauto.
  constructor.
Qed.

Lemma step_act_steps :
  forall state da state',
    Step state (Act da) state' ->
    Steps state (da :: nil) state'.
Proof.
  intros state da state' HStep.
  replace (da :: nil) with (label_trace (Act da) ++ nil) by reflexivity.
  econstructor; eauto.
  constructor.
Qed.

Lemma steps_trans :
  forall state trace1 state' trace2 state'',
    Steps state trace1 state' ->
    Steps state' trace2 state'' ->
    Steps state (trace1 ++ trace2) state''.
Proof.
  intros state trace1 state' trace2 state'' HSteps1 HSteps2.
  induction HSteps1.
  - simpl. assumption.
  - rewrite <- app_assoc.
    econstructor; eauto.
Qed.

Lemma step_deterministic :
  forall state label1 state1 label2 state2,
    Step state label1 state1 ->
    Step state label2 state2 ->
    label1 = label2 /\ state1 = state2.
Proof.
  intros state label1 state1 label2 state2 HStep1 HStep2.
  inversion HStep1; subst; inversion HStep2; subst; try congruence.
  all:
    repeat match goal with
    | H1 : find_E ?x ?env = Some ?v1,
      H2 : find_E ?x ?env = Some ?v2 |- _ =>
        rewrite H1 in H2; inversion H2; subst; clear H2
    | H1 : find_R ?x ?rho = Some ?v1,
      H2 : find_R ?x ?rho = Some ?v2 |- _ =>
        rewrite H1 in H2; inversion H2; subst; clear H2
    | H1 : find_H ?x ?heap = Some ?v1,
      H2 : find_H ?x ?heap = Some ?v2 |- _ =>
        rewrite H1 in H2; inversion H2; subst; clear H2
    | H1 : allocate_H ?heap ?r = ?l1,
      H2 : allocate_H ?heap ?r = ?l2 |- _ =>
        rewrite H1 in H2; subst; clear H2
    end;
    split; reflexivity.
Qed.

Lemma terminal_steps_refl :
  forall state trace state',
    Terminal state ->
    Steps state trace state' ->
    trace = nil /\ state' = state.
Proof.
  intros state trace state' HTerminal HSteps.
  induction HSteps.
  - split; reflexivity.
  - exfalso. eapply terminal_no_step; eauto.
Qed.

Theorem steps_terminal_state_deterministic :
  forall state trace1 state1,
    Steps state trace1 state1 ->
    Terminal state1 ->
    forall trace2 state2,
      Steps state trace2 state2 ->
      Terminal state2 ->
      trace1 = trace2 /\ state1 = state2.
Proof.
  intros state trace1 state1 HSteps1 HTerminal1.
  induction HSteps1 as
    [state | state label state' trace state'' HStep HSteps IH];
    intros trace2 state2 HSteps2 HTerminal2.
  - destruct (terminal_steps_refl state trace2 state2 HTerminal1 HSteps2)
      as [HTrace HState].
    subst. split; reflexivity.
  - inversion HSteps2 as
      [| ? label2 state2' trace2' state2'' HStep2 HSteps2']; subst.
    + exfalso. eapply terminal_no_step; eauto.
    + destruct (step_deterministic _ _ _ _ _ HStep HStep2)
        as [HLabel HState].
      subst.
      destruct (IH HTerminal1 _ _ HSteps2' HTerminal2)
        as [HTrace HFinal].
      subst. split; reflexivity.
Qed.

Theorem Steps_terminal_deterministic :
  forall state trace1 heap1 v1 trace2 heap2 v2,
    Steps state trace1 (StDone heap1 v1) ->
    Steps state trace2 (StDone heap2 v2) ->
    trace1 = trace2 /\ heap1 = heap2 /\ v1 = v2.
Proof.
  intros state trace1 heap1 v1 trace2 heap2 v2 HSteps1 HSteps2.
  destruct
    (steps_terminal_state_deterministic
      state trace1 (StDone heap1 v1) HSteps1
      (Terminal_Done heap1 v1)
      trace2 (StDone heap2 v2) HSteps2
      (Terminal_Done heap2 v2))
    as [HTrace HState].
  split; [exact HTrace |].
  inversion HState; subst.
  split; reflexivity.
Qed.
