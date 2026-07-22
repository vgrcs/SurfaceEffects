From Stdlib Require Import List.

Require Import theories.Runtime.Heap.
Require Import theories.Core.Regions.
Require Import theories.Core.Values.
Require Import theories.Runtime.SmallStep.

Lemma state_heap_with_state_heap :
  forall heap state,
    state_heap (with_state_heap heap state) = heap.
Proof.
  intros heap state.
  revert heap.
  induction state; intros heap0; simpl; auto.
Qed.

Definition NonPairParRunState (state : State) : Prop :=
  match state with
  | StPairParRun _ _ _ => False
  | _ => True
  end.

Lemma with_state_heap_state_heap :
  forall state,
    NonPairParRunState state ->
    with_state_heap (state_heap state) state = state.
Proof.
  intros state HNonPair.
  destruct state; simpl in *; auto; contradiction.
Qed.

Definition CanStep (state : State) : Prop :=
  exists label state', Step state label state'.

Definition StepsStayNonPairParRun (state : State) : Prop :=
  forall trace state',
    Steps state trace state' ->
    NonPairParRunState state'.

Lemma with_state_heap_non_pairpar :
  forall heap state,
    NonPairParRunState state ->
    NonPairParRunState (with_state_heap heap state).
Proof.
  intros heap state HNonPair.
  destruct state; simpl in *; auto.
Qed.

Inductive PairParCheckState : State -> Prop :=
| PPCS_Check :
    forall heap ef1 ea1 ef2 ea2 env rho theta1 theta2 k,
      PairParCheckState
        (StReturn heap (Eff theta2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)).

Fixpoint StatePairParCheckBoundary (state : State) : Prop :=
  match state with
  | StPairParRun left_state right_state _ =>
      StatePairParCheckBoundary left_state \/
      StatePairParCheckBoundary right_state
  | _ => PairParCheckState state
  end.

Definition NotStuck (state : State) : Prop :=
  Terminal state \/ CanStep state \/ StatePairParCheckBoundary state.

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

Lemma steps_stay_non_pairpar_run_tail :
  forall state label state',
    StepsStayNonPairParRun state ->
    Step state label state' ->
    StepsStayNonPairParRun state'.
Proof.
  intros state label state' HStay HStep trace state'' HSteps.
  eapply HStay.
  econstructor; eauto.
Qed.

Lemma step_deterministic :
  forall state label1 state1 label2 state2,
    NonPairParRunState state ->
    Step state label1 state1 ->
    Step state label2 state2 ->
    label1 = label2 /\ state1 = state2.
Proof.
  intros state label1 state1 label2 state2 HNonPair HStep1 HStep2.
  destruct state as
    [heap env rho e k | heap v k | heap v | left_state right_state k];
    simpl in HNonPair; try contradiction;
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

Lemma step_deterministic_non_pairpar :
  forall state label1 state1 label2 state2,
    NonPairParRunState state ->
    Step state label1 state1 ->
    Step state label2 state2 ->
    label1 = label2 /\ state1 = state2.
Proof.
  intros.
  eapply step_deterministic; eauto.
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
    StepsStayNonPairParRun state ->
    Steps state trace1 state1 ->
    Terminal state1 ->
    forall trace2 state2,
      Steps state trace2 state2 ->
      Terminal state2 ->
      trace1 = trace2 /\ state1 = state2.
Proof.
  intros state trace1 state1 HStay HSteps1.
  revert HStay.
  induction HSteps1 as
    [state | state label state' trace state'' HStep HSteps IH];
    intros HStayCurrent HTerminal1 trace2 state2 HSteps2 HTerminal2.
  - destruct (terminal_steps_refl state trace2 state2 HTerminal1 HSteps2)
      as [HTrace HState].
    subst. split; reflexivity.
  - inversion HSteps2 as
      [| ? label2 state2' trace2' state2'' HStep2 HSteps2']; subst.
    + exfalso. eapply terminal_no_step; eauto.
    + assert (HNonPairCurrent : NonPairParRunState state).
      {
        eapply HStayCurrent.
        constructor.
      }
      destruct (step_deterministic _ _ _ _ _ HNonPairCurrent HStep HStep2)
        as [HLabel HState].
      assert (HStayNext : StepsStayNonPairParRun state').
      {
        eapply steps_stay_non_pairpar_run_tail; eauto.
      }
      subst.
      destruct (IH HStayNext HTerminal1 _ _ HSteps2' HTerminal2)
        as [HTrace HFinal].
      subst. split; reflexivity.
Qed.

Theorem Steps_terminal_deterministic :
  forall state trace1 heap1 v1 trace2 heap2 v2,
    StepsStayNonPairParRun state ->
    Steps state trace1 (StDone heap1 v1) ->
    Steps state trace2 (StDone heap2 v2) ->
    trace1 = trace2 /\ heap1 = heap2 /\ v1 = v2.
Proof.
  intros state trace1 heap1 v1 trace2 heap2 v2
    HStay HSteps1 HSteps2.
  destruct
    (steps_terminal_state_deterministic
      state trace1 (StDone heap1 v1) HStay HSteps1
      (Terminal_Done heap1 v1)
      trace2 (StDone heap2 v2) HSteps2
      (Terminal_Done heap2 v2))
    as [HTrace HState].
  split; [exact HTrace |].
  inversion HState; subst.
  split; reflexivity.
Qed.
