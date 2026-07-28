From Stdlib Require Import List.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Runtime.Machine.

Import ListNotations.

Inductive Steps : State -> Trace -> State -> Prop :=
| StepsRefl :
    forall state,
      Steps state [] state
| StepsStep :
    forall state label state' phi state'',
      Step state label state' ->
      Steps state' phi state'' ->
      Steps state (label_trace label ++ phi) state''.

Inductive StepsN : nat -> State -> Trace -> State -> Prop :=
| StepsNRefl :
    forall state,
      StepsN 0 state [] state
| StepsNStep :
    forall n state label state' phi state'',
      Step state label state' ->
      StepsN n state' phi state'' ->
      StepsN (S n) state (label_trace label ++ phi) state''.

Lemma StepsN_to_Steps :
  forall n state phi state',
    StepsN n state phi state' ->
    Steps state phi state'.
Proof.
  intros n state phi state' HSteps.
  induction HSteps.
  - constructor.
  - eapply StepsStep; eauto.
Qed.

Lemma Steps_to_StepsN :
  forall state phi state',
    Steps state phi state' ->
    exists n,
      StepsN n state phi state'.
Proof.
  intros state phi state' HSteps.
  induction HSteps as
    [state | state label state' phi state'' HStep _ IH].
  - exists 0. constructor.
  - destruct IH as (n & HStepsN).
    exists (S n).
    eapply StepsNStep; eauto.
Qed.

Lemma Steps_trans :
  forall state1 phi12 state2 phi23 state3,
    Steps state1 phi12 state2 ->
    Steps state2 phi23 state3 ->
    Steps state1 (phi12 ++ phi23) state3.
Proof.
  intros state1 phi12 state2 phi23 state3 H12 H23.
  induction H12 as
    [state | state label state' phi state'' HStep _ IH].
  - simpl. exact H23.
  - replace ((label_trace label ++ phi) ++ phi23)
      with (label_trace label ++ (phi ++ phi23))
      by apply app_assoc.
    eapply StepsStep; eauto.
Qed.

Lemma Steps_done_inv :
  forall heap v phi state,
    Steps (StDone heap v) phi state ->
    phi = [] /\ state = StDone heap v.
Proof.
  intros heap v phi state HSteps.
  inversion HSteps; subst.
  - split; reflexivity.
  - inversion H.
Qed.
