From Stdlib Require Import List.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Runtime.Machine.

Import ListNotations.

Inductive NSteps : NState -> Trace -> NState -> Prop :=
| StepsRefl :
    forall state,
      NSteps state [] state
| StepsStep :
    forall state label state' phi state'',
      NStep state label state' ->
      NSteps state' phi state'' ->
      NSteps state (label_trace label ++ phi) state''.

Inductive NStepsN : nat -> NState -> Trace -> NState -> Prop :=
| StepsNRefl :
    forall state,
      NStepsN 0 state [] state
| StepsNStep :
    forall n state label state' phi state'',
      NStep state label state' ->
      NStepsN n state' phi state'' ->
      NStepsN (S n) state (label_trace label ++ phi) state''.

Lemma NStepsN_to_NSteps :
  forall n state phi state',
    NStepsN n state phi state' ->
    NSteps state phi state'.
Proof.
  intros n state phi state' HSteps.
  induction HSteps.
  - constructor.
  - eapply StepsStep; eauto.
Qed.

Lemma NSteps_to_NStepsN :
  forall state phi state',
    NSteps state phi state' ->
    exists n,
      NStepsN n state phi state'.
Proof.
  intros state phi state' HSteps.
  induction HSteps as
    [state | state label state' phi state'' HStep _ IH].
  - exists 0. constructor.
  - destruct IH as (n & HStepsN).
    exists (S n).
    eapply StepsNStep; eauto.
Qed.

Lemma NSteps_trans :
  forall state1 phi12 state2 phi23 state3,
    NSteps state1 phi12 state2 ->
    NSteps state2 phi23 state3 ->
    NSteps state1 (phi12 ++ phi23) state3.
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

Lemma NSteps_done_inv :
  forall heap v phi state,
    NSteps (StDone heap v) phi state ->
    phi = [] /\ state = StDone heap v.
Proof.
  intros heap v phi state HSteps.
  inversion HSteps; subst.
  - split; reflexivity.
  - inversion H.
Qed.
