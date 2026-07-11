Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepTyping.

Lemma WTState_terminal_not_stuck :
  forall state,
    WTState state ->
    Terminal state ->
    NotStuck state.
Proof.
  intros state _ HTerminal.
  now apply terminal_not_stuck.
Qed.

Lemma WTState_done_is_not_stuck :
  forall heap v,
    WTState (StDone heap v) ->
    NotStuck (StDone heap v).
Proof.
  intros heap v _.
  apply terminal_not_stuck.
  constructor.
Qed.

Lemma WTStateTyped_terminal_not_stuck :
  forall state t,
    WTStateTyped state t ->
    Terminal state ->
    NotStuck state.
Proof.
  intros state t _ HTerminal.
  now apply terminal_not_stuck.
Qed.

Lemma WTStateTyped_done_is_not_stuck :
  forall heap v t,
    WTStateTyped (StDone heap v) t ->
    NotStuck (StDone heap v).
Proof.
  intros heap v t _.
  apply terminal_not_stuck.
  constructor.
Qed.
