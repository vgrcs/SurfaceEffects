From Stdlib Require Import List.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.DynamicActions.

Inductive PairParState : Type :=
| PPS_State : State -> PairParState
| PPS_Run : State -> State -> Kont -> PairParState.

Definition pairpar_checked_initial
    (heap : Heap) (env : Env) (rho : Rho)
    (ef1 ea1 ef2 ea2 : Expr) (k : Kont) : PairParState :=
  PPS_Run
    (initial_state heap env rho (Mu_App ef1 ea1))
    (initial_state heap env rho (Mu_App ef2 ea2))
    k.

Inductive PairParStep : PairParState -> Label -> PairParState -> Prop :=
| PPStep_State :
    forall state label state',
      Step state label state' ->
      PairParStep (PPS_State state) label (PPS_State state')
| PPStep_Left :
    forall left right k label left',
      Step left label left' ->
      PairParStep (PPS_Run left right k) label
        (PPS_Run left' (with_state_heap (state_heap left') right) k)
| PPStep_Right :
    forall left right k label right',
      Step right label right' ->
      PairParStep (PPS_Run left right k) label
        (PPS_Run (with_state_heap (state_heap right') left) right' k)
| PPStep_Done :
    forall heap v1 v2 k,
      PairParStep (PPS_Run (StDone heap v1) (StDone heap v2) k) Silent
        (PPS_State (StReturn heap (Pair (v1, v2)) k)).

Inductive PairParSteps : PairParState -> Trace -> PairParState -> Prop :=
| PairParSteps_Refl :
    forall state,
      PairParSteps state nil state
| PairParSteps_Step :
    forall state label state' trace state'',
      PairParStep state label state' ->
      PairParSteps state' trace state'' ->
      PairParSteps state (label_trace label ++ trace) state''.

Definition PairParCanStep (state : PairParState) : Prop :=
  exists label state', PairParStep state label state'.

Definition PairParRunHeapsAgree (state : PairParState) : Prop :=
  match state with
  | PPS_State _ => True
  | PPS_Run left_state right_state _ =>
      state_heap left_state = state_heap right_state
  end.

Lemma pairpar_step_preserves_heap_agreement :
  forall state label state',
    PairParRunHeapsAgree state ->
    PairParStep state label state' ->
    PairParRunHeapsAgree state'.
Proof.
  intros state label state' HAgree HStep.
  inversion HStep; subst; simpl in *; auto.
  - rewrite state_heap_with_state_heap. reflexivity.
  - rewrite state_heap_with_state_heap. reflexivity.
Qed.

Lemma pairpar_steps_trans :
  forall state trace1 state' trace2 state'',
    PairParSteps state trace1 state' ->
    PairParSteps state' trace2 state'' ->
    PairParSteps state (trace1 ++ trace2) state''.
Proof.
  intros state trace1 state' trace2 state'' HSteps1 HSteps2.
  induction HSteps1.
  - simpl. assumption.
  - rewrite <- app_assoc.
    econstructor; eauto.
Qed.

Lemma pairpar_steps_preserve_heap_agreement :
  forall state trace state',
    PairParRunHeapsAgree state ->
    PairParSteps state trace state' ->
    PairParRunHeapsAgree state'.
Proof.
  intros state trace state' HAgree HSteps.
  induction HSteps.
  - assumption.
  - apply IHHSteps.
    eapply pairpar_step_preserves_heap_agreement; eauto.
Qed.

Lemma pairpar_left_can_step :
  forall left right k,
    CanStep left ->
    PairParCanStep (PPS_Run left right k).
Proof.
  intros left right k (label & left' & HStep).
  exists label, (PPS_Run left' (with_state_heap (state_heap left') right) k).
  now apply PPStep_Left.
Qed.

Lemma pairpar_right_can_step :
  forall left right k,
    CanStep right ->
    PairParCanStep (PPS_Run left right k).
Proof.
  intros left right k (label & right' & HStep).
  exists label, (PPS_Run (with_state_heap (state_heap right') left) right' k).
  now apply PPStep_Right.
Qed.

Lemma pairpar_done_can_step :
  forall heap v1 v2 k,
    PairParCanStep (PPS_Run (StDone heap v1) (StDone heap v2) k).
Proof.
  intros heap v1 v2 k.
  exists Silent, (PPS_State (StReturn heap (Pair (v1, v2)) k)).
  constructor.
Qed.

Lemma pairpar_checked_initial_heaps_agree :
  forall heap env rho ef1 ea1 ef2 ea2 k,
    PairParRunHeapsAgree
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k.
  reflexivity.
Qed.

Lemma pairpar_checked_initial_left_step :
  forall heap env rho ef1 ea1 ef2 ea2 k label left',
    Step (initial_state heap env rho (Mu_App ef1 ea1)) label left' ->
    PairParStep
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k)
      label
      (PPS_Run left'
        (with_state_heap (state_heap left')
          (initial_state heap env rho (Mu_App ef2 ea2)))
        k).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k label left' HStep.
  apply PPStep_Left.
  exact HStep.
Qed.

Lemma pairpar_checked_initial_left_can_step :
  forall heap env rho ef1 ea1 ef2 ea2 k,
    PairParCanStep
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k.
  eapply pairpar_left_can_step.
  exists Silent,
    (StEval heap env rho ef1 (KMuAppFun ea1 env rho KDone)).
  constructor.
Qed.

Lemma pairpar_checked_initial_right_step :
  forall heap env rho ef1 ea1 ef2 ea2 k label right',
    Step (initial_state heap env rho (Mu_App ef2 ea2)) label right' ->
    PairParStep
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k)
      label
      (PPS_Run
        (with_state_heap (state_heap right')
          (initial_state heap env rho (Mu_App ef1 ea1)))
        right'
        k).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k label right' HStep.
  apply PPStep_Right.
  exact HStep.
Qed.

Lemma pairpar_checked_initial_right_can_step :
  forall heap env rho ef1 ea1 ef2 ea2 k,
    PairParCanStep
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k.
  eapply pairpar_right_can_step.
  exists Silent,
    (StEval heap env rho ef2 (KMuAppFun ea2 env rho KDone)).
  constructor.
Qed.

Lemma pairpar_finished_branches_return_pair :
  forall heap v1 v2 k,
    PairParStep (PPS_Run (StDone heap v1) (StDone heap v2) k) Silent
      (PPS_State (StReturn heap (Pair (v1, v2)) k)).
Proof.
  intros heap v1 v2 k.
  constructor.
Qed.
