From Stdlib Require Import List.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.DynamicActions.

(* Branch-scheduled Pair_Par runs are part of the ordinary [Step] machine:
   [State] has the [StPairParRun] constructor and [Step] contains the
   left/right/done rules for it.  The [PairParState]/[PairParStep] layer below
   is a proof view used to name the checked branch scheduler and to split
   traces into state/left/right components.  The conversion lemmas
   [pairpar_step_as_step], [pairpar_step_of_step], [pairpar_steps_as_steps], and
   [pairpar_steps_of_steps] keep this view connected to the single transition
   system. *)

Inductive PairParState : Type :=
| PPS_State : State -> PairParState
| PPS_Run : State -> State -> Kont -> PairParState.

Definition pairpar_state_as_state (state : PairParState) : State :=
  match state with
  | PPS_State state => state
  | PPS_Run left_state right_state k =>
      StPairParRun left_state right_state k
  end.

Definition pairpar_state_of_state (state : State) : PairParState :=
  match state with
  | StPairParRun left_state right_state k =>
      PPS_Run left_state right_state k
  | _ => PPS_State state
  end.

Lemma pairpar_state_of_state_non_pair :
  forall state,
    NonPairParRunState state ->
    pairpar_state_of_state state = PPS_State state.
Proof.
  intros state HNonPair.
  destruct state; simpl in *; try reflexivity.
  contradiction.
Qed.

Lemma pairpar_state_as_state_of_state :
  forall state,
    pairpar_state_as_state (pairpar_state_of_state state) = state.
Proof.
  intros state.
  destruct state; reflexivity.
Qed.

Lemma pairpar_state_of_state_as_state_run :
  forall left_state right_state k,
    pairpar_state_of_state
      (pairpar_state_as_state (PPS_Run left_state right_state k)) =
    PPS_Run left_state right_state k.
Proof.
  reflexivity.
Qed.

Definition pairpar_checked_initial
    (heap : Heap) (env : Env) (rho : Rho)
    (ef1 ea1 ef2 ea2 : Expr) (k : Kont) : PairParState :=
  PPS_Run
    (initial_state heap env rho (Mu_App ef1 ea1))
    (initial_state heap env rho (Mu_App ef2 ea2))
    k.

Definition pairpar_unified_checked_initial
    (heap : Heap) (env : Env) (rho : Rho)
    (ef1 ea1 ef2 ea2 : Expr) (k : Kont) : State :=
  StPairParRun
    (initial_state heap env rho (Mu_App ef1 ea1))
    (initial_state heap env rho (Mu_App ef2 ea2))
    k.

Lemma pairpar_checked_initial_as_state :
  forall heap env rho ef1 ea1 ef2 ea2 k,
    pairpar_state_as_state
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k) =
    pairpar_unified_checked_initial heap env rho ef1 ea1 ef2 ea2 k.
Proof.
  reflexivity.
Qed.

Inductive PairParStep : PairParState -> Label -> PairParState -> Prop :=
| PPStep_State :
    forall state label state',
      NonPairParRunState state ->
      Step state label state' ->
      PairParStep (PPS_State state) label (pairpar_state_of_state state')
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

Fixpoint StateRunHeapsAgree (state : State) : Prop :=
  match state with
  | StPairParRun left_state right_state _ =>
      state_heap left_state = state_heap right_state /\
      StateRunHeapsAgree left_state /\
      StateRunHeapsAgree right_state
  | _ => True
  end.

Definition PairParRunHeapsAgree (state : PairParState) : Prop :=
  match state with
  | PPS_State state => StateRunHeapsAgree state
  | PPS_Run left_state right_state _ =>
      state_heap left_state = state_heap right_state /\
      StateRunHeapsAgree left_state /\
      StateRunHeapsAgree right_state
  end.

Lemma NonPairParRunState_run_heaps_agree :
  forall state,
    NonPairParRunState state ->
    StateRunHeapsAgree state.
Proof.
  intros state HNonPair.
  destruct state; simpl in *; try exact I.
  exfalso. exact HNonPair.
Qed.

Lemma StateRunHeapsAgree_with_state_heap :
  forall heap state,
    StateRunHeapsAgree state ->
    StateRunHeapsAgree (with_state_heap heap state).
Proof.
  intros heap state.
  revert heap.
  induction state; intros heap0 HAgree; simpl in *; auto.
  destruct HAgree as [_ [HLeft HRight]].
  split.
  - repeat rewrite state_heap_with_state_heap. reflexivity.
  - split; auto.
Qed.

Lemma with_state_heap_state_heap_agree :
  forall state,
    StateRunHeapsAgree state ->
    with_state_heap (state_heap state) state = state.
Proof.
  intros state HAgree.
  induction state; simpl in *; auto.
  destruct HAgree as [HHeap [HLeftAgree HRightAgree]].
  rewrite (IHstate1 HLeftAgree).
  rewrite HHeap.
  rewrite (IHstate2 HRightAgree).
  reflexivity.
Qed.

Lemma step_preserves_state_run_heaps_agree :
  forall state label state',
    StateRunHeapsAgree state ->
    Step state label state' ->
    StateRunHeapsAgree state'.
Proof.
	  intros state label state' HAgree HStep.
	  induction HStep; simpl in *; auto.
	  - destruct HAgree as [HHeap [HLeftAgree HRightAgree]].
	    split.
	    + rewrite state_heap_with_state_heap. reflexivity.
	    + split.
	      * apply IHHStep. exact HLeftAgree.
	      * apply StateRunHeapsAgree_with_state_heap. exact HRightAgree.
	  - destruct HAgree as [HHeap [HLeftAgree HRightAgree]].
	    split.
	    + rewrite state_heap_with_state_heap. reflexivity.
	    + split.
	      * apply StateRunHeapsAgree_with_state_heap. exact HLeftAgree.
	      * apply IHHStep. exact HRightAgree.
Qed.

Lemma pairpar_step_preserves_heap_agreement :
  forall state label state',
    PairParRunHeapsAgree state ->
    PairParStep state label state' ->
    PairParRunHeapsAgree state'.
Proof.
	  intros state label state' HAgree HStep.
	  inversion HStep; subst; simpl in *; auto.
	  - destruct state'0 as
	      [heap env rho e k | heap v k | heap v | left right k];
	      simpl in *; auto.
	    change (StateRunHeapsAgree (StPairParRun left right k)).
	    eapply step_preserves_state_run_heaps_agree; eauto.
	  - destruct HAgree as [_ [HLeftAgree HRightAgree]].
	    split.
	    + rewrite state_heap_with_state_heap. reflexivity.
	    + split.
	      * eapply step_preserves_state_run_heaps_agree.
	        -- exact HLeftAgree.
	        -- eassumption.
	      * apply StateRunHeapsAgree_with_state_heap. exact HRightAgree.
	  - destruct HAgree as [_ [HLeftAgree HRightAgree]].
	    split.
	    + rewrite state_heap_with_state_heap. reflexivity.
	    + split.
	      * apply StateRunHeapsAgree_with_state_heap. exact HLeftAgree.
	      * eapply step_preserves_state_run_heaps_agree.
	        -- exact HRightAgree.
	        -- eassumption.
Qed.

Lemma pairpar_step_as_step :
  forall state label state',
    PairParRunHeapsAgree state ->
    PairParStep state label state' ->
    Step (pairpar_state_as_state state) label
      (pairpar_state_as_state state').
Proof.
  intros state label state' HAgree HStep.
	  inversion HStep; subst; simpl in *.
	  - rewrite pairpar_state_as_state_of_state. exact H0.
	  - destruct HAgree as [HHeap _].
	    eapply Step_PairParRun_Left; eauto.
	  - destruct HAgree as [HHeap _].
	    eapply Step_PairParRun_Right; eauto.
	  - apply Step_PairParRun_Done.
Qed.

Lemma pairpar_step_of_step :
  forall state label state',
    Step state label state' ->
    PairParStep
      (pairpar_state_of_state state)
      label
      (pairpar_state_of_state state').
Proof.
  intros state label state' HStep.
  destruct state as
    [heap env rho e k | heap v k | heap v | left_state right_state k];
    simpl in *.
  - apply PPStep_State; [exact I | exact HStep].
  - apply PPStep_State; [exact I | exact HStep].
  - inversion HStep.
  - inversion HStep; subst.
    + apply PPStep_Left. eassumption.
    + apply PPStep_Right. eassumption.
    + apply PPStep_Done.
Qed.

Lemma pairpar_steps_as_steps :
  forall state trace state',
    PairParRunHeapsAgree state ->
    PairParSteps state trace state' ->
    Steps
      (pairpar_state_as_state state)
      trace
      (pairpar_state_as_state state').
Proof.
  intros state trace state' HAgree HSteps.
  induction HSteps.
  - constructor.
  - econstructor.
    + eapply pairpar_step_as_step; eauto.
    + apply IHHSteps.
      eapply pairpar_step_preserves_heap_agreement; eauto.
Qed.

Lemma pairpar_steps_of_steps :
  forall state trace state',
    Steps state trace state' ->
    PairParSteps
      (pairpar_state_of_state state)
      trace
      (pairpar_state_of_state state').
Proof.
  intros state trace state' HSteps.
  induction HSteps.
  - constructor.
  - econstructor.
    + apply pairpar_step_of_step. exact H.
    + exact IHHSteps.
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
  simpl. split.
  - reflexivity.
  - split; simpl; exact I.
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
