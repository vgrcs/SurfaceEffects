From stdpp Require Import gmap.
From Stdlib Require Import Program.Equality.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepPreservationTheorems.
Require Import theories.Runtime.SmallStepExplicitStoreBase.
Require Import theories.Runtime.SmallStepExplicitStoreHeap.
Require Import theories.Runtime.SmallStepExplicitStoreTheorems.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.HeapFacts.
Require Import theories.Meta.RegionSubstitutionFacts.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.TraceTypingFacts.
Require Import theories.Meta.TypeFacts.
Require Import theories.Meta.TypingWeakeningFacts.

Require Import theories.Runtime.SmallStepParallelPreservationBase.
Require Export theories.Runtime.SmallStepParallelTyping.

Lemma WTPairParStateRuntimeHeapShapeAt_state_step_preservation :
  forall state tout stty lbl state',
    WTPairParStateRuntimeHeapShapeAt (PPS_State state) tout stty ->
    WTStateRuntimeHeapShapeAt state' tout stty ->
    PairParStep (PPS_State state) lbl (pairpar_state_of_state state') ->
    WTPairParStateRuntimeHeapShapeAt (pairpar_state_of_state state') tout stty.
Proof.
  intros state tout stty lbl state' _ HState' HStep.
  destruct state' as
    [heap env rho e k | heap v k | heap v | left right k];
    simpl in *.
  - constructor; [exact I | exact HState'].
  - constructor; [exact I | exact HState'].
  - constructor; [exact I | exact HState'].
  - inversion HState'; subst.
    eapply WTPPRSA_Run with (tleft := tleft) (tright := tright); eauto.
    intros heap v1 v2 HLeft HRight.
    subst.
    eapply WTStateRuntimeHeapShapeAt_done_pair_return; eauto.
Qed.

Lemma WTPairParStateRuntimeHeapShapeAt_done_step_preservation :
  forall heap v1 v2 k tout stty,
    WTPairParStateRuntimeHeapShapeAt
      (PPS_Run (StDone heap v1) (StDone heap v2) k) tout stty ->
    WTPairParStateRuntimeHeapShapeAt
      (PPS_State (StReturn heap (Pair (v1, v2)) k)) tout stty.
Proof.
	  intros heap v1 v2 k tout stty HWT.
	  inversion HWT; subst.
	  constructor; [exact I |].
	  match goal with
	  | H : PairParDoneContinuationReadyAt
        (StDone heap v1) (StDone heap v2) k tout stty |- _ =>
      eapply H; reflexivity
  end.
Qed.

Lemma WTPairParStateRuntimeHeapShapeAt_left_step_preservation :
  forall left right k tout stty stty' lbl left' tleft',
    WTPairParStateRuntimeHeapShapeAt (PPS_Run left right k) tout stty ->
    Step left lbl left' ->
    WTStateRuntimeHeapShapeAt left' tleft' stty' ->
    TcHeap (state_heap left', stty') ->
    RuntimeHeapShape (state_heap left') stty' ->
    StoreExtends stty stty' ->
    PairParDoneContinuationReadyAt
      left' (with_state_heap (state_heap left') right) k tout stty' ->
    WTPairParStateRuntimeHeapShapeAt
      (PPS_Run left' (with_state_heap (state_heap left') right) k) tout stty'.
Proof.
  intros left right k tout stty stty' lbl left' tleft'
    HWT _ HLeft' HTcHeap HHeapShape HExt HDone.
  inversion HWT; subst.
  eapply WTPPRSA_Run with (tleft := tleft') (tright := tright).
  - exact HLeft'.
  - eapply WTStateRuntimeHeapShapeAt_reheap_store_ext; eauto.
  - exact HDone.
Qed.

Lemma WTPairParStateRuntimeHeapShapeAt_right_step_preservation :
  forall left right k tout stty stty' lbl right' tright',
    WTPairParStateRuntimeHeapShapeAt (PPS_Run left right k) tout stty ->
    Step right lbl right' ->
    WTStateRuntimeHeapShapeAt right' tright' stty' ->
    TcHeap (state_heap right', stty') ->
    RuntimeHeapShape (state_heap right') stty' ->
    StoreExtends stty stty' ->
    PairParDoneContinuationReadyAt
      (with_state_heap (state_heap right') left) right' k tout stty' ->
    WTPairParStateRuntimeHeapShapeAt
      (PPS_Run (with_state_heap (state_heap right') left) right' k) tout stty'.
Proof.
  intros left right k tout stty stty' lbl right' tright'
    HWT _ HRight' HTcHeap HHeapShape HExt HDone.
  inversion HWT; subst.
  eapply WTPPRSA_Run with (tleft := tleft) (tright := tright').
  - eapply WTStateRuntimeHeapShapeAt_reheap_store_ext; eauto.
  - exact HRight'.
  - exact HDone.
Qed.

Lemma WTPairParStateRuntimeHeapShapeAtStrong_done_step_preservation :
  forall heap v1 v2 k tout stty,
    WTPairParStateRuntimeHeapShapeAtStrong
      (PPS_Run (StDone heap v1) (StDone heap v2) k) tout stty ->
    WTPairParStateRuntimeHeapShapeAtStrong
      (PPS_State (StReturn heap (Pair (v1, v2)) k)) tout stty.
Proof.
	  intros heap v1 v2 k tout stty HWT.
	  inversion HWT; subst.
	  constructor; [exact I |].
	  eapply WTStateRuntimeHeapShapeAt_done_pair_return; eauto.
Qed.

Lemma WTPairParStateRuntimeHeapShapeAtStrong_left_step_preservation :
  forall left right k tout stty stty' lbl left',
    WTPairParStateRuntimeHeapShapeAtStrong
      (PPS_Run left right k) tout stty ->
    Step left lbl left' ->
    (forall tleft,
        WTStateRuntimeHeapShapeAt left tleft stty ->
        WTStateRuntimeHeapShapeAt left' tleft stty') ->
    TcHeap (state_heap left', stty') ->
    RuntimeHeapShape (state_heap left') stty' ->
    StoreExtends stty stty' ->
    WTPairParStateRuntimeHeapShapeAtStrong
      (PPS_Run left' (with_state_heap (state_heap left') right) k) tout stty'.
Proof.
  intros left right k tout stty stty' lbl left'
    HWT _ HActive HTcHeap HHeapShape HExt.
  inversion HWT; subst.
  eapply WTPPRSAS_Run with (tleft := tleft) (tright := tright).
  - eapply HActive; eauto.
  - eapply WTStateRuntimeHeapShapeAt_reheap_store_ext; eauto.
  - eapply WTKontRuntime_store_ext; eauto.
Qed.

Lemma WTPairParStateRuntimeHeapShapeAtStrong_right_step_preservation :
  forall left right k tout stty stty' lbl right',
    WTPairParStateRuntimeHeapShapeAtStrong
      (PPS_Run left right k) tout stty ->
    Step right lbl right' ->
    (forall tright,
        WTStateRuntimeHeapShapeAt right tright stty ->
        WTStateRuntimeHeapShapeAt right' tright stty') ->
    TcHeap (state_heap right', stty') ->
    RuntimeHeapShape (state_heap right') stty' ->
    StoreExtends stty stty' ->
    WTPairParStateRuntimeHeapShapeAtStrong
      (PPS_Run (with_state_heap (state_heap right') left) right' k) tout stty'.
Proof.
  intros left right k tout stty stty' lbl right'
    HWT _ HActive HTcHeap HHeapShape HExt.
  inversion HWT; subst.
  eapply WTPPRSAS_Run with (tleft := tleft) (tright := tright).
  - eapply WTStateRuntimeHeapShapeAt_reheap_store_ext; eauto.
  - eapply HActive; eauto.
  - eapply WTKontRuntime_store_ext; eauto.
Qed.


Theorem WTPairParStateRuntimeHeapShapeAtStrong_step_preservation_with_active :
  WTStateRuntimeHeapShapeAtStepPreservation ->
  forall state tout stty lbl state',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParStep state lbl state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' /\
      StoreExtends stty stty'.
Proof.
  intros HActive state tout stty lbl state' HWT HStep.
  inversion HStep; subst.
	  - inversion HWT; subst.
	    match goal with
	    | HState : WTStateRuntimeHeapShapeAt ?state ?tout ?stty,
	      HStepState : Step ?state ?lbl ?state' |- _ =>
	        destruct (HActive state tout stty lbl state' HState HStepState)
	          as (stty' & HState' & _ & _ & HExt)
	    end.
	    exists stty'. split.
	    + destruct state'0 as
	        [heap env rho e k | heap v k | heap v | left right k];
	        simpl in *.
	      * constructor; [exact I | exact HState'].
	      * constructor; [exact I | exact HState'].
	      * constructor; [exact I | exact HState'].
	      * inversion HState'; subst.
	        eapply WTPPRSAS_Run with (tleft := tleft) (tright := tright);
	          eauto.
	    + exact HExt.
  - inversion HWT; subst.
    match goal with
    | HLeft : WTStateRuntimeHeapShapeAt left tleft stty,
      HLeftStep : Step left lbl left' |- _ =>
        destruct (HActive left tleft stty lbl left' HLeft HLeftStep)
          as (stty' & HLeft' & HTcHeap' & HHeapShape' & HExt)
    end.
    exists stty'. split.
    + eapply WTPPRSAS_Run with (tleft := tleft) (tright := tright).
      * exact HLeft'.
      * eapply WTStateRuntimeHeapShapeAt_reheap_store_ext; eauto.
      * eapply WTKontRuntime_store_ext; eauto.
    + exact HExt.
  - inversion HWT; subst.
    match goal with
    | HRight : WTStateRuntimeHeapShapeAt right tright stty,
      HRightStep : Step right lbl right' |- _ =>
        destruct (HActive right tright stty lbl right' HRight HRightStep)
          as (stty' & HRight' & HTcHeap' & HHeapShape' & HExt)
    end.
    exists stty'. split.
    + eapply WTPPRSAS_Run with (tleft := tleft) (tright := tright).
      * eapply WTStateRuntimeHeapShapeAt_reheap_store_ext; eauto.
      * exact HRight'.
      * eapply WTKontRuntime_store_ext; eauto.
    + exact HExt.
  - exists stty. split.
    + eapply WTPairParStateRuntimeHeapShapeAtStrong_done_step_preservation;
        eauto.
    + apply StoreExtends_refl.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_steps_preservation_with_active :
  WTStateRuntimeHeapShapeAtStepPreservation ->
  forall state tout stty trace state',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParSteps state trace state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' /\
      StoreExtends stty stty'.
Proof.
  intros HActive state tout stty trace state' HWT HSteps.
  revert tout stty HWT.
  induction HSteps as
    [state0
    | state0 label state1 trace state2 HStep HSteps IHHSteps];
    intros tout stty HWT.
  - exists stty. split.
    + exact HWT.
    + apply StoreExtends_refl.
  - destruct
      (WTPairParStateRuntimeHeapShapeAtStrong_step_preservation_with_active
        HActive state0 tout stty label state1 HWT HStep)
      as (stty' & HWT' & HExt).
    destruct (IHHSteps tout stty' HWT') as (stty'' & HWT'' & HExt').
    exists stty''. split.
    + exact HWT''.
    + eapply StoreExtends_trans; eauto.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_step_preservation :
  forall state tout stty lbl state',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParStep state lbl state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' /\
      StoreExtends stty stty'.
Proof.
  intros state tout stty lbl state' HWT HStep.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_step_preservation_with_active;
    eauto.
  exact WTStateRuntimeHeapShapeAt_step_preservation.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_steps_preservation :
  forall state tout stty trace state',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParSteps state trace state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' /\
      StoreExtends stty stty'.
Proof.
  intros state tout stty trace state' HWT HSteps.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_steps_preservation_with_active;
    eauto.
  exact WTStateRuntimeHeapShapeAt_step_preservation.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_unified_step_preservation :
  forall state tout stty lbl state',
    WTPairParStateRuntimeHeapShapeAtStrong
      (pairpar_state_of_state state) tout stty ->
    Step state lbl state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong
        (pairpar_state_of_state state') tout stty' /\
      StoreExtends stty stty'.
Proof.
  intros state tout stty lbl state' HWT HStep.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_step_preservation
    with (state' := pairpar_state_of_state state'); eauto.
  exact (pairpar_step_of_step state lbl state' HStep).
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_unified_steps_preservation :
  forall state tout stty trace state',
    WTPairParStateRuntimeHeapShapeAtStrong
      (pairpar_state_of_state state) tout stty ->
    Steps state trace state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong
        (pairpar_state_of_state state') tout stty' /\
      StoreExtends stty stty'.
Proof.
  intros state tout stty trace state' HWT HSteps.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_steps_preservation
    with (state' := pairpar_state_of_state state'); eauto.
  exact (pairpar_steps_of_steps state trace state' HSteps).
Qed.

Theorem unified_step_preserves_pairpar_heap_agreement :
  forall state lbl state',
    PairParRunHeapsAgree (pairpar_state_of_state state) ->
    Step state lbl state' ->
    PairParRunHeapsAgree (pairpar_state_of_state state').
Proof.
  intros state lbl state' HAgree HStep.
  eapply pairpar_step_preserves_heap_agreement
    with (state' := pairpar_state_of_state state'); eauto.
  exact (pairpar_step_of_step state lbl state' HStep).
Qed.

Theorem unified_steps_preserve_pairpar_heap_agreement :
  forall state trace state',
    PairParRunHeapsAgree (pairpar_state_of_state state) ->
    Steps state trace state' ->
    PairParRunHeapsAgree (pairpar_state_of_state state').
Proof.
  intros state trace state' HAgree HSteps.
  eapply pairpar_steps_preserve_heap_agreement
    with (state' := pairpar_state_of_state state'); eauto.
  exact (pairpar_steps_of_steps state trace state' HSteps).
Qed.

Lemma WTPairParStateRuntimeHeapShape_state_step_preservation :
  forall state tout lbl state',
    WTPairParStateRuntimeHeapShape (PPS_State state) tout ->
    PairParStep (PPS_State state) lbl (pairpar_state_of_state state') ->
    WTPairParStateRuntimeHeapShape (pairpar_state_of_state state') tout.
Proof.
  intros state tout lbl state' HWT HStep.
  inversion HWT; subst.
  inversion HStep; subst.
	  pose proof
	    (WTStateRuntimeHeapShape_step_preservation
	      state tout lbl state'0 H1 H3 H5) as HState'.
  destruct state'0 as
    [heap env rho e k | heap v k | heap v | left right k];
    simpl in *.
  - constructor; [exact I | exact HState'].
  - constructor; [exact I | exact HState'].
  - constructor; [exact I | exact HState'].
  - inversion HState'; subst.
    eapply WTPPRS_Run with (tleft := tleft) (tright := tright); eauto.
Qed.

Lemma WTPairParStateRuntimeHeapShape_done_step_preservation :
  forall heap v1 v2 k tout,
    WTPairParStateRuntimeHeapShape
      (PPS_Run (StDone heap v1) (StDone heap v2) k) tout ->
    WTPairParStateRuntimeHeapShape
      (PPS_State (StReturn heap (Pair (v1, v2)) k)) tout.
Proof.
	  intros heap v1 v2 k tout HWT.
	  inversion HWT; subst.
	  constructor; [exact I |].
	  match goal with
  | H : forall heap0 v3 v4,
        StDone heap v1 = StDone heap0 v3 ->
        StDone heap v2 = StDone heap0 v4 ->
        WTStateRuntimeHeapShape (StReturn heap0 (Pair (v3, v4)) k) tout |- _ =>
      eapply H; reflexivity
  end.
Qed.

Lemma WTPairParStateRuntimeHeapShape_left_step_preservation :
	  forall left right k tout lbl left',
	    WTPairParStateRuntimeHeapShape (PPS_Run left right k) tout ->
	    NonPairParRunState left ->
	    Step left lbl left' ->
    (forall tright,
        WTStateRuntimeHeapShape right tright ->
        IdleBranchRetyped (state_heap left') right tright) ->
    PairParDoneContinuationReady
      left' (with_state_heap (state_heap left') right) k tout ->
    WTPairParStateRuntimeHeapShape
      (PPS_Run left' (with_state_heap (state_heap left') right) k) tout.
Proof.
  intros left right k tout lbl left' HWT HNonRun HStep HRetype HDone.
  inversion HWT; subst.
  eapply WTPPRS_Run with (tleft := tleft) (tright := tright).
  - eapply WTStateRuntimeHeapShape_step_preservation; eauto.
  - eapply HRetype; eauto.
  - exact HDone.
Qed.

Lemma WTPairParStateRuntimeHeapShape_right_step_preservation :
	  forall left right k tout lbl right',
	    WTPairParStateRuntimeHeapShape (PPS_Run left right k) tout ->
	    NonPairParRunState right ->
	    Step right lbl right' ->
    (forall tleft,
        WTStateRuntimeHeapShape left tleft ->
        IdleBranchRetyped (state_heap right') left tleft) ->
    PairParDoneContinuationReady
      (with_state_heap (state_heap right') left) right' k tout ->
    WTPairParStateRuntimeHeapShape
      (PPS_Run (with_state_heap (state_heap right') left) right' k) tout.
Proof.
  intros left right k tout lbl right' HWT HNonRun HStep HRetype HDone.
  inversion HWT; subst.
  eapply WTPPRS_Run with (tleft := tleft) (tright := tright).
  - eapply HRetype; eauto.
  - eapply WTStateRuntimeHeapShape_step_preservation; eauto.
  - exact HDone.
Qed.
