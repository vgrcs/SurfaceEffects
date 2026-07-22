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
Require Import theories.Runtime.SmallStepTraceSafety.
Require Export theories.Runtime.SmallStepParallelStepPreservation.
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

Definition PairParTerminal (state : PairParState) : Prop :=
  match state with
  | PPS_State state => Terminal state
  | PPS_Run _ _ _ => False
  end.

Definition PairParCheckBoundary (state : PairParState) : Prop :=
  match state with
  | PPS_State state => StatePairParCheckBoundary state
  | PPS_Run left_state right_state _ =>
      StatePairParCheckBoundary left_state \/
      StatePairParCheckBoundary right_state
  end.

Definition PairParNotStuck (state : PairParState) : Prop :=
  PairParTerminal state \/ PairParCanStep state \/ PairParCheckBoundary state.

Definition PairParEvalHeadRegionsResolved (state : PairParState) : Prop :=
  match state with
  | PPS_State state => StateEvalHeadRegionsResolved state
  | PPS_Run left_state right_state _ =>
      StateEvalHeadRegionsResolved left_state /\
      StateEvalHeadRegionsResolved right_state
  end.

Lemma PairParEvalHeadRegionsResolved_left_step :
  forall left right k left',
    PairParEvalHeadRegionsResolved (PPS_Run left right k) ->
    StateEvalHeadRegionsResolved left' ->
    PairParEvalHeadRegionsResolved
      (PPS_Run left' (with_state_heap (state_heap left') right) k).
Proof.
  intros left right k left' HReady HLeftReady.
  simpl in *.
  destruct HReady as [_ HRightReady].
  split.
  - exact HLeftReady.
  - apply StateEvalHeadRegionsResolved_with_state_heap.
    exact HRightReady.
Qed.

Lemma PairParEvalHeadRegionsResolved_right_step :
  forall left right k right',
    PairParEvalHeadRegionsResolved (PPS_Run left right k) ->
    StateEvalHeadRegionsResolved right' ->
    PairParEvalHeadRegionsResolved
      (PPS_Run (with_state_heap (state_heap right') left) right' k).
Proof.
  intros left right k right' HReady HRightReady.
  simpl in *.
  destruct HReady as [HLeftReady _].
  split.
  - apply StateEvalHeadRegionsResolved_with_state_heap.
    exact HLeftReady.
  - exact HRightReady.
Qed.

Lemma WTPairParStateRuntimeHeapShape_eval_heads_resolved :
  forall state tout,
    WTPairParStateRuntimeHeapShape state tout ->
    PairParEvalHeadRegionsResolved state.
Proof.
  intros state tout HWT.
  inversion HWT; subst; simpl.
  - eapply WTStateRuntimeHeapShape_eval_heads_resolved; eauto.
  - split;
      eapply WTStateRuntimeHeapShape_eval_heads_resolved; eauto.
Qed.

Lemma WTPairParStateRuntimeHeapShapeAtStrong_eval_heads_resolved :
  forall state tout stty,
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParEvalHeadRegionsResolved state.
Proof.
  intros state tout stty HWT.
  eapply WTPairParStateRuntimeHeapShape_eval_heads_resolved.
  eapply WTPairParStateRuntimeHeapShapeAt_forget.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_forget; eauto.
Qed.

Theorem WTStateRuntimeHeapShape_not_stuck_with_run_agreement :
  PairParCheckDecidable ->
  forall state tout,
    WTStateRuntimeHeapShape state tout ->
    StateRunHeapsAgree state ->
    StateEvalHeadRegionsResolved state ->
    NotStuck state.
Proof.
  intros HDec state tout HWT.
  induction HWT; intros HAgree HReady; simpl in *.
  - apply
      (WTStateRuntimeHeapShape_not_stuck
        HDec (StEval heap env rho e k) tout).
    + econstructor; eauto.
    + exact I.
    + intros heap0 env0 rho0 e0 k0 HState.
      inversion HState; subst. exact HReady.
  - apply
      (WTStateRuntimeHeapShape_not_stuck
        HDec (StReturn heap v k) tout).
    + econstructor; eauto.
    + exact I.
    + intros heap0 env0 rho0 e0 k0 HState.
      discriminate HState.
  - left. constructor.
  - destruct HAgree as [HHeap [HLeftAgree HRightAgree]].
    destruct HReady as [HLeftReady HRightReady].
    destruct (IHHWT1 HLeftAgree HLeftReady)
      as [HLeftTerminal | [HLeftCanStep | HLeftCheck]].
    + inversion HLeftTerminal; subst.
      destruct (IHHWT2 HRightAgree HRightReady)
        as [HRightTerminal | [HRightCanStep | HRightCheck]].
      * inversion HRightTerminal; subst.
        simpl in HHeap. subst.
        right. left.
        eexists Silent. eexists.
        apply Step_PairParRun_Done.
      * right. left.
        destruct HRightCanStep as [label [right' HRightStep]].
        eexists label. eexists.
        eapply Step_PairParRun_Right; eauto.
      * right. right. right. exact HRightCheck.
    + right. left.
      destruct HLeftCanStep as [label [left' HLeftStep]].
      eexists label. eexists.
      eapply Step_PairParRun_Left; eauto.
    + right. right. left. exact HLeftCheck.
Qed.

Theorem WTPairParStateRuntimeHeapShape_not_stuck :
  PairParCheckDecidable ->
  forall state tout,
    WTPairParStateRuntimeHeapShape state tout ->
    PairParRunHeapsAgree state ->
    PairParEvalHeadRegionsResolved state ->
    PairParNotStuck state.
Proof.
	  intros HDec state tout HWT HAgree HReady.
	  inversion HWT as
	    [state0 tout0 HNonRun HState
	    | left_state right_state k tleft tright tout0 HLeft HRight HDone];
	    subst.
	  - destruct
	      (WTStateRuntimeHeapShape_not_stuck_with_run_agreement
	        HDec state0 tout HState HAgree HReady)
	      as [HTerminal | [HCanStep | HCheck]].
	    + left. exact HTerminal.
	    + right. left.
	      destruct HCanStep as (label & state' & HStep).
	      exists label, (pairpar_state_of_state state').
	      apply PPStep_State; eauto.
	    + right. right. exact HCheck.
	  - simpl in HAgree.
	    simpl in HReady.
	    destruct HAgree as [HHeap [HLeftAgree HRightAgree]].
	    destruct HReady as [HLeftReady HRightReady].
	    destruct
	      (WTStateRuntimeHeapShape_not_stuck_with_run_agreement
	        HDec left_state tleft HLeft HLeftAgree HLeftReady)
	      as [HLeftTerminal | [HLeftCanStep | HLeftCheck]].
	    + inversion HLeftTerminal; subst.
	      destruct
	        (WTStateRuntimeHeapShape_not_stuck_with_run_agreement
	          HDec right_state tright HRight HRightAgree HRightReady)
	        as [HRightTerminal | [HRightCanStep | HRightCheck]].
	      * inversion HRightTerminal; subst.
	        simpl in HHeap. subst.
	        right. left. apply pairpar_done_can_step.
      * right. left. apply pairpar_right_can_step. exact HRightCanStep.
      * right. right. right. exact HRightCheck.
    + right. left. apply pairpar_left_can_step. exact HLeftCanStep.
    + right. right. left. exact HLeftCheck.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_not_stuck :
  PairParCheckDecidable ->
  forall state tout stty,
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParRunHeapsAgree state ->
    PairParEvalHeadRegionsResolved state ->
    PairParNotStuck state.
Proof.
  intros HDec state tout stty HWT HAgree HReady.
  eapply (WTPairParStateRuntimeHeapShape_not_stuck HDec); eauto.
  eapply WTPairParStateRuntimeHeapShapeAt_forget.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_forget; eauto.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_steps_not_stuck :
  PairParCheckDecidable ->
  forall state tout stty trace state',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParRunHeapsAgree state ->
    PairParSteps state trace state' ->
    PairParEvalHeadRegionsResolved state' ->
    PairParNotStuck state'.
Proof.
  intros HDec state tout stty trace state' HWT HAgree HSteps HReady.
  destruct
    (WTPairParStateRuntimeHeapShapeAtStrong_steps_preservation
      state tout stty trace state' HWT HSteps)
    as (stty' & HWT' & _).
  eapply WTPairParStateRuntimeHeapShapeAtStrong_not_stuck; eauto.
  eapply pairpar_steps_preserve_heap_agreement; eauto.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_steps_eval_heads_resolved :
  forall state tout stty trace state',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParSteps state trace state' ->
    PairParEvalHeadRegionsResolved state'.
Proof.
  intros state tout stty trace state' HWT HSteps.
  destruct
    (WTPairParStateRuntimeHeapShapeAtStrong_steps_preservation
      state tout stty trace state' HWT HSteps)
    as (stty' & HWT' & _).
  eapply WTPairParStateRuntimeHeapShapeAtStrong_eval_heads_resolved; eauto.
Qed.

Definition PairParEvalHeadRegionsResolvedAfterSteps
    (state : PairParState) : Prop :=
  forall trace state',
    PairParSteps state trace state' ->
    PairParEvalHeadRegionsResolved state'.

Definition PairParNeverStuck (state : PairParState) : Prop :=
  forall trace state',
    PairParSteps state trace state' ->
    PairParNotStuck state'.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_never_stuck :
  PairParCheckDecidable ->
  forall state tout stty,
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParRunHeapsAgree state ->
    PairParEvalHeadRegionsResolvedAfterSteps state ->
    PairParNeverStuck state.
Proof.
  intros HDec state tout stty HWT HAgree HReady trace state' HSteps.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_steps_not_stuck; eauto.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_never_stuck_typed :
  PairParCheckDecidable ->
  forall state tout stty,
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParRunHeapsAgree state ->
    PairParNeverStuck state.
Proof.
  intros HDec state tout stty HWT HAgree trace state' HSteps.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_steps_not_stuck; eauto.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_steps_eval_heads_resolved; eauto.
Qed.

Lemma pairpar_checked_initial_eval_heads_resolved :
  forall heap env rho ef1 ea1 ef2 ea2 k,
    PairParEvalHeadRegionsResolved
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k.
  unfold pairpar_checked_initial, initial_state.
  simpl.
  split; exact I.
Qed.

Lemma pairpar_checked_initial_not_stuck :
  forall heap env rho ef1 ea1 ef2 ea2 k,
    PairParNotStuck
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k.
  right. left.
  apply pairpar_checked_initial_left_can_step.
Qed.

Theorem pairpar_checked_initial_never_stuck_typed :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    PairParNeverStuck
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k).
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_never_stuck_typed.
  - exact HDec.
  - eapply WTPairParStateRuntimeHeapShapeAtStrong_checked_initial; eauto.
  - apply pairpar_checked_initial_heaps_agree.
Qed.
