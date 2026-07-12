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
Require Import theories.Runtime.SmallStepParallelProgress.
Require Import theories.Runtime.SmallStepParallelSafety.
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

Lemma WTPairParStateRuntimeHeapShapeAtStrong_step_label_typed :
  forall state tout stty label state' stty',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParStep state label state' ->
    WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' ->
    TcPhi stty' (trace_as_phi (label_trace label)).
Proof.
  intros state tout stty label state' stty' HWT HStep HWT'.
  dependent destruction HStep.
  - dependent destruction HWT.
    dependent destruction HWT'.
    match goal with
    | HState : WTStateRuntimeHeapShapeAt ?inner ?tout stty,
      HInnerStep : Step _ _ _,
      HStateOut : WTStateRuntimeHeapShapeAt _ _ _ |- _ =>
        eapply WTStateRuntimeHeapShapeAt_step_label_typed;
          [exact HState | exact HInnerStep | exact HStateOut]
    end.
  - dependent destruction HWT.
    dependent destruction HWT'.
    match goal with
    | HLeft : WTStateRuntimeHeapShapeAt ?left ?tleft stty,
      HLeftOut : WTStateRuntimeHeapShapeAt _ _ _ |- _ =>
        match goal with
        | HLeftStep : Step _ _ _ |- _ =>
            eapply WTStateRuntimeHeapShapeAt_step_label_typed;
              [exact HLeft | exact HLeftStep | exact HLeftOut]
        end
    end.
  - dependent destruction HWT.
    dependent destruction HWT'.
    match goal with
    | HRight : WTStateRuntimeHeapShapeAt ?right ?tright stty,
      HRightOut : WTStateRuntimeHeapShapeAt _ _ _ |- _ =>
        match goal with
        | HRightStep : Step _ _ _ |- _ =>
            eapply WTStateRuntimeHeapShapeAt_step_label_typed;
              [exact HRight | exact HRightStep | exact HRightOut]
        end
    end.
  - simpl. apply TcPhi_nil.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_steps_trace_typed :
  forall state tout stty trace state',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParSteps state trace state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' /\
      StoreExtends stty stty' /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros state tout stty trace state' HWT HSteps.
  revert tout stty HWT.
  induction HSteps as [state | state label state1 trace state2 HStep HSteps IH];
    intros tout stty HWT.
  - exists stty.
    split; [exact HWT |].
    split; [apply StoreExtends_refl | apply TcPhi_nil].
  - destruct
      (WTPairParStateRuntimeHeapShapeAtStrong_step_preservation
        state tout stty label state1 HWT HStep)
      as (stty1 & HWT1 & HExt1).
    destruct (IH tout stty1 HWT1) as (stty2 & HWT2 & HExt2 & HTcTrace).
    pose proof
      (WTPairParStateRuntimeHeapShapeAtStrong_step_label_typed
        state tout stty label state1 stty1 HWT HStep HWT1)
      as HTcLabel1.
    pose proof
      (TcPhi_weaken
        stty1 stty2 (trace_as_phi (label_trace label))
        HExt2 HTcLabel1)
      as HTcLabel2.
    exists stty2.
    split; [exact HWT2 |].
    split; [eapply StoreExtends_trans; eauto |].
    apply TcPhi_trace_as_phi_app; assumption.
Qed.

