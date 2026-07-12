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

Require Export theories.Runtime.SmallStepParallelTraceTyping.

Definition PairParTraceSafeAt
    (state : PairParState) (tout : Tau) (stty : Sigma) : Prop :=
  forall trace state',
    PairParSteps state trace state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' /\
      StoreExtends stty stty' /\
      PairParRunHeapsAgree state' /\
      PairParNotStuck state' /\
      TcPhi stty' (trace_as_phi trace).

Theorem WTPairParStateRuntimeHeapShapeAtStrong_trace_safe_typed :
  PairParCheckDecidable ->
  forall state tout stty,
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParRunHeapsAgree state ->
    PairParTraceSafeAt state tout stty.
Proof.
  intros HDec state tout stty HWT HAgree trace state' HSteps.
  destruct
    (WTPairParStateRuntimeHeapShapeAtStrong_steps_trace_typed
      state tout stty trace state' HWT HSteps)
    as (stty' & HWT' & HExt & HTcTrace).
  assert (HAgree' : PairParRunHeapsAgree state').
  {
    eapply pairpar_steps_preserve_heap_agreement; eauto.
  }
  pose proof
    (WTPairParStateRuntimeHeapShapeAtStrong_never_stuck_typed
      HDec state tout stty HWT HAgree)
    as HNeverStuck.
  exists stty'. split; [exact HWT' |].
  split; [exact HExt |].
  split; [exact HAgree' |].
  split; [exact (HNeverStuck trace state' HSteps) | exact HTcTrace].
Qed.

Theorem PairParTraceSafeAt_terminal_value :
  forall state tout stty trace heap' v,
    PairParTraceSafeAt state tout stty ->
    PairParSteps state trace (PPS_State (StDone heap' v)) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, tout) /\
      RuntimeValShape stty' tout v /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros state tout stty trace heap' v HSafe HSteps.
  destruct (HSafe trace (PPS_State (StDone heap' v)) HSteps)
    as (stty' & HWT' & HExt & _ & _ & HTcTrace).
  destruct
    (WTPairParStateRuntimeHeapShapeAtStrong_done_value
      heap' v tout stty' HWT')
    as (HTcHeap' & HHeapShape' & HTcVal' & HValShape').
  exists stty'. split; [exact HExt |].
  split; [exact HTcHeap' |].
  split; [exact HHeapShape' |].
  split; [exact HTcVal' |].
  split; [exact HValShape' | exact HTcTrace].
Qed.

Theorem PairParTraceSafeAt_kdone_terminal_pair :
  forall state stty rho ty1 ty2 trace heap' v,
    PairParTraceSafeAt state (subst_rho rho (Ty_Pair ty1 ty2)) stty ->
    PairParSteps state trace (PPS_State (StDone heap' v)) ->
    exists stty' v1 v2,
      v = Pair (v1, v2) /\
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v1, subst_rho rho ty1) /\
      RuntimeValShape stty' (subst_rho rho ty1) v1 /\
      TcVal (stty', v2, subst_rho rho ty2) /\
      RuntimeValShape stty' (subst_rho rho ty2) v2 /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros state stty rho ty1 ty2 trace heap' v HSafe HSteps.
  destruct
    (PairParTraceSafeAt_terminal_value
      state (subst_rho rho (Ty_Pair ty1 ty2)) stty trace heap' v
      HSafe HSteps)
    as (stty' & HExt & HTcHeap' & HHeapShape' & HTcVal' & HValShape' &
        HTcTrace).
  rewrite subst_rho_pair in HTcVal'.
  rewrite subst_rho_pair in HValShape'.
  destruct
    (RuntimeValShape_pair_inv
      stty' (subst_rho rho ty1) (subst_rho rho ty2) v HValShape')
    as (v1 & v2 & Hv & HValShape1 & HValShape2).
  subst v.
  destruct
    (TcVal_pair_value_inv
      stty' (subst_rho rho ty1) (subst_rho rho ty2) v1 v2 HTcVal')
    as (HTcVal1 & HTcVal2).
  exists stty', v1, v2.
  split; [reflexivity |].
  split; [exact HExt |].
  split; [exact HTcHeap' |].
  split; [exact HHeapShape' |].
  split; [exact HTcVal1 |].
  split; [exact HValShape1 |].
  split; [exact HTcVal2 |].
  split; [exact HValShape2 | exact HTcTrace].
Qed.

