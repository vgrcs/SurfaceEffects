From stdpp Require Import gmap.
From Stdlib Require Import Program.Equality.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepExplicitStoreBase.
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

Definition IdleBranchRetyped (heap : Heap) (state : State) (t : Tau) : Prop :=
  WTStateRuntimeHeapShape state t ->
  WTStateRuntimeHeapShape (with_state_heap heap state) t.


Lemma WTStateRuntimeHeapShapeAt_idle_retyped :
  forall state tout stty heap' stty',
    WTStateRuntimeHeapShapeAt state tout stty ->
    TcHeap (heap', stty') ->
    RuntimeHeapShape heap' stty' ->
    StoreExtends stty stty' ->
    IdleBranchRetyped heap' state tout.
Proof.
  intros state tout stty heap' stty' HAt HTcHeap HHeapShape HExt _.
  eapply WTStateRuntimeHeapShapeAt_forget.
  eapply WTStateRuntimeHeapShapeAt_reheap_store_ext; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_idle_retyped_same_store :
  forall state tout stty heap',
    WTStateRuntimeHeapShapeAt state tout stty ->
    TcHeap (heap', stty) ->
    RuntimeHeapShape heap' stty ->
    IdleBranchRetyped heap' state tout.
Proof.
  intros state tout stty heap' HAt HTcHeap HHeapShape _.
  eapply WTStateRuntimeHeapShapeAt_forget.
  eapply WTStateRuntimeHeapShapeAt_reheap_same_store; eauto.
Qed.

Definition PairParDoneContinuationReadyAt
    (left right : State) (k : Kont) (tout : Tau) (stty : Sigma) : Prop :=
  forall heap v1 v2,
    left = StDone heap v1 ->
    right = StDone heap v2 ->
    WTStateRuntimeHeapShapeAt (StReturn heap (Pair (v1, v2)) k) tout stty.
