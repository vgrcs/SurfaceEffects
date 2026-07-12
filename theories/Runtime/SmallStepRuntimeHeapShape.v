From stdpp Require Import gmap.
From Stdlib Require Import Sets.Ensembles.

Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepTyping.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepReturnProgress.
Require Import theories.Runtime.SmallStepEvalProgress.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.MapFacts.
Require Import theories.Meta.RegionSubstitutionFacts.
Require Import theories.Meta.HeapFacts.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.TypingWeakeningFacts.
Require Import theories.Meta.TypeFacts.
Require Import theories.Meta.LocallyNameless.


Definition RuntimeHeapShape (heap : Heap) (stty : Sigma) : Prop :=
  forall k v t,
    find_H k heap = Some v ->
    find_ST k stty = Some t ->
    RuntimeValShape stty t v.

Lemma RuntimeHeapShape_update_existing :
  forall heap stty k v t,
    RuntimeHeapShape heap stty ->
    RuntimeValShape stty t v ->
    find_ST k stty = Some t ->
    RuntimeHeapShape (update_H (k, v) heap) stty.
Proof.
  intros heap stty k v t HHeapShape HShape HFindST
    k0 v0 t0 HFindH0 HFindST0.
  unfold find_H, update_H in HFindH0; simpl in HFindH0.
  apply lookup_insert_Some in HFindH0.
  destruct HFindH0 as [[HKey HVal] | [HNe HFindHOld]].
  - inversion HKey; subst k0.
    inversion HVal; subst v0.
    pose proof (PairType_unique_type stty k t0 t HFindST0 HFindST) as HTy.
    subst. assumption.
  - eapply HHeapShape; eauto.
Qed.

Lemma RuntimeHeapShape_update_fresh :
  forall heap stty k v t,
    RuntimeHeapShape heap stty ->
    RuntimeValShape stty t v ->
    find_ST k stty = None ->
    RuntimeHeapShape (update_H (k, v) heap) (update_ST k t stty).
Proof.
  intros heap stty k v t HHeapShape HShape HFresh
    k0 v0 t0 HFindH0 HFindST0.
  assert (HExt : forall k' t',
    find_ST k' stty = Some t' ->
    find_ST k' (update_ST k t stty) = Some t').
  {
    intros k' t' HFindST.
    unfold find_ST, update_ST in *.
    destruct (decide (k' = k)); subst.
    - rewrite HFresh in HFindST. discriminate.
    - eapply G_diff_keys_2; eauto.
  }
  unfold find_H, update_H in HFindH0; simpl in HFindH0.
  unfold find_ST, update_ST in HFindST0.
  apply lookup_insert_Some in HFindH0.
  apply lookup_insert_Some in HFindST0.
  destruct HFindH0 as [[HKeyH HVal] | [HNeH HFindHOld]];
  destruct HFindST0 as [[HKeyST HTy] | [HNeST HFindSTOld]]; subst.
  - eapply RuntimeValShape_store_ext; eauto.
  - contradiction.
  - contradiction.
  - eapply RuntimeValShape_store_ext; eauto.
Qed.

