From stdpp Require Import gmap.
Require Import theories.BigStep.Typing.TypeSyntax.
Require Import theories.BigStep.Typing.TypingJudgments.
Require Export theories.BigStep.Runtime.Heap.

Inductive TcHeap : (Heap * Sigma) -> Prop := 
| TC_Heap : forall heap store,
    (forall k v,
        (find_H k heap = Some v ->
         exists t, find_ST k store = Some t)) ->
    (forall k t,
        (find_ST k store = Some t ->
         exists v, find_H k heap = Some v)) ->
    (forall k v t,
        (find_H k heap = Some v ->
         find_ST k store = Some t ->
         TcVal (store, v, t))) ->
    TcHeap (heap, store).

Lemma DisjointHeap_implies_DisjointStore:
  forall heap1 heap2 stty1 stty2,
    TcHeap(heap1, stty1) ->
    TcHeap(heap2, stty2) ->
    heap1 ##ₘ heap2 ->
    stty1 ##ₘ stty2.
Proof.
  intros.
  inversion H; subst. 
  inversion H0; subst.  
  apply map_disjoint_spec. intros.
  unfold find_ST in H5. unfold find_ST in H8.
  apply H5 in H2.
  apply H8 in H3.
  assert (H' :forall i x y, heap1 !! i = Some x → heap2 !! i = Some y → False).
  apply map_disjoint_spec. assumption.
  destruct H2. destruct H3.
  eapply H' in H2; eauto.
Qed.

Lemma TcHeap_none_implies_none:
  forall heap stty,
    TcHeap(heap, stty) ->
    (forall (k : SigmaKey),
        find_ST k stty = None -> find_H k heap = None).
Proof.
  intros heap stty HTcHeap k HStoreNone.
  destruct (find_H k heap) eqn:HHeapFind; auto.
  inversion HTcHeap as [? ? HHeapStore _ _]; subst.
  destruct (HHeapStore k v HHeapFind) as [t HStoreFind].
  rewrite HStoreNone in HStoreFind.
  discriminate.
Qed.
  
Lemma djt_heap_implies_djt_stty:
  forall heap heap1 heap2 stty stty1 stty2,
    TcHeap(heap, stty) ->
    TcHeap(heap1, stty1) ->
    TcHeap(heap2, stty2) ->
    (heap1 ∖ heap) ##ₘ (heap2 ∖ heap) ->
    (stty1 ∖ stty) ##ₘ (stty2 ∖ stty).
Proof.
  intros heap heap1 heap2 stty stty1 stty2 H1 H2 H3.
  inversion H1. inversion H2. inversion H3. subst.
  intro.
  apply map_disjoint_spec. intros.
  clear H6. clear H11. clear H16.
  unfold find_ST in H5. unfold find_ST in H10. unfold find_ST in H15.
  apply lookup_difference_Some in H0. destruct H0.
  apply lookup_difference_Some in H7. destruct H7. clear H8.
  apply H10 in H0.
  apply H15 in H7.
  assert (H' : forall i x y,
             (heap1 ∖ heap) !! i = Some x -> (heap2 ∖ heap) !! i = Some y -> False).
  apply map_disjoint_spec. assumption.
  destruct H0. destruct H7.
  assert (heap !! i = None). eapply TcHeap_none_implies_none; eauto.
  assert ((heap1 ∖ heap) !! i = Some x0) by (apply lookup_difference_Some; auto).
  assert ((heap2 ∖ heap) !! i = Some x1) by (apply lookup_difference_Some; auto).
  eapply H' in H11; eauto.
Qed.

Lemma djt_heap_implies_djt_stty_2:
  forall heap heap1 heap2 stty stty1 stty2,
    TcHeap(heap, stty) ->
    TcHeap(heap1, stty1) ->
    TcHeap(heap2, stty2) ->
    heap ∪ (heap1 ∖ heap) ##ₘ heap ∪ (heap2 ∖ heap) ->
    stty ∪ (stty1 ∖ stty) ##ₘ stty ∪ (stty2 ∖ stty).
Proof.
  intros heap heap1 heap2 stty stty1 stty2 H1 H2 H3.
  inversion H1. inversion H2. inversion H3. subst.
  intro.
  apply map_disjoint_spec. intros.
  clear H6. clear H11. clear H16.
  unfold find_ST in H5. unfold find_ST in H10. unfold find_ST in H15.
  apply lookup_union_Some_raw in H0.
  apply lookup_union_Some_raw in H7.
  assert (H' : forall i x y,
             (heap ∪ (heap1 ∖ heap)) !! i = Some x ->
             (heap ∪ (heap2 ∖ heap)) !! i = Some y -> False)
    by (apply map_disjoint_spec; assumption).
  destruct H0; destruct H7.
  - apply H5 in H0.
    apply H5 in H6.
    destruct H0. destruct H6. 
    assert ((heap ∪ (heap1 ∖ heap)) !! i = Some x0)
      by (apply lookup_union_Some_raw; left; assumption).
    assert ((heap ∪ (heap2 ∖ heap)) !! i = Some x1)
      by (apply lookup_union_Some_raw; left; assumption).    
    eapply H' in H7; eauto.
  - destruct H6.
    rewrite H0 in H6. inversion H6.
  - destruct H0.
    rewrite H0 in H6. inversion H6.
  - destruct H0. destruct H6.
    apply lookup_difference_Some in H7. destruct H7. 
    apply lookup_difference_Some in H8. destruct H8.
    clear H11. clear H6. clear H12.
    apply H10 in H7. apply H15 in H8.
    destruct H7. destruct H8.
    assert (heap !! i = None). eapply TcHeap_none_implies_none; eauto.
    assert ((heap ∪ (heap1 ∖ heap)) !! i = Some x0)
      by (apply lookup_union_Some_raw; right; split;
          [auto | apply lookup_difference_Some; auto]).
    assert ((heap ∪ (heap2 ∖ heap)) !! i = Some x1)
      by (apply lookup_union_Some_raw; right; split;
          [auto | apply lookup_difference_Some; auto]).
    eapply H' in H11; eauto.
Qed.
