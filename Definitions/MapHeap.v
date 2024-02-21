From stdpp Require Import gmap.
Require Import Definitions.GHeap.

Lemma H_same_key_1: 
  forall l v (h : Heap), 
    lookup (M:=gmap HeapKey HeapVal) l (<[ l:=v ]> h) = Some v.
Proof.
  intros.
  rewrite lookup_insert_Some.
  left. split; reflexivity.
Qed. 

Lemma H_same_key_2:
  forall l1 l2 v h,
    l1 = l2 -> 
    lookup (M:=gmap HeapKey HeapVal) l1 h = Some v ->
    lookup (M:=gmap HeapKey HeapVal) l1 (<[ l2:=v ]> h) = Some v.
Proof.
  intros.
  rewrite H.
  rewrite  lookup_insert_Some.
  left. split; reflexivity.
Qed.


