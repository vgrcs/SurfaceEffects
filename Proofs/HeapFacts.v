From stdpp Require Import gmap.
Require Import Coq.Program.Equality.
Require Import Definitions.GHeap.
Require Import Definitions.GTypes.
Require Import Definitions.Values.
Require Import Definitions.Semantics.
Require Import Definitions.DynamicActions.
Require Import Proofs.TypeFacts.
Require Import Definitions.Axioms.

Import Expressions.
Import ComputedActions.

Lemma TcHeapEmpty:
  forall (heap : gmap HeapKey HeapVal) (stty : gmap SigmaKey Tau),
    heap = ∅ ->
    stty = ∅ ->
    TcHeap (heap, stty).
Proof.
  intros heap stty H1 H2.
  econstructor; unfold find_H, find_ST in *; subst.
  - intros.
    assert(H3: ¬is_Some ((∅ : Heap) !! k)). apply lookup_empty_is_Some.
    contradict H3. unfold is_Some. subst. exists v. assumption.
  - intros. inversion H.
  - intros. inversion H.
Qed.

  
Lemma H_same_key_1: 
  forall l v (heap : gmap HeapKey HeapVal),
    (<[ l:=v ]> heap) !! l = Some v.
Proof.
  intros.
  rewrite lookup_insert_Some.
  left. split; reflexivity.
Qed. 



Lemma H_same_key_2:
  forall l1 l2 v (heap : gmap HeapKey HeapVal),
    l1 = l2 -> 
    heap !! l1 = Some v ->
    (<[ l2:=v ]> heap) !! l1 = Some v.
Proof.
  intros.
  rewrite H.
  rewrite  lookup_insert_Some.
  left. split; reflexivity.
Qed.


Lemma H_diff_keys_1:
  forall a b v v' (heap : gmap HeapKey HeapVal),   
    a <> b ->
    (<[ b:=v ]> heap) !! a = Some v' -> 
    heap !! a = Some v'.
Proof.
  intros a b v v' e Hneq Hfind.
  rewrite lookup_insert_Some in Hfind.
  destruct Hfind as [[Ha Hb] | [Hc Hd]].
  - contradict Hneq. auto.
  - assumption.
Qed.

Lemma H_diff_keys_2:
  forall a b v v' (heap : gmap HeapKey HeapVal),   
    b <> a ->
    heap !! a = Some v' ->
    (<[ b:=v ]> heap) !! a = Some v'.
Proof.
  intros a b v v' e Hneq Hfind.
  rewrite lookup_insert_Some.
  right. split; [assumption | assumption].
Qed.


Lemma H_update_same_value: 
  forall (heap : gmap HeapKey HeapVal) l v v',
    (<[ l:=v ]> heap) !! l= Some v' -> v = v'.
Proof.
  intros heap l v v' Hfind. 
  rewrite lookup_insert_Some in Hfind.
  destruct Hfind as [[Ha Hb] | [Hc Hd]].
  - assumption.
  - contradict Hc. reflexivity.
Qed.
  

Lemma H_Same_Domain:
  forall stty heap, 
    TcHeap (heap, stty) ->
    (forall k v t,
       find_ST k stty = None -> 
       (forall (k0 : HeapKey) (v0 : Val),
          find_H k0 (update_H (k, v) heap) = Some v0 ->
          exists t0 : Tau, find_ST k0 (update_ST k t stty) = Some t0) /\
       (forall (k0 : SigmaKey) (t0 : Tau),
          find_ST k0 (update_ST k t stty) = Some t0 ->
          exists v0 : Val, find_H k0 (update_H (k, v) heap) = Some v0)) /\
    (forall k v t,
       find_ST k stty = Some t ->
       (forall (k0 : HeapKey) (v0 : Val),
          find_H k0 (update_H (k, v) heap) = Some v0 ->
          exists t0 : Tau, find_ST k0 stty = Some t0) /\
       (forall (k0 : SigmaKey) (t0 : Tau),
          find_ST k0 stty = Some t0 ->
          exists v0 : Val, find_H k0 (update_H (k, v) heap) = Some v0)).
Proof.
  intros stty heap Hhp;
  inversion_clear Hhp as [? ? TcHeap_STFind TcHeap_HFind TcHeap_tcVal]; split.
  - intros k v t Hnone; split.
    + intros k0 v0 Hfind'.
      destruct k0 as [r0 l0]; destruct k as [r l];
        destruct (eq_nat_dec l l0); destruct (eq_nat_dec r r0); subst;
        try (apply H_diff_keys_1 in Hfind';
             [ destruct (TcHeap_STFind (r0, l0) v0 Hfind') as [t0 STfind'];
               exists t0; apply ST_diff_key_2;
               [contradict n; inversion n; reflexivity | assumption] |
               contradict n; inversion n; reflexivity ]).
      * exists t. apply ST_same_key_1.
    + intros k0 t0 STfind'; 
      destruct k0 as [r0 l0];
        destruct k as [r l];
        destruct (eq_nat_dec l l0);
        destruct (eq_nat_dec r r0); subst;
        try ( apply ST_diff_keys_1 in STfind';
            [ destruct (TcHeap_HFind (r0, l0) t0 STfind') as [v0 Hfind'];
              exists v0;
              apply H_diff_keys_2 | ]; simpl; intuition; apply n; now inversion H).
      exists v. unfold find_H, update_H. apply H_same_key_1.
  - intros k v t STfind; split.
    + intros k0 v0 Hfind'.
      destruct k0 as [r0 l0];
        destruct k as [r l];
        destruct (eq_nat_dec l l0);
        destruct (eq_nat_dec r r0); subst;
        try (apply H_diff_keys_1 in Hfind';
           [destruct (TcHeap_STFind (r0, l0) v0 Hfind') as [t0 STfind']; now exists t0 |
            simpl; intuition; apply n; now inversion H]).        
      now exists t. 
    + intros k0 t0 STfind'.
      destruct k0 as [r0 l0];
        destruct k as [r l];
        destruct (eq_nat_dec l l0);
        destruct (eq_nat_dec r r0); subst;
        try (destruct (TcHeap_HFind (r0, l0) t0 STfind') as [v0 Hfind'];
             exists v0; apply H_diff_keys_2;
             simpl; intuition; apply n; now inversion H).                             
      exists v; apply H_same_key_1.
Qed.


Lemma H_update_heap_fresh:
  forall stty heap,
    TcHeap (heap, stty) ->
    (forall k v t,
       find_ST k stty = None ->
       TcVal (stty, v, t) ->
       TcHeap (update_H (k, v) heap, update_ST k t stty)).
Proof. 
  intros stty heap Hhp l v t Htc STfind.
  inversion Hhp as [? ? TcHeap_STFind TcHeap_HFind TcHeap_tcVal]; subst; constructor.
  - apply H_Same_Domain in Hhp. destruct Hhp as [Hnew ?]. edestruct Hnew; eauto.
  - apply H_Same_Domain in Hhp. destruct Hhp as [Hnew ?]. edestruct Hnew; eauto.
  - intros k v0 t0 Hfind' STfind'. destruct l as [r l]; destruct k as [r0 l0]. 
    destruct (eq_nat_dec l l0);  destruct (eq_nat_dec r r0); subst;
    try (eapply ST_diff_keys_1 in STfind'; eapply H_diff_keys_1 in Hfind'; eauto;
         try (simpl; intuition; apply n; congruence); 
         apply ext_stores__val with (stty:=stty);
         [intros k1 t1 STfind''; destruct k1 as [r1 l1]; 
           destruct (eq_nat_dec l0 l1);  destruct (eq_nat_dec r0 r1); subst;
           try (apply ST_diff_key_2; [simpl; intuition; apply n; congruence | assumption]) |
          now apply TcHeap_tcVal with (k := (r0, l0)) ] ).
    apply ST_update_same_type in STfind'; 
    apply H_update_same_value in Hfind'; simpl in *; subst.
    apply ext_stores__val with (stty:=stty); auto.
    intros k1 t1 STfind'. destruct k1 as [r1 l1].
    destruct (eq_nat_dec l0 l1);  destruct (eq_nat_dec r0 r1); subst;
    try (apply ST_diff_key_2; [ simpl; intuition; apply n; now inversion H | assumption] ).
    rewrite STfind' in Htc. discriminate.
Qed.



Lemma H_update_heap_exists:
  forall stty heap,
    TcHeap (heap, stty) ->
    (forall k v t,
       find_ST k stty = Some t ->
       TcVal (stty, v, t) ->
       TcHeap (update_H (k, v) heap, stty)).
Proof. 
  intros stty heap Hhp l v t Htc STfind.
  inversion Hhp as [? ? TcHeap_STFind TcHeap_HFind TcHeap_tcVal]; subst; constructor.
  - apply H_Same_Domain in Hhp. destruct Hhp as [? Hupdate]. edestruct Hupdate; eauto.
  - apply H_Same_Domain in Hhp. destruct Hhp as [? Hupdate]. edestruct Hupdate; eauto.
  - intros k0 v0 t0 Hfind' STfind'. destruct l as [r l]; destruct k0 as [r0 l0]. 
    destruct (eq_nat_dec l l0);  destruct (eq_nat_dec r r0); subst;
    try (eapply H_diff_keys_1 in Hfind'; eauto; simpl; intuition; apply n; congruence).
    apply H_update_same_value in Hfind'; subst.
    rewrite STfind' in Htc. now inversion Htc. 
Qed.


Lemma EmptyTracePreservesHeap_1: 
  forall h r env e same_h v' acts,
    (h, r, env, e) ⇓ (same_h, v', acts) ->
    acts = Phi_Nil ->
    h ≡@{Heap} same_h.
Proof.
  intros h r env e same_h v' acts H Hnil.
  dependent induction H; auto; inversion Hnil.  
  - eapply IHBigStep. reflexivity. auto. reflexivity.
  - eapply IHBigStep; [reflexivity | auto | reflexivity]. 
Qed.

Lemma Equal_heap_equal:
  forall (heap1 heap2 : Heap),
    heap1 = heap2 -> heap1 ≡@{Heap} heap2.
Proof.
  intros heap1 heap2 H. subst. auto.
Qed.

Lemma EqualHeaps:
 forall heap_a heap_b store,
   TcHeap (heap_a, store) ->
   heap_a ≡@{Heap} heap_b ->
   TcHeap (heap_b, store).
Proof.
  intros heap_a heap_b store HTcHeap HEqual.
  unfold equiv, heap_equiv in HEqual; subst.
  assumption.
Qed.


Lemma EmptyTracePreservesHeap_2 : 
  forall h r env e same_h v acts,
    (h, r, env, e) ⇓ (h, v, acts) ->
    h ≡@{Heap} same_h ->
    (same_h, r, env, e) ⇓ (same_h, v, acts).
Proof.
  intros h r env e same_h v' acts Dyn H.
  unfold equiv, heap_equiv in H. now subst.
Qed.

Lemma EmptyTracePreservesHeap_3 : 
  forall h r env e same_h v acts,
    (same_h, r, env, e) ⇓ (same_h, v, acts) ->
    (h, r, env, e) ⇓ (same_h, v, acts) ->
    acts = Phi_Nil ->
    (h, r, env, e) ⇓ (h, v, acts).
Proof.
  intros h r env e same_h v' acts Dyn Hheap Hnil.
  apply EmptyTracePreservesHeap_1 in Hheap; unfold equiv, heap_equiv in Hheap;
  now subst.
Qed.

Lemma EmptyTracePreservesHeap_4 : 
  forall h r env e same_h v,
    (h, r, env, e) ⇓ (same_h, v, Phi_Nil) ->
    h ≡@{Heap} same_h.
Proof.
   intros h r env e same_h v' Dyn1.
   dependent induction Dyn1; auto;  unfold equiv, heap_equiv.
   eapply IHDyn1.
   - reflexivity.
   - econstructor.
   - eapply IHDyn1.
     + reflexivity.
     + econstructor. 
Qed.


Lemma EmptyTracePreservesHeap_5 : 
  forall h r env e  v,
    (h, r, env, e) ⇓ (h, v, Phi_Nil) ->
    exists same_h,  (same_h, r, env, e) ⇓ (h, v, Phi_Nil).
Proof.
  intros h r env e v H.
  dependent induction H; exists h; econstructor; auto. 
Qed.

Lemma H_same_key_add_twice_1 :
  forall r l r0 l0 v v0 (heap : gmap HeapKey HeapVal), 
    (<[ (r0, l0):=v0 ]> (<[ (r, l):=v ]> heap)) !!  (r0, l0) =
    (<[ (r0, l0):=v0 ]> heap) !! (r0, l0).
Proof.
  intros. rewrite H_same_key_1. rewrite H_same_key_1. reflexivity.
Qed. 

Lemma H_same_key_add_twice_2 :
  forall k k0 v v0 (heap : gmap HeapKey HeapVal),
    k <> k0 ->
    ( <[ k:=v ]> (<[ k0:=v0 ]> heap)) !! k0 = ( <[k0:=v0]> heap) !! k0.
Proof.
  intros. rewrite H_same_key_1. apply H_diff_keys_2; [assumption | apply H_same_key_1]. 
Qed.

Lemma H_same_key_add_twice_3 :
  forall k k0 v v0 (heap : gmap HeapKey HeapVal),
    (<[k0:=v0]> (<[k:=v]> heap)) !! k0 = (<[k0:=v0]> heap) !! k0.
Proof.
  intros. rewrite H_same_key_1. symmetry. apply H_same_key_1. 
Qed. 

Lemma H_diff_key_add_twice_1 :
  forall k0 k (heap : gmap HeapKey HeapVal) (v v0 e: Val), 
    (<[k0:=v0]> heap) !! k0 = Some e ->
    (<[k0:=v0]> (<[k:=v]> heap)) !! k0 = Some e.
Proof.
  intros k0 k heap v v0 e H.
  rewrite H_same_key_add_twice_3. assumption.
Qed.

Lemma H_diff_key_add_twice_2 :
  forall k0 k (heap : gmap HeapKey HeapVal) (v v0 e: Val),
    k <> k0 ->
    (<[ k:= v]> heap) !! k = Some e ->
    (<[ k:=v]> (<[k0:=v0]> heap)) !! k = Some e.
Proof.
  intros k0 k heap v v0 e H. intro. 
  rewrite H_same_key_add_twice_3. auto. 
Qed.

Lemma H_diff_key_add_comm_1:
  forall k k1 k0 (heap : gmap HeapKey HeapVal) e v v0,
    k1 <> k ->
    k <> k0 ->
    (<[ k0:=v0]> (<[k1:=v]> heap)) !! k = Some e ->
    (<[k1:=v]> heap) !! k = Some e. 
Proof.
  intros  k k1 k0 heap e v v0 H1 H2 H3.
  apply  H_diff_keys_1 in H3; assumption.
Qed.

Lemma H_diff_key_add_comm_2:
  forall k k1 k0 (heap : gmap HeapKey HeapVal) e v v0,
    k1 <> k ->
    k <> k0 ->
    (<[ k1:=v]>  heap) !! k = Some e ->
    (<[ k1:=v]> (<[k0:=v0]> heap)) !! k = Some e. 
Proof.
  intros  k k1 k0 heap e v v0 H1 H2 H3.
  apply  H_diff_keys_1 in H3.
  - apply  H_diff_keys_2.
   + assumption.
   + apply  H_diff_keys_2.
     * symmetry; assumption.
     * assumption.
  - symmetry; assumption.
Qed.


Lemma H_diff_keys_same_outer_k_2 :
  forall r r0 r1 l l0 l1 v v0  (heap : gmap HeapKey HeapVal) e, 
    (r0, l0) <> (r, l) -> 
    ( <[(r, l):=v]> (<[(r0, l0):=v0]> heap)) !! (r1, l1) = Some e ->
    (update_H (r0, l0, v0) (update_H (r, l, v) heap)) !! (r1, l1) = Some e.
Proof.
  intros  r r0 r1 l l0 l1 v v0 heap e H1 H2.
  destruct (keys_eq_dec (r1, l1) (r0, l0)) as [K1 | K2];
    destruct (keys_eq_dec (r1, l1) (r, l)) as [K3 | K4]; subst;
    unfold keys_eq, Nat.eq in *; simpl in *.
  - destruct K1 as [Ha Hb]; destruct K3 as [Hc Hd]; subst.
    apply  H_diff_key_add_twice_2; auto.
    apply  H_diff_keys_1 in H2; auto.   
  - destruct K1 as [Ha Hb]. 
    rewrite Ha in *.  rewrite Hb in *.
    apply  H_diff_keys_1 in H2; auto. apply H_diff_key_add_twice_2; auto.
  - destruct K3 as [Ha Hb]. 
    rewrite Ha in *.  rewrite Hb in *.
    apply  H_diff_keys_2; auto.
    rewrite  H_same_key_add_twice_3 in H2; auto.
  - apply  H_diff_keys_2; simpl.
    + intuition.  apply H0; subst; inversion H; subst; reflexivity.
    + apply  H_diff_keys_2; auto; simpl in *.
      * intuition.  apply H3; subst; inversion H; subst; reflexivity.      
      * apply  H_diff_keys_1 in H2. apply  H_diff_keys_1 in H2; auto.
        { intuition.  apply H0; subst; inversion H; subst; reflexivity. }
        { intuition. apply H3; subst; inversion H; subst; reflexivity.  }
Qed.


Lemma H_monotonic_updates:
  forall phi phi' (heap heap' : gmap HeapKey HeapVal),
     (phi, heap) ===> (phi', heap') ->
     forall r l,
       find_H (r, l) heap ≠ None ->
       find_H (r, l) heap' ≠ None.
Proof.
  intros phi phi' heap heap' H.  
  dependent induction H; intros; unfold find_H, update_H in *; simpl in *.
  - intro. apply H.
    apply lookup_insert_None in H0. destruct H0.
    assumption.
  - intro. apply H0. assumption.
  - intro. apply H0.
    apply lookup_insert_None in H1. destruct H1.
    assumption.
  - apply IHPhi_Heap_Step with (phi:=phi1) (heap:=heap) (phi':=phi1').
    + reflexivity.
    + reflexivity.
    + assumption.
  - apply IHPhi_Heap_Step with (phi:=phi2) (heap:=heap) (phi':=phi2'). 
    + reflexivity.
    + reflexivity.
    + assumption.
  - assumption.
  - apply IHPhi_Heap_Step with (phi:=phi1) (heap:=heap) (phi':=phi1').
    + reflexivity.
    + reflexivity.
    + assumption.
  - apply IHPhi_Heap_Step with (phi:=phi2) (heap:=heap) (phi':=phi2'). 
    + reflexivity.
    + reflexivity.
    + assumption.
 - assumption.
Qed.

