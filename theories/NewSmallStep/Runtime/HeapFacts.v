From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.PeanoNat.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.Machine.

Import ListNotations.

Definition NHeapKeysBounded (heap : Heap) : Prop :=
  forall r l v,
    In (r, l, v) heap ->
    l < length heap.

Definition NHeapLookupsBounded (heap : Heap) : Prop :=
  forall r l v,
    heap_lookup r l heap = Some v ->
    l < length heap.

Lemma heap_lookup_in :
  forall heap r l v,
    heap_lookup r l heap = Some v ->
    In (r, l, v) heap.
Proof.
  induction heap as [| [[r0 l0] v0] heap IH];
    intros r l v HLookup; simpl in *.
  - inversion HLookup.
  - destruct (Nat.eqb r r0 && Nat.eqb l l0) eqn:HEq.
    + apply andb_true_iff in HEq.
      destruct HEq as [HR HL].
      apply Nat.eqb_eq in HR.
      apply Nat.eqb_eq in HL.
      inversion HLookup; subst.
      left. subst. reflexivity.
    + right. eapply IH. exact HLookup.
Qed.

Lemma heap_in_lookup_key_exists :
  forall heap r l v,
    In (r, l, v) heap ->
    exists v',
      heap_lookup r l heap = Some v'.
Proof.
  induction heap as [| [[r0 l0] v0] heap IH];
    intros r l v HIn; simpl in *.
  - contradiction.
  - destruct HIn as [HHead | HTail].
    + inversion HHead; subst.
      rewrite Nat.eqb_refl, Nat.eqb_refl.
      eexists. reflexivity.
    + destruct (Nat.eqb r r0 && Nat.eqb l l0) eqn:HEq.
      * eexists. reflexivity.
      * eapply IH; eauto.
Qed.

Lemma NHeapKeysBounded_to_lookups_bounded :
  forall heap,
    NHeapKeysBounded heap ->
    NHeapLookupsBounded heap.
Proof.
  intros heap HBounded r l v HLookup.
  eapply HBounded.
  eapply heap_lookup_in; eauto.
Qed.

Lemma heap_bounded_lookup_lt :
  forall heap r l v,
    NHeapKeysBounded heap ->
    heap_lookup r l heap = Some v ->
    l < length heap.
Proof.
  intros heap r l v HBounded HLookup.
  eapply HBounded.
  eapply heap_lookup_in.
  exact HLookup.
Qed.

Lemma heap_bounded_fresh_lookup_none :
  forall heap r,
    NHeapKeysBounded heap ->
    heap_lookup r (length heap) heap = None.
Proof.
  intros heap r HBounded.
  destruct (heap_lookup r (length heap) heap) as [v |] eqn:HLookup;
    [| reflexivity].
  pose proof
    (heap_bounded_lookup_lt heap r (length heap) v HBounded HLookup)
    as HLen.
  lia.
Qed.

Lemma heap_alloc_result :
  forall heap r v l heap',
    heap_alloc r v heap = (l, heap') ->
    l = length heap /\ heap' = (r, length heap, v) :: heap.
Proof.
  intros heap r v l heap' HAlloc.
  unfold heap_alloc in HAlloc.
  inversion HAlloc.
  split; reflexivity.
Qed.

Lemma heap_lookup_alloc_same :
  forall heap r v l heap',
    heap_alloc r v heap = (l, heap') ->
    heap_lookup r l heap' = Some v.
Proof.
  intros heap r v l heap' HAlloc.
  destruct (heap_alloc_result heap r v l heap' HAlloc) as [-> ->].
  simpl.
  rewrite Nat.eqb_refl, Nat.eqb_refl.
  reflexivity.
Qed.

Lemma heap_lookup_alloc_old :
  forall heap r_alloc v_alloc l_alloc heap' r l v,
    NHeapKeysBounded heap ->
    heap_alloc r_alloc v_alloc heap = (l_alloc, heap') ->
    heap_lookup r l heap = Some v ->
    heap_lookup r l heap' = Some v.
Proof.
  intros heap r_alloc v_alloc l_alloc heap' r l v
    HBounded HAlloc HLookup.
  destruct (heap_alloc_result heap r_alloc v_alloc l_alloc heap' HAlloc)
    as [-> ->].
  simpl.
  destruct (Nat.eqb r r_alloc && Nat.eqb l (length heap)) eqn:HEq;
    [| exact HLookup].
  apply andb_true_iff in HEq.
  destruct HEq as [_ HL].
  apply Nat.eqb_eq in HL.
  subst l.
  pose proof
    (heap_bounded_lookup_lt heap r (length heap) v HBounded HLookup)
    as HLen.
  lia.
Qed.

Lemma heap_update_lookup_same :
  forall heap r l v,
    heap_lookup r l heap <> None ->
    heap_lookup r l (heap_update r l v heap) = Some v.
Proof.
  induction heap as [| [[r0 l0] v0] heap IH];
    intros r l v HSome; simpl in *.
  - contradiction HSome. reflexivity.
  - destruct (Nat.eqb r r0 && Nat.eqb l l0) eqn:HEq.
    + simpl. rewrite HEq. reflexivity.
    + simpl. rewrite HEq.
      apply IH.
      exact HSome.
Qed.

Lemma heap_update_lookup_other :
  forall heap r l v r' l',
    r <> r' \/ l <> l' ->
    heap_lookup r' l' (heap_update r l v heap) =
    heap_lookup r' l' heap.
Proof.
  induction heap as [| [[r0 l0] v0] heap IH];
    intros r l v r' l' HNeq; simpl.
  - reflexivity.
  - destruct (Nat.eqb r r0 && Nat.eqb l l0) eqn:HUpd.
    + simpl.
      destruct (Nat.eqb r' r0 && Nat.eqb l' l0) eqn:HLookup;
        [| reflexivity].
      apply andb_true_iff in HUpd.
      apply andb_true_iff in HLookup.
      destruct HUpd as [HR HL].
      destruct HLookup as [HR' HL'].
      apply Nat.eqb_eq in HR.
      apply Nat.eqb_eq in HL.
      apply Nat.eqb_eq in HR'.
      apply Nat.eqb_eq in HL'.
      subst.
      destruct HNeq as [HNeq | HNeq]; contradiction.
    + simpl. destruct (Nat.eqb r' r0 && Nat.eqb l' l0); auto.
Qed.

Lemma heap_update_length :
  forall heap r l v,
    length (heap_update r l v heap) = length heap.
Proof.
  induction heap as [| [[r0 l0] v0] heap IH];
    intros r l v; simpl.
  - reflexivity.
  - destruct (Nat.eqb r r0 && Nat.eqb l l0); simpl; auto.
Qed.

Lemma heap_update_in_key :
  forall heap r l v r' l' v',
    In (r', l', v') (heap_update r l v heap) ->
    exists old,
      In (r', l', old) heap.
Proof.
  induction heap as [| [[r0 l0] v0] heap IH];
    intros r l v r' l' v' HIn; simpl in *.
  - contradiction.
  - destruct (Nat.eqb r r0 && Nat.eqb l l0) eqn:HEq;
      simpl in HIn;
      destruct HIn as [HIn | HIn].
    + injection HIn as Hr Hl Hv.
      subst r' l' v'.
      exists v0. left. reflexivity.
    + exists v'. right. exact HIn.
    + injection HIn as Hr Hl Hv.
      subst r' l' v'.
      exists v0. left. reflexivity.
    + destruct (IH r l v r' l' v' HIn) as (old & HOld).
      exists old. right. exact HOld.
Qed.

Lemma heap_update_preserves_bounded :
  forall heap r l v,
    NHeapKeysBounded heap ->
    NHeapKeysBounded (heap_update r l v heap).
Proof.
  intros heap r l v HBounded r' l' v' HIn.
  destruct
    (heap_update_in_key heap r l v r' l' v' HIn)
    as (old & HOld).
  rewrite heap_update_length.
  eapply HBounded.
  exact HOld.
Qed.

Lemma heap_alloc_preserves_bounded :
  forall heap r v l heap',
    NHeapKeysBounded heap ->
    heap_alloc r v heap = (l, heap') ->
    NHeapKeysBounded heap'.
Proof.
  intros heap r v l heap' HBounded HAlloc.
  destruct (heap_alloc_result heap r v l heap' HAlloc) as [-> ->].
  intros r' l' v' HIn.
  simpl in HIn.
  destruct HIn as [HIn | HIn].
  - inversion HIn; subst. simpl. lia.
  - specialize (HBounded r' l' v' HIn).
    simpl. lia.
Qed.
