From stdpp Require Import gmap.
From Stdlib Require Import List Lia String.
Require Import theories.Core.Values.

Definition HeapVal := Val.
Definition HeapKey := prod nat nat.
Definition Heap := gmap HeapKey HeapVal.

Definition HeapKey' := prod HeapKey nat.
Definition Heap' := gmap HeapKey' HeapVal.

Definition keys_eq (x y : HeapKey)
  := Nat.eq (fst x) (fst y) /\ Nat.eq (snd x) (snd y).

Lemma keys_eq_dec : forall (k : HeapKey) (k' : HeapKey),
    { keys_eq k k' } + { ~ keys_eq k k' }.
Proof.
  intros. unfold keys_eq, Nat.eq.  destruct k as [r l];
    destruct k' as [r' l']; subst; simpl.
  destruct (eq_nat_dec r r'); destruct (eq_nat_dec l l'). 
  - left. unfold Nat.eq. auto.
  - right. intro. contradict n. intuition.
  - right. intro. contradict n. intuition.
  - right. intro. contradict n. intuition.
Qed. 

Definition Heap_equiv (x y : Heap) : Prop :=
  x =@{gmap HeapKey HeapVal} y.

Global Instance heap_equiv : Equiv Heap := λ a b, a =@{Heap} b.
Global Instance heap_equivalence : Equivalence (≡@{Heap}).
Proof.
 split; [unfold Reflexive | unfold Symmetric | unfold Transitive].
  - intros x. unfold Heap_equiv. reflexivity.
  - intros x y H. unfold equiv, heap_equiv in *. subst. reflexivity.
  - intros x y z H1 H2. unfold equiv, heap_equiv in *. subst. reflexivity.
Qed.

Global Instance val_equiv : Equiv Val := λ a b, a = b.
Global Instance val_equivalence : Equivalence (≡@{Val}).
Proof.
  unfold equiv, val_equiv.
  split; congruence.
Qed.

Lemma Test:
  forall (h1 h2: Heap) k x,
    h1 ≡@{Heap} h2 ->
    h1 !! k = Some x ->
    ∃ y, h2 !! k = Some y ∧ x ≡@{Val} y.
Proof.
  intros.
  apply map_equiv_lookup_l with (m1:=h1). 
  inversion H; subst. reflexivity.
  assumption.
Qed.

Lemma Test2:
  forall (h1 h2: Heap),
    h1 ≡@{Heap} h2 ->
    ∀ k, h1 !! k ≡ h2 !! k.
Proof.
  intros.
  inversion H; subst.
  reflexivity.
Qed.

Lemma Test3:
  forall (h1 h2: Heap),
    h1 = h2 ->
    h1 ≡@{Heap} h2.    
Proof.
  intros.
  assumption.
Qed.

Definition find_H (k: HeapKey) (m: Heap) : option Val
  := m !! k.
Definition update_H (p: HeapKey * Val) (m: Heap)
  :=  <[ fst p := snd p ]>  m.

Definition HeapLookupEquivalent (h1 h2 : Heap) : Prop :=
  forall k, find_H k h1 = find_H k h2.

Global Instance HeapLookupEquivalent_equivalence :
  Equivalence HeapLookupEquivalent.
Proof.
  split.
  - intros h k. reflexivity.
  - intros h1 h2 H k. symmetry. apply H.
  - intros h1 h2 h3 H12 H23 k.
    rewrite H12. apply H23.
Qed.

Lemma heap_equiv_lookup_equivalent :
  forall h1 h2,
    h1 ≡@{Heap} h2 ->
    HeapLookupEquivalent h1 h2.
Proof.
  intros h1 h2 HEqual.
  unfold equiv, heap_equiv in HEqual.
  subst.
  intros k.
  reflexivity.
Qed.

Lemma heap_lookup_equivalent_eq :
  forall h1 h2,
    HeapLookupEquivalent h1 h2 ->
    h1 = h2.
Proof.
  intros h1 h2 HLookup.
  apply map_eq.
  intros k.
  apply HLookup.
Qed.

Lemma heap_lookup_equivalent_heap_equiv :
  forall h1 h2,
    HeapLookupEquivalent h1 h2 ->
    h1 ≡@{Heap} h2.
Proof.
  intros h1 h2 HLookup.
  apply heap_lookup_equivalent_eq.
  exact HLookup.
Qed.

Fixpoint max_location_for_region
    (r : nat) (entries : list (HeapKey * HeapVal)) : nat :=
  match entries with
  | nil => 0
  | ((r', l), _) :: entries' =>
      let rest := max_location_for_region r entries' in
      if Nat.eq_dec r r' then S (Nat.max l rest) else rest
  end.

Definition allocate_H (m : Heap) (r : nat) : nat :=
  max_location_for_region r (map_to_list m).

Lemma max_location_for_region_lt :
  forall entries r l v,
    In ((r, l), v) entries ->
    l < max_location_for_region r entries.
Proof.
  induction entries as [| [[r' l'] v'] entries IH]; intros r l v HIn;
    simpl in *.
  - contradiction.
  - destruct HIn as [HHead | HTail].
    + inversion HHead; subst.
      destruct (Nat.eq_dec r r); lia.
    + destruct (Nat.eq_dec r r').
      * specialize (IH r l v HTail). lia.
      * eapply IH; eauto.
Qed.

Lemma allocate_H_fresh : forall (m : Heap) (r: nat),
  find_H (r, allocate_H m r) m = None.
Proof.
  intros m r.
  unfold find_H.
  destruct (m !! (r, allocate_H m r)) eqn:HLookup; [| exact HLookup].
  assert (HIn : ((r, allocate_H m r), h) ∈ map_to_list m).
  { apply elem_of_map_to_list. exact HLookup. }
  apply elem_of_list_In in HIn.
  assert (Hlt : allocate_H m r < allocate_H m r).
  { unfold allocate_H at 2.
    eapply max_location_for_region_lt; eauto. }
  lia.
Qed.

Lemma allocate_H_determ :
  forall (m1 m2 : Heap) (r: nat),
    m1 =@{Heap} m2 ->
    allocate_H m1 r = allocate_H m2 r.
Proof.
  intros m1 m2 r HEqual.
  unfold equiv, heap_equiv in HEqual; subst.
  reflexivity.
Qed.
