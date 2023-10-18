Require Import Coq.Program.Equality.
Require Import Definitions.Keys.
Require Import Definitions.Values.
Require Import Definitions.DynamicActions.

Module H := FMapAVL.Make (RegionVars).
Module HMapP := FMapFacts.Facts H.


Definition Heap  := H.t Val. 
Definition H_Key := H.key.

Definition find_H (k: H_Key) (m: Heap) : option Val := H.find k m.
Definition update_H (p: H_Key * Val) (m: Heap) := H.add (fst p) (snd p) m.

Axiom allocate_H : Heap -> nat -> nat.
Axiom allocate_H_fresh : forall (m : Heap) (r: nat),
    find_H (r, allocate_H m r) m = None.
Axiom allocate_H_determ : forall (m1 m2 : Heap) (r: nat),
                            H.Equal m1 m2 ->
                            allocate_H m1 r = allocate_H m2 r.

Definition Functional_Map_Union_Heap (heap1 heap2 : Heap) : Heap :=
  let f := fun (k : nat * nat) (v : Val) (m : Heap) => H.add k v m
  in H.fold f heap1 heap2.


Reserved Notation "phi_heap '===>' phi'_heap'" (at level 50, left associativity).
Inductive Phi_Heap_Step : (Phi * Heap) -> (Phi * Heap) -> Prop :=
| PHS_Alloc  :  forall r l v heap,
    (Phi_Elem (DA_Alloc r l v), heap) ===> (Phi_Nil, update_H ((r,l), v) heap)
| PHS_Read   :  forall r l v heap,
    find_H (r,l) heap = Some v ->
    (Phi_Elem (DA_Read r l v), heap) ===> (Phi_Nil, heap)
| PHS_Write  :  forall r l v heap,
    H.In (r,l) heap ->
    (Phi_Elem (DA_Write r l v), heap) ===> (Phi_Nil, update_H ((r, l), v) heap)
| PHS_Seq_1  : forall phi1 phi1' heap heap',
    (phi1, heap) ===> (phi1', heap') ->
    forall phi2,
      (Phi_Seq phi1 phi2, heap) ===> (Phi_Seq phi1' phi2, heap')
| PHS_Seq_2  : forall phi2 phi2' heap heap',
    (phi2, heap) ===> (phi2', heap') ->
    (Phi_Seq Phi_Nil phi2, heap) ===> (Phi_Seq Phi_Nil phi2', heap')
| PHS_Seq_3  : forall heap,
    (Phi_Seq Phi_Nil Phi_Nil, heap) ===> (Phi_Nil, heap)
| PHS_Par_1  : forall phi1 phi1' heap heap',
    (phi1, heap) ===> (phi1', heap') ->
    forall phi2,
      (Phi_Par phi1 phi2, heap) ===> (Phi_Par phi1' phi2, heap')
| PHS_Par_2  : forall phi2 phi2' heap heap',
    (phi2, heap) ===> (phi2', heap') ->
    forall phi1,
      (Phi_Par phi1 phi2, heap) ===> (Phi_Par phi1 phi2', heap')
| PHS_Par_3  : forall heap,
    (Phi_Par Phi_Nil Phi_Nil, heap) ===> (Phi_Nil, heap)                                 
where "phi_heap '===>' phi'_heap'" := (Phi_Heap_Step phi_heap phi'_heap') : type_scope.

   
        
Reserved Notation "phi_heap '=a=>*' phi'_heap'_n'" (at level 50, left associativity).
Inductive Phi_Heap_StepsAux : (Phi * Heap) -> (Phi * Heap * nat) -> Prop :=
| PHT_Refl : forall phi heap,
    (phi, heap) =a=>* (phi, heap, 0)
| PHT_Step : forall phi phi' heap heap',
    (phi, heap) ===> (phi', heap') ->
    (phi, heap) =a=>* (phi', heap', 1)
| PHT_Trans : forall phi phi' phi'' heap heap' heap'' n' n'',
    (phi, heap) =a=>* (phi', heap', n') ->
    (phi', heap') =a=>* (phi'', heap'', n'') ->
    (phi, heap) =a=>* (phi'', heap'', (1 + n' + n'')%nat)
where "phi_heap '=a=>*' phi'_heap'_n'" := (Phi_Heap_StepsAux phi_heap phi'_heap'_n') : type_scope.


Reserved Notation "phi_heap '==>*' phi'_heap'" (at level 50, left associativity).
Definition Phi_Heap_Steps phi_heap phi'_heap' :=
  exists n',
    match phi'_heap' with
    | (phi', heap') => phi_heap =a=>* (phi', heap', n')
    end.
Notation "phi_heap '==>*' phi'_heap'" := (Phi_Heap_Steps phi_heap phi'_heap') : type_scope.


Lemma monotonic_heap_updates:
  forall phi heap phi' heap',
     (phi, heap) ===> (phi', heap') ->
     forall r l,
       H.In (r, l) heap ->
       H.In (r, l) heap'.
Proof.
  intros phi heap phi' heap' H.
  dependent induction H; intros.
  - destruct (RegionVars.eq_dec (r0, l0) (r, l)).
    + apply HMapP.add_in_iff. left. simpl. inversion e. intuition.
    + apply HMapP.add_neq_in_iff.
      * intro. apply n. unfold RegionVars.eq. intuition.
      * assumption.
  - assumption.
  - destruct (RegionVars.eq_dec (r0, l0) (r, l)).
     + apply HMapP.add_in_iff. left. simpl. inversion e. intuition.
    + apply HMapP.add_neq_in_iff.
      * intro. apply n. unfold RegionVars.eq. intuition.
      * assumption.
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


Export H.
Export HMapP.
