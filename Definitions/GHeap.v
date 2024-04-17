From stdpp Require Import gmap.
Require Import Definitions.Values.
Require Import Definitions.Regions.
Require Import Definitions.ComputedActions.
Require Import Definitions.DynamicActions.
Require Import Definitions.Expressions.
Require Import Definitions.GTypes.

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


(* Define an equivalence relation for MyType *)
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


Axiom timestamp_Write: Val -> HeapVal.
Axiom timestamp_Read : option HeapVal -> option Val.
Axiom timestamp : HeapVal -> nat.

Definition find_H (k: HeapKey) (m: Heap) : option Val
  := m !! k.
Definition update_H (p: HeapKey * Val) (m: Heap)
  :=  <[ fst p := snd p ]>  m.

(* returns new address *)
Axiom allocate_H : Heap -> nat -> nat.
Axiom allocate_H_fresh : forall (m : Heap) (r: nat),
  find_H (r, allocate_H m r) m = None.
Axiom allocate_H_determ :
  forall (m1 m2 : Heap) (r: nat),
    m1 =@{Heap} m2 ->
    allocate_H m1 r = allocate_H m2 r.

Definition Merge_Function (v1 v2 : option HeapVal) : option HeapVal :=
  match (v1, v2) with
  | (None, None) => None
  | (None, Some v) => Some v
  | (Some v, None) => Some v
  | (Some v1, Some v2) =>
      if (Nat.lt_dec (timestamp v1) (timestamp v2)) then Some v2 else Some v1
end.

Definition Functional_Map_Union_Heap (heap1 heap2 : Heap) : Heap
  := merge Merge_Function heap1 heap2.

  

Reserved Notation "phi_heap '===>' phi'_heap'" (at level 50, left associativity).
Inductive Phi_Heap_Step : (Phi * Heap) -> (Phi * Heap) -> Prop :=
| PHS_Alloc:  forall r l v heap,
    (Phi_Elem (DA_Alloc r l v), heap) ===> (Phi_Nil, update_H ((r,l), v) heap)
| PHS_Read:  forall r l v heap,
    find_H (r,l) heap = Some v ->
    (Phi_Elem (DA_Read r l v), heap) ===> (Phi_Nil, heap)
| PHS_Write:  forall r l v heap ,
    find_H (r,l)  heap <> None ->
    (Phi_Elem (DA_Write r l v), heap) ===> (Phi_Nil, update_H ((r, l), v) heap)
| PHS_Seq_1: forall phi1 phi1' heap heap',
    (phi1, heap) ===> (phi1', heap') ->
    forall phi2,
      (Phi_Seq phi1 phi2, heap) ===> (Phi_Seq phi1' phi2, heap')
| PHS_Seq_2: forall phi2 phi2' heap heap',
    (phi2, heap) ===> (phi2', heap') ->
    (Phi_Seq Phi_Nil phi2, heap) ===> (Phi_Seq Phi_Nil phi2', heap')
| PHS_Seq_3: forall heap,
    (Phi_Seq Phi_Nil Phi_Nil, heap) ===> (Phi_Nil, heap)
| PHS_Par_1: forall phi1 phi1' heap heap',
    (phi1, heap) ===> (phi1', heap') ->
    forall phi2,
      (Phi_Par phi1 phi2, heap) ===> (Phi_Par phi1' phi2, heap')
| PHS_Par_2: forall phi2 phi2' heap heap',
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



