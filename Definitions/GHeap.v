From stdpp Require Import gmap.
Require Import Definitions.Values.
Require Import Definitions.Regions.
Require Import Definitions.ComputedActions.
Require Import Definitions.DynamicActions.
Require Import Definitions.Expressions.
Require Import Definitions.Types.
Require Import Definitions.Semantics.

Definition HeapVal := prod nat Val.
Definition HeapKey := prod nat  nat.
Definition Heap := gmap HeapKey HeapVal.

Definition timestamp_Write (p: Val) : HeapVal :=
  (S 0, p).

Definition timestamp_Read (p: option HeapVal) : option Val :=
  match p with
    None => None | Some v => Some (snd v)
  end.


Definition find_H (k: HeapKey) (m: Heap) : option Val := timestamp_Read (m !! k).
Definition update_H (p: HeapKey * Val) (m: Heap) :=  <[ fst p := timestamp_Write (snd p) ]>  m.

(* returns new address *)
Axiom allocate_H : Heap -> nat -> HeapKey.
Axiom allocate_H_fresh : forall (m : Heap) (r: nat),
  find_H (allocate_H m r) m = None.
Axiom allocate_H_determ :
  forall (m1 m2 : Heap) (r: nat),
    m1 = m2 ->
    allocate_H m1 r = allocate_H m2 r.

Definition Merge_Function (v1 v2 : option HeapVal) : option HeapVal :=
  match (v1, v2) with
  | (None, None) => None
  | (None, Some v) => Some v
  | (Some v, None) => Some v
  | (Some (t1, v1), Some (t2, v2)) =>
      if (Nat.lt_dec t1 t2) then Some (t2, v2) else Some (t1, v1)
end.

Definition Functional_Map_Union_Heap (heap1 heap2 : Heap) : Heap := merge Merge_Function heap1 heap2.


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


Reserved Notation "e '⇓' n" (at level 50, left associativity, only parsing).
Inductive BigStep   : (Heap * Env * Rho * Expr) -> (Heap * Val * Phi) -> Prop:=
| BS_Pair_Par: forall env rho ea1 ef1 ea2 ef2 v1 v2 theta1 theta2
                      (heap_eff1 heap_eff2 heap heap_mu1 heap_mu2 heap' : Heap)
                      (acts_mu1 acts_mu2 acts_eff1 acts_eff2 : Phi),
    (heap, env, rho, Eff_App ef1 ea1) ⇓ (heap_eff1, Eff theta1, acts_eff1) ->
    (heap, env, rho, Eff_App ef2 ea2) ⇓ (heap_eff2, Eff theta2, acts_eff2) ->
    Disjointness theta1 theta2 /\ not (Conflictness theta1 theta2) ->
    (heap, env, rho, Mu_App ef1 ea1) ⇓ (heap_mu1, v1, acts_mu1) ->
    (heap, env, rho, Mu_App ef2 ea2) ⇓ (heap_mu2, v2, acts_mu2) ->
    (Phi_Par acts_mu1 acts_mu2, heap) ==>* (Phi_Nil, heap') ->
    (heap, env, rho, Pair_Par ef1 ea1 ef2 ea2)
      ⇓ (heap', Pair (v1, v2), Phi_Seq (Phi_Par acts_eff1 acts_eff2) (Phi_Par acts_mu1 acts_mu2))
where "e '⇓' n" := (BigStep e n) : type_scope.


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

Axiom TcHeap_Extended:
  forall hp hp' ef1 ea1 ef2 ea2 v1 v2 env rho 
  	heap heap_mu1 heap_mu2 sttym sttya acts_mu1 acts_mu2,
    (heap, env, rho, Mu_App ef1 ea1) ⇓ (heap_mu1, v1, acts_mu1) ->

    (heap, env, rho, Mu_App ef2 ea2) ⇓ (heap_mu2, v2, acts_mu2) ->
    (Phi_Par acts_mu1 acts_mu2, hp) ==>* (Phi_Nil, hp') ->
    TcHeap (heap_mu1, sttym) ->
    TcHeap (heap_mu2, sttya) ->
    TcHeap (hp', Functional_Map_Union sttym sttya).
