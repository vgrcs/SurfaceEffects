Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FSetWeakList.
Require Import Coq.MSets.MSetWeakList.
Require Import Coq.FSets.FSetFacts.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FMapFacts.

Require Import Top0.Keys.

Inductive type2 :=
  | Ty2_Natural : type2
  | Ty2_Boolean : type2.

Definition tau := type2.

Module ST := FMapAVL.Make (RegionVars).
Definition Sigma : Type := ST.t tau.

Module STMapP := FMapFacts.Facts ST.
Module STRaw := ST.Raw.
Module STProofs := ST.Raw.Proofs.

  
Definition Functional_Map_Union (stty1 stty2 : Sigma) : Sigma :=
  let f := fun (k : nat * nat) (v : tau) (m : Sigma) => ST.add k v m
  in ST.fold f stty1 stty2.
  
Axiom Functional_Map_Union_find:
  forall sttya sttyb (l : ST.key) (t' : tau),
    ST.find (elt:=tau) l (Functional_Map_Union sttya sttyb) = ST.find (elt:=tau) l sttya.
