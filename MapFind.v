Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FSetWeakList.
Require Import Coq.MSets.MSetWeakList.
Require Import Coq.FSets.FSetFacts.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Program.Equality.

Require Import Top0.Keys.
Require Import Top0.Definitions.
Require Import Top0.Nameless.

(*Module ST := FMapAVL.Make (RegionVars).
Definition Sigma : Type := ST.t tau.

Module STMapP := FMapFacts.Facts ST.
Module STRaw := ST.Raw.
Module STProofs := ST.Raw.Proofs.*)
Module EProofs := ST.Raw.Proofs.

Definition Functional_Map_Union (stty1 stty2 : Sigma) : Sigma :=
  let f := fun (k : nat * nat) (v : tau) (m : Sigma) => ST.add k v m
  in ST.fold f stty1 stty2.


(*Lemma StoreTyping_Extended:
  forall stty sttya sttyb,
    (forall rho env ctxt, TcEnv (stty, rho, env, ctxt) ) ->
    (forall (l : ST.key) (t' : tau),
       ST.find (elt:=tau) l stty = Some t' -> ST.find (elt:=tau) l sttya = Some t' ) ->
    (forall (l : ST.key) (t' : tau),
       ST.find (elt:=tau) l stty = Some t' -> ST.find (elt:=tau) l sttyb = Some t' ) ->
    (forall (l : ST.key) (t' : tau),
    	ST.find (elt:=tau) l stty = Some t' -> ST.find (elt:=tau) l (Functional_Map_Union sttya sttyb) = Some t' ).
Proof. 
  intros stty sttya sttyb Ha Hb.
  intros l t' H.
  assert ((forall rho env ctxt, TcEnv (stty, rho, env, ctxt) -> TcEnv (sttya, rho, env, ctxt))) as HA.
  apply ext_stores__env; auto.
  assert ((forall rho env ctxt, TcEnv (stty, rho, env, ctxt) -> TcEnv (sttyb, rho, env, ctxt))) as HB.
  apply ext_stores__env; auto.
  assert (forall (rho : Rho) (env : Env) (ctxt : Gamma), TcEnv (sttya, rho, env, ctxt)) as HTCEnv_a
       by (intros; apply HA; auto).
  assert (forall (rho : Rho) (env : Env) (ctxt : Gamma), TcEnv (sttyb, rho, env, ctxt)) as HTCEnv_b
       by (intros; apply HB; auto).
  edestruct HTCEnv_a.
  unfold ST.find in *.
  intro.
  apply EProofs.find_1 with (e:=H) (m:=ST.this (Functional_Map_Union sttya sttyb)) (x:=t').
  edestruct (Ha l t' H).
  generalize l. 
  apply Functional_Map_Union_find.
Admitted.*)

  
Lemma Functional_Map_Union_find:
  forall sttya sttyb (l : ST.key) (t' : tau),
    ST.find (elt:=tau) l (Functional_Map_Union sttya sttyb) = ST.find (elt:=tau) l sttya.
Proof.
  intros.
  unfold Functional_Map_Union. (*ST.fold.*)
  destruct sttya. destruct sttyb. simpl. induction this0.
  - inversion is_bst; subst.
    + reflexivity. 
    + unfold ST.find, ST.fold. simpl.
      destruct ( RegionVars.compare l x); simpl.
      * admit.
      * admit.
      * admit.
  - inversion is_bst0; subst.

    assert (
         ST.find (elt:=tau) l
           (ST.fold (fun (k0 : nat * nat) (v : tau) (m : Sigma) => ST.add k0 v m)
                    {| ST.this := this; ST.is_bst := is_bst |}
                    {| ST.this := this0_1; ST.is_bst := H3 |}) =
           ST.find (elt:=tau) l {| ST.this := this; ST.is_bst := is_bst |}) as HA
        by (apply IHthis0_1).

   assert (
         ST.find (elt:=tau) l
           (ST.fold (fun (k0 : nat * nat) (v : tau) (m : Sigma) => ST.add k0 v m)
                    {| ST.this := this; ST.is_bst := is_bst |}
                    {| ST.this := this0_2; ST.is_bst := H5 |}) =
           ST.find (elt:=tau) l {| ST.this := this; ST.is_bst := is_bst |}) as HB
       by (apply IHthis0_2).
Admitted.
