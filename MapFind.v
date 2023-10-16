Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FSetWeakList.
Require Import Coq.MSets.MSetWeakList.
Require Import Coq.FSets.FSetFacts.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Program.Equality.
Require Import Lia.



Require Import Coq.Setoids.Setoid.

Definition equivalent (n m : nat) : Prop :=
  n = m.

#[export]
Instance equiv_rel : Equivalence equivalent.
Proof.
  split.
  - unfold Reflexive. intros n. reflexivity.
  - unfold Symmetric. intros n m H. symmetry. assumption.
  - unfold Transitive. intros n m p H1 H2. transitivity m; assumption.
Qed.

Definition nat_equiv_class (n : nat) : Type :=
  { m : nat | equivalent n m }.



Require Import Top0.Keys.
Require Import Top0.Definitions.
Require Import Top0.Nameless.

Lemma NotNoneIsSome:
  forall {A} x,
    x <> None <-> exists a : A, x = Some a.
Proof.
  intuition.
  - destruct x.
    + exists a. reflexivity.
    + contradict H. reflexivity.
  - subst. destruct H. inversion H.          
Qed.

Module STProofs := ST.Raw.Proofs.
Module STMapP := FMapFacts.Facts ST.
Module STMapProp := FMapFacts.Properties ST.

Definition AddToMap :=
  fun(k : nat * nat) (v : tau) (m : Sigma) => ST.add k v m.

Definition Functional_Map_Union (stty1 stty2 : Sigma) : Sigma :=
  ST.fold AddToMap stty1 stty2.

Lemma In_node_iff_fold:
  forall k e t l d this this1 this2 is_bst is_bst0 is_bst1 is_bst2,
    ST.Raw.MapsTo l d (ST.this (ST.fold AddToMap {| ST.this := this; ST.is_bst := is_bst |}
       {| ST.this := ST.Raw.Node this1 k e this2 t; ST.is_bst := is_bst0 |}))  
   <-> (ST.Raw.MapsTo l d (ST.this(ST.fold AddToMap {| ST.this := this; ST.is_bst := is_bst |}
       {| ST.this := this1; ST.is_bst := is_bst1 |}))) \/
       (ST.Raw.MapsTo l d (ST.this(ST.fold AddToMap {| ST.this := this; ST.is_bst := is_bst |}
       {| ST.this := this2; ST.is_bst := is_bst2 |}))) \/
       ( ST.Raw.MapsTo k e this /\ l = k /\ d=e).
Admitted.

Lemma MapsTo_fold_Leaf:
  forall l d l0 x e r h is_bst is_bst0,
    ST.Raw.MapsTo l d
      (ST.this
         (ST.fold AddToMap {| ST.this := ST.Raw.Node l0 x e r h; ST.is_bst := is_bst |}
                  {| ST.this := ST.Raw.Leaf tau; ST.is_bst := is_bst0 |})) <->
      ST.Raw.MapsTo l d (ST.Raw.Node l0 x e r h).
Proof.
  intros.
  split; intro; apply STProofs.elements_mapsto.
  + apply STProofs.elements_mapsto in H.
    unfold ST.fold in H. rewrite STProofs.fold_1 in H. simpl in *; auto.
    unfold fold_left in H.
Admitted.

Lemma Functional_Map_Union_find_2:
  forall (sttya sttyb: ST.t tau) (l : ST.key) (t' : tau),
    ST.Raw.bst (ST.this sttya) ->
    ST.Raw.bst (ST.this (ST.fold AddToMap sttya sttyb)) ->
    ST.find (elt:=tau) l (Functional_Map_Union sttya sttyb) = ST.find (elt:=tau) l sttya.
Proof.
  intros.
  unfold Functional_Map_Union.
  apply STProofs.find_mapsto_equiv; auto. 
  split; intro.
  - destruct sttya. destruct sttyb. simpl. induction this0.
     + inversion is_bst; subst.
       * simpl in *. assumption.
       * eapply MapsTo_fold_Leaf.
         eauto.         
     + eapply In_node_iff_fold in H1.
       destruct H1 as [HA | [HB | HC]]. 
       * eapply IHthis0_1.  admit.
         eauto.
       * eapply IHthis0_2. admit.
         eauto.
       * unfold AddToMap in HC. 
         destruct HC as [HA' [HB' HC']].
         subst.  assumption.
  - destruct sttya. destruct sttyb. simpl. induction this0.
    + inversion is_bst; subst.
      * simpl in *. assumption.
      * apply STProofs.lt_tree_not_in in H4.
        apply STProofs.gt_tree_not_in in H5.
        now apply MapsTo_fold_Leaf.        
    + eapply In_node_iff_fold.
      * left. apply IHthis0_1.
        admit.
Admitted.



  

                   
Lemma Functional_Map_Union_find_1:
  forall sttya sttyb (l : ST.key) (t' : tau),
    ST.find (elt:=tau) l (Functional_Map_Union sttya sttyb) = ST.find (elt:=tau) l sttya.
Proof.
  intros.
  unfold Functional_Map_Union.
  destruct sttya. destruct sttyb. simpl. induction this0.
  - inversion is_bst; subst.
    + reflexivity. 
    + replace (ST.fold AddToMap
                       {| ST.this := ST.Raw.Node l0 x e r h; ST.is_bst := is_bst |}
                       {| ST.this := ST.Raw.Leaf tau; ST.is_bst := is_bst0 |})
        with ( {| ST.this := ST.Raw.Node l0 x e r h; ST.is_bst := is_bst |} ).
      * reflexivity.
      * unfold ST.fold. rewrite STProofs.fold_1; simpl; auto.
        unfold fold_left. unfold ST.Raw.elements. simpl.
        admit.
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
