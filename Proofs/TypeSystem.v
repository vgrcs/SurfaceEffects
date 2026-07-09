From stdpp Require Import gmap.
From stdpp Require Import strings.
From stdpp Require Import fin_maps.

Require Import Coq.Sets.Ensembles.
Require Import Coq.Program.Equality.

Require Import Definitions.Tactics.
Require Import Proofs.LocallyNameless.
Require Import Definitions.GHeap. 
Require Import Proofs.Determinism.
Require Import Definitions.GTypes.
Require Import Definitions.DynamicActions.
Require Import Proofs.EffectFacts.
Require Import Proofs.RegionFacts.
Require Import Proofs.TypeFacts.
Require Import Proofs.HeapFacts.


Module TypeSoundness.

  Import GHeap.
  Import Regions.
  Import GTypes.
  Import StaticActions.
  Import ComputedActions.
  Import Values.
  Import Expressions.
  Import Semantics.
  Import TypeFacts.
  Import Ensembles.


Lemma PairType_unique_type:
  forall stty k t1 t2,
    find_ST k stty = Some t1 ->
    find_ST k stty = Some t2 ->
    t1 = t2.
Proof.
  intros stty k t1 t2 H1 H2.
  unfold find_ST in *.
  apply elem_of_map_to_list in H1.
  apply elem_of_map_to_list in H2.           
  apply map_to_list_unique with (m:=stty) (i:=k); auto.
Qed.

  
Lemma stty_merge_comm:
  forall (sttya sttyb : Sigma),
  forall (k : SigmaKey),
    sttya ##ₘ sttyb ->
    Merge_ST (sttya !! k) (sttyb !! k) =
      Merge_ST (sttyb !! k) (sttya !! k).
Proof.
  intros.
  assert (forall i, sttya !! i = None ∨ sttyb !! i = None).
  now apply map_disjoint_alt.
  destruct (H0 k); unfold Merge_ST. clear H0.
  - rewrite H1.
    destruct (sttyb !! k); simpl; reflexivity.
  - rewrite H1.
    destruct (sttyb !! k); simpl; reflexivity. 
Qed.


      
      
Lemma StoreTyping_Union:
  forall l t (sttya sttyb : Sigma),
    sttya ##ₘ sttyb ->
    find_ST l sttya = Some t \/ find_ST l sttyb = Some t <->
    find_ST l (Functional_Map_Union_Sigma sttya sttyb) = Some t.
Proof.
  intros l t sttya sttyb HDisjoint.
  split.
  - intro.
    unfold find_ST, Functional_Map_Union_Sigma in *.
    assert (Hcomm : merge Merge_ST sttya sttyb = merge Merge_ST sttyb sttya)
             by (apply merge_comm; intro; now apply stty_merge_comm).
    destruct H.
    + replace (merge Merge_ST sttya sttyb !! l)
      with (diag_None Merge_ST (sttya !! l) (sttyb !! l)) by
        (rewrite lookup_merge; reflexivity).
      destruct (sttya !! l); destruct (sttyb !! l); unfold Merge_ST; simpl;
      try (solve [assumption | inversion H]).
    + rewrite Hcomm.
      replace (merge Merge_ST sttyb sttya !! l)
      with (diag_None Merge_ST (sttyb !! l) (sttya !! l)) by
      (rewrite lookup_merge; reflexivity).
      destruct (sttya !! l); destruct (sttyb !! l); unfold Merge_ST; simpl;
      try (solve [assumption | inversion H]).
  - intro.
    unfold find_ST, Functional_Map_Union_Sigma in *. 
    replace (merge Merge_ST sttya sttyb !! l)
      with (diag_None Merge_ST (sttya !! l) (sttyb !! l)) in H by
        (rewrite lookup_merge; reflexivity).
    destruct (sttya !! l); destruct (sttyb !! l); unfold Merge_ST in H; simpl in H.
    + left. assumption.
    + left. assumption.
    + right. assumption.
    + inversion H.  
Qed.


Lemma StoreTyping_Union_2:
  forall l t (stty sttya sttyb : Sigma),
    sttya ∖ stty ##ₘ sttyb ∖ stty ->
    find_ST l stty = Some t ->
    find_ST l sttya = Some t ->
    find_ST l sttyb = Some t ->
    find_ST l (stty ∪ (sttya ∖ stty ∪ sttyb ∖ stty)) = Some t.
Proof.
  intros. unfold find_ST in *.
  rewrite lookup_union_l' with (m2 := (sttya ∖ stty ∪ sttyb ∖ stty)).
  assumption.
  auto.
Qed.

Lemma TcValExtended:
  forall  stty1 stty2 v1 v2 rho ty1 ty2,
    stty1 ##ₘ stty2 ->
    TcVal (stty1, v1, subst_rho rho ty1) ->
    TcVal (stty2, v2, subst_rho rho ty2) ->
    TcVal (Functional_Map_Union_Sigma stty1 stty2,
        Pair (v1, v2), subst_rho rho (Ty_Pair ty1 ty2)).
Proof.
  intros.
  replace (subst_rho rho (Ty_Pair ty1 ty2))
    with (Ty_Pair (subst_rho rho ty1) (subst_rho rho ty2))
    by (now rewrite subst_rho_pair).
  econstructor.  
  - apply ext_stores__val with (stty:=stty1).
    intros.
    + apply StoreTyping_Union; auto.
    + assumption.
  - apply ext_stores__val with (stty:=stty2).
    intros. 
    + apply StoreTyping_Union; auto. 
    + assumption.
Qed.

Lemma WeakenigImpliesSubsetEq:
forall stty stty',
  (forall (l : SigmaKey) (t' : Tau),
     find_ST l stty = Some t' -> find_ST l stty' = Some t') ->
  stty ⊆ stty'.
Proof.
  intros stty stty' H.
  apply map_subseteq_spec. auto.
Qed.      
  
Lemma TcValExtended_2:
  forall  stty stty1 stty2 v1 v2 rho ty1 ty2,
    stty1 ∖ stty ##ₘ stty2 ∖ stty ->
    (∀ (l : SigmaKey) (t' : Tau),
        find_ST l stty = Some t' → find_ST l stty1 = Some t') ->
    (∀ (l : SigmaKey) (t' : Tau),
          find_ST l stty = Some t' → find_ST l stty2 = Some t') ->
    TcVal (stty1, v1, subst_rho rho ty1) ->
    TcVal (stty2, v2, subst_rho rho ty2) ->
    TcVal (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty), Pair (v1, v2),
        subst_rho rho (Ty_Pair ty1 ty2)).
Proof.
  intros stty stty1 stty2 v1 v2 rho ty1 ty2
    Hdisj Hext1 Hext2 HTcVal1 HTcVal2.
  replace (subst_rho rho (Ty_Pair ty1 ty2))
    with (Ty_Pair (subst_rho rho ty1) (subst_rho rho ty2))
    by (now rewrite subst_rho_pair).
  econstructor; eauto.
  - apply ext_stores__val with (stty:=stty1).
    + intros l t' Hfind.
      unfold find_ST in *.
      apply lookup_union_Some_raw.
      destruct (stty !! l) eqn:Hbase.
      * left.
        apply Hext1 in Hbase.
        unfold find_ST in Hbase.
        rewrite Hfind in Hbase.
        inversion Hbase; subst.
        assumption.
      * right. split; [reflexivity |].
        apply lookup_union_Some_raw.
        left.
        apply lookup_difference_Some.
        split.
        -- assumption.
        -- rewrite Hbase. reflexivity.
    + assumption.
  - apply ext_stores__val with (stty:=stty2).
    + intros l t' Hfind.
      unfold find_ST in *.
      apply lookup_union_Some_raw.
      destruct (stty !! l) eqn:Hbase.
      * left.
        apply Hext2 in Hbase.
        unfold find_ST in Hbase.
        rewrite Hfind in Hbase.
        inversion Hbase; subst.
        assumption.
      * right. split; [reflexivity |].
        assert (Hdiff2 : (stty2 ∖ stty) !! l = Some t').
        { apply lookup_difference_Some. split.
          - assumption.
          - rewrite Hbase. reflexivity. }
        apply lookup_union_Some_raw.
        right. split; [| assumption].
        assert (Hdisj_spec : forall i x y,
                   (stty1 ∖ stty) !! i = Some x ->
                   (stty2 ∖ stty) !! i = Some y -> False)
          by (apply map_disjoint_spec; assumption).
        destruct ((stty1 ∖ stty) !! l) eqn:Hdiff1; auto.
        exfalso. eapply Hdisj_spec; eauto.
    + assumption.
Qed.

Inductive Phi_Updates : SigmaKey -> Val -> Phi -> Prop :=
| PU_Alloc : forall r l v,
    Phi_Updates (r, l) v (Phi_Elem (DA_Alloc r l v))
| PU_Write : forall r l v,
    Phi_Updates (r, l) v (Phi_Elem (DA_Write r l v))
| PU_Seq_L : forall k v phi1 phi2,
    Phi_Updates k v phi1 ->
    Phi_Updates k v (Phi_Seq phi1 phi2)
| PU_Seq_R : forall k v phi1 phi2,
    Phi_Updates k v phi2 ->
    Phi_Updates k v (Phi_Seq phi1 phi2)
| PU_Par_L : forall k v phi1 phi2,
    Phi_Updates k v phi1 ->
    Phi_Updates k v (Phi_Par phi1 phi2)
| PU_Par_R : forall k v phi1 phi2,
    Phi_Updates k v phi2 ->
    Phi_Updates k v (Phi_Par phi1 phi2).

Inductive Phi_Allocates : SigmaKey -> Phi -> Prop :=
| PA_Alloc : forall r l v,
    Phi_Allocates (r, l) (Phi_Elem (DA_Alloc r l v))
| PA_Seq_L : forall k phi1 phi2,
    Phi_Allocates k phi1 ->
    Phi_Allocates k (Phi_Seq phi1 phi2)
| PA_Seq_R : forall k phi1 phi2,
    Phi_Allocates k phi2 ->
    Phi_Allocates k (Phi_Seq phi1 phi2)
| PA_Par_L : forall k phi1 phi2,
    Phi_Allocates k phi1 ->
    Phi_Allocates k (Phi_Par phi1 phi2)
| PA_Par_R : forall k phi1 phi2,
    Phi_Allocates k phi2 ->
    Phi_Allocates k (Phi_Par phi1 phi2).

Definition TcPhi (stty : Sigma) (phi : Phi) : Prop :=
  forall k v,
    Phi_Updates k v phi ->
    exists t, find_ST k stty = Some t /\ TcVal (stty, v, t).

Lemma Phi_Updates_nil_false :
  forall k v, ~ Phi_Updates k v Phi_Nil.
Proof.
  intros k v H. inversion H.
Qed.

Lemma Phi_Allocates_nil_false :
  forall k, ~ Phi_Allocates k Phi_Nil.
Proof.
  intros k H. inversion H.
Qed.

Lemma TcPhi_nil :
  forall stty, TcPhi stty Phi_Nil.
Proof.
  unfold TcPhi. intros stty k v H. inversion H.
Qed.

Lemma TcPhi_weaken :
  forall stty stty' phi,
    (forall k t, find_ST k stty = Some t -> find_ST k stty' = Some t) ->
    TcPhi stty phi ->
    TcPhi stty' phi.
Proof.
  unfold TcPhi.
  intros stty stty' phi Hweak HTcPhi k v HUpdate.
  destruct (HTcPhi k v HUpdate) as [t [Hfind HTcVal]].
  exists t. split; [now apply Hweak |].
  eapply ext_stores__val; eauto.
Qed.

Lemma TcPhi_seq :
  forall stty phi1 phi2,
    TcPhi stty phi1 ->
    TcPhi stty phi2 ->
    TcPhi stty (Phi_Seq phi1 phi2).
Proof.
  unfold TcPhi.
  intros stty phi1 phi2 H1 H2 k v HUpdate.
  inversion HUpdate; subst; eauto.
Qed.

Lemma TcPhi_par :
  forall stty phi1 phi2,
    TcPhi stty phi1 ->
    TcPhi stty phi2 ->
    TcPhi stty (Phi_Par phi1 phi2).
Proof.
  unfold TcPhi.
  intros stty phi1 phi2 H1 H2 k v HUpdate.
  inversion HUpdate; subst; eauto.
Qed.

Lemma StoreTyping_Extended_Base :
  forall l t (stty stty1 stty2 : Sigma),
    stty1 ∖ stty ##ₘ stty2 ∖ stty ->
    (forall k t', find_ST k stty = Some t' -> find_ST k stty1 = Some t') ->
    (forall k t', find_ST k stty = Some t' -> find_ST k stty2 = Some t') ->
    find_ST l stty = Some t ->
    find_ST l (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty)) = Some t.
Proof.
  intros.
  eapply StoreTyping_Union_2; eauto.
Qed.

Lemma StoreTyping_Extended_Left :
  forall l t (stty stty1 stty2 : Sigma),
    stty1 ∖ stty ##ₘ stty2 ∖ stty ->
    (forall k t', find_ST k stty = Some t' -> find_ST k stty1 = Some t') ->
    find_ST l stty1 = Some t ->
    find_ST l (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty)) = Some t.
Proof.
  intros l t stty stty1 stty2 Hdisj Hext Hfind.
  unfold find_ST in *.
  apply lookup_union_Some_raw.
  destruct (stty !! l) eqn:Hbase.
  - left.
    assert (Hbase_ext := Hbase).
    apply Hext in Hbase_ext.
    unfold find_ST in Hbase_ext.
    rewrite Hfind in Hbase_ext.
    inversion Hbase_ext; subst.
    assumption.
  - right. split; [exact Hbase |].
    apply lookup_union_Some_raw.
    left.
    apply lookup_difference_Some. split; auto.
Qed.

Lemma StoreTyping_Extended_Right :
  forall l t (stty stty1 stty2 : Sigma),
    stty1 ∖ stty ##ₘ stty2 ∖ stty ->
    (forall k t', find_ST k stty = Some t' -> find_ST k stty2 = Some t') ->
    find_ST l stty2 = Some t ->
    find_ST l (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty)) = Some t.
Proof.
  intros l t stty stty1 stty2 Hdisj Hext Hfind.
  unfold find_ST in *.
  apply lookup_union_Some_raw.
  destruct (stty !! l) eqn:Hbase.
  - left.
    assert (Hbase_ext := Hbase).
    apply Hext in Hbase_ext.
    unfold find_ST in Hbase_ext.
    rewrite Hfind in Hbase_ext.
    inversion Hbase_ext; subst.
    assumption.
  - right. split; [exact Hbase |].
    assert (Hdiff2 : (stty2 ∖ stty) !! l = Some t).
    { apply lookup_difference_Some. split; auto. }
    apply lookup_union_Some_raw.
    right. split; [| assumption].
    assert (Hdisj_spec : forall i x y,
               (stty1 ∖ stty) !! i = Some x ->
               (stty2 ∖ stty) !! i = Some y -> False)
      by (apply map_disjoint_spec; assumption).
    destruct ((stty1 ∖ stty) !! l) eqn:Hdiff1; auto.
    exfalso. eapply Hdisj_spec; eauto.
Qed.

Lemma Phi_Heap_Step_preserves_updates :
  forall phi phi' heap heap' k v,
    (phi, heap) ===> (phi', heap') ->
    Phi_Updates k v phi' ->
    Phi_Updates k v phi.
Proof.
  intros phi phi' heap heap' k v HStep.
  dependent induction HStep; intros HUpdate; inversion HUpdate; subst; eauto using Phi_Updates.
Qed.

Lemma Phi_Heap_StepsAux_preserves_updates :
  forall phi heap phi' heap' n k v,
    (phi, heap) =a=>* (phi', heap', n) ->
    Phi_Updates k v phi' ->
    Phi_Updates k v phi.
Proof.
  intros phi heap phi' heap' n k v HSteps.
  dependent induction HSteps; intros HUpdate.
  - assumption.
  - eapply Phi_Heap_Step_preserves_updates; eauto.
  - eapply IHHSteps1; try reflexivity.
    eapply IHHSteps2; try reflexivity; eauto.
Qed.

Lemma Phi_Heap_Step_preserves_allocates :
  forall phi phi' heap heap' k,
    (phi, heap) ===> (phi', heap') ->
    Phi_Allocates k phi' ->
    Phi_Allocates k phi.
Proof.
  intros phi phi' heap heap' k HStep.
  dependent induction HStep; intros HAlloc; inversion HAlloc; subst; eauto using Phi_Allocates.
Qed.

Lemma Phi_Heap_StepsAux_preserves_allocates :
  forall phi heap phi' heap' n k,
    (phi, heap) =a=>* (phi', heap', n) ->
    Phi_Allocates k phi' ->
    Phi_Allocates k phi.
Proof.
  intros phi heap phi' heap' n k HSteps.
  dependent induction HSteps; intros HAlloc.
  - assumption.
  - eapply Phi_Heap_Step_preserves_allocates; eauto.
  - eapply IHHSteps1; try reflexivity.
    eapply IHHSteps2; try reflexivity; eauto.
Qed.

Lemma Phi_Heap_Step_lookup_source :
  forall phi phi' heap heap' k v,
    (phi, heap) ===> (phi', heap') ->
    find_H k heap' = Some v ->
    find_H k heap = Some v \/ Phi_Updates k v phi.
Proof.
  intros phi phi' heap heap' k v HStep.
  dependent induction HStep; intros Hfind; simpl in *.
  - destruct (decide (k = (r, l))) as [Heq | Hneq].
    + subst.
      assert (Hsame : find_H (r, l) (update_H ((r, l), v0) heap) = Some v0).
      { unfold find_H, update_H. simpl. apply H_same_key_1. }
      rewrite Hsame in Hfind. inversion Hfind; subst.
      right. constructor.
    + left. unfold find_H, update_H in Hfind. simpl in Hfind.
      unfold find_H. eapply H_diff_keys_1; eauto.
  - left. assumption.
  - destruct (decide (k = (r, l))) as [Heq | Hneq].
    + subst.
      assert (Hsame : find_H (r, l) (update_H ((r, l), v0) heap) = Some v0).
      { unfold find_H, update_H. simpl. apply H_same_key_1. }
      rewrite Hsame in Hfind. inversion Hfind; subst.
      right. constructor.
    + left. unfold find_H, update_H in Hfind. simpl in Hfind.
      unfold find_H. eapply H_diff_keys_1; eauto.
  - destruct (IHHStep _ _ _ _ eq_refl eq_refl Hfind) as [HOld | HUpdate].
    + left. assumption.
    + right. now apply PU_Seq_L.
  - destruct (IHHStep _ _ _ _ eq_refl eq_refl Hfind) as [HOld | HUpdate].
    + left. assumption.
    + right. now apply PU_Seq_R.
  - left. assumption.
  - destruct (IHHStep _ _ _ _ eq_refl eq_refl Hfind) as [HOld | HUpdate].
    + left. assumption.
    + right. now apply PU_Par_L.
  - destruct (IHHStep _ _ _ _ eq_refl eq_refl Hfind) as [HOld | HUpdate].
    + left. assumption.
    + right. now apply PU_Par_R.
  - left. assumption.
Qed.

Lemma Phi_Heap_StepsAux_lookup_source :
  forall phi heap phi' heap' n k v,
    (phi, heap) =a=>* (phi', heap', n) ->
    find_H k heap' = Some v ->
    find_H k heap = Some v \/ Phi_Updates k v phi.
Proof.
  intros phi heap phi' heap' n k v HSteps.
  generalize dependent v.
  generalize dependent k.
  dependent induction HSteps; intros k v Hfind.
  - left. assumption.
  - eapply Phi_Heap_Step_lookup_source; eauto.
  - destruct (IHHSteps2 _ _ _ _ _ eq_refl eq_refl k v Hfind) as [Hmid | HUpdateMid].
    + destruct (IHHSteps1 _ _ _ _ _ eq_refl eq_refl k v Hmid) as [Hstart | HUpdateStart].
      * left. assumption.
      * right. assumption.
    + right.
      eapply Phi_Heap_StepsAux_preserves_updates; eauto.
Qed.

Lemma Phi_Heap_Steps_lookup_source :
  forall phi heap phi' heap' k v,
    (phi, heap) ==>* (phi', heap') ->
    find_H k heap' = Some v ->
    find_H k heap = Some v \/ Phi_Updates k v phi.
Proof.
  intros phi heap phi' heap' k v [n HSteps] Hfind.
  eapply Phi_Heap_StepsAux_lookup_source; eauto.
Qed.

Lemma Phi_Heap_Step_preserves_domain :
  forall phi phi' heap heap' k v,
    (phi, heap) ===> (phi', heap') ->
    find_H k heap = Some v ->
    exists v', find_H k heap' = Some v'.
Proof.
  intros phi phi' heap heap' k v HStep.
  dependent induction HStep; intros Hfind; simpl in *.
  - destruct (decide (k = (r, l))).
    + subst. exists v0. unfold find_H, update_H. simpl. apply H_same_key_1.
    + exists v. unfold find_H in Hfind. unfold find_H, update_H. simpl.
      eapply H_diff_keys_2; eauto.
  - exists v. assumption.
  - destruct (decide (k = (r, l))).
    + subst. exists v0. unfold find_H, update_H. simpl. apply H_same_key_1.
    + exists v. unfold find_H in Hfind. unfold find_H, update_H. simpl.
      eapply H_diff_keys_2; eauto.
  - eapply IHHStep; try reflexivity; eauto.
  - eapply IHHStep; try reflexivity; eauto.
  - exists v. assumption.
  - eapply IHHStep; try reflexivity; eauto.
  - eapply IHHStep; try reflexivity; eauto.
  - exists v. assumption.
Qed.

Lemma Phi_Heap_StepsAux_preserves_domain :
  forall phi heap phi' heap' n k v,
    (phi, heap) =a=>* (phi', heap', n) ->
    find_H k heap = Some v ->
    exists v', find_H k heap' = Some v'.
Proof.
  intros phi heap phi' heap' n k v HSteps.
  generalize dependent v.
  generalize dependent k.
  dependent induction HSteps; intros k v Hfind.
  - exists v. assumption.
  - eapply Phi_Heap_Step_preserves_domain; eauto.
  - destruct (IHHSteps1 _ _ _ _ _ eq_refl eq_refl k v Hfind) as [vmid Hmid].
    destruct (IHHSteps2 _ _ _ _ _ eq_refl eq_refl k vmid Hmid) as [vfinal Hfinal].
    exists vfinal. assumption.
Qed.

Lemma Phi_Heap_Steps_preserves_domain :
  forall phi heap phi' heap' k v,
    (phi, heap) ==>* (phi', heap') ->
    find_H k heap = Some v ->
    exists v', find_H k heap' = Some v'.
Proof.
  intros phi heap phi' heap' k v [n HSteps] Hfind.
  eapply Phi_Heap_StepsAux_preserves_domain; eauto.
Qed.

Lemma Phi_Heap_Step_alloc_source :
  forall phi phi' heap heap' k v,
    (phi, heap) ===> (phi', heap') ->
    find_H k heap' = Some v ->
    find_H k heap = None ->
    Phi_Allocates k phi.
Proof.
  intros phi phi' heap heap' k v HStep.
  dependent induction HStep; intros Hfind Hnone; simpl in *.
  - destruct (decide (k = (r, l))) as [Heq | Hneq].
    + subst. constructor.
    + unfold find_H, update_H in Hfind. simpl in Hfind.
      assert (Hold : find_H k heap = Some v).
      { unfold find_H. eapply H_diff_keys_1; eauto. }
      rewrite Hnone in Hold. discriminate.
  - rewrite Hnone in Hfind. discriminate.
  - destruct (decide (k = (r, l))) as [Heq | Hneq].
    + subst. rewrite Hnone in H. contradiction.
    + unfold find_H, update_H in Hfind. simpl in Hfind.
      assert (Hold : find_H k heap = Some v).
      { unfold find_H. eapply H_diff_keys_1; eauto. }
      rewrite Hnone in Hold. discriminate.
  - eauto using Phi_Allocates.
  - eauto using Phi_Allocates.
  - rewrite Hnone in Hfind. discriminate.
  - eauto using Phi_Allocates.
  - eauto using Phi_Allocates.
  - rewrite Hnone in Hfind. discriminate.
Qed.

Lemma Phi_Heap_StepsAux_alloc_source :
  forall phi heap phi' heap' n k v,
    (phi, heap) =a=>* (phi', heap', n) ->
    find_H k heap' = Some v ->
    find_H k heap = None ->
    Phi_Allocates k phi.
Proof.
  intros phi heap phi' heap' n k v HSteps.
  generalize dependent v.
  generalize dependent k.
  dependent induction HSteps; intros k v Hfind Hnone.
  - rewrite Hnone in Hfind. discriminate.
  - eapply Phi_Heap_Step_alloc_source; eauto.
  - destruct (find_H k heap'0) eqn:Hmid.
    + eapply IHHSteps1; try reflexivity; eauto.
    + assert (Halloc_mid : Phi_Allocates k phi'0).
      { eapply IHHSteps2; try reflexivity; eauto. }
      eapply Phi_Heap_StepsAux_preserves_allocates; eauto.
Qed.

Lemma Phi_Heap_Steps_alloc_source :
  forall phi heap phi' heap' k v,
    (phi, heap) ==>* (phi', heap') ->
    find_H k heap' = Some v ->
    find_H k heap = None ->
    Phi_Allocates k phi.
Proof.
  intros phi heap phi' heap' k v [n HSteps] Hfind Hnone.
  eapply Phi_Heap_StepsAux_alloc_source; eauto.
Qed.

Lemma Phi_Heap_Step_alloc_done :
  forall phi phi' heap heap' k,
    (phi, heap) ===> (phi', heap') ->
    Phi_Allocates k phi \/ (exists v, find_H k heap = Some v) ->
    Phi_Allocates k phi' \/ (exists v, find_H k heap' = Some v).
Proof.
  intros phi phi' heap heap' k HStep.
  dependent induction HStep; intros HPending.
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc; subst.
      right. exists v. unfold find_H, update_H. simpl. apply H_same_key_1.
    + right. eapply Phi_Heap_Step_preserves_domain with (v:=w);
        [constructor; eauto | exact Hfind].
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc.
    + right. exists w. assumption.
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc.
    + right. eapply Phi_Heap_Step_preserves_domain with (v:=w);
        [constructor; eauto | exact Hfind].
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc; subst.
      * destruct (IHHStep _ _ _ _ eq_refl eq_refl (or_introl H1)) as [HAlloc' | HDone].
        -- left. now apply PA_Seq_L.
        -- right. assumption.
      * left. now apply PA_Seq_R.
    + right. eapply Phi_Heap_Step_preserves_domain with (v:=w);
        [constructor; eauto | exact Hfind].
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc; subst.
      * inversion H1.
      * destruct (IHHStep _ _ _ _ eq_refl eq_refl (or_introl H1)) as [HAlloc' | HDone].
        -- left. now apply PA_Seq_R.
        -- right. assumption.
    + right. eapply Phi_Heap_Step_preserves_domain with (v:=w);
        [constructor; eauto | exact Hfind].
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc; subst; inversion H1.
    + right. exists w. assumption.
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc; subst.
      * destruct (IHHStep _ _ _ _ eq_refl eq_refl (or_introl H1)) as [HAlloc' | HDone].
        -- left. now apply PA_Par_L.
        -- right. assumption.
      * left. now apply PA_Par_R.
    + right. eapply Phi_Heap_Step_preserves_domain with (v:=w);
        [constructor; eauto | exact Hfind].
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc; subst.
      * left. now apply PA_Par_L.
      * destruct (IHHStep _ _ _ _ eq_refl eq_refl (or_introl H1)) as [HAlloc' | HDone].
        -- left. now apply PA_Par_R.
        -- right. assumption.
    + right. eapply Phi_Heap_Step_preserves_domain with (v:=w);
        [constructor; eauto | exact Hfind].
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc; subst; inversion H1.
    + right. exists w. assumption.
  Unshelve. all: eauto.
Qed.

Lemma Phi_Heap_StepsAux_alloc_done :
  forall phi heap phi' heap' n k,
    (phi, heap) =a=>* (phi', heap', n) ->
    Phi_Allocates k phi \/ (exists v, find_H k heap = Some v) ->
    Phi_Allocates k phi' \/ (exists v, find_H k heap' = Some v).
Proof.
  intros phi heap phi' heap' n k HSteps.
  dependent induction HSteps; intros HAlloc.
  - assumption.
  - eapply Phi_Heap_Step_alloc_done; eauto.
  - eapply IHHSteps2; try reflexivity.
    eapply IHHSteps1; try reflexivity; eauto.
Qed.

Lemma Phi_Heap_Steps_alloc_done :
  forall phi heap heap' k,
    (phi, heap) ==>* (Phi_Nil, heap') ->
    Phi_Allocates k phi ->
    exists v, find_H k heap' = Some v.
Proof.
  intros phi heap heap' k [n HSteps] HAlloc.
  destruct (Phi_Heap_StepsAux_alloc_done phi heap Phi_Nil heap' n k HSteps
              (or_introl HAlloc)) as [HNilAlloc | HDone].
  - exfalso. eapply Phi_Allocates_nil_false; eauto.
  - assumption.
Qed.
  
Lemma DisjointImpliesSomeOrNone:
  forall heap_1 heap_2,
    heap_1 ##ₘ heap_2 ->
    forall k v,
        (find_H k heap_1 = Some v -> find_H k heap_2 = None)
         /\ (find_H k heap_2 = Some v -> find_H k heap_1 = None).
Proof.
  intros.
  assert (H'' : forall i,
             heap_1 !! i = None ∨ heap_2 !! i = None).
  intro.
  eapply map_disjoint_alt. auto.
  destruct (H'' k).
  - split; intros.        
    unfold find_H in H1.
    replace (heap_1 !! k) with (None: option Val) in H1.
    inversion H1.
    + assumption.  
  -  split; intros.
     + assumption.
     + unfold find_H in H1.
      replace (heap_2 !! k) with (None: option Val) in H1.
      inversion H1.
Qed.


Lemma TcHeap_Extended_2:
  forall heap env rho ef1 ef2 ea1 ea2 v1 v2 ty1 ty2 acts_mu1 acts_mu2
         heap_mu1 heap_mu2 stty stty1 stty2 hp',
    heap_mu1 ∖ heap ##ₘ heap_mu2 ∖ heap ->
    (heap, env, rho, Mu_App ef1 ea1) ⇓ (heap_mu1, v1, acts_mu1) ->
    (heap, env, rho, Mu_App ef2 ea2) ⇓ (heap_mu2, v2, acts_mu2) ->
    (Phi_Par acts_mu1 acts_mu2, heap) ==>* (Phi_Nil, hp') ->
    TcPhi stty1 acts_mu1 ->
    TcPhi stty2 acts_mu2 ->
    TcVal (stty1, v1, subst_rho rho ty1) ->
    TcVal (stty2, v2, subst_rho rho ty2) ->
    TcHeap (heap, stty) ->
    (forall l t, find_ST l stty = Some t -> find_ST l stty1 = Some t) ->
    (forall l t, find_ST l stty = Some t -> find_ST l stty2 = Some t) ->
    TcHeap (heap_mu1, stty1) ->
    TcHeap (heap_mu2, stty2) ->
    TcHeap (hp', stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty)).
Proof.
  intros heap env rho ef1 ef2 ea1 ea2 v1 v2 ty1 ty2 acts_mu1 acts_mu2
    heap_mu1 heap_mu2 stty stty1 stty2 hp'
    HheapDisj Hstep1 Hstep2 Hpar HTcPhi1 HTcPhi2 _ _
    HTcHeap Hext1 Hext2 HTcHeap1 HTcHeap2.
  assert (HsttyDisj : stty1 ∖ stty ##ₘ stty2 ∖ stty)
    by (eapply djt_heap_implies_djt_stty; eauto).
  assert (Hsteps1 : (acts_mu1, heap) ==>* (Phi_Nil, heap_mu1))
    by (eapply BigStep_replays_trace; eauto).
  assert (Hsteps2 : (acts_mu2, heap) ==>* (Phi_Nil, heap_mu2))
    by (eapply BigStep_replays_trace; eauto).
  constructor.
  - intros k v HfindHp.
    destruct (Phi_Heap_Steps_lookup_source
                (Phi_Par acts_mu1 acts_mu2) heap Phi_Nil hp' k v Hpar HfindHp)
      as [HfindBase | Hupdate].
    + inversion HTcHeap as [? ? HHeapStore _ _]; subst.
      destruct (HHeapStore k v HfindBase) as [t HfindStty].
      exists t. eapply StoreTyping_Extended_Base; eauto.
    + inversion Hupdate; subst.
      * match goal with
        | H : Phi_Updates k v acts_mu1 |- _ =>
            destruct (HTcPhi1 k v H) as [t [HfindStty1 _]]
        end.
        exists t. eapply StoreTyping_Extended_Left; eauto.
      * match goal with
        | H : Phi_Updates k v acts_mu2 |- _ =>
            destruct (HTcPhi2 k v H) as [t [HfindStty2 _]]
        end.
        exists t. eapply StoreTyping_Extended_Right; eauto.
  - intros k t HfindStore.
    unfold find_ST in HfindStore.
    apply lookup_union_Some_raw in HfindStore.
    destruct HfindStore as [HfindBaseStore | [HbaseNone HfindDiffs]].
    + inversion HTcHeap as [? ? _ HStoreHeap _]; subst.
      destruct (HStoreHeap k t HfindBaseStore) as [v HfindHeap].
      eapply Phi_Heap_Steps_preserves_domain; eauto.
    + apply lookup_union_Some_raw in HfindDiffs.
      destruct HfindDiffs as [HfindDiff1 | [_ HfindDiff2]].
      * apply lookup_difference_Some in HfindDiff1.
        destruct HfindDiff1 as [HfindStty1 HfindBaseNone].
        inversion HTcHeap1 as [? ? _ HStoreHeap1 _]; subst.
        destruct (HStoreHeap1 k t HfindStty1) as [v HfindHeapMu1].
        assert (HfindHeapNone : find_H k heap = None).
        { eapply TcHeap_none_implies_none; eauto. }
        assert (Halloc : Phi_Allocates k acts_mu1).
        { eapply Phi_Heap_Steps_alloc_source; eauto. }
        eapply Phi_Heap_Steps_alloc_done; eauto.
        now apply PA_Par_L.
      * apply lookup_difference_Some in HfindDiff2.
        destruct HfindDiff2 as [HfindStty2 HfindBaseNone].
        inversion HTcHeap2 as [? ? _ HStoreHeap2 _]; subst.
        destruct (HStoreHeap2 k t HfindStty2) as [v HfindHeapMu2].
        assert (HfindHeapNone : find_H k heap = None).
        { eapply TcHeap_none_implies_none; eauto. }
        assert (Halloc : Phi_Allocates k acts_mu2).
        { eapply Phi_Heap_Steps_alloc_source; eauto. }
        eapply Phi_Heap_Steps_alloc_done; eauto.
        now apply PA_Par_R.
  - intros k v t HfindHp HfindStore.
    destruct (Phi_Heap_Steps_lookup_source
                (Phi_Par acts_mu1 acts_mu2) heap Phi_Nil hp' k v Hpar HfindHp)
      as [HfindBase | Hupdate].
    + inversion HTcHeap as [? ? HHeapStore _ HHeapVals]; subst.
      destruct (HHeapStore k v HfindBase) as [t0 HfindStty].
      assert (HfindStore0 :
                find_ST k (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty)) = Some t0)
        by (eapply StoreTyping_Extended_Base; eauto).
      assert (t = t0)
        by (eapply PairType_unique_type; eauto).
      subst.
      eapply ext_stores__val with (stty:=stty); eauto.
      intros l t' Hfind. eapply StoreTyping_Extended_Base; eauto.
    + inversion Hupdate; subst.
      * match goal with
        | H : Phi_Updates k v acts_mu1 |- _ =>
            destruct (HTcPhi1 k v H) as [t1 [HfindStty1 HTcVal1]]
        end.
        assert (HfindStore1 :
                  find_ST k (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty)) = Some t1)
          by (eapply StoreTyping_Extended_Left; eauto).
        assert (t = t1)
          by (eapply PairType_unique_type; eauto).
        subst.
        eapply ext_stores__val with (stty:=stty1); eauto.
        intros l t' Hfind. eapply StoreTyping_Extended_Left; eauto.
      * match goal with
        | H : Phi_Updates k v acts_mu2 |- _ =>
            destruct (HTcPhi2 k v H) as [t2 [HfindStty2 HTcVal2]]
        end.
        assert (HfindStore2 :
                  find_ST k (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty)) = Some t2)
          by (eapply StoreTyping_Extended_Right; eauto).
        assert (t = t2)
          by (eapply PairType_unique_type; eauto).
        subst.
        eapply ext_stores__val with (stty:=stty2); eauto.
        intros l t' Hfind. eapply StoreTyping_Extended_Right; eauto.
Qed.

      
Lemma subst_rho_eps_aux_1 :
 forall rho rho' n x e e1 sa sa',
   lc_type_eps e ->
   lc_type_sa sa' ->
   fold_subst_eps rho e1 = (fold_subst_eps rho' (closing_rgn_in_eps n x e)) ->
   fold_subst_sa rho sa = fold_subst_sa rho' (closing_rgn_in_sa n x sa') /\ e1 sa /\ e sa'.
Proof.
  intros rho rho' n x e e1 sa sa' Hlc _ _.
  exfalso.
  inversion Hlc as [eps HAll]; subst.
  destruct (HAll (SA_Alloc (Rgn_BVar true true 0))) as [_ HBad].
  inversion HBad; subst.
  match goal with
  | H : lc_type_rgn (Rgn_BVar _ _ _) |- _ => inversion H
  end.
Qed.


Lemma subst_rho_open_close_rgn :
  forall rho n w v' rho' r r0 x,
    lc_type_rgn r0 ->
    find_R w rho = Some v' ->
    fold_subst_rgn rho r = fold_subst_rgn rho' (closing_rgn_in_rgn n x r0) ->
    fold_subst_rgn rho' (opening_rgn_in_rgn n (Rgn_Const true true v')
                           (closing_rgn_in_rgn n x r0))
    = fold_subst_rgn rho (opening_rgn_in_rgn n (mk_rgn_type w) r).
Proof. 
  intros rho n w v' rho' r r0 x Hlc1 HF H.
  unfold Region_in_Type in r.
  unfold Region_in_Type in r0. 
  unfold Region_in_Expr in w.
  dependent induction r; dependent induction Hlc1; simpl in *.
  - repeat rewrite subst_rho_rgn_const in *. auto.
  - destruct (Ascii.ascii_dec r0 x); subst; simpl in *.
    + rewrite subst_rho_index in H. rewrite subst_rho_rgn_const in H. inversion H.
    + auto.
  - auto.
  - destruct (Ascii.ascii_dec r0 x); subst; simpl in *.
    + rewrite subst_rho_index in H.
      destruct (subst_rho_fvar_1 rho r) as [[v0 H0] | H0];
      rewrite H0 in H; inversion H.
    + auto.
  - rewrite subst_rho_index in H. rewrite subst_rho_rgn_const in H. inversion H.
  - destruct (Ascii.ascii_dec r x); subst; simpl in *.
    + repeat rewrite subst_rho_index in H. inversion H; subst.
      rewrite Nat.eqb_refl.
      rewrite subst_rho_rgn_const.
      dependent induction w; simpl.
      * inversion HF; subst.
        rewrite subst_rho_rgn_const.
        reflexivity.
      * inversion HF. symmetry.
        apply subst_rho_fvar_2. now simpl.
    + rewrite subst_rho_index in H.
      destruct (subst_rho_fvar_1 rho' r) as [[v H0] | H0];
      rewrite H0 in H; inversion H.
Qed.

Lemma subst_rho_open_close_sa:
  forall rho n w v' rho' sa sa1 x,
    lc_type_sa sa ->
    find_R w rho = Some v' ->
    fold_subst_sa rho sa1 = fold_subst_sa rho' (closing_rgn_in_sa n x sa) ->
    fold_subst_sa rho' (opening_rgn_in_sa n (Rgn_Const true true v')
                          (closing_rgn_in_sa n x sa)) =
    fold_subst_sa rho (opening_rgn_in_sa n (mk_rgn_type w) sa1).
Proof.
  intros rho n w v' rho' sa sa1 x Hlc HF H.
  unfold fold_subst_sa.
  inversion Hlc; subst; induction sa1;
  unfold fold_subst_sa in H; inversion H; simpl in *;
  erewrite subst_rho_open_close_rgn; eauto.
Qed.    

Lemma subst_rho_open_close_eps:
  forall rho n w v' rho' e e1 x,
    lc_type_eps e ->
    find_R w rho = Some v' ->
    fold_subst_eps rho e1 = fold_subst_eps rho' (closing_rgn_in_eps n x e) ->
    fold_subst_eps rho' (opening_rgn_in_eps n (Rgn_Const true true v')
                           (closing_rgn_in_eps n x e)) =
    fold_subst_eps rho (opening_rgn_in_eps n (mk_rgn_type w) e1).
Proof.
  intros rho n w v' rho' e e1 x  Hcl1 HF H. 
  apply Extensionality_Ensembles.  
  unfold Same_set, Included.
  split; intros; unfold In in *.
  - unfold fold_subst_eps.  unfold fold_subst_eps in H0. 
    unfold opening_rgn_in_eps, closing_rgn_in_eps.
    unfold opening_rgn_in_eps, closing_rgn_in_eps in H0.
    destruct H0 as [sa [[sa' [[sa'' [H2 H3]] H4]] H5]].
    rewrite <- H5. rewrite <- H4. rewrite <- H3.
    inversion Hcl1. destruct (H0 sa'').

    assert (fold_subst_sa rho sa = fold_subst_sa rho' (closing_rgn_in_sa n x sa'')
            /\ e1 sa /\ e sa'') 
      by (eapply subst_rho_eps_aux_1; eauto).

    assert(H' : fold_subst_sa rho' (opening_rgn_in_sa n (Rgn_Const true true v') 
                  (closing_rgn_in_sa n x sa'')) =  
                fold_subst_sa rho (opening_rgn_in_sa n (mk_rgn_type w) sa)) 
    by (apply subst_rho_open_close_sa; auto; intuition).
    rewrite H'. 
    exists (opening_rgn_in_sa n (mk_rgn_type w) sa).
    intuition.
    exists sa.
    split; [ assumption | reflexivity].
 - unfold fold_subst_eps.  unfold fold_subst_eps in H0. 
   unfold opening_rgn_in_eps, closing_rgn_in_eps.
   unfold opening_rgn_in_eps, closing_rgn_in_eps in H0.
   destruct H0 as [sa [[sa' [H1 H2]] H3]].
   rewrite <- H3. rewrite <- H2.    
   exists (opening_rgn_in_sa n (Rgn_Const true true v') (closing_rgn_in_sa n x sa)). 
   inversion Hcl1. destruct (H0 sa).
   split.  
   + exists (closing_rgn_in_sa n x sa).  split; [ | reflexivity].
     exists sa. split; [ | reflexivity].  
     apply subst_rho_eps_aux_1 with (sa := sa') (sa':=sa) in H; auto.
   + eapply subst_rho_open_close_sa; eauto. 
     apply subst_rho_eps_aux_1 with (sa := sa') (sa':=sa) in H; auto.
     destruct H as [A [B C]]; auto.
Qed.
   
Lemma subst_rho_open_close :
  forall rho w v' rho' x tyr0 tyr,
    lc_type tyr0 ->
    find_R w rho = Some v' ->
    subst_rho rho' (close_var x tyr0) = subst_rho rho tyr ->
    subst_rho rho' (open (mk_rgn_type (Rgn_Const true false v')) (close_var x tyr0)) =
    subst_rho rho (open (mk_rgn_type w) tyr).
Proof.
  unfold open, close_var.
  intros rho w v' rho' x tyr0 tyr Hcl1 HF.  
  generalize dependent 0.   
  generalize dependent tyr. generalize dependent tyr0. 
  induction tyr0; induction tyr; intros n;
  simpl;
  repeat (rewrite subst_rho_natural ||
                  rewrite subst_rho_boolean ||
                  rewrite subst_rho_unit ||
                  rewrite subst_rho_forallrgn ||
                  rewrite subst_rho_effect ||
                  rewrite subst_rho_pair
         );
  try (solve [intro Z; inversion Z | intro Y; reflexivity | intro X; assumption |
              intros; rewrite subst_rho_tyref in H; inversion H |
              intros; rewrite subst_rho_arrow in H; inversion H ]).
  - inversion Hcl1; subst. 
    intros. f_equal; inversion H.  
    + erewrite <- IHtyr0_1; eauto.
    + erewrite <- IHtyr0_2; eauto. 
  - intro. symmetry in H. rewrite  subst_rho_tyref in H.
    rewrite  subst_rho_tyref in H. inversion H as [ [HR1 HR2] ].
    repeat rewrite subst_rho_tyref. f_equal.
    + erewrite subst_rho_open_close_rgn; eauto. now inversion Hcl1.
    + erewrite IHtyr0; eauto. now inversion Hcl1. 
  - intro. symmetry in H. rewrite  subst_rho_arrow in H.
    rewrite  subst_rho_tyref in H. now inversion H.
  - intro.  rewrite  subst_rho_tyref in H. rewrite  subst_rho_arrow in H. now inversion H.
  - repeat rewrite subst_rho_arrow. intro Z. inversion Z.
    f_equal.
    + rewrite <- IHtyr0_1; auto. now inversion Hcl1.
    + apply subst_rho_open_close_eps; [ now inversion Hcl1 | assumption | now inversion Z].  
    + rewrite <- IHtyr0_2; auto. now inversion Hcl1.
    + apply subst_rho_open_close_eps; [ now inversion Hcl1 | assumption | now inversion Z].  
    + rewrite <- IHtyr0_3; auto. now inversion Hcl1.
  - repeat rewrite subst_rho_forallrgn.
    intro Z; inversion Z.
     f_equal.
    + apply subst_rho_open_close_eps; [ now inversion Hcl1 | assumption | now inversion Z].
    + rewrite <- IHtyr0; auto. now inversion Hcl1.
Qed.

Lemma ty_sound_var :   
  forall x v stty rho env ctxt t,
  TcEnv (stty, rho, env, ctxt) ->
  find_E x env = Some v -> find_T x ctxt = Some t -> 
  TcVal (stty, v, subst_rho rho t).
Proof.
  intros x v stty rho env ctxt t HTcEnv FindEnv FindCtxt. (* Hclosed. *)
  inversion_clear HTcEnv as [? ? ?  HBst HFwd HBack HTc].
  destruct (HFwd x v FindEnv) as [y FindEnv']. 
  rewrite FindEnv' in FindCtxt. inversion FindCtxt; subst. 
  eapply HTc; [eexact FindEnv | eexact FindEnv' ]. (*| assumption]. *)
Qed.
 
Lemma ty_sound_closure:  
  forall stty rgns env rho ctxt f x ec ee tyx tyc effc effe, 
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns)->
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns,  Mu f x ec ee, Ty_Arrow tyx effc tyc effe Ty_Effect,
        Empty_Static_Action) -> 
    TcVal (stty, Cls (env, rho,  Mu f x ec ee),
        subst_rho rho (Ty_Arrow tyx effc tyc effe Ty_Effect)).   
Proof.
  intros; econstructor; eauto.
Qed.

Lemma ty_sound_region_closure:
  forall stty rgns env rho ctxt x er tyr effr, 
    TcRho (rho, rgns) -> 
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns, Lambda x er, Ty_ForallRgn (close_var_eff x effr) (close_var x tyr),
        Empty_Static_Action) ->
    TcVal (stty, Cls (env, rho, Lambda x er),
        subst_rho rho (Ty_ForallRgn (close_var_eff x effr) (close_var x tyr))).
Proof.
  intros. econstructor; eauto.
Qed.  
  
Lemma weakening_trans :
   forall stty stty' stty'', 
     (forall (l : SigmaKey) (t : Tau),
        find_ST l stty = Some t -> find_ST l stty' = Some t) ->
     (forall (l : SigmaKey) (t : Tau),
        find_ST l stty' = Some t -> find_ST l stty'' = Some t) ->
     (forall (l : SigmaKey) (t : Tau),
        find_ST l stty = Some t -> find_ST l stty'' = Some t).
Proof.
  intros stty stty' stty'' Weak Weak'.
  intros l t ?. apply Weak'. now apply Weak. 
Qed.

Lemma bound_var_is_fresh :
  forall rho rgns  x,
    TcRho (rho, rgns) ->
    not_set_elem rgns x ->
    x ∉ dom rho.
Proof.
  intros rho rgns x H1 H2.
  inversion H1; subst.
  unfold not_set_elem in H2. unfold Ensembles.Complement in H2. 
  unfold not. intro.
  apply H2. apply H0.
  contradict H. apply not_elem_of_dom. assumption.
Qed.
 
Lemma update_inc:
  forall rgns ctxt x,
    TcInc (ctxt, rgns) ->
    TcInc (ctxt, set_union rgns (singleton_set x)).
Proof.
  intros.
  econstructor. inversion H; subst.
  intros. apply H1 in H0.
  unfold included, set_union, Included in *.
  intros. apply H0 in H2.
  now apply Union_introl.
Qed.

  

Lemma ty_sound_strong:
  forall e env rho hp hp' v dynamic_eff,
    (hp, env, rho, e) ⇓ (hp', v, dynamic_eff) ->
    forall stty ctxt rgns t static_eff,
      TcHeap (hp, stty) ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns)->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e, t, static_eff) ->
      exists stty',
        (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
         /\ TcHeap (hp', stty')
         /\ TcVal (stty', v, subst_rho rho t)
         /\ TcPhi stty' dynamic_eff.
Proof.
  intros e env rho hp hp'  v dynamic_eff D. 
  dynamic_cases (dependent induction D) Case;
  intros stty ctxt rgns t static_eff Hhp Hrho Hinc Henv Hexp; 
  inversion Hexp; subst.    
  Case "cnt n"%string.
    exists stty; split; [auto |]; split; [auto |]; split;
      [try rewrite subst_rho_natural; apply TC_Num | apply TcPhi_nil].
  Case "bool b".
    exists stty; split; [auto |]; split; [auto |]; split;
      [try rewrite subst_rho_boolean; apply TC_Bit | apply TcPhi_nil].
  Case "var x".
    exists stty; split; [auto |]; split; [auto |]; split;
      [eapply ty_sound_var; eassumption | apply TcPhi_nil].
  Case "mu_abs".
    exists stty; split; [auto |]; split; [auto |]; split;
      [eapply ty_sound_closure; try (solve [eassumption]); auto | apply TcPhi_nil].
  Case "rgn_abs".
    exists stty; split; [auto |]; split; [auto |]; split;
      [eapply ty_sound_region_closure; try (solve [eassumption]) | apply TcPhi_nil].
  Case "mu_app".
    edestruct IHD1 as [sttym [Weak1 [TcHeap1 [TcVal_mu TcPhi_mu]]]]; eauto. 
    edestruct IHD2 as [sttya [Weaka [TcHeapa [TcVal_arg TcPhi_arg]]]]; eauto.  
    eapply ext_stores__env; eauto.
    inversion TcVal_mu as [ | | | ? ? ? ? ? ? ? TcRho_rho' TcRho_Inc' TcEnv_env' TcExp_abs | | |] ; subst.    
    inversion TcExp_abs as [ | |  | ? ? ? ? ? ? ? ? ? ? ? ? ? TcExp_ec TcExp_ee | | | | | | | | | | | | | | | | | | | | | ]; subst.   
    rewrite <- H5 in TcVal_mu.   
    do 2 rewrite subst_rho_arrow in H5. inversion H5.  
    assert (SubstEq1: subst_rho rho' tyx = subst_rho rho tya) by assumption. 
    assert (SubstEq2: subst_rho rho' tyc = subst_rho rho t) by assumption. 
    rewrite <- SubstEq1 in TcVal_arg.
    unfold update_rec_E, update_rec_T in *.     
    edestruct IHD3 with (ctxt:=update_T (x, tyx)
                                 (update_T (f, Ty_Arrow tyx effc0 tyc effe0 Ty_Effect) ctxt0))
      as [sttyb [Weakb [TcHeapb [TcVal_res TcPhi_res]]]]; eauto. simpl in *.
    SCase "TcInc".
    {apply ExtendedTcInv_2. 
     - assumption.
     - inversion_clear TcRho_Inc' as [? ? HInc].
       now apply HInc in H1.
     - inversion_clear TcRho_Inc' as [? ? HInc].
       now apply HInc in H2.  }
    SCase "TcEnv".
      apply update_env. apply update_env. eapply ext_stores__env; eauto.  
      eapply ext_stores__val; eauto. eassumption.
    SCase "TcHeap".
      exists sttyb. split.
      { intros l t' Hfind. apply Weakb. apply Weaka. now apply Weak1. }
      split; [assumption |].
      split; [assumption |].
      assert (HTcPhi_fun_arg : TcPhi sttyb (Phi_Seq facts aacts)).
      { apply TcPhi_seq;
        [ eapply TcPhi_weaken with (stty:=sttym);
          [intros l t' Hfind; apply Weakb; now apply Weaka | exact TcPhi_mu]
        | eapply TcPhi_weaken with (stty:=sttya);
          [exact Weakb | exact TcPhi_arg] ]. }
      apply TcPhi_seq; assumption.
    SCase "TcVal".
      edestruct IHD1 as [sttyl [Weak1 [TcHeap1 [TcVal_lam TcPhi_lam]]]]; eauto. 
      inversion TcVal_lam as  [ | | | ? ? ? ? ? ? ?  TcRho_rho' TcInc'  TcEnv_env' TcExp_lam | | |]; subst.   
      inversion TcExp_lam as [ | | | | ? ? ? ? ? ? ? ? ? TcExp_eb | | | | | | | | | | | | | | | | | | | |  ]; subst.   
      { edestruct IHD2 with (rgns:=set_union rgns0 (singleton_set x))
        as [sttyr [Weak2 [TcHeap2 [TcVal_res TcPhi_res]]]]; eauto using update_env, ext_stores__env.
        - { apply update_rho; [ assumption | assumption]. }
        - apply update_inc. assumption.
        - eapply extended_rho; eauto.
        - exists sttyr. split.
          { intros l t' Hfind. apply Weak2. now apply Weak1. }
          split; [assumption |].
          split.
          + rewrite subst_rho_forallrgn in H5.
            rewrite subst_rho_forallrgn in H5.
            inversion H5.  
            unfold update_R in TcVal_res. 
            simpl in TcVal_res. rewrite subst_add_comm in TcVal_res.
            * unfold subst_in_type in TcVal_res.
              rewrite SUBST_AS_CLOSE_OPEN in TcVal_res; auto.
              erewrite subst_rho_open_close in TcVal_res; eauto.
            * eapply map_to_list_unique with (m:=<[x:=v']> rho'); eauto.
            * apply not_elem_of_dom.
              eapply bound_var_is_fresh; eauto.
          + apply TcPhi_seq.
            * eapply TcPhi_weaken with (stty:=sttyl);
                [exact Weak2 | exact TcPhi_lam].
            * exact TcPhi_res. }
  Case "eff_app". 
    edestruct IHD1 as [sttym [Weak1 [TcHeap1 [TcVal_mu TcPhi_mu]]]]; eauto.
    edestruct IHD2 as [sttya [Weaka [TcHeapa [TcVal_arg TcPhi_arg]]]]; eauto using ext_stores__env.
    inversion TcVal_mu as  [ | | | ? ? ? ? ? ? ? TcRho_rho' TcInc' TcEnv_env' TcExp_abs | | |]; subst. 
    inversion TcExp_abs as [ | | | | ? ? ? ? ? ? ? ? ? TcExp_eb | | | | | | | | | | | | | | | | | | | |  ]; subst. 
    edestruct IHD3 with (ctxt:=update_T (x, tyx)
                                 (update_T (f, Ty_Arrow tyx effc0 tyc0 effe0 Ty_Effect) ctxt0))
      as [sttyb [Weakb [TcHeapb [TcVal_res TcPhi_res]]]]; eauto. simpl in *.
    SCase "Extended Inc". 
    {apply ExtendedTcInv_2. 
     - assumption.
     - inversion_clear TcInc' as [? ? HInc].
       now apply HInc in H0.
     - inversion_clear TcInc' as [? ? HInc].
       now apply HInc in H1.  }
    SCase "Extended Env". 
      apply update_env. 
      SSCase "TcEnv". 
      { apply update_env. 
        - eapply ext_stores__env; eauto.
        - rewrite <- H4 in TcVal_mu.  eapply ext_stores__val; eauto. }
      SSCase "TcVal".
        do 2 rewrite subst_rho_arrow in H4.
        inversion H4. 
        assert (SubstEq: subst_rho rho' tyx = subst_rho rho tya) by assumption.
        rewrite <- SubstEq in TcVal_arg.  eassumption. 
        exists sttyb. split.
        { intros l t' Hfind. apply Weakb. apply Weaka. now apply Weak1. }
        split; [assumption |].
        split.
        { rewrite subst_rho_effect. rewrite subst_rho_effect in TcVal_res.
          assumption. }
        assert (HTcPhi_fun_arg : TcPhi sttyb (Phi_Seq facts aacts)).
        { apply TcPhi_seq;
          [ eapply TcPhi_weaken with (stty:=sttym);
            [intros l t' Hfind; apply Weakb; now apply Weaka | exact TcPhi_mu]
          | eapply TcPhi_weaken with (stty:=sttya);
            [exact Weakb | exact TcPhi_arg] ]. }
        apply TcPhi_seq; assumption.
  Case "par_pair".
    edestruct IHD3 as [sttym [Weak1 [TcHeap1 [TcVal_app1 TcPhi_app1]]]]; eauto.  
    edestruct IHD4 as [sttya [Weaka [TcHeapa [TcVal_app2 TcPhi_app2]]]]; eauto. 
    assert (exists stty' : Sigma,
           (forall (l : SigmaKey) (t' : Tau),
            find_ST l stty = Some t' -> find_ST l stty' = Some t') /\
             TcHeap (heap_eff1, stty') /\
             TcVal (stty', Eff theta1, subst_rho rho ty3) /\
             TcPhi stty' acts_eff1)
      as HTyped3.
    eapply IHD1; eauto.
    assert (exists stty' : Sigma,
           (forall (l : SigmaKey) (t' : Tau),
            find_ST l stty = Some t' -> find_ST l stty' = Some t') /\
             TcHeap (heap_eff2, stty') /\
             TcVal (stty', Eff theta2, subst_rho rho ty4) /\
             TcPhi stty' acts_eff2)
      as HTyped4.
    eapply IHD2; eauto.
    assert (exists stty' : Sigma,
           (forall (l : SigmaKey) (t' : Tau),
            find_ST l stty = Some t' -> find_ST l stty' = Some t') /\
             TcHeap (heap_mu1, stty') /\
             TcVal (stty', v1, subst_rho rho ty1) /\
             TcPhi stty' acts_mu1)
      as HTyped1.
    eapply IHD3; eauto.
    assert (exists stty' : Sigma,
           (forall (l : SigmaKey) (t' : Tau),
            find_ST l stty = Some t' -> find_ST l stty' = Some t') /\
             TcHeap (heap_mu2, stty') /\
             TcVal (stty', v2, subst_rho rho ty2) /\
             TcPhi stty' acts_mu2)
      as HTyped2.
    eapply IHD4; eauto.
    destruct HTyped1 as[ stty1 [HA1  [HA2 [HA3 HA4]]]].
    destruct HTyped2 as[ stty2 [HB1  [HB2 [HB3 HB4]]]].
    destruct HTyped3 as[ stty3 [HC1  [HC2 [HC3 HC4]]]].
    destruct HTyped4 as[ stty4 [HD1  [HD2 [HD3 HD4]]]].  
    { exists (stty ∪ ((stty1 ∖ stty) ∪ (stty2 ∖ stty))).
      destruct H0 as [HEff1 HEff2].
      split.  
      + assert (stty1 ∖ stty ##ₘ stty2 ∖ stty)
          by (eapply djt_heap_implies_djt_stty; eauto).
        intros.
        assert (find_ST l stty1 = Some t') by (apply HA1; auto).
        assert (find_ST l stty2 = Some t') by (apply HB1; auto).
        intros. eapply StoreTyping_Union_2; eauto.
      + split.
          * eapply TcHeap_Extended_2
              with (acts_mu1:=acts_mu1) (acts_mu2:=acts_mu2); eauto.
        * split.
          -- eapply TcValExtended_2; eauto.
             eapply djt_heap_implies_djt_stty; eauto.
          -- assert (HsttyDisj : stty1 ∖ stty ##ₘ stty2 ∖ stty)
               by (eapply djt_heap_implies_djt_stty; eauto).
             assert (HCto :
                       forall l t',
                         find_ST l stty3 = Some t' ->
                         find_ST l (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty)) = Some t').
             { intros l t' Hfind3.
               inversion HC2 as [? ? _ HStoreHeap3 _]; subst.
               destruct (HStoreHeap3 l t' Hfind3) as [v HfindEff].
               unfold equiv, heap_equiv in HEff1; subst heap_eff1.
               inversion Hhp as [? ? HHeapStore _ _]; subst.
               destruct (HHeapStore l v HfindEff) as [t0 HfindBase].
               assert (Hfind3base : find_ST l stty3 = Some t0)
                 by (apply HC1; assumption).
               assert (t' = t0) by (eapply PairType_unique_type; eauto).
               subst. eapply StoreTyping_Extended_Base; eauto. }
             assert (HDto :
                       forall l t',
                         find_ST l stty4 = Some t' ->
                         find_ST l (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty)) = Some t').
             { intros l t' Hfind4.
               inversion HD2 as [? ? _ HStoreHeap4 _]; subst.
               destruct (HStoreHeap4 l t' Hfind4) as [v HfindEff].
               unfold equiv, heap_equiv in HEff2; subst heap_eff2.
               inversion Hhp as [? ? HHeapStore _ _]; subst.
               destruct (HHeapStore l v HfindEff) as [t0 HfindBase].
               assert (Hfind4base : find_ST l stty4 = Some t0)
                 by (apply HD1; assumption).
               assert (t' = t0) by (eapply PairType_unique_type; eauto).
               subst. eapply StoreTyping_Extended_Base; eauto. }
             assert (HTcPhi_eff :
                       TcPhi (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty))
                         (Phi_Par acts_eff1 acts_eff2)).
             { apply TcPhi_par.
               - eapply TcPhi_weaken with (stty:=stty3); eauto.
               - eapply TcPhi_weaken with (stty:=stty4); eauto. }
             assert (HTcPhi_mu :
                       TcPhi (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty))
                         (Phi_Par acts_mu1 acts_mu2)).
             { apply TcPhi_par.
               - eapply TcPhi_weaken with (stty:=stty1); eauto.
                 intros l t' Hfind. eapply StoreTyping_Extended_Left; eauto.
               - eapply TcPhi_weaken with (stty:=stty2); eauto.
                 intros l t' Hfind. eapply StoreTyping_Extended_Right; eauto. }
             apply TcPhi_seq; assumption.
    }
  Case "cond_true".
    edestruct IHD1 as [sttyb [Weakb [TcHeapvb [TcVal_e0 TcPhi_e0]]]]; eauto. 
    edestruct IHD2 as [stty1 [Weak1 [TcHeapv1 [TcVal_e1 TcPhi_e1]]]]; 
      eauto using ext_stores__env.
    exists stty1. split.
    { intros l t' Hfind. apply Weak1. now apply Weakb. }
    split; [assumption |].
    split; [assumption |].
    apply TcPhi_seq; [eapply TcPhi_weaken; eauto | assumption].
  Case "cond_false".
    edestruct IHD1 as [sttyb [Weakb [TcHeapvb [TcVal_e0 TcPhi_e0]]]]; eauto. 
    edestruct IHD2 as [stty2 [Weak2 [TcHeapv2 [TcVal_e2 TcPhi_e2]]]]; 
      eauto using ext_stores__env.
    exists stty2. split.
    { intros l t' Hfind. apply Weak2. now apply Weakb. }
    split; [assumption |].
    split; [assumption |].
    apply TcPhi_seq; [eapply TcPhi_weaken; eauto | assumption].
  Case "new_ref e".
    edestruct IHD with (stty := stty)
                      (ctxt := ctxt)
                      (rgns := rgns)  
                      (t := t0)
                      (static_eff := veff)
      as [sttyv [Weakv [TcHeapv [TcVal_v TcPhi_v]]]]; eauto.
    assert (find_H (r, allocate_H heap' r) heap' = None)
      by (apply allocate_H_fresh).
    assert (HfreshST : find_ST (r, allocate_H heap' r) sttyv = None).
    { destruct (find_ST (r, allocate_H heap' r) sttyv) as [t |] eqn:Hfind; auto.
      inversion_clear TcHeapv as [? ? ? STfind_Hfind ?].
      destruct (STfind_Hfind (r, allocate_H heap' r) t Hfind) as [? ex].
      rewrite H0 in ex. discriminate. }
    assert (Weakv_update :
              forall k' t',
                find_ST k' sttyv = Some t' ->
                find_ST k'
                  (update_ST (r, allocate_H heap' r)
                     (subst_rho rho t0) sttyv) = Some t').
    { intros k' t' STfind.
      destruct (decide (k' = (r, allocate_H heap' r))) as [Heq | Hneq].
      - subst. rewrite HfreshST in STfind. discriminate.
      - apply G_diff_keys_2;
          [ intro Heq; apply Hneq; now symmetry | assumption ]. }
    exists (update_ST (r, allocate_H heap' r) (subst_rho rho t0) sttyv);
      split; [ | split; [ | split]].
    SCase "Extended stores".
      intros k' t' STfind. apply Weakv_update. now apply Weakv.
    SCase "Heap typeness".
      apply H_update_heap_fresh; eauto.
    SCase "Loc is well-typed".
      simpl in H; inversion H; subst. 
      rewrite subst_rho_tyref. unfold mk_rgn_type. rewrite subst_rho_rgn_const.
      econstructor;
        [ unfold find_ST, update_ST; apply lookup_insert
        | intro; eapply TcVal_implies_closed in TcVal_v; eauto ].
    SCase "Trace is well-typed".
      apply TcPhi_seq;
        [ eapply TcPhi_weaken; eauto
        | unfold TcPhi; intros k' v' HUpdate;
          inversion HUpdate; subst;
          exists (subst_rho rho t0); split;
          [ unfold find_ST, update_ST; apply lookup_insert
          | eapply ext_stores__val; eauto ] ].
  Case "get_ref e".
    edestruct IHD with (hp' := hp')
                      (v := Loc (Rgn_Const true false s) l) 
                      (stty := stty)
                      (rgns := rgns)
                      (ctxt := ctxt)
                      (t := Ty_Ref (mk_rgn_type ((Rgn_Const true false s))) t)
                      (static_eff := aeff)
                      (dynamic_eff := aacts)
    as [sttyv [Weakv [TcHeapv [TcVal_v TcPhi_v]]]]; eauto.
    exists sttyv. split; [ | split; [ | split]].
    SCase "HeapTyping extends".
      apply Weakv.
    SCase "Heap is well typed".
      apply TcHeapv.
    SCase "Value is well-typed".
      inversion_clear TcHeapv as [? ? ? ? HeapTcVal]. eapply HeapTcVal; eauto. 
      inversion TcVal_v; subst; simpl in H; inversion H; subst.
      rewrite subst_rho_tyref in H7. inversion H7. subst.
      assumption.
    SCase "Trace is well-typed".
      apply TcPhi_seq;
        [ assumption
        | unfold TcPhi; intros k' v' HUpdate; inversion HUpdate ].
  Case "set_ref e1 e2".
    edestruct IHD1 with (hp' := heap')
                       (v := Loc (Rgn_Const true false s) l) 
                       (stty := stty)
                       (ctxt := ctxt)
                       (rgns := rgns)
                       (t := Ty_Ref (mk_rgn_type ((Rgn_Const true false s))) t0)
                       (static_eff := aeff)
                       (dynamic_eff := aacts)
       as [sttya [Weaka [TcHeapa [TcVal_a TcPhi_a]]]]; eauto.
    edestruct IHD2 with (stty := sttya)
                       (ctxt := ctxt)
                       (rgns := rgns)  
                       (t := t0)
                       (static_eff := veff)
      as [sttyv [Weakv [TcHeapv [TcVal_v TcPhi_v]]]]; eauto using ext_stores__env.
    assert (HwriteST : find_ST (r, l) sttyv = Some (subst_rho rho t0)).
    { apply Weakv. inversion TcVal_a; subst.
      simpl in H0; inversion H0; subst.
      match goal with
      | Hty : _ = subst_rho _ (Ty_Ref _ _) |- _ =>
          rewrite subst_rho_tyref in Hty; inversion Hty; subst
      | Hty : subst_rho _ (Ty_Ref _ _) = _ |- _ =>
          rewrite subst_rho_tyref in Hty; inversion Hty; subst
      end.
      assumption. }
    exists sttyv. split; [ | split; [ | split]].
    SCase "HeapTyping extends".
      eapply weakening_trans; eauto.
    SCase "New heap is well typed".
      apply H_update_heap_exists with (t:= subst_rho rho t0).   
      { assumption. }
      { assumption. }
      { assumption. }
    SCase "Result value is well-typed".
      rewrite subst_rho_unit. constructor.
    SCase "Trace is well-typed".
      assert (HTcPhi_av : TcPhi sttyv (Phi_Seq aacts vacts)).
      { apply TcPhi_seq;
          [ eapply TcPhi_weaken with (stty:=sttya); eauto
          | exact TcPhi_v ]. }
      apply TcPhi_seq;
        [ exact HTcPhi_av
        | unfold TcPhi; intros k' v' HUpdate; inversion HUpdate; subst;
          exists (subst_rho rho t0); split; [ exact HwriteST | exact TcVal_v ] ].
  Case "nat_plus x y".
    edestruct IHD1 as [sttyx [Weakx [TcHeapvx [TcVal_x TcPhi_x]]]]; eauto. 
    edestruct IHD2 as [sttyy [Weaky [TcHeapvy [TcVal_y TcPhi_y]]]]; 
      eauto using ext_stores__env. 
    exists sttyy. split.
    { intros l t' Hfind. apply Weaky. now apply Weakx. }
    split; [assumption |].
    split; [rewrite subst_rho_natural; constructor |].
    apply TcPhi_seq;
      [ eapply TcPhi_weaken with (stty:=sttyx); eauto
      | assumption ].
  Case "nat_minus x y".
    edestruct IHD1 as [sttyx [Weakx [TcHeapvx [TcVal_x TcPhi_x]]]]; eauto. 
    edestruct IHD2 as [sttyy [Weaky [TcHeapvy [TcVal_y TcPhi_y]]]]; 
      eauto using ext_stores__env.
    exists sttyy. split.
    { intros l t' Hfind. apply Weaky. now apply Weakx. }
    split; [assumption |].
    split; [rewrite subst_rho_natural; constructor |].
    apply TcPhi_seq;
      [ eapply TcPhi_weaken with (stty:=sttyx); eauto
      | assumption ].
  Case "nat_times x y".
    edestruct IHD1 as [sttyx [Weakx [TcHeapvx [TcVal_x TcPhi_x]]]]; eauto. 
    edestruct IHD2 as [sttyy [Weaky [TcHeapvy [TcVal_y TcPhi_y]]]]; 
      eauto using ext_stores__env.
    exists sttyy. split.
    { intros l t' Hfind. apply Weaky. now apply Weakx. }
    split; [assumption |].
    split; [rewrite subst_rho_natural; constructor |].
    apply TcPhi_seq;
      [ eapply TcPhi_weaken with (stty:=sttyx); eauto
      | assumption ].
  Case "bool_eq x y".
    edestruct IHD1 as [sttyx [Weakx [TcHeapvx [TcVal_x TcPhi_x]]]]; eauto. 
    edestruct IHD2 as [sttyy [Weaky [TcHeapvy [TcVal_y TcPhi_y]]]]; 
      eauto using ext_stores__env.
    exists sttyy. split.
    { intros l t' Hfind. apply Weaky. now apply Weakx. }
    split; [assumption |].
    split; [rewrite subst_rho_boolean; constructor |].
    apply TcPhi_seq;
      [ eapply TcPhi_weaken with (stty:=sttyx); eauto
      | assumption ].
  Case "alloc_abs".
    exists stty; split; [auto |]; split; [auto |]; split;
      [rewrite subst_rho_effect; constructor | subst; apply TcPhi_nil].
  Case "read_abs".
    exists stty; split; [auto |]; split; [auto |]; split;
      [rewrite subst_rho_effect; constructor | subst; apply TcPhi_nil].
  Case "write_abs".
    exists stty; split; [auto |]; split; [auto |]; split;
      [rewrite subst_rho_effect; constructor | subst; apply TcPhi_nil].
  Case "read_conc".
    exists stty. split; [auto |].
    split.
    { assert (hp = hp') by (eapply EmptyTracePreservesHeap_1; eauto; reflexivity);
      now subst. }
    split; [rewrite subst_rho_effect; constructor | subst; apply TcPhi_nil].
  Case "write_conc".
    exists stty. split; [auto |].
    split.
    { assert (hp = hp') by (eapply EmptyTracePreservesHeap_1; eauto; reflexivity);
      now subst. }
    split; [rewrite subst_rho_effect; constructor | subst; apply TcPhi_nil].
  Case "eff_concat".
    edestruct IHD1 as [sttya [Weaka [TcHeapa [TcVal_a TcPhi_a]]]]; eauto.
    edestruct IHD2 with (stty := sttya)
      as [sttyb [Weakb [TcHeapb [TcVal_b TcPhi_b]]]];
      eauto using ext_stores__env.
    exists sttyb. split.
    { intros l t' Hfind. apply Weakb. now apply Weaka. }
    split; [assumption |].
    split; [rewrite subst_rho_effect; constructor |].
    apply TcPhi_seq;
      [ eapply TcPhi_weaken with (stty:=sttya); eauto
      | assumption ].
  Case "eff_top".
    exists stty; split; [auto |]; split; [auto |]; split;
      [rewrite subst_rho_effect; constructor | subst; apply TcPhi_nil].
  Case "eff_empty".
    exists stty; split; [auto |]; split; [auto |]; split;
      [rewrite subst_rho_effect; constructor | subst; apply TcPhi_nil].
Qed.

Lemma ty_sound:
  forall e env rho hp hp' v dynamic_eff,
    (hp, env, rho, e) ⇓ (hp', v, dynamic_eff) ->
    forall stty ctxt rgns t static_eff,
      TcHeap (hp, stty) ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns)->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e, t, static_eff) ->
      exists stty',
        (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
         /\ TcHeap (hp', stty')
         /\ TcVal (stty', v, subst_rho rho t).
Proof.
  intros e env rho hp hp' v dynamic_eff HD
         stty ctxt rgns t static_eff Hhp Hrho Hinc Henv Hexp.
  destruct (ty_sound_strong e env rho hp hp' v dynamic_eff HD
              stty ctxt rgns t static_eff Hhp Hrho Hinc Henv Hexp)
    as [stty' [Hweak [HTcHeap [HTcVal _]]]].
  exists stty'. intuition.
Qed.

End TypeSoundness.
