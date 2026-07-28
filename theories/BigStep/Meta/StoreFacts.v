From stdpp Require Import gmap.
From stdpp Require Import fin_maps.
From stdpp Require Import list.

Require Import theories.BigStep.Typing.TypeSyntax.
Require Import theories.BigStep.Typing.TypingJudgments.
Require Import theories.BigStep.Core.Values.
Require Import theories.BigStep.Meta.MapFacts.
Require Import theories.BigStep.Meta.RegionFacts.
Require Import theories.BigStep.Meta.TypingWeakeningFacts.

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

Definition StoreExtends (stty stty' : Sigma) : Prop :=
  forall k t,
    find_ST k stty = Some t ->
    find_ST k stty' = Some t.

Lemma StoreExtends_refl :
  forall stty,
    StoreExtends stty stty.
Proof.
  intros stty k t HFind.
  exact HFind.
Qed.

Lemma StoreExtends_trans :
  forall stty1 stty2 stty3,
    StoreExtends stty1 stty2 ->
    StoreExtends stty2 stty3 ->
    StoreExtends stty1 stty3.
Proof.
  intros stty1 stty2 stty3 HExt12 HExt23 k t HFind.
  apply HExt23.
  now apply HExt12.
Qed.

Lemma StoreExtends_update_fresh :
  forall stty k t,
    find_ST k stty = None ->
    StoreExtends stty (update_ST k t stty).
Proof.
  intros stty k t HFresh k0 t0 HFind.
  unfold StoreExtends, find_ST, update_ST in *.
  destruct (decide (k0 = k)); subst.
  - rewrite HFresh in HFind. discriminate.
  - eapply G_diff_keys_2; eauto.
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

Lemma TcVal_Extended_Left :
  forall stty stty1 stty2 v t,
    stty1 ∖ stty ##ₘ stty2 ∖ stty ->
    StoreExtends stty stty1 ->
    TcVal (stty1, v, t) ->
    TcVal (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty), v, t).
Proof.
  intros stty stty1 stty2 v t Hdisj Hext HTcVal.
  eapply (ext_stores__val stty1); [| exact HTcVal].
  intros l t' Hfind.
  eapply StoreTyping_Extended_Left; eauto.
Qed.

Lemma TcVal_Extended_Right :
  forall stty stty1 stty2 v t,
    stty1 ∖ stty ##ₘ stty2 ∖ stty ->
    StoreExtends stty stty2 ->
    TcVal (stty2, v, t) ->
    TcVal (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty), v, t).
Proof.
  intros stty stty1 stty2 v t Hdisj Hext HTcVal.
  eapply (ext_stores__val stty2); [| exact HTcVal].
  intros l t' Hfind.
  eapply StoreTyping_Extended_Right; eauto.
Qed.

Lemma TcEnv_Extended_Left :
  forall stty stty1 stty2 rho env ctxt,
    stty1 ∖ stty ##ₘ stty2 ∖ stty ->
    StoreExtends stty stty1 ->
    TcEnv (stty1, rho, env, ctxt) ->
    TcEnv (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty), rho, env, ctxt).
Proof.
  intros stty stty1 stty2 rho env ctxt Hdisj Hext HTcEnv.
  eapply (ext_stores__env stty1); [| exact HTcEnv].
  intros l t' Hfind.
  eapply StoreTyping_Extended_Left; eauto.
Qed.

Lemma TcEnv_Extended_Right :
  forall stty stty1 stty2 rho env ctxt,
    stty1 ∖ stty ##ₘ stty2 ∖ stty ->
    StoreExtends stty stty2 ->
    TcEnv (stty2, rho, env, ctxt) ->
    TcEnv (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty), rho, env, ctxt).
Proof.
  intros stty stty1 stty2 rho env ctxt Hdisj Hext HTcEnv.
  eapply (ext_stores__env stty2); [| exact HTcEnv].
  intros l t' Hfind.
  eapply StoreTyping_Extended_Right; eauto.
Qed.
