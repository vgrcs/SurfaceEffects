From stdpp Require Import gmap.
Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Definitions.StaticActions.
Require Import Definitions.ComputedActions.
Require Import Definitions.Regions.
Require Import Definitions.GTypes.
Require Import Definitions.Keys.
Require Import Definitions.Values.
Require Import Definitions.Axioms.
Require Import Proofs.RegionFacts.
Require Import Proofs.EffectFacts.
Require Import Proofs.LocallyNameless.
Require Import Definitions.GHeap.

Definition find_type_ext_stores_def  := 
   forall stty stty' l (t' : Tau),
      find_ST l stty = Some t' ->
      find_ST l stty' = Some t' -> 
      find_ST l stty =  find_ST l stty'.

Lemma find_type_ext_stores: find_type_ext_stores_def.  
Proof.
  intros stty stty' l t' H1 H2.
  rewrite <- H1 in H2.
  symmetry in H2.
  assumption.
Qed.


Lemma ST_same_key_1:
  forall (l : SigmaKey) (ty : Tau) (stty : Sigma), 
    find_ST l (update_ST l ty stty) = Some ty.
Proof.
  intros.
  unfold find_ST, update_ST. apply lookup_insert.
Qed. 

Lemma ST_diff_keys_1:
  forall  a b v v' (stty : gmap SigmaKey Tau),
    a <> b ->
    <[b:=v]> stty !! a = Some v' ->
    stty !! a = Some v'.
Proof.
  intros a b v v' e Hneq Hfind.
  unfold find_ST, update_ST in *.
  rewrite lookup_insert_Some in Hfind.
  destruct Hfind as [[Ha Hb] | [Hc Hd]].
  - contradict Hneq. auto.
  - assumption.
Qed.


Lemma H_diff_keys_2:
  forall a b v v' (heap : gmap HeapKey HeapVal),   
    b <> a ->
    heap !! a = Some v' ->
    (<[ b:=v ]> heap) !! a = Some v'.
Proof.
  intros a b v v' e Hneq Hfind.
  rewrite lookup_insert_Some.
  right. split; [assumption | assumption].
Qed.


Lemma ST_diff_key_2:
  forall a b v v' (stty : gmap SigmaKey Tau),
    b <> a ->
    stty !! a = Some v' ->
    (<[b:=v]> stty) !! a = Some v'.
Proof.
  intros.
  unfold find_ST, update_ST in *.
  rewrite lookup_insert_Some.
  right. split; [assumption | assumption].
Qed.


Lemma ST_update_same_type:
  forall stty l0 t t0,
  find_ST l0 (update_ST l0 t stty) = Some t0 -> 
  t = t0.
Proof.
  intros stty l0 t t0 H. 
  rewrite ST_same_key_1 in H. inversion H. reflexivity.
Qed.



Definition get_store_typing_val {A B:Type} (p : Sigma * A * B) : Sigma   
  := fst (fst p).

Definition get_store_typing_env {A B C:Type} (p : Sigma * A * B * C) : Sigma   
  := fst (fst (fst p)).

Definition mk_TcVal_ext_store_ty (p : Sigma * Val * Tau) (stty' : Sigma)
  := TcVal (stty', snd (fst p), snd p).

Definition mk_TcEnv_ext_store_ty (p : Sigma * Rho * Env * Gamma) (stty' : Sigma)
  := TcEnv (stty', snd (fst (fst p)), snd (fst p), snd p).

Lemma ext_stores__exp__bt__aux:
  (forall p, TcExp p ->
             match p with (ctxt, rgns, e, t, eff) => 
                TcExp (ctxt, rgns, e, t, eff)
             end)
    /\
  (forall p, BackTriangle p ->
             match p with (ctxt, rgns, rho, ec, ee) => 
                BackTriangle (ctxt, rgns, rho, ec, ee)
             end)
   /\  
  (forall p,
        TcVal p ->        
        forall stty stty',
        (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t') -> 
        get_store_typing_val p = stty -> mk_TcVal_ext_store_ty p stty') 
  /\
     (forall p,
        TcEnv p ->           
        forall stty stty',
        (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t') -> 
        get_store_typing_env p = stty -> mk_TcEnv_ext_store_ty p stty').
Proof.
  apply tc__xind; try (solve [econstructor;eauto] ).
  - intros. 
    unfold mk_TcVal_ext_store_ty, 
           mk_TcEnv_ext_store_ty, 
           get_store_typing_val, 
           get_store_typing_env in *; simpl in *.
    subst.
    econstructor; eauto.
  - intros.
     unfold mk_TcVal_ext_store_ty, 
           mk_TcEnv_ext_store_ty, 
           get_store_typing_val, 
           get_store_typing_env in *; simpl in *.
    subst.
    econstructor; eauto.
  - intros.
    unfold mk_TcVal_ext_store_ty, 
           mk_TcEnv_ext_store_ty, 
           get_store_typing_val, 
           get_store_typing_env in *; simpl in *.
    subst.
    econstructor; eauto.
  - intros.
    unfold mk_TcVal_ext_store_ty, 
           mk_TcEnv_ext_store_ty, 
           get_store_typing_val, 
           get_store_typing_env in *; simpl in *.
    subst.
    econstructor; eauto.
Qed.

Lemma ext_stores__val:
   forall stty stty',
     (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t') -> 
     (forall v t, TcVal (stty, v, t) -> 
      TcVal (stty', v, t)).
Proof.
  intros.
  eapply (match ext_stores__exp__bt__aux with conj _ (conj _ (conj F _)) =>
   F (stty, v, t) end); eauto.
Qed.

Lemma ext_stores__env:
   forall stty stty',
     (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t') -> 
     (forall rho env ctxt, TcEnv (stty, rho, env, ctxt) ->  
      TcEnv (stty', rho, env, ctxt)).
Proof.
  intros.
  eapply (match ext_stores__exp__bt__aux 
          with conj _ (conj _ (conj _ F)) =>
               F (stty, rho, env, ctxt) end); eauto.
Qed.


Lemma update_rho: forall rho rgns x v,
                    TcRho (rho, rgns) ->
                    not_set_elem rgns x ->
                    TcRho (update_R (x, v) rho, set_union rgns (singleton_set x)).
Proof.
  intros rho rgns x v HRho HFresh.
  unfold update_R; simpl. 
  econstructor.  
  intro r. split.
  - inversion_clear HRho as [rho' rgns' HRgn'  HRho''].
    destruct (AsciiVars.eq_dec x r) as [c | c].
    + unfold AsciiVars.eq in c; intros; subst.
      unfold set_elem, set_union, singleton_set.
      apply Ensembles.Union_intror.
      apply Ensembles.In_singleton.
    + destruct (HRgn' r).
      intro. 
      apply H0 in H. 
      * eapply R_diff_key_3 in H1; auto.  
        apply Ensembles.Union_introl. 
        apply HRgn'. assumption.
      * eapply R_diff_key_3 in H1; auto.  
  - inversion_clear HRho as [rho' rgns' HRgn'  HRho''].
    destruct (AsciiVars.eq_dec x r) as [c | c].
    + unfold AsciiVars.eq in c; intros; subst.
      apply RMapP.in_find_iff. apply RMapP.add_in_iff. intuition.
    + destruct (HRgn' r).
      intro. apply H0 in H. 
      * rewrite <- RMapP.in_find_iff.  rewrite RMapP.add_in_iff.
        right. rewrite RMapP.in_find_iff. 
        assumption.
      * destruct H1; [apply H0; assumption | inversion H1; subst; contradict c; reflexivity].
Qed.


Lemma subst_type_rgn_comm_2:
  forall r k1 k2 v1 v2,
    k1 <> k2 ->
    subst_rgn k1 (Rgn_Const true false v1) (subst_rgn k2 (Rgn_Const true false v2) r) =
    subst_rgn k2 (Rgn_Const true false v2) (subst_rgn k1 (Rgn_Const true false v1) r).
Proof.
  intros r k1 k2 v1 v2 H.
  unfold Region_in_Type in r.
  dependent induction r; try (solve [simpl; reflexivity ]).
  unfold subst_rgn. destruct (AsciiVars.eq_dec k1 k2).
  - inversion e. contradiction.
  - simpl. destruct (AsciiVars.eq_dec k2 v).
    + assert (~ AsciiVars.eq k1 v) by (inversion e; congruence).
      unfold  AsciiVars.eq in *.
      destruct (AsciiVars.eq_dec k1 v).
      * now absurd (k1=v).
      * inversion e; subst; now destruct (AsciiVars.eq_dec v v).
    + destruct (AsciiVars.eq_dec k1 v); [reflexivity |].
      now destruct (AsciiVars.eq_dec k2 v).
Qed.  


Lemma subst_type_sa_comm_2:
  forall sa k1 k2 v1 v2,
    k1 <> k2 ->
    subst_sa k1 (Rgn_Const true false v1) (subst_sa k2 (Rgn_Const true false v2) sa) =
    subst_sa k2 (Rgn_Const true false v2) (subst_sa k1 (Rgn_Const true false v1) sa).
Proof.
  intros sa k1 k2 v1 v2 H.
  destruct sa; simpl; apply f_equal; apply subst_type_rgn_comm_2; auto.
Qed.

Lemma subst_type_eps_comm_2 :
  forall (k1 : R.key) (v1 : RgnId) (k2 : R.key) (v2 : RgnId) (e : Epsilon),
    k1 <> k2 ->
    subst_eps k1 (Rgn_Const true false v1) (subst_eps k2 (Rgn_Const true false v2) e) =
      subst_eps k2 (Rgn_Const true false v2) (subst_eps k1 (Rgn_Const true false v1) e).
Proof.
  intros k1 v1 k2 v2 e H. unfold subst_eps.
  apply Extensionality_Ensembles; unfold Same_set, Included.
  split; intros; unfold Ensembles.In in *; destruct H0 as [x' [[x'' [H1 H2]] H3]];
  subst; repeat (eexists || split || subst); eauto using subst_type_sa_comm_2.
Qed.


Lemma subst_type_type_comm_2 :
  forall (k1 : R.key) (v1 : RgnId) (k2 : R.key) (v2 : RgnId) (b : Tau),
    k1 <> k2 ->
    subst_in_type k1 v1 (subst_in_type k2 v2 b) =
      subst_in_type k2 v2 (subst_in_type k1 v1 b).
Proof.
  intros k1 v1 k2 v2 b H.
  unfold subst_in_type.
  induction b; simpl; try (solve [simpl; reflexivity ]).
  - f_equal; [apply IHb1 | apply IHb2].
  - f_equal; [ | apply IHb].
    now apply  subst_type_rgn_comm_2.
  - f_equal; [ apply IHb1 | |  apply IHb2 | |  apply IHb3];
      eauto using subst_type_eps_comm_2.
  - f_equal; [ | apply IHb]; eauto using subst_type_eps_comm_2.
Qed.


Lemma subst_add_comm_rgn :
  forall k v rho ,
    ~ R.In (elt:=RgnId) k rho ->
    forall rgn, 
      fold_subst_rgn (R.add k v rho) rgn = fold_subst_rgn rho (subst_in_rgn k v rgn).
Proof.
  intros k v rho H rgn.
   apply fold_add_type. 
   - assumption.
   - intros k0 v0 b0 H'.
     rewrite subst_type_rgn_comm_2.
     + reflexivity.
     + intro; subst.
       destruct H.
       apply RMapProp.F.elements_in_iff.
       exists v0.
       apply RMapProp.F.elements_mapsto_iff.
       assumption.
Qed.

Lemma subst_add_comm_sa :
  forall k v rho ,
    ~ R.In (elt:=RgnId) k rho ->
    forall sa, 
      fold_subst_sa (R.add k v rho) sa = fold_subst_sa rho (subst_in_sa k v sa).
Proof.
  intros k v rho H sa.
  unfold fold_subst_sa.
  induction sa; simpl; f_equal; apply subst_add_comm_rgn; assumption.
Qed.


Lemma subst_add_comm_eff :
  forall k v rho ,
    ~ R.In (elt:=RgnId) k rho ->
    forall eff, 
      fold_subst_eps (R.add k v rho) eff = fold_subst_eps rho (subst_in_eff k v eff). 
Proof.
  intros k v rho H eff. unfold fold_subst_eps.
  apply Extensionality_Ensembles; unfold Same_set, Included. 
  intuition; unfold Ensembles.In in *. 
  - destruct H0 as [sa [H1 H2]].
    exists (subst_in_sa k v sa).
    rewrite <- subst_add_comm_sa; eauto.
    intuition.
    unfold subst_in_eff, subst_in_sa.
    unfold subst_eps, subst_sa.
    exists sa. intuition.
  - destruct H0 as [sa [H1 H2]].
    unfold subst_in_eff, subst_eps in H1.
    destruct H1 as [sa' [H3 H4]]. subst.
    exists sa'. rewrite subst_add_comm_sa; eauto.
Qed.


Lemma subst_add_comm :
  forall k v rho ,
    ~ R.In (elt:=RgnId) k rho ->
    forall ty, 
      subst_rho (R.add k v rho) ty = subst_rho rho (subst_in_type k v ty). 
Proof.
  intros k v rho H ty.
  (*unfold subst_rho, subst_in_type.*)
  apply fold_add_type.  
  - assumption.
  - intros k0 v0 b0 H'.
    rewrite subst_type_type_comm_2.
    + reflexivity.
    + intro; subst.
      destruct H.
      apply RMapProp.F.elements_in_iff.
      exists v0.
      apply RMapProp.F.elements_mapsto_iff.
      assumption.
Qed.

Lemma not_set_elem_not_in_rho:
  forall rho rgns x,
    TcRho (rho, rgns) ->
    not_set_elem rgns x ->
    ~R.In (elt:=RgnId) x rho.
Proof.
  intros rho rgns  x HRho H .
  inversion_clear HRho as [rho' rgns' HRgn' HVal''].
  unfold not_set_elem in H. unfold Ensembles.Complement in H.
  intro. 
  apply RMapP.in_find_iff in H0.
  eapply HRgn' in H0. contradiction.
Qed.



Lemma NotFreeInEmptyEps:
  forall x,
    ~ free_rgn_vars_in_eps (Empty_set StaticAction) x.
Proof.
  intro x. intro. 
  unfold free_rgn_vars_in_eps, empty_set in H.
  destruct H as [sa]. destruct H.
  inversion H.
Qed.


Module EProofs := Raw.Proofs.
Module EMapP := FMapFacts.Facts E.


Lemma E_same_key:
  forall t x v e, 
    E.find (elt := t) x (E.add x v e) = Some v.
Proof.
  intros. rewrite <- EMapP.find_mapsto_iff. rewrite -> EMapP.add_mapsto_iff.
  left. intuition. 
Qed.  

Lemma E_diff_key_1:
  forall t a b v v' e,   
    a <> b ->
    E.find (elt := t) a (E.add b v e) = Some v' -> 
    E.find (elt := t) a e = Some v'.
Proof.
  intros. 
  rewrite <- EMapP.find_mapsto_iff in H0. rewrite -> EMapP.add_mapsto_iff in H0.
  destruct H0; destruct H0; [destruct H | rewrite -> EMapP.find_mapsto_iff in H1]; auto.
Qed.


Lemma E_diff_key_2:
  forall t a b v v' e,   
    b <> a ->
    E.find (elt := t) a e = Some v' ->
    E.find (elt := t) a (E.add b v e) = Some v'.
Proof.
  intros. 
  rewrite <- EMapP.find_mapsto_iff. rewrite -> EMapP.add_mapsto_iff.
  right; split; [exact H | now rewrite EMapP.find_mapsto_iff ].
Qed.


Lemma ExtendedTcInv_2:
  forall ctxt rgns f x tyx effe tyc effc, 
    TcInc (ctxt, rgns)->
    included (frv tyx) rgns ->
    included (frv (Ty_Arrow tyx effc tyc effe Ty_Effect)) rgns ->
    TcInc (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect) (x, tyx) ctxt, rgns).
Proof.
  intros ctxt rgns f x tyx effe tyc effc HInc HFind1 HFind2.
  inversion HInc as [? ? HFrv]; subst.
  unfold included, Included in *.
  econstructor.    
  intros. unfold find_T in H, HFrv.
  unfold update_rec_T in H. simpl in H.
  destruct (AsciiVars.eq_dec x0 x) as [c | c].
  - inversion c; subst.
    rewrite E_same_key in H.
    inversion H; subst.
    do 2 intro. eapply HFind1. assumption.
  - destruct (AsciiVars.eq_dec x0 f) as [d | d].
    + inversion d; subst.
      unfold AsciiVars.eq in c.
      eapply E_diff_key_1 in H; auto.
      rewrite E_same_key in H.
      inversion H; subst.
      do 2 intro. eapply HFind2. assumption.
    + eapply E_diff_key_1 in H; eauto. 
      eapply E_diff_key_1 in H; eauto.
      do 2 intro.
      eapply HFrv; eauto.
Qed.


Lemma subst_rho_free_vars_eps:
  forall rho x (e : Ensemble StaticAction),
   R.find (elt:=RgnId) x rho = None ->  
   not_set_elem (free_rgn_vars_in_eps (fold_subst_eps rho e)) x ->
   not_set_elem (free_rgn_vars_in_eps e) x.
Proof.
  intro rho. destruct rho. induction this; intros x e' H1 H2.
  - intro. apply H2. unfold In in *. clear H2.
    unfold free_rgn_vars_in_eps in *.
    destruct H as [sa [Ha Hb]]. 
    exists sa; intuition.
    unfold fold_subst_eps. 
    exists sa. intuition. 
    unfold fold_subst_sa, fold_subst_rgn, subst_rgn, R.fold, R.Raw.fold ; simpl.
    induction sa; reflexivity.
  - inversion is_bst; subst. 
    destruct (AsciiVars.compare x k); subst.
    + eapply IHthis1 with (is_bst:=H5); eauto.
      * eapply find_rho_1; eauto.
      * intro. apply H2. unfold In in *.
        eapply subst_rho_free_vars_eps_aux_1; eauto.
    + inversion e0; subst.
      intro. apply H2. unfold In in *. 
      unfold free_rgn_vars_in_eps, fold_subst_eps in *.
      destruct H as [sa [Ha Hb]].
      exists sa. split; [| assumption].
      exists sa. split; [assumption|]. 
      apply equal_fold_subst_sa; auto.
    + eapply IHthis2  with (is_bst:=H7); eauto. 
      * eapply find_rho_2; eauto.  
      * intro. apply H2. unfold In in *.
        eapply subst_rho_free_vars_eps_aux_2. assumption.
        eassumption.
Qed.

Lemma subst_rho_free_vars :
  forall t rho x,
    x # subst_rho rho t ->
    R.find (elt:=nat) x rho = None ->
    x # t.
Proof.
  intro t. dependent induction t; intros rho x H1 H2. 
  - rewrite subst_rho_natural in H1. assumption.
  - rewrite subst_rho_boolean in H1. assumption.
  - rewrite subst_rho_effect in H1. assumption.
  - rewrite subst_rho_unit in H1. assumption.
  - rewrite subst_rho_pair in H1. simpl in *.
    apply subst_rho_free_vars_union_1 in H1; auto. destruct H1.
    apply subst_rho_free_vars_union_2.
    split; [eapply IHt1 | eapply IHt2]; eauto.
  - rewrite subst_rho_tyref in H1. simpl in *.
    apply subst_rho_free_vars_union_1 in H1; auto. destruct H1.
    apply subst_rho_free_vars_union_2.
    split; [ eapply subst_rho_free_vars_rgn | eapply IHt]; eauto.
  - rewrite subst_rho_arrow in H1. simpl in *.
    eapply subst_rho_free_vars_union_1 in H1. destruct H1.
    eapply subst_rho_free_vars_union_1 in H0. destruct H0.
    eapply subst_rho_free_vars_union_1 in H0. destruct H0.
    eapply subst_rho_free_vars_union_1 in H1. destruct H1.
    apply subst_rho_free_vars_union_2.
    split;  [eapply IHt1 | apply subst_rho_free_vars_union_2]; eauto.
    split.
    + apply subst_rho_free_vars_union_2.
      split; [ eapply subst_rho_free_vars_eps | eapply subst_rho_free_vars_eps]; eauto. 
    + eapply subst_rho_free_vars_union_2.
      split; [eapply IHt2 | eapply IHt3]; eauto. 
  - rewrite subst_rho_forallrgn in H1; simpl in *.
    eapply subst_rho_free_vars_union_1 in H1. destruct H1.
    eapply subst_rho_free_vars_union_2.
    split; [ eapply subst_rho_free_vars_eps | eapply IHt]; eauto.
Qed.


Lemma TypedExpressionFrv :
  forall ctxt rgns e t eff,
  TcInc (ctxt, rgns) ->
  TcExp (ctxt, rgns, e, t, eff) ->
  included (frv t) rgns /\ included (free_rgn_vars_in_eps eff) rgns.
Proof. 
  intros ctxt rgns e t eff HInc HExp.  
  generalize dependent HInc.  
  dependent induction HExp;
  intros HInc; unfold included, Included, In;
  try (solve [intuition; [inversion H | contradict H; apply NotFreeInEmptyEps] ]). 
  - inversion HInc as [? ? HFrv]; subst.
    intuition; eapply HFrv; eauto. contradict H0; apply NotFreeInEmptyEps.
  - inversion HInc as [? ? HFrv]; subst.
    assert (H' : included (frv tyc) rgns /\ included (free_rgn_vars_in_eps effc) rgns).
    { eapply IHHExp1; eauto. 
      simpl in H0. 
      assert (H': included (frv tyx) rgns) 
        by  (apply IncludedUnion_Name_1 in H0; destruct H0; assumption). 
      apply ExtendedTcInv_2; eauto. }
     
    { assert (H'' : included (frv Ty_Effect) rgns /\ 
                    included (free_rgn_vars_in_eps effe) rgns).
      eapply IHHExp2; eauto.
      - simpl in H0. 
        assert (H''': included (frv tyx) rgns) 
          by  (apply IncludedUnion_Name_1 in H0; destruct H0; assumption).  
        apply ExtendedTcInv_2; eauto. 
      - split; auto.
        intro. intro. contradict H1. apply NotFreeInEmptyEps. }
  - inversion HInc as [? ? HFrv]; subst.
    assert (H' : included (frv tyr) (set_union rgns (singleton_set x)) /\ 
                 included (free_rgn_vars_in_eps effr) (set_union rgns (singleton_set x))).
    { eapply IHHExp; eauto.
      econstructor.
      intros. intro. intros.
      apply Union_introl. eapply HFrv; eauto. } 
    split; simpl.
    intuition.
    + unfold included, Included in *.
      destruct H5; unfold In in *.
      * eapply RegionAbsFrv_1; eauto.
      * eapply RegionAbsFrv_3; eauto.
    + intros. contradict H3. apply NotFreeInEmptyEps.
  - assert (H' : included (frv (Ty_Arrow tya effc t effe Ty_Effect)) rgns /\ 
                 included (free_rgn_vars_in_eps efff) rgns) by (eapply IHHExp1; eauto).
    assert (H'' : included (frv tya) rgns /\ 
                  included (free_rgn_vars_in_eps effa) rgns) by (eapply IHHExp2; eauto).
    destruct H' as [H2 H3].
    destruct H'' as [H4 H5].
    split.
    + do 2 intro. apply H2. simpl.
      apply Union_intror. apply Union_intror. apply Union_introl. assumption.
    + intro. apply IncludedUnion_Static_Action_4; [apply IncludedUnion_Static_Action_4 |].
      * apply H3.
      * apply H5.
      * intro. apply H0. auto.
  - inversion HInc as [? ? HFrv]; subst.
    assert (H' : included (frv (Ty_ForallRgn effr tyr)) rgns /\ 
                 included (free_rgn_vars_in_eps efff) rgns).
    eapply IHHExp; eauto.
    destruct H' as [H2 H3].
    split.
    + simpl in H2.
      apply IncludedUnion_Name_1 in H2. 
      destruct H2 as [H4 H5].
      apply RegionAppFrv_1; auto.
    + intro. apply IncludedUnion_Static_Action_4.
      * apply H3.
      * apply H1.
  -inversion HInc as [? ? HFrv]; subst.
    assert (H' : included (frv ( Ty_Arrow tya effc tyc effe Ty_Effect)) rgns /\ 
                 included (free_rgn_vars_in_eps efff) rgns).
    eapply IHHExp1; eauto.
    assert (H'' : included (frv tya) rgns /\ 
                  included (free_rgn_vars_in_eps effa) rgns).
    eapply IHHExp2; eauto.
    destruct H' as [H1 H2].
    destruct H'' as [H3 H4].
    split.
    + do 2 intro. inversion H0.
    + intro. apply IncludedUnion_Static_Action_4; [apply IncludedUnion_Static_Action_4 |].
      * apply H2.
      * apply H4. 
      * apply H. 
  - assert (H1 : included (frv ty1) rgns /\ included (free_rgn_vars_in_eps eff1) rgns)
      by (eapply IHHExp1; eauto).
    assert (H2 : included (frv ty2) rgns /\ included (free_rgn_vars_in_eps eff2) rgns)
      by (eapply IHHExp2; eauto).
    assert (H3 : included (frv ty3) rgns /\ included (free_rgn_vars_in_eps eff3) rgns)
      by (eapply IHHExp3; eauto).
    assert (H4 : included (frv ty4) rgns /\ included (free_rgn_vars_in_eps eff4) rgns)
      by (eapply IHHExp4; eauto).
    split.
    + do 2 intro. simpl in H.
      destruct H.
      * destruct H1. apply H0. assumption.
      * destruct H2. apply H0. assumption.
    + intro. apply IncludedUnion_Static_Action_4; 
             [apply IncludedUnion_Static_Action_4; [apply IncludedUnion_Static_Action_4 |] |];
             [destruct H3 | destruct H4 | destruct H2 | destruct H1]; apply H0. 
  - assert (H1 : included (frv t0) rgns /\ included (free_rgn_vars_in_eps veff) rgns)
      by (eapply IHHExp; eauto).
    destruct H1 as [H2 H3].
    split.
    + do 2 intro. simpl in H.
      rewrite EmptyUnionisEmptySet_Name_Left in H.
      apply H2. assumption.
    + intro. apply IncludedUnion_Static_Action_4; [apply H3 |].
      simpl. apply H0. 
  - assert (H2 : included (frv (Ty_Ref (mk_rgn_type (Rgn_Const true false s)) t)) rgns /\ 
                 included (free_rgn_vars_in_eps aeff) rgns)
      by (eapply IHHExp; eauto).
    destruct H2 as [H3 H4].
    split.
    + do 2 intro. apply H3; simpl.
      apply Union_intror. assumption.
    + intro. apply IncludedUnion_Static_Action_4; [apply H4 |].
      simpl. apply H1.
  - assert (H2 : included (frv (Ty_Ref (mk_rgn_type (Rgn_Const true false s)) t0)) rgns
                 /\ included (free_rgn_vars_in_eps aeff) rgns)
      by (eapply IHHExp1; eauto).
    assert (H3 : included (frv t0) rgns /\ 
                 included (free_rgn_vars_in_eps veff) rgns)
      by (eapply IHHExp2; eauto).
     destruct H2 as [H4 H5].
     destruct H3 as [H6 H7].
     split.
     + do 2 intro. inversion H.
     + intro.  apply IncludedUnion_Static_Action_4; [ apply IncludedUnion_Static_Action_4  |].
       * apply H5.
       * apply H7. 
       * simpl. apply H1. 
  - assert (H1 : included (frv Ty_Boolean) rgns /\ 
                 included (free_rgn_vars_in_eps eff0) rgns)
      by (eapply IHHExp1; eauto).
    assert (H2 : included (frv t) rgns /\ 
                 included (free_rgn_vars_in_eps eff1) rgns)
      by (eapply IHHExp2; eauto).
    assert (H3 : included (frv t) rgns /\ 
                 included (free_rgn_vars_in_eps eff2) rgns)
      by (eapply IHHExp3; eauto).
    destruct H1 as [H4 H5].
    destruct H2 as [H6 H7].
    destruct H3 as [H8 H9].
    split.
    + do 2 intro. apply H6. assumption.
    + intro.  apply IncludedUnion_Static_Action_4; [ | apply IncludedUnion_Static_Action_4 ].
      * apply H5.
      * apply H7.
      * apply H9. 
  - assert (H1 : included (frv Ty_Natural) rgns /\ 
                 included (free_rgn_vars_in_eps eff1) rgns)
      by (eapply IHHExp1; eauto).
    assert (H2 : included (frv Ty_Natural) rgns /\ 
                 included (free_rgn_vars_in_eps eff2) rgns)
      by (eapply IHHExp2; eauto).
    destruct H1 as [H3 H4].
    destruct H2 as [H5 H6].
    split.
    + do 2 intro. apply H3. assumption.
    + intro. apply IncludedUnion_Static_Action_4; [apply H4 | apply H6].
  - assert (H1 : included (frv Ty_Natural) rgns /\ 
                 included (free_rgn_vars_in_eps eff1) rgns)
      by (eapply IHHExp1; eauto).
    assert (H2 : included (frv Ty_Natural) rgns /\ 
                 included (free_rgn_vars_in_eps eff2) rgns)
      by (eapply IHHExp2; eauto).
    destruct H1 as [H3 H4].
    destruct H2 as [H5 H6].
    split.
    + do 2 intro. apply H3. assumption.
    + intro. apply IncludedUnion_Static_Action_4; [apply H4 | apply H6].
  - assert (H1 : included (frv Ty_Natural) rgns /\ 
                 included (free_rgn_vars_in_eps eff1) rgns)
      by (eapply IHHExp1; eauto).
    assert (H2 : included (frv Ty_Natural) rgns /\ 
                 included (free_rgn_vars_in_eps eff2) rgns)
      by (eapply IHHExp2; eauto).
    destruct H1 as [H3 H4].
    destruct H2 as [H5 H6].
    split.
    + do 2 intro. apply H3. assumption.
    + intro. apply IncludedUnion_Static_Action_4; [apply H4 | apply H6].
  - assert (H1 : included (frv Ty_Natural) rgns /\ 
                 included (free_rgn_vars_in_eps eff1) rgns)
      by (eapply IHHExp1; eauto).
    assert (H2 : included (frv Ty_Natural) rgns /\ 
                 included (free_rgn_vars_in_eps eff2) rgns)
      by (eapply IHHExp2; eauto).
    destruct H1 as [H3 H4].
    destruct H2 as [H5 H6].
    split.
    + do 2 intro. apply H3. assumption.
    + intro. apply IncludedUnion_Static_Action_4; [apply H4 | apply H6].
  - assert (H1 : included (frv (Ty_Ref (Rgn_Const true true r) t0)) rgns /\ 
                 included (free_rgn_vars_in_eps eff) rgns)
      by (eapply IHHExp; eauto).
    destruct H1 as [H2 H3].
    intuition. inversion H.
  - assert (H1 : included (frv (Ty_Ref (Rgn_Const true true r) t0)) rgns /\ 
                 included (free_rgn_vars_in_eps eff) rgns)
      by (eapply IHHExp; eauto).
    destruct H1 as [H2 H3].
    intuition. inversion H.
  - assert (H1 : included (frv Ty_Effect) rgns /\ 
                 included (free_rgn_vars_in_eps eff1) rgns)
      by (eapply IHHExp1; eauto).
    assert (H2 : included (frv Ty_Effect) rgns /\ 
                 included (free_rgn_vars_in_eps eff2) rgns)
      by (eapply IHHExp2; eauto).
    destruct H1 as [H3 H4].
    destruct H2 as [H5 H6].
    split.
    + do 2 intro. apply H3. assumption.
    + intro. apply IncludedUnion_Static_Action_4; [apply H4 | apply H6].
Qed.


Theorem TcVal_implies_closed :
  forall stty v t,
    TcVal (stty, v, t) ->
    (forall r, r # t).
Proof.
  intros stty v t HTcVal.
  dependent induction HTcVal; intros;
  try ( solve [ unfold not_set_elem, Complement; simpl;
                intro; unfold Ensembles.In, empty_set in H; contradiction] ).
  - unfold not_set_elem, Complement; simpl.
    intro. destruct H1; [contradiction |contradict H1; apply H0].
  - eapply TypedExpressionFrv in H2; eauto.  
    eapply TcRhoIncludedNoFreeVars; eauto.
    intuition.
  - unfold not_set_elem, Complement; simpl. 
    intro. destruct H; contradict H; [eapply IHHTcVal1 | eapply IHHTcVal2]; eauto.
Qed.


Lemma subst_rho_fresh_var :
  forall rho rgns x stty v t r,
    TcRho (rho, rgns) ->
    not_set_elem rgns x ->
    TcVal (stty, v, subst_rho rho t) ->
    TcVal (stty, v, subst_rho rho (subst_in_type x r t)).
Proof.
  intros rho rgns x stty v t r HTcRho H_not_set HTcVal.
  assert ( x # (subst_rho rho t)) by (eapply TcVal_implies_closed; eauto).
  generalize dependent rgns.
  generalize dependent r.
  generalize dependent x.  
  dependent induction HTcVal; intros;
    inversion HTcRho as [rho' rgns' HRgn HVal'']; subst;
  try (solve [ unfold subst_in_type;
               assert (R.find (elt:=nat) x0 rho = None) 
                 by (eapply contrapositiveTcRho; eauto; apply HRgn);
               rewrite  SUBST_FRESH; [rewrite <- x; econstructor; eauto | 
                                      eapply subst_rho_free_vars; eauto]  ] ).
Qed.

Lemma extended_rho : forall stty rho env ctxt,
                       TcEnv (stty, rho, env, ctxt) ->
                       forall x r rgns,
                         TcRho (rho, rgns) ->
                         not_set_elem rgns x -> 
                         TcEnv (stty, update_R (x, r) rho, env, ctxt). 
Proof.
  intros stty rho env ctxt HEnv x r rgns HRho HRgns. 
  inversion_clear HEnv as [ stty' rho' env' ctxt' ? HE HT HV]. 
  inversion_clear HRho as [rho' rgns' HRgn' HVal''].
  constructor; auto.
  intros x0 v0 t0 HE' HT'. eapply HV in HE'; eauto. unfold update_R. simpl.
  rewrite subst_add_comm. 
  - eapply subst_rho_fresh_var; eauto. econstructor; auto. 
  - unfold not_set_elem in HRgns. unfold Ensembles.Complement in HRgns.
    intro. 
    apply RMapP.in_find_iff in H0.
    eapply HRgn' in H0. contradiction.
Qed.


Lemma TcRhoIncludedNoFreeVarsTyRef:
  forall rho rgns r0 t x,
    TcRho (rho, rgns) ->
    included (set_union (free_rgn_vars_in_rgn r0) (frv t)) rgns ->
    ~free_rgn_vars_in_rgn (fold_subst_rgn rho r0) x.
Proof.
  intros rho rgns r0 t x HRho HInc H.
  generalize dependent r0.
  unfold Region_in_Type.
  dependent induction r0; intros.
  - rewrite subst_rho_rgn_const in H.
    simpl in H. contradiction.
  - destruct (AsciiVars.eq_dec x v) as [c | c].
    + inversion c; subst.   
      inversion HRho; subst.   
      contradict H.
      destruct (subst_rho_fvar_1 rho v) as [[v' H0] | H0]. 
      * rewrite H0. simpl. intro. contradiction.
      * rewrite H0. simpl. intro. 
        unfold set_elem, In in H1.
        destruct H1 with (r:=v). 
        { apply H3 in HInc.
          - apply NotNoneIsSome in HInc.
            destruct HInc.
            apply subst_rho_fvar_2 in H4.
            rewrite H4 in H0. 
            inversion H0.
          - apply Union_introl. simpl. auto. }
   + unfold AsciiVars.eq in c; subst.   
     inversion HRho; subst.
     contradict H.
     destruct (subst_rho_fvar_1 rho v) as [[v' H0] | H0].
     * rewrite H0. simpl. intro. contradiction.
     * rewrite H0. simpl. intro. inversion H. auto.
  - rewrite subst_rho_index in H.
    simpl in H. contradiction. 
Qed.



Lemma TcRhoIncludedNoFreeVarsEps_main:
  forall rho rgns e x,
    TcRho (rho, rgns) ->
    free_rgn_vars_in_eps e x ->
    included (free_rgn_vars_in_eps e) rgns ->
    ~ (free_rgn_vars_in_eps (fold_subst_eps rho e)) x.
Proof.
  intros.
  apply TcRhoIncludedNoFreeVarsEps_find.
  inversion H; subst. apply H3. apply H1.
  unfold In.
  assumption.
Qed.

Lemma TcRhoIncludedNoFreeVars:
  forall rho rgns t r, 
    TcRho (rho, rgns) ->
    included (frv t) rgns ->
    r # subst_rho rho t.
Proof.
  intros.
  generalize dependent t.
  dependent induction t; intro HInc; simpl in HInc.
  - rewrite subst_rho_natural; simpl. intro. contradiction. 
  - rewrite subst_rho_boolean; simpl. intro. contradiction.
  - rewrite subst_rho_effect; simpl. intro. contradiction.
  - rewrite subst_rho_unit; simpl. intro. contradiction.
  - rewrite subst_rho_pair; simpl.
    unfold not_set_elem, Complement. intro.
    destruct H0.
    + contradict H0. apply IHt1. 
      unfold included, Included in *.
      intros. apply HInc.
      apply Ensembles.Union_introl.
      assumption.
    + contradict H0. apply IHt2. 
      unfold included, Included in *.
      intros. apply HInc.
      apply Ensembles.Union_intror.
      assumption.
  - rewrite subst_rho_tyref; simpl. 
    unfold not_set_elem, Complement. intro.
    destruct H0.
    + apply IHt.   
      * unfold included, Included in *.
        intros. apply HInc.
        apply Ensembles.Union_intror.
        assumption.
      * contradict H0. unfold Ensembles.In.
        eapply TcRhoIncludedNoFreeVarsTyRef; eauto.
    + unfold included, Included, Ensembles.In in *.
      apply IHt.
      * intros. apply HInc. apply Ensembles.Union_intror. assumption.
      * assumption.
  - rewrite subst_rho_arrow; simpl.
    unfold not_set_elem, Complement. intro.
    destruct H0. 
    + apply IHt1; auto. 
      unfold included, Included in *. 
      intros. apply HInc. apply Union_introl. assumption.
    + destruct H0.
      * { destruct H0.
          - eapply TcRhoIncludedNoFreeVarsEps_main  with (e:=e); eauto.
            + unfold In in H0. eapply TcRhoIncludedNoFreeVarsEps_aux_fold; eauto. 
            + unfold included, Included, Ensembles.In in *.
              intro. intro.
              apply HInc.
              apply Ensembles.Union_intror. apply Ensembles.Union_introl.
              apply Ensembles.Union_introl. assumption.
          - eapply TcRhoIncludedNoFreeVarsEps_main with (e:=e0); eauto.
            + unfold In in H0. eapply TcRhoIncludedNoFreeVarsEps_aux_fold; eauto. 
            + unfold included, Included, Ensembles.In in *.
              intro. intro. apply HInc.
              apply Ensembles.Union_intror. apply Ensembles.Union_introl.
              apply Ensembles.Union_intror. assumption. }
      * { repeat destruct H0.
          - apply IHt2; auto. 
            unfold included, Included in *. 
            intros. apply HInc. 
            apply Union_intror. apply Union_intror. apply Union_introl. assumption.
          - apply IHt3; auto. 
            unfold included, Included in *. 
            intros. apply HInc. 
            apply Union_intror. apply Union_intror. apply Union_intror. assumption. }
  - rewrite subst_rho_forallrgn; simpl.
    unfold not_set_elem, Complement. intro.
    destruct H0.
    + eapply TcRhoIncludedNoFreeVarsEps_main with (e:=e); eauto. 
      * eapply TcRhoIncludedNoFreeVarsEps_aux_fold; eauto. 
      * unfold included, Included, In in *. intro. intro.
        apply HInc.
        apply Union_introl. assumption.
    + apply IHt; auto. 
      unfold included, Included in *. 
      intros. apply HInc. 
      apply Union_intror. assumption.
Qed.

Lemma Functional_Map_Union_find:
  forall sttya sttyb (k : SigmaKey),
    find_ST k (Functional_Map_Union_Sigma sttya sttyb) = find_ST k sttya.
Proof.
  intros.  unfold find_ST, Functional_Map_Union_Sigma.
  assert (merge Merge_ST sttya sttyb !! k = diag_None Merge_ST (sttya !! k) (sttyb !! k))
    by (rewrite lookup_merge; reflexivity).
  replace (merge Merge_ST sttya sttyb !! k)
    with (diag_None Merge_ST (sttya !! k) (sttyb !! k)).
  destruct (sttyb !! k); destruct (sttya !! k); unfold Merge_ST; simpl; reflexivity.
Qed.

Lemma StoreTyping_Extended:
  forall stty sttya sttyb,
    (forall (l : SigmaKey) (t' : Tau),
       find_ST l stty = Some t' -> find_ST l sttya = Some t' ) ->
    (forall (l : SigmaKey) (t' : Tau),
       find_ST l stty = Some t' -> find_ST l sttyb = Some t' ) ->
    (forall (l : SigmaKey) (t' : Tau),
        find_ST l stty = Some t' ->
        find_ST l (Functional_Map_Union_Sigma sttya sttyb) = Some t' ).
Proof. 
  intros stty sttya sttyb Ha Hb.
  intros l t' H.
  edestruct (Ha l t' H).
  generalize l. 
  apply Functional_Map_Union_find.
Qed.


Lemma Raw_diff_key_1:
  forall t a b v v' e,
    Raw.bst e ->
    b <> a ->
    Raw.find (elt := t) a (Raw.add b v e) = Some v' -> 
    Raw.find (elt := t) a e = Some v'.
Proof.
  intros. 
  apply EProofs.find_1; auto.
  apply EProofs.find_2 in H1. now apply EProofs.add_3 in H1.
Qed.

Require Import Lia.

Lemma Raw_same_key:
  forall t x v e, 
    Raw.bst e ->
    Raw.find (elt := t) x (Raw.add x v e) = Some v.
Proof.
  intros. rewrite EProofs.add_find; auto.
  case_eq (AsciiVars.compare x x); intros; 
  now try repeat (unfold AsciiVars.lt in l; lia).
Qed.  

Lemma Raw_diff_key_2:
  forall t a b v v' e,
    Raw.bst e ->
    b <> a ->
    Raw.find (elt := t) a e = Some v' ->
    Raw.find (elt := t) a (Raw.add b v e) = Some v'.
Proof.
  intros. apply EProofs.find_1; 
  [now apply EProofs.add_bst | apply EProofs.find_2 in H1; now apply EProofs.add_2 ].
Qed.


Lemma update_env:
  forall stty rho env ctxt, 
    TcEnv (stty, rho, env, ctxt) -> 
    (forall x v t, 
       TcVal (stty, v, subst_rho rho t) ->
       TcEnv (stty, rho, update_E (x, v) env, update_T (x, t) ctxt) ).
Proof. 
  intros stty rho env ctxt HEnv x v t HTc.  
  inversion_clear HEnv as [ stty' rho' env' ctxt' ? HE HT HV]. 
  apply TC_Env;
  unfold find_E, update_E, find_T, update_T in *; simpl.
  clear HTc.
  - now apply EProofs.add_bst. (** "env is a bst" **)
  - intros x0 v0 HF. (** "TcEnv is well-typed: HE" **)
    destruct (AsciiVars.eq_dec x0 x) as [c | c].
    + unfold AsciiVars.eq in c; intros. 
      subst. exists t. now rewrite E_same_key.
    + unfold AsciiVars.eq in c; intros. 
      eapply Raw_diff_key_1 in HF; auto; subst.
      * destruct (HE x0 v0) as [t0 HU] ; [auto | ] ; exists t0.
        eapply E_diff_key_2 ; [ auto | exact HU]. 
  - intros x0 t0 HF. (** "TcEnv is well-typed: HT".  **)
    destruct (AsciiVars.eq_dec x0 x) as [c | c]; 
    unfold AsciiVars.eq in c; intros; subst.  
    + exists v. now rewrite Raw_same_key.
    + eapply E_diff_key_1 in HF; auto.
      destruct (HT x0 t0) as [x1 ?] ; [auto | ].
      exists x1; [eapply Raw_diff_key_2]; auto.
  - intros x0 v0 t0 HFindE HFindT. (** "Type preservation: HV". **)
    destruct (AsciiVars.eq_dec x0 x) as [c | c];
    unfold AsciiVars.eq in c; intros; subst.
    + rewrite Raw_same_key in HFindE by assumption.
      inversion HFindE; subst.
      rewrite E_same_key in HFindT by assumption.
      inversion HFindT; subst. assumption.
    + eapply Raw_diff_key_1 in HFindE; auto.
      eapply E_diff_key_1 in HFindT; auto.
      eapply HV; eauto.
Qed.
