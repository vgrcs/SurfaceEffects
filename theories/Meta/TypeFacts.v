From stdpp Require Import gmap.
From stdpp Require Import fin_maps.
From stdpp Require Import list.
From stdpp Require Import base.
From stdpp Require Import strings.

From Stdlib Require Import Program.Equality.
From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.

Require Import theories.Core.StaticActions.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.Regions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Core.Values.
Require Import theories.Meta.Tactics.


Require Import theories.Meta.MapFacts.
Require Export theories.Meta.RegionFacts.
Require Export theories.Meta.TypeSubstitutionFacts.
Require Import theories.Meta.EffectFacts.
Require Import theories.Meta.LocallyNameless.

Import Expressions.
Import Ascii.

Lemma not_set_elem_not_in_rho:
  forall rho rgns x,
    TcRho (rho, rgns) ->
    not_set_elem rgns x ->
    x ∉ dom rho.
Proof.
  intros rho rgns  x HRho H .
  inversion_clear HRho as [rho' rgns' HRgn' HVal''].
  unfold not_set_elem in H. unfold Ensembles.Complement in H.
  intro.
  apply elem_of_dom in H0. unfold is_Some in H0.
  apply NotNoneIsSome in H0.
    eapply HRgn' in H0. contradiction.
Qed.


Lemma update_rho:
  forall rho rgns x v,
    TcRho (rho, rgns) ->
    not_set_elem rgns x ->
    TcRho (update_R (x, v) rho, set_union rgns (singleton_set x)).
Proof.
  intros rho rgns x v HRho HFresh.
  unfold update_R; simpl.
  econstructor; split.
  - inversion_clear HRho as [rho' rgns' HRgn'  HRho''].
    destruct (ascii_dec x r) as [c | c].
    + intros; subst.
      unfold set_elem, set_union, singleton_set.
      apply Ensembles.Union_intror.
      apply Ensembles.In_singleton.
    + destruct (HRgn' r).
      intro. 
      apply H0 in H. 
      * eapply G_diff_keys_3 in H1; auto.  
        apply Ensembles.Union_introl. 
        apply HRgn'. assumption.
      * eapply G_diff_keys_3 in H1; auto.  
  - inversion_clear HRho as [rho' rgns' HRgn'  HRho''].
    destruct (ascii_dec x r) as [c | c].
    + intros; subst.
      replace (<[r:=v]> rho !! r) with (Some v) by (symmetry; apply lookup_insert).
      intro H'. inversion H'.
    + destruct (HRgn' r).
      intro. apply H0 in H. 
      * assert (is_Some (<[x:=v]> rho !! r)). 
        apply lookup_insert_is_Some. 
        right. unfold is_Some. split; [ assumption | now apply NotNoneIsSome].
        unfold is_Some in H2. now apply NotNoneIsSome in H2.
      * destruct H1; [apply H0; assumption |
                       inversion H1; subst; contradict c; reflexivity].
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


Lemma ExtendedTcInv_2:
  forall (ctxt: Gamma) rgns f x tyx effe tyc effc, 
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
  destruct (ascii_dec x0 x) as [c | c]; subst.  
  - unfold update_T in H; simpl in H.    
    assert ( HSubst : <[x:=tyx]> (<[f:=Ty_Arrow tyx effc tyc effe Ty_Effect]> ctxt) !! x
                      = Some tyx)
      by (apply lookup_insert). 
    rewrite H in HSubst.
    inversion HSubst; subst.
    do 2 intro. eapply HFind1. assumption.
  - destruct (ascii_dec x0 f) as [d | d].
    + inversion d; subst.
      eapply G_diff_keys_1 in H; auto.
      unfold update_T in H; simpl in H.
      assert ( HSame : forall x v (e : gmap VarId Tau), (<[ x:=v ]> e) !! x = Some v)
               by (intros; apply  lookup_insert).      
      rewrite HSame in H.      
      inversion H; subst.
      do 2 intro. eapply HFind2. assumption.
    + eapply G_diff_keys_1 in H; eauto. 
      eapply G_diff_keys_1 in H; eauto.
      do 2 intro.
      eapply HFrv; eauto.
Qed.

Lemma equal_fold_subst_rgn:
  forall l r k,
    (list_to_map l: Rho) !! k = None ->
    free_rgn_vars_in_rgn r k ->
    fold_subst_rgn_alt l r = r.
Proof.
  intros.
  intros. unfold Region_in_Type in r. dependent induction r; simpl in *.
  - inversion H0.
  - inversion H0. subst.
    unfold fold_subst_rgn_alt.
    apply fold_subst_rho_free_vars_rgn_not_elem.
    apply not_elem_of_list_to_map in H.
    assumption.
  - inversion H0.
Qed.

Lemma equal_fold_subst_sa:
  forall l k sa,
    (list_to_map l: Rho) !! k = None ->
    free_rgn_vars_in_sa sa k ->
    fold_subst_sa_alt l sa = sa.
Proof.
  intros. induction sa; simpl in *; f_equal; eapply equal_fold_subst_rgn; eauto.
Qed.

Lemma subst_rho_free_vars_eps_aux_2:
  forall k v x l e,
    (list_to_map ((k,v)::l) : Rho) !! x = None ->
    free_rgn_vars_in_eps e x ->
    free_rgn_vars_in_eps (fold_subst_eps_alt ((k,v)::l) e) x.
Proof.
  intros k v x l e H H'.
  unfold fold_subst_eps_alt.
  unfold free_rgn_vars_in_eps in H'.
  destruct H' as [sa [Ha Hb]].
  exists sa. split; [| assumption].
  exists sa. split; [assumption |].
  erewrite equal_fold_subst_sa; eauto.
Qed.


Lemma subst_rho_free_vars_eps_aux:
  forall (l: list(RgnName*RgnVal)) x (e : Ensemble StaticAction),
   (list_to_map l : Rho) !! x = None ->  
   not_set_elem (free_rgn_vars_in_eps (fold_subst_eps_alt l e)) x ->
   not_set_elem (free_rgn_vars_in_eps e) x.
Proof.
  intro l. induction l; intros x e' H1 H2.
  - intro. apply H2. unfold In in *. clear H2.
    unfold free_rgn_vars_in_eps in *.
    destruct H as [sa [Ha Hb]].
    exists sa; intuition. 
    unfold fold_subst_eps_alt. 
    exists sa. intuition. 
    unfold fold_subst_sa_alt. simpl.
    induction sa; reflexivity.
  - apply IHl;  clear IHl. 
    + destruct a as [k v].
      destruct (ascii_dec x k); subst.
      * contradict H1. apply NotNoneIsSome. exists v.
        apply lookup_insert.
      * apply not_elem_of_list_to_map_2 in H1.
        apply not_elem_of_list_to_map_1.
        assert ( x ≠ k ∧ x ∉ l.*1) by (apply not_elem_of_cons; assumption).
        intuition.
    + destruct a as [k v]. 
      destruct (ascii_dec x k); subst.
      * intro. apply H2. unfold In in *.  
        unfold free_rgn_vars_in_eps, fold_subst_eps_alt in *.  
        destruct H as [sa [[sa' [Ha Hb]] Hc]]. 
        exists sa. split; [| assumption].
        exists sa'. split; [assumption|]. 
        rewrite <-Hb. rewrite <- Hb in Hc.  
        { rewrite equal_fold_subst_sa with (k:=k); auto.
          - erewrite equal_fold_subst_sa; eauto.
            + apply not_elem_of_list_to_map_2 in H1.
              contradict H1.              
              apply elem_of_cons. left. reflexivity.
            + eapply TcRhoIncludedNoFreeVarsSa_aux_fold.
              eassumption.
          - eapply TcRhoIncludedNoFreeVarsSa_aux_fold.
            eassumption. }
      * intro. apply H2.      
        unfold In in *. apply subst_rho_free_vars_eps_aux_2. auto.
        eapply TcRhoIncludedNoFreeVarsEps_aux_fold; eauto.
Qed.
          
    
Lemma subst_rho_free_vars_eps:
  forall rho x (e : Ensemble StaticAction),
   rho !! x = None ->  
   not_set_elem (free_rgn_vars_in_eps (fold_subst_eps rho e)) x ->
   not_set_elem (free_rgn_vars_in_eps e) x.
Proof.
  intros rho x e H H'. intro. apply H'.
  unfold In in *.
  unfold free_rgn_vars_in_eps, fold_subst_eps in *.
  destruct H0 as [sa [Ha Hb]].
  exists sa. split; [| assumption].
  exists sa. split; [assumption |].
  rewrite fold_subst_sa_fold_foldr.
  erewrite equal_fold_subst_sa; eauto.
  replace (list_to_map (map_to_list rho)) with rho
    by (symmetry; apply list_to_map_to_list). 
  assumption.
Qed.

Lemma subst_rho_free_vars :
  forall t rho x,
    x # subst_rho rho t ->
    rho !! x = None ->
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
      apply HFrv in H1. simpl in H1.

      assert (H': included (frv tyx) rgns) 
        by  (apply IncludedUnion_Name_1 in H1; destruct H1; assumption). 
      apply ExtendedTcInv_2; eauto. }
     
    { assert (H'' : included (frv Ty_Effect) rgns /\ 
                    included (free_rgn_vars_in_eps effe) rgns).
      eapply IHHExp2; eauto.
      - apply HFrv in H1. simpl in H1.
        assert (H''': included (frv tyx) rgns) 
          by  (apply IncludedUnion_Name_1 in H1; destruct H1; assumption).  
        apply ExtendedTcInv_2; eauto. 
      - apply HFrv in H1. simpl in H1.
        split; auto.
        intro. intro. contradict H2. apply NotFreeInEmptyEps. }
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
	  - split; intros x HFree.
	    + inversion HFree.
	    + contradict HFree. apply NotFreeInEmptyEps.
	  - split; intros x HFree.
	    + inversion HFree.
	    + contradict HFree. apply NotFreeInEmptyEps.
	  - assert (H1 : included (frv (Ty_Ref (Rgn_Const true true r) t0)) rgns /\ 
	                 included (free_rgn_vars_in_eps eff) rgns)
	      by (eapply IHHExp; eauto).
	    destruct H1 as [H2 H3].
	    intuition. inversion H.
	  - split; intros x HFree.
	    + inversion HFree.
	    + contradict HFree. apply NotFreeInEmptyEps.
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
               assert (rho !! x0  = None) 
                 by (eapply contrapositiveTcRho; eauto; apply HRgn);
               rewrite  SUBST_FRESH; [rewrite <- x; econstructor; eauto | 
                                      eapply subst_rho_free_vars; eauto]  ] ).
Qed.


Lemma extended_rho :
  forall stty rho env ctxt,
    TcEnv (stty, rho, env, ctxt) ->
    forall x r rgns,
      TcRho (rho, rgns) ->
      not_set_elem rgns x ->
      TcEnv (stty, update_R (x, r) rho, env, ctxt). 
Proof.
  intros stty rho env ctxt HEnv x r rgns HRho HRgns. 
  inversion_clear HEnv as [ stty' rho' env' ctxt' HE HT HV].  
  inversion  HRho as [rho' rgns' HRgn' HVal'']; subst.
  constructor; auto.
  intros x0 v0 t0 HE' HT'. eapply HV in HE'; eauto. unfold update_R. simpl. 
  rewrite subst_add_comm.  
  - eapply subst_rho_fresh_var; eauto.
  - eapply map_to_list_unique with (m:=<[x:=r]> rho); eauto.
  - unfold not_set_elem in HRgns. unfold Ensembles.Complement in HRgns.
    apply not_elem_of_dom.
    intro. apply elem_of_dom in H.
    unfold is_Some in H. apply NotNoneIsSome in H.
    eapply HRgn' in H. contradiction. 
Qed.

Lemma update_env:
  forall stty rho env ctxt, 
    TcEnv (stty, rho, env, ctxt) -> 
    (forall x v t, 
       TcVal (stty, v, subst_rho rho t) ->
       TcEnv (stty, rho, update_E (x, v) env, update_T (x, t) ctxt) ).
Proof. 
  intros stty rho env ctxt HEnv x v t HTc.  
  inversion_clear HEnv as [ stty' rho' env' ctxt' HE HT HV]. 
  apply TC_Env;
  unfold find_E, update_E, find_T, update_T in *; simpl.
  clear HTc.
  - intros x0 v0 HF. (** "TcEnv is well-typed: HE" **)
    destruct (ascii_dec x0 x) as [c | c]; subst.
    + subst. exists t.
      apply lookup_insert.
    + eapply G_diff_keys_1 in HF; auto; subst. 
      destruct (HE x0 v0) as [t0 HU] ; [auto | ] ; exists t0.
      eapply G_diff_keys_2; [ auto | exact HU]. 
  - intros x0 t0 HF. (** "TcEnv is well-typed: HT".  **)
    destruct (ascii_dec x0 x) as [c | c]; intros; subst.    
    + exists v. apply lookup_insert.
    + eapply G_diff_keys_1 in HF; auto.
      destruct (HT x0 t0) as [x1 ?] ; [auto | ].
      exists x1; [eapply G_diff_keys_2]; auto.
  - intros x0 v0 t0 HFindE HFindT. (** "Type preservation: HV". **)
    destruct (ascii_dec x0 x) as [c | c]; intros; subst.
    + assert (<[x:=v]> env !! x = Some v) by (apply lookup_insert).
      rewrite H in HFindE.
      inversion HFindE; subst.
      assert (<[x:=t]> ctxt !! x = Some t) by (apply lookup_insert).
      rewrite H0 in HFindT.      
      inversion HFindT; subst. assumption.
    + eapply G_diff_keys_1 in HFindE; auto.
      eapply G_diff_keys_1 in HFindT; auto.
      eapply HV; eauto.
Qed.
