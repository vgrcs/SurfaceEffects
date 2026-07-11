From stdpp Require Import gmap.
From stdpp Require Import fin_maps.
From stdpp Require Import list.
From stdpp Require Import base.
From stdpp Require Import strings.
Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import theories.Core.Regions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.StaticActions.
Require Import theories.Meta.MapFacts.
Require Export theories.Meta.RegionSubstitutionFacts.
Require Import Coq.FSets.FMapFacts.
Require Import Ascii.

Import Ensembles.

Lemma TcRhoIncludedNoFreeVarsSa:
  forall k rc r x,
    free_rgn_vars_in_rgn (subst_rgn k (Rgn_Const true false rc) r) x ->
    free_rgn_vars_in_rgn r x.
Proof.
  intros.
  unfold Region_in_Type in r.
  dependent induction r;
  unfold free_rgn_vars_in_rgn, subst_rgn in *; simpl.
  - inversion H.
  - destruct (ascii_dec k r); subst; simpl in *.
    + inversion H.
    + assumption.
  - inversion H.
Qed.


Lemma TcRhoIncludedNoFreeVarsRgn:
  forall k rc sa x,
    free_rgn_vars_in_sa (subst_sa k (Rgn_Const true false rc) sa) x ->
    free_rgn_vars_in_sa sa x.
Proof.
  intros.
  dependent induction sa;
  unfold free_rgn_vars_in_sa, subst_sa in *; simpl;
  eapply TcRhoIncludedNoFreeVarsSa; eauto.
Qed.

Lemma TcRhoIncludedNoFreeVarsEps:
  forall k rc x e,
    (free_rgn_vars_in_eps (subst_eps k (Rgn_Const _ _ rc) e)) x ->
    (free_rgn_vars_in_eps e) x.
Proof.
  intros.
  unfold free_rgn_vars_in_eps in *.
  destruct H as [sa H].
  unfold subst_eps in H. 
  destruct H as [H1 H2].
  destruct H1 as [sa' H3].
  exists sa'; intuition.
  rewrite <- H0 in H2.
  eapply TcRhoIncludedNoFreeVarsRgn; eauto.
Qed.

Lemma TcRhoIncludedNoFreeVarsEps_included:
  forall k rc e,
    included
      (free_rgn_vars_in_eps (subst_eps k (Rgn_Const _ _ rc) e))
      (free_rgn_vars_in_eps e).
Proof.
  intros k rc e.
  unfold included, Included, In. 
  intro. intro.
  eapply TcRhoIncludedNoFreeVarsEps; eauto.
Qed.

Lemma TcRhoIncludedNoFreeVarsSa_aux:
  forall x rc sa,
    ~ free_rgn_vars_in_sa (subst_sa x (Rgn_Const true false rc) sa) x.
Proof.
  intros.
  induction sa; unfold subst_sa in *;
  unfold Region_in_Type in r; dependent induction r; simpl; 
  try (solve [ intro; contradict H | 
               intro; unfold free_rgn_vars_in_rgn in H;
               destruct (ascii_dec x r); subst; 
               [inversion H | inversion H; symmetry in H0; contradiction] ]).
Qed.

Lemma TcRhoIncludedNoFreeVarsEps_aux:
  forall x e0 e,
  ~ free_rgn_vars_in_eps (subst_eps x (Rgn_Const true false e0) e) x.
Proof.
  intros.
  unfold subst_in_eff.  intro.
  unfold free_rgn_vars_in_eps, subst_eps in *.
  destruct H as [sa [H1 H2]].
  destruct H1 as [sa' [H3 H4]].
  rewrite <- H4 in H2.
  eapply TcRhoIncludedNoFreeVarsSa_aux; eauto.
Qed.


Lemma TcRhoIncludedNoFreeVarsTyRef:
  forall rho rgns r0 t x,
    TcRho (rho, rgns) ->
    included (set_union (free_rgn_vars_in_rgn r0) (frv t)) rgns ->
    ~ free_rgn_vars_in_rgn (fold_subst_rgn rho r0) x.
Proof.
  intros rho rgns r0 t x HRho HInc H.
  generalize dependent r0.
  unfold Region_in_Type.
  dependent induction r0; intros.
  - rewrite subst_rho_rgn_const in H.
    simpl in H. contradiction.
  - destruct (ascii_dec x r) as [c | c].
    + inversion c; subst.   
      inversion HRho; subst.   
      contradict H.
      destruct (subst_rho_fvar_1 rho r) as [[v' H1] | H1]. 
      * rewrite H1. simpl. intro. contradiction.
      * rewrite H1. simpl. intro. 
        unfold set_elem, In in H2.
        destruct H2 with (r:=r). 
        { apply H4 in HInc.
          - apply NotNoneIsSome in HInc.
            destruct HInc.
            apply subst_rho_fvar_2 in H5. 
            rewrite H5 in H1. 
            inversion H1.
          - apply Union_introl. simpl. auto. }
   + inversion HRho; subst.
     contradict H.
     destruct (subst_rho_fvar_1 rho r) as [[v' H0] | H0].
     * rewrite H0. simpl. intro. contradiction.
     * rewrite H0. simpl. intro. inversion H. auto.
  - rewrite subst_rho_index in H.
    simpl in H. contradiction. 
Qed.


Lemma not_free_vars_in_head_after_subst:
  forall x v sa,
    ~free_rgn_vars_in_sa (head_fold_subst_sa_alt (x, v) sa) x.
Proof.
  intros.
  unfold head_fold_subst_sa_alt. destruct sa;
   unfold Region_in_Type in r;
  dependent induction r;
    unfold free_rgn_vars_in_rgn, subst_rgn in *; simpl;
    try( solve[intro; inversion H]).
  - destruct (ascii_dec x r); subst.
    + unfold free_rgn_vars_in_rgn.
      intro. inversion H.
    + unfold free_rgn_vars_in_rgn.
      intro. inversion H. subst. contradiction.
  - destruct (ascii_dec x r).
    + unfold free_rgn_vars_in_rgn.
      intro. inversion H.
    + unfold free_rgn_vars_in_rgn.
      intro. inversion H. subst. contradiction.
  - destruct (ascii_dec x r).
    + unfold free_rgn_vars_in_rgn.
      intro. inversion H.
    + unfold free_rgn_vars_in_rgn.
      intro. inversion H. subst. contradiction.
Qed. 

Lemma not_free_vars_in_head_after_subst_2:
  forall r x v sa,
    r <> x ->
    free_rgn_vars_in_sa (head_fold_subst_sa_alt (r, v) sa) x ->
    free_rgn_vars_in_sa sa x.
Proof.
  intros. unfold free_rgn_vars_in_sa in *.
  unfold head_fold_subst_sa_alt in *. 
  unfold fold_subst_sa_alt in *.
  destruct sa;
  unfold Region_in_Type in r0;
  dependent induction r0;
  unfold free_rgn_vars_in_rgn, subst_rgn in *;
    simpl in *; try (solve
                       [assumption |
                         destruct (ascii_dec r r0); [inversion H0 |
                                                             assumption]]).
Qed.

Lemma TcRhoIncludedNoFreeVarsSa_aux_fold_3:
  forall l sa a x,
    free_rgn_vars_in_sa (head_fold_subst_sa_alt a (fold_subst_sa_alt l sa)) x ->
    free_rgn_vars_in_sa sa x.
Proof.
  intros.
  apply TcRhoIncludedNoFreeVarsSa_aux_fold with (rho:=l).
  destruct a as [r v].
  destruct (ascii_dec r x); subst; simpl in *.
  - contradict H. apply not_free_vars_in_head_after_subst.
  - eapply not_free_vars_in_head_after_subst_2; eauto.
Qed.  

Lemma subst_rgn_not_elem_1:
  forall r v x,
    x ≠ r ->
    uncurry (λ (x0 : RgnName) (r0 : RgnVal) (rgn : Region_in_Type),
        subst_rgn x0 (Rgn_Const true false r0) rgn)
      (r, v) (Rgn_FVar true true x) = (Rgn_FVar true true x).
Proof.
  intros.
  unfold subst_rgn. simpl.
  destruct (ascii_dec r x); subst.
  - contradiction.
  - reflexivity.
Qed.

Lemma subst_rgn_not_elem_2:
  forall r v n,
    uncurry
      (λ (x0 : RgnName) (r0 : RgnVal) (rgn : Region_in_Type),
        subst_rgn x0 (Rgn_Const true false r0) rgn)
      (r, v) (Rgn_BVar true true n) = (Rgn_BVar true true n).
Proof.
  intros.
  unfold subst_rgn. simpl.
  reflexivity.
Qed.

                                                    
Lemma not_free_vars_compose_head_sa_fold:
  forall r v sa x,
    free_rgn_vars_in_sa sa x ->
    x ≠ r ->
    free_rgn_vars_in_sa (head_fold_subst_sa_alt (r, v) sa) x.
Proof.
  intros. unfold free_rgn_vars_in_sa in *.
  unfold head_fold_subst_sa_alt in *. 
  unfold fold_subst_sa_alt in *.
  destruct sa;
  unfold Region_in_Type in r0;
  dependent induction r0;
    unfold free_rgn_vars_in_rgn. try (solve [unfold subst_rgn in *; assumption]).
  - inversion H; subst.
    replace (uncurry
      (λ (x0 : RgnName) (r0 : RgnVal) (rgn : Region_in_Type),
        subst_rgn x0 (Rgn_Const true false r0) rgn) (r, v) (Rgn_FVar true true x))
      with (Rgn_FVar true true x).
    + apply In_singleton.
    + symmetry; apply subst_rgn_not_elem_1; auto.
  - replace ( uncurry
      (λ (x0 : RgnName) (r0 : RgnVal) (rgn : Region_in_Type),
        subst_rgn x0 (Rgn_Const true false r0) rgn) (r, v) (Rgn_BVar true true n))
      with (Rgn_BVar true true n).
    + inversion H.
    + unfold subst_rgn. simpl.
      reflexivity.
  - replace (uncurry
      (λ (x0 : RgnName) (r1 : RgnVal) (rgn : Region_in_Type),
        subst_rgn x0 (Rgn_Const true false r1) rgn) (r, v) (Rgn_Const true true r0))
              with ((Rgn_Const true true r0)).
    + inversion H.
    + unfold subst_rgn. simpl.
      reflexivity.
  - inversion H; subst.
    replace (uncurry
      (λ (x0 : RgnName) (r0 : RgnVal) (rgn : Region_in_Type),
        subst_rgn x0 (Rgn_Const true false r0) rgn) (r, v) (Rgn_FVar true true x))
      with (Rgn_FVar true true x).
    + apply In_singleton.
    + symmetry; apply subst_rgn_not_elem_1; auto.
  - replace ( uncurry
      (λ (x0 : RgnName) (r0 : RgnVal) (rgn : Region_in_Type),
        subst_rgn x0 (Rgn_Const true false r0) rgn) (r, v) (Rgn_BVar true true n))
      with (Rgn_BVar true true n).
    + inversion H.
    + unfold subst_rgn. simpl.
      reflexivity.
  - replace (uncurry
      (λ (x0 : RgnName) (r1 : RgnVal) (rgn : Region_in_Type),
        subst_rgn x0 (Rgn_Const true false r1) rgn) (r, v) (Rgn_Const true true r0))
              with ((Rgn_Const true true r0)).
    + inversion H.
    + unfold subst_rgn. simpl.
      reflexivity.
  - inversion H; subst.
    replace (uncurry
      (λ (x0 : RgnName) (r0 : RgnVal) (rgn : Region_in_Type),
        subst_rgn x0 (Rgn_Const true false r0) rgn) (r, v) (Rgn_FVar true true x))
      with (Rgn_FVar true true x).
    + apply In_singleton.
    + symmetry; apply subst_rgn_not_elem_1; auto.
  - replace ( uncurry
      (λ (x0 : RgnName) (r0 : RgnVal) (rgn : Region_in_Type),
        subst_rgn x0 (Rgn_Const true false r0) rgn) (r, v) (Rgn_BVar true true n))
      with (Rgn_BVar true true n).
    + inversion H.
    + unfold subst_rgn. simpl.
      reflexivity.
Qed.      
     
   

Lemma not_free_vars_compose_head_eps_fold:
  forall a l e x,
    ~ (free_rgn_vars_in_eps (fold_subst_eps_alt_head a e) x /\
         free_rgn_vars_in_eps (fold_subst_eps_alt l e) x) ->
    ~free_rgn_vars_in_eps (fold_subst_eps_alt_head a (fold_subst_eps_alt l e)) x.    
Proof.
  intros. intro. apply H. split. clear H. 
  - unfold free_rgn_vars_in_eps in H0. 
    destruct H0 as [sa [H1 H2]].
    unfold fold_subst_eps_alt_head in H1.
    destruct H1 as [sa' [Ha Hb]].
    unfold fold_subst_eps_alt in Ha.
    destruct Ha as [sa'' [Hf Hg]].
    destruct a as [r v].
    destruct (ascii_dec x r).
    + subst. contradict H2.
      apply not_free_vars_in_head_after_subst.
    + subst.
      unfold free_rgn_vars_in_eps. unfold fold_subst_eps_alt_head.
      exists (head_fold_subst_sa_alt (r, v) sa'').
      split.
      * unfold fold_subst_eps_alt_head.
        exists sa''. intuition.
      * subst.    
        apply not_free_vars_in_head_after_subst_2 in H2; auto.
        apply TcRhoIncludedNoFreeVarsSa_aux_fold in H2.
        apply not_free_vars_compose_head_sa_fold; auto.
  - apply TcRhoIncludedNoFreeVarsEps_aux_fold_1 in H0.
    assumption.
Qed.


Lemma TcRhoIncludedNoFreeVarsEps_find:
  forall (rho: Rho) (x: RgnName),
    rho !! x <> None ->
    forall e, ~(free_rgn_vars_in_eps (fold_subst_eps rho e)) x.
Proof.
  intros.
  unfold find_R in H.
  apply NotNoneIsSome in H. destruct H as [v H].
  apply find_R_in_list with (p:=(x,v)) in H.
  rewrite fold_subst_eps_fold_foldr.
  induction (map_to_list rho); simpl.
  - contradict H.
    apply not_elem_of_nil.
  - rewrite fold_subst_eps_cons.
    apply not_free_vars_compose_head_eps_fold. 
    apply elem_of_cons in H.
    destruct H as [Ha | Hb].
    + intro. destruct H.
      subst. clear IHl. clear H0. 
      unfold free_rgn_vars_in_eps, fold_subst_eps_alt_head in *.
      destruct H as [sa [[sa' [H1 H2]]]].
      rewrite <- H2 in H.  clear H2. 
      contradict H. apply not_free_vars_in_head_after_subst.                
    + intro. destruct H.
      apply IHl; assumption.
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
            + unfold In in H0. eapply TcRhoIncludedNoFreeVarsEps_aux_fold. 
              apply free_rgn_vars_in_eps_map_to_list. eauto. 
            + unfold included, Included, Ensembles.In in *.
              intro. intro.
              apply HInc.
              apply Ensembles.Union_intror. apply Ensembles.Union_introl.
              apply Ensembles.Union_introl. assumption.
          - eapply TcRhoIncludedNoFreeVarsEps_main with (e:=e0); eauto.
            + unfold In in H0. eapply TcRhoIncludedNoFreeVarsEps_aux_fold.
              apply free_rgn_vars_in_eps_map_to_list. eauto. 
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
      * eapply TcRhoIncludedNoFreeVarsEps_aux_fold.
        apply free_rgn_vars_in_eps_map_to_list. eauto. 
      * unfold included, Included, In in *. intro. intro.
        apply HInc.
        apply Union_introl. assumption.
    + apply IHt; auto. 
      unfold included, Included in *. 
      intros. apply HInc. 
      apply Union_intror. assumption.
Qed.


Lemma subst_rho_free_vars_union_1 :
  forall x (e1 e2 : Ensemble RgnName),
    not_set_elem (set_union e1 e2) x ->
    not_set_elem e1 x /\ not_set_elem e2 x.
Proof.
  intros. split; intro; apply H; [ apply Union_introl | apply Union_intror]; auto.
Qed.

Lemma subst_rho_free_vars_union_2 :
  forall x (e1 e2 : Ensemble RgnName),
    not_set_elem e1 x /\ not_set_elem e2 x ->
    not_set_elem (set_union e1 e2) x.
Proof.
  intros. destruct H. intro. destruct H1; [apply H | apply H0]; auto.
Qed.



Lemma contrapositiveTcRho :
  forall (rho : Rho) (rgns : Ensemble RgnName) (x : RgnName),
    (forall r, rho !! r <> None -> set_elem rgns r) ->
    not_set_elem rgns x ->
    rho !! x = None.
Proof.
  intros.
  unfold not_set_elem in H0. unfold Ensembles.Complement in H0.
  unfold set_elem in H. unfold Ensembles.Complement in H. 
  apply not_elem_of_dom.
  intro. apply H0.
  assert (Hr : forall r (rho : Rho), r ∈ dom rho -> rho !! r <> None)
    by (intros; apply elem_of_dom in H2; apply not_eq_None_Some in H2; assumption).
  apply H.
  apply Hr.
  assumption.
Qed.
