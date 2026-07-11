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
Require Import Coq.FSets.FMapFacts.
Require Import Ascii.

Import Ensembles.

Lemma find_R_in_list:
  forall (rho : Rho) (p : RgnName*RgnVal),
    rho !! p.1 = Some p.2 ->
    p ∈ map_to_list rho.
Proof.
  apply elem_of_map_to_list'.
Qed.
  

Lemma subst_rgn_aux_comm :
  forall j1 j2 z1 z2 r,
    j1 <> j2 ->
    subst_rgn j1 (Rgn_Const true false z1) (subst_rgn j2 (Rgn_Const true false z2) r) =
      subst_rgn j2 (Rgn_Const true false z2) (subst_rgn j1 (Rgn_Const true false z1) r).
Proof.
  intros.
  generalize dependent r.
  unfold Region_in_Type.
  dependent induction r; intros; unfold subst_rgn; simpl.
  - reflexivity.
  - destruct (ascii_dec j2 r); destruct (ascii_dec j1 r); simpl.
    + subst. contradiction.
    + subst. destruct (ascii_dec r r).
      * reflexivity.
      * contradiction.
    + reflexivity.
    + subst. destruct (ascii_dec j2 r); subst.
      * contradiction.
      * reflexivity.
  - reflexivity.
Qed.

Lemma subst_sa_aux_comm:
  forall j1 j2 z1 z2 sa,
    j1 <> j2 ->
    subst_sa j1 (Rgn_Const true false z1) (subst_sa j2 (Rgn_Const true false z2) sa) =
      subst_sa j2 (Rgn_Const true false z2) (subst_sa j1 (Rgn_Const true false z1) sa).
Proof.
  intros j1 j2 z1 z2 sa H. induction sa.
  - generalize dependent r. unfold Region_in_Type. dependent induction r; simpl.
    + reflexivity.
    + destruct (ascii_dec j1 r); destruct (ascii_dec j2 r); subst; simpl.
      * contradiction.
      * destruct (ascii_dec r r); subst;
          [reflexivity | contradiction].
      * destruct (ascii_dec r r); subst;
          [reflexivity | contradiction].
      * { destruct (ascii_dec j1 r); destruct (ascii_dec j2 r); subst; simpl.
          - contradiction.
          - contradiction.
          - contradiction.
          - reflexivity. }
    + reflexivity.
  - generalize dependent r. unfold Region_in_Type. dependent induction r; simpl.
    + reflexivity.
    + destruct (ascii_dec j1 r); destruct (ascii_dec j2 r); subst; simpl.
      * contradiction.
      * destruct (ascii_dec r r); subst;
          [reflexivity | contradiction].
      * destruct (ascii_dec r r); subst;
          [reflexivity | contradiction].
      * { destruct (ascii_dec j1 r); destruct (ascii_dec j2 r); subst; simpl.
          - contradiction.
          - contradiction.
          - contradiction.
          - reflexivity. }
    + reflexivity.
  - generalize dependent r. unfold Region_in_Type. dependent induction r; simpl.
    + reflexivity.
    + destruct (ascii_dec j1 r); destruct (ascii_dec j2 r); subst; simpl.
      * contradiction.
      * destruct (ascii_dec r r); subst;
          [reflexivity | contradiction].
      * destruct (ascii_dec r r); subst;
          [reflexivity | contradiction].
      * { destruct (ascii_dec j1 r); destruct (ascii_dec j2 r); subst; simpl.
          - contradiction.
          - contradiction.
          - contradiction.
          - reflexivity. }
    + reflexivity.
Qed.

  
Lemma subst_eps_aux_comm :
  forall j1 j2 z1 z2 e,
    j1 <> j2 ->
    subst_in_eff j1 z1 (subst_in_eff j2 z2 e) =
      subst_in_eff j2 z2 (subst_in_eff j1 z1 e).
Proof.
  intros. unfold subst_in_eff, subst_eps.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Ensembles.In; split; intros x H1. 
  - destruct H1 as [sa [? ?]].  destruct H0 as [sa' [? ?]].   
    exists (subst_sa j1 (Rgn_Const true false z1) sa').
    split. 
    + exists sa'.
      split.
      * auto.
      * reflexivity.
    + rewrite <- H1. rewrite <- H2.
      rewrite subst_sa_aux_comm.
      * reflexivity.
      * auto.
  - destruct H1 as [sa [? ?]].  destruct H0 as [sa' [? ?]].   
    exists (subst_sa j2 (Rgn_Const true false z2) sa').
    split. 
    + exists sa'.
      split.
      * auto.
      * reflexivity.
    + rewrite <- H1. rewrite <- H2.
      rewrite subst_sa_aux_comm;[reflexivity | assumption].
Qed.                                        


Lemma subst_in_type_fold_foldr:
  forall (rho : Rho) (ty :Tau),
    map_fold subst_in_type ty rho =
      (foldr (uncurry subst_in_type)) ty (map_to_list rho).
Proof.
  intros rho tau.
  apply map_fold_foldr.
Qed.

Lemma subst_rgn_fold_foldr:
  forall (rho : Rho) (rt : Region_in_Type),
    map_fold (fun x r rgn => subst_rgn x (Rgn_Const true false r) rgn) rt rho =
      (foldr (uncurry(fun x r rgn => subst_rgn x (Rgn_Const true false r) rgn)))
        rt (map_to_list rho).
Proof.
  intros.
  apply map_fold_foldr.
Qed.
    

Lemma subst_rho_natural :
  forall (rho : Rho),
    subst_rho rho Ty_Natural = Ty_Natural.
Proof.
  intros. unfold subst_rho.
  rewrite subst_in_type_fold_foldr.
  induction (map_to_list rho); simpl.
  - reflexivity.
  - rewrite IHl.
    replace (uncurry subst_in_type a Ty_Natural)
      with (Ty_Natural)
      by (unfold uncurry; induction a; reflexivity).
    reflexivity.
Qed.

Lemma subst_rho_boolean :
  forall rho, subst_rho rho Ty_Boolean = Ty_Boolean.
Proof.  
  intros. unfold subst_rho.
  rewrite subst_in_type_fold_foldr.
  induction (map_to_list rho); simpl.
  - reflexivity.
  - rewrite IHl.
    replace (uncurry subst_in_type a Ty_Boolean)
      with (Ty_Boolean)
      by (unfold uncurry; induction a; reflexivity).
    reflexivity.
Qed.

Lemma subst_rho_unit :
  forall rho, subst_rho rho Ty_Unit = Ty_Unit.
Proof.  
  intros. unfold subst_rho.
  rewrite subst_in_type_fold_foldr.
  induction (map_to_list rho); simpl.
  - reflexivity.
  - rewrite IHl.
    replace (uncurry subst_in_type a Ty_Unit)
      with (Ty_Unit)
      by (unfold uncurry; induction a; reflexivity).
    reflexivity.
Qed.

Lemma subst_rho_effect :
  forall rho, subst_rho rho Ty_Effect = Ty_Effect.
Proof.
  intros. unfold subst_rho.
  rewrite subst_in_type_fold_foldr.
  induction (map_to_list rho); simpl.
  - reflexivity.
  - rewrite IHl.
    replace (uncurry subst_in_type a Ty_Effect)
      with (Ty_Effect)
      by (unfold uncurry; induction a; reflexivity).
    reflexivity.
Qed.

Lemma fold_subst_rho_free_vars_rgn_not_elem:
  forall (l: list (RgnName*RgnVal)) (x : RgnName),
    x ∉ l.*1 ->
    foldr (uncurry (λ (x0 : RgnName) (r : RgnVal) (rgn : Region_in_Type),
               subst_rgn x0 (Rgn_Const true false r) rgn))
      (Rgn_FVar true true x) l =
      (Rgn_FVar true true x).
Proof.
  intros.
  induction l; simpl.
   - reflexivity.
  - rewrite IHl. unfold subst_rgn.
    destruct a.  simpl. 
    destruct (ascii_dec r x).
    + simpl in H. subst. 
      contradict H. apply elem_of_cons. left. reflexivity.
    + reflexivity.
    + apply not_elem_of_cons in H.
      destruct H. assumption.
Qed.     
   


Lemma fold_subst_rho_free_vars_rgn_not_elem_2:
  forall (l: list (RgnName*RgnVal)) (p : (RgnName*RgnVal)),
    p.1 ∉ dom (list_to_map l : Rho) ->
    foldr (uncurry (λ (x0 : RgnName) (r : RgnVal) (rgn : Region_in_Type),
               subst_rgn x0 (Rgn_Const true false r) rgn))
      (Rgn_FVar true true p.1) l =
      (Rgn_FVar true true p.1).
Proof.
  intros.
  apply not_elem_of_dom in H.
  induction l; simpl.
   - reflexivity.
   - rewrite IHl.
     + unfold subst_rgn.  
       apply not_elem_of_list_to_map in H.
       apply not_elem_of_cons in H. destruct H. clear H0.
       destruct a.  simpl in *.
       destruct (ascii_dec r p.1).
       * contradict H. auto.
       * reflexivity.
     + apply not_elem_of_list_to_map in H.
       apply not_elem_of_cons in H. destruct H.
       apply not_elem_of_list_to_map.
       assumption.
Qed.     

Lemma fold_subst_rho_free_vars_rgn_aux:
  forall (rho : Rho) (r : RgnName),
    rho !! r = None ->
    fold_subst_rgn rho (Rgn_FVar true true r) = (Rgn_FVar true true r).
Proof.
  intros. unfold fold_subst_rgn.
  rewrite subst_rgn_fold_foldr.
  apply fold_subst_rho_free_vars_rgn_not_elem.
  apply not_elem_of_list_to_map.
  replace (list_to_map (map_to_list rho))
    with (rho).
  - assumption.
  - symmetry. apply list_to_map_to_list.
Qed.      

Lemma fold_subst_rho_free_vars_rgn_aux_2:
  forall (l : list (RgnName*RgnVal)) (r : RgnName),
    r ∉ dom (list_to_map l : Rho) ->
    fold_subst_rgn (list_to_map l) (Rgn_FVar true true r) = (Rgn_FVar true true r).
Proof.
  intros.
  apply  fold_subst_rho_free_vars_rgn_aux.
  apply not_elem_of_dom_1 in H.
  assumption.
Qed.


Lemma subst_rho_rgn_const_aux :
  forall a c,
    uncurry (λ (x1 : RgnName) (r : RgnVal) (rgn : Region_in_Type),
        subst_rgn x1 (Rgn_Const true false r) rgn) a (Rgn_Const true true c) =
      Rgn_Const true true c.
Proof.
  intros. unfold subst_rgn.
  destruct a. simpl.
  reflexivity.
Qed.
  

Lemma subst_rho_rgn_const :
  forall rho c,
    fold_subst_rgn rho (Rgn_Const true true c) = (Rgn_Const true true c).
Proof.
  intros.
  unfold fold_subst_rgn.
  rewrite subst_rgn_fold_foldr.
  induction (map_to_list rho); simpl.
  - reflexivity.
  - rewrite IHl.
    apply subst_rho_rgn_const_aux.            
Qed.    

Lemma subst_rho_index :
  forall rho n,
    fold_subst_rgn rho (Rgn_BVar true true n) = (Rgn_BVar true true n).
Proof.
  intros.
  unfold fold_subst_rgn.
  rewrite subst_rgn_fold_foldr.
  induction (map_to_list rho); simpl.
  - reflexivity.
  - rewrite IHl. unfold subst_rgn.
    destruct a. simpl.
    reflexivity.
Qed.

Lemma subst_rho_pair : 
  forall rho t1 t2,
    subst_rho rho (Ty_Pair t1 t2) = Ty_Pair (subst_rho rho t1) (subst_rho rho t2).
Proof.
  intros.
  unfold subst_rho.  
  do 3 rewrite subst_in_type_fold_foldr.
  induction (map_to_list rho); simpl.
  - reflexivity.
  - rewrite IHl; simpl.
    destruct a.
    assert (Hr: forall r u t1 t2,
               (uncurry subst_in_type) (r, u) (Ty_Pair t1 t2) =
                 Ty_Pair ((uncurry subst_in_type) (r, u) t1)
                   ((uncurry subst_in_type) (r, u) t2))
        by (unfold subst_in_type, subst_type; simpl; f_equal).
    rewrite Hr.
    f_equal.
Qed.


Definition subst_in_rgn_alt (r : RgnName) (v : RgnVal) (rgn : Region_in_Type)
  : Region_in_Type
  := subst_rgn r (Rgn_Const true false v) rgn.

Definition fold_subst_rgn_alt (lrho : list(RgnName*RgnVal)) (rt : Region_in_Type)
 := foldr (uncurry subst_in_rgn_alt) rt lrho.
                              


Lemma fold_subst_rgn_cons:
  forall r v l (rt : Region_in_Type),
    fold_subst_rgn_alt ((r,v) :: l) rt =
      subst_in_rgn r v (fold_subst_rgn_alt l rt).
Proof.
  intros.
  generalize dependent rt.
  unfold Region_in_Type. dependent induction rt.
  - unfold fold_subst_rgn_alt.
    rewrite foldr_cons; simpl.
    reflexivity.
  - unfold fold_subst_rgn_alt.
    rewrite foldr_cons; simpl.
    reflexivity.
  - unfold fold_subst_rgn_alt.
    rewrite foldr_cons; simpl.
    reflexivity.
Qed.    


Definition fold_subst_sa_alt (lrho: list (RgnName * RgnVal)) (sa : StaticAction) :=
  let fn := λ rt,
      (foldr (uncurry (λ x r rgn, subst_rgn x (Rgn_Const true false r) rgn))) rt lrho
  in match sa with
    | SA_Alloc rt => SA_Alloc (fn rt)
    | SA_Read rt => SA_Read (fn rt)
    | SA_Write rt => SA_Write (fn rt)
  end.

Definition head_fold_subst_sa_alt (p: (RgnName * RgnVal)) (sa : StaticAction) :=
  let fn := λ rt,
      (uncurry (λ x r rgn, subst_rgn x (Rgn_Const true false r) rgn)) p rt 
  in match sa with
    | SA_Alloc rt => SA_Alloc (fn rt)
    | SA_Read rt => SA_Read (fn rt)
    | SA_Write rt => SA_Write (fn rt)
  end.

Lemma fold_subst_sa_cons:
  forall r rs sa,
    fold_subst_sa_alt (r :: rs) sa = head_fold_subst_sa_alt r (fold_subst_sa_alt rs sa).
Proof.
  intros.
  unfold fold_subst_sa_alt, head_fold_subst_sa_alt.
  destruct sa; simpl; f_equal.
Qed.
  

Lemma fold_subst_sa_fold_foldr:
  forall rho sa,
    fold_subst_sa rho sa = fold_subst_sa_alt (map_to_list rho) sa.
Proof.
  intros.
  unfold fold_subst_sa, fold_subst_sa_alt.
  induction sa; f_equal; unfold fold_subst_rgn; now rewrite subst_rgn_fold_foldr.
Qed.

Definition fold_subst_eps_alt (lrho: list (RgnName * RgnVal)) eps :=
  fun sa => exists sa', eps sa' /\ fold_subst_sa_alt lrho sa' = sa.

Definition fold_subst_eps_alt_head (p: (RgnName * RgnVal)) eps :=
  fun sa => exists sa', eps sa' /\ head_fold_subst_sa_alt p sa' = sa.


Lemma fold_subst_eps_fold_foldr:
  forall rho eps,
  fold_subst_eps rho eps = fold_subst_eps_alt (map_to_list rho) eps.
Proof.
  intros.
  unfold fold_subst_eps, fold_subst_eps_alt.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Ensembles.In; split; intros x H.
  - destruct H as [? [? H2]]. exists x0. split; [assumption|].
    now rewrite <- fold_subst_sa_fold_foldr.
  - destruct H as [? [? H2]]. exists x0. split; [assumption|].
    now rewrite fold_subst_sa_fold_foldr.
Qed.


Lemma fold_subst_eps_cons:
  forall r rs eps,
    fold_subst_eps_alt (r :: rs) eps =
      fold_subst_eps_alt_head r (fold_subst_eps_alt rs eps).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Ensembles.In; split; intros x H.
  - unfold fold_subst_eps_alt, fold_subst_eps_alt_head in *.
    destruct x; simpl;
    destruct H as [sa [H1 H2]].
    + exists (fold_subst_sa_alt rs sa).
      split; [exists sa; intuition |].
      rewrite <- H2. now rewrite fold_subst_sa_cons.
    + exists (fold_subst_sa_alt rs sa).
      split; [exists sa; intuition |].
      rewrite <- H2. now rewrite fold_subst_sa_cons.
    + exists (fold_subst_sa_alt rs sa).
      split; [exists sa; intuition |].
      rewrite <- H2. now rewrite fold_subst_sa_cons.
  - unfold fold_subst_eps_alt, fold_subst_eps_alt_head in *.
    destruct x; simpl;
      destruct H as [sa [[sa' [H1 H2]] H3]].
    + rewrite <- H2 in H3.
      exists sa'; split; [assumption | now rewrite fold_subst_sa_cons].
    + rewrite <- H2 in H3.
      exists sa'; split; [assumption | now rewrite fold_subst_sa_cons].
    + rewrite <- H2 in H3.
      exists sa'; split; [assumption | now rewrite fold_subst_sa_cons].    
Qed.


Lemma subst_rho_arrow :
  forall rho tyr1 eff1 tyr2 eff2 tyr3,
    subst_rho rho (Ty_Arrow tyr1 eff1 tyr2 eff2 tyr3) =
      Ty_Arrow (subst_rho rho tyr1) (fold_subst_eps rho eff1)
        (subst_rho rho tyr2) (fold_subst_eps rho eff2) (subst_rho rho tyr3) .
Proof.
  intros.
  unfold subst_rho. 
  do 2 rewrite fold_subst_eps_fold_foldr.
  do 4 rewrite subst_in_type_fold_foldr. 
  induction (map_to_list rho). simpl.
  - f_equal.
    + apply Extensionality_Ensembles.
      unfold Same_set, Included, Ensembles.In; split; intros sa H1.
      * exists sa. split; [assumption |].
        unfold fold_subst_sa_alt.
        destruct sa; reflexivity.
      * destruct H1 as [? [? H2]].
        rewrite <- H2.
        unfold fold_subst_sa_alt.
        destruct x; simpl; assumption.
    + apply Extensionality_Ensembles.
      unfold Same_set, Included, Ensembles.In; split; intros sa H1.
      * exists sa. split; [assumption |].
        unfold fold_subst_sa_alt.
        destruct sa; reflexivity.
      * destruct H1 as [? [? H2]].
        rewrite <- H2.
        unfold fold_subst_sa_alt.
        destruct x; simpl; assumption.
  - do 4 rewrite foldr_cons. 
    rewrite IHl.
    assert (Hr : forall r u aty ceff crty eeff erty,
                 (uncurry subst_in_type) (r, u) (Ty_Arrow aty ceff crty eeff erty) =
                   Ty_Arrow (uncurry subst_in_type (r, u) aty)
                     (uncurry subst_in_eff (r, u) ceff) (uncurry subst_in_type (r, u) crty)
                     (uncurry subst_in_eff (r, u) eeff) (uncurry subst_in_type (r, u) erty))
        by (unfold subst_in_type, subst_type; simpl; f_equal).   
    destruct a.
    rewrite Hr.
    f_equal.
    + rewrite fold_subst_eps_cons.
      apply Extensionality_Ensembles.
      unfold Same_set, Included, Ensembles.In; split; intros sa H1.
      * unfold fold_subst_eps_alt_head, fold_subst_eps_alt.
        unfold subst_in_eff, fold_subst_eps_alt, subst_eps in H1. simpl in H1.
        destruct H1 as [? [[? [H2 H3]] H4]].
        exists x.
        split; [ exists x0; auto | assumption]. 
      * unfold fold_subst_eps_alt_head, fold_subst_eps_alt.
        unfold subst_in_eff, fold_subst_eps_alt, subst_eps in H1. simpl in H1.
        destruct H1 as [? [[? [H2 H3]] H4]].
        exists x.
        split; [ exists x0; auto | assumption].
    + rewrite fold_subst_eps_cons.
      apply Extensionality_Ensembles.
      unfold Same_set, Included, Ensembles.In; split; intros sa H1.
      * unfold fold_subst_eps_alt_head, fold_subst_eps_alt.
        unfold subst_in_eff, fold_subst_eps_alt, subst_eps in H1. simpl in H1.
        destruct H1 as [? [[? [H2 H3]] H4]].
        exists x.
        split; [ exists x0; auto | assumption]. 
      * unfold fold_subst_eps_alt_head, fold_subst_eps_alt.
        unfold subst_in_eff, fold_subst_eps_alt, subst_eps in H1. simpl in H1.
        destruct H1 as [? [[? [H2 H3]] H4]].
        exists x.
        split; [ exists x0; auto | assumption].
Qed.     


Lemma subst_rho_forallrgn  :
  forall rho eff rty, 
    subst_rho rho (Ty_ForallRgn eff rty) =
      Ty_ForallRgn (fold_subst_eps rho eff) (subst_rho rho rty).
Proof.
  intros.
  unfold subst_rho. 
  rewrite fold_subst_eps_fold_foldr.
  do 2 rewrite subst_in_type_fold_foldr. 
  induction (map_to_list rho); simpl.
  - f_equal.  apply Extensionality_Ensembles.
    unfold Same_set, Included, Ensembles.In; split; intros sa H1.
    + unfold fold_subst_eps_alt.
      exists sa. split.
      * assumption.
      * unfold fold_subst_sa_alt.
        destruct sa; simpl; reflexivity.
    + unfold fold_subst_eps_alt in H1.
      destruct H1 as [? [H2 H3]]. rewrite <- H3.
      unfold fold_subst_sa_alt.
      destruct x; simpl; assumption.
  - rewrite fold_subst_eps_cons. 
    rewrite IHl.
    assert (Hr : forall r u eff rty,
                 (uncurry subst_in_type) (r, u) (Ty_ForallRgn eff rty) =
                   Ty_ForallRgn (uncurry subst_in_eff (r, u) eff)
                     (uncurry subst_in_type (r, u) rty))    
      by (unfold subst_in_type, subst_type; simpl; f_equal).
    destruct a.
    rewrite Hr.
    f_equal.
Qed.
    
 
Lemma subst_rho_tyref :
  forall rho r ty,
    subst_rho rho (Ty_Ref r ty) = Ty_Ref (fold_subst_rgn rho r) (subst_rho rho ty).
Proof.
  intros.
  unfold subst_rho, fold_subst_rgn.
  rewrite subst_rgn_fold_foldr. 
  do 2 rewrite subst_in_type_fold_foldr. 
  induction (map_to_list rho). simpl.
  - f_equal.
  - rewrite foldr_cons.
    rewrite IHl.
    assert (Hr : forall x u rgn rty,
                 (uncurry subst_in_type) (x, u) (Ty_Ref rgn rty) =
                   Ty_Ref (uncurry  subst_rgn (x, (Rgn_Const true false u)) rgn)
                     (uncurry subst_in_type (x, u) rty))
      by (unfold subst_in_type, subst_type; simpl; f_equal).
    destruct a.
    rewrite Hr.
    f_equal.
Qed.



Lemma subst_rho_fvar_1:
  forall rho x,
    (exists v, fold_subst_rgn rho (Rgn_FVar true true x) = Rgn_Const true true v) \/ 
    fold_subst_rgn rho (Rgn_FVar true true x) = Rgn_FVar true true x.
Proof.
  intros rho x.
  unfold fold_subst_rgn.
  rewrite subst_rgn_fold_foldr.
  induction (map_to_list); simpl.
  - right. reflexivity.
  - destruct IHl. 
    + left. destruct H. exists x0. rewrite H.
      apply subst_rho_rgn_const_aux.
    + rewrite H. 
      unfold subst_rgn.
      destruct a. simpl. destruct (ascii_dec r x).
      * left. exists r0. reflexivity.
      * right. reflexivity. 
Qed. 


Lemma subst_rho_fvar_1_2:
  forall (l: list(RgnName*RgnVal)) x,
    (exists v, fold_subst_rgn_alt l (Rgn_FVar true true x) = Rgn_Const true true v) \/ 
    fold_subst_rgn_alt l (Rgn_FVar true true x) = Rgn_FVar true true x.
Proof.
  intros l x.
  unfold fold_subst_rgn_alt.
  induction l; simpl.
  - right. reflexivity.
  - destruct IHl. 
    + left. destruct H. exists x0. rewrite H.
      apply subst_rho_rgn_const_aux.
    + rewrite H. 
      unfold subst_rgn.
      destruct a. simpl. destruct (ascii_dec r x).
      * left. exists r0. reflexivity.
      * right. reflexivity. 
Qed.

Lemma subst_rho_fvar_2:
  forall rho x v,
   rho !! x = Some v ->
   fold_subst_rgn rho (Rgn_FVar true true x) = Rgn_Const true true v.
Proof.
  intros rho x v HSome.
  assert ((x,v) ∈ map_to_list rho) by (apply elem_of_map_to_list'; auto).
  unfold fold_subst_rgn. 
  rewrite subst_rgn_fold_foldr.   
  assert (HNoDup: base.NoDup ((map_to_list rho).*1)) by apply NoDup_fst_map_to_list.
  induction (map_to_list rho); simpl.  
  - contradict H.
    apply not_elem_of_nil. 
  - apply elem_of_cons in H. 
    destruct H.
    + clear IHl. 
      subst.  simpl. 
      replace ((foldr (uncurry
          (λ (x0 : RgnName) (r : RgnVal) (rgn : Region_in_Type),
            subst_rgn x0 (Rgn_Const true false r) rgn)) (Rgn_FVar true true x) l))
        with (Rgn_FVar true true x).
      * simpl. destruct (ascii_dec x x). 
        reflexivity. contradiction.
      * { rewrite fold_subst_rho_free_vars_rgn_not_elem.
          - reflexivity.
          - eapply NoDup_cons_1_1; eassumption. }
    + rewrite IHl.
      * destruct a. unfold subst_rgn. simpl. reflexivity.
      * assumption.
      * eapply NoDup_cons_1_2; eassumption.
Qed.


Lemma subst_rho_free_vars_rgn:
 forall rho x r,
   rho !! x = None ->
   not_set_elem (free_rgn_vars_in_rgn (fold_subst_rgn rho r)) x ->
   not_set_elem (free_rgn_vars_in_rgn r) x.
Proof.
  intros rho x r HFind HNotElem.
  unfold Region_in_Type in r. dependent induction r. 
  - rewrite subst_rho_rgn_const in HNotElem. assumption.
  - assert ((exists v', fold_subst_rgn rho (Rgn_FVar true true r) =  
                         Rgn_Const true true v') \/ 
            fold_subst_rgn rho (Rgn_FVar true true r) = Rgn_FVar true true r) 
      by (apply subst_rho_fvar_1).
    destruct (subst_rho_fvar_1 rho r) as [[v' H0] | H0]; simpl in *.
    + destruct (ascii_dec r x) as [c | c]; auto.
      * inversion c; subst. intro.
        rewrite fold_subst_rho_free_vars_rgn_aux in H0; auto.
        inversion H0.
      * intro. apply c.  inversion H1. reflexivity.
    + rewrite H0 in HNotElem. 
      simpl in HNotElem.
      assumption.
  - rewrite subst_rho_index in HNotElem. 
    assumption.
Qed.
    

Lemma TcRhoIncludedNoFreeVarsRgn_aux_fold:
  forall rho r x,
    free_rgn_vars_in_rgn (fold_subst_rgn rho r) x ->
    free_rgn_vars_in_rgn r x.
Proof.
  intros. 
  unfold Region_in_Type in r; dependent induction r.
  - rewrite subst_rho_rgn_const in H. assumption.
  - assert ((exists v', fold_subst_rgn rho (Rgn_FVar true true r)
                        = Rgn_Const true true v') \/ 
            fold_subst_rgn rho (Rgn_FVar true true r) = Rgn_FVar true true r) 
      by (apply subst_rho_fvar_1).
    destruct H0. 
    + destruct H0. rewrite H0 in H. 
      unfold free_rgn_vars_in_rgn in H. inversion H.
    + rewrite H0 in H.
      assumption.
  - rewrite subst_rho_index in H. assumption.
Qed.


Lemma subst_rho_rgn_const_2 :
  forall l c,
    fold_subst_rgn_alt l (Rgn_Const true true c) = (Rgn_Const true true c).
Proof.
  intros.
  unfold fold_subst_rgn_alt.
  induction l; simpl.
  - reflexivity.
  - rewrite IHl.
    apply subst_rho_rgn_const_aux.            
Qed.

Lemma subst_rho_index_2 :
  forall l n,
    fold_subst_rgn_alt l (Rgn_BVar true true n) = (Rgn_BVar true true n).
Proof.
  intros.
  unfold fold_subst_rgn_alt.
  induction l; simpl.
  - reflexivity.
  - rewrite IHl. unfold subst_rgn.
    destruct a. simpl.
    reflexivity.
Qed.

Lemma TcRhoIncludedNoFreeVarsRgn_aux_fold_2:
  forall (l : list (RgnName*RgnVal)) r x,
    free_rgn_vars_in_rgn (fold_subst_rgn_alt l r) x ->
    free_rgn_vars_in_rgn r x.
Proof.
  intros. 
  unfold Region_in_Type in r; dependent induction r.
  - rewrite subst_rho_rgn_const_2 in H. assumption.
  - assert ((exists v', fold_subst_rgn_alt l (Rgn_FVar true true r)
                        = Rgn_Const true true v') \/ 
            fold_subst_rgn_alt l (Rgn_FVar true true r) = Rgn_FVar true true r) 
      by (apply subst_rho_fvar_1_2).
    destruct H0. 
    + destruct H0. rewrite H0 in H. 
      unfold free_rgn_vars_in_rgn in H. inversion H.
    + rewrite H0 in H.
      assumption.
  - rewrite subst_rho_index_2 in H. assumption.
Qed.


Lemma TcRhoIncludedNoFreeVarsSa_aux_fold:
  forall rho sa x,
    free_rgn_vars_in_sa (fold_subst_sa_alt rho sa) x ->
    free_rgn_vars_in_sa sa x.
Proof.
  intros. 
  induction sa; unfold free_rgn_vars_in_sa, fold_subst_sa_alt in *;
    eapply TcRhoIncludedNoFreeVarsRgn_aux_fold_2; eauto. 
Qed.
 
Lemma TcRhoIncludedNoFreeVarsEps_aux_fold:
  forall rho e x,
    free_rgn_vars_in_eps (fold_subst_eps_alt rho e) x ->
    free_rgn_vars_in_eps e x.
Proof.
  intros. unfold  free_rgn_vars_in_eps, fold_subst_eps_alt in *.
  destruct H as [sa [[sa' [H1 H2]] H3]].
  exists sa'. intuition.
  rewrite <- H2 in H3.
  eapply TcRhoIncludedNoFreeVarsSa_aux_fold; eauto.
Qed.


Lemma TcRhoIncludedNoFreeVarsSa_aux_fold_2:
  forall a sa x,
    free_rgn_vars_in_sa (head_fold_subst_sa_alt a sa) x ->
    free_rgn_vars_in_sa sa x.
Proof.
  intros.
  induction sa. unfold free_rgn_vars_in_sa in *.
  - unfold head_fold_subst_sa_alt in H.
    apply TcRhoIncludedNoFreeVarsRgn_aux_fold_2 with (l:= cons a nil).
    now assumption.
  - unfold head_fold_subst_sa_alt in H.
    apply TcRhoIncludedNoFreeVarsRgn_aux_fold_2 with (l:= cons a nil).
    now assumption.
  - unfold head_fold_subst_sa_alt in H.
    apply TcRhoIncludedNoFreeVarsRgn_aux_fold_2 with (l:= cons a nil).
    now assumption.
Qed. 


Lemma TcRhoIncludedNoFreeVarsEps_aux_fold_1:
  forall (a : (RgnName * RgnVal)) e (x: RgnName),
    free_rgn_vars_in_eps (fold_subst_eps_alt_head a e) x ->
    free_rgn_vars_in_eps e x.
Proof.
  intros.
  intros. unfold  free_rgn_vars_in_eps, fold_subst_eps in *.
  destruct H as [sa [[sa' [H1 H2]] H3]].
  exists sa'. intuition.
  rewrite <- H2 in H3.
  eapply TcRhoIncludedNoFreeVarsSa_aux_fold_2; eauto.
Qed.


Lemma subst_rgn_fold_foldr_3:
  forall k v (l : list (RgnName*RgnVal)) (rt : Region_in_Type),
    base.NoDup l.*1 ->
    (list_to_map l : Rho) !! k = None ->
    map_fold (fun x r rgn => subst_rgn x (Rgn_Const true false r) rgn)
      rt (<[k:=v]> (list_to_map l : Rho)) =
      (foldr (uncurry(fun x r rgn => subst_rgn x (Rgn_Const true false r) rgn)))
        rt ((k, v)::l).
Proof.
  intros.
  rewrite subst_rgn_fold_foldr.
  assert (Hperm :
            map_to_list (<[k:=v]> (list_to_map l : Rho)) ≡ₚ (k, v) :: l).
  { transitivity ((k, v) :: map_to_list (list_to_map l : Rho)).
    - apply map_to_list_insert; assumption.
    - apply perm_skip.
      apply map_to_list_to_map; assumption. }
  apply foldr_permutation.
  - constructor.
    + unfold Reflexive. reflexivity.
    + unfold Transitive. intros. subst. reflexivity.
  - solve_proper.
  - intros j1 [x1 r1] j2 [x2 r2] rgn Hneq Hj1 Hj2.
    simpl.
    apply subst_rgn_aux_comm.
    intro Heq. subst.
    apply Hneq.
    assert (HNoDupMap :
              base.NoDup (map_to_list (<[k:=v]> (list_to_map l : Rho))).*1)
      by apply NoDup_fst_map_to_list.
    eapply NoDup_lookup; eauto;
      rewrite list_lookup_fmap;
      [rewrite Hj1 | rewrite Hj2]; reflexivity.
  - assumption.
Qed.


Lemma fold_subst_SA_Alloc_head_insert:
  forall k v (l: list (RgnName*RgnVal)) (r: Region_in_Type),
    (list_to_map l : Rho) !! k = None ->
    base.NoDup l.*1 ->
    head_fold_subst_sa_alt (k, v) (fold_subst_sa_alt l (SA_Alloc r)) =
      SA_Alloc (fold_subst_rgn (<[k:=v]> (list_to_map l)) r).
Proof.
  intros.
  unfold fold_subst_rgn.  
  unfold Region_in_Type in r; dependent induction r. simpl.
  - f_equal. rewrite subst_rgn_fold_foldr_3.
    + simpl. reflexivity.
    + assumption.
    + assumption.
  - f_equal. rewrite subst_rgn_fold_foldr_3.
    + simpl. reflexivity.
    + assumption.
    + assumption.
  - f_equal. rewrite subst_rgn_fold_foldr_3.
    + simpl. reflexivity.
    + assumption.
    + assumption.        
Qed.

Lemma fold_subst_SA_Read_head_insert:
  forall k v l (r: Region_in_Type),
    (list_to_map l : Rho) !! k = None ->
    base.NoDup l.*1 ->
    head_fold_subst_sa_alt (k,v) (fold_subst_sa_alt l (SA_Read r)) =
      SA_Read (fold_subst_rgn (<[k:=v]> (list_to_map l)) r).
Proof.
  intros.
  unfold fold_subst_rgn.  
  unfold Region_in_Type in r; dependent induction r. simpl.
  - f_equal. rewrite subst_rgn_fold_foldr_3.
    + simpl. reflexivity.
    + assumption.
    + assumption.
  - f_equal. rewrite subst_rgn_fold_foldr_3.
    + simpl. reflexivity.
    + assumption.
    + assumption.
  - f_equal. rewrite subst_rgn_fold_foldr_3.
    + simpl. reflexivity.
    + assumption.
    + assumption.
Qed.

Lemma fold_subst_SA_Write_head_insert:
  forall k v l (r: Region_in_Type),
    (list_to_map l : Rho) !! k = None ->
    base.NoDup l.*1 ->
    head_fold_subst_sa_alt (k,v) (fold_subst_sa_alt l (SA_Write r)) =
      SA_Write (fold_subst_rgn (<[k:=v]> (list_to_map l)) r).
Proof.
  intros.
  unfold fold_subst_rgn.  
  unfold Region_in_Type in r; dependent induction r. simpl.
  - f_equal. rewrite subst_rgn_fold_foldr_3.
    + simpl. reflexivity.
    + assumption.
    + assumption.
  - f_equal. rewrite subst_rgn_fold_foldr_3.
    + simpl. reflexivity.
    + assumption.
    + assumption.
  - f_equal. rewrite subst_rgn_fold_foldr_3.
    + simpl. reflexivity.
    + assumption.
    + assumption.
Qed.


Lemma fold_subst_sa_map_to_list:
  forall a (l : list (RgnName*RgnVal)) sa,
    (list_to_map l : Rho) !! a.1 = None ->
    base.NoDup l.*1 ->
    fold_subst_sa_alt (a :: l) sa = fold_subst_sa (<[a.1:=a.2]> (list_to_map l)) sa.
Proof.
  intros.
  rewrite fold_subst_sa_cons.
  unfold fold_subst_sa, fold_subst_rgn_alt.
  destruct sa; destruct a as [k v].
  - apply fold_subst_SA_Alloc_head_insert; auto.
  - apply fold_subst_SA_Read_head_insert; auto.
  - apply fold_subst_SA_Write_head_insert; auto.
Qed.



Lemma free_rgn_vars_in_eps_map_to_list_2:
  forall (l : list (RgnName*RgnVal)) e x,
    base.NoDup l.*1 ->
    free_rgn_vars_in_eps (fold_subst_eps (list_to_map l) e) x ->
    free_rgn_vars_in_eps (fold_subst_eps_alt l e) x.
Proof.
  intros l e x HNoDup H.
  induction l; simpl in H;
    unfold fold_subst_eps_alt;
    unfold fold_subst_eps in H;
    destruct H as [sa [[sa' [H1 H2]] H3]];
    unfold free_rgn_vars_in_eps.
  - exists sa. split; [exists sa'; intuition | assumption].
  - pose proof (NoDup_cons_1_1 _ _ HNoDup) as HNotIn.
    pose proof (NoDup_cons_1_2 _ _ HNoDup) as HNoDupTail.
    exists sa. split.
    + exists sa'. intuition.
      rewrite <- H2. 
      apply fold_subst_sa_map_to_list.
      apply not_elem_of_list_to_map_1.
      * assumption.
      * assumption. 
    + assumption.      
Qed.

Lemma free_rgn_vars_in_eps_map_to_list:
  forall (rho: Rho) e x,
    free_rgn_vars_in_eps (fold_subst_eps rho e) x ->
    free_rgn_vars_in_eps (fold_subst_eps_alt (map_to_list rho) e) x.
Proof.
  intros.
  replace (fold_subst_eps rho e) with (fold_subst_eps_alt (map_to_list rho) e) in H.
  - assumption.
  - symmetry. apply fold_subst_eps_fold_foldr.
Qed.


