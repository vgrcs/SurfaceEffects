From stdpp Require Import gmap.
From stdpp Require Import fin_maps.
From stdpp Require Import list.
From stdpp Require Import base.
From stdpp Require Import strings.
Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Definitions.Regions.
Require Import Definitions.GTypes.
Require Import Definitions.ComputedActions.
Require Import Definitions.StaticActions.
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
  

Lemma G_diff_keys_3 `{Countable K} {A}:
  forall a b v (m : gmap K A),   
    a <> b ->
    (<[ b:=v ]> m) !! a <> None -> 
    m !! a <> None.
Proof.
  intros.
  contradict H1. apply lookup_insert_None. auto.
Qed.


Lemma find_rho_3 `{Countable K} {A}:
  forall x (m : gmap K A) (e : A),
    m !! x  = None -> ~ m !! x = Some e.
Proof.
  intros. apply eq_None_not_Some in H0. contradict H0.
  unfold is_Some. exists e. assumption.
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
  - destruct (ascii_eq_dec j2 r); destruct (ascii_eq_dec j1 r); simpl.
    + subst. contradiction.
    + subst. destruct (ascii_eq_dec r r).
      * reflexivity.
      * contradiction.
    + reflexivity.
    + subst. destruct (ascii_eq_dec j2 r); subst.
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
    + destruct (ascii_eq_dec j1 r); destruct (ascii_eq_dec j2 r); subst; simpl.
      * contradiction.
      * destruct (ascii_eq_dec r r); subst;
          [reflexivity | contradiction].
      * destruct (ascii_eq_dec r r); subst;
          [reflexivity | contradiction].
      * { destruct (ascii_eq_dec j1 r); destruct (ascii_eq_dec j2 r); subst; simpl.
          - contradiction.
          - contradiction.
          - contradiction.
          - reflexivity. }
    + reflexivity.
  - generalize dependent r. unfold Region_in_Type. dependent induction r; simpl.
    + reflexivity.
    + destruct (ascii_eq_dec j1 r); destruct (ascii_eq_dec j2 r); subst; simpl.
      * contradiction.
      * destruct (ascii_eq_dec r r); subst;
          [reflexivity | contradiction].
      * destruct (ascii_eq_dec r r); subst;
          [reflexivity | contradiction].
      * { destruct (ascii_eq_dec j1 r); destruct (ascii_eq_dec j2 r); subst; simpl.
          - contradiction.
          - contradiction.
          - contradiction.
          - reflexivity. }
    + reflexivity.
  - generalize dependent r. unfold Region_in_Type. dependent induction r; simpl.
    + reflexivity.
    + destruct (ascii_eq_dec j1 r); destruct (ascii_eq_dec j2 r); subst; simpl.
      * contradiction.
      * destruct (ascii_eq_dec r r); subst;
          [reflexivity | contradiction].
      * destruct (ascii_eq_dec r r); subst;
          [reflexivity | contradiction].
      * { destruct (ascii_eq_dec j1 r); destruct (ascii_eq_dec j2 r); subst; simpl.
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
      rewrite subst_sa_aux_comm;[reflexivity | symmetry; assumption].
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
  apply (map_fold_foldr _ (map_to_list rho)).
  - solve_proper.
  - intros j1 j2 z1 z2 y ? ? ?.
    induction y; try (solve [unfold subst_in_type, subst_type; simpl;reflexivity]).
    + assert (Hr : forall r u t1 t2,
                 subst_in_type r u (Ty_Pair t1 t2) =
                   Ty_Pair (subst_in_type r u t1) (subst_in_type r u t2))
        by (unfold subst_in_type, subst_type; simpl; f_equal).        
      do 4 rewrite Hr. f_equal; assumption.
    + assert (Hr : forall r u rgn ty,
                 subst_in_type r u (Ty_Ref rgn ty) =
                   Ty_Ref (subst_rgn r (Rgn_Const true false u) rgn)
                     (subst_in_type r u ty))
        by (unfold subst_in_type, subst_type; simpl; f_equal).   
      do 4 rewrite Hr. f_equal; try (solve [assumption]).
      rewrite subst_rgn_aux_comm; auto.      
    + assert (Hr : forall r u aty ceff crty eeff erty,
                 subst_in_type r u (Ty_Arrow aty ceff crty eeff erty) =
                   Ty_Arrow (subst_in_type r u aty)
                     (subst_in_eff r u ceff) (subst_in_type r u crty)
                     (subst_in_eff r u eeff) (subst_in_type r u erty))
        by (unfold subst_in_type, subst_type; simpl; f_equal).   
      do 4 rewrite Hr. f_equal; try (solve [assumption]).
      rewrite subst_eps_aux_comm; auto.
      rewrite subst_eps_aux_comm; auto.
    + assert (Hr : forall r u eff rty,
                 subst_in_type r u (Ty_ForallRgn eff rty) =
                   Ty_ForallRgn (subst_in_eff r u eff) (subst_in_type r u rty))
        by (unfold subst_in_type, subst_type; simpl; f_equal).   
      do 4 rewrite Hr.
      f_equal; try (solve [assumption]).
      rewrite subst_eps_aux_comm; auto.
  - reflexivity.
Qed.

Lemma subst_rgn_fold_foldr:
  forall (rho : Rho) (rt : Region_in_Type),
    map_fold (fun x r rgn => subst_rgn x (Rgn_Const true false r) rgn) rt rho =
      (foldr (uncurry(fun x r rgn => subst_rgn x (Rgn_Const true false r) rgn)))
        rt (map_to_list rho).
Proof.
  intros.
  apply (map_fold_foldr _ (map_to_list rho)).
  - solve_proper.
  - intros j1 j2 z1 z2 y ? ? ?.
    rewrite subst_rgn_aux_comm; auto.
  - reflexivity.
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
    destruct (ascii_eq_dec r x).
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
       destruct (ascii_eq_dec r p.1).
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
      destruct a. simpl. destruct (ascii_eq_dec r x).
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
      destruct a. simpl. destruct (ascii_eq_dec r x).
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
      * simpl. destruct (ascii_eq_dec x x). 
        reflexivity. contradiction.
      * { apply list.NoDup_cons in HNoDup.
          rewrite fold_subst_rho_free_vars_rgn_not_elem.
          - reflexivity. 
          - destruct HNoDup.
            assumption. }
    + rewrite IHl.
      * destruct a. unfold subst_rgn. simpl. reflexivity.
      * assumption.
      * apply list.NoDup_cons in HNoDup.
        destruct HNoDup. assumption.
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
    + destruct (ascii_eq_dec r x) as [c | c]; auto.
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
  apply (map_fold_foldr _ ((k, v)::l)).
  - solve_proper.
  - intros j1 j2 z1 z2 y ? ? ?.
    rewrite subst_rgn_aux_comm; auto.
  -  assert (map_to_list (<[k:=v]> (list_to_map l)) ≡ₚ
              (k, v) :: map_to_list(list_to_map l))
       by (apply map_to_list_insert; assumption).
     rewrite H1.
     rewrite map_to_list_to_map.
     + reflexivity.
     + assumption.
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
  - apply list.NoDup_cons in HNoDup. destruct HNoDup.
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
  - destruct (ascii_eq_dec k r); subst; simpl in *.
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
               destruct (ascii_eq_dec x r); subst; 
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
  - destruct (ascii_eq_dec x r) as [c | c].
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
  - destruct (ascii_eq_dec x r); subst.
    + unfold free_rgn_vars_in_rgn.
      intro. inversion H.
    + unfold free_rgn_vars_in_rgn.
      intro. inversion H. subst. contradiction.
  - destruct (ascii_eq_dec x r).
    + unfold free_rgn_vars_in_rgn.
      intro. inversion H.
    + unfold free_rgn_vars_in_rgn.
      intro. inversion H. subst. contradiction.
  - destruct (ascii_eq_dec x r).
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
                         destruct (ascii_eq_dec r r0); [inversion H0 |
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
  destruct (ascii_eq_dec r x); subst.
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
