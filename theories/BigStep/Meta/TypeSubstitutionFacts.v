From stdpp Require Import gmap.
From stdpp Require Import fin_maps.
From stdpp Require Import list.
From stdpp Require Import base.
From stdpp Require Import strings.

From Stdlib Require Import Program.Equality.
From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.

Require Import theories.BigStep.Core.StaticActions.
Require Import theories.BigStep.Core.ComputedActions.
Require Import theories.BigStep.Core.Regions.
Require Import theories.BigStep.Typing.TypeSyntax.
Require Import theories.BigStep.Typing.TypingJudgments.
Require Import theories.BigStep.Meta.Tactics.
Require Import theories.BigStep.Meta.MapFacts.
Require Import theories.BigStep.Meta.RegionFacts.

Import Expressions.
Import Ascii.

Lemma subst_type_rgn_comm_2:
  forall r k1 k2 v1 v2,
    k1 <> k2 ->
    subst_rgn k1 (Rgn_Const true false v1) (subst_rgn k2 (Rgn_Const true false v2) r) =
    subst_rgn k2 (Rgn_Const true false v2) (subst_rgn k1 (Rgn_Const true false v1) r).
Proof.
  intros r k1 k2 v1 v2 H.
  unfold Region_in_Type in r.
  dependent induction r; try (solve [simpl; reflexivity ]).
  unfold subst_rgn. destruct (ascii_dec k1 k2).
  - inversion e. contradiction.
  - simpl. destruct (ascii_dec k2 r).
    + assert (k1 <> r) by congruence.
      destruct (ascii_dec k1 r).
      * now absurd (k1=r).
      * inversion e; subst; now destruct (ascii_dec r r).
    + destruct (ascii_dec k1 r); [reflexivity |].
      now destruct (ascii_dec k2 r).
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
  forall (k1 k2 : RgnName) (v1 v2: RgnVal) (e : Epsilon),
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
  forall (k1 k2: RgnName) (v1 v2: RgnVal) (b : Tau),
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

Definition RhoList := list (RgnName * RgnVal).


Lemma baz_2:
  forall (l: list(RgnName*RgnVal)),
  forall (k: RgnName) (v: RgnVal),
    (list_to_map l : Rho) !! k = None ->
    exists elems1 elems2,
      elems1 ++ (k,v)::elems2 = (k, v) :: l /\
        elems1 ++ elems2 = l.
Proof.
  intros.
  induction l.
  - exists nil. exists nil.
    rewrite app_nil_l. rewrite app_nil_r.
    split; reflexivity.
  - destruct a as [k' v'].
    destruct (ascii_dec k k').
    + subst. contradict H.
      replace (list_to_map ((k', v') :: l)) with (<[k':=v']>(list_to_map l: Rho))
        by (symmetry; apply list_to_map_cons).
      apply NotNoneIsSome.
      exists v'.
      apply lookup_insert_Some. intuition.
    + exists nil. exists ((k', v') :: l).
      split.
      * rewrite app_nil_l. reflexivity.
      * rewrite app_nil_l. reflexivity.
Qed.        



Lemma subst_rgn_aux_comm_uncurry :
  forall (j1 : nat) (a1 : RgnName * RgnVal) (j2 : nat) (a2 : RgnName * RgnVal)
         (b : Region_in_Type) (l : list(RgnName*RgnVal)),
    NoDup l.*1 ->
    j1 ≠ j2 ->
    l !! j1 = Some a1 ->
    l !! j2 = Some a2 ->
    uncurry subst_in_rgn_alt a1 (uncurry subst_in_rgn_alt a2 b) =
      uncurry subst_in_rgn_alt a2 (uncurry subst_in_rgn_alt a1 b).
Proof.
  intros.
  generalize dependent b.
  unfold Region_in_Type.
  dependent induction b; intros.
  - unfold subst_in_rgn_alt.
    destruct a1. destruct a2. simpl.
    reflexivity.
  - unfold subst_in_rgn_alt.
    destruct a1. destruct a2. simpl.
    destruct (ascii_dec r2 r); destruct (ascii_dec r0 r); subst.
    + { assert (HSubst: r1 = r3).
        apply elem_of_list_lookup_2 in H1.
        apply elem_of_list_lookup_2 in H2.
        assert ((list_to_map l : Rho) !! r = Some r1)
          by (eapply elem_of_list_to_map_1; eauto).
        assert ((list_to_map l : Rho) !! r = Some r3)
          by (eapply elem_of_list_to_map_1; eauto).
        rewrite H3 in H4. inversion H4. auto.        
        subst. reflexivity. }
    + destruct (ascii_dec r r); destruct (ascii_dec r0 r); simpl.
      * contradiction.
      * destruct (ascii_dec r r); [reflexivity| contradiction].
      * contradiction.
      * contradiction.
    + destruct (ascii_dec r r); destruct (ascii_dec r2 r); simpl.
      * contradiction.
      * destruct (ascii_dec r r); [reflexivity| contradiction].
      * contradiction.
      * contradiction.  
    + destruct (ascii_dec r2 r); destruct (ascii_dec r0 r); simpl.      
      * contradiction.
      * contradiction.
      * contradiction.
      * destruct (ascii_dec r2 r); destruct (ascii_dec r0 r);
          try (solve [reflexivity| contradiction]).        
  - unfold subst_in_rgn_alt.
    destruct a1. destruct a2. simpl.
    reflexivity.
Qed.



Lemma subst_rho_pair_uncurry : 
  forall (a1 a2: RgnName*RgnVal) (b1 b2: Tau),
    uncurry subst_in_type a1 (uncurry subst_in_type a2 (Ty_Pair b1 b2)) =
      (Ty_Pair (uncurry subst_in_type a1 (uncurry subst_in_type a2 b1))
         (uncurry subst_in_type a1 (uncurry subst_in_type a2 b2))).
Proof.
  intros.
  destruct a1 as [x1 v1]; destruct a2 as [x2 v2]. simpl.
  unfold uncurry, subst_in_type, subst_type; simpl; f_equal. 
Qed.

Lemma subst_rho_ref_uncurry : 
  forall (a1 a2: RgnName*RgnVal) r (b: Tau),
    uncurry subst_in_type a1 (uncurry subst_in_type a2 (Ty_Ref r b)) =
      Ty_Ref  (uncurry subst_in_rgn a1 (uncurry subst_in_rgn a2 r))
        (uncurry subst_in_type a1 (uncurry subst_in_type a2 b)).
Proof.
  intros.
  destruct a1 as [x1 v1]; destruct a2 as [x2 v2]. simpl.
  unfold uncurry, subst_in_type, subst_type; simpl; f_equal. 
Qed.

Lemma subst_rho_arrow_uncurry :
  forall (a1 a2: RgnName*RgnVal) (e e': Epsilon)  (b1 b2 b3: Tau),
    uncurry subst_in_type a1 (uncurry subst_in_type a2 (Ty_Arrow b1 e b2 e' b3)) =
    Ty_Arrow (uncurry subst_in_type a1 (uncurry subst_in_type a2 b1))
                (uncurry subst_in_eff a1 (uncurry subst_in_eff a2 e))
                (uncurry subst_in_type a1 (uncurry subst_in_type a2 b2))
                (uncurry subst_in_eff a1 (uncurry subst_in_eff a2 e'))
                (uncurry subst_in_type a1 (uncurry subst_in_type a2 b3)).
Proof.
  intros.
  destruct a1 as [x1 v1]; destruct a2 as [x2 v2]. simpl.
  unfold uncurry, subst_in_type, subst_type; simpl; f_equal.
Qed.


Lemma subst_rho_forall_uncurry :
  forall (a1 a2: RgnName*RgnVal) (e: Epsilon)  (b: Tau),
    uncurry subst_in_type a1 (uncurry subst_in_type a2 (Ty_ForallRgn e b)) =
      Ty_ForallRgn (uncurry subst_in_eff a1 (uncurry subst_in_eff a2 e))
                      (uncurry subst_in_type a1 (uncurry subst_in_type a2 b)).
Proof.
  intros.
  destruct a1 as [x1 v1]; destruct a2 as [x2 v2]. simpl.
  unfold uncurry, subst_in_type, subst_type; simpl; f_equal. 
Qed.
              
Lemma subst_type_aux_comm_uncurry :
  forall (j1 : nat) (a1 : RgnName * RgnVal) (j2 : nat) (a2 : RgnName * RgnVal)
         (b : Tau) (l : list(RgnName*RgnVal)),
    (forall x y1 y2, (x,y1) ∈ l -> (x,y2) ∈ l -> y1 = y2) ->
    j1 ≠ j2 ->
    l !! j1 = Some a1 ->
    l !! j2 = Some a2 ->
    uncurry subst_in_type a1 (uncurry subst_in_type a2 b) =
      uncurry subst_in_type a2 (uncurry subst_in_type a1 b).
Proof.
  intros.
  generalize dependent b.
  dependent induction b; intros;
    try (solve [unfold subst_in_type;destruct a1; destruct a2;reflexivity]).
  - do 2 rewrite subst_rho_pair_uncurry.
    f_equal; auto.
  - do 2 rewrite subst_rho_ref_uncurry.
    f_equal; auto. 
    destruct a1 as [x1 v1]; destruct a2 as [x2 v2]. simpl.
    destruct (ascii_dec x1 x2); subst.
    + apply elem_of_list_lookup_2 in H1.
      apply elem_of_list_lookup_2 in H2.
      eapply H in H1; eauto. subst.
      reflexivity.
    + unfold subst_in_rgn.
      apply subst_rgn_aux_comm. assumption.  
  - do 2 rewrite subst_rho_arrow_uncurry.
    f_equal; auto;  
    destruct a1 as [x1 v1]; destruct a2 as [x2 v2]; simpl. 
    + destruct (ascii_dec x1 x2); subst.
      * apply elem_of_list_lookup_2 in H1.
        apply elem_of_list_lookup_2 in H2.
        eapply H in H1; eauto. subst.
        reflexivity.
      * apply subst_eps_aux_comm. assumption.  
    + destruct (ascii_dec x1 x2); subst.
      * apply elem_of_list_lookup_2 in H1.
        apply elem_of_list_lookup_2 in H2.
        eapply H in H1; eauto. subst.
        reflexivity.
      * apply subst_eps_aux_comm. assumption.  
  - do 2 rewrite subst_rho_forall_uncurry.
    f_equal; auto.
    destruct a1 as [x1 v1]; destruct a2 as [x2 v2]; simpl. 
    + destruct (ascii_dec x1 x2); subst.
      * apply elem_of_list_lookup_2 in H1.
        apply elem_of_list_lookup_2 in H2.
        eapply H in H1; eauto. subst.
        reflexivity.
      * apply subst_eps_aux_comm. assumption.
Qed.

  
Lemma NoDup_cons_app:
  forall a (l1 l2 :  list (RgnName * RgnVal)),
    NoDup ((a :: l1).*1 ++ l2.*1) ->
    NoDup (l1.*1 ++ l2.*1).
Proof.
  intros a l1 l2 HNoDup.
  apply NoDup_app.
  split.
  - apply NoDup_app in HNoDup.
    destruct HNoDup as [H1 H2].
    assert (H1' : a.1 ∉ l1.*1 ∧ NoDup l1.*1) by (apply NoDup_cons; assumption).
    destruct H1'.
    assumption.
  - split; apply NoDup_app in HNoDup; destruct HNoDup as [H1 H2]; destruct H2.
    + apply NoDup_cons in H1.
      destruct H1.
      intros. apply H.
      apply elem_of_cons. right. assumption.
    + assumption.
Qed.

Lemma NoDup_comm_some_function:
  forall A,
  forall (f : RgnName → RgnVal → A → A),
  forall a k v (l1 l2 :  list (RgnName * RgnVal)),
    NoDup ((a :: l1).*1 ++ l2.*1) ->
    (forall (k' : RgnName) (v' : RgnVal) (b' : A),
        (list_to_map (a :: l1) : Rho) !! k' = Some v ->
        f k' v' (f k v b') = f k v (f k' v' b')) ->
      forall (k' : RgnName) (v' : RgnVal) (b' : A),
        (list_to_map l1 : Rho) !! k' = Some v ->
        f k' v' (f k v b') = f k v (f k' v' b').
Proof.
  intros A f a k v l1 l2 HNoDup H1 k' v' b' H0'.
  apply H1.
  destruct a as [ka va].
  replace (list_to_map ((ka, va) :: l1))
    with (<[ka:=va]>(list_to_map l1: Rho))
    by (symmetry; apply list_to_map_cons).
  destruct (ascii_dec k' ka).
  - apply NoDup_app in HNoDup; destruct HNoDup as [Ha Hb]; destruct Hb.
    assert (H1' : ka ∉ l1.*1 ∧ NoDup l1.*1)
      by (apply NoDup_cons; assumption).
    destruct H1'. rewrite e in H0'.
    apply not_elem_of_list_to_map_1 in H2.
    replace (list_to_map l1 !! ka) with (Some v) in H2.
    inversion H2.
  - apply lookup_insert_Some.
    right. intuition.    
Qed.

Lemma foldr_subst_rgn_app:
  forall (f : RgnName → RgnVal → Region_in_Type → Region_in_Type),
  forall (l1 l2 : list (RgnName * RgnVal)),    
  forall k v (b : Region_in_Type),
    f = subst_in_rgn ->
    base.NoDup (l1.*1 ++ ((k,v)::l2).*1) ->
    (forall k' v' b',
        (list_to_map l1 : Rho) !! k' = Some v ->
       f k' v' (f k v b') = f k v (f k' v' b')) ->
    foldr (uncurry f) b (l1 ++ (k, v) :: l2) =
      foldr (uncurry f) (f k v b) (l1 ++ l2).
Proof.
  intros f.  
  dependent induction l1; intros l2 k v b Hf HNoDup H. 
  - rewrite app_nil_l. rewrite app_nil_l.
    replace (f k v b) with (uncurry f (k,v) b) by (reflexivity).
    rewrite <- foldr_snoc.
    apply foldr_permutation.
    + constructor.
      * unfold Reflexive.
        reflexivity.
      * unfold Transitive.
        intuition. subst. reflexivity.
    + solve_proper.
    + intros. rewrite Hf.
      eapply subst_rgn_aux_comm_uncurry with (l:=(k, v) :: l2); eauto.
    + replace ((k, v) :: l2) with ( cons (k,v) nil ++ l2) by (simpl; reflexivity).
      apply app_Permutation_comm.      
  - simpl. rewrite IHl1; clear IHl1. 
    + reflexivity.
    + assumption.
    + eapply NoDup_cons_app; eauto.
    + eapply NoDup_comm_some_function; eauto.
Qed.


Lemma NoDup_cons_app_comm:
  forall k v (elems1 elems2 : list (RgnName*RgnVal)),
    NoDup ((k, v) :: elems1 ++ elems2).*1 ->
    NoDup (elems1.*1 ++ ((k, v) :: elems2).*1).
Proof.
  intros.
  replace (((k, v) :: elems1 ++ elems2).*1)
    with (((k, v) :: elems1).*1 ++ elems2.*1) in H
      by (now rewrite <- fmap_app).
  apply NoDup_app in H. destruct H.
  replace (((k, v) :: elems1).*1)
    with (k :: elems1.*1) in H0
      by (symmetry; now rewrite fmap_cons).
  assert (k ∉ elems1.*1 ∧ NoDup elems1.*1)
    by (now apply NoDup_cons).
  apply NoDup_app.
  split.
  - destruct H1; assumption.
  - destruct H1; split.
    + intros. destruct H0.
      replace (((k, v) :: elems2).*1)
        with (k::elems2.*1)
        by (symmetry; now rewrite fmap_cons).
      rewrite not_elem_of_cons.
      destruct (ascii_dec x k); subst. 
      * contradict H1. assumption.
      * {split.
         - assumption.
         - apply H0.
           replace (((k, v) :: elems1).*1)
             with (k::elems1.*1)
             by (symmetry; now rewrite fmap_cons).
           apply elem_of_cons. right. assumption. }        
    +replace (((k, v) :: elems2).*1)
       with (k::elems2.*1)
       by (symmetry; now rewrite fmap_cons).
     destruct H0.
     apply NoDup_cons. split;[| assumption].
     apply H0.
     replace (((k, v) :: elems1).*1)
       with (k::elems1.*1)
       by (symmetry; now rewrite fmap_cons).
     rewrite elem_of_cons.
     intuition.
Qed.

Lemma fold_add_rgn:
  forall (f : RgnName → RgnVal → Region_in_Type → Region_in_Type),
  forall (l : list (RgnName * RgnVal)),
  forall (k: RgnName) (v: RgnVal) (b: Region_in_Type),
    f = subst_in_rgn ->
    base.NoDup ((k,v)::l).*1 ->
    (list_to_map l : Rho) !! k = None ->
    (forall k' v' b',
       (list_to_map l : Rho) !! k' = Some v ->
       f k' v' (f k v b') = f k v (f k' v' b')) ->
    foldr (uncurry f) b ( (k, v)::l) = foldr (uncurry f) (f k v b) l.
Proof.  
  intros f l k v b Hf HNoDup H' H.
  destruct (baz_2 l k v H') as [elems1 [elems2 [H1 H2]]].
  rewrite <- H1.
  rewrite <- H2.
  apply foldr_subst_rgn_app.
  - assumption.
  - rewrite <- H2 in HNoDup.
    now apply NoDup_cons_app_comm.
  - intros k1 v1 b' In_k1_v1. apply H.
    rewrite <- H2.
    replace (list_to_map (elems1 ++ elems2))
      with ((list_to_map elems1 : Rho) ∪ (list_to_map elems2: Rho))
      by (symmetry; apply list_to_map_app).
    apply lookup_union_Some_raw.
    left. assumption.
Qed.

Lemma fold_subst_type:
  forall (f : RgnName → RgnVal → Tau → Tau),
  forall (l1 l2 : list (RgnName * RgnVal)),    
  forall k v (b : Tau),
    f = subst_in_type ->
    (forall x y1 y2,       
        (x, y1) ∈ (k, v) :: l2 ->
        (x, y2) ∈ (k, v) :: l2 -> y1 = y2) ->
    base.NoDup (l1.*1 ++ l2.*1) ->
    (forall k' v' b',
        (list_to_map l1 : Rho) !! k' = Some v ->
        f k' v' (f k v b') = f k v (f k' v' b')) ->
    foldr (uncurry f) b (l1 ++ (k, v) :: l2) =
      foldr (uncurry f) (f k v b) (l1 ++ l2).
Proof.
  intros f.
  induction l1; intros l2 k v b Hf HInj HNoDup H.
  - rewrite app_nil_l. rewrite app_nil_l.
    replace (f k v b) with (uncurry f (k,v) b) by (reflexivity).
    rewrite <- foldr_snoc.
    apply foldr_permutation.
    + constructor.
      * unfold Reflexive.
        reflexivity.
      * unfold Transitive.
        intuition. subst. reflexivity.
    + solve_proper.
    + intros. rewrite Hf.
      eapply subst_type_aux_comm_uncurry with (l:=(k, v) :: l2); eauto.
    + replace ((k, v) :: l2) with ( cons (k,v) nil ++ l2) by (simpl; reflexivity).
      apply app_Permutation_comm.
  - simpl. rewrite IHl1; clear IHl1. 
    + reflexivity.
    + assumption.
    + assumption.      
    + eapply NoDup_cons_app; eauto.
    + eapply NoDup_comm_some_function; eauto.
Qed.


Lemma fold_add_type:
  forall (f : RgnName → RgnVal → Tau → Tau),
  forall (l : list (RgnName * RgnVal)),
  forall (k: RgnName) (v: RgnVal) (b: Tau),
    f = subst_in_type ->
    (forall x y1 y2,
        (x, y1) ∈ (k, v)::l ->
        (x, y2) ∈ (k, v)::l ->
        y1 = y2) ->
    base.NoDup l.*1 ->
    (list_to_map l : Rho) !! k = None ->
    (forall k' v' b',
       (list_to_map l : Rho) !! k' = Some v ->
       f k' v' (f k v b') = f k v (f k' v' b')) ->
    foldr (uncurry f) b ( (k, v)::l) = foldr (uncurry f) (f k v b) l.
Proof.
  intros f l k v b Hf HInj HNoDup H' H.
  destruct (baz_2 l k v H') as [elems1 [elems2 [H1 H2]]]. 
  rewrite <- H1.
  rewrite <- H2.
  apply fold_subst_type.
  - assumption.
  - intros. apply HInj with (x:=x).
    + apply elem_of_cons in H0. destruct H0.
      * apply  elem_of_cons. left. assumption.
      * apply  elem_of_cons. right. rewrite <- H2.
        apply elem_of_app. right. assumption.
    + apply elem_of_cons in H3. destruct H3.
      * apply  elem_of_cons. left. assumption.
      * apply  elem_of_cons. right. rewrite <- H2.
        apply elem_of_app. right. assumption.    
  - rewrite <- H2 in HNoDup.
    replace (elems1.*1 ++ elems2.*1) with ((elems1 ++ elems2).*1).
    assumption.
    apply fmap_app.
  - intros k1 v1 b' In_k1_v1. apply H.
    rewrite <- H2.
    replace (list_to_map (elems1 ++ elems2))
      with ((list_to_map elems1 : Rho) ∪ (list_to_map elems2: Rho))
      by (symmetry; apply list_to_map_app).
    apply lookup_union_Some_raw.
    left. assumption.
Qed.  

Lemma subst_add_comm_rgn_aux:
  forall k v (rho : Rho),
    rho !! k = None ->
    forall rt, 
      fold_subst_rgn_alt ((k,v)::(map_to_list rho)) rt =
        fold_subst_rgn_alt (map_to_list rho) (subst_in_rgn k v rt).
Proof.
  intros.
  apply fold_add_rgn.
  - reflexivity.
  - econstructor.
    + apply not_elem_of_list_to_map_2. simpl.
      replace (list_to_map (map_to_list rho))
        with rho by (symmetry; apply list_to_map_to_list).
      assumption.
    + apply NoDup_fst_map_to_list.
  - replace (list_to_map (map_to_list rho)) with (rho)
      by (symmetry; apply list_to_map_to_list).
    assumption.
  -  intros k0 v0 b0 H'.
     unfold subst_in_rgn_alt.
     rewrite subst_type_rgn_comm_2.
     + reflexivity.
     + intro; subst.
       contradict H.
       apply NotNoneIsSome.
       exists v.
       replace (list_to_map (map_to_list rho)) with (rho) in H'
           by (symmetry; apply list_to_map_to_list).
       assumption.
Qed.


Lemma subst_add_comm_rgn:
  forall k v (rho : Rho),
    (forall  x y1 y2,
        (x, y1) ∈ (map_to_list (<[k:=v]> rho)) ->
        (x, y2) ∈ (map_to_list (<[k:=v]> rho)) -> y1 = y2) ->
    rho !! k = None ->
    forall rt, 
      fold_subst_rgn (<[ k:=v ]> rho) rt =
        fold_subst_rgn rho (subst_in_rgn k v rt).
Proof.
  intros.
  assert (k ∉ (map_to_list rho).*1)
    by (apply not_elem_of_list_to_map;
        replace (list_to_map (map_to_list rho)) with (rho)
          by (symmetry; apply list_to_map_to_list);
        assumption).  
  unfold fold_subst_rgn.
  do 2 rewrite subst_rgn_fold_foldr.
    replace (foldr (uncurry (λ (x : RgnName) (r : RgnVal) (rgn : Region_in_Type),
                      subst_rgn x (Rgn_Const true false r) rgn)) rt
             (map_to_list (<[k:=v]> rho)))
    with (foldr (uncurry subst_in_rgn_alt) rt (map_to_list (<[k:=v]> rho)))
    by (unfold subst_in_rgn_alt; reflexivity).
    replace (foldr (uncurry (λ (x : RgnName) (r : RgnVal) (rgn : Region_in_Type),
                        subst_rgn x (Rgn_Const true false r) rgn))
               (subst_in_rgn k v rt)  (map_to_list rho))
    with (foldr (uncurry subst_in_rgn_alt) (subst_in_rgn k v rt) (map_to_list rho))
      by (unfold subst_in_rgn_alt; reflexivity).
    
  assert (map_to_list (<[k:=v]> rho) ≡ₚ (k, v) :: map_to_list rho)
    by (apply map_to_list_insert; assumption).
  
  eapply  subst_add_comm_rgn_aux with (v:=v) (rt:=rt) in H0.
  unfold fold_subst_rgn_alt in H0. 
  rewrite <- H0.
  apply foldr_permutation. 
  - constructor.
    + unfold Reflexive.
      unfold Region_in_Type. dependent induction x; reflexivity.
    + unfold Transitive.
      unfold Region_in_Type. dependent induction x; intros; subst; reflexivity.
  - solve_proper.
  - intros.  eapply subst_rgn_aux_comm_uncurry; eauto.       
    assert (NoDup ((map_to_list rho).*1)) by apply NoDup_fst_map_to_list.
    assert (NoDup (((k,v)::(map_to_list rho)).*1)).  
    apply NoDup_cons; auto.   
    apply NoDup_fmap_1 in H7. 
    apply NoDup_fmap_fst; [now apply H |].
    apply NoDup_ListNoDup. apply NoDup_ListNoDup in H7.
    apply Permutation_sym in H2. 
    eapply Permutation_NoDup in H2; eauto.
  - assumption.
Qed.


Lemma subst_add_comm_sa:
  forall k v rho,
    (forall  x y1 y2,
        (x, y1) ∈ (map_to_list (<[k:=v]> rho)) ->
        (x, y2) ∈ (map_to_list (<[k:=v]> rho)) -> y1 = y2) ->
    rho !! k = None ->
    forall sa, 
      fold_subst_sa ((<[ k:=v ]> rho)) sa =
        fold_subst_sa rho (subst_in_sa k v sa).
Proof.
  intros k v rho HInj H sa.
  destruct sa; unfold Region_in_Type in r; dependent induction r;
    try (solve [unfold fold_subst_sa, subst_in_sa, subst_sa;
                f_equal; apply subst_add_comm_rgn; auto]).
Qed.


Lemma subst_add_comm_eff :
  forall k v rho,
    (forall  x y1 y2,
        (x, y1) ∈ (map_to_list (<[k:=v]> rho)) ->
        (x, y2) ∈ (map_to_list (<[k:=v]> rho)) -> y1 = y2) ->
    rho !! k = None ->
    forall eff, 
      fold_subst_eps (<[ k:=v ]> rho) eff
      = fold_subst_eps rho (subst_in_eff k v eff).
Proof.
  intros k v rho HInj H eff. unfold fold_subst_eps.
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
  forall k v (rho : Rho),
    (forall  x y1 y2,
        (x, y1) ∈ (map_to_list (<[k:=v]> rho)) ->
        (x, y2) ∈ (map_to_list (<[k:=v]> rho)) -> y1 = y2) ->
    rho !! k = None ->
    forall ty, 
      subst_rho (<[ k:=v ]> rho) ty =
        subst_rho rho (subst_in_type k v ty).
Proof.
  intros k v rho HInj H ty.
  unfold subst_rho.
  do 2 rewrite subst_in_type_fold_foldr.
  assert (map_to_list (<[k:=v]> rho) ≡ₚ (k, v) :: map_to_list rho)
    by (apply map_to_list_insert; assumption).
  assert (foldr (uncurry subst_in_type) ty (map_to_list (<[k:=v]> rho)) =
            foldr (uncurry subst_in_type) ty ((k,v) :: map_to_list rho)).
  apply foldr_permutation.
  - constructor.
    + unfold Reflexive.
      unfold Region_in_Type. dependent induction x; reflexivity.
    + unfold Transitive.
      unfold Region_in_Type. dependent induction x; intros; subst; reflexivity.
  - solve_proper.
  - intros.  eapply subst_type_aux_comm_uncurry; eauto.
  - assumption.
  - rewrite H1. 
    apply fold_add_type.
    + reflexivity.  
    + intros.
      apply HInj with (x:=x); try (solve [apply elem_of_list_In; 
        apply elem_of_list_In in H2;
        apply elem_of_list_In in H3;
        apply Permutation_sym in H0;
        eapply Permutation_in; eauto]).
    +  apply NoDup_fst_map_to_list.
    + replace ( list_to_map (map_to_list rho))
        with rho
        by (symmetry; apply list_to_map_to_list). 
      assumption.  
    + intros k0 v0 b0 H'.
      rewrite subst_type_type_comm_2.
      * reflexivity.
      * intro; subst.
        replace ( list_to_map (map_to_list rho))
        with rho in H'
            by (symmetry; apply list_to_map_to_list).
        rewrite H in H'. inversion H'.
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

