From stdpp Require Import gmap.
From stdpp Require Import fin_maps.
From stdpp Require Import list.
From stdpp Require Import base.
From stdpp Require Import strings.

Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import String.

Require Import Definitions.StaticActions.
Require Import Definitions.ComputedActions.
Require Import Definitions.Regions.
Require Import Definitions.GTypes.
Require Import Definitions.Values.
Require Import Definitions.Axioms.
Require Import Definitions.Tactics.

Require Import Proofs.RegionFacts.
Require Import Proofs.EffectFacts.
Require Import Proofs.LocallyNameless.
Require Import Definitions.GHeap.

Import Expressions.

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

  
Lemma update_rho:
  forall rho rgns x v,
    TcRho (rho, rgns) ->
    not_set_elem rgns x ->
    TcRho (update_R (x, v) rho, set_union rgns (singleton_set x)).
Proof.
  intros rho rgns x v HRho HFresh.
  unfold update_R; simpl. 
  econstructor.  
  intro r. split.
  - inversion_clear HRho as [rho' rgns' HRgn'  HRho''].
    destruct (ascii_eq_dec x r) as [c | c].
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
    destruct (ascii_eq_dec x r) as [c | c].
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


Lemma subst_type_rgn_comm_2:
  forall r k1 k2 v1 v2,
    k1 <> k2 ->
    subst_rgn k1 (Rgn_Const true false v1) (subst_rgn k2 (Rgn_Const true false v2) r) =
    subst_rgn k2 (Rgn_Const true false v2) (subst_rgn k1 (Rgn_Const true false v1) r).
Proof.
  intros r k1 k2 v1 v2 H.
  unfold Region_in_Type in r.
  dependent induction r; try (solve [simpl; reflexivity ]).
  unfold subst_rgn. destruct (ascii_eq_dec k1 k2).
  - inversion e. contradiction.
  - simpl. destruct (ascii_eq_dec k2 r).
    + assert (k1 <> r) by congruence.
      destruct (ascii_eq_dec k1 r).
      * now absurd (k1=r).
      * inversion e; subst; now destruct (ascii_eq_dec r r).
    + destruct (ascii_eq_dec k1 r); [reflexivity |].
      now destruct (ascii_eq_dec k2 r).
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
    destruct (ascii_eq_dec k k').
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
    destruct (ascii_eq_dec r2 r); destruct (ascii_eq_dec r0 r); subst.
    + { assert (HSubst: r1 = r3).
        apply Rho_SameKey_SameValue with (l:=l) (x:=r).
        - eapply elem_of_list_lookup_2; eauto.
        - eapply elem_of_list_lookup_2; eauto.
        - subst. reflexivity. }
    + simpl. destruct (ascii_eq_dec r r).
      * reflexivity.
      * contradiction.      
    + simpl. destruct (ascii_eq_dec r r).
      * reflexivity.
      * contradiction.
    + simpl. destruct (ascii_eq_dec r2 r); destruct (ascii_eq_dec r0 r); subst.      
      * contradiction.
      * contradiction.
      * contradiction.
      * reflexivity.
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
    destruct (ascii_eq_dec x1 x2); subst.
    + apply elem_of_list_lookup_2 in H0.
      apply elem_of_list_lookup_2 in H1.
      eapply Rho_SameKey_SameValue in H0; eauto. subst.
      reflexivity.
    + unfold subst_in_rgn.
      apply subst_rgn_aux_comm. assumption.  
  - do 2 rewrite subst_rho_arrow_uncurry.
    f_equal; auto;  
    destruct a1 as [x1 v1]; destruct a2 as [x2 v2]; simpl. 
    + destruct (ascii_eq_dec x1 x2); subst.
      * apply elem_of_list_lookup_2 in H0.
        apply elem_of_list_lookup_2 in H1.
        eapply Rho_SameKey_SameValue in H0; eauto. subst.
        reflexivity.
      * apply subst_eps_aux_comm. assumption.  
    + destruct (ascii_eq_dec x1 x2); subst.
      * apply elem_of_list_lookup_2 in H0.
        apply elem_of_list_lookup_2 in H1.
        eapply Rho_SameKey_SameValue in H0; eauto. subst.
        reflexivity.
      * apply subst_eps_aux_comm. assumption.  
  - do 2 rewrite subst_rho_forall_uncurry.
    f_equal; auto.
    destruct a1 as [x1 v1]; destruct a2 as [x2 v2]; simpl. 
    + destruct (ascii_eq_dec x1 x2); subst.
      * apply elem_of_list_lookup_2 in H0.
        apply elem_of_list_lookup_2 in H1.
        eapply Rho_SameKey_SameValue in H0; eauto. subst.
        reflexivity.
      * apply subst_eps_aux_comm. assumption.
Qed.

  
Lemma NoDup_cons_app:
  forall a (l1 l2 :  list (RgnName * RgnVal)),
    NoDup ((a :: l1).*1 ++ l2.*1) ->
    NoDup (l1.*1 ++ l2.*1).
Proof.
  intros a l1 l2 HNoDup.
  apply list.NoDup_app.
  split.
  - apply NoDup_app in HNoDup.
    destruct HNoDup as [H1 H2].
    assert (H1' : a.1 ∉ l1.*1 ∧ NoDup l1.*1) by (apply list.NoDup_cons; assumption).
    destruct H1'.
    assumption.
  - split; apply NoDup_app in HNoDup; destruct HNoDup as [H1 H2]; destruct H2.
    + apply list.NoDup_cons in H1.
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
  destruct (ascii_eq_dec k' ka).
  - apply NoDup_app in HNoDup; destruct HNoDup as [Ha Hb]; destruct Hb.
    assert (H1' : ka ∉ l1.*1 ∧ NoDup l1.*1)
      by (apply list.NoDup_cons; assumption).
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
    base.NoDup (l1.*1++ l2.*1) ->
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


Lemma fold_add_rgn:
  forall (f : RgnName → RgnVal → Region_in_Type → Region_in_Type),
  forall (l : list (RgnName * RgnVal)),
  forall (k: RgnName) (v: RgnVal) (b: Region_in_Type),
    f = subst_in_rgn ->
    base.NoDup l.*1 ->
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

Lemma fold_subst_type:
  forall (f : RgnName → RgnVal → Tau → Tau),
  forall (l1 l2 : list (RgnName * RgnVal)),    
  forall k v (b : Tau),
    f = subst_in_type ->
    base.NoDup (l1.*1 ++ l2.*1) ->
    (forall k' v' b',
        (list_to_map l1 : Rho) !! k' = Some v ->
        f k' v' (f k v b') = f k v (f k' v' b')) ->
    foldr (uncurry f) b (l1 ++ (k, v) :: l2) =
      foldr (uncurry f) (f k v b) (l1 ++ l2).
Proof.
  intros f.
  induction l1; intros l2 k v b Hf HNoDup H.
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
    + eapply NoDup_cons_app; eauto.
    + eapply NoDup_comm_some_function; eauto.
Qed.


Lemma fold_add_type:
  forall (f : RgnName → RgnVal → Tau → Tau),
  forall (l : list (RgnName * RgnVal)),
  forall (k: RgnName) (v: RgnVal) (b: Tau),
    f = subst_in_type ->
    base.NoDup l.*1 ->
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
  apply fold_subst_type.
  - assumption.
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
  - assert (H' : base.NoDup (map_to_list rho)) by (apply NoDup_map_to_list).
    apply rho_NoDup_map_fst.
    assumption.
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
    rho !! k = None ->
    forall rt, 
      fold_subst_rgn (<[ k:=v ]> rho) rt =
        fold_subst_rgn rho (subst_in_rgn k v rt).
Proof.
  intros. 
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
  
  eapply  subst_add_comm_rgn_aux with (v:=v) (rt:=rt) in H.
  unfold fold_subst_rgn_alt in H.
  rewrite <- H.
  
  apply foldr_permutation.
  - constructor.
    + unfold Reflexive.
      unfold Region_in_Type. dependent induction x; reflexivity.
    + unfold Transitive.
      unfold Region_in_Type. dependent induction x; intros; subst; reflexivity.
  - solve_proper.
  - intros.  eapply subst_rgn_aux_comm_uncurry; eauto.
  - assumption.
Qed.

Lemma subst_add_comm_sa:
  forall k v rho,
    rho !! k = None ->
    forall sa, 
      fold_subst_sa ((<[ k:=v ]> rho)) sa =
        fold_subst_sa rho (subst_in_sa k v sa).
Proof.
  intros k v rho H sa.
  destruct sa; unfold Region_in_Type in r; dependent induction r;
    try (solve [unfold fold_subst_sa, subst_in_sa, subst_sa;
                f_equal; apply subst_add_comm_rgn; auto]).
Qed.


Lemma subst_add_comm_eff :
  forall k v rho,
    rho !! k = None ->
    forall eff, 
      fold_subst_eps (<[ k:=v ]> rho) eff
      = fold_subst_eps rho (subst_in_eff k v eff).
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
  forall k v (rho : Rho),
    rho !! k = None ->
    forall ty, 
      subst_rho (<[ k:=v ]> rho) ty =
        subst_rho rho (subst_in_type k v ty).
Proof.
  intros k v rho H ty.
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
    + assert (H' : base.NoDup (map_to_list rho)) by (apply NoDup_map_to_list).
      now apply rho_NoDup_map_fst.
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



Lemma NotFreeInEmptyEps:
  forall x,
    ~ free_rgn_vars_in_eps (Empty_set StaticAction) x.
Proof.
  intro x. intro. 
  unfold free_rgn_vars_in_eps, empty_set in H.
  destruct H as [sa]. destruct H.
  inversion H.
Qed.


Lemma G_same_key {A}:
  forall l1 l2 v (heap : gmap RgnName A),
    l1 = l2 -> 
    heap !! l1 = Some v ->
    (<[ l2:=v ]> heap) !! l1 = Some v.
Proof.
  intros.
  rewrite H.
  rewrite  lookup_insert_Some.
  left. split; reflexivity.
Qed.

Lemma G_update_same_value `{Countable K} {A}: 
  forall (heap : gmap K A) l v v',
    (<[ l:=v ]> heap) !! l= Some v' ->
    v = v'.
Proof.
  intros heap l v v' Hfind. 
  rewrite lookup_insert_Some in Hfind.
  destruct Hfind as [[Ha Hb] | [Hc Hd]].
  - assumption.
  - contradict Hc. reflexivity.
Qed.

Lemma G_diff_keys_1 `{Countable K} {A} :
  forall a b v v' (env : gmap K A),
    a <> b ->
    (<[ b:=v ]> env) !! a = Some v' -> 
    env !! a = Some v'.
Proof.
  intros.
  apply lookup_insert_Some in H1.
  destruct H1 as [[Ha Hb] | [Hc Hd]].
  - contradict H0. now symmetry.
  - assumption.
Qed.


Lemma G_diff_keys_2 `{Countable K} {A}:
  forall a b v v' (env : gmap K A),
    b <> a ->
    env !! a = Some v' ->
    (<[ b:=v ]> env) !! a = Some v'.
Proof.
  intros.
  apply  lookup_insert_Some.
  right. split; assumption.
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
  destruct (ascii_eq_dec x0 x) as [c | c]; subst.  
  - unfold update_T in H; simpl in H.    
    assert ( HSubst : <[x:=tyx]> (<[f:=Ty_Arrow tyx effc tyc effe Ty_Effect]> ctxt) !! x
                      = Some tyx)
      by (apply lookup_insert). 
    rewrite H in HSubst.
    inversion HSubst; subst.
    do 2 intro. eapply HFind1. assumption.
  - destruct (ascii_eq_dec x0 f) as [d | d].
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
      destruct (ascii_eq_dec x k); subst.
      * contradict H1. apply NotNoneIsSome. exists v.
        apply lookup_insert.
      * apply not_elem_of_list_to_map_2 in H1.
        apply not_elem_of_list_to_map_1.
        assert ( x ≠ k ∧ x ∉ l.*1) by (apply not_elem_of_cons; assumption).
        intuition.
    + destruct a as [k v]. 
      destruct (ascii_eq_dec x k); subst.
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
  inversion_clear HRho as [rho' rgns' HRgn' HVal''].
  constructor; auto.
  intros x0 v0 t0 HE' HT'. eapply HV in HE'; eauto. unfold update_R. simpl.
  rewrite subst_add_comm. 
  - eapply subst_rho_fresh_var; eauto. econstructor; auto. 
  - unfold not_set_elem in HRgns. unfold Ensembles.Complement in HRgns.
    apply not_elem_of_dom.
    intro. apply elem_of_dom in H.
    unfold is_Some in H. apply NotNoneIsSome in H.
    eapply HRgn' in H. contradiction. 
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
  - destruct (ascii_eq_dec x r) as [c | c]; subst.
    + inversion HRho; subst.   
      contradict H.
      destruct (subst_rho_fvar_1 rho r) as [[v' H0] | H0]. 
      * rewrite H0. simpl. intro. contradiction.
      * rewrite H0. simpl. intro. 
        unfold set_elem, In in H1.
        destruct H1 with (r:=r). 
        { apply H3 in HInc.
          - apply NotNoneIsSome in HInc.
            destruct HInc. 
            apply subst_rho_fvar_2 in H4.
            rewrite H4 in H0. 
            inversion H0.
          - apply Union_introl. simpl. auto. }
   + inversion HRho; subst.
     contradict H.
     destruct (subst_rho_fvar_1 rho r) as [[v' H0] | H0].
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
            + unfold In in H0.
              rewrite fold_subst_eps_fold_foldr in H0.
              eapply TcRhoIncludedNoFreeVarsEps_aux_fold; eauto. 
            + unfold included, Included, Ensembles.In in *.
              intro. intro.
              apply HInc.
              apply Ensembles.Union_intror. apply Ensembles.Union_introl.
              apply Ensembles.Union_introl. assumption.
          - eapply TcRhoIncludedNoFreeVarsEps_main with (e:=e0); eauto.
            + unfold In in H0.
              rewrite fold_subst_eps_fold_foldr in H0.
              eapply TcRhoIncludedNoFreeVarsEps_aux_fold; eauto. 
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
      * rewrite fold_subst_eps_fold_foldr in H0.
        eapply TcRhoIncludedNoFreeVarsEps_aux_fold; eauto.        
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
    destruct (ascii_eq_dec x0 x) as [c | c]; subst.
    + subst. exists t.
      apply lookup_insert.
    + eapply G_diff_keys_1 in HF; auto; subst. 
      destruct (HE x0 v0) as [t0 HU] ; [auto | ] ; exists t0.
      eapply G_diff_keys_2; [ auto | exact HU]. 
  - intros x0 t0 HF. (** "TcEnv is well-typed: HT".  **)
    destruct (ascii_eq_dec x0 x) as [c | c]; intros; subst.    
    + exists v. apply lookup_insert.
    + eapply G_diff_keys_1 in HF; auto.
      destruct (HT x0 t0) as [x1 ?] ; [auto | ].
      exists x1; [eapply G_diff_keys_2]; auto.
  - intros x0 v0 t0 HFindE HFindT. (** "Type preservation: HV". **)
    destruct (ascii_eq_dec x0 x) as [c | c]; intros; subst.
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
