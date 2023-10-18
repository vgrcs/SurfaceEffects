Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Ascii.
Require Import StaticActions.
Require Import ComputedActions.
Require Import Types.
Require Import Regions.
Require Import Keys.
Require Import Coq.Arith.PeanoNat.

Lemma ClosedType :
 forall tau x,
   frv tau = empty_set ->
   x # tau.
Proof.
  intros.
  unfold not_set_elem, Complement.
  rewrite H.
  intuition.
  contradiction.
Qed.

Lemma FreeVariables1 :
 forall x t, x # t ->  not_set_elem_frv t x .
Proof.
  intro x. induction t; intro; try (solve [unfold not_set_elem; simpl; auto]).
  - simpl in *. 
    unfold not_set_elem, Complement, not in *.
    split; try (solve [intro; apply H; constructor; assumption]).
  - simpl in *.
    unfold not_set_elem, Complement, not in *.
    split; try (solve [intro; apply H; constructor; assumption]).
  - simpl in *.
    unfold not_set_elem, Complement, not in *.
    repeat split; intro; apply H.
    + now apply Union_introl.
    + apply Union_intror. apply Union_introl.  now apply Union_introl.
    + apply Union_intror. apply Union_introl.  now apply Union_intror.
    + apply Union_intror. apply Union_intror. now apply Union_introl.
    +  apply Union_intror. apply Union_intror. now apply Union_intror.   
  - simpl in *.
    unfold not_set_elem, Complement, not in *.
    split; intro; apply H.
    + now apply Union_introl.
    + now apply Union_intror.  
Qed.

Lemma FreeVariables2 :
 forall x t,  not_set_elem_frv t x -> x # t.
Proof.
 intro x. induction t; intro; unfold not_set_elem, Complement. 
 - intro HG. contradict HG.
 - intro HG. contradict HG.
 - intro HG. contradict HG.
 - intro HG. contradict HG.
 - destruct H as [HA HB].
   unfold not_set_elem, Complement, not in *.
   intro.
   inversion H as [H1 H2 | H3 H4]; subst; [now apply HA | now apply HB]. 
 - destruct H as [HA HB].
   unfold not_set_elem, Complement, not in *.
   intro.
   inversion H as [H1 H2 | H3 H4]; subst; [now apply HA | now apply HB]. 
 - destruct H as [H1 H2]. 
   destruct H2 as [HA [HB [HC HD]]].
   unfold not; intro HG.
   destruct HG; [apply H1; auto |].  
    do 2 destruct H; [apply HA | apply HB | apply HC | apply HD]; auto.
 - destruct H.
   unfold not; intro HG. destruct HG; unfold not_set_elem, Complement in H; now apply H.
Qed.

 (** end of free regions **)
 


Lemma subst_as_close_open_rgn :
  forall n r x u,
    lc_type_rgn r ->
    subst_rgn x u r = opening_rgn_in_rgn n (mk_rgn_type u) (closing_rgn_in_rgn n x r).
Proof.
  intros n r x u H. inversion H; subst; simpl.
  - reflexivity.
  - destruct (AsciiVars.eq_dec x r0).
    + inversion e. destruct (AsciiVars.eq_dec r0 r0); simpl.
      * rewrite PeanoNat.Nat.eqb_refl. reflexivity.
      * unfold AsciiVars.eq in *. contradict n0. reflexivity.
    + destruct (AsciiVars.eq_dec r0 x); unfold AsciiVars.eq in *.
      * symmetry in e. contradiction.
      * simpl. reflexivity.
Qed.        

      
Lemma subst_as_close_open_sa :
  forall n x u sa,
    lc_type_sa sa ->
    subst_sa x u sa =
    opening_rgn_in_sa n (mk_rgn_type u) (closing_rgn_in_sa n x sa).
Proof.
  intros n x u sa H.
  inversion H; subst;
  unfold subst_sa, opening_rgn_in_sa, closing_rgn_in_sa;
  f_equal; apply subst_as_close_open_rgn; auto.
Qed.  


Lemma subst_as_close_open_eps :
  forall n x u e,
    lc_type_eps e ->
    subst_eps x u e =
    opening_rgn_in_eps n (mk_rgn_type u) (closing_rgn_in_eps n x e).
Proof.
  intros n x u e H . 
  apply Extensionality_Ensembles. 
  unfold Same_set, Included. intuition; unfold In in *.
  - unfold subst_eps in H0. inversion H; subst.
    unfold opening_rgn_in_eps, closing_rgn_in_eps.
    destruct H0 as [sa [H2 H3]]. subst.
    exists (closing_rgn_in_sa n x sa). split.
    + exists sa. intuition.
    + rewrite <- subst_as_close_open_sa; auto.
      destruct (H1 sa). assumption.
  - unfold subst_eps. inversion H; subst.
    unfold opening_rgn_in_eps, closing_rgn_in_eps in H0.
    destruct H0 as [x' [[x'' [H2 H3]] H4]]. subst.
    destruct (H1 x''). exists x''. intuition.
    rewrite <- subst_as_close_open_sa; auto.
Qed.    


Definition close_open_var := forall t x, x # t -> close_var x (open_var t x) = t.

Definition open_close_var := forall x t, lc_type t -> open_var (close_var x t) x = t.

Definition open_var_inj := forall x t1 t2, x # t1 -> x # t2 -> open_var t1 x = open_var t2 x -> t1 = t2.

Definition open_lc := forall u t, lc_type t -> open u t = t.

Definition subst_open := forall x u t v, lc u -> [x := u] (open v t) = open (subst_rgn x u v) ([x := u] t).

Definition subst_open_var := forall x y u t, x <> y -> lc u -> [x := u] (open_var t y) = open_var ([x := u] t) y.

Definition subst_fresh := forall x t u, x # t -> [x := u] t = t.

Definition subst_intro := forall x t u, x # t -> lc u -> open (mk_rgn_type u) t = [x := u] (open_var t x).
 
Definition subst_as_close_open := forall x t u, lc_type t ->
                                                [x := u] t = open  (mk_rgn_type u) (close_var x t).

Lemma SUBST_AS_CLOSE_OPEN : subst_as_close_open.
Proof.
  intros x t u H. unfold open, close_var. generalize 0. intro. 
  dependent induction t; intros; simpl; try (solve [reflexivity]).
  - inversion H; subst.
    f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal;[ | apply IHt]. unfold subst_rgn, opening_rgn_in_rgn, closing_rgn_in_rgn.
    unfold Region_in_Type in r. dependent induction r. 
    + reflexivity.
    + destruct (AsciiVars.eq_dec v x); destruct (AsciiVars.eq_dec x v).
      * rewrite PeanoNat.Nat.eqb_refl. reflexivity.
      * unfold  AsciiVars.eq in *. symmetry in e. contradiction.
      * unfold  AsciiVars.eq in *. symmetry in e. contradiction.
      * reflexivity. 
    + inversion H; subst.  inversion H2.
    + inversion H; subst. assumption.
  - f_equal;[apply IHt1 | | apply IHt2 | | apply IHt3]; try auto; inversion H; subst; auto.
    + apply subst_as_close_open_eps; auto.
    + apply subst_as_close_open_eps; auto.
  - f_equal.
    + apply subst_as_close_open_eps. inversion H. assumption. 
    + apply IHt. inversion H; subst; auto.
    
Qed.

Lemma close_open_rgn : 
  forall r n x, (In VarId (free_rgn_vars_in_rgn r) x -> False) ->
                closing_rgn_in_rgn n x (opening_rgn_in_rgn n (Rgn2_FVar true true x) r) = r.
Proof.
  intros r n x H.
  unfold closing_rgn_in_rgn, opening_rgn_in_rgn. 
  unfold Region_in_Type in r; dependent induction r; intros.
  - reflexivity.
  - case (AsciiVars.eq_dec v x); intros.
    + contradict H. inversion e; subst. unfold free_rgn_vars_in_rgn. apply In_singleton.
    + reflexivity.
  - case_eq (Nat.eqb n n0); intros; simpl; [ | reflexivity].
    destruct (AsciiVars.eq_dec x x).
    + apply Nat.eqb_eq in H0.  subst; reflexivity.
    + contradict n1. unfold AsciiVars.eq. reflexivity.
Qed.

Lemma close_open_sa : 
  forall sa n x, (In VarId (free_rgn_vars_in_sa sa) x -> False) ->
                 closing_rgn_in_sa n x (opening_rgn_in_sa n (Rgn2_FVar true true x) sa) = sa.
Proof.
  intros sa n x H.
  unfold closing_rgn_in_sa, opening_rgn_in_sa. 
  destruct sa; rewrite close_open_rgn; auto.
Qed.
  
Lemma close_open_eps :
  forall e x n , (In VarId (free_rgn_vars_in_eps e) x -> False) ->
                 closing_rgn_in_eps n x (opening_rgn_in_eps n (Rgn2_FVar true true x) e) = e. 
Proof.
  intros e x n H.
  apply Extensionality_Ensembles.
  split. 
  + intro sa. unfold In in *.
    unfold closing_rgn_in_eps; unfold opening_rgn_in_eps; simpl. 
    
    intros [sa' [[sa'' [H2 H3]] H1]]. subst.
    rewrite close_open_sa; eauto.
    intro. apply H.
    unfold free_rgn_vars_in_eps; unfold In.
    exists sa''; auto.
  + intro sa. unfold In in *.
    unfold closing_rgn_in_eps; unfold opening_rgn_in_eps; simpl.
    intro H1.
    exists (opening_rgn_in_sa n (Rgn2_FVar true true x) sa).
    rewrite close_open_sa.
    split; [exists sa; auto | reflexivity].
    intro. apply H.
    unfold free_rgn_vars_in_eps; unfold In.
    exists sa; auto.
Qed.

Lemma CLOSE_OPEN_VAR : close_open_var. 
Proof. 
  intros t x H.  unfold close_var, open_var.  generalize 0.
  induction t; simpl; intro; try (solve [reflexivity]);
  unfold not_set_elem, set_union, empty_set, Complement, not in *. 
  - f_equal; [apply IHt1 | apply IHt2]; simpl in H; intro; apply H.
    + now apply Union_introl.
    + now apply Union_intror.
  - simpl in H. assert (H' : In VarId (free_rgn_vars_in_rgn r) x -> False)
      by (intros; apply H; now apply Union_introl).
    f_equal; unfold Region_in_Type in r; dependent induction r; subst; simpl.
    + reflexivity.
    + case (AsciiVars.eq_dec v x); intros. unfold AsciiVars.eq in e; subst.
      * contradict H'. unfold free_rgn_vars_in_rgn. apply In_singleton.
      * reflexivity.
    + case_eq (Nat.eqb n n0); intros; simpl.
      * apply Nat.eqb_eq in H0; subst.
        destruct (AsciiVars.eq_dec x x);  [reflexivity | contradict n; reflexivity].
      * reflexivity.
    + apply IHt. intros. apply H. now apply Union_intror.
    + apply IHt. intros. apply H. now apply Union_intror.
    + apply IHt. intros. apply H. now apply Union_intror.
  - simpl in H. f_equal.
    + apply IHt1. intro; apply H. now apply Union_introl.
    + apply close_open_eps.
      intros. apply H. apply Union_intror. apply Union_introl. now apply Union_introl.
    + apply IHt2.  intro; apply H. apply Union_intror. apply Union_intror. now apply Union_introl.
    + apply close_open_eps.
      intros. apply H. apply Union_intror. apply Union_introl. now apply Union_intror.
    +  apply IHt3. intro; apply H.  apply Union_intror. apply Union_intror. now apply Union_intror.
  - simpl in H. f_equal.
    + apply close_open_eps.
      intros. apply H. apply Union_introl; auto.
    + apply IHt.
      intros. apply H. apply Union_intror; auto.
Qed.


Lemma OPEN_VAR_INJ : open_var_inj.
Proof.
  intros x t1 t2 HF1 HF2 HEq.
  rewrite <- (CLOSE_OPEN_VAR t1 x); auto.
  rewrite <- (CLOSE_OPEN_VAR t2 x); auto.
  f_equal. assumption.
Qed.



Lemma open_close_rgn :
  forall r n x,
    lc_type_rgn r ->
    opening_rgn_in_rgn n (Rgn2_FVar true true x) (closing_rgn_in_rgn n x r) = r.
Proof. 
  intros. induction H; unfold opening_rgn_in_rgn, closing_rgn_in_rgn.
  - reflexivity.
  - destruct (AsciiVars.eq_dec r x).
    + rewrite PeanoNat.Nat.eqb_refl.
      inversion e; subst.
      reflexivity.
    + reflexivity.
Qed.      


Lemma opening_lc_sa :
  forall n x sa,
    lc_type_sa sa ->
    opening_rgn_in_sa n (Rgn2_FVar true true x) sa = sa.
Proof.
  intros n x sa H. unfold opening_rgn_in_sa.
  dependent induction sa; f_equal; inversion H; subst; inversion H1; simpl; reflexivity.
Qed.

Lemma open_close_sa :
  forall n x sa,
    lc_type_sa sa ->
    opening_rgn_in_sa n (Rgn2_FVar true true x) (closing_rgn_in_sa n x sa) = sa.
Proof.
  intros n x sa H.
  induction H; unfold opening_rgn_in_sa, closing_rgn_in_sa;
  rewrite open_close_rgn; auto.
Qed.


Lemma open_close_eps :
  forall eff n x,
    lc_type_eps eff ->
    opening_rgn_in_eps n (Rgn2_FVar true true x) (closing_rgn_in_eps n x eff) = eff.
Proof. 
  intros eff n x H. unfold opening_rgn_in_eps, closing_rgn_in_eps. 
  apply Extensionality_Ensembles.
  split.
  - intro sa. unfold In in *. 
    intros [sa' [[sa'' [H2 H3]] H1]]. subst. inversion H; subst. 
    destruct (H0 sa'').
    unfold opening_rgn_in_sa, closing_rgn_in_sa.  
    destruct sa''; rewrite open_close_rgn; auto; inversion H3; subst; assumption.
  - intro sa. intros. unfold In in *. 
    inversion H; subst.    
    exists (closing_rgn_in_sa n x sa). split. 
    + exists sa. intuition.  
    + destruct (H1 sa).
      rewrite open_close_sa; auto.
Qed.
    
Lemma OPEN_CLOSE_VAR : open_close_var.
Proof.
  intros x t H. unfold open_var, close_var. generalize 0.
  induction H; intros; simpl.
  - reflexivity.
  - f_equal; [apply IHlc_type1 | apply IHlc_type2].
  - f_equal; [ rewrite open_close_rgn; auto | apply IHlc_type].
  - f_equal; try (solve [rewrite  open_close_eps; auto]); [apply IHlc_type1 | apply IHlc_type2 | apply IHlc_type3].
  - f_equal. rewrite  open_close_eps; auto. apply  IHlc_type.
Qed.

Lemma open_subst_lc_sa:
  forall n u sa,
    lc_type_sa sa ->
    opening_rgn_in_sa n u sa = sa.
Proof.
  intros n u sa H.
  unfold opening_rgn_in_sa.
  inversion H; subst;
  unfold opening_rgn_in_rgn; unfold Region_in_Type in r;
  dependent induction r; try (solve [reflexivity | inversion H1 | inversion H; inversion H2]).
Qed.  

Lemma open_subst_lc_eps:
  forall n u eff,
    lc_type_eps eff ->
    opening_rgn_in_eps n u eff = eff.
Proof.
  intros n u eff Hlc.
  induction Hlc; intros; simpl.
  apply Extensionality_Ensembles. unfold Same_set, Included.
  intuition; unfold In in *.
  - unfold opening_rgn_in_eps in H0.
    destruct H0 as [x' [H1 H2]].
    erewrite open_subst_lc_sa in H2; eauto.
    + subst. assumption.
    + destruct (H x'); auto. 
  - unfold opening_rgn_in_eps.
    exists x. intuition.
    erewrite open_subst_lc_sa; eauto.
    destruct (H x); auto.
Qed.
    
Lemma OPEN_LC : open_lc. 
Proof.
  intros u t Hlc. unfold open.
  generalize 0. induction Hlc; intros; simpl.
  - reflexivity.
  - f_equal; [apply IHHlc1  | apply IHHlc2].
  - f_equal; [| apply IHHlc].
    unfold opening_rgn_in_rgn.
    unfold Region_in_Type in r. dependent induction r.
    + reflexivity.
    + reflexivity.
    + inversion H.
  - f_equal; try (solve [apply IHHlc1 | apply IHHlc2 | apply IHHlc3]).
    + apply Extensionality_Ensembles. unfold Same_set, Included.
      split; intros. unfold In in *.
      * destruct H1 as [x' ?]. intuition.
        inversion H; subst.
        destruct (H1 x').
        eapply open_subst_lc_sa in H4; eauto.
        rewrite H4. assumption.
      * rewrite open_subst_lc_eps; auto.
    + apply Extensionality_Ensembles. unfold Same_set, Included.
      split; intros. unfold In in *.
      * destruct H1 as [x' ?]. intuition.
        inversion H0; subst.
        destruct (H1 x').
        eapply open_subst_lc_sa in H4; eauto.
        rewrite H4. assumption.
      * rewrite open_subst_lc_eps; auto.       
  - f_equal; [ rewrite open_subst_lc_eps; auto | apply IHHlc].
Qed.

Lemma subst_open_rgn :
  forall x u n v r,
    subst_rgn x u (opening_rgn_in_rgn n v r) =
      opening_rgn_in_rgn n (subst_rgn x u v) (subst_rgn x u r).
Proof.
  intros x u n v r.
  unfold Region_in_Type in r.
  dependent induction r; try (solve [reflexivity]). 
  - destruct (AsciiVars.eq_dec v0 x). 
    + unfold subst_rgn, opening_rgn_in_rgn, closing_rgn_in_rgn.
      inversion e; subst.
      destruct (AsciiVars.eq_dec x x); [ | reflexivity].
      unfold Region_in_Expr in u.
      dependent induction u; simpl; reflexivity.
    + unfold subst_rgn, opening_rgn_in_rgn, closing_rgn_in_rgn.
      unfold AsciiVars.eq in n0.
      destruct (AsciiVars.eq_dec x v0); [ | reflexivity].
      unfold AsciiVars.eq in e. symmetry in e. contradiction.
  - unfold subst_rgn, opening_rgn_in_rgn, closing_rgn_in_rgn.
    case (Nat.eqb n0 n); [ | reflexivity].
    unfold Region_in_Type in v.
    dependent induction v; reflexivity.
Qed.

Lemma subst_open_sa:
  forall n x u v e,
    subst_sa x u (opening_rgn_in_sa n v e) =
      opening_rgn_in_sa n (subst_rgn x u v) (subst_sa x u e).
Proof.
  intros n x u v e.
  destruct e; simpl; f_equal; rewrite subst_open_rgn; reflexivity.
Qed.


Lemma subst_open_eps:
  forall n x u v e,
    subst_eps x u (opening_rgn_in_eps n v e) =
      opening_rgn_in_eps n (subst_rgn x u v) (subst_eps x u e).
Proof.
  intros n x u v e.
  unfold subst_eps, opening_rgn_in_eps. 
  apply Extensionality_Ensembles; unfold Same_set, Included.
  intuition; unfold In in *;
  destruct H as [x1 [[x2 [H2 H3]] H4]]; subst.
  - rewrite subst_open_sa.
    exists (subst_sa x u x2); intuition. exists x2; intuition.
  - rewrite <- subst_open_sa.
    exists (opening_rgn_in_sa n v x2); intuition. exists x2; intuition.
Qed.


Lemma SUBST_OPEN : subst_open.
Proof. 
  intros x u t v.  unfold open.  generalize 0.
  induction t; intros; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.  
  - f_equal; [apply IHt1 |  apply IHt2]; assumption.
  - (*unfold open_rgn_in_type, close_rgn_in_type; simpl.*)
    f_equal; [ |  apply IHt]; auto.
    fold (subst_rgn x u (opening_rgn_in_rgn n v r)).
    fold (subst_rgn x u r).
    rewrite subst_open_rgn; auto.
  - (*unfold open_rgn_in_type, close_rgn_in_type; simpl.*)
    f_equal; try (solve [apply IHt1;auto | apply IHt2;auto | apply IHt3;auto]). 
    + rewrite subst_open_eps; auto. 
    + rewrite subst_open_eps; auto. 
  - f_equal; [ |  apply IHt]; auto.
    rewrite subst_open_eps; auto. 
Qed.

Lemma SUBST_OPEN_VAR : subst_open_var.
Proof.
  intros x y u t H Hlc. 
  unfold open_var.
  rewrite SUBST_OPEN; auto.
  unfold open. f_equal. simpl.
  destruct (AsciiVars.eq_dec x y).
  - inversion e. contradiction.
  - reflexivity.
Qed.

Lemma singleton_eq :
  forall x y,
    x = y <-> Singleton VarId x y.
Proof.
  intros x y. split.
  - intros H; subst. apply In_singleton.
  - intros H. inversion H. reflexivity.
Qed.

Lemma subst_fresh_rgn :
  forall r x u,
    not_set_elem (free_region r) x ->
    subst_rgn x u r = r.
Proof.
  intros r x u H.
  unfold not_set_elem, free_region, Complement in H.
  unfold free_rgn_vars_in_rgn in H.
  unfold subst_rgn.
  unfold Region_in_Type in r.
  dependent induction r.
  - reflexivity.
  - unfold not, In, singleton_set in H.
    assert (x <> v) by (contradict H; apply singleton_eq; auto).
    destruct (AsciiVars.eq_dec x v).
    + inversion e. contradiction.
    + reflexivity.
  - reflexivity.
Qed.

Lemma subst_fresh_sa :
  forall sa x u,
    not_set_elem (free_rgn_vars_in_sa sa) x ->
    subst_sa x u sa = sa.
Proof.  
  intros sa x u H.
  unfold not_set_elem, Complement, free_rgn_vars_in_sa in H.
  induction sa; unfold subst_sa, subst_rgn; f_equal;
  unfold free_rgn_vars_in_rgn in H; unfold In in *; 
  unfold Region_in_Type in r;
  dependent induction r; try (solve [reflexivity |
                                     assert (x <> v) by (contradict H; now apply singleton_eq);
                                     destruct (AsciiVars.eq_dec x v); [inversion e; contradiction | reflexivity]]). 
Qed.

Lemma subst_fresh_sa_ext :
  forall (e : Epsilon) sa x u,
    e sa -> not_set_elem (free_rgn_vars_in_sa sa) x ->
    (exists sa' : StaticAction, e sa' /\ subst_sa x u sa' = sa).
Proof.
  intros e sa x u H.
  exists sa. intuition.
  now apply subst_fresh_sa.
Qed.


Lemma subst_fresh_eps :
  forall e x u,
    not_set_elem (free_rgn_vars_in_eps e) x ->
    subst_eps x u e = e.
Proof.
  intros e x u H.
  unfold free_rgn_vars_in_eps in H.
  unfold subst_eps.
  apply Extensionality_Ensembles; unfold Same_set, Included.
  split.
  - unfold In. intros x0. 
    intros [sa' [H1 H2]]. subst.
    rewrite subst_fresh_sa; auto.
    unfold not_set_elem, Complement, In, not in *.
    intros. apply H. exists sa'. 
    split; intuition.
    (*+ subst. inversion H1.*)
  - unfold In.   intros x0 H0.
    exists x0. intuition.
    rewrite subst_fresh_sa; auto.
    unfold not_set_elem, Complement, In, not in *.
    intros. apply H. exists x0. 
    split; intuition.
    (*+ subst. inversion H0.*)
Qed.

Lemma SUBST_FRESH : subst_fresh.
Proof.
  intros x. induction t; intros u H; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.  
  - f_equal; [apply IHt1 | apply IHt2]; 
    simpl in H; unfold not, not_set_elem, Complement in *;
    intro; apply H.
    + now apply Union_introl.
    + now apply Union_intror.
  - unfold not_set_elem, Complement in H.
    f_equal; [ | apply IHt].
    + apply subst_fresh_rgn.
      unfold not_set_elem, free_region, Complement.
      unfold not in *; intros. apply H. simpl. apply Union_introl. assumption.
    + unfold not_set_elem, free_region, Complement.
      unfold not in *; intros. apply H. simpl. apply Union_intror. assumption.
  - unfold not_set_elem, Complement in H.
    f_equal; [apply IHt1 | | apply IHt2 | | apply IHt3].
    + unfold not_set_elem, free_region, Complement.
      unfold not in *; intros. apply H. simpl. apply Union_introl. assumption.
    + rewrite subst_fresh_eps; auto.
      unfold not_set_elem, free_region, Complement.
      simpl in H. unfold not in *. intros.
      apply H.  apply Union_intror.  apply Union_introl. apply Union_introl. assumption.
    + unfold not_set_elem, free_region, Complement.
      simpl in H. unfold not in *. intros.
      apply H. apply Union_intror.  apply Union_intror. apply Union_introl. assumption.
    + rewrite subst_fresh_eps; auto.
      unfold not_set_elem, free_region, Complement.
      simpl in H. unfold not in *. intros.
      apply H.  apply Union_intror.  apply Union_introl. apply Union_intror. assumption.
    + unfold not_set_elem, free_region, Complement.
      simpl in H. unfold not in *. intros.
      apply H. apply Union_intror.  apply Union_intror. apply Union_intror. assumption.
  - f_equal; [ | apply IHt].
    + rewrite subst_fresh_eps; auto.
      unfold not_set_elem, free_region, Complement in *.
      simpl in H. unfold not in *. intros.
      apply H.  apply Union_introl. assumption.
    + simpl in H. unfold not_set_elem, free_region, Complement in *.
      unfold not in *. intros. apply H. apply Union_intror. assumption.
Qed. 

Lemma SUBST_INTRO : subst_intro.
Proof.
  intros x t u H1 H2. unfold open_var.
  replace (opening_rgn_exp 0 (Rgn2_FVar true true x) t) with (open  (Rgn2_FVar true true x) t) by (now unfold open).
  rewrite SUBST_OPEN; auto. f_equal.
  - simpl in *; destruct (AsciiVars.eq_dec x x); intros;
    [reflexivity | unfold AsciiVars.eq in n; contradict n; reflexivity ].
  - symmetry. apply SUBST_FRESH. assumption.
Qed .


