Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Omega.

Add LoadPath "." as Top0.
Require Import Top0.Tactics.
Require Import Top0.Keys.
Require Import Top0.Nameless.
Require Import Top0.Definitions.
Require Import Top0.Axioms.


Lemma subst_rho_natural :
  forall rho, subst_rho rho Ty2_Natural = Ty2_Natural.
Proof.
  unfold subst_rho. unfold R.fold. unfold R.Raw.fold.
  intro rho. destruct rho. simpl. induction this.
  - reflexivity.
  - inversion is_bst; subst.
    rewrite IHthis1 by assumption.
    replace (subst_in_type k e Ty2_Natural) with Ty2_Natural.
    rewrite IHthis2 by assumption.
    reflexivity.
    unfold subst_in_type, open_var, close_var.
    simpl. reflexivity.
Qed.

Lemma subst_rho_boolean :
  forall rho, subst_rho rho Ty2_Boolean = Ty2_Boolean.
Proof.
  unfold subst_rho. unfold R.fold. unfold R.Raw.fold.
  intro rho. destruct rho. simpl. induction this.
  - reflexivity.
  - inversion is_bst; subst.
    rewrite IHthis1 by assumption.
    replace (subst_in_type k e Ty2_Boolean) with Ty2_Boolean.
    rewrite IHthis2 by assumption.
    reflexivity.
    unfold subst_in_type, open_var, close_var.
    simpl. reflexivity.
Qed.

Lemma subst_rho_unit :
  forall rho, subst_rho rho Ty2_Unit = Ty2_Unit.
Proof.
  unfold subst_rho. unfold R.fold. unfold R.Raw.fold.
  intro rho. destruct rho. simpl. induction this.
  - reflexivity.
  - inversion is_bst; subst.
    rewrite IHthis1 by assumption.
    replace (subst_in_type k e  Ty2_Unit) with  Ty2_Unit.
    rewrite IHthis2 by assumption.
    reflexivity.
    unfold subst_in_type, open_var, close_var.
    simpl. reflexivity.
Qed.

Lemma subst_rho_effect :
  forall rho, subst_rho rho Ty2_Effect = Ty2_Effect.
Proof.
  unfold subst_rho. unfold R.fold. unfold R.Raw.fold.
  intro rho. destruct rho. simpl. induction this.
  - reflexivity.
  - inversion is_bst; subst.
    rewrite IHthis1 by assumption.
    replace (subst_in_type k e  Ty2_Effect) with  Ty2_Effect.
    rewrite IHthis2 by assumption.
    reflexivity.
    unfold subst_in_type, open_var, close_var.
    simpl. reflexivity.
Qed. 


Lemma subst_rho_rgn_const :
  forall rho c, fold_subst_rgn rho (Rgn2_Const true true c) = (Rgn2_Const true true c).
Proof.
  intros rho c.
  unfold  fold_subst_rgn. unfold R.fold. unfold R.Raw.fold.
  destruct rho. simpl. induction this.
  - reflexivity.
  - inversion is_bst; subst.
    rewrite IHthis1 by assumption.
    replace (subst_rgn k (Rgn2_Const true false e) (Rgn2_Const true true c)) with (Rgn2_Const true true c).
    rewrite IHthis2 by assumption.
    reflexivity.
    simpl. reflexivity.
Qed.

Lemma subst_rho_index :
  forall rho n, fold_subst_rgn rho (Rgn2_BVar true true n) = (Rgn2_BVar true true n).
Proof.
  intros rho n.
  unfold  fold_subst_rgn. unfold R.fold. unfold R.Raw.fold.
  destruct rho. simpl. induction this.
  - reflexivity.
  - inversion is_bst; subst.
    rewrite IHthis1 by assumption.
    replace (subst_rgn k (Rgn2_Const true false e) (Rgn2_BVar true true n)) with (Rgn2_BVar true true n).
    rewrite IHthis2 by assumption.
    reflexivity.
    simpl. reflexivity.
Qed.


Lemma fold_eps_leaf :
forall eff is_bst,
  eff = (fun sa : StaticAction2 =>
           exists sa' : StaticAction2, eff sa' /\
                                       fold_subst_sa {| R.this := R.Raw.Leaf Region; R.is_bst := is_bst |} sa' = sa).
Proof.
 intros eff is_bst.  
 apply Extensionality_Ensembles;
      unfold Same_set, Included; split; intros x H.
      * unfold In in *.
        exists x. intuition. unfold fold_subst_sa. destruct x; unfold fold_subst_rgn, subst_rgn; f_equal.
      * unfold In in *.  destruct H as [sa [? ?]].
        assert ( fold_subst_sa {| R.this := R.Raw.Leaf Region; R.is_bst := is_bst |} sa = sa)
          by (unfold fold_subst_sa, fold_subst_rgn, subst_rgn; simpl; destruct sa; subst; f_equal).
        rewrite H1 in H0. now subst.
Qed.

Lemma fold_eps_node :
  forall eff k t e this1 this2
         (Hl : R.Raw.bst this1)
         (Hr : R.Raw.bst this2)
         (is_bst : R.Raw.bst (R.Raw.Node this1 k e this2 t)),
    fold_subst_eps {| R.this := this2; R.is_bst := Hr |}
     (subst_eps k (Rgn2_Const true false e)
        (fold_subst_eps {| R.this := this1; R.is_bst := Hl |} eff)) =
   fold_subst_eps
     {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := is_bst |} eff.
Proof.
  intros eff k t e this1 this2 Hl Hr is_bst.
  apply Extensionality_Ensembles;
  unfold Same_set, Included; split; intros x H; unfold In in *.
  - unfold fold_subst_eps in *. 
    destruct H as [sa [[sa' [[sa'' [H1 H2]] H3]] H4]]. 
    exists sa''. intuition. subst.
    unfold fold_subst_sa, subst_sa; destruct sa''; f_equal.
  - unfold fold_subst_eps in *. 
    destruct H as [sa [H1 H2]]. 
    exists (subst_sa k (Rgn2_Const true false e) (fold_subst_sa {| R.this := this1; R.is_bst := Hl |} sa)).
    split.
    + unfold subst_eps.
      exists (fold_subst_sa {| R.this := this1; R.is_bst := Hl |} sa).
      intuition. exists sa. intuition.
    + destruct sa; rewrite <- H2; simpl; f_equal.
Qed.

Lemma subst_rho_pair : 
  forall rho t1 t2,
    subst_rho rho (Ty2_Pair t1 t2) = Ty2_Pair (subst_rho rho t1) (subst_rho rho t2).
Proof.
  unfold subst_rho.
  unfold R.fold. unfold R.Raw.fold.
  intro rho. destruct rho. simpl. induction this; intros t1 t2.
  - reflexivity.
  - assert (Hl: R.Raw.bst this1) by (inversion is_bst; auto).
    assert (Hr: R.Raw.bst this2) by (inversion is_bst; auto).
    rewrite IHthis1 by assumption. f_equal. 
    unfold subst_in_type; simpl.
    rewrite IHthis2 by assumption. f_equal. 
Qed.
 
Lemma subst_rho_arrow :
  forall rho tyr1 eff1 tyr2 eff2 tyr3,
    subst_rho rho (Ty2_Arrow tyr1 eff1 tyr2 eff2 tyr3) = Ty2_Arrow (subst_rho rho tyr1) (fold_subst_eps rho eff1) (subst_rho rho tyr2)
                                                                   (fold_subst_eps rho eff2) (subst_rho rho tyr3) .
Proof.
  unfold subst_rho.
  unfold R.fold. unfold R.Raw.fold.
  intro rho. destruct rho. simpl. induction this; intros tyr1 eff1 tyr2 eff2 tyr3.
  - f_equal; unfold fold_subst_eps; apply fold_eps_leaf.
  - assert (Hl: R.Raw.bst this1) by (inversion is_bst; auto).
    assert (Hr: R.Raw.bst this2) by (inversion is_bst; auto).
    rewrite IHthis1 with (is_bst:=Hl) by assumption. f_equal.  
    unfold subst_in_type; simpl.
    rewrite IHthis2 with (is_bst:=Hr) by assumption. f_equal.
    + apply fold_eps_node.
    + apply fold_eps_node.
Qed.  

Lemma subst_rho_tyref : forall rho r ty,subst_rho rho (Ty2_Ref r ty) =  Ty2_Ref (fold_subst_rgn rho r) (subst_rho rho ty).
Proof.
  unfold subst_rho, fold_subst_rgn. unfold R.fold. unfold R.Raw.fold.
  intro rho. destruct rho. simpl. induction this; intros r ty.
  - reflexivity.
  - inversion is_bst; subst.
    rewrite IHthis1 by assumption. 
    unfold subst_in_type, open_var, close_var; simpl.
    rewrite IHthis2 by assumption.
    unfold subst_in_type, open_var, close_var. simpl.
    reflexivity.
Qed.



Lemma subst_rho_forallrgn  :
  forall rho eff rty, 
    subst_rho rho (Ty2_ForallRgn eff rty) = Ty2_ForallRgn (fold_subst_eps rho eff) (subst_rho rho rty).
Proof.
  unfold subst_rho, fold_subst_eps. unfold R.fold. unfold R.Raw.fold.
  intro rho. destruct rho. simpl. induction this; intros eff rty.
  - f_equal; unfold fold_subst_eps; apply fold_eps_leaf.
  - assert (Hl: R.Raw.bst this1) by (inversion is_bst; auto).
    assert (Hr: R.Raw.bst this2) by (inversion is_bst; auto).
    rewrite IHthis1 with (is_bst:=Hl) by assumption. f_equal.  
    unfold subst_in_type; simpl.
    rewrite IHthis2 with (is_bst:=Hr) by assumption. f_equal.
    apply fold_eps_node.
Qed.

Lemma subst_rho_fvar_1:
  forall rho x,
    (exists v, fold_subst_rgn rho (Rgn2_FVar true true x) = Rgn2_Const true true v) \/ 
    fold_subst_rgn rho (Rgn2_FVar true true x) = Rgn2_FVar true true x.
Proof.
  intro rho. destruct rho. induction this; intros x.
  - unfold fold_subst_rgn, R.fold, R.Raw.fold; simpl. right. reflexivity.
  - assert (Hl: R.Raw.bst this1) by (inversion is_bst; auto).
    assert (Hr: R.Raw.bst this2) by (inversion is_bst; auto).  
    replace (fold_subst_rgn {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := is_bst |} (Rgn2_FVar true true x))
    with
    (fold_subst_rgn {| R.this := this2; R.is_bst := Hr |}
                    (subst_rgn k (Rgn2_Const true false e)
                               (fold_subst_rgn {| R.this := this1; R.is_bst := Hl |} (Rgn2_FVar true true x)))
    ) by (unfold fold_subst_rgn, R.fold, R.Raw.fold in *; reflexivity).
    destruct (IHthis1 Hl x).
    + destruct H as [v ?].
      left. exists v.
      rewrite H.  
      replace (subst_rgn k (Rgn2_Const true false e) (Rgn2_Const true true v)) with (Rgn2_Const true true v) by (simpl; reflexivity).
      apply subst_rho_rgn_const.
    + rewrite H.
      unfold subst_rgn.
      destruct (RMapP.eq_dec k x); subst; simpl.
      * left. exists e.
        apply subst_rho_rgn_const.
      * apply IHthis2.
Qed.

Lemma subst_rho_fvar_2:
  forall rho x v,
   find_R (Rgn2_FVar true false x) rho = Some v ->
   fold_subst_rgn rho (Rgn2_FVar true true x) = Rgn2_Const true true v.
Proof.
  intro rho.
  destruct rho. 
  induction this; intros x v H.
  - unfold fold_subst_rgn, R.fold, R.Raw.fold; simpl.
    inversion H.
  - assert (Hl: R.Raw.bst this1) by (inversion is_bst; auto).
    assert (Hr: R.Raw.bst this2) by (inversion is_bst; auto).
    replace (fold_subst_rgn {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := is_bst |} (Rgn2_FVar true true x))
    with
    (fold_subst_rgn {| R.this := this2; R.is_bst := Hr |}
                    (subst_rgn k (Rgn2_Const true false e)
                               (fold_subst_rgn {| R.this := this1; R.is_bst := Hl |} (Rgn2_FVar true true x)))
    ) by (unfold fold_subst_rgn, R.fold, R.Raw.fold in *; reflexivity).
    apply  RMapP.find_mapsto_iff in H.    
    inversion H; subst. 
    + (* x = k *)
      destruct (AsciiVars.compare k k); try (solve [unfold AsciiVars.lt in l; omega]).
      replace (fold_subst_rgn {| R.this := this2; R.is_bst := Hr |} 
                              (subst_rgn k (Rgn2_Const true false e)
                              (fold_subst_rgn {| R.this := this1; R.is_bst := Hl |} (Rgn2_FVar true true k))))
      with (fold_subst_rgn {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := is_bst |} 
                           (Rgn2_FVar true true k)) by
          (unfold fold_subst_rgn, R.fold, R.Raw.fold in *; reflexivity).  
      eapply R.Raw.Proofs.find_1 in H; auto.
      apply fold_subst_rgn_eq_1; auto.
    + apply R.Raw.Proofs.find_1 in H1; auto.
      apply IHthis1 with (is_bst := Hl) in H1. rewrite H1. simpl.
      rewrite subst_rho_rgn_const. reflexivity.
    + apply R.Raw.Proofs.find_1 in H1; auto.
      assert (R.Raw.In x this2) by (apply R.Raw.Proofs.find_iff in H1; 
                                    [ eapply R.Raw.Proofs.MapsTo_In; eassumption | assumption]).
      apply IHthis2 with (is_bst := Hr) in H1.
      erewrite fold_subst_rgn_left_1; eauto; simpl.
      assert (AsciiVars.lt k x) by (eapply fold_subst_rgn_left_2; eauto).
      apply AsciiVars.lt_not_eq in H2.
      destruct (RMapP.eq_dec k x); subst; [contradict H0; auto | assumption].
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
    included (set_union (free_rgn_vars_in_rgn2 r0) (frv t)) rgns ->
    ~ free_rgn_vars_in_rgn2 (fold_subst_rgn rho r0) x.
Proof.
  intros rho rgns r0 t x HRho HInc H.
  generalize dependent r0.
  unfold rgn2_in_typ.
  dependent induction r0; intros.
  - rewrite subst_rho_rgn_const in H.
    simpl in H. contradiction.
  - destruct (AsciiVars.eq_dec x n) as [c | c].
    + inversion c; subst.   
      inversion HRho; subst.   
      contradict H.
      destruct (subst_rho_fvar_1 rho n) as [[v H0] | H0]. 
      * rewrite H0. simpl. intro. contradiction.
      * rewrite H0. simpl. intro. 
        unfold set_elem, In in H1.
        destruct H1 with (r:=n). 
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
     destruct (subst_rho_fvar_1 rho n) as [[v H0] | H0].
     * rewrite H0. simpl. intro. contradiction.
     * rewrite H0. simpl. intro. inversion H. auto.
  - rewrite subst_rho_index in H.
    simpl in H. contradiction. 
Qed.

Lemma no_free_vars_subst_sa_const:
  forall x e0 sa,
    free_rgn_vars_in_sa2 (subst_sa x (Rgn2_Const true false e0) sa) x -> 
    empty_set x.
Proof.
  intros.
  induction sa; contradict H; 
  unfold free_rgn_vars_in_sa2, subst_sa;
  unfold free_rgn_vars_in_rgn2, subst_rgn;
  unfold rgn2_in_typ in r;
  dependent induction r; try (solve [intro; contradiction]).
  + destruct (RMapProp.F.eq_dec x n); subst.
    * simpl. intro. contradiction.
    * intro. inversion H. unfold not in n0. apply n0. auto.
  + destruct (RMapProp.F.eq_dec x n); subst.
    * simpl. intro. contradiction.
    * intro. inversion H. unfold not in n0. apply n0. auto.
  + destruct (RMapProp.F.eq_dec x n); subst.
    * simpl. intro. contradiction.
    * intro. inversion H. unfold not in n0. apply n0. auto.
Qed.

Lemma free_vars_subst_sa_diff:
  forall x k e0 sa,
    k <> x ->
    free_rgn_vars_in_sa2 (subst_sa k (Rgn2_Const true false e0) sa) x -> 
    empty_set x \/ exists n, singleton_set n x.
Proof.
  intros. 
  induction sa. 
  - unfold free_rgn_vars_in_sa2, subst_sa in H0.
    unfold free_rgn_vars_in_rgn2, subst_rgn in H0.
    unfold rgn2_in_typ in r.
    dependent induction r.
    + left. assumption. 
    + destruct (RMapProp.F.eq_dec k n); subst.
      * simpl in H0. left. assumption.
      * right. exists n. assumption.
    + left. assumption.
  - unfold free_rgn_vars_in_sa2, subst_sa in H0.
    unfold free_rgn_vars_in_rgn2, subst_rgn in H0.
    unfold rgn2_in_typ in r.
    dependent induction r.
    + left. assumption. 
    + destruct (RMapProp.F.eq_dec k n); subst.
      * simpl in H0. left. assumption.
      * right. exists n. assumption.
    + left. assumption.
  - unfold free_rgn_vars_in_sa2, subst_sa in H0.
    unfold free_rgn_vars_in_rgn2, subst_rgn in H0.
    unfold rgn2_in_typ in r.
    dependent induction r.
    + contradiction.
    + destruct (RMapProp.F.eq_dec k n); subst.
      * simpl in H0. contradiction.
      * right. exists n. assumption.
    + contradiction.
Qed.

Lemma free_vars_subst_sa:
  forall k x e0 sa,
    free_rgn_vars_in_sa2 (subst_sa k (Rgn2_Const true false e0) sa) x ->
    empty_set x \/ (exists n, singleton_set n x).
Proof.
  intros.
  destruct (AsciiVars.eq_dec k x) as [c | c].
  - inversion c; subst.
    left; eapply no_free_vars_subst_sa_const; eauto.
  - unfold AsciiVars.eq in c. 
    eapply free_vars_subst_sa_diff in c; eauto.
Qed.

Lemma TcRhoIncludedNoFreeVarsEps_aux_0:
  forall rho e x,
    free_rgn_vars_in_eps2 (fold_subst_eps rho e) x ->
    free_rgn_vars_in_eps2 e x.
Admitted.

Lemma TcRhoIncludedNoFreeVarEps_Problem:
  forall x e0 e x0,
     free_rgn_vars_in_eps2 (subst_eps x (Rgn2_Const true false e0) e) x0 ->
     free_rgn_vars_in_eps2 e x0.
Proof.
  intros x e0 e x0 H.
  unfold free_rgn_vars_in_eps2 in *.
  destruct H. destruct H.
  exists x1.
  split.
  - intuition. subst.
    apply H.
    apply Extensionality_Ensembles; unfold Same_set, Included.
    split; intro; intro; unfold In in *; repeat destruct H1.
  - intro. apply H0.
    unfold subst_eps.
    exists x1. split; [assumption |]. 
    unfold subst_sa. 
    induction x1; 
    unfold rgn2_in_typ in r;
    dependent induction r; simpl; try ( solve [reflexivity]).
    + destruct (RMapProp.F.eq_dec x n); subst.
      * (* SA2_Alloc (Rgn2_Const true true rc) = SA2_Alloc (Rgn2_FVar true true n) *)
        admit.
      * reflexivity.
    + admit.
    + admit.
Admitted.

Lemma TcRhoIncludedNoFreeVarsEps_aux_2:
forall k rc x e,
    ~ (free_rgn_vars_in_eps2 e) x ->
    ~ (free_rgn_vars_in_eps2 (subst_eps k (Rgn2_Const _ _ rc) e)) x.
Proof.
  intros.
  intro. unfold not in H. apply H.
  eapply TcRhoIncludedNoFreeVarEps_Problem; eauto.
Admitted.

Lemma TcRhoIncludedNoFreeVarsEps_aux_2_1:
  forall k rc e,
    included
      (free_rgn_vars_in_eps2 (subst_eps k (Rgn2_Const _ _ rc) e))
      (free_rgn_vars_in_eps2 e).
Proof.
  intros k rc e.
  unfold included, Included, In.
  intro. intro. 
  eapply TcRhoIncludedNoFreeVarEps_Problem; eauto.
Admitted.

Lemma TcRhoIncludedNoFreeVarsEps_aux_AlsoProblem:
  forall x e0 e,
    ~ free_rgn_vars_in_eps2 (subst_in_eff x e0 e) x.
Proof.
  intros.
  unfold subst_in_eff. intro.
  apply TcRhoIncludedNoFreeVarsEps_aux_2_1 in H.
  contradict H.
  unfold In.
  (* no enough assumptions *)
Admitted.
        
Lemma TcRhoIncludedNoFreeVarsEps_aux_1_1:
  forall x e0 e,
    included
      (free_rgn_vars_in_eps2 (subst_in_eff x e0 e))
      (free_rgn_vars_in_eps2 e).
Proof.
  intros.
  unfold included, Included, In in *.
  intro. intro. unfold subst_in_eff in H.
  eapply TcRhoIncludedNoFreeVarEps_Problem; eauto.
Admitted.

Lemma TcRhoIncludedNoFreeVarsEps_aux_3:
  forall rho x,
    R.find x rho <> None ->
    forall e,
      ~ (free_rgn_vars_in_eps2 (fold_subst_eps rho e)) x.
Proof.
  intros.
  destruct rho. induction this.
  - unfold fold_subst_eps.  
    replace (fun sa : StaticAction2 =>
               exists sa' : StaticAction2,
                 e sa' /\
                 fold_subst_sa {| R.this := R.Raw.Leaf nat; R.is_bst := is_bst |} sa' =
                 sa)
    with e by (rewrite <- fold_eps_leaf with (is_bst := is_bst); reflexivity).
    intro. unfold R.find, R.Raw.find in H. simpl in H. contradict H. reflexivity.
  - inversion is_bst; subst.
    replace (fold_subst_eps
               {| R.this := R.Raw.Node this1 k e0 this2 t; R.is_bst := is_bst |} e)
    with (fold_subst_eps {| R.this := this2; R.is_bst := H6 |}
                         (subst_eps k (Rgn2_Const true false e0)
                                    (fold_subst_eps {| R.this := this1; R.is_bst := H4 |} e)))
    by (rewrite <- fold_eps_node with (Hr:=H6) (Hl:=H4); reflexivity).
    intro.
    apply frv_in_subst_eps in H0.
    destruct H0 as [Hl | [Hc | Hr]]. 
    + contradict Hl.
      eapply IHthis2; eauto. 
      assert (R.find (elt:=Region) x
                 {| R.this := R.Raw.Node this1 k e0 this2 t; R.is_bst := is_bst |} <> None -> 
              R.find (elt:=Region) x {| R.this := this2; R.is_bst := H6 |} <> None) 
        by admit.
      auto.
    + contradict Hc.
      eapply TcRhoIncludedNoFreeVarsEps_aux_AlsoProblem; eauto.
    + contradict Hr.
      eapply IHthis1; eauto. 
      assert (R.find (elt:=Region) x
                 {| R.this := R.Raw.Node this1 k e0 this2 t; R.is_bst := is_bst |} <> None -> 
              R.find (elt:=Region) x {| R.this := this1; R.is_bst := H4 |} <> None) 
        by admit.
      auto.
Admitted.    

Lemma TcRhoIncludedNoFreeVarsEps:
  forall rho rgns e x,
    TcRho (rho, rgns) ->
    free_rgn_vars_in_eps2 e x ->
    included (free_rgn_vars_in_eps2 e) rgns ->
    ~ (free_rgn_vars_in_eps2 (fold_subst_eps rho e)) x.
Proof.
  intros.
  apply TcRhoIncludedNoFreeVarsEps_aux_3.
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
          - eapply TcRhoIncludedNoFreeVarsEps  with (e:=e); eauto.
            + unfold In in H0. eapply TcRhoIncludedNoFreeVarsEps_aux_0; eauto. 
            + unfold included, Included, Ensembles.In in *.
              intro. intro.
              apply HInc.
              apply Ensembles.Union_intror. apply Ensembles.Union_introl.
              apply Ensembles.Union_introl. assumption.
          - eapply TcRhoIncludedNoFreeVarsEps with (e:=e0); eauto.
            + unfold In in H0. eapply TcRhoIncludedNoFreeVarsEps_aux_0; eauto. 
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
    + eapply TcRhoIncludedNoFreeVarsEps with (e:=e); eauto. 
      * eapply TcRhoIncludedNoFreeVarsEps_aux_0; eauto. 
      * unfold included, Included, In in *. intro. intro.
        apply HInc.
        apply Union_introl. assumption.
    + apply IHt; auto. 
      unfold included, Included in *. 
      intros. apply HInc. 
      apply Union_intror. assumption.
Qed.