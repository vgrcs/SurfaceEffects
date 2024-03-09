Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Lia.
Require Import Definitions.Keys.
Require Import Definitions.Regions.
Require Import Definitions.GTypes.
Require Import Definitions.ComputedActions.
Require Import Definitions.StaticActions.
Require Import Coq.FSets.FMapFacts.

Lemma R_diff_key_1:
  forall t a b v v' e,   
    a <> b ->
    R.find (elt := t) a (R.add b v e) = Some v' -> 
    R.find (elt := t) a e = Some v'.
Proof.
  intros. 
  rewrite <- RMapP.find_mapsto_iff in H0. rewrite -> RMapP.add_mapsto_iff in H0.
  destruct H0; destruct H0; [destruct H | rewrite -> RMapP.find_mapsto_iff in H1]; auto.
Qed.

Lemma R_diff_key_2:
  forall t a b v v' e,   
    b <> a ->
    R.find (elt := t) a e = Some v' ->
    R.find (elt := t) a (R.add b v e) = Some v'.
Proof.
  intros. 
  rewrite <- RMapP.find_mapsto_iff. rewrite -> RMapP.add_mapsto_iff.
  right; split; [exact H | now rewrite RMapP.find_mapsto_iff ].
Qed.


Lemma R_diff_key_3:
  forall t a b v e,   
    a <> b ->
    R.find (elt := t) a (R.add b v e) <> None -> 
    R.find (elt := t) a e <> None.
Proof.
  intros. 
  rewrite <- RMapP.in_find_iff in H0. rewrite -> RMapP.add_in_iff in H0.
  intuition. apply RMapP.in_find_iff in H2. contradiction.
Qed.


Lemma find_rho_3:
  forall x this1 this2 k e t He,
    R.find (elt:=nat) x {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := He |} = None ->
    ~ R.find (elt:=nat) x {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := He |} 
    = Some e.
Proof.
 intros.
 apply RMapP.not_find_in_iff in H.
 contradict H.
 apply RMapP.in_find_iff.
 rewrite H. intro H1. inversion H1.
Qed.

Lemma not_in_raw_rho:
  forall x this1 this2 k e  t0 He Hl Hr, 
    ~ R.In (elt:=nat) x {| R.this := R.Raw.Node this1 k e this2 t0; R.is_bst := He |} ->
    ~ R.In (elt:=nat) x {| R.this := this1 ; R.is_bst := Hl |}  /\ 
    ~ R.In (elt:=nat) x {| R.this := this2; R.is_bst := Hr |} /\
    x <> k /\
    ~ R.find (elt:=nat) x {| R.this := R.Raw.Node this1 k e this2 t0; R.is_bst := He |} = Some e.
Proof.
  intros; repeat split; 
  try (intro; apply H; apply RMapP.in_find_iff in H0; apply RMapP.in_find_iff; 
                               contradict H0). 
  - apply RMapP.not_find_in_iff in H0.
    apply RMapP.not_find_in_iff. intro. 
    apply H0. unfold R.In in H1. 
    unfold R.Raw.In0 in H1.
    destruct H1.
    unfold R.In, R.Raw.In0. exists x0.
    apply  R.Raw.MapsLeft. simpl in H1. 
    assumption.
  - apply RMapP.not_find_in_iff in H0. 
    apply RMapP.not_find_in_iff. intro. 
    apply H0. unfold R.In in H1. 
    unfold R.Raw.In0 in H1.
    destruct H1.
    unfold R.In, R.Raw.In0. exists x0. simpl. simpl in H1.
    apply  R.Raw.MapsRight. assumption.
  - contradict H. rewrite H. clear H. unfold R.In.  
    econstructor. simpl. econstructor. reflexivity.
  - apply find_rho_3.
    apply RMapP.not_find_in_iff.
    assumption.
Qed.

Lemma find_rho_1:
  forall x this1 this2 k e t He Hl,
    R.find (elt:=nat) x {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := He |} = None ->
    R.find (elt:=nat) x {| R.this := this1; R.is_bst := Hl |} = None.
Proof.
  intros.
  inversion He; subst.
  apply RMapP.not_find_in_iff in H.
  eapply not_in_raw_rho with (Hr:=H6) (Hl:=Hl) in H; auto.
  destruct H as [HNotIn1 [HNotIn2 [HNotIn3  HNotIn4]]]. 
  apply RMapP.not_find_in_iff.
  assumption.
Qed.

Lemma find_rho_2:
  forall x this1 this2 k e t He Hr,
    R.find (elt:=nat) x {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := He |} = None ->
    R.find (elt:=nat) x {| R.this := this2; R.is_bst := Hr |} = None.
Proof.
  intros.
  inversion He; subst.
  apply RMapP.not_find_in_iff in H.
  eapply not_in_raw_rho with (Hr:=Hr) (Hl:=H4) in H; auto.
  destruct H as [HNotIn1 [HNotIn2 [HNotIn3  HNotIn4]]]. 
  apply RMapP.not_find_in_iff.
  assumption.
Qed.

Lemma decompose_find_in_rho:
  forall x this1 this2 k e v t He Hl Hr, 
    R.find (elt:=RgnId) x {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := He |} = Some v ->
    R.find (elt:=RgnId) x {| R.this := this1; R.is_bst := Hl |} = Some v \/
    R.find (elt:=RgnId) x {| R.this := this2; R.is_bst := Hr |} = Some v \/
    e = v.
Proof.
  intros.
  apply RMapP.find_mapsto_iff  in H.
  inversion H; subst.
  - right. right. reflexivity.
  - left. apply RMapP.find_mapsto_iff. auto.
  - right. left.  apply RMapP.find_mapsto_iff. auto.
Qed. 

Lemma subst_rho_natural :
  forall rho, subst_rho rho Ty_Natural = Ty_Natural.
Proof.
  unfold subst_rho. unfold R.fold. unfold R.Raw.fold.
  intro rho. destruct rho. simpl. induction this.
  - reflexivity.
  - inversion is_bst; subst.
    rewrite IHthis1 by assumption.
    replace (subst_in_type k e Ty_Natural) with Ty_Natural. 
    rewrite IHthis2 by assumption.
    reflexivity.
    unfold subst_in_type, open_var, close_var.
    simpl. reflexivity.
Qed.

Lemma subst_rho_boolean :
  forall rho, subst_rho rho Ty_Boolean = Ty_Boolean.
Proof.
  unfold subst_rho. unfold R.fold. unfold R.Raw.fold.
  intro rho. destruct rho. simpl. induction this.
  - reflexivity.
  - inversion is_bst; subst.
    rewrite IHthis1 by assumption.
    replace (subst_in_type k e Ty_Boolean) with Ty_Boolean.
    rewrite IHthis2 by assumption.
    reflexivity.
    unfold subst_in_type, open_var, close_var.
    simpl. reflexivity.
Qed.

Lemma subst_rho_unit :
  forall rho, subst_rho rho Ty_Unit = Ty_Unit.
Proof.
  unfold subst_rho. unfold R.fold. unfold R.Raw.fold.
  intro rho. destruct rho. simpl. induction this.
  - reflexivity.
  - inversion is_bst; subst.
    rewrite IHthis1 by assumption.
    replace (subst_in_type k e  Ty_Unit) with  Ty_Unit.
    rewrite IHthis2 by assumption.
    reflexivity.
    unfold subst_in_type, open_var, close_var.
    simpl. reflexivity.
Qed.

Lemma subst_rho_effect :
  forall rho, subst_rho rho Ty_Effect = Ty_Effect.
Proof.
  unfold subst_rho. unfold R.fold. unfold R.Raw.fold.
  intro rho. destruct rho. simpl. induction this.
  - reflexivity.
  - inversion is_bst; subst.
    rewrite IHthis1 by assumption.
    replace (subst_in_type k e  Ty_Effect) with  Ty_Effect.
    rewrite IHthis2 by assumption.
    reflexivity.
    unfold subst_in_type, open_var, close_var.
    simpl. reflexivity.
Qed. 

Lemma fold_subst_rho_free_vars_rgn_aux:
  forall rho x,
    R.find (elt:=nat) x rho = None ->
    fold_subst_rgn rho (Rgn_FVar true true x) =  (Rgn_FVar true true x).
Proof.
  intros rho. destruct rho. induction this; intros x H.
  - unfold R.find, R.Raw.find in H. simpl in H.
    unfold fold_subst_rgn, subst_rgn, R.fold, R.Raw.fold. simpl. 
    reflexivity.
  - inversion is_bst; subst.
    apply RMapP.not_find_in_iff in H. 
    eapply not_in_raw_rho in H; eauto.
    destruct H as [HNotIn1 [HNotIn2 [HNotIn3  HNotIn4]]].
    replace (fold_subst_rgn {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := is_bst |} 
                            (Rgn_FVar true true x))
    with
    (fold_subst_rgn {| R.this := this2; R.is_bst := H6 |}
                    (subst_rgn k (Rgn_Const true false e)
                               (fold_subst_rgn {| R.this := this1; R.is_bst := H4 |} (Rgn_FVar true true x)))
    ) by (unfold fold_subst_rgn, R.fold, R.Raw.fold in *; reflexivity).
    apply RMapP.not_find_in_iff in HNotIn1.
    assert (fold_subst_rgn {| R.this := this1; R.is_bst := H4 |}
                           (Rgn_FVar true true x) = Rgn_FVar true true x).
    eapply IHthis1; eauto. rewrite H.
    apply RMapP.not_find_in_iff in HNotIn2.
    assert (fold_subst_rgn {| R.this := this2; R.is_bst := H6 |}
                           (Rgn_FVar true true x) = Rgn_FVar true true x).
    eapply IHthis2; eauto.
    unfold subst_rgn. simpl.
    destruct (AsciiVars.eq_dec k x) as [c | c]; auto.
    inversion c; subst.
    contradiction.
Qed.

Lemma subst_rho_rgn_const :
  forall rho c, fold_subst_rgn rho (Rgn_Const true true c) = (Rgn_Const true true c).
Proof.
  intros rho c.
  unfold  fold_subst_rgn. unfold R.fold. unfold R.Raw.fold.
  destruct rho. simpl. induction this.
  - reflexivity.
  - inversion is_bst; subst.
    rewrite IHthis1 by assumption.
    replace (subst_rgn k (Rgn_Const true false e) (Rgn_Const true true c))
      with (Rgn_Const true true c).
    rewrite IHthis2 by assumption.
    reflexivity.
    simpl. reflexivity.
Qed.

Lemma subst_rho_index :
  forall rho n, fold_subst_rgn rho (Rgn_BVar true true n) = (Rgn_BVar true true n).
Proof.
  intros rho n.
  unfold  fold_subst_rgn. unfold R.fold. unfold R.Raw.fold.
  destruct rho. simpl. induction this.
  - reflexivity.
  - inversion is_bst; subst.
    rewrite IHthis1 by assumption.
    replace (subst_rgn k (Rgn_Const true false e) (Rgn_BVar true true n))
      with (Rgn_BVar true true n).
    rewrite IHthis2 by assumption.
    reflexivity.
    simpl. reflexivity.
Qed.

Lemma fold_eps_node :
  forall eff k t e this1 this2
         (Hl : R.Raw.bst this1)
         (Hr : R.Raw.bst this2)
         (is_bst : R.Raw.bst (R.Raw.Node this1 k e this2 t)),
    fold_subst_eps {| R.this := this2; R.is_bst := Hr |}
     (subst_eps k (Rgn_Const true false e)
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
    exists (subst_sa k (Rgn_Const true false e) (fold_subst_sa {| R.this := this1; R.is_bst := Hl |} sa)).
    split.
    + unfold subst_eps.
      exists (fold_subst_sa {| R.this := this1; R.is_bst := Hl |} sa).
      intuition. exists sa. intuition.
    + destruct sa; rewrite <- H2; simpl; f_equal.
Qed.

Lemma subst_rho_pair : 
  forall rho t1 t2,
    subst_rho rho (Ty_Pair t1 t2) = Ty_Pair (subst_rho rho t1) (subst_rho rho t2).
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



Lemma fold_eps_leaf :
forall eff is_bst,
  eff = (fun sa : StaticAction =>
           exists sa' : StaticAction, eff sa' /\
                                        fold_subst_sa {| R.this := R.Raw.Leaf RgnId; R.is_bst := is_bst |} sa' = sa).
Proof.
 intros eff is_bst.  
 apply Extensionality_Ensembles;
      unfold Same_set, Included; split; intros x H.
      * unfold In in *.
        exists x. intuition. unfold fold_subst_sa. destruct x; unfold fold_subst_rgn, subst_rgn; f_equal.
      * unfold In in *.  destruct H as [sa [? ?]].
        assert ( fold_subst_sa {| R.this := R.Raw.Leaf RgnId; R.is_bst := is_bst |} sa = sa)
          by (unfold fold_subst_sa, fold_subst_rgn, subst_rgn; simpl; destruct sa; subst; f_equal).
        rewrite H1 in H0. now subst.
Qed.


Lemma subst_rho_arrow :
  forall rho tyr1 eff1 tyr2 eff2 tyr3,
    subst_rho rho (Ty_Arrow tyr1 eff1 tyr2 eff2 tyr3) =
      Ty_Arrow (subst_rho rho tyr1) (fold_subst_eps rho eff1)
        (subst_rho rho tyr2) (fold_subst_eps rho eff2) (subst_rho rho tyr3) .
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

Lemma subst_rho_tyref :
  forall rho r ty,
    subst_rho rho (Ty_Ref r ty) = Ty_Ref (fold_subst_rgn rho r) (subst_rho rho ty).
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
    subst_rho rho (Ty_ForallRgn eff rty) =
      Ty_ForallRgn (fold_subst_eps rho eff) (subst_rho rho rty).
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
    (exists v, fold_subst_rgn rho (Rgn_FVar true true x) = Rgn_Const true true v) \/ 
    fold_subst_rgn rho (Rgn_FVar true true x) = Rgn_FVar true true x.
Proof.
  intro rho. destruct rho. induction this; intros x.
  - unfold fold_subst_rgn, R.fold, R.Raw.fold; simpl. right. reflexivity.
  - assert (Hl: R.Raw.bst this1) by (inversion is_bst; auto).
    assert (Hr: R.Raw.bst this2) by (inversion is_bst; auto).  
    replace (fold_subst_rgn {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := is_bst |} (Rgn_FVar true true x))
    with
    (fold_subst_rgn {| R.this := this2; R.is_bst := Hr |}
                    (subst_rgn k (Rgn_Const true false e)
                               (fold_subst_rgn {| R.this := this1; R.is_bst := Hl |} (Rgn_FVar true true x)))
    ) by (unfold fold_subst_rgn, R.fold, R.Raw.fold in *; reflexivity).
    destruct (IHthis1 Hl x).
    + destruct H as [v ?].
      left. exists v.
      rewrite H.  
      replace (subst_rgn k (Rgn_Const true false e) (Rgn_Const true true v))
        with (Rgn_Const true true v) by (simpl; reflexivity).
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
   find_R (Rgn_FVar true false x) rho = Some v ->
   fold_subst_rgn rho (Rgn_FVar true true x) = Rgn_Const true true v.
Proof.
  intro rho.
  destruct rho. 
  induction this; intros x v H.
  - unfold fold_subst_rgn, R.fold, R.Raw.fold; simpl.
    inversion H.
  - assert (Hl: R.Raw.bst this1) by (inversion is_bst; auto).
    assert (Hr: R.Raw.bst this2) by (inversion is_bst; auto). 
    replace (fold_subst_rgn {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := is_bst |} 
                            (Rgn_FVar true true x))
    with
    (fold_subst_rgn {| R.this := this2; R.is_bst := Hr |}
                    (subst_rgn k (Rgn_Const true false e)
                               (fold_subst_rgn {| R.this := this1; R.is_bst := Hl |} (Rgn_FVar true true x)))
    ) by (unfold fold_subst_rgn, R.fold, R.Raw.fold in *; reflexivity). 
    simpl in H. 
    eapply decompose_find_in_rho in H; eauto.
    destruct H as [HA | [HB | HC]].  
    + assert (H' : fold_subst_rgn {| R.this := this1; R.is_bst := Hl |}
                                 (Rgn_FVar true true x) = Rgn_Const true true v)
       by (apply IHthis1; simpl; assumption).    
      rewrite H'. simpl. rewrite subst_rho_rgn_const. reflexivity.
    + assert (H'' : fold_subst_rgn {| R.this := this2; R.is_bst := Hr |}
                                 (Rgn_FVar true true x) = Rgn_Const true true v)
          by (apply IHthis2; simpl; assumption).
      rewrite<- H''. unfold subst_rgn. simpl.
      admit.
    + subst.
      replace (subst_rgn k (Rgn_Const true false v)
                 (fold_subst_rgn {| R.this := this1; R.is_bst := Hl |}
                    (Rgn_FVar true true x))) with (Rgn_Const true true v).
      admit.
Admitted.

Lemma subst_rho_free_vars_rgn:
 forall rho x r,
   R.find (elt:=RgnId) x rho = None ->
   not_set_elem (free_rgn_vars_in_rgn (fold_subst_rgn rho r)) x ->
   not_set_elem (free_rgn_vars_in_rgn r) x.
Proof.
  intros rho x r HFind HNotElem.
  unfold Region_in_Type in r. dependent induction r. 
  - rewrite subst_rho_rgn_const in HNotElem. assumption.
  - assert ((exists v', fold_subst_rgn rho (Rgn_FVar true true v) =  
                         Rgn_Const true true v') \/ 
            fold_subst_rgn rho (Rgn_FVar true true v) = Rgn_FVar true true v) 
      by (apply subst_rho_fvar_1).
    destruct (subst_rho_fvar_1 rho v) as [[v' H0] | H0]; simpl in *.
    + destruct (AsciiVars.eq_dec v x) as [c | c]; auto.
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
  - assert ((exists v', fold_subst_rgn rho (Rgn_FVar true true v)
                        = Rgn_Const true true v') \/ 
            fold_subst_rgn rho (Rgn_FVar true true v) = Rgn_FVar true true v) 
      by (apply subst_rho_fvar_1).
    destruct H0. 
    + destruct H0. rewrite H0 in H. 
      unfold free_rgn_vars_in_rgn in H. inversion H.
    + rewrite H0 in H.
      assumption.
  - rewrite subst_rho_index in H. assumption.
Qed.


Lemma TcRhoIncludedNoFreeVarsSa_aux_fold:
  forall rho sa x,
    free_rgn_vars_in_sa (fold_subst_sa rho sa) x ->
    free_rgn_vars_in_sa sa x.
Proof.
  intros. 
  induction sa; unfold free_rgn_vars_in_sa, fold_subst_sa in *;
  eapply TcRhoIncludedNoFreeVarsRgn_aux_fold; eauto. 
Qed.
 
Lemma TcRhoIncludedNoFreeVarsEps_aux_fold:
  forall rho e x,
    free_rgn_vars_in_eps (fold_subst_eps rho e) x ->
    free_rgn_vars_in_eps e x.
Proof.
  intros. unfold  free_rgn_vars_in_eps, fold_subst_eps in *.
  destruct H as [sa [[sa' [H1 H2]] H3]].
  exists sa'. intuition.
  rewrite <- H2 in H3.
  eapply TcRhoIncludedNoFreeVarsSa_aux_fold; eauto.
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
  - destruct (RMapProp.F.eq_dec k v); subst; simpl in *.
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
               destruct (RMapProp.F.eq_dec x v); subst; 
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


Module RProofs := R.Raw.Proofs.
Lemma FindIfLowerThan:
  forall x this1 this2 k e t is_bst H,
    R.find (elt:=RgnId) x
        {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := is_bst |} <> None ->
    AsciiVars.lt x k ->
    R.find (elt:=RgnId) x {| R.this := this1; R.is_bst := H |} <> None.
Proof.
  intros x this1 this2 k e t is_bst H H1 H2.
  inversion is_bst; subst.
  apply RProofs.find_in in H1.  
  inversion H1; subst. 
  - unfold AsciiVars.lt in H2; lia.
  - apply RProofs.in_find.
    + inversion is_bst; subst.
      assumption.
    + assumption.
  - apply RProofs.in_find.
    + assumption.
    + eapply RProofs.gt_tree_trans in H2; eauto.
      assert (~ R.Raw.In x this2) by (apply RProofs.gt_tree_not_in in H2; auto).
      contradiction.
Qed.    

Lemma FindIfGreaterThan:
  forall x this1 this2 k e t is_bst H,
    R.find (elt:=RgnId) x
        {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := is_bst |} <> None ->
    AsciiVars.lt k x ->
    R.find (elt:=RgnId) x {| R.this := this2; R.is_bst := H |} <> None.
Proof.
  intros x this1 this2 k e t is_bst H H1 H2.
  inversion is_bst; subst.
  apply RProofs.find_in in H1.  
  inversion H1; subst. 
  - unfold AsciiVars.lt in H2; lia.
 - apply RProofs.in_find.
    + assumption.
    + eapply RProofs.lt_tree_trans in H2; eauto.
      assert (~ R.Raw.In x this1) by (apply RProofs.lt_tree_not_in in H2; auto).
      contradiction.
  - apply RProofs.in_find.
    + inversion is_bst; subst.
      assumption.
    + assumption.
Qed.

Lemma TcRhoIncludedNoFreeVarsEps_find:
  forall rho x,
    R.find x rho <> None ->
    forall e,
      ~ (free_rgn_vars_in_eps (fold_subst_eps rho e)) x.
Proof. 
  intros rho. destruct rho. induction this; intros x H e'.
  - unfold fold_subst_eps.
    replace (fun sa : StaticAction =>
               exists sa' : StaticAction,
                 e' sa' /\
                 fold_subst_sa {| R.this := R.Raw.Leaf nat; R.is_bst := is_bst |} sa' =
                 sa)
    with e' by (rewrite <- fold_eps_leaf with (is_bst := is_bst); reflexivity).
    intro. unfold R.find, R.Raw.find in H. simpl in H. contradict H. reflexivity.
  - inversion is_bst; subst. 
    replace (fold_subst_eps
               {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := is_bst |} e')
    with (fold_subst_eps {| R.this := this2; R.is_bst := H6 |}
                         (subst_eps k (Rgn_Const true false e)
                                    (fold_subst_eps {| R.this := this1; R.is_bst := H4 |} e')))
    by (rewrite <- fold_eps_node with (Hr:=H6) (Hl:=H4); reflexivity).
    intro.
    (*apply NotNoneIsSome in H. destruct H.
    eapply decompose_find_in_rho in H.*)
    destruct (AsciiVars.compare x k); subst.
    + apply TcRhoIncludedNoFreeVarsEps_aux_fold in H0.
      apply TcRhoIncludedNoFreeVarsEps in H0. 
      contradict H0.
      apply IHthis1.
      assert (~ R.Raw.In k this1) by (apply RProofs.lt_tree_not_in in H7; auto).
      assert (~ R.Raw.In k this2) by (apply RProofs.gt_tree_not_in in H8; auto).
      eapply FindIfLowerThan; eauto.
    + inversion e0; subst.
      apply TcRhoIncludedNoFreeVarsEps_aux_fold in H0.
      contradict H0.
      apply TcRhoIncludedNoFreeVarsEps_aux.
    + contradict H0.
      apply IHthis2.
      eapply FindIfGreaterThan; eauto.
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




Lemma subst_rho_free_vars_rgn_aux_1:
  forall this1 this2 k e t Hc Hl x r,
    R.find (elt:=nat) x {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := Hc |} =
     None ->
    free_rgn_vars_in_rgn (fold_subst_rgn {| R.this := this1; R.is_bst := Hl |} r) x ->
    fold_subst_rgn {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := Hc |} r = 
    fold_subst_rgn {| R.this := this1; R.is_bst := Hl |} r.
Proof.
  intros. unfold Region_in_Type in r. dependent induction r; 
  eapply TcRhoIncludedNoFreeVarsRgn_aux_fold in H0; eauto.
  + unfold free_rgn_vars_in_rgn in *; simpl in *. 
    inversion H0.
  + symmetry. rewrite fold_subst_rho_free_vars_rgn_aux. 
    symmetry. rewrite fold_subst_rho_free_vars_rgn_aux.
    reflexivity.
    * simpl in H0. inversion H0. subst.
      assumption.
    * simpl in H0. inversion H0. subst.
      apply RMapP.not_find_in_iff in H. 
      inversion Hc; subst.
      eapply not_in_raw_rho with (Hr:=H7) in H; auto.
      destruct H as [HNotIn1 [HNotIn2 [HNotIn3  HNotIn4]]]. 
      apply RMapP.not_find_in_iff.
      eassumption.
  + unfold free_rgn_vars_in_rgn in *; simpl in *. 
    inversion H0.
Qed.

Lemma subst_rho_free_vars_rgn_aux_2:
  forall this1 this2 k e t Hc Hr x r,
    R.find (elt:=nat) x {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := Hc |} =
     None ->
    free_rgn_vars_in_rgn (fold_subst_rgn {| R.this := this2; R.is_bst := Hr |} r) x ->
    fold_subst_rgn {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := Hc |} r = 
    fold_subst_rgn {| R.this := this2; R.is_bst := Hr |} r.
Proof.
  intros. unfold Region_in_Type in r. dependent induction r; 
  eapply TcRhoIncludedNoFreeVarsRgn_aux_fold in H0; eauto.
  + unfold free_rgn_vars_in_rgn in *; simpl in *. 
    inversion H0.
  + symmetry. rewrite fold_subst_rho_free_vars_rgn_aux. 
    symmetry. rewrite fold_subst_rho_free_vars_rgn_aux.
    reflexivity.
    * simpl in H0. inversion H0. subst.
      assumption.
    * simpl in H0. inversion H0. subst.
      apply RMapP.not_find_in_iff in H. 
      inversion Hc; subst.
      eapply not_in_raw_rho with (Hl:=H5) in H; auto.
      destruct H as [HNotIn1 [HNotIn2 [HNotIn3  HNotIn4]]]. 
      apply RMapP.not_find_in_iff.
      eassumption.
  + unfold free_rgn_vars_in_rgn in *; simpl in *. 
    inversion H0.
Qed.


Lemma subst_rho_free_vars_union_1 :
  forall x (e1 e2 : Ensemble VarId),
    not_set_elem (set_union e1 e2) x ->
    not_set_elem e1 x /\ not_set_elem e2 x.
Proof.
  intros. split; intro; apply H; [ apply Union_introl | apply Union_intror]; auto.
Qed.

Lemma subst_rho_free_vars_union_2 :
  forall x (e1 e2 : Ensemble VarId),
    not_set_elem e1 x /\ not_set_elem e2 x ->
    not_set_elem (set_union e1 e2) x.
Proof.
  intros. destruct H. intro. destruct H1; [apply H | apply H0]; auto.
Qed.

Lemma subst_rho_free_vars_sa_aux_1:
  forall this1 this2 k e t Hc Hl x sa,
    R.find (elt:=nat) x {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := Hc |} =
     None ->
    free_rgn_vars_in_sa (fold_subst_sa {| R.this := this1; R.is_bst := Hl |} sa) x ->
    fold_subst_sa {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := Hc |} sa = 
    fold_subst_sa {| R.this := this1; R.is_bst := Hl |} sa.
Proof.
  intros. induction sa;
  unfold free_rgn_vars_in_sa in *; simpl in *; f_equal;
  eapply subst_rho_free_vars_rgn_aux_1; eauto.
Qed.

Lemma subst_rho_free_vars_sa_aux_2:
  forall this1 this2 k e t Hc Hr x sa,
    R.find (elt:=nat) x {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := Hc |} =
     None ->
    free_rgn_vars_in_sa (fold_subst_sa {| R.this := this2; R.is_bst := Hr |} sa) x ->
    fold_subst_sa {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := Hc |} sa = 
    fold_subst_sa {| R.this := this2; R.is_bst := Hr |} sa.
Proof.
  intros. induction sa;
  unfold free_rgn_vars_in_sa in *; simpl in *; f_equal;
  eapply subst_rho_free_vars_rgn_aux_2; eauto.
Qed.


Lemma subst_rho_free_vars_eps_aux_1:
  forall this1 this2 k e t Hc Hl x e',
    R.find (elt:=nat) x {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := Hc |} =
     None ->
   free_rgn_vars_in_eps (fold_subst_eps {| R.this := this1; R.is_bst := Hl |} e') x ->
   free_rgn_vars_in_eps (fold_subst_eps
                     {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := Hc |} e') x.
Proof.
  intros. 
  unfold fold_subst_eps in *.
  destruct H0 as [sa1 [[sa1' [H1a H1b]] H1c]].
  exists sa1. split; [| assumption].
  exists sa1'. split; [assumption |].
  rewrite <- H1b.
  rewrite <- H1b in H1c.
  eapply subst_rho_free_vars_sa_aux_1; eauto.
Qed.


Lemma subst_rho_free_vars_eps_aux_2:
  forall this1 this2 k e t Hc Hr x e',
    R.find (elt:=nat) x {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := Hc |} =
     None ->
    free_rgn_vars_in_eps (fold_subst_eps {| R.this := this2; R.is_bst := Hr |} e') x ->
    free_rgn_vars_in_eps (fold_subst_eps
                     {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := Hc |} e') x.
Proof.
  intros. 
  unfold fold_subst_eps in *.
  destruct H0 as [sa1 [[sa1' [H1a H1b]] H1c]].
  exists sa1. split; [| assumption].
  exists sa1'. split; [assumption |].
  rewrite <- H1b.
  rewrite <- H1b in H1c.
  eapply subst_rho_free_vars_sa_aux_2; eauto.
Qed.

Lemma equal_fold_subst_rgn:
  forall this1 this2 k e t Hc r,
    R.find (elt:=nat) k {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := Hc |} = None ->
    free_rgn_vars_in_rgn r k ->
    fold_subst_rgn {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := Hc |} r = r.
Proof.
  intros. unfold Region_in_Type in r. dependent induction r; simpl in *.
  - inversion H0.
  - inversion H0. subst.
    apply fold_subst_rho_free_vars_rgn_aux. auto.   
  - inversion H0.
Qed.

Lemma equal_fold_subst_sa:
  forall this1 this2 k e t Hc sa, 
    R.find (elt:=nat) k {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := Hc |} = None ->
    free_rgn_vars_in_sa sa k ->
    fold_subst_sa {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := Hc |} sa = sa.
Proof.
  intros. induction sa; simpl in *; f_equal; apply equal_fold_subst_rgn; auto.
Qed.


Lemma baz:
  forall (rho : R.t RgnId),
  forall (k': R.key) (v': RgnId),
    ~ R.In k' rho ->
    exists elems1 elems2,
      elems1 ++ (k',v')::elems2 = R.elements (R.add k' v' rho) /\
      elems1 ++ elems2 = R.elements rho.
Proof.
  destruct rho. induction this; intros k' v' H.
  - exists nil. exists nil. intuition.
  - destruct (AsciiVars.compare k' k).
    + admit.
    + inversion e0; subst.
      contradict H. unfold R.In, R.Raw.In0. simpl. eauto.
    + admit.
Admitted.

Lemma fold_subst:
  forall A,
  forall (f : A -> (R.key * RgnId) -> A),
  forall l1 x' l2 b,
    (forall (y : R.key * RgnId) b0,
       In y l1 ->
       f (f b0 y) x' = f (f b0 x') y) ->
    List.fold_left f (l1 ++ x'::l2) b = fold_left f (l1 ++ l2) (f b x'). 
Proof.  
  intros f. 
  induction l1; intros x' l2 b H. 
  - simpl. reflexivity.
  - simpl. rewrite IHl1.
    + rewrite H.
      * reflexivity.
      * apply in_eq.
    + intros y b0 In_y. apply H. apply in_cons. apply In_y.
Qed.


Lemma fold_add_type:
  forall A,
  forall (f : R.key -> RgnId -> A -> A),
  forall (rho : R.t RgnId),
  forall (k': R.key) (v': RgnId) (b: A),
    ~ R.In k' rho ->
    (forall k v b0,
       R.MapsTo k v rho ->
       f k' v' (f k v b0) = f k v (f k' v' b0)) ->
    R.fold f (R.add k' v' rho) b = R.fold f rho (f k' v' b).
Proof.
  intros A f rho k' v' b H' H.
  repeat (rewrite R.fold_1). 
  destruct (baz rho k' v' H') as [elems1 [elems2 [H1 H2]]]. 
  rewrite <- H1.
  rewrite <- H2.
  apply fold_subst.
  intros [k1 v1] b0 In_k1_v1. simpl. apply H.
  apply R.elements_2.
  apply In_InA.
  - repeat constructor.
    + destruct H0. auto.
    + destruct H0; auto.
    + destruct H0; rewrite H0. destruct H3. auto.
    + destruct H0; rewrite H4. destruct H3. auto.
  - rewrite <- H2.
    apply List.in_or_app. left. apply In_k1_v1.
Qed.


Lemma contrapositiveTcRho :
  forall rho rgns x,
    (forall r : R.key, 
       R.find (elt:=nat) r rho <> None -> set_elem rgns r) ->
    not_set_elem rgns x ->
    R.find (elt:=nat) x rho = None.
Proof.
  intros.
  unfold not_set_elem in H0. unfold Ensembles.Complement in H0.
  unfold set_elem in H. unfold Ensembles.Complement in H.
  apply RMapP.not_find_in_iff.
  intro. apply H0.
  apply H.
  assert (Hr : forall t r rho,
             R.In (elt:=t) r rho -> R.find (elt:=t) r rho <> None) by
    (intros; apply RMapP.in_find_iff; auto).
  apply Hr.
  assumption.
Qed.
