Require Import Coq.Arith.Peano_dec.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sets.Ensembles.
Require Import Ascii.
Require Import Coq.ZArith.Znat.
Require Import Coq.Program.Equality.

Add LoadPath "." as Top0.
Require Import Top0.Tactics.
Require Import Top0.Keys.
Require Import Top0.Definitions.
Require Import Top0.Nameless.
Require Import Top0.CorrectnessLemmas.
Require Import Top0.Environment.
Require Import Top0.Heap. 
Require Import Top0.Determinism.
Require Import Top0.Axioms.

Require Import Omega.

Module TypeSoundness.

  Import Heap.
  Import Environment.

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
    (exists v, fold_subst_rgn rho (Rgn2_FVar true true x) = Rgn2_Const true true v) \/ fold_subst_rgn rho (Rgn2_FVar true true x) = Rgn2_FVar true true x.
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

Module RMapOrdProp := FMapFacts.OrdProperties R.

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

Lemma subst_rho_open_close_rgn :
  forall rho n w v' rho' r r0 x,
    lc_type_rgn r0 ->
    find_R w rho = Some v' ->
    fold_subst_rgn rho r = fold_subst_rgn rho' (closing_rgn_in_rgn2 n x r0) ->
    fold_subst_rgn rho' (opening_rgn_in_rgn2 n (Rgn2_Const true true v') (closing_rgn_in_rgn2 n x r0)) =
    fold_subst_rgn rho (opening_rgn_in_rgn2 n (mk_rgn_type w) r).
Proof. 
  intros rho n w v' rho' r r0 x Hlc1 HF H.
  unfold rgn2_in_typ in r.
  unfold rgn2_in_typ in r0. 
  unfold rgn2_in_exp in w.
  dependent induction r; dependent induction Hlc1; simpl in *.
  - repeat rewrite subst_rho_rgn_const in *. auto.
  - destruct (RMapP.eq_dec r0 x); subst; simpl in *.
    + rewrite subst_rho_index in H. rewrite subst_rho_rgn_const in H. inversion H.
    + auto.
  - auto.
  - destruct (RMapP.eq_dec r x); subst; simpl in *.
    + rewrite subst_rho_index in H.
      destruct (subst_rho_fvar_1 rho n0) as [[v H0] | H0];
      rewrite H0 in H; inversion H.
    + auto.
  - rewrite subst_rho_index in H. rewrite subst_rho_rgn_const in H. inversion H.
  - destruct (RMapP.eq_dec r x); subst; simpl in *.
    + repeat rewrite subst_rho_index in H. inversion H; subst.
      rewrite NPeano.Nat.eqb_refl.
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
    fold_subst_sa rho sa1 = fold_subst_sa rho' (closing_rgn_in_sa2 n x sa) ->
    fold_subst_sa rho' (opening_rgn_in_sa2 n (Rgn2_Const true true v') (closing_rgn_in_sa2 n x sa)) =
    fold_subst_sa rho (opening_rgn_in_sa2 n (mk_rgn_type w) sa1).
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
    fold_subst_eps rho e1 = fold_subst_eps rho' (closing_rgn_in_eps2 n x e) ->
    fold_subst_eps rho' (opening_rgn_in_eps2 n (Rgn2_Const true true v') (closing_rgn_in_eps2 n x e)) =
    fold_subst_eps rho (opening_rgn_in_eps2 n (mk_rgn_type w) e1).
Proof.
  intros rho n w v' rho' e e1 x  Hcl1 HF H. 
  apply Extensionality_Ensembles.  
  unfold Same_set, Included.
  split; intros; unfold In in *.
  - unfold fold_subst_eps.  unfold fold_subst_eps in H0. 
    unfold opening_rgn_in_eps2, closing_rgn_in_eps2. unfold opening_rgn_in_eps2, closing_rgn_in_eps2 in H0.
    destruct H0 as [sa [[sa' [[sa'' [H2 H3]] H4]] H5]].
    rewrite <- H5. rewrite <- H4. rewrite <- H3.
    inversion Hcl1. destruct (H0 sa'').

    assert (fold_subst_sa rho sa = fold_subst_sa rho' (closing_rgn_in_sa2 n x sa'') /\ e1 sa /\ e sa'') by
        (eapply subst_rho_eps_aux_1; eauto).

    assert(fold_subst_sa rho' (opening_rgn_in_sa2 n (Rgn2_Const true true v') (closing_rgn_in_sa2 n x sa'')) =
            fold_subst_sa rho (opening_rgn_in_sa2 n (mk_rgn_type w) sa)). 
    apply subst_rho_open_close_sa; auto. intuition.
    rewrite H9. 
    exists (opening_rgn_in_sa2 n (mk_rgn_type w) sa).
    intuition.
    exists sa.
    intuition.
 - unfold fold_subst_eps.  unfold fold_subst_eps in H0. 
   unfold opening_rgn_in_eps2, closing_rgn_in_eps2. unfold opening_rgn_in_eps2, closing_rgn_in_eps2 in H0.
   destruct H0 as [sa [[sa' [H1 H2]] H3]].
   rewrite <- H3. rewrite <- H2. 
   exists (opening_rgn_in_sa2 n (Rgn2_Const true true v') (closing_rgn_in_sa2 n x sa')). 
   split.  
   + exists (closing_rgn_in_sa2 n x sa').  intuition.
     exists sa'. intuition.  
     assert (fold_subst_sa rho sa = fold_subst_sa rho' (closing_rgn_in_sa2 n x sa') /\ e1 sa /\ e sa') by
         (eapply subst_rho_eps_aux_1 in H; eauto; intuition; eauto).
     intuition.
   + inversion Hcl1. destruct (H0 sa').
     eapply subst_rho_open_close_sa; eauto. 
     eapply subst_rho_eps_aux_2; eauto.
Qed.
   
Lemma subst_rho_open_close :
  forall rho w v' rho' x tyr0 tyr,
    lc_type tyr0 ->
    find_R w rho = Some v' ->
    subst_rho rho' (close_var x tyr0) = subst_rho rho tyr ->
    subst_rho rho' (open (mk_rgn_type (Rgn2_Const true false v')) (close_var x tyr0)) =
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



Lemma ty_sound_var :   
  forall x v stty rho env ctxt t,
  TcEnv (stty, rho, env, ctxt) ->
  find_E x env = Some v -> find_T x ctxt = Some t -> 
  TcVal (stty, v, subst_rho rho t).
Proof.
  intros x v stty rho env ctxt t HTcEnv FindEnv FindCtxt. (* Hclosed. *)
  inversion_clear HTcEnv as [? ? ? ? HBst HFwd HBack HTc].
  destruct (HFwd x v FindEnv) as [y FindEnv']. 
  rewrite FindEnv' in FindCtxt. inversion FindCtxt; subst. 
  eapply HTc; [eexact FindEnv | eexact FindEnv' ]. (*| assumption]. *)
Qed.
 
Lemma ty_sound_closure:  
  forall stty rgns env rho ctxt f x ec ee tyx tyc effc effe, 
    TcRho (rho, rgns) -> 
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (stty, ctxt, rgns,  Mu f x ec ee, Ty2_Arrow tyx effc tyc effe Ty2_Effect, Empty_Static_Action) ->  
    TcVal (stty, Cls (env, rho,  Mu f x ec ee),  subst_rho rho (Ty2_Arrow tyx effc tyc effe Ty2_Effect)).   
Proof.
  intros; econstructor; eassumption.
Qed.

Lemma ty_sound_region_closure:
  forall stty rgns env rho ctxt x er tyr effr, 
    TcRho (rho, rgns) -> 
    TcEnv (stty, rho, env,ctxt) ->
    TcExp (stty, ctxt, rgns, Lambda x er, Ty2_ForallRgn (close_var_eff x effr) (close_var x tyr),  Empty_Static_Action) ->
    TcVal (stty, Cls (env, rho, Lambda x er), subst_rho rho (Ty2_ForallRgn (close_var_eff x effr) (close_var x tyr))).
Proof.
  intros. econstructor; eassumption.
Qed.  
  
Lemma weakening_trans :
   forall stty stty' stty'', 
     (forall (l : ST.key) (t : tau),
        ST.find (elt:=tau) l stty = Some t -> ST.find (elt:=tau) l stty' = Some t) ->
     (forall (l : ST.key) (t : tau),
        ST.find (elt:=tau) l stty' = Some t -> ST.find (elt:=tau) l stty'' = Some t) ->
     (forall (l : ST.key) (t : tau),
        ST.find (elt:=tau) l stty = Some t -> ST.find (elt:=tau) l stty'' = Some t).
Proof.
  intros stty stty' stty'' Weak Weak'.
  intros l t ?. apply Weak'. now apply Weak. 
Qed.

Lemma bound_var_is_fresh :
  forall rho rgns x,
    TcRho (rho, rgns) -> not_set_elem rgns x -> ~ R.In (elt:=Region) x rho.
Proof.
  intros rho rgns x H1 H2.
  inversion H1; subst.
  unfold not_set_elem in H2. unfold Ensembles.Complement in H2. 
  unfold not. intro. 
  apply RMapP.in_find_iff in H. 
  apply H2. (* double negation *)
  eapply H3; eassumption.
Qed.  

Lemma ty_sound:
  forall e env rho hp hp' v dynamic_eff,
    (hp, env, rho, e) ⇓ (hp', v, dynamic_eff) ->
    forall stty ctxt rgns t static_eff,
      TcHeap (hp, stty) ->
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (stty, ctxt, rgns, e, t, static_eff) ->
      exists stty',
        (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
         /\ TcHeap (hp', stty')
         /\ TcVal (stty', v, subst_rho rho t).
Proof.
  intros e env rho hp hp'  v dynamic_eff D.
  dynamic_cases (dependent induction D) Case;
  intros stty ctxt rgns t static_eff Hhp Hrho Henv Hexp; 
  inversion Hexp; subst.   
  Case "cnt n".
    exists stty; (split; [| split]; auto). rewrite subst_rho_natural.
    econstructor; eassumption.
  Case "bool b".
    exists stty;  (split; [| split]; auto). rewrite subst_rho_boolean.
    econstructor; eassumption. 
  Case "var x".
    exists stty; (split; [| split]; auto).
    eapply ty_sound_var; eassumption. 
  Case "mu_abs". 
    exists stty; (split; [| split]; auto).
    eapply ty_sound_closure; try (solve [eassumption]).
  Case "rgn_abs". 
    exists stty;  (split; [| split]; auto). 
    eapply ty_sound_region_closure; try (solve [eassumption]).
  Case "mu_app".   
    edestruct IHD1 as [sttym [Weak1 [TcHeap1 TcVal_mu]]]; eauto. 
    edestruct IHD2 as [sttya [Weaka [TcHeapa TcVal_arg]]]; eauto.  
    eapply ext_stores__env; eauto. eapply ext_stores__exp. eassumption. eassumption. 
    inversion TcVal_mu as [ | | | ? ? ? ? ? ? ?   TcRho_rho' TcEnv_env' TcExp_abs | | |] ; subst.      
    inversion TcExp_abs as [ | |  | ? ? ? ? ? ? ? ? ? ? ? ? TcExp_ec TcExp_ee | | | | | | | | | | | | | | | | | | | | | ]; subst.
    rewrite <- H4 in TcVal_mu. 
    do 2 rewrite subst_rho_arrow in H4. inversion H4.
    assert (SubstEq1: subst_rho rho' tyx = subst_rho rho tya) by assumption. 
    assert (SubstEq2: subst_rho rho' tyc = subst_rho rho t) by assumption.
    rewrite <- SubstEq1 in TcVal_arg.
    unfold update_rec_E, update_rec_T in *. 
    edestruct IHD3 as [sttyb [Weakb [TcHeapb TcVal_res]]]; eauto.
    apply update_env. apply update_env. eapply ext_stores__env; eauto.  
    eapply ext_stores__val; eauto. eassumption.
    eapply ext_stores__exp; eauto.
    exists sttyb; intuition.  
  Case "rgn_app".     
    edestruct IHD1 as [sttyl [Weak1 [TcHeap1 TcVal_lam]]]; eauto. 
    inversion TcVal_lam as  [ | | | ? ? ? ? ? ? ? TcRho_rho' TcEnv_env' TcExp_lam | | |]; subst.   
    inversion TcExp_lam as [ | | | | ? ? ? ? ? ? ? ? ? TcExp_eb | | | | | | | | | | | | | | | | | | | |  ]; subst.  
    edestruct IHD2 as [sttyr [Weak2 [TcHeap2 TcVal_res]]]; eauto using update_env, ext_stores__env, ext_stores__exp.
    apply update_rho. assumption. assumption. eapply extended_rho; eauto. 
    exists sttyr; intuition. 
    rewrite subst_rho_forallrgn in H5.
    rewrite subst_rho_forallrgn in H5.
    inversion H5.  
    unfold update_R in TcVal_res. 
    simpl in TcVal_res. rewrite subst_add_comm in TcVal_res.
    SCase "abstraction body is well typed".
    unfold subst_in_type in TcVal_res.
    rewrite SUBST_AS_CLOSE_OPEN in TcVal_res; auto.
    erewrite subst_rho_open_close in TcVal_res; eauto. 
    SCase "bound variable is free".
    eapply bound_var_is_fresh; eauto.
  Case "eff_app".
    edestruct IHD1 as [sttym [Weak1 [TcHeap1 TcVal_mu]]]; eauto.
    edestruct IHD2 as [sttya [Weaka [TcHeapa TcVal_arg]]]; eauto using ext_stores__env, ext_stores__exp.
    inversion TcVal_mu as  [ | | | ? ? ? ? ? ? ? TcRho_rho' TcEnv_env' TcExp_abs | | |]; subst. 
    inversion TcExp_abs as [ | | | | ? ? ? ? ? ? ? ? ? TcExp_eb | | | | | | | | | | | | | | | | | | | |  ]; subst. 
    edestruct IHD3 as [sttyb [Weakb [TcHeapb TcVal_res]]]; eauto.
    SCase "Extended Env".
      apply update_env.
      SSCase "TcEnv". apply update_env.
        SSSCase "Extended". eapply ext_stores__env; eauto.
        SSSCase "Extended TcVal". rewrite <- H4 in TcVal_mu.  eapply ext_stores__val; eauto.
      SSCase "TcVal". do 2 rewrite subst_rho_arrow in H4.
          inversion H4.
          assert (SubstEq: subst_rho rho' tyx = subst_rho rho tya) by assumption.
          rewrite <- SubstEq in TcVal_arg.  eassumption. 
    eapply ext_stores__exp; eauto.
    exists sttyb. intuition.
    rewrite subst_rho_effect. rewrite subst_rho_effect in TcVal_res.
    assumption.
  Case "par_pair".
    edestruct IHD3 as [sttym [Weak1 [TcHeap1 TcVal_app1]]]; eauto. 
    edestruct IHD4 as [sttya [Weaka [TcHeapa TcVal_app2]]]; eauto.
    inversion TcVal_app1 as [A B [C D HRApp1] | | | | | |]; subst. 
    inversion TcVal_app2 as [A B [C D HRApp2] | | | | | |]; subst.  
    exists (Functional_Map_Union sttya sttym). intuition. 
    SCase "Weakening".
      apply UnionStoreTyping; [apply Weaka | apply Weak1]; auto.
    SCase "TcHeap".
      eapply UnionTcHeap; eauto.
    SCase "TcVal".
      econstructor; [rewrite <- HRApp1 | rewrite <- HRApp2]; constructor.
  Case "cond_true".  
    edestruct IHD1 as [sttyb [Weakb [TcHeapvb TcVal_e0]]]; eauto. 
    edestruct IHD2 as [stty1 [Weak1 [TcHeapv1 TcVal_e1]]]; 
      eauto using ext_stores__env, ext_stores__exp.
    exists stty1. intuition.
  Case "cond_false".
    edestruct IHD1 as [sttyb [Weakb [TcHeapvb TcVal_e0]]]; eauto. 
    edestruct IHD2 as [stty2 [Weak2 [TcHeapv2 TcVal_e2]]]; 
      eauto using ext_stores__env, ext_stores__exp.
    exists stty2. intuition.  
  Case "new_ref e".          
    destruct IHD with (stty := stty)
                      (ctxt := ctxt)
                      (rgns := rgns)  
                      (t := t0)
                      (static_eff := veff)
      as [sttyv [Weakv [TcHeapv TcVal_v]]]; eauto.
    exists (update_ST ((r, l), subst_rho rho t0) sttyv); split; [ | split].  
    SCase "Extended stores".   
      intros k' t' STfind. destruct k' as [r' l'].
      destruct (eq_nat_dec r r'); destruct (eq_nat_dec l l'); subst. 
      SSCase "New address must be fresh, prove by contradiction".
        apply Weakv in STfind. 
        inversion_clear TcHeapv as [? ? ?  STfind_Hfind ?].  
        destruct (STfind_Hfind (r', l') t' STfind) as [x F].
        assert (C : None = Some x) by (rewrite <- F; rewrite <- H0; reflexivity).
        discriminate. 
      SSCase "Existing addresses are well-typed 1".
        apply ST_diff_key_2; [ simpl; intuition; apply n; congruence | now apply Weakv in STfind ].
      SSCase "Existing addresses are well-typed 2".
        apply ST_diff_key_2; [ simpl; intuition; apply n; congruence | now apply Weakv in STfind ].
      SSCase "Existing addresses are well-typed 3".
        apply ST_diff_key_2; [simpl; intuition; apply n; congruence | now apply Weakv ].
    SCase "Heap typeness".  
      apply update_heap_fresh; eauto. 
      remember (find_ST (r, l) sttyv) as to; symmetry in Heqto.
      destruct to as [ t | ]. 
      SSCase "New address must be fresh, prove by contradiction".
        inversion_clear TcHeapv as [? ? ? STfind_Hfind ?].  
        destruct (STfind_Hfind (r, l) t Heqto) as [? ex].
        rewrite H0 in ex. discriminate.
      SSCase "Heap typeness is preserved".
         reflexivity. 
    SCase "Loc is well-typed".
       simpl in H; inversion H; subst. 
       rewrite subst_rho_tyref. unfold mk_rgn_type. rewrite subst_rho_rgn_const.
       econstructor. apply ST_same_key_1.
  Case "get_ref e".    
    destruct IHD with (hp'0 := hp')
                      (v := Loc (Rgn2_Const true false s) l) 
                      (stty := stty)
                      (rgns := rgns)
                      (ctxt := ctxt)
                      (t := Ty2_Ref (mk_rgn_type ((Rgn2_Const true false s))) t)
                      (static_eff := aeff)
                      (dynamic_eff := aacts)
    as [sttyv [Weakv [TcHeapv TcVal_v]]]; eauto.
    exists sttyv. split; [ | split].
    SCase "HeapTyping extends".
      apply Weakv.
    SCase "Heap is well typed".
      apply TcHeapv.
    SCase "Value is well-typed". 
      inversion_clear TcHeapv as [? ? ? ? HeapTcVal]. eapply HeapTcVal; eauto. 
      inversion TcVal_v; subst; simpl in H; inversion H; subst.
      rewrite subst_rho_tyref in H7. inversion H7. subst.
      assumption.
  Case "set_ref e1 e2".  
    destruct IHD1 with (hp' := heap')
                       (v := Loc (Rgn2_Const true false s) l) 
                       (stty := stty)
                       (ctxt := ctxt)
                       (rgns := rgns)
                       (t := Ty2_Ref (mk_rgn_type ((Rgn2_Const true false s))) t0)
                       (static_eff := aeff)
                       (dynamic_eff := aacts)
       as [sttya [Weaka [TcHeapa TcVal_a]]]; eauto.
    destruct IHD2 with (stty := sttya)
                       (ctxt := ctxt)
                       (rgns := rgns)  
                       (t := t0)
                       (static_eff := veff)
      as [sttyv [Weakv [TcHeapv TcVal_v]]];
      eauto using ext_stores__env, ext_stores__exp.
    exists sttyv. split; [ | split].
    SCase "HeapTyping extends".
      eapply weakening_trans; eauto.
    SCase "New heap is well typed". 
      apply update_heap_exists with (t:= subst_rho rho t0).   
      { assumption. }
      { apply Weakv. inversion TcVal_a; subst. 
        simpl in H; inversion H; subst.
        rewrite subst_rho_tyref in H4. inversion H4. subst.
        assumption. }
      { assumption. }
    SCase "Result value is well-typed".
      rewrite subst_rho_unit. constructor.
  Case "nat_plus x y". 
    edestruct IHD1 as [sttyx [Weakx [TcHeapvx TcVal_x]]]; eauto. 
    edestruct IHD2 as [sttyy [Weaky [TcHeapvy TcVal_y]]]; 
      eauto using ext_stores__env, ext_stores__exp. 
    exists sttyy. intuition. rewrite subst_rho_natural. constructor.
  Case "nat_minus x y". 
    edestruct IHD1 as [sttyx [Weakx [TcHeapvx TcVal_x]]]; eauto. 
    edestruct IHD2 as [sttyy [Weaky [TcHeapvy TcVal_y]]]; 
      eauto using ext_stores__env, ext_stores__exp.
    exists sttyy. intuition. rewrite subst_rho_natural. constructor.
  Case "nat_times x y". 
    edestruct IHD1 as [sttyx [Weakx [TcHeapvx TcVal_x]]]; eauto. 
    edestruct IHD2 as [sttyy [Weaky [TcHeapvy TcVal_y]]]; 
      eauto using ext_stores__env, ext_stores__exp.
    exists sttyy. intuition. rewrite subst_rho_natural. constructor.
  Case "bool_eq x y". 
    edestruct IHD1 as [sttyx [Weakx [TcHeapvx TcVal_x]]]; eauto. 
    edestruct IHD2 as [sttyy [Weaky [TcHeapvy TcVal_y]]]; 
      eauto using ext_stores__env, ext_stores__exp.
    exists sttyy. intuition. rewrite subst_rho_boolean. constructor.
  Case "alloc_abs".
    exists stty. intuition. rewrite subst_rho_effect. constructor.
  Case "read_abs".
    exists stty. intuition. rewrite subst_rho_effect. constructor.
  Case "write_abs".
    exists stty. intuition. rewrite subst_rho_effect. constructor.
  Case "read_conc".
    exists stty. intuition.
    assert (hp = hp') by (eapply EmptyTracePreservesHeap_1; eauto; reflexivity); now subst.
    rewrite subst_rho_effect. constructor.      
  Case "write_conc".
    exists stty. intuition.
    assert (hp = hp') by (eapply EmptyTracePreservesHeap_1; eauto; reflexivity); now subst.
    rewrite subst_rho_effect. constructor. 
  Case "eff_concat". exists stty. intuition. rewrite subst_rho_effect. constructor.
  Case "eff_top". exists stty. intuition. rewrite subst_rho_effect. constructor.
  Case "eff_empty". exists stty. intuition. rewrite subst_rho_effect. constructor.
Qed.

End TypeSoundness.
