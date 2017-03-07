Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FSetWeakList.
Require Import Coq.MSets.MSetWeakList.
Require Import Coq.FSets.FSetFacts.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FMapFacts.

Add LoadPath "." as Top0.
Require Import Top0.Keys.
Require Import Top0.Nameless.

Module R := FMapAVL.Make (AsciiVars).
Module RMapP := FMapFacts.Facts R.
Module RMapProp := FMapFacts.Properties R.

Definition Epsilon := Epsilon2.
Definition tau := type2.

(* commutativity of f, paired key *)
Lemma fold_subst:
  forall A,
  forall (f : A -> (R.key * Region) -> A),
  forall l1 x' l2 b,
    (forall y b0,
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

Lemma baz:
  forall (rho : R.t Region),
  forall (k': R.key) (v': Region),
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

(* commutativity of f, unpaired key *)
Lemma fold_add_type:
  forall A,
  forall (f : R.key -> Region -> A -> A),
  forall (rho : R.t Region),
  forall (k': R.key) (v': Region) (b: A),
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


Lemma subst_type_rgn_comm: forall r k1 k2 v1 v2, 
   not_set_elem (free_rgn_vars_in_rgn2 r) k1 ->
   not_set_elem (free_rgn_vars_in_rgn2 r) k2 ->
   subst_rgn k1 (Rgn2_Const true false v1) (subst_rgn k2 (Rgn2_Const true false v2) r) =
   subst_rgn k2 (Rgn2_Const true false v2) (subst_rgn k1 (Rgn2_Const true false v1) r).
Proof.
  intros r k1 k2 v1 v2 Hr1 Hr2.
  unfold subst_rgn. unfold rgn2_in_typ in r.
  dependent induction r.
  - reflexivity.
  - destruct (AsciiVars.eq_dec k2 n).
    + inversion e; subst. 
      unfold not_set_elem, Complement in Hr2. 
      unfold not, Ensembles.In in Hr2.
      contradict Hr2. simpl. apply In_singleton.
    + simpl. destruct (AsciiVars.eq_dec k1 n).
      * reflexivity.
      * destruct (AsciiVars.eq_dec k2 n); unfold AsciiVars.eq in *. 
        contradiction. reflexivity.  
  - reflexivity.
Qed.

Lemma subst_type_rgn_comm_2: forall r k1 k2 v1 v2,
                               k1 <> k2 ->
                               subst_rgn k1 (Rgn2_Const true false v1) (subst_rgn k2 (Rgn2_Const true false v2) r) =
                               subst_rgn k2 (Rgn2_Const true false v2) (subst_rgn k1 (Rgn2_Const true false v1) r).
Proof.
  intros r k1 k2 v1 v2 H.
  unfold rgn2_in_typ in r.
  dependent induction r; try (solve [simpl; reflexivity ]).
  unfold subst_rgn. destruct (AsciiVars.eq_dec k1 k2).
  - inversion e. contradiction.
  - simpl. destruct (AsciiVars.eq_dec k2 n).
    + assert (~ AsciiVars.eq k1 n) by (inversion e; congruence).
      unfold  AsciiVars.eq in *.
      destruct (AsciiVars.eq_dec k1 n).
      * now absurd (k1=n).
      * inversion e; subst; now destruct (AsciiVars.eq_dec n n).
    + destruct (AsciiVars.eq_dec k1 n); [reflexivity |].
      now destruct (AsciiVars.eq_dec k2 n).
Qed.      

Lemma subst_type_sa_comm_2: forall sa k1 k2 v1 v2,
                               k1 <> k2 ->
                               subst_sa k1 (Rgn2_Const true false v1) (subst_sa k2 (Rgn2_Const true false v2) sa) =
                               subst_sa k2 (Rgn2_Const true false v2) (subst_sa k1 (Rgn2_Const true false v1) sa).
Proof.
  intros sa k1 k2 v1 v2 H.
  destruct sa; simpl; apply f_equal; apply subst_type_rgn_comm_2; auto.
Qed.

Lemma subst_type_eps_comm_2 : forall (k1 : R.key) (v1 : Region) (k2 : R.key) (v2 : Region) (e : Epsilon),
                                k1 <> k2 ->
                                subst_eps k1 (Rgn2_Const true false v1) (subst_eps k2 (Rgn2_Const true false v2) e) =
                                subst_eps k2 (Rgn2_Const true false v2) (subst_eps k1 (Rgn2_Const true false v1) e).
Proof.
  intros k1 v1 k2 v2 e H. unfold subst_eps.
  apply Extensionality_Ensembles; unfold Same_set, Included.
  split; intros; unfold Ensembles.In in *; destruct H0 as [x' [[x'' [H1 H2]] H3]];
  subst; repeat (eexists || split || subst); eauto using subst_type_sa_comm_2.
Qed.

Definition subst_in_type := fun x r ty => subst_type x (Rgn2_Const true false r) ty.

Definition subst_in_eff := fun x r eff => subst_eps x (Rgn2_Const true false r) eff.

Definition subst_in_sa := fun x r sa => subst_sa x (Rgn2_Const true false r) sa.

Definition subst_in_rgn := fun x r rgn => subst_rgn x (Rgn2_Const true false r) rgn.

Definition subst_rho := R.fold subst_in_type.

Definition fold_subst_rgn := R.fold (fun x r rgn => subst_rgn x (Rgn2_Const true false r) rgn).

Definition fold_subst_sa rho sa:=
  match sa with
    | SA2_Alloc rgn => SA2_Alloc (fold_subst_rgn rho rgn)
    | SA2_Read rgn => SA2_Read (fold_subst_rgn rho rgn)
    | SA2_Write rgn => SA2_Write (fold_subst_rgn rho rgn)
  end.

Definition fold_subst_eps rho eps :=
  fun sa => exists sa', eps sa' /\ fold_subst_sa rho sa' = sa.

Lemma subst_type_type_comm_2 : forall (k1 : R.key) (v1 : Region) (k2 : R.key) (v2 : Region) (b : tau),
                          k1 <> k2 -> 
                          subst_in_type k1 v1 (subst_in_type k2 v2 b) = subst_in_type k2 v2 (subst_in_type k1 v1 b).
Proof.
  intros k1 v1 k2 v2 b H.
  unfold subst_in_type.
  induction b; simpl; try (solve [simpl; reflexivity ]).
  - f_equal; [apply IHb1 | apply IHb2].
  - f_equal; [ | apply IHb].
    now apply  subst_type_rgn_comm_2.
  - f_equal; [ apply IHb1 | |  apply IHb2 | |  apply IHb3]; eauto using subst_type_eps_comm_2.
  - f_equal; [ | apply IHb]; eauto using subst_type_eps_comm_2.
Qed.

Lemma subst_add_comm :
  forall k v rho ,
    ~ R.In (elt:=Region) k rho ->
    forall ty, 
      subst_rho (R.add k v rho) ty = subst_rho rho (subst_in_type k v ty). 
Proof.
  intros k v rho H ty.
  (*unfold subst_rho, subst_in_type.*)
  apply fold_add_type.  
  - assumption.
  - intros k0 v0 b0 H'.
    rewrite subst_type_type_comm_2.
    + reflexivity.
    + intro; subst.
      destruct H.
      apply RMapProp.F.elements_in_iff.
      exists v0.
      apply RMapProp.F.elements_mapsto_iff.
      assumption.
Qed.

Lemma subst_add_comm_rgn :
  forall k v rho ,
    ~ R.In (elt:=Region) k rho ->
    forall rgn, 
      fold_subst_rgn (R.add k v rho) rgn = fold_subst_rgn rho (subst_in_rgn k v rgn).
Proof.
  intros k v rho H rgn.
   apply fold_add_type. 
   - assumption.
   - intros k0 v0 b0 H'.
     rewrite subst_type_rgn_comm_2.
     + reflexivity.
     + intro; subst.
       destruct H.
       apply RMapProp.F.elements_in_iff.
       exists v0.
       apply RMapProp.F.elements_mapsto_iff.
       assumption.
Qed.

Lemma subst_add_comm_sa :
  forall k v rho ,
    ~ R.In (elt:=Region) k rho ->
    forall sa, 
      fold_subst_sa (R.add k v rho) sa = fold_subst_sa rho (subst_in_sa k v sa).
Proof.
  intros k v rho H sa.
  unfold fold_subst_sa.
  induction sa; simpl; f_equal; apply subst_add_comm_rgn; assumption.
Qed.

Lemma subst_add_comm_eff :
  forall k v rho ,
    ~ R.In (elt:=Region) k rho ->
    forall eff, 
      fold_subst_eps (R.add k v rho) eff = fold_subst_eps rho (subst_in_eff k v eff). 
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

Axiom fold_subst_rgn_eq:
  forall k rho e,
    R.find k rho  = Some e ->
    fold_subst_rgn rho (Rgn2_FVar true true k) = Rgn2_Const true true e.

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

Lemma FindInRhoNotFreeInRgn:
  forall x rho r r0,
    R.find (elt:=nat) r rho = Some x ->
    ~ free_rgn_vars_in_rgn2 (fold_subst_rgn rho r0) r.  
Proof.
  intros.
  unfold Ensembles.In. 
  unfold rgn2_in_typ in r0.
  dependent induction r0.
  - rewrite subst_rho_rgn_const. simpl. intro. contradiction. 
  - destruct (AsciiVars.eq_dec n r). 
    + inversion e; subst.     
      rewrite  fold_subst_rgn_eq with (e:=x); eauto.
      unfold free_rgn_vars_in_rgn2.
      intro. contradiction.
    + unfold AsciiVars.eq in n0.  
      admit.
  - rewrite subst_rho_index.
    unfold free_rgn_vars_in_rgn2. intro. contradiction.
Admitted.

Lemma FindInRhoNotFreeInSa:
  forall r rho x sa,
    R.find (elt:=nat) r rho = Some x ->
    ~ free_rgn_vars_in_sa2 sa r.
Proof.
  intros.
  induction sa; unfold free_rgn_vars_in_sa2; simpl.
  - unfold  free_rgn_vars_in_rgn2.
    unfold rgn2_in_typ in r0.
    dependent induction r0.
    + intro. inversion H0.
    + intro. admit.
    + intro. inversion H0.
  -  unfold  free_rgn_vars_in_rgn2.
    unfold rgn2_in_typ in r0.
    dependent induction r0.
    + intro. inversion H0.
    + intro. admit.
    + intro. inversion H0.
  - unfold  free_rgn_vars_in_rgn2.
    unfold rgn2_in_typ in r0.
    dependent induction r0.
    + intro. inversion H0.
    + intro. admit.
    + intro. inversion H0.
Admitted.

Lemma FindInRhoNotFreeInEps:
  forall r rho x e,
    R.find (elt:=nat) r rho = Some x ->
    ~ free_rgn_vars_in_eps2 (fold_subst_eps rho e) r.
Proof.
  unfold free_rgn_vars_in_eps2. intros.
  intro.
  unfold fold_subst_eps in H0.
  destruct H0. 
Admitted.

Lemma FindInRhoNotFreeInType:
  forall r rho x t,
    R.find (elt:=nat) r rho = Some x ->
    ~ frv (subst_rho rho t) r.
Proof.
  intros.  
  induction t.
  - rewrite subst_rho_natural; simpl. intro. contradiction.
  - rewrite subst_rho_boolean; simpl. intro. contradiction.
  - rewrite subst_rho_effect; simpl. intro. contradiction.
  - rewrite subst_rho_unit; simpl. intro. contradiction.
  - rewrite subst_rho_pair; simpl. intuition.
    destruct H0; intuition.
  - rewrite subst_rho_tyref; simpl. intuition.
    destruct H0. 
    + apply IHt.   
      contradict H0.
      eapply FindInRhoNotFreeInRgn; eauto.
    + apply IHt. auto.
  - rewrite subst_rho_arrow; simpl. intuition.
    destruct H0.
    + auto.
    + destruct H0.
      * { destruct H0.
          - eapply FindInRhoNotFreeInEps; eauto.
          - eapply FindInRhoNotFreeInEps; eauto. }
      * { destruct H0.
          - auto.
          - auto. }
  - rewrite subst_rho_forallrgn; simpl. intuition.
    destruct H0.
    * apply IHt.
      unfold In in H0.  
      contradict H0.
      eapply FindInRhoNotFreeInEps; eauto.
    * auto.
Qed.

