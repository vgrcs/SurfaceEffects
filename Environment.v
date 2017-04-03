
Add LoadPath "." as Top0.
Require Import Top0.Tactics.
Require Import Top0.Definitions.
Require Import Top0.Keys.
Require Import Coq.FSets.FSetInterface.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Program.Equality.
Require Import Top0.Axioms.
Require Import Top0.TypeLemmas.
Require Import Top0.AdditionalLemmas.
Require Import Top0.CorrectnessLemmas.
Require Import Top0.Heap.

Module STMapP := FMapFacts.Facts ST.
Module EMapP := FMapFacts.Facts E.
Module RMapP := FMapFacts.Facts R.
Module EProofs := Raw.Proofs.

Lemma E_same_key:
  forall t x v e, 
    E.find (elt := t) x (E.add x v e) = Some v.
Proof.
  intros. rewrite <- EMapP.find_mapsto_iff. rewrite -> EMapP.add_mapsto_iff.
  left. intuition. 
Qed.  

Lemma R_same_key:
  forall t x v e, 
    R.find (elt := t) x (R.add x v e) = Some v.
Proof.
  intros. rewrite <- RMapP.find_mapsto_iff. rewrite -> RMapP.add_mapsto_iff.
  left. intuition. 
Qed.  

Lemma E_diff_key_1:
  forall t a b v v' e,   
    a <> b ->
    E.find (elt := t) a (E.add b v e) = Some v' -> 
    E.find (elt := t) a e = Some v'.
Proof.
  intros. 
  rewrite <- EMapP.find_mapsto_iff in H0. rewrite -> EMapP.add_mapsto_iff in H0.
  destruct H0; destruct H0; [destruct H | rewrite -> EMapP.find_mapsto_iff in H1]; auto.
Qed.

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

Lemma E_diff_key_2:
  forall t a b v v' e,   
    b <> a ->
    E.find (elt := t) a e = Some v' ->
    E.find (elt := t) a (E.add b v e) = Some v'.
Proof.
  intros. 
  rewrite <- EMapP.find_mapsto_iff. rewrite -> EMapP.add_mapsto_iff.
  right; split; [exact H | now rewrite EMapP.find_mapsto_iff ].
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

Require Import Omega.

Lemma Raw_same_key:
  forall t x v e, 
    Raw.bst e ->
    Raw.find (elt := t) x (Raw.add x v e) = Some v.
Proof.
  intros. rewrite EProofs.add_find; auto.
  case_eq (AsciiVars.compare x x); intros; 
  now try repeat (unfold AsciiVars.lt in l; omega).
Qed.  

Lemma Raw_diff_key_1:
  forall t a b v v' e,
    Raw.bst e ->
    b <> a ->
    Raw.find (elt := t) a (Raw.add b v e) = Some v' -> 
    Raw.find (elt := t) a e = Some v'.
Proof.
  intros. 
  apply EProofs.find_1; auto.
  apply EProofs.find_2 in H1. now apply EProofs.add_3 in H1.
Qed.

Lemma Raw_diff_key_2:
  forall t a b v v' e,
    Raw.bst e ->
    b <> a ->
    Raw.find (elt := t) a e = Some v' ->
    Raw.find (elt := t) a (Raw.add b v e) = Some v'.
Proof.
  intros. apply EProofs.find_1; 
  [now apply EProofs.add_bst | apply EProofs.find_2 in H1; now apply EProofs.add_2 ].
Qed.


Lemma update_env:
  forall stty rho env ctxt, 
    TcEnv (stty, rho, env, ctxt) -> 
    (forall x v t, 
       TcVal (stty, v, subst_rho rho t) ->
       TcEnv (stty, rho, update_E (x, v) env, update_T (x, t) ctxt) ).
Proof. 
  intros stty rho env ctxt HEnv x v t HTc. 
  inversion_clear HEnv as [ stty' rho' env' ctxt' ? HE HT HV]. 
  apply TC_Env;
  unfold find_E, update_E, find_T, update_T in *; simpl.
  clear HTc.
  Case "env is a bst". now apply EProofs.add_bst.
  Case "TcEnv is well-typed: HE".  
    intros x0 v0 HF.
    destruct (AsciiVars.eq_dec x0 x) as [c | c]. 
    unfold AsciiVars.eq in c; intros.
    SCase "x0 = x". subst; exists t.
        now rewrite E_same_key. 
    SCase "x0 <> x". 
      eapply Raw_diff_key_1 in HF; auto.      
      destruct (HE x0 v0) as [t0 HU] ; [auto | ] ; exists t0.
      eapply E_diff_key_2 ; [ auto | exact HU]. 
  Case "TcEnv is well-typed: HT". 
    intros x0 t0 HF.
    destruct (AsciiVars.eq_dec x0 x) as [c | c]; 
    unfold AsciiVars.eq in c; intros; subst.  
    SCase "x0 = x". exists v.
        now rewrite Raw_same_key.
    SCase "x0 <> x". 
      eapply E_diff_key_1 in HF; auto.
      destruct (HT x0 t0) as [x1 ?] ; [auto | ].
      exists x1; [eapply Raw_diff_key_2]; auto.
  Case "Type preservation: HV". 
    intros x0 v0 t0 HFindE HFindT. 
    destruct (AsciiVars.eq_dec x0 x) as [c | c];
    unfold AsciiVars.eq in c; intros; subst.
    SCase "x0 = x".
      rewrite Raw_same_key in HFindE by assumption.
      inversion HFindE; subst.
      rewrite E_same_key in HFindT by assumption.
      inversion HFindT; subst. assumption.
    SCase "x0 <> x". 
      eapply Raw_diff_key_1 in HFindE; auto.
      eapply E_diff_key_1 in HFindT; auto.
      eapply HV; eauto.
Qed.


Lemma yyy :
  forall t r rho,
    R.In (elt:=t) r rho -> R.find (elt:=t) r rho <> None.
Proof.
  intros.
  apply RMapP.in_find_iff. auto.
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
  apply yyy.
  assumption.
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
  - eapply find_rho_1. eassumption. 
  - eapply find_rho_2; eassumption. 
  - contradict H. rewrite H. clear H. unfold R.In.  
    econstructor. simpl. econstructor. reflexivity.
  - apply find_rho_3.
    apply RMapP.not_find_in_iff.
    assumption.
Qed.

Lemma subst_rho_free_vars_union_1 :
  forall x (e1 e2 : Ensemble Name),
    not_set_elem (set_union e1 e2) x ->
    not_set_elem e1 x /\ not_set_elem e2 x.
Proof.
  intros. split; intro; apply H; [ apply Union_introl | apply Union_intror]; auto.
Qed.

Lemma subst_rho_free_vars_union_2 :
  forall x (e1 e2 : Ensemble Name),
    not_set_elem e1 x /\ not_set_elem e2 x ->
    not_set_elem (set_union e1 e2) x.
Proof.
  intros. destruct H. intro. destruct H1; [apply H | apply H0]; auto.
Qed.

Lemma fold_subst_rho_free_vars_rgn_aux:
  forall rho x,
    R.find (elt:=nat) x rho = None ->
    fold_subst_rgn rho (Rgn2_FVar true true x) =  (Rgn2_FVar true true x).
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
                            (Rgn2_FVar true true x))
    with
    (fold_subst_rgn {| R.this := this2; R.is_bst := H6 |}
                    (subst_rgn k (Rgn2_Const true false e)
                               (fold_subst_rgn {| R.this := this1; R.is_bst := H4 |} (Rgn2_FVar true true x)))
    ) by (unfold fold_subst_rgn, R.fold, R.Raw.fold in *; reflexivity).
    apply RMapP.not_find_in_iff in HNotIn1.
    assert (fold_subst_rgn {| R.this := this1; R.is_bst := H4 |}
                           (Rgn2_FVar true true x) = Rgn2_FVar true true x).
    eapply IHthis1; eauto. rewrite H.
    apply RMapP.not_find_in_iff in HNotIn2.
    assert (fold_subst_rgn {| R.this := this2; R.is_bst := H6 |}
                           (Rgn2_FVar true true x) = Rgn2_FVar true true x).
    eapply IHthis2; eauto.
    unfold subst_rgn. simpl.
    destruct (AsciiVars.eq_dec k x) as [c | c]; auto.
    inversion c; subst.
    contradiction.
Qed.

Lemma subst_rho_free_vars_rgn:
 forall rho x r,
   R.find (elt:=nat) x rho = None ->
   not_set_elem (free_rgn_vars_in_rgn2 (fold_subst_rgn rho r)) x ->
   not_set_elem (free_rgn_vars_in_rgn2 r) x.
Proof.
  intros rho x r HFind HNotElem.
  unfold rgn2_in_typ in r. dependent induction r. 
  - rewrite subst_rho_rgn_const in HNotElem. assumption.
  - assert ((exists v, fold_subst_rgn rho (Rgn2_FVar true true n) =  
                         Rgn2_Const true true v) \/ 
            fold_subst_rgn rho (Rgn2_FVar true true n) = Rgn2_FVar true true n) 
      by (apply subst_rho_fvar_1).
    destruct (subst_rho_fvar_1 rho n) as [[v H0] | H0]; simpl in *.
    + destruct (AsciiVars.eq_dec n x) as [c | c]; auto.
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

Axiom subst_rho_free_vars_eps:
  forall e rho x,
  R.find (elt:=nat) x rho = None ->  
  not_set_elem (free_rgn_vars_in_eps2 (fold_subst_eps rho e)) x ->
  not_set_elem (free_rgn_vars_in_eps2 e) x.

Lemma subst_rho_free_vars :
  forall t rho x,
    x # subst_rho rho t ->
    R.find (elt:=nat) x rho = None ->
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

Lemma not_set_elem_not_in_rho: forall rho rgns x,
                                 TcRho (rho, rgns) ->
                                 not_set_elem rgns x ->
                                 ~ R.In (elt:=Region) x rho.
Proof.
  intros rho rgns  x HRho H .
  inversion_clear HRho as [rho' rgns' HRgn' HVal''].
  unfold not_set_elem in H. unfold Ensembles.Complement in H.
  intro. 
  apply RMapP.in_find_iff in H0.
  eapply HRgn' in H0. contradiction.
Qed.

Lemma update_rho: forall rho rgns x v,
                    TcRho (rho, rgns) ->
                    not_set_elem rgns x ->
                    TcRho (update_R (x, v) rho, set_union rgns (singleton_set x)).
Proof.
  intros rho rgns x v HRho HFresh.
  unfold update_R; simpl. 
  econstructor.  
  intro r. split.
  - inversion_clear HRho as [rho' rgns' HRgn'  HRho''].
    destruct (AsciiVars.eq_dec x r) as [c | c].
    + unfold AsciiVars.eq in c; intros; subst.
      unfold set_elem, set_union, singleton_set.
      apply Ensembles.Union_intror.
      apply Ensembles.In_singleton.
    + destruct (HRgn' r).
      intro. 
      apply H0 in H. 
      * eapply R_diff_key_3 in H1; auto.  
        apply Ensembles.Union_introl. 
        apply HRgn'. assumption.
      * eapply R_diff_key_3 in H1; auto.  
  - inversion_clear HRho as [rho' rgns' HRgn'  HRho''].
    destruct (AsciiVars.eq_dec x r) as [c | c].
    + unfold AsciiVars.eq in c; intros; subst.
      apply RMapP.in_find_iff. apply RMapP.add_in_iff. intuition.
    + destruct (HRgn' r).
      intro. apply H0 in H. 
      * rewrite <- RMapP.in_find_iff.  rewrite RMapP.add_in_iff.
        right. rewrite RMapP.in_find_iff. 
        assumption.
      * destruct H1; [apply H0; assumption | inversion H1; subst; intuition]. 
Qed.

Lemma NotFreeInEmptyEps:
  forall x,
    ~ free_rgn_vars_in_eps2 (Empty_set StaticAction) x.
Proof.
  intro x. intro. 
  unfold free_rgn_vars_in_eps2, empty_set in H.
  destruct H as [sa]. destruct H.
  inversion H.
Qed.

Lemma ExtendedTcInv:
  forall ctxt rgns f x tyx effe tyc effc, 
    TcInc (ctxt, rgns)->
    find_T x ctxt = Some tyx ->
    find_T f ctxt = Some (Ty2_Arrow tyx effc tyc effe Ty2_Effect) ->
    TcInc (update_rec_T (f, Ty2_Arrow tyx effc tyc effe Ty2_Effect) (x, tyx) ctxt, rgns).
Proof.
  intros ctxt rgns f x tyx effe tyc effc HInc HFind1 HFind2.
  inversion HInc as [? ? HFrv]; subst.
  econstructor. 
  intros. apply HFrv with (x:=x0). 
  unfold update_rec_T in H; simpl in H.
  destruct (AsciiVars.eq_dec x0 x) as [c | c].
  - inversion c; subst.
    unfold find_T in H.
    rewrite E_same_key in H.
    inversion H; subst.
    assumption.
  - unfold AsciiVars.eq in c.  
    eapply E_diff_key_1 in H; eauto.
    destruct (AsciiVars.eq_dec x0 f) as [d | d].
    + inversion d; subst.
      rewrite E_same_key in H.
      inversion H; subst.
      assumption.
    + eapply E_diff_key_1 in H; eauto.
Qed.

Lemma EmptyUnionisEmptySet_Name_Left :
  forall acts,
    Union Name (Empty_set Name) acts = acts.
Proof.
  intros acts;
  apply Extensionality_Ensembles;
  unfold Same_set, Included;
  split.
  - intros x Hx. unfold In in *. destruct Hx; auto. inversion H.
  - intros x Hx. apply Union_intror. assumption.
Qed. 

Lemma EmptyUnionisEmptySet_Name_Right :
  forall acts,
    Union Name acts (Empty_set Name) = acts.
Proof.
  intros acts;
  apply Extensionality_Ensembles;
  unfold Same_set, Included;
  split.
  - intros x Hx. unfold In in *. destruct Hx; auto. inversion H.
  - intros x Hx. apply Union_introl. assumption.
Qed. 

Lemma IncludedRemoveSingleton:
  forall n x rgns,
    n <> x ->
    included (singleton_set n) (Union Name rgns (singleton_set x)) ->
    included (singleton_set n) rgns.
Proof.
  intros n x rgns H1 H2.
  unfold included, Included, In in *. 
  intro. intro.  destruct (H2 x0); auto.  
  inversion H; subst. 
  contradict H0. intro. inversion H0. 
  apply H1. symmetry. assumption.
Qed.

Lemma IncludedUnion_Name_1:
  forall (a b : Ensemble Name) rgns,
    included (set_union a b) rgns ->
    included a rgns /\
    included b rgns.
Proof.
  intros.
  split.
  - intro. intro. apply H.
    apply Union_introl. assumption.
  - intro. intro. apply H.
    + apply Union_intror. assumption.
Qed.

Lemma IncludedUnion_Name_2:
  forall (a b c d : Ensemble Name) rgns,
    included (set_union a (set_union b c))
             (set_union rgns d) ->
    included (set_union a b)
             (set_union rgns d) /\
    included (set_union a c)
             (set_union rgns d).
Proof.
  intros.
  split.
  - intro. intro. apply H.
    unfold In, set_union in *.
    inversion H0; subst.
    + apply Union_introl. assumption.
    + apply Union_intror. apply Union_introl. assumption.
  - intro. intro. apply H.
    unfold In, set_union in *.
    inversion H0; subst.
    + apply Union_introl. assumption.
    + apply Union_intror. apply Union_intror. assumption.    
Qed.

Lemma IncludedUnion_Name_5:
  forall (a b c : Ensemble Name) rgns,
    included (set_union a b)
             (set_union rgns c) ->
    included a (set_union rgns c) /\
    included b (set_union rgns c).
Proof.
  intros.
  split.
  - intro. intro. apply H.
    apply Union_introl. assumption.
  - intro. intro. apply H.
    apply Union_intror. assumption.    
Qed.


Lemma IncludedUnion_Name_3:
  forall (a b c : Ensemble Name) rgns,
    included (set_union a b) rgns /\
    included (set_union a c) rgns ->
    included (set_union a (set_union b c)) rgns.
Proof.
  intros. 
  intro. intro. unfold In, set_union in *.
  destruct H.
  apply IncludedUnion_Name_1 in H. destruct H.
  apply IncludedUnion_Name_1 in H1. destruct H1.
  repeat destruct H0; [apply H | apply H2 | apply H3]; assumption. 
Qed.

Lemma IncludedUnion_Name_4:
  forall (a b c : Ensemble Name) rgns,
    included (set_union a b) rgns /\
    included (set_union a c) rgns ->
    included (set_union a (set_union c b)) rgns.
Proof.
  intros. 
  intro. intro. unfold In, set_union in *.
  destruct H.
  apply IncludedUnion_Name_1 in H. destruct H.
  apply IncludedUnion_Name_1 in H1. destruct H1.
  repeat destruct H0; [apply H1 | apply H3 | apply H2]; assumption. 
Qed.

Lemma IncludedUnion_Static_Action_4:
  forall (a b : Ensemble StaticAction2) (rgns : Ensemble Name) (x : Name),
    (free_rgn_vars_in_eps2 a x -> rgns x) ->
    (free_rgn_vars_in_eps2 b x -> rgns x) ->                        
    (free_rgn_vars_in_eps2 (Union_Static_Action a b) x -> rgns x).
Proof.
  intros a b rgns x H1 H2 H3.
  unfold free_rgn_vars_in_eps2 in *.
  destruct H3 as [sa [H4 H5]].
  destruct H4; [apply H1 | apply H2]; exists x0; auto.
Qed.


Lemma IncludedUnion_Name_6:
  forall (a b: Ensemble Name) rgns,
    included a rgns /\
    included b rgns ->
    included (set_union a b) rgns.
Proof.
  intros. 
  intro. intro. unfold In, set_union in *.
  destruct H0; destruct H; [apply H | apply H1]; assumption. 
Qed.

Lemma RegionAbsFrv_2:
  forall  x r rgns n,
    included (free_rgn_vars_in_rgn2 r) (set_union rgns (singleton_set x)) ->
    included (free_rgn_vars_in_rgn2 (closing_rgn_in_rgn2 n x r)) rgns.
Proof.
  intros. unfold rgn2_in_typ in r. 
  dependent induction r; simpl in *; do 2 intro.
  - inversion H0.
  - destruct (RMapProp.F.eq_dec n x); subst.
    + simpl in *. inversion H0.
    + apply IncludedRemoveSingleton in H; auto.
  - inversion H0.
Qed. 

Lemma NoFreeVarsAfterClosingRgn:
  forall n x r,
    ~ free_rgn_vars_in_rgn2 (closing_rgn_in_rgn2 n x r) x.
Proof.
  intros n x r.
  unfold rgn2_in_typ in r. dependent induction r; intro;
  unfold free_rgn_vars_in_rgn2, closing_rgn_in_rgn2 in H.
  - inversion H.
  - destruct (RMapProp.F.eq_dec n0 x); subst.
    + inversion H.
    + inversion H. apply n1. assumption.
  - inversion H.
Qed.

Lemma NoFreeVarsAfterClosingSa:
 forall n sa x,
   ~ free_rgn_vars_in_sa2 (closing_rgn_in_sa2 n x sa) x.
Proof.
  intros n sa x. intro.
  induction sa;
  unfold free_rgn_vars_in_sa2, closing_rgn_in_sa2 in H; 
  eapply NoFreeVarsAfterClosingRgn; eauto.
Qed.

Lemma RegionAbsFrv_1:
   forall effr rgns (x : Name) n, 
     included (free_rgn_vars_in_eps2 effr) (set_union rgns (singleton_set x)) ->
     included (free_rgn_vars_in_eps2 (closing_rgn_in_eps2 n x effr)) rgns.
Proof.
  intros effr rgns x n H.
  unfold free_rgn_vars_in_eps2 in *.
  do 2 intro. unfold In in *.
  destruct H0 as [sa [H1 H2]].
  unfold closing_rgn_in_eps2 in H1.
  destruct H1 as [sa' [H3 H4]].
  rewrite <- H4 in H2. 
  unfold included, Included, In in H.
  destruct (H x0); auto.
  - exists sa'. intuition.
    destruct (RMapProp.F.eq_dec x x0); subst.
    + contradict H2. apply NoFreeVarsAfterClosingSa.
    + induction sa'; unfold rgn2_in_typ in r; dependent induction r; 
      simpl in *; unfold free_rgn_vars_in_rgn2 in *;
      try (solve [inversion H2 | destruct  (RMapProp.F.eq_dec n0 x); subst; [inversion H2 | assumption]]).
  - destruct (RMapProp.F.eq_dec x x0); subst.
    + contradict H2. apply NoFreeVarsAfterClosingSa.
    + exfalso. contradict n0. inversion H0. auto.
Qed.

Lemma RegionAbsFrv_3:
   forall tyr rgns (x : Name), 
     included (frv tyr) (set_union rgns (singleton_set x)) ->
     included (frv (close_var x tyr)) rgns. 
Proof.
  intros tyr rgns x H.
  unfold close_var.
  generalize 0.
  dependent induction tyr; simpl in *; intro;
  try (solve [intro; intro; inversion H0]).
  - unfold included, Included, In in *. 
    intro. intro.  
    destruct H0.
    + eapply IHtyr1; auto. 
      intro. intro. apply H.
      apply Union_introl. assumption. eassumption.
    + eapply IHtyr2; auto.
      intro. intro. apply H.
      apply Union_intror. assumption. eassumption.
  - apply IncludedUnion_Name_6.
    split.
    + apply IncludedUnion_Name_1 in H. destruct H. clear H0. 
      apply RegionAbsFrv_2; eauto.
    + eapply IHtyr.
      do 2 intro. apply H.
       apply Union_intror. assumption.
  - repeat (apply IncludedUnion_Name_4; split); 
    apply IncludedUnion_Name_6; split;
    try (solve [apply IHtyr1; do 2 intro; apply H; apply Union_introl; assumption]).
    + apply IHtyr3. intro. intro.
      apply H.
      apply Union_intror. apply Union_intror. apply Union_intror. assumption. 
    + apply IHtyr2. intro. intro.
      apply H.
      apply Union_intror. apply Union_intror. apply Union_introl. assumption. 
    + apply IncludedUnion_Name_5 in H; destruct H as [H1  H]. clear H1.
      apply IncludedUnion_Name_5 in H; destruct H as [H  H1]. clear H1.
      apply IncludedUnion_Name_5 in H; destruct H as [H1  H]. clear H1.
      eapply RegionAbsFrv_1; eauto.
    + apply IncludedUnion_Name_5 in H; destruct H as [H1  H]. clear H1.
      apply IncludedUnion_Name_5 in H; destruct H as [H  H1]. clear H1.
      apply IncludedUnion_Name_5 in H; destruct H as [H  H1]. clear H1.
      eapply RegionAbsFrv_1; eauto.
  - apply IncludedUnion_Name_6.
    split.
    + apply IncludedUnion_Name_1 in H. destruct H. clear H0.
      eapply RegionAbsFrv_1; eauto.
    + apply IHtyr.
      do 2 intro.
      apply H. apply Union_intror. assumption. 
Qed.  

Lemma RegionAppFrv_2:
  forall region r x n,
    lc_type_rgn r ->
    free_rgn_vars_in_rgn2 (opening_rgn_in_rgn2 n region r) x ->
    free_rgn_vars_in_rgn2 r x.
Proof.
  intros.
  unfold rgn2_in_typ in r.
  dependent induction r; simpl in *.
  - inversion H0.
  - assumption.
  - inversion H.
Qed.

Lemma RegionAppFrv_3:
  forall region e x n,
    lc_type_eps e ->
    free_rgn_vars_in_eps2 (opening_rgn_in_eps2 n region e) x ->
    free_rgn_vars_in_eps2 e x.
Proof.
  intros region e x n H1 H2.
  inversion H1; subst.
  unfold free_rgn_vars_in_eps2 in *.
  destruct H2 as [sa [H3 H4]].
  destruct (H sa).
  exists sa. auto.
Qed.

Lemma RegionAppFrv_1:
  forall tyr rgns w,
    lc_type tyr ->
    included (frv tyr) rgns ->
    included (frv (open (mk_rgn_type w) tyr)) rgns.
Proof.
  intros tyr rgns w Hlc H.
  unfold open.
  generalize 0.
  unfold rgn2_in_exp in w; intro.
  dependent induction w; simpl.
  - dependent induction tyr; simpl in *;
    inversion Hlc; subst;
    try (solve [do 2 intro; inversion H | do 2 intro; inversion H0]).
    + apply IncludedUnion_Name_6.
      split; [apply IHtyr1 |  apply IHtyr2]; auto.
      * do 2 intro. apply H; simpl.
        apply Union_introl. assumption.
      * do 2 intro. apply H; simpl.
        apply Union_intror. assumption. 
    + apply IncludedUnion_Name_6.
      split.
      * do 2 intro. apply H; simpl.
        apply Union_introl. unfold In in *. 
        eapply RegionAppFrv_2; eauto.
      * apply IHtyr; auto. do 2 intro. 
        apply H; simpl.
        apply Union_intror. assumption. 
    + apply IncludedUnion_Name_6. 
      split; [apply IHtyr1; auto; do 2 intro; apply H; simpl; apply Union_introl; assumption |].
      apply IncludedUnion_Name_6.
      split; [apply IncludedUnion_Name_6; split | apply IncludedUnion_Name_6; split].
      * do 2 intro. apply H; simpl. 
        apply Union_intror. apply Union_introl. apply Union_introl.
        unfold In in *.
        eapply RegionAppFrv_3; eauto.
      * do 2 intro. apply H; simpl. 
        apply Union_intror. apply Union_introl. apply Union_intror.
        unfold In in *.
        eapply RegionAppFrv_3; eauto.
      * apply IHtyr2; auto; do 2 intro; apply H; simpl. 
        apply Union_intror; apply Union_intror. apply Union_introl. assumption.
      * apply IHtyr3; auto; do 2 intro; apply H; simpl. 
        apply Union_intror; apply Union_intror. apply Union_intror. assumption.
    + apply IncludedUnion_Name_6. 
      split; [| apply IHtyr; auto; do 2 intro; apply H; simpl; apply Union_intror; assumption].
      do 2 intro. apply H; simpl in *.
      apply Union_introl.  unfold In in *.
      eapply RegionAppFrv_3; eauto.
  - dependent induction tyr; simpl;
    inversion Hlc; subst;
    try (solve [do 2 intro; inversion H0]).
    + apply IncludedUnion_Name_6.
      split; [apply IHtyr1 |  apply IHtyr2]; auto.
      * do 2 intro. apply H; simpl.
        apply Union_introl. assumption.
      * do 2 intro. apply H; simpl.
        apply Union_intror. assumption. 
    + apply IncludedUnion_Name_6.
      split.
      * do 2 intro. apply H; simpl.
        apply Union_introl. unfold In in *. 
        eapply RegionAppFrv_2; eauto.
      * apply IHtyr; auto. do 2 intro. 
        apply H; simpl.
        apply Union_intror. assumption. 
    + apply IncludedUnion_Name_6. 
      split; [apply IHtyr1; auto; do 2 intro; apply H; simpl; apply Union_introl; assumption |].
      apply IncludedUnion_Name_6.
      split; [apply IncludedUnion_Name_6; split | apply IncludedUnion_Name_6; split].
      * do 2 intro. apply H; simpl. 
        apply Union_intror. apply Union_introl. apply Union_introl.
        unfold In in *.
        eapply RegionAppFrv_3; eauto.
      * do 2 intro. apply H; simpl. 
        apply Union_intror. apply Union_introl. apply Union_intror.
        unfold In in *.
        eapply RegionAppFrv_3; eauto.
      * apply IHtyr2; auto; do 2 intro; apply H; simpl. 
        apply Union_intror; apply Union_intror. apply Union_introl. assumption.
      * apply IHtyr3; auto; do 2 intro; apply H; simpl. 
        apply Union_intror; apply Union_intror. apply Union_intror. assumption.
    + apply IncludedUnion_Name_6. 
      split; [| apply IHtyr; auto; do 2 intro; apply H; simpl; apply Union_intror; assumption].
      do 2 intro. apply H; simpl in *.
      apply Union_introl.  unfold In in *.
      eapply RegionAppFrv_3; eauto.
Qed.

Lemma TypedExpressionFrv :
  forall ctxt rgns e t eff,
  TcInc (ctxt, rgns) ->
  TcExp (ctxt, rgns, e, t, eff) ->
  included (frv t) rgns /\ included (free_rgn_vars_in_eps2 eff) rgns.
Proof. 
  intros ctxt rgns e t eff HInc HExp.  
  generalize dependent HInc.  
  dependent induction HExp;
  intros HInc; unfold included, Included, In;
  try (solve [intuition; [inversion H | contradict H; apply NotFreeInEmptyEps] ]). 
  - inversion HInc as [? ? HFrv]; subst.
    intuition; eapply HFrv; eauto. contradict H0; apply NotFreeInEmptyEps.
  - inversion HInc as [? ? HFrv]; subst.
    assert (H' : included (frv tyc) rgns /\ included (free_rgn_vars_in_eps2 effc) rgns).
    { eapply IHHExp1; eauto; apply ExtendedTcInv; eauto. }
   
    { assert (H'' : included (frv Ty2_Effect) rgns /\ 
                    included (free_rgn_vars_in_eps2 effe) rgns).
      eapply IHHExp2; eauto.
      - apply ExtendedTcInv; eauto.
      - split.
        + intro. intro.
          eapply HFrv; eauto.
        + intro. intro. contradict H2. apply NotFreeInEmptyEps. }
  - inversion HInc as [? ? HFrv]; subst.
    assert (H' : included (frv tyr) (set_union rgns (singleton_set x)) /\ 
                 included (free_rgn_vars_in_eps2 effr) (set_union rgns (singleton_set x))).
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
  - assert (H' : included (frv (Ty2_Arrow tya effc t effe Ty2_Effect)) rgns /\ 
                 included (free_rgn_vars_in_eps2 efff) rgns) by (eapply IHHExp1; eauto).
    assert (H'' : included (frv tya) rgns /\ 
                  included (free_rgn_vars_in_eps2 effa) rgns) by (eapply IHHExp2; eauto).
    destruct H' as [H2 H3].
    destruct H'' as [H4 H5].
    split.
    + replace (forall x : Name, frv t x -> rgns x)
      with (included (frv t) rgns) by (unfold included, Included, In; reflexivity).
      assumption.
    + intro. apply IncludedUnion_Static_Action_4; [apply IncludedUnion_Static_Action_4 |].
      * apply H3.
      * apply H5.
      * apply H1.
  - inversion HInc as [? ? HFrv]; subst.
    assert (H' : included (frv (Ty2_ForallRgn effr tyr)) rgns /\ 
                 included (free_rgn_vars_in_eps2 efff) rgns).
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
    assert (H' : included (frv ( Ty2_Arrow tya effc tyc effe Ty2_Effect)) rgns /\ 
                 included (free_rgn_vars_in_eps2 efff) rgns).
    eapply IHHExp1; eauto.
    assert (H'' : included (frv tya) rgns /\ 
                  included (free_rgn_vars_in_eps2 effa) rgns).
    eapply IHHExp2; eauto.
    destruct H' as [H1 H2].
    destruct H'' as [H3 H4].
    split.
    + do 2 intro. inversion H0.
    + intro. apply IncludedUnion_Static_Action_4; [apply IncludedUnion_Static_Action_4 |].
      * apply H2.
      * apply H4. 
      * apply H. 
  - assert (H1 : included (frv ty1) rgns /\ included (free_rgn_vars_in_eps2 eff1) rgns)
      by (eapply IHHExp1; eauto).
    assert (H2 : included (frv ty2) rgns /\ included (free_rgn_vars_in_eps2 eff2) rgns)
      by (eapply IHHExp2; eauto).
    assert (H3 : included (frv ty3) rgns /\ included (free_rgn_vars_in_eps2 eff3) rgns)
      by (eapply IHHExp3; eauto).
    assert (H4 : included (frv ty4) rgns /\ included (free_rgn_vars_in_eps2 eff4) rgns)
      by (eapply IHHExp4; eauto).
    split.
    + do 2 intro. simpl in H.
      destruct H.
      * destruct H1. apply H0. assumption.
      * destruct H2. apply H0. assumption.
    + intro. apply IncludedUnion_Static_Action_4; 
             [apply IncludedUnion_Static_Action_4; [apply IncludedUnion_Static_Action_4 |] |];
             [destruct H3 | destruct H4 | destruct H2 | destruct H1]; apply H0. 
  - assert (H1 : included (frv t0) rgns /\ included (free_rgn_vars_in_eps2 veff) rgns)
      by (eapply IHHExp; eauto).
    destruct H1 as [H2 H3].
    split.
    + do 2 intro. simpl in H.
      rewrite EmptyUnionisEmptySet_Name_Left in H.
      apply H2. assumption.
    + intro. apply IncludedUnion_Static_Action_4; [apply H3 |].
      simpl. apply H0. 
  - assert (H2 : included (frv (Ty2_Ref (mk_rgn_type (Rgn2_Const true false s)) t)) rgns /\ 
                 included (free_rgn_vars_in_eps2 aeff) rgns)
      by (eapply IHHExp; eauto).
    destruct H2 as [H3 H4].
    split.
    + do 2 intro. apply H3; simpl.
      apply Union_intror. assumption.
    + intro. apply IncludedUnion_Static_Action_4; [apply H4 |].
      simpl. apply H1.
  - assert (H2 : included (frv (Ty2_Ref (mk_rgn_type (Rgn2_Const true false s)) t0)) rgns /\ 
                 included (free_rgn_vars_in_eps2 aeff) rgns)
      by (eapply IHHExp1; eauto).
    assert (H3 : included (frv t0) rgns /\ 
                 included (free_rgn_vars_in_eps2 veff) rgns)
      by (eapply IHHExp2; eauto).
     destruct H2 as [H4 H5].
     destruct H3 as [H6 H7].
     split.
     + do 2 intro. inversion H.
     + intro.  apply IncludedUnion_Static_Action_4; [ apply IncludedUnion_Static_Action_4  |].
       * apply H5.
       * apply H7. 
       * simpl. apply H1. 
  - assert (H1 : included (frv Ty2_Boolean) rgns /\ 
                 included (free_rgn_vars_in_eps2 eff0) rgns)
      by (eapply IHHExp1; eauto).
    assert (H2 : included (frv t) rgns /\ 
                 included (free_rgn_vars_in_eps2 eff1) rgns)
      by (eapply IHHExp2; eauto).
    assert (H3 : included (frv t) rgns /\ 
                 included (free_rgn_vars_in_eps2 eff2) rgns)
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
  - assert (H1 : included (frv Ty2_Natural) rgns /\ 
                 included (free_rgn_vars_in_eps2 eff1) rgns)
      by (eapply IHHExp1; eauto).
    assert (H2 : included (frv Ty2_Natural) rgns /\ 
                 included (free_rgn_vars_in_eps2 eff2) rgns)
      by (eapply IHHExp2; eauto).
    destruct H1 as [H3 H4].
    destruct H2 as [H5 H6].
    split.
    + do 2 intro. apply H3. assumption.
    + intro. apply IncludedUnion_Static_Action_4; [apply H4 | apply H6].
  - assert (H1 : included (frv Ty2_Natural) rgns /\ 
                 included (free_rgn_vars_in_eps2 eff1) rgns)
      by (eapply IHHExp1; eauto).
    assert (H2 : included (frv Ty2_Natural) rgns /\ 
                 included (free_rgn_vars_in_eps2 eff2) rgns)
      by (eapply IHHExp2; eauto).
    destruct H1 as [H3 H4].
    destruct H2 as [H5 H6].
    split.
    + do 2 intro. apply H3. assumption.
    + intro. apply IncludedUnion_Static_Action_4; [apply H4 | apply H6].
  - assert (H1 : included (frv Ty2_Natural) rgns /\ 
                 included (free_rgn_vars_in_eps2 eff1) rgns)
      by (eapply IHHExp1; eauto).
    assert (H2 : included (frv Ty2_Natural) rgns /\ 
                 included (free_rgn_vars_in_eps2 eff2) rgns)
      by (eapply IHHExp2; eauto).
    destruct H1 as [H3 H4].
    destruct H2 as [H5 H6].
    split.
    + do 2 intro. apply H3. assumption.
    + intro. apply IncludedUnion_Static_Action_4; [apply H4 | apply H6].
  - assert (H1 : included (frv Ty2_Natural) rgns /\ 
                 included (free_rgn_vars_in_eps2 eff1) rgns)
      by (eapply IHHExp1; eauto).
    assert (H2 : included (frv Ty2_Natural) rgns /\ 
                 included (free_rgn_vars_in_eps2 eff2) rgns)
      by (eapply IHHExp2; eauto).
    destruct H1 as [H3 H4].
    destruct H2 as [H5 H6].
    split.
    + do 2 intro. apply H3. assumption.
    + intro. apply IncludedUnion_Static_Action_4; [apply H4 | apply H6].
  - assert (H1 : included (frv (Ty2_Ref (Rgn2_Const true true r) t0)) rgns /\ 
                 included (free_rgn_vars_in_eps2 eff) rgns)
      by (eapply IHHExp; eauto).
    destruct H1 as [H2 H3].
    intuition. inversion H.
  - assert (H1 : included (frv (Ty2_Ref (Rgn2_Const true true r) t0)) rgns /\ 
                 included (free_rgn_vars_in_eps2 eff) rgns)
      by (eapply IHHExp; eauto).
    destruct H1 as [H2 H3].
    intuition. inversion H.
  - assert (H1 : included (frv Ty2_Effect) rgns /\ 
                 included (free_rgn_vars_in_eps2 eff1) rgns)
      by (eapply IHHExp1; eauto).
    assert (H2 : included (frv Ty2_Effect) rgns /\ 
                 included (free_rgn_vars_in_eps2 eff2) rgns)
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
               assert (R.find (elt:=nat) x0 rho = None) 
                 by (eapply contrapositiveTcRho; eauto; apply HRgn);
               rewrite  SUBST_FRESH; [rewrite <- x; econstructor; eauto | 
                                      eapply subst_rho_free_vars; eauto]  ] ).
Qed.

Lemma extended_rho : forall stty rho env ctxt,
                       TcEnv (stty, rho, env, ctxt) ->
                       forall x r rgns,
                         TcRho (rho, rgns) ->
                         not_set_elem rgns x -> 
                         TcEnv (stty, update_R (x, r) rho, env, ctxt). 
Proof.
  intros stty rho env ctxt HEnv x r rgns HRho HRgns. 
  inversion_clear HEnv as [ stty' rho' env' ctxt' ? HE HT HV]. 
  inversion_clear HRho as [rho' rgns' HRgn' HVal''].
  constructor; auto.
  intros x0 v0 t0 HE' HT'. eapply HV in HE'; eauto. unfold update_R. simpl.
  rewrite subst_add_comm. 
  - eapply subst_rho_fresh_var; eauto. econstructor; auto. 
  - unfold not_set_elem in HRgns. unfold Ensembles.Complement in HRgns.
    intro. 
    apply RMapP.in_find_iff in H0.
    eapply HRgn' in H0. contradiction.
Qed.