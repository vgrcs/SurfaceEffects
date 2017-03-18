
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
    ~ R.find (elt:=nat) x {| R.this := R.Raw.Node this1 k e this2 t0; R.is_bst := He |} = Some e.
Proof.
  intros; repeat split; 
  try (intro; apply H; apply RMapP.in_find_iff in H0; apply RMapP.in_find_iff; 
                               contradict H0). 
  - eapply find_rho_1; eassumption. 
  - eapply find_rho_2; eassumption. 
  - apply find_rho_3.
    apply RMapP.not_find_in_iff.
    assumption.
Qed.

Lemma subst_rho_free_vars :
  forall x rho t,
    x # subst_rho rho t ->
    R.find (elt:=nat) x rho = None ->
    x # t.
Proof.
  intros. 
  apply RMapP.not_find_in_iff in H0. 
  unfold not_set_elem in *. unfold Ensembles.Complement in *. 
  destruct rho; induction this.
  - unfold subst_rho, R.fold, R.Raw.fold in *; simpl in *; auto.
  - inversion is_bst; subst.  
    replace 
      (subst_rho {| R.this := R.Raw.Node this1 k e this2 t0; R.is_bst := is_bst |} t)
    with (subst_rho {| R.this := this2; R.is_bst := H7 |} 
                    (subst_in_type k e (subst_rho {| R.this := this1; R.is_bst := H5 |} t)))
      in * by (unfold subst_rho, R.fold, R.Raw.fold in *; simpl; reflexivity).
    
    unfold In in *. 
    eapply not_in_raw_rho in H0; eauto. destruct H0. 
    apply not_frv_in_subst_rho in H. destruct H.
    + apply IHthis1 with (is_bst:=H5); auto. 
    + destruct H.  
      * destruct H1. apply H.
        contradict H2. rewrite <- H2.
        apply RMapP.find_mapsto_iff. econstructor. reflexivity.
      * destruct H1. apply IHthis2 with (is_bst:=H7); auto. 
    Unshelve. auto. auto.
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

Lemma EmptySetImpliesFalse_1:
  forall (sa : Name), 
    empty_set sa -> False.
Proof.
  intro. intro. inversion H.
Qed.

Lemma EmptySetImpliesFalse_2:
  forall (sa : StaticAction2), 
    empty_set sa -> False.
Proof.
  intro. intro. inversion H.
Qed.

Lemma NotFreeInEmptyEps:
  forall x,
    ~ free_rgn_vars_in_eps2 (Empty_set StaticAction) x.
Proof.
  intro x. intro. 
  unfold free_rgn_vars_in_eps2, empty_set in H.
  destruct H as [sa]. destruct H.
  contradict H. reflexivity.
Qed.

Lemma TypedExpressionFrv :
  forall stty rho env ctxt rgns e t eff,
  TcEnv (stty, rho, env, ctxt) ->
  (forall x t, 
     find_T x ctxt = Some t ->
     included (frv t) rgns) ->
  TcExp (ctxt, rgns, e, t, eff) ->
  included (frv t) rgns /\ included (free_rgn_vars_in_eps2 eff) rgns.
Proof. 
  intros stty rho env ctxt rgns e t eff HEnv HNew HExp.  
  generalize dependent stty.
  generalize dependent env.
  generalize dependent rho.  
  generalize dependent HNew.  
  dependent induction HExp;
    intros HFrv rho env stty TcEnv; 
    unfold included, Included, In;
  try (solve [intuition; [inversion H | contradict H; apply NotFreeInEmptyEps] ]). 
  - intuition; eapply HFrv; eauto. contradict H0; apply NotFreeInEmptyEps.
  - assert (H' : included (frv tyc) rgns /\ included (free_rgn_vars_in_eps2 effc) rgns).
    { eapply IHHExp1; eauto.
      - intros. eapply HFrv with (x:=x0); eauto. admit.
      - eapply update_env. simpl.  
        + eapply update_env; eauto.
          inversion TcEnv as [? ? ? ? ? FindE_T FindT_E FindET_TcVal]; subst. 
          eapply FindET_TcVal. admit. admit.
        + inversion TcEnv as [? ? ? ? ? FindE_T FindT_E FindET_TcVal]; subst. 
          eapply FindET_TcVal. admit. admit. }
    assert (H'' : included (frv Ty2_Effect) rgns /\ 
                  included (free_rgn_vars_in_eps2 effe) rgns).
    { eapply IHHExp2; eauto.
      - intros. admit.
      -  eapply update_env. simpl.  
        + eapply update_env; eauto.
          inversion TcEnv as [? ? ? ? ? FindE_T FindT_E FindET_TcVal]; subst. 
          eapply FindET_TcVal. admit. admit.
        + inversion TcEnv as [? ? ? ? ? FindE_T FindT_E FindET_TcVal]; subst. 
          eapply FindET_TcVal. admit. admit. } 
    split.
    + intro. intro.
      destruct H1.
      * inversion H0; subst. apply H6; auto.
      * intuition. 
        { do 2 destruct H1.
          - apply H3; auto.
          - apply H5; auto.
          - apply H2; auto.
          - apply H4; auto. }  
    + intro. intro. contradict H1. apply NotFreeInEmptyEps.
  -
Admitted.

Theorem TcVal_implies_closed :
  forall stty v t,
    TcVal (stty, v, t) ->
    (forall r, r # t).
Proof.
  intros stty v t  HTcVal.
  dependent induction HTcVal; intros;
  try ( solve [ unfold not_set_elem, Complement; simpl;
                intro; unfold Ensembles.In, empty_set in H; contradiction] ).
  - unfold not_set_elem, Complement; simpl.
    intro. destruct H1; [contradiction |contradict H1; apply H0].
  - assert (forall t, included (frv t) rgns) by admit.
    eapply TypedExpressionFrv in H1; eauto.  
    eapply TcRhoIncludedNoFreeVars; eauto.
  - unfold not_set_elem, Complement; simpl. 
    intro. destruct H; contradict H; [eapply IHHTcVal1 | eapply IHHTcVal2]; eauto.
Admitted.  

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