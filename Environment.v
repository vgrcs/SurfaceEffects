
Add LoadPath "." as Top0.
Require Import Top0.Tactics.
Require Import Top0.Definitions.
Require Import Top0.Keys.
Require Import Coq.FSets.FSetInterface.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Program.Equality.
Require Import Top0.Axioms.

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

Lemma zzz:
  forall {A} x,
    x <> None <-> exists a : A, x = Some a.
Proof.
  intuition.
  - destruct x.
    + exists a. reflexivity.
    + contradict H. reflexivity.
  - subst. destruct H. inversion H.          
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
    eapply not_in_raw_rho in H0; eauto. 
    
    destruct H0;
    eapply not_frv_in_subst_rho in H; eauto;
    destruct H. destruct H2.
    apply IHthis1 with (is_bst:=H5); auto. 

    Unshelve. auto. auto.
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
  inversion_clear HTcRho as [rho' rgns' HRgn HVal''].
  - unfold subst_in_type. 
    rewrite  SUBST_FRESH. rewrite <- x. constructor.
    assert (R.find (elt:=nat) x0 rho = None).    
    eapply contrapositiveTcRho; eauto.
    eapply subst_rho_free_vars; eauto.
  - unfold subst_in_type. 
    rewrite  SUBST_FRESH. rewrite <- x. constructor.
    assert (R.find (elt:=nat) x0 rho = None).    
    eapply contrapositiveTcRho; eauto.
    eapply subst_rho_free_vars; eauto.
  - unfold subst_in_type. 
    rewrite  SUBST_FRESH. rewrite <- x. constructor.
    assumption. assumption.
    assert (R.find (elt:=nat) x0 rho = None).    
    eapply contrapositiveTcRho; eauto. 
    eapply subst_rho_free_vars; eauto.
  - unfold subst_in_type. 
    rewrite  SUBST_FRESH. rewrite <- x. econstructor; eauto.
    assert (R.find (elt:=nat) x0 rho = None).    
    eapply contrapositiveTcRho; eauto.
    eapply subst_rho_free_vars; eauto.
  - unfold subst_in_type. 
    rewrite  SUBST_FRESH. rewrite <- x. econstructor; eauto.
    assert (R.find (elt:=nat) x0 rho = None).    
    eapply contrapositiveTcRho; eauto.
    eapply subst_rho_free_vars; eauto.
  - unfold subst_in_type. 
    rewrite  SUBST_FRESH. rewrite <- x. econstructor; eauto.
    assert (R.find (elt:=nat) x0 rho = None).    
    eapply contrapositiveTcRho; eauto.
    eapply subst_rho_free_vars; eauto.
  - unfold subst_in_type. 
    rewrite  SUBST_FRESH. rewrite <- x. econstructor; eauto.
    assert (R.find (elt:=nat) x0 rho = None).    
    eapply contrapositiveTcRho; eauto.
    eapply subst_rho_free_vars; eauto.
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
  - intros r HF.
    inversion_clear HRho as [rho' rgns' HRgn'  HRho''].
    destruct (AsciiVars.eq_dec x r) as [c | c].
    + unfold AsciiVars.eq in c; intros; subst.
      unfold set_elem, set_union, singleton_set.
      apply Ensembles.Union_intror.
      apply Ensembles.In_singleton.
    + eapply R_diff_key_3 in HF; auto.  
      apply HRgn' in HF. apply Ensembles.Union_introl. 
      assumption.
Qed.


  