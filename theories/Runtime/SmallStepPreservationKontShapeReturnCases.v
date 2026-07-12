From stdpp Require Import gmap.
From Stdlib Require Import Sets.Ensembles.

Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepTyping.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.MapFacts.
Require Import theories.Meta.RegionSubstitutionFacts.
Require Import theories.Meta.HeapFacts.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.TypingWeakeningFacts.
Require Import theories.Meta.TypeFacts.
Require Import theories.Meta.LocallyNameless.

Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepPreservationHeapShapeCases.

Lemma WTStateRuntimeKontShape_cond_true_preservation :
  forall heap env rho et ef k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Bit true) (KCond et ef env rho k)) tout ->
    Step (StReturn heap (Bit true) (KCond et ef env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho et ef k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KCond _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Eval; eauto.
Qed.

Lemma WTStateRuntimeKontShape_cond_false_preservation :
  forall heap env rho et ef k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Bit false) (KCond et ef env rho k)) tout ->
    Step (StReturn heap (Bit false) (KCond et ef env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho et ef k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KCond _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Eval; eauto.
Qed.

Lemma WTStateRuntimeKontShape_plus_eval_right_preservation :
  forall heap env rho e2 n k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Num n) (KPlusL e2 env rho k)) tout ->
    Step (StReturn heap (Num n) (KPlusL e2 env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho e2 n k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPlusL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Eval with (t := Ty_Natural); eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_PlusR; eauto.
Qed.

Lemma WTStateRuntimeKontShape_plus_done_preservation :
  forall heap n1 n2 k tout lbl state',
    WTStateRuntimeKontShape (StReturn heap (Num n2) (KPlusR n1 k)) tout ->
    Step (StReturn heap (Num n2) (KPlusR n1 k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap n1 n2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPlusR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Return with (t := Ty_Natural); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_minus_eval_right_preservation :
  forall heap env rho e2 n k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Num n) (KMinusL e2 env rho k)) tout ->
    Step (StReturn heap (Num n) (KMinusL e2 env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho e2 n k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KMinusL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Eval with (t := Ty_Natural); eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_MinusR; eauto.
Qed.

Lemma WTStateRuntimeKontShape_minus_done_preservation :
  forall heap n1 n2 k tout lbl state',
    WTStateRuntimeKontShape (StReturn heap (Num n2) (KMinusR n1 k)) tout ->
    Step (StReturn heap (Num n2) (KMinusR n1 k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap n1 n2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KMinusR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Return with (t := Ty_Natural); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_times_eval_right_preservation :
  forall heap env rho e2 n k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Num n) (KTimesL e2 env rho k)) tout ->
    Step (StReturn heap (Num n) (KTimesL e2 env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho e2 n k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KTimesL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Eval with (t := Ty_Natural); eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_TimesR; eauto.
Qed.

Lemma WTStateRuntimeKontShape_times_done_preservation :
  forall heap n1 n2 k tout lbl state',
    WTStateRuntimeKontShape (StReturn heap (Num n2) (KTimesR n1 k)) tout ->
    Step (StReturn heap (Num n2) (KTimesR n1 k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap n1 n2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KTimesR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Return with (t := Ty_Natural); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_eq_eval_right_preservation :
  forall heap env rho e2 n k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Num n) (KEqL e2 env rho k)) tout ->
    Step (StReturn heap (Num n) (KEqL e2 env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho e2 n k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KEqL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Eval with (t := Ty_Natural); eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_EqR; eauto.
Qed.

Lemma WTStateRuntimeKontShape_eq_done_preservation :
  forall heap n1 n2 k tout lbl state',
    WTStateRuntimeKontShape (StReturn heap (Num n2) (KEqR n1 k)) tout ->
    Step (StReturn heap (Num n2) (KEqR n1 k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap n1 n2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KEqR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Return with (t := Ty_Boolean); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_read_conc_done_preservation :
  forall heap r l k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Loc (Rgn_Const true false r) l) (KReadConc k)) tout ->
    Step (StReturn heap (Loc (Rgn_Const true false r) l) (KReadConc k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap r l k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KReadConc _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_write_conc_done_preservation :
  forall heap r l k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Loc (Rgn_Const true false r) l) (KWriteConc k)) tout ->
    Step (StReturn heap (Loc (Rgn_Const true false r) l) (KWriteConc k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap r l k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KWriteConc _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_concat_eval_right_preservation :
  forall heap env rho e2 theta k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Eff theta) (KConcatL e2 env rho k)) tout ->
    Step (StReturn heap (Eff theta) (KConcatL e2 env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho e2 theta k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KConcatL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Eval with (t := Ty_Effect); eauto.
  rewrite (subst_rho_effect rho).
  eapply WTKR_ConcatR; eauto.
Qed.

Lemma WTStateRuntimeKontShape_concat_done_preservation :
  forall heap theta1 theta2 k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Eff theta2) (KConcatR theta1 k)) tout ->
    Step (StReturn heap (Eff theta2) (KConcatR theta1 k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap theta1 theta2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KConcatR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_mu_app_eval_arg_preservation :
  forall heap env rho k ea env' rho' f x ec ee tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KMuAppFun ea env rho k)) tout ->
    Step
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KMuAppFun ea env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho k ea env' rho' f x ec ee tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KMuAppFun _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HShape : RuntimeValShape _ _
      (Cls (env', rho', Mu f x ec ee)) |- _ =>
      destruct (RuntimeValShape_mu_closure_inv
        _ _ _ _ _ _ _ _ HShape)
        as (rgns_cl & ctxt_cl & tya_cl & effc_cl &
            tyc_cl & effe_cl & HClosureTy & HTcRhoCl & HTcIncCl &
            HTcEnvCl & HEnvShapeCl & HTcExpCl);
      pose proof (subst_rho_arrow_arg_eq _ _ _ _ _ _ _ _ _ _ HClosureTy)
        as HArgEq;
      pose proof (subst_rho_arrow_result_eq _ _ _ _ _ _ _ _ _ _ HClosureTy)
        as HResultEq
  end.
  match goal with
  | HTcExp : TcExp (_, _, Mu _ _ _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  eapply WTSRKS_Eval; eauto.
  rewrite HArgEq.
  eapply WTKR_MuAppArg; eauto.
  - inversion HTcIncCl as [? ? HFrvCl]; subst.
    eapply ExtendedTcInv_2; eauto;
      eapply HFrvCl; eauto.
  - rewrite <- HResultEq.
    eauto.
Qed.

Lemma WTStateRuntimeKontShape_eff_app_eval_arg_preservation :
  forall heap env rho k ea env' rho' f x ec ee tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KEffAppFun ea env rho k)) tout ->
    Step
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KEffAppFun ea env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho k ea env' rho' f x ec ee tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KEffAppFun _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HShape : RuntimeValShape _ _
      (Cls (env', rho', Mu f x ec ee)) |- _ =>
      destruct (RuntimeValShape_mu_closure_inv
        _ _ _ _ _ _ _ _ HShape)
        as (rgns_cl & ctxt_cl & tya_cl & effc_cl &
            tyc_cl & effe_cl & HClosureTy & HTcRhoCl & HTcIncCl &
            HTcEnvCl & HEnvShapeCl & HTcExpCl);
      pose proof (subst_rho_arrow_arg_eq _ _ _ _ _ _ _ _ _ _ HClosureTy)
        as HArgEq
  end.
  match goal with
  | HTcExp : TcExp (_, _, Mu _ _ _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  eapply WTSRKS_Eval; eauto.
  rewrite HArgEq.
  eapply WTKR_EffAppArg; eauto.
  inversion HTcIncCl as [? ? HFrvCl]; subst.
  eapply ExtendedTcInv_2; eauto;
    eapply HFrvCl; eauto.
Qed.

Lemma WTStateRuntimeKontShape_assign_eval_val_preservation :
  forall heap env rho w ev l k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Loc w l) (KAssignLoc w ev env rho k)) tout ->
    Step (StReturn heap (Loc w l) (KAssignLoc w ev env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho w ev l k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KAssignLoc _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HTcVal : TcVal (_, Loc _ _, _) |- _ =>
      inversion HTcVal; subst
  end.
  match goal with
  | HRefEq :
      Ty_Ref (Rgn_Const true true _) _ =
      subst_rho _ (Ty_Ref (Rgn_Const true true _) _) |- _ =>
      rewrite subst_rho_ref_const in HRefEq;
      inversion HRefEq; subst
  end.
  eapply WTSRKS_Eval; eauto.
  eapply WTKR_AssignVal with (r := s); eauto.
Qed.

Lemma WTStateRuntimeKontShape_assign_done_preservation :
  forall heap rho w l v k tout lbl state',
    WTStateRuntimeKontShape (StReturn heap v (KAssignVal w l rho k)) tout ->
    Step (StReturn heap v (KAssignVal w l rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap rho w l v k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KAssignVal _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HFind1 : find_R w rho = Some ?r1,
    HFind2 : find_R w rho = Some ?r2 |- _ =>
      rewrite HFind1 in HFind2;
      inversion HFind2; subst
  end.
  eapply WTSRKS_Return with (t := Ty_Unit); eauto.
  - eapply H_update_heap_exists; eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_ref_done_preservation :
  forall heap rho w v k tout lbl state',
    WTStateRuntimeKontShape (StReturn heap v (KRef w rho k)) tout ->
    Step (StReturn heap v (KRef w rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap rho w v k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KRef _ _ _) |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HFindR : find_R (Rgn_Const true false ?s) rho = Some ?r |- _ =>
      simpl in HFindR; inversion HFindR; subst
  end.
  assert (HFreshH : find_H (r, allocate_H heap r) heap = None)
    by apply allocate_H_fresh.
  assert (HFreshST : find_ST (r, allocate_H heap r) stty = None).
  {
    destruct (find_ST (r, allocate_H heap r) stty) eqn:HFindSTFresh; auto.
    exfalso.
    match goal with
    | HTcHeap : TcHeap (heap, stty) |- _ =>
        inversion HTcHeap as [? ? _ HStoreHeap _]; subst;
        destruct (HStoreHeap (r, allocate_H heap r) t HFindSTFresh)
          as [old HFindHOld];
        rewrite HFreshH in HFindHOld;
        discriminate
    end.
  }
  eapply WTSRKS_Return
    with
      (stty := update_ST (r, allocate_H heap r) (subst_rho rho t0) stty)
      (t := Ty_Ref (Rgn_Const true true r) (subst_rho rho t0)).
  - eapply H_update_heap_fresh; eauto.
  - constructor.
    + unfold find_ST, update_ST.
      apply lookup_insert.
    + intros rgn.
      eapply TcVal_implies_closed; eauto.
  - match goal with
    | HKont : WTKontRuntime stty
        (subst_rho rho (Ty_Ref (mk_rgn_type (Rgn_Const true false r)) ?ty))
        tout k |- _ =>
        simpl in HKont;
        rewrite subst_rho_ref_const in HKont;
        eapply WTKontRuntime_store_ext;
        [ exact HKont
        | apply StoreExtends_update_fresh; exact HFreshST ]
    end.
  - constructor.
Qed.
