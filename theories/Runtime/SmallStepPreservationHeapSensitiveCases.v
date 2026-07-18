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
Require Import theories.Runtime.SmallStepPreservationKontShapeCases.

Lemma WTStateRuntimeHeapShape_deref_done_preservation :
  forall heap rho w l k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Loc w l) (KDeRef w rho k)) tout ->
    Step (StReturn heap (Loc w l) (KDeRef w rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap rho w l k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KDeRef _ _ _) |- _ =>
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
  match goal with
  | HFindR : find_R (Rgn_Const true false ?s) rho = Some ?r |- _ =>
      simpl in HFindR; inversion HFindR; subst
  end.
  assert (HTcRead : TcVal (stty, v, subst_rho rho t0)).
  {
    match goal with
    | HTcHeap : TcHeap (heap, stty),
      HFindH : find_H ?key heap = Some v,
      HFindST : find_ST ?key stty = Some (subst_rho rho t0) |- _ =>
        inversion HTcHeap as [? ? _ _ HHeapVal]; subst;
        eapply HHeapVal; eauto
    end.
  }
  assert (HReadShape : RuntimeValShape stty (subst_rho rho t0) v).
  {
    match goal with
    | HHeapShape : RuntimeHeapShape heap stty,
      HFindH : find_H ?key heap = Some v,
      HFindST : find_ST ?key stty = Some (subst_rho rho t0) |- _ =>
        eapply HHeapShape; eauto
    end.
  }
  eapply WTSRHS_Return with (t := subst_rho rho t0); eauto.
Qed.

Lemma WTStateRuntimeHeapShape_assign_done_preservation :
  forall heap rho w l v k tout lbl state',
    WTStateRuntimeHeapShape (StReturn heap v (KAssignVal w l rho k)) tout ->
    Step (StReturn heap v (KAssignVal w l rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
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
  eapply WTSRHS_Return with (t := Ty_Unit); eauto.
  - eapply H_update_heap_exists; eauto.
  - eapply RuntimeHeapShape_update_existing; eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShape_ref_done_preservation :
  forall heap rho w v k tout lbl state',
    WTStateRuntimeHeapShape (StReturn heap v (KRef w rho k)) tout ->
    Step (StReturn heap v (KRef w rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
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
  eapply WTSRHS_Return
    with
      (stty := update_ST (r, allocate_H heap r) (subst_rho rho t0) stty)
      (t := Ty_Ref (Rgn_Const true true r) (subst_rho rho t0)).
  - eapply H_update_heap_fresh; eauto.
  - eapply RuntimeHeapShape_update_fresh; eauto.
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

Lemma WTStateRuntimeHeapShape_mu_app_eval_arg_preservation :
  forall heap env rho k ea env' rho' f x ec ee tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KMuAppFun ea env rho k)) tout ->
    Step
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KMuAppFun ea env rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
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
  eapply WTSRHS_Eval; eauto.
  rewrite HArgEq.
  eapply WTKR_MuAppArg; eauto.
  - inversion HTcIncCl as [? ? HFrvCl]; subst.
    eapply ExtendedTcInv_2; eauto;
      eapply HFrvCl; eauto.
  - rewrite <- HResultEq.
    eauto.
Qed.

Lemma WTStateRuntimeHeapShape_eff_app_eval_arg_preservation :
  forall heap env rho k ea env' rho' f x ec ee tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KEffAppFun ea env rho k)) tout ->
    Step
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KEffAppFun ea env rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
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
  eapply WTSRHS_Eval; eauto.
  rewrite HArgEq.
  eapply WTKR_EffAppArg; eauto.
  inversion HTcIncCl as [? ? HFrvCl]; subst.
  eapply ExtendedTcInv_2; eauto;
    eapply HFrvCl; eauto.
Qed.

Lemma WTStateRuntimeKontShape_mu_app_body_preservation :
  forall heap env rho f x ec ee v k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap v (KMuAppArg env rho f x ec ee k)) tout ->
    Step
      (StReturn heap v (KMuAppArg env rho f x ec ee k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho f x ec ee v k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KMuAppArg _ _ _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  assert (HClosureVal :
    TcVal
      (stty, Cls (env, rho, Mu f x ec ee),
        subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))) by
    (eapply TC_Cls with (rgns := rgns) (ctxt := ctxt); eauto).
  assert (HClosureShape :
    RuntimeValShape stty
      (subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))
      (Cls (env, rho, Mu f x ec ee))) by
    (eapply RVS_Arrow with (rgns := rgns) (ctxt := ctxt); eauto).
  eapply WTSRKS_Eval
    with
      (stty := stty)
      (ctxt :=
        update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya)
          ctxt)
      (rgns := rgns)
      (t := tyc)
      (eff := effc); eauto.
  - eapply TcEnv_update_rec; eauto.
  - eapply RuntimeEnvShape_update_rec; eauto.
Qed.

Lemma WTStateRuntimeKontShape_eff_app_body_preservation :
  forall heap env rho f x ec ee v k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap v (KEffAppArg env rho f x ec ee k)) tout ->
    Step
      (StReturn heap v (KEffAppArg env rho f x ec ee k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho f x ec ee v k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KEffAppArg _ _ _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  assert (HClosureVal :
    TcVal
      (stty, Cls (env, rho, Mu f x ec ee),
        subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))) by
    (eapply TC_Cls with (rgns := rgns) (ctxt := ctxt); eauto).
  assert (HClosureShape :
    RuntimeValShape stty
      (subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))
      (Cls (env, rho, Mu f x ec ee))) by
    (eapply RVS_Arrow with (rgns := rgns) (ctxt := ctxt); eauto).
  eapply WTSRKS_Eval
    with
      (stty := stty)
      (ctxt :=
        update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya)
          ctxt)
      (rgns := rgns)
      (t := Ty_Effect)
      (eff := effe); eauto.
  - eapply TcEnv_update_rec; eauto.
  - eapply RuntimeEnvShape_update_rec; eauto.
  - rewrite (subst_rho_effect rho); eauto.
Qed.

Lemma WTStateRuntimeHeapShape_mu_app_body_preservation :
  forall heap env rho f x ec ee v k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap v (KMuAppArg env rho f x ec ee k)) tout ->
    Step
      (StReturn heap v (KMuAppArg env rho f x ec ee k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho f x ec ee v k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KMuAppArg _ _ _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  assert (HClosureVal :
    TcVal
      (stty, Cls (env, rho, Mu f x ec ee),
        subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))) by
    (eapply TC_Cls with (rgns := rgns) (ctxt := ctxt); eauto).
  assert (HClosureShape :
    RuntimeValShape stty
      (subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))
      (Cls (env, rho, Mu f x ec ee))) by
    (eapply RVS_Arrow with (rgns := rgns) (ctxt := ctxt); eauto).
  eapply WTSRHS_Eval
    with
      (stty := stty)
      (ctxt :=
        update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya)
          ctxt)
      (rgns := rgns)
      (t := tyc)
      (eff := effc); eauto.
  - eapply TcEnv_update_rec; eauto.
  - eapply RuntimeEnvShape_update_rec; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_eff_app_body_preservation :
  forall heap env rho f x ec ee v k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap v (KEffAppArg env rho f x ec ee k)) tout ->
    Step
      (StReturn heap v (KEffAppArg env rho f x ec ee k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho f x ec ee v k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KEffAppArg _ _ _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  assert (HClosureVal :
    TcVal
      (stty, Cls (env, rho, Mu f x ec ee),
        subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))) by
    (eapply TC_Cls with (rgns := rgns) (ctxt := ctxt); eauto).
  assert (HClosureShape :
    RuntimeValShape stty
      (subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))
      (Cls (env, rho, Mu f x ec ee))) by
    (eapply RVS_Arrow with (rgns := rgns) (ctxt := ctxt); eauto).
  eapply WTSRHS_Eval
    with
      (stty := stty)
      (ctxt :=
        update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya)
          ctxt)
      (rgns := rgns)
      (t := Ty_Effect)
      (eff := effe); eauto.
  - eapply TcEnv_update_rec; eauto.
  - eapply RuntimeEnvShape_update_rec; eauto.
  - rewrite (subst_rho_effect rho); eauto.
Qed.

Lemma WTStateRuntimeKontShape_rgn_app_body_preservation :
  forall heap rho w env' rho' x eb k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Cls (env', rho', Lambda x eb)) (KRgnApp w rho k)) tout ->
    Step
      (StReturn heap (Cls (env', rho', Lambda x eb)) (KRgnApp w rho k))
      lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap rho w env' rho' x eb k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KRgnApp _ _ _) |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HShape : RuntimeValShape _ _
      (Cls (env', rho', Lambda x eb)) |- _ =>
      destruct (RuntimeValShape_lambda_closure_inv
        _ _ _ _ _ _ HShape)
        as (rgns_cl & ctxt_cl & effr_cl & tyr_cl &
            HClosureTy & HTcRhoCl & HTcIncCl &
            HTcEnvCl & HEnvShapeCl & HTcExpCl)
  end.
  match goal with
  | HTcExp : TcExp (_, _, Lambda _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  assert (HBodyTyEq :
    subst_rho rho' (close_var x tyr0) = subst_rho rho tyr).
  {
    symmetry.
    eapply subst_rho_forall_body_eq.
    exact HClosureTy.
  }
  assert (HResumeTyEq :
    subst_rho (update_R (x, r) rho') tyr0 =
      subst_rho rho (open (mk_rgn_type w) tyr)).
  {
    eapply subst_rho_update_open_close; eauto.
  }
  eapply WTSRKS_Eval
    with
      (stty := stty)
      (ctxt := ctxt_cl)
      (rgns := set_union rgns_cl (singleton_set x))
      (t := tyr0)
      (eff := effr0); eauto.
  - eapply update_rho; eauto.
  - eapply TcInc_extend_rgn_singleton; eauto.
  - eapply extended_rho; eauto.
  - eapply RuntimeEnvShape_extended_rho; eauto.
  - rewrite HResumeTyEq; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_rgn_app_body_preservation :
  forall heap rho w env' rho' x eb k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Cls (env', rho', Lambda x eb)) (KRgnApp w rho k)) tout ->
    Step
      (StReturn heap (Cls (env', rho', Lambda x eb)) (KRgnApp w rho k))
      lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap rho w env' rho' x eb k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KRgnApp _ _ _) |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HShape : RuntimeValShape _ _
      (Cls (env', rho', Lambda x eb)) |- _ =>
      destruct (RuntimeValShape_lambda_closure_inv
        _ _ _ _ _ _ HShape)
        as (rgns_cl & ctxt_cl & effr_cl & tyr_cl &
            HClosureTy & HTcRhoCl & HTcIncCl &
            HTcEnvCl & HEnvShapeCl & HTcExpCl)
  end.
  match goal with
  | HTcExp : TcExp (_, _, Lambda _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  assert (HBodyTyEq :
    subst_rho rho' (close_var x tyr0) = subst_rho rho tyr).
  {
    symmetry.
    eapply subst_rho_forall_body_eq.
    exact HClosureTy.
  }
  assert (HResumeTyEq :
    subst_rho (update_R (x, r) rho') tyr0 =
      subst_rho rho (open (mk_rgn_type w) tyr)).
  {
    eapply subst_rho_update_open_close; eauto.
  }
  eapply WTSRHS_Eval
    with
      (stty := stty)
      (ctxt := ctxt_cl)
      (rgns := set_union rgns_cl (singleton_set x))
      (t := tyr0)
      (eff := effr0); eauto.
  - eapply update_rho; eauto.
  - eapply TcInc_extend_rgn_singleton; eauto.
  - eapply extended_rho; eauto.
  - eapply RuntimeEnvShape_extended_rho; eauto.
  - rewrite HResumeTyEq; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_pairpar_eval_eff1_preservation :
  forall heap env rho ef1 ea1 ef2 ea2 k tout lbl state',
    WTStateRuntimeHeapShape
      (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k) tout ->
    Step (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Pair_Par _ _ _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HEff1 : TcExp (_, _, Eff_App ef1 ea1, _, _) |- _ =>
      inversion HEff1; subst
  end.
  match goal with
  | HEff2 : TcExp (_, _, Eff_App ef2 ea2, _, _) |- _ =>
      inversion HEff2; subst
  end.
  eapply WTSRHS_Eval with (t := Ty_Effect); eauto.
  rewrite (subst_rho_effect rho).
  eapply WTKR_PairParEff1; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_pairpar_eval_eff2_preservation :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Eff theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)) tout ->
    Step
      (StReturn heap (Eff theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPairParEff1 _ _ _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Eval with (t := Ty_Effect); eauto.
  rewrite (subst_rho_effect rho).
  eapply WTKR_PairParEff2; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_pairpar_eval_mu1_preservation :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Eff theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)) tout ->
    Step
      (StReturn heap (Eff theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k tout lbl state'
    HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPairParEff2 _ _ _ _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Eval; eauto.
  eapply WTKR_PairParMu1; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_pairpar_eval_mu2_preservation :
  forall heap env rho ef2 ea2 v1 k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap v1 (KPairParMu1 ef2 ea2 env rho k)) tout ->
    Step (StReturn heap v1 (KPairParMu1 ef2 ea2 env rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho ef2 ea2 v1 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPairParMu1 _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Eval; eauto.
  eapply WTKR_PairParMu2; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_pairpar_done_preservation :
  forall heap v1 v2 k tout lbl state',
    WTStateRuntimeHeapShape (StReturn heap v2 (KPairParMu2 v1 k)) tout ->
    Step (StReturn heap v2 (KPairParMu2 v1 k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap v1 v2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPairParMu2 _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Return with (t := subst_rho rho (Ty_Pair ty1 ty2)); eauto.
  - rewrite subst_rho_pair.
    constructor; eauto.
  - rewrite subst_rho_pair.
    constructor; eauto.
Qed.
