From stdpp Require Import gmap.
From Stdlib Require Import Program.Equality.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.HeapFacts.
Require Import theories.Meta.RegionSubstitutionFacts.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.TypeFacts.
Require Import theories.Meta.TypingWeakeningFacts.
Require Import theories.Runtime.SmallStepExplicitStoreBase.
Require Import theories.Runtime.SmallStepExplicitStoreHeap.

Lemma WTStateRuntimeHeapShapeAt_mu_app_eval_arg_step_preservation :
  forall heap env rho k ea env' rho' f x ec ee tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KMuAppFun ea env rho k)) tout stty ->
    Step
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KMuAppFun ea env rho k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho k ea env' rho' f x ec ee tout stty lbl state'
    HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval; eauto.
  rewrite HArgEq.
  eapply WTKR_MuAppArg; eauto.
  - inversion HTcIncCl as [? ? HFrvCl]; subst.
    eapply ExtendedTcInv_2; eauto;
      eapply HFrvCl; eauto.
  - rewrite <- HResultEq.
    eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_eff_app_eval_arg_step_preservation :
  forall heap env rho k ea env' rho' f x ec ee tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KEffAppFun ea env rho k)) tout stty ->
    Step
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KEffAppFun ea env rho k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho k ea env' rho' f x ec ee tout stty lbl state'
    HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval; eauto.
  rewrite HArgEq.
  eapply WTKR_EffAppArg; eauto.
  inversion HTcIncCl as [? ? HFrvCl]; subst.
  eapply ExtendedTcInv_2; eauto;
    eapply HFrvCl; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_mu_app_body_step_preservation :
  forall heap env rho f x ec ee v k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap v (KMuAppArg env rho f x ec ee k)) tout stty ->
    Step
      (StReturn heap v (KMuAppArg env rho f x ec ee k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho f x ec ee v k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval
    with
      (ctxt :=
        update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya)
          ctxt)
      (rgns := rgns)
      (t := tyc)
      (eff := effc); eauto.
  - eapply TcEnv_update_rec; eauto.
  - eapply RuntimeEnvShape_update_rec; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_eff_app_body_step_preservation :
  forall heap env rho f x ec ee v k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap v (KEffAppArg env rho f x ec ee k)) tout stty ->
    Step
      (StReturn heap v (KEffAppArg env rho f x ec ee k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho f x ec ee v k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval
    with
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

Lemma WTStateRuntimeHeapShapeAt_rgn_app_body_step_preservation :
  forall heap rho w env' rho' x eb k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Cls (env', rho', Lambda x eb)) (KRgnApp w rho k))
      tout stty ->
    Step
      (StReturn heap (Cls (env', rho', Lambda x eb)) (KRgnApp w rho k))
      lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap rho w env' rho' x eb k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval
    with
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

Lemma WTStateRuntimeHeapShapeAt_done_step_preservation :
  forall heap v tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StReturn heap v KDone) tout stty ->
    Step (StReturn heap v KDone) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap v tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ KDone |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Done; eauto.
Qed.
