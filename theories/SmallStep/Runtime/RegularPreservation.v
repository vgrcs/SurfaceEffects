From Stdlib Require Import List.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Core.Values.
Require Import theories.SmallStep.Runtime.HeapFacts.
Require Import theories.SmallStep.Runtime.HeapNeutral.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Runtime.RegularStateShape.
Require Import theories.SmallStep.Runtime.Trace.
Require Import theories.SmallStep.Runtime.TraceView.
Require Import theories.SmallStep.Runtime.Typing.
Require Import theories.SmallStep.Typing.Judgments.
Require Import theories.SmallStep.Typing.Regularity.
Require Import theories.SmallStep.Typing.Resolve.
Require Import theories.SmallStep.Typing.Types.

Import ListNotations.

Lemma NRegularResolvedStateShape_const_preservation :
  forall heap env rho n k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho (EConst n) k)
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap (VNat n) k)
      ty_out.
Proof.
  intros heap env rho n k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NRRSS_Return; eauto using NRRVS_Nat.
Qed.

Lemma NRegularResolvedStateShape_bool_preservation :
  forall heap env rho b k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho (EBool b) k)
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap (VBool b) k)
      ty_out.
Proof.
  intros heap env rho b k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NRRSS_Return; eauto using NRRVS_Bool.
Qed.

Lemma NRegularResolvedStateShape_var_preservation :
  forall heap env rho x v k ty_out,
    env_lookup x env = Some v ->
    NRegularResolvedStateShape
      (StEval heap env rho (EVar x) k)
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap v k)
      ty_out.
Proof.
  intros heap env rho x v k ty_out HLookup HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  match goal with
  | HBind : ctx_binds x ty gamma |- _ =>
      destruct
        (NRegularResolvedEnvShape_lookup
          rho heap env gamma x ty ty_res HEnv HBind HResolve)
        as (v_typed & HLookupTyped & HV)
  end.
  rewrite HLookup in HLookupTyped.
  inversion HLookupTyped; subst.
  eapply NRRSS_Return; eauto.
Qed.

Lemma NRegularResolvedStateShape_mu_preservation :
  forall heap env rho f x ec ee k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho (EMu f x ec ee) k)
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap (VClosure env rho f x ec ee) k)
      ty_out.
Proof.
  intros heap env rho f x ec ee k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ HReg) as HTyWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  inversion HTyWF; subst.
  eapply NRRSS_Return; eauto.
  eapply NRRVS_Closure with
    (gamma := gamma) (omega := omega)
    (ty_arg := ty_arg) (ty_body := ty_body); eauto.
Qed.

Lemma NRegularResolvedStateShape_lambda_rgn_preservation :
  forall heap env rho x e k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho (ELambdaRgn x e) k)
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap (VRegionClosure env rho x e) k)
      ty_out.
Proof.
  intros heap env rho x e k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ HReg) as HTyWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  inversion HTyWF; subst.
  eapply NRRSS_Return; eauto.
  eapply NRRVS_RegionClosure with
    (gamma := gamma) (omega := omega)
    (ty := ty) (eff := eff); eauto.
  - rewrite H1. exact H4.
  - rewrite H2. exact H11.
  - constructor; eauto.
Qed.

Lemma NRegularResolvedStateShape_empty_preservation :
  forall heap env rho k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho EEmpty k)
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap (VSummary (SummarySet [])) k)
      ty_out.
Proof.
  intros heap env rho k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NRRSS_Return; eauto using NRRVS_Summary.
Qed.

Lemma NRegularResolvedStateShape_top_preservation :
  forall heap env rho k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho ETop k)
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap (VSummary SummaryTop) k)
      ty_out.
Proof.
  intros heap env rho k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NRRSS_Return; eauto using NRRVS_Summary.
Qed.

Lemma NRegularResolvedStateShape_cond_eval_preservation :
  forall heap env rho e et ef k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho (ECond e et ef) k)
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho e (KCond et ef env rho k))
      ty_out.
Proof.
  intros heap env rho e et ef k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ HReg) as HTyWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyBool) (ty_res := TyBool) (eff := eff_e0);
    eauto using NResolve_Bool.
  eapply NRRKS_Cond with
    (gamma := gamma) (omega := omega)
    (ty := ty) (ty_res := ty_res)
    (eff_t := eff_t0) (eff_f := eff_f0); eauto.
Qed.

Lemma NRegularResolvedStateShape_ref_eval_preservation :
  forall heap env rho r e r_val k ty_out,
    eval_region rho r = Some r_val ->
    NRegularResolvedStateShape
      (StEval heap env rho (ERef r e) k)
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho e (KRef r_val k))
      ty_out.
Proof.
  intros heap env rho r e r_val k ty_out
    HRgn HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ HReg) as HTyWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  match goal with
  | HRgnResolved :
      NResolveRegionType rho (region_expr_to_type r) ?rgn_res |- _ =>
      pose proof
        (NResolveRegionType_region_expr_to_type rho r r_val HRgn)
        as HRgnExpected;
      pose proof
        (NResolveRegionType_deterministic
          rho (region_expr_to_type r) rgn_res
          (region_const_type r_val)
          HRgnResolved HRgnExpected);
      subst rgn_res
  end.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty0) (ty_res := ty') (eff := eff0);
    eauto.
  - eapply NRRKS_Ref; eauto.
Qed.

Lemma NRegularResolvedStateShape_ref_return_preservation_bounded :
  forall heap v r_val k l heap' ty_out,
    NHeapKeysBounded heap ->
    heap_alloc r_val v heap = (l, heap') ->
    NRegularResolvedStateShape
      (StReturn heap v (KRef r_val k))
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap' (VLoc r_val l) k)
      ty_out.
Proof.
  intros heap v r_val k l heap' ty_out
    HBounded HAlloc HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HVal HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NRRSS_Return with
    (ty := TyRef (region_const_type r_val) ty).
  - eapply NRegularResolvedHeapShape_alloc; eauto.
  - eapply NRRVS_Loc.
    + eapply heap_lookup_alloc_same; eauto.
    + eapply NRegularResolvedValShape_heap_alloc; eauto.
  - eapply NRegularResolvedKontShape_heap_alloc; eauto.
Qed.

Lemma NStoreResolvedStateShape_ref_return_preservation :
  forall store heap v r_val k l heap' ty_out,
    heap_alloc r_val v heap = (l, heap') ->
    NStoreResolvedStateShape store
      (StReturn heap v (KRef r_val k))
      ty_out ->
    exists store',
      NStoreResolvedStateShape store'
        (StReturn heap' (VLoc r_val l) k)
        ty_out.
Proof.
  intros store heap v r_val k l heap' ty_out HAlloc HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HVal HK | | |];
    subst; clear HState.
  inversion HK; subst.
  exists ((r_val, l, ty) :: store).
  eapply NSRSS_Return with
    (ty := TyRef (region_const_type r_val) ty).
  - eapply NStoreKeysBoundedByHeap_alloc; eauto.
  - eapply NStoreResolvedHeapShape_alloc; eauto.
  - eapply NSRVS_Loc.
    apply store_ty_lookup_extend_same.
  - destruct (heap_alloc_result heap r_val v l heap') as [HFresh _];
      [exact HAlloc |].
    eapply NStoreResolvedKontShape_store_extend; eauto.
Qed.

Lemma NRegularResolvedStateShape_deref_eval_preservation :
  forall heap env rho r e k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho (EDeref r e) k)
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho e (KDeref r k))
      ty_out.
Proof.
  intros heap env rho r e k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ HReg) as HTyWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  match goal with
  | HWF : region_expr_wf omega r |- _ =>
      destruct (NRhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyRef (region_expr_to_type r) ty)
    (ty_res := TyRef (region_const_type r_val) ty_res)
    (eff := eff0); eauto.
  - eapply NResolve_Ref; eauto.
    eapply NResolveRegionType_region_expr_to_type.
    exact HRgn.
  - eapply NRRKS_Deref; eauto.
Qed.

Lemma NRegularResolvedStateShape_assign_eval_preservation :
  forall heap env rho r ea ev k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho (EAssign r ea ev) k)
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho ea (KAssignLoc r ev env rho k))
      ty_out.
Proof.
  intros heap env rho r ea ev k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  match goal with
  | HWF : region_expr_wf omega r |- _ =>
      destruct (NRhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ H10) as HTyCellWF.
  destruct
    (NResolveTy_exists 0 omega rho ty HRho HTyCellWF)
    as (ty_cell_res & HTyResolve).
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyRef (region_expr_to_type r) ty)
    (ty_res := TyRef (region_const_type r_val) ty_cell_res)
    (eff := eff_a0);
    eauto.
  - eapply NResolve_Ref; eauto.
    eapply NResolveRegionType_region_expr_to_type.
    exact HRgn.
  - eapply NRRKS_AssignLoc with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_cell_res)
      (eff_v := eff_v0);
    eauto.
Qed.

Lemma NRegularResolvedStateShape_assign_loc_preservation :
  forall heap r_static ev env rho r l k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VLoc r l) (KAssignLoc r_static ev env rho k))
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho ev (KAssignVal r_static (VLoc r l) k))
      ty_out.
Proof.
  intros heap r_static ev env rho r l k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRRSS_Eval; eauto.
  eapply NRRKS_AssignVal; eauto.
Qed.

Lemma NStoreResolvedStateShape_assign_val_preservation :
  forall store heap r_static r l v k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap v (KAssignVal r_static (VLoc r l) k))
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn (heap_update r l v heap) VUnit k)
      ty_out.
Proof.
  intros store heap r_static r l v k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HVal HK | | |];
    subst; clear HState.
  inversion HK; subst.
  match goal with
  | HLoc : NStoreResolvedValShape store (VLoc r l)
      (TyRef (region_const_type ?r0) ?ty_cell) |- _ =>
      inversion HLoc; subst
  end.
  destruct HHeap as (HHeapToStore & HStoreToHeap).
  match goal with
  | HStoreLookup : store_ty_lookup ?r_loc ?l_loc store = Some ?ty_cell |- _ =>
      destruct (HStoreToHeap r_loc l_loc ty_cell HStoreLookup)
        as (old & HOldLookup & _);
      eapply NSRSS_Return with (ty := TyUnit);
      [ eapply NStoreKeysBoundedByHeap_update; eauto
      | eapply NStoreResolvedHeapShape_update; eauto;
        split; [exact HHeapToStore | exact HStoreToHeap]
      | constructor
      | assumption ]
  end.
Qed.

Lemma NStoreResolvedStateShape_const_preservation :
  forall store heap env rho n k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho (EConst n) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap (VNat n) k)
      ty_out.
Proof.
  intros store heap env rho n k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NSRSS_Return; eauto using NSRVS_Nat.
Qed.

Lemma NStoreResolvedStateShape_bool_preservation :
  forall store heap env rho b k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho (EBool b) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap (VBool b) k)
      ty_out.
Proof.
  intros store heap env rho b k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NSRSS_Return; eauto using NSRVS_Bool.
Qed.

Lemma NStoreResolvedStateShape_var_preservation :
  forall store heap env rho x v k ty_out,
    env_lookup x env = Some v ->
    NStoreResolvedStateShape store
      (StEval heap env rho (EVar x) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap v k)
      ty_out.
Proof.
  intros store heap env rho x v k ty_out HLookup HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  match goal with
  | HBind : ctx_binds x ty gamma |- _ =>
      destruct
        (NStoreResolvedEnvShape_lookup
          store rho env gamma x ty ty_res HEnv HBind HResolve)
        as (v_typed & HLookupTyped & HV)
  end.
  rewrite HLookup in HLookupTyped.
  inversion HLookupTyped; subst.
  eapply NSRSS_Return; eauto.
Qed.

Lemma NStoreResolvedStateShape_mu_preservation :
  forall store heap env rho f x ec ee k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho (EMu f x ec ee) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap (VClosure env rho f x ec ee) k)
      ty_out.
Proof.
  intros store heap env rho f x ec ee k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ HReg) as HTyWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  inversion HTyWF; subst.
  eapply NSRSS_Return; eauto.
  eapply NSRVS_Closure with
    (gamma := gamma) (omega := omega)
    (ty_arg := ty_arg) (ty_body := ty_body); eauto.
Qed.

Lemma NStoreResolvedStateShape_lambda_rgn_preservation :
  forall store heap env rho x e k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho (ELambdaRgn x e) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap (VRegionClosure env rho x e) k)
      ty_out.
Proof.
  intros store heap env rho x e k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ HReg) as HTyWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  inversion HTyWF; subst.
  eapply NSRSS_Return; eauto.
  eapply NSRVS_RegionClosure with
    (gamma := gamma) (omega := omega)
    (ty := ty) (eff := eff); eauto.
  - rewrite H1. exact H4.
  - rewrite H2. exact H11.
  - constructor; eauto.
Qed.

Lemma NStoreResolvedStateShape_empty_preservation :
  forall store heap env rho k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho EEmpty k)
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap (VSummary (SummarySet [])) k)
      ty_out.
Proof.
  intros store heap env rho k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NSRSS_Return; eauto using NSRVS_Summary.
Qed.

Lemma NStoreResolvedStateShape_top_preservation :
  forall store heap env rho k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho ETop k)
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap (VSummary SummaryTop) k)
      ty_out.
Proof.
  intros store heap env rho k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NSRSS_Return; eauto using NSRVS_Summary.
Qed.

Lemma NStoreResolvedStateShape_alloc_abs_preservation :
  forall store heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    NStoreResolvedStateShape store
      (StEval heap env rho (EAllocAbs r) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap (VSummary (SummarySet [CAllocAbs r_val])) k)
      ty_out.
Proof.
  intros store heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NSRSS_Return; eauto using NSRVS_Summary.
Qed.

Lemma NStoreResolvedStateShape_read_abs_preservation :
  forall store heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    NStoreResolvedStateShape store
      (StEval heap env rho (EReadAbs r) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap (VSummary (SummarySet [CReadAbs r_val])) k)
      ty_out.
Proof.
  intros store heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NSRSS_Return; eauto using NSRVS_Summary.
Qed.

Lemma NStoreResolvedStateShape_write_abs_preservation :
  forall store heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    NStoreResolvedStateShape store
      (StEval heap env rho (EWriteAbs r) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap (VSummary (SummarySet [CWriteAbs r_val])) k)
      ty_out.
Proof.
  intros store heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NSRSS_Return; eauto using NSRVS_Summary.
Qed.

Lemma NStoreResolvedStateShape_read_conc_preservation :
  forall store heap r l k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VLoc r l) (KReadConc k))
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap (VSummary (SummarySet [CReadConc r l])) k)
      ty_out.
Proof.
  intros store heap r l k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NSRSS_Return; eauto using NSRVS_Summary.
Qed.

Lemma NStoreResolvedStateShape_write_conc_preservation :
  forall store heap r l k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VLoc r l) (KWriteConc k))
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap (VSummary (SummarySet [CWriteConc r l])) k)
      ty_out.
Proof.
  intros store heap r l k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NSRSS_Return; eauto using NSRVS_Summary.
Qed.

Lemma NStoreResolvedStateShape_done_preservation :
  forall store heap v ty_out,
    NStoreResolvedStateShape store
      (StReturn heap v KDone)
      ty_out ->
    NStoreResolvedStateShape store (StDone heap v) ty_out.
Proof.
  intros store heap v ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NSRSS_Done; eauto.
Qed.

Lemma NStoreResolvedStateShape_ref_eval_preservation :
  forall store heap env rho r e r_val k ty_out,
    eval_region rho r = Some r_val ->
    NStoreResolvedStateShape store
      (StEval heap env rho (ERef r e) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho e (KRef r_val k))
      ty_out.
Proof.
  intros store heap env rho r e r_val k ty_out
    HRgn HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  match goal with
  | HRgnResolved :
      NResolveRegionType rho (region_expr_to_type r) ?rgn_res |- _ =>
      pose proof
        (NResolveRegionType_region_expr_to_type rho r r_val HRgn)
        as HRgnExpected;
      pose proof
        (NResolveRegionType_deterministic
          rho (region_expr_to_type r) rgn_res
          (region_const_type r_val)
          HRgnResolved HRgnExpected);
      subst rgn_res
  end.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty0) (ty_res := ty') (eff := eff0).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - assumption.
  - assumption.
  - eapply NSRKS_Ref; eauto.
Qed.

Lemma NStoreResolvedStateShape_deref_eval_preservation :
  forall store heap env rho r e k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho (EDeref r e) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho e (KDeref r k))
      ty_out.
Proof.
  intros store heap env rho r e k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  match goal with
  | HWF : region_expr_wf omega r |- _ =>
      destruct (NRhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyRef (region_expr_to_type r) ty)
    (ty_res := TyRef (region_const_type r_val) ty_res)
    (eff := eff0).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - eapply NResolve_Ref; eauto.
    eapply NResolveRegionType_region_expr_to_type.
    exact HRgn.
  - assumption.
  - eapply NSRKS_Deref; eauto.
Qed.

Lemma NStoreResolvedStateShape_assign_eval_preservation :
  forall store heap env rho r ea ev k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho (EAssign r ea ev) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho ea (KAssignLoc r ev env rho k))
      ty_out.
Proof.
  intros store heap env rho r ea ev k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  match goal with
  | HWF : region_expr_wf omega r |- _ =>
      destruct (NRhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ H10) as HTyCellWF.
  destruct
    (NResolveTy_exists 0 omega rho ty HRho HTyCellWF)
    as (ty_cell_res & HTyResolve).
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyRef (region_expr_to_type r) ty)
    (ty_res := TyRef (region_const_type r_val) ty_cell_res)
    (eff := eff_a0).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - eapply NResolve_Ref; eauto.
    eapply NResolveRegionType_region_expr_to_type.
    exact HRgn.
  - assumption.
  - eapply NSRKS_AssignLoc with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_cell_res)
      (eff_v := eff_v0);
    eauto.
Qed.

Lemma NStoreResolvedStateShape_assign_loc_preservation :
  forall store heap r_static ev env rho r l k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VLoc r l) (KAssignLoc r_static ev env rho k))
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho ev (KAssignVal r_static (VLoc r l) k))
      ty_out.
Proof.
  intros store heap r_static ev env rho r l k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NSRSS_Eval; eauto.
  unfold NStoreResolvedRuntimeShape.
  match goal with
  | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
      split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
  end.
  eapply NSRKS_AssignVal; eauto.
Qed.

Lemma NStoreResolvedStateShape_cond_eval_preservation :
  forall store heap env rho e et ef k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho (ECond e et ef) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho e (KCond et ef env rho k))
      ty_out.
Proof.
  intros store heap env rho e et ef k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyBool) (ty_res := TyBool) (eff := eff_e0).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - constructor.
  - eassumption.
  - eapply NSRKS_Cond with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_res)
      (eff_t := eff_t0) (eff_f := eff_f0);
      eauto.
Qed.

Lemma NStoreResolvedStateShape_plus_eval_preservation :
  forall store heap env rho e1 e2 k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho (EPlus e1 e2) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho e1 (KPlusL e2 env rho k))
      ty_out.
Proof.
  intros store heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff0).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - constructor.
  - eassumption.
  - eapply NSRKS_PlusL; eauto.
Qed.

Lemma NStoreResolvedStateShape_minus_eval_preservation :
  forall store heap env rho e1 e2 k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho (EMinus e1 e2) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho e1 (KMinusL e2 env rho k))
      ty_out.
Proof.
  intros store heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff0).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - constructor.
  - eassumption.
  - eapply NSRKS_MinusL; eauto.
Qed.

Lemma NStoreResolvedStateShape_times_eval_preservation :
  forall store heap env rho e1 e2 k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho (ETimes e1 e2) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho e1 (KTimesL e2 env rho k))
      ty_out.
Proof.
  intros store heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff0).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - constructor.
  - eassumption.
  - eapply NSRKS_TimesL; eauto.
Qed.

Lemma NStoreResolvedStateShape_eq_eval_preservation :
  forall store heap env rho e1 e2 k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho (EEq e1 e2) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho e1 (KEqL e2 env rho k))
      ty_out.
Proof.
  intros store heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff0).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - constructor.
  - eassumption.
  - eapply NSRKS_EqL; eauto.
Qed.

Lemma NStoreResolvedStateShape_concat_eval_preservation :
  forall store heap env rho e1 e2 k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho (EConcat e1 e2) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho e1 (KConcatL e2 env rho k))
      ty_out.
Proof.
  intros store heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff0).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - constructor.
  - eassumption.
  - eapply NSRKS_ConcatL; eauto.
Qed.

Lemma NStoreResolvedStateShape_cond_true_preservation :
  forall store heap et ef env rho k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VBool true) (KCond et ef env rho k))
      ty_out ->
    NStoreResolvedStateShape store (StEval heap env rho et k) ty_out.
Proof.
  intros store heap et ef env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NSRSS_Eval; eauto.
  unfold NStoreResolvedRuntimeShape.
  match goal with
  | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
      split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
  end.
Qed.

Lemma NStoreResolvedStateShape_cond_false_preservation :
  forall store heap et ef env rho k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VBool false) (KCond et ef env rho k))
      ty_out ->
    NStoreResolvedStateShape store (StEval heap env rho ef k) ty_out.
Proof.
  intros store heap et ef env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NSRSS_Eval; eauto.
  unfold NStoreResolvedRuntimeShape.
  match goal with
  | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
      split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
  end.
Qed.

Lemma NStoreResolvedStateShape_deref_preservation :
  forall store heap r_static r l v k ty_out,
    heap_lookup r l heap = Some v ->
    NStoreResolvedStateShape store
      (StReturn heap (VLoc r l) (KDeref r_static k))
      ty_out ->
    NStoreResolvedStateShape store (StReturn heap v k) ty_out.
Proof.
  intros store heap r_static r l v k ty_out HLookup HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  destruct HHeap as (HHeapToStore & HStoreToHeap).
  match goal with
  | HLookupCell : heap_lookup ?rr ?ll heap = Some v,
    HStoreLookup : store_ty_lookup ?rr ?ll store = Some ?ty_cell |- _ =>
      destruct (HHeapToStore rr ll v HLookupCell) as
        (ty_found & HStoreFound & HShapeFound);
      pose proof
        (store_ty_lookup_deterministic
          store rr ll ty_found ty_cell HStoreFound HStoreLookup)
        as HTyEq;
      subst ty_found;
      eapply NSRSS_Return with (ty := ty_cell);
      [ exact HBounded
      | split; [exact HHeapToStore | exact HStoreToHeap]
      | exact HShapeFound
      | eauto ]
  end.
Qed.

Lemma NStoreResolvedStateShape_plus_l_preservation :
  forall store heap n e2 env rho k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VNat n) (KPlusL e2 env rho k))
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho e2 (KPlusR n k))
      ty_out.
Proof.
  intros store heap n e2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - constructor.
  - assumption.
  - eapply NSRKS_PlusR; eauto.
Qed.

Lemma NStoreResolvedStateShape_plus_r_preservation :
  forall store heap n1 n2 k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VNat n2) (KPlusR n1 k))
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap (VNat (n1 + n2)) k)
      ty_out.
Proof.
  intros store heap n1 n2 k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NSRSS_Return; eauto using NSRVS_Nat.
Qed.

Lemma NStoreResolvedStateShape_minus_l_preservation :
  forall store heap n e2 env rho k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VNat n) (KMinusL e2 env rho k))
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho e2 (KMinusR n k))
      ty_out.
Proof.
  intros store heap n e2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - constructor.
  - assumption.
  - eapply NSRKS_MinusR; eauto.
Qed.

Lemma NStoreResolvedStateShape_minus_r_preservation :
  forall store heap n1 n2 k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VNat n2) (KMinusR n1 k))
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap (VNat (n1 - n2)) k)
      ty_out.
Proof.
  intros store heap n1 n2 k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NSRSS_Return; eauto using NSRVS_Nat.
Qed.

Lemma NStoreResolvedStateShape_times_l_preservation :
  forall store heap n e2 env rho k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VNat n) (KTimesL e2 env rho k))
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho e2 (KTimesR n k))
      ty_out.
Proof.
  intros store heap n e2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - constructor.
  - assumption.
  - eapply NSRKS_TimesR; eauto.
Qed.

Lemma NStoreResolvedStateShape_times_r_preservation :
  forall store heap n1 n2 k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VNat n2) (KTimesR n1 k))
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap (VNat (n1 * n2)) k)
      ty_out.
Proof.
  intros store heap n1 n2 k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NSRSS_Return; eauto using NSRVS_Nat.
Qed.

Lemma NStoreResolvedStateShape_eq_l_preservation :
  forall store heap n e2 env rho k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VNat n) (KEqL e2 env rho k))
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho e2 (KEqR n k))
      ty_out.
Proof.
  intros store heap n e2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - constructor.
  - assumption.
  - eapply NSRKS_EqR; eauto.
Qed.

Lemma NStoreResolvedStateShape_eq_r_preservation :
  forall store heap n1 n2 k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VNat n2) (KEqR n1 k))
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap (VBool (Nat.eqb n1 n2)) k)
      ty_out.
Proof.
  intros store heap n1 n2 k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NSRSS_Return; eauto using NSRVS_Bool.
Qed.

Lemma NStoreResolvedStateShape_concat_l_preservation :
  forall store heap theta1 e2 env rho k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VSummary theta1) (KConcatL e2 env rho k))
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho e2 (KConcatR theta1 k))
      ty_out.
Proof.
  intros store heap theta1 e2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - constructor.
  - assumption.
  - eapply NSRKS_ConcatR; eauto.
Qed.

Lemma NStoreResolvedStateShape_concat_r_preservation :
  forall store heap theta1 theta2 k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VSummary theta2) (KConcatR theta1 k))
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap (VSummary (summary_union theta1 theta2)) k)
      ty_out.
Proof.
  intros store heap theta1 theta2 k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NSRSS_Return; eauto using NSRVS_Summary.
Qed.

Lemma NStoreResolvedStateShape_mu_app_eval_preservation :
  forall store heap env rho ef ea k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho (EMuApp ef ea) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho ef (KMuAppFun ea env rho k))
      ty_out.
Proof.
  intros store heap env rho ef ea k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ H7) as HFunWF.
  inversion HFunWF; subst.
  match goal with
  | HArgWF : NTyWFAt 0 omega ty_arg0,
    HBodyEffWF : NStaticEffectWFAt 0 omega eff_body0,
    HSummaryEffWF : NStaticEffectWFAt 0 omega eff_summary0 |- _ =>
      destruct (NResolveTy_exists 0 omega rho ty_arg0 HRho HArgWF)
        as (ty_arg_res & HArgResolve);
      destruct
        (NResolveStaticEffect_exists
          0 omega rho eff_body0 HRho HBodyEffWF)
        as (eff_body_res & HBodyEffResolve);
      destruct
        (NResolveStaticEffect_exists
          0 omega rho eff_summary0 HRho HSummaryEffWF)
        as (eff_summary_res & HSummaryEffResolve);
      eapply NSRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyArrow ty_arg0 eff_body0 ty eff_summary0)
        (ty_res := TyArrow
          ty_arg_res eff_body_res ty_res eff_summary_res)
        (eff := eff_f0);
      [ unfold NStoreResolvedRuntimeShape;
        match goal with
        | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
            split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
        end
      | exact HRho
      | eapply NResolve_Arrow; eauto
      | eauto
      | eapply NSRKS_MuAppFun with
          (gamma := gamma) (omega := omega)
          (ty_arg := ty_arg0) (ty_body := ty)
          (eff_body := eff_body0) (eff_summary := eff_summary0)
          (eff_arg := eff_a0);
        eauto ]
  end.
Qed.

Lemma NStoreResolvedStateShape_eff_app_eval_preservation :
  forall store heap env rho ef ea k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho (EEffApp ef ea) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho ef (KEffAppFun ea env rho k))
      ty_out.
Proof.
  intros store heap env rho ef ea k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ H5) as HFunWF.
  inversion HFunWF; subst.
  match goal with
  | HArgWF : NTyWFAt 0 omega ?ty_arg0,
    HBodyEffWF : NStaticEffectWFAt 0 omega ?eff_body0,
    HBodyWF : NTyWFAt 0 omega ?ty_body0,
    HSummaryEffWF : NStaticEffectWFAt 0 omega ?eff_summary0 |- _ =>
      destruct (NResolveTy_exists 0 omega rho ty_arg0 HRho HArgWF)
        as (ty_arg_res & HArgResolve);
      destruct
        (NResolveStaticEffect_exists
          0 omega rho eff_body0 HRho HBodyEffWF)
        as (eff_body_res & HBodyEffResolve);
      destruct (NResolveTy_exists 0 omega rho ty_body0 HRho HBodyWF)
        as (ty_body_res & HBodyResolve);
      destruct
        (NResolveStaticEffect_exists
          0 omega rho eff_summary0 HRho HSummaryEffWF)
        as (eff_summary_res & HSummaryEffResolve);
      eapply NSRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyArrow ty_arg0 eff_body0 ty_body0 eff_summary0)
        (ty_res := TyArrow
          ty_arg_res eff_body_res ty_body_res eff_summary_res)
        (eff := eff_f0);
      [ unfold NStoreResolvedRuntimeShape;
        match goal with
        | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
            split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
        end
      | exact HRho
      | eapply NResolve_Arrow; eauto
      | eauto
      | eapply NSRKS_EffAppFun with
          (gamma := gamma) (omega := omega)
          (ty_arg := ty_arg0) (ty_body := ty_body0)
          (eff_body := eff_body0) (eff_summary := eff_summary0)
          (eff_arg := eff_a0);
        eauto ]
  end.
Qed.

Lemma NStoreResolvedStateShape_mu_app_eval_arg_preservation :
  forall store heap env rho ea k closure_env closure_rho f x ec ee ty_out,
    NStoreResolvedStateShape store
      (StReturn heap
        (VClosure closure_env closure_rho f x ec ee)
        (KMuAppFun ea env rho k))
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho ea
        (KMuAppArg closure_env closure_rho f x ec ee k))
      ty_out.
Proof.
  intros store heap env rho ea k closure_env closure_rho f x ec ee
    ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty_arg) (ty_res := ty_arg_res)
    (eff := eff_arg).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - assumption.
  - assumption.
  - eapply NSRKS_MuAppArg with
      (gamma := gamma0) (omega := omega0)
      (ty_arg := ty_arg0) (ty_body := ty_body0)
      (eff_body := eff_body0) (eff_summary := eff_summary0);
    eauto.
Qed.

Lemma NStoreResolvedStateShape_eff_app_eval_arg_preservation :
  forall store heap env rho ea k closure_env closure_rho f x ec ee ty_out,
    NStoreResolvedStateShape store
      (StReturn heap
        (VClosure closure_env closure_rho f x ec ee)
        (KEffAppFun ea env rho k))
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho ea
        (KEffAppArg closure_env closure_rho f x ec ee k))
      ty_out.
Proof.
  intros store heap env rho ea k closure_env closure_rho f x ec ee
    ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty_arg) (ty_res := ty_arg_res)
    (eff := eff_arg).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - assumption.
  - assumption.
  - eapply NSRKS_EffAppArg with
      (gamma := gamma0) (omega := omega0)
      (ty_arg := ty_arg0) (ty_body := ty_body0)
      (eff_body := eff_body0) (eff_summary := eff_summary0);
    eauto.
Qed.

Lemma NStoreResolvedStateShape_mu_app_body_preservation :
  forall store heap v_arg closure_env closure_rho f x ec ee k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap v_arg
        (KMuAppArg closure_env closure_rho f x ec ee k))
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap
        (env_extend x v_arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho
        ec
        k)
      ty_out.
Proof.
  intros store heap v_arg closure_env closure_rho f x ec ee k
    ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NSRSS_Eval with
    (gamma :=
      (x, ty_arg) ::
      (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
    (omega := omega)
    (ty := ty_body) (ty_res := ty_body_res) (eff := eff_body).
  - unfold NStoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | ]].
    eapply NStoreResolvedEnvShape_extend with
      (ty_res := ty); eauto.
    eapply NStoreResolvedEnvShape_extend with
      (ty_res := TyArrow
        ty eff_body_res ty_body_res eff_summary_res);
      eauto.
    + eapply NResolve_Arrow; eauto.
    + eapply NSRVS_Closure with
        (gamma := gamma) (omega := omega)
        (ty_arg := ty_arg) (ty_body := ty_body); eauto.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma NStoreResolvedStateShape_eff_app_body_preservation :
  forall store heap v_arg closure_env closure_rho f x ec ee k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap v_arg
        (KEffAppArg closure_env closure_rho f x ec ee k))
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap
        (env_extend x v_arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho
        ee
        k)
      ty_out.
Proof.
  intros store heap v_arg closure_env closure_rho f x ec ee k
    ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NSRSS_Eval with
    (gamma :=
      (x, ty_arg) ::
      (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
    (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary).
  - unfold NStoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | ]].
    eapply NStoreResolvedEnvShape_extend with
      (ty_res := ty); eauto.
    eapply NStoreResolvedEnvShape_extend with
      (ty_res := TyArrow
        ty eff_body_res ty_body_res eff_summary_res);
      eauto.
    + eapply NResolve_Arrow; eauto.
    + eapply NSRVS_Closure with
        (gamma := gamma) (omega := omega)
        (ty_arg := ty_arg) (ty_body := ty_body); eauto.
  - assumption.
  - constructor.
  - assumption.
  - assumption.
Qed.

Lemma NStoreResolvedStateShape_read_conc_eval_preservation :
  forall store heap env rho e k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho (EReadConc e) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho e (KReadConc k))
      ty_out.
Proof.
  intros store heap env rho e k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ H3) as HRefWF.
  inversion HRefWF; subst.
  match goal with
  | HRgnWF : NRegionTypeWFAt 0 omega r0,
    HTyWF : NTyWFAt 0 omega ty |- _ =>
      destruct
        (NResolveRegionType_exists 0 omega rho r0 HRho HRgnWF)
        as (rgn_res & HRgnResolve);
      destruct (NResolveTy_exists 0 omega rho ty HRho HTyWF)
        as (ty_ref_res & HTyResolve);
      destruct
        (NResolveRegionType_wf0_const
          omega rho r0 rgn_res HRgnWF HRgnResolve)
        as (r_val & HRgnResEq);
      subst rgn_res;
      eapply NSRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyRef r0 ty)
        (ty_res := TyRef (region_const_type r_val) ty_ref_res)
        (eff := eff);
      [ unfold NStoreResolvedRuntimeShape;
        match goal with
        | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
            split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
        end
      | exact HRho
      | eapply NResolve_Ref; eauto
      | eauto
      | eapply NSRKS_ReadConc; eauto ]
  end.
Qed.

Lemma NStoreResolvedStateShape_write_conc_eval_preservation :
  forall store heap env rho e k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho (EWriteConc e) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho e (KWriteConc k))
      ty_out.
Proof.
  intros store heap env rho e k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ H3) as HRefWF.
  inversion HRefWF; subst.
  match goal with
  | HRgnWF : NRegionTypeWFAt 0 omega r0,
    HTyWF : NTyWFAt 0 omega ty |- _ =>
      destruct
        (NResolveRegionType_exists 0 omega rho r0 HRho HRgnWF)
        as (rgn_res & HRgnResolve);
      destruct (NResolveTy_exists 0 omega rho ty HRho HTyWF)
        as (ty_ref_res & HTyResolve);
      destruct
        (NResolveRegionType_wf0_const
          omega rho r0 rgn_res HRgnWF HRgnResolve)
        as (r_val & HRgnResEq);
      subst rgn_res;
      eapply NSRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyRef r0 ty)
        (ty_res := TyRef (region_const_type r_val) ty_ref_res)
        (eff := eff);
      [ unfold NStoreResolvedRuntimeShape;
        match goal with
        | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
            split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
        end
      | exact HRho
      | eapply NResolve_Ref; eauto
      | eauto
      | eapply NSRKS_WriteConc; eauto ]
  end.
Qed.

Lemma NStoreResolvedStateShape_rgn_app_eval_preservation :
  forall store heap env rho er r k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho (ERgnApp er r) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho er (KRgnApp r rho k))
      ty_out.
Proof.
  intros store heap env rho er r k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty_result ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  match goal with
  | HWF : region_expr_wf omega r |- _ =>
      destruct (NRhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ H8) as HFunWF.
  inversion HFunWF; subst.
  destruct
    (NResolveStaticEffect_exists 1 omega rho eff_body0 HRho H9)
    as (eff_body_res & HEffResolve).
  destruct
    (NResolveTy_exists 1 omega rho ty0 HRho H10)
    as (ty_body_res & HTyResolve).
  pose proof
    (NResolveTy_open_ty
      rho r ty0 ty_body_res r_val HRgn HTyResolve)
    as HOpenResolve.
  rewrite H4 in HOpenResolve.
  pose proof
    (NResolveTy_deterministic
      rho (open_ty r ty) ty_res
      (open_ty_type (region_const_type r_val) ty_body_res)
      HResolve HOpenResolve)
    as HTyResEq.
  subst ty_res.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyForallRgn eff_body0 ty0)
    (ty_res := TyForallRgn eff_body_res ty_body_res)
    (eff := eff_f0).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - eapply NResolve_ForallRgn; eauto.
  - assumption.
  - eapply NSRKS_RgnApp; eauto.
Qed.

Lemma NStoreResolvedStateShape_rgn_app_return_preservation :
  forall store heap closure_env closure_rho x e arg_rho r r_val k ty_out,
    eval_region arg_rho r = Some r_val ->
    NStoreResolvedStateShape store
      (StReturn heap
        (VRegionClosure closure_env closure_rho x e)
        (KRgnApp r arg_rho k))
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap closure_env
        (rho_extend x r_val closure_rho)
        e
        k)
      ty_out.
Proof.
  intros store heap closure_env closure_rho x e arg_rho r r_val k ty_out
    HRgn HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty_in ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HV; subst.
  inversion HK; subst.
  match goal with
  | HRgnKont : eval_region arg_rho r = Some ?r_val0 |- _ =>
      rewrite HRgn in HRgnKont;
      inversion HRgnKont; subst; clear HRgnKont
  end.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := x :: omega)
    (ty := ty)
    (ty_res := open_ty_type (region_const_type r_val0) ty_res)
    (eff := eff).
  - unfold NStoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | ]].
    eapply NStoreResolvedEnvShape_extend_fresh;
      eauto using
        NCheckedRegionBody_fresh,
        NCheckedRegionBody_ctx_wf.
  - eapply NRhoModels_extend; eauto.
  - eapply NResolveTy_rho_extend_close_ty.
    + exact
        (NCheckedTcExp_ty_wf
          _ _ _ _ _
          (NCheckedRegionBody_checked _ _ _ _ _ _ H9)).
    + eauto.
  - exact (NCheckedRegionBody_checked _ _ _ _ _ _ H9).
  - assumption.
Qed.

Lemma NStoreResolvedStateShape_pair_par_eval_preservation :
  forall store heap env rho ef1 ea1 ef2 ea2 k ty_out,
    NStoreResolvedStateShape store
      (StEval heap env rho
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)) k)
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho (EEffApp ef1 ea1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      ty_out.
Proof.
  intros store heap env rho ef1 ea1 ef2 ea2 k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary0).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - constructor.
  - exact H14.
  - eapply NSRKS_PairParEff1 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff0) (eff2 := eff3)
      (eff_summary2 := eff_summary3);
      eauto.
Qed.

Lemma NStoreResolvedStateShape_pair_par_eff1_preservation :
  forall store heap theta1 ef1 ea1 ef2 ea2 env rho k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VSummary theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      ty_out ->
    NStoreResolvedStateShape store
      (StEval heap env rho (EEffApp ef2 ea2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      ty_out.
Proof.
  intros store heap theta1 ef1 ea1 ef2 ea2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary2).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - constructor.
  - assumption.
  - eapply NSRKS_PairParEff2 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff1) (eff2 := eff2);
      eauto.
Qed.

Lemma NStoreResolvedStateShape_pair_par_check_pass_preservation :
  forall store heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      ty_out ->
    NStoreResolvedStateShape store
      (StPairParRun
        (StEval heap env rho (EMuApp ef1 ea1) KDone)
        (StEval heap env rho (EMuApp ef2 ea2) KDone)
        [] [] k)
      ty_out.
Proof.
  intros store heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out
    HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NSRSS_PairParRun with
    (heap := heap) (ty1 := ty1_res) (ty2 := ty2_res);
    simpl; eauto.
  - eapply NSRSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty1) (ty_res := ty1_res) (eff := eff1).
    + unfold NStoreResolvedRuntimeShape.
      match goal with
      | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
          split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
      end.
    + assumption.
    + assumption.
    + assumption.
    + constructor.
  - eapply NSRSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty2) (ty_res := ty2_res) (eff := eff2).
    + unfold NStoreResolvedRuntimeShape.
      match goal with
      | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
          split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
      end.
    + assumption.
    + assumption.
    + assumption.
    + constructor.
Qed.

Lemma NStoreResolvedStateShape_pair_par_check_fail_preservation :
  forall store heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      ty_out ->
    NStoreResolvedStateShape store (StError heap) ty_out.
Proof.
  intros store heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out
    HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  eapply NSRSS_Error; eauto.
Qed.

Lemma NStoreResolvedStateShape_pair_par_done_pass_preservation :
  forall store heap v1 v2 phi_left phi_right k ty_out,
    NStoreResolvedStateShape store
      (StPairParRun
        (StDone heap v1)
        (StDone heap v2)
        phi_left phi_right k)
      ty_out ->
    NStoreResolvedStateShape store
      (StReturn heap (VPair v1 v2) k)
      ty_out.
Proof.
  intros store heap v1 v2 phi_left phi_right k ty_out HState.
  inversion HState as
    [| | | |
      store0 left_state right_state phi_left0 phi_right0 k0 heap0
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    subst; clear HState; simpl in *; subst.
  inversion HLeft as [| | store1 heap1 v_left ty_left HBounded1 HHeap1 HV1 | |];
    subst; clear HLeft.
  inversion HRight as [| | store2 heap2 v_right ty_right HBounded2 HHeap2 HV2 | |];
    subst; clear HRight.
  eapply NSRSS_Return; eauto.
  eapply NSRVS_Pair; eauto.
Qed.

Lemma NStoreResolvedStateShape_pair_par_done_fail_preservation :
  forall store heap v1 v2 phi_left phi_right k ty_out,
    NStoreResolvedStateShape store
      (StPairParRun
        (StDone heap v1)
        (StDone heap v2)
        phi_left phi_right k)
      ty_out ->
    NStoreResolvedStateShape store (StError heap) ty_out.
Proof.
  intros store heap v1 v2 phi_left phi_right k ty_out HState.
  inversion HState as
    [| | | |
      store0 left_state right_state phi_left0 phi_right0 k0 heap0
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    subst; clear HState; simpl in *; subst.
  inversion HLeft; subst.
  eapply NSRSS_Error; eauto.
Qed.

Lemma NStoreResolvedStateShape_pair_par_left_error_preservation :
  forall store heap right_state phi_left phi_right k ty_out,
    NStoreResolvedStateShape store
      (StPairParRun (StError heap) right_state phi_left phi_right k)
      ty_out ->
    NStoreResolvedStateShape store (StError heap) ty_out.
Proof.
  intros store heap right_state phi_left phi_right k ty_out HState.
  inversion HState as
    [| | | |
      store0 left_state right_state0 phi_left0 phi_right0 k0 heap0
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    clear HState.
  subst left_state right_state0 phi_left0 phi_right0 k0 ty_out0.
  simpl in HHeapLeft.
  subst heap0.
  inversion HLeft; subst.
  eapply NSRSS_Error; eauto.
Qed.

Lemma NStoreResolvedStateShape_pair_par_right_error_preservation :
  forall store heap_left v1 heap_right phi_left phi_right k ty_out,
    NStoreResolvedStateShape store
      (StPairParRun
        (StDone heap_left v1)
        (StError heap_right)
        phi_left phi_right k)
      ty_out ->
    NStoreResolvedStateShape store (StError heap_right) ty_out.
Proof.
  intros store heap_left v1 heap_right phi_left phi_right k ty_out HState.
  inversion HState as
    [| | | |
      store0 left_state right_state phi_left0 phi_right0 k0 heap
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    clear HState.
  subst left_state right_state phi_left0 phi_right0 k0 ty_out0.
  simpl in HHeapRight.
  subst heap.
  inversion HRight; subst.
  eapply NSRSS_Error; eauto.
Qed.

Definition NStoreStepTransport
    (store store' : NStoreTyping)
    (state state' : NState) : Prop :=
  (forall sibling ty,
    state_heap sibling = state_heap state ->
    NStoreResolvedStateShape store sibling ty ->
    NStoreResolvedStateShape store'
      (with_state_heap (state_heap state') sibling) ty) /\
  (forall env rho gamma,
    NStoreResolvedRuntimeShape
      (state_heap state) store env rho gamma ->
    NStoreResolvedRuntimeShape
      (state_heap state') store' env rho gamma) /\
  (forall k ty_in ty_out,
    NStoreResolvedKontShape store k ty_in ty_out ->
    NStoreResolvedKontShape store' k ty_in ty_out).

Lemma NStoreStepTransport_same :
  forall store state state',
    state_heap state' = state_heap state ->
    NStoreStepTransport store store state state'.
Proof.
  intros store state state' HHeap.
  split.
  - intros sibling ty HSiblingHeap HSibling.
    eapply NStoreResolvedStateShape_with_state_heap_same; eauto.
    rewrite HHeap.
    exact HSiblingHeap.
  - split.
    + intros env rho gamma HRuntime.
      rewrite HHeap.
      exact HRuntime.
    + intros k ty_in ty_out HK.
      exact HK.
Qed.

Lemma NStoreStep_ref_return_preservation :
  forall store heap v r_val k l heap' ty_out,
    heap_alloc r_val v heap = (l, heap') ->
    NStoreResolvedStateShape store
      (StReturn heap v (KRef r_val k))
      ty_out ->
    exists store',
      NStoreResolvedStateShape store'
        (StReturn heap' (VLoc r_val l) k)
        ty_out /\
      NStoreStepTransport store store'
        (StReturn heap v (KRef r_val k))
        (StReturn heap' (VLoc r_val l) k).
Proof.
  intros store heap v r_val k l heap' ty_out HAlloc HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty_cell ty_out0
      HBounded HHeap HVal HK | | |];
    subst; clear HState.
  inversion HK; subst.
  exists ((r_val, l, ty_cell) :: store).
  split.
  - eapply NSRSS_Return with
      (ty := TyRef (region_const_type r_val) ty_cell).
    + eapply NStoreKeysBoundedByHeap_alloc; eauto.
    + eapply NStoreResolvedHeapShape_alloc; eauto.
    + eapply NSRVS_Loc.
      apply store_ty_lookup_extend_same.
    + destruct (heap_alloc_result heap r_val v l heap')
        as [HFresh _]; [exact HAlloc |].
      eapply NStoreResolvedKontShape_store_extend; eauto.
  - split.
    + intros sibling ty_s HSiblingHeap HSibling.
      eapply NStoreResolvedStateShape_heap_alloc; eauto.
    + split.
      * intros env rho gamma HRuntime.
        eapply NStoreResolvedRuntimeShape_alloc; eauto.
      * intros k_frame ty_in ty_out_frame HKFrame.
        destruct (heap_alloc_result heap r_val v l heap')
          as [HFresh _]; [exact HAlloc |].
        eapply NStoreResolvedKontShape_store_extend; eauto.
Qed.

Lemma NStoreStep_assign_val_preservation :
  forall store heap r_static r l v k ty_out,
    NStoreResolvedStateShape store
      (StReturn heap v (KAssignVal r_static (VLoc r l) k))
      ty_out ->
    exists store',
      NStoreResolvedStateShape store'
        (StReturn (heap_update r l v heap) VUnit k)
        ty_out /\
      NStoreStepTransport store store'
        (StReturn heap v (KAssignVal r_static (VLoc r l) k))
        (StReturn (heap_update r l v heap) VUnit k).
Proof.
  intros store heap r_static r l v k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty_cell ty_out0
      HBounded HHeap HVal HK | | |];
    subst; clear HState.
  inversion HK; subst.
  match goal with
  | HLoc : NStoreResolvedValShape store (VLoc r l)
      (TyRef (region_const_type ?r0) ?ty_loc) |- _ =>
      inversion HLoc; subst
  end.
  destruct HHeap as (HHeapToStore & HStoreToHeap).
  match goal with
  | HStoreLookup : store_ty_lookup ?rr ?ll store = Some ?ty_loc |- _ =>
      destruct (HStoreToHeap rr ll ty_loc HStoreLookup)
        as (old & HOldLookup & _);
      exists store;
      split;
      [ eapply NSRSS_Return with (ty := TyUnit);
        [ eapply NStoreKeysBoundedByHeap_update; eauto
        | eapply NStoreResolvedHeapShape_update; eauto;
          split; [exact HHeapToStore | exact HStoreToHeap]
        | constructor
        | assumption ]
      | split;
        [ intros sibling ty_s HSiblingHeap HSibling;
          eapply NStoreResolvedStateShape_heap_update; eauto;
          simpl in HSiblingHeap; exact HSiblingHeap
        | split;
          [ intros env rho gamma HRuntime;
            eapply NStoreResolvedRuntimeShape_update; eauto
          | intros k_frame ty_in ty_out_frame HKFrame;
            exact HKFrame ] ] ]
  end.
Qed.

Theorem NStep_store_resolved_state_preservation :
  forall state label state' store ty,
    NStep state label state' ->
    NStoreResolvedStateShape store state ty ->
    exists store',
      NStoreResolvedStateShape store' state' ty /\
      NStoreStepTransport store store' state state'.
Proof.
  intros state label state' store ty HStep.
  revert store ty.
  induction HStep; intros store ty HState;
    try solve
      [ exists store; split;
        [ eauto using
            NStoreResolvedStateShape_const_preservation,
            NStoreResolvedStateShape_bool_preservation,
            NStoreResolvedStateShape_var_preservation,
            NStoreResolvedStateShape_mu_preservation,
            NStoreResolvedStateShape_lambda_rgn_preservation,
            NStoreResolvedStateShape_mu_app_eval_preservation,
            NStoreResolvedStateShape_mu_app_eval_arg_preservation,
            NStoreResolvedStateShape_mu_app_body_preservation,
            NStoreResolvedStateShape_eff_app_eval_preservation,
            NStoreResolvedStateShape_eff_app_eval_arg_preservation,
            NStoreResolvedStateShape_eff_app_body_preservation,
            NStoreResolvedStateShape_pair_par_eval_preservation,
            NStoreResolvedStateShape_pair_par_eff1_preservation,
            NStoreResolvedStateShape_pair_par_check_pass_preservation,
            NStoreResolvedStateShape_pair_par_check_fail_preservation,
            NStoreResolvedStateShape_pair_par_left_error_preservation,
            NStoreResolvedStateShape_pair_par_right_error_preservation,
            NStoreResolvedStateShape_pair_par_done_pass_preservation,
            NStoreResolvedStateShape_pair_par_done_fail_preservation,
            NStoreResolvedStateShape_rgn_app_eval_preservation,
            NStoreResolvedStateShape_rgn_app_return_preservation,
            NStoreResolvedStateShape_empty_preservation,
            NStoreResolvedStateShape_top_preservation,
            NStoreResolvedStateShape_cond_eval_preservation,
            NStoreResolvedStateShape_cond_true_preservation,
            NStoreResolvedStateShape_cond_false_preservation,
            NStoreResolvedStateShape_ref_eval_preservation,
            NStoreResolvedStateShape_deref_eval_preservation,
            NStoreResolvedStateShape_deref_preservation,
            NStoreResolvedStateShape_assign_eval_preservation,
            NStoreResolvedStateShape_assign_loc_preservation,
            NStoreResolvedStateShape_plus_eval_preservation,
            NStoreResolvedStateShape_plus_l_preservation,
            NStoreResolvedStateShape_plus_r_preservation,
            NStoreResolvedStateShape_minus_eval_preservation,
            NStoreResolvedStateShape_minus_l_preservation,
            NStoreResolvedStateShape_minus_r_preservation,
            NStoreResolvedStateShape_times_eval_preservation,
            NStoreResolvedStateShape_times_l_preservation,
            NStoreResolvedStateShape_times_r_preservation,
            NStoreResolvedStateShape_eq_eval_preservation,
            NStoreResolvedStateShape_eq_l_preservation,
            NStoreResolvedStateShape_eq_r_preservation,
            NStoreResolvedStateShape_alloc_abs_preservation,
            NStoreResolvedStateShape_read_abs_preservation,
            NStoreResolvedStateShape_write_abs_preservation,
            NStoreResolvedStateShape_read_conc_eval_preservation,
            NStoreResolvedStateShape_read_conc_preservation,
            NStoreResolvedStateShape_write_conc_eval_preservation,
            NStoreResolvedStateShape_write_conc_preservation,
            NStoreResolvedStateShape_concat_eval_preservation,
            NStoreResolvedStateShape_concat_l_preservation,
            NStoreResolvedStateShape_concat_r_preservation,
            NStoreResolvedStateShape_done_preservation
        | apply NStoreStepTransport_same; reflexivity ] ].
  - inversion HState as
      [| | | |
        store0 left_state0 right_state0 phi_left0 phi_right0 k0 heap
        ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
      subst; clear HState.
    destruct (IHHStep store ty1 HLeft) as
      (store' & HLeft' & HTransport).
    destruct HTransport as
      (HStateTransport & HRuntimeTransport & HKTransport).
    pose proof (NStoreResolvedStateShape_aligned _ _ _ HRight)
      as HAlignedRight.
    destruct
      (with_state_heap_aligned
        (state_heap left_state') right_state HAlignedRight)
      as (_ & HRightHeap').
    exists store'.
    split.
    + eapply NSRSS_PairParRun with
        (heap := state_heap left_state') (ty1 := ty1) (ty2 := ty2).
      * reflexivity.
      * exact HRightHeap'.
      * exact HLeft'.
      * eapply HStateTransport.
        -- exact HHeapRight.
        -- exact HRight.
      * eapply HKTransport; eauto.
    + split.
      * intros sibling ty_s HSiblingHeap HSibling.
        eapply HStateTransport; eauto.
      * split.
        -- intros env0 rho0 gamma0 HRuntime.
           eapply HRuntimeTransport; eauto.
        -- intros k_frame ty_in ty_out_frame HKFrame.
           eapply HKTransport; eauto.
  - inversion HState as
      [| | | |
        store0 left_state right_state0 phi_left0 phi_right0 k0 heap0
        ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
      subst; clear HState.
    destruct (IHHStep store ty2 HRight) as
      (store' & HRight' & HTransport).
    destruct HTransport as
      (HStateTransport & HRuntimeTransport & HKTransport).
    pose proof (NStoreResolvedStateShape_aligned _ _ _ HLeft)
      as HAlignedLeft.
    destruct
      (with_state_heap_aligned
        (state_heap right_state') (StDone heap v1) HAlignedLeft)
      as (_ & HLeftHeap').
    exists store'.
    split.
    + eapply NSRSS_PairParRun with
        (heap := state_heap right_state') (ty1 := ty1) (ty2 := ty2).
      * exact HLeftHeap'.
      * reflexivity.
      * eapply HStateTransport.
        -- simpl. symmetry. exact HHeapRight.
        -- exact HLeft.
      * exact HRight'.
      * eapply HKTransport; eauto.
    + split.
      * intros sibling ty_s HSiblingHeap HSibling.
        eapply HStateTransport.
        -- rewrite HHeapRight. exact HSiblingHeap.
        -- exact HSibling.
      * split.
        -- intros env0 rho0 gamma0 HRuntime.
           eapply HRuntimeTransport.
           rewrite HHeapRight.
           exact HRuntime.
        -- intros k_frame ty_in ty_out_frame HKFrame.
           eapply HKTransport; eauto.
  - exists store.
    split.
    + eapply NStoreResolvedStateShape_pair_par_right_error_preservation;
        eauto.
    + split.
      * intros sibling ty_s HSiblingHeap HSibling.
        eapply NStoreResolvedStateShape_with_state_heap_same; eauto.
        inversion HState; subst; simpl in *; congruence.
      * split.
        -- intros env0 rho0 gamma0 HRuntime.
           assert
             (state_heap (StError heap_right) =
              state_heap
                (StPairParRun
                  (StDone heap_left v1)
                  (StError heap_right)
                  phi_left phi_right k)).
           {
             inversion HState; subst; simpl in *; congruence.
           }
           rewrite H.
           exact HRuntime.
        -- intros k_frame ty_in ty_out_frame HKFrame.
           exact HKFrame.
  - eapply NStoreStep_ref_return_preservation; eauto.
  - eapply NStoreStep_assign_val_preservation; eauto.
Qed.

Theorem NSteps_store_resolved_state_preservation_with_transport :
  forall state phi state' store ty,
    NSteps state phi state' ->
    NStoreResolvedStateShape store state ty ->
    exists store',
      NStoreResolvedStateShape store' state' ty /\
      NStoreStepTransport store store' state state'.
Proof.
  intros state phi state' store ty HSteps.
  revert store ty.
  induction HSteps as
    [state | state label state1 phi state2 HStep _ IH];
    intros store ty HState.
  - exists store.
    split.
    + exact HState.
    + apply NStoreStepTransport_same. reflexivity.
  - destruct
      (NStep_store_resolved_state_preservation
        state label state1 store ty HStep HState)
      as (store1 & HState1 & HTransport1).
    destruct (IH store1 ty HState1)
      as (store2 & HState2 & HTransport2).
    destruct HTransport1 as
      (HStateTransport1 & HRuntimeTransport1 & HKTransport1).
    destruct HTransport2 as
      (HStateTransport2 & HRuntimeTransport2 & HKTransport2).
    exists store2.
    split.
    + exact HState2.
    + split.
      * intros sibling ty_s HSiblingHeap HSibling.
        specialize
          (HStateTransport1 sibling ty_s HSiblingHeap HSibling)
          as HSibling1.
        specialize
          (HStateTransport2
            (with_state_heap (state_heap state1) sibling)
            ty_s
            (state_heap_with_state_heap (state_heap state1) sibling)
            HSibling1)
          as HSibling2.
        rewrite with_state_heap_twice in HSibling2.
        exact HSibling2.
      * split.
        -- intros env0 rho0 gamma0 HRuntime.
           eapply HRuntimeTransport2.
           eapply HRuntimeTransport1.
           exact HRuntime.
        -- intros k ty_in ty_out HK.
           eapply HKTransport2.
           eapply HKTransport1.
           exact HK.
Qed.

Theorem NSteps_store_resolved_state_preservation :
  forall state phi state' store ty,
    NSteps state phi state' ->
    NStoreResolvedStateShape store state ty ->
    exists store',
      NStoreResolvedStateShape store' state' ty.
Proof.
  intros state phi state' store ty HSteps HState.
  destruct
    (NSteps_store_resolved_state_preservation_with_transport
      state phi state' store ty HSteps HState)
    as (store' & HState' & _).
  exists store'.
  exact HState'.
Qed.

Theorem NStepsN_store_resolved_state_preservation_with_transport :
  forall n state phi state' store ty,
    NStepsN n state phi state' ->
    NStoreResolvedStateShape store state ty ->
    exists store',
      NStoreResolvedStateShape store' state' ty /\
      NStoreStepTransport store store' state state'.
Proof.
  intros n state phi state' store ty HSteps HState.
  eapply NSteps_store_resolved_state_preservation_with_transport; eauto.
  eapply NStepsN_to_NSteps; eauto.
Qed.

Theorem NStepsN_store_resolved_state_preservation :
  forall n state phi state' store ty,
    NStepsN n state phi state' ->
    NStoreResolvedStateShape store state ty ->
    exists store',
      NStoreResolvedStateShape store' state' ty.
Proof.
  intros n state phi state' store ty HSteps HState.
  eapply NSteps_store_resolved_state_preservation; eauto.
  eapply NStepsN_to_NSteps; eauto.
Qed.

Theorem NStepsView_store_resolved_state_preservation_with_transport :
  forall state view state' store ty,
    NStepsView state view state' ->
    NStoreResolvedStateShape store state ty ->
    exists store',
      NStoreResolvedStateShape store' state' ty /\
      NStoreStepTransport store store' state state'.
Proof.
  intros state view state' store ty HSteps HState.
  eapply NSteps_store_resolved_state_preservation_with_transport; eauto.
  eapply NStepsView_to_NSteps; eauto.
Qed.

Theorem NStepsView_store_resolved_state_preservation :
  forall state view state' store ty,
    NStepsView state view state' ->
    NStoreResolvedStateShape store state ty ->
    exists store',
      NStoreResolvedStateShape store' state' ty.
Proof.
  intros state view state' store ty HSteps HState.
  eapply NSteps_store_resolved_state_preservation; eauto.
  eapply NStepsView_to_NSteps; eauto.
Qed.

Lemma NRegularResolvedStateShape_plus_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho (EPlus e1 e2) k)
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho e1 (KPlusL e2 env rho k))
      ty_out.
Proof.
  intros heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat);
    eauto using NResolve_Nat.
  - eapply NRRKS_PlusL; eauto.
Qed.

Lemma NRegularResolvedStateShape_minus_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho (EMinus e1 e2) k)
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho e1 (KMinusL e2 env rho k))
      ty_out.
Proof.
  intros heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat);
    eauto using NResolve_Nat.
  - eapply NRRKS_MinusL; eauto.
Qed.

Lemma NRegularResolvedStateShape_times_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho (ETimes e1 e2) k)
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho e1 (KTimesL e2 env rho k))
      ty_out.
Proof.
  intros heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat);
    eauto using NResolve_Nat.
  - eapply NRRKS_TimesL; eauto.
Qed.

Lemma NRegularResolvedStateShape_eq_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho (EEq e1 e2) k)
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho e1 (KEqL e2 env rho k))
      ty_out.
Proof.
  intros heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat);
    eauto using NResolve_Nat.
  - eapply NRRKS_EqL; eauto.
Qed.

Lemma NRegularResolvedStateShape_alloc_abs_preservation :
  forall heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    NRegularResolvedStateShape
      (StEval heap env rho (EAllocAbs r) k)
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap (VSummary (SummarySet [CAllocAbs r_val])) k)
      ty_out.
Proof.
  intros heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NRRSS_Return; eauto using NRRVS_Summary.
Qed.

Lemma NRegularResolvedStateShape_read_abs_preservation :
  forall heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    NRegularResolvedStateShape
      (StEval heap env rho (EReadAbs r) k)
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap (VSummary (SummarySet [CReadAbs r_val])) k)
      ty_out.
Proof.
  intros heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NRRSS_Return; eauto using NRRVS_Summary.
Qed.

Lemma NRegularResolvedStateShape_write_abs_preservation :
  forall heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    NRegularResolvedStateShape
      (StEval heap env rho (EWriteAbs r) k)
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap (VSummary (SummarySet [CWriteAbs r_val])) k)
      ty_out.
Proof.
  intros heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NRRSS_Return; eauto using NRRVS_Summary.
Qed.

Lemma NRegularResolvedStateShape_concat_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho (EConcat e1 e2) k)
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho e1 (KConcatL e2 env rho k))
      ty_out.
Proof.
  intros heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect);
    eauto using NResolve_Effect.
  - eapply NRRKS_ConcatL; eauto.
Qed.

Lemma NRegularResolvedStateShape_cond_true_preservation :
  forall heap et ef env rho k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VBool true) (KCond et ef env rho k))
      ty_out ->
    NRegularResolvedStateShape (StEval heap env rho et k) ty_out.
Proof.
  intros heap et ef env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRRSS_Eval; eauto.
Qed.

Lemma NRegularResolvedStateShape_cond_false_preservation :
  forall heap et ef env rho k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VBool false) (KCond et ef env rho k))
      ty_out ->
    NRegularResolvedStateShape (StEval heap env rho ef k) ty_out.
Proof.
  intros heap et ef env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRRSS_Eval; eauto.
Qed.

Lemma NRegularResolvedStateShape_deref_preservation :
  forall heap r_static r l v k ty_out,
    heap_lookup r l heap = Some v ->
    NRegularResolvedStateShape
      (StReturn heap (VLoc r l) (KDeref r_static k))
      ty_out ->
    NRegularResolvedStateShape (StReturn heap v k) ty_out.
Proof.
  intros heap r_static r l v k ty_out HLookup HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  match goal with
  | HCellLookup : heap_lookup ?rr ?ll heap = Some ?cell,
    HLookup' : heap_lookup ?rr ?ll heap = Some v,
    HCellShape : NRegularResolvedValShape heap ?cell ?ty |- _ =>
      rewrite HLookup' in HCellLookup;
      inversion HCellLookup; subst
  end.
  eapply NRRSS_Return; eauto.
Qed.

Lemma NRegularResolvedStateShape_plus_l_preservation :
  forall heap n e2 env rho k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VNat n) (KPlusL e2 env rho k))
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho e2 (KPlusR n k))
      ty_out.
Proof.
  intros heap n e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using NResolve_Nat.
  eapply NRRKS_PlusR; eauto.
Qed.

Lemma NRegularResolvedStateShape_plus_r_preservation :
  forall heap n1 n2 k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VNat n2) (KPlusR n1 k))
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap (VNat (n1 + n2)) k)
      ty_out.
Proof.
  intros heap n1 n2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRRSS_Return; eauto using NRRVS_Nat.
Qed.

Lemma NRegularResolvedStateShape_minus_l_preservation :
  forall heap n e2 env rho k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VNat n) (KMinusL e2 env rho k))
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho e2 (KMinusR n k))
      ty_out.
Proof.
  intros heap n e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using NResolve_Nat.
  eapply NRRKS_MinusR; eauto.
Qed.

Lemma NRegularResolvedStateShape_minus_r_preservation :
  forall heap n1 n2 k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VNat n2) (KMinusR n1 k))
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap (VNat (n1 - n2)) k)
      ty_out.
Proof.
  intros heap n1 n2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRRSS_Return; eauto using NRRVS_Nat.
Qed.

Lemma NRegularResolvedStateShape_times_l_preservation :
  forall heap n e2 env rho k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VNat n) (KTimesL e2 env rho k))
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho e2 (KTimesR n k))
      ty_out.
Proof.
  intros heap n e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using NResolve_Nat.
  eapply NRRKS_TimesR; eauto.
Qed.

Lemma NRegularResolvedStateShape_times_r_preservation :
  forall heap n1 n2 k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VNat n2) (KTimesR n1 k))
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap (VNat (n1 * n2)) k)
      ty_out.
Proof.
  intros heap n1 n2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRRSS_Return; eauto using NRRVS_Nat.
Qed.

Lemma NRegularResolvedStateShape_eq_l_preservation :
  forall heap n e2 env rho k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VNat n) (KEqL e2 env rho k))
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho e2 (KEqR n k))
      ty_out.
Proof.
  intros heap n e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using NResolve_Nat.
  eapply NRRKS_EqR; eauto.
Qed.

Lemma NRegularResolvedStateShape_eq_r_preservation :
  forall heap n1 n2 k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VNat n2) (KEqR n1 k))
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap (VBool (Nat.eqb n1 n2)) k)
      ty_out.
Proof.
  intros heap n1 n2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRRSS_Return; eauto using NRRVS_Bool.
Qed.

Lemma NRegularResolvedStateShape_concat_l_preservation :
  forall heap theta1 e2 env rho k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VSummary theta1) (KConcatL e2 env rho k))
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho e2 (KConcatR theta1 k))
      ty_out.
Proof.
  intros heap theta1 e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff);
    eauto using NResolve_Effect.
  eapply NRRKS_ConcatR; eauto.
Qed.

Lemma NRegularResolvedStateShape_concat_r_preservation :
  forall heap theta1 theta2 k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VSummary theta2) (KConcatR theta1 k))
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap (VSummary (summary_union theta1 theta2)) k)
      ty_out.
Proof.
  intros heap theta1 theta2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRRSS_Return; eauto using NRRVS_Summary.
Qed.

Lemma NRegularResolvedStateShape_read_conc_eval_preservation :
  forall heap env rho e k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho (EReadConc e) k)
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho e (KReadConc k))
      ty_out.
Proof.
  intros heap env rho e k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ H3) as HRefWF.
  inversion HRefWF; subst.
  match goal with
  | HRgnWF : NRegionTypeWFAt 0 omega r0,
    HTyWF : NTyWFAt 0 omega ty |- _ =>
      destruct
        (NResolveRegionType_exists 0 omega rho r0 HRho HRgnWF)
        as (rgn_res & HRgnResolve);
      destruct (NResolveTy_exists 0 omega rho ty HRho HTyWF)
        as (ty_ref_res & HTyResolve);
      destruct
        (NResolveRegionType_wf0_const
          omega rho r0 rgn_res HRgnWF HRgnResolve)
        as (r_val & HRgnResEq);
      subst rgn_res;
      eapply NRRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyRef r0 ty)
        (ty_res := TyRef (region_const_type r_val) ty_ref_res)
        (eff := eff);
        eauto;
      [ eapply NResolve_Ref; eauto
      | eapply NRRKS_ReadConc; eauto ]
  end.
Qed.

Lemma NRegularResolvedStateShape_write_conc_eval_preservation :
  forall heap env rho e k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho (EWriteConc e) k)
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho e (KWriteConc k))
      ty_out.
Proof.
  intros heap env rho e k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ H3) as HRefWF.
  inversion HRefWF; subst.
  match goal with
  | HRgnWF : NRegionTypeWFAt 0 omega r0,
    HTyWF : NTyWFAt 0 omega ty |- _ =>
      destruct
        (NResolveRegionType_exists 0 omega rho r0 HRho HRgnWF)
        as (rgn_res & HRgnResolve);
      destruct (NResolveTy_exists 0 omega rho ty HRho HTyWF)
        as (ty_ref_res & HTyResolve);
      destruct
        (NResolveRegionType_wf0_const
          omega rho r0 rgn_res HRgnWF HRgnResolve)
        as (r_val & HRgnResEq);
      subst rgn_res;
      eapply NRRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyRef r0 ty)
        (ty_res := TyRef (region_const_type r_val) ty_ref_res)
        (eff := eff);
        eauto;
      [ eapply NResolve_Ref; eauto
      | eapply NRRKS_WriteConc; eauto ]
  end.
Qed.

Lemma NRegularResolvedStateShape_read_conc_preservation :
  forall heap r l k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VLoc r l) (KReadConc k))
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap (VSummary (SummarySet [CReadConc r l])) k)
      ty_out.
Proof.
  intros heap r l k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NRRSS_Return; eauto using NRRVS_Summary.
Qed.

Lemma NRegularResolvedStateShape_write_conc_preservation :
  forall heap r l k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VLoc r l) (KWriteConc k))
      ty_out ->
    NRegularResolvedStateShape
      (StReturn heap (VSummary (SummarySet [CWriteConc r l])) k)
      ty_out.
Proof.
  intros heap r l k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NRRSS_Return; eauto using NRRVS_Summary.
Qed.

Lemma NRegularResolvedStateShape_done_preservation :
  forall heap v ty_out,
    NRegularResolvedStateShape
      (StReturn heap v KDone)
      ty_out ->
    NRegularResolvedStateShape (StDone heap v) ty_out.
Proof.
  intros heap v ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NRRSS_Done; eauto.
Qed.

Lemma NRegularResolvedStateShape_mu_app_eval_preservation :
  forall heap env rho ef ea k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho (EMuApp ef ea) k)
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho ef (KMuAppFun ea env rho k))
      ty_out.
Proof.
  intros heap env rho ef ea k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ H7) as HFunWF.
  inversion HFunWF; subst.
  match goal with
  | HArgWF : NTyWFAt 0 omega ty_arg0,
    HBodyEffWF : NStaticEffectWFAt 0 omega eff_body0,
    HSummaryEffWF : NStaticEffectWFAt 0 omega eff_summary0 |- _ =>
      destruct (NResolveTy_exists 0 omega rho ty_arg0 HRho HArgWF)
        as (ty_arg_res & HArgResolve);
      destruct
        (NResolveStaticEffect_exists
          0 omega rho eff_body0 HRho HBodyEffWF)
        as (eff_body_res & HBodyEffResolve);
      destruct
        (NResolveStaticEffect_exists
          0 omega rho eff_summary0 HRho HSummaryEffWF)
        as (eff_summary_res & HSummaryEffResolve);
      eapply NRRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyArrow ty_arg0 eff_body0 ty eff_summary0)
        (ty_res := TyArrow
          ty_arg_res eff_body_res ty_res eff_summary_res)
        (eff := eff_f0);
        eauto;
      [ eapply NResolve_Arrow; eauto
      | eapply NRRKS_MuAppFun with
          (gamma := gamma) (omega := omega)
          (ty_arg := ty_arg0) (ty_body := ty)
          (eff_body := eff_body0) (eff_summary := eff_summary0)
          (eff_arg := eff_a0);
        eauto ]
  end.
Qed.

Lemma NRegularResolvedStateShape_eff_app_eval_preservation :
  forall heap env rho ef ea k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho (EEffApp ef ea) k)
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho ef (KEffAppFun ea env rho k))
      ty_out.
Proof.
  intros heap env rho ef ea k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ H5) as HFunWF.
  inversion HFunWF; subst.
  match goal with
  | HArgWF : NTyWFAt 0 omega ?ty_arg0,
    HBodyEffWF : NStaticEffectWFAt 0 omega ?eff_body0,
    HBodyWF : NTyWFAt 0 omega ?ty_body0,
    HSummaryEffWF : NStaticEffectWFAt 0 omega ?eff_summary0 |- _ =>
      destruct (NResolveTy_exists 0 omega rho ty_arg0 HRho HArgWF)
        as (ty_arg_res & HArgResolve);
      destruct
        (NResolveStaticEffect_exists
          0 omega rho eff_body0 HRho HBodyEffWF)
        as (eff_body_res & HBodyEffResolve);
      destruct (NResolveTy_exists 0 omega rho ty_body0 HRho HBodyWF)
        as (ty_body_res & HBodyResolve);
      destruct
        (NResolveStaticEffect_exists
          0 omega rho eff_summary0 HRho HSummaryEffWF)
        as (eff_summary_res & HSummaryEffResolve);
      eapply NRRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyArrow ty_arg0 eff_body0 ty_body0 eff_summary0)
        (ty_res := TyArrow
          ty_arg_res eff_body_res ty_body_res eff_summary_res)
        (eff := eff_f0);
        eauto;
      [ eapply NResolve_Arrow; eauto
      | eapply NRRKS_EffAppFun with
          (gamma := gamma) (omega := omega)
          (ty_arg := ty_arg0) (ty_body := ty_body0)
          (eff_body := eff_body0) (eff_summary := eff_summary0)
          (eff_arg := eff_a0);
        eauto ]
  end.
Qed.

Lemma NRegularResolvedStateShape_mu_app_eval_arg_preservation :
  forall heap env rho ea k closure_env closure_rho f x ec ee ty_out,
    NRegularResolvedStateShape
      (StReturn heap
        (VClosure closure_env closure_rho f x ec ee)
        (KMuAppFun ea env rho k))
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho ea
        (KMuAppArg closure_env closure_rho f x ec ee k))
      ty_out.
Proof.
  intros heap env rho ea k closure_env closure_rho f x ec ee ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty_arg) (ty_res := ty_arg_res)
    (eff := eff_arg); eauto.
  eapply NRRKS_MuAppArg with
    (gamma := gamma0) (omega := omega0)
    (ty_arg := ty_arg0) (ty_body := ty_body0)
    (eff_body := eff_body0) (eff_summary := eff_summary0);
    eauto.
Qed.

Lemma NRegularResolvedStateShape_eff_app_eval_arg_preservation :
  forall heap env rho ea k closure_env closure_rho f x ec ee ty_out,
    NRegularResolvedStateShape
      (StReturn heap
        (VClosure closure_env closure_rho f x ec ee)
        (KEffAppFun ea env rho k))
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho ea
        (KEffAppArg closure_env closure_rho f x ec ee k))
      ty_out.
Proof.
  intros heap env rho ea k closure_env closure_rho f x ec ee ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty_arg) (ty_res := ty_arg_res)
    (eff := eff_arg); eauto.
  eapply NRRKS_EffAppArg with
    (gamma := gamma0) (omega := omega0)
    (ty_arg := ty_arg0) (ty_body := ty_body0)
    (eff_body := eff_body0) (eff_summary := eff_summary0);
    eauto.
Qed.

Lemma NRegularResolvedStateShape_mu_app_body_preservation :
  forall heap v_arg closure_env closure_rho f x ec ee k ty_out,
    NRegularResolvedStateShape
      (StReturn heap v_arg
        (KMuAppArg closure_env closure_rho f x ec ee k))
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap
        (env_extend x v_arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho
        ec
        k)
      ty_out.
Proof.
  intros heap v_arg closure_env closure_rho f x ec ee k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NRRSS_Eval with
    (gamma :=
      (x, ty_arg) ::
      (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
    (omega := omega)
    (ty := ty_body) (ty_res := ty_body_res) (eff := eff_body);
    eauto.
  eapply NRegularResolvedEnvShape_extend with
    (ty_res := ty); eauto.
  eapply NRegularResolvedEnvShape_extend with
    (ty_res := TyArrow
      ty eff_body_res ty_body_res eff_summary_res);
    eauto.
  - eapply NResolve_Arrow; eauto.
  - eapply NRRVS_Closure with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body); eauto.
Qed.

Lemma NRegularResolvedStateShape_eff_app_body_preservation :
  forall heap v_arg closure_env closure_rho f x ec ee k ty_out,
    NRegularResolvedStateShape
      (StReturn heap v_arg
        (KEffAppArg closure_env closure_rho f x ec ee k))
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap
        (env_extend x v_arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho
        ee
        k)
      ty_out.
Proof.
  intros heap v_arg closure_env closure_rho f x ec ee k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NRRSS_Eval with
    (gamma :=
      (x, ty_arg) ::
      (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
    (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary);
    eauto using NResolve_Effect.
  eapply NRegularResolvedEnvShape_extend with
    (ty_res := ty); eauto.
  eapply NRegularResolvedEnvShape_extend with
    (ty_res := TyArrow
      ty eff_body_res ty_body_res eff_summary_res);
    eauto.
  - eapply NResolve_Arrow; eauto.
  - eapply NRRVS_Closure with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body); eauto.
Qed.

Lemma NRegularResolvedStateShape_rgn_app_eval_preservation :
  forall heap env rho er r k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho (ERgnApp er r) k)
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho er (KRgnApp r rho k))
      ty_out.
Proof.
  intros heap env rho er r k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty_result ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  match goal with
  | HWF : region_expr_wf omega r |- _ =>
      destruct (NRhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ H8) as HFunWF.
  inversion HFunWF; subst.
  destruct
    (NResolveStaticEffect_exists 1 omega rho eff_body0 HRho H9)
    as (eff_body_res & HEffResolve).
  destruct
    (NResolveTy_exists 1 omega rho ty0 HRho H10)
    as (ty_body_res & HTyResolve).
  pose proof
    (NResolveTy_open_ty
      rho r ty0 ty_body_res r_val HRgn HTyResolve)
    as HOpenResolve.
  rewrite H4 in HOpenResolve.
  pose proof
    (NResolveTy_deterministic
      rho (open_ty r ty) ty_res
      (open_ty_type (region_const_type r_val) ty_body_res)
      HResolve HOpenResolve)
    as HTyResEq.
  subst ty_res.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyForallRgn eff_body0 ty0)
    (ty_res := TyForallRgn eff_body_res ty_body_res)
    (eff := eff_f0);
    eauto.
  - eapply NResolve_ForallRgn; eauto.
  - eapply NRRKS_RgnApp; eauto.
Qed.

Lemma NRegularResolvedStateShape_rgn_app_return_preservation :
  forall heap closure_env closure_rho x e arg_rho r r_val k ty_out,
    eval_region arg_rho r = Some r_val ->
    NRegularResolvedStateShape
      (StReturn heap
        (VRegionClosure closure_env closure_rho x e)
        (KRgnApp r arg_rho k))
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap closure_env
        (rho_extend x r_val closure_rho)
        e
        k)
      ty_out.
Proof.
  intros heap closure_env closure_rho x e arg_rho r r_val k ty_out
    HRgn HState.
  inversion HState as
    [| heap0 v0 k0 ty_in ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HV; subst.
  inversion HK; subst.
  match goal with
  | HRgnKont : eval_region arg_rho r = Some ?r_val0 |- _ =>
      rewrite HRgn in HRgnKont;
      inversion HRgnKont; subst; clear HRgnKont
  end.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := x :: omega)
    (ty := ty)
    (ty_res := open_ty_type (region_const_type r_val0) ty_res)
    (eff := eff);
    eauto.
  - eapply NRegularResolvedEnvShape_extend_fresh;
      eauto using
        NCheckedRegionBody_fresh,
        NCheckedRegionBody_ctx_wf.
  - eapply NRhoModels_extend; eauto.
  - eapply NResolveTy_rho_extend_close_ty.
    + exact
        (NCheckedTcExp_ty_wf
          _ _ _ _ _
          (NCheckedRegionBody_checked _ _ _ _ _ _ H9)).
    + eauto.
  - exact (NCheckedRegionBody_checked _ _ _ _ _ _ H9).
Qed.

Lemma NRegularResolvedStateShape_pair_par_eval_preservation :
  forall heap env rho ef1 ea1 ef2 ea2 k ty_out,
    NRegularResolvedStateShape
      (StEval heap env rho
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)) k)
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho (EEffApp ef1 ea1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      ty_out.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (NCheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary0).
  - exact HHeap.
  - exact HEnv.
  - exact HRho.
  - eapply NResolve_Effect.
  - exact H14.
  - eapply NRRKS_PairParEff1 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff0) (eff2 := eff3)
      (eff_summary2 := eff_summary3);
      eauto.
Qed.

Lemma NRegularResolvedStateShape_pair_par_eff1_preservation :
  forall heap theta1 ef1 ea1 ef2 ea2 env rho k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VSummary theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      ty_out ->
    NRegularResolvedStateShape
      (StEval heap env rho (EEffApp ef2 ea2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      ty_out.
Proof.
  intros heap theta1 ef1 ea1 ef2 ea2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary2);
    eauto using NResolve_Effect.
  eapply NRRKS_PairParEff2 with
    (gamma := gamma) (omega := omega)
    (ty1 := ty1) (ty2 := ty2)
    (eff1 := eff1) (eff2 := eff2);
    eauto.
Qed.

Lemma NRegularResolvedStateShape_pair_par_check_pass_preservation :
  forall heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      ty_out ->
    NRegularResolvedStateShape
      (StPairParRun
        (StEval heap env rho (EMuApp ef1 ea1) KDone)
        (StEval heap env rho (EMuApp ef2 ea2) KDone)
        [] [] k)
      ty_out.
Proof.
  intros heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRRSS_PairParRun with
    (heap := heap) (ty1 := ty1_res) (ty2 := ty2_res);
    simpl; eauto.
  - eapply NRRSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty1) (ty_res := ty1_res) (eff := eff1);
      eauto.
    constructor.
  - eapply NRRSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty2) (ty_res := ty2_res) (eff := eff2);
      eauto.
    constructor.
Qed.

Lemma NRegularResolvedStateShape_pair_par_check_fail_preservation :
  forall heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out,
    NRegularResolvedStateShape
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      ty_out ->
    NRegularResolvedStateShape (StError heap) ty_out.
Proof.
  intros heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  eapply NRRSS_Error; eauto.
Qed.

Lemma NRegularResolvedStateShape_pair_par_done_pass_preservation :
  forall heap v1 v2 phi_left phi_right k ty_out,
    NRegularResolvedStateShape
      (StPairParRun
        (StDone heap v1)
        (StDone heap v2)
        phi_left phi_right k)
      ty_out ->
    NRegularResolvedStateShape (StReturn heap (VPair v1 v2) k) ty_out.
Proof.
  intros heap v1 v2 phi_left phi_right k ty_out HState.
  inversion HState as
    [| | | |
      left_state right_state phi_left0 phi_right0 k0 heap0
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    subst; clear HState; simpl in *; subst.
  inversion HLeft as [| | heap1 v_left ty_left HHeap1 HV1 | |];
    subst; clear HLeft.
  inversion HRight as [| | heap2 v_right ty_right HHeap2 HV2 | |];
    subst; clear HRight.
  eapply NRRSS_Return; eauto.
  eapply NRRVS_Pair; eauto.
Qed.

Lemma NRegularResolvedStateShape_pair_par_done_fail_preservation :
  forall heap v1 v2 phi_left phi_right k ty_out,
    NRegularResolvedStateShape
      (StPairParRun
        (StDone heap v1)
        (StDone heap v2)
        phi_left phi_right k)
      ty_out ->
    NRegularResolvedStateShape (StError heap) ty_out.
Proof.
  intros heap v1 v2 phi_left phi_right k ty_out HState.
  inversion HState as
    [| | | |
      left_state right_state phi_left0 phi_right0 k0 heap0
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    subst; clear HState; simpl in *; subst.
  inversion HLeft; subst.
  eapply NRRSS_Error; eauto.
Qed.

Lemma NRegularResolvedStateShape_pair_par_run_left_preservation :
  forall left_state right_state phi_left phi_right k
    label left_state' ty_out,
    NStep left_state label left_state' ->
    NStateHeapsAligned
      (StPairParRun left_state right_state phi_left phi_right k) ->
    HeapNeutralTrace (label_trace label) ->
    (forall ty,
      NRegularResolvedStateShape left_state ty ->
      NRegularResolvedStateShape left_state' ty) ->
    NRegularResolvedStateShape
      (StPairParRun left_state right_state phi_left phi_right k)
      ty_out ->
    NRegularResolvedStateShape
      (StPairParRun
        left_state'
        (with_state_heap (state_heap left_state') right_state)
        (phi_left ++ label_trace label)
        phi_right
        k)
      ty_out.
Proof.
  intros left_state right_state phi_left phi_right k
    label left_state' ty_out HStep HAligned HNeutral HPreserve HState.
  inversion HState as
    [| | | |
      left_state0 right_state0 phi_left0 phi_right0 k0 heap
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    subst; clear HState.
  destruct HAligned as (HAlignedLeft & HAlignedRight & HHeapAligned).
  destruct
    (NStep_heap_neutral_preserves_alignment
      left_state label left_state' HStep HAlignedLeft HNeutral)
    as (_ & HHeapStep).
  assert
    (HRightSame :
      with_state_heap (state_heap left_state') right_state = right_state).
  {
    eapply with_state_heap_aligned_same.
    - exact HAlignedRight.
    - rewrite HHeapStep.
      symmetry. exact HHeapAligned.
  }
  rewrite HRightSame.
  eapply NRRSS_PairParRun with (ty1 := ty1) (ty2 := ty2); eauto.
Qed.

Lemma NRegularResolvedStateShape_pair_par_run_left_preservation_from_child :
  forall left_state right_state phi_left phi_right k
    label left_state' ty_out,
    NStep left_state label left_state' ->
    HeapNeutralTrace (label_trace label) ->
    (forall ty,
      NRegularResolvedStateShape left_state ty ->
      NRegularResolvedStateShape left_state' ty) ->
    NRegularResolvedStateShape
      (StPairParRun left_state right_state phi_left phi_right k)
      ty_out ->
    NRegularResolvedStateShape
      (StPairParRun
        left_state'
        (with_state_heap (state_heap left_state') right_state)
        (phi_left ++ label_trace label)
        phi_right
        k)
      ty_out.
Proof.
  intros left_state right_state phi_left phi_right k
    label left_state' ty_out HStep HNeutral HPreserve HState.
  eapply NRegularResolvedStateShape_pair_par_run_left_preservation; eauto.
  eapply NRegularResolvedStateShape_aligned; eauto.
Qed.

Lemma NRegularResolvedStateShape_pair_par_run_right_preservation :
  forall heap v1 right_state phi_left phi_right k
    label right_state' ty_out,
    NStep right_state label right_state' ->
    NStateHeapsAligned
      (StPairParRun (StDone heap v1) right_state phi_left phi_right k) ->
    HeapNeutralTrace (label_trace label) ->
    (forall ty,
      NRegularResolvedStateShape right_state ty ->
      NRegularResolvedStateShape right_state' ty) ->
    NRegularResolvedStateShape
      (StPairParRun (StDone heap v1) right_state phi_left phi_right k)
      ty_out ->
    NRegularResolvedStateShape
      (StPairParRun
        (with_state_heap (state_heap right_state') (StDone heap v1))
        right_state'
        phi_left
        (phi_right ++ label_trace label)
        k)
      ty_out.
Proof.
  intros heap v1 right_state phi_left phi_right k
    label right_state' ty_out HStep HAligned HNeutral HPreserve HState.
  inversion HState as
    [| | | |
      left_state0 right_state0 phi_left0 phi_right0 k0 heap0
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    clear HState.
  subst left_state0 right_state0 phi_left0 phi_right0 k0 ty_out0.
  simpl in HHeapLeft.
  subst heap0.
  destruct HAligned as (_ & HAlignedRight & _).
  destruct
    (NStep_heap_neutral_preserves_alignment
      right_state label right_state' HStep HAlignedRight HNeutral)
    as (_ & HHeapStep).
  assert (HRightHeap' : state_heap right_state' = heap).
  {
    rewrite HHeapStep.
    exact HHeapRight.
  }
  simpl.
  rewrite HRightHeap'.
  eapply NRRSS_PairParRun with
    (heap := heap) (ty1 := ty1) (ty2 := ty2); eauto.
Qed.

Lemma NRegularResolvedStateShape_pair_par_run_right_preservation_from_child :
  forall heap v1 right_state phi_left phi_right k
    label right_state' ty_out,
    NStep right_state label right_state' ->
    HeapNeutralTrace (label_trace label) ->
    (forall ty,
      NRegularResolvedStateShape right_state ty ->
      NRegularResolvedStateShape right_state' ty) ->
    NRegularResolvedStateShape
      (StPairParRun (StDone heap v1) right_state phi_left phi_right k)
      ty_out ->
    NRegularResolvedStateShape
      (StPairParRun
        (with_state_heap (state_heap right_state') (StDone heap v1))
        right_state'
        phi_left
        (phi_right ++ label_trace label)
        k)
      ty_out.
Proof.
  intros heap v1 right_state phi_left phi_right k
    label right_state' ty_out HStep HNeutral HPreserve HState.
  eapply NRegularResolvedStateShape_pair_par_run_right_preservation; eauto.
  eapply NRegularResolvedStateShape_aligned; eauto.
Qed.

Lemma NRegularResolvedStateShape_pair_par_left_error_preservation :
  forall heap right_state phi_left phi_right k ty_out,
    NRegularResolvedStateShape
      (StPairParRun (StError heap) right_state phi_left phi_right k)
      ty_out ->
    NRegularResolvedStateShape (StError heap) ty_out.
Proof.
  intros heap right_state phi_left phi_right k ty_out HState.
  inversion HState as
    [| | | |
      left_state right_state0 phi_left0 phi_right0 k0 heap0
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    clear HState.
  subst left_state right_state0 phi_left0 phi_right0 k0 ty_out0.
  simpl in HHeapLeft.
  subst heap0.
  inversion HLeft; subst.
  eapply NRRSS_Error; eauto.
Qed.

Lemma NRegularResolvedStateShape_pair_par_right_error_preservation :
  forall heap_left v1 heap_right phi_left phi_right k ty_out,
    NRegularResolvedStateShape
      (StPairParRun
        (StDone heap_left v1)
        (StError heap_right)
        phi_left phi_right k)
      ty_out ->
    NRegularResolvedStateShape (StError heap_right) ty_out.
Proof.
  intros heap_left v1 heap_right phi_left phi_right k ty_out HState.
  inversion HState as
    [| | | |
      left_state right_state phi_left0 phi_right0 k0 heap
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    clear HState.
  subst left_state right_state phi_left0 phi_right0 k0 ty_out0.
  simpl in HHeapRight.
  subst heap.
  inversion HRight; subst.
  eapply NRRSS_Error; eauto.
Qed.

Theorem NStep_heap_neutral_regular_state_preservation :
  forall state label state' ty,
    NStep state label state' ->
    HeapNeutralTrace (label_trace label) ->
    NRegularResolvedStateShape state ty ->
    NRegularResolvedStateShape state' ty.
Proof.
  intros state label state' ty HStep.
  revert ty.
  induction HStep; intros ty_out HNeutral HState; simpl in HNeutral.
  - eapply NRegularResolvedStateShape_const_preservation; eauto.
  - eapply NRegularResolvedStateShape_bool_preservation; eauto.
  - eapply NRegularResolvedStateShape_var_preservation; eauto.
  - eapply NRegularResolvedStateShape_mu_preservation; eauto.
  - eapply NRegularResolvedStateShape_lambda_rgn_preservation; eauto.
  - eapply NRegularResolvedStateShape_mu_app_eval_preservation; eauto.
  - eapply NRegularResolvedStateShape_mu_app_eval_arg_preservation; eauto.
  - eapply NRegularResolvedStateShape_mu_app_body_preservation; eauto.
  - eapply NRegularResolvedStateShape_eff_app_eval_preservation; eauto.
  - eapply NRegularResolvedStateShape_eff_app_eval_arg_preservation; eauto.
  - eapply NRegularResolvedStateShape_eff_app_body_preservation; eauto.
  - eapply NRegularResolvedStateShape_pair_par_eval_preservation; eauto.
  - eapply NRegularResolvedStateShape_pair_par_eff1_preservation; eauto.
  - eapply NRegularResolvedStateShape_pair_par_check_pass_preservation; eauto.
  - eapply NRegularResolvedStateShape_pair_par_check_fail_preservation; eauto.
  - eapply NRegularResolvedStateShape_pair_par_run_left_preservation_from_child;
      eauto.
  - eapply NRegularResolvedStateShape_pair_par_run_right_preservation_from_child;
      eauto.
  - eapply NRegularResolvedStateShape_pair_par_left_error_preservation; eauto.
  - eapply NRegularResolvedStateShape_pair_par_right_error_preservation; eauto.
  - eapply NRegularResolvedStateShape_pair_par_done_pass_preservation; eauto.
  - eapply NRegularResolvedStateShape_pair_par_done_fail_preservation; eauto.
  - eapply NRegularResolvedStateShape_rgn_app_eval_preservation; eauto.
  - eapply NRegularResolvedStateShape_rgn_app_return_preservation; eauto.
  - eapply NRegularResolvedStateShape_empty_preservation; eauto.
  - eapply NRegularResolvedStateShape_top_preservation; eauto.
  - eapply NRegularResolvedStateShape_cond_eval_preservation; eauto.
  - eapply NRegularResolvedStateShape_cond_true_preservation; eauto.
  - eapply NRegularResolvedStateShape_cond_false_preservation; eauto.
  - eapply NRegularResolvedStateShape_ref_eval_preservation; eauto.
  - destruct HNeutral as (HNoAlloc & _).
    exfalso. eapply HNoAlloc.
    simpl. left. reflexivity.
  - eapply NRegularResolvedStateShape_deref_eval_preservation; eauto.
  - eapply NRegularResolvedStateShape_deref_preservation; eauto.
  - eapply NRegularResolvedStateShape_assign_eval_preservation; eauto.
  - eapply NRegularResolvedStateShape_assign_loc_preservation; eauto.
  - destruct HNeutral as (_ & HReadOnly).
    exfalso. eapply HReadOnly.
    simpl. left. reflexivity.
  - eapply NRegularResolvedStateShape_plus_eval_preservation; eauto.
  - eapply NRegularResolvedStateShape_plus_l_preservation; eauto.
  - eapply NRegularResolvedStateShape_plus_r_preservation; eauto.
  - eapply NRegularResolvedStateShape_minus_eval_preservation; eauto.
  - eapply NRegularResolvedStateShape_minus_l_preservation; eauto.
  - eapply NRegularResolvedStateShape_minus_r_preservation; eauto.
  - eapply NRegularResolvedStateShape_times_eval_preservation; eauto.
  - eapply NRegularResolvedStateShape_times_l_preservation; eauto.
  - eapply NRegularResolvedStateShape_times_r_preservation; eauto.
  - eapply NRegularResolvedStateShape_eq_eval_preservation; eauto.
  - eapply NRegularResolvedStateShape_eq_l_preservation; eauto.
  - eapply NRegularResolvedStateShape_eq_r_preservation; eauto.
  - eapply NRegularResolvedStateShape_alloc_abs_preservation; eauto.
  - eapply NRegularResolvedStateShape_read_abs_preservation; eauto.
  - eapply NRegularResolvedStateShape_write_abs_preservation; eauto.
  - eapply NRegularResolvedStateShape_read_conc_eval_preservation; eauto.
  - eapply NRegularResolvedStateShape_read_conc_preservation; eauto.
  - eapply NRegularResolvedStateShape_write_conc_eval_preservation; eauto.
  - eapply NRegularResolvedStateShape_write_conc_preservation; eauto.
  - eapply NRegularResolvedStateShape_concat_eval_preservation; eauto.
  - eapply NRegularResolvedStateShape_concat_l_preservation; eauto.
  - eapply NRegularResolvedStateShape_concat_r_preservation; eauto.
  - eapply NRegularResolvedStateShape_done_preservation; eauto.
Qed.

Lemma NSteps_heap_neutral_regular_state_preservation_from_step :
  forall
    (step_preserve :
      forall state label state' ty,
        NStep state label state' ->
        HeapNeutralTrace (label_trace label) ->
        NRegularResolvedStateShape state ty ->
        NRegularResolvedStateShape state' ty)
    state phi state' ty,
    NSteps state phi state' ->
    HeapNeutralTrace phi ->
    NRegularResolvedStateShape state ty ->
    NRegularResolvedStateShape state' ty.
Proof.
  intros step_preserve state phi state' ty HSteps.
  induction HSteps as
    [state | state label state1 phi state2 HStep _ IH];
    intros HNeutral HState.
  - exact HState.
  - eapply IH.
    + eapply heap_neutral_trace_app_r. exact HNeutral.
    + eapply step_preserve.
      * exact HStep.
      * eapply heap_neutral_trace_app_l. exact HNeutral.
      * exact HState.
Qed.

Theorem NSteps_heap_neutral_regular_state_preservation :
  forall state phi state' ty,
    NSteps state phi state' ->
    HeapNeutralTrace phi ->
    NRegularResolvedStateShape state ty ->
    NRegularResolvedStateShape state' ty.
Proof.
  intros state phi state' ty HSteps HNeutral HState.
  eapply NSteps_heap_neutral_regular_state_preservation_from_step;
    eauto.
  intros state0 label state1 ty0 HStep HStepNeutral HState0.
  eapply NStep_heap_neutral_regular_state_preservation; eauto.
Qed.

Lemma NStepsN_heap_neutral_regular_state_preservation_from_step :
  forall
    (step_preserve :
      forall state label state' ty,
        NStep state label state' ->
        HeapNeutralTrace (label_trace label) ->
        NRegularResolvedStateShape state ty ->
        NRegularResolvedStateShape state' ty)
    n state phi state' ty,
    NStepsN n state phi state' ->
    HeapNeutralTrace phi ->
    NRegularResolvedStateShape state ty ->
    NRegularResolvedStateShape state' ty.
Proof.
  intros step_preserve n state phi state' ty HSteps.
  induction HSteps as
    [state | n state label state1 phi state2 HStep _ IH];
    intros HNeutral HState.
  - exact HState.
  - eapply IH.
    + eapply heap_neutral_trace_app_r. exact HNeutral.
    + eapply step_preserve.
      * exact HStep.
      * eapply heap_neutral_trace_app_l. exact HNeutral.
      * exact HState.
Qed.

Theorem NStepsN_heap_neutral_regular_state_preservation :
  forall n state phi state' ty,
    NStepsN n state phi state' ->
    HeapNeutralTrace phi ->
    NRegularResolvedStateShape state ty ->
    NRegularResolvedStateShape state' ty.
Proof.
  intros n state phi state' ty HSteps HNeutral HState.
  eapply NStepsN_heap_neutral_regular_state_preservation_from_step;
    eauto.
  intros state0 label state1 ty0 HStep HStepNeutral HState0.
  eapply NStep_heap_neutral_regular_state_preservation; eauto.
Qed.
