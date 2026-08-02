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

(** Preservation for checked/regular resolved state shapes.

    The repeated case lemmas in this file are proof scaffolding for the compact
    endpoints re-exported by [Runtime.PreservationPublic]. *)

Lemma RegularResolvedStateShape_const_preservation :
  forall heap env rho n k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho (EConst n) k)
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap (VNat n) k)
      ty_out.
Proof.
  intros heap env rho n k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply RRSS_Return; eauto using RRVS_Nat.
Qed.

Lemma RegularResolvedStateShape_bool_preservation :
  forall heap env rho b k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho (EBool b) k)
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap (VBool b) k)
      ty_out.
Proof.
  intros heap env rho b k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply RRSS_Return; eauto using RRVS_Bool.
Qed.

Lemma RegularResolvedStateShape_var_preservation :
  forall heap env rho x v k ty_out,
    env_lookup x env = Some v ->
    RegularResolvedStateShape
      (StEval heap env rho (EVar x) k)
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap v k)
      ty_out.
Proof.
  intros heap env rho x v k ty_out HLookup HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  match goal with
  | HBind : ctx_binds x ty gamma |- _ =>
      destruct
        (RegularResolvedEnvShape_lookup
          rho heap env gamma x ty ty_res HEnv HBind HResolve)
        as (v_typed & HLookupTyped & HV)
  end.
  rewrite HLookup in HLookupTyped.
  inversion HLookupTyped; subst.
  eapply RRSS_Return; eauto.
Qed.

Lemma RegularResolvedStateShape_mu_preservation :
  forall heap env rho f x ec ee k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho (EMu f x ec ee) k)
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap (VClosure env rho f x ec ee) k)
      ty_out.
Proof.
  intros heap env rho f x ec ee k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ HReg) as HTyWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  inversion HTyWF; subst.
  eapply RRSS_Return; eauto.
  eapply RRVS_Closure with
    (gamma := gamma) (omega := omega)
    (ty_arg := ty_arg) (ty_body := ty_body); eauto.
Qed.

Lemma RegularResolvedStateShape_lambda_rgn_preservation :
  forall heap env rho x e k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho (ELambdaRgn x e) k)
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap (VRegionClosure env rho x e) k)
      ty_out.
Proof.
  intros heap env rho x e k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ HReg) as HTyWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  inversion HTyWF; subst.
  eapply RRSS_Return; eauto.
  eapply RRVS_RegionClosure with
    (gamma := gamma) (omega := omega)
    (ty := ty) (eff := eff); eauto.
  - rewrite H1. exact H4.
  - rewrite H2. exact H11.
  - constructor; eauto.
Qed.

Lemma RegularResolvedStateShape_empty_preservation :
  forall heap env rho k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho EEmpty k)
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap (VSummary (SummarySet [])) k)
      ty_out.
Proof.
  intros heap env rho k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply RRSS_Return; eauto using RRVS_Summary.
Qed.

Lemma RegularResolvedStateShape_top_preservation :
  forall heap env rho k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho ETop k)
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap (VSummary SummaryTop) k)
      ty_out.
Proof.
  intros heap env rho k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply RRSS_Return; eauto using RRVS_Summary.
Qed.

Lemma RegularResolvedStateShape_cond_eval_preservation :
  forall heap env rho e et ef k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho (ECond e et ef) k)
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho e (KCond et ef env rho k))
      ty_out.
Proof.
  intros heap env rho e et ef k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ HReg) as HTyWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyBool) (ty_res := TyBool) (eff := eff_e0);
    eauto using Resolve_Bool.
  eapply RRKS_Cond with
    (gamma := gamma) (omega := omega)
    (ty := ty) (ty_res := ty_res)
    (eff_t := eff_t0) (eff_f := eff_f0); eauto.
Qed.

Lemma RegularResolvedStateShape_ref_eval_preservation :
  forall heap env rho r e r_val k ty_out,
    eval_region rho r = Some r_val ->
    RegularResolvedStateShape
      (StEval heap env rho (ERef r e) k)
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho e (KRef r_val k))
      ty_out.
Proof.
  intros heap env rho r e r_val k ty_out
    HRgn HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ HReg) as HTyWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  match goal with
  | HRgnResolved :
      ResolveRegionType rho (region_expr_to_type r) ?rgn_res |- _ =>
      pose proof
        (ResolveRegionType_region_expr_to_type rho r r_val HRgn)
        as HRgnExpected;
      pose proof
        (ResolveRegionType_deterministic
          rho (region_expr_to_type r) rgn_res
          (region_const_type r_val)
          HRgnResolved HRgnExpected);
      subst rgn_res
  end.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty0) (ty_res := ty') (eff := eff0);
    eauto.
  - eapply RRKS_Ref; eauto.
Qed.

Lemma RegularResolvedStateShape_ref_return_preservation_bounded :
  forall heap v r_val k l heap' ty_out,
    HeapKeysBounded heap ->
    heap_alloc r_val v heap = (l, heap') ->
    RegularResolvedStateShape
      (StReturn heap v (KRef r_val k))
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap' (VLoc r_val l) k)
      ty_out.
Proof.
  intros heap v r_val k l heap' ty_out
    HBounded HAlloc HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HVal HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply RRSS_Return with
    (ty := TyRef (region_const_type r_val) ty).
  - eapply RegularResolvedHeapShape_alloc; eauto.
  - eapply RRVS_Loc.
    + eapply heap_lookup_alloc_same; eauto.
    + eapply RegularResolvedValShape_heap_alloc; eauto.
  - eapply RegularResolvedKontShape_heap_alloc; eauto.
Qed.

Lemma StoreResolvedStateShape_ref_return_preservation :
  forall store heap v r_val k l heap' ty_out,
    heap_alloc r_val v heap = (l, heap') ->
    StoreResolvedStateShape store
      (StReturn heap v (KRef r_val k))
      ty_out ->
    exists store',
      StoreResolvedStateShape store'
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
  eapply SRSS_Return with
    (ty := TyRef (region_const_type r_val) ty).
  - eapply StoreKeysBoundedByHeap_alloc; eauto.
  - eapply StoreResolvedHeapShape_alloc; eauto.
  - eapply SRVS_Loc.
    apply store_ty_lookup_extend_same.
  - destruct (heap_alloc_result heap r_val v l heap') as [HFresh _];
      [exact HAlloc |].
    eapply StoreResolvedKontShape_store_extend; eauto.
Qed.

Lemma RegularResolvedStateShape_deref_eval_preservation :
  forall heap env rho r e k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho (EDeref r e) k)
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho e (KDeref r k))
      ty_out.
Proof.
  intros heap env rho r e k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ HReg) as HTyWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  match goal with
  | HWF : region_expr_wf omega r |- _ =>
      destruct (RhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyRef (region_expr_to_type r) ty)
    (ty_res := TyRef (region_const_type r_val) ty_res)
    (eff := eff0); eauto.
  - eapply Resolve_Ref; eauto.
    eapply ResolveRegionType_region_expr_to_type.
    exact HRgn.
  - eapply RRKS_Deref; eauto.
Qed.

Lemma RegularResolvedStateShape_assign_eval_preservation :
  forall heap env rho r ea ev k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho (EAssign r ea ev) k)
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho ea (KAssignLoc r ev env rho k))
      ty_out.
Proof.
  intros heap env rho r ea ev k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  match goal with
  | HWF : region_expr_wf omega r |- _ =>
      destruct (RhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ H10) as HTyCellWF.
  destruct
    (ResolveTy_exists 0 omega rho ty HRho HTyCellWF)
    as (ty_cell_res & HTyResolve).
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyRef (region_expr_to_type r) ty)
    (ty_res := TyRef (region_const_type r_val) ty_cell_res)
    (eff := eff_a0);
    eauto.
  - eapply Resolve_Ref; eauto.
    eapply ResolveRegionType_region_expr_to_type.
    exact HRgn.
  - eapply RRKS_AssignLoc with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_cell_res)
      (eff_v := eff_v0);
    eauto.
Qed.

Lemma RegularResolvedStateShape_assign_loc_preservation :
  forall heap r_static ev env rho r l k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VLoc r l) (KAssignLoc r_static ev env rho k))
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho ev (KAssignVal r_static (VLoc r l) k))
      ty_out.
Proof.
  intros heap r_static ev env rho r l k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RRSS_Eval; eauto.
  eapply RRKS_AssignVal; eauto.
Qed.

Lemma StoreResolvedStateShape_assign_val_preservation :
  forall store heap r_static r l v k ty_out,
    StoreResolvedStateShape store
      (StReturn heap v (KAssignVal r_static (VLoc r l) k))
      ty_out ->
    StoreResolvedStateShape store
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
  | HLoc : StoreResolvedValShape store (VLoc r l)
      (TyRef (region_const_type ?r0) ?ty_cell) |- _ =>
      inversion HLoc; subst
  end.
  destruct HHeap as (HHeapToStore & HStoreToHeap).
  match goal with
  | HStoreLookup : store_ty_lookup ?r_loc ?l_loc store = Some ?ty_cell |- _ =>
      destruct (HStoreToHeap r_loc l_loc ty_cell HStoreLookup)
        as (old & HOldLookup & _);
      eapply SRSS_Return with (ty := TyUnit);
      [ eapply StoreKeysBoundedByHeap_update; eauto
      | eapply StoreResolvedHeapShape_update; eauto;
        split; [exact HHeapToStore | exact HStoreToHeap]
      | constructor
      | assumption ]
  end.
Qed.

Lemma StoreResolvedStateShape_const_preservation :
  forall store heap env rho n k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho (EConst n) k)
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap (VNat n) k)
      ty_out.
Proof.
  intros store heap env rho n k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply SRSS_Return; eauto using SRVS_Nat.
Qed.

Lemma StoreResolvedStateShape_bool_preservation :
  forall store heap env rho b k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho (EBool b) k)
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap (VBool b) k)
      ty_out.
Proof.
  intros store heap env rho b k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply SRSS_Return; eauto using SRVS_Bool.
Qed.

Lemma StoreResolvedStateShape_var_preservation :
  forall store heap env rho x v k ty_out,
    env_lookup x env = Some v ->
    StoreResolvedStateShape store
      (StEval heap env rho (EVar x) k)
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap v k)
      ty_out.
Proof.
  intros store heap env rho x v k ty_out HLookup HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  match goal with
  | HBind : ctx_binds x ty gamma |- _ =>
      destruct
        (StoreResolvedEnvShape_lookup
          store rho env gamma x ty ty_res HEnv HBind HResolve)
        as (v_typed & HLookupTyped & HV)
  end.
  rewrite HLookup in HLookupTyped.
  inversion HLookupTyped; subst.
  eapply SRSS_Return; eauto.
Qed.

Lemma StoreResolvedStateShape_mu_preservation :
  forall store heap env rho f x ec ee k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho (EMu f x ec ee) k)
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap (VClosure env rho f x ec ee) k)
      ty_out.
Proof.
  intros store heap env rho f x ec ee k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ HReg) as HTyWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  inversion HTyWF; subst.
  eapply SRSS_Return; eauto.
  eapply SRVS_Closure with
    (gamma := gamma) (omega := omega)
    (ty_arg := ty_arg) (ty_body := ty_body); eauto.
Qed.

Lemma StoreResolvedStateShape_lambda_rgn_preservation :
  forall store heap env rho x e k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho (ELambdaRgn x e) k)
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap (VRegionClosure env rho x e) k)
      ty_out.
Proof.
  intros store heap env rho x e k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ HReg) as HTyWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  inversion HTyWF; subst.
  eapply SRSS_Return; eauto.
  eapply SRVS_RegionClosure with
    (gamma := gamma) (omega := omega)
    (ty := ty) (eff := eff); eauto.
  - rewrite H1. exact H4.
  - rewrite H2. exact H11.
  - constructor; eauto.
Qed.

Lemma StoreResolvedStateShape_empty_preservation :
  forall store heap env rho k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho EEmpty k)
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap (VSummary (SummarySet [])) k)
      ty_out.
Proof.
  intros store heap env rho k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply SRSS_Return; eauto using SRVS_Summary.
Qed.

Lemma StoreResolvedStateShape_top_preservation :
  forall store heap env rho k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho ETop k)
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap (VSummary SummaryTop) k)
      ty_out.
Proof.
  intros store heap env rho k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply SRSS_Return; eauto using SRVS_Summary.
Qed.

Lemma StoreResolvedStateShape_alloc_abs_preservation :
  forall store heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    StoreResolvedStateShape store
      (StEval heap env rho (EAllocAbs r) k)
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap (VSummary (SummarySet [CAllocAbs r_val])) k)
      ty_out.
Proof.
  intros store heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply SRSS_Return; eauto using SRVS_Summary.
Qed.

Lemma StoreResolvedStateShape_read_abs_preservation :
  forall store heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    StoreResolvedStateShape store
      (StEval heap env rho (EReadAbs r) k)
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap (VSummary (SummarySet [CReadAbs r_val])) k)
      ty_out.
Proof.
  intros store heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply SRSS_Return; eauto using SRVS_Summary.
Qed.

Lemma StoreResolvedStateShape_write_abs_preservation :
  forall store heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    StoreResolvedStateShape store
      (StEval heap env rho (EWriteAbs r) k)
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap (VSummary (SummarySet [CWriteAbs r_val])) k)
      ty_out.
Proof.
  intros store heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply SRSS_Return; eauto using SRVS_Summary.
Qed.

Lemma StoreResolvedStateShape_read_conc_preservation :
  forall store heap r l k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VLoc r l) (KReadConc k))
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap (VSummary (SummarySet [CReadConc r l])) k)
      ty_out.
Proof.
  intros store heap r l k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply SRSS_Return; eauto using SRVS_Summary.
Qed.

Lemma StoreResolvedStateShape_write_conc_preservation :
  forall store heap r l k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VLoc r l) (KWriteConc k))
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap (VSummary (SummarySet [CWriteConc r l])) k)
      ty_out.
Proof.
  intros store heap r l k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply SRSS_Return; eauto using SRVS_Summary.
Qed.

Lemma StoreResolvedStateShape_done_preservation :
  forall store heap v ty_out,
    StoreResolvedStateShape store
      (StReturn heap v KDone)
      ty_out ->
    StoreResolvedStateShape store (StDone heap v) ty_out.
Proof.
  intros store heap v ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply SRSS_Done; eauto.
Qed.

Lemma StoreResolvedStateShape_ref_eval_preservation :
  forall store heap env rho r e r_val k ty_out,
    eval_region rho r = Some r_val ->
    StoreResolvedStateShape store
      (StEval heap env rho (ERef r e) k)
      ty_out ->
    StoreResolvedStateShape store
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
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  match goal with
  | HRgnResolved :
      ResolveRegionType rho (region_expr_to_type r) ?rgn_res |- _ =>
      pose proof
        (ResolveRegionType_region_expr_to_type rho r r_val HRgn)
        as HRgnExpected;
      pose proof
        (ResolveRegionType_deterministic
          rho (region_expr_to_type r) rgn_res
          (region_const_type r_val)
          HRgnResolved HRgnExpected);
      subst rgn_res
  end.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty0) (ty_res := ty') (eff := eff0).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - assumption.
  - assumption.
  - eapply SRKS_Ref; eauto.
Qed.

Lemma StoreResolvedStateShape_deref_eval_preservation :
  forall store heap env rho r e k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho (EDeref r e) k)
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho e (KDeref r k))
      ty_out.
Proof.
  intros store heap env rho r e k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  match goal with
  | HWF : region_expr_wf omega r |- _ =>
      destruct (RhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyRef (region_expr_to_type r) ty)
    (ty_res := TyRef (region_const_type r_val) ty_res)
    (eff := eff0).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - eapply Resolve_Ref; eauto.
    eapply ResolveRegionType_region_expr_to_type.
    exact HRgn.
  - assumption.
  - eapply SRKS_Deref; eauto.
Qed.

Lemma StoreResolvedStateShape_assign_eval_preservation :
  forall store heap env rho r ea ev k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho (EAssign r ea ev) k)
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho ea (KAssignLoc r ev env rho k))
      ty_out.
Proof.
  intros store heap env rho r ea ev k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  match goal with
  | HWF : region_expr_wf omega r |- _ =>
      destruct (RhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ H10) as HTyCellWF.
  destruct
    (ResolveTy_exists 0 omega rho ty HRho HTyCellWF)
    as (ty_cell_res & HTyResolve).
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyRef (region_expr_to_type r) ty)
    (ty_res := TyRef (region_const_type r_val) ty_cell_res)
    (eff := eff_a0).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - eapply Resolve_Ref; eauto.
    eapply ResolveRegionType_region_expr_to_type.
    exact HRgn.
  - assumption.
  - eapply SRKS_AssignLoc with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_cell_res)
      (eff_v := eff_v0);
    eauto.
Qed.

Lemma StoreResolvedStateShape_assign_loc_preservation :
  forall store heap r_static ev env rho r l k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VLoc r l) (KAssignLoc r_static ev env rho k))
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho ev (KAssignVal r_static (VLoc r l) k))
      ty_out.
Proof.
  intros store heap r_static ev env rho r l k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply SRSS_Eval; eauto.
  unfold StoreResolvedRuntimeShape.
  match goal with
  | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
      split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
  end.
  eapply SRKS_AssignVal; eauto.
Qed.

Lemma StoreResolvedStateShape_cond_eval_preservation :
  forall store heap env rho e et ef k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho (ECond e et ef) k)
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho e (KCond et ef env rho k))
      ty_out.
Proof.
  intros store heap env rho e et ef k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyBool) (ty_res := TyBool) (eff := eff_e0).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - constructor.
  - eassumption.
  - eapply SRKS_Cond with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_res)
      (eff_t := eff_t0) (eff_f := eff_f0);
      eauto.
Qed.

Lemma StoreResolvedStateShape_plus_eval_preservation :
  forall store heap env rho e1 e2 k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho (EPlus e1 e2) k)
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho e1 (KPlusL e2 env rho k))
      ty_out.
Proof.
  intros store heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff0).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - constructor.
  - eassumption.
  - eapply SRKS_PlusL; eauto.
Qed.

Lemma StoreResolvedStateShape_minus_eval_preservation :
  forall store heap env rho e1 e2 k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho (EMinus e1 e2) k)
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho e1 (KMinusL e2 env rho k))
      ty_out.
Proof.
  intros store heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff0).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - constructor.
  - eassumption.
  - eapply SRKS_MinusL; eauto.
Qed.

Lemma StoreResolvedStateShape_times_eval_preservation :
  forall store heap env rho e1 e2 k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho (ETimes e1 e2) k)
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho e1 (KTimesL e2 env rho k))
      ty_out.
Proof.
  intros store heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff0).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - constructor.
  - eassumption.
  - eapply SRKS_TimesL; eauto.
Qed.

Lemma StoreResolvedStateShape_eq_eval_preservation :
  forall store heap env rho e1 e2 k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho (EEq e1 e2) k)
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho e1 (KEqL e2 env rho k))
      ty_out.
Proof.
  intros store heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff0).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - constructor.
  - eassumption.
  - eapply SRKS_EqL; eauto.
Qed.

Lemma StoreResolvedStateShape_concat_eval_preservation :
  forall store heap env rho e1 e2 k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho (EConcat e1 e2) k)
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho e1 (KConcatL e2 env rho k))
      ty_out.
Proof.
  intros store heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff0).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - constructor.
  - eassumption.
  - eapply SRKS_ConcatL; eauto.
Qed.

Lemma StoreResolvedStateShape_cond_true_preservation :
  forall store heap et ef env rho k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VBool true) (KCond et ef env rho k))
      ty_out ->
    StoreResolvedStateShape store (StEval heap env rho et k) ty_out.
Proof.
  intros store heap et ef env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply SRSS_Eval; eauto.
  unfold StoreResolvedRuntimeShape.
  match goal with
  | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
      split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
  end.
Qed.

Lemma StoreResolvedStateShape_cond_false_preservation :
  forall store heap et ef env rho k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VBool false) (KCond et ef env rho k))
      ty_out ->
    StoreResolvedStateShape store (StEval heap env rho ef k) ty_out.
Proof.
  intros store heap et ef env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply SRSS_Eval; eauto.
  unfold StoreResolvedRuntimeShape.
  match goal with
  | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
      split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
  end.
Qed.

Lemma StoreResolvedStateShape_deref_preservation :
  forall store heap r_static r l v k ty_out,
    heap_lookup r l heap = Some v ->
    StoreResolvedStateShape store
      (StReturn heap (VLoc r l) (KDeref r_static k))
      ty_out ->
    StoreResolvedStateShape store (StReturn heap v k) ty_out.
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
      eapply SRSS_Return with (ty := ty_cell);
      [ exact HBounded
      | split; [exact HHeapToStore | exact HStoreToHeap]
      | exact HShapeFound
      | eauto ]
  end.
Qed.

Lemma StoreResolvedStateShape_plus_l_preservation :
  forall store heap n e2 env rho k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VNat n) (KPlusL e2 env rho k))
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho e2 (KPlusR n k))
      ty_out.
Proof.
  intros store heap n e2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - constructor.
  - assumption.
  - eapply SRKS_PlusR; eauto.
Qed.

Lemma StoreResolvedStateShape_plus_r_preservation :
  forall store heap n1 n2 k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VNat n2) (KPlusR n1 k))
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap (VNat (n1 + n2)) k)
      ty_out.
Proof.
  intros store heap n1 n2 k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply SRSS_Return; eauto using SRVS_Nat.
Qed.

Lemma StoreResolvedStateShape_minus_l_preservation :
  forall store heap n e2 env rho k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VNat n) (KMinusL e2 env rho k))
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho e2 (KMinusR n k))
      ty_out.
Proof.
  intros store heap n e2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - constructor.
  - assumption.
  - eapply SRKS_MinusR; eauto.
Qed.

Lemma StoreResolvedStateShape_minus_r_preservation :
  forall store heap n1 n2 k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VNat n2) (KMinusR n1 k))
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap (VNat (n1 - n2)) k)
      ty_out.
Proof.
  intros store heap n1 n2 k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply SRSS_Return; eauto using SRVS_Nat.
Qed.

Lemma StoreResolvedStateShape_times_l_preservation :
  forall store heap n e2 env rho k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VNat n) (KTimesL e2 env rho k))
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho e2 (KTimesR n k))
      ty_out.
Proof.
  intros store heap n e2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - constructor.
  - assumption.
  - eapply SRKS_TimesR; eauto.
Qed.

Lemma StoreResolvedStateShape_times_r_preservation :
  forall store heap n1 n2 k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VNat n2) (KTimesR n1 k))
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap (VNat (n1 * n2)) k)
      ty_out.
Proof.
  intros store heap n1 n2 k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply SRSS_Return; eauto using SRVS_Nat.
Qed.

Lemma StoreResolvedStateShape_eq_l_preservation :
  forall store heap n e2 env rho k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VNat n) (KEqL e2 env rho k))
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho e2 (KEqR n k))
      ty_out.
Proof.
  intros store heap n e2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - constructor.
  - assumption.
  - eapply SRKS_EqR; eauto.
Qed.

Lemma StoreResolvedStateShape_eq_r_preservation :
  forall store heap n1 n2 k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VNat n2) (KEqR n1 k))
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap (VBool (Nat.eqb n1 n2)) k)
      ty_out.
Proof.
  intros store heap n1 n2 k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply SRSS_Return; eauto using SRVS_Bool.
Qed.

Lemma StoreResolvedStateShape_concat_l_preservation :
  forall store heap theta1 e2 env rho k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VSummary theta1) (KConcatL e2 env rho k))
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho e2 (KConcatR theta1 k))
      ty_out.
Proof.
  intros store heap theta1 e2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - constructor.
  - assumption.
  - eapply SRKS_ConcatR; eauto.
Qed.

Lemma StoreResolvedStateShape_concat_r_preservation :
  forall store heap theta1 theta2 k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VSummary theta2) (KConcatR theta1 k))
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap (VSummary (summary_union theta1 theta2)) k)
      ty_out.
Proof.
  intros store heap theta1 theta2 k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply SRSS_Return; eauto using SRVS_Summary.
Qed.

Lemma StoreResolvedStateShape_mu_app_eval_preservation :
  forall store heap env rho ef ea k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho (EMuApp ef ea) k)
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho ef (KMuAppFun ea env rho k))
      ty_out.
Proof.
  intros store heap env rho ef ea k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ H7) as HFunWF.
  inversion HFunWF; subst.
  match goal with
  | HArgWF : TyWFAt 0 omega ty_arg0,
    HBodyEffWF : StaticEffectWFAt 0 omega eff_body0,
    HSummaryEffWF : StaticEffectWFAt 0 omega eff_summary0 |- _ =>
      destruct (ResolveTy_exists 0 omega rho ty_arg0 HRho HArgWF)
        as (ty_arg_res & HArgResolve);
      destruct
        (ResolveStaticEffect_exists
          0 omega rho eff_body0 HRho HBodyEffWF)
        as (eff_body_res & HBodyEffResolve);
      destruct
        (ResolveStaticEffect_exists
          0 omega rho eff_summary0 HRho HSummaryEffWF)
        as (eff_summary_res & HSummaryEffResolve);
      eapply SRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyArrow ty_arg0 eff_body0 ty eff_summary0)
        (ty_res := TyArrow
          ty_arg_res eff_body_res ty_res eff_summary_res)
        (eff := eff_f0);
      [ unfold StoreResolvedRuntimeShape;
        match goal with
        | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
            split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
        end
      | exact HRho
      | eapply Resolve_Arrow; eauto
      | eauto
      | eapply SRKS_MuAppFun with
          (gamma := gamma) (omega := omega)
          (ty_arg := ty_arg0) (ty_body := ty)
          (eff_body := eff_body0) (eff_summary := eff_summary0)
          (eff_arg := eff_a0);
        eauto ]
  end.
Qed.

Lemma StoreResolvedStateShape_eff_app_eval_preservation :
  forall store heap env rho ef ea k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho (EEffApp ef ea) k)
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho ef (KEffAppFun ea env rho k))
      ty_out.
Proof.
  intros store heap env rho ef ea k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ H5) as HFunWF.
  inversion HFunWF; subst.
  match goal with
  | HArgWF : TyWFAt 0 omega ?ty_arg0,
    HBodyEffWF : StaticEffectWFAt 0 omega ?eff_body0,
    HBodyWF : TyWFAt 0 omega ?ty_body0,
    HSummaryEffWF : StaticEffectWFAt 0 omega ?eff_summary0 |- _ =>
      destruct (ResolveTy_exists 0 omega rho ty_arg0 HRho HArgWF)
        as (ty_arg_res & HArgResolve);
      destruct
        (ResolveStaticEffect_exists
          0 omega rho eff_body0 HRho HBodyEffWF)
        as (eff_body_res & HBodyEffResolve);
      destruct (ResolveTy_exists 0 omega rho ty_body0 HRho HBodyWF)
        as (ty_body_res & HBodyResolve);
      destruct
        (ResolveStaticEffect_exists
          0 omega rho eff_summary0 HRho HSummaryEffWF)
        as (eff_summary_res & HSummaryEffResolve);
      eapply SRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyArrow ty_arg0 eff_body0 ty_body0 eff_summary0)
        (ty_res := TyArrow
          ty_arg_res eff_body_res ty_body_res eff_summary_res)
        (eff := eff_f0);
      [ unfold StoreResolvedRuntimeShape;
        match goal with
        | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
            split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
        end
      | exact HRho
      | eapply Resolve_Arrow; eauto
      | eauto
      | eapply SRKS_EffAppFun with
          (gamma := gamma) (omega := omega)
          (ty_arg := ty_arg0) (ty_body := ty_body0)
          (eff_body := eff_body0) (eff_summary := eff_summary0)
          (eff_arg := eff_a0);
        eauto ]
  end.
Qed.

Lemma StoreResolvedStateShape_mu_app_eval_arg_preservation :
  forall store heap env rho ea k closure_env closure_rho f x ec ee ty_out,
    StoreResolvedStateShape store
      (StReturn heap
        (VClosure closure_env closure_rho f x ec ee)
        (KMuAppFun ea env rho k))
      ty_out ->
    StoreResolvedStateShape store
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
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty_arg) (ty_res := ty_arg_res)
    (eff := eff_arg).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - assumption.
  - assumption.
  - eapply SRKS_MuAppArg with
      (gamma := gamma0) (omega := omega0)
      (ty_arg := ty_arg0) (ty_body := ty_body0)
      (eff_body := eff_body0) (eff_summary := eff_summary0);
    eauto.
Qed.

Lemma StoreResolvedStateShape_eff_app_eval_arg_preservation :
  forall store heap env rho ea k closure_env closure_rho f x ec ee ty_out,
    StoreResolvedStateShape store
      (StReturn heap
        (VClosure closure_env closure_rho f x ec ee)
        (KEffAppFun ea env rho k))
      ty_out ->
    StoreResolvedStateShape store
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
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty_arg) (ty_res := ty_arg_res)
    (eff := eff_arg).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - assumption.
  - assumption.
  - eapply SRKS_EffAppArg with
      (gamma := gamma0) (omega := omega0)
      (ty_arg := ty_arg0) (ty_body := ty_body0)
      (eff_body := eff_body0) (eff_summary := eff_summary0);
    eauto.
Qed.

Lemma StoreResolvedStateShape_mu_app_body_preservation :
  forall store heap v_arg closure_env closure_rho f x ec ee k ty_out,
    StoreResolvedStateShape store
      (StReturn heap v_arg
        (KMuAppArg closure_env closure_rho f x ec ee k))
      ty_out ->
    StoreResolvedStateShape store
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
  eapply SRSS_Eval with
    (gamma :=
      (x, ty_arg) ::
      (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
    (omega := omega)
    (ty := ty_body) (ty_res := ty_body_res) (eff := eff_body).
  - unfold StoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | ]].
    eapply StoreResolvedEnvShape_extend with
      (ty_res := ty); eauto.
    eapply StoreResolvedEnvShape_extend with
      (ty_res := TyArrow
        ty eff_body_res ty_body_res eff_summary_res);
      eauto.
    + eapply Resolve_Arrow; eauto.
    + eapply SRVS_Closure with
        (gamma := gamma) (omega := omega)
        (ty_arg := ty_arg) (ty_body := ty_body); eauto.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma StoreResolvedStateShape_eff_app_body_preservation :
  forall store heap v_arg closure_env closure_rho f x ec ee k ty_out,
    StoreResolvedStateShape store
      (StReturn heap v_arg
        (KEffAppArg closure_env closure_rho f x ec ee k))
      ty_out ->
    StoreResolvedStateShape store
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
  eapply SRSS_Eval with
    (gamma :=
      (x, ty_arg) ::
      (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
    (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary).
  - unfold StoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | ]].
    eapply StoreResolvedEnvShape_extend with
      (ty_res := ty); eauto.
    eapply StoreResolvedEnvShape_extend with
      (ty_res := TyArrow
        ty eff_body_res ty_body_res eff_summary_res);
      eauto.
    + eapply Resolve_Arrow; eauto.
    + eapply SRVS_Closure with
        (gamma := gamma) (omega := omega)
        (ty_arg := ty_arg) (ty_body := ty_body); eauto.
  - assumption.
  - constructor.
  - assumption.
  - assumption.
Qed.

Lemma StoreResolvedStateShape_read_conc_eval_preservation :
  forall store heap env rho e k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho (EReadConc e) k)
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho e (KReadConc k))
      ty_out.
Proof.
  intros store heap env rho e k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ H3) as HRefWF.
  inversion HRefWF; subst.
  match goal with
  | HRgnWF : RegionTypeWFAt 0 omega r0,
    HTyWF : TyWFAt 0 omega ty |- _ =>
      destruct
        (ResolveRegionType_exists 0 omega rho r0 HRho HRgnWF)
        as (rgn_res & HRgnResolve);
      destruct (ResolveTy_exists 0 omega rho ty HRho HTyWF)
        as (ty_ref_res & HTyResolve);
      destruct
        (ResolveRegionType_wf0_const
          omega rho r0 rgn_res HRgnWF HRgnResolve)
        as (r_val & HRgnResEq);
      subst rgn_res;
      eapply SRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyRef r0 ty)
        (ty_res := TyRef (region_const_type r_val) ty_ref_res)
        (eff := eff);
      [ unfold StoreResolvedRuntimeShape;
        match goal with
        | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
            split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
        end
      | exact HRho
      | eapply Resolve_Ref; eauto
      | eauto
      | eapply SRKS_ReadConc; eauto ]
  end.
Qed.

Lemma StoreResolvedStateShape_write_conc_eval_preservation :
  forall store heap env rho e k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho (EWriteConc e) k)
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho e (KWriteConc k))
      ty_out.
Proof.
  intros store heap env rho e k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ H3) as HRefWF.
  inversion HRefWF; subst.
  match goal with
  | HRgnWF : RegionTypeWFAt 0 omega r0,
    HTyWF : TyWFAt 0 omega ty |- _ =>
      destruct
        (ResolveRegionType_exists 0 omega rho r0 HRho HRgnWF)
        as (rgn_res & HRgnResolve);
      destruct (ResolveTy_exists 0 omega rho ty HRho HTyWF)
        as (ty_ref_res & HTyResolve);
      destruct
        (ResolveRegionType_wf0_const
          omega rho r0 rgn_res HRgnWF HRgnResolve)
        as (r_val & HRgnResEq);
      subst rgn_res;
      eapply SRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyRef r0 ty)
        (ty_res := TyRef (region_const_type r_val) ty_ref_res)
        (eff := eff);
      [ unfold StoreResolvedRuntimeShape;
        match goal with
        | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
            split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
        end
      | exact HRho
      | eapply Resolve_Ref; eauto
      | eauto
      | eapply SRKS_WriteConc; eauto ]
  end.
Qed.

Lemma StoreResolvedStateShape_rgn_app_eval_preservation :
  forall store heap env rho er r k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho (ERgnApp er r) k)
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho er (KRgnApp r rho k))
      ty_out.
Proof.
  intros store heap env rho er r k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty_result ty_res eff ty_out0
      HRuntime HRho HResolve HReg HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  match goal with
  | HWF : region_expr_wf omega r |- _ =>
      destruct (RhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ H8) as HFunWF.
  inversion HFunWF; subst.
  destruct
    (ResolveStaticEffect_exists 1 omega rho eff_body0 HRho H9)
    as (eff_body_res & HEffResolve).
  destruct
    (ResolveTy_exists 1 omega rho ty0 HRho H10)
    as (ty_body_res & HTyResolve).
  pose proof
    (ResolveTy_open_ty
      rho r ty0 ty_body_res r_val HRgn HTyResolve)
    as HOpenResolve.
  rewrite H4 in HOpenResolve.
  pose proof
    (ResolveTy_deterministic
      rho (open_ty r ty) ty_res
      (open_ty_type (region_const_type r_val) ty_body_res)
      HResolve HOpenResolve)
    as HTyResEq.
  subst ty_res.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyForallRgn eff_body0 ty0)
    (ty_res := TyForallRgn eff_body_res ty_body_res)
    (eff := eff_f0).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - eapply Resolve_ForallRgn; eauto.
  - assumption.
  - eapply SRKS_RgnApp; eauto.
Qed.

Lemma StoreResolvedStateShape_rgn_app_return_preservation :
  forall store heap closure_env closure_rho x e arg_rho r r_val k ty_out,
    eval_region arg_rho r = Some r_val ->
    StoreResolvedStateShape store
      (StReturn heap
        (VRegionClosure closure_env closure_rho x e)
        (KRgnApp r arg_rho k))
      ty_out ->
    StoreResolvedStateShape store
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
  eapply SRSS_Eval with
    (gamma := gamma) (omega := x :: omega)
    (ty := ty)
    (ty_res := open_ty_type (region_const_type r_val0) ty_res)
    (eff := eff).
  - unfold StoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | ]].
    eapply StoreResolvedEnvShape_extend_fresh;
      eauto using
        CheckedRegionBody_fresh,
        CheckedRegionBody_ctx_wf.
  - eapply RhoModels_extend; eauto.
  - eapply ResolveTy_rho_extend_close_ty.
    + exact
        (CheckedTcExp_ty_wf
          _ _ _ _ _
          (CheckedRegionBody_checked _ _ _ _ _ _ H9)).
    + eauto.
  - exact (CheckedRegionBody_checked _ _ _ _ _ _ H9).
  - assumption.
Qed.

Lemma StoreResolvedStateShape_pair_par_eval_preservation :
  forall store heap env rho ef1 ea1 ef2 ea2 k ty_out,
    StoreResolvedStateShape store
      (StEval heap env rho
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)) k)
      ty_out ->
    StoreResolvedStateShape store
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
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary0).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - exact HRho.
  - constructor.
  - exact H14.
  - eapply SRKS_PairParEff1 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff0) (eff2 := eff3)
      (eff_summary2 := eff_summary3);
      eauto.
Qed.

Lemma StoreResolvedStateShape_pair_par_eff1_preservation :
  forall store heap theta1 ef1 ea1 ef2 ea2 env rho k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VSummary theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      ty_out ->
    StoreResolvedStateShape store
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
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary2).
  - unfold StoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - constructor.
  - assumption.
  - eapply SRKS_PairParEff2 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff1) (eff2 := eff2);
      eauto.
Qed.

Lemma StoreResolvedStateShape_pair_par_check_pass_preservation :
  forall store heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      ty_out ->
    StoreResolvedStateShape store
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
  eapply SRSS_PairParRun with
    (heap := heap) (ty1 := ty1_res) (ty2 := ty2_res);
    simpl; eauto.
  - eapply SRSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty1) (ty_res := ty1_res) (eff := eff1).
    + unfold StoreResolvedRuntimeShape.
      match goal with
      | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
          split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
      end.
    + assumption.
    + assumption.
    + assumption.
    + constructor.
  - eapply SRSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty2) (ty_res := ty2_res) (eff := eff2).
    + unfold StoreResolvedRuntimeShape.
      match goal with
      | HEnvShape : StoreResolvedEnvShape store rho env gamma |- _ =>
          split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
      end.
    + assumption.
    + assumption.
    + assumption.
    + constructor.
Qed.

Lemma StoreResolvedStateShape_pair_par_check_fallback_preservation :
  forall store heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out,
    StoreResolvedStateShape store
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho (EMuApp ef1 ea1)
        (KPairParFallbackLeft ef2 ea2 env rho k))
      ty_out.
Proof.
  intros store heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out
    HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty1) (ty_res := ty1_res) (eff := eff1).
  - unfold StoreResolvedRuntimeShape.
    split; [assumption | split; assumption].
  - match goal with
    | H : RhoModels omega rho |- _ => exact H
    end.
  - match goal with
    | H : ResolveTy rho ty1 ty1_res |- _ => exact H
    end.
  - match goal with
    | H : CheckedTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 |- _ =>
        exact H
    end.
  - eapply SRKS_PairParFallbackLeft with
      (gamma := gamma) (omega := omega)
      (ty2 := ty2) (ty2_res := ty2_res) (eff2 := eff2);
      eauto.
Qed.

Lemma StoreResolvedStateShape_pair_par_fallback_left_return_preservation :
  forall store heap v_left ef2 ea2 env rho k ty_out,
    StoreResolvedStateShape store
      (StReturn heap v_left
        (KPairParFallbackLeft ef2 ea2 env rho k))
      ty_out ->
    StoreResolvedStateShape store
      (StEval heap env rho (EMuApp ef2 ea2)
        (KPairParFallbackRight v_left k))
      ty_out.
Proof.
  intros store heap v_left ef2 ea2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty2) (ty_res := ty2_res) (eff := eff2).
  - unfold StoreResolvedRuntimeShape.
    split; [assumption | split; assumption].
  - match goal with
    | H : RhoModels omega rho |- _ => exact H
    end.
  - match goal with
    | H : ResolveTy rho ty2 ty2_res |- _ => exact H
    end.
  - match goal with
    | H : CheckedTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 |- _ =>
        exact H
    end.
  - eapply SRKS_PairParFallbackRight; eauto.
Qed.

Lemma StoreResolvedStateShape_pair_par_fallback_right_return_preservation :
  forall store heap v_left v_right k ty_out,
    StoreResolvedStateShape store
      (StReturn heap v_right (KPairParFallbackRight v_left k))
      ty_out ->
    StoreResolvedStateShape store
      (StReturn heap (VPair v_left v_right) k)
      ty_out.
Proof.
  intros store heap v_left v_right k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0 HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply SRSS_Return; eauto.
  eapply SRVS_Pair; eauto.
Qed.

Lemma StoreResolvedStateShape_pair_par_done_pass_preservation :
  forall store heap v1 v2 phi_left phi_right k ty_out,
    StoreResolvedStateShape store
      (StPairParRun
        (StDone heap v1)
        (StDone heap v2)
        phi_left phi_right k)
      ty_out ->
    StoreResolvedStateShape store
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
  eapply SRSS_Return; eauto.
  eapply SRVS_Pair; eauto.
Qed.

Lemma StoreResolvedStateShape_pair_par_done_fail_preservation :
  forall store heap v1 v2 phi_left phi_right k ty_out,
    StoreResolvedStateShape store
      (StPairParRun
        (StDone heap v1)
        (StDone heap v2)
        phi_left phi_right k)
      ty_out ->
    StoreResolvedStateShape store (StError heap) ty_out.
Proof.
  intros store heap v1 v2 phi_left phi_right k ty_out HState.
  inversion HState as
    [| | | |
      store0 left_state right_state phi_left0 phi_right0 k0 heap0
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    subst; clear HState; simpl in *; subst.
  inversion HLeft; subst.
  eapply SRSS_Error; eauto.
Qed.

Lemma StoreResolvedStateShape_pair_par_left_error_preservation :
  forall store heap right_state phi_left phi_right k ty_out,
    StoreResolvedStateShape store
      (StPairParRun (StError heap) right_state phi_left phi_right k)
      ty_out ->
    StoreResolvedStateShape store (StError heap) ty_out.
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
  eapply SRSS_Error; eauto.
Qed.

Lemma StoreResolvedStateShape_pair_par_right_error_preservation :
  forall store heap_left v1 heap_right phi_left phi_right k ty_out,
    StoreResolvedStateShape store
      (StPairParRun
        (StDone heap_left v1)
        (StError heap_right)
        phi_left phi_right k)
      ty_out ->
    StoreResolvedStateShape store (StError heap_right) ty_out.
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
  eapply SRSS_Error; eauto.
Qed.

Definition StoreStepTransport
    (store store' : StoreTyping)
    (state state' : State) : Prop :=
  (forall sibling ty,
    state_heap sibling = state_heap state ->
    StoreResolvedStateShape store sibling ty ->
    StoreResolvedStateShape store'
      (with_state_heap (state_heap state') sibling) ty) /\
  (forall env rho gamma,
    StoreResolvedRuntimeShape
      (state_heap state) store env rho gamma ->
    StoreResolvedRuntimeShape
      (state_heap state') store' env rho gamma) /\
  (forall k ty_in ty_out,
    StoreResolvedKontShape store k ty_in ty_out ->
    StoreResolvedKontShape store' k ty_in ty_out).

Lemma StoreStepTransport_same :
  forall store state state',
    state_heap state' = state_heap state ->
    StoreStepTransport store store state state'.
Proof.
  intros store state state' HHeap.
  split.
  - intros sibling ty HSiblingHeap HSibling.
    eapply StoreResolvedStateShape_with_state_heap_same; eauto.
    rewrite HHeap.
    exact HSiblingHeap.
  - split.
    + intros env rho gamma HRuntime.
      rewrite HHeap.
      exact HRuntime.
    + intros k ty_in ty_out HK.
      exact HK.
Qed.

Lemma StoreStep_ref_return_preservation :
  forall store heap v r_val k l heap' ty_out,
    heap_alloc r_val v heap = (l, heap') ->
    StoreResolvedStateShape store
      (StReturn heap v (KRef r_val k))
      ty_out ->
    exists store',
      StoreResolvedStateShape store'
        (StReturn heap' (VLoc r_val l) k)
        ty_out /\
      StoreStepTransport store store'
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
  - eapply SRSS_Return with
      (ty := TyRef (region_const_type r_val) ty_cell).
    + eapply StoreKeysBoundedByHeap_alloc; eauto.
    + eapply StoreResolvedHeapShape_alloc; eauto.
    + eapply SRVS_Loc.
      apply store_ty_lookup_extend_same.
    + destruct (heap_alloc_result heap r_val v l heap')
        as [HFresh _]; [exact HAlloc |].
      eapply StoreResolvedKontShape_store_extend; eauto.
  - split.
    + intros sibling ty_s HSiblingHeap HSibling.
      eapply StoreResolvedStateShape_heap_alloc; eauto.
    + split.
      * intros env rho gamma HRuntime.
        eapply StoreResolvedRuntimeShape_alloc; eauto.
      * intros k_frame ty_in ty_out_frame HKFrame.
        destruct (heap_alloc_result heap r_val v l heap')
          as [HFresh _]; [exact HAlloc |].
        eapply StoreResolvedKontShape_store_extend; eauto.
Qed.

Lemma StoreStep_assign_val_preservation :
  forall store heap r_static r l v k ty_out,
    StoreResolvedStateShape store
      (StReturn heap v (KAssignVal r_static (VLoc r l) k))
      ty_out ->
    exists store',
      StoreResolvedStateShape store'
        (StReturn (heap_update r l v heap) VUnit k)
        ty_out /\
      StoreStepTransport store store'
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
  | HLoc : StoreResolvedValShape store (VLoc r l)
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
      [ eapply SRSS_Return with (ty := TyUnit);
        [ eapply StoreKeysBoundedByHeap_update; eauto
        | eapply StoreResolvedHeapShape_update; eauto;
          split; [exact HHeapToStore | exact HStoreToHeap]
        | constructor
        | assumption ]
      | split;
        [ intros sibling ty_s HSiblingHeap HSibling;
          eapply StoreResolvedStateShape_heap_update; eauto;
          simpl in HSiblingHeap; exact HSiblingHeap
        | split;
          [ intros env rho gamma HRuntime;
            eapply StoreResolvedRuntimeShape_update; eauto
          | intros k_frame ty_in ty_out_frame HKFrame;
            exact HKFrame ] ] ]
  end.
Qed.

Theorem Step_store_resolved_state_preservation :
  forall state label state' store ty,
    Step state label state' ->
    StoreResolvedStateShape store state ty ->
    exists store',
      StoreResolvedStateShape store' state' ty /\
      StoreStepTransport store store' state state'.
Proof.
  intros state label state' store ty HStep.
  revert store ty.
  induction HStep; intros store ty HState;
    try solve
      [ exists store; split;
        [ eauto using
            StoreResolvedStateShape_const_preservation,
            StoreResolvedStateShape_bool_preservation,
            StoreResolvedStateShape_var_preservation,
            StoreResolvedStateShape_mu_preservation,
            StoreResolvedStateShape_lambda_rgn_preservation,
            StoreResolvedStateShape_mu_app_eval_preservation,
            StoreResolvedStateShape_mu_app_eval_arg_preservation,
            StoreResolvedStateShape_mu_app_body_preservation,
            StoreResolvedStateShape_eff_app_eval_preservation,
            StoreResolvedStateShape_eff_app_eval_arg_preservation,
            StoreResolvedStateShape_eff_app_body_preservation,
            StoreResolvedStateShape_pair_par_eval_preservation,
            StoreResolvedStateShape_pair_par_eff1_preservation,
            StoreResolvedStateShape_pair_par_check_pass_preservation,
            StoreResolvedStateShape_pair_par_check_fallback_preservation,
            StoreResolvedStateShape_pair_par_fallback_left_return_preservation,
            StoreResolvedStateShape_pair_par_fallback_right_return_preservation,
            StoreResolvedStateShape_pair_par_left_error_preservation,
            StoreResolvedStateShape_pair_par_right_error_preservation,
            StoreResolvedStateShape_pair_par_done_pass_preservation,
            StoreResolvedStateShape_pair_par_done_fail_preservation,
            StoreResolvedStateShape_rgn_app_eval_preservation,
            StoreResolvedStateShape_rgn_app_return_preservation,
            StoreResolvedStateShape_empty_preservation,
            StoreResolvedStateShape_top_preservation,
            StoreResolvedStateShape_cond_eval_preservation,
            StoreResolvedStateShape_cond_true_preservation,
            StoreResolvedStateShape_cond_false_preservation,
            StoreResolvedStateShape_ref_eval_preservation,
            StoreResolvedStateShape_deref_eval_preservation,
            StoreResolvedStateShape_deref_preservation,
            StoreResolvedStateShape_assign_eval_preservation,
            StoreResolvedStateShape_assign_loc_preservation,
            StoreResolvedStateShape_plus_eval_preservation,
            StoreResolvedStateShape_plus_l_preservation,
            StoreResolvedStateShape_plus_r_preservation,
            StoreResolvedStateShape_minus_eval_preservation,
            StoreResolvedStateShape_minus_l_preservation,
            StoreResolvedStateShape_minus_r_preservation,
            StoreResolvedStateShape_times_eval_preservation,
            StoreResolvedStateShape_times_l_preservation,
            StoreResolvedStateShape_times_r_preservation,
            StoreResolvedStateShape_eq_eval_preservation,
            StoreResolvedStateShape_eq_l_preservation,
            StoreResolvedStateShape_eq_r_preservation,
            StoreResolvedStateShape_alloc_abs_preservation,
            StoreResolvedStateShape_read_abs_preservation,
            StoreResolvedStateShape_write_abs_preservation,
            StoreResolvedStateShape_read_conc_eval_preservation,
            StoreResolvedStateShape_read_conc_preservation,
            StoreResolvedStateShape_write_conc_eval_preservation,
            StoreResolvedStateShape_write_conc_preservation,
            StoreResolvedStateShape_concat_eval_preservation,
            StoreResolvedStateShape_concat_l_preservation,
            StoreResolvedStateShape_concat_r_preservation,
            StoreResolvedStateShape_done_preservation
        | apply StoreStepTransport_same; reflexivity ] ].
  - inversion HState as
      [| | | |
        store0 left_state0 right_state0 phi_left0 phi_right0 k0 heap_run
        ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
      subst; clear HState.
    destruct (IHHStep store ty1 HLeft) as
      (store' & HLeft' & HTransport).
    destruct HTransport as
      (HStateTransport & HRuntimeTransport & HKTransport).
    pose proof (StoreResolvedStateShape_aligned _ _ _ HRight)
      as HAlignedRight.
    destruct
      (with_state_heap_aligned
        (state_heap left_state') right_state HAlignedRight)
      as (_ & HRightHeap').
    exists store'.
    split.
    + eapply SRSS_PairParRun with
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
    pose proof (StoreResolvedStateShape_aligned _ _ _ HLeft)
      as HAlignedLeft.
    destruct
      (with_state_heap_aligned
        (state_heap right_state') (StDone heap v1) HAlignedLeft)
      as (_ & HLeftHeap').
    exists store'.
    split.
    + eapply SRSS_PairParRun with
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
    + eapply StoreResolvedStateShape_pair_par_right_error_preservation;
        eauto.
    + split.
      * intros sibling ty_s HSiblingHeap HSibling.
        eapply StoreResolvedStateShape_with_state_heap_same; eauto.
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
  - eapply StoreStep_ref_return_preservation; eauto.
  - eapply StoreStep_assign_val_preservation; eauto.
Qed.

Theorem Steps_store_resolved_state_preservation_with_transport :
  forall state phi state' store ty,
    Steps state phi state' ->
    StoreResolvedStateShape store state ty ->
    exists store',
      StoreResolvedStateShape store' state' ty /\
      StoreStepTransport store store' state state'.
Proof.
  intros state phi state' store ty HSteps.
  revert store ty.
  induction HSteps as
    [state | state label state1 phi state2 HStep _ IH];
    intros store ty HState.
  - exists store.
    split.
    + exact HState.
    + apply StoreStepTransport_same. reflexivity.
  - destruct
      (Step_store_resolved_state_preservation
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

Theorem Steps_store_resolved_state_preservation :
  forall state phi state' store ty,
    Steps state phi state' ->
    StoreResolvedStateShape store state ty ->
    exists store',
      StoreResolvedStateShape store' state' ty.
Proof.
  intros state phi state' store ty HSteps HState.
  destruct
    (Steps_store_resolved_state_preservation_with_transport
      state phi state' store ty HSteps HState)
    as (store' & HState' & _).
  exists store'.
  exact HState'.
Qed.

Theorem StepsN_store_resolved_state_preservation_with_transport :
  forall n state phi state' store ty,
    StepsN n state phi state' ->
    StoreResolvedStateShape store state ty ->
    exists store',
      StoreResolvedStateShape store' state' ty /\
      StoreStepTransport store store' state state'.
Proof.
  intros n state phi state' store ty HSteps HState.
  eapply Steps_store_resolved_state_preservation_with_transport; eauto.
  eapply StepsN_to_Steps; eauto.
Qed.

Theorem StepsN_store_resolved_state_preservation :
  forall n state phi state' store ty,
    StepsN n state phi state' ->
    StoreResolvedStateShape store state ty ->
    exists store',
      StoreResolvedStateShape store' state' ty.
Proof.
  intros n state phi state' store ty HSteps HState.
  eapply Steps_store_resolved_state_preservation; eauto.
  eapply StepsN_to_Steps; eauto.
Qed.

Theorem StepsView_store_resolved_state_preservation_with_transport :
  forall state view state' store ty,
    StepsView state view state' ->
    StoreResolvedStateShape store state ty ->
    exists store',
      StoreResolvedStateShape store' state' ty /\
      StoreStepTransport store store' state state'.
Proof.
  intros state view state' store ty HSteps HState.
  eapply Steps_store_resolved_state_preservation_with_transport; eauto.
  eapply StepsView_to_Steps; eauto.
Qed.

Theorem StepsView_store_resolved_state_preservation :
  forall state view state' store ty,
    StepsView state view state' ->
    StoreResolvedStateShape store state ty ->
    exists store',
      StoreResolvedStateShape store' state' ty.
Proof.
  intros state view state' store ty HSteps HState.
  eapply Steps_store_resolved_state_preservation; eauto.
  eapply StepsView_to_Steps; eauto.
Qed.

Lemma RegularResolvedStateShape_plus_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho (EPlus e1 e2) k)
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho e1 (KPlusL e2 env rho k))
      ty_out.
Proof.
  intros heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat);
    eauto using Resolve_Nat.
  - eapply RRKS_PlusL; eauto.
Qed.

Lemma RegularResolvedStateShape_minus_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho (EMinus e1 e2) k)
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho e1 (KMinusL e2 env rho k))
      ty_out.
Proof.
  intros heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat);
    eauto using Resolve_Nat.
  - eapply RRKS_MinusL; eauto.
Qed.

Lemma RegularResolvedStateShape_times_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho (ETimes e1 e2) k)
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho e1 (KTimesL e2 env rho k))
      ty_out.
Proof.
  intros heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat);
    eauto using Resolve_Nat.
  - eapply RRKS_TimesL; eauto.
Qed.

Lemma RegularResolvedStateShape_eq_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho (EEq e1 e2) k)
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho e1 (KEqL e2 env rho k))
      ty_out.
Proof.
  intros heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat);
    eauto using Resolve_Nat.
  - eapply RRKS_EqL; eauto.
Qed.

Lemma RegularResolvedStateShape_alloc_abs_preservation :
  forall heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    RegularResolvedStateShape
      (StEval heap env rho (EAllocAbs r) k)
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap (VSummary (SummarySet [CAllocAbs r_val])) k)
      ty_out.
Proof.
  intros heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply RRSS_Return; eauto using RRVS_Summary.
Qed.

Lemma RegularResolvedStateShape_read_abs_preservation :
  forall heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    RegularResolvedStateShape
      (StEval heap env rho (EReadAbs r) k)
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap (VSummary (SummarySet [CReadAbs r_val])) k)
      ty_out.
Proof.
  intros heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply RRSS_Return; eauto using RRVS_Summary.
Qed.

Lemma RegularResolvedStateShape_write_abs_preservation :
  forall heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    RegularResolvedStateShape
      (StEval heap env rho (EWriteAbs r) k)
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap (VSummary (SummarySet [CWriteAbs r_val])) k)
      ty_out.
Proof.
  intros heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply RRSS_Return; eauto using RRVS_Summary.
Qed.

Lemma RegularResolvedStateShape_concat_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho (EConcat e1 e2) k)
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho e1 (KConcatL e2 env rho k))
      ty_out.
Proof.
  intros heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect);
    eauto using Resolve_Effect.
  - eapply RRKS_ConcatL; eauto.
Qed.

Lemma RegularResolvedStateShape_cond_true_preservation :
  forall heap et ef env rho k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VBool true) (KCond et ef env rho k))
      ty_out ->
    RegularResolvedStateShape (StEval heap env rho et k) ty_out.
Proof.
  intros heap et ef env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RRSS_Eval; eauto.
Qed.

Lemma RegularResolvedStateShape_cond_false_preservation :
  forall heap et ef env rho k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VBool false) (KCond et ef env rho k))
      ty_out ->
    RegularResolvedStateShape (StEval heap env rho ef k) ty_out.
Proof.
  intros heap et ef env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RRSS_Eval; eauto.
Qed.

Lemma RegularResolvedStateShape_deref_preservation :
  forall heap r_static r l v k ty_out,
    heap_lookup r l heap = Some v ->
    RegularResolvedStateShape
      (StReturn heap (VLoc r l) (KDeref r_static k))
      ty_out ->
    RegularResolvedStateShape (StReturn heap v k) ty_out.
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
    HCellShape : RegularResolvedValShape heap ?cell ?ty |- _ =>
      rewrite HLookup' in HCellLookup;
      inversion HCellLookup; subst
  end.
  eapply RRSS_Return; eauto.
Qed.

Lemma RegularResolvedStateShape_plus_l_preservation :
  forall heap n e2 env rho k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VNat n) (KPlusL e2 env rho k))
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho e2 (KPlusR n k))
      ty_out.
Proof.
  intros heap n e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using Resolve_Nat.
  eapply RRKS_PlusR; eauto.
Qed.

Lemma RegularResolvedStateShape_plus_r_preservation :
  forall heap n1 n2 k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VNat n2) (KPlusR n1 k))
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap (VNat (n1 + n2)) k)
      ty_out.
Proof.
  intros heap n1 n2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RRSS_Return; eauto using RRVS_Nat.
Qed.

Lemma RegularResolvedStateShape_minus_l_preservation :
  forall heap n e2 env rho k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VNat n) (KMinusL e2 env rho k))
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho e2 (KMinusR n k))
      ty_out.
Proof.
  intros heap n e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using Resolve_Nat.
  eapply RRKS_MinusR; eauto.
Qed.

Lemma RegularResolvedStateShape_minus_r_preservation :
  forall heap n1 n2 k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VNat n2) (KMinusR n1 k))
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap (VNat (n1 - n2)) k)
      ty_out.
Proof.
  intros heap n1 n2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RRSS_Return; eauto using RRVS_Nat.
Qed.

Lemma RegularResolvedStateShape_times_l_preservation :
  forall heap n e2 env rho k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VNat n) (KTimesL e2 env rho k))
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho e2 (KTimesR n k))
      ty_out.
Proof.
  intros heap n e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using Resolve_Nat.
  eapply RRKS_TimesR; eauto.
Qed.

Lemma RegularResolvedStateShape_times_r_preservation :
  forall heap n1 n2 k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VNat n2) (KTimesR n1 k))
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap (VNat (n1 * n2)) k)
      ty_out.
Proof.
  intros heap n1 n2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RRSS_Return; eauto using RRVS_Nat.
Qed.

Lemma RegularResolvedStateShape_eq_l_preservation :
  forall heap n e2 env rho k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VNat n) (KEqL e2 env rho k))
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho e2 (KEqR n k))
      ty_out.
Proof.
  intros heap n e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using Resolve_Nat.
  eapply RRKS_EqR; eauto.
Qed.

Lemma RegularResolvedStateShape_eq_r_preservation :
  forall heap n1 n2 k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VNat n2) (KEqR n1 k))
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap (VBool (Nat.eqb n1 n2)) k)
      ty_out.
Proof.
  intros heap n1 n2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RRSS_Return; eauto using RRVS_Bool.
Qed.

Lemma RegularResolvedStateShape_concat_l_preservation :
  forall heap theta1 e2 env rho k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VSummary theta1) (KConcatL e2 env rho k))
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho e2 (KConcatR theta1 k))
      ty_out.
Proof.
  intros heap theta1 e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff);
    eauto using Resolve_Effect.
  eapply RRKS_ConcatR; eauto.
Qed.

Lemma RegularResolvedStateShape_concat_r_preservation :
  forall heap theta1 theta2 k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VSummary theta2) (KConcatR theta1 k))
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap (VSummary (summary_union theta1 theta2)) k)
      ty_out.
Proof.
  intros heap theta1 theta2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RRSS_Return; eauto using RRVS_Summary.
Qed.

Lemma RegularResolvedStateShape_read_conc_eval_preservation :
  forall heap env rho e k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho (EReadConc e) k)
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho e (KReadConc k))
      ty_out.
Proof.
  intros heap env rho e k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ H3) as HRefWF.
  inversion HRefWF; subst.
  match goal with
  | HRgnWF : RegionTypeWFAt 0 omega r0,
    HTyWF : TyWFAt 0 omega ty |- _ =>
      destruct
        (ResolveRegionType_exists 0 omega rho r0 HRho HRgnWF)
        as (rgn_res & HRgnResolve);
      destruct (ResolveTy_exists 0 omega rho ty HRho HTyWF)
        as (ty_ref_res & HTyResolve);
      destruct
        (ResolveRegionType_wf0_const
          omega rho r0 rgn_res HRgnWF HRgnResolve)
        as (r_val & HRgnResEq);
      subst rgn_res;
      eapply RRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyRef r0 ty)
        (ty_res := TyRef (region_const_type r_val) ty_ref_res)
        (eff := eff);
        eauto;
      [ eapply Resolve_Ref; eauto
      | eapply RRKS_ReadConc; eauto ]
  end.
Qed.

Lemma RegularResolvedStateShape_write_conc_eval_preservation :
  forall heap env rho e k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho (EWriteConc e) k)
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho e (KWriteConc k))
      ty_out.
Proof.
  intros heap env rho e k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ H3) as HRefWF.
  inversion HRefWF; subst.
  match goal with
  | HRgnWF : RegionTypeWFAt 0 omega r0,
    HTyWF : TyWFAt 0 omega ty |- _ =>
      destruct
        (ResolveRegionType_exists 0 omega rho r0 HRho HRgnWF)
        as (rgn_res & HRgnResolve);
      destruct (ResolveTy_exists 0 omega rho ty HRho HTyWF)
        as (ty_ref_res & HTyResolve);
      destruct
        (ResolveRegionType_wf0_const
          omega rho r0 rgn_res HRgnWF HRgnResolve)
        as (r_val & HRgnResEq);
      subst rgn_res;
      eapply RRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyRef r0 ty)
        (ty_res := TyRef (region_const_type r_val) ty_ref_res)
        (eff := eff);
        eauto;
      [ eapply Resolve_Ref; eauto
      | eapply RRKS_WriteConc; eauto ]
  end.
Qed.

Lemma RegularResolvedStateShape_read_conc_preservation :
  forall heap r l k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VLoc r l) (KReadConc k))
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap (VSummary (SummarySet [CReadConc r l])) k)
      ty_out.
Proof.
  intros heap r l k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply RRSS_Return; eauto using RRVS_Summary.
Qed.

Lemma RegularResolvedStateShape_write_conc_preservation :
  forall heap r l k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VLoc r l) (KWriteConc k))
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap (VSummary (SummarySet [CWriteConc r l])) k)
      ty_out.
Proof.
  intros heap r l k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply RRSS_Return; eauto using RRVS_Summary.
Qed.

Lemma RegularResolvedStateShape_done_preservation :
  forall heap v ty_out,
    RegularResolvedStateShape
      (StReturn heap v KDone)
      ty_out ->
    RegularResolvedStateShape (StDone heap v) ty_out.
Proof.
  intros heap v ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply RRSS_Done; eauto.
Qed.

Lemma RegularResolvedStateShape_mu_app_eval_preservation :
  forall heap env rho ef ea k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho (EMuApp ef ea) k)
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho ef (KMuAppFun ea env rho k))
      ty_out.
Proof.
  intros heap env rho ef ea k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ H7) as HFunWF.
  inversion HFunWF; subst.
  match goal with
  | HArgWF : TyWFAt 0 omega ty_arg0,
    HBodyEffWF : StaticEffectWFAt 0 omega eff_body0,
    HSummaryEffWF : StaticEffectWFAt 0 omega eff_summary0 |- _ =>
      destruct (ResolveTy_exists 0 omega rho ty_arg0 HRho HArgWF)
        as (ty_arg_res & HArgResolve);
      destruct
        (ResolveStaticEffect_exists
          0 omega rho eff_body0 HRho HBodyEffWF)
        as (eff_body_res & HBodyEffResolve);
      destruct
        (ResolveStaticEffect_exists
          0 omega rho eff_summary0 HRho HSummaryEffWF)
        as (eff_summary_res & HSummaryEffResolve);
      eapply RRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyArrow ty_arg0 eff_body0 ty eff_summary0)
        (ty_res := TyArrow
          ty_arg_res eff_body_res ty_res eff_summary_res)
        (eff := eff_f0);
        eauto;
      [ eapply Resolve_Arrow; eauto
      | eapply RRKS_MuAppFun with
          (gamma := gamma) (omega := omega)
          (ty_arg := ty_arg0) (ty_body := ty)
          (eff_body := eff_body0) (eff_summary := eff_summary0)
          (eff_arg := eff_a0);
        eauto ]
  end.
Qed.

Lemma RegularResolvedStateShape_eff_app_eval_preservation :
  forall heap env rho ef ea k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho (EEffApp ef ea) k)
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho ef (KEffAppFun ea env rho k))
      ty_out.
Proof.
  intros heap env rho ef ea k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ H5) as HFunWF.
  inversion HFunWF; subst.
  match goal with
  | HArgWF : TyWFAt 0 omega ?ty_arg0,
    HBodyEffWF : StaticEffectWFAt 0 omega ?eff_body0,
    HBodyWF : TyWFAt 0 omega ?ty_body0,
    HSummaryEffWF : StaticEffectWFAt 0 omega ?eff_summary0 |- _ =>
      destruct (ResolveTy_exists 0 omega rho ty_arg0 HRho HArgWF)
        as (ty_arg_res & HArgResolve);
      destruct
        (ResolveStaticEffect_exists
          0 omega rho eff_body0 HRho HBodyEffWF)
        as (eff_body_res & HBodyEffResolve);
      destruct (ResolveTy_exists 0 omega rho ty_body0 HRho HBodyWF)
        as (ty_body_res & HBodyResolve);
      destruct
        (ResolveStaticEffect_exists
          0 omega rho eff_summary0 HRho HSummaryEffWF)
        as (eff_summary_res & HSummaryEffResolve);
      eapply RRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyArrow ty_arg0 eff_body0 ty_body0 eff_summary0)
        (ty_res := TyArrow
          ty_arg_res eff_body_res ty_body_res eff_summary_res)
        (eff := eff_f0);
        eauto;
      [ eapply Resolve_Arrow; eauto
      | eapply RRKS_EffAppFun with
          (gamma := gamma) (omega := omega)
          (ty_arg := ty_arg0) (ty_body := ty_body0)
          (eff_body := eff_body0) (eff_summary := eff_summary0)
          (eff_arg := eff_a0);
        eauto ]
  end.
Qed.

Lemma RegularResolvedStateShape_mu_app_eval_arg_preservation :
  forall heap env rho ea k closure_env closure_rho f x ec ee ty_out,
    RegularResolvedStateShape
      (StReturn heap
        (VClosure closure_env closure_rho f x ec ee)
        (KMuAppFun ea env rho k))
      ty_out ->
    RegularResolvedStateShape
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
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty_arg) (ty_res := ty_arg_res)
    (eff := eff_arg); eauto.
  eapply RRKS_MuAppArg with
    (gamma := gamma0) (omega := omega0)
    (ty_arg := ty_arg0) (ty_body := ty_body0)
    (eff_body := eff_body0) (eff_summary := eff_summary0);
    eauto.
Qed.

Lemma RegularResolvedStateShape_eff_app_eval_arg_preservation :
  forall heap env rho ea k closure_env closure_rho f x ec ee ty_out,
    RegularResolvedStateShape
      (StReturn heap
        (VClosure closure_env closure_rho f x ec ee)
        (KEffAppFun ea env rho k))
      ty_out ->
    RegularResolvedStateShape
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
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty_arg) (ty_res := ty_arg_res)
    (eff := eff_arg); eauto.
  eapply RRKS_EffAppArg with
    (gamma := gamma0) (omega := omega0)
    (ty_arg := ty_arg0) (ty_body := ty_body0)
    (eff_body := eff_body0) (eff_summary := eff_summary0);
    eauto.
Qed.

Lemma RegularResolvedStateShape_mu_app_body_preservation :
  forall heap v_arg closure_env closure_rho f x ec ee k ty_out,
    RegularResolvedStateShape
      (StReturn heap v_arg
        (KMuAppArg closure_env closure_rho f x ec ee k))
      ty_out ->
    RegularResolvedStateShape
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
  eapply RRSS_Eval with
    (gamma :=
      (x, ty_arg) ::
      (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
    (omega := omega)
    (ty := ty_body) (ty_res := ty_body_res) (eff := eff_body);
    eauto.
  eapply RegularResolvedEnvShape_extend with
    (ty_res := ty); eauto.
  eapply RegularResolvedEnvShape_extend with
    (ty_res := TyArrow
      ty eff_body_res ty_body_res eff_summary_res);
    eauto.
  - eapply Resolve_Arrow; eauto.
  - eapply RRVS_Closure with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body); eauto.
Qed.

Lemma RegularResolvedStateShape_eff_app_body_preservation :
  forall heap v_arg closure_env closure_rho f x ec ee k ty_out,
    RegularResolvedStateShape
      (StReturn heap v_arg
        (KEffAppArg closure_env closure_rho f x ec ee k))
      ty_out ->
    RegularResolvedStateShape
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
  eapply RRSS_Eval with
    (gamma :=
      (x, ty_arg) ::
      (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
    (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary);
    eauto using Resolve_Effect.
  eapply RegularResolvedEnvShape_extend with
    (ty_res := ty); eauto.
  eapply RegularResolvedEnvShape_extend with
    (ty_res := TyArrow
      ty eff_body_res ty_body_res eff_summary_res);
    eauto.
  - eapply Resolve_Arrow; eauto.
  - eapply RRVS_Closure with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body); eauto.
Qed.

Lemma RegularResolvedStateShape_rgn_app_eval_preservation :
  forall heap env rho er r k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho (ERgnApp er r) k)
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho er (KRgnApp r rho k))
      ty_out.
Proof.
  intros heap env rho er r k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty_result ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  match goal with
  | HWF : region_expr_wf omega r |- _ =>
      destruct (RhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  pose proof (CheckedTcExp_ty_wf _ _ _ _ _ H8) as HFunWF.
  inversion HFunWF; subst.
  destruct
    (ResolveStaticEffect_exists 1 omega rho eff_body0 HRho H9)
    as (eff_body_res & HEffResolve).
  destruct
    (ResolveTy_exists 1 omega rho ty0 HRho H10)
    as (ty_body_res & HTyResolve).
  pose proof
    (ResolveTy_open_ty
      rho r ty0 ty_body_res r_val HRgn HTyResolve)
    as HOpenResolve.
  rewrite H4 in HOpenResolve.
  pose proof
    (ResolveTy_deterministic
      rho (open_ty r ty) ty_res
      (open_ty_type (region_const_type r_val) ty_body_res)
      HResolve HOpenResolve)
    as HTyResEq.
  subst ty_res.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyForallRgn eff_body0 ty0)
    (ty_res := TyForallRgn eff_body_res ty_body_res)
    (eff := eff_f0);
    eauto.
  - eapply Resolve_ForallRgn; eauto.
  - eapply RRKS_RgnApp; eauto.
Qed.

Lemma RegularResolvedStateShape_rgn_app_return_preservation :
  forall heap closure_env closure_rho x e arg_rho r r_val k ty_out,
    eval_region arg_rho r = Some r_val ->
    RegularResolvedStateShape
      (StReturn heap
        (VRegionClosure closure_env closure_rho x e)
        (KRgnApp r arg_rho k))
      ty_out ->
    RegularResolvedStateShape
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
  eapply RRSS_Eval with
    (gamma := gamma) (omega := x :: omega)
    (ty := ty)
    (ty_res := open_ty_type (region_const_type r_val0) ty_res)
    (eff := eff);
    eauto.
  - eapply RegularResolvedEnvShape_extend_fresh;
      eauto using
        CheckedRegionBody_fresh,
        CheckedRegionBody_ctx_wf.
  - eapply RhoModels_extend; eauto.
  - eapply ResolveTy_rho_extend_close_ty.
    + exact
        (CheckedTcExp_ty_wf
          _ _ _ _ _
          (CheckedRegionBody_checked _ _ _ _ _ _ H9)).
    + eauto.
  - exact (CheckedRegionBody_checked _ _ _ _ _ _ H9).
Qed.

Lemma RegularResolvedStateShape_pair_par_eval_preservation :
  forall heap env rho ef1 ea1 ef2 ea2 k ty_out,
    RegularResolvedStateShape
      (StEval heap env rho
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)) k)
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho (EEffApp ef1 ea1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      ty_out.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HReg HK | | | |];
    subst; clear HState.
  pose proof (CheckedTcExp_to_TcExp _ _ _ _ _ HReg) as HTyped.
  pose proof (CheckedTcExp_rgn_ctx_wf _ _ _ _ _ HReg) as HRgnCtx.
  pose proof (CheckedTcExp_ctx_wf _ _ _ _ _ HReg) as HCtxWF.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HReg) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary0).
  - exact HHeap.
  - exact HEnv.
  - exact HRho.
  - eapply Resolve_Effect.
  - exact H14.
  - eapply RRKS_PairParEff1 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff0) (eff2 := eff3)
      (eff_summary2 := eff_summary3);
      eauto.
Qed.

Lemma RegularResolvedStateShape_pair_par_eff1_preservation :
  forall heap theta1 ef1 ea1 ef2 ea2 env rho k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VSummary theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      ty_out ->
    RegularResolvedStateShape
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
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary2);
    eauto using Resolve_Effect.
  eapply RRKS_PairParEff2 with
    (gamma := gamma) (omega := omega)
    (ty1 := ty1) (ty2 := ty2)
    (eff1 := eff1) (eff2 := eff2);
    eauto.
Qed.

Lemma RegularResolvedStateShape_pair_par_check_pass_preservation :
  forall heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      ty_out ->
    RegularResolvedStateShape
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
  eapply RRSS_PairParRun with
    (heap := heap) (ty1 := ty1_res) (ty2 := ty2_res);
    simpl; eauto.
  - eapply RRSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty1) (ty_res := ty1_res) (eff := eff1);
      eauto.
    constructor.
  - eapply RRSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty2) (ty_res := ty2_res) (eff := eff2);
      eauto.
    constructor.
Qed.

Lemma RegularResolvedStateShape_pair_par_check_fallback_preservation :
  forall heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out,
    RegularResolvedStateShape
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho (EMuApp ef1 ea1)
        (KPairParFallbackLeft ef2 ea2 env rho k))
      ty_out.
Proof.
  intros heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty1) (ty_res := ty1_res) (eff := eff1);
    eauto.
  eapply RRKS_PairParFallbackLeft with
    (gamma := gamma) (omega := omega)
    (ty2 := ty2) (ty2_res := ty2_res) (eff2 := eff2);
    eauto.
Qed.

Lemma RegularResolvedStateShape_pair_par_fallback_left_return_preservation :
  forall heap v_left ef2 ea2 env rho k ty_out,
    RegularResolvedStateShape
      (StReturn heap v_left
        (KPairParFallbackLeft ef2 ea2 env rho k))
      ty_out ->
    RegularResolvedStateShape
      (StEval heap env rho (EMuApp ef2 ea2)
        (KPairParFallbackRight v_left k))
      ty_out.
Proof.
  intros heap v_left ef2 ea2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty2) (ty_res := ty2_res) (eff := eff2);
    eauto.
  eapply RRKS_PairParFallbackRight; eauto.
Qed.

Lemma RegularResolvedStateShape_pair_par_fallback_right_return_preservation :
  forall heap v_left v_right k ty_out,
    RegularResolvedStateShape
      (StReturn heap v_right (KPairParFallbackRight v_left k))
      ty_out ->
    RegularResolvedStateShape
      (StReturn heap (VPair v_left v_right) k)
      ty_out.
Proof.
  intros heap v_left v_right k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply RRSS_Return; eauto.
  eapply RRVS_Pair; eauto.
Qed.

Lemma RegularResolvedStateShape_pair_par_done_pass_preservation :
  forall heap v1 v2 phi_left phi_right k ty_out,
    RegularResolvedStateShape
      (StPairParRun
        (StDone heap v1)
        (StDone heap v2)
        phi_left phi_right k)
      ty_out ->
    RegularResolvedStateShape (StReturn heap (VPair v1 v2) k) ty_out.
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
  eapply RRSS_Return; eauto.
  eapply RRVS_Pair; eauto.
Qed.

Lemma RegularResolvedStateShape_pair_par_done_fail_preservation :
  forall heap v1 v2 phi_left phi_right k ty_out,
    RegularResolvedStateShape
      (StPairParRun
        (StDone heap v1)
        (StDone heap v2)
        phi_left phi_right k)
      ty_out ->
    RegularResolvedStateShape (StError heap) ty_out.
Proof.
  intros heap v1 v2 phi_left phi_right k ty_out HState.
  inversion HState as
    [| | | |
      left_state right_state phi_left0 phi_right0 k0 heap0
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    subst; clear HState; simpl in *; subst.
  inversion HLeft; subst.
  eapply RRSS_Error; eauto.
Qed.

Lemma RegularResolvedStateShape_pair_par_run_left_preservation :
  forall left_state right_state phi_left phi_right k
    label left_state' ty_out,
    Step left_state label left_state' ->
    StateHeapsAligned
      (StPairParRun left_state right_state phi_left phi_right k) ->
    HeapNeutralTrace (label_trace label) ->
    (forall ty,
      RegularResolvedStateShape left_state ty ->
      RegularResolvedStateShape left_state' ty) ->
    RegularResolvedStateShape
      (StPairParRun left_state right_state phi_left phi_right k)
      ty_out ->
    RegularResolvedStateShape
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
    (Step_heap_neutral_preserves_alignment
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
  eapply RRSS_PairParRun with (ty1 := ty1) (ty2 := ty2); eauto.
Qed.

Lemma RegularResolvedStateShape_pair_par_run_left_preservation_from_child :
  forall left_state right_state phi_left phi_right k
    label left_state' ty_out,
    Step left_state label left_state' ->
    HeapNeutralTrace (label_trace label) ->
    (forall ty,
      RegularResolvedStateShape left_state ty ->
      RegularResolvedStateShape left_state' ty) ->
    RegularResolvedStateShape
      (StPairParRun left_state right_state phi_left phi_right k)
      ty_out ->
    RegularResolvedStateShape
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
  eapply RegularResolvedStateShape_pair_par_run_left_preservation; eauto.
  eapply RegularResolvedStateShape_aligned; eauto.
Qed.

Lemma RegularResolvedStateShape_pair_par_run_right_preservation :
  forall heap v1 right_state phi_left phi_right k
    label right_state' ty_out,
    Step right_state label right_state' ->
    StateHeapsAligned
      (StPairParRun (StDone heap v1) right_state phi_left phi_right k) ->
    HeapNeutralTrace (label_trace label) ->
    (forall ty,
      RegularResolvedStateShape right_state ty ->
      RegularResolvedStateShape right_state' ty) ->
    RegularResolvedStateShape
      (StPairParRun (StDone heap v1) right_state phi_left phi_right k)
      ty_out ->
    RegularResolvedStateShape
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
    (Step_heap_neutral_preserves_alignment
      right_state label right_state' HStep HAlignedRight HNeutral)
    as (_ & HHeapStep).
  assert (HRightHeap' : state_heap right_state' = heap).
  {
    rewrite HHeapStep.
    exact HHeapRight.
  }
  simpl.
  rewrite HRightHeap'.
  eapply RRSS_PairParRun with
    (heap := heap) (ty1 := ty1) (ty2 := ty2); eauto.
Qed.

Lemma RegularResolvedStateShape_pair_par_run_right_preservation_from_child :
  forall heap v1 right_state phi_left phi_right k
    label right_state' ty_out,
    Step right_state label right_state' ->
    HeapNeutralTrace (label_trace label) ->
    (forall ty,
      RegularResolvedStateShape right_state ty ->
      RegularResolvedStateShape right_state' ty) ->
    RegularResolvedStateShape
      (StPairParRun (StDone heap v1) right_state phi_left phi_right k)
      ty_out ->
    RegularResolvedStateShape
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
  eapply RegularResolvedStateShape_pair_par_run_right_preservation; eauto.
  eapply RegularResolvedStateShape_aligned; eauto.
Qed.

Lemma RegularResolvedStateShape_pair_par_left_error_preservation :
  forall heap right_state phi_left phi_right k ty_out,
    RegularResolvedStateShape
      (StPairParRun (StError heap) right_state phi_left phi_right k)
      ty_out ->
    RegularResolvedStateShape (StError heap) ty_out.
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
  eapply RRSS_Error; eauto.
Qed.

Lemma RegularResolvedStateShape_pair_par_right_error_preservation :
  forall heap_left v1 heap_right phi_left phi_right k ty_out,
    RegularResolvedStateShape
      (StPairParRun
        (StDone heap_left v1)
        (StError heap_right)
        phi_left phi_right k)
      ty_out ->
    RegularResolvedStateShape (StError heap_right) ty_out.
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
  eapply RRSS_Error; eauto.
Qed.

Theorem Step_heap_neutral_regular_state_preservation :
  forall state label state' ty,
    Step state label state' ->
    HeapNeutralTrace (label_trace label) ->
    RegularResolvedStateShape state ty ->
    RegularResolvedStateShape state' ty.
Proof.
  intros state label state' ty HStep.
  revert ty.
  induction HStep; intros ty_out HNeutral HState; simpl in HNeutral.
  - eapply RegularResolvedStateShape_const_preservation; eauto.
  - eapply RegularResolvedStateShape_bool_preservation; eauto.
  - eapply RegularResolvedStateShape_var_preservation; eauto.
  - eapply RegularResolvedStateShape_mu_preservation; eauto.
  - eapply RegularResolvedStateShape_lambda_rgn_preservation; eauto.
  - eapply RegularResolvedStateShape_mu_app_eval_preservation; eauto.
  - eapply RegularResolvedStateShape_mu_app_eval_arg_preservation; eauto.
  - eapply RegularResolvedStateShape_mu_app_body_preservation; eauto.
  - eapply RegularResolvedStateShape_eff_app_eval_preservation; eauto.
  - eapply RegularResolvedStateShape_eff_app_eval_arg_preservation; eauto.
  - eapply RegularResolvedStateShape_eff_app_body_preservation; eauto.
  - eapply RegularResolvedStateShape_pair_par_eval_preservation; eauto.
  - eapply RegularResolvedStateShape_pair_par_eff1_preservation; eauto.
  - eapply RegularResolvedStateShape_pair_par_check_pass_preservation; eauto.
  - eapply RegularResolvedStateShape_pair_par_check_fallback_preservation; eauto.
  - eapply RegularResolvedStateShape_pair_par_fallback_left_return_preservation;
      eauto.
  - eapply RegularResolvedStateShape_pair_par_fallback_right_return_preservation;
      eauto.
  - eapply RegularResolvedStateShape_pair_par_run_left_preservation_from_child;
      eauto.
  - eapply RegularResolvedStateShape_pair_par_run_right_preservation_from_child;
      eauto.
  - eapply RegularResolvedStateShape_pair_par_left_error_preservation; eauto.
  - eapply RegularResolvedStateShape_pair_par_right_error_preservation; eauto.
  - eapply RegularResolvedStateShape_pair_par_done_pass_preservation; eauto.
  - eapply RegularResolvedStateShape_pair_par_done_fail_preservation; eauto.
  - eapply RegularResolvedStateShape_rgn_app_eval_preservation; eauto.
  - eapply RegularResolvedStateShape_rgn_app_return_preservation; eauto.
  - eapply RegularResolvedStateShape_empty_preservation; eauto.
  - eapply RegularResolvedStateShape_top_preservation; eauto.
  - eapply RegularResolvedStateShape_cond_eval_preservation; eauto.
  - eapply RegularResolvedStateShape_cond_true_preservation; eauto.
  - eapply RegularResolvedStateShape_cond_false_preservation; eauto.
  - eapply RegularResolvedStateShape_ref_eval_preservation; eauto.
  - destruct HNeutral as (HNoAlloc & _).
    exfalso. eapply HNoAlloc.
    simpl. left. reflexivity.
  - eapply RegularResolvedStateShape_deref_eval_preservation; eauto.
  - eapply RegularResolvedStateShape_deref_preservation; eauto.
  - eapply RegularResolvedStateShape_assign_eval_preservation; eauto.
  - eapply RegularResolvedStateShape_assign_loc_preservation; eauto.
  - destruct HNeutral as (_ & HReadOnly).
    exfalso. eapply HReadOnly.
    simpl. left. reflexivity.
  - eapply RegularResolvedStateShape_plus_eval_preservation; eauto.
  - eapply RegularResolvedStateShape_plus_l_preservation; eauto.
  - eapply RegularResolvedStateShape_plus_r_preservation; eauto.
  - eapply RegularResolvedStateShape_minus_eval_preservation; eauto.
  - eapply RegularResolvedStateShape_minus_l_preservation; eauto.
  - eapply RegularResolvedStateShape_minus_r_preservation; eauto.
  - eapply RegularResolvedStateShape_times_eval_preservation; eauto.
  - eapply RegularResolvedStateShape_times_l_preservation; eauto.
  - eapply RegularResolvedStateShape_times_r_preservation; eauto.
  - eapply RegularResolvedStateShape_eq_eval_preservation; eauto.
  - eapply RegularResolvedStateShape_eq_l_preservation; eauto.
  - eapply RegularResolvedStateShape_eq_r_preservation; eauto.
  - eapply RegularResolvedStateShape_alloc_abs_preservation; eauto.
  - eapply RegularResolvedStateShape_read_abs_preservation; eauto.
  - eapply RegularResolvedStateShape_write_abs_preservation; eauto.
  - eapply RegularResolvedStateShape_read_conc_eval_preservation; eauto.
  - eapply RegularResolvedStateShape_read_conc_preservation; eauto.
  - eapply RegularResolvedStateShape_write_conc_eval_preservation; eauto.
  - eapply RegularResolvedStateShape_write_conc_preservation; eauto.
  - eapply RegularResolvedStateShape_concat_eval_preservation; eauto.
  - eapply RegularResolvedStateShape_concat_l_preservation; eauto.
  - eapply RegularResolvedStateShape_concat_r_preservation; eauto.
  - eapply RegularResolvedStateShape_done_preservation; eauto.
Qed.

Lemma Steps_heap_neutral_regular_state_preservation_from_step :
  forall
    (step_preserve :
      forall state label state' ty,
        Step state label state' ->
        HeapNeutralTrace (label_trace label) ->
        RegularResolvedStateShape state ty ->
        RegularResolvedStateShape state' ty)
    state phi state' ty,
    Steps state phi state' ->
    HeapNeutralTrace phi ->
    RegularResolvedStateShape state ty ->
    RegularResolvedStateShape state' ty.
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

Theorem Steps_heap_neutral_regular_state_preservation :
  forall state phi state' ty,
    Steps state phi state' ->
    HeapNeutralTrace phi ->
    RegularResolvedStateShape state ty ->
    RegularResolvedStateShape state' ty.
Proof.
  intros state phi state' ty HSteps HNeutral HState.
  eapply Steps_heap_neutral_regular_state_preservation_from_step;
    eauto.
  intros state0 label state1 ty0 HStep HStepNeutral HState0.
  eapply Step_heap_neutral_regular_state_preservation; eauto.
Qed.

Lemma StepsN_heap_neutral_regular_state_preservation_from_step :
  forall
    (step_preserve :
      forall state label state' ty,
        Step state label state' ->
        HeapNeutralTrace (label_trace label) ->
        RegularResolvedStateShape state ty ->
        RegularResolvedStateShape state' ty)
    n state phi state' ty,
    StepsN n state phi state' ->
    HeapNeutralTrace phi ->
    RegularResolvedStateShape state ty ->
    RegularResolvedStateShape state' ty.
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

Theorem StepsN_heap_neutral_regular_state_preservation :
  forall n state phi state' ty,
    StepsN n state phi state' ->
    HeapNeutralTrace phi ->
    RegularResolvedStateShape state ty ->
    RegularResolvedStateShape state' ty.
Proof.
  intros n state phi state' ty HSteps HNeutral HState.
  eapply StepsN_heap_neutral_regular_state_preservation_from_step;
    eauto.
  intros state0 label state1 ty0 HStep HStepNeutral HState0.
  eapply Step_heap_neutral_regular_state_preservation; eauto.
Qed.
