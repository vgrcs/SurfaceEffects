From Stdlib Require Import List.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.StateShape.
Require Import theories.NewSmallStep.Runtime.Typing.
Require Import theories.NewSmallStep.Typing.Judgments.
Require Import theories.NewSmallStep.Typing.Resolve.
Require Import theories.NewSmallStep.Typing.Types.

Import ListNotations.

Inductive NReturnSameContextKont : NKont -> Prop :=
| NRS_MuAppFun :
    forall ea env rho k,
      NReturnSameContextKont (KMuAppFun ea env rho k)
| NRS_EffAppFun :
    forall ea env rho k,
      NReturnSameContextKont (KEffAppFun ea env rho k)
| NRS_Cond :
    forall et ef env rho k,
      NReturnSameContextKont (KCond et ef env rho k)
| NRS_Deref :
    forall rgn k,
      NReturnSameContextKont (KDeref rgn k)
| NRS_AssignLoc :
    forall rgn ev env rho k,
      NReturnSameContextKont (KAssignLoc rgn ev env rho k)
| NRS_PlusL :
    forall e2 env rho k,
      NReturnSameContextKont (KPlusL e2 env rho k)
| NRS_PlusR :
    forall n k,
      NReturnSameContextKont (KPlusR n k)
| NRS_MinusL :
    forall e2 env rho k,
      NReturnSameContextKont (KMinusL e2 env rho k)
| NRS_MinusR :
    forall n k,
      NReturnSameContextKont (KMinusR n k)
| NRS_TimesL :
    forall e2 env rho k,
      NReturnSameContextKont (KTimesL e2 env rho k)
| NRS_TimesR :
    forall n k,
      NReturnSameContextKont (KTimesR n k)
| NRS_EqL :
    forall e2 env rho k,
      NReturnSameContextKont (KEqL e2 env rho k)
| NRS_EqR :
    forall n k,
      NReturnSameContextKont (KEqR n k)
| NRS_ReadConc :
    forall k,
      NReturnSameContextKont (KReadConc k)
| NRS_WriteConc :
    forall k,
      NReturnSameContextKont (KWriteConc k)
| NRS_ConcatL :
    forall e2 env rho k,
      NReturnSameContextKont (KConcatL e2 env rho k)
| NRS_ConcatR :
    forall theta k,
      NReturnSameContextKont (KConcatR theta k)
| NRS_Done :
    NReturnSameContextKont KDone.

Theorem NStep_eval_preservation :
  forall gamma omega heap env rho e k label state',
    NWTState gamma omega (StEval heap env rho e k) ->
    NStep (StEval heap env rho e k) label state' ->
    NWTState gamma omega state'.
Proof.
  intros gamma omega heap env rho e k label state' HWT HStep.
  inversion HWT as
    [gamma0 omega0 heap0 env0 rho0 e0 k0 ty eff
      HHeap HEnv HRho HTc HK
    | |];
    subst; clear HWT.
  inversion HStep; subst; clear HStep.
  - inversion HTc; subst.
    eapply NWT_Return; eauto using NVT_Nat.
  - inversion HTc; subst.
    eapply NWT_Return; eauto using NVT_Bool.
  - inversion HTc; subst.
    match goal with
    | HBind : ctx_binds x _ gamma |- _ =>
        destruct
          (NEnvHasType_lookup rho heap env gamma x ty HEnv HBind)
          as (v_typed & HLookup & HV)
    end.
    match goal with
    | HRuntime : env_lookup x env = Some v |- _ =>
        rewrite HRuntime in HLookup
    end.
    inversion HLookup; subst.
    eapply NWT_Return; eauto.
  - inversion HTc; subst.
    eapply NWT_Return; eauto.
    eapply NVT_Closure; eauto.
  - inversion HTc; subst.
    eapply NWT_Return; eauto.
    eapply NVT_RegionClosure; eauto.
  - inversion HTc; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_MuAppFun; eauto.
  - inversion HTc; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_EffAppFun; eauto.
  - inversion HTc; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_RgnApp; eauto.
  - inversion HTc; subst.
    eapply NWT_Return; eauto using NVT_Summary.
  - inversion HTc; subst.
    eapply NWT_Return; eauto using NVT_Summary.
  - inversion HTc; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_Cond; eauto.
  - inversion HTc; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_Ref; eauto.
  - inversion HTc; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_Deref; eauto.
  - inversion HTc; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_AssignLoc; eauto.
  - inversion HTc; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_PlusL; eauto.
  - inversion HTc; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_MinusL; eauto.
  - inversion HTc; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_TimesL; eauto.
  - inversion HTc; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_EqL; eauto.
  - inversion HTc; subst.
    eapply NWT_Return; eauto using NVT_Summary.
  - inversion HTc; subst.
    eapply NWT_Return; eauto using NVT_Summary.
  - inversion HTc; subst.
    eapply NWT_Return; eauto using NVT_Summary.
  - inversion HTc; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_ReadConc; eauto.
  - inversion HTc; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_WriteConc; eauto.
  - inversion HTc; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_ConcatL; eauto.
Qed.

Theorem NStep_return_same_context_preservation :
  forall gamma omega heap v k label state',
    NReturnSameContextKont k ->
    NWTState gamma omega (StReturn heap v k) ->
    NStep (StReturn heap v k) label state' ->
    NWTState gamma omega state'.
Proof.
  intros gamma omega heap v k label state' HSame HWT HStep.
  inversion HWT as
    [| gamma0 omega0 heap0 rho0 v0 k0 ty
      HHeap HRho HV HK
    |];
    subst; clear HWT.
  inversion HStep; subst; clear HStep;
    try solve [inversion HSame].
  - inversion HSame; subst.
    inversion HK; subst.
    inversion HV; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_MuAppArg; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    inversion HV; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_EffAppArg; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply NWT_Eval; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply NWT_Eval; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    match goal with
    | HVLoc : NValHasType ?rho ?heap0 (VLoc ?r ?l) (TyRef ?rgn ?ty),
      HLookup : heap_lookup ?r ?l ?heap0 = Some ?v_lookup |- _ =>
        destruct
          (NValHasType_ref_lookup rho heap0 r l rgn ty HVLoc)
          as (cell & HLookupTy & HCellTy);
        rewrite HLookup in HLookupTy
    end.
    inversion HLookupTy; subst.
    eapply NWT_Return; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_AssignVal; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_PlusR; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply NWT_Return; eauto using NVT_Nat.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_MinusR; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply NWT_Return; eauto using NVT_Nat.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_TimesR; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply NWT_Return; eauto using NVT_Nat.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_EqR; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply NWT_Return; eauto using NVT_Bool.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply NWT_Return; eauto using NVT_Summary.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply NWT_Return; eauto using NVT_Summary.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_ConcatR; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply NWT_Return; eauto using NVT_Summary.
  - inversion HSame; subst.
    eapply NWT_Done; eauto.
Qed.

Lemma NResolvedStateShape_const_preservation :
  forall heap env rho n k ty_out,
    NResolvedStateShape (StEval heap env rho (EConst n) k) ty_out ->
    NResolvedStateShape (StReturn heap (VNat n) k) ty_out.
Proof.
  intros heap env rho n k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply NRSS_Return; eauto using NRVS_Nat.
Qed.

Lemma NResolvedStateShape_bool_preservation :
  forall heap env rho b k ty_out,
    NResolvedStateShape (StEval heap env rho (EBool b) k) ty_out ->
    NResolvedStateShape (StReturn heap (VBool b) k) ty_out.
Proof.
  intros heap env rho b k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply NRSS_Return; eauto using NRVS_Bool.
Qed.

Lemma NResolvedStateShape_var_preservation :
  forall heap env rho x v k ty_out,
    env_lookup x env = Some v ->
    NResolvedStateShape (StEval heap env rho (EVar x) k) ty_out ->
    NResolvedStateShape (StReturn heap v k) ty_out.
Proof.
  intros heap env rho x v k ty_out HLookup HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  match goal with
  | HBind : ctx_binds x ty gamma |- _ =>
      destruct
        (NResolvedEnvShape_lookup
          rho heap env gamma x ty ty_res HEnv HBind HResolve)
        as (v_typed & HLookupTyped & HV)
  end.
  rewrite HLookup in HLookupTyped.
  inversion HLookupTyped; subst.
  eapply NRSS_Return; eauto.
Qed.

Lemma NResolvedStateShape_mu_preservation :
  forall heap env rho f x ec ee k ty_out,
    NResolvedStateShape (StEval heap env rho (EMu f x ec ee) k) ty_out ->
    NResolvedStateShape
      (StReturn heap (VClosure env rho f x ec ee) k)
      ty_out.
Proof.
  intros heap env rho f x ec ee k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply NRSS_Return; eauto.
  eapply NRVS_Closure with
    (gamma := gamma) (omega := omega)
    (ty_arg := ty_arg) (ty_body := ty_body); eauto.
Qed.

Lemma NResolvedStateShape_lambda_rgn_preservation :
  forall heap env rho x e k ty_out,
    NResolvedStateShape
      (StEval heap env rho (ELambdaRgn x e) k)
      ty_out ->
    NResolvedStateShape
      (StReturn heap (VRegionClosure env rho x e) k)
      ty_out.
Proof.
  intros heap env rho x e k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply NRSS_Return; eauto.
  eapply NRVS_RegionClosure with
    (gamma := gamma) (omega := omega); eauto.
Qed.

Lemma NResolvedStateShape_empty_preservation :
  forall heap env rho k ty_out,
    NResolvedStateShape (StEval heap env rho EEmpty k) ty_out ->
    NResolvedStateShape
      (StReturn heap (VSummary (SummarySet [])) k)
      ty_out.
Proof.
  intros heap env rho k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply NRSS_Return; eauto using NRVS_Summary.
Qed.

Lemma NResolvedStateShape_top_preservation :
  forall heap env rho k ty_out,
    NResolvedStateShape (StEval heap env rho ETop k) ty_out ->
    NResolvedStateShape
      (StReturn heap (VSummary SummaryTop) k)
      ty_out.
Proof.
  intros heap env rho k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply NRSS_Return; eauto using NRVS_Summary.
Qed.

Lemma NResolvedStateShape_cond_eval_preservation :
  forall heap env rho e et ef k ty_out,
    NResolvedStateShape
      (StEval heap env rho (ECond e et ef) k)
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho e (KCond et ef env rho k))
      ty_out.
Proof.
  intros heap env rho e et ef k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyBool) (ty_res := TyBool) (eff := eff_e);
    eauto using NResolve_Bool.
  eapply NRKS_Cond with
    (gamma := gamma) (omega := omega)
    (ty := ty) (ty_res := ty_res)
    (eff_t := eff_t) (eff_f := eff_f); eauto.
Qed.

Lemma NResolvedStateShape_ref_eval_preservation :
  forall heap env rho r e r_val k ty_out,
    eval_region rho r = Some r_val ->
    NResolvedStateShape
      (StEval heap env rho (ERef r e) k)
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho e (KRef r_val k))
      ty_out.
Proof.
  intros heap env rho r e r_val k ty_out HRgn HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  rewrite HRgn in H2. inversion H2; subst.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty0) (ty_res := ty') (eff := eff0);
    eauto.
  eapply NRKS_Ref; eauto.
Qed.

Lemma NResolvedStateShape_deref_eval_preservation :
  forall heap env rho r e k ty_out,
    NResolvedStateShape
      (StEval heap env rho (EDeref r e) k)
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho e (KDeref r k))
      ty_out.
Proof.
  intros heap env rho r e k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  match goal with
  | HWF : region_expr_wf omega r |- _ =>
      destruct (NRhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyRef r ty) (ty_res := TyRef (RConst r_val) ty_res)
    (eff := eff0); eauto.
  - eapply NResolve_Ref; eauto.
  - eapply NRKS_Deref; eauto.
Qed.

Lemma NResolvedStateShape_plus_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    NResolvedStateShape
      (StEval heap env rho (EPlus e1 e2) k)
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho e1 (KPlusL e2 env rho k))
      ty_out.
Proof.
  intros heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff1);
    eauto using NResolve_Nat.
  eapply NRKS_PlusL; eauto.
Qed.

Lemma NResolvedStateShape_minus_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    NResolvedStateShape
      (StEval heap env rho (EMinus e1 e2) k)
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho e1 (KMinusL e2 env rho k))
      ty_out.
Proof.
  intros heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff1);
    eauto using NResolve_Nat.
  eapply NRKS_MinusL; eauto.
Qed.

Lemma NResolvedStateShape_times_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    NResolvedStateShape
      (StEval heap env rho (ETimes e1 e2) k)
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho e1 (KTimesL e2 env rho k))
      ty_out.
Proof.
  intros heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff1);
    eauto using NResolve_Nat.
  eapply NRKS_TimesL; eauto.
Qed.

Lemma NResolvedStateShape_eq_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    NResolvedStateShape
      (StEval heap env rho (EEq e1 e2) k)
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho e1 (KEqL e2 env rho k))
      ty_out.
Proof.
  intros heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff1);
    eauto using NResolve_Nat.
  eapply NRKS_EqL; eauto.
Qed.

Lemma NResolvedStateShape_alloc_abs_preservation :
  forall heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    NResolvedStateShape
      (StEval heap env rho (EAllocAbs r) k)
      ty_out ->
    NResolvedStateShape
      (StReturn heap (VSummary (SummarySet [CAllocAbs r_val])) k)
      ty_out.
Proof.
  intros heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply NRSS_Return; eauto using NRVS_Summary.
Qed.

Lemma NResolvedStateShape_read_abs_preservation :
  forall heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    NResolvedStateShape
      (StEval heap env rho (EReadAbs r) k)
      ty_out ->
    NResolvedStateShape
      (StReturn heap (VSummary (SummarySet [CReadAbs r_val])) k)
      ty_out.
Proof.
  intros heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply NRSS_Return; eauto using NRVS_Summary.
Qed.

Lemma NResolvedStateShape_write_abs_preservation :
  forall heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    NResolvedStateShape
      (StEval heap env rho (EWriteAbs r) k)
      ty_out ->
    NResolvedStateShape
      (StReturn heap (VSummary (SummarySet [CWriteAbs r_val])) k)
      ty_out.
Proof.
  intros heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply NRSS_Return; eauto using NRVS_Summary.
Qed.

Lemma NResolvedStateShape_concat_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    NResolvedStateShape
      (StEval heap env rho (EConcat e1 e2) k)
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho e1 (KConcatL e2 env rho k))
      ty_out.
Proof.
  intros heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff1);
    eauto using NResolve_Effect.
  eapply NRKS_ConcatL; eauto.
Qed.

Lemma NResolvedStateShape_mu_app_eval_arg_preservation :
  forall heap env rho ea k closure_env closure_rho f x ec ee ty_out,
    NResolvedStateShape
      (StReturn heap
        (VClosure closure_env closure_rho f x ec ee)
        (KMuAppFun ea env rho k))
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho ea
        (KMuAppArg closure_env closure_rho f x ec ee k))
      ty_out.
Proof.
  intros heap env rho ea k closure_env closure_rho f x ec ee ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty_arg) (ty_res := ty_arg_res) (eff := eff_arg);
    eauto.
  eapply NRKS_MuAppArg with
    (gamma := gamma0) (omega := omega0)
    (ty_arg := ty_arg0) (ty_body := ty_body0)
    (eff_body := eff_body) (eff_summary := eff_summary);
    eauto.
Qed.

Lemma NResolvedStateShape_mu_app_body_preservation :
  forall heap v_arg closure_env closure_rho f x ec ee k ty_out,
    NResolvedStateShape
      (StReturn heap v_arg
        (KMuAppArg closure_env closure_rho f x ec ee k))
      ty_out ->
    NResolvedStateShape
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  eapply NRSS_Eval; eauto.
  econstructor; eauto.
  eapply NRES_EnvCons with
    (ty_res := TyArrow ty eff_body ty_body_res eff_summary).
  - eapply NResolve_Arrow; eauto.
  - eapply NRVS_Closure with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body); eauto.
  - assumption.
Qed.

Lemma NResolvedStateShape_eff_app_eval_arg_preservation :
  forall heap env rho ea k closure_env closure_rho f x ec ee ty_out,
    NResolvedStateShape
      (StReturn heap
        (VClosure closure_env closure_rho f x ec ee)
        (KEffAppFun ea env rho k))
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho ea
        (KEffAppArg closure_env closure_rho f x ec ee k))
      ty_out.
Proof.
  intros heap env rho ea k closure_env closure_rho f x ec ee ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty_arg) (ty_res := ty_arg_res) (eff := eff_arg);
    eauto.
  eapply NRKS_EffAppArg with
    (gamma := gamma0) (omega := omega0)
    (ty_arg := ty_arg0) (ty_body := ty_body0)
    (eff_body := eff_body) (eff_summary := eff_summary);
    eauto.
Qed.

Lemma NResolvedStateShape_eff_app_body_preservation :
  forall heap v_arg closure_env closure_rho f x ec ee k ty_out,
    NResolvedStateShape
      (StReturn heap v_arg
        (KEffAppArg closure_env closure_rho f x ec ee k))
      ty_out ->
    NResolvedStateShape
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  eapply NRSS_Eval with
    (gamma :=
      (x, ty_arg) ::
      (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
    (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary);
    eauto using NResolve_Effect.
  econstructor; eauto.
  eapply NRES_EnvCons with
    (ty_res := TyArrow ty eff_body ty_body_res eff_summary).
  - eapply NResolve_Arrow; eauto.
  - eapply NRVS_Closure with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body); eauto.
  - assumption.
Qed.

Lemma NResolvedStateShape_cond_true_preservation :
  forall heap et ef env rho k ty_out,
    NResolvedStateShape
      (StReturn heap (VBool true) (KCond et ef env rho k))
      ty_out ->
    NResolvedStateShape (StEval heap env rho et k) ty_out.
Proof.
  intros heap et ef env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRSS_Eval; eauto.
Qed.

Lemma NResolvedStateShape_cond_false_preservation :
  forall heap et ef env rho k ty_out,
    NResolvedStateShape
      (StReturn heap (VBool false) (KCond et ef env rho k))
      ty_out ->
    NResolvedStateShape (StEval heap env rho ef k) ty_out.
Proof.
  intros heap et ef env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRSS_Eval; eauto.
Qed.

Lemma NResolvedStateShape_deref_preservation :
  forall heap r_static r l v k ty_out,
    heap_lookup r l heap = Some v ->
    NResolvedStateShape
      (StReturn heap (VLoc r l) (KDeref r_static k))
      ty_out ->
    NResolvedStateShape (StReturn heap v k) ty_out.
Proof.
  intros heap r_static r l v k ty_out HLookup HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  match goal with
  | HCellLookup : heap_lookup ?rr ?ll heap = Some ?cell,
    HLookup' : heap_lookup ?rr ?ll heap = Some v,
    HCellShape : NResolvedValShape heap ?cell ?ty |- _ =>
      rewrite HLookup' in HCellLookup;
      inversion HCellLookup; subst
  end.
  eapply NRSS_Return; eauto.
Qed.

Lemma NResolvedStateShape_assign_loc_preservation :
  forall heap r_static ev env rho r l k ty_out,
    NResolvedStateShape
      (StReturn heap (VLoc r l) (KAssignLoc r_static ev env rho k))
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho ev (KAssignVal r_static (VLoc r l) k))
      ty_out.
Proof.
  intros heap r_static ev env rho r l k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRSS_Eval; eauto.
  eapply NRKS_AssignVal; eauto.
Qed.

Lemma NResolvedStateShape_plus_l_preservation :
  forall heap n e2 env rho k ty_out,
    NResolvedStateShape
      (StReturn heap (VNat n) (KPlusL e2 env rho k))
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho e2 (KPlusR n k))
      ty_out.
Proof.
  intros heap n e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using NResolve_Nat.
  eapply NRKS_PlusR; eauto.
Qed.

Lemma NResolvedStateShape_plus_r_preservation :
  forall heap n1 n2 k ty_out,
    NResolvedStateShape
      (StReturn heap (VNat n2) (KPlusR n1 k))
      ty_out ->
    NResolvedStateShape
      (StReturn heap (VNat (n1 + n2)) k)
      ty_out.
Proof.
  intros heap n1 n2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRSS_Return; eauto using NRVS_Nat.
Qed.

Lemma NResolvedStateShape_minus_l_preservation :
  forall heap n e2 env rho k ty_out,
    NResolvedStateShape
      (StReturn heap (VNat n) (KMinusL e2 env rho k))
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho e2 (KMinusR n k))
      ty_out.
Proof.
  intros heap n e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using NResolve_Nat.
  eapply NRKS_MinusR; eauto.
Qed.

Lemma NResolvedStateShape_minus_r_preservation :
  forall heap n1 n2 k ty_out,
    NResolvedStateShape
      (StReturn heap (VNat n2) (KMinusR n1 k))
      ty_out ->
    NResolvedStateShape
      (StReturn heap (VNat (n1 - n2)) k)
      ty_out.
Proof.
  intros heap n1 n2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRSS_Return; eauto using NRVS_Nat.
Qed.

Lemma NResolvedStateShape_times_l_preservation :
  forall heap n e2 env rho k ty_out,
    NResolvedStateShape
      (StReturn heap (VNat n) (KTimesL e2 env rho k))
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho e2 (KTimesR n k))
      ty_out.
Proof.
  intros heap n e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using NResolve_Nat.
  eapply NRKS_TimesR; eauto.
Qed.

Lemma NResolvedStateShape_times_r_preservation :
  forall heap n1 n2 k ty_out,
    NResolvedStateShape
      (StReturn heap (VNat n2) (KTimesR n1 k))
      ty_out ->
    NResolvedStateShape
      (StReturn heap (VNat (n1 * n2)) k)
      ty_out.
Proof.
  intros heap n1 n2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRSS_Return; eauto using NRVS_Nat.
Qed.

Lemma NResolvedStateShape_eq_l_preservation :
  forall heap n e2 env rho k ty_out,
    NResolvedStateShape
      (StReturn heap (VNat n) (KEqL e2 env rho k))
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho e2 (KEqR n k))
      ty_out.
Proof.
  intros heap n e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using NResolve_Nat.
  eapply NRKS_EqR; eauto.
Qed.

Lemma NResolvedStateShape_eq_r_preservation :
  forall heap n1 n2 k ty_out,
    NResolvedStateShape
      (StReturn heap (VNat n2) (KEqR n1 k))
      ty_out ->
    NResolvedStateShape
      (StReturn heap (VBool (Nat.eqb n1 n2)) k)
      ty_out.
Proof.
  intros heap n1 n2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRSS_Return; eauto using NRVS_Bool.
Qed.

Lemma NResolvedStateShape_read_conc_preservation :
  forall heap r l k ty_out,
    NResolvedStateShape
      (StReturn heap (VLoc r l) (KReadConc k))
      ty_out ->
    NResolvedStateShape
      (StReturn heap (VSummary (SummarySet [CReadConc r l])) k)
      ty_out.
Proof.
  intros heap r l k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  eapply NRSS_Return; eauto using NRVS_Summary.
Qed.

Lemma NResolvedStateShape_write_conc_preservation :
  forall heap r l k ty_out,
    NResolvedStateShape
      (StReturn heap (VLoc r l) (KWriteConc k))
      ty_out ->
    NResolvedStateShape
      (StReturn heap (VSummary (SummarySet [CWriteConc r l])) k)
      ty_out.
Proof.
  intros heap r l k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  eapply NRSS_Return; eauto using NRVS_Summary.
Qed.

Lemma NResolvedStateShape_concat_l_preservation :
  forall heap theta1 e2 env rho k ty_out,
    NResolvedStateShape
      (StReturn heap (VSummary theta1) (KConcatL e2 env rho k))
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho e2 (KConcatR theta1 k))
      ty_out.
Proof.
  intros heap theta1 e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff);
    eauto using NResolve_Effect.
  eapply NRKS_ConcatR; eauto.
Qed.

Lemma NResolvedStateShape_concat_r_preservation :
  forall heap theta1 theta2 k ty_out,
    NResolvedStateShape
      (StReturn heap (VSummary theta2) (KConcatR theta1 k))
      ty_out ->
    NResolvedStateShape
      (StReturn heap (VSummary (summary_union theta1 theta2)) k)
      ty_out.
Proof.
  intros heap theta1 theta2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRSS_Return; eauto using NRVS_Summary.
Qed.

Lemma NResolvedStateShape_done_preservation :
  forall heap v ty_out,
    NResolvedStateShape (StReturn heap v KDone) ty_out ->
    NResolvedStateShape (StDone heap v) ty_out.
Proof.
  intros heap v ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK |];
    subst; clear HState.
  inversion HK; subst.
  eapply NRSS_Done; eauto.
Qed.
