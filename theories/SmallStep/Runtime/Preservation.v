From Stdlib Require Import List.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Core.Values.
Require Import theories.SmallStep.Runtime.HeapNeutral.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Runtime.RegularPreservation.
Require Import theories.SmallStep.Runtime.RegularStateShape.
Require Import theories.SmallStep.Runtime.StateShape.
Require Import theories.SmallStep.Runtime.Trace.
Require Import theories.SmallStep.Runtime.Typing.
Require Import theories.SmallStep.Typing.Judgments.
Require Import theories.SmallStep.Typing.Regularity.
Require Import theories.SmallStep.Typing.Resolve.
Require Import theories.SmallStep.Typing.Types.

Import ListNotations.

Inductive NReturnSameContextKont : NKont -> Prop :=
| NRS_MuAppFun :
    forall ea env rho k,
      NReturnSameContextKont (KMuAppFun ea env rho k)
| NRS_EffAppFun :
    forall ea env rho k,
      NReturnSameContextKont (KEffAppFun ea env rho k)
| NRS_PairParEff1 :
    forall ef1 ea1 ef2 ea2 env rho k,
      NReturnSameContextKont
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)
| NRS_PairParEff2 :
    forall ef1 ea1 ef2 ea2 env rho theta1 k,
      NReturnSameContextKont
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)
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

Lemma NSteps_heap_neutral_resolved_state_preservation_from_step :
  forall
    (step_preserve :
      forall state label state' ty,
        NStep state label state' ->
        HeapNeutralTrace (label_trace label) ->
        NResolvedStateShape state ty ->
        NResolvedStateShape state' ty)
    state phi state' ty,
    NSteps state phi state' ->
    HeapNeutralTrace phi ->
    NResolvedStateShape state ty ->
    NResolvedStateShape state' ty.
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

Lemma NStepsN_heap_neutral_resolved_state_preservation_from_step :
  forall
    (step_preserve :
      forall state label state' ty,
        NStep state label state' ->
        HeapNeutralTrace (label_trace label) ->
        NResolvedStateShape state ty ->
        NResolvedStateShape state' ty)
    n state phi state' ty,
    NStepsN n state phi state' ->
    HeapNeutralTrace phi ->
    NResolvedStateShape state ty ->
    NResolvedStateShape state' ty.
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

Lemma NResolvedStateShape_aligned :
  forall state ty,
    NResolvedStateShape state ty ->
    NStateHeapsAligned state.
Proof.
  intros state ty HState.
  induction HState; simpl; try exact I.
  repeat split; assumption || congruence.
Qed.

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
    | | | |];
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
    eapply NKT_PairParEff1; eauto.
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
    | | |];
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
    inversion HV; subst.
    eapply NWT_Eval; eauto.
    eapply NKT_PairParEff2; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply NWT_PairParRun with (heap := heap) (rho := rho).
    + reflexivity.
    + reflexivity.
    + eapply NWT_Eval; eauto. constructor.
    + eapply NWT_Eval; eauto. constructor.
    + exact HHeap.
    + exact HRho.
    + eassumption.
  - inversion HSame; subst.
    eapply NWT_Error; eauto.
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
    subst; clear HState.
  inversion HTc; subst.
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
    subst; clear HState.
  inversion HTc; subst.
  match goal with
  | HWF : region_expr_wf omega r |- _ =>
      destruct (NRhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyRef (region_expr_to_type r) ty)
    (ty_res := TyRef (region_const_type r_val) ty_res)
    (eff := eff0); eauto.
  - eapply NResolve_Ref; eauto.
    eapply NResolveRegionType_region_expr_to_type.
    exact HRgn.
  - eapply NRKS_Deref; eauto.
Qed.

Lemma NResolvedStateShape_assign_eval_preservation_wf :
  forall heap env rho r ea ev k ty_out,
    (forall gamma omega rgn ty eff,
      NTcExp gamma omega ea (TyRef rgn ty) eff ->
      NRegionTypeWF omega rgn /\ NTyWF omega ty) ->
    NResolvedStateShape
      (StEval heap env rho (EAssign r ea ev) k)
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho ea (KAssignLoc r ev env rho k))
      ty_out.
Proof.
  intros heap env rho r ea ev k ty_out HRefWF HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | | | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  match goal with
  | HAddr :
      NTcExp gamma omega ea (TyRef (region_expr_to_type r) ?ty_cell)
        ?eff_a,
    HVal : NTcExp gamma omega ev ?ty_cell ?eff_v,
    HWF : region_expr_wf omega r |- _ =>
      destruct
        (HRefWF
          gamma omega (region_expr_to_type r) ty_cell eff_a HAddr)
        as (_ & HTyWF);
      destruct (NRhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn);
      destruct (NResolveTy_exists 0 omega rho ty_cell HRho HTyWF)
        as (ty_cell_res & HTyResolve);
      eapply NRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyRef (region_expr_to_type r) ty_cell)
        (ty_res := TyRef (region_const_type r_val) ty_cell_res)
        (eff := eff_a);
        eauto;
      [ eapply NResolve_Ref; eauto;
        eapply NResolveRegionType_region_expr_to_type;
        exact HRgn
      | eapply NRKS_AssignLoc with
          (gamma := gamma) (omega := omega)
          (ty := ty_cell) (ty_res := ty_cell_res)
          (eff_v := eff_v);
        eauto ]
  end.
Qed.

Lemma NResolvedStateShape_rgn_app_eval_preservation_resolved :
  forall heap env rho er r k gamma omega eff_body ty eff_f
    eff_body_res ty_body_res r_val ty_out,
    NResolvedHeapShape heap ->
    NResolvedEnvShape rho heap env gamma ->
    NRhoModels omega rho ->
    eval_region rho r = Some r_val ->
    NResolveStaticEffect rho eff_body eff_body_res ->
    NResolveTy rho ty ty_body_res ->
    NTcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
    NResolvedKontShape heap k
      (open_ty_type (region_const_type r_val) ty_body_res)
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho er (KRgnApp r rho k))
      ty_out.
Proof.
  intros heap env rho er r k gamma omega eff_body ty eff_f
    eff_body_res ty_body_res r_val ty_out
    HHeap HEnv HRho HRgn HEffResolve HTyResolve HTyped HK.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyForallRgn eff_body ty)
    (ty_res := TyForallRgn eff_body_res ty_body_res)
    (eff := eff_f);
    eauto.
  - eapply NResolve_ForallRgn; eauto.
  - eapply NRKS_RgnApp; eauto.
Qed.

Lemma NResolvedStateShape_rgn_app_eval_preservation_wf :
  forall heap env rho er r k ty_out,
    (forall gamma omega eff_body ty eff_f,
      NTcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
      NStaticEffectWFAt 1 omega eff_body /\
      NTyWFAt 1 omega ty) ->
    NResolvedStateShape
      (StEval heap env rho (ERgnApp er r) k)
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho er (KRgnApp r rho k))
      ty_out.
Proof.
  intros heap env rho er r k ty_out HForallWF HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty_result ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTyped HK | | | |];
    subst; clear HState.
  inversion HTyped; subst.
  match goal with
  | HWF : region_expr_wf omega r |- _ =>
      destruct (NRhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  match goal with
  | HTypedFun :
      NTcExp gamma omega er (TyForallRgn ?eff_body ?ty_body) ?eff_f
      |- _ =>
      destruct (HForallWF gamma omega eff_body ty_body eff_f HTypedFun)
        as (HEffWF & HTyWF);
      destruct
        (NResolveStaticEffect_exists
          1 omega rho eff_body HRho HEffWF)
        as (eff_body_res & HEffResolve);
      destruct
        (NResolveTy_exists
          1 omega rho ty_body HRho HTyWF)
        as (ty_body_res & HTyResolve);
      pose proof
        (NResolveTy_open_ty
          rho r ty_body ty_body_res r_val HRgn HTyResolve)
        as HOpenResolve;
      pose proof
        (NResolveTy_deterministic
          rho (open_ty r ty_body) ty_res
          (open_ty_type (region_const_type r_val) ty_body_res)
          HResolve HOpenResolve)
        as HTyResEq;
      subst ty_res;
      exact
        (NResolvedStateShape_rgn_app_eval_preservation_resolved
          heap env rho er r k gamma omega eff_body ty_body eff_f
          eff_body_res ty_body_res r_val ty_out
          HHeap HEnv HRho HRgn HEffResolve HTyResolve HTypedFun HK)
  end.
Qed.

Lemma NResolvedStateShape_rgn_app_return_preservation_wf :
  forall heap closure_env closure_rho x e arg_rho r r_val k ty_out,
    eval_region arg_rho r = Some r_val ->
    (forall gamma omega ty eff,
      NTcExp gamma (x :: omega) e ty eff ->
      ~ In x omega /\ NCtxWF omega gamma /\
      NTyWFAt 0 (x :: omega) ty) ->
    NResolvedStateShape
      (StReturn heap
        (VRegionClosure closure_env closure_rho x e)
        (KRgnApp r arg_rho k))
      ty_out ->
    NResolvedStateShape
      (StEval heap closure_env
        (rho_extend x r_val closure_rho)
        e
        k)
      ty_out.
Proof.
  intros heap closure_env closure_rho x e arg_rho r r_val k ty_out
    HRgn HBodyWF HState.
  inversion HState as
    [| heap0 v0 k0 ty_in ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HV as
    [| | | | | | |
      heap1 closure_env0 closure_rho0 x0 e0 gamma omega
      ty ty_res eff eff_res HEnv HRho HEffResolve HTyResolve HTyped];
    subst; clear HV.
  inversion HK as
    [| | | | | | |
      heap2 r0 arg_rho0 r_val0 k1 eff0 ty0 ty_out1
      HRgnKont HKInner | | | | | | | | | | | | | | | | |];
    subst; clear HK.
  rewrite HRgn in HRgnKont.
  inversion HRgnKont.
  subst r_val0.
  clear HRgnKont.
  destruct (HBodyWF gamma omega ty eff HTyped)
    as (HFresh & HCtxWF & HTyWF).
  eapply NRSS_Eval with
    (gamma := gamma) (omega := x :: omega)
    (ty := ty)
    (ty_res := open_ty_type (region_const_type r_val) ty_res)
    (eff := eff);
    eauto.
  - eapply NResolvedEnvShape_extend_fresh; eauto.
  - eapply NRhoModels_extend; eauto.
  - eapply NResolveTy_rho_extend_close_ty; eauto.
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
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
      HHeap HEnv HRho HResolve HTc HK | | | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff1);
    eauto using NResolve_Effect.
  eapply NRKS_ConcatL; eauto.
Qed.

Lemma NResolvedStateShape_mu_app_eval_preservation_wf :
  forall heap env rho ef ea k ty_out,
    (forall gamma omega ty_arg eff_body ty_body eff_summary eff_f,
      NTcExp gamma omega ef
        (TyArrow ty_arg eff_body ty_body eff_summary) eff_f ->
      NTyWF omega ty_arg /\
      NStaticEffectWF omega eff_body /\
      NTyWF omega ty_body /\
      NStaticEffectWF omega eff_summary) ->
    NResolvedStateShape
      (StEval heap env rho (EMuApp ef ea) k)
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho ef (KMuAppFun ea env rho k))
      ty_out.
Proof.
  intros heap env rho ef ea k ty_out HArrowWF HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | | | |];
    subst; clear HState.
  inversion HTc; subst.
  match goal with
  | HTypedFun :
      NTcExp gamma omega ef
        (TyArrow ?ty_arg0 ?eff_body0 ?ty_body0 ?eff_summary0)
        ?eff_f0,
    HArgTyped : NTcExp gamma omega ea ?ty_arg0 ?eff_a0 |- _ =>
      destruct
        (HArrowWF
          gamma omega ty_arg0 eff_body0 ty_body0 eff_summary0
          eff_f0 HTypedFun)
        as (HArgWF & HBodyEffWF & HBodyWF & HSummaryEffWF);
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
      pose proof
        (NResolveTy_deterministic
          rho ty_body0 ty_res ty_body_res HResolve HBodyResolve)
        as HBodyEq;
      subst ty_body_res;
      eapply NRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyArrow ty_arg0 eff_body0 ty_body0 eff_summary0)
        (ty_res := TyArrow
          ty_arg_res eff_body_res ty_res eff_summary_res)
        (eff := eff_f0);
        eauto;
      [ eapply NResolve_Arrow; eauto
      | eapply NRKS_MuAppFun with
          (gamma := gamma) (omega := omega)
          (ty_arg := ty_arg0) (ty_body := ty_body0)
          (eff_body := eff_body0) (eff_summary := eff_summary0)
          (eff_arg := eff_a0);
        eauto ]
  end.
Qed.

Lemma NResolvedStateShape_eff_app_eval_preservation_wf :
  forall heap env rho ef ea k ty_out,
    (forall gamma omega ty_arg eff_body ty_body eff_summary eff_f,
      NTcExp gamma omega ef
        (TyArrow ty_arg eff_body ty_body eff_summary) eff_f ->
      NTyWF omega ty_arg /\
      NStaticEffectWF omega eff_body /\
      NTyWF omega ty_body /\
      NStaticEffectWF omega eff_summary) ->
    NResolvedStateShape
      (StEval heap env rho (EEffApp ef ea) k)
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho ef (KEffAppFun ea env rho k))
      ty_out.
Proof.
  intros heap env rho ef ea k ty_out HArrowWF HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | | | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  match goal with
  | HTypedFun :
      NTcExp gamma omega ef
        (TyArrow ?ty_arg0 ?eff_body0 ?ty_body0 ?eff_summary0)
        ?eff_f0,
    HArgTyped : NTcExp gamma omega ea ?ty_arg0 ?eff_a0 |- _ =>
      destruct
        (HArrowWF
          gamma omega ty_arg0 eff_body0 ty_body0 eff_summary0
          eff_f0 HTypedFun)
        as (HArgWF & HBodyEffWF & HBodyWF & HSummaryEffWF);
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
      eapply NRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyArrow ty_arg0 eff_body0 ty_body0 eff_summary0)
        (ty_res := TyArrow
          ty_arg_res eff_body_res ty_body_res eff_summary_res)
        (eff := eff_f0);
        eauto;
      [ eapply NResolve_Arrow; eauto
      | eapply NRKS_EffAppFun with
          (gamma := gamma) (omega := omega)
          (ty_arg := ty_arg0) (ty_body := ty_body0)
          (eff_body := eff_body0) (eff_summary := eff_summary0)
          (eff_arg := eff_a0);
        eauto ]
  end.
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    (eff_body := eff_body0) (eff_summary := eff_summary0);
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NRSS_Eval; eauto.
  econstructor; eauto.
  eapply NRES_EnvCons with
    (ty_res := TyArrow ty eff_body_res ty_body_res eff_summary_res).
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    (eff_body := eff_body0) (eff_summary := eff_summary0);
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    (ty_res := TyArrow ty eff_body_res ty_body_res eff_summary_res).
  - eapply NResolve_Arrow; eauto.
  - eapply NRVS_Closure with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body); eauto.
  - assumption.
Qed.

Lemma NResolvedStateShape_pair_par_eval_preservation :
  forall heap env rho ef1 ea1 ef2 ea2 k ty_out,
    NResolvedStateShape
      (StEval heap env rho
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)) k)
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho (EEffApp ef1 ea1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      ty_out.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | | | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary1);
    eauto using NResolve_Effect.
  eapply NRKS_PairParEff1 with
    (gamma := gamma) (omega := omega)
    (ty1 := ty1) (ty2 := ty2)
    (eff1 := eff1) (eff2 := eff2)
    (eff_summary2 := eff_summary2);
    eauto.
Qed.

Lemma NResolvedStateShape_pair_par_eff1_preservation :
  forall heap theta1 ef1 ea1 ef2 ea2 env rho k ty_out,
    NResolvedStateShape
      (StReturn heap (VSummary theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      ty_out ->
    NResolvedStateShape
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
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary2);
    eauto using NResolve_Effect.
  eapply NRKS_PairParEff2 with
    (gamma := gamma) (omega := omega)
    (ty1 := ty1) (ty2 := ty2)
    (eff1 := eff1) (eff2 := eff2);
    eauto.
Qed.

Lemma NResolvedStateShape_pair_par_check_pass_preservation :
  forall heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out,
    NResolvedStateShape
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      ty_out ->
    NResolvedStateShape
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
  eapply NRSS_PairParRun with
    (heap := heap) (ty1 := ty1_res) (ty2 := ty2_res);
    simpl; eauto.
  - eapply NRSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty1) (ty_res := ty1_res) (eff := eff1);
      eauto.
    constructor.
  - eapply NRSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty2) (ty_res := ty2_res) (eff := eff2);
      eauto.
    constructor.
Qed.

Lemma NResolvedStateShape_pair_par_check_fail_preservation :
  forall heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out,
    NResolvedStateShape
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      ty_out ->
    NResolvedStateShape (StError heap) ty_out.
Proof.
  intros heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  eapply NRSS_Error; eauto.
Qed.

Lemma NResolvedStateShape_pair_par_done_pass_preservation :
  forall heap v1 v2 phi_left phi_right k ty_out,
    NResolvedStateShape
      (StPairParRun
        (StDone heap v1)
        (StDone heap v2)
        phi_left phi_right k)
      ty_out ->
    NResolvedStateShape (StReturn heap (VPair v1 v2) k) ty_out.
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
  eapply NRSS_Return; eauto.
  eapply NRVS_Pair; eauto.
Qed.

Lemma NResolvedStateShape_pair_par_done_fail_preservation :
  forall heap v1 v2 phi_left phi_right k ty_out,
    NResolvedStateShape
      (StPairParRun
        (StDone heap v1)
        (StDone heap v2)
        phi_left phi_right k)
      ty_out ->
    NResolvedStateShape (StError heap) ty_out.
Proof.
  intros heap v1 v2 phi_left phi_right k ty_out HState.
  inversion HState as
    [| | | |
      left_state right_state phi_left0 phi_right0 k0 heap0
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    subst; clear HState; simpl in *; subst.
  inversion HLeft; subst.
  eapply NRSS_Error; eauto.
Qed.

Lemma NResolvedStateShape_pair_par_run_left_preservation :
  forall left_state right_state phi_left phi_right k
    label left_state' ty_out,
    NStep left_state label left_state' ->
    NStateHeapsAligned
      (StPairParRun left_state right_state phi_left phi_right k) ->
    HeapNeutralTrace (label_trace label) ->
    (forall ty,
      NResolvedStateShape left_state ty ->
      NResolvedStateShape left_state' ty) ->
    NResolvedStateShape
      (StPairParRun left_state right_state phi_left phi_right k)
      ty_out ->
    NResolvedStateShape
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
  eapply NRSS_PairParRun with (ty1 := ty1) (ty2 := ty2); eauto.
Qed.

Lemma NResolvedStateShape_pair_par_run_left_preservation_from_child :
  forall left_state right_state phi_left phi_right k
    label left_state' ty_out,
    NStep left_state label left_state' ->
    HeapNeutralTrace (label_trace label) ->
    (forall ty,
      NResolvedStateShape left_state ty ->
      NResolvedStateShape left_state' ty) ->
    NResolvedStateShape
      (StPairParRun left_state right_state phi_left phi_right k)
      ty_out ->
    NResolvedStateShape
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
  eapply NResolvedStateShape_pair_par_run_left_preservation; eauto.
  eapply NResolvedStateShape_aligned; eauto.
Qed.

Lemma NResolvedStateShape_pair_par_run_right_preservation :
  forall heap v1 right_state phi_left phi_right k
    label right_state' ty_out,
    NStep right_state label right_state' ->
    NStateHeapsAligned
      (StPairParRun (StDone heap v1) right_state phi_left phi_right k) ->
    HeapNeutralTrace (label_trace label) ->
    (forall ty,
      NResolvedStateShape right_state ty ->
      NResolvedStateShape right_state' ty) ->
    NResolvedStateShape
      (StPairParRun (StDone heap v1) right_state phi_left phi_right k)
      ty_out ->
    NResolvedStateShape
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
  eapply NRSS_PairParRun with
    (heap := heap) (ty1 := ty1) (ty2 := ty2); eauto.
Qed.

Lemma NResolvedStateShape_pair_par_run_right_preservation_from_child :
  forall heap v1 right_state phi_left phi_right k
    label right_state' ty_out,
    NStep right_state label right_state' ->
    HeapNeutralTrace (label_trace label) ->
    (forall ty,
      NResolvedStateShape right_state ty ->
      NResolvedStateShape right_state' ty) ->
    NResolvedStateShape
      (StPairParRun (StDone heap v1) right_state phi_left phi_right k)
      ty_out ->
    NResolvedStateShape
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
  eapply NResolvedStateShape_pair_par_run_right_preservation; eauto.
  eapply NResolvedStateShape_aligned; eauto.
Qed.

Lemma NResolvedStateShape_pair_par_left_error_preservation :
  forall heap right_state phi_left phi_right k ty_out,
    NResolvedStateShape
      (StPairParRun (StError heap) right_state phi_left phi_right k)
      ty_out ->
    NResolvedStateShape (StError heap) ty_out.
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
  eapply NRSS_Error; eauto.
Qed.

Lemma NResolvedStateShape_pair_par_right_error_preservation :
  forall heap_left v1 heap_right phi_left phi_right k ty_out,
    NResolvedStateShape
      (StPairParRun
        (StDone heap_left v1)
        (StError heap_right)
        phi_left phi_right k)
      ty_out ->
    NResolvedStateShape (StError heap_right) ty_out.
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
  eapply NRSS_Error; eauto.
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NRSS_Return; eauto using NRVS_Bool.
Qed.

Lemma NResolvedStateShape_read_conc_eval_preservation_wf :
  forall heap env rho e k ty_out,
    (forall gamma omega rgn ty eff,
      NTcExp gamma omega e (TyRef rgn ty) eff ->
      NRegionTypeWF omega rgn /\ NTyWF omega ty) ->
    NResolvedStateShape
      (StEval heap env rho (EReadConc e) k)
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho e (KReadConc k))
      ty_out.
Proof.
  intros heap env rho e k ty_out HRefWF HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | | | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  match goal with
  | HTypedRef : NTcExp gamma omega e (TyRef ?rgn ?ty_ref) ?eff_ref
      |- _ =>
      destruct (HRefWF gamma omega rgn ty_ref eff_ref HTypedRef)
        as (HRgnWF & HTyWF);
      destruct
        (NResolveRegionType_exists 0 omega rho rgn HRho HRgnWF)
        as (rgn_res & HRgnResolve);
      destruct (NResolveTy_exists 0 omega rho ty_ref HRho HTyWF)
        as (ty_ref_res & HTyResolve);
      destruct
        (NResolveRegionType_wf0_const
          omega rho rgn rgn_res HRgnWF HRgnResolve)
        as (r_val & HRgnResEq);
      subst rgn_res;
      eapply NRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyRef rgn ty_ref)
        (ty_res := TyRef (region_const_type r_val) ty_ref_res)
        (eff := eff_ref);
        eauto;
      [ eapply NResolve_Ref; eauto
      | eapply NRKS_ReadConc; eauto ]
  end.
Qed.

Lemma NResolvedStateShape_write_conc_eval_preservation_wf :
  forall heap env rho e k ty_out,
    (forall gamma omega rgn ty eff,
      NTcExp gamma omega e (TyRef rgn ty) eff ->
      NRegionTypeWF omega rgn /\ NTyWF omega ty) ->
    NResolvedStateShape
      (StEval heap env rho (EWriteConc e) k)
      ty_out ->
    NResolvedStateShape
      (StEval heap env rho e (KWriteConc k))
      ty_out.
Proof.
  intros heap env rho e k ty_out HRefWF HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | | | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  match goal with
  | HTypedRef : NTcExp gamma omega e (TyRef ?rgn ?ty_ref) ?eff_ref
      |- _ =>
      destruct (HRefWF gamma omega rgn ty_ref eff_ref HTypedRef)
        as (HRgnWF & HTyWF);
      destruct
        (NResolveRegionType_exists 0 omega rho rgn HRho HRgnWF)
        as (rgn_res & HRgnResolve);
      destruct (NResolveTy_exists 0 omega rho ty_ref HRho HTyWF)
        as (ty_ref_res & HTyResolve);
      destruct
        (NResolveRegionType_wf0_const
          omega rho rgn rgn_res HRgnWF HRgnResolve)
        as (r_val & HRgnResEq);
      subst rgn_res;
      eapply NRSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyRef rgn ty_ref)
        (ty_res := TyRef (region_const_type r_val) ty_ref_res)
        (eff := eff_ref);
        eauto;
      [ eapply NResolve_Ref; eauto
      | eapply NRKS_WriteConc; eauto ]
  end.
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
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
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NRSS_Done; eauto.
Qed.

Theorem NStep_heap_neutral_resolved_state_preservation_wf :
  forall
    (HArrowWF :
      forall ef gamma omega ty_arg eff_body ty_body eff_summary eff_f,
        NTcExp gamma omega ef
          (TyArrow ty_arg eff_body ty_body eff_summary)
          eff_f ->
        NTyWF omega ty_arg /\
        NStaticEffectWF omega eff_body /\
        NTyWF omega ty_body /\
        NStaticEffectWF omega eff_summary)
    (HForallWF :
      forall er gamma omega eff_body ty eff_f,
        NTcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
        NStaticEffectWFAt 1 omega eff_body /\
        NTyWFAt 1 omega ty)
    (HRegionBodyWF :
      forall x e gamma omega ty eff,
        NTcExp gamma (x :: omega) e ty eff ->
        ~ In x omega /\ NCtxWF omega gamma /\
        NTyWFAt 0 (x :: omega) ty)
    (HRefWF :
      forall e gamma omega rgn ty eff,
        NTcExp gamma omega e (TyRef rgn ty) eff ->
        NRegionTypeWF omega rgn /\ NTyWF omega ty)
    state label state' ty,
    NStep state label state' ->
    HeapNeutralTrace (label_trace label) ->
    NResolvedStateShape state ty ->
    NResolvedStateShape state' ty.
Proof.
  intros HArrowWF HForallWF HRegionBodyWF HRefWF
    state label state' ty HStep.
  revert ty.
  induction HStep; intros ty_out HNeutral HState; simpl in HNeutral.
  - eapply NResolvedStateShape_const_preservation; eauto.
  - eapply NResolvedStateShape_bool_preservation; eauto.
  - eapply NResolvedStateShape_var_preservation; eauto.
  - eapply NResolvedStateShape_mu_preservation; eauto.
  - eapply NResolvedStateShape_lambda_rgn_preservation; eauto.
  - eapply NResolvedStateShape_mu_app_eval_preservation_wf; eauto.
  - eapply NResolvedStateShape_mu_app_eval_arg_preservation; eauto.
  - eapply NResolvedStateShape_mu_app_body_preservation; eauto.
  - eapply NResolvedStateShape_eff_app_eval_preservation_wf; eauto.
  - eapply NResolvedStateShape_eff_app_eval_arg_preservation; eauto.
  - eapply NResolvedStateShape_eff_app_body_preservation; eauto.
  - eapply NResolvedStateShape_pair_par_eval_preservation; eauto.
  - eapply NResolvedStateShape_pair_par_eff1_preservation; eauto.
  - eapply NResolvedStateShape_pair_par_check_pass_preservation; eauto.
  - eapply NResolvedStateShape_pair_par_check_fail_preservation; eauto.
  - eapply NResolvedStateShape_pair_par_run_left_preservation_from_child;
      eauto.
  - eapply NResolvedStateShape_pair_par_run_right_preservation_from_child;
      eauto.
  - eapply NResolvedStateShape_pair_par_left_error_preservation; eauto.
  - eapply NResolvedStateShape_pair_par_right_error_preservation; eauto.
  - eapply NResolvedStateShape_pair_par_done_pass_preservation; eauto.
  - eapply NResolvedStateShape_pair_par_done_fail_preservation; eauto.
  - eapply NResolvedStateShape_rgn_app_eval_preservation_wf; eauto.
  - eapply NResolvedStateShape_rgn_app_return_preservation_wf; eauto.
  - eapply NResolvedStateShape_empty_preservation; eauto.
  - eapply NResolvedStateShape_top_preservation; eauto.
  - eapply NResolvedStateShape_cond_eval_preservation; eauto.
  - eapply NResolvedStateShape_cond_true_preservation; eauto.
  - eapply NResolvedStateShape_cond_false_preservation; eauto.
  - eapply NResolvedStateShape_ref_eval_preservation; eauto.
  - destruct HNeutral as (HNoAlloc & _).
    exfalso. eapply HNoAlloc.
    simpl. left. reflexivity.
  - eapply NResolvedStateShape_deref_eval_preservation; eauto.
  - eapply NResolvedStateShape_deref_preservation; eauto.
  - eapply NResolvedStateShape_assign_eval_preservation_wf; eauto.
  - eapply NResolvedStateShape_assign_loc_preservation; eauto.
  - destruct HNeutral as (_ & HReadOnly).
    exfalso. eapply HReadOnly.
    simpl. left. reflexivity.
  - eapply NResolvedStateShape_plus_eval_preservation; eauto.
  - eapply NResolvedStateShape_plus_l_preservation; eauto.
  - eapply NResolvedStateShape_plus_r_preservation; eauto.
  - eapply NResolvedStateShape_minus_eval_preservation; eauto.
  - eapply NResolvedStateShape_minus_l_preservation; eauto.
  - eapply NResolvedStateShape_minus_r_preservation; eauto.
  - eapply NResolvedStateShape_times_eval_preservation; eauto.
  - eapply NResolvedStateShape_times_l_preservation; eauto.
  - eapply NResolvedStateShape_times_r_preservation; eauto.
  - eapply NResolvedStateShape_eq_eval_preservation; eauto.
  - eapply NResolvedStateShape_eq_l_preservation; eauto.
  - eapply NResolvedStateShape_eq_r_preservation; eauto.
  - eapply NResolvedStateShape_alloc_abs_preservation; eauto.
  - eapply NResolvedStateShape_read_abs_preservation; eauto.
  - eapply NResolvedStateShape_write_abs_preservation; eauto.
  - eapply NResolvedStateShape_read_conc_eval_preservation_wf; eauto.
  - eapply NResolvedStateShape_read_conc_preservation; eauto.
  - eapply NResolvedStateShape_write_conc_eval_preservation_wf; eauto.
  - eapply NResolvedStateShape_write_conc_preservation; eauto.
  - eapply NResolvedStateShape_concat_eval_preservation; eauto.
  - eapply NResolvedStateShape_concat_l_preservation; eauto.
  - eapply NResolvedStateShape_concat_r_preservation; eauto.
  - eapply NResolvedStateShape_done_preservation; eauto.
Qed.

Theorem NStep_heap_neutral_regular_state_to_resolved_preservation :
  forall state label state' ty,
    NStep state label state' ->
    HeapNeutralTrace (label_trace label) ->
    NRegularResolvedStateShape state ty ->
    NResolvedStateShape state' ty.
Proof.
  intros state label state' ty HStep HNeutral HState.
  eapply NRegularResolvedStateShape_to_resolved.
  eapply NStep_heap_neutral_regular_state_preservation; eauto.
Qed.

Theorem NSteps_heap_neutral_resolved_state_preservation_wf :
  forall
    (HArrowWF :
      forall ef gamma omega ty_arg eff_body ty_body eff_summary eff_f,
        NTcExp gamma omega ef
          (TyArrow ty_arg eff_body ty_body eff_summary)
          eff_f ->
        NTyWF omega ty_arg /\
        NStaticEffectWF omega eff_body /\
        NTyWF omega ty_body /\
        NStaticEffectWF omega eff_summary)
    (HForallWF :
      forall er gamma omega eff_body ty eff_f,
        NTcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
        NStaticEffectWFAt 1 omega eff_body /\
        NTyWFAt 1 omega ty)
    (HRegionBodyWF :
      forall x e gamma omega ty eff,
        NTcExp gamma (x :: omega) e ty eff ->
        ~ In x omega /\ NCtxWF omega gamma /\
        NTyWFAt 0 (x :: omega) ty)
    (HRefWF :
      forall e gamma omega rgn ty eff,
        NTcExp gamma omega e (TyRef rgn ty) eff ->
        NRegionTypeWF omega rgn /\ NTyWF omega ty)
    state phi state' ty,
    NSteps state phi state' ->
    HeapNeutralTrace phi ->
    NResolvedStateShape state ty ->
    NResolvedStateShape state' ty.
Proof.
  intros HArrowWF HForallWF HRegionBodyWF HRefWF
    state phi state' ty HSteps HNeutral HState.
  eapply NSteps_heap_neutral_resolved_state_preservation_from_step;
    eauto.
  intros step_state label step_state' step_ty HStep HStepNeutral HStepState.
  eapply NStep_heap_neutral_resolved_state_preservation_wf; eauto.
Qed.

Theorem NSteps_heap_neutral_regular_state_to_resolved_preservation :
  forall state phi state' ty,
    NSteps state phi state' ->
    HeapNeutralTrace phi ->
    NRegularResolvedStateShape state ty ->
    NResolvedStateShape state' ty.
Proof.
  intros state phi state' ty HSteps HNeutral HState.
  eapply NRegularResolvedStateShape_to_resolved.
  eapply NSteps_heap_neutral_regular_state_preservation; eauto.
Qed.

Theorem NStepsN_heap_neutral_resolved_state_preservation_wf :
  forall
    (HArrowWF :
      forall ef gamma omega ty_arg eff_body ty_body eff_summary eff_f,
        NTcExp gamma omega ef
          (TyArrow ty_arg eff_body ty_body eff_summary)
          eff_f ->
        NTyWF omega ty_arg /\
        NStaticEffectWF omega eff_body /\
        NTyWF omega ty_body /\
        NStaticEffectWF omega eff_summary)
    (HForallWF :
      forall er gamma omega eff_body ty eff_f,
        NTcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
        NStaticEffectWFAt 1 omega eff_body /\
        NTyWFAt 1 omega ty)
    (HRegionBodyWF :
      forall x e gamma omega ty eff,
        NTcExp gamma (x :: omega) e ty eff ->
        ~ In x omega /\ NCtxWF omega gamma /\
        NTyWFAt 0 (x :: omega) ty)
    (HRefWF :
      forall e gamma omega rgn ty eff,
        NTcExp gamma omega e (TyRef rgn ty) eff ->
        NRegionTypeWF omega rgn /\ NTyWF omega ty)
    n state phi state' ty,
    NStepsN n state phi state' ->
    HeapNeutralTrace phi ->
    NResolvedStateShape state ty ->
    NResolvedStateShape state' ty.
Proof.
  intros HArrowWF HForallWF HRegionBodyWF HRefWF
    n state phi state' ty HSteps HNeutral HState.
  eapply NStepsN_heap_neutral_resolved_state_preservation_from_step;
    eauto.
  intros step_state label step_state' step_ty HStep HStepNeutral HStepState.
  eapply NStep_heap_neutral_resolved_state_preservation_wf; eauto.
Qed.

Theorem NStepsN_heap_neutral_regular_state_to_resolved_preservation :
  forall n state phi state' ty,
    NStepsN n state phi state' ->
    HeapNeutralTrace phi ->
    NRegularResolvedStateShape state ty ->
    NResolvedStateShape state' ty.
Proof.
  intros n state phi state' ty HSteps HNeutral HState.
  eapply NRegularResolvedStateShape_to_resolved.
  eapply NStepsN_heap_neutral_regular_state_preservation; eauto.
Qed.
