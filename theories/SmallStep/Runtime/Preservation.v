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

(** Preservation for resolved state shapes.

    This file contains the rule-by-rule proof layer.  Clients should prefer the
    stable aliases in [Runtime.PreservationPublic] unless they need an internal
    case lemma directly. *)

Inductive ReturnSameContextKont : Kont -> Prop :=
| RS_MuAppFun :
    forall ea env rho k,
      ReturnSameContextKont (KMuAppFun ea env rho k)
| RS_EffAppFun :
    forall ea env rho k,
      ReturnSameContextKont (KEffAppFun ea env rho k)
| RS_PairParEff1 :
    forall ef1 ea1 ef2 ea2 env rho k,
      ReturnSameContextKont
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)
| RS_PairParEff2 :
    forall ef1 ea1 ef2 ea2 env rho theta1 k,
      ReturnSameContextKont
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)
| RS_PairParFallbackLeft :
    forall ef2 ea2 env rho k,
      ReturnSameContextKont
        (KPairParFallbackLeft ef2 ea2 env rho k)
| RS_PairParFallbackRight :
    forall v_left k,
      ReturnSameContextKont
        (KPairParFallbackRight v_left k)
| RS_Cond :
    forall et ef env rho k,
      ReturnSameContextKont (KCond et ef env rho k)
| RS_Deref :
    forall rgn k,
      ReturnSameContextKont (KDeref rgn k)
| RS_AssignLoc :
    forall rgn ev env rho k,
      ReturnSameContextKont (KAssignLoc rgn ev env rho k)
| RS_PlusL :
    forall e2 env rho k,
      ReturnSameContextKont (KPlusL e2 env rho k)
| RS_PlusR :
    forall n k,
      ReturnSameContextKont (KPlusR n k)
| RS_MinusL :
    forall e2 env rho k,
      ReturnSameContextKont (KMinusL e2 env rho k)
| RS_MinusR :
    forall n k,
      ReturnSameContextKont (KMinusR n k)
| RS_TimesL :
    forall e2 env rho k,
      ReturnSameContextKont (KTimesL e2 env rho k)
| RS_TimesR :
    forall n k,
      ReturnSameContextKont (KTimesR n k)
| RS_EqL :
    forall e2 env rho k,
      ReturnSameContextKont (KEqL e2 env rho k)
| RS_EqR :
    forall n k,
      ReturnSameContextKont (KEqR n k)
| RS_ReadConc :
    forall k,
      ReturnSameContextKont (KReadConc k)
| RS_WriteConc :
    forall k,
      ReturnSameContextKont (KWriteConc k)
| RS_ConcatL :
    forall e2 env rho k,
      ReturnSameContextKont (KConcatL e2 env rho k)
| RS_ConcatR :
    forall theta k,
      ReturnSameContextKont (KConcatR theta k)
| RS_Done :
    ReturnSameContextKont KDone.

Lemma Steps_heap_neutral_resolved_state_preservation_from_step :
  forall
    (step_preserve :
      forall state label state' ty,
        Step state label state' ->
        HeapNeutralTrace (label_trace label) ->
        ResolvedStateShape state ty ->
        ResolvedStateShape state' ty)
    state phi state' ty,
    Steps state phi state' ->
    HeapNeutralTrace phi ->
    ResolvedStateShape state ty ->
    ResolvedStateShape state' ty.
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

Lemma StepsN_heap_neutral_resolved_state_preservation_from_step :
  forall
    (step_preserve :
      forall state label state' ty,
        Step state label state' ->
        HeapNeutralTrace (label_trace label) ->
        ResolvedStateShape state ty ->
        ResolvedStateShape state' ty)
    n state phi state' ty,
    StepsN n state phi state' ->
    HeapNeutralTrace phi ->
    ResolvedStateShape state ty ->
    ResolvedStateShape state' ty.
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

Lemma ResolvedStateShape_aligned :
  forall state ty,
    ResolvedStateShape state ty ->
    StateHeapsAligned state.
Proof.
  intros state ty HState.
  induction HState; simpl; try exact I.
  repeat split; assumption || congruence.
Qed.

Theorem Step_eval_preservation :
  forall gamma omega heap env rho e k label state',
    WTState gamma omega (StEval heap env rho e k) ->
    Step (StEval heap env rho e k) label state' ->
    WTState gamma omega state'.
Proof.
  intros gamma omega heap env rho e k label state' HWT HStep.
  inversion HWT as
    [gamma0 omega0 heap0 env0 rho0 e0 k0 ty eff
      HHeap HEnv HRho HTc HK
    | | | |];
    subst; clear HWT.
  inversion HStep; subst; clear HStep.
  - inversion HTc; subst.
    eapply WT_Return; eauto using VT_Nat.
  - inversion HTc; subst.
    eapply WT_Return; eauto using VT_Bool.
  - inversion HTc; subst.
    match goal with
    | HBind : ctx_binds x _ gamma |- _ =>
        destruct
          (EnvHasType_lookup rho heap env gamma x ty HEnv HBind)
          as (v_typed & HLookup & HV)
    end.
    match goal with
    | HRuntime : env_lookup x env = Some v |- _ =>
        rewrite HRuntime in HLookup
    end.
    inversion HLookup; subst.
    eapply WT_Return; eauto.
  - inversion HTc; subst.
    eapply WT_Return; eauto.
    eapply VT_Closure; eauto.
  - inversion HTc; subst.
    eapply WT_Return; eauto.
    eapply VT_RegionClosure; eauto.
  - inversion HTc; subst.
    eapply WT_Eval; eauto.
    eapply KT_MuAppFun; eauto.
  - inversion HTc; subst.
    eapply WT_Eval; eauto.
    eapply KT_EffAppFun; eauto.
  - inversion HTc; subst.
    eapply WT_Eval; eauto.
    eapply KT_PairParEff1; eauto.
  - inversion HTc; subst.
    eapply WT_Eval; eauto.
    eapply KT_RgnApp; eauto.
  - inversion HTc; subst.
    eapply WT_Return; eauto using VT_Summary.
  - inversion HTc; subst.
    eapply WT_Return; eauto using VT_Summary.
  - inversion HTc; subst.
    eapply WT_Eval; eauto.
    eapply KT_Cond; eauto.
  - inversion HTc; subst.
    eapply WT_Eval; eauto.
    eapply KT_Ref; eauto.
  - inversion HTc; subst.
    eapply WT_Eval; eauto.
    eapply KT_Deref; eauto.
  - inversion HTc; subst.
    eapply WT_Eval; eauto.
    eapply KT_AssignLoc; eauto.
  - inversion HTc; subst.
    eapply WT_Eval; eauto.
    eapply KT_PlusL; eauto.
  - inversion HTc; subst.
    eapply WT_Eval; eauto.
    eapply KT_MinusL; eauto.
  - inversion HTc; subst.
    eapply WT_Eval; eauto.
    eapply KT_TimesL; eauto.
  - inversion HTc; subst.
    eapply WT_Eval; eauto.
    eapply KT_EqL; eauto.
  - inversion HTc; subst.
    eapply WT_Return; eauto using VT_Summary.
  - inversion HTc; subst.
    eapply WT_Return; eauto using VT_Summary.
  - inversion HTc; subst.
    eapply WT_Return; eauto using VT_Summary.
  - inversion HTc; subst.
    eapply WT_Eval; eauto.
    eapply KT_ReadConc; eauto.
  - inversion HTc; subst.
    eapply WT_Eval; eauto.
    eapply KT_WriteConc; eauto.
  - inversion HTc; subst.
    eapply WT_Eval; eauto.
    eapply KT_ConcatL; eauto.
Qed.

Theorem Step_return_same_context_preservation :
  forall gamma omega heap v k label state',
    ReturnSameContextKont k ->
    WTState gamma omega (StReturn heap v k) ->
    Step (StReturn heap v k) label state' ->
    WTState gamma omega state'.
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
    eapply WT_Eval; eauto.
    eapply KT_MuAppArg; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    inversion HV; subst.
    eapply WT_Eval; eauto.
    eapply KT_EffAppArg; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    inversion HV; subst.
    eapply WT_Eval; eauto.
    eapply KT_PairParEff2; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_PairParRun with (heap := heap) (rho := rho).
    + reflexivity.
    + reflexivity.
    + eapply WT_Eval; eauto. constructor.
    + eapply WT_Eval; eauto. constructor.
    + exact HHeap.
    + exact HRho.
    + eassumption.
  - inversion HSame; subst.
    inversion HK; subst.
    inversion HV; subst.
    eapply WT_Eval; eauto.
    eapply KT_PairParFallbackLeft; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_Eval; eauto.
    eapply KT_PairParFallbackRight; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_Return; eauto.
    eapply VT_Pair; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_Eval; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_Eval; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    match goal with
    | HVLoc : ValHasType ?rho ?heap0 (VLoc ?r ?l) (TyRef ?rgn ?ty),
      HLookup : heap_lookup ?r ?l ?heap0 = Some ?v_lookup |- _ =>
        destruct
          (ValHasType_ref_lookup rho heap0 r l rgn ty HVLoc)
          as (cell & HLookupTy & HCellTy);
        rewrite HLookup in HLookupTy
    end.
    inversion HLookupTy; subst.
    eapply WT_Return; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_Eval; eauto.
    eapply KT_AssignVal; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_Eval; eauto.
    eapply KT_PlusR; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_Return; eauto using VT_Nat.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_Eval; eauto.
    eapply KT_MinusR; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_Return; eauto using VT_Nat.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_Eval; eauto.
    eapply KT_TimesR; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_Return; eauto using VT_Nat.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_Eval; eauto.
    eapply KT_EqR; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_Return; eauto using VT_Bool.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_Return; eauto using VT_Summary.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_Return; eauto using VT_Summary.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_Eval; eauto.
    eapply KT_ConcatR; eauto.
  - inversion HSame; subst.
    inversion HK; subst.
    eapply WT_Return; eauto using VT_Summary.
  - inversion HSame; subst.
    eapply WT_Done; eauto.
Qed.

Lemma ResolvedStateShape_const_preservation :
  forall heap env rho n k ty_out,
    ResolvedStateShape (StEval heap env rho (EConst n) k) ty_out ->
    ResolvedStateShape (StReturn heap (VNat n) k) ty_out.
Proof.
  intros heap env rho n k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | | | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply RSS_Return; eauto using RVS_Nat.
Qed.

Lemma ResolvedStateShape_bool_preservation :
  forall heap env rho b k ty_out,
    ResolvedStateShape (StEval heap env rho (EBool b) k) ty_out ->
    ResolvedStateShape (StReturn heap (VBool b) k) ty_out.
Proof.
  intros heap env rho b k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | | | |];
    subst; clear HState.
  inversion HTc; subst.
  inversion HResolve; subst.
  eapply RSS_Return; eauto using RVS_Bool.
Qed.

Lemma ResolvedStateShape_var_preservation :
  forall heap env rho x v k ty_out,
    env_lookup x env = Some v ->
    ResolvedStateShape (StEval heap env rho (EVar x) k) ty_out ->
    ResolvedStateShape (StReturn heap v k) ty_out.
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
        (ResolvedEnvShape_lookup
          rho heap env gamma x ty ty_res HEnv HBind HResolve)
        as (v_typed & HLookupTyped & HV)
  end.
  rewrite HLookup in HLookupTyped.
  inversion HLookupTyped; subst.
  eapply RSS_Return; eauto.
Qed.

Lemma ResolvedStateShape_mu_preservation :
  forall heap env rho f x ec ee k ty_out,
    ResolvedStateShape (StEval heap env rho (EMu f x ec ee) k) ty_out ->
    ResolvedStateShape
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
  eapply RSS_Return; eauto.
  eapply RVS_Closure with
    (gamma := gamma) (omega := omega)
    (ty_arg := ty_arg) (ty_body := ty_body); eauto.
Qed.

Lemma ResolvedStateShape_lambda_rgn_preservation :
  forall heap env rho x e k ty_out,
    ResolvedStateShape
      (StEval heap env rho (ELambdaRgn x e) k)
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_Return; eauto.
  eapply RVS_RegionClosure with
    (gamma := gamma) (omega := omega); eauto.
Qed.

Lemma ResolvedStateShape_empty_preservation :
  forall heap env rho k ty_out,
    ResolvedStateShape (StEval heap env rho EEmpty k) ty_out ->
    ResolvedStateShape
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
  eapply RSS_Return; eauto using RVS_Summary.
Qed.

Lemma ResolvedStateShape_top_preservation :
  forall heap env rho k ty_out,
    ResolvedStateShape (StEval heap env rho ETop k) ty_out ->
    ResolvedStateShape
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
  eapply RSS_Return; eauto using RVS_Summary.
Qed.

Lemma ResolvedStateShape_cond_eval_preservation :
  forall heap env rho e et ef k ty_out,
    ResolvedStateShape
      (StEval heap env rho (ECond e et ef) k)
      ty_out ->
    ResolvedStateShape
      (StEval heap env rho e (KCond et ef env rho k))
      ty_out.
Proof.
  intros heap env rho e et ef k ty_out HState.
  inversion HState as
    [heap0 env0 rho0 e0 k0 gamma omega ty ty_res eff ty_out0
      HHeap HEnv HRho HResolve HTc HK | | | |];
    subst; clear HState.
  inversion HTc; subst.
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyBool) (ty_res := TyBool) (eff := eff_e);
    eauto using Resolve_Bool.
  eapply RKS_Cond with
    (gamma := gamma) (omega := omega)
    (ty := ty) (ty_res := ty_res)
    (eff_t := eff_t) (eff_f := eff_f); eauto.
Qed.

Lemma ResolvedStateShape_ref_eval_preservation :
  forall heap env rho r e r_val k ty_out,
    eval_region rho r = Some r_val ->
    ResolvedStateShape
      (StEval heap env rho (ERef r e) k)
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty0) (ty_res := ty') (eff := eff0);
    eauto.
  eapply RKS_Ref; eauto.
Qed.

Lemma ResolvedStateShape_deref_eval_preservation :
  forall heap env rho r e k ty_out,
    ResolvedStateShape
      (StEval heap env rho (EDeref r e) k)
      ty_out ->
    ResolvedStateShape
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
      destruct (RhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyRef (region_expr_to_type r) ty)
    (ty_res := TyRef (region_const_type r_val) ty_res)
    (eff := eff0); eauto.
  - eapply Resolve_Ref; eauto.
    eapply ResolveRegionType_region_expr_to_type.
    exact HRgn.
  - eapply RKS_Deref; eauto.
Qed.

Lemma ResolvedStateShape_assign_eval_preservation_wf :
  forall heap env rho r ea ev k ty_out,
    (forall gamma omega rgn ty eff,
      TcExp gamma omega ea (TyRef rgn ty) eff ->
      RegionTypeWF omega rgn /\ TyWF omega ty) ->
    ResolvedStateShape
      (StEval heap env rho (EAssign r ea ev) k)
      ty_out ->
    ResolvedStateShape
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
      TcExp gamma omega ea (TyRef (region_expr_to_type r) ?ty_cell)
        ?eff_a,
    HVal : TcExp gamma omega ev ?ty_cell ?eff_v,
    HWF : region_expr_wf omega r |- _ =>
      destruct
        (HRefWF
          gamma omega (region_expr_to_type r) ty_cell eff_a HAddr)
        as (_ & HTyWF);
      destruct (RhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn);
      destruct (ResolveTy_exists 0 omega rho ty_cell HRho HTyWF)
        as (ty_cell_res & HTyResolve);
      eapply RSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyRef (region_expr_to_type r) ty_cell)
        (ty_res := TyRef (region_const_type r_val) ty_cell_res)
        (eff := eff_a);
        eauto;
      [ eapply Resolve_Ref; eauto;
        eapply ResolveRegionType_region_expr_to_type;
        exact HRgn
      | eapply RKS_AssignLoc with
          (gamma := gamma) (omega := omega)
          (ty := ty_cell) (ty_res := ty_cell_res)
          (eff_v := eff_v);
        eauto ]
  end.
Qed.

Lemma ResolvedStateShape_rgn_app_eval_preservation_resolved :
  forall heap env rho er r k gamma omega eff_body ty eff_f
    eff_body_res ty_body_res r_val ty_out,
    ResolvedHeapShape heap ->
    ResolvedEnvShape rho heap env gamma ->
    RhoModels omega rho ->
    eval_region rho r = Some r_val ->
    ResolveStaticEffect rho eff_body eff_body_res ->
    ResolveTy rho ty ty_body_res ->
    TcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
    ResolvedKontShape heap k
      (open_ty_type (region_const_type r_val) ty_body_res)
      ty_out ->
    ResolvedStateShape
      (StEval heap env rho er (KRgnApp r rho k))
      ty_out.
Proof.
  intros heap env rho er r k gamma omega eff_body ty eff_f
    eff_body_res ty_body_res r_val ty_out
    HHeap HEnv HRho HRgn HEffResolve HTyResolve HTyped HK.
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyForallRgn eff_body ty)
    (ty_res := TyForallRgn eff_body_res ty_body_res)
    (eff := eff_f);
    eauto.
  - eapply Resolve_ForallRgn; eauto.
  - eapply RKS_RgnApp; eauto.
Qed.

Lemma ResolvedStateShape_rgn_app_eval_preservation_wf :
  forall heap env rho er r k ty_out,
    (forall gamma omega eff_body ty eff_f,
      TcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
      StaticEffectWFAt 1 omega eff_body /\
      TyWFAt 1 omega ty) ->
    ResolvedStateShape
      (StEval heap env rho (ERgnApp er r) k)
      ty_out ->
    ResolvedStateShape
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
      destruct (RhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  match goal with
  | HTypedFun :
      TcExp gamma omega er (TyForallRgn ?eff_body ?ty_body) ?eff_f
      |- _ =>
      destruct (HForallWF gamma omega eff_body ty_body eff_f HTypedFun)
        as (HEffWF & HTyWF);
      destruct
        (ResolveStaticEffect_exists
          1 omega rho eff_body HRho HEffWF)
        as (eff_body_res & HEffResolve);
      destruct
        (ResolveTy_exists
          1 omega rho ty_body HRho HTyWF)
        as (ty_body_res & HTyResolve);
      pose proof
        (ResolveTy_open_ty
          rho r ty_body ty_body_res r_val HRgn HTyResolve)
        as HOpenResolve;
      pose proof
        (ResolveTy_deterministic
          rho (open_ty r ty_body) ty_res
          (open_ty_type (region_const_type r_val) ty_body_res)
          HResolve HOpenResolve)
        as HTyResEq;
      subst ty_res;
      exact
        (ResolvedStateShape_rgn_app_eval_preservation_resolved
          heap env rho er r k gamma omega eff_body ty_body eff_f
          eff_body_res ty_body_res r_val ty_out
          HHeap HEnv HRho HRgn HEffResolve HTyResolve HTypedFun HK)
  end.
Qed.

Lemma ResolvedStateShape_rgn_app_return_preservation_wf :
  forall heap closure_env closure_rho x e arg_rho r r_val k ty_out,
    eval_region arg_rho r = Some r_val ->
    (forall gamma omega ty eff,
      TcExp gamma (x :: omega) e ty eff ->
      ~ In x omega /\ CtxWF omega gamma /\
      TyWFAt 0 (x :: omega) ty) ->
    ResolvedStateShape
      (StReturn heap
        (VRegionClosure closure_env closure_rho x e)
        (KRgnApp r arg_rho k))
      ty_out ->
    ResolvedStateShape
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
  inversion HK; subst; clear HK.
  match goal with
  | HRgnKont : eval_region arg_rho r = Some ?r_val0 |- _ =>
      rewrite HRgn in HRgnKont;
      inversion HRgnKont;
      subst r_val0;
      clear HRgnKont
  end.
  destruct (HBodyWF gamma omega ty eff HTyped)
    as (HFresh & HCtxWF & HTyWF).
  eapply RSS_Eval with
    (gamma := gamma) (omega := x :: omega)
    (ty := ty)
    (ty_res := open_ty_type (region_const_type r_val) ty_res)
    (eff := eff);
    eauto.
  - eapply ResolvedEnvShape_extend_fresh; eauto.
  - eapply RhoModels_extend; eauto.
  - eapply ResolveTy_rho_extend_close_ty; eauto.
Qed.

Lemma ResolvedStateShape_plus_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    ResolvedStateShape
      (StEval heap env rho (EPlus e1 e2) k)
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff1);
    eauto using Resolve_Nat.
  eapply RKS_PlusL; eauto.
Qed.

Lemma ResolvedStateShape_minus_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    ResolvedStateShape
      (StEval heap env rho (EMinus e1 e2) k)
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff1);
    eauto using Resolve_Nat.
  eapply RKS_MinusL; eauto.
Qed.

Lemma ResolvedStateShape_times_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    ResolvedStateShape
      (StEval heap env rho (ETimes e1 e2) k)
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff1);
    eauto using Resolve_Nat.
  eapply RKS_TimesL; eauto.
Qed.

Lemma ResolvedStateShape_eq_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    ResolvedStateShape
      (StEval heap env rho (EEq e1 e2) k)
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff1);
    eauto using Resolve_Nat.
  eapply RKS_EqL; eauto.
Qed.

Lemma ResolvedStateShape_alloc_abs_preservation :
  forall heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    ResolvedStateShape
      (StEval heap env rho (EAllocAbs r) k)
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_Return; eauto using RVS_Summary.
Qed.

Lemma ResolvedStateShape_read_abs_preservation :
  forall heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    ResolvedStateShape
      (StEval heap env rho (EReadAbs r) k)
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_Return; eauto using RVS_Summary.
Qed.

Lemma ResolvedStateShape_write_abs_preservation :
  forall heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    ResolvedStateShape
      (StEval heap env rho (EWriteAbs r) k)
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_Return; eauto using RVS_Summary.
Qed.

Lemma ResolvedStateShape_concat_eval_preservation :
  forall heap env rho e1 e2 k ty_out,
    ResolvedStateShape
      (StEval heap env rho (EConcat e1 e2) k)
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff1);
    eauto using Resolve_Effect.
  eapply RKS_ConcatL; eauto.
Qed.

Lemma ResolvedStateShape_mu_app_eval_preservation_wf :
  forall heap env rho ef ea k ty_out,
    (forall gamma omega ty_arg eff_body ty_body eff_summary eff_f,
      TcExp gamma omega ef
        (TyArrow ty_arg eff_body ty_body eff_summary) eff_f ->
      TyWF omega ty_arg /\
      StaticEffectWF omega eff_body /\
      TyWF omega ty_body /\
      StaticEffectWF omega eff_summary) ->
    ResolvedStateShape
      (StEval heap env rho (EMuApp ef ea) k)
      ty_out ->
    ResolvedStateShape
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
      TcExp gamma omega ef
        (TyArrow ?ty_arg0 ?eff_body0 ?ty_body0 ?eff_summary0)
        ?eff_f0,
    HArgTyped : TcExp gamma omega ea ?ty_arg0 ?eff_a0 |- _ =>
      destruct
        (HArrowWF
          gamma omega ty_arg0 eff_body0 ty_body0 eff_summary0
          eff_f0 HTypedFun)
        as (HArgWF & HBodyEffWF & HBodyWF & HSummaryEffWF);
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
      pose proof
        (ResolveTy_deterministic
          rho ty_body0 ty_res ty_body_res HResolve HBodyResolve)
        as HBodyEq;
      subst ty_body_res;
      eapply RSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyArrow ty_arg0 eff_body0 ty_body0 eff_summary0)
        (ty_res := TyArrow
          ty_arg_res eff_body_res ty_res eff_summary_res)
        (eff := eff_f0);
        eauto;
      [ eapply Resolve_Arrow; eauto
      | eapply RKS_MuAppFun with
          (gamma := gamma) (omega := omega)
          (ty_arg := ty_arg0) (ty_body := ty_body0)
          (eff_body := eff_body0) (eff_summary := eff_summary0)
          (eff_arg := eff_a0);
        eauto ]
  end.
Qed.

Lemma ResolvedStateShape_eff_app_eval_preservation_wf :
  forall heap env rho ef ea k ty_out,
    (forall gamma omega ty_arg eff_body ty_body eff_summary eff_f,
      TcExp gamma omega ef
        (TyArrow ty_arg eff_body ty_body eff_summary) eff_f ->
      TyWF omega ty_arg /\
      StaticEffectWF omega eff_body /\
      TyWF omega ty_body /\
      StaticEffectWF omega eff_summary) ->
    ResolvedStateShape
      (StEval heap env rho (EEffApp ef ea) k)
      ty_out ->
    ResolvedStateShape
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
      TcExp gamma omega ef
        (TyArrow ?ty_arg0 ?eff_body0 ?ty_body0 ?eff_summary0)
        ?eff_f0,
    HArgTyped : TcExp gamma omega ea ?ty_arg0 ?eff_a0 |- _ =>
      destruct
        (HArrowWF
          gamma omega ty_arg0 eff_body0 ty_body0 eff_summary0
          eff_f0 HTypedFun)
        as (HArgWF & HBodyEffWF & HBodyWF & HSummaryEffWF);
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
      eapply RSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyArrow ty_arg0 eff_body0 ty_body0 eff_summary0)
        (ty_res := TyArrow
          ty_arg_res eff_body_res ty_body_res eff_summary_res)
        (eff := eff_f0);
        eauto;
      [ eapply Resolve_Arrow; eauto
      | eapply RKS_EffAppFun with
          (gamma := gamma) (omega := omega)
          (ty_arg := ty_arg0) (ty_body := ty_body0)
          (eff_body := eff_body0) (eff_summary := eff_summary0)
          (eff_arg := eff_a0);
        eauto ]
  end.
Qed.

Lemma ResolvedStateShape_mu_app_eval_arg_preservation :
  forall heap env rho ea k closure_env closure_rho f x ec ee ty_out,
    ResolvedStateShape
      (StReturn heap
        (VClosure closure_env closure_rho f x ec ee)
        (KMuAppFun ea env rho k))
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty_arg) (ty_res := ty_arg_res) (eff := eff_arg);
    eauto.
  eapply RKS_MuAppArg with
    (gamma := gamma0) (omega := omega0)
    (ty_arg := ty_arg0) (ty_body := ty_body0)
    (eff_body := eff_body0) (eff_summary := eff_summary0);
    eauto.
Qed.

Lemma ResolvedStateShape_mu_app_body_preservation :
  forall heap v_arg closure_env closure_rho f x ec ee k ty_out,
    ResolvedStateShape
      (StReturn heap v_arg
        (KMuAppArg closure_env closure_rho f x ec ee k))
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_Eval; eauto.
  econstructor; eauto.
  eapply RES_EnvCons with
    (ty_res := TyArrow ty eff_body_res ty_body_res eff_summary_res).
  - eapply Resolve_Arrow; eauto.
  - eapply RVS_Closure with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body); eauto.
  - assumption.
Qed.

Lemma ResolvedStateShape_eff_app_eval_arg_preservation :
  forall heap env rho ea k closure_env closure_rho f x ec ee ty_out,
    ResolvedStateShape
      (StReturn heap
        (VClosure closure_env closure_rho f x ec ee)
        (KEffAppFun ea env rho k))
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty_arg) (ty_res := ty_arg_res) (eff := eff_arg);
    eauto.
  eapply RKS_EffAppArg with
    (gamma := gamma0) (omega := omega0)
    (ty_arg := ty_arg0) (ty_body := ty_body0)
    (eff_body := eff_body0) (eff_summary := eff_summary0);
    eauto.
Qed.

Lemma ResolvedStateShape_eff_app_body_preservation :
  forall heap v_arg closure_env closure_rho f x ec ee k ty_out,
    ResolvedStateShape
      (StReturn heap v_arg
        (KEffAppArg closure_env closure_rho f x ec ee k))
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_Eval with
    (gamma :=
      (x, ty_arg) ::
      (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
    (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary);
    eauto using Resolve_Effect.
  econstructor; eauto.
  eapply RES_EnvCons with
    (ty_res := TyArrow ty eff_body_res ty_body_res eff_summary_res).
  - eapply Resolve_Arrow; eauto.
  - eapply RVS_Closure with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body); eauto.
  - assumption.
Qed.

Lemma ResolvedStateShape_pair_par_eval_preservation :
  forall heap env rho ef1 ea1 ef2 ea2 k ty_out,
    ResolvedStateShape
      (StEval heap env rho
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)) k)
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary1);
    eauto using Resolve_Effect.
  eapply RKS_PairParEff1 with
    (gamma := gamma) (omega := omega)
    (ty1 := ty1) (ty2 := ty2)
    (eff1 := eff1) (eff2 := eff2)
    (eff_summary2 := eff_summary2);
    eauto.
Qed.

Lemma ResolvedStateShape_pair_par_eff1_preservation :
  forall heap theta1 ef1 ea1 ef2 ea2 env rho k ty_out,
    ResolvedStateShape
      (StReturn heap (VSummary theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff_summary2);
    eauto using Resolve_Effect.
  eapply RKS_PairParEff2 with
    (gamma := gamma) (omega := omega)
    (ty1 := ty1) (ty2 := ty2)
    (eff1 := eff1) (eff2 := eff2);
    eauto.
Qed.

Lemma ResolvedStateShape_pair_par_check_pass_preservation :
  forall heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out,
    ResolvedStateShape
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_PairParRun with
    (heap := heap) (ty1 := ty1_res) (ty2 := ty2_res);
    simpl; eauto.
  - eapply RSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty1) (ty_res := ty1_res) (eff := eff1);
      eauto.
    constructor.
  - eapply RSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty2) (ty_res := ty2_res) (eff := eff2);
      eauto.
    constructor.
Qed.

Lemma ResolvedStateShape_pair_par_check_fallback_preservation :
  forall heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out,
    ResolvedStateShape
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty1) (ty_res := ty1_res) (eff := eff1);
    eauto.
  eapply RKS_PairParFallbackLeft with
    (gamma := gamma) (omega := omega)
    (ty2 := ty2) (ty2_res := ty2_res) (eff2 := eff2);
    eauto.
Qed.

Lemma ResolvedStateShape_pair_par_fallback_left_return_preservation :
  forall heap v_left ef2 ea2 env rho k ty_out,
    ResolvedStateShape
      (StReturn heap v_left
        (KPairParFallbackLeft ef2 ea2 env rho k))
      ty_out ->
    ResolvedStateShape
      (StEval heap env rho (EMuApp ef2 ea2)
        (KPairParFallbackRight v_left k))
      ty_out.
Proof.
  intros heap v_left ef2 ea2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty2) (ty_res := ty2_res) (eff := eff2);
    eauto.
  eapply RKS_PairParFallbackRight; eauto.
Qed.

Lemma ResolvedStateShape_pair_par_fallback_right_return_preservation :
  forall heap v_left v_right k ty_out,
    ResolvedStateShape
      (StReturn heap v_right (KPairParFallbackRight v_left k))
      ty_out ->
    ResolvedStateShape
      (StReturn heap (VPair v_left v_right) k)
      ty_out.
Proof.
  intros heap v_left v_right k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply RSS_Return; eauto.
  eapply RVS_Pair; eauto.
Qed.

Lemma ResolvedStateShape_pair_par_done_pass_preservation :
  forall heap v1 v2 phi_left phi_right k ty_out,
    ResolvedStateShape
      (StPairParRun
        (StDone heap v1)
        (StDone heap v2)
        phi_left phi_right k)
      ty_out ->
    ResolvedStateShape (StReturn heap (VPair v1 v2) k) ty_out.
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
  eapply RSS_Return; eauto.
  eapply RVS_Pair; eauto.
Qed.

Lemma ResolvedStateShape_pair_par_done_fail_preservation :
  forall heap v1 v2 phi_left phi_right k ty_out,
    ResolvedStateShape
      (StPairParRun
        (StDone heap v1)
        (StDone heap v2)
        phi_left phi_right k)
      ty_out ->
    ResolvedStateShape (StError heap) ty_out.
Proof.
  intros heap v1 v2 phi_left phi_right k ty_out HState.
  inversion HState as
    [| | | |
      left_state right_state phi_left0 phi_right0 k0 heap0
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    subst; clear HState; simpl in *; subst.
  inversion HLeft; subst.
  eapply RSS_Error; eauto.
Qed.

Lemma ResolvedStateShape_pair_par_run_left_preservation :
  forall left_state right_state phi_left phi_right k
    label left_state' ty_out,
    Step left_state label left_state' ->
    StateHeapsAligned
      (StPairParRun left_state right_state phi_left phi_right k) ->
    HeapNeutralTrace (label_trace label) ->
    (forall ty,
      ResolvedStateShape left_state ty ->
      ResolvedStateShape left_state' ty) ->
    ResolvedStateShape
      (StPairParRun left_state right_state phi_left phi_right k)
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_PairParRun with (ty1 := ty1) (ty2 := ty2); eauto.
Qed.

Lemma ResolvedStateShape_pair_par_run_left_preservation_from_child :
  forall left_state right_state phi_left phi_right k
    label left_state' ty_out,
    Step left_state label left_state' ->
    HeapNeutralTrace (label_trace label) ->
    (forall ty,
      ResolvedStateShape left_state ty ->
      ResolvedStateShape left_state' ty) ->
    ResolvedStateShape
      (StPairParRun left_state right_state phi_left phi_right k)
      ty_out ->
    ResolvedStateShape
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
  eapply ResolvedStateShape_pair_par_run_left_preservation; eauto.
  eapply ResolvedStateShape_aligned; eauto.
Qed.

Lemma ResolvedStateShape_pair_par_run_right_preservation :
  forall heap v1 right_state phi_left phi_right k
    label right_state' ty_out,
    Step right_state label right_state' ->
    StateHeapsAligned
      (StPairParRun (StDone heap v1) right_state phi_left phi_right k) ->
    HeapNeutralTrace (label_trace label) ->
    (forall ty,
      ResolvedStateShape right_state ty ->
      ResolvedStateShape right_state' ty) ->
    ResolvedStateShape
      (StPairParRun (StDone heap v1) right_state phi_left phi_right k)
      ty_out ->
    ResolvedStateShape
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
  eapply RSS_PairParRun with
    (heap := heap) (ty1 := ty1) (ty2 := ty2); eauto.
Qed.

Lemma ResolvedStateShape_pair_par_run_right_preservation_from_child :
  forall heap v1 right_state phi_left phi_right k
    label right_state' ty_out,
    Step right_state label right_state' ->
    HeapNeutralTrace (label_trace label) ->
    (forall ty,
      ResolvedStateShape right_state ty ->
      ResolvedStateShape right_state' ty) ->
    ResolvedStateShape
      (StPairParRun (StDone heap v1) right_state phi_left phi_right k)
      ty_out ->
    ResolvedStateShape
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
  eapply ResolvedStateShape_pair_par_run_right_preservation; eauto.
  eapply ResolvedStateShape_aligned; eauto.
Qed.

Lemma ResolvedStateShape_pair_par_left_error_preservation :
  forall heap right_state phi_left phi_right k ty_out,
    ResolvedStateShape
      (StPairParRun (StError heap) right_state phi_left phi_right k)
      ty_out ->
    ResolvedStateShape (StError heap) ty_out.
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
  eapply RSS_Error; eauto.
Qed.

Lemma ResolvedStateShape_pair_par_right_error_preservation :
  forall heap_left v1 heap_right phi_left phi_right k ty_out,
    ResolvedStateShape
      (StPairParRun
        (StDone heap_left v1)
        (StError heap_right)
        phi_left phi_right k)
      ty_out ->
    ResolvedStateShape (StError heap_right) ty_out.
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
  eapply RSS_Error; eauto.
Qed.

Lemma ResolvedStateShape_cond_true_preservation :
  forall heap et ef env rho k ty_out,
    ResolvedStateShape
      (StReturn heap (VBool true) (KCond et ef env rho k))
      ty_out ->
    ResolvedStateShape (StEval heap env rho et k) ty_out.
Proof.
  intros heap et ef env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RSS_Eval; eauto.
Qed.

Lemma ResolvedStateShape_cond_false_preservation :
  forall heap et ef env rho k ty_out,
    ResolvedStateShape
      (StReturn heap (VBool false) (KCond et ef env rho k))
      ty_out ->
    ResolvedStateShape (StEval heap env rho ef k) ty_out.
Proof.
  intros heap et ef env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RSS_Eval; eauto.
Qed.

Lemma ResolvedStateShape_deref_preservation :
  forall heap r_static r l v k ty_out,
    heap_lookup r l heap = Some v ->
    ResolvedStateShape
      (StReturn heap (VLoc r l) (KDeref r_static k))
      ty_out ->
    ResolvedStateShape (StReturn heap v k) ty_out.
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
    HCellShape : ResolvedValShape heap ?cell ?ty |- _ =>
      rewrite HLookup' in HCellLookup;
      inversion HCellLookup; subst
  end.
  eapply RSS_Return; eauto.
Qed.

Lemma ResolvedStateShape_assign_loc_preservation :
  forall heap r_static ev env rho r l k ty_out,
    ResolvedStateShape
      (StReturn heap (VLoc r l) (KAssignLoc r_static ev env rho k))
      ty_out ->
    ResolvedStateShape
      (StEval heap env rho ev (KAssignVal r_static (VLoc r l) k))
      ty_out.
Proof.
  intros heap r_static ev env rho r l k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RSS_Eval; eauto.
  eapply RKS_AssignVal; eauto.
Qed.

Lemma ResolvedStateShape_plus_l_preservation :
  forall heap n e2 env rho k ty_out,
    ResolvedStateShape
      (StReturn heap (VNat n) (KPlusL e2 env rho k))
      ty_out ->
    ResolvedStateShape
      (StEval heap env rho e2 (KPlusR n k))
      ty_out.
Proof.
  intros heap n e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using Resolve_Nat.
  eapply RKS_PlusR; eauto.
Qed.

Lemma ResolvedStateShape_plus_r_preservation :
  forall heap n1 n2 k ty_out,
    ResolvedStateShape
      (StReturn heap (VNat n2) (KPlusR n1 k))
      ty_out ->
    ResolvedStateShape
      (StReturn heap (VNat (n1 + n2)) k)
      ty_out.
Proof.
  intros heap n1 n2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RSS_Return; eauto using RVS_Nat.
Qed.

Lemma ResolvedStateShape_minus_l_preservation :
  forall heap n e2 env rho k ty_out,
    ResolvedStateShape
      (StReturn heap (VNat n) (KMinusL e2 env rho k))
      ty_out ->
    ResolvedStateShape
      (StEval heap env rho e2 (KMinusR n k))
      ty_out.
Proof.
  intros heap n e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using Resolve_Nat.
  eapply RKS_MinusR; eauto.
Qed.

Lemma ResolvedStateShape_minus_r_preservation :
  forall heap n1 n2 k ty_out,
    ResolvedStateShape
      (StReturn heap (VNat n2) (KMinusR n1 k))
      ty_out ->
    ResolvedStateShape
      (StReturn heap (VNat (n1 - n2)) k)
      ty_out.
Proof.
  intros heap n1 n2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RSS_Return; eauto using RVS_Nat.
Qed.

Lemma ResolvedStateShape_times_l_preservation :
  forall heap n e2 env rho k ty_out,
    ResolvedStateShape
      (StReturn heap (VNat n) (KTimesL e2 env rho k))
      ty_out ->
    ResolvedStateShape
      (StEval heap env rho e2 (KTimesR n k))
      ty_out.
Proof.
  intros heap n e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using Resolve_Nat.
  eapply RKS_TimesR; eauto.
Qed.

Lemma ResolvedStateShape_times_r_preservation :
  forall heap n1 n2 k ty_out,
    ResolvedStateShape
      (StReturn heap (VNat n2) (KTimesR n1 k))
      ty_out ->
    ResolvedStateShape
      (StReturn heap (VNat (n1 * n2)) k)
      ty_out.
Proof.
  intros heap n1 n2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RSS_Return; eauto using RVS_Nat.
Qed.

Lemma ResolvedStateShape_eq_l_preservation :
  forall heap n e2 env rho k ty_out,
    ResolvedStateShape
      (StReturn heap (VNat n) (KEqL e2 env rho k))
      ty_out ->
    ResolvedStateShape
      (StEval heap env rho e2 (KEqR n k))
      ty_out.
Proof.
  intros heap n e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using Resolve_Nat.
  eapply RKS_EqR; eauto.
Qed.

Lemma ResolvedStateShape_eq_r_preservation :
  forall heap n1 n2 k ty_out,
    ResolvedStateShape
      (StReturn heap (VNat n2) (KEqR n1 k))
      ty_out ->
    ResolvedStateShape
      (StReturn heap (VBool (Nat.eqb n1 n2)) k)
      ty_out.
Proof.
  intros heap n1 n2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RSS_Return; eauto using RVS_Bool.
Qed.

Lemma ResolvedStateShape_read_conc_eval_preservation_wf :
  forall heap env rho e k ty_out,
    (forall gamma omega rgn ty eff,
      TcExp gamma omega e (TyRef rgn ty) eff ->
      RegionTypeWF omega rgn /\ TyWF omega ty) ->
    ResolvedStateShape
      (StEval heap env rho (EReadConc e) k)
      ty_out ->
    ResolvedStateShape
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
  | HTypedRef : TcExp gamma omega e (TyRef ?rgn ?ty_ref) ?eff_ref
      |- _ =>
      destruct (HRefWF gamma omega rgn ty_ref eff_ref HTypedRef)
        as (HRgnWF & HTyWF);
      destruct
        (ResolveRegionType_exists 0 omega rho rgn HRho HRgnWF)
        as (rgn_res & HRgnResolve);
      destruct (ResolveTy_exists 0 omega rho ty_ref HRho HTyWF)
        as (ty_ref_res & HTyResolve);
      destruct
        (ResolveRegionType_wf0_const
          omega rho rgn rgn_res HRgnWF HRgnResolve)
        as (r_val & HRgnResEq);
      subst rgn_res;
      eapply RSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyRef rgn ty_ref)
        (ty_res := TyRef (region_const_type r_val) ty_ref_res)
        (eff := eff_ref);
        eauto;
      [ eapply Resolve_Ref; eauto
      | eapply RKS_ReadConc; eauto ]
  end.
Qed.

Lemma ResolvedStateShape_write_conc_eval_preservation_wf :
  forall heap env rho e k ty_out,
    (forall gamma omega rgn ty eff,
      TcExp gamma omega e (TyRef rgn ty) eff ->
      RegionTypeWF omega rgn /\ TyWF omega ty) ->
    ResolvedStateShape
      (StEval heap env rho (EWriteConc e) k)
      ty_out ->
    ResolvedStateShape
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
  | HTypedRef : TcExp gamma omega e (TyRef ?rgn ?ty_ref) ?eff_ref
      |- _ =>
      destruct (HRefWF gamma omega rgn ty_ref eff_ref HTypedRef)
        as (HRgnWF & HTyWF);
      destruct
        (ResolveRegionType_exists 0 omega rho rgn HRho HRgnWF)
        as (rgn_res & HRgnResolve);
      destruct (ResolveTy_exists 0 omega rho ty_ref HRho HTyWF)
        as (ty_ref_res & HTyResolve);
      destruct
        (ResolveRegionType_wf0_const
          omega rho rgn rgn_res HRgnWF HRgnResolve)
        as (r_val & HRgnResEq);
      subst rgn_res;
      eapply RSS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyRef rgn ty_ref)
        (ty_res := TyRef (region_const_type r_val) ty_ref_res)
        (eff := eff_ref);
        eauto;
      [ eapply Resolve_Ref; eauto
      | eapply RKS_WriteConc; eauto ]
  end.
Qed.

Lemma ResolvedStateShape_read_conc_preservation :
  forall heap r l k ty_out,
    ResolvedStateShape
      (StReturn heap (VLoc r l) (KReadConc k))
      ty_out ->
    ResolvedStateShape
      (StReturn heap (VSummary (SummarySet [CReadConc r l])) k)
      ty_out.
Proof.
  intros heap r l k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply RSS_Return; eauto using RVS_Summary.
Qed.

Lemma ResolvedStateShape_write_conc_preservation :
  forall heap r l k ty_out,
    ResolvedStateShape
      (StReturn heap (VLoc r l) (KWriteConc k))
      ty_out ->
    ResolvedStateShape
      (StReturn heap (VSummary (SummarySet [CWriteConc r l])) k)
      ty_out.
Proof.
  intros heap r l k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply RSS_Return; eauto using RVS_Summary.
Qed.

Lemma ResolvedStateShape_concat_l_preservation :
  forall heap theta1 e2 env rho k ty_out,
    ResolvedStateShape
      (StReturn heap (VSummary theta1) (KConcatL e2 env rho k))
      ty_out ->
    ResolvedStateShape
      (StEval heap env rho e2 (KConcatR theta1 k))
      ty_out.
Proof.
  intros heap theta1 e2 env rho k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff);
    eauto using Resolve_Effect.
  eapply RKS_ConcatR; eauto.
Qed.

Lemma ResolvedStateShape_concat_r_preservation :
  forall heap theta1 theta2 k ty_out,
    ResolvedStateShape
      (StReturn heap (VSummary theta2) (KConcatR theta1 k))
      ty_out ->
    ResolvedStateShape
      (StReturn heap (VSummary (summary_union theta1 theta2)) k)
      ty_out.
Proof.
  intros heap theta1 theta2 k ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply RSS_Return; eauto using RVS_Summary.
Qed.

Lemma ResolvedStateShape_done_preservation :
  forall heap v ty_out,
    ResolvedStateShape (StReturn heap v KDone) ty_out ->
    ResolvedStateShape (StDone heap v) ty_out.
Proof.
  intros heap v ty_out HState.
  inversion HState as
    [| heap0 v0 k0 ty ty_out0 HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply RSS_Done; eauto.
Qed.

Theorem Step_heap_neutral_resolved_state_preservation_wf :
  forall
    (HArrowWF :
      forall ef gamma omega ty_arg eff_body ty_body eff_summary eff_f,
        TcExp gamma omega ef
          (TyArrow ty_arg eff_body ty_body eff_summary)
          eff_f ->
        TyWF omega ty_arg /\
        StaticEffectWF omega eff_body /\
        TyWF omega ty_body /\
        StaticEffectWF omega eff_summary)
    (HForallWF :
      forall er gamma omega eff_body ty eff_f,
        TcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
        StaticEffectWFAt 1 omega eff_body /\
        TyWFAt 1 omega ty)
    (HRegionBodyWF :
      forall x e gamma omega ty eff,
        TcExp gamma (x :: omega) e ty eff ->
        ~ In x omega /\ CtxWF omega gamma /\
        TyWFAt 0 (x :: omega) ty)
    (HRefWF :
      forall e gamma omega rgn ty eff,
        TcExp gamma omega e (TyRef rgn ty) eff ->
        RegionTypeWF omega rgn /\ TyWF omega ty)
    state label state' ty,
    Step state label state' ->
    HeapNeutralTrace (label_trace label) ->
    ResolvedStateShape state ty ->
    ResolvedStateShape state' ty.
Proof.
  intros HArrowWF HForallWF HRegionBodyWF HRefWF
    state label state' ty HStep.
  revert ty.
  induction HStep; intros ty_out HNeutral HState; simpl in HNeutral.
  - eapply ResolvedStateShape_const_preservation; eauto.
  - eapply ResolvedStateShape_bool_preservation; eauto.
  - eapply ResolvedStateShape_var_preservation; eauto.
  - eapply ResolvedStateShape_mu_preservation; eauto.
  - eapply ResolvedStateShape_lambda_rgn_preservation; eauto.
  - eapply ResolvedStateShape_mu_app_eval_preservation_wf; eauto.
  - eapply ResolvedStateShape_mu_app_eval_arg_preservation; eauto.
  - eapply ResolvedStateShape_mu_app_body_preservation; eauto.
  - eapply ResolvedStateShape_eff_app_eval_preservation_wf; eauto.
  - eapply ResolvedStateShape_eff_app_eval_arg_preservation; eauto.
  - eapply ResolvedStateShape_eff_app_body_preservation; eauto.
  - eapply ResolvedStateShape_pair_par_eval_preservation; eauto.
  - eapply ResolvedStateShape_pair_par_eff1_preservation; eauto.
  - eapply ResolvedStateShape_pair_par_check_pass_preservation; eauto.
  - eapply ResolvedStateShape_pair_par_check_fallback_preservation; eauto.
  - eapply ResolvedStateShape_pair_par_fallback_left_return_preservation;
      eauto.
  - eapply ResolvedStateShape_pair_par_fallback_right_return_preservation;
      eauto.
  - eapply ResolvedStateShape_pair_par_run_left_preservation_from_child;
      eauto.
  - eapply ResolvedStateShape_pair_par_run_right_preservation_from_child;
      eauto.
  - eapply ResolvedStateShape_pair_par_left_error_preservation; eauto.
  - eapply ResolvedStateShape_pair_par_right_error_preservation; eauto.
  - eapply ResolvedStateShape_pair_par_done_pass_preservation; eauto.
  - eapply ResolvedStateShape_pair_par_done_fail_preservation; eauto.
  - eapply ResolvedStateShape_rgn_app_eval_preservation_wf; eauto.
  - eapply ResolvedStateShape_rgn_app_return_preservation_wf; eauto.
  - eapply ResolvedStateShape_empty_preservation; eauto.
  - eapply ResolvedStateShape_top_preservation; eauto.
  - eapply ResolvedStateShape_cond_eval_preservation; eauto.
  - eapply ResolvedStateShape_cond_true_preservation; eauto.
  - eapply ResolvedStateShape_cond_false_preservation; eauto.
  - eapply ResolvedStateShape_ref_eval_preservation; eauto.
  - destruct HNeutral as (HNoAlloc & _).
    exfalso. eapply HNoAlloc.
    simpl. left. reflexivity.
  - eapply ResolvedStateShape_deref_eval_preservation; eauto.
  - eapply ResolvedStateShape_deref_preservation; eauto.
  - eapply ResolvedStateShape_assign_eval_preservation_wf; eauto.
  - eapply ResolvedStateShape_assign_loc_preservation; eauto.
  - destruct HNeutral as (_ & HReadOnly).
    exfalso. eapply HReadOnly.
    simpl. left. reflexivity.
  - eapply ResolvedStateShape_plus_eval_preservation; eauto.
  - eapply ResolvedStateShape_plus_l_preservation; eauto.
  - eapply ResolvedStateShape_plus_r_preservation; eauto.
  - eapply ResolvedStateShape_minus_eval_preservation; eauto.
  - eapply ResolvedStateShape_minus_l_preservation; eauto.
  - eapply ResolvedStateShape_minus_r_preservation; eauto.
  - eapply ResolvedStateShape_times_eval_preservation; eauto.
  - eapply ResolvedStateShape_times_l_preservation; eauto.
  - eapply ResolvedStateShape_times_r_preservation; eauto.
  - eapply ResolvedStateShape_eq_eval_preservation; eauto.
  - eapply ResolvedStateShape_eq_l_preservation; eauto.
  - eapply ResolvedStateShape_eq_r_preservation; eauto.
  - eapply ResolvedStateShape_alloc_abs_preservation; eauto.
  - eapply ResolvedStateShape_read_abs_preservation; eauto.
  - eapply ResolvedStateShape_write_abs_preservation; eauto.
  - eapply ResolvedStateShape_read_conc_eval_preservation_wf; eauto.
  - eapply ResolvedStateShape_read_conc_preservation; eauto.
  - eapply ResolvedStateShape_write_conc_eval_preservation_wf; eauto.
  - eapply ResolvedStateShape_write_conc_preservation; eauto.
  - eapply ResolvedStateShape_concat_eval_preservation; eauto.
  - eapply ResolvedStateShape_concat_l_preservation; eauto.
  - eapply ResolvedStateShape_concat_r_preservation; eauto.
  - eapply ResolvedStateShape_done_preservation; eauto.
Qed.

Theorem Step_heap_neutral_regular_state_to_resolved_preservation :
  forall state label state' ty,
    Step state label state' ->
    HeapNeutralTrace (label_trace label) ->
    RegularResolvedStateShape state ty ->
    ResolvedStateShape state' ty.
Proof.
  intros state label state' ty HStep HNeutral HState.
  eapply RegularResolvedStateShape_to_resolved.
  eapply Step_heap_neutral_regular_state_preservation; eauto.
Qed.

Theorem Steps_heap_neutral_resolved_state_preservation_wf :
  forall
    (HArrowWF :
      forall ef gamma omega ty_arg eff_body ty_body eff_summary eff_f,
        TcExp gamma omega ef
          (TyArrow ty_arg eff_body ty_body eff_summary)
          eff_f ->
        TyWF omega ty_arg /\
        StaticEffectWF omega eff_body /\
        TyWF omega ty_body /\
        StaticEffectWF omega eff_summary)
    (HForallWF :
      forall er gamma omega eff_body ty eff_f,
        TcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
        StaticEffectWFAt 1 omega eff_body /\
        TyWFAt 1 omega ty)
    (HRegionBodyWF :
      forall x e gamma omega ty eff,
        TcExp gamma (x :: omega) e ty eff ->
        ~ In x omega /\ CtxWF omega gamma /\
        TyWFAt 0 (x :: omega) ty)
    (HRefWF :
      forall e gamma omega rgn ty eff,
        TcExp gamma omega e (TyRef rgn ty) eff ->
        RegionTypeWF omega rgn /\ TyWF omega ty)
    state phi state' ty,
    Steps state phi state' ->
    HeapNeutralTrace phi ->
    ResolvedStateShape state ty ->
    ResolvedStateShape state' ty.
Proof.
  intros HArrowWF HForallWF HRegionBodyWF HRefWF
    state phi state' ty HSteps HNeutral HState.
  eapply Steps_heap_neutral_resolved_state_preservation_from_step;
    eauto.
  intros step_state label step_state' step_ty HStep HStepNeutral HStepState.
  eapply Step_heap_neutral_resolved_state_preservation_wf; eauto.
Qed.

Theorem Steps_heap_neutral_regular_state_to_resolved_preservation :
  forall state phi state' ty,
    Steps state phi state' ->
    HeapNeutralTrace phi ->
    RegularResolvedStateShape state ty ->
    ResolvedStateShape state' ty.
Proof.
  intros state phi state' ty HSteps HNeutral HState.
  eapply RegularResolvedStateShape_to_resolved.
  eapply Steps_heap_neutral_regular_state_preservation; eauto.
Qed.

Theorem StepsN_heap_neutral_resolved_state_preservation_wf :
  forall
    (HArrowWF :
      forall ef gamma omega ty_arg eff_body ty_body eff_summary eff_f,
        TcExp gamma omega ef
          (TyArrow ty_arg eff_body ty_body eff_summary)
          eff_f ->
        TyWF omega ty_arg /\
        StaticEffectWF omega eff_body /\
        TyWF omega ty_body /\
        StaticEffectWF omega eff_summary)
    (HForallWF :
      forall er gamma omega eff_body ty eff_f,
        TcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
        StaticEffectWFAt 1 omega eff_body /\
        TyWFAt 1 omega ty)
    (HRegionBodyWF :
      forall x e gamma omega ty eff,
        TcExp gamma (x :: omega) e ty eff ->
        ~ In x omega /\ CtxWF omega gamma /\
        TyWFAt 0 (x :: omega) ty)
    (HRefWF :
      forall e gamma omega rgn ty eff,
        TcExp gamma omega e (TyRef rgn ty) eff ->
        RegionTypeWF omega rgn /\ TyWF omega ty)
    n state phi state' ty,
    StepsN n state phi state' ->
    HeapNeutralTrace phi ->
    ResolvedStateShape state ty ->
    ResolvedStateShape state' ty.
Proof.
  intros HArrowWF HForallWF HRegionBodyWF HRefWF
    n state phi state' ty HSteps HNeutral HState.
  eapply StepsN_heap_neutral_resolved_state_preservation_from_step;
    eauto.
  intros step_state label step_state' step_ty HStep HStepNeutral HStepState.
  eapply Step_heap_neutral_resolved_state_preservation_wf; eauto.
Qed.

Theorem StepsN_heap_neutral_regular_state_to_resolved_preservation :
  forall n state phi state' ty,
    StepsN n state phi state' ->
    HeapNeutralTrace phi ->
    RegularResolvedStateShape state ty ->
    ResolvedStateShape state' ty.
Proof.
  intros n state phi state' ty HSteps HNeutral HState.
  eapply RegularResolvedStateShape_to_resolved.
  eapply StepsN_heap_neutral_regular_state_preservation; eauto.
Qed.
