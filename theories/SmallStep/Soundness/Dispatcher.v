From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Wf_nat.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Core.Values.
Require Import theories.SmallStep.Determinism.Terminal.
Require Import theories.SmallStep.Runtime.Continuation.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Runtime.RegularStateShape.
Require Import theories.SmallStep.Runtime.Trace.
Require Import theories.SmallStep.Runtime.Typing.
Require Import theories.SmallStep.Soundness.App.
Require Import theories.SmallStep.Soundness.Arithmetic.
Require Import theories.SmallStep.Soundness.BackTriangle.
Require Import theories.SmallStep.Soundness.Control.
Require Import theories.SmallStep.Soundness.Correctness.
Require Import theories.SmallStep.Soundness.PairPar.
Require Import theories.SmallStep.Soundness.References.
Require Import theories.SmallStep.Soundness.StaticEffect.
Require Import theories.SmallStep.Soundness.Summary.
Require Import theories.SmallStep.Typing.Regularity.
Require Import theories.SmallStep.Typing.Judgments.
Require Import theories.SmallStep.Typing.Resolve.
Require Import theories.SmallStep.Typing.Types.

Import ListNotations.

Lemma counted_immediate_silent_initial_return_trace_nil :
  forall n heap env rho expr phi heap_final v_final,
    (forall label state',
      NStep (NInitialState heap env rho expr) label state' ->
      exists v0,
        label = LSilent /\
        state' = StReturn heap v0 KDone) ->
    CountedComputationEvaluation n heap env rho expr
      phi heap_final v_final ->
    phi = [].
Proof.
  intros n heap env rho expr phi heap_final v_final HImmediate HComp.
  unfold CountedComputationEvaluation in HComp.
  inversion HComp; subst; try reflexivity.
  match goal with
  | HStep : NStep (NInitialState heap env rho expr) ?label ?state',
    HTail : NStepsN _ ?state' ?phi_tail
      (StDone heap_final v_final) |- _ =>
      destruct (HImmediate label state' HStep)
        as (v0 & HLabel & HState);
      subst label state';
      destruct
        (NSteps_return_done_inv
          heap v0 phi_tail heap_final v_final
          (NStepsN_to_NSteps
            _ _ _ _ HTail))
        as (_HHeap & _HVal & HTraceTail);
      subst phi_tail
  end.
  reflexivity.
Qed.

Lemma counted_immediate_silent_initial_return_covered :
  forall n heap env rho expr phi heap_final v_final theta,
    (forall label state',
      NStep (NInitialState heap env rho expr) label state' ->
      exists v0,
        label = LSilent /\
        state' = StReturn heap v0 KDone) ->
    CountedComputationEvaluation n heap env rho expr
      phi heap_final v_final ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n heap env rho expr phi heap_final v_final theta
    HImmediate HComp.
  pose proof
    (counted_immediate_silent_initial_return_trace_nil
      n heap env rho expr phi heap_final v_final
      HImmediate HComp)
    as HTrace.
  subst phi.
  apply trace_covered_nil.
Qed.

Lemma counted_EEmpty_summary_trace_covered :
  forall n heap env rho phi heap_final theta,
    CountedComputationEvaluation n heap env rho EEmpty
      phi heap_final (VSummary theta) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n heap env rho phi heap_final theta HComp.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (EEmpty_terminal_summary
      heap env rho phi heap_final theta
      (NStepsN_to_NSteps _ _ _ _ HComp))
    as (_ & _ & HTrace).
  subst phi.
  apply trace_covered_nil.
Qed.

Lemma counted_ETop_summary_trace_covered :
  forall n heap env rho phi heap_final theta,
    CountedComputationEvaluation n heap env rho ETop
      phi heap_final (VSummary theta) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n heap env rho phi heap_final theta HComp.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (ETop_terminal_summary
      heap env rho phi heap_final theta
      (NStepsN_to_NSteps _ _ _ _ HComp))
    as (_ & HTheta & _).
  subst theta.
  apply trace_covered_top.
Qed.

Lemma counted_EAllocAbs_summary_trace_covered :
  forall n heap env rho r phi heap_final theta,
    CountedComputationEvaluation n heap env rho (EAllocAbs r)
      phi heap_final (VSummary theta) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n heap env rho r phi heap_final theta HComp.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (EAllocAbs_terminal_summary
      heap env rho r phi heap_final theta
      (NStepsN_to_NSteps _ _ _ _ HComp))
    as (_ & _ & _ & _ & HTrace).
  subst phi.
  apply trace_covered_nil.
Qed.

Lemma counted_EReadAbs_summary_trace_covered :
  forall n heap env rho r phi heap_final theta,
    CountedComputationEvaluation n heap env rho (EReadAbs r)
      phi heap_final (VSummary theta) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n heap env rho r phi heap_final theta HComp.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (EReadAbs_terminal_summary
      heap env rho r phi heap_final theta
      (NStepsN_to_NSteps _ _ _ _ HComp))
    as (_ & _ & _ & _ & HTrace).
  subst phi.
  apply trace_covered_nil.
Qed.

Lemma counted_EWriteAbs_summary_trace_covered :
  forall n heap env rho r phi heap_final theta,
    CountedComputationEvaluation n heap env rho (EWriteAbs r)
      phi heap_final (VSummary theta) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n heap env rho r phi heap_final theta HComp.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (EWriteAbs_terminal_summary
      heap env rho r phi heap_final theta
      (NStepsN_to_NSteps _ _ _ _ HComp))
    as (_ & _ & _ & _ & HTrace).
  subst phi.
  apply trace_covered_nil.
Qed.

Lemma checked_store_summary_value_concat_from_below :
  forall n gamma omega heap env rho source1 source2 summary1 summary2
    eff_summary1 eff_summary2 phi heap_final theta,
    CheckedStoreSummaryValueSoundnessBelow n ->
    NCheckedBackTriangle gamma omega source1 summary1 ->
    NCheckedBackTriangle gamma omega source2 summary2 ->
    NCheckedTcExp gamma omega summary1 TyEffect eff_summary1 ->
    NCheckedTcExp gamma omega summary2 TyEffect eff_summary2 ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EConcat summary1 summary2) phi heap_final (VSummary theta) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho source1 source2 summary1 summary2
    eff_summary1 eff_summary2 phi heap_final theta
    HSummaryValueBelow HBack1 HBack2 HCheckedSummary1
    HCheckedSummary2 HContext HComp.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (EConcat_counted_decomposition
      n heap env rho summary1 summary2 phi heap_final theta HComp)
    as (n1 & n2 & phi1 & phi2 & theta1 & theta2 &
      heap1 & heap2 & HSummary1 & HSummary2 & HTheta &
      HHeapFinal & HTrace & HCount1 & HCount2).
  subst theta heap_final phi.
  assert (HComp1 :
    CountedComputationEvaluation n1 heap env rho summary1
      phi1 heap1 (VSummary theta1)).
  {
    unfold CountedComputationEvaluation.
    exact HSummary1.
  }
  assert (HComp2 :
    CountedComputationEvaluation n2 heap1 env rho summary2
      phi2 heap2 (VSummary theta2)).
  {
    unfold CountedComputationEvaluation.
    exact HSummary2.
  }
  assert (HCovered1 : TraceCoveredBySummary phi1 theta1).
  {
    eapply HSummaryValueBelow.
    - exact HCount1.
    - exact HBack1.
    - exact HCheckedSummary1.
    - exact HContext.
    - exact HComp1.
  }
  assert (HContext2 :
    CheckedStoreRuntimeContext gamma omega heap1 env rho).
  {
    eapply
      (checked_store_counted_computation_store_runtime_context
        n1 gamma omega heap env rho summary1 TyEffect eff_summary1
        phi1 heap1 (VSummary theta1));
      eauto.
  }
  assert (HCovered2 : TraceCoveredBySummary phi2 theta2).
  {
    eapply HSummaryValueBelow.
    - exact HCount2.
    - exact HBack2.
    - exact HCheckedSummary2.
    - exact HContext2.
    - exact HComp2.
  }
  eapply trace_covered_app_summary_union; eauto.
Qed.

Lemma checked_store_arrow_body_context_from_prefixes :
  forall gamma omega heap env rho ef ea ty_arg ty_body
    eff_body eff_summary eff_f eff_a n_fun n_arg phi_fun phi_arg
    heap_fun heap_arg closure_env closure_rho f x ec ee arg,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega ef
      (TyArrow ty_arg eff_body ty_body eff_summary) eff_f ->
    NCheckedTcExp gamma omega ea ty_arg eff_a ->
    CountedComputationEvaluation n_fun heap env rho ef
      phi_fun heap_fun
      (VClosure closure_env closure_rho f x ec ee) ->
    CountedComputationEvaluation n_arg heap_fun env rho ea
      phi_arg heap_arg arg ->
    exists gamma_body omega_body ty_arg_body ty_arg_res
      ty_body_body ty_body_res eff_body_body eff_body_res
      eff_summary_body eff_summary_res,
      CheckedStoreRuntimeContext
        ((x, ty_arg_body) ::
          (f, TyArrow ty_arg_body eff_body_body
            ty_body_body eff_summary_body) ::
          gamma_body)
        omega_body heap_arg
        (env_extend x arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho /\
      NCheckedTcExp
        ((x, ty_arg_body) ::
          (f, TyArrow ty_arg_body eff_body_body
            ty_body_body eff_summary_body) ::
          gamma_body)
        omega_body ec ty_body_body eff_body_body /\
      NCheckedTcExp
        ((x, ty_arg_body) ::
          (f, TyArrow ty_arg_body eff_body_body
            ty_body_body eff_summary_body) ::
          gamma_body)
        omega_body ee TyEffect eff_summary_body /\
      NCheckedBackTriangle
        ((x, ty_arg_body) ::
          (f, TyArrow ty_arg_body eff_body_body
            ty_body_body eff_summary_body) ::
          gamma_body)
        omega_body ec ee /\
      NResolveStaticEffect closure_rho eff_body_body eff_body_res /\
      NResolveStaticEffect closure_rho eff_summary_body
        eff_summary_res /\
      NResolveTy rho
        (TyArrow ty_arg eff_body ty_body eff_summary)
        (TyArrow ty_arg_res eff_body_res
          ty_body_res eff_summary_res).
Proof.
  intros gamma omega heap env rho ef ea ty_arg ty_body
    eff_body eff_summary eff_f eff_a n_fun n_arg phi_fun phi_arg
    heap_fun heap_arg closure_env closure_rho f x ec ee arg
    HContext HCheckedFun HCheckedArg HFun HArg.
  assert (HFunComp :
    ComputationEvaluation heap env rho ef phi_fun heap_fun
      (VClosure closure_env closure_rho f x ec ee)).
  {
    unfold ComputationEvaluation, CountedComputationEvaluation in *.
    eapply NStepsN_to_NSteps. exact HFun.
  }
  assert (HArgComp :
    ComputationEvaluation heap_fun env rho ea phi_arg heap_arg arg).
  {
    unfold ComputationEvaluation, CountedComputationEvaluation in *.
    eapply NStepsN_to_NSteps. exact HArg.
  }
  destruct
    (checked_store_sequential_computations_store_value_shapes
      gamma omega heap env rho
      ef (TyArrow ty_arg eff_body ty_body eff_summary)
        eff_f phi_fun heap_fun
        (VClosure closure_env closure_rho f x ec ee)
      ea ty_arg eff_a phi_arg heap_arg arg
      HContext HCheckedFun HCheckedArg HFunComp HArgComp)
    as (store & ty_fun_res & ty_arg_res &
      HResolveFun & HResolveArg & HBounded & HHeap &
      HValFun & HValArg).
  destruct
    (NStoreResolvedValShape_closure_inv
      store closure_env closure_rho f x ec ee ty_fun_res HValFun)
    as
      (gamma_body & omega_body &
        ty_arg_body & ty_arg_body_res &
        ty_body_body & ty_body_res &
        eff_body_body & eff_body_res &
        eff_summary_body & eff_summary_res &
        HTyFun & HEnvClosure & HRhoClosure &
        HResolveClosureArg & HResolveClosureBody &
        HResolveClosureBodyTy & HResolveClosureSummary &
        HCheckedBody & HCheckedSummary & HBodyBack).
  assert (HArgResEq : ty_arg_res = ty_arg_body_res).
  {
    rewrite HTyFun in HResolveFun.
    inversion HResolveFun; subst.
    eapply NResolveTy_deterministic; eauto.
  }
  assert (HValFunArrow :
    NStoreResolvedValShape store
      (VClosure closure_env closure_rho f x ec ee)
      (TyArrow ty_arg_body_res eff_body_res
        ty_body_res eff_summary_res)).
  {
    rewrite <- HTyFun.
    exact HValFun.
  }
  exists gamma_body, omega_body,
    ty_arg_body, ty_arg_body_res,
    ty_body_body, ty_body_res,
    eff_body_body, eff_body_res,
    eff_summary_body, eff_summary_res.
  split.
  - split.
    + exists store.
      unfold NStoreResolvedRuntimeShape.
      split; [exact HBounded |].
      split; [exact HHeap |].
      eapply NStoreResolvedEnvShape_extend with
        (ty_res := ty_arg_body_res).
      * exact HResolveClosureArg.
      * rewrite <- HArgResEq. exact HValArg.
      * eapply NStoreResolvedEnvShape_extend with
          (ty_res :=
            TyArrow ty_arg_body_res eff_body_res
              ty_body_res eff_summary_res).
        -- eapply NResolve_Arrow; eauto.
        -- exact HValFunArrow.
        -- exact HEnvClosure.
    + exact HRhoClosure.
  - split; [exact HCheckedBody |].
    split; [exact HCheckedSummary |].
    split; [exact HBodyBack |].
    split; [exact HResolveClosureBody |].
    split; [exact HResolveClosureSummary |].
    rewrite HTyFun in HResolveFun.
    exact HResolveFun.
Qed.

Lemma checked_store_region_body_context_from_prefix :
  forall gamma omega heap env rho er r eff_body ty eff_f
    eff_open_res n_fun phi_fun heap_fun closure_env closure_rho x e
    r_val,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
    eval_region rho r = Some r_val ->
    NResolveStaticEffect rho (open_static_effect r eff_body)
      eff_open_res ->
    CountedComputationEvaluation n_fun heap env rho er
      phi_fun heap_fun
      (VRegionClosure closure_env closure_rho x e) ->
    exists gamma_body omega_body ty_body eff_body_inner,
      CheckedStoreRuntimeContext gamma_body (x :: omega_body)
        heap_fun closure_env
        (rho_extend x r_val closure_rho) /\
      NCheckedTcExp gamma_body (x :: omega_body)
        e ty_body eff_body_inner /\
      NResolveStaticEffect (rho_extend x r_val closure_rho)
        eff_body_inner eff_open_res.
Proof.
  intros gamma omega heap env rho er r eff_body ty eff_f
    eff_open_res n_fun phi_fun heap_fun closure_env closure_rho x e
    r_val HContext HCheckedFun HRgn HResolveOpen HFun.
  destruct
    (checked_store_counted_computation_store_value_shape_resolved
      n_fun gamma omega heap env rho er
      (TyForallRgn eff_body ty) eff_f
      phi_fun heap_fun
      (VRegionClosure closure_env closure_rho x e)
      HContext HCheckedFun HFun)
    as (store_fun & ty_fun_res & HResolveFun & HBoundedFun &
      HHeapFun & HValFun).
  destruct
    (NStoreResolvedValShape_region_closure_inv
      store_fun closure_env closure_rho x e ty_fun_res HValFun)
    as (gamma_body & omega_body & ty_body_inner & ty_body_res &
      eff_body_inner & eff_body_res & HTyFun & HEnvBody &
      HRhoBody & HResolveCloseEff & _HResolveCloseTy &
      HBodyChecked).
  rewrite HTyFun in HResolveFun.
  inversion HResolveFun as
    [| | | | | | | rho0 eff_forall eff_forall_res ty_forall ty_forall_res
      HResolveForallEff HResolveForallTy];
    subst.
  pose proof
    (NResolveStaticEffect_open_static_effect
      rho r eff_body eff_body_res r_val HRgn HResolveForallEff)
    as HResolveOpenExpected.
  pose proof
    (NResolveStaticEffect_deterministic
      rho (open_static_effect r eff_body)
      eff_open_res
      (open_static_effect_type (region_const_type r_val)
        eff_body_res)
      HResolveOpen HResolveOpenExpected)
    as HOpenEq.
  subst eff_open_res.
  pose proof
    (NCheckedRegionBody_checked
      x gamma_body omega_body e ty_body_inner eff_body_inner
      HBodyChecked)
    as HCheckedBody.
  pose proof
    (NCheckedTcExp_eff_wf
      gamma_body (x :: omega_body) e ty_body_inner
      eff_body_inner HCheckedBody)
    as HBodyEffWF.
  assert (HResolveBody :
    NResolveStaticEffect (rho_extend x r_val closure_rho)
      eff_body_inner
      (open_static_effect_type (region_const_type r_val)
        eff_body_res)).
  {
    unfold NStaticEffectWF in HBodyEffWF.
    unfold close_static_effect, open_static_effect_type in *.
    eapply NResolveStaticEffect_rho_extend_close_static_effect_at;
      eauto.
  }
  exists gamma_body, omega_body, ty_body_inner, eff_body_inner.
  split.
  - split.
    + exists store_fun.
      unfold NStoreResolvedRuntimeShape.
      split; [exact HBoundedFun |].
      split; [exact HHeapFun |].
      eapply NStoreResolvedEnvShape_extend_fresh;
        eauto using
          NCheckedRegionBody_fresh,
          NCheckedRegionBody_ctx_wf.
    + eapply NRhoModels_extend; eauto.
  - split; [exact HCheckedBody |].
    exact HResolveBody.
Qed.

Lemma resolved_alloc_action_from_eval_region :
  forall rho r r_val action,
    eval_region rho r = Some r_val ->
    NResolveStaticAction rho (SAlloc (region_expr_to_type r)) action ->
    action = SAlloc (region_const_type r_val).
Proof.
  intros rho r r_val action HRgn HResolve.
  pose proof
    (NResolveStaticAction_deterministic
      rho (SAlloc (region_expr_to_type r)) action
      (SAlloc (region_const_type r_val))
      HResolve
      (NResolve_SAlloc rho (region_expr_to_type r)
        (region_const_type r_val)
        (NResolveRegionType_region_expr_to_type rho r r_val HRgn)))
    as HAction.
  exact HAction.
Qed.

Lemma resolved_read_action_from_eval_region :
  forall rho r r_val action,
    eval_region rho r = Some r_val ->
    NResolveStaticAction rho (SRead (region_expr_to_type r)) action ->
    action = SRead (region_const_type r_val).
Proof.
  intros rho r r_val action HRgn HResolve.
  pose proof
    (NResolveStaticAction_deterministic
      rho (SRead (region_expr_to_type r)) action
      (SRead (region_const_type r_val))
      HResolve
      (NResolve_SRead rho (region_expr_to_type r)
        (region_const_type r_val)
        (NResolveRegionType_region_expr_to_type rho r r_val HRgn)))
    as HAction.
  exact HAction.
Qed.

Lemma resolved_write_action_from_eval_region :
  forall rho r r_val action,
    eval_region rho r = Some r_val ->
    NResolveStaticAction rho (SWrite (region_expr_to_type r)) action ->
    action = SWrite (region_const_type r_val).
Proof.
  intros rho r r_val action HRgn HResolve.
  pose proof
    (NResolveStaticAction_deterministic
      rho (SWrite (region_expr_to_type r)) action
      (SWrite (region_const_type r_val))
      HResolve
      (NResolve_SWrite rho (region_expr_to_type r)
        (region_const_type r_val)
        (NResolveRegionType_region_expr_to_type rho r r_val HRgn)))
    as HAction.
  exact HAction.
Qed.

Lemma KReadConc_loc_terminal_trace_nil :
  forall heap r l phi heap_final v_final,
    NSteps
      (StReturn heap (VLoc r l) (KReadConc KDone))
      phi
      (StDone heap_final v_final) ->
    heap_final = heap /\ phi = [].
Proof.
  intros heap r l phi heap_final v_final HSteps.
  remember
    (StReturn heap (VLoc r l) (KReadConc KDone))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as
    [state | state label state' phi_tail state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (NSteps_return_done_inv
        heap
        (VSummary (SummarySet [CReadConc r l]))
        phi_tail heap_final v_final HTail)
      as (HHeap & _HVal & HTrace).
    simpl in *.
    split; assumption.
Qed.

Lemma KWriteConc_loc_terminal_trace_nil :
  forall heap r l phi heap_final v_final,
    NSteps
      (StReturn heap (VLoc r l) (KWriteConc KDone))
      phi
      (StDone heap_final v_final) ->
    heap_final = heap /\ phi = [].
Proof.
  intros heap r l phi heap_final v_final HSteps.
  remember
    (StReturn heap (VLoc r l) (KWriteConc KDone))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as
    [state | state label state' phi_tail state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (NSteps_return_done_inv
        heap
        (VSummary (SummarySet [CWriteConc r l]))
        phi_tail heap_final v_final HTail)
      as (HHeap & _HVal & HTrace).
    simpl in *.
    split; assumption.
Qed.

Lemma EReadConc_counted_decomposition_static :
  forall n heap env rho e phi heap_final v_final,
    CountedComputationEvaluation n heap env rho (EReadConc e)
      phi heap_final v_final ->
    exists n_e phi_e heap_e r l,
      CountedComputationEvaluation n_e heap env rho e
        phi_e heap_e (VLoc r l) /\
      n_e < n /\
      heap_final = heap_e /\
      phi = phi_e.
Proof.
  intros n heap env rho e phi heap_final v_final HComp.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (NInitialState heap env rho (EReadConc e))
      LSilent
      (StEval heap env rho e (KReadConc KDone))
      phi heap_final v_final
      (StepReadConc heap env rho e KDone)
      HComp)
    as (n_tail & phi_tail & _HStart & HExprWithKont & HTraceStart).
  destruct
    (NStepsN_append_kont_terminal_split_counted
      n_tail
      (StEval heap env rho e (KReadConc KDone))
      phi_tail heap_final v_final HExprWithKont
      (NInitialState heap env rho e)
      (KReadConc KDone)
      eq_refl)
    as (n_e & n_after & phi_e & heap_e & v_loc &
      phi_after & HExpr & HAfter & HCountExpr & HTraceExpr).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KReadConc_terminal_value_is_loc
        heap_e v_loc KDone phi_after heap_final v_final
        (NStepsN_to_NSteps _ _ _ _ HAfter))
      as (r_loc & l & HLoc).
    subst v_loc.
    destruct
      (KReadConc_loc_terminal_trace_nil
        heap_e r_loc l phi_after heap_final v_final
        (NStepsN_to_NSteps _ _ _ _ HAfter))
      as (HHeapFinal & HTraceAfter).
    subst heap_final phi_after.
    assert (HAfterPositive : 0 < n_after).
    { destruct n_after; [inversion HAfter | lia]. }
    exists n_e, phi_e, heap_e, r_loc, l.
    repeat split; try assumption; try lia.
    simpl in HTraceStart.
    subst phi.
    try rewrite HTraceExpr.
    try rewrite app_nil_r.
    reflexivity.
Qed.

Lemma EWriteConc_counted_decomposition_static :
  forall n heap env rho e phi heap_final v_final,
    CountedComputationEvaluation n heap env rho (EWriteConc e)
      phi heap_final v_final ->
    exists n_e phi_e heap_e r l,
      CountedComputationEvaluation n_e heap env rho e
        phi_e heap_e (VLoc r l) /\
      n_e < n /\
      heap_final = heap_e /\
      phi = phi_e.
Proof.
  intros n heap env rho e phi heap_final v_final HComp.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (NInitialState heap env rho (EWriteConc e))
      LSilent
      (StEval heap env rho e (KWriteConc KDone))
      phi heap_final v_final
      (StepWriteConc heap env rho e KDone)
      HComp)
    as (n_tail & phi_tail & _HStart & HExprWithKont & HTraceStart).
  destruct
    (NStepsN_append_kont_terminal_split_counted
      n_tail
      (StEval heap env rho e (KWriteConc KDone))
      phi_tail heap_final v_final HExprWithKont
      (NInitialState heap env rho e)
      (KWriteConc KDone)
      eq_refl)
    as (n_e & n_after & phi_e & heap_e & v_loc &
      phi_after & HExpr & HAfter & HCountExpr & HTraceExpr).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KWriteConc_terminal_value_is_loc
        heap_e v_loc KDone phi_after heap_final v_final
        (NStepsN_to_NSteps _ _ _ _ HAfter))
      as (r_loc & l & HLoc).
    subst v_loc.
    destruct
      (KWriteConc_loc_terminal_trace_nil
        heap_e r_loc l phi_after heap_final v_final
        (NStepsN_to_NSteps _ _ _ _ HAfter))
      as (HHeapFinal & HTraceAfter).
    subst heap_final phi_after.
    assert (HAfterPositive : 0 < n_after).
    { destruct n_after; [inversion HAfter | lia]. }
    exists n_e, phi_e, heap_e, r_loc, l.
    repeat split; try assumption; try lia.
    simpl in HTraceStart.
    subst phi.
    try rewrite HTraceExpr.
    try rewrite app_nil_r.
    reflexivity.
Qed.

Lemma counted_immediate_silent_initial_return_static_covered :
  forall n heap env rho expr phi heap_final v_final eff,
    (forall label state',
      NStep (NInitialState heap env rho expr) label state' ->
      exists v0,
        label = LSilent /\
        state' = StReturn heap v0 KDone) ->
    CountedComputationEvaluation n heap env rho expr
      phi heap_final v_final ->
    TraceCoveredByStaticEffect phi eff.
Proof.
  intros n heap env rho expr phi heap_final v_final eff
    HImmediate HComp.
  pose proof
    (counted_immediate_silent_initial_return_trace_nil
      n heap env rho expr phi heap_final v_final
      HImmediate HComp)
    as HTrace.
  subst phi.
  apply TraceCoveredByStaticEffect_nil.
Qed.

Lemma checked_store_counted_tyeffect_value_is_summary :
  forall n gamma omega heap env rho expr eff phi heap_final v_final,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr TyEffect eff ->
    CountedComputationEvaluation n heap env rho expr
      phi heap_final v_final ->
    exists theta,
      v_final = VSummary theta.
Proof.
  intros n gamma omega heap env rho expr eff phi heap_final v_final
    HContext HChecked HComp.
  destruct
    (checked_store_counted_computation_store_value_shape_resolved
      n gamma omega heap env rho expr TyEffect eff
      phi heap_final v_final HContext HChecked HComp)
    as (store & ty_res & HResolveTy & _HBounded & _HHeap & HVal).
  assert (HTyRes : ty_res = TyEffect).
  {
    eapply NResolveTy_deterministic.
    - exact HResolveTy.
    - constructor.
  }
  subst ty_res.
  inversion HVal; subst.
  exists theta.
  reflexivity.
Qed.

Lemma checked_store_counted_tynat_value_is_nat :
  forall n gamma omega heap env rho expr eff phi heap_final v_final,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr TyNat eff ->
    CountedComputationEvaluation n heap env rho expr
      phi heap_final v_final ->
    exists n_final,
      v_final = VNat n_final.
Proof.
  intros n gamma omega heap env rho expr eff phi heap_final v_final
    HContext HChecked HComp.
  destruct
    (checked_store_counted_computation_store_value_shape_resolved
      n gamma omega heap env rho expr TyNat eff
      phi heap_final v_final HContext HChecked HComp)
    as (store & ty_res & HResolveTy & _HBounded & _HHeap & HVal).
  assert (HTyRes : ty_res = TyNat).
  {
    eapply NResolveTy_deterministic.
    - exact HResolveTy.
    - constructor.
  }
  subst ty_res.
  inversion HVal; subst.
  exists n0.
  reflexivity.
Qed.

Lemma checked_store_counted_tybool_value_is_bool :
  forall n gamma omega heap env rho expr eff phi heap_final v_final,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr TyBool eff ->
    CountedComputationEvaluation n heap env rho expr
      phi heap_final v_final ->
    exists b_final,
      v_final = VBool b_final.
Proof.
  intros n gamma omega heap env rho expr eff phi heap_final v_final
    HContext HChecked HComp.
  destruct
    (checked_store_counted_computation_store_value_shape_resolved
      n gamma omega heap env rho expr TyBool eff
      phi heap_final v_final HContext HChecked HComp)
    as (store & ty_res & HResolveTy & _HBounded & _HHeap & HVal).
  assert (HTyRes : ty_res = TyBool).
  {
    eapply NResolveTy_deterministic.
    - exact HResolveTy.
    - constructor.
  }
  subst ty_res.
  inversion HVal; subst.
  exists b.
  reflexivity.
Qed.

Definition CheckedStoreComputationTraceSoundnessBelow (n : nat) : Prop :=
  forall n_eval gamma omega heap env rho expr ty eff
    phi heap_final v_final eff_res,
    n_eval < n ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr ty eff ->
    CountedComputationEvaluation n_eval heap env rho expr
      phi heap_final v_final ->
    NResolveStaticEffect rho eff eff_res ->
    TraceCoveredByStaticEffect phi eff_res.

Theorem checked_store_computation_trace_soundness_below :
  forall n,
    CheckedStoreComputationTraceSoundnessBelow n.
Proof.
  induction n as [n IH] using lt_wf_ind.
  unfold CheckedStoreComputationTraceSoundnessBelow.
  intros n_eval gamma omega heap env rho expr ty eff
    phi heap_final v_final eff_res HCount HContext HChecked
    HComp HResolve.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HShape; subst; clear HShape.
  - eapply counted_immediate_silent_initial_return_static_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - eapply counted_immediate_silent_initial_return_static_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - eapply counted_immediate_silent_initial_return_static_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - eapply counted_immediate_silent_initial_return_static_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - eapply counted_immediate_silent_initial_return_static_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - destruct
      (NResolveStaticEffect_static_union_inv
        rho eff_f (static_union eff_a eff_body) eff_res HResolve)
      as (eff_f_res & eff_tail_res & HEffRes &
        HResolveFun & HResolveTail).
    destruct
      (NResolveStaticEffect_static_union_inv
        rho eff_a eff_body eff_tail_res HResolveTail)
      as (eff_a_res & eff_body_res & HTailRes &
        HResolveArg & HResolveBody).
    subst eff_res eff_tail_res.
    unfold CountedComputationEvaluation in HComp.
    destruct
      (EMuApp_counted_decomposition
        n_eval heap env rho ef ea phi heap_final v_final HComp)
      as (n_fun & n_arg & n_body &
        phi_fun & phi_arg & phi_body &
        closure_env & closure_rho & f & x & ec & ee & arg &
        heap_arg & heap_fun &
        HFun & HArg & HBody &
        HCountFun & HCountArg & HCountBody & HTrace).
    assert (HFunComp :
      CountedComputationEvaluation n_fun heap env rho ef
        phi_fun heap_fun
        (VClosure closure_env closure_rho f x ec ee)).
    { unfold CountedComputationEvaluation. exact HFun. }
    assert (HContextArg :
      CheckedStoreRuntimeContext gamma omega heap_fun env rho).
    {
      eapply checked_store_counted_computation_store_runtime_context.
      - exact HContext.
      - match goal with
        | HFunChecked : NCheckedTcExp gamma omega ef
            (TyArrow ty_arg eff_body ty eff_summary) eff_f |- _ =>
            exact HFunChecked
        end.
      - exact HFunComp.
    }
    assert (HArgComp :
      CountedComputationEvaluation n_arg heap_fun env rho ea
        phi_arg heap_arg arg).
    { unfold CountedComputationEvaluation. exact HArg. }
    destruct
      (checked_store_arrow_body_context_from_prefixes
        gamma omega heap env rho ef ea ty_arg ty
        eff_body eff_summary eff_f eff_a
        n_fun n_arg phi_fun phi_arg heap_fun heap_arg
        closure_env closure_rho f x ec ee arg
        HContext
        ltac:(match goal with
        | HFunChecked : NCheckedTcExp gamma omega ef
            (TyArrow ty_arg eff_body ty eff_summary) eff_f |- _ =>
            exact HFunChecked
        end)
        ltac:(match goal with
        | HArgChecked : NCheckedTcExp gamma omega ea ty_arg eff_a |- _ =>
            exact HArgChecked
        end)
        HFunComp HArgComp)
      as (gamma_body & omega_body & ty_arg_body &
        ty_arg_res & ty_body_body & ty_body_res &
        eff_body_body & eff_body_res_body &
        eff_summary_body & eff_summary_res &
        HBodyContext & HCheckedBody & _HCheckedSummary &
        _HBodyBack & HResolveBodyClosure &
        _HResolveSummaryClosure & HResolveFunArrow).
    inversion HResolveFunArrow; subst.
    match goal with
    | HBodyResolved : NResolveStaticEffect rho eff_body eff_body_res_body |- _ =>
        pose proof
          (NResolveStaticEffect_deterministic
            rho eff_body eff_body_res eff_body_res_body
            HResolveBody HBodyResolved)
          as HBodyResEq
    end.
    subst eff_body_res_body.
    assert (HBodyComp :
      CountedComputationEvaluation n_body heap_arg
        (env_extend x arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho ec phi_body heap_final v_final).
    { unfold CountedComputationEvaluation. exact HBody. }
    eapply TraceCoveredByStaticEffect_app3.
    + eapply (IH n_eval HCount).
      * exact HCountFun.
      * exact HContext.
      * exact H.
      * exact HFunComp.
      * exact HResolveFun.
    + eapply (IH n_eval HCount).
      * exact HCountArg.
      * exact HContextArg.
      * exact H0.
      * exact HArgComp.
      * exact HResolveArg.
    + eapply (IH n_eval HCount).
      * exact HCountBody.
      * exact HBodyContext.
      * exact HCheckedBody.
      * exact HBodyComp.
      * exact HResolveBodyClosure.
  - destruct
      (NResolveStaticEffect_static_union_inv
        rho eff_f (open_static_effect r eff_body) eff_res HResolve)
      as (eff_f_res & eff_open_res & HEffRes &
        HResolveFun & HResolveOpen).
    subst eff_res.
    unfold CountedComputationEvaluation in HComp.
    destruct
      (ERgnApp_counted_decomposition
        n_eval heap env rho er r phi heap_final v_final HComp)
      as (n_fun & n_body & phi_fun & phi_body &
        closure_env & closure_rho & x & e & heap_fun & r_val &
        HRgn & HFun & HBody & HCountFun & HCountBody & HTrace).
    assert (HFunComp :
      CountedComputationEvaluation n_fun heap env rho er
        phi_fun heap_fun
        (VRegionClosure closure_env closure_rho x e)).
    { unfold CountedComputationEvaluation. exact HFun. }
    match goal with
    | HFunChecked : NCheckedTcExp gamma omega er
        (TyForallRgn eff_body ?ty_body) eff_f |- _ =>
        destruct
          (checked_store_region_body_context_from_prefix
            gamma omega heap env rho er r eff_body ty_body eff_f
            eff_open_res n_fun phi_fun heap_fun closure_env closure_rho
            x e r_val HContext HFunChecked HRgn HResolveOpen HFunComp)
          as (gamma_body & omega_body & ty_body_inner &
            eff_body_inner & HBodyContext & HCheckedBody &
            HResolveBody)
    end.
    assert (HBodyComp :
      CountedComputationEvaluation n_body heap_fun closure_env
        (rho_extend x r_val closure_rho)
        e phi_body heap_final v_final).
    { unfold CountedComputationEvaluation. exact HBody. }
    subst phi.
    eapply TraceCoveredByStaticEffect_app.
    + eapply (IH n_eval HCount).
      * exact HCountFun.
      * exact HContext.
      * match goal with
        | HFunChecked : NCheckedTcExp gamma omega er
            (TyForallRgn eff_body ?ty_body) eff_f |- _ =>
            exact HFunChecked
        end.
      * exact HFunComp.
      * exact HResolveFun.
    + eapply (IH n_eval HCount).
      * exact HCountBody.
      * exact HBodyContext.
      * exact HCheckedBody.
      * exact HBodyComp.
      * exact HResolveBody.
  - destruct
      (NResolveStaticEffect_static_union_inv
        rho eff_f (static_union eff_a eff_summary) eff_res HResolve)
      as (eff_f_res & eff_tail_res & HEffRes &
        HResolveFun & HResolveTail).
    destruct
      (NResolveStaticEffect_static_union_inv
        rho eff_a eff_summary eff_tail_res HResolveTail)
      as (eff_a_res & eff_summary_res & HTailRes &
        HResolveArg & HResolveSummary).
    subst eff_res eff_tail_res.
    destruct
      (checked_store_counted_tyeffect_value_is_summary
        n_eval gamma omega heap env rho
        (EEffApp ef ea)
        (static_union eff_f (static_union eff_a eff_summary))
        phi heap_final v_final
        HContext HChecked HComp)
      as (theta & HFinalSummary).
    subst v_final.
    unfold CountedComputationEvaluation in HComp.
    destruct
      (EEffApp_counted_decomposition
        n_eval heap env rho ef ea phi heap_final
        theta HComp)
      as (n_fun & n_arg & n_summary &
        phi_fun & phi_arg & phi_summary &
        closure_env & closure_rho & f & x & ec & ee & arg &
        heap_arg & heap_fun & HFun & HArg & HBody &
        HCountFun & HCountArg & HCountSummary & HTrace).
    assert (HFunComp :
      CountedComputationEvaluation n_fun heap env rho ef
        phi_fun heap_fun
        (VClosure closure_env closure_rho f x ec ee)).
    { unfold CountedComputationEvaluation. exact HFun. }
    assert (HArgComp :
      CountedComputationEvaluation n_arg heap_fun env rho ea
        phi_arg heap_arg arg).
    { unfold CountedComputationEvaluation. exact HArg. }
    assert (HContextArg :
      CheckedStoreRuntimeContext gamma omega heap_fun env rho).
    {
      eapply checked_store_counted_computation_store_runtime_context.
      - exact HContext.
      - match goal with
        | HFunChecked : NCheckedTcExp gamma omega ef
            (TyArrow ty_arg eff_body ty_body eff_summary) eff_f |- _ =>
            exact HFunChecked
        end.
      - exact HFunComp.
    }
    destruct
      (checked_store_arrow_body_context_from_prefixes
        gamma omega heap env rho ef ea ty_arg ty_body
        eff_body eff_summary eff_f eff_a
        n_fun n_arg phi_fun phi_arg heap_fun heap_arg
        closure_env closure_rho f x ec ee arg
        HContext
        ltac:(match goal with
        | HFunChecked : NCheckedTcExp gamma omega ef
            (TyArrow ty_arg eff_body ty_body eff_summary) eff_f |- _ =>
            exact HFunChecked
        end)
        ltac:(match goal with
        | HArgChecked : NCheckedTcExp gamma omega ea ty_arg eff_a |- _ =>
            exact HArgChecked
        end)
        HFunComp HArgComp)
      as (gamma_body & omega_body & ty_arg_body &
        ty_arg_res & ty_body_body & ty_body_res &
        eff_body_body & eff_body_res &
        eff_summary_body & eff_summary_res_body &
        HBodyContext & _HCheckedBody & HCheckedSummary &
        _HBodyBack & _HResolveBodyClosure &
        HResolveSummaryClosure & HResolveFunArrow).
    inversion HResolveFunArrow; subst.
    match goal with
    | HSummaryResolved :
        NResolveStaticEffect rho eff_summary eff_summary_res_body |- _ =>
        pose proof
          (NResolveStaticEffect_deterministic
            rho eff_summary eff_summary_res eff_summary_res_body
            HResolveSummary HSummaryResolved)
          as HSummaryResEq
    end.
    subst eff_summary_res_body.
    assert (HSummaryComp :
      CountedComputationEvaluation n_summary heap_arg
        (env_extend x arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho ee phi_summary heap_final (VSummary theta)).
    { unfold CountedComputationEvaluation. exact HBody. }
    eapply TraceCoveredByStaticEffect_app3.
    + eapply (IH n_eval HCount).
      * exact HCountFun.
      * exact HContext.
      * match goal with
        | HFunChecked : NCheckedTcExp gamma omega ef
            (TyArrow ty_arg eff_body ty_body eff_summary) eff_f |- _ =>
            exact HFunChecked
        end.
      * exact HFunComp.
      * exact HResolveFun.
    + eapply (IH n_eval HCount).
      * exact HCountArg.
      * exact HContextArg.
      * match goal with
        | HArgChecked : NCheckedTcExp gamma omega ea ty_arg eff_a |- _ =>
            exact HArgChecked
        end.
      * exact HArgComp.
      * exact HResolveArg.
    + eapply (IH n_eval HCount).
      * exact HCountSummary.
      * exact HBodyContext.
      * exact HCheckedSummary.
      * exact HSummaryComp.
      * exact HResolveSummaryClosure.
  - destruct
      (NResolveStaticEffect_static_union_inv
        rho (static_union eff_summary1 eff_summary2)
        (static_union eff1 eff2) eff_res HResolve)
      as (eff_summaries_res & eff_bodies_res & HEffRes &
        HResolveSummaries & HResolveBodies).
    destruct
      (NResolveStaticEffect_static_union_inv
        rho eff_summary1 eff_summary2 eff_summaries_res
        HResolveSummaries)
      as (eff_summary1_res & eff_summary2_res & HSummariesRes &
        HResolveSummary1 & HResolveSummary2).
    destruct
      (NResolveStaticEffect_static_union_inv
        rho eff1 eff2 eff_bodies_res HResolveBodies)
      as (eff1_res & eff2_res & HBodiesRes &
        HResolve1 & HResolve2).
    subst eff_res eff_summaries_res eff_bodies_res.
    unfold CountedComputationEvaluation in HComp.
    destruct
      (EPairPar_counted_decomposition
        n_eval heap env rho ef1 ea1 ef2 ea2
        phi heap_final v_final HComp)
      as (n_eff1 & n_eff2 & n_left & n_right &
        phi_eff1 & phi_eff2 & phi_left & phi_right &
        theta1 & theta2 & heap_eff1 & heap_eff2 &
        heap_left & heap_right & v_left & v_right &
        HSummary1 & HSummary2 & HLeft & HRight &
        HCountSummary1 & HCountSummary2 & HCountLeft &
        HCountRight & _HSummaryDisjoint & _HTraceDisjoint &
        HHeapFinal & HValueFinal & HTrace).
    assert (HSummary1Comp :
      CountedComputationEvaluation n_eff1 heap env rho
        (EEffApp ef1 ea1) phi_eff1 heap_eff1 (VSummary theta1)).
    { unfold CountedComputationEvaluation. exact HSummary1. }
    assert (HContextSummary2 :
      CheckedStoreRuntimeContext gamma omega heap_eff1 env rho).
    {
      eapply checked_store_counted_computation_store_runtime_context.
      - exact HContext.
      - match goal with
        | HSummary1Checked :
            NCheckedTcExp gamma omega (EEffApp ef1 ea1)
              TyEffect eff_summary1 |- _ =>
            exact HSummary1Checked
        end.
      - exact HSummary1Comp.
    }
    assert (HSummary2Comp :
      CountedComputationEvaluation n_eff2 heap_eff1 env rho
        (EEffApp ef2 ea2) phi_eff2 heap_eff2 (VSummary theta2)).
    { unfold CountedComputationEvaluation. exact HSummary2. }
    assert (HContextLeft :
      CheckedStoreRuntimeContext gamma omega heap_eff2 env rho).
    {
      eapply checked_store_counted_computation_store_runtime_context.
      - exact HContextSummary2.
      - match goal with
        | HSummary2Checked :
            NCheckedTcExp gamma omega (EEffApp ef2 ea2)
              TyEffect eff_summary2 |- _ =>
            exact HSummary2Checked
        end.
      - exact HSummary2Comp.
    }
    assert (HLeftComp :
      CountedComputationEvaluation n_left heap_eff2 env rho
        (EMuApp ef1 ea1) phi_left heap_left v_left).
    { unfold CountedComputationEvaluation. exact HLeft. }
    assert (HContextRight :
      CheckedStoreRuntimeContext gamma omega heap_left env rho).
    {
      eapply checked_store_counted_computation_store_runtime_context.
      - exact HContextLeft.
      - match goal with
        | HLeftChecked :
            NCheckedTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 |- _ =>
            exact HLeftChecked
        end.
      - exact HLeftComp.
    }
    assert (HRightComp :
      CountedComputationEvaluation n_right heap_left env rho
        (EMuApp ef2 ea2) phi_right heap_right v_right).
    { unfold CountedComputationEvaluation. exact HRight. }
    subst heap_final v_final phi.
    eapply TraceCoveredByStaticEffect_app4.
    + eapply (IH n_eval HCount).
      * exact HCountSummary1.
      * exact HContext.
      * match goal with
        | HSummary1Checked :
            NCheckedTcExp gamma omega (EEffApp ef1 ea1)
              TyEffect eff_summary1 |- _ =>
            exact HSummary1Checked
        end.
      * exact HSummary1Comp.
      * exact HResolveSummary1.
    + eapply (IH n_eval HCount).
      * exact HCountSummary2.
      * exact HContextSummary2.
      * match goal with
        | HSummary2Checked :
            NCheckedTcExp gamma omega (EEffApp ef2 ea2)
              TyEffect eff_summary2 |- _ =>
            exact HSummary2Checked
        end.
      * exact HSummary2Comp.
      * exact HResolveSummary2.
    + eapply (IH n_eval HCount).
      * exact HCountLeft.
      * exact HContextLeft.
      * match goal with
        | HLeftChecked :
            NCheckedTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 |- _ =>
            exact HLeftChecked
        end.
      * exact HLeftComp.
      * exact HResolve1.
    + eapply (IH n_eval HCount).
      * exact HCountRight.
      * exact HContextRight.
      * match goal with
        | HRightChecked :
            NCheckedTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 |- _ =>
            exact HRightChecked
        end.
      * exact HRightComp.
      * exact HResolve2.
  - destruct
      (NResolveStaticEffect_static_union_inv
        rho eff_e (static_union eff_t eff_f) eff_res HResolve)
      as (eff_e_res & eff_branch_res & HEffRes &
        HResolveCond & HResolveBranches).
    destruct
      (NResolveStaticEffect_static_union_inv
        rho eff_t eff_f eff_branch_res HResolveBranches)
      as (eff_t_res & eff_f_res & HBranchRes &
        HResolveThen & HResolveElse).
    subst eff_res eff_branch_res.
    unfold CountedComputationEvaluation in HComp.
    destruct
      (ECond_counted_decomposition
        n_eval heap env rho e et ef phi heap_final v_final HComp)
      as (n_cond & n_branch & phi_cond & b & heap_cond &
        phi_branch & HCond & HBranch & HTrace &
        HCountCond & HCountBranch).
    assert (HCondComp :
      CountedComputationEvaluation n_cond heap env rho e
        phi_cond heap_cond (VBool b)).
    { unfold CountedComputationEvaluation. exact HCond. }
    assert (HContextBranch :
      CheckedStoreRuntimeContext gamma omega heap_cond env rho).
    {
      eapply checked_store_counted_computation_store_runtime_context.
      - exact HContext.
      - match goal with
        | HCondChecked : NCheckedTcExp gamma omega e TyBool eff_e |- _ =>
            exact HCondChecked
        end.
      - exact HCondComp.
    }
    assert (HBranchComp :
      CountedComputationEvaluation n_branch heap_cond env rho
        (if b then et else ef) phi_branch heap_final v_final).
    { unfold CountedComputationEvaluation. exact HBranch. }
    subst phi.
    destruct b.
    + eapply TraceCoveredByStaticEffect_weaken.
      * eapply TraceCoveredByStaticEffect_app.
        -- eapply (IH n_eval HCount).
           ++ exact HCountCond.
           ++ exact HContext.
           ++ match goal with
              | HCondChecked :
                  NCheckedTcExp gamma omega e TyBool eff_e |- _ =>
                  exact HCondChecked
              end.
           ++ exact HCondComp.
           ++ exact HResolveCond.
        -- eapply (IH n_eval HCount).
           ++ exact HCountBranch.
           ++ exact HContextBranch.
           ++ match goal with
              | HThenChecked :
                  NCheckedTcExp gamma omega et ty eff_t |- _ =>
                  exact HThenChecked
              end.
           ++ exact HBranchComp.
           ++ exact HResolveThen.
      * apply StaticEffectIncluded_app.
        -- apply StaticEffectIncluded_refl.
        -- apply StaticEffectIncluded_app_l.
    + eapply TraceCoveredByStaticEffect_weaken.
      * eapply TraceCoveredByStaticEffect_app.
        -- eapply (IH n_eval HCount).
           ++ exact HCountCond.
           ++ exact HContext.
           ++ match goal with
              | HCondChecked :
                  NCheckedTcExp gamma omega e TyBool eff_e |- _ =>
                  exact HCondChecked
              end.
           ++ exact HCondComp.
           ++ exact HResolveCond.
        -- eapply (IH n_eval HCount).
           ++ exact HCountBranch.
           ++ exact HContextBranch.
           ++ match goal with
              | HElseChecked :
                  NCheckedTcExp gamma omega ef ty eff_f |- _ =>
                  exact HElseChecked
              end.
           ++ exact HBranchComp.
           ++ exact HResolveElse.
      * apply StaticEffectIncluded_app.
        -- apply StaticEffectIncluded_refl.
        -- apply StaticEffectIncluded_app_r.
  - inversion HResolve as
      [| rho0 action action_res eff_child eff_child_res
         HResolveAction HResolveChild];
      subst.
    unfold CountedComputationEvaluation in HComp.
    destruct
      (ERef_counted_decomposition
        n_eval heap env rho r e phi heap_final v_final HComp)
      as (n_e & phi_e & heap_e & v & r_val & l &
        HRgn & HExpr & HAlloc & HLoc & HTrace & HCountExpr).
    pose proof
      (resolved_alloc_action_from_eval_region
        rho r r_val action_res HRgn HResolveAction)
      as HActionEq.
    subst action_res v_final phi.
    assert (HExprComp :
      CountedComputationEvaluation n_e heap env rho e
        phi_e heap_e v).
    { unfold CountedComputationEvaluation. exact HExpr. }
    eapply TraceCoveredByStaticEffect_weaken.
    + eapply TraceCoveredByStaticEffect_app.
      * eapply (IH n_eval HCount).
        -- exact HCountExpr.
        -- exact HContext.
        -- match goal with
           | HExprChecked : NCheckedTcExp gamma omega e ?ty_child ?eff_child_expr |- _ =>
               exact HExprChecked
           end.
        -- exact HExprComp.
        -- exact HResolveChild.
      * apply TraceCoveredByStaticEffect_singleton.
    + apply StaticEffectIncluded_app_singleton_front.
  - inversion HResolve as
      [| rho0 action action_res eff_child eff_child_res
         HResolveAction HResolveChild];
      subst.
    unfold CountedComputationEvaluation in HComp.
    destruct
      (EDeref_counted_decomposition
        n_eval heap env rho r e phi heap_final v_final HComp)
      as (n_e & phi_e & heap_e & r_loc & l &
        HExpr & _HLookup & HHeapFinal & HTrace & HCountExpr).
    assert (HExprComp :
      CountedComputationEvaluation n_e heap env rho e
        phi_e heap_e (VLoc r_loc l)).
    { unfold CountedComputationEvaluation. exact HExpr. }
    match goal with
    | HExprChecked : NCheckedTcExp gamma omega e
        (TyRef (region_expr_to_type r) ?ty_cell) ?eff_child_expr |- _ =>
        destruct
          (checked_store_counted_computation_store_value_shape_resolved
            n_e gamma omega heap env rho e
            (TyRef (region_expr_to_type r) ty_cell) eff_child_expr
            phi_e heap_e (VLoc r_loc l)
            HContext HExprChecked HExprComp)
          as (store & ty_res & HResolveTy & _HBounded &
            _HHeap & HVal);
        pose proof
          (NStoreResolvedValShape_loc_ref_region
            store rho r ty_cell ty_res r_loc l HResolveTy HVal)
          as HRgn
    end.
    pose proof
      (resolved_read_action_from_eval_region
        rho r r_loc action_res HRgn HResolveAction)
      as HActionEq.
    subst action_res heap_final phi.
    eapply TraceCoveredByStaticEffect_weaken.
    + eapply TraceCoveredByStaticEffect_app.
      * eapply (IH n_eval HCount).
        -- exact HCountExpr.
        -- exact HContext.
        -- match goal with
           | HExprChecked : NCheckedTcExp gamma omega e
               (TyRef (region_expr_to_type r) ?ty_cell) ?eff_child_expr |- _ =>
               exact HExprChecked
           end.
        -- exact HExprComp.
        -- exact HResolveChild.
      * apply TraceCoveredByStaticEffect_singleton.
    + apply StaticEffectIncluded_app_singleton_front.
  - inversion HResolve as
      [| rho0 action action_res eff_tail eff_tail_res
         HResolveAction HResolveTail];
      subst.
    destruct
      (NResolveStaticEffect_static_union_inv
        rho eff_a eff_v eff_tail_res HResolveTail)
      as (eff_a_res & eff_v_res & HTailRes &
        HResolveAddr & HResolveVal).
    subst eff_tail_res.
    unfold CountedComputationEvaluation in HComp.
    destruct
      (EAssign_counted_decomposition
        n_eval heap env rho r ea ev phi heap_final v_final HComp)
      as (n_addr & n_val & phi_addr & phi_val &
        heap_addr & heap_val & r_loc & l & v &
        HAddr & HVal & HHeapFinal & HValueFinal &
        HTrace & HCountAddr & HCountVal).
    assert (HAddrComp :
      CountedComputationEvaluation n_addr heap env rho ea
        phi_addr heap_addr (VLoc r_loc l)).
    { unfold CountedComputationEvaluation. exact HAddr. }
    match goal with
    | HAddrChecked : NCheckedTcExp gamma omega ea
        (TyRef (region_expr_to_type r) ?ty_cell) eff_a |- _ =>
        destruct
          (checked_store_counted_computation_store_value_shape_resolved
            n_addr gamma omega heap env rho ea
            (TyRef (region_expr_to_type r) ty_cell) eff_a
            phi_addr heap_addr (VLoc r_loc l)
            HContext HAddrChecked HAddrComp)
          as (store & ty_res & HResolveTy & _HBounded &
            _HHeap & HLocVal);
        pose proof
          (NStoreResolvedValShape_loc_ref_region
            store rho r ty_cell ty_res r_loc l HResolveTy HLocVal)
          as HRgn
    end.
    pose proof
      (resolved_write_action_from_eval_region
        rho r r_loc action_res HRgn HResolveAction)
      as HActionEq.
    subst action_res heap_final v_final phi.
    assert (HContextVal :
      CheckedStoreRuntimeContext gamma omega heap_addr env rho).
    {
      eapply checked_store_counted_computation_store_runtime_context.
      - exact HContext.
      - match goal with
        | HAddrChecked : NCheckedTcExp gamma omega ea
            (TyRef (region_expr_to_type r) ?ty_cell) eff_a |- _ =>
            exact HAddrChecked
        end.
      - exact HAddrComp.
    }
    assert (HValComp :
      CountedComputationEvaluation n_val heap_addr env rho ev
        phi_val heap_val v).
    { unfold CountedComputationEvaluation. exact HVal. }
    eapply TraceCoveredByStaticEffect_weaken.
    + eapply TraceCoveredByStaticEffect_app3.
      * eapply (IH n_eval HCount).
        -- exact HCountAddr.
        -- exact HContext.
        -- match goal with
           | HAddrChecked : NCheckedTcExp gamma omega ea
               (TyRef (region_expr_to_type r) ?ty_cell) eff_a |- _ =>
               exact HAddrChecked
           end.
        -- exact HAddrComp.
        -- exact HResolveAddr.
      * eapply (IH n_eval HCount).
        -- exact HCountVal.
        -- exact HContextVal.
        -- match goal with
           | HValChecked : NCheckedTcExp gamma omega ev ?ty_cell eff_v |- _ =>
               exact HValChecked
           end.
        -- exact HValComp.
        -- exact HResolveVal.
      * apply TraceCoveredByStaticEffect_singleton.
    + apply StaticEffectIncluded_app3_singleton_front.
  - destruct
      (checked_store_counted_tynat_value_is_nat
        n_eval gamma omega heap env rho (EPlus e1 e2)
        (static_union eff1 eff2) phi heap_final v_final
        HContext HChecked HComp)
      as (n_final & HFinalNat).
    subst v_final.
    destruct
      (NResolveStaticEffect_static_union_inv
        rho eff1 eff2 eff_res HResolve)
      as (eff1_res & eff2_res & HEffRes &
        HResolve1 & HResolve2).
    subst eff_res.
    unfold CountedComputationEvaluation in HComp.
    destruct
      (EPlus_counted_decomposition
        n_eval heap env rho e1 e2 phi heap_final n_final HComp)
      as (n1_steps & n2_steps & phi1 & phi2 & n1 & n2 &
        heap1 & heap2 & HLeft & HRight & _HResult & HHeapFinal & HTrace &
        HCount1 & HCount2).
    assert (HLeftComp :
      CountedComputationEvaluation n1_steps heap env rho e1
        phi1 heap1 (VNat n1)).
    { unfold CountedComputationEvaluation. exact HLeft. }
    assert (HContextRight :
      CheckedStoreRuntimeContext gamma omega heap1 env rho).
    {
      eapply checked_store_counted_computation_store_runtime_context.
      - exact HContext.
      - match goal with
        | HLeftChecked : NCheckedTcExp gamma omega e1 TyNat eff1 |- _ =>
            exact HLeftChecked
        end.
      - exact HLeftComp.
    }
    assert (HRightComp :
      CountedComputationEvaluation n2_steps heap1 env rho e2
        phi2 heap2 (VNat n2)).
    { unfold CountedComputationEvaluation. exact HRight. }
    subst heap_final phi.
    eapply TraceCoveredByStaticEffect_app.
    + eapply (IH n_eval HCount).
      * exact HCount1.
      * exact HContext.
      * exact H.
      * exact HLeftComp.
      * exact HResolve1.
    + eapply (IH n_eval HCount).
      * exact HCount2.
      * exact HContextRight.
      * exact H0.
      * exact HRightComp.
      * exact HResolve2.
  - destruct
      (checked_store_counted_tynat_value_is_nat
        n_eval gamma omega heap env rho (EMinus e1 e2)
        (static_union eff1 eff2) phi heap_final v_final
        HContext HChecked HComp)
      as (n_final & HFinalNat).
    subst v_final.
    destruct
      (NResolveStaticEffect_static_union_inv
        rho eff1 eff2 eff_res HResolve)
      as (eff1_res & eff2_res & HEffRes &
        HResolve1 & HResolve2).
    subst eff_res.
    unfold CountedComputationEvaluation in HComp.
    destruct
      (EMinus_counted_decomposition
        n_eval heap env rho e1 e2 phi heap_final n_final HComp)
      as (n1_steps & n2_steps & phi1 & phi2 & n1 & n2 &
        heap1 & heap2 & HLeft & HRight & _HResult & HHeapFinal & HTrace &
        HCount1 & HCount2).
    assert (HLeftComp :
      CountedComputationEvaluation n1_steps heap env rho e1
        phi1 heap1 (VNat n1)).
    { unfold CountedComputationEvaluation. exact HLeft. }
    assert (HContextRight :
      CheckedStoreRuntimeContext gamma omega heap1 env rho).
    {
      eapply checked_store_counted_computation_store_runtime_context.
      - exact HContext.
      - exact H.
      - exact HLeftComp.
    }
    assert (HRightComp :
      CountedComputationEvaluation n2_steps heap1 env rho e2
        phi2 heap2 (VNat n2)).
    { unfold CountedComputationEvaluation. exact HRight. }
    subst heap_final phi.
    eapply TraceCoveredByStaticEffect_app.
    + eapply (IH n_eval HCount).
      * exact HCount1.
      * exact HContext.
      * exact H.
      * exact HLeftComp.
      * exact HResolve1.
    + eapply (IH n_eval HCount).
      * exact HCount2.
      * exact HContextRight.
      * exact H0.
      * exact HRightComp.
      * exact HResolve2.
  - destruct
      (checked_store_counted_tynat_value_is_nat
        n_eval gamma omega heap env rho (ETimes e1 e2)
        (static_union eff1 eff2) phi heap_final v_final
        HContext HChecked HComp)
      as (n_final & HFinalNat).
    subst v_final.
    destruct
      (NResolveStaticEffect_static_union_inv
        rho eff1 eff2 eff_res HResolve)
      as (eff1_res & eff2_res & HEffRes &
        HResolve1 & HResolve2).
    subst eff_res.
    unfold CountedComputationEvaluation in HComp.
    destruct
      (ETimes_counted_decomposition
        n_eval heap env rho e1 e2 phi heap_final n_final HComp)
      as (n1_steps & n2_steps & phi1 & phi2 & n1 & n2 &
        heap1 & heap2 & HLeft & HRight & _HResult & HHeapFinal & HTrace &
        HCount1 & HCount2).
    assert (HLeftComp :
      CountedComputationEvaluation n1_steps heap env rho e1
        phi1 heap1 (VNat n1)).
    { unfold CountedComputationEvaluation. exact HLeft. }
    assert (HContextRight :
      CheckedStoreRuntimeContext gamma omega heap1 env rho).
    {
      eapply checked_store_counted_computation_store_runtime_context.
      - exact HContext.
      - exact H.
      - exact HLeftComp.
    }
    assert (HRightComp :
      CountedComputationEvaluation n2_steps heap1 env rho e2
        phi2 heap2 (VNat n2)).
    { unfold CountedComputationEvaluation. exact HRight. }
    subst heap_final phi.
    eapply TraceCoveredByStaticEffect_app.
    + eapply (IH n_eval HCount).
      * exact HCount1.
      * exact HContext.
      * exact H.
      * exact HLeftComp.
      * exact HResolve1.
    + eapply (IH n_eval HCount).
      * exact HCount2.
      * exact HContextRight.
      * exact H0.
      * exact HRightComp.
      * exact HResolve2.
  - destruct
      (checked_store_counted_tybool_value_is_bool
        n_eval gamma omega heap env rho (EEq e1 e2)
        (static_union eff1 eff2) phi heap_final v_final
        HContext HChecked HComp)
      as (b_final & HFinalBool).
    subst v_final.
    destruct
      (NResolveStaticEffect_static_union_inv
        rho eff1 eff2 eff_res HResolve)
      as (eff1_res & eff2_res & HEffRes &
        HResolve1 & HResolve2).
    subst eff_res.
    unfold CountedComputationEvaluation in HComp.
    destruct
      (EEq_counted_decomposition
        n_eval heap env rho e1 e2 phi heap_final b_final HComp)
      as (n1_steps & n2_steps & phi1 & phi2 & n1 & n2 &
        heap1 & heap2 & HLeft & HRight & _HResult & HHeapFinal & HTrace &
        HCount1 & HCount2).
    assert (HLeftComp :
      CountedComputationEvaluation n1_steps heap env rho e1
        phi1 heap1 (VNat n1)).
    { unfold CountedComputationEvaluation. exact HLeft. }
    assert (HContextRight :
      CheckedStoreRuntimeContext gamma omega heap1 env rho).
    {
      eapply checked_store_counted_computation_store_runtime_context.
      - exact HContext.
      - exact H.
      - exact HLeftComp.
    }
    assert (HRightComp :
      CountedComputationEvaluation n2_steps heap1 env rho e2
        phi2 heap2 (VNat n2)).
    { unfold CountedComputationEvaluation. exact HRight. }
    subst heap_final phi.
    eapply TraceCoveredByStaticEffect_app.
    + eapply (IH n_eval HCount).
      * exact HCount1.
      * exact HContext.
      * exact H.
      * exact HLeftComp.
      * exact HResolve1.
    + eapply (IH n_eval HCount).
      * exact HCount2.
      * exact HContextRight.
      * exact H0.
      * exact HRightComp.
      * exact HResolve2.
  - eapply counted_immediate_silent_initial_return_static_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - eapply counted_immediate_silent_initial_return_static_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - eapply counted_immediate_silent_initial_return_static_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - destruct
      (EReadConc_counted_decomposition_static
        n_eval heap env rho e phi heap_final v_final HComp)
      as (n_e & phi_e & heap_e & r_loc & l &
        HExprComp & HCountExpr & HHeapFinal & HTrace).
    subst heap_final phi.
    eapply (IH n_eval HCount).
    + exact HCountExpr.
    + exact HContext.
    + match goal with
      | HExprChecked : NCheckedTcExp gamma omega e ?ty_ref eff |- _ =>
          exact HExprChecked
      end.
    + exact HExprComp.
    + exact HResolve.
  - destruct
      (EWriteConc_counted_decomposition_static
        n_eval heap env rho e phi heap_final v_final HComp)
      as (n_e & phi_e & heap_e & r_loc & l &
        HExprComp & HCountExpr & HHeapFinal & HTrace).
    subst heap_final phi.
    eapply (IH n_eval HCount).
    + exact HCountExpr.
    + exact HContext.
    + match goal with
      | HExprChecked : NCheckedTcExp gamma omega e ?ty_ref eff |- _ =>
          exact HExprChecked
      end.
    + exact HExprComp.
    + exact HResolve.
  - destruct
      (checked_store_counted_tyeffect_value_is_summary
        n_eval gamma omega heap env rho (EConcat e1 e2)
        (static_union eff1 eff2) phi heap_final v_final
        HContext HChecked HComp)
      as (theta & HFinalSummary).
    subst v_final.
    destruct
      (NResolveStaticEffect_static_union_inv
        rho eff1 eff2 eff_res HResolve)
      as (eff1_res & eff2_res & HEffRes &
        HResolve1 & HResolve2).
    subst eff_res.
    unfold CountedComputationEvaluation in HComp.
    destruct
      (EConcat_counted_decomposition
        n_eval heap env rho e1 e2 phi heap_final theta HComp)
      as (n1 & n2 & phi1 & phi2 & theta1 & theta2 &
        heap1 & heap2 & HLeft & HRight & _HTheta &
        HHeapFinal & HTrace & HCount1 & HCount2).
    assert (HLeftComp :
      CountedComputationEvaluation n1 heap env rho e1
        phi1 heap1 (VSummary theta1)).
    { unfold CountedComputationEvaluation. exact HLeft. }
    assert (HContextRight :
      CheckedStoreRuntimeContext gamma omega heap1 env rho).
    {
      eapply checked_store_counted_computation_store_runtime_context.
      - exact HContext.
      - exact H.
      - exact HLeftComp.
    }
    assert (HRightComp :
      CountedComputationEvaluation n2 heap1 env rho e2
        phi2 heap2 (VSummary theta2)).
    { unfold CountedComputationEvaluation. exact HRight. }
    subst heap_final phi.
    eapply TraceCoveredByStaticEffect_app.
    + eapply (IH n_eval HCount).
      * exact HCount1.
      * exact HContext.
      * exact H.
      * exact HLeftComp.
      * exact HResolve1.
    + eapply (IH n_eval HCount).
      * exact HCount2.
      * exact HContextRight.
      * exact H0.
      * exact HRightComp.
      * exact HResolve2.
  - eapply counted_immediate_silent_initial_return_static_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - eapply counted_immediate_silent_initial_return_static_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
Qed.

Theorem checked_store_computation_trace_soundness :
  CheckedStoreComputationTraceSoundnessGoal.
Proof.
  unfold CheckedStoreComputationTraceSoundnessGoal,
    CheckedComputationTraceSoundnessFor.
  intros gamma omega heap env rho HContext expr ty eff
    phi heap_final v_final eff_res HChecked HComp HResolve.
  unfold ComputationEvaluation in HComp.
  destruct
    (NSteps_to_NStepsN
      (NInitialState heap env rho expr)
      phi
      (StDone heap_final v_final)
      HComp)
    as (n & HCompN).
  eapply
    (checked_store_computation_trace_soundness_below (S n) n);
    eauto; lia.
Qed.

Theorem checked_store_context_case_dispatch :
  forall n gamma omega heap env rho expr summary_expr
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    CheckedStoreSummaryValueSoundnessBelow n ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    NCheckedBackTriangle gamma omega expr summary_expr ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho expr
      phi heap_final v_final ->
    SummaryEvaluation heap env rho summary_expr
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho expr summary_expr
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HSummaryValueBelow HComputationTraceSound
    HSummaryTraceSound HBack HContext HComp HSummary.
  pose proof HBack as HBackCase.
  destruct HBack.
  - eapply counted_immediate_silent_initial_return_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - eapply counted_immediate_silent_initial_return_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - eapply counted_immediate_silent_initial_return_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - eapply counted_immediate_silent_initial_return_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - eapply counted_immediate_silent_initial_return_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - eapply EMuApp_checked_store_context_case_from_below; eauto.
  - eapply EPairPar_checked_store_context_case_from_below; eauto.
  - eapply ERgnApp_checked_store_context_case_from_below; eauto.
  - eapply ECond_checked_store_context_case_from_below; eauto.
  - eapply ERef_checked_store_context_case_from_below; eauto.
  - eapply EDeref_checked_store_context_case_from_below; eauto.
  - eapply EAssign_checked_store_context_case_from_below; eauto.
  - eapply EPlus_checked_store_context_case_from_below; eauto.
  - eapply EMinus_checked_store_context_case_from_below; eauto.
  - eapply ETimes_checked_store_context_case_from_below; eauto.
  - eapply EEq_checked_store_context_case_from_below; eauto.
  - unfold SummaryEvaluation in HSummary.
    destruct
      (ETop_terminal_summary
        heap env rho phi_summary heap_summary theta HSummary)
      as (_HHeapSummary & HTheta & _HTraceSummary).
    subst theta.
    apply trace_covered_top.
Qed.

Definition CheckedStoreContextAndSummaryValueSoundnessBelow
    (n : nat) : Prop :=
  CheckedStoreContextSmallStepCorrectnessBelow n /\
  CheckedStoreSummaryValueSoundnessBelow n.

(* Simultaneous induction core: the trace premise is discharged below by
   checked_store_computation_trace_soundness before exposing terminal theorems. *)
Local Theorem checked_store_context_and_summary_value_below_from_trace_soundness :
  CheckedStoreComputationTraceSoundnessGoal ->
  forall n,
    CheckedStoreContextAndSummaryValueSoundnessBelow n.
Proof.
  intros HComputationTraceGoal n.
  pose proof
    (checked_store_summary_trace_soundness_from_computation
      HComputationTraceGoal)
    as HSummaryTraceGoal.
  induction n as [n IH] using lt_wf_ind.
  split.
  - unfold CheckedStoreContextSmallStepCorrectnessBelow.
    intros n_child gamma omega heap env rho expr summary_expr
      phi heap_final v_final phi_summary heap_summary theta
      HCount HBack HContext HComp HSummary.
    destruct (IH n_child HCount) as (HBelowChild & HSummaryValueChild).
    eapply checked_store_context_case_dispatch.
    + exact HBelowChild.
    + exact HSummaryValueChild.
    + eapply CheckedComputationTraceSoundnessFor_from_store_goal;
        eauto.
    + eapply CheckedSummaryTraceSoundnessFor_from_store_goal;
        eauto.
    + exact HBack.
    + exact HContext.
    + exact HComp.
    + exact HSummary.
  - unfold CheckedStoreSummaryValueSoundnessBelow.
    intros n_child gamma omega heap env rho expr summary_expr eff
      phi heap_summary theta HCount HBack HCheckedSummary HContext
      HComp.
    pose proof HBack as HBackCase.
    destruct (IH n_child HCount) as (HBelowChild & HSummaryValueChild).
    pose proof
      (CheckedSummaryTraceSoundnessFor_from_store_goal
        gamma omega heap env rho HSummaryTraceGoal HContext)
      as HSummaryTraceSound.
    pose proof
      (CheckedComputationTraceSoundnessFor_from_store_goal
        gamma omega heap env rho HComputationTraceGoal HContext)
      as HComputationTraceSound.
    destruct HBack.
    + eapply counted_EEmpty_summary_trace_covered; eauto.
    + eapply counted_EEmpty_summary_trace_covered; eauto.
    + eapply counted_EEmpty_summary_trace_covered; eauto.
    + eapply counted_EEmpty_summary_trace_covered; eauto.
    + eapply counted_EEmpty_summary_trace_covered; eauto.
    + destruct
        (NCBT_App_components _ _ _ _ HBackCase)
        as (_ty_mu & _eff_mu & eff_eff_app & _ty_ef & _ty_ea &
          _eff_ef & _eff_ea & _HCheckedApp & HCheckedEffApp &
          _HCheckedFun & _HCheckedArg & HStaticEff &
          _HStaticFun & _HStaticArg & _HBackFun & _HBackArg).
      destruct
        (checked_store_counted_computation_heap_neutral
          n_child gamma omega heap env rho
          (EEffApp ef ea) TyEffect eff_eff_app
          phi heap_summary (VSummary theta)
          HContext HComputationTraceSound HCheckedEffApp
          HStaticEff HComp)
        as (HHeapSummary & _HNeutralSummary).
      subst heap_summary.
      eapply
        (EEffApp_counted_checked_summary_trace_covered_from_store_entry_at
          n_child gamma omega heap env rho ef ea phi theta).
      * exact HBelowChild.
      * exact HSummaryValueChild.
      * exact HBackCase.
      * exact HContext.
      * exact HSummaryTraceSound.
      * exact HComp.
    + destruct
        (NCBT_PairPar_components _ _ _ _ _ _ HBackCase)
        as (_ty1 & _ty2 & _eff1 & _eff2 &
          _eff_summary1 & _eff_summary2 &
          _HCheckedLeft & _HCheckedRight &
          _HCheckedSummary1 & _HCheckedSummary2 &
          _HStaticNeutral1 & _HStaticNeutral2 &
          _HNoAllocLeft & _HNoAllocRight &
          HBackLeft & HBackRight).
      destruct
        (NCheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBackLeft)
        as (eff_left_summary & HCheckedLeftSummary & _).
      destruct
        (NCheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBackRight)
        as (eff_right_summary & HCheckedRightSummary & _).
      eapply
        (checked_store_summary_value_concat_from_below
          n_child gamma omega heap env rho
          (EMuApp ef1 ea1) (EMuApp ef2 ea2)
          (EEffApp ef1 ea1) (EEffApp ef2 ea2)
          eff_left_summary eff_right_summary
          phi heap_summary theta).
      * exact HSummaryValueChild.
      * exact HBackLeft.
      * exact HBackRight.
      * exact HCheckedLeftSummary.
      * exact HCheckedRightSummary.
      * exact HContext.
      * exact HComp.
    + eapply counted_EEmpty_summary_trace_covered; eauto.
    + destruct
        (NCBT_Cond_components _ _ _ _ _ _ _ HBackCase)
        as (eff_e_cond & _ty & _ty_t & _ty_f & _eff_et & _eff_ef &
          _HCheckedCond & HCheckedCondition & _HCheckedThen &
          _HCheckedElse & HBackCondition & HBackThen & HBackElse).
      unfold CountedComputationEvaluation in HComp.
      destruct
        (ECond_counted_decomposition
          n_child heap env rho e efft efff
          phi heap_summary (VSummary theta) HComp)
        as (n_cond & n_branch & phi_cond & b & heap_cond &
          phi_branch & HCond & HBranch & HTrace & HCountCond &
          HCountBranch).
      assert (HCondComp :
        CountedComputationEvaluation n_cond heap env rho e
          phi_cond heap_cond (VBool b)).
      {
        unfold CountedComputationEvaluation.
        exact HCond.
      }
      assert (HCoveredCond :
        TraceCoveredBySummary phi_cond
          (SummarySet ([] : list ComputedAction))).
      {
        eapply
          (HBelowChild n_cond gamma omega heap env rho e EEmpty
            phi_cond heap_cond (VBool b)
            ([] : Trace) heap
            (SummarySet ([] : list ComputedAction))).
        - exact HCountCond.
        - exact HBackCondition.
        - exact HContext.
        - exact HCondComp.
        - apply EEmpty_summary_evaluation.
      }
      pose proof
        (trace_covered_empty_summary_nil phi_cond HCoveredCond)
        as HCondNil.
      assert (HContextBranch :
        CheckedStoreRuntimeContext gamma omega heap_cond env rho).
      {
        eapply
          (checked_store_counted_computation_store_runtime_context
            n_cond gamma omega heap env rho e TyBool eff_e_cond
            phi_cond heap_cond (VBool b));
          eauto.
      }
      subst phi.
      rewrite HCondNil.
      simpl.
      destruct b.
      * destruct
          (NCheckedBackTriangle_summary_checked_heap_neutral
            _ _ _ _ HBackThen)
          as (eff_then_summary & HCheckedThenSummary & _).
        eapply HSummaryValueChild.
        -- exact HCountBranch.
        -- exact HBackThen.
        -- exact HCheckedThenSummary.
        -- exact HContextBranch.
        -- unfold CountedComputationEvaluation in *.
           simpl in HBranch.
           exact HBranch.
      * destruct
          (NCheckedBackTriangle_summary_checked_heap_neutral
            _ _ _ _ HBackElse)
          as (eff_else_summary & HCheckedElseSummary & _).
        eapply HSummaryValueChild.
        -- exact HCountBranch.
        -- exact HBackElse.
        -- exact HCheckedElseSummary.
        -- exact HContextBranch.
        -- unfold CountedComputationEvaluation in *.
           simpl in HBranch.
           exact HBranch.
    + destruct
        (NCBT_Ref_components _ _ _ _ _ HBackCase)
        as (_ty & _static & _ty_ref & _eff_ref &
          _HCheckedExpr & _HCheckedRef & HBackExpr).
      destruct
        (NCheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBackExpr)
        as (eff_expr_summary & HCheckedExprSummary & _).
      unfold CountedComputationEvaluation in HComp.
      destruct
        (EConcat_counted_decomposition
          n_child heap env rho eff0 (EAllocAbs r)
          phi heap_summary theta HComp)
        as (n_expr & n_abs & phi_expr & phi_abs &
          theta_expr & theta_abs & heap_expr & heap_abs &
          HExprSummary & HAbsSummary & HTheta & HHeapFinal &
          HTrace & HCountExpr & HCountAbs).
      subst theta heap_summary phi.
      assert (HCompExpr :
        CountedComputationEvaluation n_expr heap env rho eff0
          phi_expr heap_expr (VSummary theta_expr)).
      {
        unfold CountedComputationEvaluation.
        exact HExprSummary.
      }
      assert (HCompAbs :
        CountedComputationEvaluation n_abs heap_expr env rho
          (EAllocAbs r) phi_abs heap_abs (VSummary theta_abs)).
      {
        unfold CountedComputationEvaluation.
        exact HAbsSummary.
      }
      assert (HCoveredExpr : TraceCoveredBySummary phi_expr theta_expr).
      {
        eapply HSummaryValueChild.
        - exact HCountExpr.
        - exact HBackExpr.
        - exact HCheckedExprSummary.
        - exact HContext.
        - exact HCompExpr.
      }
      assert (HCoveredAbs : TraceCoveredBySummary phi_abs theta_abs).
      {
        eapply counted_EAllocAbs_summary_trace_covered; eauto.
      }
      eapply trace_covered_app_summary_union; eauto.
    + destruct
        (NCBT_Deref_components _ _ _ _ _ HBackCase)
        as (_ty & _static & _ty_deref & _eff_deref &
          _HCheckedExpr & _HCheckedDeref & HBackExpr).
      destruct
        (NCheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBackExpr)
        as (eff_expr_summary & HCheckedExprSummary & _).
      unfold CountedComputationEvaluation in HComp.
      destruct
        (EConcat_counted_decomposition
          n_child heap env rho eff0 (EReadAbs r)
          phi heap_summary theta HComp)
        as (n_expr & n_abs & phi_expr & phi_abs &
          theta_expr & theta_abs & heap_expr & heap_abs &
          HExprSummary & HAbsSummary & HTheta & HHeapFinal &
          HTrace & HCountExpr & HCountAbs).
      subst theta heap_summary phi.
      assert (HCompExpr :
        CountedComputationEvaluation n_expr heap env rho eff0
          phi_expr heap_expr (VSummary theta_expr)).
      {
        unfold CountedComputationEvaluation.
        exact HExprSummary.
      }
      assert (HCompAbs :
        CountedComputationEvaluation n_abs heap_expr env rho
          (EReadAbs r) phi_abs heap_abs (VSummary theta_abs)).
      {
        unfold CountedComputationEvaluation.
        exact HAbsSummary.
      }
      assert (HCoveredExpr : TraceCoveredBySummary phi_expr theta_expr).
      {
        eapply HSummaryValueChild.
        - exact HCountExpr.
        - exact HBackExpr.
        - exact HCheckedExprSummary.
        - exact HContext.
        - exact HCompExpr.
      }
      assert (HCoveredAbs : TraceCoveredBySummary phi_abs theta_abs).
      {
        eapply counted_EReadAbs_summary_trace_covered; eauto.
      }
      eapply trace_covered_app_summary_union; eauto.
    + destruct
        (NCBT_Assign_components _ _ _ _ _ _ _ HBackCase)
        as (_ty_addr & _static_addr & _ty_assign & _eff_assign &
          _HCheckedAddr & _HCheckedAssign & _HNeutralAddr &
          HBackAddr & HBackVal).
      destruct
        (NCheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBackAddr)
        as (eff_addr_summary & HCheckedAddrSummary & _).
      destruct
        (NCheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBackVal)
        as (eff_val_summary & HCheckedValSummary & _).
      unfold CountedComputationEvaluation in HComp.
      destruct
        (EConcat_counted_decomposition
          n_child heap env rho eff1 (EConcat eff2 (EWriteAbs r))
          phi heap_summary theta HComp)
        as (n_addr & n_rest & phi_addr & phi_rest &
          theta_addr & theta_rest & heap_addr & heap_rest &
          HAddrSummary & HRestSummary & HTheta & HHeapFinal &
          HTrace & HCountAddr & HCountRest).
      destruct
        (EConcat_counted_decomposition
          n_rest heap_addr env rho eff2 (EWriteAbs r)
          phi_rest heap_rest theta_rest HRestSummary)
        as (n_val & n_abs & phi_val & phi_abs &
          theta_val & theta_abs & heap_val & heap_abs &
          HValSummary & HAbsSummary & HThetaRest & HHeapRest &
          HTraceRest & HCountVal & HCountAbs).
      subst theta_rest heap_rest phi_rest theta heap_summary phi.
      assert (HCompAddr :
        CountedComputationEvaluation n_addr heap env rho eff1
          phi_addr heap_addr (VSummary theta_addr)).
      {
        unfold CountedComputationEvaluation.
        exact HAddrSummary.
      }
      assert (HContextVal :
        CheckedStoreRuntimeContext gamma omega heap_addr env rho).
      {
        eapply
          (checked_store_counted_computation_store_runtime_context
            n_addr gamma omega heap env rho eff1 TyEffect
            eff_addr_summary phi_addr heap_addr
            (VSummary theta_addr));
          eauto.
      }
      assert (HCompVal :
        CountedComputationEvaluation n_val heap_addr env rho eff2
          phi_val heap_val (VSummary theta_val)).
      {
        unfold CountedComputationEvaluation.
        exact HValSummary.
      }
      assert (HCompAbs :
        CountedComputationEvaluation n_abs heap_val env rho
          (EWriteAbs r) phi_abs heap_abs (VSummary theta_abs)).
      {
        unfold CountedComputationEvaluation.
        exact HAbsSummary.
      }
      assert (HCoveredAddr :
        TraceCoveredBySummary phi_addr theta_addr).
      {
        eapply HSummaryValueChild.
        - exact HCountAddr.
        - exact HBackAddr.
        - exact HCheckedAddrSummary.
        - exact HContext.
        - exact HCompAddr.
      }
      assert (HCoveredVal :
        TraceCoveredBySummary phi_val theta_val).
      {
        eapply
          (HSummaryValueChild
            n_val gamma omega heap_addr env rho e2 eff2
            eff_val_summary phi_val heap_val theta_val).
        - lia.
        - exact HBackVal.
        - exact HCheckedValSummary.
        - exact HContextVal.
        - exact HCompVal.
      }
      assert (HCoveredAbs :
        TraceCoveredBySummary phi_abs theta_abs).
      {
        eapply counted_EWriteAbs_summary_trace_covered; eauto.
      }
      eapply trace_covered_app_summary_union; eauto.
      eapply trace_covered_app_summary_union; eauto.
    + destruct
        (NCheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBack1)
        as (eff_left_summary & HCheckedLeftSummary & _).
      destruct
        (NCheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBack2)
        as (eff_right_summary & HCheckedRightSummary & _).
      eapply
        (checked_store_summary_value_concat_from_below
          n_child gamma omega heap env rho e1 e2 eff1 eff2
          eff_left_summary eff_right_summary phi heap_summary theta).
      * exact HSummaryValueChild.
      * exact HBack1.
      * exact HBack2.
      * exact HCheckedLeftSummary.
      * exact HCheckedRightSummary.
      * exact HContext.
      * exact HComp.
    + destruct
        (NCheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBack1)
        as (eff_left_summary & HCheckedLeftSummary & _).
      destruct
        (NCheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBack2)
        as (eff_right_summary & HCheckedRightSummary & _).
      eapply
        (checked_store_summary_value_concat_from_below
          n_child gamma omega heap env rho e1 e2 eff1 eff2
          eff_left_summary eff_right_summary phi heap_summary theta).
      * exact HSummaryValueChild.
      * exact HBack1.
      * exact HBack2.
      * exact HCheckedLeftSummary.
      * exact HCheckedRightSummary.
      * exact HContext.
      * exact HComp.
    + destruct
        (NCheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBack1)
        as (eff_left_summary & HCheckedLeftSummary & _).
      destruct
        (NCheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBack2)
        as (eff_right_summary & HCheckedRightSummary & _).
      eapply
        (checked_store_summary_value_concat_from_below
          n_child gamma omega heap env rho e1 e2 eff1 eff2
          eff_left_summary eff_right_summary phi heap_summary theta).
      * exact HSummaryValueChild.
      * exact HBack1.
      * exact HBack2.
      * exact HCheckedLeftSummary.
      * exact HCheckedRightSummary.
      * exact HContext.
      * exact HComp.
    + destruct
        (NCheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBack1)
        as (eff_left_summary & HCheckedLeftSummary & _).
      destruct
        (NCheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBack2)
        as (eff_right_summary & HCheckedRightSummary & _).
      eapply
        (checked_store_summary_value_concat_from_below
          n_child gamma omega heap env rho e1 e2 eff1 eff2
          eff_left_summary eff_right_summary phi heap_summary theta).
      * exact HSummaryValueChild.
      * exact HBack1.
      * exact HBack2.
      * exact HCheckedLeftSummary.
      * exact HCheckedRightSummary.
      * exact HContext.
      * exact HComp.
    + eapply counted_ETop_summary_trace_covered; eauto.
Qed.

Local Theorem checked_store_context_small_step_correctness_below_from_trace_soundness :
  CheckedStoreComputationTraceSoundnessGoal ->
  forall n,
    CheckedStoreContextSmallStepCorrectnessBelow n.
Proof.
  intros HComputationTraceGoal n.
  destruct
    (checked_store_context_and_summary_value_below_from_trace_soundness
      HComputationTraceGoal n)
    as (HBelow & _).
  exact HBelow.
Qed.

Local Theorem checked_store_summary_value_soundness_below_from_trace_soundness :
  CheckedStoreComputationTraceSoundnessGoal ->
  forall n,
    CheckedStoreSummaryValueSoundnessBelow n.
Proof.
  intros HComputationTraceGoal n.
  destruct
    (checked_store_context_and_summary_value_below_from_trace_soundness
      HComputationTraceGoal n)
    as (_ & HSummaryValueBelow).
  exact HSummaryValueBelow.
Qed.

Theorem checked_context_terminal_correctness_from_store_dispatch :
  CheckedContextTerminalCorrectnessGoal.
Proof.
  eapply checked_context_terminal_correctness_from_store_below.
  eapply checked_store_context_small_step_correctness_below_from_trace_soundness;
    exact checked_store_computation_trace_soundness.
Qed.

Theorem checked_context_structured_terminal_correctness_from_store_dispatch :
  CheckedContextStructuredTerminalCorrectnessGoal.
Proof.
  eapply checked_context_structured_terminal_correctness_from_store_below.
  eapply checked_store_context_small_step_correctness_below_from_trace_soundness;
    exact checked_store_computation_trace_soundness.
Qed.
