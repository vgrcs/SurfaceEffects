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
Require Import theories.SmallStep.Soundness.CheckedExecution.
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

Local Ltac checked_runtime_non_pairpar_step :=
  eapply CheckedStepRuntime;
  [ eauto using
      StepConcat, StepConcatL, StepConcatR,
      StepMuApp, StepMuAppFun, StepMuAppArg,
      StepEffApp, StepEffAppFun, StepEffAppArg,
      StepRgnApp, StepRgnAppReturn,
      StepCond, StepCondTrue, StepCondFalse,
      StepRef, StepRefReturn,
      StepDeref, StepDerefReturn,
      StepAssign, StepAssignLoc, StepAssignVal,
      StepPlus, StepPlusL, StepPlusR,
      StepMinus, StepMinusL, StepMinusR,
      StepTimes, StepTimesL, StepTimesR,
      StepEq, StepEqL, StepEqR
  | intros HFail;
    destruct HFail as
      (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & HState & _);
    discriminate
  | intros HRun; exact HRun ].

Lemma counted_immediate_silent_initial_return_trace_nil :
  forall n heap env rho expr phi heap_final v_final,
    (forall label state',
      Step (InitialState heap env rho expr) label state' ->
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
  | HStep : Step (InitialState heap env rho expr) ?label ?state',
    HTail : StepsN _ ?state' ?phi_tail
      (StDone heap_final v_final) |- _ =>
      destruct (HImmediate label state' HStep)
        as (v0 & HLabel & HState);
      subst label state';
      destruct
        (Steps_return_done_inv
          heap v0 phi_tail heap_final v_final
          (StepsN_to_Steps
            _ _ _ _ HTail))
        as (_HHeap & _HVal & HTraceTail);
      subst phi_tail
  end.
  reflexivity.
Qed.

Lemma counted_immediate_silent_initial_return_covered :
  forall n heap env rho expr phi heap_final v_final theta,
    (forall label state',
      Step (InitialState heap env rho expr) label state' ->
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
      (StepsN_to_Steps _ _ _ _ HComp))
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
      (StepsN_to_Steps _ _ _ _ HComp))
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
      (StepsN_to_Steps _ _ _ _ HComp))
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
      (StepsN_to_Steps _ _ _ _ HComp))
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
      (StepsN_to_Steps _ _ _ _ HComp))
    as (_ & _ & _ & _ & HTrace).
  subst phi.
  apply trace_covered_nil.
Qed.

Lemma checked_store_summary_value_concat_from_below :
  forall n gamma omega heap env rho source1 source2 summary1 summary2
    eff_summary1 eff_summary2 phi heap_final theta,
    CheckedStoreSummaryValueSoundnessBelow n ->
    CheckedBackTriangle gamma omega source1 summary1 ->
    CheckedBackTriangle gamma omega source2 summary2 ->
    CheckedTcExp gamma omega summary1 TyEffect eff_summary1 ->
    CheckedTcExp gamma omega summary2 TyEffect eff_summary2 ->
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
    CheckedTcExp gamma omega ef
      (TyArrow ty_arg eff_body ty_body eff_summary) eff_f ->
    CheckedTcExp gamma omega ea ty_arg eff_a ->
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
      CheckedTcExp
        ((x, ty_arg_body) ::
          (f, TyArrow ty_arg_body eff_body_body
            ty_body_body eff_summary_body) ::
          gamma_body)
        omega_body ec ty_body_body eff_body_body /\
      CheckedTcExp
        ((x, ty_arg_body) ::
          (f, TyArrow ty_arg_body eff_body_body
            ty_body_body eff_summary_body) ::
          gamma_body)
        omega_body ee TyEffect eff_summary_body /\
      CheckedBackTriangle
        ((x, ty_arg_body) ::
          (f, TyArrow ty_arg_body eff_body_body
            ty_body_body eff_summary_body) ::
          gamma_body)
        omega_body ec ee /\
      ResolveStaticEffect closure_rho eff_body_body eff_body_res /\
      ResolveStaticEffect closure_rho eff_summary_body
        eff_summary_res /\
      ResolveTy rho
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
    eapply StepsN_to_Steps. exact HFun.
  }
  assert (HArgComp :
    ComputationEvaluation heap_fun env rho ea phi_arg heap_arg arg).
  {
    unfold ComputationEvaluation, CountedComputationEvaluation in *.
    eapply StepsN_to_Steps. exact HArg.
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
    (StoreResolvedValShape_closure_inv
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
    eapply ResolveTy_deterministic; eauto.
  }
  assert (HValFunArrow :
    StoreResolvedValShape store
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
      unfold StoreResolvedRuntimeShape.
      split; [exact HBounded |].
      split; [exact HHeap |].
      eapply StoreResolvedEnvShape_extend with
        (ty_res := ty_arg_body_res).
      * exact HResolveClosureArg.
      * rewrite <- HArgResEq. exact HValArg.
      * eapply StoreResolvedEnvShape_extend with
          (ty_res :=
            TyArrow ty_arg_body_res eff_body_res
              ty_body_res eff_summary_res).
        -- eapply Resolve_Arrow; eauto.
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
    CheckedTcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
    eval_region rho r = Some r_val ->
    ResolveStaticEffect rho (open_static_effect r eff_body)
      eff_open_res ->
    CountedComputationEvaluation n_fun heap env rho er
      phi_fun heap_fun
      (VRegionClosure closure_env closure_rho x e) ->
    exists gamma_body omega_body ty_body eff_body_inner,
      CheckedStoreRuntimeContext gamma_body (x :: omega_body)
        heap_fun closure_env
        (rho_extend x r_val closure_rho) /\
      CheckedTcExp gamma_body (x :: omega_body)
        e ty_body eff_body_inner /\
      ResolveStaticEffect (rho_extend x r_val closure_rho)
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
    (StoreResolvedValShape_region_closure_inv
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
    (ResolveStaticEffect_open_static_effect
      rho r eff_body eff_body_res r_val HRgn HResolveForallEff)
    as HResolveOpenExpected.
  pose proof
    (ResolveStaticEffect_deterministic
      rho (open_static_effect r eff_body)
      eff_open_res
      (open_static_effect_type (region_const_type r_val)
        eff_body_res)
      HResolveOpen HResolveOpenExpected)
    as HOpenEq.
  subst eff_open_res.
  pose proof
    (CheckedRegionBody_checked
      x gamma_body omega_body e ty_body_inner eff_body_inner
      HBodyChecked)
    as HCheckedBody.
  pose proof
    (CheckedTcExp_eff_wf
      gamma_body (x :: omega_body) e ty_body_inner
      eff_body_inner HCheckedBody)
    as HBodyEffWF.
  assert (HResolveBody :
    ResolveStaticEffect (rho_extend x r_val closure_rho)
      eff_body_inner
      (open_static_effect_type (region_const_type r_val)
        eff_body_res)).
  {
    unfold StaticEffectWF in HBodyEffWF.
    unfold close_static_effect, open_static_effect_type in *.
    eapply ResolveStaticEffect_rho_extend_close_static_effect_at;
      eauto.
  }
  exists gamma_body, omega_body, ty_body_inner, eff_body_inner.
  split.
  - split.
    + exists store_fun.
      unfold StoreResolvedRuntimeShape.
      split; [exact HBoundedFun |].
      split; [exact HHeapFun |].
      eapply StoreResolvedEnvShape_extend_fresh;
        eauto using
          CheckedRegionBody_fresh,
          CheckedRegionBody_ctx_wf.
    + eapply RhoModels_extend; eauto.
  - split; [exact HCheckedBody |].
    exact HResolveBody.
Qed.

Lemma resolved_alloc_action_from_eval_region :
  forall rho r r_val action,
    eval_region rho r = Some r_val ->
    ResolveStaticAction rho (SAlloc (region_expr_to_type r)) action ->
    action = SAlloc (region_const_type r_val).
Proof.
  intros rho r r_val action HRgn HResolve.
  pose proof
    (ResolveStaticAction_deterministic
      rho (SAlloc (region_expr_to_type r)) action
      (SAlloc (region_const_type r_val))
      HResolve
      (Resolve_SAlloc rho (region_expr_to_type r)
        (region_const_type r_val)
        (ResolveRegionType_region_expr_to_type rho r r_val HRgn)))
    as HAction.
  exact HAction.
Qed.

Lemma resolved_read_action_from_eval_region :
  forall rho r r_val action,
    eval_region rho r = Some r_val ->
    ResolveStaticAction rho (SRead (region_expr_to_type r)) action ->
    action = SRead (region_const_type r_val).
Proof.
  intros rho r r_val action HRgn HResolve.
  pose proof
    (ResolveStaticAction_deterministic
      rho (SRead (region_expr_to_type r)) action
      (SRead (region_const_type r_val))
      HResolve
      (Resolve_SRead rho (region_expr_to_type r)
        (region_const_type r_val)
        (ResolveRegionType_region_expr_to_type rho r r_val HRgn)))
    as HAction.
  exact HAction.
Qed.

Lemma resolved_write_action_from_eval_region :
  forall rho r r_val action,
    eval_region rho r = Some r_val ->
    ResolveStaticAction rho (SWrite (region_expr_to_type r)) action ->
    action = SWrite (region_const_type r_val).
Proof.
  intros rho r r_val action HRgn HResolve.
  pose proof
    (ResolveStaticAction_deterministic
      rho (SWrite (region_expr_to_type r)) action
      (SWrite (region_const_type r_val))
      HResolve
      (Resolve_SWrite rho (region_expr_to_type r)
        (region_const_type r_val)
        (ResolveRegionType_region_expr_to_type rho r r_val HRgn)))
    as HAction.
  exact HAction.
Qed.

Lemma KReadConc_loc_terminal_trace_nil :
  forall heap r l phi heap_final v_final,
    Steps
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
      (Steps_return_done_inv
        heap
        (VSummary (SummarySet [CReadConc r l]))
        phi_tail heap_final v_final HTail)
      as (HHeap & _HVal & HTrace).
    simpl in *.
    split; assumption.
Qed.

Lemma KWriteConc_loc_terminal_trace_nil :
  forall heap r l phi heap_final v_final,
    Steps
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
      (Steps_return_done_inv
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
    (StepsN_known_first_step_terminal_inv
      n
      (InitialState heap env rho (EReadConc e))
      LSilent
      (StEval heap env rho e (KReadConc KDone))
      phi heap_final v_final
      (StepReadConc heap env rho e KDone)
      HComp)
    as (n_tail & phi_tail & _HStart & HExprWithKont & HTraceStart).
  destruct
    (StepsN_append_kont_terminal_split_counted
      n_tail
      (StEval heap env rho e (KReadConc KDone))
      phi_tail heap_final v_final HExprWithKont
      (InitialState heap env rho e)
      (KReadConc KDone)
      eq_refl)
    as (n_e & n_after & phi_e & heap_e & v_loc &
      phi_after & HExpr & HAfter & HCountExpr & HTraceExpr).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KReadConc_terminal_value_is_loc
        heap_e v_loc KDone phi_after heap_final v_final
        (StepsN_to_Steps _ _ _ _ HAfter))
      as (r_loc & l & HLoc).
    subst v_loc.
    destruct
      (KReadConc_loc_terminal_trace_nil
        heap_e r_loc l phi_after heap_final v_final
        (StepsN_to_Steps _ _ _ _ HAfter))
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
    (StepsN_known_first_step_terminal_inv
      n
      (InitialState heap env rho (EWriteConc e))
      LSilent
      (StEval heap env rho e (KWriteConc KDone))
      phi heap_final v_final
      (StepWriteConc heap env rho e KDone)
      HComp)
    as (n_tail & phi_tail & _HStart & HExprWithKont & HTraceStart).
  destruct
    (StepsN_append_kont_terminal_split_counted
      n_tail
      (StEval heap env rho e (KWriteConc KDone))
      phi_tail heap_final v_final HExprWithKont
      (InitialState heap env rho e)
      (KWriteConc KDone)
      eq_refl)
    as (n_e & n_after & phi_e & heap_e & v_loc &
      phi_after & HExpr & HAfter & HCountExpr & HTraceExpr).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KWriteConc_terminal_value_is_loc
        heap_e v_loc KDone phi_after heap_final v_final
        (StepsN_to_Steps _ _ _ _ HAfter))
      as (r_loc & l & HLoc).
    subst v_loc.
    destruct
      (KWriteConc_loc_terminal_trace_nil
        heap_e r_loc l phi_after heap_final v_final
        (StepsN_to_Steps _ _ _ _ HAfter))
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
      Step (InitialState heap env rho expr) label state' ->
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
    CheckedTcExp gamma omega expr TyEffect eff ->
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
    eapply ResolveTy_deterministic.
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
    CheckedTcExp gamma omega expr TyNat eff ->
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
    eapply ResolveTy_deterministic.
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
    CheckedTcExp gamma omega expr TyBool eff ->
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
    eapply ResolveTy_deterministic.
    - exact HResolveTy.
    - constructor.
  }
  subst ty_res.
  inversion HVal; subst.
  exists b.
  reflexivity.
Qed.

Lemma checked_execution_counted_to_counted :
  forall n heap env rho expr phi heap_final v_final,
    CheckedCountedComputationEvaluation n heap env rho expr
      phi heap_final v_final ->
    CountedComputationEvaluation n heap env rho expr
      phi heap_final v_final.
Proof.
  intros n heap env rho expr phi heap_final v_final HComp.
  unfold CheckedCountedComputationEvaluation,
    CountedComputationEvaluation in *.
  eapply CheckedStepsN_to_StepsN_done.
  exact HComp.
Qed.

Lemma checked_execution_counted_immediate_silent_initial_return_covered :
  forall n heap env rho expr phi heap_final v_final theta,
    (forall label state',
      Step (InitialState heap env rho expr) label state' ->
      exists v0,
        label = LSilent /\
        state' = StReturn heap v0 KDone) ->
    CheckedCountedComputationEvaluation n heap env rho expr
      phi heap_final v_final ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n heap env rho expr phi heap_final v_final theta
    HImmediate HComp.
  eapply counted_immediate_silent_initial_return_covered.
  - exact HImmediate.
  - eapply checked_execution_counted_to_counted.
    exact HComp.
Qed.

Lemma checked_execution_store_runtime_context_after_counted :
  forall n gamma omega heap env rho expr ty eff phi heap_final v_final,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedTcExp gamma omega expr ty eff ->
    CheckedCountedComputationEvaluation n heap env rho expr
      phi heap_final v_final ->
    CheckedStoreRuntimeContext gamma omega heap_final env rho.
Proof.
  intros n gamma omega heap env rho expr ty eff phi heap_final v_final
    HContext HChecked HComp.
  eapply
    (checked_store_counted_computation_store_runtime_context
      n gamma omega heap env rho expr ty eff phi heap_final v_final);
    eauto.
  eapply checked_execution_counted_to_counted.
  exact HComp.
Qed.

Lemma checked_execution_store_counted_computation_heap_neutral :
  forall n gamma omega heap env rho expr ty eff phi heap' v,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CheckedTcExp gamma omega expr ty eff ->
    static_heap_neutral eff ->
    CheckedCountedComputationEvaluation n heap env rho expr phi heap' v ->
    heap' = heap /\ HeapNeutralTrace phi.
Proof.
  intros n gamma omega heap env rho expr ty eff phi heap' v
    HContext HSound HChecked HHeapNeutral HComp.
  eapply
    (checked_store_counted_computation_heap_neutral
      n gamma omega heap env rho expr ty eff phi heap' v);
    eauto.
  eapply checked_execution_counted_to_counted.
  exact HComp.
Qed.

Lemma checked_execution_store_counted_tyeffect_value_is_summary :
  forall n gamma omega heap env rho expr eff phi heap_final v_final,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedTcExp gamma omega expr TyEffect eff ->
    CheckedCountedComputationEvaluation n heap env rho expr
      phi heap_final v_final ->
    exists theta,
      v_final = VSummary theta.
Proof.
  intros n gamma omega heap env rho expr eff phi heap_final v_final
    HContext HChecked HComp.
  eapply checked_store_counted_tyeffect_value_is_summary; eauto.
  eapply checked_execution_counted_to_counted.
  exact HComp.
Qed.

Lemma checked_execution_store_counted_computation_store_value_shape :
  forall n gamma omega heap env rho expr ty eff phi heap' v,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedTcExp gamma omega expr ty eff ->
    CheckedCountedComputationEvaluation n heap env rho expr phi heap' v ->
    exists store ty_res,
      StoreKeysBoundedByHeap heap' store /\
      StoreResolvedHeapShape heap' store /\
      StoreResolvedValShape store v ty_res.
Proof.
  intros n gamma omega heap env rho expr ty eff phi heap' v
    HContext HChecked HComp.
  eapply checked_store_counted_computation_store_value_shape; eauto.
  eapply checked_execution_counted_to_counted.
  exact HComp.
Qed.

Lemma checked_execution_store_counted_computation_store_value_shape_resolved :
  forall n gamma omega heap env rho expr ty eff phi heap' v,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedTcExp gamma omega expr ty eff ->
    CheckedCountedComputationEvaluation n heap env rho expr phi heap' v ->
    exists store ty_res,
      ResolveTy rho ty ty_res /\
      StoreKeysBoundedByHeap heap' store /\
      StoreResolvedHeapShape heap' store /\
      StoreResolvedValShape store v ty_res.
Proof.
  intros n gamma omega heap env rho expr ty eff phi heap' v
    HContext HChecked HComp.
  eapply checked_store_counted_computation_store_value_shape_resolved; eauto.
  eapply checked_execution_counted_to_counted.
  exact HComp.
Qed.

Lemma checked_execution_store_counted_tynat_value_is_nat :
  forall n gamma omega heap env rho expr eff phi heap_final v_final,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedTcExp gamma omega expr TyNat eff ->
    CheckedCountedComputationEvaluation n heap env rho expr
      phi heap_final v_final ->
    exists n_final,
      v_final = VNat n_final.
Proof.
  intros n gamma omega heap env rho expr eff phi heap_final v_final
    HContext HChecked HComp.
  eapply checked_store_counted_tynat_value_is_nat; eauto.
  eapply checked_execution_counted_to_counted.
  exact HComp.
Qed.

Lemma checked_execution_store_counted_tybool_value_is_bool :
  forall n gamma omega heap env rho expr eff phi heap_final v_final,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedTcExp gamma omega expr TyBool eff ->
    CheckedCountedComputationEvaluation n heap env rho expr
      phi heap_final v_final ->
    exists b_final,
      v_final = VBool b_final.
Proof.
  intros n gamma omega heap env rho expr eff phi heap_final v_final
    HContext HChecked HComp.
  eapply checked_store_counted_tybool_value_is_bool; eauto.
  eapply checked_execution_counted_to_counted.
  exact HComp.
Qed.

Lemma CheckedEConcat_counted_decomposition :
  forall n heap env rho e1 e2 phi heap_final theta,
    CheckedStepsN n
      (InitialState heap env rho (EConcat e1 e2))
      phi
      (StDone heap_final (VSummary theta)) ->
    exists n1 n2 phi1 phi2 theta1 theta2 heap1 heap2,
      CheckedStepsN n1
        (InitialState heap env rho e1)
        phi1
        (StDone heap1 (VSummary theta1)) /\
      CheckedStepsN n2
        (InitialState heap1 env rho e2)
        phi2
        (StDone heap2 (VSummary theta2)) /\
      theta = summary_union theta1 theta2 /\
      heap_final = heap2 /\
      phi = phi1 ++ phi2 /\
      n1 < n /\
      n2 < n.
Proof.
  intros n heap env rho e1 e2 phi heap_final theta HSteps.
  destruct
    (CheckedStepsN_known_first_step_terminal_inv
      n
      (InitialState heap env rho (EConcat e1 e2))
      LSilent
      (StEval heap env rho e1 (KConcatL e2 env rho KDone))
      phi heap_final (VSummary theta)
      ltac:(checked_runtime_non_pairpar_step)
      HSteps)
    as (n1_tail & phi_tail & HnStart &
      HLeftWithKont & HTraceStart).
  destruct
    (CheckedStepsN_append_kont_terminal_split_counted
      n1_tail
      (StEval heap env rho e1 (KConcatL e2 env rho KDone))
      phi_tail
      heap_final (VSummary theta)
      HLeftWithKont
      (InitialState heap env rho e1)
      (KConcatL e2 env rho KDone)
      eq_refl)
    as (n1 & n_after_left & phi1 & heap1 & v1 &
      phi_after_left & HLeft & HAfterLeft & HCountLeft &
      HTraceLeft).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KConcatL_terminal_value_is_summary
        heap1 v1 e2 env rho KDone
        phi_after_left heap_final (VSummary theta)
        (StepsN_to_Steps _ _ _ _
          (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterLeft)))
      as (theta1 & HTheta1).
    subst v1.
    destruct
      (CheckedStepsN_known_first_step_terminal_inv
        n_after_left
        (StReturn heap1 (VSummary theta1)
          (KConcatL e2 env rho KDone))
        LSilent
        (StEval heap1 env rho e2 (KConcatR theta1 KDone))
        phi_after_left heap_final (VSummary theta)
        ltac:(checked_runtime_non_pairpar_step)
        HAfterLeft)
      as (n2_tail & phi2_tail & HCountAfterLeft &
        HRightWithKont & HTraceAfterLeft).
    destruct
      (CheckedStepsN_append_kont_terminal_split_counted
        n2_tail
        (StEval heap1 env rho e2 (KConcatR theta1 KDone))
        phi2_tail
        heap_final (VSummary theta)
        HRightWithKont
        (InitialState heap1 env rho e2)
        (KConcatR theta1 KDone)
        eq_refl)
      as (n2 & n_after_right & phi2 & heap2 & v2 &
        phi_after_right & HRight & HAfterRight & HCountRight &
        HTraceRight).
    + intros heap_done v_done HDone. inversion HDone.
    + destruct
        (KConcatR_terminal_summary_result
          heap2 theta1 v2 phi_after_right heap_final theta
          (StepsN_to_Steps _ _ _ _
            (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterRight)))
        as (theta2 & HTheta2 & HTheta & HHeap & HTraceAfterRight).
      subst v2 theta heap_final phi_after_right.
      assert (HAfterRightPositive : 0 < n_after_right).
      { destruct n_after_right; [inversion HAfterRight | lia]. }
      exists n1, n2, phi1, phi2, theta1, theta2, heap1, heap2.
      repeat split; try assumption.
      * rewrite HTraceStart, HTraceLeft, HTraceAfterLeft,
          HTraceRight.
        rewrite app_nil_r.
        reflexivity.
      * lia.
      * lia.
Qed.

Lemma CheckedEMuApp_counted_decomposition :
  forall n heap env rho ef ea phi heap_final v_final,
    CheckedStepsN n
      (InitialState heap env rho (EMuApp ef ea))
      phi
      (StDone heap_final v_final) ->
    exists n_fun n_arg n_body
      phi_fun phi_arg phi_body
      closure_env closure_rho f x ec ee arg heap_arg,
    exists heap_fun,
      CheckedStepsN n_fun
        (InitialState heap env rho ef)
        phi_fun
        (StDone heap_fun (VClosure closure_env closure_rho f x ec ee)) /\
      CheckedStepsN n_arg
        (InitialState heap_fun env rho ea)
        phi_arg
        (StDone heap_arg arg) /\
      CheckedStepsN n_body
        (InitialState heap_arg
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ec)
        phi_body
        (StDone heap_final v_final) /\
      n_fun < n /\
      n_arg < n /\
      n_body < n /\
      phi = phi_fun ++ phi_arg ++ phi_body.
Proof.
  intros n heap env rho ef ea phi heap_final v_final HSteps.
  destruct
    (CheckedStepsN_known_first_step_terminal_inv
      n
      (InitialState heap env rho (EMuApp ef ea))
      LSilent
      (StEval heap env rho ef (KMuAppFun ea env rho KDone))
      phi heap_final v_final
      ltac:(checked_runtime_non_pairpar_step)
      HSteps)
    as (n_fun_tail & phi_fun_tail & HnStart &
      HFunWithKont & HTraceStart).
  destruct
    (CheckedStepsN_append_kont_terminal_split_counted
      n_fun_tail
      (StEval heap env rho ef (KMuAppFun ea env rho KDone))
      phi_fun_tail
      heap_final v_final
      HFunWithKont
      (InitialState heap env rho ef)
      (KMuAppFun ea env rho KDone)
      eq_refl)
    as (n_fun & n_after_fun & phi_fun & heap_fun & v_fun &
      phi_after_fun & HFun & HAfterFun & HCountFun & HTraceFun).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KMuAppFun_terminal_value_is_closure
        heap_fun v_fun ea env rho KDone
        phi_after_fun heap_final v_final
        (StepsN_to_Steps _ _ _ _
          (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterFun)))
      as (closure_env & closure_rho & f & x & ec & ee & HClosure).
    subst v_fun.
    destruct
      (CheckedStepsN_known_first_step_terminal_inv
        n_after_fun
        (StReturn heap_fun
          (VClosure closure_env closure_rho f x ec ee)
          (KMuAppFun ea env rho KDone))
        LSilent
        (StEval heap_fun env rho ea
          (KMuAppArg closure_env closure_rho f x ec ee KDone))
        phi_after_fun heap_final v_final
        ltac:(checked_runtime_non_pairpar_step)
        HAfterFun)
      as (n_arg_tail & phi_arg_tail & HCountAfterFun &
        HArgWithKont & HTraceAfterFun).
    destruct
      (CheckedStepsN_append_kont_terminal_split_counted
        n_arg_tail
        (StEval heap_fun env rho ea
          (KMuAppArg closure_env closure_rho f x ec ee KDone))
        phi_arg_tail
        heap_final v_final
        HArgWithKont
        (InitialState heap_fun env rho ea)
        (KMuAppArg closure_env closure_rho f x ec ee KDone)
        eq_refl)
      as (n_arg & n_after_arg & phi_arg & heap_arg & arg &
        phi_after_arg & HArg & HAfterArg & HCountArg & HTraceArg).
    + intros heap_done v_done HDone. inversion HDone.
    + destruct
        (CheckedStepsN_known_first_step_terminal_inv
          n_after_arg
          (StReturn heap_arg arg
            (KMuAppArg closure_env closure_rho f x ec ee KDone))
          LSilent
          (InitialState heap_arg
            (env_extend x arg
              (env_extend f
                (VClosure closure_env closure_rho f x ec ee)
                closure_env))
            closure_rho ec)
          phi_after_arg heap_final v_final
          ltac:(checked_runtime_non_pairpar_step)
          HAfterArg)
        as (n_body & phi_body & HCountAfterArg &
          HBody & HTraceAfterArg).
      exists n_fun, n_arg, n_body,
        phi_fun, phi_arg, phi_body,
        closure_env, closure_rho, f, x, ec, ee, arg, heap_arg,
        heap_fun.
      repeat split; try assumption.
      * lia.
      * lia.
      * lia.
      * rewrite HTraceStart, HTraceFun, HTraceAfterFun,
          HTraceArg, HTraceAfterArg.
        reflexivity.
Qed.

Lemma CheckedEEffApp_counted_decomposition :
  forall n heap env rho ef ea phi heap_final theta,
    CheckedStepsN n
      (InitialState heap env rho (EEffApp ef ea))
      phi
      (StDone heap_final (VSummary theta)) ->
    exists n_fun n_arg n_summary
      phi_fun phi_arg phi_summary
      closure_env closure_rho f x ec ee arg heap_arg,
    exists heap_fun,
      CheckedStepsN n_fun
        (InitialState heap env rho ef)
        phi_fun
        (StDone heap_fun (VClosure closure_env closure_rho f x ec ee)) /\
      CheckedStepsN n_arg
        (InitialState heap_fun env rho ea)
        phi_arg
        (StDone heap_arg arg) /\
      CheckedStepsN n_summary
        (InitialState heap_arg
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ee)
        phi_summary
        (StDone heap_final (VSummary theta)) /\
      n_fun < n /\
      n_arg < n /\
      n_summary < n /\
      phi = phi_fun ++ phi_arg ++ phi_summary.
Proof.
  intros n heap env rho ef ea phi heap_final theta HSteps.
  destruct
    (CheckedStepsN_known_first_step_terminal_inv
      n
      (InitialState heap env rho (EEffApp ef ea))
      LSilent
      (StEval heap env rho ef (KEffAppFun ea env rho KDone))
      phi heap_final (VSummary theta)
      ltac:(checked_runtime_non_pairpar_step)
      HSteps)
    as (n_fun_tail & phi_fun_tail & HnStart &
      HFunWithKont & HTraceStart).
  destruct
    (CheckedStepsN_append_kont_terminal_split_counted
      n_fun_tail
      (StEval heap env rho ef (KEffAppFun ea env rho KDone))
      phi_fun_tail
      heap_final (VSummary theta)
      HFunWithKont
      (InitialState heap env rho ef)
      (KEffAppFun ea env rho KDone)
      eq_refl)
    as (n_fun & n_after_fun & phi_fun & heap_fun & v_fun &
      phi_after_fun & HFun & HAfterFun & HCountFun & HTraceFun).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KEffAppFun_terminal_value_is_closure
        heap_fun v_fun ea env rho KDone
        phi_after_fun heap_final (VSummary theta)
        (StepsN_to_Steps _ _ _ _
          (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterFun)))
      as (closure_env & closure_rho & f & x & ec & ee & HClosure).
    subst v_fun.
    destruct
      (CheckedStepsN_known_first_step_terminal_inv
        n_after_fun
        (StReturn heap_fun
          (VClosure closure_env closure_rho f x ec ee)
          (KEffAppFun ea env rho KDone))
        LSilent
        (StEval heap_fun env rho ea
          (KEffAppArg closure_env closure_rho f x ec ee KDone))
        phi_after_fun heap_final (VSummary theta)
        ltac:(checked_runtime_non_pairpar_step)
        HAfterFun)
      as (n_arg_tail & phi_arg_tail & HCountAfterFun &
        HArgWithKont & HTraceAfterFun).
    destruct
      (CheckedStepsN_append_kont_terminal_split_counted
        n_arg_tail
        (StEval heap_fun env rho ea
          (KEffAppArg closure_env closure_rho f x ec ee KDone))
        phi_arg_tail
        heap_final (VSummary theta)
        HArgWithKont
        (InitialState heap_fun env rho ea)
        (KEffAppArg closure_env closure_rho f x ec ee KDone)
        eq_refl)
      as (n_arg & n_after_arg & phi_arg & heap_arg & arg &
        phi_after_arg & HArg & HAfterArg & HCountArg & HTraceArg).
    + intros heap_done v_done HDone. inversion HDone.
    + destruct
        (CheckedStepsN_known_first_step_terminal_inv
          n_after_arg
          (StReturn heap_arg arg
            (KEffAppArg closure_env closure_rho f x ec ee KDone))
          LSilent
          (InitialState heap_arg
            (env_extend x arg
              (env_extend f
                (VClosure closure_env closure_rho f x ec ee)
                closure_env))
            closure_rho ee)
          phi_after_arg heap_final (VSummary theta)
          ltac:(checked_runtime_non_pairpar_step)
          HAfterArg)
        as (n_summary & phi_summary & HCountAfterArg &
          HSummary & HTraceAfterArg).
      exists n_fun, n_arg, n_summary,
        phi_fun, phi_arg, phi_summary,
        closure_env, closure_rho, f, x, ec, ee, arg, heap_arg,
        heap_fun.
      repeat split; try assumption.
      * lia.
      * lia.
      * lia.
      * rewrite HTraceStart, HTraceFun, HTraceAfterFun,
          HTraceArg, HTraceAfterArg.
        reflexivity.
Qed.

Lemma CheckedERgnApp_counted_decomposition :
  forall n heap env rho er r phi heap_final v_final,
    CheckedStepsN n
      (InitialState heap env rho (ERgnApp er r))
      phi
      (StDone heap_final v_final) ->
    exists n_fun n_body phi_fun phi_body
      closure_env closure_rho x e heap_fun r_val,
      eval_region rho r = Some r_val /\
      CheckedStepsN n_fun
        (InitialState heap env rho er)
        phi_fun
        (StDone heap_fun
          (VRegionClosure closure_env closure_rho x e)) /\
      CheckedStepsN n_body
        (InitialState heap_fun closure_env
          (rho_extend x r_val closure_rho)
          e)
        phi_body
        (StDone heap_final v_final) /\
      n_fun < n /\
      n_body < n /\
      phi = phi_fun ++ phi_body.
Proof.
  intros n heap env rho er r phi heap_final v_final HSteps.
  destruct
    (CheckedStepsN_known_first_step_terminal_inv
      n
      (InitialState heap env rho (ERgnApp er r))
      LSilent
      (StEval heap env rho er (KRgnApp r rho KDone))
      phi heap_final v_final
      ltac:(checked_runtime_non_pairpar_step)
      HSteps)
    as (n_fun_tail & phi_fun_tail & HnStart &
      HFunWithKont & HTraceStart).
  destruct
    (CheckedStepsN_append_kont_terminal_split_counted
      n_fun_tail
      (StEval heap env rho er (KRgnApp r rho KDone))
      phi_fun_tail
      heap_final v_final
      HFunWithKont
      (InitialState heap env rho er)
      (KRgnApp r rho KDone)
      eq_refl)
    as (n_fun & n_after_fun & phi_fun & heap_fun & v_fun &
      phi_after_fun & HFun & HAfterFun & HCountFun & HTraceFun).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KRgnApp_terminal_value_is_region_closure
        heap_fun v_fun r rho KDone
        phi_after_fun heap_final v_final
        (StepsN_to_Steps _ _ _ _
          (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterFun)))
      as (closure_env & closure_rho & x & e & HClosure).
    subst v_fun.
    destruct
      (KRgnApp_region_closure_terminal_region
        heap_fun closure_env closure_rho x e r rho KDone
        phi_after_fun heap_final v_final
        (StepsN_to_Steps _ _ _ _
          (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterFun)))
      as (r_val & HRgn).
    destruct
      (CheckedStepsN_known_first_step_terminal_inv
        n_after_fun
        (StReturn heap_fun
          (VRegionClosure closure_env closure_rho x e)
          (KRgnApp r rho KDone))
        LSilent
        (InitialState heap_fun closure_env
          (rho_extend x r_val closure_rho) e)
        phi_after_fun heap_final v_final
        ltac:(checked_runtime_non_pairpar_step)
        HAfterFun)
      as (n_body & phi_body & HCountAfterFun &
        HBody & HTraceAfterFun).
    exists n_fun, n_body, phi_fun, phi_body,
      closure_env, closure_rho, x, e, heap_fun, r_val.
    repeat split; try assumption.
    * lia.
    * lia.
    * rewrite HTraceStart, HTraceFun, HTraceAfterFun.
      reflexivity.
Qed.

Lemma CheckedECond_counted_decomposition :
  forall n heap env rho e et ef phi heap_final v_final,
    CheckedStepsN n
      (InitialState heap env rho (ECond e et ef))
      phi
      (StDone heap_final v_final) ->
    exists n_cond n_branch phi_cond b heap_cond phi_branch,
      CheckedStepsN n_cond
        (InitialState heap env rho e)
        phi_cond
        (StDone heap_cond (VBool b)) /\
      CheckedStepsN n_branch
        (InitialState heap_cond env rho (if b then et else ef))
        phi_branch
        (StDone heap_final v_final) /\
      phi = phi_cond ++ phi_branch /\
      n_cond < n /\
      n_branch < n.
Proof.
  intros n heap env rho e et ef phi heap_final v_final HSteps.
  destruct
    (CheckedStepsN_known_first_step_terminal_inv
      n
      (InitialState heap env rho (ECond e et ef))
      LSilent
      (StEval heap env rho e (KCond et ef env rho KDone))
      phi heap_final v_final
      ltac:(checked_runtime_non_pairpar_step)
      HSteps)
    as (n_cond_tail & phi_cond_tail & HnStart &
      HCondWithKont & HTraceStart).
  destruct
    (CheckedStepsN_append_kont_terminal_split_counted
      n_cond_tail
      (StEval heap env rho e (KCond et ef env rho KDone))
      phi_cond_tail
      heap_final
      v_final
      HCondWithKont
      (InitialState heap env rho e)
      (KCond et ef env rho KDone)
      eq_refl)
    as (n_cond & n_after_cond & phi_cond & heap_cond & v_cond &
      phi_after_cond & HCond & HAfterCond & HCountCond &
      HTraceCond).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KCond_terminal_value_is_bool
        heap_cond v_cond et ef env rho KDone
        phi_after_cond heap_final v_final
        (StepsN_to_Steps _ _ _ _
          (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterCond)))
      as (b & HBool).
    subst v_cond.
    destruct b.
    + destruct
        (CheckedStepsN_known_first_step_terminal_inv
          n_after_cond
          (StReturn heap_cond (VBool true)
            (KCond et ef env rho KDone))
          LSilent
          (InitialState heap_cond env rho et)
          phi_after_cond heap_final v_final
          ltac:(checked_runtime_non_pairpar_step)
          HAfterCond)
        as (n_branch & phi_branch & HCountAfterCond &
          HBranch & HTraceAfterCond).
      exists n_cond, n_branch, phi_cond, true, heap_cond,
        phi_branch.
      repeat split; try assumption; try lia.
      rewrite HTraceStart, HTraceCond, HTraceAfterCond.
      reflexivity.
    + destruct
        (CheckedStepsN_known_first_step_terminal_inv
          n_after_cond
          (StReturn heap_cond (VBool false)
            (KCond et ef env rho KDone))
          LSilent
          (InitialState heap_cond env rho ef)
          phi_after_cond heap_final v_final
          ltac:(checked_runtime_non_pairpar_step)
          HAfterCond)
        as (n_branch & phi_branch & HCountAfterCond &
          HBranch & HTraceAfterCond).
      exists n_cond, n_branch, phi_cond, false, heap_cond,
        phi_branch.
      repeat split; try assumption; try lia.
      rewrite HTraceStart, HTraceCond, HTraceAfterCond.
      reflexivity.
Qed.

Lemma CheckedERef_counted_decomposition :
  forall n heap env rho r e phi heap_final loc,
    CheckedStepsN n
      (InitialState heap env rho (ERef r e))
      phi
      (StDone heap_final loc) ->
    exists n_e phi_e heap_e v r_val l,
      eval_region rho r = Some r_val /\
      CheckedStepsN n_e
        (InitialState heap env rho e)
        phi_e
        (StDone heap_e v) /\
      heap_alloc r_val v heap_e = (l, heap_final) /\
      loc = VLoc r_val l /\
      phi = phi_e ++ [DAlloc r_val l] /\
      n_e < n.
Proof.
  intros n heap env rho r e phi heap_final loc HSteps.
  pose proof
    (CheckedStepsN_to_StepsN_done _ _ _ _ _ HSteps)
    as HRawSteps.
  destruct
    (ERef_terminal_first_step_N
      n heap env rho r e phi heap_final loc HRawSteps)
    as (r_val & _n_expr_tail_raw & _phi_tail_raw & HRgn &
      _HnStartRaw & _HExprRaw & _HTraceRaw).
  destruct
    (CheckedStepsN_known_first_step_terminal_inv
      n
      (InitialState heap env rho (ERef r e))
      LSilent
      (StEval heap env rho e (KRef r_val KDone))
      phi heap_final loc
      ltac:(checked_runtime_non_pairpar_step)
      HSteps)
    as (n_expr_tail & phi_tail & HnStart &
      HExprWithKont & HTraceStart).
  destruct
    (CheckedStepsN_append_kont_terminal_split_counted
      n_expr_tail
      (StEval heap env rho e (KRef r_val KDone))
      phi_tail
      heap_final
      loc
      HExprWithKont
      (InitialState heap env rho e)
      (KRef r_val KDone)
      eq_refl)
    as (n_e & n_after_expr & phi_e & heap_e & v &
      phi_after_expr & HExpr & HAfterExpr & HCountExpr &
      HTraceExpr).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KRef_terminal_alloc_result
        heap_e v r_val phi_after_expr heap_final loc
        (StepsN_to_Steps _ _ _ _
          (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterExpr)))
      as (l & HAlloc & HLoc & HTraceAfterExpr).
    subst loc phi_after_expr.
    assert (HAfterExprPositive : 0 < n_after_expr).
    { destruct n_after_expr; [inversion HAfterExpr | lia]. }
    exists n_e, phi_e, heap_e, v, r_val, l.
    repeat split; try assumption.
    + rewrite HTraceStart, HTraceExpr.
      reflexivity.
    + lia.
Qed.

Lemma CheckedEDeref_counted_decomposition :
  forall n heap env rho r_static e phi heap_final v_final,
    CheckedStepsN n
      (InitialState heap env rho (EDeref r_static e))
      phi
      (StDone heap_final v_final) ->
    exists n_e phi_e heap_e r l,
      CheckedStepsN n_e
        (InitialState heap env rho e)
        phi_e
        (StDone heap_e (VLoc r l)) /\
      heap_lookup r l heap_e = Some v_final /\
      heap_final = heap_e /\
      phi = phi_e ++ [DRead r l] /\
      n_e < n.
Proof.
  intros n heap env rho r_static e phi heap_final v_final HSteps.
  destruct
    (CheckedStepsN_known_first_step_terminal_inv
      n
      (InitialState heap env rho (EDeref r_static e))
      LSilent
      (StEval heap env rho e (KDeref r_static KDone))
      phi heap_final v_final
      ltac:(checked_runtime_non_pairpar_step)
      HSteps)
    as (n_expr_tail & phi_tail & HnStart &
      HExprWithKont & HTraceStart).
  destruct
    (CheckedStepsN_append_kont_terminal_split_counted
      n_expr_tail
      (StEval heap env rho e (KDeref r_static KDone))
      phi_tail
      heap_final
      v_final
      HExprWithKont
      (InitialState heap env rho e)
      (KDeref r_static KDone)
      eq_refl)
    as (n_e & n_after_expr & phi_e & heap_e & v_loc &
      phi_after_expr & HExpr & HAfterExpr & HCountExpr &
      HTraceExpr).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KDeref_terminal_value_is_loc
        heap_e v_loc r_static KDone
        phi_after_expr heap_final v_final
        (StepsN_to_Steps _ _ _ _
          (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterExpr)))
      as (r & l & HLoc).
    subst v_loc.
    destruct
      (KDeref_loc_terminal_read_result
        heap_e r_static r l phi_after_expr heap_final v_final
        (StepsN_to_Steps _ _ _ _
          (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterExpr)))
      as (HLookup & HHeap & HTraceAfterExpr).
    subst heap_final phi_after_expr.
    assert (HAfterExprPositive : 0 < n_after_expr).
    { destruct n_after_expr; [inversion HAfterExpr | lia]. }
    exists n_e, phi_e, heap_e, r, l.
    repeat split; try assumption.
    + rewrite HTraceStart, HTraceExpr.
      reflexivity.
    + lia.
Qed.

Lemma CheckedEAssign_counted_decomposition :
  forall n heap env rho r_static ea ev phi heap_final v_final,
    CheckedStepsN n
      (InitialState heap env rho (EAssign r_static ea ev))
      phi
      (StDone heap_final v_final) ->
    exists n_addr n_val phi_addr phi_val
      heap_addr heap_val r l v,
      CheckedStepsN n_addr
        (InitialState heap env rho ea)
        phi_addr
        (StDone heap_addr (VLoc r l)) /\
      CheckedStepsN n_val
        (InitialState heap_addr env rho ev)
        phi_val
        (StDone heap_val v) /\
      heap_final = heap_update r l v heap_val /\
      v_final = VUnit /\
      phi = phi_addr ++ phi_val ++ [DWrite r l] /\
      n_addr < n /\
      n_val < n.
Proof.
  intros n heap env rho r_static ea ev phi heap_final v_final HSteps.
  destruct
    (CheckedStepsN_known_first_step_terminal_inv
      n
      (InitialState heap env rho (EAssign r_static ea ev))
      LSilent
      (StEval heap env rho ea
        (KAssignLoc r_static ev env rho KDone))
      phi heap_final v_final
      ltac:(checked_runtime_non_pairpar_step)
      HSteps)
    as (n_addr_tail & phi_tail & HnStart & HAddrWithKont &
      HTraceStart).
  destruct
    (CheckedStepsN_append_kont_terminal_split_counted
      n_addr_tail
      (StEval heap env rho ea
        (KAssignLoc r_static ev env rho KDone))
      phi_tail
      heap_final
      v_final
      HAddrWithKont
      (InitialState heap env rho ea)
      (KAssignLoc r_static ev env rho KDone)
      eq_refl)
    as (n_addr & n_after_addr & phi_addr & heap_addr & v_addr &
      phi_after_addr & HAddr & HAfterAddr & HCountAddr &
      HTraceAddr).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KAssignLoc_terminal_value_is_loc
        heap_addr v_addr r_static ev env rho KDone
        phi_after_addr heap_final v_final
        (StepsN_to_Steps _ _ _ _
          (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterAddr)))
      as (r & l & HLoc).
    subst v_addr.
    destruct
      (CheckedStepsN_known_first_step_terminal_inv
        n_after_addr
        (StReturn heap_addr (VLoc r l)
          (KAssignLoc r_static ev env rho KDone))
        LSilent
        (StEval heap_addr env rho ev
          (KAssignVal r_static (VLoc r l) KDone))
        phi_after_addr heap_final v_final
        ltac:(checked_runtime_non_pairpar_step)
        HAfterAddr)
      as (n_val_tail & phi_val_tail & HCountAfterAddr &
        HValWithKont & HTraceAfterAddr).
    destruct
      (CheckedStepsN_append_kont_terminal_split_counted
        n_val_tail
        (StEval heap_addr env rho ev
          (KAssignVal r_static (VLoc r l) KDone))
        phi_val_tail
        heap_final
        v_final
        HValWithKont
        (InitialState heap_addr env rho ev)
        (KAssignVal r_static (VLoc r l) KDone)
        eq_refl)
      as (n_val & n_after_val & phi_val & heap_val & v &
        phi_after_val & HVal & HAfterVal & HCountVal &
        HTraceVal).
    + intros heap_done v_done HDone. inversion HDone.
    + destruct
        (KAssignVal_terminal_write_result
          heap_val v r_static r l phi_after_val heap_final v_final
          (StepsN_to_Steps _ _ _ _
            (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterVal)))
        as (HHeap & HUnit & HTraceAfterVal).
      subst heap_final v_final phi_after_val.
      assert (HAfterValPositive : 0 < n_after_val).
      { destruct n_after_val; [inversion HAfterVal | lia]. }
      exists n_addr, n_val, phi_addr, phi_val,
        heap_addr, heap_val, r, l, v.
      repeat split; try assumption.
      * rewrite HTraceStart, HTraceAddr, HTraceAfterAddr,
          HTraceVal.
        reflexivity.
      * lia.
      * lia.
Qed.

Lemma CheckedEPlus_counted_decomposition :
  forall n heap env rho e1 e2 phi heap_final n_final,
    CheckedStepsN n
      (InitialState heap env rho (EPlus e1 e2))
      phi
      (StDone heap_final (VNat n_final)) ->
    exists n1_steps n2_steps phi1 phi2 n1 n2 heap1 heap2,
      CheckedStepsN n1_steps
        (InitialState heap env rho e1)
        phi1
        (StDone heap1 (VNat n1)) /\
      CheckedStepsN n2_steps
        (InitialState heap1 env rho e2)
        phi2
        (StDone heap2 (VNat n2)) /\
      n_final = n1 + n2 /\
      heap_final = heap2 /\
      phi = phi1 ++ phi2 /\
      n1_steps < n /\
      n2_steps < n.
Proof.
  intros n heap env rho e1 e2 phi heap_final n_final HSteps.
  destruct
    (CheckedStepsN_known_first_step_terminal_inv
      n (InitialState heap env rho (EPlus e1 e2))
      LSilent
      (StEval heap env rho e1 (KPlusL e2 env rho KDone))
      phi heap_final (VNat n_final)
      ltac:(checked_runtime_non_pairpar_step)
      HSteps)
    as (n_left_tail & phi_left_tail & HnStart &
      HLeftWithKont & HTraceStart).
  destruct
    (CheckedStepsN_append_kont_terminal_split_counted
      n_left_tail
      (StEval heap env rho e1 (KPlusL e2 env rho KDone))
      phi_left_tail heap_final (VNat n_final) HLeftWithKont
      (InitialState heap env rho e1)
      (KPlusL e2 env rho KDone) eq_refl)
    as (n1_steps & n_after_left & phi1 & heap1 & v1 &
      phi_after_left & HLeft & HAfterLeft & HCountLeft &
      HTraceLeft).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KPlusL_terminal_value_is_nat
        heap1 v1 e2 env rho KDone
        phi_after_left heap_final (VNat n_final)
        (StepsN_to_Steps _ _ _ _
          (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterLeft)))
      as (n1 & HNat1).
    subst v1.
    destruct
      (CheckedStepsN_known_first_step_terminal_inv
        n_after_left
        (StReturn heap1 (VNat n1) (KPlusL e2 env rho KDone))
        LSilent
        (StEval heap1 env rho e2 (KPlusR n1 KDone))
        phi_after_left heap_final (VNat n_final)
        ltac:(checked_runtime_non_pairpar_step)
        HAfterLeft)
      as (n_right_tail & phi_right_tail & HCountAfterLeft &
        HRightWithKont & HTraceAfterLeft).
    destruct
      (CheckedStepsN_append_kont_terminal_split_counted
        n_right_tail
        (StEval heap1 env rho e2 (KPlusR n1 KDone))
        phi_right_tail heap_final (VNat n_final) HRightWithKont
        (InitialState heap1 env rho e2)
        (KPlusR n1 KDone) eq_refl)
      as (n2_steps & n_after_right & phi2 & heap2 & v2 &
        phi_after_right & HRight & HAfterRight & HCountRight &
        HTraceRight).
    + intros heap_done v_done HDone. inversion HDone.
    + destruct
        (KPlusR_terminal_nat_result
          heap2 n1 v2 phi_after_right heap_final n_final
          (StepsN_to_Steps _ _ _ _
            (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterRight)))
        as (n2 & HNat2 & HResult & HHeap & HTraceAfterRight).
      subst v2 n_final heap_final phi_after_right.
      assert (HAfterRightPositive : 0 < n_after_right).
      { destruct n_after_right; [inversion HAfterRight | lia]. }
      exists n1_steps, n2_steps, phi1, phi2, n1, n2,
        heap1, heap2.
      repeat split; try assumption.
      * rewrite HTraceStart, HTraceLeft, HTraceAfterLeft,
          HTraceRight.
        rewrite app_nil_r.
        reflexivity.
      * lia.
      * lia.
Qed.

Lemma CheckedEMinus_counted_decomposition :
  forall n heap env rho e1 e2 phi heap_final n_final,
    CheckedStepsN n
      (InitialState heap env rho (EMinus e1 e2))
      phi
      (StDone heap_final (VNat n_final)) ->
    exists n1_steps n2_steps phi1 phi2 n1 n2 heap1 heap2,
      CheckedStepsN n1_steps
        (InitialState heap env rho e1)
        phi1
        (StDone heap1 (VNat n1)) /\
      CheckedStepsN n2_steps
        (InitialState heap1 env rho e2)
        phi2
        (StDone heap2 (VNat n2)) /\
      n_final = n1 - n2 /\
      heap_final = heap2 /\
      phi = phi1 ++ phi2 /\
      n1_steps < n /\
      n2_steps < n.
Proof.
  intros n heap env rho e1 e2 phi heap_final n_final HSteps.
  destruct
    (CheckedStepsN_known_first_step_terminal_inv
      n (InitialState heap env rho (EMinus e1 e2))
      LSilent
      (StEval heap env rho e1 (KMinusL e2 env rho KDone))
      phi heap_final (VNat n_final)
      ltac:(checked_runtime_non_pairpar_step)
      HSteps)
    as (n_left_tail & phi_left_tail & HnStart &
      HLeftWithKont & HTraceStart).
  destruct
    (CheckedStepsN_append_kont_terminal_split_counted
      n_left_tail
      (StEval heap env rho e1 (KMinusL e2 env rho KDone))
      phi_left_tail heap_final (VNat n_final) HLeftWithKont
      (InitialState heap env rho e1)
      (KMinusL e2 env rho KDone) eq_refl)
    as (n1_steps & n_after_left & phi1 & heap1 & v1 &
      phi_after_left & HLeft & HAfterLeft & HCountLeft &
      HTraceLeft).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KMinusL_terminal_value_is_nat
        heap1 v1 e2 env rho KDone
        phi_after_left heap_final (VNat n_final)
        (StepsN_to_Steps _ _ _ _
          (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterLeft)))
      as (n1 & HNat1).
    subst v1.
    destruct
      (CheckedStepsN_known_first_step_terminal_inv
        n_after_left
        (StReturn heap1 (VNat n1) (KMinusL e2 env rho KDone))
        LSilent
        (StEval heap1 env rho e2 (KMinusR n1 KDone))
        phi_after_left heap_final (VNat n_final)
        ltac:(checked_runtime_non_pairpar_step)
        HAfterLeft)
      as (n_right_tail & phi_right_tail & HCountAfterLeft &
        HRightWithKont & HTraceAfterLeft).
    destruct
      (CheckedStepsN_append_kont_terminal_split_counted
        n_right_tail
        (StEval heap1 env rho e2 (KMinusR n1 KDone))
        phi_right_tail heap_final (VNat n_final) HRightWithKont
        (InitialState heap1 env rho e2)
        (KMinusR n1 KDone) eq_refl)
      as (n2_steps & n_after_right & phi2 & heap2 & v2 &
        phi_after_right & HRight & HAfterRight & HCountRight &
        HTraceRight).
    + intros heap_done v_done HDone. inversion HDone.
    + destruct
        (KMinusR_terminal_nat_result
          heap2 n1 v2 phi_after_right heap_final n_final
          (StepsN_to_Steps _ _ _ _
            (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterRight)))
        as (n2 & HNat2 & HResult & HHeap & HTraceAfterRight).
      subst v2 n_final heap_final phi_after_right.
      assert (HAfterRightPositive : 0 < n_after_right).
      { destruct n_after_right; [inversion HAfterRight | lia]. }
      exists n1_steps, n2_steps, phi1, phi2, n1, n2,
        heap1, heap2.
      repeat split; try assumption.
      * rewrite HTraceStart, HTraceLeft, HTraceAfterLeft,
          HTraceRight.
        rewrite app_nil_r.
        reflexivity.
      * lia.
      * lia.
Qed.

Lemma CheckedETimes_counted_decomposition :
  forall n heap env rho e1 e2 phi heap_final n_final,
    CheckedStepsN n
      (InitialState heap env rho (ETimes e1 e2))
      phi
      (StDone heap_final (VNat n_final)) ->
    exists n1_steps n2_steps phi1 phi2 n1 n2 heap1 heap2,
      CheckedStepsN n1_steps
        (InitialState heap env rho e1)
        phi1
        (StDone heap1 (VNat n1)) /\
      CheckedStepsN n2_steps
        (InitialState heap1 env rho e2)
        phi2
        (StDone heap2 (VNat n2)) /\
      n_final = n1 * n2 /\
      heap_final = heap2 /\
      phi = phi1 ++ phi2 /\
      n1_steps < n /\
      n2_steps < n.
Proof.
  intros n heap env rho e1 e2 phi heap_final n_final HSteps.
  destruct
    (CheckedStepsN_known_first_step_terminal_inv
      n (InitialState heap env rho (ETimes e1 e2))
      LSilent
      (StEval heap env rho e1 (KTimesL e2 env rho KDone))
      phi heap_final (VNat n_final)
      ltac:(checked_runtime_non_pairpar_step)
      HSteps)
    as (n_left_tail & phi_left_tail & HnStart &
      HLeftWithKont & HTraceStart).
  destruct
    (CheckedStepsN_append_kont_terminal_split_counted
      n_left_tail
      (StEval heap env rho e1 (KTimesL e2 env rho KDone))
      phi_left_tail heap_final (VNat n_final) HLeftWithKont
      (InitialState heap env rho e1)
      (KTimesL e2 env rho KDone) eq_refl)
    as (n1_steps & n_after_left & phi1 & heap1 & v1 &
      phi_after_left & HLeft & HAfterLeft & HCountLeft &
      HTraceLeft).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KTimesL_terminal_value_is_nat
        heap1 v1 e2 env rho KDone
        phi_after_left heap_final (VNat n_final)
        (StepsN_to_Steps _ _ _ _
          (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterLeft)))
      as (n1 & HNat1).
    subst v1.
    destruct
      (CheckedStepsN_known_first_step_terminal_inv
        n_after_left
        (StReturn heap1 (VNat n1) (KTimesL e2 env rho KDone))
        LSilent
        (StEval heap1 env rho e2 (KTimesR n1 KDone))
        phi_after_left heap_final (VNat n_final)
        ltac:(checked_runtime_non_pairpar_step)
        HAfterLeft)
      as (n_right_tail & phi_right_tail & HCountAfterLeft &
        HRightWithKont & HTraceAfterLeft).
    destruct
      (CheckedStepsN_append_kont_terminal_split_counted
        n_right_tail
        (StEval heap1 env rho e2 (KTimesR n1 KDone))
        phi_right_tail heap_final (VNat n_final) HRightWithKont
        (InitialState heap1 env rho e2)
        (KTimesR n1 KDone) eq_refl)
      as (n2_steps & n_after_right & phi2 & heap2 & v2 &
        phi_after_right & HRight & HAfterRight & HCountRight &
        HTraceRight).
    + intros heap_done v_done HDone. inversion HDone.
    + destruct
        (KTimesR_terminal_nat_result
          heap2 n1 v2 phi_after_right heap_final n_final
          (StepsN_to_Steps _ _ _ _
            (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterRight)))
        as (n2 & HNat2 & HResult & HHeap & HTraceAfterRight).
      subst v2 n_final heap_final phi_after_right.
      assert (HAfterRightPositive : 0 < n_after_right).
      { destruct n_after_right; [inversion HAfterRight | lia]. }
      exists n1_steps, n2_steps, phi1, phi2, n1, n2,
        heap1, heap2.
      repeat split; try assumption.
      * rewrite HTraceStart, HTraceLeft, HTraceAfterLeft,
          HTraceRight.
        rewrite app_nil_r.
        reflexivity.
      * lia.
      * lia.
Qed.

Lemma CheckedEEq_counted_decomposition :
  forall n heap env rho e1 e2 phi heap_final b_final,
    CheckedStepsN n
      (InitialState heap env rho (EEq e1 e2))
      phi
      (StDone heap_final (VBool b_final)) ->
    exists n1_steps n2_steps phi1 phi2 n1 n2 heap1 heap2,
      CheckedStepsN n1_steps
        (InitialState heap env rho e1)
        phi1
        (StDone heap1 (VNat n1)) /\
      CheckedStepsN n2_steps
        (InitialState heap1 env rho e2)
        phi2
        (StDone heap2 (VNat n2)) /\
      b_final = Nat.eqb n1 n2 /\
      heap_final = heap2 /\
      phi = phi1 ++ phi2 /\
      n1_steps < n /\
      n2_steps < n.
Proof.
  intros n heap env rho e1 e2 phi heap_final b_final HSteps.
  destruct
    (CheckedStepsN_known_first_step_terminal_inv
      n (InitialState heap env rho (EEq e1 e2))
      LSilent
      (StEval heap env rho e1 (KEqL e2 env rho KDone))
      phi heap_final (VBool b_final)
      ltac:(checked_runtime_non_pairpar_step)
      HSteps)
    as (n_left_tail & phi_left_tail & HnStart &
      HLeftWithKont & HTraceStart).
  destruct
    (CheckedStepsN_append_kont_terminal_split_counted
      n_left_tail
      (StEval heap env rho e1 (KEqL e2 env rho KDone))
      phi_left_tail heap_final (VBool b_final) HLeftWithKont
      (InitialState heap env rho e1)
      (KEqL e2 env rho KDone) eq_refl)
    as (n1_steps & n_after_left & phi1 & heap1 & v1 &
      phi_after_left & HLeft & HAfterLeft & HCountLeft &
      HTraceLeft).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KEqL_terminal_value_is_nat
        heap1 v1 e2 env rho KDone
        phi_after_left heap_final (VBool b_final)
        (StepsN_to_Steps _ _ _ _
          (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterLeft)))
      as (n1 & HNat1).
    subst v1.
    destruct
      (CheckedStepsN_known_first_step_terminal_inv
        n_after_left
        (StReturn heap1 (VNat n1) (KEqL e2 env rho KDone))
        LSilent
        (StEval heap1 env rho e2 (KEqR n1 KDone))
        phi_after_left heap_final (VBool b_final)
        ltac:(checked_runtime_non_pairpar_step)
        HAfterLeft)
      as (n_right_tail & phi_right_tail & HCountAfterLeft &
        HRightWithKont & HTraceAfterLeft).
    destruct
      (CheckedStepsN_append_kont_terminal_split_counted
        n_right_tail
        (StEval heap1 env rho e2 (KEqR n1 KDone))
        phi_right_tail heap_final (VBool b_final) HRightWithKont
        (InitialState heap1 env rho e2)
        (KEqR n1 KDone) eq_refl)
      as (n2_steps & n_after_right & phi2 & heap2 & v2 &
        phi_after_right & HRight & HAfterRight & HCountRight &
        HTraceRight).
    + intros heap_done v_done HDone. inversion HDone.
    + destruct
        (KEqR_terminal_bool_result
          heap2 n1 v2 phi_after_right heap_final b_final
          (StepsN_to_Steps _ _ _ _
            (CheckedStepsN_to_StepsN_done _ _ _ _ _ HAfterRight)))
        as (n2 & HNat2 & HResult & HHeap & HTraceAfterRight).
      subst v2 b_final heap_final phi_after_right.
      assert (HAfterRightPositive : 0 < n_after_right).
      { destruct n_after_right; [inversion HAfterRight | lia]. }
      exists n1_steps, n2_steps, phi1, phi2, n1, n2,
        heap1, heap2.
      repeat split; try assumption.
      * rewrite HTraceStart, HTraceLeft, HTraceAfterLeft,
          HTraceRight.
        rewrite app_nil_r.
        reflexivity.
      * lia.
      * lia.
Qed.

Lemma checked_execution_store_summary_value_concat_from_below :
  forall n gamma omega heap env rho source1 source2 summary1 summary2
    eff_summary1 eff_summary2 phi heap_final theta,
    CheckedExecutionStoreSummaryValueSoundnessBelow n ->
    CheckedBackTriangle gamma omega source1 summary1 ->
    CheckedBackTriangle gamma omega source2 summary2 ->
    CheckedTcExp gamma omega summary1 TyEffect eff_summary1 ->
    CheckedTcExp gamma omega summary2 TyEffect eff_summary2 ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedCountedComputationEvaluation n heap env rho
      (EConcat summary1 summary2) phi heap_final (VSummary theta) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho source1 source2 summary1 summary2
    eff_summary1 eff_summary2 phi heap_final theta
    HSummaryValueBelow HBack1 HBack2 HCheckedSummary1
    HCheckedSummary2 HContext HComp.
  unfold CheckedCountedComputationEvaluation in HComp.
  destruct
    (CheckedEConcat_counted_decomposition
      n heap env rho summary1 summary2 phi heap_final theta HComp)
    as (n1 & n2 & phi1 & phi2 & theta1 & theta2 &
      heap1 & heap2 & HSummary1 & HSummary2 & HTheta &
      HHeapFinal & HTrace & HCount1 & HCount2).
  subst theta heap_final phi.
  assert (HComp1 :
    CheckedCountedComputationEvaluation n1 heap env rho summary1
      phi1 heap1 (VSummary theta1)).
  {
    unfold CheckedCountedComputationEvaluation.
    exact HSummary1.
  }
  assert (HComp2 :
    CheckedCountedComputationEvaluation n2 heap1 env rho summary2
      phi2 heap2 (VSummary theta2)).
  {
    unfold CheckedCountedComputationEvaluation.
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
      (checked_execution_store_runtime_context_after_counted
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

Theorem EMuApp_checked_execution_store_context_case_from_below :
  forall n gamma omega heap env rho ef ea
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedExecutionStoreContextSmallStepCorrectnessBelow n ->
    CheckedBackTriangle gamma omega (EMuApp ef ea) (EEffApp ef ea) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CheckedCountedComputationEvaluation n heap env rho
      (EMuApp ef ea) phi heap_final v_final ->
    SummaryEvaluation heap env rho (EEffApp ef ea)
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho ef ea
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext HComputationTraceSound HComp HSummary.
  destruct
    (CBT_App_components gamma omega ef ea HBack)
    as (ty_mu & eff_mu & eff_eff & ty_ef & ty_ea & eff_ef &
      eff_ea & HCheckedApp & HCheckedEffApp & HCheckedFun &
      HCheckedArg & _HStaticEff & HStaticFun & HStaticArg &
      HBackFun & HBackArg).
  unfold CheckedCountedComputationEvaluation in HComp.
  destruct
    (CheckedEMuApp_counted_decomposition
      n heap env rho ef ea phi heap_final v_final HComp)
    as (n_fun & n_arg & n_body &
      phi_fun & phi_arg & phi_body &
      closure_env & closure_rho & f & x & ec & ee & arg &
      heap_arg & heap_fun &
      HFun & HArg & HBody &
      HCountFun & HCountArg & HCountBody & HTrace).
  assert (HFunComp :
    CheckedCountedComputationEvaluation n_fun heap env rho ef
      phi_fun heap_fun (VClosure closure_env closure_rho f x ec ee)).
  {
    unfold CheckedCountedComputationEvaluation.
    exact HFun.
  }
  destruct
    (checked_execution_store_counted_computation_heap_neutral
      n_fun gamma omega heap env rho ef ty_ef eff_ef
      phi_fun heap_fun (VClosure closure_env closure_rho f x ec ee)
      HContext HComputationTraceSound HCheckedFun HStaticFun HFunComp)
    as (HHeapFun & _HNeutralFun).
  subst heap_fun.
  assert (HArgComp :
    CheckedCountedComputationEvaluation n_arg heap env rho ea
      phi_arg heap_arg arg).
  {
    unfold CheckedCountedComputationEvaluation.
    exact HArg.
  }
  destruct
    (checked_execution_store_counted_computation_heap_neutral
      n_arg gamma omega heap env rho ea ty_ea eff_ea
      phi_arg heap_arg arg
      HContext HComputationTraceSound HCheckedArg HStaticArg HArgComp)
    as (HHeapArg & _HNeutralArg).
  subst heap_arg.
  destruct
    (EEffApp_decomposition
      heap env rho ef ea phi_summary heap_summary theta HSummary)
    as (phi_fun_summary & phi_arg_summary & phi_body_summary &
      closure_env_summary & closure_rho_summary &
      f_summary & x_summary & ec_summary & ee_summary &
      arg_summary & heap_arg_summary & heap_fun_summary &
      HFunSummary & HArgSummary & HBodySummary & _HSummaryTrace).
  destruct
    (Steps_terminal_trace_deterministic
      (InitialState heap env rho ef)
      phi_fun heap (VClosure closure_env closure_rho f x ec ee)
      phi_fun_summary heap_fun_summary
      (VClosure closure_env_summary closure_rho_summary
        f_summary x_summary ec_summary ee_summary))
    as (_HTraceFunEq & HHeapFunSummaryEq & HClosureEq).
  - eapply StepsN_to_Steps.
    eapply CheckedStepsN_to_StepsN_done.
    exact HFun.
  - exact HFunSummary.
  - subst heap_fun_summary.
    inversion HClosureEq; subst
      closure_env_summary closure_rho_summary
      f_summary x_summary ec_summary ee_summary.
    destruct
      (Steps_terminal_trace_deterministic
        (InitialState heap env rho ea)
        phi_arg heap arg
        phi_arg_summary heap_arg_summary arg_summary)
      as (_HTraceArgEq & HHeapArgSummaryEq & HArgEq).
    + eapply StepsN_to_Steps.
      eapply CheckedStepsN_to_StepsN_done.
      exact HArg.
    + exact HArgSummary.
    + subst heap_arg_summary arg_summary.
      assert (HFunRaw :
        StepsN n_fun
          (InitialState heap env rho ef)
          phi_fun
          (StDone heap
            (VClosure closure_env closure_rho f x ec ee))).
      {
        eapply CheckedStepsN_to_StepsN_done.
        exact HFun.
      }
      assert (HArgRaw :
        StepsN n_arg
          (InitialState heap env rho ea)
          phi_arg
          (StDone heap arg)).
      {
        eapply CheckedStepsN_to_StepsN_done.
        exact HArg.
      }
      destruct
        (EEffApp_checked_summary_body_store_context_from_prefixes
          gamma omega heap env rho ef ea
          n_fun n_arg phi_fun phi_arg
          closure_env closure_rho f x ec ee arg
          HBack HContext HFunRaw HArgRaw)
        as (gamma_body & omega_body &
          ty_arg_body & ty_body & eff_body & eff_summary &
          HBodyContext & _HCheckedBody & _HCheckedSummary &
          HBodyBack).
      assert (HCoveredFun : TraceCoveredBySummary phi_fun theta).
      {
        eapply
          (HBelow n_fun gamma omega heap env rho
            ef (EEffApp ef ea)
            phi_fun heap (VClosure closure_env closure_rho f x ec ee)
            phi_summary heap_summary theta);
          eauto.
      }
      assert (HCoveredArg : TraceCoveredBySummary phi_arg theta).
      {
        eapply
          (HBelow n_arg gamma omega heap env rho
            ea (EEffApp ef ea)
            phi_arg heap arg
            phi_summary heap_summary theta);
          eauto.
      }
      assert (HBodySummaryEval :
        SummaryEvaluation heap
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ee
          phi_body_summary heap_summary theta).
      {
        unfold SummaryEvaluation.
        exact HBodySummary.
      }
      assert (HBodyComp :
        CheckedCountedComputationEvaluation n_body heap
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ec phi_body heap_final v_final).
      {
        unfold CheckedCountedComputationEvaluation.
        exact HBody.
      }
      assert (HCoveredBody : TraceCoveredBySummary phi_body theta).
      {
        eapply
          (HBelow n_body
            ((x, ty_arg_body) ::
              (f, TyArrow ty_arg_body eff_body ty_body eff_summary) ::
              gamma_body)
            omega_body heap
            (env_extend x arg
              (env_extend f
                (VClosure closure_env closure_rho f x ec ee)
                closure_env))
            closure_rho ec ee
            phi_body heap_final v_final
            phi_body_summary heap_summary theta).
        - exact HCountBody.
        - exact HBodyBack.
        - exact HBodyContext.
        - exact HBodyComp.
        - exact HBodySummaryEval.
      }
      subst phi.
      apply trace_covered_app_same.
      * exact HCoveredFun.
	      * apply trace_covered_app_same.
	        -- exact HCoveredArg.
	        -- exact HCoveredBody.
Qed.

Theorem EEffApp_checked_execution_counted_summary_trace_covered_from_store_entry_at :
  forall n_eval gamma omega heap env rho ef ea phi heap_final theta,
    CheckedExecutionStoreContextSmallStepCorrectnessBelow n_eval ->
    CheckedExecutionStoreSummaryValueSoundnessBelow n_eval ->
    CheckedBackTriangle gamma omega
      (EMuApp ef ea) (EEffApp ef ea) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CheckedCountedComputationEvaluation n_eval heap env rho
      (EEffApp ef ea) phi heap_final (VSummary theta) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n_eval gamma omega heap env rho ef ea phi heap_final theta
    HBelow HSummaryValueBelow HBack HContext HComputationTraceSound
    HComp.
  destruct
    (CBT_App_components gamma omega ef ea HBack)
    as (_ty_mu & _eff_mu & eff_eff & ty_ef & ty_ea &
      eff_ef & eff_ea & _HCheckedApp & HCheckedEffApp &
      HCheckedFun & HCheckedArg & HStaticEff &
      HStaticFun & HStaticArg & HBackFun & HBackArg).
  assert
    (HSummaryEval :
      SummaryEvaluation heap env rho (EEffApp ef ea)
        phi heap_final theta).
  {
    unfold SummaryEvaluation.
    unfold CheckedCountedComputationEvaluation in HComp.
    eapply StepsN_to_Steps.
    eapply CheckedStepsN_to_StepsN_done.
    exact HComp.
  }
  destruct
    (checked_execution_store_counted_computation_heap_neutral
      n_eval gamma omega heap env rho
      (EEffApp ef ea) TyEffect eff_eff
      phi heap_final (VSummary theta)
      HContext HComputationTraceSound HCheckedEffApp
      HStaticEff HComp)
    as (HHeapFinal & _HNeutralSummary).
  subst heap_final.
  unfold CheckedCountedComputationEvaluation in HComp.
  destruct
    (CheckedEEffApp_counted_decomposition
      n_eval heap env rho ef ea phi heap theta HComp)
    as (n_fun & n_arg & n_summary &
      phi_fun & phi_arg & phi_summary &
      closure_env & closure_rho & f & x & ec & ee & arg &
      heap_arg & heap_fun & HFun & HArg & HBody &
      HCountFun & HCountArg & HCountSummary & HTrace).
  assert
    (HFunComp :
      CheckedCountedComputationEvaluation n_fun heap env rho ef
        phi_fun heap_fun
        (VClosure closure_env closure_rho f x ec ee)).
  {
    unfold CheckedCountedComputationEvaluation.
    exact HFun.
  }
  destruct
    (checked_execution_store_counted_computation_heap_neutral
      n_fun gamma omega heap env rho ef ty_ef eff_ef
      phi_fun heap_fun (VClosure closure_env closure_rho f x ec ee)
      HContext HComputationTraceSound HCheckedFun HStaticFun HFunComp)
    as (HHeapFun & _HNeutralFun).
  subst heap_fun.
  assert
    (HArgComp :
      CheckedCountedComputationEvaluation n_arg heap env rho ea
        phi_arg heap_arg arg).
  {
    unfold CheckedCountedComputationEvaluation.
    exact HArg.
  }
  destruct
    (checked_execution_store_counted_computation_heap_neutral
      n_arg gamma omega heap env rho ea ty_ea eff_ea
      phi_arg heap_arg arg
      HContext HComputationTraceSound HCheckedArg HStaticArg HArgComp)
    as (HHeapArg & _HNeutralArg).
  subst heap_arg.
  assert (HFunRaw :
    StepsN n_fun
      (InitialState heap env rho ef)
      phi_fun
      (StDone heap
        (VClosure closure_env closure_rho f x ec ee))).
  {
    eapply CheckedStepsN_to_StepsN_done.
    exact HFun.
  }
  assert (HArgRaw :
    StepsN n_arg
      (InitialState heap env rho ea)
      phi_arg
      (StDone heap arg)).
  {
    eapply CheckedStepsN_to_StepsN_done.
    exact HArg.
  }
  destruct
    (EEffApp_checked_summary_body_store_context_from_prefixes
      gamma omega heap env rho ef ea
      n_fun n_arg phi_fun phi_arg
      closure_env closure_rho f x ec ee arg
      HBack HContext HFunRaw HArgRaw)
    as (gamma_body & omega_body & ty_arg_body & ty_body &
      eff_body & eff_summary & HBodyContext & _HCheckedBody &
      HCheckedSummary & HBodyBack).
  assert (HCoveredFun : TraceCoveredBySummary phi_fun theta).
  {
    eapply
      (HBelow
        n_fun gamma omega heap env rho
        ef (EEffApp ef ea)
        phi_fun heap
        (VClosure closure_env closure_rho f x ec ee)
        phi heap theta).
    - exact HCountFun.
    - exact HBackFun.
    - exact HContext.
    - exact HFunComp.
    - exact HSummaryEval.
  }
  assert (HCoveredArg : TraceCoveredBySummary phi_arg theta).
  {
    eapply
      (HBelow
        n_arg gamma omega heap env rho
        ea (EEffApp ef ea)
        phi_arg heap arg
        phi heap theta).
    - exact HCountArg.
    - exact HBackArg.
    - exact HContext.
    - exact HArgComp.
    - exact HSummaryEval.
  }
  assert (HBodyComp :
    CheckedCountedComputationEvaluation n_summary heap
      (env_extend x arg
        (env_extend f
          (VClosure closure_env closure_rho f x ec ee)
          closure_env))
      closure_rho ee phi_summary heap (VSummary theta)).
  {
    unfold CheckedCountedComputationEvaluation.
    exact HBody.
  }
  assert (HCoveredSummary : TraceCoveredBySummary phi_summary theta).
  {
    eapply
      (HSummaryValueBelow
        n_summary
        ((x, ty_arg_body) ::
          (f, TyArrow ty_arg_body eff_body ty_body eff_summary) ::
          gamma_body)
        omega_body heap
        (env_extend x arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho ec ee eff_summary
        phi_summary heap theta).
    - exact HCountSummary.
    - exact HBodyBack.
    - exact HCheckedSummary.
    - exact HBodyContext.
    - exact HBodyComp.
  }
  subst phi.
  apply trace_covered_app_same.
  - exact HCoveredFun.
  - apply trace_covered_app_same; assumption.
Qed.

Theorem ERgnApp_checked_execution_store_context_case_from_below :
  forall n gamma omega heap env rho er r
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedExecutionStoreContextSmallStepCorrectnessBelow n ->
    CheckedBackTriangle gamma omega (ERgnApp er r) EEmpty ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedCountedComputationEvaluation n heap env rho
      (ERgnApp er r) phi heap_final v_final ->
    SummaryEvaluation heap env rho EEmpty
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho er r
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext HComp _HSummary.
  destruct
    (CBT_RgnApp_components gamma omega er r HBack)
    as (ty_er & eff_er & _ty_app & _eff_app &
      HCheckedEr & _HCheckedApp & HBackEr).
  unfold CheckedCountedComputationEvaluation in HComp.
  destruct
    (CheckedERgnApp_counted_decomposition
      n heap env rho er r phi heap_final v_final HComp)
    as (n_fun & n_body & phi_fun & phi_body &
      closure_env & closure_rho & x & e & heap_fun & r_val &
      HRgn & HFun & HBody & HCountFun & HCountBody & HTrace).
  assert
    (HFunCovered :
      TraceCoveredBySummary phi_fun
        (SummarySet ([] : list ComputedAction))).
  {
    eapply
      (HBelow n_fun gamma omega heap env rho er EEmpty
        phi_fun heap_fun
        (VRegionClosure closure_env closure_rho x e)
        ([] : Trace) heap
        (SummarySet ([] : list ComputedAction))).
    - exact HCountFun.
    - exact HBackEr.
    - exact HContext.
    - unfold CheckedCountedComputationEvaluation. exact HFun.
    - apply App_EEmpty_summary_evaluation.
  }
  pose proof
    (trace_covered_empty_summary_nil phi_fun HFunCovered)
    as HFunNil.
  assert
    (HFunComp :
      CheckedCountedComputationEvaluation n_fun heap env rho er
        phi_fun heap_fun
        (VRegionClosure closure_env closure_rho x e)).
  {
    unfold CheckedCountedComputationEvaluation.
    exact HFun.
  }
  destruct
    (checked_execution_store_counted_computation_store_value_shape
      n_fun gamma omega heap env rho er ty_er eff_er
      phi_fun heap_fun
      (VRegionClosure closure_env closure_rho x e)
      HContext HCheckedEr HFunComp)
    as (store_fun & ty_fun_res & HBoundedFun & HHeapFun & HValFun).
  destruct
    (StoreResolvedValShape_region_closure_inv
      store_fun closure_env closure_rho x e ty_fun_res HValFun)
    as (gamma_body & omega_body & ty_body & _ty_body_res &
      eff_body & _eff_body_res & _HTyFun & HEnvBody &
      HRhoBody & _HEffResolveBody & _HTyResolveBody & HBodyChecked).
  assert
    (HBodyContext :
      CheckedStoreRuntimeContext gamma_body (x :: omega_body)
        heap_fun closure_env
        (rho_extend x r_val closure_rho)).
  {
    split.
    - exists store_fun.
      unfold StoreResolvedRuntimeShape.
      split; [exact HBoundedFun |].
      split; [exact HHeapFun |].
      eapply StoreResolvedEnvShape_extend_fresh;
        eauto using
          CheckedRegionBody_fresh,
          CheckedRegionBody_ctx_wf.
    - eapply RhoModels_extend; eauto.
  }
  assert
    (HBodyCovered :
      TraceCoveredBySummary phi_body
        (SummarySet ([] : list ComputedAction))).
  {
    eapply
      (HBelow n_body gamma_body (x :: omega_body)
        heap_fun closure_env
        (rho_extend x r_val closure_rho)
        e EEmpty phi_body heap_final v_final
        ([] : Trace) heap_fun
        (SummarySet ([] : list ComputedAction))).
    - exact HCountBody.
    - exact
        (CheckedRegionBody_backtriangle
          x gamma_body omega_body e ty_body eff_body HBodyChecked).
    - exact HBodyContext.
    - unfold CheckedCountedComputationEvaluation. exact HBody.
    - apply App_EEmpty_summary_evaluation.
  }
  pose proof
    (trace_covered_empty_summary_nil phi_body HBodyCovered)
    as HBodyNil.
  subst phi.
  rewrite HFunNil, HBodyNil.
  simpl.
  apply trace_covered_nil.
Qed.

Theorem ECond_checked_execution_store_context_case_from_below :
  forall n gamma omega heap env rho
    e et ef efft efff phi heap_final v_final
    phi_summary heap_summary theta,
    CheckedExecutionStoreContextSmallStepCorrectnessBelow n ->
    CheckedBackTriangle gamma omega
      (ECond e et ef) (ECond e efft efff) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedCountedComputationEvaluation n heap env rho
      (ECond e et ef) phi heap_final v_final ->
    SummaryEvaluation heap env rho
      (ECond e efft efff) phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho
    e et ef efft efff phi heap_final v_final
    phi_summary heap_summary theta
    HBelow HBack HContext HComp HSummary.
  destruct
    (CBT_Cond_components
      gamma omega e et ef efft efff HBack)
    as (eff_e & ty & ty_t & ty_f & eff_et & eff_ef &
      HCheckedCond & _ & _ & _ & HBackCond & HBackThen & HBackElse).
  unfold CheckedCountedComputationEvaluation in HComp.
  destruct
    (CheckedECond_counted_decomposition
      n heap env rho e et ef phi heap_final v_final HComp)
    as (n_cond & n_branch & phi_cond & b & heap_cond &
      phi_branch & HCond & HBranch & HTrace & HCountCond &
      HCountBranch).
  unfold SummaryEvaluation in HSummary.
  destruct
    (ECond_decomposition
      heap env rho e efft efff phi_summary heap_summary
      (VSummary theta) HSummary)
    as (phi_cond_summary & b_summary & heap_cond_summary &
      phi_branch_summary & HCondSummary & HBranchSummary &
      _HTraceSummary).
  destruct
    (Steps_terminal_trace_deterministic
      (InitialState heap env rho e)
      phi_cond heap_cond (VBool b)
      phi_cond_summary heap_cond_summary (VBool b_summary))
    as (HTraceCond & HHeapCond & HValCond).
  - eapply StepsN_to_Steps.
    eapply CheckedStepsN_to_StepsN_done.
    exact HCond.
  - exact HCondSummary.
  - inversion HValCond; subst b_summary.
    subst phi_cond_summary heap_cond_summary.
    assert
      (TraceCoveredBySummary phi_cond
        (SummarySet ([] : list ComputedAction))) as HCoverCond.
    {
      eapply
        (HBelow n_cond gamma omega heap env rho e EEmpty
          phi_cond heap_cond (VBool b)
          ([] : Trace) heap (SummarySet ([] : list ComputedAction))).
      - exact HCountCond.
      - exact HBackCond.
      - exact HContext.
      - unfold CheckedCountedComputationEvaluation. exact HCond.
      - apply EEmpty_summary_evaluation.
    }
    pose proof
      (trace_covered_empty_summary_nil phi_cond HCoverCond)
      as HCondNil.
    assert
      (CheckedStoreRuntimeContext gamma omega heap_cond env rho)
      as HContextBranch.
    {
      eapply
        (checked_execution_store_runtime_context_after_counted
          n_cond gamma omega heap env rho e TyBool eff_e
          phi_cond heap_cond (VBool b)); eauto.
    }
    subst phi.
    rewrite HCondNil.
    simpl.
    destruct b.
    + simpl in HBranch, HBranchSummary.
      eapply
        (HBelow n_branch gamma omega heap_cond env rho et efft
          phi_branch heap_final v_final phi_branch_summary
          heap_summary theta).
      * exact HCountBranch.
      * exact HBackThen.
      * exact HContextBranch.
      * unfold CheckedCountedComputationEvaluation. exact HBranch.
      * unfold SummaryEvaluation. exact HBranchSummary.
    + simpl in HBranch, HBranchSummary.
      eapply
        (HBelow n_branch gamma omega heap_cond env rho ef efff
          phi_branch heap_final v_final phi_branch_summary
          heap_summary theta).
      * exact HCountBranch.
      * exact HBackElse.
      * exact HContextBranch.
      * unfold CheckedCountedComputationEvaluation. exact HBranch.
      * unfold SummaryEvaluation. exact HBranchSummary.
Qed.

Theorem ERef_checked_execution_store_context_case_from_below :
  forall n gamma omega heap env rho r e eff
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedExecutionStoreContextSmallStepCorrectnessBelow n ->
    CheckedBackTriangle gamma omega
      (ERef r e) (EConcat eff (EAllocAbs r)) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedCountedComputationEvaluation n heap env rho
      (ERef r e) phi heap_final v_final ->
    SummaryEvaluation heap env rho (EConcat eff (EAllocAbs r))
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho r e eff
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext HComp HSummary.
  destruct
    (CBT_Ref_components gamma omega r e eff HBack)
    as (_ty & _static & _ty_ref & _eff_ref &
      _HCheckedExpr & _HCheckedRef & HBackExpr).
  unfold CheckedCountedComputationEvaluation in HComp.
  destruct
    (CheckedERef_counted_decomposition
      n heap env rho r e phi heap_final v_final HComp)
    as (n_e & phi_e & heap_e & v & r_val & l & HRgn &
      HExpr & _HAlloc & HLoc & HTrace & HCountExpr).
  subst v_final phi.
  unfold SummaryEvaluation in HSummary.
  destruct
    (EConcat_decomposition
      heap env rho eff (EAllocAbs r)
      phi_summary heap_summary theta HSummary)
    as (phi_summary_e & phi_summary_alloc & theta_e & theta_alloc &
      heap_summary_e & heap_summary_alloc & HSummaryExpr &
      HSummaryAlloc & HTheta & _HHeapSummary & _HTraceSummary).
  destruct
    (EAllocAbs_terminal_summary
      heap_summary_e env rho r phi_summary_alloc
      heap_summary_alloc theta_alloc HSummaryAlloc)
    as (r_summary & HRgnSummary & _HHeapAlloc & HThetaAlloc &
      _HTraceAlloc).
  rewrite HRgn in HRgnSummary.
  inversion HRgnSummary; subst r_summary.
  subst theta_alloc theta.
  assert (HCoveredExpr : TraceCoveredBySummary phi_e theta_e).
  {
    eapply
      (HBelow n_e gamma omega heap env rho e eff
        phi_e heap_e v phi_summary_e heap_summary_e theta_e).
    - exact HCountExpr.
    - exact HBackExpr.
    - exact HContext.
    - unfold CheckedCountedComputationEvaluation. exact HExpr.
    - unfold SummaryEvaluation. exact HSummaryExpr.
  }
  eapply trace_covered_app_summary_union; eauto.
  apply trace_covered_single_alloc_abs.
Qed.

Theorem EDeref_checked_execution_store_context_case_from_below :
  forall n gamma omega heap env rho r e eff
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedExecutionStoreContextSmallStepCorrectnessBelow n ->
    CheckedBackTriangle gamma omega
      (EDeref r e) (EConcat eff (EReadAbs r)) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedCountedComputationEvaluation n heap env rho
      (EDeref r e) phi heap_final v_final ->
    SummaryEvaluation heap env rho (EConcat eff (EReadAbs r))
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho r e eff
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext HComp HSummary.
  destruct
    (CBT_Deref_components gamma omega r e eff HBack)
    as (_ty & _static & ty_deref & eff_deref &
      _HCheckedExpr & HCheckedDeref & HBackExpr).
  destruct
    (CheckedTcExp_deref_child_ref_from_deref
      gamma omega r e ty_deref eff_deref HCheckedDeref)
    as (ty_cell & eff_child & HCheckedChildRef).
  unfold CheckedCountedComputationEvaluation in HComp.
  destruct
    (CheckedEDeref_counted_decomposition
      n heap env rho r e phi heap_final v_final HComp)
    as (n_e & phi_e & heap_e & r_loc & l & HExpr &
      _HLookup & HHeapFinal & HTrace & HCountExpr).
  subst heap_final phi.
  assert
    (HExprComp :
      CheckedCountedComputationEvaluation n_e heap env rho e
        phi_e heap_e (VLoc r_loc l)).
  {
    unfold CheckedCountedComputationEvaluation.
    exact HExpr.
  }
  destruct
    (checked_execution_store_counted_computation_store_value_shape_resolved
      n_e gamma omega heap env rho e
      (TyRef (region_expr_to_type r) ty_cell) eff_child
      phi_e heap_e (VLoc r_loc l) HContext HCheckedChildRef
      HExprComp)
    as (store_e & ty_res & HResolveChild & _HBoundedExpr &
      _HHeapExpr & HValLoc).
  pose proof
    (StoreResolvedValShape_loc_ref_region
      store_e rho r ty_cell ty_res r_loc l
      HResolveChild HValLoc)
    as HRegionLoc.
  unfold SummaryEvaluation in HSummary.
  destruct
    (EConcat_decomposition
      heap env rho eff (EReadAbs r)
      phi_summary heap_summary theta HSummary)
    as (phi_summary_e & phi_summary_read & theta_e & theta_read &
      heap_summary_e & heap_summary_read & HSummaryExpr &
      HSummaryRead & HTheta & _HHeapSummary & _HTraceSummary).
  destruct
    (EReadAbs_terminal_summary
      heap_summary_e env rho r phi_summary_read
      heap_summary_read theta_read HSummaryRead)
    as (r_summary & HRgnSummary & _HHeapRead & HThetaRead &
      _HTraceRead).
  rewrite HRegionLoc in HRgnSummary.
  inversion HRgnSummary; subst r_summary.
  subst theta_read theta.
  assert (HCoveredExpr : TraceCoveredBySummary phi_e theta_e).
  {
    eapply
      (HBelow n_e gamma omega heap env rho e eff
        phi_e heap_e (VLoc r_loc l)
        phi_summary_e heap_summary_e theta_e).
    - exact HCountExpr.
    - exact HBackExpr.
    - exact HContext.
    - exact HExprComp.
    - unfold SummaryEvaluation. exact HSummaryExpr.
  }
  eapply trace_covered_app_summary_union; eauto.
  apply trace_covered_single_read_abs.
Qed.

Theorem EAssign_checked_execution_store_context_case_from_below :
  forall n gamma omega heap env rho r e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedExecutionStoreContextSmallStepCorrectnessBelow n ->
    CheckedBackTriangle gamma omega
      (EAssign r e1 e2) (EConcat eff1 (EConcat eff2 (EWriteAbs r))) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CheckedCountedComputationEvaluation n heap env rho
      (EAssign r e1 e2) phi heap_final v_final ->
    SummaryEvaluation heap env rho
      (EConcat eff1 (EConcat eff2 (EWriteAbs r)))
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho r e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext HComputationTraceSound HComp HSummary.
  destruct
    (CBT_Assign_components gamma omega r e1 e2 eff1 eff2 HBack)
    as (ty_addr & static_addr & ty_assign & eff_assign &
      HCheckedAddr & HCheckedAssign & HNeutralAddr &
      HBackAddr & HBackVal).
  destruct
    (CheckedTcExp_assign_children_from_assign
      gamma omega r e1 e2 ty_assign eff_assign HCheckedAssign)
    as (ty_cell & eff_addr_ref & _eff_val &
      HCheckedAddrRef & _HCheckedVal).
  unfold CheckedCountedComputationEvaluation in HComp.
  destruct
    (CheckedEAssign_counted_decomposition
      n heap env rho r e1 e2 phi heap_final v_final HComp)
    as (n_addr & n_val & phi_addr & phi_val &
      heap_addr & heap_val & r_loc & l & v &
      HAddr & HVal & HHeapFinal & HUnit & HTrace &
      HCountAddr & HCountVal).
  subst heap_final v_final phi.
  assert
    (HAddrComp :
      CheckedCountedComputationEvaluation n_addr heap env rho e1
        phi_addr heap_addr (VLoc r_loc l)).
  {
    unfold CheckedCountedComputationEvaluation.
    exact HAddr.
  }
  destruct
    (checked_execution_store_counted_computation_heap_neutral
      n_addr gamma omega heap env rho e1 ty_addr static_addr
      phi_addr heap_addr (VLoc r_loc l)
      HContext HComputationTraceSound HCheckedAddr HNeutralAddr
      HAddrComp)
    as (HHeapAddr & _HAddrNeutralTrace).
  subst heap_addr.
  assert
    (HAddrCompHeap :
      CheckedCountedComputationEvaluation n_addr heap env rho e1
        phi_addr heap (VLoc r_loc l)).
  {
    exact HAddrComp.
  }
  destruct
    (checked_execution_store_counted_computation_store_value_shape_resolved
      n_addr gamma omega heap env rho e1
      (TyRef (region_expr_to_type r) ty_cell) eff_addr_ref
      phi_addr heap (VLoc r_loc l) HContext HCheckedAddrRef
      HAddrCompHeap)
    as (store_addr & ty_res_addr & HResolveAddr & _HBoundedAddr &
      _HHeapAddr & HValLoc).
  pose proof
    (StoreResolvedValShape_loc_ref_region
      store_addr rho r ty_cell ty_res_addr r_loc l
      HResolveAddr HValLoc)
    as HRegionLoc.
  unfold SummaryEvaluation in HSummary.
  destruct
    (EConcat_decomposition
      heap env rho eff1 (EConcat eff2 (EWriteAbs r))
      phi_summary heap_summary theta HSummary)
    as (phi_summary_addr & phi_summary_rest &
      theta_addr & theta_rest & heap_summary_addr &
      heap_summary_rest & HSummaryAddr & HSummaryRest &
      HTheta & _HHeapSummary & _HTraceSummary).
  destruct
    (CheckedBackTriangle_summary_checked_heap_neutral
      gamma omega e1 eff1 HBackAddr)
    as (eff_summary_addr & HCheckedSummaryAddr &
      HNeutralSummaryAddr).
  destruct
    (Steps_to_StepsN
      (InitialState heap env rho eff1)
      phi_summary_addr
      (StDone heap_summary_addr (VSummary theta_addr))
      HSummaryAddr)
    as (n_summary_addr & HSummaryAddrN).
  destruct
    (checked_store_counted_computation_heap_neutral
      n_summary_addr gamma omega heap env rho eff1
      TyEffect eff_summary_addr
      phi_summary_addr heap_summary_addr (VSummary theta_addr)
      HContext HComputationTraceSound HCheckedSummaryAddr
      HNeutralSummaryAddr)
    as (HHeapSummaryAddr & _HSummaryAddrNeutralTrace).
  {
    unfold CountedComputationEvaluation.
    exact HSummaryAddrN.
  }
  subst heap_summary_addr.
  destruct
    (EConcat_decomposition
      heap env rho eff2 (EWriteAbs r)
      phi_summary_rest heap_summary_rest theta_rest HSummaryRest)
    as (phi_summary_val & phi_summary_write &
      theta_val & theta_write & heap_summary_val &
      heap_summary_write & HSummaryVal & HSummaryWrite &
      HThetaRest & _HHeapSummaryRest & _HTraceSummaryRest).
  destruct
    (EWriteAbs_terminal_summary
      heap_summary_val env rho r phi_summary_write
      heap_summary_write theta_write HSummaryWrite)
    as (r_summary & HRgnSummary & _HHeapWrite & HThetaWrite &
      _HTraceWrite).
  rewrite HRegionLoc in HRgnSummary.
  inversion HRgnSummary; subst r_summary.
  subst theta_write theta_rest theta.
  assert (HCoveredAddr : TraceCoveredBySummary phi_addr theta_addr).
  {
    eapply
      (HBelow n_addr gamma omega heap env rho e1 eff1
        phi_addr heap (VLoc r_loc l)
        phi_summary_addr heap theta_addr).
    - exact HCountAddr.
    - exact HBackAddr.
    - exact HContext.
    - exact HAddrCompHeap.
    - unfold SummaryEvaluation. exact HSummaryAddr.
  }
  assert (HCoveredVal : TraceCoveredBySummary phi_val theta_val).
  {
    eapply
      (HBelow n_val gamma omega heap env rho e2 eff2
        phi_val heap_val v
        phi_summary_val heap_summary_val theta_val).
    - exact HCountVal.
    - exact HBackVal.
    - exact HContext.
    - unfold CheckedCountedComputationEvaluation. exact HVal.
    - unfold SummaryEvaluation. exact HSummaryVal.
  }
  eapply trace_covered_app_summary_union; eauto.
  eapply trace_covered_app_summary_union; eauto.
  apply trace_covered_single_write_abs.
Qed.

Theorem EPlus_checked_execution_store_context_case_from_below :
  forall n gamma omega heap env rho e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedExecutionStoreContextSmallStepCorrectnessBelow n ->
    CheckedBackTriangle gamma omega
      (EPlus e1 e2) (EConcat eff1 eff2) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CheckedCountedComputationEvaluation n heap env rho
      (EPlus e1 e2) phi heap_final v_final ->
    SummaryEvaluation heap env rho (EConcat eff1 eff2)
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext HComputationTraceSound HComp HSummary.
  destruct
    (CBT_Plus_components gamma omega e1 e2 eff1 eff2 HBack)
    as (eff_static & eff_e1 & HCheckedPlus & HCheckedLeft &
      HNeutralLeft & HBackLeft & HBackRight).
  destruct
    (checked_execution_store_counted_tynat_value_is_nat
      n gamma omega heap env rho (EPlus e1 e2) eff_static
      phi heap_final v_final HContext HCheckedPlus HComp)
    as (n_final & HFinalNat).
  subst v_final.
  unfold CheckedCountedComputationEvaluation in HComp.
  destruct
    (CheckedEPlus_counted_decomposition
      n heap env rho e1 e2 phi heap_final n_final HComp)
    as (n1_steps & n2_steps & phi1 & phi2 & n1 & n2 &
      heap1 & heap2 & HLeft & HRight & _HResult & HHeapFinal &
      HTrace & HCountLeft & HCountRight).
  subst heap_final.
  unfold SummaryEvaluation in HSummary.
  destruct
    (EConcat_decomposition
      heap env rho eff1 eff2 phi_summary heap_summary theta HSummary)
    as (phi_summary1 & phi_summary2 & theta1 & theta2 &
      heap_summary1 & heap_summary2 & HSummary1 & HSummary2 &
      HTheta & _HHeapSummary & _HTraceSummary).
  destruct
    (CheckedBackTriangle_summary_checked_heap_neutral
      gamma omega e1 eff1 HBackLeft)
    as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
  destruct
    (Steps_to_StepsN
      (InitialState heap env rho eff1)
      phi_summary1
      (StDone heap_summary1 (VSummary theta1))
      HSummary1)
    as (n_summary1 & HSummary1N).
  destruct
    (checked_store_counted_computation_heap_neutral
      n_summary1 gamma omega heap env rho eff1 TyEffect eff_summary1
      phi_summary1 heap_summary1 (VSummary theta1)
      HContext HComputationTraceSound HCheckedSummary1 HNeutralSummary1)
    as (HHeapSummary1 & _).
  {
    unfold CountedComputationEvaluation.
    exact HSummary1N.
  }
  subst heap_summary1.
  assert
    (HLeftComp :
      CheckedCountedComputationEvaluation n1_steps heap env rho e1
        phi1 heap1 (VNat n1)).
  {
    unfold CheckedCountedComputationEvaluation.
    exact HLeft.
  }
  destruct
    (checked_execution_store_counted_computation_heap_neutral
      n1_steps gamma omega heap env rho e1 TyNat eff_e1
      phi1 heap1 (VNat n1)
      HContext HComputationTraceSound HCheckedLeft HNeutralLeft
      HLeftComp)
    as (HHeap1 & _).
  subst heap1.
  assert
    (HLeftCompHeap :
      CheckedCountedComputationEvaluation n1_steps heap env rho e1
        phi1 heap (VNat n1)).
  {
    exact HLeftComp.
  }
  assert (HCoveredLeft : TraceCoveredBySummary phi1 theta1).
  {
    eapply
      (HBelow n1_steps gamma omega heap env rho e1 eff1
        phi1 heap (VNat n1) phi_summary1 heap theta1).
    - exact HCountLeft.
    - exact HBackLeft.
    - exact HContext.
    - exact HLeftCompHeap.
    - unfold SummaryEvaluation. exact HSummary1.
  }
  assert (HCoveredRight : TraceCoveredBySummary phi2 theta2).
  {
    eapply
      (HBelow n2_steps gamma omega heap env rho e2 eff2
        phi2 heap2 (VNat n2) phi_summary2 heap_summary2 theta2).
    - exact HCountRight.
    - exact HBackRight.
    - exact HContext.
    - unfold CheckedCountedComputationEvaluation. exact HRight.
    - unfold SummaryEvaluation. exact HSummary2.
  }
  subst phi theta.
  eapply trace_covered_app_summary_union; eauto.
Qed.

Theorem EMinus_checked_execution_store_context_case_from_below :
  forall n gamma omega heap env rho e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedExecutionStoreContextSmallStepCorrectnessBelow n ->
    CheckedBackTriangle gamma omega
      (EMinus e1 e2) (EConcat eff1 eff2) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CheckedCountedComputationEvaluation n heap env rho
      (EMinus e1 e2) phi heap_final v_final ->
    SummaryEvaluation heap env rho (EConcat eff1 eff2)
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext HComputationTraceSound HComp HSummary.
  destruct
    (CBT_Minus_components gamma omega e1 e2 eff1 eff2 HBack)
    as (eff_static & eff_e1 & HCheckedMinus & HCheckedLeft &
      HNeutralLeft & HBackLeft & HBackRight).
  destruct
    (checked_execution_store_counted_tynat_value_is_nat
      n gamma omega heap env rho (EMinus e1 e2) eff_static
      phi heap_final v_final HContext HCheckedMinus HComp)
    as (n_final & HFinalNat).
  subst v_final.
  unfold CheckedCountedComputationEvaluation in HComp.
  destruct
    (CheckedEMinus_counted_decomposition
      n heap env rho e1 e2 phi heap_final n_final HComp)
    as (n1_steps & n2_steps & phi1 & phi2 & n1 & n2 &
      heap1 & heap2 & HLeft & HRight & _HResult & HHeapFinal &
      HTrace & HCountLeft & HCountRight).
  subst heap_final.
  unfold SummaryEvaluation in HSummary.
  destruct
    (EConcat_decomposition
      heap env rho eff1 eff2 phi_summary heap_summary theta HSummary)
    as (phi_summary1 & phi_summary2 & theta1 & theta2 &
      heap_summary1 & heap_summary2 & HSummary1 & HSummary2 &
      HTheta & _HHeapSummary & _HTraceSummary).
  destruct
    (CheckedBackTriangle_summary_checked_heap_neutral
      gamma omega e1 eff1 HBackLeft)
    as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
  destruct
    (Steps_to_StepsN
      (InitialState heap env rho eff1)
      phi_summary1
      (StDone heap_summary1 (VSummary theta1))
      HSummary1)
    as (n_summary1 & HSummary1N).
  destruct
    (checked_store_counted_computation_heap_neutral
      n_summary1 gamma omega heap env rho eff1 TyEffect eff_summary1
      phi_summary1 heap_summary1 (VSummary theta1)
      HContext HComputationTraceSound HCheckedSummary1 HNeutralSummary1)
    as (HHeapSummary1 & _).
  {
    unfold CountedComputationEvaluation.
    exact HSummary1N.
  }
  subst heap_summary1.
  assert
    (HLeftComp :
      CheckedCountedComputationEvaluation n1_steps heap env rho e1
        phi1 heap1 (VNat n1)).
  {
    unfold CheckedCountedComputationEvaluation.
    exact HLeft.
  }
  destruct
    (checked_execution_store_counted_computation_heap_neutral
      n1_steps gamma omega heap env rho e1 TyNat eff_e1
      phi1 heap1 (VNat n1)
      HContext HComputationTraceSound HCheckedLeft HNeutralLeft
      HLeftComp)
    as (HHeap1 & _).
  subst heap1.
  assert
    (HLeftCompHeap :
      CheckedCountedComputationEvaluation n1_steps heap env rho e1
        phi1 heap (VNat n1)).
  {
    exact HLeftComp.
  }
  assert (HCoveredLeft : TraceCoveredBySummary phi1 theta1).
  {
    eapply
      (HBelow n1_steps gamma omega heap env rho e1 eff1
        phi1 heap (VNat n1) phi_summary1 heap theta1).
    - exact HCountLeft.
    - exact HBackLeft.
    - exact HContext.
    - exact HLeftCompHeap.
    - unfold SummaryEvaluation. exact HSummary1.
  }
  assert (HCoveredRight : TraceCoveredBySummary phi2 theta2).
  {
    eapply
      (HBelow n2_steps gamma omega heap env rho e2 eff2
        phi2 heap2 (VNat n2) phi_summary2 heap_summary2 theta2).
    - exact HCountRight.
    - exact HBackRight.
    - exact HContext.
    - unfold CheckedCountedComputationEvaluation. exact HRight.
    - unfold SummaryEvaluation. exact HSummary2.
  }
  subst phi theta.
  eapply trace_covered_app_summary_union; eauto.
Qed.

Theorem ETimes_checked_execution_store_context_case_from_below :
  forall n gamma omega heap env rho e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedExecutionStoreContextSmallStepCorrectnessBelow n ->
    CheckedBackTriangle gamma omega
      (ETimes e1 e2) (EConcat eff1 eff2) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CheckedCountedComputationEvaluation n heap env rho
      (ETimes e1 e2) phi heap_final v_final ->
    SummaryEvaluation heap env rho (EConcat eff1 eff2)
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext HComputationTraceSound HComp HSummary.
  destruct
    (CBT_Times_components gamma omega e1 e2 eff1 eff2 HBack)
    as (eff_static & eff_e1 & HCheckedTimes & HCheckedLeft &
      HNeutralLeft & HBackLeft & HBackRight).
  destruct
    (checked_execution_store_counted_tynat_value_is_nat
      n gamma omega heap env rho (ETimes e1 e2) eff_static
      phi heap_final v_final HContext HCheckedTimes HComp)
    as (n_final & HFinalNat).
  subst v_final.
  unfold CheckedCountedComputationEvaluation in HComp.
  destruct
    (CheckedETimes_counted_decomposition
      n heap env rho e1 e2 phi heap_final n_final HComp)
    as (n1_steps & n2_steps & phi1 & phi2 & n1 & n2 &
      heap1 & heap2 & HLeft & HRight & _HResult & HHeapFinal &
      HTrace & HCountLeft & HCountRight).
  subst heap_final.
  unfold SummaryEvaluation in HSummary.
  destruct
    (EConcat_decomposition
      heap env rho eff1 eff2 phi_summary heap_summary theta HSummary)
    as (phi_summary1 & phi_summary2 & theta1 & theta2 &
      heap_summary1 & heap_summary2 & HSummary1 & HSummary2 &
      HTheta & _HHeapSummary & _HTraceSummary).
  destruct
    (CheckedBackTriangle_summary_checked_heap_neutral
      gamma omega e1 eff1 HBackLeft)
    as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
  destruct
    (Steps_to_StepsN
      (InitialState heap env rho eff1)
      phi_summary1
      (StDone heap_summary1 (VSummary theta1))
      HSummary1)
    as (n_summary1 & HSummary1N).
  destruct
    (checked_store_counted_computation_heap_neutral
      n_summary1 gamma omega heap env rho eff1 TyEffect eff_summary1
      phi_summary1 heap_summary1 (VSummary theta1)
      HContext HComputationTraceSound HCheckedSummary1 HNeutralSummary1)
    as (HHeapSummary1 & _).
  {
    unfold CountedComputationEvaluation.
    exact HSummary1N.
  }
  subst heap_summary1.
  assert
    (HLeftComp :
      CheckedCountedComputationEvaluation n1_steps heap env rho e1
        phi1 heap1 (VNat n1)).
  {
    unfold CheckedCountedComputationEvaluation.
    exact HLeft.
  }
  destruct
    (checked_execution_store_counted_computation_heap_neutral
      n1_steps gamma omega heap env rho e1 TyNat eff_e1
      phi1 heap1 (VNat n1)
      HContext HComputationTraceSound HCheckedLeft HNeutralLeft
      HLeftComp)
    as (HHeap1 & _).
  subst heap1.
  assert
    (HLeftCompHeap :
      CheckedCountedComputationEvaluation n1_steps heap env rho e1
        phi1 heap (VNat n1)).
  {
    exact HLeftComp.
  }
  assert (HCoveredLeft : TraceCoveredBySummary phi1 theta1).
  {
    eapply
      (HBelow n1_steps gamma omega heap env rho e1 eff1
        phi1 heap (VNat n1) phi_summary1 heap theta1).
    - exact HCountLeft.
    - exact HBackLeft.
    - exact HContext.
    - exact HLeftCompHeap.
    - unfold SummaryEvaluation. exact HSummary1.
  }
  assert (HCoveredRight : TraceCoveredBySummary phi2 theta2).
  {
    eapply
      (HBelow n2_steps gamma omega heap env rho e2 eff2
        phi2 heap2 (VNat n2) phi_summary2 heap_summary2 theta2).
    - exact HCountRight.
    - exact HBackRight.
    - exact HContext.
    - unfold CheckedCountedComputationEvaluation. exact HRight.
    - unfold SummaryEvaluation. exact HSummary2.
  }
  subst phi theta.
  eapply trace_covered_app_summary_union; eauto.
Qed.

Theorem EEq_checked_execution_store_context_case_from_below :
  forall n gamma omega heap env rho e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedExecutionStoreContextSmallStepCorrectnessBelow n ->
    CheckedBackTriangle gamma omega
      (EEq e1 e2) (EConcat eff1 eff2) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CheckedCountedComputationEvaluation n heap env rho
      (EEq e1 e2) phi heap_final v_final ->
    SummaryEvaluation heap env rho (EConcat eff1 eff2)
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext HComputationTraceSound HComp HSummary.
  destruct
    (CBT_Eq_components gamma omega e1 e2 eff1 eff2 HBack)
    as (eff_static & eff_e1 & HCheckedEq & HCheckedLeft &
      HNeutralLeft & HBackLeft & HBackRight).
  destruct
    (checked_execution_store_counted_tybool_value_is_bool
      n gamma omega heap env rho (EEq e1 e2) eff_static
      phi heap_final v_final HContext HCheckedEq HComp)
    as (b_final & HFinalBool).
  subst v_final.
  unfold CheckedCountedComputationEvaluation in HComp.
  destruct
    (CheckedEEq_counted_decomposition
      n heap env rho e1 e2 phi heap_final b_final HComp)
    as (n1_steps & n2_steps & phi1 & phi2 & n1 & n2 &
      heap1 & heap2 & HLeft & HRight & _HResult & HHeapFinal &
      HTrace & HCountLeft & HCountRight).
  subst heap_final.
  unfold SummaryEvaluation in HSummary.
  destruct
    (EConcat_decomposition
      heap env rho eff1 eff2 phi_summary heap_summary theta HSummary)
    as (phi_summary1 & phi_summary2 & theta1 & theta2 &
      heap_summary1 & heap_summary2 & HSummary1 & HSummary2 &
      HTheta & _HHeapSummary & _HTraceSummary).
  destruct
    (CheckedBackTriangle_summary_checked_heap_neutral
      gamma omega e1 eff1 HBackLeft)
    as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
  destruct
    (Steps_to_StepsN
      (InitialState heap env rho eff1)
      phi_summary1
      (StDone heap_summary1 (VSummary theta1))
      HSummary1)
    as (n_summary1 & HSummary1N).
  destruct
    (checked_store_counted_computation_heap_neutral
      n_summary1 gamma omega heap env rho eff1 TyEffect eff_summary1
      phi_summary1 heap_summary1 (VSummary theta1)
      HContext HComputationTraceSound HCheckedSummary1 HNeutralSummary1)
    as (HHeapSummary1 & _).
  {
    unfold CountedComputationEvaluation.
    exact HSummary1N.
  }
  subst heap_summary1.
  assert
    (HLeftComp :
      CheckedCountedComputationEvaluation n1_steps heap env rho e1
        phi1 heap1 (VNat n1)).
  {
    unfold CheckedCountedComputationEvaluation.
    exact HLeft.
  }
  destruct
    (checked_execution_store_counted_computation_heap_neutral
      n1_steps gamma omega heap env rho e1 TyNat eff_e1
      phi1 heap1 (VNat n1)
      HContext HComputationTraceSound HCheckedLeft HNeutralLeft
      HLeftComp)
    as (HHeap1 & _).
  subst heap1.
  assert
    (HLeftCompHeap :
      CheckedCountedComputationEvaluation n1_steps heap env rho e1
        phi1 heap (VNat n1)).
  {
    exact HLeftComp.
  }
  assert (HCoveredLeft : TraceCoveredBySummary phi1 theta1).
  {
    eapply
      (HBelow n1_steps gamma omega heap env rho e1 eff1
        phi1 heap (VNat n1) phi_summary1 heap theta1).
    - exact HCountLeft.
    - exact HBackLeft.
    - exact HContext.
    - exact HLeftCompHeap.
    - unfold SummaryEvaluation. exact HSummary1.
  }
  assert (HCoveredRight : TraceCoveredBySummary phi2 theta2).
  {
    eapply
      (HBelow n2_steps gamma omega heap env rho e2 eff2
        phi2 heap2 (VNat n2) phi_summary2 heap_summary2 theta2).
    - exact HCountRight.
    - exact HBackRight.
    - exact HContext.
    - unfold CheckedCountedComputationEvaluation. exact HRight.
    - unfold SummaryEvaluation. exact HSummary2.
  }
  subst phi theta.
  eapply trace_covered_app_summary_union; eauto.
Qed.

Definition CheckedStoreComputationTraceSoundnessBelow (n : nat) : Prop :=
  forall n_eval gamma omega heap env rho expr ty eff
    phi heap_final v_final eff_res,
    n_eval < n ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedTcExp gamma omega expr ty eff ->
    CountedComputationEvaluation n_eval heap env rho expr
      phi heap_final v_final ->
    ResolveStaticEffect rho eff eff_res ->
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
  pose proof (CheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
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
      (ResolveStaticEffect_static_union_inv
        rho eff_f (static_union eff_a eff_body) eff_res HResolve)
      as (eff_f_res & eff_tail_res & HEffRes &
        HResolveFun & HResolveTail).
    destruct
      (ResolveStaticEffect_static_union_inv
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
        | HFunChecked : CheckedTcExp gamma omega ef
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
        | HFunChecked : CheckedTcExp gamma omega ef
            (TyArrow ty_arg eff_body ty eff_summary) eff_f |- _ =>
            exact HFunChecked
        end)
        ltac:(match goal with
        | HArgChecked : CheckedTcExp gamma omega ea ty_arg eff_a |- _ =>
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
    | HBodyResolved : ResolveStaticEffect rho eff_body eff_body_res_body |- _ =>
        pose proof
          (ResolveStaticEffect_deterministic
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
      (ResolveStaticEffect_static_union_inv
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
    | HFunChecked : CheckedTcExp gamma omega er
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
        | HFunChecked : CheckedTcExp gamma omega er
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
      (ResolveStaticEffect_static_union_inv
        rho eff_f (static_union eff_a eff_summary) eff_res HResolve)
      as (eff_f_res & eff_tail_res & HEffRes &
        HResolveFun & HResolveTail).
    destruct
      (ResolveStaticEffect_static_union_inv
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
        | HFunChecked : CheckedTcExp gamma omega ef
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
        | HFunChecked : CheckedTcExp gamma omega ef
            (TyArrow ty_arg eff_body ty_body eff_summary) eff_f |- _ =>
            exact HFunChecked
        end)
        ltac:(match goal with
        | HArgChecked : CheckedTcExp gamma omega ea ty_arg eff_a |- _ =>
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
        ResolveStaticEffect rho eff_summary eff_summary_res_body |- _ =>
        pose proof
          (ResolveStaticEffect_deterministic
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
        | HFunChecked : CheckedTcExp gamma omega ef
            (TyArrow ty_arg eff_body ty_body eff_summary) eff_f |- _ =>
            exact HFunChecked
        end.
      * exact HFunComp.
      * exact HResolveFun.
    + eapply (IH n_eval HCount).
      * exact HCountArg.
      * exact HContextArg.
      * match goal with
        | HArgChecked : CheckedTcExp gamma omega ea ty_arg eff_a |- _ =>
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
      (ResolveStaticEffect_static_union_inv
        rho (static_union eff_summary1 eff_summary2)
        (static_union eff1 eff2) eff_res HResolve)
      as (eff_summaries_res & eff_bodies_res & HEffRes &
        HResolveSummaries & HResolveBodies).
    destruct
      (ResolveStaticEffect_static_union_inv
        rho eff_summary1 eff_summary2 eff_summaries_res
        HResolveSummaries)
      as (eff_summary1_res & eff_summary2_res & HSummariesRes &
        HResolveSummary1 & HResolveSummary2).
    destruct
      (ResolveStaticEffect_static_union_inv
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
	        HCountRight & _HCheckOutcome & HHeapFinal &
	        HValueFinal & HTrace).
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
            CheckedTcExp gamma omega (EEffApp ef1 ea1)
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
            CheckedTcExp gamma omega (EEffApp ef2 ea2)
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
            CheckedTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 |- _ =>
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
            CheckedTcExp gamma omega (EEffApp ef1 ea1)
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
            CheckedTcExp gamma omega (EEffApp ef2 ea2)
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
            CheckedTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 |- _ =>
            exact HLeftChecked
        end.
      * exact HLeftComp.
      * exact HResolve1.
    + eapply (IH n_eval HCount).
      * exact HCountRight.
      * exact HContextRight.
      * match goal with
        | HRightChecked :
            CheckedTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 |- _ =>
            exact HRightChecked
        end.
      * exact HRightComp.
      * exact HResolve2.
  - destruct
      (ResolveStaticEffect_static_union_inv
        rho eff_e (static_union eff_t eff_f) eff_res HResolve)
      as (eff_e_res & eff_branch_res & HEffRes &
        HResolveCond & HResolveBranches).
    destruct
      (ResolveStaticEffect_static_union_inv
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
        | HCondChecked : CheckedTcExp gamma omega e TyBool eff_e |- _ =>
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
                  CheckedTcExp gamma omega e TyBool eff_e |- _ =>
                  exact HCondChecked
              end.
           ++ exact HCondComp.
           ++ exact HResolveCond.
        -- eapply (IH n_eval HCount).
           ++ exact HCountBranch.
           ++ exact HContextBranch.
           ++ match goal with
              | HThenChecked :
                  CheckedTcExp gamma omega et ty eff_t |- _ =>
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
                  CheckedTcExp gamma omega e TyBool eff_e |- _ =>
                  exact HCondChecked
              end.
           ++ exact HCondComp.
           ++ exact HResolveCond.
        -- eapply (IH n_eval HCount).
           ++ exact HCountBranch.
           ++ exact HContextBranch.
           ++ match goal with
              | HElseChecked :
                  CheckedTcExp gamma omega ef ty eff_f |- _ =>
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
           | HExprChecked : CheckedTcExp gamma omega e ?ty_child ?eff_child_expr |- _ =>
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
    | HExprChecked : CheckedTcExp gamma omega e
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
          (StoreResolvedValShape_loc_ref_region
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
           | HExprChecked : CheckedTcExp gamma omega e
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
      (ResolveStaticEffect_static_union_inv
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
    | HAddrChecked : CheckedTcExp gamma omega ea
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
          (StoreResolvedValShape_loc_ref_region
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
        | HAddrChecked : CheckedTcExp gamma omega ea
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
           | HAddrChecked : CheckedTcExp gamma omega ea
               (TyRef (region_expr_to_type r) ?ty_cell) eff_a |- _ =>
               exact HAddrChecked
           end.
        -- exact HAddrComp.
        -- exact HResolveAddr.
      * eapply (IH n_eval HCount).
        -- exact HCountVal.
        -- exact HContextVal.
        -- match goal with
           | HValChecked : CheckedTcExp gamma omega ev ?ty_cell eff_v |- _ =>
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
      (ResolveStaticEffect_static_union_inv
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
        | HLeftChecked : CheckedTcExp gamma omega e1 TyNat eff1 |- _ =>
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
      (ResolveStaticEffect_static_union_inv
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
      (ResolveStaticEffect_static_union_inv
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
      (ResolveStaticEffect_static_union_inv
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
      | HExprChecked : CheckedTcExp gamma omega e ?ty_ref eff |- _ =>
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
      | HExprChecked : CheckedTcExp gamma omega e ?ty_ref eff |- _ =>
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
      (ResolveStaticEffect_static_union_inv
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
    (Steps_to_StepsN
      (InitialState heap env rho expr)
      phi
      (StDone heap_final v_final)
      HComp)
    as (n & HCompN).
  eapply
    (checked_store_computation_trace_soundness_below (S n) n);
    eauto; lia.
Qed.

Definition TraceCoveredOrPairParFallback
    (heap : Heap) (env : Env) (rho : Rho)
    (expr : Expr) (phi : Trace) (heap_final : Heap)
    (v_final : Val) (theta : Summary) : Prop :=
  TraceCoveredBySummary phi theta \/
  exists ef1 ea1 ef2 ea2,
    expr = EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2) /\
    EPairParFallbackOutcome
      heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final.

Theorem checked_store_context_case_dispatch_or_pairpar_fallback :
  forall n gamma omega heap env rho expr summary_expr
    phi heap_final v_final phi_summary heap_summary theta,
  CheckedStoreContextSmallStepCorrectnessBelow n ->
  CheckedStoreSummaryValueSoundnessBelow n ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CheckedBackTriangle gamma omega expr summary_expr ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
  CountedComputationEvaluation n heap env rho expr
    phi heap_final v_final ->
  SummaryEvaluation heap env rho summary_expr
    phi_summary heap_summary theta ->
  TraceCoveredOrPairParFallback
    heap env rho expr phi heap_final v_final theta.
Proof.
  intros n gamma omega heap env rho expr summary_expr
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HSummaryValueBelow HComputationTraceSound
    HSummaryTraceSound HBack HContext HComp HSummary.
  pose proof HBack as HBackCase.
  unfold TraceCoveredOrPairParFallback.
  destruct HBack.
  - left. eapply counted_immediate_silent_initial_return_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - left. eapply counted_immediate_silent_initial_return_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - left. eapply counted_immediate_silent_initial_return_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - left. eapply counted_immediate_silent_initial_return_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - left. eapply counted_immediate_silent_initial_return_covered; eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - left. eapply EMuApp_checked_store_context_case_from_below; eauto.
  - destruct
      (EPairPar_checked_store_context_case_from_below
        n gamma omega heap env rho ef1 ea1 ef2 ea2
        phi heap_final v_final phi_summary heap_summary theta
        HBelow HSummaryValueBelow HBackCase HContext
        HSummaryTraceSound HComp HSummary)
      as [HCovered | HFallback].
    + left. exact HCovered.
    + right.
      exists ef1, ea1, ef2, ea2.
      split; [reflexivity | exact HFallback].
  - left. eapply ERgnApp_checked_store_context_case_from_below; eauto.
  - left. eapply ECond_checked_store_context_case_from_below; eauto.
  - left. eapply ERef_checked_store_context_case_from_below; eauto.
  - left. eapply EDeref_checked_store_context_case_from_below; eauto.
  - left. eapply EAssign_checked_store_context_case_from_below; eauto.
  - left. eapply EPlus_checked_store_context_case_from_below; eauto.
  - left. eapply EMinus_checked_store_context_case_from_below; eauto.
  - left. eapply ETimes_checked_store_context_case_from_below; eauto.
  - left. eapply EEq_checked_store_context_case_from_below; eauto.
  - unfold SummaryEvaluation in HSummary.
    destruct
      (ETop_terminal_summary
        heap env rho phi_summary heap_summary theta HSummary)
      as (_HHeapSummary & HTheta & _HTraceSummary).
    subst theta.
	    left. apply trace_covered_top.
Qed.

Theorem checked_execution_store_context_case_dispatch :
  forall n gamma omega heap env rho expr summary_expr
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedExecutionStoreContextSmallStepCorrectnessBelow n ->
    CheckedExecutionStoreSummaryValueSoundnessBelow n ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CheckedBackTriangle gamma omega expr summary_expr ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedCountedComputationEvaluation n heap env rho expr
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
  - eapply checked_execution_counted_immediate_silent_initial_return_covered;
      eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - eapply checked_execution_counted_immediate_silent_initial_return_covered;
      eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - eapply checked_execution_counted_immediate_silent_initial_return_covered;
      eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - eapply checked_execution_counted_immediate_silent_initial_return_covered;
      eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - eapply checked_execution_counted_immediate_silent_initial_return_covered;
      eauto.
    intros label state' HStep. inversion HStep; subst; eauto.
  - eapply EMuApp_checked_execution_store_context_case_from_below; eauto.
  - eapply
      (EPairPar_checked_execution_store_context_case_from_below
        n gamma omega heap env rho ef1 ea1 ef2 ea2
        phi heap_final v_final phi_summary heap_summary theta);
      eauto.
  - eapply ERgnApp_checked_execution_store_context_case_from_below; eauto.
  - eapply ECond_checked_execution_store_context_case_from_below; eauto.
  - eapply ERef_checked_execution_store_context_case_from_below; eauto.
  - eapply EDeref_checked_execution_store_context_case_from_below; eauto.
  - eapply EAssign_checked_execution_store_context_case_from_below; eauto.
  - eapply EPlus_checked_execution_store_context_case_from_below; eauto.
  - eapply EMinus_checked_execution_store_context_case_from_below; eauto.
  - eapply ETimes_checked_execution_store_context_case_from_below; eauto.
  - eapply EEq_checked_execution_store_context_case_from_below; eauto.
  - unfold SummaryEvaluation in HSummary.
    destruct
      (ETop_terminal_summary
        heap env rho phi_summary heap_summary theta HSummary)
      as (_HHeapSummary & HTheta & _HTraceSummary).
    subst theta.
    apply trace_covered_top.
Qed.

Definition CheckedExecutionStoreContextAndSummaryValueSoundnessBelow
    (n : nat) : Prop :=
  CheckedExecutionStoreContextSmallStepCorrectnessBelow n /\
  CheckedExecutionStoreSummaryValueSoundnessBelow n.

Local Theorem
  checked_execution_store_context_and_summary_value_below_from_trace_soundness :
  CheckedStoreComputationTraceSoundnessGoal ->
  forall n,
    CheckedExecutionStoreContextAndSummaryValueSoundnessBelow n.
Proof.
  intros HComputationTraceGoal n.
  pose proof
    (checked_store_summary_trace_soundness_from_computation
      HComputationTraceGoal)
    as HSummaryTraceGoal.
  induction n as [n IH] using lt_wf_ind.
  split.
  - unfold CheckedExecutionStoreContextSmallStepCorrectnessBelow.
    intros n_child gamma omega heap env rho expr summary_expr
      phi heap_final v_final phi_summary heap_summary theta
      HCount HBack HContext HComp HSummary.
    destruct (IH n_child HCount) as (HBelowChild & HSummaryValueChild).
    eapply checked_execution_store_context_case_dispatch.
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
  - unfold CheckedExecutionStoreSummaryValueSoundnessBelow.
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
    + eapply counted_EEmpty_summary_trace_covered.
      eapply checked_execution_counted_to_counted. exact HComp.
    + eapply counted_EEmpty_summary_trace_covered.
      eapply checked_execution_counted_to_counted. exact HComp.
    + eapply counted_EEmpty_summary_trace_covered.
      eapply checked_execution_counted_to_counted. exact HComp.
    + eapply counted_EEmpty_summary_trace_covered.
      eapply checked_execution_counted_to_counted. exact HComp.
    + eapply counted_EEmpty_summary_trace_covered.
      eapply checked_execution_counted_to_counted. exact HComp.
    + destruct
        (CBT_App_components _ _ _ _ HBackCase)
        as (_ty_mu & _eff_mu & eff_eff_app & _ty_ef & _ty_ea &
          _eff_ef & _eff_ea & _HCheckedApp & HCheckedEffApp &
          _HCheckedFun & _HCheckedArg & HStaticEff &
          _HStaticFun & _HStaticArg & _HBackFun & _HBackArg).
      destruct
        (checked_execution_store_counted_computation_heap_neutral
          n_child gamma omega heap env rho
          (EEffApp ef ea) TyEffect eff_eff_app
          phi heap_summary (VSummary theta)
          HContext HComputationTraceSound HCheckedEffApp
          HStaticEff HComp)
        as (HHeapSummary & _HNeutralSummary).
      subst heap_summary.
      eapply
        (EEffApp_checked_execution_counted_summary_trace_covered_from_store_entry_at
          n_child gamma omega heap env rho ef ea phi heap theta).
      * exact HBelowChild.
      * exact HSummaryValueChild.
      * exact HBackCase.
      * exact HContext.
      * exact HComputationTraceSound.
      * exact HComp.
    + destruct
        (CBT_PairPar_components _ _ _ _ _ _ HBackCase)
        as (_ty1 & _ty2 & _eff1 & _eff2 &
          _eff_summary1 & _eff_summary2 &
          _HCheckedLeft & _HCheckedRight &
          _HCheckedSummary1 & _HCheckedSummary2 &
          _HStaticNeutral1 & _HStaticNeutral2 &
          _HNoAllocLeft & _HNoAllocRight &
          HBackLeft & HBackRight).
      destruct
        (CheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBackLeft)
        as (eff_left_summary & HCheckedLeftSummary & _).
      destruct
        (CheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBackRight)
        as (eff_right_summary & HCheckedRightSummary & _).
      eapply
        (checked_execution_store_summary_value_concat_from_below
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
    + eapply counted_EEmpty_summary_trace_covered.
      eapply checked_execution_counted_to_counted. exact HComp.
    + destruct
        (CBT_Cond_components _ _ _ _ _ _ _ HBackCase)
        as (eff_e_cond & _ty & _ty_t & _ty_f & _eff_et & _eff_ef &
          _HCheckedCond & HCheckedCondition & _HCheckedThen &
          _HCheckedElse & HBackCondition & HBackThen & HBackElse).
      unfold CheckedCountedComputationEvaluation in HComp.
      destruct
        (CheckedECond_counted_decomposition
          n_child heap env rho e efft efff
          phi heap_summary (VSummary theta) HComp)
        as (n_cond & n_branch & phi_cond & b & heap_cond &
          phi_branch & HCond & HBranch & HTrace & HCountCond &
          HCountBranch).
      assert (HCondComp :
        CheckedCountedComputationEvaluation n_cond heap env rho e
          phi_cond heap_cond (VBool b)).
      {
        unfold CheckedCountedComputationEvaluation.
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
          (checked_execution_store_runtime_context_after_counted
            n_cond gamma omega heap env rho e TyBool eff_e_cond
            phi_cond heap_cond (VBool b));
          eauto.
      }
      subst phi.
      rewrite HCondNil.
      simpl.
      destruct b.
      * destruct
          (CheckedBackTriangle_summary_checked_heap_neutral
            _ _ _ _ HBackThen)
          as (eff_then_summary & HCheckedThenSummary & _).
        eapply HSummaryValueChild.
        -- exact HCountBranch.
        -- exact HBackThen.
        -- exact HCheckedThenSummary.
        -- exact HContextBranch.
        -- unfold CheckedCountedComputationEvaluation in *.
           simpl in HBranch.
           exact HBranch.
      * destruct
          (CheckedBackTriangle_summary_checked_heap_neutral
            _ _ _ _ HBackElse)
          as (eff_else_summary & HCheckedElseSummary & _).
        eapply HSummaryValueChild.
        -- exact HCountBranch.
        -- exact HBackElse.
        -- exact HCheckedElseSummary.
        -- exact HContextBranch.
        -- unfold CheckedCountedComputationEvaluation in *.
           simpl in HBranch.
           exact HBranch.
    + destruct
        (CBT_Ref_components _ _ _ _ _ HBackCase)
        as (_ty & _static & _ty_ref & _eff_ref &
          _HCheckedExpr & _HCheckedRef & HBackExpr).
      destruct
        (CheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBackExpr)
        as (eff_expr_summary & HCheckedExprSummary & _).
      unfold CheckedCountedComputationEvaluation in HComp.
      destruct
        (CheckedEConcat_counted_decomposition
          n_child heap env rho eff0 (EAllocAbs r)
          phi heap_summary theta HComp)
        as (n_expr & n_abs & phi_expr & phi_abs &
          theta_expr & theta_abs & heap_expr & heap_abs &
          HExprSummary & HAbsSummary & HTheta & HHeapFinal &
          HTrace & HCountExpr & HCountAbs).
      subst theta heap_summary phi.
      assert (HCompExpr :
        CheckedCountedComputationEvaluation n_expr heap env rho eff0
          phi_expr heap_expr (VSummary theta_expr)).
      {
        unfold CheckedCountedComputationEvaluation.
        exact HExprSummary.
      }
      assert (HCompAbs :
        CheckedCountedComputationEvaluation n_abs heap_expr env rho
          (EAllocAbs r) phi_abs heap_abs (VSummary theta_abs)).
      {
        unfold CheckedCountedComputationEvaluation.
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
        eapply counted_EAllocAbs_summary_trace_covered.
        eapply checked_execution_counted_to_counted.
        exact HCompAbs.
      }
      eapply trace_covered_app_summary_union; eauto.
    + destruct
        (CBT_Deref_components _ _ _ _ _ HBackCase)
        as (_ty & _static & _ty_deref & _eff_deref &
          _HCheckedExpr & _HCheckedDeref & HBackExpr).
      destruct
        (CheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBackExpr)
        as (eff_expr_summary & HCheckedExprSummary & _).
      unfold CheckedCountedComputationEvaluation in HComp.
      destruct
        (CheckedEConcat_counted_decomposition
          n_child heap env rho eff0 (EReadAbs r)
          phi heap_summary theta HComp)
        as (n_expr & n_abs & phi_expr & phi_abs &
          theta_expr & theta_abs & heap_expr & heap_abs &
          HExprSummary & HAbsSummary & HTheta & HHeapFinal &
          HTrace & HCountExpr & HCountAbs).
      subst theta heap_summary phi.
      assert (HCompExpr :
        CheckedCountedComputationEvaluation n_expr heap env rho eff0
          phi_expr heap_expr (VSummary theta_expr)).
      {
        unfold CheckedCountedComputationEvaluation.
        exact HExprSummary.
      }
      assert (HCompAbs :
        CheckedCountedComputationEvaluation n_abs heap_expr env rho
          (EReadAbs r) phi_abs heap_abs (VSummary theta_abs)).
      {
        unfold CheckedCountedComputationEvaluation.
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
        eapply counted_EReadAbs_summary_trace_covered.
        eapply checked_execution_counted_to_counted.
        exact HCompAbs.
      }
      eapply trace_covered_app_summary_union; eauto.
    + destruct
        (CBT_Assign_components _ _ _ _ _ _ _ HBackCase)
        as (_ty_addr & _static_addr & _ty_assign & _eff_assign &
          _HCheckedAddr & _HCheckedAssign & _HNeutralAddr &
          HBackAddr & HBackVal).
      destruct
        (CheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBackAddr)
        as (eff_addr_summary & HCheckedAddrSummary & _).
      destruct
        (CheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBackVal)
        as (eff_val_summary & HCheckedValSummary & _).
      unfold CheckedCountedComputationEvaluation in HComp.
      destruct
        (CheckedEConcat_counted_decomposition
          n_child heap env rho eff1 (EConcat eff2 (EWriteAbs r))
          phi heap_summary theta HComp)
        as (n_addr & n_rest & phi_addr & phi_rest &
          theta_addr & theta_rest & heap_addr & heap_rest &
          HAddrSummary & HRestSummary & HTheta & HHeapFinal &
          HTrace & HCountAddr & HCountRest).
      destruct
        (CheckedEConcat_counted_decomposition
          n_rest heap_addr env rho eff2 (EWriteAbs r)
          phi_rest heap_rest theta_rest HRestSummary)
        as (n_val & n_abs & phi_val & phi_abs &
          theta_val & theta_abs & heap_val & heap_abs &
          HValSummary & HAbsSummary & HThetaRest & HHeapRest &
          HTraceRest & HCountVal & HCountAbs).
      subst theta_rest heap_rest phi_rest theta heap_summary phi.
      assert (HCompAddr :
        CheckedCountedComputationEvaluation n_addr heap env rho eff1
          phi_addr heap_addr (VSummary theta_addr)).
      {
        unfold CheckedCountedComputationEvaluation.
        exact HAddrSummary.
      }
      assert (HContextVal :
        CheckedStoreRuntimeContext gamma omega heap_addr env rho).
      {
        eapply
          (checked_execution_store_runtime_context_after_counted
            n_addr gamma omega heap env rho eff1 TyEffect
            eff_addr_summary phi_addr heap_addr
            (VSummary theta_addr));
          eauto.
      }
      assert (HCompVal :
        CheckedCountedComputationEvaluation n_val heap_addr env rho eff2
          phi_val heap_val (VSummary theta_val)).
      {
        unfold CheckedCountedComputationEvaluation.
        exact HValSummary.
      }
      assert (HCompAbs :
        CheckedCountedComputationEvaluation n_abs heap_val env rho
          (EWriteAbs r) phi_abs heap_abs (VSummary theta_abs)).
      {
        unfold CheckedCountedComputationEvaluation.
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
        eapply counted_EWriteAbs_summary_trace_covered.
        eapply checked_execution_counted_to_counted.
        exact HCompAbs.
      }
      eapply trace_covered_app_summary_union; eauto.
      eapply trace_covered_app_summary_union; eauto.
    + destruct
        (CheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBack1)
        as (eff_left_summary & HCheckedLeftSummary & _).
      destruct
        (CheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBack2)
        as (eff_right_summary & HCheckedRightSummary & _).
      eapply
        (checked_execution_store_summary_value_concat_from_below
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
        (CheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBack1)
        as (eff_left_summary & HCheckedLeftSummary & _).
      destruct
        (CheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBack2)
        as (eff_right_summary & HCheckedRightSummary & _).
      eapply
        (checked_execution_store_summary_value_concat_from_below
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
        (CheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBack1)
        as (eff_left_summary & HCheckedLeftSummary & _).
      destruct
        (CheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBack2)
        as (eff_right_summary & HCheckedRightSummary & _).
      eapply
        (checked_execution_store_summary_value_concat_from_below
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
        (CheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBack1)
        as (eff_left_summary & HCheckedLeftSummary & _).
      destruct
        (CheckedBackTriangle_summary_checked_heap_neutral
          _ _ _ _ HBack2)
        as (eff_right_summary & HCheckedRightSummary & _).
      eapply
        (checked_execution_store_summary_value_concat_from_below
          n_child gamma omega heap env rho e1 e2 eff1 eff2
          eff_left_summary eff_right_summary phi heap_summary theta).
      * exact HSummaryValueChild.
      * exact HBack1.
      * exact HBack2.
      * exact HCheckedLeftSummary.
      * exact HCheckedRightSummary.
      * exact HContext.
      * exact HComp.
    + eapply counted_ETop_summary_trace_covered.
      eapply checked_execution_counted_to_counted. exact HComp.
Qed.

Theorem
  checked_execution_store_context_small_step_correctness_below_from_trace_soundness :
  CheckedStoreComputationTraceSoundnessGoal ->
  forall n,
    CheckedExecutionStoreContextSmallStepCorrectnessBelow n.
Proof.
  intros HComputationTraceGoal n.
  destruct
    (checked_execution_store_context_and_summary_value_below_from_trace_soundness
      HComputationTraceGoal n)
    as (HBelow & _).
  exact HBelow.
Qed.

Theorem
  checked_execution_store_summary_value_soundness_below_from_trace_soundness :
  CheckedStoreComputationTraceSoundnessGoal ->
  forall n,
    CheckedExecutionStoreSummaryValueSoundnessBelow n.
Proof.
  intros HComputationTraceGoal n.
  destruct
    (checked_execution_store_context_and_summary_value_below_from_trace_soundness
      HComputationTraceGoal n)
    as (_ & HSummaryValueBelow).
  exact HSummaryValueBelow.
Qed.

Theorem checked_execution_store_context_terminal_correctness_from_store_dispatch :
  CheckedExecutionStoreContextTerminalCorrectnessGoal.
Proof.
  unfold CheckedExecutionStoreContextTerminalCorrectnessGoal.
  intros gamma omega heap env rho expr summary_expr phi heap' v
    phi_summary heap_summary theta HBack HContext HComp HSummary.
  destruct
    (CheckedComputationEvaluation_to_counted
      heap env rho expr phi heap' v HComp)
    as (n & HCompN).
  eapply
    (checked_execution_store_context_small_step_correctness_below_from_trace_soundness
      checked_store_computation_trace_soundness (S n) n);
    eauto; lia.
Qed.
