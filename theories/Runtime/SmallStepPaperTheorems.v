From stdpp Require Import gmap.
From Stdlib Require Import Program.Equality.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeHeapShape.
Require Import theories.Runtime.SmallStepRuntimeKontTyping.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepPreservationTheorems.
Require Import theories.Runtime.SmallStepExplicitStoreBase.
Require Import theories.Runtime.SmallStepExplicitStoreTheorems.
Require Import theories.Runtime.SmallStepTraceSafety.
Require Import theories.Runtime.SmallStepParallelTraceSafe.
Require Import theories.Runtime.SmallStepSequentialSoundness.
Require Import theories.Runtime.SmallStepStructuredTrace.
Require Import theories.Runtime.SmallStepCorrectness.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.DynamicActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.EffectFacts.
Require Import theories.Meta.TraceTypingFacts.
Require Import theories.Determinism.SmallStepPairParScheduleDeterminism.

Theorem PaperSmallStepFinitePrefixSafety :
  PairParCheckDecidable ->
  forall heap env rho e stty ctxt rgns t eff trace state',
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    Steps (initial_state heap env rho e) trace state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' (subst_rho rho t) stty' /\
      StoreExtends stty stty' /\
      NotStuck state' /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  exact initial_state_steps_safety_with_trace.
Qed.

Theorem PaperSmallStepTerminalSoundness :
  forall heap env rho e stty ctxt rgns t eff trace heap' v,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    Steps (initial_state heap env rho e) trace (StDone heap' v) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, subst_rho rho t) /\
      RuntimeValShape stty' (subst_rho rho t) v /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  exact initial_state_terminal_value_with_trace.
Qed.

Theorem PaperPairParCheckedOrBlockedTraceSafety :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout theta1 theta2,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    (PairParCheckPass theta1 theta2 /\
      PairParTraceSafeAt
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
        tout stty) \/
    (PairParCheckFail theta1 theta2 /\
      NotStuck
        (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)).
Proof.
  exact pairpar_check_decidable_trace_safe.
Qed.

Theorem PaperPairParCheckedOrBlockedTerminalSoundness :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout theta1 theta2,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    (PairParCheckPass theta1 theta2 /\
      forall trace heap' v,
        PairParSteps
          (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
          trace (PPS_State (StDone heap' v)) ->
        exists stty',
          StoreExtends stty stty' /\
          TcHeap (heap', stty') /\
          RuntimeHeapShape heap' stty' /\
          TcVal (stty', v, tout) /\
          RuntimeValShape stty' tout v /\
          TcPhi stty' (trace_as_phi trace)) \/
    (PairParCheckFail theta1 theta2 /\
      NotStuck
        (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)).
Proof.
  exact pairpar_check_decidable_terminal_value.
Qed.

Theorem PaperPairParSummaryPassSmallStepSoundPrefix :
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, static_eff1) ->
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    PairParCheckPass theta1 theta2 ->
    exists phi_source,
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      StepsPhi
        (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
        phi_source
        (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k) /\
      phi_as_list phi_source =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2.
Proof.
  exact PairParSequentialEffectSummaryStepsPhi_source_pass_small_step_sound_prefix.
Qed.

Theorem PaperPairParSummaryFailSmallStepSoundPrefix :
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, static_eff1) ->
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    PairParCheckFail theta1 theta2 ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
    PairParCheckState
      (pairpar_check_state heap_eff2 env rho ef1 ea1 ef2 ea2 theta1 theta2 k) /\
    forall label state',
      ~ Step
        (pairpar_check_state heap_eff2 env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
        label state'.
Proof.
  exact PairParSequentialEffectSummaryStepsPhi_source_fail_small_step_sound_prefix.
Qed.

Theorem PaperPairParCheckedStructuredTopSound :
  forall heap env rho ef1 ea1 ef2 ea2
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v,
    phi =
      pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2 ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    phi_mu1 ⋞ theta1 ->
    phi_mu2 ⋞ theta2 ->
    phi ⋞ theta_with_phi_prefixes
      phi_eff1 phi_eff2 (Union_Theta theta1 theta2).
Proof.
  exact PairParCheckedStructuredStepsPhi_top_sound.
Qed.

Theorem PaperPairParCheckedPackedTerminalSoundness :
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout phi heap' v theta1 theta2,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    PairParCheckedPackedStepsPhi theta1 theta2
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi
      (PPS_State (StDone heap' v)) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, tout) /\
      RuntimeValShape stty' tout v /\
      TcPhi stty' phi.
Proof.
  exact PairParCheckedPackedStepsPhi_terminal_value_with_trace.
Qed.

Theorem PaperScheduledSmallStepTerminalValueSoundness :
  forall state tout stty phi heap' v,
    WTStateRuntimeHeapShapeAt state tout stty ->
    ScheduledStepsPhi state phi (StDone heap' v) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, tout) /\
      RuntimeValShape stty' tout v.
Proof.
  exact WTStateRuntimeHeapShapeAt_scheduled_terminal_value.
Qed.

Lemma TcExp_mu_app_summary_readonly :
  forall ctxt rgns rho ef ea ty static,
    TcExp (ctxt, rgns, Mu_App ef ea, ty, static) ->
    exists static_eff,
      TcExp (ctxt, rgns, Eff_App ef ea, Ty_Effect, static_eff) /\
      ReadOnlyStatic (fold_subst_eps rho static_eff).
Proof.
  intros ctxt rgns rho ef ea ty static HTcMu.
  inversion HTcMu; subst.
  match goal with
  | HBackAll : forall rho0,
      BackTriangle (ctxt, rgns, rho0, Mu_App ef ea, Eff_App ef ea) |- _ =>
      pose proof (HBackAll rho) as HBack
  end.
  inversion HBack; subst; try solve [discriminate].
  exists static_ee.
  split.
  - inversion H11; subst. exact H11.
  - exact H12.
Qed.

Lemma PairParEffectSummaryStepsPhi_readonly_from_pairpar_typed :
  forall heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns ty static
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyPhi phi_eff1 /\ ReadOnlyPhi phi_eff2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns ty static
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcPair HSummary.
  inversion HTcPair; subst.
  match goal with
  | HMu1 : TcExp (ctxt, rgns, Mu_App ef1 ea1, _, _),
    HMu2 : TcExp (ctxt, rgns, Mu_App ef2 ea2, _, _) |- _ =>
      destruct (TcExp_mu_app_summary_readonly
        ctxt rgns rho ef1 ea1 _ _ HMu1)
        as (static_eff1 & HTcEff1 & HReadOnly1);
      destruct (TcExp_mu_app_summary_readonly
        ctxt rgns rho ef2 ea2 _ _ HMu2)
        as (static_eff2 & HTcEff2 & HReadOnly2);
      exact
        (PairParEffectSummaryStepsPhi_readonly_from_small_step_sound
          heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
          phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
          static_eff1 static_eff2
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcEff1 HTcEff2 HSummary HReadOnly1 HReadOnly2)
  end.
Qed.

Theorem WTStateRuntimeHeapShapeAt_scheduled_terminal_value_with_trace :
  forall state tout stty phi heap' v,
    WTStateRuntimeHeapShapeAt state tout stty ->
    ScheduledStepsPhi state phi (StDone heap' v) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, tout) /\
      RuntimeValShape stty' tout v /\
      TcPhi stty' phi.
Proof.
  intros state tout stty phi heap' v HWT HSteps.
  revert tout stty HWT.
  dependent induction HSteps; intros tout stty HWT.
  - destruct (WTStateRuntimeHeapShapeAt_done_value heap' v tout stty HWT)
      as (HTcHeap & HHeapShape & HTcVal & HValShape).
    exists stty.
    split; [apply StoreExtends_refl |].
    split; [exact HTcHeap |].
    split; [exact HHeapShape |].
    split; [exact HTcVal |].
    split; [exact HValShape | apply TcPhi_nil].
  - destruct
      (WTStateRuntimeHeapShapeAt_step_preservation
        state tout stty label state' HWT H0)
      as (stty1 & HWT1 & _ & _ & HExt1).
    destruct (IHHSteps heap' v eq_refl tout stty1 HWT1)
      as (stty2 & HExt2 & HTcHeap2 & HHeapShape2 &
          HTcVal2 & HValShape2 & HTcPhi2).
    pose proof
      (WTStateRuntimeHeapShapeAt_step_label_phi_typed
        state tout stty label state' tout stty1 HWT H0 HWT1)
      as HTcLabel1.
    pose proof
      (TcPhi_weaken stty1 stty2 (label_phi label) HExt2 HTcLabel1)
      as HTcLabel2.
    exists stty2.
    split; [eapply StoreExtends_trans; eauto |].
    split; [exact HTcHeap2 |].
    split; [exact HHeapShape2 |].
    split; [exact HTcVal2 |].
    split; [exact HValShape2 |].
    apply TcPhi_seq; assumption.
  - inversion HWT; subst.
    match goal with
    | HTcExp : TcExp (_, _, Pair_Par _ _ _ _, _, _) |- _ =>
        inversion HTcExp; subst
    end.
    destruct
      (PairParCheckedPackedStepsPhi_terminal_value_with_trace
        heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
        ty1 ty2 eff1 eff2 tout phi_mu heap' v theta1 theta2)
      as (stty' & HExt & HTcHeap' & HHeapShape' & HTcVal' &
          HValShape' & HTcPhiMu);
      eauto.
    destruct
      (PairParEffectSummaryStepsPhi_readonly_from_pairpar_typed
        heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
        (Ty_Pair ty1 ty2)
        (Union_Static_Action
          (Union_Static_Action (Union_Static_Action eff3 eff4) eff2) eff1)
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2)
      as (HReadOnlyEff1 & HReadOnlyEff2);
      eauto.
    exists stty'.
    split; [exact HExt |].
    split; [exact HTcHeap' |].
    split; [exact HHeapShape' |].
    split; [exact HTcVal' |].
    split; [exact HValShape' |].
    apply TcPhi_pairpar_checked_packed_structured_trace.
    + apply ReadOnlyPhi_TcPhi. exact HReadOnlyEff1.
    + apply ReadOnlyPhi_TcPhi. exact HReadOnlyEff2.
    + exact HTcPhiMu.
Qed.

Theorem PaperScheduledSmallStepTerminalTraceSoundness :
  forall state tout stty phi heap' v,
    WTStateRuntimeHeapShapeAt state tout stty ->
    ScheduledStepsPhi state phi (StDone heap' v) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, tout) /\
      RuntimeValShape stty' tout v /\
      TcPhi stty' phi.
Proof.
  exact WTStateRuntimeHeapShapeAt_scheduled_terminal_value_with_trace.
Qed.

Theorem PaperScheduledExpressionTerminalValueSoundness :
  forall heap env rho e stty ctxt rgns t eff phi heap' v,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    ScheduledStepsPhi
      (initial_state heap env rho e)
      phi
      (StDone heap' v) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, subst_rho rho t) /\
      RuntimeValShape stty' (subst_rho rho t) v.
Proof.
  exact initial_state_scheduled_terminal_value.
Qed.

Theorem PaperScheduledExpressionTerminalTraceSoundness :
  forall heap env rho e stty ctxt rgns t eff phi heap' v,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    ScheduledStepsPhi
      (initial_state heap env rho e)
      phi
      (StDone heap' v) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, subst_rho rho t) /\
      RuntimeValShape stty' (subst_rho rho t) v /\
      TcPhi stty' phi.
Proof.
  intros heap env rho e stty ctxt rgns t eff phi heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps.
  eapply WTStateRuntimeHeapShapeAt_scheduled_terminal_value_with_trace; eauto.
  eapply WTStateRuntimeHeapShapeAt_initial; eauto.
Qed.

Theorem PaperSmallStepTerminalDeterminism :
  forall state trace1 heap1 v1 trace2 heap2 v2,
    Steps state trace1 (StDone heap1 v1) ->
    Steps state trace2 (StDone heap2 v2) ->
    trace1 = trace2 /\ heap1 = heap2 /\ v1 = v2.
Proof.
  exact Steps_terminal_deterministic.
Qed.

Theorem PaperSmallStepStructuredTerminalDeterminism :
  forall state phi1 heap1 v1 phi2 heap2 v2,
    StepsPhi state phi1 (StDone heap1 v1) ->
    StepsPhi state phi2 (StDone heap2 v2) ->
    phi_as_list phi1 = phi_as_list phi2 /\
    heap1 = heap2 /\
    v1 = v2.
Proof.
  exact StepsPhi_terminal_deterministic.
Qed.

Theorem PaperScheduledSmallStepTerminalDeterminism :
  forall state phi1 heap1 v1 phi2 heap2 v2,
    ScheduledStepsPhi state phi1 (StDone heap1 v1) ->
    ScheduledStepsPhi state phi2 (StDone heap2 v2) ->
    heap1 = heap2 /\ v1 = v2.
Proof.
  exact ScheduledStepsPhi_terminal_deterministic.
Qed.

Theorem PaperScheduledExpressionTerminalDeterminism :
  forall heap env rho e phi1 heap1 v1 phi2 heap2 v2,
    ScheduledStepsPhi
      (initial_state heap env rho e)
      phi1
      (StDone heap1 v1) ->
    ScheduledStepsPhi
      (initial_state heap env rho e)
      phi2
      (StDone heap2 v2) ->
    heap1 = heap2 /\ v1 = v2.
Proof.
  exact ScheduledInitialState_terminal_deterministic.
Qed.

Theorem PaperSmallStepStructuredEffectTerminalDeterminism :
  forall state phi1 heap1 theta1 phi2 heap2 theta2,
    StepsPhi state phi1 (StDone heap1 (Eff theta1)) ->
    StepsPhi state phi2 (StDone heap2 (Eff theta2)) ->
    phi_as_list phi1 = phi_as_list phi2 /\
    heap1 = heap2 /\
    theta1 = theta2.
Proof.
  exact StepsPhi_effect_terminal_deterministic.
Qed.
