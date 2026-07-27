From stdpp Require Import gmap.
From Stdlib Require Import Program.Equality.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.TraceSemantics.
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
Require Import theories.Runtime.SmallStepParallelTyping.
Require Import theories.Runtime.SmallStepParallelProgress.
Require Import theories.Runtime.SmallStepParallelTraceSafety.
Require Import theories.Runtime.SmallStepParallelTraceSafe.
Require Import theories.Runtime.SmallStepPairParDispatch.
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
Require Import theories.Meta.TraceFacts.
Require Import theories.Meta.TraceTypingFacts.

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
    StepsStayNonPairParRun (initial_state heap env rho e) ->
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

Theorem PaperUnifiedPairParCheckedFinitePrefixSafety :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout trace state',
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    Steps
      (pairpar_unified_checked_initial heap env rho ef1 ea1 ef2 ea2 k)
      trace state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong
        (pairpar_state_of_state state') tout stty' /\
      StoreExtends stty stty' /\
      PairParRunHeapsAgree (pairpar_state_of_state state') /\
      PairParNotStuck (pairpar_state_of_state state') /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  exact pairpar_unified_checked_initial_steps_safety_with_trace.
Qed.

Theorem PaperUnifiedPairParCheckedBranchProgress :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k,
    PairParCheckPass theta1 theta2 ->
    PairParRunHeapsAgree
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k) /\
    exists left_state right_state,
      Step
        (pairpar_unified_checked_initial heap env rho ef1 ea1 ef2 ea2 k)
        Silent left_state /\
      Step
        (pairpar_unified_checked_initial heap env rho ef1 ea1 ef2 ea2 k)
        Silent right_state.
Proof.
  exact pairpar_check_pass_unified_dispatch.
Qed.

Theorem PaperUnifiedPairParTraceSafety :
  PairParCheckDecidable ->
  forall state tout stty,
    WTPairParStateRuntimeHeapShapeAtStrong
      (pairpar_state_of_state state) tout stty ->
    PairParRunHeapsAgree (pairpar_state_of_state state) ->
    UnifiedPairParTraceSafeAt state tout stty.
Proof.
  exact WTPairParStateRuntimeHeapShapeAtStrong_unified_trace_safe_typed.
Qed.

Lemma PairParNotStuck_as_NotStuck :
  forall state,
    PairParRunHeapsAgree (pairpar_state_of_state state) ->
    PairParNotStuck (pairpar_state_of_state state) ->
    NotStuck state.
Proof.
  intros state HAgree HNotStuck.
  destruct HNotStuck as [HTerminal | [HCanStep | HCheck]].
  - destruct state as
      [heap env rho e k | heap v k | heap v | left right k];
      inversion HTerminal; subst.
    left. constructor.
  - right. left.
    destruct HCanStep as (label & state' & HStep).
    exists label, (pairpar_state_as_state state').
    rewrite <- (pairpar_state_as_state_of_state state).
    eapply pairpar_step_as_step; eauto.
  - right. right.
    destruct state as
      [heap env rho e k | heap v k | heap v | left right k];
      simpl in *; exact HCheck.
Qed.

Theorem PaperUnifiedSmallStepFinitePrefixSafety :
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
      PairParRunHeapsAgree (pairpar_state_of_state state') /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros HDec heap env rho e stty ctxt rgns t eff trace state'
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps.
  assert
    (HWT :
      WTStateRuntimeHeapShapeAt
        (initial_state heap env rho e) (subst_rho rho t) stty).
  {
    eapply WTStateRuntimeHeapShapeAt_initial; eauto.
  }
  assert
    (HWTStrong :
      WTPairParStateRuntimeHeapShapeAtStrong
        (pairpar_state_of_state (initial_state heap env rho e))
        (subst_rho rho t) stty).
  {
    simpl. constructor; [exact I | exact HWT].
  }
  assert
    (HAgree :
      PairParRunHeapsAgree
        (pairpar_state_of_state (initial_state heap env rho e))).
  {
    simpl. exact I.
  }
  destruct
    (WTPairParStateRuntimeHeapShapeAtStrong_unified_trace_safe_typed
      HDec
      (initial_state heap env rho e) (subst_rho rho t) stty
      HWTStrong HAgree
      trace state' HSteps)
    as (stty' & HWTStrong' & HExt & HAgree' & HPairNotStuck & HTcPhi).
  exists stty'.
  split.
  - pose proof
      (WTPairParStateRuntimeHeapShapeAtStrong_as_state
        (pairpar_state_of_state state') (subst_rho rho t) stty'
        HWTStrong') as HWTState'.
    now rewrite pairpar_state_as_state_of_state in HWTState'.
  - split; [exact HExt |].
    split.
    + eapply PairParNotStuck_as_NotStuck; eauto.
    + split; [exact HAgree' | exact HTcPhi].
Qed.

Theorem PaperUnifiedPairParTerminalSoundnessFromSafety :
  forall state tout stty trace heap' v,
    UnifiedPairParTraceSafeAt state tout stty ->
    Steps state trace (StDone heap' v) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, tout) /\
      RuntimeValShape stty' tout v /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  exact UnifiedPairParTraceSafeAt_terminal_value.
Qed.

Theorem PaperUnifiedPairParCheckedTerminalSoundness :
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout trace heap' v,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    Steps
      (pairpar_unified_checked_initial heap env rho ef1 ea1 ef2 ea2 k)
      trace (StDone heap' v) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, tout) /\
      RuntimeValShape stty' tout v /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  exact pairpar_unified_checked_initial_terminal_value_with_trace.
Qed.

Theorem PaperUnifiedPairParCheckedTerminalPairSoundness :
  forall heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    ty1 ty2 eff1 eff2 trace heap' v,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    Steps
      (pairpar_unified_checked_initial heap env rho ef1 ea1 ef2 ea2 KDone)
      trace (StDone heap' v) ->
    exists stty' v1 v2,
      v = Pair (v1, v2) /\
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v1, subst_rho rho ty1) /\
      RuntimeValShape stty' (subst_rho rho ty1) v1 /\
      TcVal (stty', v2, subst_rho rho ty2) /\
      RuntimeValShape stty' (subst_rho rho ty2) v2 /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  exact pairpar_unified_checked_initial_kdone_terminal_pair_with_trace.
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
    PairParSourceOrderedEffectSummaryStepsPhi
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
        (pairpar_checked_run_start heap_eff2 env rho ef1 ea1 ef2 ea2 k) /\
      phi_as_list phi_source =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2.
Proof.
  exact PairParSourceOrderedEffectSummaryStepsPhi_source_pass_small_step_sound_prefix.
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
    PairParSourceOrderedEffectSummaryStepsPhi
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
  exact PairParSourceOrderedEffectSummaryStepsPhi_source_fail_small_step_sound_prefix.
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

Theorem WTStateRuntimeHeapShapeAt_scheduled_as_steps_exists :
  forall state tout stty phi state',
    WTStateRuntimeHeapShapeAt state tout stty ->
    ScheduledStepsPhi state phi state' ->
    exists trace,
      Steps state trace state'.
Proof.
  intros state tout stty phi state' HWT HScheduled.
  revert tout stty HWT.
  induction HScheduled as
    [state0
    | state0 label state1 phi0 state2 HNotPair HStep HScheduledTail IH
    | heap env rho ef1 ea1 ef2 ea2 k
        phi_eff1 phi_eff2 heap_eff1 heap_eff2 theta1 theta2
        phi_mu state1 HSummary HPass HPacked];
    intros tout stty HWT.
  - exists nil. constructor.
  - destruct
      (WTStateRuntimeHeapShapeAt_step_preservation
        state0 tout stty label state1 HWT HStep)
      as (stty1 & HWT1 & _ & _ & _).
    destruct (IH tout stty1 HWT1)
      as (trace_tail & HStepsTail).
    exists (label_trace label ++ trace_tail).
    econstructor; eauto.
  - inversion HWT; subst.
    match goal with
    | HTcExp : TcExp (_, _, Pair_Par _ _ _ _, _, _) |- _ =>
        pose proof HTcExp as HTcPair;
        inversion HTcExp; subst
    end.
    destruct
      (PairParEffectSummaryStepsPhi_readonly_from_pairpar_typed
        heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
        (Ty_Pair ty1 ty2)
        (Union_Static_Action
          (Union_Static_Action (Union_Static_Action eff3 eff4) eff2) eff1)
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2)
      as (HReadOnlyEff1 & HReadOnlyEff2);
      eauto.
    assert (HHeapEff1 : heap_eff1 = heap).
    {
      eapply PairParEffectSummaryStepsPhi_first_readonly_heap_neutral;
        eauto.
    }
    assert (HHeapEff2 : heap_eff2 = heap).
    {
      inversion HSummary; subst.
      eapply pairpar_effect_summary_steps_phi_heap_neutral; eauto.
    }
    assert
      (HSummarySeq :
        PairParSourceOrderedEffectSummaryStepsPhi
          heap env rho ef1 ea1 ef2 ea2
          phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2).
    {
      eapply PairParEffectSummaryStepsPhi_source_ordered_when_first_heap_unchanged;
        eauto.
    }
    destruct
      (PairParSourceOrderedEffectSummaryStepsPhi_source_pass_prefix
        heap env rho ef1 ea1 ef2 ea2 k
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2)
      as (phi_source & HSourcePhi & _).
    + exact HSummarySeq.
    + destruct HPass as [HPassCore _].
      exact HPassCore.
    + pose proof (StepsPhi_as_steps _ _ _ HSourcePhi) as HSourceSteps.
      subst heap_eff2.
      destruct
        (PairParPackedStepsPhi_as_steps_exists
          (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
          phi_mu
          (PPS_State state1))
        as (trace_mu & HMuSteps).
      * apply pairpar_checked_initial_heaps_agree.
      * eapply PairParCheckedPackedStepsPhi_forget; eauto.
      * exists (phi_as_list phi_source ++ trace_mu).
        eapply steps_trans; eauto.
Qed.

Theorem PaperScheduledSmallStepOrdinaryStepsWitness :
  forall state tout stty phi state',
    WTStateRuntimeHeapShapeAt state tout stty ->
    ScheduledStepsPhi state phi state' ->
    exists trace,
      Steps state trace state'.
Proof.
  exact WTStateRuntimeHeapShapeAt_scheduled_as_steps_exists.
Qed.

Theorem WTStateRuntimeHeapShapeAt_scheduled_replays_heap :
  forall state tout stty phi state',
    WTStateRuntimeHeapShapeAt state tout stty ->
    ScheduledStepsPhi state phi state' ->
    Phi_Heap_Steps
      (phi, state_heap state)
      (Phi_Nil, state_heap state').
Proof.
  intros state tout stty phi state' HWT HScheduled.
  revert tout stty HWT.
  induction HScheduled as
    [state0
    | state0 label state1 phi0 state2 HNotPair HStep HScheduledTail IH
    | heap env rho ef1 ea1 ef2 ea2 k
        phi_eff1 phi_eff2 heap_eff1 heap_eff2 theta1 theta2
        phi_mu state1 HSummary HPass HChecked];
    intros tout stty HWT.
  - exists 0. constructor.
  - destruct
      (WTStateRuntimeHeapShapeAt_step_preservation
        state0 tout stty label state1 HWT HStep)
      as (stty1 & HWT1 & _ & _ & _).
    eapply structured_phi_seq_steps.
    + eapply step_label_phi_replays_heap; eauto.
    + exact (IH tout stty1 HWT1).
  - inversion HWT; subst.
    match goal with
    | HTcExp : TcExp (_, _, Pair_Par _ _ _ _, _, _) |- _ =>
        inversion HTcExp; subst
    end.
    inversion HSummary as
      [phi_eff1' phi_eff2' heap_eff1' heap_eff2'
        theta1' theta2' HStepsEff1 HStepsEff2]; subst.
    destruct
      (PairParEffectSummaryStepsPhi_readonly_from_pairpar_typed
        heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
        (Ty_Pair ty1 ty2)
        (Union_Static_Action
          (Union_Static_Action (Union_Static_Action eff3 eff4) eff2) eff1)
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2)
      as (HReadOnlyEff1 & HReadOnlyEff2);
      eauto.
    assert (HHeapEff1 : heap_eff1 = heap).
    {
      eapply pairpar_effect_summary_steps_phi_heap_neutral; eauto.
    }
    assert (HHeapEff2 : heap_eff2 = heap).
    {
      eapply pairpar_effect_summary_steps_phi_heap_neutral; eauto.
    }
    rewrite HHeapEff1 in HStepsEff1.
    rewrite HHeapEff2 in HStepsEff2.
    destruct
      (PairParCheckedPackedStepsPhi_unpacked
        theta1 theta2
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
        phi_mu
        (PPS_State state1)
        HChecked)
      as (phi_state & phi_left & phi_right &
          HPairSteps & HMuTrace & _HSoundLeft & _HSoundRight).
    subst phi_mu.
    simpl.
    eapply structured_phi_seq_steps.
    + eapply structured_phi_par_steps.
      * exact (StepsPhi_replays_heap _ _ _ HStepsEff1).
      * exact (StepsPhi_replays_heap _ _ _ HStepsEff2).
    + change (state_heap (StDone heap (Eff theta2))) with heap.
      exact
        (PairParStepsPhi_checked_replays_heap
          heap env rho ef1 ea1 ef2 ea2 k
          phi_state phi_left phi_right (PPS_State state1)
          HPairSteps).
Qed.

Theorem PaperScheduledSmallStepStructuredTraceReplay :
  forall state tout stty phi state',
    WTStateRuntimeHeapShapeAt state tout stty ->
    ScheduledStepsPhi state phi state' ->
    Phi_Heap_Steps
      (phi, state_heap state)
      (Phi_Nil, state_heap state').
Proof.
  exact WTStateRuntimeHeapShapeAt_scheduled_replays_heap.
Qed.

Theorem WTStateRuntimeHeapShapeAt_scheduled_readonly_preserves_heap :
  forall state tout stty phi state',
    WTStateRuntimeHeapShapeAt state tout stty ->
    ScheduledStepsPhi state phi state' ->
    ReadOnlyPhi phi ->
    state_heap state = state_heap state'.
Proof.
  intros state tout stty phi state' HWT HSteps HReadOnly.
  pose proof
    (WTStateRuntimeHeapShapeAt_scheduled_replays_heap
      state tout stty phi state' HWT HSteps)
    as HReplay.
  pose proof
    (ReadOnlyPhi_Heap_Steps_preserves_heap
      phi (state_heap state) Phi_Nil (state_heap state')
      HReplay HReadOnly)
    as HHeap.
  unfold equiv, heap_equiv in HHeap.
  exact HHeap.
Qed.

Theorem PaperScheduledSmallStepReadOnlyHeapNeutrality :
  forall state tout stty phi state',
    WTStateRuntimeHeapShapeAt state tout stty ->
    ScheduledStepsPhi state phi state' ->
    ReadOnlyPhi phi ->
    state_heap state = state_heap state'.
Proof.
  exact WTStateRuntimeHeapShapeAt_scheduled_readonly_preserves_heap.
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
    StepsStayNonPairParRun state ->
    Steps state trace1 (StDone heap1 v1) ->
    Steps state trace2 (StDone heap2 v2) ->
    trace1 = trace2 /\ heap1 = heap2 /\ v1 = v2.
Proof.
  exact Steps_terminal_deterministic.
Qed.

Theorem PaperSmallStepStructuredTerminalDeterminism :
  forall state phi1 heap1 v1 phi2 heap2 v2,
    StepsStayNonPairParRun state ->
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

Theorem PaperScheduledCheckedTerminalDeterminism :
  forall state phi1 heap1 v1 phi2 heap2 v2,
    ScheduledCheckedTerminal state phi1 heap1 v1 ->
    ScheduledCheckedTerminal state phi2 heap2 v2 ->
    heap1 = heap2 /\ v1 = v2.
Proof.
  exact ScheduledCheckedTerminal_deterministic.
Qed.

Theorem PaperScheduledCheckedTerminalReplay :
  forall state phi heap v,
    ScheduledCheckedTerminal state phi heap v ->
    Steps state (phi_as_list phi) (StDone heap v).
Proof.
  exact ScheduledCheckedTerminal_as_steps.
Qed.

Theorem PaperScheduledCheckedExpressionTerminalDeterminism :
  forall heap env rho e phi1 heap1 v1 phi2 heap2 v2,
    ScheduledCheckedTerminal
      (initial_state heap env rho e)
      phi1
      heap1
      v1 ->
    ScheduledCheckedTerminal
      (initial_state heap env rho e)
      phi2
      heap2
      v2 ->
    heap1 = heap2 /\ v1 = v2.
Proof.
  intros heap env rho e phi1 heap1 v1 phi2 heap2 v2 HRun1 HRun2.
  eapply PaperScheduledCheckedTerminalDeterminism; eauto.
Qed.

Theorem PaperPairParCheckedArbitraryScheduleTerminalDeterminism :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_state1 phi_left1 phi_right1
    phi_state2 phi_left2 phi_right2
    heap1 heap2 v1 v2
    theta_left1 theta_right1 theta_left2 theta_right2,
    PairParCheckPass theta_left1 theta_right1 ->
    PairParCheckPass theta_left2 theta_right2 ->
    phi_left1 ⋞ theta_left1 ->
    phi_right1 ⋞ theta_right1 ->
    phi_left2 ⋞ theta_left2 ->
    phi_right2 ⋞ theta_right2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi_state1
      phi_left1
      phi_right1
      (PPS_State (StDone heap1 v1)) ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi_state2
      phi_left2
      phi_right2
      (PPS_State (StDone heap2 v2)) ->
    heap1 = heap2 /\ v1 = v2.
Proof.
  exact PairParCheckedArbitraryScheduleContinuationTerminalDeterminism.
Qed.

Theorem PaperSmallStepStructuredEffectTerminalDeterminism :
  forall state phi1 heap1 theta1 phi2 heap2 theta2,
    StepsStayNonPairParRun state ->
    StepsPhi state phi1 (StDone heap1 (Eff theta1)) ->
    StepsPhi state phi2 (StDone heap2 (Eff theta2)) ->
    phi_as_list phi1 = phi_as_list phi2 /\
    heap1 = heap2 /\
    theta1 = theta2.
Proof.
  exact StepsPhi_effect_terminal_deterministic.
Qed.
