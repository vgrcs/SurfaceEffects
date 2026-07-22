From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Wf_nat.

(* Pair_Par-specific correctness lemmas over the checked structured runtime. *)

Require Export theories.Runtime.SmallStepPaperTheorems.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepPairParDispatch.
Require Import theories.Runtime.SmallStepTraceSafety.
Require Import theories.Runtime.SmallStepStructuredTrace.
Require Import theories.Runtime.SmallStepCorrectness.
Require Import theories.Runtime.SmallStepEffectSoundness.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.DynamicActions.
Require Import theories.Core.Expressions.
Require Import theories.Core.StaticActions.
Require Import theories.Core.Values.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.EffectFacts.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.TraceTypingFacts.
Require Import theories.Meta.TypingWeakeningFacts.
Require Import theories.Meta.TypeFacts.
Require Import theories.Soundness.SmallStepBackTriangle.


Require Export theories.Soundness.SmallStepCorrectnessApps.

Theorem PairParBackTriangleEffectSummaries_readonly_heap_neutral :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyPhi phi_eff1 /\
    ReadOnlyPhi phi_eff2 /\
    heap_eff1 = heap /\
    heap_eff2 = heap.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HSummary.
  inversion HBack; subst; try discriminate.
  match goal with
  | HLeft : TcExp (ctxt, rgns, Eff_App ef1 ea1, _, _),
    HRight : TcExp (ctxt, rgns, Eff_App ef2 ea2, _, _) |- _ =>
      inversion HLeft; subst; inversion HRight; subst
  end.
  match goal with
  | HTcEff1 : TcExp
      (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, ?static_eff1),
    HTcEff2 : TcExp
      (ctxt, rgns, Eff_App ef2 ea2, Ty_Effect, ?static_eff2),
    HReadOnly1 : ReadOnlyStatic (fold_subst_eps rho ?static_eff1),
    HReadOnly2 : ReadOnlyStatic (fold_subst_eps rho ?static_eff2) |- _ =>
      destruct
        (PairParEffectSummaryStepsPhi_readonly_from_small_step_sound
          heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
          phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
          static_eff1 static_eff2
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcEff1 HTcEff2 HSummary HReadOnly1 HReadOnly2)
        as [HReadOnlyPhi1 HReadOnlyPhi2];
      destruct
        (PairParEffectSummaryStepsPhi_readonly_heap_neutral_from_small_step_sound
          heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
          phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
          static_eff1 static_eff2
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcEff1 HTcEff2 HSummary HReadOnly1 HReadOnly2)
        as [HHeapEff1 HHeapEff2];
      repeat split; assumption
  end.
Qed.

Theorem PairParCheckedParallelTopSound_reduces_to_same_heap_branch_soundness :
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
  intros heap env rho ef1 ea1 ef2 ea2
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    HTrace HSummary HPass HSteps HSoundMu1 HSoundMu2.
  eapply PairParCheckedStructuredStepsPhi_top_sound; eauto.
Qed.

Theorem PairParCheckedParallelTopSound_reduces_to_augmented_branch_soundness :
  forall heap env rho ef1 ea1 ef2 ea2
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    branch_theta1 branch_theta2 heap' v,
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
    phi_mu1 ⋞ branch_theta1 ->
    phi_mu2 ⋞ branch_theta2 ->
    phi ⋞ theta_with_phi_prefixes
      phi_eff1 phi_eff2 (Union_Theta branch_theta1 branch_theta2).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    branch_theta1 branch_theta2 heap' v
    HTrace _ _ HSteps HSoundMu1 HSoundMu2.
  subst.
  unfold pairpar_checked_structured_trace.
  apply PTS_Seq.
  - apply PTS_Par.
    + apply theta_with_phi_prefixes_left_sound.
    + apply theta_with_phi_prefixes_middle_sound.
  - apply PTS_Seq.
    + apply theta_with_phi_prefixes_right_sound.
      apply PTS_Par.
      * apply Theta_introl. exact HSoundMu1.
      * apply Theta_intror. exact HSoundMu2.
    + apply Phi_Theta_Soundness_of_phi_as_list_nil.
	      eapply PairParStepsPhi_top_terminal_state_trace_nil; eauto.
Qed.

Theorem PairParCheckedParallelTopSound_actual_runtime_branches :
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
    phi ⋞ theta_with_phi_prefixes
      phi_eff1 phi_eff2
      (Union_Theta (theta_of_phi phi_mu1) (theta_of_phi phi_mu2)).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    HTrace HSummary HPass HSteps.
  eapply
    (PairParCheckedParallelTopSound_reduces_to_augmented_branch_soundness
      heap env rho ef1 ea1 ef2 ea2
      phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2
      (theta_of_phi phi_mu1)
      (theta_of_phi phi_mu2)
      heap' v);
    eauto using theta_of_phi_sound.
Qed.

Theorem PairParCheckedParallelCanonicalTopSound_reduces_to_branch_soundness :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    stty ctxt rgns
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
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
    ReadOnlyPhi phi_eff1 /\
    ReadOnlyPhi phi_eff2 /\
    heap_eff1 = heap /\
    heap_eff2 = heap /\
    phi ⋞ theta_with_phi_prefixes
      phi_eff1 phi_eff2 (Union_Theta theta1 theta2).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    stty ctxt rgns
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTrace HSummary HPass HSteps HSoundMu1 HSoundMu2.
  destruct
    (PairParBackTriangleEffectSummaries_readonly_heap_neutral
      heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
      stty ctxt rgns
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HSummary)
    as (HReadOnlyEff1 & HReadOnlyEff2 & HHeapEff1 & HHeapEff2).
  repeat split; try assumption.
  eapply PairParCheckedParallelTopSound_reduces_to_same_heap_branch_soundness;
    eauto.
Qed.

Theorem PairParCheckedStructuredTopSound_from_typed_branch_soundness :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
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
    (BackTriangle
      (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) ->
      phi_mu1 ⋞ theta1) ->
    (BackTriangle
      (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) ->
      phi_mu2 ⋞ theta2) ->
    phi ⋞ theta_with_phi_prefixes
      phi_eff1 phi_eff2 (Union_Theta theta1 theta2).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    HTc HTrace HSummary HPass HSteps HSoundLeft HSoundRight.
  destruct
    (TcExp_pair_par_branch_backtriangles
      ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc)
    as (HBackLeft & HBackRight).
  eapply PairParCheckedStructuredStepsPhi_top_sound; eauto.
Qed.

Theorem PairParCheckedStructuredTopSound_from_typed_branch_runs :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
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
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_mu1
      (StDone heap_mu1 v_mu1) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_mu2 v_mu2) ->
    (BackTriangle
      (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) ->
      StepsPhi
        (initial_state heap env rho (Mu_App ef1 ea1))
        phi_mu1
        (StDone heap_mu1 v_mu1) ->
      phi_mu1 ⋞ theta1) ->
    (BackTriangle
      (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) ->
      StepsPhi
        (initial_state heap env rho (Mu_App ef2 ea2))
        phi_mu2
        (StDone heap_mu2 v_mu2) ->
      phi_mu2 ⋞ theta2) ->
    phi ⋞ theta_with_phi_prefixes
      phi_eff1 phi_eff2 (Union_Theta theta1 theta2).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTrace HSummary HPass HSteps HStepsLeft HStepsRight
    HSoundLeft HSoundRight.
  assert
    (HLeft :
      BackTriangle
        (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) ->
      phi_mu1 ⋞ theta1).
  {
    intros HBackLeft. eapply HSoundLeft; eauto.
  }
  assert
    (HRight :
      BackTriangle
        (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) ->
      phi_mu2 ⋞ theta2).
  {
    intros HBackRight. eapply HSoundRight; eauto.
  }
	  eapply PairParCheckedStructuredTopSound_from_typed_branch_soundness;
	    eauto.
Qed.

Theorem PairParCheckedStructuredTopSound_from_typed_branch_runs_with_branch_reasoning :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
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
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_mu1
      (StDone heap_mu1 v_mu1) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_mu2 v_mu2) ->
    (BackTriangle
      (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) ->
      StepsPhi
        (initial_state heap env rho (Mu_App ef1 ea1))
        phi_mu1
        (StDone heap_mu1 v_mu1) ->
      StepsPhi
        (initial_state heap env rho (Eff_App ef1 ea1))
        phi_eff1
        (StDone heap_eff1 (Eff theta1)) ->
      phi_mu1 ⋞ theta1) ->
    (BackTriangle
      (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) ->
      StepsPhi
        (initial_state heap env rho (Mu_App ef2 ea2))
        phi_mu2
        (StDone heap_mu2 v_mu2) ->
      StepsPhi
        (initial_state heap env rho (Eff_App ef2 ea2))
        phi_eff2
        (StDone heap_eff2 (Eff theta2)) ->
      phi_mu2 ⋞ theta2) ->
    phi ⋞ theta_with_phi_prefixes
      phi_eff1 phi_eff2 (Union_Theta theta1 theta2).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTrace HSummary HPass HSteps HMu1 HMu2
    HSoundLeft HSoundRight.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HEff1 HEff2]; subst.
  destruct
    (TcExp_pair_par_branch_backtriangles
      ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc)
    as (HBackLeft & HBackRight).
  pose proof (HSoundLeft HBackLeft HMu1 HEff1) as HSoundMu1.
  pose proof (HSoundRight HBackRight HMu2 HEff2) as HSoundMu2.
  eapply PairParCheckedStructuredStepsPhi_top_sound; eauto.
Qed.

Theorem PairParCheckedStructuredTopSound_from_typed_app_body_runs :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
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
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_mu1
      (StDone heap_mu1 v_mu1) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_mu2 v_mu2) ->
    StepsStayNonPairParRun (initial_state heap env rho ef1) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea1)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef2) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea2)) ->
    exists phi_fun_mu1 phi_arg_mu1 phi_body_mu1
      phi_fun_mu2 phi_arg_mu2 phi_body_mu2,
      ReadOnlyPhi phi_fun_mu1 /\
      ReadOnlyPhi phi_arg_mu1 /\
      ReadOnlyPhi phi_fun_mu2 /\
      ReadOnlyPhi phi_arg_mu2 /\
      (phi_body_mu1 ⋞ theta1 ->
       phi_body_mu2 ⋞ theta2 ->
       phi ⋞ theta_with_phi_prefixes
         phi_eff1 phi_eff2
         (Union_Theta
           (theta_with_phi_prefixes phi_fun_mu1 phi_arg_mu1 theta1)
           (theta_with_phi_prefixes phi_fun_mu2 phi_arg_mu2 theta2))).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTrace HSummary HPass HSteps HMu1 HMu2
    HStayFun1 HStayArg1 HStayFun2 HStayArg2.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HEff1 HEff2]; subst.
  destruct
    (TcExp_pair_par_branch_backtriangles
      ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc)
    as (HBackLeft & HBackRight).
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_from_body_soundness
      heap env rho ef1 ea1
      phi_mu1 heap_mu1 v_mu1 phi_eff1 heap_eff1 theta1
      stty ctxt rgns
      HBackLeft HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu1 HEff1 HStayFun1 HStayArg1)
    as (phi_fun_mu1 & phi_arg_mu1 & phi_body_mu1 &
        phi_fun_eff1 & phi_arg_eff1 & phi_body_eff1 &
        env_closure1 & rho_closure1 & f1 & x1 & ec1 & ee1 & v_arg1 &
        _HFunMu1 & _HFunEff1 & _HArgMu1 & _HArgEff1 &
        _HBodyMu1 & _HBodyEff1 & _HFunTrace1 & _HArgTrace1 &
        HFunRO1 & HArgRO1 & HSoundLeft).
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_from_body_soundness
      heap env rho ef2 ea2
      phi_mu2 heap_mu2 v_mu2 phi_eff2 heap_eff2 theta2
      stty ctxt rgns
      HBackRight HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu2 HEff2 HStayFun2 HStayArg2)
    as (phi_fun_mu2 & phi_arg_mu2 & phi_body_mu2 &
        phi_fun_eff2 & phi_arg_eff2 & phi_body_eff2 &
        env_closure2 & rho_closure2 & f2 & x2 & ec2 & ee2 & v_arg2 &
        _HFunMu2 & _HFunEff2 & _HArgMu2 & _HArgEff2 &
        _HBodyMu2 & _HBodyEff2 & _HFunTrace2 & _HArgTrace2 &
        HFunRO2 & HArgRO2 & HSoundRight).
  exists phi_fun_mu1, phi_arg_mu1, phi_body_mu1.
  exists phi_fun_mu2, phi_arg_mu2, phi_body_mu2.
  repeat split; try assumption.
  intros HBodySound1 HBodySound2.
  pose proof (HSoundLeft HBodySound1) as HBranchSound1.
  pose proof (HSoundRight HBodySound2) as HBranchSound2.
  eapply
    (PairParCheckedParallelTopSound_reduces_to_augmented_branch_soundness
      heap env rho ef1 ea1 ef2 ea2
      (pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2)
      phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2
      (theta_with_phi_prefixes phi_fun_mu1 phi_arg_mu1 theta1)
      (theta_with_phi_prefixes phi_fun_mu2 phi_arg_mu2 theta2)
      heap' v);
	  eauto.
Qed.

Theorem PairParCheckedStructuredTopSound_from_typed_app_body_runs_with_body_reasoning :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
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
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_mu1
      (StDone heap_mu1 v_mu1) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_mu2 v_mu2) ->
    StepsStayNonPairParRun (initial_state heap env rho ef1) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea1)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef2) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea2)) ->
    (forall stty_body ctxt_body rgns_body tyx effc tyc effe
       env_closure rho_closure f x ec ee v_arg
       phi_body_mu phi_body_eff,
      StoreExtends stty stty_body ->
      TcHeap (heap, stty_body) ->
      RuntimeHeapShape heap stty_body ->
      TcRho (rho_closure, rgns_body) ->
      TcInc (ctxt_body, rgns_body) ->
      TcEnv (stty_body, rho_closure, env_closure, ctxt_body) ->
      RuntimeEnvShape stty_body rho_closure env_closure ctxt_body ->
      TcExp
        (ctxt_body, rgns_body, Mu f x ec ee,
          Ty_Arrow tyx effc tyc effe Ty_Effect,
          Empty_Static_Action) ->
      BackTriangle
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, rho_closure, ec, ee) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, ec, tyc, effc) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, ee, Ty_Effect, effe) ->
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu1 v_mu1) ->
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff1 (Eff theta1)) ->
      phi_body_mu ⋞ theta1) ->
    (forall stty_body ctxt_body rgns_body tyx effc tyc effe
       env_closure rho_closure f x ec ee v_arg
       phi_body_mu phi_body_eff,
      StoreExtends stty stty_body ->
      TcHeap (heap, stty_body) ->
      RuntimeHeapShape heap stty_body ->
      TcRho (rho_closure, rgns_body) ->
      TcInc (ctxt_body, rgns_body) ->
      TcEnv (stty_body, rho_closure, env_closure, ctxt_body) ->
      RuntimeEnvShape stty_body rho_closure env_closure ctxt_body ->
      TcExp
        (ctxt_body, rgns_body, Mu f x ec ee,
          Ty_Arrow tyx effc tyc effe Ty_Effect,
          Empty_Static_Action) ->
      BackTriangle
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, rho_closure, ec, ee) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, ec, tyc, effc) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, ee, Ty_Effect, effe) ->
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu2 v_mu2) ->
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff2 (Eff theta2)) ->
      phi_body_mu ⋞ theta2) ->
    exists phi_fun_mu1 phi_arg_mu1 phi_fun_mu2 phi_arg_mu2,
      ReadOnlyPhi phi_fun_mu1 /\
      ReadOnlyPhi phi_arg_mu1 /\
      ReadOnlyPhi phi_fun_mu2 /\
      ReadOnlyPhi phi_arg_mu2 /\
      phi ⋞ theta_with_phi_prefixes
        phi_eff1 phi_eff2
        (Union_Theta
          (theta_with_phi_prefixes phi_fun_mu1 phi_arg_mu1 theta1)
          (theta_with_phi_prefixes phi_fun_mu2 phi_arg_mu2 theta2)).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTrace HSummary HPass HSteps HMu1 HMu2
    HStayFun1 HStayArg1 HStayFun2 HStayArg2
    HBodyReasoningLeft HBodyReasoningRight.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HEff1 HEff2]; subst.
  destruct
    (TcExp_pair_par_branch_backtriangles
      ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc)
    as (HBackLeft & HBackRight).
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_with_body_reasoning
      heap env rho ef1 ea1
      phi_mu1 heap_mu1 v_mu1 phi_eff1 heap_eff1 theta1
      stty ctxt rgns
      HBackLeft HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu1 HEff1 HStayFun1 HStayArg1 HBodyReasoningLeft)
    as (phi_fun_mu1 & phi_arg_mu1 & phi_body_mu1 &
        phi_fun_eff1 & phi_arg_eff1 & phi_body_eff1 &
        env_closure1 & rho_closure1 & f1 & x1 & ec1 & ee1 & v_arg1 &
        _HFunMu1 & _HFunEff1 & _HArgMu1 & _HArgEff1 &
        _HBodyMu1 & _HBodyEff1 & HFunRO1 & HArgRO1 & HBranchSound1).
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_with_body_reasoning
      heap env rho ef2 ea2
      phi_mu2 heap_mu2 v_mu2 phi_eff2 heap_eff2 theta2
      stty ctxt rgns
      HBackRight HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu2 HEff2 HStayFun2 HStayArg2 HBodyReasoningRight)
    as (phi_fun_mu2 & phi_arg_mu2 & phi_body_mu2 &
        phi_fun_eff2 & phi_arg_eff2 & phi_body_eff2 &
        env_closure2 & rho_closure2 & f2 & x2 & ec2 & ee2 & v_arg2 &
        _HFunMu2 & _HFunEff2 & _HArgMu2 & _HArgEff2 &
        _HBodyMu2 & _HBodyEff2 & HFunRO2 & HArgRO2 & HBranchSound2).
  exists phi_fun_mu1, phi_arg_mu1, phi_fun_mu2, phi_arg_mu2.
  repeat split; try assumption.
  eapply
    (PairParCheckedParallelTopSound_reduces_to_augmented_branch_soundness
      heap env rho ef1 ea1 ef2 ea2
      (pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2)
      phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2
      (theta_with_phi_prefixes phi_fun_mu1 phi_arg_mu1 theta1)
      (theta_with_phi_prefixes phi_fun_mu2 phi_arg_mu2 theta2)
      heap' v);
	    eauto.
Qed.

Theorem PairParCheckedStructuredTopSound_from_typed_app_runs_from_below :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
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
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_mu1
      (StDone heap_mu1 v_mu1) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_mu2 v_mu2) ->
    StepsStayNonPairParRun (initial_state heap env rho ef1) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea1)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef2) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea2)) ->
    (forall n, SmallStepCorrectnessBelow n) ->
    exists phi_fun_mu1 phi_arg_mu1 phi_fun_mu2 phi_arg_mu2,
      ReadOnlyPhi phi_fun_mu1 /\
      ReadOnlyPhi phi_arg_mu1 /\
      ReadOnlyPhi phi_fun_mu2 /\
      ReadOnlyPhi phi_arg_mu2 /\
      phi ⋞ theta_with_phi_prefixes
        phi_eff1 phi_eff2
        (Union_Theta
          (theta_with_phi_prefixes phi_fun_mu1 phi_arg_mu1 theta1)
          (theta_with_phi_prefixes phi_fun_mu2 phi_arg_mu2 theta2)).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTrace HSummary HPass HSteps HMu1 HMu2
    HStayFun1 HStayArg1 HStayFun2 HStayArg2 HBelowAll.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HEff1 HEff2]; subst.
  destruct
    (TcExp_pair_par_branch_backtriangles
      ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc)
    as (HBackLeft & HBackRight).
  destruct (StepsPhi_to_StepsPhiN _ _ _ HMu1) as (n1 & HMu1N).
  destruct (StepsPhi_to_StepsPhiN _ _ _ HMu2) as (n2 & HMu2N).
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_from_below
      n1 heap env rho ef1 ea1
      phi_mu1 heap_mu1 v_mu1 phi_eff1 heap_eff1 theta1
      stty ctxt rgns
      HBackLeft HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu1N HEff1 HStayFun1 HStayArg1 (HBelowAll n1))
    as (phi_fun_mu1 & phi_arg_mu1 & phi_body_mu1 &
        phi_fun_eff1 & phi_arg_eff1 & phi_body_eff1 &
        env_closure1 & rho_closure1 & f1 & x1 & ec1 & ee1 & v_arg1 &
        _HFunMu1 & _HFunEff1 & _HArgMu1 & _HArgEff1 &
        _HBodyMu1 & _HBodyEff1 & HFunRO1 & HArgRO1 & HBranchSound1).
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_from_below
      n2 heap env rho ef2 ea2
      phi_mu2 heap_mu2 v_mu2 phi_eff2 heap_eff2 theta2
      stty ctxt rgns
      HBackRight HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu2N HEff2 HStayFun2 HStayArg2 (HBelowAll n2))
    as (phi_fun_mu2 & phi_arg_mu2 & phi_body_mu2 &
        phi_fun_eff2 & phi_arg_eff2 & phi_body_eff2 &
        env_closure2 & rho_closure2 & f2 & x2 & ec2 & ee2 & v_arg2 &
        _HFunMu2 & _HFunEff2 & _HArgMu2 & _HArgEff2 &
        _HBodyMu2 & _HBodyEff2 & HFunRO2 & HArgRO2 & HBranchSound2).
  exists phi_fun_mu1, phi_arg_mu1, phi_fun_mu2, phi_arg_mu2.
  repeat split; try assumption.
  eapply
    (PairParCheckedParallelTopSound_reduces_to_augmented_branch_soundness
      heap env rho ef1 ea1 ef2 ea2
      (pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2)
      phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2
      (theta_with_phi_prefixes phi_fun_mu1 phi_arg_mu1 theta1)
      (theta_with_phi_prefixes phi_fun_mu2 phi_arg_mu2 theta2)
      heap' v);
    eauto.
Qed.

Theorem PairParCheckedStructuredTopSound_same_abstraction_from_below :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
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
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_mu1
      (StDone heap_mu1 v_mu1) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_mu2 v_mu2) ->
    StepsStayNonPairParRun (initial_state heap env rho ef1) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea1)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef2) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea2)) ->
    (forall n, SmallStepCorrectnessBelow n) ->
    phi ⋞ theta_with_phi_prefixes
      phi_eff1 phi_eff2 (Union_Theta theta1 theta2).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTrace HSummary HPass HSteps HMu1 HMu2
    HStayFun1 HStayArg1 HStayFun2 HStayArg2 HBelowAll.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HEff1 HEff2]; subst.
  destruct
    (TcExp_pair_par_branch_backtriangles
      ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc)
    as (HBackLeft & HBackRight).
  destruct (StepsPhi_to_StepsPhiN _ _ _ HMu1) as (n1 & HMu1N).
  destruct (StepsPhi_to_StepsPhiN _ _ _ HMu2) as (n2 & HMu2N).
  pose proof
    (MuAppEffAppTerminalSound_raw_from_below
      n1 heap env rho ef1 ea1
      phi_mu1 heap_mu1 v_mu1 phi_eff1 heap_eff1 theta1
      stty ctxt rgns
      HBackLeft HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu1N HEff1 HStayFun1 HStayArg1 (HBelowAll n1))
    as HSoundLeft.
  pose proof
    (MuAppEffAppTerminalSound_raw_from_below
      n2 heap env rho ef2 ea2
      phi_mu2 heap_mu2 v_mu2 phi_eff2 heap_eff2 theta2
      stty ctxt rgns
      HBackRight HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu2N HEff2 HStayFun2 HStayArg2 (HBelowAll n2))
    as HSoundRight.
  eapply PairParCheckedParallelTopSound_reduces_to_same_heap_branch_soundness;
    eauto.
Qed.

Theorem PairParCheckedStructuredTopSound_from_typed_app_actual_body_runs :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
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
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_mu1
      (StDone heap_mu1 v_mu1) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_mu2 v_mu2) ->
    StepsStayNonPairParRun (initial_state heap env rho ef1) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea1)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef2) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea2)) ->
    exists phi_fun_mu1 phi_arg_mu1 phi_body_mu1
      phi_fun_mu2 phi_arg_mu2 phi_body_mu2,
      ReadOnlyPhi phi_fun_mu1 /\
      ReadOnlyPhi phi_arg_mu1 /\
      ReadOnlyPhi phi_fun_mu2 /\
      ReadOnlyPhi phi_arg_mu2 /\
      phi ⋞ theta_with_phi_prefixes
        phi_eff1 phi_eff2
        (Union_Theta
          (theta_with_phi_prefixes
            phi_fun_mu1 phi_arg_mu1 (theta_of_phi phi_body_mu1))
          (theta_with_phi_prefixes
            phi_fun_mu2 phi_arg_mu2 (theta_of_phi phi_body_mu2))).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTrace HSummary HPass HSteps HMu1 HMu2
    HStayFun1 HStayArg1 HStayFun2 HStayArg2.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HEff1 HEff2]; subst.
  destruct
    (TcExp_pair_par_branch_backtriangles
      ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc)
    as (HBackLeft & HBackRight).
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_actual_body
      heap env rho ef1 ea1
      phi_mu1 heap_mu1 v_mu1 phi_eff1 heap_eff1 theta1
      stty ctxt rgns
      HBackLeft HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu1 HEff1 HStayFun1 HStayArg1)
    as (phi_fun_mu1 & phi_arg_mu1 & phi_body_mu1 &
        phi_fun_eff1 & phi_arg_eff1 & phi_body_eff1 &
        env_closure1 & rho_closure1 & f1 & x1 & ec1 & ee1 & v_arg1 &
        _HFunMu1 & _HFunEff1 & _HArgMu1 & _HArgEff1 &
        _HBodyMu1 & _HBodyEff1 & HFunRO1 & HArgRO1 & HSoundLeft).
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_actual_body
      heap env rho ef2 ea2
      phi_mu2 heap_mu2 v_mu2 phi_eff2 heap_eff2 theta2
      stty ctxt rgns
      HBackRight HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu2 HEff2 HStayFun2 HStayArg2)
    as (phi_fun_mu2 & phi_arg_mu2 & phi_body_mu2 &
        phi_fun_eff2 & phi_arg_eff2 & phi_body_eff2 &
        env_closure2 & rho_closure2 & f2 & x2 & ec2 & ee2 & v_arg2 &
        _HFunMu2 & _HFunEff2 & _HArgMu2 & _HArgEff2 &
        _HBodyMu2 & _HBodyEff2 & HFunRO2 & HArgRO2 & HSoundRight).
  exists phi_fun_mu1, phi_arg_mu1, phi_body_mu1.
  exists phi_fun_mu2, phi_arg_mu2, phi_body_mu2.
  repeat split; try assumption.
  eapply
    (PairParCheckedParallelTopSound_reduces_to_augmented_branch_soundness
      heap env rho ef1 ea1 ef2 ea2
      (pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2)
      phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2
      (theta_with_phi_prefixes
        phi_fun_mu1 phi_arg_mu1 (theta_of_phi phi_body_mu1))
      (theta_with_phi_prefixes
        phi_fun_mu2 phi_arg_mu2 (theta_of_phi phi_body_mu2))
      heap' v);
    eauto.
Qed.
