Require Export theories.Soundness.SmallStepCorrectnessDirect.
Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeHeapShape.
Require Import theories.Runtime.SmallStepSequentialSoundness.
Require Import theories.Runtime.SmallStepStructuredTrace.
Require Import theories.Runtime.SmallStepCorrectness.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.DynamicActions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Meta.EffectFacts.
Require Import theories.Typing.TypingJudgments.

Open Scope type_scope.

Theorem PaperPairParCheckedStructuredTerminalCorrectness :
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
  exact PairParCheckedStructuredTopSound_from_typed_app_actual_body_runs.
Qed.
