From Stdlib Require Import Program.Equality.

Require Export theories.Soundness.SmallStepCorrectnessPairPar.
Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeKontTyping.
Require Import theories.Runtime.SmallStepRuntimeHeapShape.
Require Import theories.Runtime.SmallStepPairParDispatch.
Require Import theories.Runtime.SmallStepStructuredTrace.
Require Import theories.Runtime.SmallStepCorrectness.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.DynamicActions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Meta.EffectFacts.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.TraceTypingFacts.
Require Import theories.Typing.TypingJudgments.

Open Scope type_scope.

Theorem PaperScheduledPairParCheckedTerminalCorrectness :
  forall heap env rho ef1 ea1 ef2 ea2 phi heap' v,
    ScheduledStepsPhi
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi
      (StDone heap' v) ->
    exists phi_eff1 phi_eff2 theta1 theta2,
      PairParCheckPass theta1 theta2 /\
      phi ⋞ theta_with_phi_prefixes
        phi_eff1 phi_eff2 (Union_Theta theta1 theta2).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 phi heap' v HSteps.
  remember (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
    as state0 eqn:HState0.
  revert heap env rho ef1 ea1 ef2 ea2 HState0.
  dependent induction HSteps; intros heap0 env0 rho0 ef10 ea10 ef20 ea20 HState0.
  - discriminate HState0.
  - rewrite HState0 in H. simpl in H. contradiction.
  - inversion HState0; subst.
    destruct
      (PairParCheckedPackedStepsPhi_unpacked
        theta1 theta2
        (pairpar_checked_start heap0 env0 rho0 ef10 ea10 ef20 ea20 KDone)
        phi_mu
        (PPS_State (StDone heap' v))
        H1)
      as (phi_mu_state & phi_mu1 & phi_mu2 &
          HRun & HMuTrace & HSoundMu1 & HSoundMu2).
    subst phi_mu.
    exists phi_eff1, phi_eff2, theta1, theta2.
    split; [exact H0 |].
    eapply
      (PairParCheckedParallelTopSound_reduces_to_same_heap_branch_soundness
        heap0 env0 rho0 ef10 ea10 ef20 ea20
        (pairpar_checked_packed_structured_trace
          phi_eff1 phi_eff2
          (pairpar_runtime_phi
            (pairpar_checked_start heap0 env0 rho0 ef10 ea10 ef20 ea20 KDone)
            phi_mu_state phi_mu1 phi_mu2))
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
        heap_eff1 theta1 heap_eff2 theta2 heap' v);
      eauto.
Qed.

Theorem PaperPairParCheckedStructuredTerminalCorrectness :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v,
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
    phi ⋞ theta_with_phi_prefixes
      phi_eff1 phi_eff2
      (Union_Theta (theta_of_phi phi_mu1) (theta_of_phi phi_mu2)).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    _HTc _HTcHeap _HHeapShape _HTcRho _HTcInc _HTcEnv _HEnvShape
    HTrace HSummary HPass HSteps.
  eapply PairParCheckedParallelTopSound_actual_runtime_branches; eauto.
Qed.
