From Stdlib Require Import Program.Equality.
From Stdlib Require Import List.

Require Export theories.Soundness.SmallStepCorrectnessPairPar.
Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeHeapShape.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepPairParDispatch.
Require Import theories.Runtime.SmallStepStructuredTrace.
Require Import theories.Runtime.SmallStepCorrectness.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.DynamicActions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Meta.EffectFacts.
Require Import theories.Typing.TypingJudgments.

Open Scope type_scope.

(* Paper-facing checked tuple correctness is justified by the static
   BackTriangle relation.  In particular, the branch coverage facts below are
   obtained from BackTriangle plus the existing below-induction package, not
   from the runtime checked-pair package. *)
Theorem PaperScheduledPairParCheckedTerminalCorrectness :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final,
    BackTriangle
      (ctxt, rgns, rho,
       Pair_Par ef1 ea1 ef2 ea2,
       Concat
         (Concat eff1 eff2)
         (Concat (Eff_App ef1 ea1) (Eff_App ef2 ea2))) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi
      heap_final
      v_final ->
    (forall n, ScheduledSmallStepCorrectnessBelow n) ->
    exists (phi_eff1 phi_eff2 phi_pair phi_tail phi_left phi_right : Phi)
      (theta1 theta2 : Theta)
      (heap_right : Heap) (v_right : Val)
      (heap_left : Heap) (v_left : Val),
      phi =
        pairpar_checked_packed_structured_trace
          phi_eff1 phi_eff2 (Phi_Seq phi_pair phi_tail) /\
      PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 /\
      PairParLoosePackedStepsPhi
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
        phi_pair
        Phi_Nil
        phi_left
        phi_right
        (PPS_State
          (StReturn heap_left (Pair (v_left, v_right)) KDone)) /\
      ScheduledCheckedTerminal
        (initial_state heap env rho (Mu_App ef2 ea2))
        phi_right
        heap_right
        v_right /\
      ScheduledCheckedTerminal
        (initial_state heap_right env rho (Mu_App ef1 ea1))
        phi_left
        heap_left
        v_left /\
      ScheduledCheckedTerminal
        (StReturn heap_left (Pair (v_left, v_right)) KDone)
        phi_tail
        heap_final
        v_final /\
      phi_left ⋞ theta1 /\
      phi_right ⋞ theta2.
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HRun HBelow.
  eapply ScheduledCheckedPairParTerminalBranchSound_from_below_all;
    eauto.
Qed.

Theorem PaperScheduledPairParCheckedTerminalComputationTraceCoverage :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final,
    BackTriangle
      (ctxt, rgns, rho,
       Pair_Par ef1 ea1 ef2 ea2,
       Concat
         (Concat eff1 eff2)
         (Concat (Eff_App ef1 ea1) (Eff_App ef2 ea2))) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi
      heap_final
      v_final ->
    (forall n, ScheduledSmallStepCorrectnessBelow n) ->
    exists (phi_eff1 phi_eff2 phi_pair phi_tail phi_left phi_right : Phi)
      (theta1 theta2 : Theta),
      phi =
        pairpar_checked_packed_structured_trace
          phi_eff1 phi_eff2 (Phi_Seq phi_pair phi_tail) /\
      PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 /\
      phi_left ⋞ theta1 /\
      phi_right ⋞ theta2.
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HRun HBelow.
  destruct
    (PaperScheduledPairParCheckedTerminalCorrectness
      ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
      stty phi heap_final v_final
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HRun HBelow)
    as (phi_eff1 & phi_eff2 & phi_pair & phi_tail &
        phi_left & phi_right & theta1 & theta2 &
        _heap_right & _v_right & _heap_left & _v_left &
        HTrace & HObserved & _HLoose & _HRight & _HLeft &
        _HTail & HLeftSound & HRightSound).
  exists phi_eff1, phi_eff2, phi_pair, phi_tail.
  exists phi_left, phi_right, theta1, theta2.
  split; [exact HTrace |].
  split; [exact HObserved |].
  split; assumption.
Qed.

Theorem PaperScheduledPairParCheckedTerminalComputationReplay :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final,
    BackTriangle
      (ctxt, rgns, rho,
       Pair_Par ef1 ea1 ef2 ea2,
       Concat
         (Concat eff1 eff2)
         (Concat (Eff_App ef1 ea1) (Eff_App ef2 ea2))) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi
      heap_final
      v_final ->
    (forall n, ScheduledSmallStepCorrectnessBelow n) ->
    exists (phi_eff1 phi_eff2 phi_pair phi_tail phi_left phi_right : Phi)
      (theta1 theta2 : Theta)
      (heap_right : Heap) (v_right : Val)
      (heap_left : Heap) (v_left : Val),
      phi =
        pairpar_checked_packed_structured_trace
          phi_eff1 phi_eff2 (Phi_Seq phi_pair phi_tail) /\
      PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 /\
      PairParLoosePackedStepsPhi
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
        phi_pair
        Phi_Nil
        phi_left
        phi_right
        (PPS_State
          (StReturn heap_left (Pair (v_left, v_right)) KDone)) /\
      ScheduledCheckedTerminal
        (StReturn heap_left (Pair (v_left, v_right)) KDone)
        phi_tail
        heap_final
        v_final /\
      phi_left ⋞ theta1 /\
      phi_right ⋞ theta2.
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HRun HBelow.
  destruct
    (PaperScheduledPairParCheckedTerminalCorrectness
      ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
      stty phi heap_final v_final
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HRun HBelow)
    as (phi_eff1 & phi_eff2 & phi_pair & phi_tail &
        phi_left & phi_right & theta1 & theta2 &
        heap_right & v_right & heap_left & v_left &
        HTrace & HObserved & HLoose & _HRight & _HLeft &
        HTail & HLeftSound & HRightSound).
  exists phi_eff1, phi_eff2, phi_pair, phi_tail.
  exists phi_left, phi_right, theta1, theta2.
  exists heap_right, v_right, heap_left, v_left.
  split; [exact HTrace |].
  split; [exact HObserved |].
  split; [exact HLoose |].
  split; [exact HTail |].
  split; assumption.
Qed.
