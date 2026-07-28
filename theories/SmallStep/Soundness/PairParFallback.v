From Stdlib Require Import List.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Core.Values.
Require Import theories.SmallStep.Runtime.Continuation.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Runtime.Trace.
Require Import theories.SmallStep.Soundness.Correctness.
Require Import theories.SmallStep.Typing.Regularity.

Import ListNotations.

Inductive PairParFallbackRun : State -> Trace -> State -> Prop :=
| PPFR_CheckedPass :
    forall heap env rho ef1 ea1 ef2 ea2 k
      phi_summary_left phi_summary_right phi_run
      heap_summary_left heap_summary_right
      theta1 theta2 state_final,
      Steps
        (InitialState heap env rho (EEffApp ef1 ea1))
        phi_summary_left
        (StDone heap_summary_left (VSummary theta1)) ->
      Steps
        (InitialState heap_summary_left env rho (EEffApp ef2 ea2))
        phi_summary_right
        (StDone heap_summary_right (VSummary theta2)) ->
      summary_disjointb theta1 theta2 = true ->
      Steps
        (StPairParRun
          (StEval heap_summary_right env rho (EMuApp ef1 ea1) KDone)
          (StEval heap_summary_right env rho (EMuApp ef2 ea2) KDone)
          [] [] k)
        phi_run
        state_final ->
      PairParFallbackRun
        (StEval heap env rho
          (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)) k)
        (phi_summary_left ++ phi_summary_right ++ phi_run)
        state_final
| PPFR_SequentialFallback :
    forall heap env rho ef1 ea1 ef2 ea2 k
      phi_summary_left phi_summary_right phi_left phi_right
      heap_summary_left heap_summary_right heap_left heap_right
      theta1 theta2 v_left v_right,
      Steps
        (InitialState heap env rho (EEffApp ef1 ea1))
        phi_summary_left
        (StDone heap_summary_left (VSummary theta1)) ->
      Steps
        (InitialState heap_summary_left env rho (EEffApp ef2 ea2))
        phi_summary_right
        (StDone heap_summary_right (VSummary theta2)) ->
      summary_disjointb theta1 theta2 = false ->
      Steps
        (InitialState heap_summary_right env rho (EMuApp ef1 ea1))
        phi_left
        (StDone heap_left v_left) ->
      Steps
        (InitialState heap_left env rho (EMuApp ef2 ea2))
        phi_right
        (StDone heap_right v_right) ->
      PairParFallbackRun
        (StEval heap env rho
          (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)) k)
        (phi_summary_left ++ phi_summary_right ++ phi_left ++ phi_right)
        (StReturn heap_right (VPair v_left v_right) k).

Theorem PairParFallbackRun_checked_pass_to_Steps :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_summary_left phi_summary_right phi_run
    heap_summary_left heap_summary_right theta1 theta2 state_final,
    Steps
      (InitialState heap env rho (EEffApp ef1 ea1))
      phi_summary_left
      (StDone heap_summary_left (VSummary theta1)) ->
    Steps
      (InitialState heap_summary_left env rho (EEffApp ef2 ea2))
      phi_summary_right
      (StDone heap_summary_right (VSummary theta2)) ->
    summary_disjointb theta1 theta2 = true ->
    Steps
      (StPairParRun
        (StEval heap_summary_right env rho (EMuApp ef1 ea1) KDone)
        (StEval heap_summary_right env rho (EMuApp ef2 ea2) KDone)
        [] [] k)
      phi_run
      state_final ->
    Steps
      (StEval heap env rho
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)) k)
      (phi_summary_left ++ phi_summary_right ++ phi_run)
      state_final.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_summary_left phi_summary_right phi_run
    heap_summary_left heap_summary_right theta1 theta2 state_final
    HSummaryLeft HSummaryRight HCheck HRun.
  change (phi_summary_left ++ phi_summary_right ++ phi_run)
    with (label_trace LSilent ++
      (phi_summary_left ++ phi_summary_right ++ phi_run)).
  eapply StepsStep.
  - apply StepPairPar.
  - simpl.
    eapply Steps_trans.
    + pose proof
        (Steps_append_kont
          (InitialState heap env rho (EEffApp ef1 ea1))
          phi_summary_left
          (StDone heap_summary_left (VSummary theta1))
          (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)
          HSummaryLeft)
        as HLeft.
      simpl in HLeft.
      exact HLeft.
    + simpl.
      change (phi_summary_right ++ phi_run)
        with (label_trace LSilent ++ (phi_summary_right ++ phi_run)).
      eapply StepsStep.
      * apply StepPairParEff1.
      * simpl.
        eapply Steps_trans.
        -- pose proof
             (Steps_append_kont
               (InitialState heap_summary_left env rho (EEffApp ef2 ea2))
               phi_summary_right
               (StDone heap_summary_right (VSummary theta2))
               (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)
               HSummaryRight)
             as HRight.
           simpl in HRight.
           exact HRight.
        -- simpl.
           change phi_run with (label_trace LSilent ++ phi_run).
           eapply StepsStep.
           ++ eapply StepPairParCheckPass.
              exact HCheck.
           ++ simpl.
              exact HRun.
Qed.

Corollary PairParFallbackRun_checked_pass :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_summary_left phi_summary_right phi_run
    heap_summary_left heap_summary_right theta1 theta2 state_final,
    Steps
      (InitialState heap env rho (EEffApp ef1 ea1))
      phi_summary_left
      (StDone heap_summary_left (VSummary theta1)) ->
    Steps
      (InitialState heap_summary_left env rho (EEffApp ef2 ea2))
      phi_summary_right
      (StDone heap_summary_right (VSummary theta2)) ->
    summary_disjointb theta1 theta2 = true ->
    Steps
      (StPairParRun
        (StEval heap_summary_right env rho (EMuApp ef1 ea1) KDone)
        (StEval heap_summary_right env rho (EMuApp ef2 ea2) KDone)
        [] [] k)
      phi_run
      state_final ->
    PairParFallbackRun
      (StEval heap env rho
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)) k)
      (phi_summary_left ++ phi_summary_right ++ phi_run)
      state_final.
Proof.
  intros.
  eapply PPFR_CheckedPass; eauto.
Qed.

Corollary PairParFallbackRun_check_fail_sequential :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_summary_left phi_summary_right phi_left phi_right
    heap_summary_left heap_summary_right heap_left heap_right
    theta1 theta2 v_left v_right,
    Steps
      (InitialState heap env rho (EEffApp ef1 ea1))
      phi_summary_left
      (StDone heap_summary_left (VSummary theta1)) ->
    Steps
      (InitialState heap_summary_left env rho (EEffApp ef2 ea2))
      phi_summary_right
      (StDone heap_summary_right (VSummary theta2)) ->
    summary_disjointb theta1 theta2 = false ->
    Steps
      (InitialState heap_summary_right env rho (EMuApp ef1 ea1))
      phi_left
      (StDone heap_left v_left) ->
    Steps
      (InitialState heap_left env rho (EMuApp ef2 ea2))
      phi_right
      (StDone heap_right v_right) ->
    PairParFallbackRun
      (StEval heap env rho
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)) k)
      (phi_summary_left ++ phi_summary_right ++ phi_left ++ phi_right)
      (StReturn heap_right (VPair v_left v_right) k).
Proof.
  intros.
  eapply PPFR_SequentialFallback; eauto.
Qed.

Theorem PairParFallbackRun_from_component_evaluations :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_summary_left phi_summary_right phi_left phi_right
    heap_summary_left heap_summary_right heap_left heap_right
    theta1 theta2 v_left v_right,
    SummaryEvaluation
      heap env rho (EEffApp ef1 ea1)
      phi_summary_left heap_summary_left theta1 ->
    SummaryEvaluation
      heap_summary_left env rho (EEffApp ef2 ea2)
      phi_summary_right heap_summary_right theta2 ->
    ComputationEvaluation
      heap_summary_right env rho (EMuApp ef1 ea1)
      phi_left heap_left v_left ->
    ComputationEvaluation
      heap_left env rho (EMuApp ef2 ea2)
      phi_right heap_right v_right ->
    exists phi state_final,
      PairParFallbackRun
        (StEval heap env rho
          (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)) k)
        phi
        state_final /\
      (summary_disjointb theta1 theta2 = true /\
        phi = phi_summary_left ++ phi_summary_right ++ [] /\
        state_final =
          (StPairParRun
            (StEval heap_summary_right env rho (EMuApp ef1 ea1) KDone)
            (StEval heap_summary_right env rho (EMuApp ef2 ea2) KDone)
            [] [] k) \/
       summary_disjointb theta1 theta2 = false /\
        phi = phi_summary_left ++ phi_summary_right ++ phi_left ++ phi_right /\
        state_final = StReturn heap_right (VPair v_left v_right) k).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_summary_left phi_summary_right phi_left phi_right
    heap_summary_left heap_summary_right heap_left heap_right
    theta1 theta2 v_left v_right
    HSummaryLeft HSummaryRight HLeft HRight.
  unfold SummaryEvaluation in HSummaryLeft, HSummaryRight.
  unfold ComputationEvaluation in HLeft, HRight.
  destruct (summary_disjointb theta1 theta2) eqn:HCheck.
  - exists (phi_summary_left ++ phi_summary_right ++ []),
      (StPairParRun
        (StEval heap_summary_right env rho (EMuApp ef1 ea1) KDone)
        (StEval heap_summary_right env rho (EMuApp ef2 ea2) KDone)
        [] [] k).
    split.
    + eapply PPFR_CheckedPass; eauto.
      constructor.
    + left.
      repeat split; eauto.
  - exists (phi_summary_left ++ phi_summary_right ++ phi_left ++ phi_right),
      (StReturn heap_right (VPair v_left v_right) k).
    split.
    + eapply PPFR_SequentialFallback; eauto.
    + right.
      repeat split; eauto.
Qed.

Theorem PairParFallbackRun_checked_components :
  forall gamma omega heap env rho ef1 ea1 ef2 ea2 k
    phi_summary_left phi_summary_right phi_left phi_right
    heap_summary_left heap_summary_right heap_left heap_right
    theta1 theta2 v_left v_right,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    SummaryEvaluation
      heap env rho (EEffApp ef1 ea1)
      phi_summary_left heap_summary_left theta1 ->
    SummaryEvaluation
      heap_summary_left env rho (EEffApp ef2 ea2)
      phi_summary_right heap_summary_right theta2 ->
    ComputationEvaluation
      heap_summary_right env rho (EMuApp ef1 ea1)
      phi_left heap_left v_left ->
    ComputationEvaluation
      heap_left env rho (EMuApp ef2 ea2)
      phi_right heap_right v_right ->
    exists phi state_final,
      PairParFallbackRun
        (StEval heap env rho
          (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)) k)
        phi
        state_final.
Proof.
  intros gamma omega heap env rho ef1 ea1 ef2 ea2 k
    phi_summary_left phi_summary_right phi_left phi_right
    heap_summary_left heap_summary_right heap_left heap_right
    theta1 theta2 v_left v_right
    _HBack HSummaryLeft HSummaryRight HLeft HRight.
  destruct
    (PairParFallbackRun_from_component_evaluations
      heap env rho ef1 ea1 ef2 ea2 k
      phi_summary_left phi_summary_right phi_left phi_right
      heap_summary_left heap_summary_right heap_left heap_right
      theta1 theta2 v_left v_right
      HSummaryLeft HSummaryRight HLeft HRight)
    as (phi & state_final & HRun & _).
  exists phi, state_final.
  exact HRun.
Qed.
