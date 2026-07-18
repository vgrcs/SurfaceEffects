From Stdlib Require Import List.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepPreservationTheorems.
Require Import theories.Runtime.SmallStepExplicitStoreBase.
Require Import theories.Runtime.SmallStepExplicitStoreTheorems.
Require Import theories.Runtime.SmallStepTraceSafety.
Require Import theories.Runtime.SmallStepParallelTyping.
Require Import theories.Runtime.SmallStepParallelTraceSafe.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.TraceTypingFacts.

Definition PairParCheckPass (theta1 theta2 : Theta) : Prop :=
  Disjointness theta1 theta2 /\ ~ Conflictness theta1 theta2.

Definition PairParCheckFail (theta1 theta2 : Theta) : Prop :=
  ~ PairParCheckPass theta1 theta2.

Definition pairpar_check_state
    (heap : Heap) (env : Env) (rho : Rho)
    (ef1 ea1 ef2 ea2 : Expr) (theta1 theta2 : Theta)
    (k : Kont) : State :=
  StReturn heap (Eff theta2)
    (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k).

Definition pairpar_sequential_start
    (heap : Heap) (env : Env) (rho : Rho)
    (ef1 ea1 ef2 ea2 : Expr) (k : Kont) : State :=
  StEval heap env rho (Mu_App ef1 ea1)
    (KPairParMu1 ef2 ea2 env rho k).

Definition pairpar_checked_start
    (heap : Heap) (env : Env) (rho : Rho)
    (ef1 ea1 ef2 ea2 : Expr) (k : Kont) : PairParState :=
  pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k.

Theorem pairpar_check_passes_to_sequential_start :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k,
    PairParCheckPass theta1 theta2 ->
    Step
      (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
      Silent
      (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k [HDisj HNoConf].
  unfold pairpar_check_state, pairpar_sequential_start.
  eapply Step_PairPar_EvalMu1; eauto.
Qed.

Theorem pairpar_check_fail_no_step :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k,
    PairParCheckFail theta1 theta2 ->
    forall label state',
      ~ Step
        (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
        label state'.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k
    HFail label state' HStep.
  unfold pairpar_check_state in HStep.
  inversion HStep; subst.
  apply HFail.
  split; assumption.
Qed.

Theorem pairpar_checked_start_can_step_both_branches :
  forall heap env rho ef1 ea1 ef2 ea2 k,
    exists left_state right_state,
      PairParStep
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
        Silent left_state /\
      PairParStep
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
        Silent right_state.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k.
  unfold pairpar_checked_start.
  eexists; eexists.
  split.
  - eapply pairpar_checked_initial_left_step.
    constructor.
  - eapply pairpar_checked_initial_right_step.
    constructor.
Qed.

Theorem pairpar_check_pass_dispatch :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k,
    PairParCheckPass theta1 theta2 ->
    Step
      (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
      Silent
      (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k) /\
    PairParRunHeapsAgree
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k) /\
    exists left_state right_state,
      PairParStep
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
        Silent left_state /\
      PairParStep
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
        Silent right_state.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k HPass.
  split.
  - now apply pairpar_check_passes_to_sequential_start.
  - split.
    + apply pairpar_checked_initial_heaps_agree.
    + apply pairpar_checked_start_can_step_both_branches.
Qed.

Theorem pairpar_check_fail_boundary :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k,
    PairParCheckFail theta1 theta2 ->
    PairParCheckState
      (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k _.
  unfold pairpar_check_state.
  constructor.
Qed.

Theorem pairpar_check_decidable_dispatch :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k,
    (PairParCheckPass theta1 theta2 /\
      Step
        (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
        Silent
        (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k) /\
      PairParRunHeapsAgree
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k) /\
      (exists left_state right_state,
        PairParStep
          (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
          Silent left_state /\
        PairParStep
          (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
          Silent right_state)) \/
    (PairParCheckFail theta1 theta2 /\
      PairParCheckState
        (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k) /\
      forall label state',
        ~ Step
          (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
          label state').
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k.
  destruct (HDec theta1 theta2) as [HPass | HFail].
  - left.
    destruct
      (pairpar_check_pass_dispatch
        heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k HPass)
      as (HStep & HAgree & HBranches).
    split; [exact HPass |].
    split; [exact HStep |].
    split; [exact HAgree | exact HBranches].
  - right.
    split; [exact HFail |].
    split.
    + now apply pairpar_check_fail_boundary.
    + now apply pairpar_check_fail_no_step.
Qed.

Theorem pairpar_check_state_typed :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    WTStateRuntimeHeapShapeAt
      (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
      tout stty.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont.
  unfold pairpar_check_state.
  eapply WTSRHSA_Return with (t := Ty_Effect); eauto.
  - constructor.
  - eapply WTKR_PairParEff2
      with (ctxt := ctxt) (rgns := rgns)
        (ty1 := ty1) (ty2 := ty2) (eff1 := eff1) (eff2 := eff2);
      eauto.
  - constructor.
Qed.

Theorem pairpar_check_fail_not_stuck_at :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k tout stty,
    WTStateRuntimeHeapShapeAt
      (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
      tout stty ->
    PairParCheckFail theta1 theta2 ->
    NotStuck
      (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k).
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k tout stty
    HWT HFail.
  right. right.
  now apply pairpar_check_fail_boundary.
Qed.

Theorem pairpar_check_fail_not_stuck :
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
    PairParCheckFail theta1 theta2 ->
    NotStuck
      (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k).
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout theta1 theta2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont HFail.
  eapply pairpar_check_fail_not_stuck_at; eauto.
  eapply pairpar_check_state_typed; eauto.
Qed.

Theorem pairpar_check_pass_checked_trace_safe :
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
    PairParCheckPass theta1 theta2 ->
    PairParTraceSafeAt
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      tout stty.
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout theta1 theta2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont _.
  unfold pairpar_checked_start.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_trace_safe_typed; eauto.
  - eapply WTPairParStateRuntimeHeapShapeAtStrong_checked_initial; eauto.
  - apply pairpar_checked_initial_heaps_agree.
Qed.

Theorem pairpar_check_decidable_trace_safe :
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
  intros HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout theta1 theta2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont.
  destruct (HDec theta1 theta2) as [HPass | HFail].
  - left. split; [exact HPass |].
    eapply pairpar_check_pass_checked_trace_safe; eauto.
  - right. split; [exact HFail |].
    eapply pairpar_check_fail_not_stuck; eauto.
Qed.

Theorem pairpar_check_decidable_terminal_value :
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
  intros HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout theta1 theta2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont.
  destruct
    (pairpar_check_decidable_trace_safe
      HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
      ty1 ty2 eff1 eff2 tout theta1 theta2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcExp1 HTcExp2 HKont)
    as [(HPass & HSafe) | (HFail & HSafe)].
  - left.
    split; [exact HPass |].
    intros trace heap' v HSteps.
    eapply PairParTraceSafeAt_terminal_value; eauto.
  - right.
    split; [exact HFail | exact HSafe].
Qed.
