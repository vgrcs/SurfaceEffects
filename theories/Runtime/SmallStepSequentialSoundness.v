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

Theorem pairpar_check_fails_to_sequential_start :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k,
    PairParCheckFail theta1 theta2 ->
    Step
      (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
      Silent
      (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k HFail.
  unfold pairpar_check_state, pairpar_sequential_start.
  eapply Step_PairPar_FallbackMu1; eauto.
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

Theorem pairpar_check_fail_dispatch :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k,
    PairParCheckFail theta1 theta2 ->
    Step
      (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
      Silent
      (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k HFail.
  now apply pairpar_check_fails_to_sequential_start.
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
      Step
        (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
        Silent
        (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k)).
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
    now apply pairpar_check_fail_dispatch.
Qed.

Theorem pairpar_check_fail_sequential_preservation :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k tout stty,
    WTStateRuntimeHeapShapeAt
      (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
      tout stty ->
    PairParCheckFail theta1 theta2 ->
    exists stty',
      WTStateRuntimeHeapShapeAt
        (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k)
        tout stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k tout stty HWT HFail.
  pose proof
    (pairpar_check_fails_to_sequential_start
      heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k HFail)
    as HStep.
  destruct
    (WTStateRuntimeHeapShapeAt_step_preservation
      (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
      tout stty Silent
      (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k)
      HWT HStep)
    as (stty' & HWT' & _ & _ & HExt).
  exists stty'. split; [exact HWT' | exact HExt].
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

Theorem pairpar_check_fail_sequential_trace_safe_at :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k tout stty,
    WTStateRuntimeHeapShapeAt
      (pairpar_check_state heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
      tout stty ->
    PairParCheckFail theta1 theta2 ->
    exists stty',
      StoreExtends stty stty' /\
      StateTraceSafeAt
        (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k)
        tout stty'.
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k tout stty
    HWT HFail.
  destruct
    (pairpar_check_fail_sequential_preservation
      heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k tout stty HWT HFail)
    as (stty' & HWT' & HExt).
  exists stty'. split; [exact HExt |].
  eapply WTStateRuntimeHeapShapeAt_trace_safe_typed; eauto.
Qed.

Theorem pairpar_check_fail_sequential_trace_safe :
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
    exists stty',
      StoreExtends stty stty' /\
      StateTraceSafeAt
        (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k)
        tout stty'.
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout theta1 theta2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont HFail.
  eapply pairpar_check_fail_sequential_trace_safe_at; eauto.
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
      exists stty',
        StoreExtends stty stty' /\
        StateTraceSafeAt
          (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k)
          tout stty').
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout theta1 theta2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont.
  destruct (HDec theta1 theta2) as [HPass | HFail].
  - left. split; [exact HPass |].
    eapply pairpar_check_pass_checked_trace_safe; eauto.
  - right. split; [exact HFail |].
    eapply pairpar_check_fail_sequential_trace_safe; eauto.
Qed.
