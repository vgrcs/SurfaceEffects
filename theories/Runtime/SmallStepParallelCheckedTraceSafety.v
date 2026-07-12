From stdpp Require Import gmap.
From Stdlib Require Import Program.Equality.

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
Require Import theories.Runtime.SmallStepTraceSafety.
Require Import theories.Runtime.SmallStepParallelProgress.
Require Import theories.Runtime.SmallStepParallelSafety.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.HeapFacts.
Require Import theories.Meta.RegionSubstitutionFacts.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.TraceTypingFacts.
Require Import theories.Meta.TypeFacts.
Require Import theories.Meta.TypingWeakeningFacts.

Require Export theories.Runtime.SmallStepParallelTraceSafe.

Theorem pairpar_checked_initial_steps_trace_typed :
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
    PairParSteps
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k)
      trace state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' /\
      StoreExtends stty stty' /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout trace state'
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont HSteps.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_steps_trace_typed; eauto.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_checked_initial; eauto.
Qed.

Theorem pairpar_checked_initial_trace_safe_typed :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
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
    PairParTraceSafeAt
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k)
      tout stty.
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_trace_safe_typed; eauto.
  - eapply WTPairParStateRuntimeHeapShapeAtStrong_checked_initial; eauto.
  - apply pairpar_checked_initial_heaps_agree.
Qed.

Theorem pairpar_checked_initial_kdone_trace_safe_typed :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    ty1 ty2 eff1 eff2,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    PairParTraceSafeAt
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 KDone)
      (subst_rho rho (Ty_Pair ty1 ty2)) stty.
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    ty1 ty2 eff1 eff2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2.
  eapply
    (pairpar_checked_initial_trace_safe_typed
      HDec heap env rho ef1 ea1 ef2 ea2 KDone stty ctxt rgns
      ty1 ty2 eff1 eff2 (subst_rho rho (Ty_Pair ty1 ty2))); eauto.
  constructor.
Qed.

Theorem pairpar_checked_initial_steps_safety_with_trace :
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
    PairParSteps
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k)
      trace state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' /\
      StoreExtends stty stty' /\
      PairParRunHeapsAgree state' /\
      PairParNotStuck state' /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout trace state'
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont HSteps.
  destruct
    (pairpar_checked_initial_steps_trace_typed
      heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
      ty1 ty2 eff1 eff2 tout trace state'
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcExp1 HTcExp2 HKont HSteps)
    as (stty' & HWT' & HExt & HTcTrace).
  assert (HAgree' : PairParRunHeapsAgree state').
  {
    eapply pairpar_steps_preserve_heap_agreement; eauto.
    apply pairpar_checked_initial_heaps_agree.
  }
  pose proof
    (pairpar_checked_initial_never_stuck_typed
      HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
      ty1 ty2 eff1 eff2 tout
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcExp1 HTcExp2 HKont)
    as HNeverStuck.
  exists stty'. split; [exact HWT' |].
  split; [exact HExt |].
  split; [exact HAgree' |].
  split; [exact (HNeverStuck trace state' HSteps) | exact HTcTrace].
Qed.

Theorem pairpar_checked_initial_kdone_steps_safety_with_trace :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    ty1 ty2 eff1 eff2 trace state',
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    PairParSteps
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 KDone)
      trace state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong
        state' (subst_rho rho (Ty_Pair ty1 ty2)) stty' /\
      StoreExtends stty stty' /\
      PairParRunHeapsAgree state' /\
      PairParNotStuck state' /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    ty1 ty2 eff1 eff2 trace state'
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HSteps.
  eapply
    (pairpar_checked_initial_steps_safety_with_trace
      HDec heap env rho ef1 ea1 ef2 ea2 KDone stty ctxt rgns
      ty1 ty2 eff1 eff2 (subst_rho rho (Ty_Pair ty1 ty2))
      trace state'); eauto.
  constructor.
Qed.

