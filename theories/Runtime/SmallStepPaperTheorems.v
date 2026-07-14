From stdpp Require Import gmap.

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
Require Import theories.Runtime.SmallStepTraceSafety.
Require Import theories.Runtime.SmallStepParallelTraceSafe.
Require Import theories.Runtime.SmallStepSequentialSoundness.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.StoreFacts.
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

Theorem PaperPairParCheckedOrFallbackTraceSafety :
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
  exact pairpar_check_decidable_trace_safe.
Qed.

Theorem PaperPairParCheckedOrFallbackTerminalSoundness :
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
      forall trace heap' v,
        Steps
          (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k)
          trace (StDone heap' v) ->
        exists stty',
          StoreExtends stty stty' /\
          TcHeap (heap', stty') /\
          RuntimeHeapShape heap' stty' /\
          TcVal (stty', v, tout) /\
          RuntimeValShape stty' tout v /\
          TcPhi stty' (trace_as_phi trace)).
Proof.
  exact pairpar_check_decidable_terminal_value.
Qed.
