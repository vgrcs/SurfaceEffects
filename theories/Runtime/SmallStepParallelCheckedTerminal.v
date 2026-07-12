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

Require Export theories.Runtime.SmallStepParallelCheckedTraceSafety.

Theorem pairpar_checked_initial_terminal_value_with_trace :
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
    PairParSteps
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k)
      trace (PPS_State (StDone heap' v)) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, tout) /\
      RuntimeValShape stty' tout v /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout trace heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont HSteps.
  destruct
    (pairpar_checked_initial_steps_trace_typed
      heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
      ty1 ty2 eff1 eff2 tout trace (PPS_State (StDone heap' v))
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcExp1 HTcExp2 HKont HSteps)
    as (stty' & HWT' & HExt & HTcTrace).
  destruct
    (WTPairParStateRuntimeHeapShapeAtStrong_done_value
      heap' v tout stty' HWT')
    as (HTcHeap' & HHeapShape' & HTcVal' & HValShape').
  exists stty'. split; [exact HExt |].
  split; [exact HTcHeap' |].
  split; [exact HHeapShape' |].
  split; [exact HTcVal' |].
  split; [exact HValShape' | exact HTcTrace].
Qed.

Theorem pairpar_checked_initial_kdone_terminal_value_with_trace :
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
    PairParSteps
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 KDone)
      trace (PPS_State (StDone heap' v)) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, subst_rho rho (Ty_Pair ty1 ty2)) /\
      RuntimeValShape stty' (subst_rho rho (Ty_Pair ty1 ty2)) v /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    ty1 ty2 eff1 eff2 trace heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HSteps.
  eapply
    (pairpar_checked_initial_terminal_value_with_trace
      heap env rho ef1 ea1 ef2 ea2 KDone stty ctxt rgns
      ty1 ty2 eff1 eff2 (subst_rho rho (Ty_Pair ty1 ty2))
      trace heap' v); eauto.
  constructor.
Qed.

Theorem pairpar_checked_initial_kdone_terminal_pair_with_trace :
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
    PairParSteps
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 KDone)
      trace (PPS_State (StDone heap' v)) ->
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
  intros heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    ty1 ty2 eff1 eff2 trace heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HSteps.
  destruct
    (pairpar_checked_initial_kdone_terminal_value_with_trace
      heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
      ty1 ty2 eff1 eff2 trace heap' v
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcExp1 HTcExp2 HSteps)
    as (stty' & HExt & HTcHeap' & HHeapShape' & HTcVal' & HValShape' &
        HTcTrace).
  rewrite subst_rho_pair in HTcVal'.
  rewrite subst_rho_pair in HValShape'.
  destruct
    (RuntimeValShape_pair_inv
      stty' (subst_rho rho ty1) (subst_rho rho ty2) v HValShape')
    as (v1 & v2 & Hv & HValShape1 & HValShape2).
  subst v.
  destruct
    (TcVal_pair_value_inv
      stty' (subst_rho rho ty1) (subst_rho rho ty2) v1 v2 HTcVal')
    as (HTcVal1 & HTcVal2).
  exists stty', v1, v2.
  split; [reflexivity |].
  split; [exact HExt |].
  split; [exact HTcHeap' |].
  split; [exact HHeapShape' |].
  split; [exact HTcVal1 |].
  split; [exact HValShape1 |].
  split; [exact HTcVal2 |].
  split; [exact HValShape2 | exact HTcTrace].
Qed.
