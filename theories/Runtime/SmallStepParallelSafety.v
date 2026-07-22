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

Require Import theories.Runtime.SmallStepParallelPreservationBase.
Require Import theories.Runtime.SmallStepParallelProgress.

Theorem pairpar_checked_initial_steps_preservation :
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
      StoreExtends stty stty'.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout trace state'
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont HSteps.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_steps_preservation; eauto.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_checked_initial; eauto.
Qed.

Theorem pairpar_checked_initial_steps_safety :
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
      PairParNotStuck state'.
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout trace state'
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont HSteps.
  destruct
    (pairpar_checked_initial_steps_preservation
      heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
      ty1 ty2 eff1 eff2 tout trace state'
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcExp1 HTcExp2 HKont HSteps)
    as (stty' & HWT' & HExt).
  assert (HAgree' : PairParRunHeapsAgree state').
  {
    eapply pairpar_steps_preserve_heap_agreement; eauto.
    apply pairpar_checked_initial_heaps_agree.
  }
  exists stty'. split; [exact HWT' | split; [exact HExt | split; [exact HAgree' |]]].
  pose proof
    (pairpar_checked_initial_never_stuck_typed
      HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
      ty1 ty2 eff1 eff2 tout
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcExp1 HTcExp2 HKont)
    as HNeverStuck.
  exact (HNeverStuck trace state' HSteps).
Qed.

Lemma WTPairParStateRuntimeHeapShapeAtStrong_done_value :
  forall heap v tout stty,
    WTPairParStateRuntimeHeapShapeAtStrong
      (PPS_State (StDone heap v)) tout stty ->
    TcHeap (heap, stty) /\
    RuntimeHeapShape heap stty /\
    TcVal (stty, v, tout) /\
    RuntimeValShape stty tout v.
Proof.
  intros heap v tout stty HWT.
  dependent destruction HWT.
  match goal with
  | HState : WTStateRuntimeHeapShapeAt (StDone heap v) tout stty |- _ =>
      dependent destruction HState
  end.
  split; [exact H0 |].
  split; [exact H1 |].
  split; [exact H2 | exact H3].
Qed.

Theorem pairpar_checked_initial_terminal_value :
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
      RuntimeValShape stty' tout v.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout trace heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont HSteps.
  destruct
    (pairpar_checked_initial_steps_preservation
      heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
      ty1 ty2 eff1 eff2 tout trace (PPS_State (StDone heap' v))
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcExp1 HTcExp2 HKont HSteps)
    as (stty' & HWT' & HExt).
  destruct
    (WTPairParStateRuntimeHeapShapeAtStrong_done_value
      heap' v tout stty' HWT')
    as (HTcHeap' & HHeapShape' & HTcVal' & HValShape').
  exists stty'. split; [exact HExt |].
  split; [exact HTcHeap' |].
  split; [exact HHeapShape' |].
  split; [exact HTcVal' | exact HValShape'].
Qed.

Theorem pairpar_checked_initial_kdone_steps_safety :
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
      PairParNotStuck state'.
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    ty1 ty2 eff1 eff2 trace state'
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HSteps.
  eapply
    (pairpar_checked_initial_steps_safety
      HDec heap env rho ef1 ea1 ef2 ea2 KDone stty ctxt rgns
      ty1 ty2 eff1 eff2 (subst_rho rho (Ty_Pair ty1 ty2))
      trace state'); eauto.
  constructor.
Qed.

Theorem pairpar_checked_initial_kdone_terminal_value :
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
      RuntimeValShape stty' (subst_rho rho (Ty_Pair ty1 ty2)) v.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    ty1 ty2 eff1 eff2 trace heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HSteps.
  eapply
    (pairpar_checked_initial_terminal_value
      heap env rho ef1 ea1 ef2 ea2 KDone stty ctxt rgns
      ty1 ty2 eff1 eff2 (subst_rho rho (Ty_Pair ty1 ty2))
      trace heap' v); eauto.
  constructor.
Qed.

Lemma RuntimeValShape_pair_inv :
  forall stty t1 t2 v,
    RuntimeValShape stty (Ty_Pair t1 t2) v ->
    exists v1 v2,
      v = Pair (v1, v2) /\
      RuntimeValShape stty t1 v1 /\
      RuntimeValShape stty t2 v2.
Proof.
  intros stty t1 t2 v HShape.
  inversion HShape; subst; try discriminate; try discriminate_subst_rho_shape.
  repeat eexists; eauto.
Qed.

Lemma TcVal_pair_value_inv :
  forall stty t1 t2 v1 v2,
    TcVal (stty, Pair (v1, v2), Ty_Pair t1 t2) ->
    TcVal (stty, v1, t1) /\ TcVal (stty, v2, t2).
Proof.
  intros stty t1 t2 v1 v2 HTcVal.
  inversion HTcVal; subst; try discriminate.
  split; assumption.
Qed.

Theorem pairpar_checked_initial_kdone_terminal_pair :
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
      RuntimeValShape stty' (subst_rho rho ty2) v2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    ty1 ty2 eff1 eff2 trace heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HSteps.
  destruct
    (pairpar_checked_initial_kdone_terminal_value
      heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
      ty1 ty2 eff1 eff2 trace heap' v
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcExp1 HTcExp2 HSteps)
    as (stty' & HExt & HTcHeap' & HHeapShape' & HTcVal' & HValShape').
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
  split; [exact HTcVal2 | exact HValShape2].
Qed.
