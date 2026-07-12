From stdpp Require Import gmap.
From Stdlib Require Import Sets.Ensembles.

Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepTyping.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepReturnProgress.
Require Import theories.Runtime.SmallStepEvalProgress.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.MapFacts.
Require Import theories.Meta.RegionSubstitutionFacts.
Require Import theories.Meta.HeapFacts.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.TypingWeakeningFacts.
Require Import theories.Meta.TypeFacts.
Require Import theories.Meta.LocallyNameless.


Require Export theories.Runtime.SmallStepRuntimeHeapShape.
Require Export theories.Runtime.SmallStepRuntimeKontTyping.

Inductive WTStateRuntimeKontShape : State -> Tau -> Prop :=
| WTSRKS_Eval :
    forall heap env rho e k stty ctxt rgns t eff tout,
      TcHeap (heap, stty) ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e, t, eff) ->
      WTKontRuntime stty (subst_rho rho t) tout k ->
      WTStateRuntimeKontShape (StEval heap env rho e k) tout
| WTSRKS_Return :
    forall heap v k stty t tout,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      WTKontRuntime stty t tout k ->
      RuntimeValShape stty t v ->
      WTStateRuntimeKontShape (StReturn heap v k) tout
| WTSRKS_Done :
    forall heap v stty t,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      RuntimeValShape stty t v ->
      WTStateRuntimeKontShape (StDone heap v) t.

Inductive WTStateRuntimeHeapShape : State -> Tau -> Prop :=
| WTSRHS_Eval :
    forall heap env rho e k stty ctxt rgns t eff tout,
      TcHeap (heap, stty) ->
      RuntimeHeapShape heap stty ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e, t, eff) ->
      WTKontRuntime stty (subst_rho rho t) tout k ->
      WTStateRuntimeHeapShape (StEval heap env rho e k) tout
| WTSRHS_Return :
    forall heap v k stty t tout,
      TcHeap (heap, stty) ->
      RuntimeHeapShape heap stty ->
      TcVal (stty, v, t) ->
      WTKontRuntime stty t tout k ->
      RuntimeValShape stty t v ->
      WTStateRuntimeHeapShape (StReturn heap v k) tout
| WTSRHS_Done :
    forall heap v stty t,
      TcHeap (heap, stty) ->
      RuntimeHeapShape heap stty ->
      TcVal (stty, v, t) ->
      RuntimeValShape stty t v ->
      WTStateRuntimeHeapShape (StDone heap v) t.

Lemma WTStateRuntimeHeapShape_forget :
  forall state t,
    WTStateRuntimeHeapShape state t ->
    WTStateRuntimeKontShape state t.
Proof.
  intros state t HState.
  inversion HState; subst; econstructor; eauto.
Qed.

Lemma WTStateRuntimeKontShape_initial :
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    WTStateRuntimeKontShape
      (initial_state heap env rho e)
      (subst_rho rho t).
Proof.
  intros.
  unfold initial_state.
  econstructor; eauto.
  constructor.
Qed.

Lemma WTStateRuntimeHeapShape_initial :
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    WTStateRuntimeHeapShape
      (initial_state heap env rho e)
      (subst_rho rho t).
Proof.
  intros.
  unfold initial_state.
  econstructor; eauto.
  constructor.
Qed.
