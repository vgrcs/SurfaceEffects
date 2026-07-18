From stdpp Require Import gmap.
From Stdlib Require Import Ascii.
From Stdlib Require Import Program.Equality.

Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepTyping.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.DynamicActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.MapFacts.
Require Import theories.Meta.RegionSubstitutionFacts.
Require Import theories.Meta.TypingWeakeningFacts.

Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepReturnProgress.
Require Import theories.Runtime.SmallStepEvalProgress.

Inductive WTStateRuntimeShape : State -> Tau -> Prop :=
| WTSRS_Eval :
    forall heap env rho e k stty ctxt rgns t eff tout,
      TcHeap (heap, stty) ->
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e, t, eff) ->
      WTKontTyped stty t tout k ->
      WTStateRuntimeShape (StEval heap env rho e k) tout
| WTSRS_Return :
    forall heap v k stty t tout,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      WTKontTyped stty t tout k ->
      RuntimeValShape stty t v ->
      WTStateRuntimeShape (StReturn heap v k) tout
| WTSRS_Done :
    forall heap v stty t,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      RuntimeValShape stty t v ->
      WTStateRuntimeShape (StDone heap v) t.

Lemma WTStateRuntimeShape_forget :
  forall state t,
    WTStateRuntimeShape state t ->
    WTStateTyped state t.
Proof.
  intros state t HState.
  inversion HState; subst; econstructor; eauto.
Qed.

Lemma WTStateRuntimeShape_initial :
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    TcRho (rho, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns, e, t, eff) ->
    WTStateRuntimeShape (initial_state heap env rho e) t.
Proof.
  intros.
  unfold initial_state.
  econstructor; eauto.
  constructor.
Qed.

Lemma WTStateRuntimeShape_return_progress :
  forall heap v k tout,
    WTStateRuntimeShape (StReturn heap v k) tout ->
    CanStep (StReturn heap v k).
Proof.
  intros heap v k tout HState.
  inversion HState; subst.
  eapply typed_return_runtime_shape_progress; eauto.
Qed.

Lemma WTStateRuntimeShape_eval_sequential_head_progress :
  forall heap env rho e k tout,
    WTStateRuntimeShape (StEval heap env rho e k) tout ->
    SequentialHead e ->
    EvalHeadRegionsResolved rho e ->
    CanStep (StEval heap env rho e k).
Proof.
  intros heap env rho e k tout HState HSequential HResolved.
  inversion HState; subst.
  eapply typed_eval_sequential_head_progress; eauto.
Qed.

Lemma WTStateRuntimeShape_not_stuck :
  forall state tout,
    WTStateRuntimeShape state tout ->
    (forall heap env rho e k,
        state = StEval heap env rho e k ->
        SequentialHead e /\ EvalHeadRegionsResolved rho e) ->
    NotStuck state.
Proof.
  intros state tout HState HEvalReady.
  destruct HState.
  - right. left.
    destruct (HEvalReady heap env rho e k eq_refl) as [HSeq HResolved].
    eapply typed_eval_sequential_head_progress; eauto.
  - right. left.
    eapply typed_return_runtime_shape_progress; eauto.
  - left. constructor.
Qed.

Inductive WTStateRuntimeEnvShape : State -> Tau -> Prop :=
| WTSRES_Eval :
    forall heap env rho e k stty ctxt rgns t eff tout,
      TcHeap (heap, stty) ->
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e, t, eff) ->
      WTKontTyped stty t tout k ->
      WTStateRuntimeEnvShape (StEval heap env rho e k) tout
| WTSRES_Return :
    forall heap v k stty t tout,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      WTKontTyped stty t tout k ->
      RuntimeValShape stty t v ->
      WTStateRuntimeEnvShape (StReturn heap v k) tout
| WTSRES_Done :
    forall heap v stty t,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      RuntimeValShape stty t v ->
      WTStateRuntimeEnvShape (StDone heap v) t.

Lemma WTStateRuntimeEnvShape_forget :
  forall state t,
    WTStateRuntimeEnvShape state t ->
    WTStateRuntimeShape state t.
Proof.
  intros state t HState.
  inversion HState; subst; econstructor; eauto.
Qed.

Lemma WTStateRuntimeEnvShape_initial :
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    TcRho (rho, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    WTStateRuntimeEnvShape (initial_state heap env rho e) t.
Proof.
  intros.
  unfold initial_state.
  econstructor; eauto.
  constructor.
Qed.

Lemma WTStateRuntimeEnvShape_var_value :
  forall heap env rho x k tout,
    WTStateRuntimeEnvShape (StEval heap env rho (Var x) k) tout ->
    exists stty value t,
      find_E x env = Some value /\
      RuntimeValShape stty (subst_rho rho t) value.
Proof.
  intros heap env rho x k tout HState.
  inversion HState; subst.
  inversion H9; subst.
  match goal with
  | HEnvShape : RuntimeEnvShape ?stty rho env ?ctxt,
    HTcEnv : TcEnv (?stty, rho, env, ?ctxt),
    HTcExp : TcExp (?ctxt, ?rgns, Var x, ?t, Empty_Static_Action) |- _ =>
      destruct (RuntimeEnvShape_var_value stty rho env ctxt rgns x t
        HTcEnv HEnvShape HTcExp) as [value [HFindE HShape]];
      exists stty, value, t;
      split; assumption
  end.
Qed.

Lemma WTStateRuntimeEnvShape_not_stuck :
  forall state tout,
    WTStateRuntimeEnvShape state tout ->
    (forall heap env rho e k,
        state = StEval heap env rho e k ->
        SequentialHead e /\ EvalHeadRegionsResolved rho e) ->
    NotStuck state.
Proof.
  intros state tout HState HEvalReady.
  eapply WTStateRuntimeShape_not_stuck; eauto.
  eapply WTStateRuntimeEnvShape_forget; eauto.
Qed.
