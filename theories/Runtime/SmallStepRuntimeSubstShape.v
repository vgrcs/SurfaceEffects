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


Inductive WTStateRuntimeSubstShape : State -> Tau -> Prop :=
| WTSRSS_Eval :
    forall heap env rho e k stty ctxt rgns t eff tout,
      TcHeap (heap, stty) ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e, t, eff) ->
      WTKontTyped stty (subst_rho rho t) tout k ->
      WTStateRuntimeSubstShape (StEval heap env rho e k) tout
| WTSRSS_Return :
    forall heap v k stty t tout,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      WTKontTyped stty t tout k ->
      RuntimeValShape stty t v ->
      WTStateRuntimeSubstShape (StReturn heap v k) tout
| WTSRSS_Done :
    forall heap v stty t,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      RuntimeValShape stty t v ->
      WTStateRuntimeSubstShape (StDone heap v) t.

Lemma WTStateRuntimeSubstShape_forget :
  forall state t,
    WTStateRuntimeSubstShape state t ->
    WTState state.
Proof.
  intros state t HState.
  inversion HState; subst.
  - econstructor; eauto.
    eapply WTKontTyped_forget; eauto.
  - econstructor; eauto.
    eapply WTKontTyped_forget; eauto.
  - econstructor; eauto.
Qed.

Lemma WTStateRuntimeSubstShape_initial :
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    WTStateRuntimeSubstShape
      (initial_state heap env rho e)
      (subst_rho rho t).
Proof.
  intros.
  unfold initial_state.
  econstructor; eauto.
  constructor.
Qed.

Lemma WTStateRuntimeSubstShape_eval_sequential_head_progress :
  forall heap env rho e k tout,
    WTStateRuntimeSubstShape (StEval heap env rho e k) tout ->
    SequentialHead e ->
    EvalHeadRegionsResolved rho e ->
    CanStep (StEval heap env rho e k).
Proof.
  intros heap env rho e k tout HState HSequential HResolved.
  inversion HState; subst.
  eapply typed_eval_sequential_head_progress_unindexed; eauto.
Qed.

Lemma WTStateRuntimeSubstShape_return_progress :
  forall heap v k tout,
    WTStateRuntimeSubstShape (StReturn heap v k) tout ->
    CanStep (StReturn heap v k).
Proof.
  intros heap v k tout HState.
  inversion HState; subst.
  eapply typed_return_runtime_shape_progress; eauto.
Qed.

Lemma WTStateRuntimeSubstShape_not_stuck :
  forall state tout,
    WTStateRuntimeSubstShape state tout ->
    (forall heap env rho e k,
        state = StEval heap env rho e k ->
        SequentialHead e /\ EvalHeadRegionsResolved rho e) ->
    NotStuck state.
Proof.
  intros state tout HState HEvalReady.
  destruct HState.
  - right.
    destruct (HEvalReady heap env rho e k eq_refl) as [HSeq HResolved].
    eapply typed_eval_sequential_head_progress_unindexed; eauto.
  - right.
    eapply typed_return_runtime_shape_progress; eauto.
  - left. constructor.
Qed.

Lemma WTStateRuntimeSubstShape_const_step_preservation :
  forall heap env rho n k tout lbl state',
    WTStateRuntimeSubstShape (StEval heap env rho (Const n) k) tout ->
    Step (StEval heap env rho (Const n) k) lbl state' ->
    WTStateRuntimeSubstShape state' tout.
Proof.
  intros heap env rho n k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Const _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontTyped _ (subst_rho ?rho0 Ty_Natural) _ _ |- _ =>
      rewrite (subst_rho_natural rho0) in HKont
  end.
  eapply WTSRSS_Return with (t := Ty_Natural); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeSubstShape_bool_step_preservation :
  forall heap env rho b k tout lbl state',
    WTStateRuntimeSubstShape (StEval heap env rho (Bool b) k) tout ->
    Step (StEval heap env rho (Bool b) k) lbl state' ->
    WTStateRuntimeSubstShape state' tout.
Proof.
  intros heap env rho b k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Bool _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontTyped _ (subst_rho ?rho0 Ty_Boolean) _ _ |- _ =>
      rewrite (subst_rho_boolean rho0) in HKont
  end.
  eapply WTSRSS_Return with (t := Ty_Boolean); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeSubstShape_mu_step_preservation :
  forall heap env rho f x ec ee k tout lbl state',
    WTStateRuntimeSubstShape (StEval heap env rho (Mu f x ec ee) k) tout ->
    Step (StEval heap env rho (Mu f x ec ee) k) lbl state' ->
    WTStateRuntimeSubstShape state' tout.
Proof.
  intros heap env rho f x ec ee k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Mu _ _ _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HTcExp : TcExp
      (ctxt, rgns, Mu f x ec ee,
        Ty_Arrow ?tyx ?effc ?tyc ?effe Ty_Effect, Empty_Static_Action) |- _ =>
      eapply WTSRSS_Return
        with (t := subst_rho rho
          (Ty_Arrow tyx effc tyc effe Ty_Effect)); eauto;
      econstructor; eauto
  end.
Qed.

Lemma WTStateRuntimeSubstShape_lambda_step_preservation :
  forall heap env rho x eb k tout lbl state',
    WTStateRuntimeSubstShape (StEval heap env rho (Lambda x eb) k) tout ->
    Step (StEval heap env rho (Lambda x eb) k) lbl state' ->
    WTStateRuntimeSubstShape state' tout.
Proof.
  intros heap env rho x eb k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Lambda _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HTcExp : TcExp
      (ctxt, rgns, Lambda x eb, Ty_ForallRgn ?effr ?tyr,
        Empty_Static_Action) |- _ =>
      eapply WTSRSS_Return
        with (t := subst_rho rho (Ty_ForallRgn effr tyr)); eauto;
      econstructor; eauto
  end.
Qed.

Lemma WTStateRuntimeSubstShape_var_step_preservation :
  forall heap env rho x k tout lbl state',
    WTStateRuntimeSubstShape (StEval heap env rho (Var x) k) tout ->
    Step (StEval heap env rho (Var x) k) lbl state' ->
    WTStateRuntimeSubstShape state' tout.
Proof.
  intros heap env rho x k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Var _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HTcEnv : TcEnv (stty, rho, env, ctxt),
    HEnvShape : RuntimeEnvShape stty rho env ctxt,
    HFindE : find_E x env = Some v,
    HFindT : find_T x ctxt = Some ?ty,
    HKont : WTKontTyped stty (subst_rho rho ?ty) tout k |- _ =>
      assert (HTcVal : TcVal (stty, v, subst_rho rho ty)) by
        (inversion HTcEnv as [? ? ? ? _ _ HValEnv]; subst;
         eapply HValEnv; eauto);
      assert (HShape : RuntimeValShape stty (subst_rho rho ty) v) by
        (eapply RuntimeEnvShape_find; eauto);
      eapply WTSRSS_Return with (t := subst_rho rho ty); eauto
  end.
Qed.

Lemma subst_rho_arrow_arg_eq :
  forall rho1 rho2 tya1 effc1 tyc1 effe1 tya2 effc2 tyc2 effe2,
    subst_rho rho1 (Ty_Arrow tya1 effc1 tyc1 effe1 Ty_Effect) =
      subst_rho rho2 (Ty_Arrow tya2 effc2 tyc2 effe2 Ty_Effect) ->
    subst_rho rho1 tya1 = subst_rho rho2 tya2.
Proof.
  intros rho1 rho2 tya1 effc1 tyc1 effe1 tya2 effc2 tyc2 effe2 H.
  rewrite !subst_rho_arrow in H.
  inversion H.
  reflexivity.
Qed.

Lemma subst_rho_arrow_result_eq :
  forall rho1 rho2 tya1 effc1 tyc1 effe1 tya2 effc2 tyc2 effe2,
    subst_rho rho1 (Ty_Arrow tya1 effc1 tyc1 effe1 Ty_Effect) =
      subst_rho rho2 (Ty_Arrow tya2 effc2 tyc2 effe2 Ty_Effect) ->
    subst_rho rho1 tyc1 = subst_rho rho2 tyc2.
Proof.
  intros rho1 rho2 tya1 effc1 tyc1 effe1 tya2 effc2 tyc2 effe2 H.
  rewrite !subst_rho_arrow in H.
  inversion H.
  reflexivity.
Qed.

Lemma subst_rho_forall_body_eq :
  forall rho1 rho2 eff1 tyr1 eff2 tyr2,
    subst_rho rho1 (Ty_ForallRgn eff1 tyr1) =
      subst_rho rho2 (Ty_ForallRgn eff2 tyr2) ->
    subst_rho rho1 tyr1 = subst_rho rho2 tyr2.
Proof.
  intros rho1 rho2 eff1 tyr1 eff2 tyr2 H.
  rewrite !subst_rho_forallrgn in H.
  inversion H.
  reflexivity.
Qed.

Lemma subst_rho_ref_const :
  forall rho s t,
    subst_rho rho (Ty_Ref (Rgn_Const true true s) t) =
      Ty_Ref (Rgn_Const true true s) (subst_rho rho t).
Proof.
  intros rho s t.
  rewrite subst_rho_tyref.
  now rewrite subst_rho_rgn_const.
Qed.

