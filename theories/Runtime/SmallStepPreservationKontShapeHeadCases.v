From stdpp Require Import gmap.
From Stdlib Require Import Sets.Ensembles.

Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepTyping.
Require Import theories.Runtime.SmallStepProgressBase.
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

Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepPreservationHeapShapeCases.

Lemma WTStateRuntimeKontShape_const_step_preservation :
  forall heap env rho n k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (Const n) k) tout ->
    Step (StEval heap env rho (Const n) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho n k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Const _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontRuntime stty (subst_rho rho Ty_Natural) tout k |- _ =>
      rewrite (subst_rho_natural rho) in HKont
  end.
  eapply WTSRKS_Return with (t := Ty_Natural); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_bool_step_preservation :
  forall heap env rho b k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (Bool b) k) tout ->
    Step (StEval heap env rho (Bool b) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho b k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Bool _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontRuntime stty (subst_rho rho Ty_Boolean) tout k |- _ =>
      rewrite (subst_rho_boolean rho) in HKont
  end.
  eapply WTSRKS_Return with (t := Ty_Boolean); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_var_step_preservation :
  forall heap env rho x k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (Var x) k) tout ->
    Step (StEval heap env rho (Var x) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
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
    HKont : WTKontRuntime stty (subst_rho rho ?ty) tout k |- _ =>
      assert (HTcVal : TcVal (stty, v, subst_rho rho ty)) by
        (inversion HTcEnv as [? ? ? ? _ _ HValEnv]; subst;
         eapply HValEnv; eauto);
      assert (HShape : RuntimeValShape stty (subst_rho rho ty) v) by
        (eapply RuntimeEnvShape_find; eauto);
      eapply WTSRKS_Return with (t := subst_rho rho ty); eauto
  end.
Qed.

Lemma WTStateRuntimeKontShape_mu_step_preservation :
  forall heap env rho f x ec ee k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (Mu f x ec ee) k) tout ->
    Step (StEval heap env rho (Mu f x ec ee) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
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
      eapply WTSRKS_Return
        with (t := subst_rho rho
          (Ty_Arrow tyx effc tyc effe Ty_Effect)); eauto;
      econstructor; eauto
  end.
Qed.

Lemma WTStateRuntimeKontShape_lambda_step_preservation :
  forall heap env rho x eb k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (Lambda x eb) k) tout ->
    Step (StEval heap env rho (Lambda x eb) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
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
      eapply WTSRKS_Return
        with (t := subst_rho rho (Ty_ForallRgn effr tyr)); eauto;
      econstructor; eauto
  end.
Qed.

Lemma WTStateRuntimeKontShape_alloc_abs_step_preservation :
  forall heap env rho w k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (AllocAbs w) k) tout ->
    Step (StEval heap env rho (AllocAbs w) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho w k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, AllocAbs _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontRuntime stty (subst_rho rho Ty_Effect) tout k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  eapply WTSRKS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_read_abs_step_preservation :
  forall heap env rho w k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (ReadAbs w) k) tout ->
    Step (StEval heap env rho (ReadAbs w) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho w k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, ReadAbs _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontRuntime stty (subst_rho rho Ty_Effect) tout k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  eapply WTSRKS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_write_abs_step_preservation :
  forall heap env rho w k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (WriteAbs w) k) tout ->
    Step (StEval heap env rho (WriteAbs w) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho w k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, WriteAbs _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontRuntime stty (subst_rho rho Ty_Effect) tout k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  eapply WTSRKS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_top_step_preservation :
  forall heap env rho k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho Top k) tout ->
    Step (StEval heap env rho Top k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Top, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontRuntime stty (subst_rho rho Ty_Effect) tout k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  eapply WTSRKS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_empty_step_preservation :
  forall heap env rho k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho Empty k) tout ->
    Step (StEval heap env rho Empty k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Empty, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontRuntime stty (subst_rho rho Ty_Effect) tout k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  eapply WTSRKS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_done_step_preservation :
  forall heap v tout lbl state',
    WTStateRuntimeKontShape (StReturn heap v KDone) tout ->
    Step (StReturn heap v KDone) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap v tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ KDone |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Done; eauto.
Qed.
