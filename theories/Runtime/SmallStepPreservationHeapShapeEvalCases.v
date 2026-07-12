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

Lemma WTStateRuntimeHeapShape_mu_app_eval_fun_preservation :
  forall heap env rho ef ea k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (Mu_App ef ea) k) tout ->
    Step (StEval heap env rho (Mu_App ef ea) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho ef ea k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Mu_App _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HFun : TcExp (ctxt, rgns, ef,
        Ty_Arrow ?tya ?effc ?tyc ?effe Ty_Effect, ?efff),
    HArg : TcExp (ctxt, rgns, ea, ?tya, ?effa),
    HKont : WTKontRuntime stty (subst_rho rho ?tyc) tout k |- _ =>
      eapply WTSRHS_Eval
        with
          (stty := stty) (ctxt := ctxt) (rgns := rgns)
          (t := Ty_Arrow tya effc tyc effe Ty_Effect) (eff := efff);
      eauto;
      eapply WTKR_MuAppFun; eauto
  end.
Qed.

Lemma WTStateRuntimeHeapShape_rgn_app_eval_fun_preservation :
  forall heap env rho er w k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (Rgn_App er w) k) tout ->
    Step (StEval heap env rho (Rgn_App er w) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho er w k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Rgn_App _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HFun : TcExp (ctxt, rgns, er, Ty_ForallRgn ?effr ?tyr, ?efff),
    HKont : WTKontRuntime stty
      (subst_rho rho (open (mk_rgn_type w) ?tyr)) tout k |- _ =>
      eapply WTSRHS_Eval
        with
          (stty := stty) (ctxt := ctxt) (rgns := rgns)
          (t := Ty_ForallRgn effr tyr) (eff := efff);
      eauto;
      eapply WTKR_RgnApp; eauto
  end.
Qed.

Lemma WTStateRuntimeHeapShape_eff_app_eval_fun_preservation :
  forall heap env rho ef ea k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (Eff_App ef ea) k) tout ->
    Step (StEval heap env rho (Eff_App ef ea) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho ef ea k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Eff_App _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontRuntime stty (subst_rho rho Ty_Effect) tout k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  match goal with
  | HFun : TcExp (ctxt, rgns, ef,
        Ty_Arrow ?tya ?effc ?tyc ?effe Ty_Effect, ?efff),
    HArg : TcExp (ctxt, rgns, ea, ?tya, ?effa),
    HKont : WTKontRuntime stty Ty_Effect tout k |- _ =>
      eapply WTSRHS_Eval
        with
          (stty := stty) (ctxt := ctxt) (rgns := rgns)
          (t := Ty_Arrow tya effc tyc effe Ty_Effect) (eff := efff);
      eauto;
      eapply WTKR_EffAppFun; eauto
  end.
Qed.

Lemma WTStateRuntimeHeapShape_cond_eval_guard_preservation :
  forall heap env rho e et ef k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (Cond e et ef) k) tout ->
    Step (StEval heap env rho (Cond e et ef) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho e et ef k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Cond _ _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  eapply WTSRHS_Eval
    with
      (stty := stty) (ctxt := ctxt) (rgns := rgns)
      (t := Ty_Boolean);
  eauto.
  rewrite (subst_rho_boolean rho).
  eapply WTKR_Cond; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_ref_eval_arg_preservation :
  forall heap env rho w e k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (Ref w e) k) tout ->
    Step (StEval heap env rho (Ref w e) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho w e k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Ref _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  eapply WTSRHS_Eval with (stty := stty) (ctxt := ctxt) (rgns := rgns);
    eauto.
  eapply WTKR_Ref; eauto; try constructor.
Qed.

Lemma WTStateRuntimeHeapShape_deref_eval_arg_preservation :
  forall heap env rho w e k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (DeRef w e) k) tout ->
    Step (StEval heap env rho (DeRef w e) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho w e k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, DeRef _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  eapply WTSRHS_Eval with (stty := stty) (ctxt := ctxt) (rgns := rgns);
    eauto.
  eapply WTKR_DeRef; eauto; try constructor.
Qed.

Lemma WTStateRuntimeHeapShape_assign_eval_loc_preservation :
  forall heap env rho w ea ev k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (Assign w ea ev) k) tout ->
    Step (StEval heap env rho (Assign w ea ev) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho w ea ev k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Assign _ _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontRuntime stty (subst_rho rho Ty_Unit) tout k |- _ =>
      rewrite (subst_rho_unit rho) in HKont
  end.
  eapply WTSRHS_Eval with (stty := stty) (ctxt := ctxt) (rgns := rgns);
    eauto.
  eapply WTKR_AssignLoc; eauto; try constructor.
Qed.

Lemma WTStateRuntimeHeapShape_plus_eval_left_preservation :
  forall heap env rho e1 e2 k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (Plus e1 e2) k) tout ->
    Step (StEval heap env rho (Plus e1 e2) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho e1 e2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Plus _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontRuntime stty (subst_rho rho Ty_Natural) tout k |- _ =>
      rewrite (subst_rho_natural rho) in HKont
  end.
  eapply WTSRHS_Eval
    with (stty := stty) (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural);
    eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_PlusL; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_minus_eval_left_preservation :
  forall heap env rho e1 e2 k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (Minus e1 e2) k) tout ->
    Step (StEval heap env rho (Minus e1 e2) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho e1 e2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Minus _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontRuntime stty (subst_rho rho Ty_Natural) tout k |- _ =>
      rewrite (subst_rho_natural rho) in HKont
  end.
  eapply WTSRHS_Eval
    with (stty := stty) (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural);
    eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_MinusL; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_times_eval_left_preservation :
  forall heap env rho e1 e2 k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (Times e1 e2) k) tout ->
    Step (StEval heap env rho (Times e1 e2) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho e1 e2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Times _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontRuntime stty (subst_rho rho Ty_Natural) tout k |- _ =>
      rewrite (subst_rho_natural rho) in HKont
  end.
  eapply WTSRHS_Eval
    with (stty := stty) (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural);
    eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_TimesL; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_eq_eval_left_preservation :
  forall heap env rho e1 e2 k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (Eq e1 e2) k) tout ->
    Step (StEval heap env rho (Eq e1 e2) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho e1 e2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Eq _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontRuntime stty (subst_rho rho Ty_Boolean) tout k |- _ =>
      rewrite (subst_rho_boolean rho) in HKont
  end.
  eapply WTSRHS_Eval
    with (stty := stty) (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural);
    eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_EqL; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_read_conc_eval_arg_preservation :
  forall heap env rho e k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (ReadConc e) k) tout ->
    Step (StEval heap env rho (ReadConc e) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho e k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, ReadConc _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontRuntime stty (subst_rho rho Ty_Effect) tout k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  eapply WTSRHS_Eval with (stty := stty) (ctxt := ctxt) (rgns := rgns);
    eauto.
  eapply WTKR_ReadConc; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_write_conc_eval_arg_preservation :
  forall heap env rho e k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (WriteConc e) k) tout ->
    Step (StEval heap env rho (WriteConc e) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho e k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, WriteConc _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontRuntime stty (subst_rho rho Ty_Effect) tout k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  eapply WTSRHS_Eval with (stty := stty) (ctxt := ctxt) (rgns := rgns);
    eauto.
  eapply WTKR_WriteConc; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_concat_eval_left_preservation :
  forall heap env rho e1 e2 k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (Concat e1 e2) k) tout ->
    Step (StEval heap env rho (Concat e1 e2) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho e1 e2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Concat _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontRuntime stty (subst_rho rho Ty_Effect) tout k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  eapply WTSRHS_Eval
    with (stty := stty) (ctxt := ctxt) (rgns := rgns) (t := Ty_Effect);
    eauto.
  rewrite (subst_rho_effect rho).
  eapply WTKR_ConcatL; eauto.
Qed.
