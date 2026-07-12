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

Lemma WTStateRuntimeHeapShape_cond_true_preservation :
  forall heap env rho et ef k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Bit true) (KCond et ef env rho k)) tout ->
    Step (StReturn heap (Bit true) (KCond et ef env rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho et ef k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KCond _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Eval; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_cond_false_preservation :
  forall heap env rho et ef k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Bit false) (KCond et ef env rho k)) tout ->
    Step (StReturn heap (Bit false) (KCond et ef env rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho et ef k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KCond _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Eval; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_plus_eval_right_preservation :
  forall heap env rho e2 n k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Num n) (KPlusL e2 env rho k)) tout ->
    Step (StReturn heap (Num n) (KPlusL e2 env rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho e2 n k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPlusL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Eval with (t := Ty_Natural); eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_PlusR; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_plus_done_preservation :
  forall heap n1 n2 k tout lbl state',
    WTStateRuntimeHeapShape (StReturn heap (Num n2) (KPlusR n1 k)) tout ->
    Step (StReturn heap (Num n2) (KPlusR n1 k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap n1 n2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPlusR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Return with (t := Ty_Natural); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShape_minus_eval_right_preservation :
  forall heap env rho e2 n k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Num n) (KMinusL e2 env rho k)) tout ->
    Step (StReturn heap (Num n) (KMinusL e2 env rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho e2 n k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KMinusL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Eval with (t := Ty_Natural); eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_MinusR; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_minus_done_preservation :
  forall heap n1 n2 k tout lbl state',
    WTStateRuntimeHeapShape (StReturn heap (Num n2) (KMinusR n1 k)) tout ->
    Step (StReturn heap (Num n2) (KMinusR n1 k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap n1 n2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KMinusR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Return with (t := Ty_Natural); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShape_times_eval_right_preservation :
  forall heap env rho e2 n k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Num n) (KTimesL e2 env rho k)) tout ->
    Step (StReturn heap (Num n) (KTimesL e2 env rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho e2 n k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KTimesL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Eval with (t := Ty_Natural); eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_TimesR; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_times_done_preservation :
  forall heap n1 n2 k tout lbl state',
    WTStateRuntimeHeapShape (StReturn heap (Num n2) (KTimesR n1 k)) tout ->
    Step (StReturn heap (Num n2) (KTimesR n1 k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap n1 n2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KTimesR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Return with (t := Ty_Natural); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShape_eq_eval_right_preservation :
  forall heap env rho e2 n k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Num n) (KEqL e2 env rho k)) tout ->
    Step (StReturn heap (Num n) (KEqL e2 env rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho e2 n k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KEqL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Eval with (t := Ty_Natural); eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_EqR; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_eq_done_preservation :
  forall heap n1 n2 k tout lbl state',
    WTStateRuntimeHeapShape (StReturn heap (Num n2) (KEqR n1 k)) tout ->
    Step (StReturn heap (Num n2) (KEqR n1 k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap n1 n2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KEqR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Return with (t := Ty_Boolean); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShape_read_conc_done_preservation :
  forall heap r l k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Loc (Rgn_Const true false r) l) (KReadConc k)) tout ->
    Step (StReturn heap (Loc (Rgn_Const true false r) l) (KReadConc k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap r l k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KReadConc _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShape_write_conc_done_preservation :
  forall heap r l k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Loc (Rgn_Const true false r) l) (KWriteConc k)) tout ->
    Step (StReturn heap (Loc (Rgn_Const true false r) l) (KWriteConc k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap r l k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KWriteConc _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShape_concat_eval_right_preservation :
  forall heap env rho e2 theta k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Eff theta) (KConcatL e2 env rho k)) tout ->
    Step (StReturn heap (Eff theta) (KConcatL e2 env rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho e2 theta k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KConcatL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Eval with (t := Ty_Effect); eauto.
  rewrite (subst_rho_effect rho).
  eapply WTKR_ConcatR; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_concat_done_preservation :
  forall heap theta1 theta2 k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Eff theta2) (KConcatR theta1 k)) tout ->
    Step (StReturn heap (Eff theta2) (KConcatR theta1 k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap theta1 theta2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KConcatR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.


Lemma WTStateRuntimeHeapShape_assign_eval_val_preservation :
  forall heap env rho w ev l k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Loc w l) (KAssignLoc w ev env rho k)) tout ->
    Step (StReturn heap (Loc w l) (KAssignLoc w ev env rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho w ev l k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KAssignLoc _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HTcVal : TcVal (_, Loc _ _, _) |- _ =>
      inversion HTcVal; subst
  end.
  match goal with
  | HRefEq :
      Ty_Ref (Rgn_Const true true _) _ =
      subst_rho _ (Ty_Ref (Rgn_Const true true _) _) |- _ =>
      rewrite subst_rho_ref_const in HRefEq;
      inversion HRefEq; subst
  end.
  eapply WTSRHS_Eval; eauto.
  eapply WTKR_AssignVal with (r := s); eauto.
Qed.
