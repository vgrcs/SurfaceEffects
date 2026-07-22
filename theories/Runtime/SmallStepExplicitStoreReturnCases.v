From stdpp Require Import gmap.
From Stdlib Require Import Program.Equality.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
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
Require Import theories.Meta.TypeFacts.
Require Import theories.Meta.TypingWeakeningFacts.
Require Import theories.Runtime.SmallStepExplicitStoreBase.
Require Import theories.Runtime.SmallStepExplicitStoreHeap.

Lemma WTStateRuntimeHeapShapeAt_cond_true_step_preservation :
  forall heap env rho et ef k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Bit true) (KCond et ef env rho k)) tout stty ->
    Step (StReturn heap (Bit true) (KCond et ef env rho k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho et ef k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KCond _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_cond_false_step_preservation :
  forall heap env rho et ef k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Bit false) (KCond et ef env rho k)) tout stty ->
    Step (StReturn heap (Bit false) (KCond et ef env rho k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho et ef k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KCond _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_plus_eval_right_step_preservation :
  forall heap env rho e2 n k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Num n) (KPlusL e2 env rho k)) tout stty ->
    Step (StReturn heap (Num n) (KPlusL e2 env rho k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho e2 n k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPlusL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval with (t := Ty_Natural); eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_PlusR; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_minus_eval_right_step_preservation :
  forall heap env rho e2 n k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Num n) (KMinusL e2 env rho k)) tout stty ->
    Step (StReturn heap (Num n) (KMinusL e2 env rho k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho e2 n k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KMinusL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval with (t := Ty_Natural); eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_MinusR; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_times_eval_right_step_preservation :
  forall heap env rho e2 n k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Num n) (KTimesL e2 env rho k)) tout stty ->
    Step (StReturn heap (Num n) (KTimesL e2 env rho k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho e2 n k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KTimesL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval with (t := Ty_Natural); eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_TimesR; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_eq_eval_right_step_preservation :
  forall heap env rho e2 n k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Num n) (KEqL e2 env rho k)) tout stty ->
    Step (StReturn heap (Num n) (KEqL e2 env rho k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho e2 n k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KEqL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval with (t := Ty_Natural); eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_EqR; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_concat_eval_right_step_preservation :
  forall heap env rho e2 theta k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Eff theta) (KConcatL e2 env rho k)) tout stty ->
    Step (StReturn heap (Eff theta) (KConcatL e2 env rho k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho e2 theta k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KConcatL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval with (t := Ty_Effect); eauto.
  rewrite (subst_rho_effect rho).
  eapply WTKR_ConcatR; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_assign_eval_val_step_preservation :
  forall heap env rho w ev l k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Loc w l) (KAssignLoc w ev env rho k)) tout stty ->
    Step (StReturn heap (Loc w l) (KAssignLoc w ev env rho k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho w ev l k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval; eauto.
  eapply WTKR_AssignVal with (r := s); eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_pairpar_eval_eff1_step_preservation :
  forall heap env rho ef1 ea1 ef2 ea2 k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k) tout stty ->
    Step (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Pair_Par _ _ _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HEff1 : TcExp (_, _, Eff_App ef1 ea1, _, _) |- _ =>
      inversion HEff1; subst
  end.
  match goal with
  | HEff2 : TcExp (_, _, Eff_App ef2 ea2, _, _) |- _ =>
      inversion HEff2; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval with (t := Ty_Effect); eauto.
  rewrite (subst_rho_effect rho).
  eapply WTKR_PairParEff1; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_pairpar_eval_eff2_step_preservation :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Eff theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)) tout stty ->
    Step
      (StReturn heap (Eff theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 k tout stty lbl state'
    HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPairParEff1 _ _ _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval with (t := Ty_Effect); eauto.
  rewrite (subst_rho_effect rho).
  eapply WTKR_PairParEff2; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_pairpar_eval_mu1_step_preservation :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Eff theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)) tout stty ->
    Step
      (StReturn heap (Eff theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k tout stty lbl state'
    HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
	  match goal with
	  | HKont : WTKontRuntime _ _ _ (KPairParEff2 _ _ _ _ _ _ _ _) |- _ =>
	      inversion HKont; subst
	  end.
	  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
	  eapply WTSRHSA_PairParRun
	    with (tleft := subst_rho rho ty1) (tright := subst_rho rho ty2).
	  - unfold initial_state.
	    eapply WTSRHSA_Eval with (t := ty1) (eff := eff1); eauto.
	    constructor.
	  - unfold initial_state.
	    eapply WTSRHSA_Eval with (t := ty2) (eff := eff2); eauto.
	    constructor.
	  - rewrite subst_rho_pair in H23.
	    exact H23.
Qed.

Lemma WTStateRuntimeHeapShapeAt_pairpar_eval_mu2_step_preservation :
  forall heap env rho ef2 ea2 v1 k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap v1 (KPairParMu1 ef2 ea2 env rho k)) tout stty ->
    Step (StReturn heap v1 (KPairParMu1 ef2 ea2 env rho k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho ef2 ea2 v1 k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPairParMu1 _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval; eauto.
  eapply WTKR_PairParMu2; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_pairpar_done_step_preservation :
  forall heap v1 v2 k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap v2 (KPairParMu2 v1 k)) tout stty ->
    Step (StReturn heap v2 (KPairParMu2 v1 k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap v1 v2 k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPairParMu2 _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Return with (t := subst_rho rho (Ty_Pair ty1 ty2)); eauto.
  - rewrite subst_rho_pair.
    constructor; eauto.
  - rewrite subst_rho_pair.
    constructor; eauto.
Qed.
