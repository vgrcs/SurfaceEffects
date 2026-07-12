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

Lemma WTStateRuntimeHeapShapeAt_const_step_preservation :
  forall heap env rho n k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (Const n) k) tout stty ->
    Step (StEval heap env rho (Const n) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho n k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Return with (t := Ty_Natural); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShapeAt_bool_step_preservation :
  forall heap env rho b k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (Bool b) k) tout stty ->
    Step (StEval heap env rho (Bool b) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho b k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Return with (t := Ty_Boolean); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShapeAt_var_step_preservation :
  forall heap env rho x k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (Var x) k) tout stty ->
    Step (StEval heap env rho (Var x) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho x k tout stty lbl state' HState HStep.
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
      eapply WTStateRuntimeHeapShapeAt_pack_same_store_step;
      eapply WTSRHSA_Return with (t := subst_rho rho ty); eauto
  end.
Qed.

Lemma WTStateRuntimeHeapShapeAt_mu_step_preservation :
  forall heap env rho f x ec ee k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (Mu f x ec ee) k) tout stty ->
    Step (StEval heap env rho (Mu f x ec ee) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho f x ec ee k tout stty lbl state' HState HStep.
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
      eapply WTStateRuntimeHeapShapeAt_pack_same_store_step;
      eapply WTSRHSA_Return
        with (t := subst_rho rho
          (Ty_Arrow tyx effc tyc effe Ty_Effect)); eauto;
      econstructor; eauto
  end.
Qed.

Lemma WTStateRuntimeHeapShapeAt_lambda_step_preservation :
  forall heap env rho x eb k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (Lambda x eb) k) tout stty ->
    Step (StEval heap env rho (Lambda x eb) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho x eb k tout stty lbl state' HState HStep.
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
      eapply WTStateRuntimeHeapShapeAt_pack_same_store_step;
      eapply WTSRHSA_Return
        with (t := subst_rho rho (Ty_ForallRgn effr tyr)); eauto;
      econstructor; eauto
  end.
Qed.

Lemma WTStateRuntimeHeapShapeAt_alloc_abs_step_preservation :
  forall heap env rho w k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (AllocAbs w) k) tout stty ->
    Step (StEval heap env rho (AllocAbs w) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho w k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShapeAt_read_abs_step_preservation :
  forall heap env rho w k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (ReadAbs w) k) tout stty ->
    Step (StEval heap env rho (ReadAbs w) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho w k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShapeAt_write_abs_step_preservation :
  forall heap env rho w k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (WriteAbs w) k) tout stty ->
    Step (StEval heap env rho (WriteAbs w) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho w k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShapeAt_top_step_preservation :
  forall heap env rho k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho Top k) tout stty ->
    Step (StEval heap env rho Top k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShapeAt_empty_step_preservation :
  forall heap env rho k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho Empty k) tout stty ->
    Step (StEval heap env rho Empty k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShapeAt_plus_done_step_preservation :
  forall heap n1 n2 k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StReturn heap (Num n2) (KPlusR n1 k)) tout stty ->
    Step (StReturn heap (Num n2) (KPlusR n1 k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap n1 n2 k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPlusR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Return with (t := Ty_Natural); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShapeAt_minus_done_step_preservation :
  forall heap n1 n2 k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StReturn heap (Num n2) (KMinusR n1 k)) tout stty ->
    Step (StReturn heap (Num n2) (KMinusR n1 k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap n1 n2 k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KMinusR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Return with (t := Ty_Natural); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShapeAt_times_done_step_preservation :
  forall heap n1 n2 k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StReturn heap (Num n2) (KTimesR n1 k)) tout stty ->
    Step (StReturn heap (Num n2) (KTimesR n1 k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap n1 n2 k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KTimesR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Return with (t := Ty_Natural); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShapeAt_eq_done_step_preservation :
  forall heap n1 n2 k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StReturn heap (Num n2) (KEqR n1 k)) tout stty ->
    Step (StReturn heap (Num n2) (KEqR n1 k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap n1 n2 k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KEqR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Return with (t := Ty_Boolean); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShapeAt_read_conc_done_step_preservation :
  forall heap r l k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Loc (Rgn_Const true false r) l) (KReadConc k))
      tout stty ->
    Step
      (StReturn heap (Loc (Rgn_Const true false r) l) (KReadConc k))
      lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap r l k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KReadConc _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShapeAt_write_conc_done_step_preservation :
  forall heap r l k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Loc (Rgn_Const true false r) l) (KWriteConc k))
      tout stty ->
    Step
      (StReturn heap (Loc (Rgn_Const true false r) l) (KWriteConc k))
      lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap r l k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KWriteConc _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShapeAt_concat_done_step_preservation :
  forall heap theta1 theta2 k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Eff theta2) (KConcatR theta1 k)) tout stty ->
    Step (StReturn heap (Eff theta2) (KConcatR theta1 k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap theta1 theta2 k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KConcatR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.
