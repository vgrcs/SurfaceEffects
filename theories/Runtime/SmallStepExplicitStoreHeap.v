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

Lemma WTStateRuntimeHeapShapeAt_deref_done_step_preservation :
  forall heap rho w l k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Loc w l) (KDeRef w rho k)) tout stty ->
    Step (StReturn heap (Loc w l) (KDeRef w rho k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap rho w l k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KDeRef _ _ _) |- _ =>
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
  match goal with
  | HFindR : find_R (Rgn_Const true false ?s) rho = Some ?r |- _ =>
      simpl in HFindR; inversion HFindR; subst
  end.
  assert (HTcRead : TcVal (stty, v, subst_rho rho t0)).
  {
    match goal with
    | HTcHeap : TcHeap (heap, stty),
      HFindH : find_H ?key heap = Some v,
      HFindST : find_ST ?key stty = Some (subst_rho rho t0) |- _ =>
        inversion HTcHeap as [? ? _ _ HHeapVal]; subst;
        eapply HHeapVal; eauto
    end.
  }
  assert (HReadShape : RuntimeValShape stty (subst_rho rho t0) v).
  {
    match goal with
    | HHeapShape : RuntimeHeapShape heap stty,
      HFindH : find_H ?key heap = Some v,
      HFindST : find_ST ?key stty = Some (subst_rho rho t0) |- _ =>
        eapply HHeapShape; eauto
    end.
  }
  exists stty. split.
  - eapply WTSRHSA_Return with (t := subst_rho rho t0); eauto.
  - split; [ simpl; assumption | split; [ simpl; assumption | apply StoreExtends_refl ] ].
Qed.

Lemma WTStateRuntimeHeapShapeAt_assign_done_step_preservation :
  forall heap rho w l v k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap v (KAssignVal w l rho k)) tout stty ->
    Step (StReturn heap v (KAssignVal w l rho k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap rho w l v k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KAssignVal _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HFind1 : find_R w rho = Some ?r1,
    HFind2 : find_R w rho = Some ?r2 |- _ =>
      rewrite HFind1 in HFind2;
      inversion HFind2; subst
  end.
  match goal with
  | HFindStep : find_R w rho = Some ?rstep |- _ =>
      assert (HTcHeap' : TcHeap (update_H ((rstep, l), v) heap, stty))
        by (eapply H_update_heap_exists; eauto);
      assert (HHeapShape' :
        RuntimeHeapShape (update_H ((rstep, l), v) heap) stty)
        by (eapply RuntimeHeapShape_update_existing; eauto)
  end.
  exists stty. split.
  - eapply WTSRHSA_Return with (t := Ty_Unit); eauto.
    + constructor.
    + constructor.
  - split; [ simpl; exact HTcHeap' | split; [ simpl; exact HHeapShape' | apply StoreExtends_refl ] ].
Qed.

Lemma WTStateRuntimeHeapShapeAt_ref_done_step_preservation :
  forall heap rho w v k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap v (KRef w rho k)) tout stty ->
    Step (StReturn heap v (KRef w rho k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap rho w v k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KRef _ _ _) |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HFindR : find_R (Rgn_Const true false ?s) rho = Some ?r |- _ =>
      simpl in HFindR; inversion HFindR; subst
  end.
  assert (HFreshH : find_H (r, allocate_H heap r) heap = None)
    by apply allocate_H_fresh.
  assert (HFreshST : find_ST (r, allocate_H heap r) stty = None).
  {
    destruct (find_ST (r, allocate_H heap r) stty) eqn:HFindSTFresh; auto.
    exfalso.
    match goal with
    | HTcHeap : TcHeap (heap, stty) |- _ =>
        inversion HTcHeap as [? ? _ HStoreHeap _]; subst;
        destruct (HStoreHeap (r, allocate_H heap r) t HFindSTFresh)
          as [old HFindHOld];
        rewrite HFreshH in HFindHOld;
        discriminate
    end.
  }
  set (stty' := update_ST (r, allocate_H heap r) (subst_rho rho t0) stty).
  assert (HExt : StoreExtends stty stty').
  {
    subst stty'. apply StoreExtends_update_fresh. exact HFreshST.
  }
  assert (HTcHeap' :
      TcHeap
        (update_H ((r, allocate_H heap r), v) heap, stty')).
  {
    subst stty'. eapply H_update_heap_fresh; eauto.
  }
  assert (HHeapShape' :
      RuntimeHeapShape
        (update_H ((r, allocate_H heap r), v) heap) stty').
  {
    subst stty'. eapply RuntimeHeapShape_update_fresh; eauto.
  }
  exists stty'. split.
  - eapply WTSRHSA_Return
      with (t := Ty_Ref (Rgn_Const true true r) (subst_rho rho t0)); eauto.
    + subst stty'. constructor.
      * unfold find_ST, update_ST.
        apply lookup_insert.
      * intros rgn.
        eapply TcVal_implies_closed; eauto.
    + match goal with
      | HKont : WTKontRuntime stty
          (subst_rho rho (Ty_Ref (mk_rgn_type (Rgn_Const true false r)) ?ty))
          tout k |- _ =>
          simpl in HKont;
          rewrite subst_rho_ref_const in HKont;
          eapply WTKontRuntime_store_ext;
          [ exact HKont
          | exact HExt ]
      end.
    + constructor.
  - split; [ simpl; exact HTcHeap' | split; [ simpl; exact HHeapShape' | exact HExt ] ].
Qed.

Definition WTStateRuntimeHeapShapeAtStepPreservation : Prop :=
  forall state tout stty lbl state',
    WTStateRuntimeHeapShapeAt state tout stty ->
    Step state lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.

Lemma WTStateRuntimeHeapShapeAt_pack_same_store_step :
  forall state tout stty,
    WTStateRuntimeHeapShapeAt state tout stty ->
    exists stty',
      WTStateRuntimeHeapShapeAt state tout stty' /\
      TcHeap (state_heap state, stty') /\
      RuntimeHeapShape (state_heap state) stty' /\
      StoreExtends stty stty'.
Proof.
  intros state tout stty HState.
  exists stty. split.
  - exact HState.
  - inversion HState; subst; simpl;
      [ split; [ assumption | split; [ assumption | apply StoreExtends_refl ] ]
      | split; [ assumption | split; [ assumption | apply StoreExtends_refl ] ]
      | split; [ assumption | split; [ assumption | apply StoreExtends_refl ] ] ].
Qed.
