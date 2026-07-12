From stdpp Require Import gmap.
From Stdlib Require Import Program.Equality.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepProgress.
Require Import theories.Runtime.SmallStepPreservation.
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

Inductive WTStateRuntimeHeapShapeAt : State -> Tau -> Sigma -> Prop :=
| WTSRHSA_Eval :
    forall heap env rho e k stty ctxt rgns t eff tout,
      TcHeap (heap, stty) ->
      RuntimeHeapShape heap stty ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e, t, eff) ->
      WTKontRuntime stty (subst_rho rho t) tout k ->
      WTStateRuntimeHeapShapeAt (StEval heap env rho e k) tout stty
| WTSRHSA_Return :
    forall heap v k stty t tout,
      TcHeap (heap, stty) ->
      RuntimeHeapShape heap stty ->
      TcVal (stty, v, t) ->
      WTKontRuntime stty t tout k ->
      RuntimeValShape stty t v ->
      WTStateRuntimeHeapShapeAt (StReturn heap v k) tout stty
| WTSRHSA_Done :
    forall heap v stty t,
      TcHeap (heap, stty) ->
      RuntimeHeapShape heap stty ->
      TcVal (stty, v, t) ->
      RuntimeValShape stty t v ->
      WTStateRuntimeHeapShapeAt (StDone heap v) t stty.

Lemma WTStateRuntimeHeapShapeAt_forget :
  forall state tout stty,
    WTStateRuntimeHeapShapeAt state tout stty ->
    WTStateRuntimeHeapShape state tout.
Proof.
  intros state tout stty HWT.
  inversion HWT; subst; econstructor; eauto.
Qed.

Definition IdleBranchRetyped (heap : Heap) (state : State) (t : Tau) : Prop :=
  WTStateRuntimeHeapShape state t ->
  WTStateRuntimeHeapShape (with_state_heap heap state) t.

Lemma WTStateRuntimeHeapShapeAt_reheap_store_ext :
  forall state tout stty heap' stty',
    WTStateRuntimeHeapShapeAt state tout stty ->
    TcHeap (heap', stty') ->
    RuntimeHeapShape heap' stty' ->
    StoreExtends stty stty' ->
    WTStateRuntimeHeapShapeAt (with_state_heap heap' state) tout stty'.
Proof.
  intros state tout stty heap' stty' HWT HTcHeap' HHeapShape' HExt.
  inversion HWT; subst; simpl.
  - eapply WTSRHSA_Eval with (ctxt := ctxt) (rgns := rgns) (t := t)
      (eff := eff); eauto.
    + eapply ext_stores__env; eauto.
    + eapply RuntimeEnvShape_store_ext; eauto.
    + eapply WTKontRuntime_store_ext; eauto.
  - eapply WTSRHSA_Return; eauto.
    + eapply ext_stores__val; eauto.
    + eapply WTKontRuntime_store_ext; eauto.
    + eapply RuntimeValShape_store_ext; eauto.
  - eapply WTSRHSA_Done; eauto.
    + eapply ext_stores__val; eauto.
    + eapply RuntimeValShape_store_ext; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_reheap_same_store :
  forall state tout stty heap',
    WTStateRuntimeHeapShapeAt state tout stty ->
    TcHeap (heap', stty) ->
    RuntimeHeapShape heap' stty ->
    WTStateRuntimeHeapShapeAt (with_state_heap heap' state) tout stty.
Proof.
  intros state tout stty heap' HWT HTcHeap HHeapShape.
  eapply WTStateRuntimeHeapShapeAt_reheap_store_ext; eauto.
  intros k t HFind. exact HFind.
Qed.

Lemma WTStateRuntimeHeapShapeAt_idle_retyped :
  forall state tout stty heap' stty',
    WTStateRuntimeHeapShapeAt state tout stty ->
    TcHeap (heap', stty') ->
    RuntimeHeapShape heap' stty' ->
    StoreExtends stty stty' ->
    IdleBranchRetyped heap' state tout.
Proof.
  intros state tout stty heap' stty' HAt HTcHeap HHeapShape HExt _.
  eapply WTStateRuntimeHeapShapeAt_forget.
  eapply WTStateRuntimeHeapShapeAt_reheap_store_ext; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_idle_retyped_same_store :
  forall state tout stty heap',
    WTStateRuntimeHeapShapeAt state tout stty ->
    TcHeap (heap', stty) ->
    RuntimeHeapShape heap' stty ->
    IdleBranchRetyped heap' state tout.
Proof.
  intros state tout stty heap' HAt HTcHeap HHeapShape _.
  eapply WTStateRuntimeHeapShapeAt_forget.
  eapply WTStateRuntimeHeapShapeAt_reheap_same_store; eauto.
Qed.

Definition PairParDoneContinuationReadyAt
    (left right : State) (k : Kont) (tout : Tau) (stty : Sigma) : Prop :=
  forall heap v1 v2,
    left = StDone heap v1 ->
    right = StDone heap v2 ->
    WTStateRuntimeHeapShapeAt (StReturn heap (Pair (v1, v2)) k) tout stty.

Inductive WTPairParStateRuntimeHeapShapeAt :
    PairParState -> Tau -> Sigma -> Prop :=
| WTPPRSA_State :
    forall state tout stty,
      WTStateRuntimeHeapShapeAt state tout stty ->
      WTPairParStateRuntimeHeapShapeAt (PPS_State state) tout stty
| WTPPRSA_Run :
    forall left right k tleft tright tout stty,
      WTStateRuntimeHeapShapeAt left tleft stty ->
      WTStateRuntimeHeapShapeAt right tright stty ->
      PairParDoneContinuationReadyAt left right k tout stty ->
      WTPairParStateRuntimeHeapShapeAt (PPS_Run left right k) tout stty.

Lemma WTPairParStateRuntimeHeapShapeAt_checked_initial :
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    WTPairParStateRuntimeHeapShapeAt
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k)
      tout stty.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont.
  unfold pairpar_checked_initial, initial_state.
  eapply WTPPRSA_Run
    with (tleft := subst_rho rho ty1) (tright := subst_rho rho ty2).
  - eapply WTSRHSA_Eval with (ctxt := ctxt) (rgns := rgns) (t := ty1)
      (eff := eff1); eauto.
    constructor.
  - eapply WTSRHSA_Eval with (ctxt := ctxt) (rgns := rgns) (t := ty2)
      (eff := eff2); eauto.
    constructor.
  - intros heap0 v1 v2 HLeftDone _.
    discriminate HLeftDone.
Qed.

Lemma WTPairParStateRuntimeHeapShapeAt_state_step_preservation :
  forall state tout stty lbl state',
    WTPairParStateRuntimeHeapShapeAt (PPS_State state) tout stty ->
    WTStateRuntimeHeapShapeAt state' tout stty ->
    PairParStep (PPS_State state) lbl (PPS_State state') ->
    WTPairParStateRuntimeHeapShapeAt (PPS_State state') tout stty.
Proof.
  intros state tout stty lbl state' _ HState' HStep.
  inversion HStep; subst.
  constructor. exact HState'.
Qed.

Lemma WTPairParStateRuntimeHeapShapeAt_done_step_preservation :
  forall heap v1 v2 k tout stty,
    WTPairParStateRuntimeHeapShapeAt
      (PPS_Run (StDone heap v1) (StDone heap v2) k) tout stty ->
    WTPairParStateRuntimeHeapShapeAt
      (PPS_State (StReturn heap (Pair (v1, v2)) k)) tout stty.
Proof.
  intros heap v1 v2 k tout stty HWT.
  inversion HWT; subst.
  constructor.
  match goal with
  | H : PairParDoneContinuationReadyAt
        (StDone heap v1) (StDone heap v2) k tout stty |- _ =>
      eapply H; reflexivity
  end.
Qed.

Lemma WTPairParStateRuntimeHeapShapeAt_left_step_preservation :
  forall left right k tout stty stty' lbl left' tleft',
    WTPairParStateRuntimeHeapShapeAt (PPS_Run left right k) tout stty ->
    Step left lbl left' ->
    WTStateRuntimeHeapShapeAt left' tleft' stty' ->
    TcHeap (state_heap left', stty') ->
    RuntimeHeapShape (state_heap left') stty' ->
    StoreExtends stty stty' ->
    PairParDoneContinuationReadyAt
      left' (with_state_heap (state_heap left') right) k tout stty' ->
    WTPairParStateRuntimeHeapShapeAt
      (PPS_Run left' (with_state_heap (state_heap left') right) k) tout stty'.
Proof.
  intros left right k tout stty stty' lbl left' tleft'
    HWT _ HLeft' HTcHeap HHeapShape HExt HDone.
  inversion HWT; subst.
  eapply WTPPRSA_Run with (tleft := tleft') (tright := tright).
  - exact HLeft'.
  - eapply WTStateRuntimeHeapShapeAt_reheap_store_ext; eauto.
  - exact HDone.
Qed.

Lemma WTPairParStateRuntimeHeapShapeAt_right_step_preservation :
  forall left right k tout stty stty' lbl right' tright',
    WTPairParStateRuntimeHeapShapeAt (PPS_Run left right k) tout stty ->
    Step right lbl right' ->
    WTStateRuntimeHeapShapeAt right' tright' stty' ->
    TcHeap (state_heap right', stty') ->
    RuntimeHeapShape (state_heap right') stty' ->
    StoreExtends stty stty' ->
    PairParDoneContinuationReadyAt
      (with_state_heap (state_heap right') left) right' k tout stty' ->
    WTPairParStateRuntimeHeapShapeAt
      (PPS_Run (with_state_heap (state_heap right') left) right' k) tout stty'.
Proof.
  intros left right k tout stty stty' lbl right' tright'
    HWT _ HRight' HTcHeap HHeapShape HExt HDone.
  inversion HWT; subst.
  eapply WTPPRSA_Run with (tleft := tleft) (tright := tright').
  - eapply WTStateRuntimeHeapShapeAt_reheap_store_ext; eauto.
  - exact HRight'.
  - exact HDone.
Qed.

Lemma WTStateRuntimeHeapShapeAt_done_pair_return :
  forall heap v1 v2 k tleft tright tout stty,
    WTStateRuntimeHeapShapeAt (StDone heap v1) tleft stty ->
    WTStateRuntimeHeapShapeAt (StDone heap v2) tright stty ->
    WTKontRuntime stty (Ty_Pair tleft tright) tout k ->
    WTStateRuntimeHeapShapeAt (StReturn heap (Pair (v1, v2)) k) tout stty.
Proof.
  intros heap v1 v2 k tleft tright tout stty HLeft HRight HKont.
  inversion HLeft; subst.
  inversion HRight; subst.
  eapply WTSRHSA_Return with (t := Ty_Pair tleft tright); eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Inductive WTPairParStateRuntimeHeapShapeAtStrong :
    PairParState -> Tau -> Sigma -> Prop :=
| WTPPRSAS_State :
    forall state tout stty,
      WTStateRuntimeHeapShapeAt state tout stty ->
      WTPairParStateRuntimeHeapShapeAtStrong (PPS_State state) tout stty
| WTPPRSAS_Run :
    forall left right k tleft tright tout stty,
      WTStateRuntimeHeapShapeAt left tleft stty ->
      WTStateRuntimeHeapShapeAt right tright stty ->
      WTKontRuntime stty (Ty_Pair tleft tright) tout k ->
      WTPairParStateRuntimeHeapShapeAtStrong (PPS_Run left right k) tout stty.

Lemma WTPairParStateRuntimeHeapShapeAtStrong_forget :
  forall state tout stty,
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    WTPairParStateRuntimeHeapShapeAt state tout stty.
Proof.
  intros state tout stty HWT.
  inversion HWT; subst.
  - econstructor; eauto.
  - eapply WTPPRSA_Run with (tleft := tleft) (tright := tright); eauto.
    intros heap v1 v2 HLeftDone HRightDone.
    subst.
    eapply WTStateRuntimeHeapShapeAt_done_pair_return; eauto.
Qed.

Lemma WTPairParStateRuntimeHeapShapeAtStrong_checked_initial :
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    WTPairParStateRuntimeHeapShapeAtStrong
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k)
      tout stty.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont.
  unfold pairpar_checked_initial, initial_state.
  rewrite subst_rho_pair in HKont.
  eapply WTPPRSAS_Run
    with (tleft := subst_rho rho ty1) (tright := subst_rho rho ty2).
  - eapply WTSRHSA_Eval with (ctxt := ctxt) (rgns := rgns) (t := ty1)
      (eff := eff1); eauto.
    constructor.
  - eapply WTSRHSA_Eval with (ctxt := ctxt) (rgns := rgns) (t := ty2)
      (eff := eff2); eauto.
    constructor.
  - exact HKont.
Qed.

Lemma WTPairParStateRuntimeHeapShapeAtStrong_done_step_preservation :
  forall heap v1 v2 k tout stty,
    WTPairParStateRuntimeHeapShapeAtStrong
      (PPS_Run (StDone heap v1) (StDone heap v2) k) tout stty ->
    WTPairParStateRuntimeHeapShapeAtStrong
      (PPS_State (StReturn heap (Pair (v1, v2)) k)) tout stty.
Proof.
  intros heap v1 v2 k tout stty HWT.
  inversion HWT; subst.
  constructor.
  eapply WTStateRuntimeHeapShapeAt_done_pair_return; eauto.
Qed.

Lemma WTPairParStateRuntimeHeapShapeAtStrong_left_step_preservation :
  forall left right k tout stty stty' lbl left',
    WTPairParStateRuntimeHeapShapeAtStrong
      (PPS_Run left right k) tout stty ->
    Step left lbl left' ->
    (forall tleft,
        WTStateRuntimeHeapShapeAt left tleft stty ->
        WTStateRuntimeHeapShapeAt left' tleft stty') ->
    TcHeap (state_heap left', stty') ->
    RuntimeHeapShape (state_heap left') stty' ->
    StoreExtends stty stty' ->
    WTPairParStateRuntimeHeapShapeAtStrong
      (PPS_Run left' (with_state_heap (state_heap left') right) k) tout stty'.
Proof.
  intros left right k tout stty stty' lbl left'
    HWT _ HActive HTcHeap HHeapShape HExt.
  inversion HWT; subst.
  eapply WTPPRSAS_Run with (tleft := tleft) (tright := tright).
  - eapply HActive; eauto.
  - eapply WTStateRuntimeHeapShapeAt_reheap_store_ext; eauto.
  - eapply WTKontRuntime_store_ext; eauto.
Qed.

Lemma WTPairParStateRuntimeHeapShapeAtStrong_right_step_preservation :
  forall left right k tout stty stty' lbl right',
    WTPairParStateRuntimeHeapShapeAtStrong
      (PPS_Run left right k) tout stty ->
    Step right lbl right' ->
    (forall tright,
        WTStateRuntimeHeapShapeAt right tright stty ->
        WTStateRuntimeHeapShapeAt right' tright stty') ->
    TcHeap (state_heap right', stty') ->
    RuntimeHeapShape (state_heap right') stty' ->
    StoreExtends stty stty' ->
    WTPairParStateRuntimeHeapShapeAtStrong
      (PPS_Run (with_state_heap (state_heap right') left) right' k) tout stty'.
Proof.
  intros left right k tout stty stty' lbl right'
    HWT _ HActive HTcHeap HHeapShape HExt.
  inversion HWT; subst.
  eapply WTPPRSAS_Run with (tleft := tleft) (tright := tright).
  - eapply WTStateRuntimeHeapShapeAt_reheap_store_ext; eauto.
  - eapply HActive; eauto.
  - eapply WTKontRuntime_store_ext; eauto.
Qed.

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

Lemma WTStateRuntimeHeapShapeAt_mu_app_eval_fun_step_preservation :
  forall heap env rho ef ea k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (Mu_App ef ea) k) tout stty ->
    Step (StEval heap env rho (Mu_App ef ea) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho ef ea k tout stty lbl state' HState HStep.
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
      eapply WTStateRuntimeHeapShapeAt_pack_same_store_step;
      eapply WTSRHSA_Eval
        with
          (ctxt := ctxt) (rgns := rgns)
          (t := Ty_Arrow tya effc tyc effe Ty_Effect) (eff := efff);
      eauto;
      eapply WTKR_MuAppFun; eauto
  end.
Qed.

Lemma WTStateRuntimeHeapShapeAt_rgn_app_eval_fun_step_preservation :
  forall heap env rho er w k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (Rgn_App er w) k) tout stty ->
    Step (StEval heap env rho (Rgn_App er w) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho er w k tout stty lbl state' HState HStep.
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
      eapply WTStateRuntimeHeapShapeAt_pack_same_store_step;
      eapply WTSRHSA_Eval
        with
          (ctxt := ctxt) (rgns := rgns)
          (t := Ty_ForallRgn effr tyr) (eff := efff);
      eauto;
      eapply WTKR_RgnApp; eauto
  end.
Qed.

Lemma WTStateRuntimeHeapShapeAt_eff_app_eval_fun_step_preservation :
  forall heap env rho ef ea k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (Eff_App ef ea) k) tout stty ->
    Step (StEval heap env rho (Eff_App ef ea) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho ef ea k tout stty lbl state' HState HStep.
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
      eapply WTStateRuntimeHeapShapeAt_pack_same_store_step;
      eapply WTSRHSA_Eval
        with
          (ctxt := ctxt) (rgns := rgns)
          (t := Ty_Arrow tya effc tyc effe Ty_Effect) (eff := efff);
      eauto;
      eapply WTKR_EffAppFun; eauto
  end.
Qed.

Lemma WTStateRuntimeHeapShapeAt_cond_eval_guard_step_preservation :
  forall heap env rho e et ef k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (Cond e et ef) k) tout stty ->
    Step (StEval heap env rho (Cond e et ef) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho e et ef k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Cond _ _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval
    with (ctxt := ctxt) (rgns := rgns) (t := Ty_Boolean);
    eauto.
  rewrite (subst_rho_boolean rho).
  eapply WTKR_Cond; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_ref_eval_arg_step_preservation :
  forall heap env rho w e k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (Ref w e) k) tout stty ->
    Step (StEval heap env rho (Ref w e) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho w e k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Ref _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval with (ctxt := ctxt) (rgns := rgns); eauto.
  eapply WTKR_Ref; eauto; try constructor.
Qed.

Lemma WTStateRuntimeHeapShapeAt_deref_eval_arg_step_preservation :
  forall heap env rho w e k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (DeRef w e) k) tout stty ->
    Step (StEval heap env rho (DeRef w e) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho w e k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, DeRef _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval with (ctxt := ctxt) (rgns := rgns); eauto.
  eapply WTKR_DeRef; eauto; try constructor.
Qed.

Lemma WTStateRuntimeHeapShapeAt_assign_eval_loc_step_preservation :
  forall heap env rho w ea ev k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (Assign w ea ev) k) tout stty ->
    Step (StEval heap env rho (Assign w ea ev) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho w ea ev k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval with (ctxt := ctxt) (rgns := rgns); eauto.
  eapply WTKR_AssignLoc; eauto; try constructor.
Qed.

Lemma WTStateRuntimeHeapShapeAt_plus_eval_left_step_preservation :
  forall heap env rho e1 e2 k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (Plus e1 e2) k) tout stty ->
    Step (StEval heap env rho (Plus e1 e2) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho e1 e2 k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval
    with (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural);
    eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_PlusL; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_minus_eval_left_step_preservation :
  forall heap env rho e1 e2 k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (Minus e1 e2) k) tout stty ->
    Step (StEval heap env rho (Minus e1 e2) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho e1 e2 k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval
    with (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural);
    eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_MinusL; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_times_eval_left_step_preservation :
  forall heap env rho e1 e2 k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (Times e1 e2) k) tout stty ->
    Step (StEval heap env rho (Times e1 e2) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho e1 e2 k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval
    with (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural);
    eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_TimesL; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_eq_eval_left_step_preservation :
  forall heap env rho e1 e2 k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (Eq e1 e2) k) tout stty ->
    Step (StEval heap env rho (Eq e1 e2) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho e1 e2 k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval
    with (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural);
    eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_EqL; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_read_conc_eval_arg_step_preservation :
  forall heap env rho e k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (ReadConc e) k) tout stty ->
    Step (StEval heap env rho (ReadConc e) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho e k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval with (ctxt := ctxt) (rgns := rgns); eauto.
  eapply WTKR_ReadConc; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_write_conc_eval_arg_step_preservation :
  forall heap env rho e k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (WriteConc e) k) tout stty ->
    Step (StEval heap env rho (WriteConc e) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho e k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval with (ctxt := ctxt) (rgns := rgns); eauto.
  eapply WTKR_WriteConc; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_concat_eval_left_step_preservation :
  forall heap env rho e1 e2 k tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StEval heap env rho (Concat e1 e2) k) tout stty ->
    Step (StEval heap env rho (Concat e1 e2) k) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho e1 e2 k tout stty lbl state' HState HStep.
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
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval
    with (ctxt := ctxt) (rgns := rgns) (t := Ty_Effect);
    eauto.
  rewrite (subst_rho_effect rho).
  eapply WTKR_ConcatL; eauto.
Qed.

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
  - match goal with
    | HKont : WTKontRuntime _ _ _ (KPairParEff2 _ _ _ _ _ _ _ _) |- _ =>
        inversion HKont; subst
    end.
    eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
    eapply WTSRHSA_Eval; eauto.
    eapply WTKR_PairParMu1; eauto.
  - match goal with
    | HKont : WTKontRuntime _ _ _ (KPairParEff2 _ _ _ _ _ _ _ _) |- _ =>
        inversion HKont; subst
    end.
    eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
    eapply WTSRHSA_Eval; eauto.
    eapply WTKR_PairParMu1; eauto.
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

Lemma WTStateRuntimeHeapShapeAt_mu_app_eval_arg_step_preservation :
  forall heap env rho k ea env' rho' f x ec ee tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KMuAppFun ea env rho k)) tout stty ->
    Step
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KMuAppFun ea env rho k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho k ea env' rho' f x ec ee tout stty lbl state'
    HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KMuAppFun _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HShape : RuntimeValShape _ _
      (Cls (env', rho', Mu f x ec ee)) |- _ =>
      destruct (RuntimeValShape_mu_closure_inv
        _ _ _ _ _ _ _ _ HShape)
        as (rgns_cl & ctxt_cl & tya_cl & effc_cl &
            tyc_cl & effe_cl & HClosureTy & HTcRhoCl & HTcIncCl &
            HTcEnvCl & HEnvShapeCl & HTcExpCl);
      pose proof (subst_rho_arrow_arg_eq _ _ _ _ _ _ _ _ _ _ HClosureTy)
        as HArgEq;
      pose proof (subst_rho_arrow_result_eq _ _ _ _ _ _ _ _ _ _ HClosureTy)
        as HResultEq
  end.
  match goal with
  | HTcExp : TcExp (_, _, Mu _ _ _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval; eauto.
  rewrite HArgEq.
  eapply WTKR_MuAppArg; eauto.
  - inversion HTcIncCl as [? ? HFrvCl]; subst.
    eapply ExtendedTcInv_2; eauto;
      eapply HFrvCl; eauto.
  - rewrite <- HResultEq.
    eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_eff_app_eval_arg_step_preservation :
  forall heap env rho k ea env' rho' f x ec ee tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KEffAppFun ea env rho k)) tout stty ->
    Step
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KEffAppFun ea env rho k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho k ea env' rho' f x ec ee tout stty lbl state'
    HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KEffAppFun _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HShape : RuntimeValShape _ _
      (Cls (env', rho', Mu f x ec ee)) |- _ =>
      destruct (RuntimeValShape_mu_closure_inv
        _ _ _ _ _ _ _ _ HShape)
        as (rgns_cl & ctxt_cl & tya_cl & effc_cl &
            tyc_cl & effe_cl & HClosureTy & HTcRhoCl & HTcIncCl &
            HTcEnvCl & HEnvShapeCl & HTcExpCl);
      pose proof (subst_rho_arrow_arg_eq _ _ _ _ _ _ _ _ _ _ HClosureTy)
        as HArgEq
  end.
  match goal with
  | HTcExp : TcExp (_, _, Mu _ _ _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval; eauto.
  rewrite HArgEq.
  eapply WTKR_EffAppArg; eauto.
  inversion HTcIncCl as [? ? HFrvCl]; subst.
  eapply ExtendedTcInv_2; eauto;
    eapply HFrvCl; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_mu_app_body_step_preservation :
  forall heap env rho f x ec ee v k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap v (KMuAppArg env rho f x ec ee k)) tout stty ->
    Step
      (StReturn heap v (KMuAppArg env rho f x ec ee k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho f x ec ee v k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KMuAppArg _ _ _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  assert (HClosureVal :
    TcVal
      (stty, Cls (env, rho, Mu f x ec ee),
        subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))) by
    (eapply TC_Cls with (rgns := rgns) (ctxt := ctxt); eauto).
  assert (HClosureShape :
    RuntimeValShape stty
      (subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))
      (Cls (env, rho, Mu f x ec ee))) by
    (eapply RVS_Arrow with (rgns := rgns) (ctxt := ctxt); eauto).
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval
    with
      (ctxt :=
        update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya)
          ctxt)
      (rgns := rgns)
      (t := tyc)
      (eff := effc); eauto.
  - eapply TcEnv_update_rec; eauto.
  - eapply RuntimeEnvShape_update_rec; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_eff_app_body_step_preservation :
  forall heap env rho f x ec ee v k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap v (KEffAppArg env rho f x ec ee k)) tout stty ->
    Step
      (StReturn heap v (KEffAppArg env rho f x ec ee k)) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap env rho f x ec ee v k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KEffAppArg _ _ _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  assert (HClosureVal :
    TcVal
      (stty, Cls (env, rho, Mu f x ec ee),
        subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))) by
    (eapply TC_Cls with (rgns := rgns) (ctxt := ctxt); eauto).
  assert (HClosureShape :
    RuntimeValShape stty
      (subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))
      (Cls (env, rho, Mu f x ec ee))) by
    (eapply RVS_Arrow with (rgns := rgns) (ctxt := ctxt); eauto).
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval
    with
      (ctxt :=
        update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya)
          ctxt)
      (rgns := rgns)
      (t := Ty_Effect)
      (eff := effe); eauto.
  - eapply TcEnv_update_rec; eauto.
  - eapply RuntimeEnvShape_update_rec; eauto.
  - rewrite (subst_rho_effect rho); eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_rgn_app_body_step_preservation :
  forall heap rho w env' rho' x eb k tout stty lbl state',
    WTStateRuntimeHeapShapeAt
      (StReturn heap (Cls (env', rho', Lambda x eb)) (KRgnApp w rho k))
      tout stty ->
    Step
      (StReturn heap (Cls (env', rho', Lambda x eb)) (KRgnApp w rho k))
      lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap rho w env' rho' x eb k tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KRgnApp _ _ _) |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HShape : RuntimeValShape _ _
      (Cls (env', rho', Lambda x eb)) |- _ =>
      destruct (RuntimeValShape_lambda_closure_inv
        _ _ _ _ _ _ HShape)
        as (rgns_cl & ctxt_cl & effr_cl & tyr_cl &
            HClosureTy & HTcRhoCl & HTcIncCl &
            HTcEnvCl & HEnvShapeCl & HTcExpCl)
  end.
  match goal with
  | HTcExp : TcExp (_, _, Lambda _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  assert (HBodyTyEq :
    subst_rho rho' (close_var x tyr0) = subst_rho rho tyr).
  {
    symmetry.
    eapply subst_rho_forall_body_eq.
    exact HClosureTy.
  }
  assert (HResumeTyEq :
    subst_rho (update_R (x, r) rho') tyr0 =
      subst_rho rho (open (mk_rgn_type w) tyr)).
  {
    eapply subst_rho_update_open_close; eauto.
  }
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Eval
    with
      (ctxt := ctxt_cl)
      (rgns := set_union rgns_cl (singleton_set x))
      (t := tyr0)
      (eff := effr0); eauto.
  - eapply update_rho; eauto.
  - eapply TcInc_extend_rgn_singleton; eauto.
  - eapply extended_rho; eauto.
  - eapply RuntimeEnvShape_extended_rho; eauto.
  - rewrite HResumeTyEq; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_done_step_preservation :
  forall heap v tout stty lbl state',
    WTStateRuntimeHeapShapeAt (StReturn heap v KDone) tout stty ->
    Step (StReturn heap v KDone) lbl state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      TcHeap (state_heap state', stty') /\
      RuntimeHeapShape (state_heap state') stty' /\
      StoreExtends stty stty'.
Proof.
  intros heap v tout stty lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ KDone |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateRuntimeHeapShapeAt_pack_same_store_step.
  eapply WTSRHSA_Done; eauto.
Qed.

Theorem WTStateRuntimeHeapShapeAt_step_preservation :
  WTStateRuntimeHeapShapeAtStepPreservation.
Proof.
  unfold WTStateRuntimeHeapShapeAtStepPreservation.
  intros state tout stty lbl state' HState HStep.
  inversion HStep; subst; eauto
    using
      WTStateRuntimeHeapShapeAt_const_step_preservation,
      WTStateRuntimeHeapShapeAt_bool_step_preservation,
      WTStateRuntimeHeapShapeAt_var_step_preservation,
      WTStateRuntimeHeapShapeAt_mu_step_preservation,
      WTStateRuntimeHeapShapeAt_lambda_step_preservation,
      WTStateRuntimeHeapShapeAt_mu_app_eval_fun_step_preservation,
      WTStateRuntimeHeapShapeAt_mu_app_eval_arg_step_preservation,
      WTStateRuntimeHeapShapeAt_mu_app_body_step_preservation,
      WTStateRuntimeHeapShapeAt_rgn_app_eval_fun_step_preservation,
      WTStateRuntimeHeapShapeAt_rgn_app_body_step_preservation,
      WTStateRuntimeHeapShapeAt_eff_app_eval_fun_step_preservation,
      WTStateRuntimeHeapShapeAt_eff_app_eval_arg_step_preservation,
      WTStateRuntimeHeapShapeAt_eff_app_body_step_preservation,
      WTStateRuntimeHeapShapeAt_pairpar_eval_eff1_step_preservation,
      WTStateRuntimeHeapShapeAt_pairpar_eval_eff2_step_preservation,
      WTStateRuntimeHeapShapeAt_pairpar_eval_mu1_step_preservation,
      WTStateRuntimeHeapShapeAt_pairpar_eval_mu2_step_preservation,
      WTStateRuntimeHeapShapeAt_pairpar_done_step_preservation,
      WTStateRuntimeHeapShapeAt_cond_eval_guard_step_preservation,
      WTStateRuntimeHeapShapeAt_cond_true_step_preservation,
      WTStateRuntimeHeapShapeAt_cond_false_step_preservation,
      WTStateRuntimeHeapShapeAt_ref_eval_arg_step_preservation,
      WTStateRuntimeHeapShapeAt_ref_done_step_preservation,
      WTStateRuntimeHeapShapeAt_deref_eval_arg_step_preservation,
      WTStateRuntimeHeapShapeAt_deref_done_step_preservation,
      WTStateRuntimeHeapShapeAt_assign_eval_loc_step_preservation,
      WTStateRuntimeHeapShapeAt_assign_eval_val_step_preservation,
      WTStateRuntimeHeapShapeAt_assign_done_step_preservation,
      WTStateRuntimeHeapShapeAt_plus_eval_left_step_preservation,
      WTStateRuntimeHeapShapeAt_plus_eval_right_step_preservation,
      WTStateRuntimeHeapShapeAt_plus_done_step_preservation,
      WTStateRuntimeHeapShapeAt_minus_eval_left_step_preservation,
      WTStateRuntimeHeapShapeAt_minus_eval_right_step_preservation,
      WTStateRuntimeHeapShapeAt_minus_done_step_preservation,
      WTStateRuntimeHeapShapeAt_times_eval_left_step_preservation,
      WTStateRuntimeHeapShapeAt_times_eval_right_step_preservation,
      WTStateRuntimeHeapShapeAt_times_done_step_preservation,
      WTStateRuntimeHeapShapeAt_eq_eval_left_step_preservation,
      WTStateRuntimeHeapShapeAt_eq_eval_right_step_preservation,
      WTStateRuntimeHeapShapeAt_eq_done_step_preservation,
      WTStateRuntimeHeapShapeAt_alloc_abs_step_preservation,
      WTStateRuntimeHeapShapeAt_read_abs_step_preservation,
      WTStateRuntimeHeapShapeAt_write_abs_step_preservation,
      WTStateRuntimeHeapShapeAt_read_conc_eval_arg_step_preservation,
      WTStateRuntimeHeapShapeAt_read_conc_done_step_preservation,
      WTStateRuntimeHeapShapeAt_write_conc_eval_arg_step_preservation,
      WTStateRuntimeHeapShapeAt_write_conc_done_step_preservation,
      WTStateRuntimeHeapShapeAt_concat_eval_left_step_preservation,
      WTStateRuntimeHeapShapeAt_concat_eval_right_step_preservation,
      WTStateRuntimeHeapShapeAt_concat_done_step_preservation,
      WTStateRuntimeHeapShapeAt_top_step_preservation,
      WTStateRuntimeHeapShapeAt_empty_step_preservation,
      WTStateRuntimeHeapShapeAt_done_step_preservation.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_step_preservation_with_active :
  WTStateRuntimeHeapShapeAtStepPreservation ->
  forall state tout stty lbl state',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParStep state lbl state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' /\
      StoreExtends stty stty'.
Proof.
  intros HActive state tout stty lbl state' HWT HStep.
  inversion HStep; subst.
  - inversion HWT; subst.
    match goal with
    | HState : WTStateRuntimeHeapShapeAt ?state ?tout ?stty,
      HStepState : Step ?state ?lbl ?state' |- _ =>
        destruct (HActive state tout stty lbl state' HState HStepState)
          as (stty' & HState' & _ & _ & HExt)
    end.
    exists stty'. split.
    + constructor. exact HState'.
    + exact HExt.
  - inversion HWT; subst.
    match goal with
    | HLeft : WTStateRuntimeHeapShapeAt left tleft stty,
      HLeftStep : Step left lbl left' |- _ =>
        destruct (HActive left tleft stty lbl left' HLeft HLeftStep)
          as (stty' & HLeft' & HTcHeap' & HHeapShape' & HExt)
    end.
    exists stty'. split.
    + eapply WTPPRSAS_Run with (tleft := tleft) (tright := tright).
      * exact HLeft'.
      * eapply WTStateRuntimeHeapShapeAt_reheap_store_ext; eauto.
      * eapply WTKontRuntime_store_ext; eauto.
    + exact HExt.
  - inversion HWT; subst.
    match goal with
    | HRight : WTStateRuntimeHeapShapeAt right tright stty,
      HRightStep : Step right lbl right' |- _ =>
        destruct (HActive right tright stty lbl right' HRight HRightStep)
          as (stty' & HRight' & HTcHeap' & HHeapShape' & HExt)
    end.
    exists stty'. split.
    + eapply WTPPRSAS_Run with (tleft := tleft) (tright := tright).
      * eapply WTStateRuntimeHeapShapeAt_reheap_store_ext; eauto.
      * exact HRight'.
      * eapply WTKontRuntime_store_ext; eauto.
    + exact HExt.
  - exists stty. split.
    + eapply WTPairParStateRuntimeHeapShapeAtStrong_done_step_preservation;
        eauto.
    + apply StoreExtends_refl.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_steps_preservation_with_active :
  WTStateRuntimeHeapShapeAtStepPreservation ->
  forall state tout stty trace state',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParSteps state trace state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' /\
      StoreExtends stty stty'.
Proof.
  intros HActive state tout stty trace state' HWT HSteps.
  revert tout stty HWT.
  induction HSteps as
    [state0
    | state0 label state1 trace state2 HStep HSteps IHHSteps];
    intros tout stty HWT.
  - exists stty. split.
    + exact HWT.
    + apply StoreExtends_refl.
  - destruct
      (WTPairParStateRuntimeHeapShapeAtStrong_step_preservation_with_active
        HActive state0 tout stty label state1 HWT HStep)
      as (stty' & HWT' & HExt).
    destruct (IHHSteps tout stty' HWT') as (stty'' & HWT'' & HExt').
    exists stty''. split.
    + exact HWT''.
    + eapply StoreExtends_trans; eauto.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_step_preservation :
  forall state tout stty lbl state',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParStep state lbl state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' /\
      StoreExtends stty stty'.
Proof.
  intros state tout stty lbl state' HWT HStep.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_step_preservation_with_active;
    eauto.
  exact WTStateRuntimeHeapShapeAt_step_preservation.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_steps_preservation :
  forall state tout stty trace state',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParSteps state trace state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' /\
      StoreExtends stty stty'.
Proof.
  intros state tout stty trace state' HWT HSteps.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_steps_preservation_with_active;
    eauto.
  exact WTStateRuntimeHeapShapeAt_step_preservation.
Qed.

Inductive WTPairParStateRuntimeHeapShape : PairParState -> Tau -> Prop :=
| WTPPRS_State :
    forall state tout,
      WTStateRuntimeHeapShape state tout ->
      WTPairParStateRuntimeHeapShape (PPS_State state) tout
| WTPPRS_Run :
    forall left right k tleft tright tout,
      WTStateRuntimeHeapShape left tleft ->
      WTStateRuntimeHeapShape right tright ->
      (forall heap v1 v2,
          left = StDone heap v1 ->
          right = StDone heap v2 ->
          WTStateRuntimeHeapShape (StReturn heap (Pair (v1, v2)) k) tout) ->
      WTPairParStateRuntimeHeapShape (PPS_Run left right k) tout.

Lemma WTPairParStateRuntimeHeapShapeAt_forget :
  forall state tout stty,
    WTPairParStateRuntimeHeapShapeAt state tout stty ->
    WTPairParStateRuntimeHeapShape state tout.
Proof.
  intros state tout stty HWT.
  inversion HWT; subst.
  - constructor.
    eapply WTStateRuntimeHeapShapeAt_forget; eauto.
  - eapply WTPPRS_Run with (tleft := tleft) (tright := tright).
    + eapply WTStateRuntimeHeapShapeAt_forget; eauto.
    + eapply WTStateRuntimeHeapShapeAt_forget; eauto.
    + intros heap v1 v2 HLeft HRight.
      eapply WTStateRuntimeHeapShapeAt_forget.
      eapply H1; eauto.
Qed.

Definition PairParDoneContinuationReady
    (left right : State) (k : Kont) (tout : Tau) : Prop :=
  forall heap v1 v2,
    left = StDone heap v1 ->
    right = StDone heap v2 ->
    WTStateRuntimeHeapShape (StReturn heap (Pair (v1, v2)) k) tout.

Lemma WTPairParStateRuntimeHeapShape_checked_initial :
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    WTPairParStateRuntimeHeapShape
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k)
      tout.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont.
  unfold pairpar_checked_initial, initial_state.
  eapply WTPPRS_Run
    with (tleft := subst_rho rho ty1) (tright := subst_rho rho ty2).
  - eapply WTSRHS_Eval with (stty := stty) (ctxt := ctxt) (rgns := rgns);
      eauto.
    constructor.
  - eapply WTSRHS_Eval with (stty := stty) (ctxt := ctxt) (rgns := rgns);
      eauto.
    constructor.
  - intros heap0 v1 v2 HLeftDone _.
    discriminate HLeftDone.
Qed.

Lemma WTPairParStateRuntimeHeapShape_state_step_preservation :
  forall state tout lbl state',
    WTPairParStateRuntimeHeapShape (PPS_State state) tout ->
    PairParStep (PPS_State state) lbl (PPS_State state') ->
    WTPairParStateRuntimeHeapShape (PPS_State state') tout.
Proof.
  intros state tout lbl state' HWT HStep.
  inversion HWT; subst.
  inversion HStep; subst.
  constructor.
  eapply WTStateRuntimeHeapShape_step_preservation; eauto.
Qed.

Lemma WTPairParStateRuntimeHeapShape_done_step_preservation :
  forall heap v1 v2 k tout,
    WTPairParStateRuntimeHeapShape
      (PPS_Run (StDone heap v1) (StDone heap v2) k) tout ->
    WTPairParStateRuntimeHeapShape
      (PPS_State (StReturn heap (Pair (v1, v2)) k)) tout.
Proof.
  intros heap v1 v2 k tout HWT.
  inversion HWT; subst.
  constructor.
  match goal with
  | H : forall heap0 v3 v4,
        StDone heap v1 = StDone heap0 v3 ->
        StDone heap v2 = StDone heap0 v4 ->
        WTStateRuntimeHeapShape (StReturn heap0 (Pair (v3, v4)) k) tout |- _ =>
      eapply H; reflexivity
  end.
Qed.

Lemma WTPairParStateRuntimeHeapShape_left_step_preservation :
  forall left right k tout lbl left',
    WTPairParStateRuntimeHeapShape (PPS_Run left right k) tout ->
    Step left lbl left' ->
    (forall tright,
        WTStateRuntimeHeapShape right tright ->
        IdleBranchRetyped (state_heap left') right tright) ->
    PairParDoneContinuationReady
      left' (with_state_heap (state_heap left') right) k tout ->
    WTPairParStateRuntimeHeapShape
      (PPS_Run left' (with_state_heap (state_heap left') right) k) tout.
Proof.
  intros left right k tout lbl left' HWT HStep HRetype HDone.
  inversion HWT; subst.
  eapply WTPPRS_Run with (tleft := tleft) (tright := tright).
  - eapply WTStateRuntimeHeapShape_step_preservation; eauto.
  - eapply HRetype; eauto.
  - exact HDone.
Qed.

Lemma WTPairParStateRuntimeHeapShape_right_step_preservation :
  forall left right k tout lbl right',
    WTPairParStateRuntimeHeapShape (PPS_Run left right k) tout ->
    Step right lbl right' ->
    (forall tleft,
        WTStateRuntimeHeapShape left tleft ->
        IdleBranchRetyped (state_heap right') left tleft) ->
    PairParDoneContinuationReady
      (with_state_heap (state_heap right') left) right' k tout ->
    WTPairParStateRuntimeHeapShape
      (PPS_Run (with_state_heap (state_heap right') left) right' k) tout.
Proof.
  intros left right k tout lbl right' HWT HStep HRetype HDone.
  inversion HWT; subst.
  eapply WTPPRS_Run with (tleft := tleft) (tright := tright).
  - eapply HRetype; eauto.
  - eapply WTStateRuntimeHeapShape_step_preservation; eauto.
  - exact HDone.
Qed.

Definition PairParTerminal (state : PairParState) : Prop :=
  match state with
  | PPS_State state => Terminal state
  | PPS_Run _ _ _ => False
  end.

Definition PairParNotStuck (state : PairParState) : Prop :=
  PairParTerminal state \/ PairParCanStep state.

Definition StateEvalHeadRegionsResolved (state : State) : Prop :=
  forall heap env rho e k,
    state = StEval heap env rho e k ->
    EvalHeadRegionsResolved rho e.

Lemma TcExp_eval_head_regions_resolved :
  forall ctxt rgns e t eff rho,
    TcRho (rho, rgns) ->
    TcExp (ctxt, rgns, e, t, eff) ->
    EvalHeadRegionsResolved rho e.
Proof.
  intros ctxt rgns e t eff rho HTcRho HTcExp.
  destruct e; simpl; try exact I;
    inversion HTcExp; subst; eapply TcRho_TcRgn_find_R; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_eval_heads_resolved :
  forall state tout,
    WTStateRuntimeHeapShape state tout ->
    StateEvalHeadRegionsResolved state.
Proof.
  intros state tout HWT.
  destruct state as [heap0 env0 rho0 e0 k0 | heap0 v k0 | heap0 v];
    intros heap env rho e k HEq; inversion HEq; subst.
  inversion HWT; subst.
  eapply TcExp_eval_head_regions_resolved; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_eval_heads_resolved :
  forall state tout stty,
    WTStateRuntimeHeapShapeAt state tout stty ->
    StateEvalHeadRegionsResolved state.
Proof.
  intros state tout stty HWT.
  destruct state as [heap0 env0 rho0 e0 k0 | heap0 v k0 | heap0 v];
    intros heap env rho e k HEq; inversion HEq; subst.
  inversion HWT; subst.
  eapply TcExp_eval_head_regions_resolved; eauto.
Qed.

Lemma StateEvalHeadRegionsResolved_with_state_heap :
  forall heap state,
    StateEvalHeadRegionsResolved state ->
    StateEvalHeadRegionsResolved (with_state_heap heap state).
Proof.
  intros heap state HReady heap0 env rho e k HEq.
  destruct state; simpl in HEq; inversion HEq; subst.
  eapply HReady. reflexivity.
Qed.

Definition PairParEvalHeadRegionsResolved (state : PairParState) : Prop :=
  match state with
  | PPS_State state => StateEvalHeadRegionsResolved state
  | PPS_Run left_state right_state _ =>
      StateEvalHeadRegionsResolved left_state /\
      StateEvalHeadRegionsResolved right_state
  end.

Lemma PairParEvalHeadRegionsResolved_left_step :
  forall left right k left',
    PairParEvalHeadRegionsResolved (PPS_Run left right k) ->
    StateEvalHeadRegionsResolved left' ->
    PairParEvalHeadRegionsResolved
      (PPS_Run left' (with_state_heap (state_heap left') right) k).
Proof.
  intros left right k left' HReady HLeftReady.
  simpl in *.
  destruct HReady as [_ HRightReady].
  split.
  - exact HLeftReady.
  - apply StateEvalHeadRegionsResolved_with_state_heap.
    exact HRightReady.
Qed.

Lemma PairParEvalHeadRegionsResolved_right_step :
  forall left right k right',
    PairParEvalHeadRegionsResolved (PPS_Run left right k) ->
    StateEvalHeadRegionsResolved right' ->
    PairParEvalHeadRegionsResolved
      (PPS_Run (with_state_heap (state_heap right') left) right' k).
Proof.
  intros left right k right' HReady HRightReady.
  simpl in *.
  destruct HReady as [HLeftReady _].
  split.
  - apply StateEvalHeadRegionsResolved_with_state_heap.
    exact HLeftReady.
  - exact HRightReady.
Qed.

Lemma WTPairParStateRuntimeHeapShape_eval_heads_resolved :
  forall state tout,
    WTPairParStateRuntimeHeapShape state tout ->
    PairParEvalHeadRegionsResolved state.
Proof.
  intros state tout HWT.
  inversion HWT; subst; simpl.
  - eapply WTStateRuntimeHeapShape_eval_heads_resolved; eauto.
  - split;
      eapply WTStateRuntimeHeapShape_eval_heads_resolved; eauto.
Qed.

Lemma WTPairParStateRuntimeHeapShapeAtStrong_eval_heads_resolved :
  forall state tout stty,
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParEvalHeadRegionsResolved state.
Proof.
  intros state tout stty HWT.
  eapply WTPairParStateRuntimeHeapShape_eval_heads_resolved.
  eapply WTPairParStateRuntimeHeapShapeAt_forget.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_forget; eauto.
Qed.

Theorem WTPairParStateRuntimeHeapShape_not_stuck :
  PairParCheckDecidable ->
  forall state tout,
    WTPairParStateRuntimeHeapShape state tout ->
    PairParRunHeapsAgree state ->
    PairParEvalHeadRegionsResolved state ->
    PairParNotStuck state.
Proof.
  intros HDec state tout HWT HAgree HReady.
  inversion HWT as
    [state0 tout0 HState
    | left_state right_state k tleft tright tout0 HLeft HRight HDone];
    subst.
  - destruct
      (WTStateRuntimeHeapShape_not_stuck
        HDec state0 tout HState HReady)
      as [HTerminal | HCanStep].
    + left. exact HTerminal.
    + right.
      destruct HCanStep as (label & state' & HStep).
      exists label, (PPS_State state').
      constructor. exact HStep.
  - simpl in HAgree.
    simpl in HReady.
    destruct HReady as [HLeftReady HRightReady].
    destruct
      (WTStateRuntimeHeapShape_not_stuck
        HDec left_state tleft HLeft HLeftReady)
      as [HLeftTerminal | HLeftCanStep].
    + inversion HLeftTerminal; subst.
      destruct
        (WTStateRuntimeHeapShape_not_stuck
          HDec right_state tright HRight HRightReady)
        as [HRightTerminal | HRightCanStep].
      * inversion HRightTerminal; subst.
        simpl in HAgree. subst.
        right. apply pairpar_done_can_step.
      * right. apply pairpar_right_can_step. exact HRightCanStep.
    + right. apply pairpar_left_can_step. exact HLeftCanStep.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_not_stuck :
  PairParCheckDecidable ->
  forall state tout stty,
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParRunHeapsAgree state ->
    PairParEvalHeadRegionsResolved state ->
    PairParNotStuck state.
Proof.
  intros HDec state tout stty HWT HAgree HReady.
  eapply (WTPairParStateRuntimeHeapShape_not_stuck HDec); eauto.
  eapply WTPairParStateRuntimeHeapShapeAt_forget.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_forget; eauto.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_steps_not_stuck :
  PairParCheckDecidable ->
  forall state tout stty trace state',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParRunHeapsAgree state ->
    PairParSteps state trace state' ->
    PairParEvalHeadRegionsResolved state' ->
    PairParNotStuck state'.
Proof.
  intros HDec state tout stty trace state' HWT HAgree HSteps HReady.
  destruct
    (WTPairParStateRuntimeHeapShapeAtStrong_steps_preservation
      state tout stty trace state' HWT HSteps)
    as (stty' & HWT' & _).
  eapply WTPairParStateRuntimeHeapShapeAtStrong_not_stuck; eauto.
  eapply pairpar_steps_preserve_heap_agreement; eauto.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_steps_eval_heads_resolved :
  forall state tout stty trace state',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParSteps state trace state' ->
    PairParEvalHeadRegionsResolved state'.
Proof.
  intros state tout stty trace state' HWT HSteps.
  destruct
    (WTPairParStateRuntimeHeapShapeAtStrong_steps_preservation
      state tout stty trace state' HWT HSteps)
    as (stty' & HWT' & _).
  eapply WTPairParStateRuntimeHeapShapeAtStrong_eval_heads_resolved; eauto.
Qed.

Definition PairParEvalHeadRegionsResolvedAfterSteps
    (state : PairParState) : Prop :=
  forall trace state',
    PairParSteps state trace state' ->
    PairParEvalHeadRegionsResolved state'.

Definition PairParNeverStuck (state : PairParState) : Prop :=
  forall trace state',
    PairParSteps state trace state' ->
    PairParNotStuck state'.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_never_stuck :
  PairParCheckDecidable ->
  forall state tout stty,
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParRunHeapsAgree state ->
    PairParEvalHeadRegionsResolvedAfterSteps state ->
    PairParNeverStuck state.
Proof.
  intros HDec state tout stty HWT HAgree HReady trace state' HSteps.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_steps_not_stuck; eauto.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_never_stuck_typed :
  PairParCheckDecidable ->
  forall state tout stty,
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParRunHeapsAgree state ->
    PairParNeverStuck state.
Proof.
  intros HDec state tout stty HWT HAgree trace state' HSteps.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_steps_not_stuck; eauto.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_steps_eval_heads_resolved; eauto.
Qed.

Lemma pairpar_checked_initial_eval_heads_resolved :
  forall heap env rho ef1 ea1 ef2 ea2 k,
    PairParEvalHeadRegionsResolved
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k.
  unfold pairpar_checked_initial, initial_state.
  simpl.
  split; intros heap0 env0 rho0 e0 k0 HEq;
    inversion HEq; subst; simpl; exact I.
Qed.

Lemma pairpar_checked_initial_not_stuck :
  forall heap env rho ef1 ea1 ef2 ea2 k,
    PairParNotStuck
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k.
  right.
  apply pairpar_checked_initial_left_can_step.
Qed.

Theorem pairpar_checked_initial_never_stuck_typed :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    PairParNeverStuck
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k).
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_never_stuck_typed.
  - exact HDec.
  - eapply WTPairParStateRuntimeHeapShapeAtStrong_checked_initial; eauto.
  - apply pairpar_checked_initial_heaps_agree.
Qed.

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
  split; [exact H |].
  split; [exact H0 |].
  split; [exact H1 | exact H2].
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

Lemma WTStateRuntimeHeapShapeAt_step_label_typed :
  forall state tin stty label state' tout stty',
    WTStateRuntimeHeapShapeAt state tin stty ->
    Step state label state' ->
    WTStateRuntimeHeapShapeAt state' tout stty' ->
    TcPhi stty' (trace_as_phi (label_trace label)).
Proof.
  intros state tin stty label state' tout stty' HWT HStep HWT'.
  inversion HStep; subst; simpl; try apply TcPhi_nil.
  - apply TcPhi_trace_as_phi_single.
    dependent destruction HWT'.
    eapply TcPhi_elem_alloc_from_heap; eauto.
    unfold find_H, update_H. simpl.
    apply H_same_key_1.
  - apply TcPhi_trace_as_phi_single.
    apply TcPhi_elem_read.
  - apply TcPhi_trace_as_phi_single.
    dependent destruction HWT'.
    eapply TcPhi_elem_write_from_heap; eauto.
    unfold find_H, update_H. simpl.
    apply H_same_key_1.
Qed.

Theorem WTStateRuntimeHeapShapeAt_steps_trace_typed :
  forall state tout stty trace state',
    WTStateRuntimeHeapShapeAt state tout stty ->
    Steps state trace state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      StoreExtends stty stty' /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros state tout stty trace state' HWT HSteps.
  revert tout stty HWT.
  induction HSteps as [state | state label state1 trace state2 HStep HSteps IH];
    intros tout stty HWT.
  - exists stty.
    split; [exact HWT |].
    split; [apply StoreExtends_refl | apply TcPhi_nil].
  - destruct
      (WTStateRuntimeHeapShapeAt_step_preservation
        state tout stty label state1 HWT HStep)
      as (stty1 & HWT1 & _ & _ & HExt1).
    destruct (IH tout stty1 HWT1) as (stty2 & HWT2 & HExt2 & HTcTrace).
    pose proof
      (WTStateRuntimeHeapShapeAt_step_label_typed
        state tout stty label state1 tout stty1 HWT HStep HWT1)
      as HTcLabel1.
    pose proof
      (TcPhi_weaken
        stty1 stty2 (trace_as_phi (label_trace label))
        HExt2 HTcLabel1)
      as HTcLabel2.
    exists stty2.
    split; [exact HWT2 |].
    split; [eapply StoreExtends_trans; eauto |].
    apply TcPhi_trace_as_phi_app; assumption.
Qed.

Lemma WTStateRuntimeHeapShapeAt_initial :
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    WTStateRuntimeHeapShapeAt
      (initial_state heap env rho e) (subst_rho rho t) stty.
Proof.
  intros heap env rho e stty ctxt rgns t eff
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp.
  unfold initial_state.
  eapply WTSRHSA_Eval with (ctxt := ctxt) (rgns := rgns) (t := t)
    (eff := eff); eauto.
  constructor.
Qed.

Theorem initial_state_steps_trace_typed :
  forall heap env rho e stty ctxt rgns t eff trace state',
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    Steps (initial_state heap env rho e) trace state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' (subst_rho rho t) stty' /\
      StoreExtends stty stty' /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros heap env rho e stty ctxt rgns t eff trace state'
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps.
  eapply WTStateRuntimeHeapShapeAt_steps_trace_typed; eauto.
  eapply WTStateRuntimeHeapShapeAt_initial; eauto.
Qed.

Theorem WTStateRuntimeHeapShapeAt_steps_safety_with_trace :
  PairParCheckDecidable ->
  forall state tout stty trace state',
    WTStateRuntimeHeapShapeAt state tout stty ->
    Steps state trace state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      StoreExtends stty stty' /\
      NotStuck state' /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros HDec state tout stty trace state' HWT HSteps.
  destruct
    (WTStateRuntimeHeapShapeAt_steps_trace_typed
      state tout stty trace state' HWT HSteps)
    as (stty' & HWT' & HExt & HTcTrace).
  assert (HReady' : StateEvalHeadRegionsResolved state').
  {
    eapply WTStateRuntimeHeapShapeAt_eval_heads_resolved; eauto.
  }
  assert (HNotStuck' : NotStuck state').
  {
    eapply WTStateRuntimeHeapShape_not_stuck; eauto.
    eapply WTStateRuntimeHeapShapeAt_forget; eauto.
  }
  exists stty'. split; [exact HWT' |].
  split; [exact HExt |].
  split; [exact HNotStuck' | exact HTcTrace].
Qed.

Theorem initial_state_steps_safety_with_trace :
  PairParCheckDecidable ->
  forall heap env rho e stty ctxt rgns t eff trace state',
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    Steps (initial_state heap env rho e) trace state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' (subst_rho rho t) stty' /\
      StoreExtends stty stty' /\
      NotStuck state' /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros HDec heap env rho e stty ctxt rgns t eff trace state'
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps.
  eapply WTStateRuntimeHeapShapeAt_steps_safety_with_trace; eauto.
  eapply WTStateRuntimeHeapShapeAt_initial; eauto.
Qed.

Definition StateTraceSafeAt (state : State) (tout : Tau) (stty : Sigma) : Prop :=
  forall trace state',
    Steps state trace state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      StoreExtends stty stty' /\
      NotStuck state' /\
      TcPhi stty' (trace_as_phi trace).

Theorem WTStateRuntimeHeapShapeAt_trace_safe_typed :
  PairParCheckDecidable ->
  forall state tout stty,
    WTStateRuntimeHeapShapeAt state tout stty ->
    StateTraceSafeAt state tout stty.
Proof.
  intros HDec state tout stty HWT trace state' HSteps.
  eapply WTStateRuntimeHeapShapeAt_steps_safety_with_trace; eauto.
Qed.

Theorem initial_state_trace_safe_typed :
  PairParCheckDecidable ->
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    StateTraceSafeAt (initial_state heap env rho e) (subst_rho rho t) stty.
Proof.
  intros HDec heap env rho e stty ctxt rgns t eff
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp.
  eapply WTStateRuntimeHeapShapeAt_trace_safe_typed; eauto.
  eapply WTStateRuntimeHeapShapeAt_initial; eauto.
Qed.

Definition StateNeverStuck (state : State) : Prop :=
  forall trace state',
    Steps state trace state' ->
    NotStuck state'.

Theorem WTStateRuntimeHeapShapeAt_never_stuck_typed :
  PairParCheckDecidable ->
  forall state tout stty,
    WTStateRuntimeHeapShapeAt state tout stty ->
    StateNeverStuck state.
Proof.
  intros HDec state tout stty HWT trace state' HSteps.
  destruct
    (WTStateRuntimeHeapShapeAt_steps_safety_with_trace
      HDec state tout stty trace state' HWT HSteps)
    as (_ & _ & _ & HNotStuck & _).
  exact HNotStuck.
Qed.

Theorem initial_state_never_stuck_typed :
  PairParCheckDecidable ->
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    StateNeverStuck (initial_state heap env rho e).
Proof.
  intros HDec heap env rho e stty ctxt rgns t eff
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp.
  eapply WTStateRuntimeHeapShapeAt_never_stuck_typed; eauto.
  eapply WTStateRuntimeHeapShapeAt_initial; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_done_value :
  forall heap v tout stty,
    WTStateRuntimeHeapShapeAt (StDone heap v) tout stty ->
    TcHeap (heap, stty) /\
    RuntimeHeapShape heap stty /\
    TcVal (stty, v, tout) /\
    RuntimeValShape stty tout v.
Proof.
  intros heap v tout stty HWT.
  dependent destruction HWT.
  split; [exact H |].
  split; [exact H0 |].
  split; [exact H1 | exact H2].
Qed.

Theorem initial_state_terminal_value_with_trace :
  forall heap env rho e stty ctxt rgns t eff trace heap' v,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    Steps (initial_state heap env rho e) trace (StDone heap' v) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, subst_rho rho t) /\
      RuntimeValShape stty' (subst_rho rho t) v /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros heap env rho e stty ctxt rgns t eff trace heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps.
  destruct
    (initial_state_steps_trace_typed
      heap env rho e stty ctxt rgns t eff trace (StDone heap' v)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps)
    as (stty' & HWT' & HExt & HTcTrace).
  destruct
    (WTStateRuntimeHeapShapeAt_done_value heap' v (subst_rho rho t) stty' HWT')
    as (HTcHeap' & HHeapShape' & HTcVal' & HValShape').
  exists stty'. split; [exact HExt |].
  split; [exact HTcHeap' |].
  split; [exact HHeapShape' |].
  split; [exact HTcVal' |].
  split; [exact HValShape' | exact HTcTrace].
Qed.

Lemma WTPairParStateRuntimeHeapShapeAtStrong_step_label_typed :
  forall state tout stty label state' stty',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParStep state label state' ->
    WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' ->
    TcPhi stty' (trace_as_phi (label_trace label)).
Proof.
  intros state tout stty label state' stty' HWT HStep HWT'.
  dependent destruction HStep.
  - dependent destruction HWT.
    dependent destruction HWT'.
    match goal with
    | HState : WTStateRuntimeHeapShapeAt ?inner ?tout stty,
      HInnerStep : Step _ _ _,
      HStateOut : WTStateRuntimeHeapShapeAt _ _ _ |- _ =>
        eapply WTStateRuntimeHeapShapeAt_step_label_typed;
          [exact HState | exact HInnerStep | exact HStateOut]
    end.
  - dependent destruction HWT.
    dependent destruction HWT'.
    match goal with
    | HLeft : WTStateRuntimeHeapShapeAt ?left ?tleft stty,
      HLeftOut : WTStateRuntimeHeapShapeAt _ _ _ |- _ =>
        match goal with
        | HLeftStep : Step _ _ _ |- _ =>
            eapply WTStateRuntimeHeapShapeAt_step_label_typed;
              [exact HLeft | exact HLeftStep | exact HLeftOut]
        end
    end.
  - dependent destruction HWT.
    dependent destruction HWT'.
    match goal with
    | HRight : WTStateRuntimeHeapShapeAt ?right ?tright stty,
      HRightOut : WTStateRuntimeHeapShapeAt _ _ _ |- _ =>
        match goal with
        | HRightStep : Step _ _ _ |- _ =>
            eapply WTStateRuntimeHeapShapeAt_step_label_typed;
              [exact HRight | exact HRightStep | exact HRightOut]
        end
    end.
  - simpl. apply TcPhi_nil.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_steps_trace_typed :
  forall state tout stty trace state',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParSteps state trace state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' /\
      StoreExtends stty stty' /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros state tout stty trace state' HWT HSteps.
  revert tout stty HWT.
  induction HSteps as [state | state label state1 trace state2 HStep HSteps IH];
    intros tout stty HWT.
  - exists stty.
    split; [exact HWT |].
    split; [apply StoreExtends_refl | apply TcPhi_nil].
  - destruct
      (WTPairParStateRuntimeHeapShapeAtStrong_step_preservation
        state tout stty label state1 HWT HStep)
      as (stty1 & HWT1 & HExt1).
    destruct (IH tout stty1 HWT1) as (stty2 & HWT2 & HExt2 & HTcTrace).
    pose proof
      (WTPairParStateRuntimeHeapShapeAtStrong_step_label_typed
        state tout stty label state1 stty1 HWT HStep HWT1)
      as HTcLabel1.
    pose proof
      (TcPhi_weaken
        stty1 stty2 (trace_as_phi (label_trace label))
        HExt2 HTcLabel1)
      as HTcLabel2.
    exists stty2.
    split; [exact HWT2 |].
    split; [eapply StoreExtends_trans; eauto |].
    apply TcPhi_trace_as_phi_app; assumption.
Qed.

Definition PairParTraceSafeAt
    (state : PairParState) (tout : Tau) (stty : Sigma) : Prop :=
  forall trace state',
    PairParSteps state trace state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' /\
      StoreExtends stty stty' /\
      PairParRunHeapsAgree state' /\
      PairParNotStuck state' /\
      TcPhi stty' (trace_as_phi trace).

Theorem WTPairParStateRuntimeHeapShapeAtStrong_trace_safe_typed :
  PairParCheckDecidable ->
  forall state tout stty,
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParRunHeapsAgree state ->
    PairParTraceSafeAt state tout stty.
Proof.
  intros HDec state tout stty HWT HAgree trace state' HSteps.
  destruct
    (WTPairParStateRuntimeHeapShapeAtStrong_steps_trace_typed
      state tout stty trace state' HWT HSteps)
    as (stty' & HWT' & HExt & HTcTrace).
  assert (HAgree' : PairParRunHeapsAgree state').
  {
    eapply pairpar_steps_preserve_heap_agreement; eauto.
  }
  pose proof
    (WTPairParStateRuntimeHeapShapeAtStrong_never_stuck_typed
      HDec state tout stty HWT HAgree)
    as HNeverStuck.
  exists stty'. split; [exact HWT' |].
  split; [exact HExt |].
  split; [exact HAgree' |].
  split; [exact (HNeverStuck trace state' HSteps) | exact HTcTrace].
Qed.

Theorem pairpar_checked_initial_steps_trace_typed :
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
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout trace state'
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont HSteps.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_steps_trace_typed; eauto.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_checked_initial; eauto.
Qed.

Theorem pairpar_checked_initial_trace_safe_typed :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    PairParTraceSafeAt
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 k)
      tout stty.
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_trace_safe_typed; eauto.
  - eapply WTPairParStateRuntimeHeapShapeAtStrong_checked_initial; eauto.
  - apply pairpar_checked_initial_heaps_agree.
Qed.

Theorem pairpar_checked_initial_kdone_trace_safe_typed :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    ty1 ty2 eff1 eff2,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    PairParTraceSafeAt
      (pairpar_checked_initial heap env rho ef1 ea1 ef2 ea2 KDone)
      (subst_rho rho (Ty_Pair ty1 ty2)) stty.
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    ty1 ty2 eff1 eff2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2.
  eapply
    (pairpar_checked_initial_trace_safe_typed
      HDec heap env rho ef1 ea1 ef2 ea2 KDone stty ctxt rgns
      ty1 ty2 eff1 eff2 (subst_rho rho (Ty_Pair ty1 ty2))); eauto.
  constructor.
Qed.

Theorem pairpar_checked_initial_steps_safety_with_trace :
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
      PairParNotStuck state' /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout trace state'
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont HSteps.
  destruct
    (pairpar_checked_initial_steps_trace_typed
      heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
      ty1 ty2 eff1 eff2 tout trace state'
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcExp1 HTcExp2 HKont HSteps)
    as (stty' & HWT' & HExt & HTcTrace).
  assert (HAgree' : PairParRunHeapsAgree state').
  {
    eapply pairpar_steps_preserve_heap_agreement; eauto.
    apply pairpar_checked_initial_heaps_agree.
  }
  pose proof
    (pairpar_checked_initial_never_stuck_typed
      HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
      ty1 ty2 eff1 eff2 tout
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcExp1 HTcExp2 HKont)
    as HNeverStuck.
  exists stty'. split; [exact HWT' |].
  split; [exact HExt |].
  split; [exact HAgree' |].
  split; [exact (HNeverStuck trace state' HSteps) | exact HTcTrace].
Qed.

Theorem pairpar_checked_initial_kdone_steps_safety_with_trace :
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
      PairParNotStuck state' /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    ty1 ty2 eff1 eff2 trace state'
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HSteps.
  eapply
    (pairpar_checked_initial_steps_safety_with_trace
      HDec heap env rho ef1 ea1 ef2 ea2 KDone stty ctxt rgns
      ty1 ty2 eff1 eff2 (subst_rho rho (Ty_Pair ty1 ty2))
      trace state'); eauto.
  constructor.
Qed.

Theorem pairpar_checked_initial_terminal_value_with_trace :
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
      RuntimeValShape stty' tout v /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout trace heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont HSteps.
  destruct
    (pairpar_checked_initial_steps_trace_typed
      heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
      ty1 ty2 eff1 eff2 tout trace (PPS_State (StDone heap' v))
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcExp1 HTcExp2 HKont HSteps)
    as (stty' & HWT' & HExt & HTcTrace).
  destruct
    (WTPairParStateRuntimeHeapShapeAtStrong_done_value
      heap' v tout stty' HWT')
    as (HTcHeap' & HHeapShape' & HTcVal' & HValShape').
  exists stty'. split; [exact HExt |].
  split; [exact HTcHeap' |].
  split; [exact HHeapShape' |].
  split; [exact HTcVal' |].
  split; [exact HValShape' | exact HTcTrace].
Qed.

Theorem pairpar_checked_initial_kdone_terminal_value_with_trace :
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
      RuntimeValShape stty' (subst_rho rho (Ty_Pair ty1 ty2)) v /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    ty1 ty2 eff1 eff2 trace heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HSteps.
  eapply
    (pairpar_checked_initial_terminal_value_with_trace
      heap env rho ef1 ea1 ef2 ea2 KDone stty ctxt rgns
      ty1 ty2 eff1 eff2 (subst_rho rho (Ty_Pair ty1 ty2))
      trace heap' v); eauto.
  constructor.
Qed.

Theorem pairpar_checked_initial_kdone_terminal_pair_with_trace :
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
      RuntimeValShape stty' (subst_rho rho ty2) v2 /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    ty1 ty2 eff1 eff2 trace heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HSteps.
  destruct
    (pairpar_checked_initial_kdone_terminal_value_with_trace
      heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
      ty1 ty2 eff1 eff2 trace heap' v
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcExp1 HTcExp2 HSteps)
    as (stty' & HExt & HTcHeap' & HHeapShape' & HTcVal' & HValShape' &
        HTcTrace).
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
  split; [exact HTcVal2 |].
  split; [exact HValShape2 | exact HTcTrace].
Qed.
