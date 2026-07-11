Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepProgress.
Require Import theories.Runtime.SmallStepPreservation.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
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
