From stdpp Require Import gmap.
From Stdlib Require Import Program.Equality.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepPreservationTheorems.
Require Import theories.Runtime.SmallStepExplicitStoreBase.
Require Import theories.Runtime.SmallStepExplicitStoreHeap.
Require Import theories.Runtime.SmallStepExplicitStoreTheorems.
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

Require Import theories.Runtime.SmallStepParallelPreservationBase.

Inductive WTPairParStateRuntimeHeapShapeAt :
    PairParState -> Tau -> Sigma -> Prop :=
	| WTPPRSA_State :
	    forall state tout stty,
	      NonPairParRunState state ->
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
	      NonPairParRunState state ->
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

Inductive WTPairParStateRuntimeHeapShape : PairParState -> Tau -> Prop :=
	| WTPPRS_State :
	    forall state tout,
	      NonPairParRunState state ->
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
	  - constructor; eauto.
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
