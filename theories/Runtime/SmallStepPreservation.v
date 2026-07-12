From stdpp Require Import gmap.
From Stdlib Require Import Sets.Ensembles.

Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepTyping.
Require Import theories.Runtime.SmallStepProgress.
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

Definition RuntimeHeapShape (heap : Heap) (stty : Sigma) : Prop :=
  forall k v t,
    find_H k heap = Some v ->
    find_ST k stty = Some t ->
    RuntimeValShape stty t v.

Lemma RuntimeHeapShape_update_existing :
  forall heap stty k v t,
    RuntimeHeapShape heap stty ->
    RuntimeValShape stty t v ->
    find_ST k stty = Some t ->
    RuntimeHeapShape (update_H (k, v) heap) stty.
Proof.
  intros heap stty k v t HHeapShape HShape HFindST
    k0 v0 t0 HFindH0 HFindST0.
  unfold find_H, update_H in HFindH0; simpl in HFindH0.
  apply lookup_insert_Some in HFindH0.
  destruct HFindH0 as [[HKey HVal] | [HNe HFindHOld]].
  - inversion HKey; subst k0.
    inversion HVal; subst v0.
    pose proof (PairType_unique_type stty k t0 t HFindST0 HFindST) as HTy.
    subst. assumption.
  - eapply HHeapShape; eauto.
Qed.

Lemma RuntimeHeapShape_update_fresh :
  forall heap stty k v t,
    RuntimeHeapShape heap stty ->
    RuntimeValShape stty t v ->
    find_ST k stty = None ->
    RuntimeHeapShape (update_H (k, v) heap) (update_ST k t stty).
Proof.
  intros heap stty k v t HHeapShape HShape HFresh
    k0 v0 t0 HFindH0 HFindST0.
  assert (HExt : forall k' t',
    find_ST k' stty = Some t' ->
    find_ST k' (update_ST k t stty) = Some t').
  {
    intros k' t' HFindST.
    unfold find_ST, update_ST in *.
    destruct (decide (k' = k)); subst.
    - rewrite HFresh in HFindST. discriminate.
    - eapply G_diff_keys_2; eauto.
  }
  unfold find_H, update_H in HFindH0; simpl in HFindH0.
  unfold find_ST, update_ST in HFindST0.
  apply lookup_insert_Some in HFindH0.
  apply lookup_insert_Some in HFindST0.
  destruct HFindH0 as [[HKeyH HVal] | [HNeH HFindHOld]];
  destruct HFindST0 as [[HKeyST HTy] | [HNeST HFindSTOld]]; subst.
  - eapply RuntimeValShape_store_ext; eauto.
  - contradiction.
  - contradiction.
  - eapply RuntimeValShape_store_ext; eauto.
Qed.

Inductive WTKontRuntime : Sigma -> Tau -> Tau -> Kont -> Prop :=
| WTKR_Done :
    forall stty t,
      WTKontRuntime stty t t KDone
| WTKR_MuAppFun :
    forall stty ea env rho k ctxt rgns tya effa effc tyc effe tout,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, ea, tya, effa) ->
      WTKontRuntime stty (subst_rho rho tyc) tout k ->
      WTKontRuntime stty
        (subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))
        tout
        (KMuAppFun ea env rho k)
| WTKR_MuAppArg :
    forall stty env rho f x ec ee k ctxt rgns tya effc tyc effe tout,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcInc
        (update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya)
          ctxt, rgns) ->
      TcExp
        (ctxt, rgns, Mu f x ec ee,
          Ty_Arrow tya effc tyc effe Ty_Effect, Empty_Static_Action) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya) ctxt,
          rgns, ec, tyc, effc) ->
      WTKontRuntime stty (subst_rho rho tyc) tout k ->
      WTKontRuntime stty (subst_rho rho tya) tout
        (KMuAppArg env rho f x ec ee k)
| WTKR_RgnApp :
    forall stty w rho k rgns effr tyr tout,
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      WTKontRuntime stty (subst_rho rho (open (mk_rgn_type w) tyr)) tout k ->
      WTKontRuntime stty (subst_rho rho (Ty_ForallRgn effr tyr)) tout
        (KRgnApp w rho k)
| WTKR_EffAppFun :
    forall stty ea env rho k ctxt rgns tya effa effc tyc effe tout,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, ea, tya, effa) ->
      WTKontRuntime stty Ty_Effect tout k ->
      WTKontRuntime stty
        (subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))
        tout
        (KEffAppFun ea env rho k)
| WTKR_EffAppArg :
    forall stty env rho f x ec ee k ctxt rgns tya effc tyc effe tout,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcInc
        (update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya)
          ctxt, rgns) ->
      TcExp
        (ctxt, rgns, Mu f x ec ee,
          Ty_Arrow tya effc tyc effe Ty_Effect, Empty_Static_Action) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya) ctxt,
          rgns, ee, Ty_Effect, effe) ->
      WTKontRuntime stty Ty_Effect tout k ->
      WTKontRuntime stty (subst_rho rho tya) tout
        (KEffAppArg env rho f x ec ee k)
| WTKR_PairParEff1 :
    forall stty ef1 ea1 ef2 ea2 env rho k ctxt rgns
      ty1 ty2 eff1 eff2 eff3 tout,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
      TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
      TcExp (ctxt, rgns, Eff_App ef2 ea2, Ty_Effect, eff3) ->
      WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
      WTKontRuntime stty Ty_Effect tout
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)
| WTKR_PairParEff2 :
    forall stty ef1 ea1 ef2 ea2 env rho theta1 k ctxt rgns
      ty1 ty2 eff1 eff2 tout,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
      TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
      WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
      WTKontRuntime stty Ty_Effect tout
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)
| WTKR_PairParMu1 :
    forall stty ef2 ea2 env rho k ctxt rgns ty1 ty2 eff2 tout,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
      WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
      WTKontRuntime stty (subst_rho rho ty1) tout
        (KPairParMu1 ef2 ea2 env rho k)
| WTKR_PairParMu2 :
    forall stty v1 k rho ty1 ty2 tout,
      TcVal (stty, v1, subst_rho rho ty1) ->
      RuntimeValShape stty (subst_rho rho ty1) v1 ->
      WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
      WTKontRuntime stty (subst_rho rho ty2) tout
        (KPairParMu2 v1 k)
| WTKR_Cond :
    forall stty et ef env rho k ctxt rgns t efft efff tout,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, et, t, efft) ->
      TcExp (ctxt, rgns, ef, t, efff) ->
      WTKontRuntime stty (subst_rho rho t) tout k ->
      WTKontRuntime stty Ty_Boolean tout (KCond et ef env rho k)
| WTKR_Ref :
    forall stty w rho k rgns t tout s,
      w = Rgn_Const true false s ->
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      WTKontRuntime stty (subst_rho rho (Ty_Ref (mk_rgn_type w) t)) tout k ->
      WTKontRuntime stty (subst_rho rho t) tout (KRef w rho k)
| WTKR_DeRef :
    forall stty w rho k rgns t tout s,
      w = Rgn_Const true false s ->
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      WTKontRuntime stty (subst_rho rho t) tout k ->
      WTKontRuntime stty (subst_rho rho (Ty_Ref (mk_rgn_type w) t)) tout
        (KDeRef w rho k)
| WTKR_AssignLoc :
    forall stty w ev env rho k ctxt rgns t veff tout s,
      w = Rgn_Const true false s ->
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, ev, t, veff) ->
      WTKontRuntime stty Ty_Unit tout k ->
      WTKontRuntime stty (subst_rho rho (Ty_Ref (mk_rgn_type w) t)) tout
        (KAssignLoc w ev env rho k)
| WTKR_AssignVal :
    forall stty w l rho k rgns r t tout,
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      find_R w rho = Some r ->
      find_ST (r, l) stty = Some t ->
      WTKontRuntime stty Ty_Unit tout k ->
      WTKontRuntime stty t tout (KAssignVal w l rho k)
| WTKR_PlusL :
    forall stty e2 env rho k ctxt rgns eff2 tout,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
      WTKontRuntime stty Ty_Natural tout k ->
      WTKontRuntime stty Ty_Natural tout (KPlusL e2 env rho k)
| WTKR_PlusR :
    forall stty n k tout,
      WTKontRuntime stty Ty_Natural tout k ->
      WTKontRuntime stty Ty_Natural tout (KPlusR n k)
| WTKR_MinusL :
    forall stty e2 env rho k ctxt rgns eff2 tout,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
      WTKontRuntime stty Ty_Natural tout k ->
      WTKontRuntime stty Ty_Natural tout (KMinusL e2 env rho k)
| WTKR_MinusR :
    forall stty n k tout,
      WTKontRuntime stty Ty_Natural tout k ->
      WTKontRuntime stty Ty_Natural tout (KMinusR n k)
| WTKR_TimesL :
    forall stty e2 env rho k ctxt rgns eff2 tout,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
      WTKontRuntime stty Ty_Natural tout k ->
      WTKontRuntime stty Ty_Natural tout (KTimesL e2 env rho k)
| WTKR_TimesR :
    forall stty n k tout,
      WTKontRuntime stty Ty_Natural tout k ->
      WTKontRuntime stty Ty_Natural tout (KTimesR n k)
| WTKR_EqL :
    forall stty e2 env rho k ctxt rgns eff2 tout,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
      WTKontRuntime stty Ty_Boolean tout k ->
      WTKontRuntime stty Ty_Natural tout (KEqL e2 env rho k)
| WTKR_EqR :
    forall stty n k tout,
      WTKontRuntime stty Ty_Boolean tout k ->
      WTKontRuntime stty Ty_Natural tout (KEqR n k)
| WTKR_ReadConc :
    forall stty k rho r t tout,
      WTKontRuntime stty Ty_Effect tout k ->
      WTKontRuntime stty
        (subst_rho rho (Ty_Ref (Rgn_Const true true r) t))
        tout
        (KReadConc k)
| WTKR_WriteConc :
    forall stty k rho r t tout,
      WTKontRuntime stty Ty_Effect tout k ->
      WTKontRuntime stty
        (subst_rho rho (Ty_Ref (Rgn_Const true true r) t))
        tout
        (KWriteConc k)
| WTKR_ConcatL :
    forall stty e2 env rho k ctxt rgns eff2 tout,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e2, Ty_Effect, eff2) ->
      WTKontRuntime stty Ty_Effect tout k ->
      WTKontRuntime stty Ty_Effect tout (KConcatL e2 env rho k)
| WTKR_ConcatR :
    forall stty theta k tout,
      WTKontRuntime stty Ty_Effect tout k ->
      WTKontRuntime stty Ty_Effect tout (KConcatR theta k).

Lemma WTKontRuntime_store_ext :
  forall stty tin tout k,
    WTKontRuntime stty tin tout k ->
    forall stty',
      StoreExtends stty stty' ->
      WTKontRuntime stty' tin tout k.
Proof.
  intros stty tin tout k HKont.
  induction HKont; intros stty' HExt;
    try solve
      [econstructor; eauto;
        try eapply ext_stores__env; eauto;
        try eapply RuntimeEnvShape_store_ext; eauto].
  - eapply WTKR_MuAppArg with
      (ctxt := ctxt) (rgns := rgns)
      (effc := effc) (tyc := tyc) (effe := effe); eauto.
    + eapply ext_stores__env; eauto.
    + eapply RuntimeEnvShape_store_ext; eauto.
  - eapply WTKR_EffAppArg with
      (ctxt := ctxt) (rgns := rgns)
      (effc := effc) (tyc := tyc) (effe := effe); eauto.
    + eapply ext_stores__env; eauto.
    + eapply RuntimeEnvShape_store_ext; eauto.
  - eapply WTKR_PairParMu2 with (rho := rho) (ty1 := ty1) (ty2 := ty2);
      eauto.
    + eapply ext_stores__val; eauto.
    + eapply RuntimeValShape_store_ext; eauto.
Qed.

Lemma TcEnv_update_rec :
  forall stty rho env ctxt f vf x vx tf tx,
    TcEnv (stty, rho, env, ctxt) ->
    TcVal (stty, vf, subst_rho rho tf) ->
    TcVal (stty, vx, subst_rho rho tx) ->
    TcEnv (stty, rho,
      update_rec_E (f, vf) (x, vx) env,
      update_rec_T (f, tf) (x, tx) ctxt).
Proof.
  intros stty rho env ctxt f vf x vx tf tx HTcEnv HFVal HXVal.
  unfold update_rec_E, update_rec_T.
  eapply update_env; eauto.
  eapply update_env; eauto.
Qed.

Lemma RuntimeEnvShape_extended_rho :
  forall stty rho env ctxt,
    RuntimeEnvShape stty rho env ctxt ->
    forall x r rgns,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      not_set_elem rgns x ->
      RuntimeEnvShape stty (update_R (x, r) rho) env ctxt.
Proof.
  intros stty rho env ctxt HEnvShape x r rgns HTcRho HTcInc HFresh
    y v t HFindE HFindT.
  unfold update_R; simpl.
  rewrite subst_add_comm.
  - unfold subst_in_type.
    rewrite SUBST_FRESH.
    + eapply HEnvShape; eauto.
    + inversion HTcInc as [? ? HFrv]; subst.
      unfold not_set_elem, Complement in *.
      intro HIn.
      apply HFresh.
      eapply HFrv; eauto.
  - eapply map_to_list_unique with (m := <[x:=r]> rho); eauto.
  - apply not_elem_of_dom.
    eapply not_set_elem_not_in_rho; eauto.
Qed.

Lemma subst_rho_update_open_close :
  forall rho w r rho' x tyr0 tyr rgns,
    lc_type tyr0 ->
    TcRho (rho', rgns) ->
    not_set_elem rgns x ->
    find_R w rho = Some r ->
    subst_rho rho' (close_var x tyr0) = subst_rho rho tyr ->
    subst_rho (update_R (x, r) rho') tyr0 =
      subst_rho rho (open (mk_rgn_type w) tyr).
Proof.
  intros rho w r rho' x tyr0 tyr rgns Hlc HTcRho HFresh HFindR HEq.
  unfold update_R; simpl.
  rewrite subst_add_comm.
  - unfold subst_in_type.
    rewrite SUBST_AS_CLOSE_OPEN by assumption.
    eapply subst_rho_open_close; eauto.
  - eapply map_to_list_unique with (m := <[x:=r]> rho'); eauto.
  - apply not_elem_of_dom.
    eapply not_set_elem_not_in_rho; eauto.
Qed.

Lemma TcInc_extend_rgn_singleton :
  forall ctxt rgns x,
    TcInc (ctxt, rgns) ->
    TcInc (ctxt, set_union rgns (singleton_set x)).
Proof.
  intros ctxt rgns x HTcInc.
  inversion HTcInc as [? ? HFrv]; subst.
  constructor.
  intros y t HFind r HIn.
  apply Union_introl.
  eapply HFrv; eauto.
Qed.

Inductive WTStateRuntimeKontShape : State -> Tau -> Prop :=
| WTSRKS_Eval :
    forall heap env rho e k stty ctxt rgns t eff tout,
      TcHeap (heap, stty) ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e, t, eff) ->
      WTKontRuntime stty (subst_rho rho t) tout k ->
      WTStateRuntimeKontShape (StEval heap env rho e k) tout
| WTSRKS_Return :
    forall heap v k stty t tout,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      WTKontRuntime stty t tout k ->
      RuntimeValShape stty t v ->
      WTStateRuntimeKontShape (StReturn heap v k) tout
| WTSRKS_Done :
    forall heap v stty t,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      RuntimeValShape stty t v ->
      WTStateRuntimeKontShape (StDone heap v) t.

Inductive WTStateRuntimeHeapShape : State -> Tau -> Prop :=
| WTSRHS_Eval :
    forall heap env rho e k stty ctxt rgns t eff tout,
      TcHeap (heap, stty) ->
      RuntimeHeapShape heap stty ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e, t, eff) ->
      WTKontRuntime stty (subst_rho rho t) tout k ->
      WTStateRuntimeHeapShape (StEval heap env rho e k) tout
| WTSRHS_Return :
    forall heap v k stty t tout,
      TcHeap (heap, stty) ->
      RuntimeHeapShape heap stty ->
      TcVal (stty, v, t) ->
      WTKontRuntime stty t tout k ->
      RuntimeValShape stty t v ->
      WTStateRuntimeHeapShape (StReturn heap v k) tout
| WTSRHS_Done :
    forall heap v stty t,
      TcHeap (heap, stty) ->
      RuntimeHeapShape heap stty ->
      TcVal (stty, v, t) ->
      RuntimeValShape stty t v ->
      WTStateRuntimeHeapShape (StDone heap v) t.

Lemma WTStateRuntimeHeapShape_forget :
  forall state t,
    WTStateRuntimeHeapShape state t ->
    WTStateRuntimeKontShape state t.
Proof.
  intros state t HState.
  inversion HState; subst; econstructor; eauto.
Qed.

Lemma WTStateRuntimeKontShape_initial :
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    WTStateRuntimeKontShape
      (initial_state heap env rho e)
      (subst_rho rho t).
Proof.
  intros.
  unfold initial_state.
  econstructor; eauto.
  constructor.
Qed.

Lemma WTStateRuntimeHeapShape_initial :
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    WTStateRuntimeHeapShape
      (initial_state heap env rho e)
      (subst_rho rho t).
Proof.
  intros.
  unfold initial_state.
  econstructor; eauto.
  constructor.
Qed.

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

Lemma WTStateRuntimeHeapShape_const_step_preservation :
  forall heap env rho n k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (Const n) k) tout ->
    Step (StEval heap env rho (Const n) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
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
  eapply WTSRHS_Return with (t := Ty_Natural); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShape_bool_step_preservation :
  forall heap env rho b k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (Bool b) k) tout ->
    Step (StEval heap env rho (Bool b) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
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
  eapply WTSRHS_Return with (t := Ty_Boolean); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShape_var_step_preservation :
  forall heap env rho x k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (Var x) k) tout ->
    Step (StEval heap env rho (Var x) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
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
      eapply WTSRHS_Return with (t := subst_rho rho ty); eauto
  end.
Qed.

Lemma WTStateRuntimeHeapShape_mu_step_preservation :
  forall heap env rho f x ec ee k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (Mu f x ec ee) k) tout ->
    Step (StEval heap env rho (Mu f x ec ee) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
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
      eapply WTSRHS_Return
        with (t := subst_rho rho
          (Ty_Arrow tyx effc tyc effe Ty_Effect)); eauto;
      econstructor; eauto
  end.
Qed.

Lemma WTStateRuntimeHeapShape_lambda_step_preservation :
  forall heap env rho x eb k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (Lambda x eb) k) tout ->
    Step (StEval heap env rho (Lambda x eb) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
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
      eapply WTSRHS_Return
        with (t := subst_rho rho (Ty_ForallRgn effr tyr)); eauto;
      econstructor; eauto
  end.
Qed.

Lemma WTStateRuntimeHeapShape_alloc_abs_step_preservation :
  forall heap env rho w k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (AllocAbs w) k) tout ->
    Step (StEval heap env rho (AllocAbs w) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
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
  eapply WTSRHS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShape_read_abs_step_preservation :
  forall heap env rho w k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (ReadAbs w) k) tout ->
    Step (StEval heap env rho (ReadAbs w) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
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
  eapply WTSRHS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShape_write_abs_step_preservation :
  forall heap env rho w k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho (WriteAbs w) k) tout ->
    Step (StEval heap env rho (WriteAbs w) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
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
  eapply WTSRHS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShape_top_step_preservation :
  forall heap env rho k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho Top k) tout ->
    Step (StEval heap env rho Top k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
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
  eapply WTSRHS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShape_empty_step_preservation :
  forall heap env rho k tout lbl state',
    WTStateRuntimeHeapShape (StEval heap env rho Empty k) tout ->
    Step (StEval heap env rho Empty k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
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
  eapply WTSRHS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShape_done_step_preservation :
  forall heap v tout lbl state',
    WTStateRuntimeHeapShape (StReturn heap v KDone) tout ->
    Step (StReturn heap v KDone) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap v tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ KDone |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Done; eauto.
Qed.

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

Lemma WTStateRuntimeKontShape_mu_app_eval_fun_preservation :
  forall heap env rho ef ea k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (Mu_App ef ea) k) tout ->
    Step (StEval heap env rho (Mu_App ef ea) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
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
      eapply WTSRKS_Eval
        with
          (stty := stty) (ctxt := ctxt) (rgns := rgns)
          (t := Ty_Arrow tya effc tyc effe Ty_Effect) (eff := efff);
      eauto;
      eapply WTKR_MuAppFun; eauto
  end.
Qed.

Lemma WTStateRuntimeKontShape_rgn_app_eval_fun_preservation :
  forall heap env rho er w k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (Rgn_App er w) k) tout ->
    Step (StEval heap env rho (Rgn_App er w) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
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
      eapply WTSRKS_Eval
        with
          (stty := stty) (ctxt := ctxt) (rgns := rgns)
          (t := Ty_ForallRgn effr tyr) (eff := efff);
      eauto;
      eapply WTKR_RgnApp; eauto
  end.
Qed.

Lemma WTStateRuntimeKontShape_eff_app_eval_fun_preservation :
  forall heap env rho ef ea k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (Eff_App ef ea) k) tout ->
    Step (StEval heap env rho (Eff_App ef ea) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
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
      eapply WTSRKS_Eval
        with
          (stty := stty) (ctxt := ctxt) (rgns := rgns)
          (t := Ty_Arrow tya effc tyc effe Ty_Effect) (eff := efff);
      eauto;
      eapply WTKR_EffAppFun; eauto
  end.
Qed.

Lemma WTStateRuntimeKontShape_cond_eval_guard_preservation :
  forall heap env rho e et ef k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (Cond e et ef) k) tout ->
    Step (StEval heap env rho (Cond e et ef) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho e et ef k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Cond _ _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  eapply WTSRKS_Eval
    with
      (stty := stty) (ctxt := ctxt) (rgns := rgns)
      (t := Ty_Boolean);
  eauto.
  rewrite (subst_rho_boolean rho).
  eapply WTKR_Cond; eauto.
Qed.

Lemma WTStateRuntimeKontShape_ref_eval_arg_preservation :
  forall heap env rho w e k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (Ref w e) k) tout ->
    Step (StEval heap env rho (Ref w e) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho w e k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Ref _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  eapply WTSRKS_Eval with (stty := stty) (ctxt := ctxt) (rgns := rgns);
    eauto.
  eapply WTKR_Ref; eauto; try constructor.
Qed.

Lemma WTStateRuntimeKontShape_deref_eval_arg_preservation :
  forall heap env rho w e k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (DeRef w e) k) tout ->
    Step (StEval heap env rho (DeRef w e) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho w e k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, DeRef _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  eapply WTSRKS_Eval with (stty := stty) (ctxt := ctxt) (rgns := rgns);
    eauto.
  eapply WTKR_DeRef; eauto; try constructor.
Qed.

Lemma WTStateRuntimeKontShape_assign_eval_loc_preservation :
  forall heap env rho w ea ev k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (Assign w ea ev) k) tout ->
    Step (StEval heap env rho (Assign w ea ev) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
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
  eapply WTSRKS_Eval with (stty := stty) (ctxt := ctxt) (rgns := rgns);
    eauto.
  eapply WTKR_AssignLoc; eauto; try constructor.
Qed.

Lemma WTStateRuntimeKontShape_plus_eval_left_preservation :
  forall heap env rho e1 e2 k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (Plus e1 e2) k) tout ->
    Step (StEval heap env rho (Plus e1 e2) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
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
  eapply WTSRKS_Eval
    with (stty := stty) (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural);
    eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_PlusL; eauto.
Qed.

Lemma WTStateRuntimeKontShape_minus_eval_left_preservation :
  forall heap env rho e1 e2 k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (Minus e1 e2) k) tout ->
    Step (StEval heap env rho (Minus e1 e2) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
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
  eapply WTSRKS_Eval
    with (stty := stty) (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural);
    eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_MinusL; eauto.
Qed.

Lemma WTStateRuntimeKontShape_times_eval_left_preservation :
  forall heap env rho e1 e2 k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (Times e1 e2) k) tout ->
    Step (StEval heap env rho (Times e1 e2) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
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
  eapply WTSRKS_Eval
    with (stty := stty) (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural);
    eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_TimesL; eauto.
Qed.

Lemma WTStateRuntimeKontShape_eq_eval_left_preservation :
  forall heap env rho e1 e2 k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (Eq e1 e2) k) tout ->
    Step (StEval heap env rho (Eq e1 e2) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
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
  eapply WTSRKS_Eval
    with (stty := stty) (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural);
    eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_EqL; eauto.
Qed.

Lemma WTStateRuntimeKontShape_read_conc_eval_arg_preservation :
  forall heap env rho e k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (ReadConc e) k) tout ->
    Step (StEval heap env rho (ReadConc e) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
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
  eapply WTSRKS_Eval with (stty := stty) (ctxt := ctxt) (rgns := rgns);
    eauto.
  eapply WTKR_ReadConc; eauto.
Qed.

Lemma WTStateRuntimeKontShape_write_conc_eval_arg_preservation :
  forall heap env rho e k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (WriteConc e) k) tout ->
    Step (StEval heap env rho (WriteConc e) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
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
  eapply WTSRKS_Eval with (stty := stty) (ctxt := ctxt) (rgns := rgns);
    eauto.
  eapply WTKR_WriteConc; eauto.
Qed.

Lemma WTStateRuntimeKontShape_concat_eval_left_preservation :
  forall heap env rho e1 e2 k tout lbl state',
    WTStateRuntimeKontShape (StEval heap env rho (Concat e1 e2) k) tout ->
    Step (StEval heap env rho (Concat e1 e2) k) lbl state' ->
    WTStateRuntimeKontShape state' tout.
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
  eapply WTSRKS_Eval
    with (stty := stty) (ctxt := ctxt) (rgns := rgns) (t := Ty_Effect);
    eauto.
  rewrite (subst_rho_effect rho).
  eapply WTKR_ConcatL; eauto.
Qed.

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

Lemma WTStateRuntimeKontShape_cond_true_preservation :
  forall heap env rho et ef k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Bit true) (KCond et ef env rho k)) tout ->
    Step (StReturn heap (Bit true) (KCond et ef env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho et ef k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KCond _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Eval; eauto.
Qed.

Lemma WTStateRuntimeKontShape_cond_false_preservation :
  forall heap env rho et ef k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Bit false) (KCond et ef env rho k)) tout ->
    Step (StReturn heap (Bit false) (KCond et ef env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho et ef k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KCond _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Eval; eauto.
Qed.

Lemma WTStateRuntimeKontShape_plus_eval_right_preservation :
  forall heap env rho e2 n k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Num n) (KPlusL e2 env rho k)) tout ->
    Step (StReturn heap (Num n) (KPlusL e2 env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho e2 n k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPlusL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Eval with (t := Ty_Natural); eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_PlusR; eauto.
Qed.

Lemma WTStateRuntimeKontShape_plus_done_preservation :
  forall heap n1 n2 k tout lbl state',
    WTStateRuntimeKontShape (StReturn heap (Num n2) (KPlusR n1 k)) tout ->
    Step (StReturn heap (Num n2) (KPlusR n1 k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap n1 n2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPlusR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Return with (t := Ty_Natural); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_minus_eval_right_preservation :
  forall heap env rho e2 n k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Num n) (KMinusL e2 env rho k)) tout ->
    Step (StReturn heap (Num n) (KMinusL e2 env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho e2 n k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KMinusL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Eval with (t := Ty_Natural); eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_MinusR; eauto.
Qed.

Lemma WTStateRuntimeKontShape_minus_done_preservation :
  forall heap n1 n2 k tout lbl state',
    WTStateRuntimeKontShape (StReturn heap (Num n2) (KMinusR n1 k)) tout ->
    Step (StReturn heap (Num n2) (KMinusR n1 k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap n1 n2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KMinusR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Return with (t := Ty_Natural); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_times_eval_right_preservation :
  forall heap env rho e2 n k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Num n) (KTimesL e2 env rho k)) tout ->
    Step (StReturn heap (Num n) (KTimesL e2 env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho e2 n k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KTimesL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Eval with (t := Ty_Natural); eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_TimesR; eauto.
Qed.

Lemma WTStateRuntimeKontShape_times_done_preservation :
  forall heap n1 n2 k tout lbl state',
    WTStateRuntimeKontShape (StReturn heap (Num n2) (KTimesR n1 k)) tout ->
    Step (StReturn heap (Num n2) (KTimesR n1 k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap n1 n2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KTimesR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Return with (t := Ty_Natural); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_eq_eval_right_preservation :
  forall heap env rho e2 n k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Num n) (KEqL e2 env rho k)) tout ->
    Step (StReturn heap (Num n) (KEqL e2 env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho e2 n k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KEqL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Eval with (t := Ty_Natural); eauto.
  rewrite (subst_rho_natural rho).
  eapply WTKR_EqR; eauto.
Qed.

Lemma WTStateRuntimeKontShape_eq_done_preservation :
  forall heap n1 n2 k tout lbl state',
    WTStateRuntimeKontShape (StReturn heap (Num n2) (KEqR n1 k)) tout ->
    Step (StReturn heap (Num n2) (KEqR n1 k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap n1 n2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KEqR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Return with (t := Ty_Boolean); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_read_conc_done_preservation :
  forall heap r l k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Loc (Rgn_Const true false r) l) (KReadConc k)) tout ->
    Step (StReturn heap (Loc (Rgn_Const true false r) l) (KReadConc k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap r l k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KReadConc _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_write_conc_done_preservation :
  forall heap r l k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Loc (Rgn_Const true false r) l) (KWriteConc k)) tout ->
    Step (StReturn heap (Loc (Rgn_Const true false r) l) (KWriteConc k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap r l k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KWriteConc _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_concat_eval_right_preservation :
  forall heap env rho e2 theta k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Eff theta) (KConcatL e2 env rho k)) tout ->
    Step (StReturn heap (Eff theta) (KConcatL e2 env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho e2 theta k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KConcatL _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Eval with (t := Ty_Effect); eauto.
  rewrite (subst_rho_effect rho).
  eapply WTKR_ConcatR; eauto.
Qed.

Lemma WTStateRuntimeKontShape_concat_done_preservation :
  forall heap theta1 theta2 k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Eff theta2) (KConcatR theta1 k)) tout ->
    Step (StReturn heap (Eff theta2) (KConcatR theta1 k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap theta1 theta2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KConcatR _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRKS_Return with (t := Ty_Effect); eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_mu_app_eval_arg_preservation :
  forall heap env rho k ea env' rho' f x ec ee tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KMuAppFun ea env rho k)) tout ->
    Step
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KMuAppFun ea env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho k ea env' rho' f x ec ee tout lbl state' HState HStep.
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
  eapply WTSRKS_Eval; eauto.
  rewrite HArgEq.
  eapply WTKR_MuAppArg; eauto.
  - inversion HTcIncCl as [? ? HFrvCl]; subst.
    eapply ExtendedTcInv_2; eauto;
      eapply HFrvCl; eauto.
  - rewrite <- HResultEq.
    eauto.
Qed.

Lemma WTStateRuntimeKontShape_eff_app_eval_arg_preservation :
  forall heap env rho k ea env' rho' f x ec ee tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KEffAppFun ea env rho k)) tout ->
    Step
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KEffAppFun ea env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho k ea env' rho' f x ec ee tout lbl state' HState HStep.
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
  eapply WTSRKS_Eval; eauto.
  rewrite HArgEq.
  eapply WTKR_EffAppArg; eauto.
  inversion HTcIncCl as [? ? HFrvCl]; subst.
  eapply ExtendedTcInv_2; eauto;
    eapply HFrvCl; eauto.
Qed.

Lemma WTStateRuntimeKontShape_assign_eval_val_preservation :
  forall heap env rho w ev l k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Loc w l) (KAssignLoc w ev env rho k)) tout ->
    Step (StReturn heap (Loc w l) (KAssignLoc w ev env rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
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
  eapply WTSRKS_Eval; eauto.
  eapply WTKR_AssignVal with (r := s); eauto.
Qed.

Lemma WTStateRuntimeKontShape_assign_done_preservation :
  forall heap rho w l v k tout lbl state',
    WTStateRuntimeKontShape (StReturn heap v (KAssignVal w l rho k)) tout ->
    Step (StReturn heap v (KAssignVal w l rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap rho w l v k tout lbl state' HState HStep.
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
  eapply WTSRKS_Return with (t := Ty_Unit); eauto.
  - eapply H_update_heap_exists; eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeKontShape_ref_done_preservation :
  forall heap rho w v k tout lbl state',
    WTStateRuntimeKontShape (StReturn heap v (KRef w rho k)) tout ->
    Step (StReturn heap v (KRef w rho k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap rho w v k tout lbl state' HState HStep.
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
  eapply WTSRKS_Return
    with
      (stty := update_ST (r, allocate_H heap r) (subst_rho rho t0) stty)
      (t := Ty_Ref (Rgn_Const true true r) (subst_rho rho t0)).
  - eapply H_update_heap_fresh; eauto.
  - constructor.
    + unfold find_ST, update_ST.
      apply lookup_insert.
    + intros rgn.
      eapply TcVal_implies_closed; eauto.
  - match goal with
    | HKont : WTKontRuntime stty
        (subst_rho rho (Ty_Ref (mk_rgn_type (Rgn_Const true false r)) ?ty))
        tout k |- _ =>
        simpl in HKont;
        rewrite subst_rho_ref_const in HKont;
        eapply WTKontRuntime_store_ext;
        [ exact HKont
        | apply StoreExtends_update_fresh; exact HFreshST ]
    end.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShape_deref_done_preservation :
  forall heap rho w l k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Loc w l) (KDeRef w rho k)) tout ->
    Step (StReturn heap (Loc w l) (KDeRef w rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap rho w l k tout lbl state' HState HStep.
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
  eapply WTSRHS_Return with (t := subst_rho rho t0); eauto.
Qed.

Lemma WTStateRuntimeHeapShape_assign_done_preservation :
  forall heap rho w l v k tout lbl state',
    WTStateRuntimeHeapShape (StReturn heap v (KAssignVal w l rho k)) tout ->
    Step (StReturn heap v (KAssignVal w l rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap rho w l v k tout lbl state' HState HStep.
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
  eapply WTSRHS_Return with (t := Ty_Unit); eauto.
  - eapply H_update_heap_exists; eauto.
  - eapply RuntimeHeapShape_update_existing; eauto.
  - constructor.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShape_ref_done_preservation :
  forall heap rho w v k tout lbl state',
    WTStateRuntimeHeapShape (StReturn heap v (KRef w rho k)) tout ->
    Step (StReturn heap v (KRef w rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap rho w v k tout lbl state' HState HStep.
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
  eapply WTSRHS_Return
    with
      (stty := update_ST (r, allocate_H heap r) (subst_rho rho t0) stty)
      (t := Ty_Ref (Rgn_Const true true r) (subst_rho rho t0)).
  - eapply H_update_heap_fresh; eauto.
  - eapply RuntimeHeapShape_update_fresh; eauto.
  - constructor.
    + unfold find_ST, update_ST.
      apply lookup_insert.
    + intros rgn.
      eapply TcVal_implies_closed; eauto.
  - match goal with
    | HKont : WTKontRuntime stty
        (subst_rho rho (Ty_Ref (mk_rgn_type (Rgn_Const true false r)) ?ty))
        tout k |- _ =>
        simpl in HKont;
        rewrite subst_rho_ref_const in HKont;
        eapply WTKontRuntime_store_ext;
        [ exact HKont
        | apply StoreExtends_update_fresh; exact HFreshST ]
    end.
  - constructor.
Qed.

Lemma WTStateRuntimeHeapShape_mu_app_eval_arg_preservation :
  forall heap env rho k ea env' rho' f x ec ee tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KMuAppFun ea env rho k)) tout ->
    Step
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KMuAppFun ea env rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho k ea env' rho' f x ec ee tout lbl state' HState HStep.
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
  eapply WTSRHS_Eval; eauto.
  rewrite HArgEq.
  eapply WTKR_MuAppArg; eauto.
  - inversion HTcIncCl as [? ? HFrvCl]; subst.
    eapply ExtendedTcInv_2; eauto;
      eapply HFrvCl; eauto.
  - rewrite <- HResultEq.
    eauto.
Qed.

Lemma WTStateRuntimeHeapShape_eff_app_eval_arg_preservation :
  forall heap env rho k ea env' rho' f x ec ee tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KEffAppFun ea env rho k)) tout ->
    Step
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KEffAppFun ea env rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho k ea env' rho' f x ec ee tout lbl state' HState HStep.
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
  eapply WTSRHS_Eval; eauto.
  rewrite HArgEq.
  eapply WTKR_EffAppArg; eauto.
  inversion HTcIncCl as [? ? HFrvCl]; subst.
  eapply ExtendedTcInv_2; eauto;
    eapply HFrvCl; eauto.
Qed.

Lemma WTStateRuntimeKontShape_mu_app_body_preservation :
  forall heap env rho f x ec ee v k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap v (KMuAppArg env rho f x ec ee k)) tout ->
    Step
      (StReturn heap v (KMuAppArg env rho f x ec ee k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho f x ec ee v k tout lbl state' HState HStep.
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
  eapply WTSRKS_Eval
    with
      (stty := stty)
      (ctxt :=
        update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya)
          ctxt)
      (rgns := rgns)
      (t := tyc)
      (eff := effc); eauto.
  - eapply TcEnv_update_rec; eauto.
  - eapply RuntimeEnvShape_update_rec; eauto.
Qed.

Lemma WTStateRuntimeKontShape_eff_app_body_preservation :
  forall heap env rho f x ec ee v k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap v (KEffAppArg env rho f x ec ee k)) tout ->
    Step
      (StReturn heap v (KEffAppArg env rho f x ec ee k)) lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap env rho f x ec ee v k tout lbl state' HState HStep.
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
  eapply WTSRKS_Eval
    with
      (stty := stty)
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

Lemma WTStateRuntimeHeapShape_mu_app_body_preservation :
  forall heap env rho f x ec ee v k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap v (KMuAppArg env rho f x ec ee k)) tout ->
    Step
      (StReturn heap v (KMuAppArg env rho f x ec ee k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho f x ec ee v k tout lbl state' HState HStep.
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
  eapply WTSRHS_Eval
    with
      (stty := stty)
      (ctxt :=
        update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya)
          ctxt)
      (rgns := rgns)
      (t := tyc)
      (eff := effc); eauto.
  - eapply TcEnv_update_rec; eauto.
  - eapply RuntimeEnvShape_update_rec; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_eff_app_body_preservation :
  forall heap env rho f x ec ee v k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap v (KEffAppArg env rho f x ec ee k)) tout ->
    Step
      (StReturn heap v (KEffAppArg env rho f x ec ee k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho f x ec ee v k tout lbl state' HState HStep.
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
  eapply WTSRHS_Eval
    with
      (stty := stty)
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

Lemma WTStateRuntimeKontShape_rgn_app_body_preservation :
  forall heap rho w env' rho' x eb k tout lbl state',
    WTStateRuntimeKontShape
      (StReturn heap (Cls (env', rho', Lambda x eb)) (KRgnApp w rho k)) tout ->
    Step
      (StReturn heap (Cls (env', rho', Lambda x eb)) (KRgnApp w rho k))
      lbl state' ->
    WTStateRuntimeKontShape state' tout.
Proof.
  intros heap rho w env' rho' x eb k tout lbl state' HState HStep.
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
  eapply WTSRKS_Eval
    with
      (stty := stty)
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

Lemma WTStateRuntimeHeapShape_rgn_app_body_preservation :
  forall heap rho w env' rho' x eb k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Cls (env', rho', Lambda x eb)) (KRgnApp w rho k)) tout ->
    Step
      (StReturn heap (Cls (env', rho', Lambda x eb)) (KRgnApp w rho k))
      lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap rho w env' rho' x eb k tout lbl state' HState HStep.
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
  eapply WTSRHS_Eval
    with
      (stty := stty)
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

Lemma WTStateRuntimeHeapShape_pairpar_eval_eff1_preservation :
  forall heap env rho ef1 ea1 ef2 ea2 k tout lbl state',
    WTStateRuntimeHeapShape
      (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k) tout ->
    Step (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k tout lbl state' HState HStep.
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
  eapply WTSRHS_Eval with (t := Ty_Effect); eauto.
  rewrite (subst_rho_effect rho).
  eapply WTKR_PairParEff1; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_pairpar_eval_eff2_preservation :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Eff theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)) tout ->
    Step
      (StReturn heap (Eff theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPairParEff1 _ _ _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Eval with (t := Ty_Effect); eauto.
  rewrite (subst_rho_effect rho).
  eapply WTKR_PairParEff2; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_pairpar_eval_mu1_preservation :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap (Eff theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)) tout ->
    Step
      (StReturn heap (Eff theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k tout lbl state'
    HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  - match goal with
    | HKont : WTKontRuntime _ _ _ (KPairParEff2 _ _ _ _ _ _ _ _) |- _ =>
        inversion HKont; subst
    end.
    eapply WTSRHS_Eval; eauto.
    eapply WTKR_PairParMu1; eauto.
  - match goal with
    | HKont : WTKontRuntime _ _ _ (KPairParEff2 _ _ _ _ _ _ _ _) |- _ =>
        inversion HKont; subst
    end.
    eapply WTSRHS_Eval; eauto.
    eapply WTKR_PairParMu1; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_pairpar_eval_mu2_preservation :
  forall heap env rho ef2 ea2 v1 k tout lbl state',
    WTStateRuntimeHeapShape
      (StReturn heap v1 (KPairParMu1 ef2 ea2 env rho k)) tout ->
    Step (StReturn heap v1 (KPairParMu1 ef2 ea2 env rho k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap env rho ef2 ea2 v1 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPairParMu1 _ _ _ _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Eval; eauto.
  eapply WTKR_PairParMu2; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_pairpar_done_preservation :
  forall heap v1 v2 k tout lbl state',
    WTStateRuntimeHeapShape (StReturn heap v2 (KPairParMu2 v1 k)) tout ->
    Step (StReturn heap v2 (KPairParMu2 v1 k)) lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros heap v1 v2 k tout lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontRuntime _ _ _ (KPairParMu2 _ _) |- _ =>
      inversion HKont; subst
  end.
  eapply WTSRHS_Return with (t := subst_rho rho (Ty_Pair ty1 ty2)); eauto.
  - rewrite subst_rho_pair.
    constructor; eauto.
  - rewrite subst_rho_pair.
    constructor; eauto.
Qed.

Theorem WTStateRuntimeHeapShape_step_preservation :
  forall state tout lbl state',
    WTStateRuntimeHeapShape state tout ->
    Step state lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros state tout lbl state' HState HStep.
  inversion HStep; subst; try solve
    [ eapply WTStateRuntimeHeapShape_const_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_bool_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_var_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_mu_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_lambda_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_mu_app_eval_fun_preservation; eauto
    | eapply WTStateRuntimeHeapShape_mu_app_eval_arg_preservation; eauto
    | eapply WTStateRuntimeHeapShape_mu_app_body_preservation; eauto
    | eapply WTStateRuntimeHeapShape_rgn_app_eval_fun_preservation; eauto
    | eapply WTStateRuntimeHeapShape_rgn_app_body_preservation; eauto
    | eapply WTStateRuntimeHeapShape_eff_app_eval_fun_preservation; eauto
    | eapply WTStateRuntimeHeapShape_eff_app_eval_arg_preservation; eauto
    | eapply WTStateRuntimeHeapShape_eff_app_body_preservation; eauto
    | eapply WTStateRuntimeHeapShape_pairpar_eval_eff1_preservation; eauto
    | eapply WTStateRuntimeHeapShape_pairpar_eval_eff2_preservation; eauto
    | eapply WTStateRuntimeHeapShape_pairpar_eval_mu1_preservation; eauto
    | eapply WTStateRuntimeHeapShape_pairpar_eval_mu2_preservation; eauto
    | eapply WTStateRuntimeHeapShape_pairpar_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_cond_eval_guard_preservation; eauto
    | eapply WTStateRuntimeHeapShape_cond_true_preservation; eauto
    | eapply WTStateRuntimeHeapShape_cond_false_preservation; eauto
    | eapply WTStateRuntimeHeapShape_ref_eval_arg_preservation; eauto
    | eapply WTStateRuntimeHeapShape_ref_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_deref_eval_arg_preservation; eauto
    | eapply WTStateRuntimeHeapShape_deref_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_assign_eval_loc_preservation; eauto
    | eapply WTStateRuntimeHeapShape_assign_eval_val_preservation; eauto
    | eapply WTStateRuntimeHeapShape_assign_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_plus_eval_left_preservation; eauto
    | eapply WTStateRuntimeHeapShape_plus_eval_right_preservation; eauto
    | eapply WTStateRuntimeHeapShape_plus_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_minus_eval_left_preservation; eauto
    | eapply WTStateRuntimeHeapShape_minus_eval_right_preservation; eauto
    | eapply WTStateRuntimeHeapShape_minus_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_times_eval_left_preservation; eauto
    | eapply WTStateRuntimeHeapShape_times_eval_right_preservation; eauto
    | eapply WTStateRuntimeHeapShape_times_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_eq_eval_left_preservation; eauto
    | eapply WTStateRuntimeHeapShape_eq_eval_right_preservation; eauto
    | eapply WTStateRuntimeHeapShape_eq_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_alloc_abs_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_read_abs_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_write_abs_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_read_conc_eval_arg_preservation; eauto
    | eapply WTStateRuntimeHeapShape_read_conc_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_write_conc_eval_arg_preservation; eauto
    | eapply WTStateRuntimeHeapShape_write_conc_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_concat_eval_left_preservation; eauto
    | eapply WTStateRuntimeHeapShape_concat_eval_right_preservation; eauto
    | eapply WTStateRuntimeHeapShape_concat_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_top_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_empty_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_done_step_preservation; eauto ].
Qed.

Theorem WTStateRuntimeHeapShape_steps_preservation :
  forall state tout trace state',
    WTStateRuntimeHeapShape state tout ->
    Steps state trace state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros state tout trace state' HState HSteps.
  induction HSteps.
  - assumption.
  - apply IHHSteps.
    eapply WTStateRuntimeHeapShape_step_preservation; eauto.
Qed.

Corollary WTStateRuntimeHeapShape_initial_steps_preservation :
  forall heap env rho e stty ctxt rgns t eff trace state',
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    Steps (initial_state heap env rho e) trace state' ->
    WTStateRuntimeHeapShape state' (subst_rho rho t).
Proof.
  intros heap env rho e stty ctxt rgns t eff trace state'
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps.
  eapply WTStateRuntimeHeapShape_steps_preservation; eauto.
  eapply WTStateRuntimeHeapShape_initial; eauto.
Qed.

Inductive PairParCheckState : State -> Prop :=
| PPCS_Check :
    forall heap ef1 ea1 ef2 ea2 env rho theta1 theta2 k,
      PairParCheckState
        (StReturn heap (Eff theta2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)).

Definition PairParCheckDecidable : Prop :=
  forall theta1 theta2,
    (Disjointness theta1 theta2 /\ ~ Conflictness theta1 theta2) \/
    ~ (Disjointness theta1 theta2 /\ ~ Conflictness theta1 theta2).

Lemma pairpar_check_state_ready :
  forall heap ef1 ea1 ef2 ea2 env rho theta1 theta2 k,
    Disjointness theta1 theta2 ->
    ~ Conflictness theta1 theta2 ->
    CanStep
      (StReturn heap (Eff theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)).
Proof.
  intros heap ef1 ea1 ef2 ea2 env rho theta1 theta2 k HDisj HNoConf.
  exists Silent,
    (StEval heap env rho (Mu_App ef1 ea1)
      (KPairParMu1 ef2 ea2 env rho k)).
  econstructor; eauto.
Qed.

Lemma pairpar_check_state_fallback_ready :
  forall heap ef1 ea1 ef2 ea2 env rho theta1 theta2 k,
    ~ (Disjointness theta1 theta2 /\ ~ Conflictness theta1 theta2) ->
    CanStep
      (StReturn heap (Eff theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)).
Proof.
  intros heap ef1 ea1 ef2 ea2 env rho theta1 theta2 k HFail.
  exists Silent,
    (StEval heap env rho (Mu_App ef1 ea1)
      (KPairParMu1 ef2 ea2 env rho k)).
  eapply Step_PairPar_FallbackMu1; eauto.
Qed.

Lemma pairpar_check_state_decidable_ready :
  PairParCheckDecidable ->
  forall heap ef1 ea1 ef2 ea2 env rho theta1 theta2 k,
    CanStep
      (StReturn heap (Eff theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)).
Proof.
  intros HDec heap ef1 ea1 ef2 ea2 env rho theta1 theta2 k.
  destruct (HDec theta1 theta2) as [[HDisj HNoConf] | HFail].
  - eapply pairpar_check_state_ready; eauto.
  - eapply pairpar_check_state_fallback_ready; eauto.
Qed.

Lemma WTKontRuntime_return_progress_or_pairpar_check :
  forall heap stty v tin tout k,
    TcHeap (heap, stty) ->
    TcVal (stty, v, tin) ->
    WTKontRuntime stty tin tout k ->
    RuntimeValShape stty tin v ->
    CanStep (StReturn heap v k) \/
      PairParCheckState (StReturn heap v k).
Proof.
  intros heap stty v tin tout k HTcHeap HTcVal HKont HShape.
  revert heap v HTcHeap HTcVal HShape.
  induction HKont; intros heap0 v HTcHeap HTcVal HShape.
  - left. apply return_frame_ready_progress. simpl. exact I.
  - left. apply return_frame_ready_progress. simpl.
    rewrite subst_rho_arrow in HShape.
    rewrite (subst_rho_effect rho) in HShape.
    now eapply RuntimeValShape_arrow_inv; eauto.
  - left. apply return_frame_ready_progress. simpl. exact I.
  - left. apply return_frame_ready_progress. simpl.
    rewrite subst_rho_forallrgn in HShape.
    destruct (RuntimeValShape_forall_inv stty v
      (fold_subst_eps rho effr) (subst_rho rho tyr) HShape)
      as (env' & rho' & x & eb & HValue).
    destruct (TcRho_TcRgn_find_R rho rgns w H H0) as [r HFind].
    repeat eexists; eauto.
  - left. apply return_frame_ready_progress. simpl.
    rewrite subst_rho_arrow in HShape.
    rewrite (subst_rho_effect rho) in HShape.
    now eapply RuntimeValShape_arrow_inv; eauto.
  - left. apply return_frame_ready_progress. simpl. exact I.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_effect_inv; eauto.
  - right.
    destruct (RuntimeValShape_effect_inv stty v HShape) as [theta2 HValue].
    subst. constructor.
  - left. apply return_frame_ready_progress. simpl. exact I.
  - left. apply return_frame_ready_progress. simpl. exact I.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_boolean_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    eapply TcRho_TcRgn_find_R; eauto.
  - subst.
    left. apply return_frame_ready_progress. simpl.
    unfold mk_rgn_type in HShape, HTcVal; simpl in HShape, HTcVal.
    rewrite subst_rho_ref_const in HShape.
    rewrite subst_rho_ref_const in HTcVal.
    destruct (RuntimeValShape_ref_const_inv stty v s (subst_rho rho t) HShape)
      as [l HValue].
    subst.
    pose proof (TcVal_loc_find_ST stty s l (subst_rho rho t) HTcVal)
      as HFindST.
    destruct (TcHeap_find_ST_find_H heap0 stty (s, l) (subst_rho rho t)
      HTcHeap HFindST) as [value HFindH].
    exists l, s, value.
    repeat split; auto.
  - subst.
    left. apply return_frame_ready_progress. simpl.
    unfold mk_rgn_type in HShape; simpl in HShape.
    rewrite subst_rho_ref_const in HShape.
    destruct (RuntimeValShape_ref_const_inv stty v s (subst_rho rho t) HShape)
      as [l HValue].
    exists l. exact HValue.
  - left. apply return_frame_ready_progress. simpl.
    exists r. split; [assumption |].
    eapply TcHeap_find_ST_find_H_not_none; eauto.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_natural_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_natural_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_natural_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_natural_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_natural_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_natural_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_natural_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_natural_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    rewrite subst_rho_ref_const in HShape.
    destruct (RuntimeValShape_ref_const_inv stty v r (subst_rho rho t) HShape)
      as [l HValue].
    exists r, l. exact HValue.
  - left. apply return_frame_ready_progress. simpl.
    rewrite subst_rho_ref_const in HShape.
    destruct (RuntimeValShape_ref_const_inv stty v r (subst_rho rho t) HShape)
      as [l HValue].
    exists r, l. exact HValue.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_effect_inv; eauto.
	  - left. apply return_frame_ready_progress. simpl.
	    now eapply RuntimeValShape_effect_inv; eauto.
Qed.

Lemma WTKontRuntime_return_progress :
  PairParCheckDecidable ->
  forall heap stty v tin tout k,
    TcHeap (heap, stty) ->
    TcVal (stty, v, tin) ->
    WTKontRuntime stty tin tout k ->
    RuntimeValShape stty tin v ->
    CanStep (StReturn heap v k).
Proof.
  intros HDec heap stty v tin tout k HTcHeap HTcVal HKont HShape.
  destruct (WTKontRuntime_return_progress_or_pairpar_check
    heap stty v tin tout k HTcHeap HTcVal HKont HShape)
    as [HCanStep | HCheck].
  - exact HCanStep.
  - inversion HCheck; subst.
    eapply pairpar_check_state_decidable_ready; eauto.
Qed.

Theorem WTStateRuntimeHeapShape_not_stuck_or_pairpar_check :
  forall state tout,
    WTStateRuntimeHeapShape state tout ->
    (forall heap env rho e k,
        state = StEval heap env rho e k ->
        EvalHeadRegionsResolved rho e) ->
    NotStuck state \/ PairParCheckState state.
Proof.
  intros state tout HState HEvalReady.
  inversion HState; subst.
  - left. right.
    destruct e; simpl in *; try solve
      [ eapply typed_eval_sequential_head_progress_unindexed; eauto;
        try exact I; try (eapply HEvalReady; reflexivity) ].
    exists Silent,
      (StEval heap env rho (Eff_App e1 e2)
        (KPairParEff1 e1 e2 e3 e4 env rho k)).
    constructor.
  - destruct (WTKontRuntime_return_progress_or_pairpar_check
      heap stty v t tout k H H1 H2 H3) as [HCanStep | HCheck].
    + left. right. exact HCanStep.
    + right. exact HCheck.
	  - left. left. constructor.
Qed.

Theorem WTStateRuntimeHeapShape_not_stuck :
  PairParCheckDecidable ->
  forall state tout,
    WTStateRuntimeHeapShape state tout ->
    (forall heap env rho e k,
        state = StEval heap env rho e k ->
        EvalHeadRegionsResolved rho e) ->
    NotStuck state.
Proof.
  intros HDec state tout HState HEvalReady.
  inversion HState; subst.
  - right.
    destruct e; simpl in *; try solve
      [ eapply typed_eval_sequential_head_progress_unindexed; eauto;
        try exact I; try (eapply HEvalReady; reflexivity) ].
    exists Silent,
      (StEval heap env rho (Eff_App e1 e2)
        (KPairParEff1 e1 e2 e3 e4 env rho k)).
    constructor.
  - right.
    eapply WTKontRuntime_return_progress; eauto.
  - left. constructor.
Qed.
