From stdpp Require Import gmap.
From Stdlib Require Import Sets.Ensembles.

Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepTyping.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepReturnProgress.
Require Import theories.Runtime.SmallStepEvalProgress.
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

