From stdpp Require Import gmap.
From Stdlib Require Import Sets.Ensembles.

Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepExplicitStoreBase.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.DynamicActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.EffectFacts.
Require Import theories.Meta.HeapFacts.
Require Import theories.Meta.LocallyNameless.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.TraceTypingFacts.
Require Import theories.Meta.TypeFacts.
Require Import theories.Meta.TypingWeakeningFacts.
Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeKontTyping.

Definition eps3 (a b c : Epsilon) : Epsilon :=
  Union_Static_Action a (Union_Static_Action b c).

Definition eps4 (a b c d : Epsilon) : Epsilon :=
  Union_Static_Action a (eps3 b c d).

Definition folded_singleton_alloc rho w : Epsilon :=
  fold_subst_eps rho (Singleton_Static_Action (SA_Alloc (mk_rgn_type w))).

Definition folded_singleton_read rho w : Epsilon :=
  fold_subst_eps rho (Singleton_Static_Action (SA_Read (mk_rgn_type w))).

Definition folded_singleton_write rho w : Epsilon :=
  fold_subst_eps rho (Singleton_Static_Action (SA_Write (mk_rgn_type w))).

Lemma Included_static_refl :
  forall eps,
    Included StaticAction eps eps.
Proof.
  unfold Included.
  auto.
Qed.

Lemma Included_static_empty_l :
  forall eps,
    Included StaticAction Empty_Static_Action eps.
Proof.
  intros eps sa HIn.
  inversion HIn.
Qed.

Lemma Included_static_union_empty_r :
  forall eps,
    Included StaticAction (Union_Static_Action eps Empty_Static_Action) eps.
Proof.
  intros eps sa HIn.
  destruct HIn as [sa HIn | sa HIn].
  - exact HIn.
  - inversion HIn.
Qed.

Lemma Included_static_union_empty_l :
  forall eps,
    Included StaticAction (Union_Static_Action Empty_Static_Action eps) eps.
Proof.
  intros eps sa HIn.
  destruct HIn as [sa HIn | sa HIn].
  - inversion HIn.
  - exact HIn.
Qed.

Lemma Included_static_trans :
  forall eps1 eps2 eps3,
    Included StaticAction eps1 eps2 ->
    Included StaticAction eps2 eps3 ->
    Included StaticAction eps1 eps3.
Proof.
  unfold Included.
  eauto.
Qed.

Ltac solve_static_inclusion :=
  unfold Included in *;
  intros;
  repeat match goal with
  | H : Union_Static_Action _ _ _ |- _ => destruct H as [? H | ? H]
  | H : Empty_Static_Action _ |- _ => inversion H
  end;
  eauto using Union_introl, Union_intror.

Lemma Included_static_union_l :
  forall eps1 eps2,
    Included StaticAction eps1 (Union_Static_Action eps1 eps2).
Proof.
  intros eps1 eps2 sa HIn.
  apply Union_introl.
  exact HIn.
Qed.

Lemma Included_static_union_r :
  forall eps1 eps2,
    Included StaticAction eps2 (Union_Static_Action eps1 eps2).
Proof.
  intros eps1 eps2 sa HIn.
  apply Union_intror.
  exact HIn.
Qed.

Lemma Included_static_union_mono :
  forall eps1 eps1' eps2 eps2',
    Included StaticAction eps1 eps1' ->
    Included StaticAction eps2 eps2' ->
    Included StaticAction
      (Union_Static_Action eps1 eps2)
      (Union_Static_Action eps1' eps2').
Proof.
  intros eps1 eps1' eps2 eps2' HInc1 HInc2 sa HIn.
  destruct HIn as [sa HIn | sa HIn].
  - apply Union_introl. eapply HInc1; eauto.
  - apply Union_intror. eapply HInc2; eauto.
Qed.

Lemma Included_static_union_join :
  forall eps1 eps2 eps,
    Included StaticAction eps1 eps ->
    Included StaticAction eps2 eps ->
    Included StaticAction (Union_Static_Action eps1 eps2) eps.
Proof.
  intros eps1 eps2 eps HInc1 HInc2 sa HIn.
  destruct HIn as [sa HIn1 | sa HIn2].
  - eapply HInc1; eauto.
  - eapply HInc2; eauto.
Qed.

Lemma Included_static_union_assoc_lr :
  forall eps1 eps2 eps3,
    Included StaticAction
      (Union_Static_Action (Union_Static_Action eps1 eps2) eps3)
      (Union_Static_Action eps1 (Union_Static_Action eps2 eps3)).
Proof.
  intros eps1 eps2 eps3 sa HIn.
  destruct HIn as [sa HIn12 | sa HIn3].
  - destruct HIn12 as [sa HIn1 | sa HIn2].
    + apply Union_introl. exact HIn1.
    + apply Union_intror. apply Union_introl. exact HIn2.
  - apply Union_intror. apply Union_intror. exact HIn3.
Qed.

Lemma Included_static_union_assoc_rl :
  forall eps1 eps2 eps3,
    Included StaticAction
      (Union_Static_Action eps1 (Union_Static_Action eps2 eps3))
      (Union_Static_Action (Union_Static_Action eps1 eps2) eps3).
Proof.
  intros eps1 eps2 eps3 sa HIn.
  destruct HIn as [sa HIn1 | sa HIn23].
  - apply Union_introl. apply Union_introl. exact HIn1.
  - destruct HIn23 as [sa HIn2 | sa HIn3].
    + apply Union_introl. apply Union_intror. exact HIn2.
    + apply Union_intror. exact HIn3.
Qed.

Lemma Included_static_union_eps3 :
  forall e1 e2 e3 e4,
    Included StaticAction
      (Union_Static_Action e1 (eps3 e2 e3 e4))
      (Union_Static_Action
        (Union_Static_Action (Union_Static_Action e1 e2) e3)
        e4).
Proof.
  unfold eps3.
  intros e1 e2 e3 e4 sa HIn.
  destruct HIn as [sa HIn1 | sa HIn234].
  - repeat apply Union_introl. exact HIn1.
  - destruct HIn234 as [sa HIn2 | sa HIn34].
    + apply Union_introl. apply Union_introl. apply Union_intror.
      exact HIn2.
    + destruct HIn34 as [sa HIn3 | sa HIn4].
      * apply Union_introl. apply Union_intror. exact HIn3.
      * apply Union_intror. exact HIn4.
Qed.

Lemma Included_static_union_eps3_right_assoc :
  forall e1 e2 e3 e4,
    Included StaticAction
      (Union_Static_Action e1 (eps3 e2 e3 e4))
      (Union_Static_Action
        (Union_Static_Action e1 (Union_Static_Action e2 e3))
        e4).
Proof.
  unfold eps3.
  intros e1 e2 e3 e4 sa HIn.
  destruct HIn as [sa HIn1 | sa HIn234].
  - apply Union_introl. apply Union_introl. exact HIn1.
  - destruct HIn234 as [sa HIn2 | sa HIn34].
    + apply Union_introl. apply Union_intror. apply Union_introl.
      exact HIn2.
    + destruct HIn34 as [sa HIn3 | sa HIn4].
      * apply Union_introl. apply Union_intror. apply Union_intror.
        exact HIn3.
      * apply Union_intror. exact HIn4.
Qed.

Lemma Included_static_union_eps3_keep_left :
  forall e1 e2 e3,
    Included StaticAction
      (Union_Static_Action e1 e3)
      (eps3 e1 e2 e3).
Proof.
  unfold eps3.
  intros e1 e2 e3 sa HIn.
  destruct HIn as [sa HIn1 | sa HIn3].
  - apply Union_introl. exact HIn1.
  - apply Union_intror. apply Union_intror. exact HIn3.
Qed.

Lemma Included_static_union_eps3_keep_middle :
  forall e1 e2 e3,
    Included StaticAction
      (Union_Static_Action e2 e3)
      (eps3 e1 e2 e3).
Proof.
  unfold eps3.
  intros e1 e2 e3 sa HIn.
  destruct HIn as [sa HIn2 | sa HIn3].
  - apply Union_intror. apply Union_introl. exact HIn2.
  - apply Union_intror. apply Union_intror. exact HIn3.
Qed.

Lemma Included_static_union_eps4 :
  forall e1 e2 e3 e4 e5,
    Included StaticAction
      (Union_Static_Action e1 (eps4 e2 e3 e4 e5))
      (Union_Static_Action
        (Union_Static_Action
          (Union_Static_Action (Union_Static_Action e1 e2) e3)
          e4)
        e5).
Proof.
  unfold eps4, eps3.
  intros e1 e2 e3 e4 e5 sa HIn.
  destruct HIn as [sa HIn1 | sa HIn2345].
  - repeat apply Union_introl. exact HIn1.
  - destruct HIn2345 as [sa HIn2 | sa HIn345].
    + apply Union_introl. apply Union_introl. apply Union_introl.
      apply Union_intror. exact HIn2.
    + destruct HIn345 as [sa HIn3 | sa HIn45].
      * apply Union_introl. apply Union_introl. apply Union_intror.
        exact HIn3.
      * destruct HIn45 as [sa HIn4 | sa HIn5].
        -- apply Union_introl. apply Union_intror. exact HIn4.
        -- apply Union_intror. exact HIn5.
Qed.

Lemma Included_static_step_cons :
  forall label_eff trace_eff eps_tail eps_mid eps,
    Included StaticAction
      (Union_Static_Action trace_eff eps_tail)
      eps_mid ->
    Included StaticAction
      (Union_Static_Action label_eff eps_mid)
      eps ->
    Included StaticAction
      (Union_Static_Action
        (Union_Static_Action label_eff trace_eff)
        eps_tail)
      eps.
Proof.
  intros label_eff trace_eff eps_tail eps_mid eps HTail HStep sa HIn.
  destruct HIn as [sa HHead | sa HTailOrRest].
  - destruct HHead as [sa HLabel | sa HTrace].
    + apply HStep. apply Union_introl. exact HLabel.
    + apply HStep. apply Union_intror.
      apply HTail. apply Union_introl. exact HTrace.
  - apply HStep. apply Union_intror.
    apply HTail. apply Union_intror. exact HTailOrRest.
Qed.

Lemma subst_rho_arrow_compute_effect_eq :
  forall rho1 rho2 tya1 effc1 tyc1 effe1 tya2 effc2 tyc2 effe2,
    subst_rho rho1 (Ty_Arrow tya1 effc1 tyc1 effe1 Ty_Effect) =
      subst_rho rho2 (Ty_Arrow tya2 effc2 tyc2 effe2 Ty_Effect) ->
    fold_subst_eps rho1 effc1 = fold_subst_eps rho2 effc2.
Proof.
  intros rho1 rho2 tya1 effc1 tyc1 effe1 tya2 effc2 tyc2 effe2 H.
  rewrite !subst_rho_arrow in H.
  inversion H.
  reflexivity.
Qed.

Lemma subst_rho_arrow_effect_effect_eq :
  forall rho1 rho2 tya1 effc1 tyc1 effe1 tya2 effc2 tyc2 effe2,
    subst_rho rho1 (Ty_Arrow tya1 effc1 tyc1 effe1 Ty_Effect) =
      subst_rho rho2 (Ty_Arrow tya2 effc2 tyc2 effe2 Ty_Effect) ->
    fold_subst_eps rho1 effe1 = fold_subst_eps rho2 effe2.
Proof.
  intros rho1 rho2 tya1 effc1 tyc1 effe1 tya2 effc2 tyc2 effe2 H.
  rewrite !subst_rho_arrow in H.
  inversion H.
  reflexivity.
Qed.

Lemma subst_rho_forall_effect_eq :
  forall rho1 rho2 eff1 tyr1 eff2 tyr2,
    subst_rho rho1 (Ty_ForallRgn eff1 tyr1) =
      subst_rho rho2 (Ty_ForallRgn eff2 tyr2) ->
    fold_subst_eps rho1 eff1 = fold_subst_eps rho2 eff2.
Proof.
  intros rho1 rho2 eff1 tyr1 eff2 tyr2 H.
  rewrite !subst_rho_forallrgn in H.
  inversion H.
  reflexivity.
Qed.

Lemma fold_subst_eps_update_open_close :
  forall rho w r rho' x eff0 eff rgns,
    lc_type_eps eff0 ->
    TcRho (rho', rgns) ->
    not_set_elem rgns x ->
    find_R w rho = Some r ->
    fold_subst_eps rho' (close_var_eff x eff0) = fold_subst_eps rho eff ->
    fold_subst_eps (update_R (x, r) rho') eff0 =
      fold_subst_eps rho (open_rgn_eff (mk_rgn_type w) eff).
Proof.
  intros rho w r rho' x eff0 eff rgns Hlc HTcRho HFresh HFindR HEq.
  unfold update_R; simpl.
  rewrite subst_add_comm_eff.
  - unfold subst_in_eff.
    rewrite (subst_as_close_open_eps 0 x (Rgn_Const true false r) eff0 Hlc).
    unfold close_var_eff, open_rgn_eff in *.
    eapply subst_rho_open_close_eps; eauto.
  - eapply map_to_list_unique with (m := <[x:=r]> rho'); eauto.
  - apply not_elem_of_dom.
    eapply not_set_elem_not_in_rho; eauto.
Qed.

Inductive WTKontEffect : Sigma -> Tau -> Tau -> Kont -> Epsilon -> Prop :=
| WTKE_Done :
    forall stty t,
      WTKontEffect stty t t KDone Empty_Static_Action
| WTKE_MuAppFun :
    forall stty ea env rho k ctxt rgns tya effa effc tyc effe tout eps_k,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, ea, tya, effa) ->
      WTKontEffect stty (subst_rho rho tyc) tout k eps_k ->
      WTKontEffect stty
        (subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))
        tout
        (KMuAppFun ea env rho k)
        (eps3 (fold_subst_eps rho effa) (fold_subst_eps rho effc) eps_k)
| WTKE_MuAppArg :
    forall stty env rho f x ec ee k ctxt rgns tya effc tyc effe tout eps_k,
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
      WTKontEffect stty (subst_rho rho tyc) tout k eps_k ->
      WTKontEffect stty (subst_rho rho tya) tout
        (KMuAppArg env rho f x ec ee k)
        (Union_Static_Action (fold_subst_eps rho effc) eps_k)
| WTKE_RgnApp :
    forall stty w rho k rgns effr tyr tout eps_k,
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      WTKontEffect stty (subst_rho rho (open (mk_rgn_type w) tyr)) tout k eps_k ->
      WTKontEffect stty (subst_rho rho (Ty_ForallRgn effr tyr)) tout
        (KRgnApp w rho k)
        (Union_Static_Action
          (fold_subst_eps rho (open_rgn_eff (mk_rgn_type w) effr))
          eps_k)
| WTKE_EffAppFun :
    forall stty ea env rho k ctxt rgns tya effa effc tyc effe tout eps_k,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, ea, tya, effa) ->
      WTKontEffect stty Ty_Effect tout k eps_k ->
      WTKontEffect stty
        (subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))
        tout
        (KEffAppFun ea env rho k)
        (eps3 (fold_subst_eps rho effa) (fold_subst_eps rho effe) eps_k)
| WTKE_EffAppArg :
    forall stty env rho f x ec ee k ctxt rgns tya effc tyc effe tout eps_k,
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
      WTKontEffect stty Ty_Effect tout k eps_k ->
      WTKontEffect stty (subst_rho rho tya) tout
        (KEffAppArg env rho f x ec ee k)
        (Union_Static_Action (fold_subst_eps rho effe) eps_k)
| WTKE_PairParEff1 :
    forall stty ef1 ea1 ef2 ea2 env rho k ctxt rgns
      ty1 ty2 eff1 eff2 eff3 tout eps_k,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
      TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
      TcExp (ctxt, rgns, Eff_App ef2 ea2, Ty_Effect, eff3) ->
      WTKontEffect stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k eps_k ->
      WTKontEffect stty Ty_Effect tout
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)
        (eps4
          (fold_subst_eps rho eff3)
          (fold_subst_eps rho eff1)
          (fold_subst_eps rho eff2)
          eps_k)
| WTKE_PairParEff2 :
    forall stty ef1 ea1 ef2 ea2 env rho theta1 k ctxt rgns
      ty1 ty2 eff1 eff2 tout eps_k,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
      TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
      WTKontEffect stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k eps_k ->
      WTKontEffect stty Ty_Effect tout
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)
        (eps3 (fold_subst_eps rho eff1) (fold_subst_eps rho eff2) eps_k)
| WTKE_PairParMu1 :
    forall stty ef2 ea2 env rho k ctxt rgns ty1 ty2 eff2 tout eps_k,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
      WTKontEffect stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k eps_k ->
      WTKontEffect stty (subst_rho rho ty1) tout
        (KPairParMu1 ef2 ea2 env rho k)
        (Union_Static_Action (fold_subst_eps rho eff2) eps_k)
| WTKE_PairParMu2 :
    forall stty v1 k rho ty1 ty2 tout eps_k,
      TcVal (stty, v1, subst_rho rho ty1) ->
      RuntimeValShape stty (subst_rho rho ty1) v1 ->
      WTKontEffect stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k eps_k ->
      WTKontEffect stty (subst_rho rho ty2) tout
        (KPairParMu2 v1 k) eps_k
| WTKE_Cond :
    forall stty et ef env rho k ctxt rgns t efft efff tout eps_k,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, et, t, efft) ->
      TcExp (ctxt, rgns, ef, t, efff) ->
      WTKontEffect stty (subst_rho rho t) tout k eps_k ->
      WTKontEffect stty Ty_Boolean tout (KCond et ef env rho k)
        (eps3 (fold_subst_eps rho efft) (fold_subst_eps rho efff) eps_k)
| WTKE_Ref :
    forall stty w rho k rgns t tout s eps_k,
      w = Rgn_Const true false s ->
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      WTKontEffect stty (subst_rho rho (Ty_Ref (mk_rgn_type w) t)) tout k eps_k ->
      WTKontEffect stty (subst_rho rho t) tout (KRef w rho k)
        (Union_Static_Action (folded_singleton_alloc rho w) eps_k)
| WTKE_DeRef :
    forall stty w rho k rgns t tout s eps_k,
      w = Rgn_Const true false s ->
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      WTKontEffect stty (subst_rho rho t) tout k eps_k ->
      WTKontEffect stty (subst_rho rho (Ty_Ref (mk_rgn_type w) t)) tout
        (KDeRef w rho k)
        (Union_Static_Action (folded_singleton_read rho w) eps_k)
| WTKE_AssignLoc :
    forall stty w ev env rho k ctxt rgns t veff tout s eps_k,
      w = Rgn_Const true false s ->
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, ev, t, veff) ->
      WTKontEffect stty Ty_Unit tout k eps_k ->
      WTKontEffect stty (subst_rho rho (Ty_Ref (mk_rgn_type w) t)) tout
        (KAssignLoc w ev env rho k)
        (eps3
          (fold_subst_eps rho veff)
          (folded_singleton_write rho w)
          eps_k)
| WTKE_AssignVal :
    forall stty w l rho k rgns r t tout eps_k,
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      find_R w rho = Some r ->
      find_ST (r, l) stty = Some t ->
      WTKontEffect stty Ty_Unit tout k eps_k ->
      WTKontEffect stty t tout (KAssignVal w l rho k)
        (Union_Static_Action (folded_singleton_write rho w) eps_k)
| WTKE_PlusL :
    forall stty e2 env rho k ctxt rgns eff2 tout eps_k,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
      WTKontEffect stty Ty_Natural tout k eps_k ->
      WTKontEffect stty Ty_Natural tout (KPlusL e2 env rho k)
        (Union_Static_Action (fold_subst_eps rho eff2) eps_k)
| WTKE_PlusR :
    forall stty n k tout eps_k,
      WTKontEffect stty Ty_Natural tout k eps_k ->
      WTKontEffect stty Ty_Natural tout (KPlusR n k) eps_k
| WTKE_MinusL :
    forall stty e2 env rho k ctxt rgns eff2 tout eps_k,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
      WTKontEffect stty Ty_Natural tout k eps_k ->
      WTKontEffect stty Ty_Natural tout (KMinusL e2 env rho k)
        (Union_Static_Action (fold_subst_eps rho eff2) eps_k)
| WTKE_MinusR :
    forall stty n k tout eps_k,
      WTKontEffect stty Ty_Natural tout k eps_k ->
      WTKontEffect stty Ty_Natural tout (KMinusR n k) eps_k
| WTKE_TimesL :
    forall stty e2 env rho k ctxt rgns eff2 tout eps_k,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
      WTKontEffect stty Ty_Natural tout k eps_k ->
      WTKontEffect stty Ty_Natural tout (KTimesL e2 env rho k)
        (Union_Static_Action (fold_subst_eps rho eff2) eps_k)
| WTKE_TimesR :
    forall stty n k tout eps_k,
      WTKontEffect stty Ty_Natural tout k eps_k ->
      WTKontEffect stty Ty_Natural tout (KTimesR n k) eps_k
| WTKE_EqL :
    forall stty e2 env rho k ctxt rgns eff2 tout eps_k,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
      WTKontEffect stty Ty_Boolean tout k eps_k ->
      WTKontEffect stty Ty_Natural tout (KEqL e2 env rho k)
        (Union_Static_Action (fold_subst_eps rho eff2) eps_k)
| WTKE_EqR :
    forall stty n k tout eps_k,
      WTKontEffect stty Ty_Boolean tout k eps_k ->
      WTKontEffect stty Ty_Natural tout (KEqR n k) eps_k
| WTKE_ReadConc :
    forall stty k rho r t tout eps_k,
      WTKontEffect stty Ty_Effect tout k eps_k ->
      WTKontEffect stty
        (subst_rho rho (Ty_Ref (Rgn_Const true true r) t))
        tout
        (KReadConc k) eps_k
| WTKE_WriteConc :
    forall stty k rho r t tout eps_k,
      WTKontEffect stty Ty_Effect tout k eps_k ->
      WTKontEffect stty
        (subst_rho rho (Ty_Ref (Rgn_Const true true r) t))
        tout
        (KWriteConc k) eps_k
| WTKE_ConcatL :
    forall stty e2 env rho k ctxt rgns eff2 tout eps_k,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e2, Ty_Effect, eff2) ->
      WTKontEffect stty Ty_Effect tout k eps_k ->
      WTKontEffect stty Ty_Effect tout (KConcatL e2 env rho k)
        (Union_Static_Action (fold_subst_eps rho eff2) eps_k)
| WTKE_ConcatR :
    forall stty theta k tout eps_k,
      WTKontEffect stty Ty_Effect tout k eps_k ->
      WTKontEffect stty Ty_Effect tout (KConcatR theta k) eps_k.

Inductive WTStateEffectAt : State -> Tau -> Sigma -> Epsilon -> Prop :=
| WTSEA_Eval :
    forall heap env rho e k stty ctxt rgns t eff tout eps_k eps,
      TcHeap (heap, stty) ->
      RuntimeHeapShape heap stty ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e, t, eff) ->
      WTKontEffect stty (subst_rho rho t) tout k eps_k ->
      Included StaticAction
        (Union_Static_Action (fold_subst_eps rho eff) eps_k)
        eps ->
      WTStateEffectAt (StEval heap env rho e k) tout stty eps
| WTSEA_Return :
    forall heap v k stty t tout eps_k eps,
      TcHeap (heap, stty) ->
      RuntimeHeapShape heap stty ->
      TcVal (stty, v, t) ->
      WTKontEffect stty t tout k eps_k ->
      RuntimeValShape stty t v ->
      Included StaticAction eps_k eps ->
      WTStateEffectAt (StReturn heap v k) tout stty eps
| WTSEA_Done :
    forall heap v stty t eps,
      TcHeap (heap, stty) ->
      RuntimeHeapShape heap stty ->
      TcVal (stty, v, t) ->
      RuntimeValShape stty t v ->
      Included StaticAction Empty_Static_Action eps ->
      WTStateEffectAt (StDone heap v) t stty eps.

Lemma WTKontEffect_forget :
  forall stty tin tout k eps,
    WTKontEffect stty tin tout k eps ->
    WTKontRuntime stty tin tout k.
Proof.
  intros stty tin tout k eps HKont.
  induction HKont; try solve [econstructor; eauto].
  - eapply WTKR_MuAppArg with
      (ctxt := ctxt) (rgns := rgns)
      (effc := effc) (tyc := tyc) (effe := effe); eauto.
  - eapply WTKR_EffAppArg with
      (ctxt := ctxt) (rgns := rgns)
      (effc := effc) (tyc := tyc) (effe := effe); eauto.
Qed.

Lemma WTStateEffectAt_forget :
  forall state tout stty eps,
    WTStateEffectAt state tout stty eps ->
    WTStateRuntimeHeapShapeAt state tout stty.
Proof.
  intros state tout stty eps HState.
  inversion HState; subst.
  - econstructor; eauto using WTKontEffect_forget.
  - econstructor; eauto using WTKontEffect_forget.
  - econstructor; eauto.
Qed.

Lemma WTStateEffectAt_initial :
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    WTStateEffectAt
      (initial_state heap env rho e)
      (subst_rho rho t)
      stty
      (fold_subst_eps rho eff).
Proof.
  intros.
  unfold initial_state.
  eapply WTSEA_Eval with (eps_k := Empty_Static_Action); eauto.
  - constructor.
  - apply Included_static_union_empty_r.
Qed.

Lemma WTKontEffect_store_ext :
  forall stty tin tout k eps,
    WTKontEffect stty tin tout k eps ->
    forall stty',
      StoreExtends stty stty' ->
      WTKontEffect stty' tin tout k eps.
Proof.
  intros stty tin tout k eps HKont.
  induction HKont; intros stty' HExt;
    try solve
      [econstructor; eauto;
        try eapply ext_stores__env; eauto;
        try eapply RuntimeEnvShape_store_ext; eauto].
  - eapply WTKE_MuAppArg with
      (ctxt := ctxt) (rgns := rgns)
      (effc := effc) (tyc := tyc) (effe := effe); eauto.
    + eapply ext_stores__env; eauto.
    + eapply RuntimeEnvShape_store_ext; eauto.
  - eapply WTKE_EffAppArg with
      (ctxt := ctxt) (rgns := rgns)
      (effc := effc) (tyc := tyc) (effe := effe); eauto.
    + eapply ext_stores__env; eauto.
    + eapply RuntimeEnvShape_store_ext; eauto.
  - eapply WTKE_PairParMu2 with (rho := rho) (ty1 := ty1) (ty2 := ty2);
      eauto.
    + eapply ext_stores__val; eauto.
    + eapply RuntimeValShape_store_ext; eauto.
Qed.

Lemma WTStateEffectAt_weaken :
  forall state tout stty eps eps',
    WTStateEffectAt state tout stty eps ->
    Included StaticAction eps eps' ->
    WTStateEffectAt state tout stty eps'.
Proof.
  intros state tout stty eps eps' HState HInc.
  inversion HState; subst.
  - eapply WTSEA_Eval with
      (ctxt := ctxt) (rgns := rgns) (t := t) (eff := eff)
      (eps_k := eps_k); eauto.
    eapply Included_static_trans; eauto.
  - eapply WTSEA_Return; eauto.
    eapply Included_static_trans; eauto.
  - eapply WTSEA_Done; eauto.
    eapply Included_static_trans; eauto.
Qed.

Lemma WTStateEffectAt_reheap_store_ext :
  forall state tout stty eps heap' stty',
    WTStateEffectAt state tout stty eps ->
    TcHeap (heap', stty') ->
    RuntimeHeapShape heap' stty' ->
    StoreExtends stty stty' ->
    WTStateEffectAt (with_state_heap heap' state) tout stty' eps.
Proof.
  intros state tout stty eps heap' stty' HState HTcHeap' HHeapShape' HExt.
  inversion HState; subst; simpl.
  - eapply WTSEA_Eval with
      (ctxt := ctxt) (rgns := rgns) (t := t) (eff := eff)
      (eps_k := eps_k); eauto.
    + eapply ext_stores__env; eauto.
    + eapply RuntimeEnvShape_store_ext; eauto.
    + eapply WTKontEffect_store_ext; eauto.
  - eapply WTSEA_Return; eauto.
    + eapply ext_stores__val; eauto.
    + eapply WTKontEffect_store_ext; eauto.
    + eapply RuntimeValShape_store_ext; eauto.
  - eapply WTSEA_Done; eauto.
    + eapply ext_stores__val; eauto.
    + eapply RuntimeValShape_store_ext; eauto.
Qed.
Lemma WTKontEffect_ref_done_label_included :
  forall stty w rho k t tout eps r l v,
    WTKontEffect stty (subst_rho rho t) tout (KRef w rho k) eps ->
    find_R w rho = Some r ->
    Included StaticAction
      (Phi_Static_Effect (Phi_Elem (DA_Alloc r l v)))
      eps.
Proof.
  intros stty w rho k t tout eps r l v HKont HFind.
  inversion HKont; subst.
  unfold Phi_Static_Effect, DynamicAction_Epsilon.
  intros sa HIn.
  inversion HIn; subst.
  apply Union_introl.
  eapply fold_subst_eps_singleton_alloc_find_R; eauto.
Qed.

Lemma WTKontEffect_deref_done_label_included :
  forall stty w rho k t tout eps r l v,
    WTKontEffect stty
      (subst_rho rho (Ty_Ref (mk_rgn_type w) t)) tout
      (KDeRef w rho k) eps ->
    find_R w rho = Some r ->
    Included StaticAction
      (Phi_Static_Effect (Phi_Elem (DA_Read r l v)))
      eps.
Proof.
  intros stty w rho k t tout eps r l v HKont HFind.
  inversion HKont; subst.
  unfold Phi_Static_Effect, DynamicAction_Epsilon.
  intros sa HIn.
  inversion HIn; subst.
  apply Union_introl.
  eapply fold_subst_eps_singleton_read_find_R; eauto.
Qed.

Lemma WTKontEffect_assign_done_label_included :
  forall stty w l rho k t tout eps r v,
    WTKontEffect stty t tout (KAssignVal w l rho k) eps ->
    find_R w rho = Some r ->
    Included StaticAction
      (Phi_Static_Effect (Phi_Elem (DA_Write r l v)))
      eps.
Proof.
  intros stty w l rho k t tout eps r v HKont HFind.
  inversion HKont; subst.
  unfold Phi_Static_Effect, DynamicAction_Epsilon.
  intros sa HIn.
  inversion HIn; subst.
  apply Union_introl.
  eapply fold_subst_eps_singleton_write_find_R; eauto.
Qed.

Definition label_static_effect (label : Label) : Epsilon :=
  match label with
  | Silent => Empty_Static_Action
  | Act da => Phi_Static_Effect (Phi_Elem da)
  end.

Lemma WTStateEffectAt_silent_budget_result :
  forall state' tout stty stty' eps eps',
    StoreExtends stty stty' ->
    WTStateEffectAt state' tout stty' eps' ->
    Included StaticAction eps' eps ->
    exists stty'' eps'',
      StoreExtends stty stty'' /\
      WTStateEffectAt state' tout stty'' eps'' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect Silent) eps'')
        eps.
Proof.
  intros state' tout stty stty' eps eps' HExt HState' HInc.
  exists stty', eps'.
  split; [exact HExt | split; [exact HState' |]].
  simpl.
  eapply Included_static_trans; [apply Included_static_union_empty_l |].
  exact HInc.
Qed.

Lemma WTStateEffectAt_done_step_budget :
  forall heap v tout stty eps lbl state',
    WTStateEffectAt (StReturn heap v KDone) tout stty eps ->
    Step (StReturn heap v KDone) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap v tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ KDone _ |- _ =>
      inversion HKont; subst
  end.
  exists stty, eps.
  split; [apply StoreExtends_refl | split].
  - eapply WTSEA_Done; eauto.
  - simpl.
    apply Included_static_union_empty_l.
Qed.

Lemma WTStateEffectAt_const_step_budget :
  forall heap env rho k n tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (Const n) k) tout stty eps ->
    Step (StEval heap env rho (Const n) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho k n tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Const _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontEffect stty (subst_rho rho Ty_Natural) tout k eps_k |- _ =>
      rewrite (subst_rho_natural rho) in HKont
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty) (eps' := eps_k).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return with (t := Ty_Natural); eauto.
    + constructor.
    + constructor.
    + apply Included_static_refl.
  - eapply Included_static_trans; [apply Included_static_union_r | eassumption].
Qed.

Lemma WTStateEffectAt_bool_step_budget :
  forall heap env rho k b tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (Bool b) k) tout stty eps ->
    Step (StEval heap env rho (Bool b) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho k b tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Bool _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontEffect stty (subst_rho rho Ty_Boolean) tout k eps_k |- _ =>
      rewrite (subst_rho_boolean rho) in HKont
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty) (eps' := eps_k).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return with (t := Ty_Boolean); eauto.
    + constructor.
    + constructor.
    + apply Included_static_refl.
  - eapply Included_static_trans; [apply Included_static_union_r | eassumption].
Qed.

Lemma WTStateEffectAt_var_step_budget :
  forall heap env rho k x tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (Var x) k) tout stty eps ->
    Step (StEval heap env rho (Var x) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho k x tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Var _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  assert (HTcVar : TcVal (stty, v, subst_rho rho t)).
  {
    match goal with
    | HTcEnv : TcEnv (stty, rho, env, ctxt) |- _ =>
        inversion HTcEnv; subst; eauto
    end.
  }
  assert (HShapeVar : RuntimeValShape stty (subst_rho rho t) v)
    by (eapply RuntimeEnvShape_find; eauto).
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty) (eps' := eps_k).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return with (t := subst_rho rho t); eauto.
    apply Included_static_refl.
  - eapply Included_static_trans; [apply Included_static_union_r | eassumption].
Qed.

Lemma WTStateEffectAt_mu_step_budget :
  forall heap env rho k f x ec ee tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (Mu f x ec ee) k) tout stty eps ->
    Step (StEval heap env rho (Mu f x ec ee) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho k f x ec ee tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Mu _ _ _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty) (eps' := eps_k).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return
      with (t := subst_rho rho
        (Ty_Arrow tyx effc tyc effe Ty_Effect)); eauto.
    + eapply TC_Cls; eauto.
    + eapply RVS_Arrow with (rgns := rgns) (ctxt := ctxt); eauto.
    + apply Included_static_refl.
  - eapply Included_static_trans; [apply Included_static_union_r | eassumption].
Qed.

Lemma WTStateEffectAt_lambda_step_budget :
  forall heap env rho k x eb tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (Lambda x eb) k) tout stty eps ->
    Step (StEval heap env rho (Lambda x eb) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho k x eb tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Lambda _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty) (eps' := eps_k).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return
      with (t := subst_rho rho (Ty_ForallRgn (close_var_eff x effr) (close_var x tyr)));
      eauto.
    + eapply TC_Cls; eauto.
    + eapply RVS_ForallRgn with (rgns := rgns) (ctxt := ctxt); eauto.
    + apply Included_static_refl.
  - eapply Included_static_trans; [apply Included_static_union_r | eassumption].
Qed.

Lemma WTStateEffectAt_alloc_abs_step_budget :
  forall heap env rho k w tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (AllocAbs w) k) tout stty eps ->
    Step (StEval heap env rho (AllocAbs w) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho k w tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, AllocAbs _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontEffect stty (subst_rho rho Ty_Effect) tout k eps_k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty) (eps' := eps_k).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return with (t := Ty_Effect); eauto.
    + constructor.
    + constructor.
    + apply Included_static_refl.
  - eapply Included_static_trans; [apply Included_static_union_r | eassumption].
Qed.

Lemma WTStateEffectAt_read_abs_step_budget :
  forall heap env rho k w tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (ReadAbs w) k) tout stty eps ->
    Step (StEval heap env rho (ReadAbs w) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho k w tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, ReadAbs _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontEffect stty (subst_rho rho Ty_Effect) tout k eps_k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty) (eps' := eps_k).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return with (t := Ty_Effect); eauto.
    + constructor.
    + constructor.
    + apply Included_static_refl.
  - eapply Included_static_trans; [apply Included_static_union_r | eassumption].
Qed.

Lemma WTStateEffectAt_write_abs_step_budget :
  forall heap env rho k w tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (WriteAbs w) k) tout stty eps ->
    Step (StEval heap env rho (WriteAbs w) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho k w tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, WriteAbs _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontEffect stty (subst_rho rho Ty_Effect) tout k eps_k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty) (eps' := eps_k).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return with (t := Ty_Effect); eauto.
    + constructor.
    + constructor.
    + apply Included_static_refl.
  - eapply Included_static_trans; [apply Included_static_union_r | eassumption].
Qed.

Lemma WTStateEffectAt_top_step_budget :
  forall heap env rho k tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho Top k) tout stty eps ->
    Step (StEval heap env rho Top k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Top, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontEffect stty (subst_rho rho Ty_Effect) tout k eps_k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty) (eps' := eps_k).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return with (t := Ty_Effect); eauto.
    + constructor.
    + constructor.
    + apply Included_static_refl.
  - eapply Included_static_trans; [apply Included_static_union_r | eassumption].
Qed.

Lemma WTStateEffectAt_empty_step_budget :
  forall heap env rho k tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho Empty k) tout stty eps ->
    Step (StEval heap env rho Empty k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Empty, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontEffect stty (subst_rho rho Ty_Effect) tout k eps_k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty) (eps' := eps_k).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return with (t := Ty_Effect); eauto.
    + constructor.
    + constructor.
    + apply Included_static_refl.
  - eapply Included_static_trans; [apply Included_static_union_r | eassumption].
Qed.

Lemma WTStateEffectAt_ref_done_step_budget :
  forall heap rho w v k tout stty eps lbl state',
    WTStateEffectAt (StReturn heap v (KRef w rho k)) tout stty eps ->
    Step (StReturn heap v (KRef w rho k)) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap rho w v k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KRef _ _ _) _ |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HFindR : find_R (Rgn_Const true false ?s) rho = Some ?r |- _ =>
      simpl in HFindR; inversion HFindR; subst
  end.
  assert (HLabelKont :
      Included StaticAction
        (Phi_Static_Effect (Phi_Elem (DA_Alloc r (allocate_H heap r) v)))
        (Union_Static_Action
          (folded_singleton_alloc rho (Rgn_Const true false r))
          eps_k0)).
  {
    unfold Phi_Static_Effect, DynamicAction_Epsilon.
    intros sa HIn.
    inversion HIn; subst.
    apply Union_introl.
    eapply fold_subst_eps_singleton_alloc_find_R; eauto.
  }
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
  exists stty', eps_k0.
  split; [exact HExt | split].
  - eapply WTSEA_Return
      with (t := Ty_Ref (Rgn_Const true true r) (subst_rho rho t0)); eauto.
    + subst stty'. constructor.
      * unfold find_ST, update_ST.
        apply lookup_insert.
      * intros rgn.
        eapply TcVal_implies_closed; eauto.
    + match goal with
      | HKont : WTKontEffect stty
          (subst_rho rho
            (Ty_Ref (mk_rgn_type (Rgn_Const true false r)) ?ty))
          tout k eps_k0 |- _ =>
          simpl in HKont;
          rewrite subst_rho_ref_const in HKont;
          eapply WTKontEffect_store_ext; eauto
      end.
    + constructor.
    + apply Included_static_refl.
  - simpl.
    eapply Included_static_trans; [| eassumption].
    eapply Included_static_union_join.
    + exact HLabelKont.
    + apply Included_static_union_r.
Qed.

Lemma WTStateEffectAt_deref_done_step_budget :
  forall heap rho w l k tout stty eps lbl state',
    WTStateEffectAt (StReturn heap (Loc w l) (KDeRef w rho k)) tout stty eps ->
    Step (StReturn heap (Loc w l) (KDeRef w rho k)) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap rho w l k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KDeRef _ _ _) _ |- _ =>
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
  assert (HLabelKont :
      Included StaticAction
        (Phi_Static_Effect (Phi_Elem (DA_Read r l v)))
        (Union_Static_Action
          (folded_singleton_read rho (Rgn_Const true false r))
          eps_k0)).
  {
    unfold Phi_Static_Effect, DynamicAction_Epsilon.
    intros sa HIn.
    inversion HIn; subst.
    apply Union_introl.
    eapply fold_subst_eps_singleton_read_find_R; eauto.
  }
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
  exists stty, eps_k0.
  split; [apply StoreExtends_refl | split].
  - eapply WTSEA_Return with (t := subst_rho rho t0); eauto.
    apply Included_static_refl.
  - simpl.
    eapply Included_static_trans; [| eassumption].
    eapply Included_static_union_join.
    + exact HLabelKont.
    + apply Included_static_union_r.
Qed.

Lemma WTStateEffectAt_assign_done_step_budget :
  forall heap rho w l v k tout stty eps lbl state',
    WTStateEffectAt (StReturn heap v (KAssignVal w l rho k)) tout stty eps ->
    Step (StReturn heap v (KAssignVal w l rho k)) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap rho w l v k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  assert (HLabelKont :
      Included StaticAction
        (Phi_Static_Effect (Phi_Elem (DA_Write r l v))) eps_k).
  {
    eapply WTKontEffect_assign_done_label_included; eauto.
  }
  match goal with
  | HKont : WTKontEffect _ _ _ (KAssignVal _ _ _ _) _ |- _ =>
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
  exists stty, eps_k0.
  split; [apply StoreExtends_refl | split].
  - eapply WTSEA_Return with (t := Ty_Unit); eauto.
    + constructor.
    + constructor.
    + apply Included_static_refl.
  - simpl.
    eapply Included_static_trans; [| eassumption].
    eapply Included_static_union_join.
    + exact HLabelKont.
    + apply Included_static_union_r.
Qed.

Lemma WTStateEffectAt_read_conc_done_step_budget :
  forall heap r l k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap (Loc (Rgn_Const true false r) l) (KReadConc k))
      tout stty eps ->
    Step
      (StReturn heap (Loc (Rgn_Const true false r) l) (KReadConc k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap r l k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KReadConc _) _ |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty) (eps' := eps_k).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return with (t := Ty_Effect); eauto.
    + constructor.
    + constructor.
    + apply Included_static_refl.
  - eassumption.
Qed.

Lemma WTStateEffectAt_write_conc_done_step_budget :
  forall heap r l k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap (Loc (Rgn_Const true false r) l) (KWriteConc k))
      tout stty eps ->
    Step
      (StReturn heap (Loc (Rgn_Const true false r) l) (KWriteConc k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap r l k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KWriteConc _) _ |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty) (eps' := eps_k).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return with (t := Ty_Effect); eauto.
    + constructor.
    + constructor.
    + apply Included_static_refl.
  - eassumption.
Qed.

Lemma WTStateEffectAt_concat_done_step_budget :
  forall heap theta1 theta2 k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap (Eff theta2) (KConcatR theta1 k))
      tout stty eps ->
    Step
      (StReturn heap (Eff theta2) (KConcatR theta1 k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap theta1 theta2 k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KConcatR _ _) _ |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty) (eps' := eps_k).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return with (t := Ty_Effect); eauto.
    + constructor.
    + constructor.
    + apply Included_static_refl.
  - eassumption.
Qed.

Lemma WTStateEffectAt_read_conc_eval_arg_step_budget :
  forall heap env rho e k tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (ReadConc e) k) tout stty eps ->
    Step (StEval heap env rho (ReadConc e) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho e k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, ReadConc _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontEffect stty (subst_rho rho Ty_Effect) tout k eps_k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  match goal with
  | HArg : TcExp
      (ctxt, rgns, e, Ty_Ref (Rgn_Const true true ?rv) ?ty, ?eff_arg)
    |- _ =>
      eapply WTStateEffectAt_silent_budget_result with
        (stty' := stty)
        (eps' := Union_Static_Action (fold_subst_eps rho eff_arg) eps_k);
      [ apply StoreExtends_refl
      | eapply WTSEA_Eval with
          (ctxt := ctxt) (rgns := rgns)
          (t := Ty_Ref (Rgn_Const true true rv) ty)
          (eff := eff_arg) (eps_k := eps_k); eauto;
        [ eapply WTKE_ReadConc; eauto
        | apply Included_static_refl ]
      | eassumption ]
  end.
Qed.

Lemma WTStateEffectAt_write_conc_eval_arg_step_budget :
  forall heap env rho e k tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (WriteConc e) k) tout stty eps ->
    Step (StEval heap env rho (WriteConc e) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho e k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, WriteConc _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontEffect stty (subst_rho rho Ty_Effect) tout k eps_k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  match goal with
  | HArg : TcExp
      (ctxt, rgns, e, Ty_Ref (Rgn_Const true true ?rv) ?ty, ?eff_arg)
    |- _ =>
      eapply WTStateEffectAt_silent_budget_result with
        (stty' := stty)
        (eps' := Union_Static_Action (fold_subst_eps rho eff_arg) eps_k);
      [ apply StoreExtends_refl
      | eapply WTSEA_Eval with
          (ctxt := ctxt) (rgns := rgns)
          (t := Ty_Ref (Rgn_Const true true rv) ty)
          (eff := eff_arg) (eps_k := eps_k); eauto;
        [ eapply WTKE_WriteConc; eauto
        | apply Included_static_refl ]
      | eassumption ]
  end.
Qed.

Lemma WTStateEffectAt_concat_eval_left_step_budget :
  forall heap env rho e1 e2 k tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (Concat e1 e2) k) tout stty eps ->
    Step (StEval heap env rho (Concat e1 e2) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho e1 e2 k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Concat _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HInc : Included StaticAction
      (Union_Static_Action
        (fold_subst_eps rho (Union_Static_Action eff1 eff2)) eps_k)
      eps |- _ =>
      rewrite fold_dist_union in HInc
  end.
  match goal with
  | HKont : WTKontEffect stty (subst_rho rho Ty_Effect) tout k eps_k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action
      (fold_subst_eps rho eff1)
      (Union_Static_Action (fold_subst_eps rho eff2) eps_k)).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt := ctxt) (rgns := rgns) (t := Ty_Effect)
      (eff := eff1)
      (eps_k := Union_Static_Action (fold_subst_eps rho eff2) eps_k);
      [ eassumption | eassumption | eassumption | eassumption
      | eassumption | eassumption | eassumption
      | rewrite (subst_rho_effect rho);
        eapply WTKE_ConcatL; eauto
      | apply Included_static_refl ].
  - eapply Included_static_trans; [apply Included_static_union_assoc_rl |].
    eassumption.
Qed.

Lemma WTStateEffectAt_concat_eval_right_step_budget :
  forall heap env rho e2 theta k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap (Eff theta) (KConcatL e2 env rho k))
      tout stty eps ->
    Step
      (StReturn heap (Eff theta) (KConcatL e2 env rho k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho e2 theta k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KConcatL _ _ _ _) _ |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action (fold_subst_eps rho eff2) eps_k0).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt := ctxt) (rgns := rgns) (t := Ty_Effect)
      (eff := eff2) (eps_k := eps_k0); eauto.
    + rewrite (subst_rho_effect rho).
      eapply WTKE_ConcatR; eauto.
    + apply Included_static_refl.
  - eassumption.
Qed.

Lemma WTStateEffectAt_ref_eval_arg_step_budget :
  forall heap env rho w e k tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (Ref w e) k) tout stty eps ->
    Step (StEval heap env rho (Ref w e) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho w e k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Ref _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HInc : Included StaticAction
      (Union_Static_Action
        (fold_subst_eps rho
          (Union_Static_Action veff
            (Singleton_Static_Action
              (SA_Alloc (mk_rgn_type (Rgn_Const true false s))))))
        eps_k)
      eps |- _ =>
      rewrite fold_dist_union in HInc
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action
      (fold_subst_eps rho veff)
      (Union_Static_Action
        (folded_singleton_alloc rho (Rgn_Const true false s)) eps_k)).
  - apply StoreExtends_refl.
  - match goal with
    | HArg : TcExp (ctxt, rgns, e, ?ty_arg, veff) |- _ =>
        eapply WTSEA_Eval with
          (ctxt := ctxt) (rgns := rgns) (t := ty_arg)
          (eff := veff)
          (eps_k := Union_Static_Action
            (folded_singleton_alloc rho (Rgn_Const true false s)) eps_k);
        [ eassumption | eassumption | eassumption | eassumption
        | eassumption | eassumption | exact HArg
        | eapply WTKE_Ref with (rgns := rgns) (s := s); eauto;
          try constructor
        | apply Included_static_refl ]
    end.
  - eapply Included_static_trans; [apply Included_static_union_assoc_rl |].
    eassumption.
Qed.

Lemma WTStateEffectAt_deref_eval_arg_step_budget :
  forall heap env rho w e k tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (DeRef w e) k) tout stty eps ->
    Step (StEval heap env rho (DeRef w e) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho w e k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, DeRef _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HInc : Included StaticAction
      (Union_Static_Action
        (fold_subst_eps rho
          (Union_Static_Action aeff
            (Singleton_Static_Action
              (SA_Read (mk_rgn_type (Rgn_Const true false s))))))
        eps_k)
      eps |- _ =>
      rewrite fold_dist_union in HInc
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action
      (fold_subst_eps rho aeff)
      (Union_Static_Action
        (folded_singleton_read rho (Rgn_Const true false s)) eps_k)).
  - apply StoreExtends_refl.
  - match goal with
    | HArg : TcExp
        (ctxt, rgns, e,
          Ty_Ref (mk_rgn_type (Rgn_Const true false s)) ?ty_arg, aeff)
      |- _ =>
        eapply WTSEA_Eval with
          (ctxt := ctxt) (rgns := rgns)
          (t := Ty_Ref (mk_rgn_type (Rgn_Const true false s)) ty_arg)
          (eff := aeff)
          (eps_k := Union_Static_Action
            (folded_singleton_read rho (Rgn_Const true false s)) eps_k);
        eauto;
        [ eapply WTKE_DeRef with (rgns := rgns) (s := s);
          eauto; try constructor
        | apply Included_static_refl ]
    end.
  - eapply Included_static_trans; [apply Included_static_union_assoc_rl |].
    eassumption.
Qed.

Lemma WTStateEffectAt_assign_eval_loc_step_budget :
  forall heap env rho w ea ev k tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (Assign w ea ev) k) tout stty eps ->
    Step (StEval heap env rho (Assign w ea ev) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho w ea ev k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Assign _ _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontEffect stty (subst_rho rho Ty_Unit) tout k eps_k |- _ =>
      rewrite (subst_rho_unit rho) in HKont
  end.
  match goal with
  | HInc : Included StaticAction
      (Union_Static_Action
        (fold_subst_eps rho
          (Union_Static_Action
            (Union_Static_Action aeff veff)
            (Singleton_Static_Action
              (SA_Write (mk_rgn_type (Rgn_Const true false s))))))
        eps_k)
      eps |- _ =>
      rewrite fold_dist_union in HInc;
      rewrite fold_dist_union in HInc
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action
      (fold_subst_eps rho aeff)
      (eps3
        (fold_subst_eps rho veff)
        (folded_singleton_write rho (Rgn_Const true false s))
        eps_k)).
  - apply StoreExtends_refl.
  - match goal with
    | HLoc : TcExp
        (ctxt, rgns, ea,
          Ty_Ref (mk_rgn_type (Rgn_Const true false s)) ?ty_arg, aeff)
      |- _ =>
        eapply WTSEA_Eval with
          (ctxt := ctxt) (rgns := rgns)
          (t := Ty_Ref (mk_rgn_type (Rgn_Const true false s)) ty_arg)
          (eff := aeff)
          (eps_k := eps3
            (fold_subst_eps rho veff)
            (folded_singleton_write rho (Rgn_Const true false s))
            eps_k);
        eauto;
        [ eapply WTKE_AssignLoc with (rgns := rgns) (s := s);
          eauto; try constructor
        | apply Included_static_refl ]
    end.
  - eapply Included_static_trans; [apply Included_static_union_eps3 |].
    eassumption.
Qed.

Lemma WTStateEffectAt_assign_eval_val_step_budget :
  forall heap env rho w ev l k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap (Loc w l) (KAssignLoc w ev env rho k))
      tout stty eps ->
    Step
      (StReturn heap (Loc w l) (KAssignLoc w ev env rho k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho w ev l k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KAssignLoc _ _ _ _ _) _ |- _ =>
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
  | HInner : WTKontEffect stty Ty_Unit tout k ?eps_inner,
    HVal : TcExp (ctxt, rgns, ev, ?ty_static, veff) |- _ =>
      eapply WTStateEffectAt_silent_budget_result with
        (stty' := stty)
        (eps' := eps3
          (fold_subst_eps rho veff)
          (folded_singleton_write rho (Rgn_Const true false s))
          eps_inner);
      [ apply StoreExtends_refl
      | eapply WTSEA_Eval with
          (ctxt := ctxt) (rgns := rgns)
          (t := ty_static) (eff := veff)
          (eps_k := Union_Static_Action
            (folded_singleton_write rho (Rgn_Const true false s))
            eps_inner);
        eauto;
        [ eapply WTKE_AssignVal with (r := s); eauto; simpl; eauto
        | apply Included_static_refl ]
      | eassumption ]
  end.
Qed.

Lemma WTStateEffectAt_plus_eval_left_step_budget :
  forall heap env rho e1 e2 k tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (Plus e1 e2) k) tout stty eps ->
    Step (StEval heap env rho (Plus e1 e2) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho e1 e2 k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Plus _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontEffect stty (subst_rho rho Ty_Natural) tout k eps_k |- _ =>
      rewrite (subst_rho_natural rho) in HKont
  end.
  match goal with
  | HInc : Included StaticAction
      (Union_Static_Action
        (fold_subst_eps rho (Union_Static_Action eff1 eff2)) eps_k)
      eps |- _ =>
      rewrite fold_dist_union in HInc
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action
      (fold_subst_eps rho eff1)
      (Union_Static_Action (fold_subst_eps rho eff2) eps_k)).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural)
      (eff := eff1)
      (eps_k := Union_Static_Action (fold_subst_eps rho eff2) eps_k);
      eauto.
    + rewrite (subst_rho_natural rho).
      eapply WTKE_PlusL; eauto.
    + apply Included_static_refl.
  - eapply Included_static_trans; [apply Included_static_union_assoc_rl |].
    eassumption.
Qed.

Lemma WTStateEffectAt_plus_eval_right_step_budget :
  forall heap env rho e2 n k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap (Num n) (KPlusL e2 env rho k))
      tout stty eps ->
    Step
      (StReturn heap (Num n) (KPlusL e2 env rho k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho e2 n k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KPlusL _ _ _ _) _ |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HInner : WTKontEffect stty Ty_Natural tout k ?eps_inner,
    HExp : TcExp (ctxt, rgns, e2, Ty_Natural, eff2) |- _ =>
      eapply WTStateEffectAt_silent_budget_result with
        (stty' := stty)
        (eps' := Union_Static_Action (fold_subst_eps rho eff2) eps_inner);
      [ apply StoreExtends_refl
      | eapply WTSEA_Eval with
          (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural)
          (eff := eff2) (eps_k := eps_inner);
        eauto;
        [ rewrite (subst_rho_natural rho);
          eapply WTKE_PlusR; eauto
        | apply Included_static_refl ]
      | eassumption ]
  end.
Qed.

Lemma WTStateEffectAt_plus_done_step_budget :
  forall heap n1 n2 k tout stty eps lbl state',
    WTStateEffectAt (StReturn heap (Num n2) (KPlusR n1 k)) tout stty eps ->
    Step (StReturn heap (Num n2) (KPlusR n1 k)) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap n1 n2 k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KPlusR _ _) _ |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty) (eps' := eps_k).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return with (t := Ty_Natural); eauto.
    + constructor.
    + constructor.
    + apply Included_static_refl.
  - eassumption.
Qed.

Lemma WTStateEffectAt_minus_eval_left_step_budget :
  forall heap env rho e1 e2 k tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (Minus e1 e2) k) tout stty eps ->
    Step (StEval heap env rho (Minus e1 e2) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho e1 e2 k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Minus _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontEffect stty (subst_rho rho Ty_Natural) tout k eps_k |- _ =>
      rewrite (subst_rho_natural rho) in HKont
  end.
  match goal with
  | HInc : Included StaticAction
      (Union_Static_Action
        (fold_subst_eps rho (Union_Static_Action eff1 eff2)) eps_k)
      eps |- _ =>
      rewrite fold_dist_union in HInc
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action
      (fold_subst_eps rho eff1)
      (Union_Static_Action (fold_subst_eps rho eff2) eps_k)).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural)
      (eff := eff1)
      (eps_k := Union_Static_Action (fold_subst_eps rho eff2) eps_k);
      eauto.
    + rewrite (subst_rho_natural rho).
      eapply WTKE_MinusL; eauto.
    + apply Included_static_refl.
  - eapply Included_static_trans; [apply Included_static_union_assoc_rl |].
    eassumption.
Qed.

Lemma WTStateEffectAt_minus_eval_right_step_budget :
  forall heap env rho e2 n k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap (Num n) (KMinusL e2 env rho k))
      tout stty eps ->
    Step
      (StReturn heap (Num n) (KMinusL e2 env rho k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho e2 n k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KMinusL _ _ _ _) _ |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HInner : WTKontEffect stty Ty_Natural tout k ?eps_inner,
    HExp : TcExp (ctxt, rgns, e2, Ty_Natural, eff2) |- _ =>
      eapply WTStateEffectAt_silent_budget_result with
        (stty' := stty)
        (eps' := Union_Static_Action (fold_subst_eps rho eff2) eps_inner);
      [ apply StoreExtends_refl
      | eapply WTSEA_Eval with
          (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural)
          (eff := eff2) (eps_k := eps_inner);
        eauto;
        [ rewrite (subst_rho_natural rho);
          eapply WTKE_MinusR; eauto
        | apply Included_static_refl ]
      | eassumption ]
  end.
Qed.

Lemma WTStateEffectAt_minus_done_step_budget :
  forall heap n1 n2 k tout stty eps lbl state',
    WTStateEffectAt (StReturn heap (Num n2) (KMinusR n1 k)) tout stty eps ->
    Step (StReturn heap (Num n2) (KMinusR n1 k)) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap n1 n2 k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KMinusR _ _) _ |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty) (eps' := eps_k).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return with (t := Ty_Natural); eauto.
    + constructor.
    + constructor.
    + apply Included_static_refl.
  - eassumption.
Qed.

Lemma WTStateEffectAt_times_eval_left_step_budget :
  forall heap env rho e1 e2 k tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (Times e1 e2) k) tout stty eps ->
    Step (StEval heap env rho (Times e1 e2) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho e1 e2 k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Times _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontEffect stty (subst_rho rho Ty_Natural) tout k eps_k |- _ =>
      rewrite (subst_rho_natural rho) in HKont
  end.
  match goal with
  | HInc : Included StaticAction
      (Union_Static_Action
        (fold_subst_eps rho (Union_Static_Action eff1 eff2)) eps_k)
      eps |- _ =>
      rewrite fold_dist_union in HInc
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action
      (fold_subst_eps rho eff1)
      (Union_Static_Action (fold_subst_eps rho eff2) eps_k)).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural)
      (eff := eff1)
      (eps_k := Union_Static_Action (fold_subst_eps rho eff2) eps_k);
      eauto.
    + rewrite (subst_rho_natural rho).
      eapply WTKE_TimesL; eauto.
    + apply Included_static_refl.
  - eapply Included_static_trans; [apply Included_static_union_assoc_rl |].
    eassumption.
Qed.

Lemma WTStateEffectAt_times_eval_right_step_budget :
  forall heap env rho e2 n k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap (Num n) (KTimesL e2 env rho k))
      tout stty eps ->
    Step
      (StReturn heap (Num n) (KTimesL e2 env rho k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho e2 n k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KTimesL _ _ _ _) _ |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HInner : WTKontEffect stty Ty_Natural tout k ?eps_inner,
    HExp : TcExp (ctxt, rgns, e2, Ty_Natural, eff2) |- _ =>
      eapply WTStateEffectAt_silent_budget_result with
        (stty' := stty)
        (eps' := Union_Static_Action (fold_subst_eps rho eff2) eps_inner);
      [ apply StoreExtends_refl
      | eapply WTSEA_Eval with
          (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural)
          (eff := eff2) (eps_k := eps_inner);
        eauto;
        [ rewrite (subst_rho_natural rho);
          eapply WTKE_TimesR; eauto
        | apply Included_static_refl ]
      | eassumption ]
  end.
Qed.

Lemma WTStateEffectAt_times_done_step_budget :
  forall heap n1 n2 k tout stty eps lbl state',
    WTStateEffectAt (StReturn heap (Num n2) (KTimesR n1 k)) tout stty eps ->
    Step (StReturn heap (Num n2) (KTimesR n1 k)) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap n1 n2 k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KTimesR _ _) _ |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty) (eps' := eps_k).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return with (t := Ty_Natural); eauto.
    + constructor.
    + constructor.
    + apply Included_static_refl.
  - eassumption.
Qed.

Lemma WTStateEffectAt_eq_eval_left_step_budget :
  forall heap env rho e1 e2 k tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (Eq e1 e2) k) tout stty eps ->
    Step (StEval heap env rho (Eq e1 e2) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho e1 e2 k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Eq _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontEffect stty (subst_rho rho Ty_Boolean) tout k eps_k |- _ =>
      rewrite (subst_rho_boolean rho) in HKont
  end.
  match goal with
  | HInc : Included StaticAction
      (Union_Static_Action
        (fold_subst_eps rho (Union_Static_Action eff1 eff2)) eps_k)
      eps |- _ =>
      rewrite fold_dist_union in HInc
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action
      (fold_subst_eps rho eff1)
      (Union_Static_Action (fold_subst_eps rho eff2) eps_k)).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural)
      (eff := eff1)
      (eps_k := Union_Static_Action (fold_subst_eps rho eff2) eps_k);
      eauto.
    + rewrite (subst_rho_natural rho).
      eapply WTKE_EqL; eauto.
    + apply Included_static_refl.
  - eapply Included_static_trans; [apply Included_static_union_assoc_rl |].
    eassumption.
Qed.

Lemma WTStateEffectAt_eq_eval_right_step_budget :
  forall heap env rho e2 n k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap (Num n) (KEqL e2 env rho k))
      tout stty eps ->
    Step
      (StReturn heap (Num n) (KEqL e2 env rho k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho e2 n k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KEqL _ _ _ _) _ |- _ =>
      inversion HKont; subst
  end.
  match goal with
  | HInner : WTKontEffect stty Ty_Boolean tout k ?eps_inner,
    HExp : TcExp (ctxt, rgns, e2, Ty_Natural, eff2) |- _ =>
      eapply WTStateEffectAt_silent_budget_result with
        (stty' := stty)
        (eps' := Union_Static_Action (fold_subst_eps rho eff2) eps_inner);
      [ apply StoreExtends_refl
      | eapply WTSEA_Eval with
          (ctxt := ctxt) (rgns := rgns) (t := Ty_Natural)
          (eff := eff2) (eps_k := eps_inner);
        eauto;
        [ rewrite (subst_rho_natural rho);
          eapply WTKE_EqR; eauto
        | apply Included_static_refl ]
      | eassumption ]
  end.
Qed.

Lemma WTStateEffectAt_eq_done_step_budget :
  forall heap n1 n2 k tout stty eps lbl state',
    WTStateEffectAt (StReturn heap (Num n2) (KEqR n1 k)) tout stty eps ->
    Step (StReturn heap (Num n2) (KEqR n1 k)) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap n1 n2 k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KEqR _ _) _ |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty) (eps' := eps_k).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return with (t := Ty_Boolean); eauto.
    + constructor.
    + constructor.
    + apply Included_static_refl.
  - eassumption.
Qed.

Lemma WTStateEffectAt_cond_eval_guard_step_budget :
  forall heap env rho e et ef k tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (Cond e et ef) k) tout stty eps ->
    Step (StEval heap env rho (Cond e et ef) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho e et ef k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Cond _ _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HInc : Included StaticAction
      (Union_Static_Action
        (fold_subst_eps rho
          (Union_Static_Action ?effg (Union_Static_Action ?efft ?efff)))
        eps_k)
      eps |- _ =>
      rewrite fold_dist_union in HInc;
      rewrite fold_dist_union in HInc;
      eapply WTStateEffectAt_silent_budget_result with
        (stty' := stty)
        (eps' := Union_Static_Action
          (fold_subst_eps rho effg)
          (eps3 (fold_subst_eps rho efft) (fold_subst_eps rho efff) eps_k));
      [ apply StoreExtends_refl
      | eapply WTSEA_Eval with
          (ctxt := ctxt) (rgns := rgns) (t := Ty_Boolean)
          (eff := effg)
          (eps_k := eps3
            (fold_subst_eps rho efft) (fold_subst_eps rho efff) eps_k);
        eauto;
        [ rewrite (subst_rho_boolean rho);
          eapply WTKE_Cond; eauto
        | apply Included_static_refl ]
      | eapply Included_static_trans;
        [ apply Included_static_union_eps3_right_assoc | eassumption ] ]
  end.
Qed.

Lemma WTStateEffectAt_cond_true_step_budget :
  forall heap env rho et ef k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap (Bit true) (KCond et ef env rho k))
      tout stty eps ->
    Step
      (StReturn heap (Bit true) (KCond et ef env rho k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho et ef k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KCond _ _ _ _ _) _ |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action (fold_subst_eps rho efft) eps_k0).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt := ctxt) (rgns := rgns) (t := t0)
      (eff := efft) (eps_k := eps_k0);
      eauto.
    apply Included_static_refl.
  - eapply Included_static_trans;
      [ apply Included_static_union_eps3_keep_left | eassumption ].
Qed.

Lemma WTStateEffectAt_cond_false_step_budget :
  forall heap env rho et ef k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap (Bit false) (KCond et ef env rho k))
      tout stty eps ->
    Step
      (StReturn heap (Bit false) (KCond et ef env rho k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho et ef k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KCond _ _ _ _ _) _ |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action (fold_subst_eps rho efff) eps_k0).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt := ctxt) (rgns := rgns) (t := t0)
      (eff := efff) (eps_k := eps_k0);
      eauto.
    apply Included_static_refl.
  - eapply Included_static_trans;
      [ apply Included_static_union_eps3_keep_middle | eassumption ].
Qed.

Lemma WTStateEffectAt_rgn_app_eval_fun_step_budget :
  forall heap env rho er w k tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (Rgn_App er w) k) tout stty eps ->
    Step (StEval heap env rho (Rgn_App er w) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho er w k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Rgn_App _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HInc : Included StaticAction
      (Union_Static_Action
        (fold_subst_eps rho
          (Union_Static_Action efff (open_rgn_eff (mk_rgn_type w) effr)))
        eps_k)
      eps |- _ =>
      rewrite fold_dist_union in HInc
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action
      (fold_subst_eps rho efff)
      (Union_Static_Action
        (fold_subst_eps rho (open_rgn_eff (mk_rgn_type w) effr))
        eps_k)).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt := ctxt) (rgns := rgns)
      (t := Ty_ForallRgn effr tyr) (eff := efff)
      (eps_k := Union_Static_Action
        (fold_subst_eps rho (open_rgn_eff (mk_rgn_type w) effr))
        eps_k);
      eauto.
    + eapply WTKE_RgnApp; eauto.
    + apply Included_static_refl.
  - eapply Included_static_trans; [apply Included_static_union_assoc_rl |].
    eassumption.
Qed.

Lemma WTStateEffectAt_mu_app_eval_fun_step_budget :
  forall heap env rho ef ea k tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (Mu_App ef ea) k) tout stty eps ->
    Step (StEval heap env rho (Mu_App ef ea) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho ef ea k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Mu_App _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HInc : Included StaticAction
      (Union_Static_Action
        (fold_subst_eps rho
          (Union_Static_Action (Union_Static_Action efff effa) effc))
        eps_k)
      eps |- _ =>
      rewrite fold_dist_union in HInc;
      rewrite fold_dist_union in HInc
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action
      (fold_subst_eps rho efff)
      (eps3 (fold_subst_eps rho effa) (fold_subst_eps rho effc) eps_k)).
  - apply StoreExtends_refl.
  - match goal with
    | HFun : TcExp
        (ctxt, rgns, ef,
          Ty_Arrow ?tya0 ?effc0 ?tyc0 ?effe0 Ty_Effect, efff)
      |- _ =>
        eapply WTSEA_Eval with
          (ctxt := ctxt) (rgns := rgns)
          (t := Ty_Arrow tya0 effc0 tyc0 effe0 Ty_Effect)
          (eff := efff)
          (eps_k := eps3
            (fold_subst_eps rho effa) (fold_subst_eps rho effc0) eps_k);
        eauto;
        [ eapply WTKE_MuAppFun; eauto
        | apply Included_static_refl ]
    end.
  - eapply Included_static_trans; [apply Included_static_union_eps3 |].
    eassumption.
Qed.

Lemma WTStateEffectAt_eff_app_eval_fun_step_budget :
  forall heap env rho ef ea k tout stty eps lbl state',
    WTStateEffectAt (StEval heap env rho (Eff_App ef ea) k) tout stty eps ->
    Step (StEval heap env rho (Eff_App ef ea) k) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho ef ea k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Eff_App _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HKont : WTKontEffect stty (subst_rho rho Ty_Effect) tout k eps_k |- _ =>
      rewrite (subst_rho_effect rho) in HKont
  end.
  match goal with
  | HInc : Included StaticAction
      (Union_Static_Action
        (fold_subst_eps rho
          (Union_Static_Action (Union_Static_Action efff effa) effe))
        eps_k)
      eps |- _ =>
      rewrite fold_dist_union in HInc;
      rewrite fold_dist_union in HInc
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action
      (fold_subst_eps rho efff)
      (eps3 (fold_subst_eps rho effa) (fold_subst_eps rho effe) eps_k)).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt := ctxt) (rgns := rgns)
      (t := Ty_Arrow tya effc tyc effe Ty_Effect)
      (eff := efff)
      (eps_k := eps3
        (fold_subst_eps rho effa) (fold_subst_eps rho effe) eps_k);
      eauto.
    + eapply WTKE_EffAppFun; eauto.
    + apply Included_static_refl.
  - eapply Included_static_trans; [apply Included_static_union_eps3 |].
    eassumption.
Qed.

Lemma WTStateEffectAt_mu_app_eval_arg_step_budget :
  forall heap env rho ea env' rho' f x ec ee k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KMuAppFun ea env rho k))
      tout stty eps ->
    Step
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KMuAppFun ea env rho k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho ea env' rho' f x ec ee k tout stty eps lbl state'
    HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KMuAppFun _ _ _ _) _ |- _ =>
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
        as HResultEq;
      pose proof (subst_rho_arrow_compute_effect_eq
        _ _ _ _ _ _ _ _ _ _ HClosureTy) as HCompEffEq
  end.
  match goal with
  | HTcExp : TcExp (_, _, Mu _ _ _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action
      (fold_subst_eps rho effa)
      (Union_Static_Action (fold_subst_eps rho effc) eps_k0)).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt := ctxt) (rgns := rgns) (t := tya)
      (eff := effa)
      (eps_k := Union_Static_Action (fold_subst_eps rho effc) eps_k0);
      eauto.
    + rewrite HArgEq.
      rewrite HCompEffEq.
      eapply WTKE_MuAppArg with
        (ctxt := ctxt_cl) (rgns := rgns_cl)
        (effc := effc_cl) (tyc := tyc_cl) (effe := effe_cl);
        eauto.
      * inversion HTcIncCl as [? ? HFrvCl]; subst.
        eapply ExtendedTcInv_2; eauto;
          eapply HFrvCl; eauto.
      * rewrite <- HResultEq.
        eauto.
    + apply Included_static_refl.
  - eassumption.
Qed.

Lemma WTStateEffectAt_mu_app_eval_body_step_budget :
  forall heap env rho f x ec ee v k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap v (KMuAppArg env rho f x ec ee k))
      tout stty eps ->
    Step
      (StReturn heap v (KMuAppArg env rho f x ec ee k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho f x ec ee v k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KMuAppArg _ _ _ _ _ _ _) _ |- _ =>
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
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action (fold_subst_eps rho effc) eps_k0).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt :=
        update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya)
          ctxt)
      (rgns := rgns) (t := tyc) (eff := effc) (eps_k := eps_k0);
      eauto.
    + eapply TcEnv_update_rec; eauto.
    + eapply RuntimeEnvShape_update_rec; eauto.
    + apply Included_static_refl.
  - eassumption.
Qed.

Lemma WTStateEffectAt_eff_app_eval_arg_step_budget :
  forall heap env rho ea env' rho' f x ec ee k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KEffAppFun ea env rho k))
      tout stty eps ->
    Step
      (StReturn heap (Cls (env', rho', Mu f x ec ee))
        (KEffAppFun ea env rho k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho ea env' rho' f x ec ee k tout stty eps lbl state'
    HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KEffAppFun _ _ _ _) _ |- _ =>
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
      pose proof (subst_rho_arrow_effect_effect_eq
        _ _ _ _ _ _ _ _ _ _ HClosureTy) as HEffEffEq
  end.
  match goal with
  | HTcExp : TcExp (_, _, Mu _ _ _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action
      (fold_subst_eps rho effa)
      (Union_Static_Action (fold_subst_eps rho effe) eps_k0)).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt := ctxt) (rgns := rgns) (t := tya)
      (eff := effa)
      (eps_k := Union_Static_Action (fold_subst_eps rho effe) eps_k0);
      eauto.
    + rewrite HArgEq.
      rewrite HEffEffEq.
      eapply WTKE_EffAppArg with
        (ctxt := ctxt_cl) (rgns := rgns_cl)
        (effc := effc_cl) (tyc := tyc_cl) (effe := effe_cl);
        eauto.
      inversion HTcIncCl as [? ? HFrvCl]; subst.
      eapply ExtendedTcInv_2; eauto;
        eapply HFrvCl; eauto.
    + apply Included_static_refl.
  - eassumption.
Qed.

Lemma WTStateEffectAt_eff_app_eval_body_step_budget :
  forall heap env rho f x ec ee v k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap v (KEffAppArg env rho f x ec ee k))
      tout stty eps ->
    Step
      (StReturn heap v (KEffAppArg env rho f x ec ee k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho f x ec ee v k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KEffAppArg _ _ _ _ _ _ _) _ |- _ =>
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
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action (fold_subst_eps rho effe) eps_k0).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt :=
        update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya)
          ctxt)
      (rgns := rgns) (t := Ty_Effect) (eff := effe) (eps_k := eps_k0);
      eauto.
    + eapply TcEnv_update_rec; eauto.
    + eapply RuntimeEnvShape_update_rec; eauto.
    + rewrite (subst_rho_effect rho); eauto.
    + apply Included_static_refl.
  - eassumption.
Qed.

Lemma WTStateEffectAt_rgn_app_eval_body_step_budget :
  forall heap rho w env' rho' x eb k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap (Cls (env', rho', Lambda x eb)) (KRgnApp w rho k))
      tout stty eps ->
    Step
      (StReturn heap (Cls (env', rho', Lambda x eb)) (KRgnApp w rho k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap rho w env' rho' x eb k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KRgnApp _ _ _) _ |- _ =>
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
  assert (HBodyEffEq :
    fold_subst_eps rho' (close_var_eff x effr0) =
      fold_subst_eps rho effr).
  {
    symmetry.
    eapply subst_rho_forall_effect_eq.
    exact HClosureTy.
  }
  assert (HResumeTyEq :
    subst_rho (update_R (x, r) rho') tyr0 =
      subst_rho rho (open (mk_rgn_type w) tyr)).
  {
    eapply subst_rho_update_open_close; eauto.
  }
  assert (HResumeEffEq :
    fold_subst_eps (update_R (x, r) rho') effr0 =
      fold_subst_eps rho (open_rgn_eff (mk_rgn_type w) effr)).
  {
    eapply fold_subst_eps_update_open_close; eauto.
  }
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action
      (fold_subst_eps rho (open_rgn_eff (mk_rgn_type w) effr))
      eps_k0).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt := ctxt_cl)
      (rgns := set_union rgns_cl (singleton_set x))
      (t := tyr0) (eff := effr0) (eps_k := eps_k0);
      eauto.
    + eapply update_rho; eauto.
    + eapply TcInc_extend_rgn_singleton; eauto.
    + eapply extended_rho; eauto.
    + eapply RuntimeEnvShape_extended_rho; eauto.
    + rewrite HResumeTyEq; eauto.
    + rewrite HResumeEffEq.
      apply Included_static_refl.
  - eassumption.
Qed.

Lemma WTStateEffectAt_pairpar_eval_eff1_step_budget :
  forall heap env rho ef1 ea1 ef2 ea2 k tout stty eps lbl state',
    WTStateEffectAt
      (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
      tout stty eps ->
    Step (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k tout stty eps lbl state'
    HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HTcExp : TcExp (_, _, Pair_Par _ _ _ _, _, _) |- _ =>
      inversion HTcExp; subst
  end.
  match goal with
  | HInc : Included StaticAction
      (Union_Static_Action
        (fold_subst_eps rho
          (Union_Static_Action
            (Union_Static_Action
              (Union_Static_Action ?eff3 ?eff4) ?eff2) ?eff1))
        eps_k)
      eps |- _ =>
      repeat rewrite fold_dist_union in HInc
  end.
  match goal with
  | HEff1 : TcExp (ctxt, rgns, Eff_App ef1 ea1, ty3, eff3) |- _ =>
      assert (HEff1Ty :
        TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, eff3))
        by (inversion HEff1; subst; eauto)
  end.
  match goal with
  | HEff2 : TcExp (ctxt, rgns, Eff_App ef2 ea2, ty4, eff4) |- _ =>
      assert (HEff2Ty :
        TcExp (ctxt, rgns, Eff_App ef2 ea2, Ty_Effect, eff4))
        by (inversion HEff2; subst; eauto)
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action
      (fold_subst_eps rho eff3)
      (eps4
        (fold_subst_eps rho eff4)
        (fold_subst_eps rho eff1)
        (fold_subst_eps rho eff2)
        eps_k)).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt := ctxt) (rgns := rgns) (t := Ty_Effect)
      (eff := eff3)
      (eps_k := eps4
        (fold_subst_eps rho eff4)
        (fold_subst_eps rho eff1)
        (fold_subst_eps rho eff2)
        eps_k);
      eauto.
    + rewrite (subst_rho_effect rho).
      eapply WTKE_PairParEff1; eauto.
    + apply Included_static_refl.
  - eapply Included_static_trans with
      (eps2 := Union_Static_Action
        (Union_Static_Action
          (Union_Static_Action
            (Union_Static_Action
              (fold_subst_eps rho eff3)
              (fold_subst_eps rho eff4))
            (fold_subst_eps rho eff2))
          (fold_subst_eps rho eff1))
        eps_k).
    + unfold eps4, eps3.
      intros sa HIn.
      destruct HIn as [sa HInEff3 | sa HInRest].
      * repeat apply Union_introl. exact HInEff3.
      * destruct HInRest as [sa HInEff4 | sa HInRest].
        -- apply Union_introl. apply Union_introl. apply Union_introl.
           apply Union_intror. exact HInEff4.
        -- destruct HInRest as [sa HInEff1 | sa HInRest].
           ++ apply Union_introl. apply Union_intror. exact HInEff1.
           ++ destruct HInRest as [sa HInEff2 | sa HInK].
              ** apply Union_introl. apply Union_introl. apply Union_intror.
                 exact HInEff2.
              ** apply Union_intror. exact HInK.
    + eassumption.
Qed.

Lemma WTStateEffectAt_pairpar_eval_eff2_step_budget :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap (Eff theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      tout stty eps ->
    Step
      (StReturn heap (Eff theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 k tout stty eps lbl state'
    HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KPairParEff1 _ _ _ _ _ _ _) _ |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action
      (fold_subst_eps rho eff3)
      (eps3
        (fold_subst_eps rho eff1)
        (fold_subst_eps rho eff2)
        eps_k0)).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt := ctxt) (rgns := rgns) (t := Ty_Effect)
      (eff := eff3)
      (eps_k := eps3
        (fold_subst_eps rho eff1)
        (fold_subst_eps rho eff2)
        eps_k0);
      eauto.
    + rewrite (subst_rho_effect rho).
      eapply WTKE_PairParEff2; eauto.
    + apply Included_static_refl.
  - eassumption.
Qed.

Lemma WTStateEffectAt_pairpar_eval_mu1_step_budget :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap (Eff theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      tout stty eps ->
    Step
      (StReturn heap (Eff theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k tout stty eps lbl
    state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  - match goal with
    | HKont : WTKontEffect _ _ _ (KPairParEff2 _ _ _ _ _ _ _ _) _ |- _ =>
        inversion HKont; subst
    end.
    eapply WTStateEffectAt_silent_budget_result with
      (stty' := stty)
      (eps' := Union_Static_Action
        (fold_subst_eps rho eff1)
        (Union_Static_Action (fold_subst_eps rho eff2) eps_k0)).
    + apply StoreExtends_refl.
    + eapply WTSEA_Eval with
        (ctxt := ctxt) (rgns := rgns) (t := ty1) (eff := eff1)
        (eps_k := Union_Static_Action (fold_subst_eps rho eff2) eps_k0);
        eauto.
      * eapply WTKE_PairParMu1; eauto.
      * apply Included_static_refl.
    + eassumption.
  - match goal with
    | HKont : WTKontEffect _ _ _ (KPairParEff2 _ _ _ _ _ _ _ _) _ |- _ =>
        inversion HKont; subst
    end.
    eapply WTStateEffectAt_silent_budget_result with
      (stty' := stty)
      (eps' := Union_Static_Action
        (fold_subst_eps rho eff1)
        (Union_Static_Action (fold_subst_eps rho eff2) eps_k0)).
    + apply StoreExtends_refl.
    + eapply WTSEA_Eval with
        (ctxt := ctxt) (rgns := rgns) (t := ty1) (eff := eff1)
        (eps_k := Union_Static_Action (fold_subst_eps rho eff2) eps_k0);
        eauto.
      * eapply WTKE_PairParMu1; eauto.
      * apply Included_static_refl.
    + eassumption.
Qed.

Lemma WTStateEffectAt_pairpar_eval_mu2_step_budget :
  forall heap env rho ef2 ea2 v1 k tout stty eps lbl state',
    WTStateEffectAt
      (StReturn heap v1 (KPairParMu1 ef2 ea2 env rho k))
      tout stty eps ->
    Step (StReturn heap v1 (KPairParMu1 ef2 ea2 env rho k))
      lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap env rho ef2 ea2 v1 k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KPairParMu1 _ _ _ _ _) _ |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateEffectAt_silent_budget_result with
    (stty' := stty)
    (eps' := Union_Static_Action (fold_subst_eps rho eff2) eps_k0).
  - apply StoreExtends_refl.
  - eapply WTSEA_Eval with
      (ctxt := ctxt) (rgns := rgns) (t := ty2)
      (eff := eff2) (eps_k := eps_k0);
      eauto.
    + eapply WTKE_PairParMu2 with (rho := rho) (ty1 := ty1) (ty2 := ty2);
        eauto.
    + apply Included_static_refl.
  - eassumption.
Qed.

Lemma WTStateEffectAt_pairpar_done_step_budget :
  forall heap v1 v2 k tout stty eps lbl state',
    WTStateEffectAt (StReturn heap v2 (KPairParMu2 v1 k)) tout stty eps ->
    Step (StReturn heap v2 (KPairParMu2 v1 k)) lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros heap v1 v2 k tout stty eps lbl state' HState HStep.
  inversion HState; subst.
  inversion HStep; subst.
  match goal with
  | HKont : WTKontEffect _ _ _ (KPairParMu2 _ _) _ |- _ =>
      inversion HKont; subst
  end.
  eapply WTStateEffectAt_silent_budget_result with (stty' := stty).
  - apply StoreExtends_refl.
  - eapply WTSEA_Return with
      (t := subst_rho rho (Ty_Pair ty1 ty2)).
    + eauto.
    + eauto.
    + rewrite subst_rho_pair.
      constructor; eauto.
    + eauto.
    + rewrite subst_rho_pair.
      constructor; eauto.
    + apply Included_static_refl.
  - eassumption.
Qed.

#[local] Hint Resolve
  WTStateEffectAt_done_step_budget
  WTStateEffectAt_const_step_budget
  WTStateEffectAt_bool_step_budget
  WTStateEffectAt_var_step_budget
  WTStateEffectAt_mu_step_budget
  WTStateEffectAt_lambda_step_budget
  WTStateEffectAt_alloc_abs_step_budget
  WTStateEffectAt_read_abs_step_budget
  WTStateEffectAt_write_abs_step_budget
  WTStateEffectAt_top_step_budget
  WTStateEffectAt_empty_step_budget
  WTStateEffectAt_ref_done_step_budget
  WTStateEffectAt_deref_done_step_budget
  WTStateEffectAt_assign_done_step_budget
  WTStateEffectAt_read_conc_done_step_budget
  WTStateEffectAt_write_conc_done_step_budget
  WTStateEffectAt_concat_done_step_budget
  WTStateEffectAt_read_conc_eval_arg_step_budget
  WTStateEffectAt_write_conc_eval_arg_step_budget
  WTStateEffectAt_concat_eval_left_step_budget
  WTStateEffectAt_concat_eval_right_step_budget
  WTStateEffectAt_ref_eval_arg_step_budget
  WTStateEffectAt_deref_eval_arg_step_budget
  WTStateEffectAt_assign_eval_loc_step_budget
  WTStateEffectAt_assign_eval_val_step_budget
  WTStateEffectAt_plus_eval_left_step_budget
  WTStateEffectAt_plus_eval_right_step_budget
  WTStateEffectAt_plus_done_step_budget
  WTStateEffectAt_minus_eval_left_step_budget
  WTStateEffectAt_minus_eval_right_step_budget
  WTStateEffectAt_minus_done_step_budget
  WTStateEffectAt_times_eval_left_step_budget
  WTStateEffectAt_times_eval_right_step_budget
  WTStateEffectAt_times_done_step_budget
  WTStateEffectAt_eq_eval_left_step_budget
  WTStateEffectAt_eq_eval_right_step_budget
  WTStateEffectAt_eq_done_step_budget
  WTStateEffectAt_cond_eval_guard_step_budget
  WTStateEffectAt_cond_true_step_budget
  WTStateEffectAt_cond_false_step_budget
  WTStateEffectAt_rgn_app_eval_fun_step_budget
  WTStateEffectAt_mu_app_eval_fun_step_budget
  WTStateEffectAt_eff_app_eval_fun_step_budget
  WTStateEffectAt_mu_app_eval_arg_step_budget
  WTStateEffectAt_mu_app_eval_body_step_budget
  WTStateEffectAt_eff_app_eval_arg_step_budget
  WTStateEffectAt_eff_app_eval_body_step_budget
  WTStateEffectAt_rgn_app_eval_body_step_budget
  WTStateEffectAt_pairpar_eval_eff1_step_budget
  WTStateEffectAt_pairpar_eval_eff2_step_budget
  WTStateEffectAt_pairpar_eval_mu1_step_budget
  WTStateEffectAt_pairpar_eval_mu2_step_budget
  WTStateEffectAt_pairpar_done_step_budget : effect_budget.

Theorem WTStateEffectAt_step_budget :
  forall state tout stty eps lbl state',
    WTStateEffectAt state tout stty eps ->
    Step state lbl state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action (label_static_effect lbl) eps')
        eps.
Proof.
  intros state tout stty eps lbl state' HState HStep.
  inversion HStep; subst; eauto with effect_budget.
Qed.

Theorem WTStateEffectAt_steps_budget :
  forall state tout stty eps trace state',
    WTStateEffectAt state tout stty eps ->
    Steps state trace state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' tout stty' eps' /\
      Included StaticAction
        (Union_Static_Action
          (Phi_Static_Effect (trace_as_phi trace))
          eps')
        eps.
Proof.
  intros state tout stty eps trace state' HState HSteps.
  revert tout stty eps HState.
  induction HSteps as
    [state
    | state label state1 trace state2 HStep HSteps IH];
    intros tout stty eps HState.
  - exists stty, eps.
    split; [apply StoreExtends_refl | split].
    + exact HState.
    + simpl. apply Included_static_union_empty_l.
  - destruct (WTStateEffectAt_step_budget
      state tout stty eps label state1 HState HStep)
      as (stty1 & eps1 & HExt1 & HState1 & HInc1).
    destruct (IH tout stty1 eps1 HState1)
      as (stty2 & eps2 & HExt2 & HState2 & HInc2).
    exists stty2, eps2.
    split; [eapply StoreExtends_trans; eauto | split].
    + exact HState2.
    + destruct label as [| da]; simpl in *.
      * eapply Included_static_trans; [exact HInc2 |].
        eapply Included_static_trans; [apply Included_static_union_r |].
        exact HInc1.
      * eapply Included_static_step_cons; eauto.
Qed.

Theorem WTStateEffectAt_initial_steps_budget :
  forall heap env rho e stty ctxt rgns t eff trace state',
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    Steps (initial_state heap env rho e) trace state' ->
    exists stty' eps',
      StoreExtends stty stty' /\
      WTStateEffectAt state' (subst_rho rho t) stty' eps' /\
      Included StaticAction
        (Union_Static_Action
          (Phi_Static_Effect (trace_as_phi trace))
          eps')
        (fold_subst_eps rho eff).
Proof.
  intros heap env rho e stty ctxt rgns t eff trace state'
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps.
  eapply WTStateEffectAt_steps_budget; eauto.
  eapply WTStateEffectAt_initial; eauto.
Qed.

Theorem WTStateEffectAt_initial_terminal_trace_budget :
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
      Included StaticAction
        (Phi_Static_Effect (trace_as_phi trace))
        (fold_subst_eps rho eff).
Proof.
  intros heap env rho e stty ctxt rgns t eff trace heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps.
  destruct
    (WTStateEffectAt_initial_steps_budget
      heap env rho e stty ctxt rgns t eff trace (StDone heap' v)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps)
    as (stty' & eps' & HExt & HState' & HInc).
  inversion HState'; subst.
  exists stty'.
  split; [exact HExt |].
  split; [eauto |].
  split; [eauto |].
  split; [eauto |].
  split; [eauto |].
  eapply Included_static_trans; [apply Included_static_union_l |].
  exact HInc.
Qed.

Theorem WTStateEffectAt_initial_effect_terminal_trace_budget :
  forall heap env rho e stty ctxt rgns eff trace heap' theta,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, Ty_Effect, eff) ->
    Steps (initial_state heap env rho e) trace (StDone heap' (Eff theta)) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      Included StaticAction
        (Phi_Static_Effect (trace_as_phi trace))
        (fold_subst_eps rho eff).
Proof.
  intros heap env rho e stty ctxt rgns eff trace heap' theta
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps.
  destruct
    (WTStateEffectAt_initial_terminal_trace_budget
      heap env rho e stty ctxt rgns Ty_Effect eff trace heap' (Eff theta)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps)
    as (stty' & HExt & HTcHeap' & HHeapShape' & _ & _ & HInc).
  exists stty'.
  split; [exact HExt |].
  split; [exact HTcHeap' |].
  split; [exact HHeapShape' |].
  exact HInc.
Qed.

Theorem small_step_eff_sound :
  forall heap env rho e stty ctxt rgns t eff trace heap' v,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    Steps (initial_state heap env rho e) trace (StDone heap' v) ->
    Epsilon_Phi_Soundness
      (fold_subst_eps rho eff, trace_as_phi trace).
Proof.
  intros heap env rho e stty ctxt rgns t eff trace heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps.
  destruct
    (WTStateEffectAt_initial_terminal_trace_budget
      heap env rho e stty ctxt rgns t eff trace heap' v
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps)
    as (_ & _ & _ & _ & _ & _ & HInc).
  apply Epsilon_Phi_Soundness_of_phi_static_included.
  exact HInc.
Qed.

Theorem small_step_effect_summary_eff_sound :
  forall heap env rho e stty ctxt rgns eff trace heap' theta,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, Ty_Effect, eff) ->
    Steps (initial_state heap env rho e) trace (StDone heap' (Eff theta)) ->
    Epsilon_Phi_Soundness
      (fold_subst_eps rho eff, trace_as_phi trace).
Proof.
  intros heap env rho e stty ctxt rgns eff trace heap' theta
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps.
  eapply small_step_eff_sound; eauto.
Qed.
