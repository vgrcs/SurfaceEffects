From Stdlib Require Import List.
From Stdlib Require Import Program.Equality.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Typing.Types.

Import ListNotations.

Inductive NResolvedRegionExpr : RegionExpr -> Prop :=
| NRR_Const :
    forall r,
      NResolvedRegionExpr (region_const_expr r).

Inductive NResolvedRegionType : RegionType -> Prop :=
| NRRT_Const :
    forall r,
      NResolvedRegionType (region_const_type r)
| NRRT_BVar :
    forall n,
      NResolvedRegionType (Rgn_BVar true true n).

Inductive NResolveRegionType :
    Rho -> RegionType -> RegionType -> Prop :=
| NResolveRegion_Const :
    forall rho r,
      NResolveRegionType rho (region_const_type r) (region_const_type r)
| NResolveRegion_FVar :
    forall rho x r,
      rho_lookup x rho = Some r ->
      NResolveRegionType rho (Rgn_FVar true true x) (region_const_type r)
| NResolveRegion_BVar :
    forall rho n,
      NResolveRegionType rho
        (Rgn_BVar true true n)
        (Rgn_BVar true true n).

Inductive NResolvedStaticAction : StaticAction -> Prop :=
| NRSA_Alloc :
    forall rgn,
      NResolvedRegionType rgn ->
      NResolvedStaticAction (SAlloc rgn)
| NRSA_Read :
    forall rgn,
      NResolvedRegionType rgn ->
      NResolvedStaticAction (SRead rgn)
| NRSA_Write :
    forall rgn,
      NResolvedRegionType rgn ->
      NResolvedStaticAction (SWrite rgn).

Definition NResolvedStaticEffect (eff : StaticEffect) : Prop :=
  Forall NResolvedStaticAction eff.

Inductive NResolveStaticAction :
    Rho -> StaticAction -> StaticAction -> Prop :=
| NResolve_SAlloc :
    forall rho rgn rgn',
      NResolveRegionType rho rgn rgn' ->
      NResolveStaticAction rho (SAlloc rgn) (SAlloc rgn')
| NResolve_SRead :
    forall rho rgn rgn',
      NResolveRegionType rho rgn rgn' ->
      NResolveStaticAction rho (SRead rgn) (SRead rgn')
| NResolve_SWrite :
    forall rho rgn rgn',
      NResolveRegionType rho rgn rgn' ->
      NResolveStaticAction rho (SWrite rgn) (SWrite rgn').

Inductive NResolveStaticEffect :
    Rho -> StaticEffect -> StaticEffect -> Prop :=
| NResolveStaticEffect_Nil :
    forall rho,
      NResolveStaticEffect rho [] []
| NResolveStaticEffect_Cons :
    forall rho action action' eff eff',
      NResolveStaticAction rho action action' ->
      NResolveStaticEffect rho eff eff' ->
      NResolveStaticEffect rho (action :: eff) (action' :: eff').

Inductive NResolvedTy : NTy -> Prop :=
| NRTy_Nat :
    NResolvedTy TyNat
| NRTy_Bool :
    NResolvedTy TyBool
| NRTy_Unit :
    NResolvedTy TyUnit
| NRTy_Effect :
    NResolvedTy TyEffect
| NRTy_Ref :
    forall rgn ty,
      NResolvedRegionType rgn ->
      NResolvedTy ty ->
      NResolvedTy (TyRef rgn ty)
| NRTy_Arrow :
    forall ty_arg eff_body ty_body eff_summary,
      NResolvedTy ty_arg ->
      NResolvedStaticEffect eff_body ->
      NResolvedTy ty_body ->
      NResolvedStaticEffect eff_summary ->
      NResolvedTy (TyArrow ty_arg eff_body ty_body eff_summary)
| NRTy_ForallRgn :
    forall eff ty,
      NResolvedStaticEffect eff ->
      NResolvedTy ty ->
      NResolvedTy (TyForallRgn eff ty).

Inductive NResolveTy : Rho -> NTy -> NTy -> Prop :=
| NResolve_Nat :
    forall rho,
      NResolveTy rho TyNat TyNat
| NResolve_Bool :
    forall rho,
      NResolveTy rho TyBool TyBool
| NResolve_Unit :
    forall rho,
      NResolveTy rho TyUnit TyUnit
| NResolve_Effect :
    forall rho,
      NResolveTy rho TyEffect TyEffect
| NResolve_Ref :
    forall rho rgn rgn' ty ty',
      NResolveRegionType rho rgn rgn' ->
      NResolveTy rho ty ty' ->
      NResolveTy rho (TyRef rgn ty) (TyRef rgn' ty')
| NResolve_Arrow :
    forall rho ty_arg ty_arg' eff_body eff_body'
      ty_body ty_body' eff_summary eff_summary',
      NResolveTy rho ty_arg ty_arg' ->
      NResolveStaticEffect rho eff_body eff_body' ->
      NResolveTy rho ty_body ty_body' ->
      NResolveStaticEffect rho eff_summary eff_summary' ->
      NResolveTy rho
        (TyArrow ty_arg eff_body ty_body eff_summary)
        (TyArrow ty_arg' eff_body' ty_body' eff_summary')
| NResolve_ForallRgn :
    forall rho eff eff' ty ty',
      NResolveStaticEffect rho eff eff' ->
      NResolveTy rho ty ty' ->
      NResolveTy rho (TyForallRgn eff ty) (TyForallRgn eff' ty').

Lemma NResolveRegionType_resolved :
  forall rho rgn rgn',
    NResolveRegionType rho rgn rgn' ->
    NResolvedRegionType rgn'.
Proof.
  intros rho rgn rgn' HResolve.
  inversion HResolve; subst; constructor.
Qed.

Lemma NResolveStaticAction_resolved :
  forall rho action action',
    NResolveStaticAction rho action action' ->
    NResolvedStaticAction action'.
Proof.
  intros rho action action' HResolve.
  inversion HResolve; subst; constructor;
    eauto using NResolveRegionType_resolved.
Qed.

Lemma NResolveStaticEffect_resolved :
  forall rho eff eff',
    NResolveStaticEffect rho eff eff' ->
    NResolvedStaticEffect eff'.
Proof.
  intros rho eff eff' HResolve.
  induction HResolve; constructor;
    eauto using NResolveStaticAction_resolved.
Qed.

Lemma NResolveTy_resolved :
  forall rho ty ty',
    NResolveTy rho ty ty' ->
    NResolvedTy ty'.
Proof.
  intros rho ty ty' HResolve.
  induction HResolve; constructor;
    eauto using NResolveRegionType_resolved,
      NResolveStaticEffect_resolved.
Qed.

Lemma NResolveTy_ref_inv :
  forall rho rgn ty ty_resolved,
    NResolveTy rho (TyRef rgn ty) ty_resolved ->
    exists rgn' ty',
      NResolveRegionType rho rgn rgn' /\
      NResolveTy rho ty ty' /\
      ty_resolved = TyRef rgn' ty'.
Proof.
  intros rho rgn ty ty_resolved HResolve.
  inversion HResolve; subst.
  exists rgn', ty'.
  repeat split; assumption || reflexivity.
Qed.

Lemma NResolveRegionType_deterministic :
  forall rho rgn rgn1 rgn2,
    NResolveRegionType rho rgn rgn1 ->
    NResolveRegionType rho rgn rgn2 ->
    rgn1 = rgn2.
Proof.
  intros rho rgn rgn1 rgn2 HLeft HRight.
  inversion HLeft; subst; inversion HRight; subst;
    try reflexivity.
  match goal with
  | H1 : rho_lookup ?x ?rho = Some ?r1,
    H2 : rho_lookup ?x ?rho = Some ?r2 |- _ =>
      rewrite H1 in H2; inversion H2; reflexivity
  end.
Qed.

Lemma NResolveStaticAction_deterministic :
  forall rho action action1 action2,
    NResolveStaticAction rho action action1 ->
    NResolveStaticAction rho action action2 ->
    action1 = action2.
Proof.
  intros rho action action1 action2 HLeft HRight.
  inversion HLeft; subst; inversion HRight; subst;
    match goal with
    | H1 : NResolveRegionType rho ?rgn ?rgn1,
      H2 : NResolveRegionType rho ?rgn ?rgn2 |- _ =>
        pose proof
          (NResolveRegionType_deterministic rho rgn rgn1 rgn2 H1 H2);
        subst
    end;
    reflexivity.
Qed.

Lemma NResolveStaticEffect_deterministic :
  forall rho eff eff1 eff2,
    NResolveStaticEffect rho eff eff1 ->
    NResolveStaticEffect rho eff eff2 ->
    eff1 = eff2.
Proof.
  intros rho eff eff1 eff2 HLeft.
  revert eff2.
  induction HLeft; intros eff2 HRight.
  - inversion HRight; reflexivity.
  - inversion HRight; subst.
    match goal with
    | H1 : NResolveStaticAction rho action action',
      H2 : NResolveStaticAction rho action ?action_other |- _ =>
        pose proof
          (NResolveStaticAction_deterministic
            rho action action' action_other H1 H2);
        subst action_other
    end.
    match goal with
    | HRest : NResolveStaticEffect rho eff ?eff_other |- _ =>
        specialize (IHHLeft _ HRest); subst
    end.
    reflexivity.
Qed.

Lemma NResolveTy_deterministic :
  forall rho ty ty1 ty2,
    NResolveTy rho ty ty1 ->
    NResolveTy rho ty ty2 ->
    ty1 = ty2.
Proof.
  intros rho ty ty_left ty_right HLeft.
  revert ty_right.
  induction HLeft; intros ty_right HRight;
    try solve [inversion HRight; subst; reflexivity].
  - destruct
      (NResolveTy_ref_inv rho rgn ty ty_right HRight)
      as (rgn_other & ty_other & HRgnOther & HTyOther & ->).
    pose proof
      (NResolveRegionType_deterministic
        rho rgn rgn' rgn_other H HRgnOther);
      subst rgn_other.
    specialize (IHHLeft _ HTyOther). subst.
    reflexivity.
  - inversion HRight; subst.
    repeat match goal with
    | IH : forall ty_res : NTy,
        NResolveTy ?rho ?ty ty_res -> ?resolved = ty_res,
      HResolve : NResolveTy ?rho ?ty ?resolved_other |- _ =>
        specialize (IH _ HResolve); subst
    end.
    match goal with
    | HLeftEff : NResolveStaticEffect rho eff_body eff_body',
      HRightEff : NResolveStaticEffect rho eff_body ?eff_body_other
      |- TyArrow _ eff_body' _ _ = TyArrow _ ?eff_body_other _ _ =>
        pose proof
          (NResolveStaticEffect_deterministic
            rho eff_body eff_body' eff_body_other HLeftEff HRightEff);
        subst eff_body_other
    end.
    match goal with
    | HLeftEff : NResolveStaticEffect rho eff_summary eff_summary',
      HRightEff : NResolveStaticEffect rho eff_summary ?eff_summary_other
      |- TyArrow _ _ _ eff_summary' = TyArrow _ _ _ ?eff_summary_other =>
        pose proof
          (NResolveStaticEffect_deterministic
            rho eff_summary eff_summary' eff_summary_other
            HLeftEff HRightEff);
        subst eff_summary_other
    end.
    subst. reflexivity.
  - inversion HRight; subst.
    repeat match goal with
    | IH : forall ty_res : NTy,
        NResolveTy ?rho ?ty ty_res -> ?resolved = ty_res,
      HResolve : NResolveTy ?rho ?ty ?resolved_other |- _ =>
        specialize (IH _ HResolve); subst
    end.
    match goal with
    | HLeftEff : NResolveStaticEffect rho eff eff',
      HRightEff : NResolveStaticEffect rho eff ?eff_other
      |- TyForallRgn eff' _ = TyForallRgn ?eff_other _ =>
        pose proof
          (NResolveStaticEffect_deterministic
            rho eff eff' eff_other HLeftEff HRightEff);
        subst eff_other
    end.
    subst.
    reflexivity.
Qed.

Lemma NResolveRegionType_const_eval :
  forall rho rgn r,
    NResolveRegionType rho rgn (region_const_type r) ->
    eval_region_type rho rgn = Some r.
Proof.
  intros rho rgn r HResolve.
  inversion HResolve; subst; try reflexivity.
  assumption.
Qed.

Lemma NResolveRegionType_region_to_type :
  forall idx rho (rgn : Region idx) r,
    eval_region_any rho rgn = Some r ->
    NResolveRegionType rho (region_to_type rgn) (region_const_type r).
Proof.
  intros idx rho rgn r HResolve.
  destruct rgn; simpl in HResolve.
  - inversion HResolve; subst. constructor.
  - econstructor. exact HResolve.
  - inversion HResolve.
Qed.

Lemma NResolveRegionType_region_expr_to_type :
  forall rho rgn r,
    eval_region rho rgn = Some r ->
    NResolveRegionType rho (region_expr_to_type rgn) (region_const_type r).
Proof.
  intros rho rgn r HResolve.
  apply NResolveRegionType_region_to_type.
  exact HResolve.
Qed.

Lemma NResolveTy_ref_same_region :
  forall rho rgn ty r ty',
    NResolveTy rho (TyRef rgn ty) (TyRef (region_const_type r) ty') ->
    eval_region_type rho rgn = Some r.
Proof.
  intros rho rgn ty r ty' HResolve.
  destruct
    (NResolveTy_ref_inv rho rgn ty (TyRef (region_const_type r) ty') HResolve)
    as (rgn0 & ty0 & HRgn & _ & HEq).
  inversion HEq; subst.
  eapply NResolveRegionType_const_eval; eauto.
Qed.
