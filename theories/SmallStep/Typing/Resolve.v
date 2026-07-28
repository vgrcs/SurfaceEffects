From stdpp Require Import gmap.
From Stdlib Require Import Ascii.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Program.Equality.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Core.Values.
Require Import theories.SmallStep.Typing.Judgments.
Require Import theories.SmallStep.Typing.Types.

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

Lemma NResolveStaticEffect_app :
  forall rho eff1 eff1' eff2 eff2',
    NResolveStaticEffect rho eff1 eff1' ->
    NResolveStaticEffect rho eff2 eff2' ->
    NResolveStaticEffect rho (eff1 ++ eff2) (eff1' ++ eff2').
Proof.
  intros rho eff1 eff1' eff2 eff2' HResolve1 HResolve2.
  revert eff2 eff2' HResolve2.
  induction HResolve1; intros eff2 eff2' HResolve2; simpl.
  - exact HResolve2.
  - constructor; [assumption |].
    eapply IHHResolve1; eauto.
Qed.

Lemma NResolveStaticEffect_app_inv :
  forall rho eff1 eff2 eff',
    NResolveStaticEffect rho (eff1 ++ eff2) eff' ->
    exists eff1' eff2',
      eff' = eff1' ++ eff2' /\
      NResolveStaticEffect rho eff1 eff1' /\
      NResolveStaticEffect rho eff2 eff2'.
Proof.
  intros rho eff1.
  induction eff1 as [| action eff1 IH];
    intros eff2 eff' HResolve.
  - exists [], eff'.
    simpl in HResolve.
    repeat split; try assumption.
    constructor.
  - simpl in HResolve.
    inversion HResolve as
      [| rho0 action0 action' eff_tail eff_tail'
        HAction HRest];
      subst.
    destruct (IH eff2 eff_tail' HRest)
      as (eff1' & eff2' & HEq & HResolve1 & HResolve2).
    subst eff_tail'.
    exists (action' :: eff1'), eff2'.
    repeat split; try assumption.
    constructor; assumption.
Qed.

Lemma NResolveStaticEffect_static_union :
  forall rho eff1 eff1' eff2 eff2',
    NResolveStaticEffect rho eff1 eff1' ->
    NResolveStaticEffect rho eff2 eff2' ->
    NResolveStaticEffect rho
      (static_union eff1 eff2)
      (static_union eff1' eff2').
Proof.
  intros rho eff1 eff1' eff2 eff2' HResolve1 HResolve2.
  unfold static_union.
  eapply NResolveStaticEffect_app; eauto.
Qed.

Lemma NResolveStaticEffect_static_union_inv :
  forall rho eff1 eff2 eff',
    NResolveStaticEffect rho (static_union eff1 eff2) eff' ->
    exists eff1' eff2',
      eff' = static_union eff1' eff2' /\
      NResolveStaticEffect rho eff1 eff1' /\
      NResolveStaticEffect rho eff2 eff2'.
Proof.
  intros rho eff1 eff2 eff' HResolve.
  unfold static_union in HResolve.
  destruct
    (NResolveStaticEffect_app_inv rho eff1 eff2 eff' HResolve)
    as (eff1' & eff2' & HEq & HResolve1 & HResolve2).
  exists eff1', eff2'.
  unfold static_union.
  repeat split; assumption.
Qed.

Inductive NResolvedTy : NTy -> Prop :=
| NRTy_Nat :
    NResolvedTy TyNat
| NRTy_Bool :
    NResolvedTy TyBool
| NRTy_Unit :
    NResolvedTy TyUnit
| NRTy_Effect :
    NResolvedTy TyEffect
| NRTy_Pair :
    forall ty1 ty2,
      NResolvedTy ty1 ->
      NResolvedTy ty2 ->
      NResolvedTy (TyPair ty1 ty2)
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
| NResolve_Pair :
    forall rho ty1 ty1' ty2 ty2',
      NResolveTy rho ty1 ty1' ->
      NResolveTy rho ty2 ty2' ->
      NResolveTy rho (TyPair ty1 ty2) (TyPair ty1' ty2')
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

Inductive NRegionTypeWFAt : nat -> NRgnCtx -> RegionType -> Prop :=
| NRTWF_Const :
    forall depth omega r,
      NRegionTypeWFAt depth omega (region_const_type r)
| NRTWF_FVar :
    forall depth omega x,
      In x omega ->
      NRegionTypeWFAt depth omega (Rgn_FVar true true x)
| NRTWF_BVar :
    forall depth omega n,
      n < depth ->
      NRegionTypeWFAt depth omega (Rgn_BVar true true n).

Definition NRegionTypeWF (omega : NRgnCtx) (rgn : RegionType) : Prop :=
  NRegionTypeWFAt 0 omega rgn.

Inductive NStaticActionWFAt
    (depth : nat) (omega : NRgnCtx) : StaticAction -> Prop :=
| NSAWF_Alloc :
    forall rgn,
      NRegionTypeWFAt depth omega rgn ->
      NStaticActionWFAt depth omega (SAlloc rgn)
| NSAWF_Read :
    forall rgn,
      NRegionTypeWFAt depth omega rgn ->
      NStaticActionWFAt depth omega (SRead rgn)
| NSAWF_Write :
    forall rgn,
      NRegionTypeWFAt depth omega rgn ->
      NStaticActionWFAt depth omega (SWrite rgn).

Definition NStaticEffectWFAt
    (depth : nat) (omega : NRgnCtx) (eff : StaticEffect) : Prop :=
  Forall (NStaticActionWFAt depth omega) eff.

Definition NStaticEffectWF (omega : NRgnCtx) (eff : StaticEffect) : Prop :=
  NStaticEffectWFAt 0 omega eff.

Inductive NTyWFAt : nat -> NRgnCtx -> NTy -> Prop :=
| NTyWF_Nat :
    forall depth omega,
      NTyWFAt depth omega TyNat
| NTyWF_Bool :
    forall depth omega,
      NTyWFAt depth omega TyBool
| NTyWF_Unit :
    forall depth omega,
      NTyWFAt depth omega TyUnit
| NTyWF_Effect :
    forall depth omega,
      NTyWFAt depth omega TyEffect
| NTyWF_Pair :
    forall depth omega ty1 ty2,
      NTyWFAt depth omega ty1 ->
      NTyWFAt depth omega ty2 ->
      NTyWFAt depth omega (TyPair ty1 ty2)
| NTyWF_Ref :
    forall depth omega rgn ty,
      NRegionTypeWFAt depth omega rgn ->
      NTyWFAt depth omega ty ->
      NTyWFAt depth omega (TyRef rgn ty)
| NTyWF_Arrow :
    forall depth omega ty_arg eff_body ty_body eff_summary,
      NTyWFAt depth omega ty_arg ->
      NStaticEffectWFAt depth omega eff_body ->
      NTyWFAt depth omega ty_body ->
      NStaticEffectWFAt depth omega eff_summary ->
      NTyWFAt depth omega
        (TyArrow ty_arg eff_body ty_body eff_summary)
| NTyWF_ForallRgn :
    forall depth omega eff ty,
      NStaticEffectWFAt (S depth) omega eff ->
      NTyWFAt (S depth) omega ty ->
      NTyWFAt depth omega (TyForallRgn eff ty).

Definition NTyWF (omega : NRgnCtx) (ty : NTy) : Prop :=
  NTyWFAt 0 omega ty.

Definition NCtxWF (omega : NRgnCtx) (gamma : NCtx) : Prop :=
  Forall (fun binding => NTyWF omega (snd binding)) gamma.

Lemma NResolveRegionType_exists :
  forall depth omega rho rgn,
    (forall x, In x omega -> exists r, rho_lookup x rho = Some r) ->
    NRegionTypeWFAt depth omega rgn ->
    exists rgn',
      NResolveRegionType rho rgn rgn'.
Proof.
  intros depth omega rho rgn HRho HWF.
  inversion HWF; subst.
  - exists (region_const_type r). constructor.
  - destruct (HRho x H) as (r & HLookup).
    exists (region_const_type r). constructor. exact HLookup.
  - exists (Rgn_BVar true true n). constructor.
Qed.

Lemma NResolveStaticAction_exists :
  forall depth omega rho action,
    (forall x, In x omega -> exists r, rho_lookup x rho = Some r) ->
    NStaticActionWFAt depth omega action ->
    exists action',
      NResolveStaticAction rho action action'.
Proof.
  intros depth omega rho action HRho HWF.
  inversion HWF; subst;
    destruct
      (NResolveRegionType_exists depth omega rho rgn HRho H)
      as (rgn' & HRgn);
    eexists; constructor; exact HRgn.
Qed.

Lemma NResolveStaticEffect_exists :
  forall depth omega rho eff,
    (forall x, In x omega -> exists r, rho_lookup x rho = Some r) ->
    NStaticEffectWFAt depth omega eff ->
    exists eff',
      NResolveStaticEffect rho eff eff'.
Proof.
  intros depth omega rho eff HRho HWF.
  induction HWF as [| action eff HAction _ IH].
  - exists []. constructor.
  - destruct
      (NResolveStaticAction_exists depth omega rho action HRho HAction)
      as (action' & HActionResolve).
    destruct IH as (eff' & HEffResolve).
    exists (action' :: eff').
    constructor; assumption.
Qed.

Lemma NResolveTy_exists :
  forall depth omega rho ty,
    (forall x, In x omega -> exists r, rho_lookup x rho = Some r) ->
    NTyWFAt depth omega ty ->
    exists ty',
      NResolveTy rho ty ty'.
Proof.
  intros depth omega rho ty HRho HWF.
  induction HWF as
    [depth omega
    | depth omega
    | depth omega
    | depth omega
    | depth omega ty1 ty2 Hty1 IH1 Hty2 IH2
    | depth omega rgn ty HRgn Hty IHTy
    | depth omega ty_arg eff_body ty_body eff_summary
      HArgTy IHArg HBodyEff HBodyTy IHBody HSummaryEff
    | depth omega eff ty HEff Hty IHTy].
  - exists TyNat. constructor.
  - exists TyBool. constructor.
  - exists TyUnit. constructor.
  - exists TyEffect. constructor.
  - destruct (IH1 HRho) as (ty1_res & HTy1).
    destruct (IH2 HRho) as (ty2_res & HTy2).
    exists (TyPair ty1_res ty2_res).
    constructor; assumption.
  - destruct
      (NResolveRegionType_exists depth omega rho rgn HRho HRgn)
      as (rgn_res & HRgnResolve).
    destruct (IHTy HRho) as (ty_res & HTy).
    exists (TyRef rgn_res ty_res).
    constructor; assumption.
  - destruct (IHArg HRho) as (ty_arg_res & HArg).
    destruct
      (NResolveStaticEffect_exists depth omega rho eff_body HRho HBodyEff)
      as (eff_body_res & HBodyEffResolve).
    destruct (IHBody HRho) as (ty_body_res & HBody).
    destruct
      (NResolveStaticEffect_exists depth omega rho
        eff_summary HRho HSummaryEff)
      as (eff_summary_res & HSummaryEffResolve).
    exists
      (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res).
    constructor; assumption.
  - destruct
      (NResolveStaticEffect_exists (S depth) omega rho eff HRho HEff)
      as (eff_res & HEffResolve).
    destruct (IHTy HRho) as (ty_res & HTy).
    exists (TyForallRgn eff_res ty_res).
    constructor; assumption.
Qed.

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
  - inversion HRight; subst.
    repeat match goal with
    | IH : forall ty_res : NTy,
        NResolveTy ?rho ?ty ty_res -> ?resolved = ty_res,
      HResolve : NResolveTy ?rho ?ty ?resolved_other |- _ =>
        specialize (IH _ HResolve); subst
    end.
    reflexivity.
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

Lemma NResolveRegionType_open_region_type_at :
  forall rho k u u_res rgn rgn_res,
    NResolveRegionType rho u u_res ->
    NResolveRegionType rho rgn rgn_res ->
    NResolveRegionType rho
      (open_region_type_at k u rgn)
      (open_region_type_at k u_res rgn_res).
Proof.
  intros rho k u u_res rgn rgn_res HOpen HResolve.
  inversion HResolve; subst; simpl.
  - constructor.
  - constructor. assumption.
  - destruct (Nat.eqb n k); assumption || constructor.
Qed.

Lemma NResolveStaticAction_open_static_action_at :
  forall rho k u u_res action action_res,
    NResolveRegionType rho u u_res ->
    NResolveStaticAction rho action action_res ->
    NResolveStaticAction rho
      (open_static_action_at k u action)
      (open_static_action_at k u_res action_res).
Proof.
  intros rho k u u_res action action_res HOpen HResolve.
  inversion HResolve; subst; simpl; constructor;
    eapply NResolveRegionType_open_region_type_at; eauto.
Qed.

Lemma NResolveStaticEffect_open_static_effect_at :
  forall rho k u u_res eff eff_res,
    NResolveRegionType rho u u_res ->
    NResolveStaticEffect rho eff eff_res ->
    NResolveStaticEffect rho
      (open_static_effect_at k u eff)
      (open_static_effect_at k u_res eff_res).
Proof.
  intros rho k u u_res eff eff_res HOpen HResolve.
  induction HResolve as
    [rho | rho action action_res eff eff_res HAction _ IH];
    simpl; constructor.
  - eapply NResolveStaticAction_open_static_action_at; eauto.
  - exact (IH HOpen).
Qed.

Lemma NResolveTy_open_ty_at :
  forall rho k u u_res ty ty_res,
    NResolveRegionType rho u u_res ->
    NResolveTy rho ty ty_res ->
    NResolveTy rho
      (open_ty_at k u ty)
      (open_ty_at k u_res ty_res).
Proof.
  intros rho k u u_res ty ty_res HOpen HResolve.
  revert k u u_res HOpen.
  induction HResolve as
    [rho
    | rho
    | rho
    | rho
    | rho ty1 ty1_res ty2 ty2_res HTy1 IH1 HTy2 IH2
    | rho rgn rgn_res ty ty_res HRgn HTy IHTy
    | rho ty_arg ty_arg_res eff_body eff_body_res
      ty_body ty_body_res eff_summary eff_summary_res
      HArg IHArg HBodyEff HBody IHBody HSummaryEff
    | rho eff eff_res ty ty_res HEff HTy IHTy];
    intros k u u_res HOpen;
    simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - eapply NResolve_Pair.
    + exact (IH1 k u u_res HOpen).
    + exact (IH2 k u u_res HOpen).
  - eapply NResolve_Ref.
    + eapply NResolveRegionType_open_region_type_at; eauto.
    + exact (IHTy k u u_res HOpen).
  - eapply NResolve_Arrow.
    + exact (IHArg k u u_res HOpen).
    + eapply NResolveStaticEffect_open_static_effect_at; eauto.
    + exact (IHBody k u u_res HOpen).
    + eapply NResolveStaticEffect_open_static_effect_at; eauto.
  - eapply NResolve_ForallRgn.
    + eapply NResolveStaticEffect_open_static_effect_at; eauto.
    + exact (IHTy (S k) u u_res HOpen).
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

Lemma NResolveStaticEffect_open_static_effect :
  forall rho r eff eff_res r_val,
    eval_region rho r = Some r_val ->
    NResolveStaticEffect rho eff eff_res ->
    NResolveStaticEffect rho
      (open_static_effect r eff)
      (open_static_effect_type (region_const_type r_val) eff_res).
Proof.
  intros rho r eff eff_res r_val HRgn HResolve.
  unfold open_static_effect, open_static_effect_type.
  eapply NResolveStaticEffect_open_static_effect_at; eauto.
  eapply NResolveRegionType_region_expr_to_type.
  exact HRgn.
Qed.

Lemma NResolveTy_open_ty :
  forall rho r ty ty_res r_val,
    eval_region rho r = Some r_val ->
    NResolveTy rho ty ty_res ->
    NResolveTy rho
      (open_ty r ty)
      (open_ty_type (region_const_type r_val) ty_res).
Proof.
  intros rho r ty ty_res r_val HRgn HResolve.
  unfold open_ty, open_ty_type.
  eapply NResolveTy_open_ty_at; eauto.
  eapply NResolveRegionType_region_expr_to_type.
  exact HRgn.
Qed.

Lemma NResolveRegionType_wf0_const :
  forall omega rho rgn rgn_res,
    NRegionTypeWF omega rgn ->
    NResolveRegionType rho rgn rgn_res ->
    exists r,
      rgn_res = region_const_type r.
Proof.
  intros omega rho rgn rgn_res HWF HResolve.
  inversion HWF; subst.
  - inversion HResolve; subst.
    exists r. reflexivity.
  - inversion HResolve; subst.
    exists r. reflexivity.
  - lia.
Qed.

Lemma rho_lookup_extend_same :
  forall rho x r,
    rho_lookup x (rho_extend x r rho) = Some r.
Proof.
  intros rho x r.
  unfold rho_lookup, rho_extend, region_var_expr, update_R, find_R.
  simpl.
  apply lookup_insert.
Qed.

Lemma rho_lookup_extend_neq :
  forall rho x y r,
    y <> x ->
    rho_lookup y (rho_extend x r rho) = rho_lookup y rho.
Proof.
  intros rho x y r HNe.
  unfold rho_lookup, rho_extend, region_var_expr, update_R, find_R.
  simpl.
  apply lookup_insert_ne.
  intro HEq. apply HNe. symmetry. exact HEq.
Qed.

Lemma NResolveRegionType_extend_fresh :
  forall depth omega rho x r_val rgn rgn_res,
    ~ In x omega ->
    NRegionTypeWFAt depth omega rgn ->
    NResolveRegionType rho rgn rgn_res ->
    NResolveRegionType (rho_extend x r_val rho) rgn rgn_res.
Proof.
  intros depth omega rho x r_val rgn rgn_res HFresh HWF HResolve.
  inversion HWF; subst; inversion HResolve; subst.
  - constructor.
  - constructor.
    rewrite rho_lookup_extend_neq; [assumption |].
    intro HEq. subst.
    contradiction.
  - constructor.
Qed.

Lemma NResolveStaticAction_extend_fresh :
  forall depth omega rho x r_val action action_res,
    ~ In x omega ->
    NStaticActionWFAt depth omega action ->
    NResolveStaticAction rho action action_res ->
    NResolveStaticAction (rho_extend x r_val rho) action action_res.
Proof.
  intros depth omega rho x r_val action action_res HFresh HWF HResolve.
  inversion HWF; subst; inversion HResolve; subst; constructor;
    eapply NResolveRegionType_extend_fresh; eauto.
Qed.

Lemma NResolveStaticEffect_extend_fresh :
  forall depth omega rho x r_val eff eff_res,
    ~ In x omega ->
    NStaticEffectWFAt depth omega eff ->
    NResolveStaticEffect rho eff eff_res ->
    NResolveStaticEffect (rho_extend x r_val rho) eff eff_res.
Proof.
  intros depth omega rho x r_val eff eff_res HFresh HWF HResolve.
  revert HWF.
  induction HResolve as
    [rho | rho action action_res eff eff_res HAction _ IH];
    intros HWF; inversion HWF; subst; constructor.
  - eapply NResolveStaticAction_extend_fresh; eauto.
  - eapply IH; eauto.
Qed.

Lemma NResolveTy_extend_fresh :
  forall depth omega rho x r_val ty ty_res,
    ~ In x omega ->
    NTyWFAt depth omega ty ->
    NResolveTy rho ty ty_res ->
    NResolveTy (rho_extend x r_val rho) ty ty_res.
Proof.
  intros depth omega rho x r_val ty ty_res HFresh HWF HResolve.
  revert depth omega HFresh HWF.
  induction HResolve as
    [rho
    | rho
    | rho
    | rho
    | rho ty1 ty1_res ty2 ty2_res HTy1 IH1 HTy2 IH2
    | rho rgn rgn_res ty ty_res HRgn HTy IHTy
    | rho ty_arg ty_arg_res eff_body eff_body_res
      ty_body ty_body_res eff_summary eff_summary_res
      HArg IHArg HBodyEff HBody IHBody HSummaryEff
    | rho eff eff_res ty ty_res HEff HTy IHTy];
    intros depth omega HFresh HWF; inversion HWF; subst.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - eapply NResolve_Pair; eauto.
  - eapply NResolve_Ref.
    + eapply NResolveRegionType_extend_fresh; eauto.
    + eapply IHTy; eauto.
  - eapply NResolve_Arrow.
    + eapply IHArg; eauto.
    + eapply NResolveStaticEffect_extend_fresh; eauto.
    + eapply IHBody; eauto.
    + eapply NResolveStaticEffect_extend_fresh; eauto.
  - eapply NResolve_ForallRgn.
    + eapply NResolveStaticEffect_extend_fresh; eauto.
    + eapply IHTy; eauto.
Qed.

Lemma NResolveRegionType_rho_extend_close_region_type_at :
  forall depth omega rho x r_val rgn rgn_res,
    NRegionTypeWFAt depth (x :: omega) rgn ->
    NResolveRegionType rho (close_region_type_at depth x rgn) rgn_res ->
    NResolveRegionType (rho_extend x r_val rho) rgn
      (open_region_type_at depth (region_const_type r_val) rgn_res).
Proof.
  intros depth omega rho x r_val rgn rgn_res HWF HResolve.
  inversion HWF; subst; simpl in *.
  - inversion HResolve; subst. constructor.
  - destruct (ascii_dec x0 x) as [HEq | HNe].
    + subst x0.
      inversion HResolve; subst.
      simpl.
      rewrite Nat.eqb_refl.
      constructor.
      apply rho_lookup_extend_same.
    + inversion HResolve; subst.
      simpl.
      constructor.
      rewrite rho_lookup_extend_neq; [assumption | exact HNe].
  - inversion HResolve; subst.
    simpl.
    destruct (Nat.eqb n depth) eqn:HEq.
    + apply Nat.eqb_eq in HEq. lia.
    + constructor.
Qed.

Lemma NResolveStaticAction_rho_extend_close_static_action_at :
  forall depth omega rho x r_val action action_res,
    NStaticActionWFAt depth (x :: omega) action ->
    NResolveStaticAction rho
      (close_static_action_at depth x action)
      action_res ->
    NResolveStaticAction (rho_extend x r_val rho) action
      (open_static_action_at depth (region_const_type r_val) action_res).
Proof.
  intros depth omega rho x r_val action action_res HWF HResolve.
  inversion HWF; subst; inversion HResolve; subst; simpl; constructor;
    eapply NResolveRegionType_rho_extend_close_region_type_at; eauto.
Qed.

Lemma NResolveStaticEffect_rho_extend_close_static_effect_at :
  forall depth omega rho x r_val eff eff_res,
    NStaticEffectWFAt depth (x :: omega) eff ->
    NResolveStaticEffect rho
      (close_static_effect_at depth x eff)
      eff_res ->
    NResolveStaticEffect (rho_extend x r_val rho) eff
      (open_static_effect_at depth (region_const_type r_val) eff_res).
Proof.
  intros depth omega rho x r_val eff eff_res HWF HResolve.
  revert depth omega eff_res HWF HResolve.
  induction eff as [| action eff IH];
    intros depth omega eff_res HWF HResolve; inversion HResolve; subst;
    simpl in *; inversion HWF; subst; constructor.
  - eapply NResolveStaticAction_rho_extend_close_static_action_at; eauto.
  - eapply IH; eauto.
Qed.

Lemma NResolveTy_rho_extend_close_ty_at :
  forall depth omega rho x r_val ty ty_res,
    NTyWFAt depth (x :: omega) ty ->
    NResolveTy rho (close_ty_at depth x ty) ty_res ->
    NResolveTy (rho_extend x r_val rho) ty
      (open_ty_at depth (region_const_type r_val) ty_res).
Proof.
  intros depth omega rho x r_val ty ty_res HWF HResolve.
  revert depth omega ty_res HWF HResolve.
  induction ty as
    [| | | | ty1 IH1 ty2 IH2 | rgn ty IH
    | ty_arg IHArg eff_body ty_body IHBody eff_summary
    | eff ty IH];
    intros depth omega ty_res HWF HResolve;
    simpl in *; inversion HResolve; subst;
    inversion HWF; subst; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - eapply NResolve_Pair; eauto.
  - eapply NResolve_Ref.
    + eapply NResolveRegionType_rho_extend_close_region_type_at; eauto.
    + eapply IH; eauto.
  - eapply NResolve_Arrow.
    + eapply IHArg; eauto.
    + eapply NResolveStaticEffect_rho_extend_close_static_effect_at; eauto.
    + eapply IHBody; eauto.
    + eapply NResolveStaticEffect_rho_extend_close_static_effect_at; eauto.
  - eapply NResolve_ForallRgn.
    + eapply NResolveStaticEffect_rho_extend_close_static_effect_at; eauto.
    + eapply IH; eauto.
Qed.

Lemma NResolveTy_rho_extend_close_ty :
  forall omega rho x r_val ty ty_res,
    NTyWFAt 0 (x :: omega) ty ->
    NResolveTy rho (close_ty x ty) ty_res ->
    NResolveTy (rho_extend x r_val rho) ty
      (open_ty_type (region_const_type r_val) ty_res).
Proof.
  intros omega rho x r_val ty ty_res HWF HResolve.
  unfold close_ty, open_ty_type.
  eapply NResolveTy_rho_extend_close_ty_at; eauto.
Qed.

Lemma NResolveStaticEffect_static_noalloc :
  forall rho eff eff',
    NResolveStaticEffect rho eff eff' ->
    static_noalloc eff ->
    static_noalloc eff'.
Proof.
  unfold static_noalloc.
  intros rho eff eff' HResolve.
  induction HResolve as
    [rho | rho action action' eff eff' HAction _ IH];
    intros HNoAlloc r HIn; simpl in HIn.
  - contradiction.
  - destruct HIn as [HHead | HTail].
    + subst action'.
      inversion HAction; subst.
      eapply HNoAlloc. simpl. left. reflexivity.
    + eapply IH.
      * intros r0 HIn0.
        eapply HNoAlloc. simpl. right. exact HIn0.
      * exact HTail.
Qed.

Lemma NResolveStaticEffect_static_noalloc_inv :
  forall rho eff eff',
    NResolveStaticEffect rho eff eff' ->
    static_noalloc eff' ->
    static_noalloc eff.
Proof.
  unfold static_noalloc.
  intros rho eff eff' HResolve.
  induction HResolve as
    [rho | rho action action' eff eff' HAction _ IH];
    intros HNoAlloc r HIn; simpl in HIn.
  - contradiction.
  - destruct HIn as [HHead | HTail].
    + subst action.
      inversion HAction; subst.
      eapply HNoAlloc. simpl. left. reflexivity.
    + eapply IH.
      * intros r0 HIn0.
        eapply HNoAlloc. simpl. right. exact HIn0.
      * exact HTail.
Qed.

Lemma NResolveStaticEffect_static_readonly :
  forall rho eff eff',
    NResolveStaticEffect rho eff eff' ->
    static_readonly eff ->
    static_readonly eff'.
Proof.
  unfold static_readonly.
  intros rho eff eff' HResolve.
  induction HResolve as
    [rho | rho action action' eff eff' HAction _ IH];
    intros HReadOnly r HIn; simpl in HIn.
  - contradiction.
  - destruct HIn as [HHead | HTail].
    + subst action'.
      inversion HAction; subst.
      eapply HReadOnly. simpl. left. reflexivity.
    + eapply IH.
      * intros r0 HIn0.
        eapply HReadOnly. simpl. right. exact HIn0.
      * exact HTail.
Qed.

Lemma NResolveStaticEffect_static_readonly_inv :
  forall rho eff eff',
    NResolveStaticEffect rho eff eff' ->
    static_readonly eff' ->
    static_readonly eff.
Proof.
  unfold static_readonly.
  intros rho eff eff' HResolve.
  induction HResolve as
    [rho | rho action action' eff eff' HAction _ IH];
    intros HReadOnly r HIn; simpl in HIn.
  - contradiction.
  - destruct HIn as [HHead | HTail].
    + subst action.
      inversion HAction; subst.
      eapply HReadOnly. simpl. left. reflexivity.
    + eapply IH.
      * intros r0 HIn0.
        eapply HReadOnly. simpl. right. exact HIn0.
      * exact HTail.
Qed.

Lemma NResolveStaticEffect_static_heap_neutral :
  forall rho eff eff',
    NResolveStaticEffect rho eff eff' ->
    static_heap_neutral eff ->
    static_heap_neutral eff'.
Proof.
  intros rho eff eff' HResolve [HNoAlloc HReadOnly].
  split.
  - eapply NResolveStaticEffect_static_noalloc; eauto.
  - eapply NResolveStaticEffect_static_readonly; eauto.
Qed.

Lemma NResolveStaticEffect_static_heap_neutral_inv :
  forall rho eff eff',
    NResolveStaticEffect rho eff eff' ->
    static_heap_neutral eff' ->
    static_heap_neutral eff.
Proof.
  intros rho eff eff' HResolve [HNoAlloc HReadOnly].
  split.
  - eapply NResolveStaticEffect_static_noalloc_inv; eauto.
  - eapply NResolveStaticEffect_static_readonly_inv; eauto.
Qed.

Lemma NResolveStaticEffect_static_heap_neutral_transfer :
  forall rho eff_src eff_dst eff_res,
    NResolveStaticEffect rho eff_src eff_res ->
    NResolveStaticEffect rho eff_dst eff_res ->
    static_heap_neutral eff_src ->
    static_heap_neutral eff_dst.
Proof.
  intros rho eff_src eff_dst eff_res HSrc HDst HNeutral.
  pose proof
    (NResolveStaticEffect_static_heap_neutral
      rho eff_src eff_res HSrc HNeutral)
    as HNeutralRes.
  eapply NResolveStaticEffect_static_heap_neutral_inv; eauto.
Qed.

Lemma NResolveStaticEffect_static_heap_neutral_transfer_any :
  forall rho_src rho_dst eff_src eff_dst eff_res,
    NResolveStaticEffect rho_src eff_src eff_res ->
    NResolveStaticEffect rho_dst eff_dst eff_res ->
    static_heap_neutral eff_src ->
    static_heap_neutral eff_dst.
Proof.
  intros rho_src rho_dst eff_src eff_dst eff_res
    HSrc HDst HNeutral.
  pose proof
    (NResolveStaticEffect_static_heap_neutral
      rho_src eff_src eff_res HSrc HNeutral)
    as HNeutralRes.
  eapply NResolveStaticEffect_static_heap_neutral_inv; eauto.
Qed.
