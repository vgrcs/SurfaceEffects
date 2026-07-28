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

Inductive ResolvedRegionExpr : RegionExpr -> Prop :=
| RR_Const :
    forall r,
      ResolvedRegionExpr (region_const_expr r).

Inductive ResolvedRegionType : RegionType -> Prop :=
| RRT_Const :
    forall r,
      ResolvedRegionType (region_const_type r)
| RRT_BVar :
    forall n,
      ResolvedRegionType (Rgn_BVar true true n).

Inductive ResolveRegionType :
    Rho -> RegionType -> RegionType -> Prop :=
| ResolveRegion_Const :
    forall rho r,
      ResolveRegionType rho (region_const_type r) (region_const_type r)
| ResolveRegion_FVar :
    forall rho x r,
      rho_lookup x rho = Some r ->
      ResolveRegionType rho (Rgn_FVar true true x) (region_const_type r)
| ResolveRegion_BVar :
    forall rho n,
      ResolveRegionType rho
        (Rgn_BVar true true n)
        (Rgn_BVar true true n).

Inductive ResolvedStaticAction : StaticAction -> Prop :=
| RSA_Alloc :
    forall rgn,
      ResolvedRegionType rgn ->
      ResolvedStaticAction (SAlloc rgn)
| RSA_Read :
    forall rgn,
      ResolvedRegionType rgn ->
      ResolvedStaticAction (SRead rgn)
| RSA_Write :
    forall rgn,
      ResolvedRegionType rgn ->
      ResolvedStaticAction (SWrite rgn).

Definition ResolvedStaticEffect (eff : StaticEffect) : Prop :=
  Forall ResolvedStaticAction eff.

Inductive ResolveStaticAction :
    Rho -> StaticAction -> StaticAction -> Prop :=
| Resolve_SAlloc :
    forall rho rgn rgn',
      ResolveRegionType rho rgn rgn' ->
      ResolveStaticAction rho (SAlloc rgn) (SAlloc rgn')
| Resolve_SRead :
    forall rho rgn rgn',
      ResolveRegionType rho rgn rgn' ->
      ResolveStaticAction rho (SRead rgn) (SRead rgn')
| Resolve_SWrite :
    forall rho rgn rgn',
      ResolveRegionType rho rgn rgn' ->
      ResolveStaticAction rho (SWrite rgn) (SWrite rgn').

Inductive ResolveStaticEffect :
    Rho -> StaticEffect -> StaticEffect -> Prop :=
| ResolveStaticEffect_Nil :
    forall rho,
      ResolveStaticEffect rho [] []
| ResolveStaticEffect_Cons :
    forall rho action action' eff eff',
      ResolveStaticAction rho action action' ->
      ResolveStaticEffect rho eff eff' ->
      ResolveStaticEffect rho (action :: eff) (action' :: eff').

Lemma ResolveStaticEffect_app :
  forall rho eff1 eff1' eff2 eff2',
    ResolveStaticEffect rho eff1 eff1' ->
    ResolveStaticEffect rho eff2 eff2' ->
    ResolveStaticEffect rho (eff1 ++ eff2) (eff1' ++ eff2').
Proof.
  intros rho eff1 eff1' eff2 eff2' HResolve1 HResolve2.
  revert eff2 eff2' HResolve2.
  induction HResolve1; intros eff2 eff2' HResolve2; simpl.
  - exact HResolve2.
  - constructor; [assumption |].
    eapply IHHResolve1; eauto.
Qed.

Lemma ResolveStaticEffect_app_inv :
  forall rho eff1 eff2 eff',
    ResolveStaticEffect rho (eff1 ++ eff2) eff' ->
    exists eff1' eff2',
      eff' = eff1' ++ eff2' /\
      ResolveStaticEffect rho eff1 eff1' /\
      ResolveStaticEffect rho eff2 eff2'.
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

Lemma ResolveStaticEffect_static_union :
  forall rho eff1 eff1' eff2 eff2',
    ResolveStaticEffect rho eff1 eff1' ->
    ResolveStaticEffect rho eff2 eff2' ->
    ResolveStaticEffect rho
      (static_union eff1 eff2)
      (static_union eff1' eff2').
Proof.
  intros rho eff1 eff1' eff2 eff2' HResolve1 HResolve2.
  unfold static_union.
  eapply ResolveStaticEffect_app; eauto.
Qed.

Lemma ResolveStaticEffect_static_union_inv :
  forall rho eff1 eff2 eff',
    ResolveStaticEffect rho (static_union eff1 eff2) eff' ->
    exists eff1' eff2',
      eff' = static_union eff1' eff2' /\
      ResolveStaticEffect rho eff1 eff1' /\
      ResolveStaticEffect rho eff2 eff2'.
Proof.
  intros rho eff1 eff2 eff' HResolve.
  unfold static_union in HResolve.
  destruct
    (ResolveStaticEffect_app_inv rho eff1 eff2 eff' HResolve)
    as (eff1' & eff2' & HEq & HResolve1 & HResolve2).
  exists eff1', eff2'.
  unfold static_union.
  repeat split; assumption.
Qed.

Inductive ResolvedTy : Ty -> Prop :=
| RTy_Nat :
    ResolvedTy TyNat
| RTy_Bool :
    ResolvedTy TyBool
| RTy_Unit :
    ResolvedTy TyUnit
| RTy_Effect :
    ResolvedTy TyEffect
| RTy_Pair :
    forall ty1 ty2,
      ResolvedTy ty1 ->
      ResolvedTy ty2 ->
      ResolvedTy (TyPair ty1 ty2)
| RTy_Ref :
    forall rgn ty,
      ResolvedRegionType rgn ->
      ResolvedTy ty ->
      ResolvedTy (TyRef rgn ty)
| RTy_Arrow :
    forall ty_arg eff_body ty_body eff_summary,
      ResolvedTy ty_arg ->
      ResolvedStaticEffect eff_body ->
      ResolvedTy ty_body ->
      ResolvedStaticEffect eff_summary ->
      ResolvedTy (TyArrow ty_arg eff_body ty_body eff_summary)
| RTy_ForallRgn :
    forall eff ty,
      ResolvedStaticEffect eff ->
      ResolvedTy ty ->
      ResolvedTy (TyForallRgn eff ty).

Inductive ResolveTy : Rho -> Ty -> Ty -> Prop :=
| Resolve_Nat :
    forall rho,
      ResolveTy rho TyNat TyNat
| Resolve_Bool :
    forall rho,
      ResolveTy rho TyBool TyBool
| Resolve_Unit :
    forall rho,
      ResolveTy rho TyUnit TyUnit
| Resolve_Effect :
    forall rho,
      ResolveTy rho TyEffect TyEffect
| Resolve_Pair :
    forall rho ty1 ty1' ty2 ty2',
      ResolveTy rho ty1 ty1' ->
      ResolveTy rho ty2 ty2' ->
      ResolveTy rho (TyPair ty1 ty2) (TyPair ty1' ty2')
| Resolve_Ref :
    forall rho rgn rgn' ty ty',
      ResolveRegionType rho rgn rgn' ->
      ResolveTy rho ty ty' ->
      ResolveTy rho (TyRef rgn ty) (TyRef rgn' ty')
| Resolve_Arrow :
    forall rho ty_arg ty_arg' eff_body eff_body'
      ty_body ty_body' eff_summary eff_summary',
      ResolveTy rho ty_arg ty_arg' ->
      ResolveStaticEffect rho eff_body eff_body' ->
      ResolveTy rho ty_body ty_body' ->
      ResolveStaticEffect rho eff_summary eff_summary' ->
      ResolveTy rho
        (TyArrow ty_arg eff_body ty_body eff_summary)
        (TyArrow ty_arg' eff_body' ty_body' eff_summary')
| Resolve_ForallRgn :
    forall rho eff eff' ty ty',
      ResolveStaticEffect rho eff eff' ->
      ResolveTy rho ty ty' ->
      ResolveTy rho (TyForallRgn eff ty) (TyForallRgn eff' ty').

Inductive RegionTypeWFAt : nat -> RgnCtx -> RegionType -> Prop :=
| RTWF_Const :
    forall depth omega r,
      RegionTypeWFAt depth omega (region_const_type r)
| RTWF_FVar :
    forall depth omega x,
      In x omega ->
      RegionTypeWFAt depth omega (Rgn_FVar true true x)
| RTWF_BVar :
    forall depth omega n,
      n < depth ->
      RegionTypeWFAt depth omega (Rgn_BVar true true n).

Definition RegionTypeWF (omega : RgnCtx) (rgn : RegionType) : Prop :=
  RegionTypeWFAt 0 omega rgn.

Inductive StaticActionWFAt
    (depth : nat) (omega : RgnCtx) : StaticAction -> Prop :=
| SAWF_Alloc :
    forall rgn,
      RegionTypeWFAt depth omega rgn ->
      StaticActionWFAt depth omega (SAlloc rgn)
| SAWF_Read :
    forall rgn,
      RegionTypeWFAt depth omega rgn ->
      StaticActionWFAt depth omega (SRead rgn)
| SAWF_Write :
    forall rgn,
      RegionTypeWFAt depth omega rgn ->
      StaticActionWFAt depth omega (SWrite rgn).

Definition StaticEffectWFAt
    (depth : nat) (omega : RgnCtx) (eff : StaticEffect) : Prop :=
  Forall (StaticActionWFAt depth omega) eff.

Definition StaticEffectWF (omega : RgnCtx) (eff : StaticEffect) : Prop :=
  StaticEffectWFAt 0 omega eff.

Inductive TyWFAt : nat -> RgnCtx -> Ty -> Prop :=
| TyWF_Nat :
    forall depth omega,
      TyWFAt depth omega TyNat
| TyWF_Bool :
    forall depth omega,
      TyWFAt depth omega TyBool
| TyWF_Unit :
    forall depth omega,
      TyWFAt depth omega TyUnit
| TyWF_Effect :
    forall depth omega,
      TyWFAt depth omega TyEffect
| TyWF_Pair :
    forall depth omega ty1 ty2,
      TyWFAt depth omega ty1 ->
      TyWFAt depth omega ty2 ->
      TyWFAt depth omega (TyPair ty1 ty2)
| TyWF_Ref :
    forall depth omega rgn ty,
      RegionTypeWFAt depth omega rgn ->
      TyWFAt depth omega ty ->
      TyWFAt depth omega (TyRef rgn ty)
| TyWF_Arrow :
    forall depth omega ty_arg eff_body ty_body eff_summary,
      TyWFAt depth omega ty_arg ->
      StaticEffectWFAt depth omega eff_body ->
      TyWFAt depth omega ty_body ->
      StaticEffectWFAt depth omega eff_summary ->
      TyWFAt depth omega
        (TyArrow ty_arg eff_body ty_body eff_summary)
| TyWF_ForallRgn :
    forall depth omega eff ty,
      StaticEffectWFAt (S depth) omega eff ->
      TyWFAt (S depth) omega ty ->
      TyWFAt depth omega (TyForallRgn eff ty).

Definition TyWF (omega : RgnCtx) (ty : Ty) : Prop :=
  TyWFAt 0 omega ty.

Definition CtxWF (omega : RgnCtx) (gamma : Ctx) : Prop :=
  Forall (fun binding => TyWF omega (snd binding)) gamma.

Lemma ResolveRegionType_exists :
  forall depth omega rho rgn,
    (forall x, In x omega -> exists r, rho_lookup x rho = Some r) ->
    RegionTypeWFAt depth omega rgn ->
    exists rgn',
      ResolveRegionType rho rgn rgn'.
Proof.
  intros depth omega rho rgn HRho HWF.
  inversion HWF; subst.
  - exists (region_const_type r). constructor.
  - destruct (HRho x H) as (r & HLookup).
    exists (region_const_type r). constructor. exact HLookup.
  - exists (Rgn_BVar true true n). constructor.
Qed.

Lemma ResolveStaticAction_exists :
  forall depth omega rho action,
    (forall x, In x omega -> exists r, rho_lookup x rho = Some r) ->
    StaticActionWFAt depth omega action ->
    exists action',
      ResolveStaticAction rho action action'.
Proof.
  intros depth omega rho action HRho HWF.
  inversion HWF; subst;
    destruct
      (ResolveRegionType_exists depth omega rho rgn HRho H)
      as (rgn' & HRgn);
    eexists; constructor; exact HRgn.
Qed.

Lemma ResolveStaticEffect_exists :
  forall depth omega rho eff,
    (forall x, In x omega -> exists r, rho_lookup x rho = Some r) ->
    StaticEffectWFAt depth omega eff ->
    exists eff',
      ResolveStaticEffect rho eff eff'.
Proof.
  intros depth omega rho eff HRho HWF.
  induction HWF as [| action eff HAction _ IH].
  - exists []. constructor.
  - destruct
      (ResolveStaticAction_exists depth omega rho action HRho HAction)
      as (action' & HActionResolve).
    destruct IH as (eff' & HEffResolve).
    exists (action' :: eff').
    constructor; assumption.
Qed.

Lemma ResolveTy_exists :
  forall depth omega rho ty,
    (forall x, In x omega -> exists r, rho_lookup x rho = Some r) ->
    TyWFAt depth omega ty ->
    exists ty',
      ResolveTy rho ty ty'.
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
      (ResolveRegionType_exists depth omega rho rgn HRho HRgn)
      as (rgn_res & HRgnResolve).
    destruct (IHTy HRho) as (ty_res & HTy).
    exists (TyRef rgn_res ty_res).
    constructor; assumption.
  - destruct (IHArg HRho) as (ty_arg_res & HArg).
    destruct
      (ResolveStaticEffect_exists depth omega rho eff_body HRho HBodyEff)
      as (eff_body_res & HBodyEffResolve).
    destruct (IHBody HRho) as (ty_body_res & HBody).
    destruct
      (ResolveStaticEffect_exists depth omega rho
        eff_summary HRho HSummaryEff)
      as (eff_summary_res & HSummaryEffResolve).
    exists
      (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res).
    constructor; assumption.
  - destruct
      (ResolveStaticEffect_exists (S depth) omega rho eff HRho HEff)
      as (eff_res & HEffResolve).
    destruct (IHTy HRho) as (ty_res & HTy).
    exists (TyForallRgn eff_res ty_res).
    constructor; assumption.
Qed.

Lemma ResolveRegionType_resolved :
  forall rho rgn rgn',
    ResolveRegionType rho rgn rgn' ->
    ResolvedRegionType rgn'.
Proof.
  intros rho rgn rgn' HResolve.
  inversion HResolve; subst; constructor.
Qed.

Lemma ResolveStaticAction_resolved :
  forall rho action action',
    ResolveStaticAction rho action action' ->
    ResolvedStaticAction action'.
Proof.
  intros rho action action' HResolve.
  inversion HResolve; subst; constructor;
    eauto using ResolveRegionType_resolved.
Qed.

Lemma ResolveStaticEffect_resolved :
  forall rho eff eff',
    ResolveStaticEffect rho eff eff' ->
    ResolvedStaticEffect eff'.
Proof.
  intros rho eff eff' HResolve.
  induction HResolve; constructor;
    eauto using ResolveStaticAction_resolved.
Qed.

Lemma ResolveTy_resolved :
  forall rho ty ty',
    ResolveTy rho ty ty' ->
    ResolvedTy ty'.
Proof.
  intros rho ty ty' HResolve.
  induction HResolve; constructor;
    eauto using ResolveRegionType_resolved,
      ResolveStaticEffect_resolved.
Qed.

Lemma ResolveTy_ref_inv :
  forall rho rgn ty ty_resolved,
    ResolveTy rho (TyRef rgn ty) ty_resolved ->
    exists rgn' ty',
      ResolveRegionType rho rgn rgn' /\
      ResolveTy rho ty ty' /\
      ty_resolved = TyRef rgn' ty'.
Proof.
  intros rho rgn ty ty_resolved HResolve.
  inversion HResolve; subst.
  exists rgn', ty'.
  repeat split; assumption || reflexivity.
Qed.

Lemma ResolveRegionType_deterministic :
  forall rho rgn rgn1 rgn2,
    ResolveRegionType rho rgn rgn1 ->
    ResolveRegionType rho rgn rgn2 ->
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

Lemma ResolveStaticAction_deterministic :
  forall rho action action1 action2,
    ResolveStaticAction rho action action1 ->
    ResolveStaticAction rho action action2 ->
    action1 = action2.
Proof.
  intros rho action action1 action2 HLeft HRight.
  inversion HLeft; subst; inversion HRight; subst;
    match goal with
    | H1 : ResolveRegionType rho ?rgn ?rgn1,
      H2 : ResolveRegionType rho ?rgn ?rgn2 |- _ =>
        pose proof
          (ResolveRegionType_deterministic rho rgn rgn1 rgn2 H1 H2);
        subst
    end;
    reflexivity.
Qed.

Lemma ResolveStaticEffect_deterministic :
  forall rho eff eff1 eff2,
    ResolveStaticEffect rho eff eff1 ->
    ResolveStaticEffect rho eff eff2 ->
    eff1 = eff2.
Proof.
  intros rho eff eff1 eff2 HLeft.
  revert eff2.
  induction HLeft; intros eff2 HRight.
  - inversion HRight; reflexivity.
  - inversion HRight; subst.
    match goal with
    | H1 : ResolveStaticAction rho action action',
      H2 : ResolveStaticAction rho action ?action_other |- _ =>
        pose proof
          (ResolveStaticAction_deterministic
            rho action action' action_other H1 H2);
        subst action_other
    end.
    match goal with
    | HRest : ResolveStaticEffect rho eff ?eff_other |- _ =>
        specialize (IHHLeft _ HRest); subst
    end.
    reflexivity.
Qed.

Lemma ResolveTy_deterministic :
  forall rho ty ty1 ty2,
    ResolveTy rho ty ty1 ->
    ResolveTy rho ty ty2 ->
    ty1 = ty2.
Proof.
  intros rho ty ty_left ty_right HLeft.
  revert ty_right.
  induction HLeft; intros ty_right HRight;
    try solve [inversion HRight; subst; reflexivity].
  - inversion HRight; subst.
    repeat match goal with
    | IH : forall ty_res : Ty,
        ResolveTy ?rho ?ty ty_res -> ?resolved = ty_res,
      HResolve : ResolveTy ?rho ?ty ?resolved_other |- _ =>
        specialize (IH _ HResolve); subst
    end.
    reflexivity.
  - destruct
      (ResolveTy_ref_inv rho rgn ty ty_right HRight)
      as (rgn_other & ty_other & HRgnOther & HTyOther & ->).
    pose proof
      (ResolveRegionType_deterministic
        rho rgn rgn' rgn_other H HRgnOther);
      subst rgn_other.
    specialize (IHHLeft _ HTyOther). subst.
    reflexivity.
  - inversion HRight; subst.
    repeat match goal with
    | IH : forall ty_res : Ty,
        ResolveTy ?rho ?ty ty_res -> ?resolved = ty_res,
      HResolve : ResolveTy ?rho ?ty ?resolved_other |- _ =>
        specialize (IH _ HResolve); subst
    end.
    match goal with
    | HLeftEff : ResolveStaticEffect rho eff_body eff_body',
      HRightEff : ResolveStaticEffect rho eff_body ?eff_body_other
      |- TyArrow _ eff_body' _ _ = TyArrow _ ?eff_body_other _ _ =>
        pose proof
          (ResolveStaticEffect_deterministic
            rho eff_body eff_body' eff_body_other HLeftEff HRightEff);
        subst eff_body_other
    end.
    match goal with
    | HLeftEff : ResolveStaticEffect rho eff_summary eff_summary',
      HRightEff : ResolveStaticEffect rho eff_summary ?eff_summary_other
      |- TyArrow _ _ _ eff_summary' = TyArrow _ _ _ ?eff_summary_other =>
        pose proof
          (ResolveStaticEffect_deterministic
            rho eff_summary eff_summary' eff_summary_other
            HLeftEff HRightEff);
        subst eff_summary_other
    end.
    subst. reflexivity.
  - inversion HRight; subst.
    repeat match goal with
    | IH : forall ty_res : Ty,
        ResolveTy ?rho ?ty ty_res -> ?resolved = ty_res,
      HResolve : ResolveTy ?rho ?ty ?resolved_other |- _ =>
        specialize (IH _ HResolve); subst
    end.
    match goal with
    | HLeftEff : ResolveStaticEffect rho eff eff',
      HRightEff : ResolveStaticEffect rho eff ?eff_other
      |- TyForallRgn eff' _ = TyForallRgn ?eff_other _ =>
        pose proof
          (ResolveStaticEffect_deterministic
            rho eff eff' eff_other HLeftEff HRightEff);
        subst eff_other
    end.
    subst.
    reflexivity.
Qed.

Lemma ResolveRegionType_open_region_type_at :
  forall rho k u u_res rgn rgn_res,
    ResolveRegionType rho u u_res ->
    ResolveRegionType rho rgn rgn_res ->
    ResolveRegionType rho
      (open_region_type_at k u rgn)
      (open_region_type_at k u_res rgn_res).
Proof.
  intros rho k u u_res rgn rgn_res HOpen HResolve.
  inversion HResolve; subst; simpl.
  - constructor.
  - constructor. assumption.
  - destruct (Nat.eqb n k); assumption || constructor.
Qed.

Lemma ResolveStaticAction_open_static_action_at :
  forall rho k u u_res action action_res,
    ResolveRegionType rho u u_res ->
    ResolveStaticAction rho action action_res ->
    ResolveStaticAction rho
      (open_static_action_at k u action)
      (open_static_action_at k u_res action_res).
Proof.
  intros rho k u u_res action action_res HOpen HResolve.
  inversion HResolve; subst; simpl; constructor;
    eapply ResolveRegionType_open_region_type_at; eauto.
Qed.

Lemma ResolveStaticEffect_open_static_effect_at :
  forall rho k u u_res eff eff_res,
    ResolveRegionType rho u u_res ->
    ResolveStaticEffect rho eff eff_res ->
    ResolveStaticEffect rho
      (open_static_effect_at k u eff)
      (open_static_effect_at k u_res eff_res).
Proof.
  intros rho k u u_res eff eff_res HOpen HResolve.
  induction HResolve as
    [rho | rho action action_res eff eff_res HAction _ IH];
    simpl; constructor.
  - eapply ResolveStaticAction_open_static_action_at; eauto.
  - exact (IH HOpen).
Qed.

Lemma ResolveTy_open_ty_at :
  forall rho k u u_res ty ty_res,
    ResolveRegionType rho u u_res ->
    ResolveTy rho ty ty_res ->
    ResolveTy rho
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
  - eapply Resolve_Pair.
    + exact (IH1 k u u_res HOpen).
    + exact (IH2 k u u_res HOpen).
  - eapply Resolve_Ref.
    + eapply ResolveRegionType_open_region_type_at; eauto.
    + exact (IHTy k u u_res HOpen).
  - eapply Resolve_Arrow.
    + exact (IHArg k u u_res HOpen).
    + eapply ResolveStaticEffect_open_static_effect_at; eauto.
    + exact (IHBody k u u_res HOpen).
    + eapply ResolveStaticEffect_open_static_effect_at; eauto.
  - eapply Resolve_ForallRgn.
    + eapply ResolveStaticEffect_open_static_effect_at; eauto.
    + exact (IHTy (S k) u u_res HOpen).
Qed.

Lemma ResolveRegionType_const_eval :
  forall rho rgn r,
    ResolveRegionType rho rgn (region_const_type r) ->
    eval_region_type rho rgn = Some r.
Proof.
  intros rho rgn r HResolve.
  inversion HResolve; subst; try reflexivity.
  assumption.
Qed.

Lemma ResolveRegionType_region_to_type :
  forall idx rho (rgn : Region idx) r,
    eval_region_any rho rgn = Some r ->
    ResolveRegionType rho (region_to_type rgn) (region_const_type r).
Proof.
  intros idx rho rgn r HResolve.
  destruct rgn; simpl in HResolve.
  - inversion HResolve; subst. constructor.
  - econstructor. exact HResolve.
  - inversion HResolve.
Qed.

Lemma ResolveRegionType_region_expr_to_type :
  forall rho rgn r,
    eval_region rho rgn = Some r ->
    ResolveRegionType rho (region_expr_to_type rgn) (region_const_type r).
Proof.
  intros rho rgn r HResolve.
  apply ResolveRegionType_region_to_type.
  exact HResolve.
Qed.

Lemma ResolveTy_ref_same_region :
  forall rho rgn ty r ty',
    ResolveTy rho (TyRef rgn ty) (TyRef (region_const_type r) ty') ->
    eval_region_type rho rgn = Some r.
Proof.
  intros rho rgn ty r ty' HResolve.
  destruct
    (ResolveTy_ref_inv rho rgn ty (TyRef (region_const_type r) ty') HResolve)
    as (rgn0 & ty0 & HRgn & _ & HEq).
  inversion HEq; subst.
  eapply ResolveRegionType_const_eval; eauto.
Qed.

Lemma ResolveStaticEffect_open_static_effect :
  forall rho r eff eff_res r_val,
    eval_region rho r = Some r_val ->
    ResolveStaticEffect rho eff eff_res ->
    ResolveStaticEffect rho
      (open_static_effect r eff)
      (open_static_effect_type (region_const_type r_val) eff_res).
Proof.
  intros rho r eff eff_res r_val HRgn HResolve.
  unfold open_static_effect, open_static_effect_type.
  eapply ResolveStaticEffect_open_static_effect_at; eauto.
  eapply ResolveRegionType_region_expr_to_type.
  exact HRgn.
Qed.

Lemma ResolveTy_open_ty :
  forall rho r ty ty_res r_val,
    eval_region rho r = Some r_val ->
    ResolveTy rho ty ty_res ->
    ResolveTy rho
      (open_ty r ty)
      (open_ty_type (region_const_type r_val) ty_res).
Proof.
  intros rho r ty ty_res r_val HRgn HResolve.
  unfold open_ty, open_ty_type.
  eapply ResolveTy_open_ty_at; eauto.
  eapply ResolveRegionType_region_expr_to_type.
  exact HRgn.
Qed.

Lemma ResolveRegionType_wf0_const :
  forall omega rho rgn rgn_res,
    RegionTypeWF omega rgn ->
    ResolveRegionType rho rgn rgn_res ->
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

Lemma ResolveRegionType_extend_fresh :
  forall depth omega rho x r_val rgn rgn_res,
    ~ In x omega ->
    RegionTypeWFAt depth omega rgn ->
    ResolveRegionType rho rgn rgn_res ->
    ResolveRegionType (rho_extend x r_val rho) rgn rgn_res.
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

Lemma ResolveStaticAction_extend_fresh :
  forall depth omega rho x r_val action action_res,
    ~ In x omega ->
    StaticActionWFAt depth omega action ->
    ResolveStaticAction rho action action_res ->
    ResolveStaticAction (rho_extend x r_val rho) action action_res.
Proof.
  intros depth omega rho x r_val action action_res HFresh HWF HResolve.
  inversion HWF; subst; inversion HResolve; subst; constructor;
    eapply ResolveRegionType_extend_fresh; eauto.
Qed.

Lemma ResolveStaticEffect_extend_fresh :
  forall depth omega rho x r_val eff eff_res,
    ~ In x omega ->
    StaticEffectWFAt depth omega eff ->
    ResolveStaticEffect rho eff eff_res ->
    ResolveStaticEffect (rho_extend x r_val rho) eff eff_res.
Proof.
  intros depth omega rho x r_val eff eff_res HFresh HWF HResolve.
  revert HWF.
  induction HResolve as
    [rho | rho action action_res eff eff_res HAction _ IH];
    intros HWF; inversion HWF; subst; constructor.
  - eapply ResolveStaticAction_extend_fresh; eauto.
  - eapply IH; eauto.
Qed.

Lemma ResolveTy_extend_fresh :
  forall depth omega rho x r_val ty ty_res,
    ~ In x omega ->
    TyWFAt depth omega ty ->
    ResolveTy rho ty ty_res ->
    ResolveTy (rho_extend x r_val rho) ty ty_res.
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
  - eapply Resolve_Pair; eauto.
  - eapply Resolve_Ref.
    + eapply ResolveRegionType_extend_fresh; eauto.
    + eapply IHTy; eauto.
  - eapply Resolve_Arrow.
    + eapply IHArg; eauto.
    + eapply ResolveStaticEffect_extend_fresh; eauto.
    + eapply IHBody; eauto.
    + eapply ResolveStaticEffect_extend_fresh; eauto.
  - eapply Resolve_ForallRgn.
    + eapply ResolveStaticEffect_extend_fresh; eauto.
    + eapply IHTy; eauto.
Qed.

Lemma ResolveRegionType_rho_extend_close_region_type_at :
  forall depth omega rho x r_val rgn rgn_res,
    RegionTypeWFAt depth (x :: omega) rgn ->
    ResolveRegionType rho (close_region_type_at depth x rgn) rgn_res ->
    ResolveRegionType (rho_extend x r_val rho) rgn
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

Lemma ResolveStaticAction_rho_extend_close_static_action_at :
  forall depth omega rho x r_val action action_res,
    StaticActionWFAt depth (x :: omega) action ->
    ResolveStaticAction rho
      (close_static_action_at depth x action)
      action_res ->
    ResolveStaticAction (rho_extend x r_val rho) action
      (open_static_action_at depth (region_const_type r_val) action_res).
Proof.
  intros depth omega rho x r_val action action_res HWF HResolve.
  inversion HWF; subst; inversion HResolve; subst; simpl; constructor;
    eapply ResolveRegionType_rho_extend_close_region_type_at; eauto.
Qed.

Lemma ResolveStaticEffect_rho_extend_close_static_effect_at :
  forall depth omega rho x r_val eff eff_res,
    StaticEffectWFAt depth (x :: omega) eff ->
    ResolveStaticEffect rho
      (close_static_effect_at depth x eff)
      eff_res ->
    ResolveStaticEffect (rho_extend x r_val rho) eff
      (open_static_effect_at depth (region_const_type r_val) eff_res).
Proof.
  intros depth omega rho x r_val eff eff_res HWF HResolve.
  revert depth omega eff_res HWF HResolve.
  induction eff as [| action eff IH];
    intros depth omega eff_res HWF HResolve; inversion HResolve; subst;
    simpl in *; inversion HWF; subst; constructor.
  - eapply ResolveStaticAction_rho_extend_close_static_action_at; eauto.
  - eapply IH; eauto.
Qed.

Lemma ResolveTy_rho_extend_close_ty_at :
  forall depth omega rho x r_val ty ty_res,
    TyWFAt depth (x :: omega) ty ->
    ResolveTy rho (close_ty_at depth x ty) ty_res ->
    ResolveTy (rho_extend x r_val rho) ty
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
  - eapply Resolve_Pair; eauto.
  - eapply Resolve_Ref.
    + eapply ResolveRegionType_rho_extend_close_region_type_at; eauto.
    + eapply IH; eauto.
  - eapply Resolve_Arrow.
    + eapply IHArg; eauto.
    + eapply ResolveStaticEffect_rho_extend_close_static_effect_at; eauto.
    + eapply IHBody; eauto.
    + eapply ResolveStaticEffect_rho_extend_close_static_effect_at; eauto.
  - eapply Resolve_ForallRgn.
    + eapply ResolveStaticEffect_rho_extend_close_static_effect_at; eauto.
    + eapply IH; eauto.
Qed.

Lemma ResolveTy_rho_extend_close_ty :
  forall omega rho x r_val ty ty_res,
    TyWFAt 0 (x :: omega) ty ->
    ResolveTy rho (close_ty x ty) ty_res ->
    ResolveTy (rho_extend x r_val rho) ty
      (open_ty_type (region_const_type r_val) ty_res).
Proof.
  intros omega rho x r_val ty ty_res HWF HResolve.
  unfold close_ty, open_ty_type.
  eapply ResolveTy_rho_extend_close_ty_at; eauto.
Qed.

Lemma ResolveStaticEffect_static_noalloc :
  forall rho eff eff',
    ResolveStaticEffect rho eff eff' ->
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

Lemma ResolveStaticEffect_static_noalloc_inv :
  forall rho eff eff',
    ResolveStaticEffect rho eff eff' ->
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

Lemma ResolveStaticEffect_static_readonly :
  forall rho eff eff',
    ResolveStaticEffect rho eff eff' ->
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

Lemma ResolveStaticEffect_static_readonly_inv :
  forall rho eff eff',
    ResolveStaticEffect rho eff eff' ->
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

Lemma ResolveStaticEffect_static_heap_neutral :
  forall rho eff eff',
    ResolveStaticEffect rho eff eff' ->
    static_heap_neutral eff ->
    static_heap_neutral eff'.
Proof.
  intros rho eff eff' HResolve [HNoAlloc HReadOnly].
  split.
  - eapply ResolveStaticEffect_static_noalloc; eauto.
  - eapply ResolveStaticEffect_static_readonly; eauto.
Qed.

Lemma ResolveStaticEffect_static_heap_neutral_inv :
  forall rho eff eff',
    ResolveStaticEffect rho eff eff' ->
    static_heap_neutral eff' ->
    static_heap_neutral eff.
Proof.
  intros rho eff eff' HResolve [HNoAlloc HReadOnly].
  split.
  - eapply ResolveStaticEffect_static_noalloc_inv; eauto.
  - eapply ResolveStaticEffect_static_readonly_inv; eauto.
Qed.

Lemma ResolveStaticEffect_static_heap_neutral_transfer :
  forall rho eff_src eff_dst eff_res,
    ResolveStaticEffect rho eff_src eff_res ->
    ResolveStaticEffect rho eff_dst eff_res ->
    static_heap_neutral eff_src ->
    static_heap_neutral eff_dst.
Proof.
  intros rho eff_src eff_dst eff_res HSrc HDst HNeutral.
  pose proof
    (ResolveStaticEffect_static_heap_neutral
      rho eff_src eff_res HSrc HNeutral)
    as HNeutralRes.
  eapply ResolveStaticEffect_static_heap_neutral_inv; eauto.
Qed.

Lemma ResolveStaticEffect_static_heap_neutral_transfer_any :
  forall rho_src rho_dst eff_src eff_dst eff_res,
    ResolveStaticEffect rho_src eff_src eff_res ->
    ResolveStaticEffect rho_dst eff_dst eff_res ->
    static_heap_neutral eff_src ->
    static_heap_neutral eff_dst.
Proof.
  intros rho_src rho_dst eff_src eff_dst eff_res
    HSrc HDst HNeutral.
  pose proof
    (ResolveStaticEffect_static_heap_neutral
      rho_src eff_src eff_res HSrc HNeutral)
    as HNeutralRes.
  eapply ResolveStaticEffect_static_heap_neutral_inv; eauto.
Qed.
