From Stdlib Require Import List.

Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Typing.Types.

Import ListNotations.

Inductive NResolvedRegionExpr : RegionExpr -> Prop :=
| NRR_Const :
    forall r,
      NResolvedRegionExpr (RConst r).

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
    forall r ty,
      NResolvedTy ty ->
      NResolvedTy (TyRef (RConst r) ty)
| NRTy_Arrow :
    forall ty_arg eff_body ty_body eff_summary,
      NResolvedTy ty_arg ->
      NResolvedTy ty_body ->
      NResolvedTy (TyArrow ty_arg eff_body ty_body eff_summary)
| NRTy_ForallRgn :
    forall x ty,
      NResolvedTy (TyForallRgn x ty).

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
    forall rho rgn ty ty' r,
      eval_region rho rgn = Some r ->
      NResolveTy rho ty ty' ->
      NResolveTy rho (TyRef rgn ty) (TyRef (RConst r) ty')
| NResolve_Arrow :
    forall rho ty_arg ty_arg' eff_body ty_body ty_body' eff_summary,
      NResolveTy rho ty_arg ty_arg' ->
      NResolveTy rho ty_body ty_body' ->
      NResolveTy rho
        (TyArrow ty_arg eff_body ty_body eff_summary)
        (TyArrow ty_arg' eff_body ty_body' eff_summary)
| NResolve_ForallRgn :
    forall rho x ty,
      NResolveTy rho (TyForallRgn x ty) (TyForallRgn x ty).

Lemma NResolveTy_resolved :
  forall rho ty ty',
    NResolveTy rho ty ty' ->
    NResolvedTy ty'.
Proof.
  intros rho ty ty' HResolve.
  induction HResolve; constructor; assumption.
Qed.

Lemma NResolveTy_ref_inv :
  forall rho rgn ty ty_resolved,
    NResolveTy rho (TyRef rgn ty) ty_resolved ->
    exists r ty',
      eval_region rho rgn = Some r /\
      NResolveTy rho ty ty' /\
      ty_resolved = TyRef (RConst r) ty'.
Proof.
  intros rho rgn ty ty_resolved HResolve.
  inversion HResolve; subst.
  exists r, ty'.
  repeat split; assumption || reflexivity.
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
      as (r_other & ty_other & HRgnOther & HTyOther & ->).
    rewrite H in HRgnOther. inversion HRgnOther; subst.
    specialize (IHHLeft _ HTyOther). subst.
    reflexivity.
  - inversion HRight; subst.
    repeat match goal with
    | IH : forall ty_res : NTy,
        NResolveTy ?rho ?ty ty_res -> ?resolved = ty_res,
      HResolve : NResolveTy ?rho ?ty ?resolved_other |- _ =>
        specialize (IH _ HResolve); subst
    end.
    subst. reflexivity.
Qed.

Lemma NResolveTy_ref_same_region :
  forall rho rgn ty r ty',
    NResolveTy rho (TyRef rgn ty) (TyRef (RConst r) ty') ->
    eval_region rho rgn = Some r.
Proof.
  intros rho rgn ty r ty' HResolve.
  destruct
    (NResolveTy_ref_inv rho rgn ty (TyRef (RConst r) ty') HResolve)
    as (r0 & ty0 & HRgn & _ & HEq).
  inversion HEq; subst.
  assumption.
Qed.
