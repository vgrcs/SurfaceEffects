Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.

Inductive NTy :=
| TyNat : NTy
| TyBool : NTy
| TyUnit : NTy
| TyEffect : NTy
| TyRef : RegionType -> NTy -> NTy
| TyArrow : NTy -> StaticEffect -> NTy -> StaticEffect -> NTy
| TyForallRgn : StaticEffect -> NTy -> NTy.

Fixpoint open_ty_at (k : nat) (u : RegionType) (ty : NTy) : NTy :=
  match ty with
  | TyNat => TyNat
  | TyBool => TyBool
  | TyUnit => TyUnit
  | TyEffect => TyEffect
  | TyRef rgn ty_inner =>
      TyRef (open_region_type_at k u rgn) (open_ty_at k u ty_inner)
  | TyArrow ty_arg eff_body ty_body eff_summary =>
      TyArrow
        (open_ty_at k u ty_arg)
        (open_static_effect_at k u eff_body)
        (open_ty_at k u ty_body)
        (open_static_effect_at k u eff_summary)
  | TyForallRgn eff ty_body =>
      TyForallRgn
        (open_static_effect_at (S k) u eff)
        (open_ty_at (S k) u ty_body)
  end.

Definition open_ty_type (u : RegionType) (ty : NTy) : NTy :=
  open_ty_at 0 u ty.

Definition open_ty (rgn : RegionExpr) (ty : NTy) : NTy :=
  open_ty_type (region_expr_to_type rgn) ty.

Fixpoint close_ty_at (k : nat) (x : VarId) (ty : NTy) : NTy :=
  match ty with
  | TyNat => TyNat
  | TyBool => TyBool
  | TyUnit => TyUnit
  | TyEffect => TyEffect
  | TyRef rgn ty_inner =>
      TyRef (close_region_type_at k x rgn) (close_ty_at k x ty_inner)
  | TyArrow ty_arg eff_body ty_body eff_summary =>
      TyArrow
        (close_ty_at k x ty_arg)
        (close_static_effect_at k x eff_body)
        (close_ty_at k x ty_body)
        (close_static_effect_at k x eff_summary)
  | TyForallRgn eff ty_body =>
      TyForallRgn
        (close_static_effect_at (S k) x eff)
        (close_ty_at (S k) x ty_body)
  end.

Definition close_ty (x : VarId) (ty : NTy) : NTy :=
  close_ty_at 0 x ty.
