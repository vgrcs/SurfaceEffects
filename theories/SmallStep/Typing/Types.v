Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.

Inductive Ty :=
| TyNat : Ty
| TyBool : Ty
| TyUnit : Ty
| TyEffect : Ty
| TyPair : Ty -> Ty -> Ty
| TyRef : RegionType -> Ty -> Ty
| TyArrow : Ty -> StaticEffect -> Ty -> StaticEffect -> Ty
| TyForallRgn : StaticEffect -> Ty -> Ty.

Fixpoint open_ty_at (k : nat) (u : RegionType) (ty : Ty) : Ty :=
  match ty with
  | TyNat => TyNat
  | TyBool => TyBool
  | TyUnit => TyUnit
  | TyEffect => TyEffect
  | TyPair ty1 ty2 =>
      TyPair (open_ty_at k u ty1) (open_ty_at k u ty2)
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

Definition open_ty_type (u : RegionType) (ty : Ty) : Ty :=
  open_ty_at 0 u ty.

Definition open_ty (rgn : RegionExpr) (ty : Ty) : Ty :=
  open_ty_type (region_expr_to_type rgn) ty.

Fixpoint close_ty_at (k : nat) (x : VarId) (ty : Ty) : Ty :=
  match ty with
  | TyNat => TyNat
  | TyBool => TyBool
  | TyUnit => TyUnit
  | TyEffect => TyEffect
  | TyPair ty1 ty2 =>
      TyPair (close_ty_at k x ty1) (close_ty_at k x ty2)
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

Definition close_ty (x : VarId) (ty : Ty) : Ty :=
  close_ty_at 0 x ty.
