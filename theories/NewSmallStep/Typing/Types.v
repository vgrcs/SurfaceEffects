Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.

Inductive NTy :=
| TyNat : NTy
| TyBool : NTy
| TyUnit : NTy
| TyEffect : NTy
| TyRef : RegionExpr -> NTy -> NTy
| TyArrow : NTy -> StaticEffect -> NTy -> StaticEffect -> NTy
| TyForallRgn : VarId -> NTy -> NTy.
