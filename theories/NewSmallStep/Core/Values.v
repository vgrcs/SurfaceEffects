From Stdlib Require Import List.
From Stdlib Require Import String.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.

Import ListNotations.

Definition Rho := list (VarId * RegionId).

Inductive NVal :=
| VNat : nat -> NVal
| VBool : bool -> NVal
| VUnit : NVal
| VLoc : RegionId -> Location -> NVal
| VClosure : NEnv -> Rho -> VarId -> VarId -> NExpr -> NExpr -> NVal
| VRegionClosure : NEnv -> Rho -> VarId -> NExpr -> NVal
| VSummary : Summary -> NVal
with NEnv :=
| EnvNil : NEnv
| EnvCons : VarId -> NVal -> NEnv -> NEnv.

Scheme NVal_ind' := Induction for NVal Sort Prop
with NEnv_ind' := Induction for NEnv Sort Prop.

Combined Scheme NVal_NEnv_ind from NVal_ind', NEnv_ind'.

Definition Heap := list (RegionId * Location * NVal).

Fixpoint rho_lookup (x : VarId) (rho : Rho) : option RegionId :=
  match rho with
  | [] => None
  | (y, r) :: rho' =>
      if String.eqb x y then Some r else rho_lookup x rho'
  end.

Definition rho_extend (x : VarId) (r : RegionId) (rho : Rho) : Rho :=
  (x, r) :: rho.

Definition eval_region (rho : Rho) (rgn : RegionExpr) : option RegionId :=
  match rgn with
  | RConst r => Some r
  | RVar x => rho_lookup x rho
  end.

Definition empty_env : NEnv := EnvNil.
Definition empty_rho : Rho := [].
