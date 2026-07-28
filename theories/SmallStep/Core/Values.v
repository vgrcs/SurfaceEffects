From stdpp Require Import gmap.
From Stdlib Require Import List.
From Stdlib Require Import Ascii.
From Stdlib Require Import Program.Equality.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.

Import ListNotations.

Inductive Val :=
| VNat : nat -> Val
| VBool : bool -> Val
| VUnit : Val
| VPair : Val -> Val -> Val
| VLoc : RegionId -> Location -> Val
| VClosure : Env -> Rho -> VarId -> VarId -> Expr -> Expr -> Val
| VRegionClosure : Env -> Rho -> VarId -> Expr -> Val
| VSummary : Summary -> Val
with Env :=
| EnvNil : Env
| EnvCons : VarId -> Val -> Env -> Env.

Scheme Val_ind' := Induction for Val Sort Prop
with Env_ind' := Induction for Env Sort Prop.

Combined Scheme Val_Env_ind from Val_ind', Env_ind'.

Definition Heap := list (RegionId * Location * Val).

Definition rho_lookup (x : VarId) (rho : Rho) : option RegionId :=
  find_R (region_var_expr x) rho.

Definition rho_extend (x : VarId) (r : RegionId) (rho : Rho) : Rho :=
  update_R (x, r) rho.

Definition eval_region_any {idx : bool * bool * bool}
    (rho : Rho) (rgn : Region idx) : option RegionId :=
  match rgn with
  | Rgn_Const _ _ r => Some r
  | Rgn_FVar _ _ x => rho_lookup x rho
  | Rgn_BVar _ _ _ => None
  end.

Definition eval_region (rho : Rho) (rgn : RegionExpr) : option RegionId :=
  eval_region_any rho rgn.

Definition eval_region_type (rho : Rho) (rgn : RegionType)
    : option RegionId :=
  eval_region_any rho rgn.

Lemma eval_region_any_region_to_type :
  forall idx rho (rgn : Region idx),
    eval_region_type rho (region_to_type rgn) =
    eval_region_any rho rgn.
Proof.
  intros idx rho rgn.
  destruct rgn; reflexivity.
Qed.

Lemma eval_region_type_region_expr_to_type :
  forall rho rgn,
    eval_region_type rho (region_expr_to_type rgn) =
    eval_region rho rgn.
Proof.
  intros rho rgn.
  apply eval_region_any_region_to_type.
Qed.

Definition empty_env : Env := EnvNil.
Definition empty_rho : Rho :=
  list_to_map ([] : list (RgnName * RgnVal)).
