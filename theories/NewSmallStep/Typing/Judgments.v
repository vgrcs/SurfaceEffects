From Stdlib Require Import List.
From Stdlib Require Import Ascii.
From Stdlib Require Import Program.Equality.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Typing.Types.

Import ListNotations.

Definition NCtx := list (VarId * NTy).
Definition NRgnCtx := list VarId.

Fixpoint ctx_lookup (x : VarId) (gamma : NCtx) : option NTy :=
  match gamma with
  | [] => None
  | (y, ty) :: gamma' =>
      if ascii_dec x y then Some ty else ctx_lookup x gamma'
  end.

Definition ctx_binds (x : VarId) (ty : NTy) (gamma : NCtx) : Prop :=
  ctx_lookup x gamma = Some ty.

Definition static_union (eff1 eff2 : StaticEffect) : StaticEffect :=
  eff1 ++ eff2.

Definition static_readonly (eff : StaticEffect) : Prop :=
  forall r, ~ In (SWrite r) eff.

Inductive region_expr_wf : NRgnCtx -> RegionExpr -> Prop :=
| REWF_Const :
    forall omega r,
      region_expr_wf omega (region_const_expr r)
| REWF_FVar :
    forall omega x,
      In x omega ->
      region_expr_wf omega (region_var_expr x).

Inductive NTcExp : NCtx -> NRgnCtx -> NExpr -> NTy -> StaticEffect -> Prop :=
| NT_Const :
    forall gamma omega n,
      NTcExp gamma omega (EConst n) TyNat []
| NT_Bool :
    forall gamma omega b,
      NTcExp gamma omega (EBool b) TyBool []
| NT_Var :
    forall gamma omega x ty,
      ctx_binds x ty gamma ->
      NTcExp gamma omega (EVar x) ty []
| NT_Mu :
    forall gamma omega f x ec ee ty_arg ty_body eff_body eff_summary,
      NTcExp
        ((x, ty_arg) :: (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      NTcExp
        ((x, ty_arg) :: (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      NTcExp gamma omega (EMu f x ec ee)
        (TyArrow ty_arg eff_body ty_body eff_summary) []
| NT_LambdaRgn :
    forall gamma omega x e ty eff,
      NBackTriangle gamma (x :: omega) e EEmpty ->
      NTcExp gamma (x :: omega) e ty eff ->
      NTcExp gamma omega (ELambdaRgn x e)
        (TyForallRgn (close_static_effect x eff) (close_ty x ty)) []
| NT_MuApp :
    forall gamma omega ef ea ty_arg ty_body eff_body eff_summary eff_f eff_a,
      NTcExp gamma omega ef
        (TyArrow ty_arg eff_body ty_body eff_summary) eff_f ->
      NTcExp gamma omega ea ty_arg eff_a ->
      NTcExp gamma omega (EMuApp ef ea) ty_body
        (static_union eff_f (static_union eff_a eff_body))
| NT_RgnApp :
    forall gamma omega er r ty eff_body eff_f,
      region_expr_wf omega r ->
      NTcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
      NTcExp gamma omega (ERgnApp er r) (open_ty r ty)
        (static_union eff_f (open_static_effect r eff_body))
| NT_EffApp :
    forall gamma omega ef ea ty_arg ty_body eff_body eff_summary eff_f eff_a,
      NTcExp gamma omega ef
        (TyArrow ty_arg eff_body ty_body eff_summary) eff_f ->
      NTcExp gamma omega ea ty_arg eff_a ->
      NTcExp gamma omega (EEffApp ef ea) TyEffect
        (static_union eff_f (static_union eff_a eff_summary))
| NT_Cond :
    forall gamma omega e et ef ty eff_e eff_t eff_f,
      NTcExp gamma omega e TyBool eff_e ->
      NTcExp gamma omega et ty eff_t ->
      NTcExp gamma omega ef ty eff_f ->
      NTcExp gamma omega (ECond e et ef) ty
        (static_union eff_e (static_union eff_t eff_f))
| NT_Ref :
    forall gamma omega r e ty eff,
      region_expr_wf omega r ->
      NTcExp gamma omega e ty eff ->
      NTcExp gamma omega (ERef r e) (TyRef (region_expr_to_type r) ty)
        (SAlloc (region_expr_to_type r) :: eff)
| NT_Deref :
    forall gamma omega r e ty eff,
      region_expr_wf omega r ->
      NTcExp gamma omega e (TyRef (region_expr_to_type r) ty) eff ->
      NTcExp gamma omega (EDeref r e) ty
        (SRead (region_expr_to_type r) :: eff)
| NT_Assign :
    forall gamma omega r ea ev ty eff_a eff_v,
      region_expr_wf omega r ->
      NTcExp gamma omega ea (TyRef (region_expr_to_type r) ty) eff_a ->
      NTcExp gamma omega ev ty eff_v ->
      NTcExp gamma omega (EAssign r ea ev) TyUnit
        (SWrite (region_expr_to_type r) :: static_union eff_a eff_v)
| NT_Plus :
    forall gamma omega e1 e2 eff1 eff2,
      NTcExp gamma omega e1 TyNat eff1 ->
      NTcExp gamma omega e2 TyNat eff2 ->
      NTcExp gamma omega (EPlus e1 e2) TyNat (static_union eff1 eff2)
| NT_Minus :
    forall gamma omega e1 e2 eff1 eff2,
      NTcExp gamma omega e1 TyNat eff1 ->
      NTcExp gamma omega e2 TyNat eff2 ->
      NTcExp gamma omega (EMinus e1 e2) TyNat (static_union eff1 eff2)
| NT_Times :
    forall gamma omega e1 e2 eff1 eff2,
      NTcExp gamma omega e1 TyNat eff1 ->
      NTcExp gamma omega e2 TyNat eff2 ->
      NTcExp gamma omega (ETimes e1 e2) TyNat (static_union eff1 eff2)
| NT_Eq :
    forall gamma omega e1 e2 eff1 eff2,
      NTcExp gamma omega e1 TyNat eff1 ->
      NTcExp gamma omega e2 TyNat eff2 ->
      NTcExp gamma omega (EEq e1 e2) TyBool (static_union eff1 eff2)
| NT_AllocAbs :
    forall gamma omega r,
      region_expr_wf omega r ->
      NTcExp gamma omega (EAllocAbs r) TyEffect []
| NT_ReadAbs :
    forall gamma omega r,
      region_expr_wf omega r ->
      NTcExp gamma omega (EReadAbs r) TyEffect []
| NT_WriteAbs :
    forall gamma omega r,
      region_expr_wf omega r ->
      NTcExp gamma omega (EWriteAbs r) TyEffect []
| NT_ReadConc :
    forall gamma omega e r ty eff,
      NTcExp gamma omega e (TyRef r ty) eff ->
      NTcExp gamma omega (EReadConc e) TyEffect eff
| NT_WriteConc :
    forall gamma omega e r ty eff,
      NTcExp gamma omega e (TyRef r ty) eff ->
      NTcExp gamma omega (EWriteConc e) TyEffect eff
| NT_Concat :
    forall gamma omega e1 e2 eff1 eff2,
      NTcExp gamma omega e1 TyEffect eff1 ->
      NTcExp gamma omega e2 TyEffect eff2 ->
      NTcExp gamma omega (EConcat e1 e2) TyEffect
        (static_union eff1 eff2)
| NT_Top :
    forall gamma omega,
      NTcExp gamma omega ETop TyEffect []
| NT_Empty :
    forall gamma omega,
      NTcExp gamma omega EEmpty TyEffect []

with NBackTriangle : NCtx -> NRgnCtx -> NExpr -> NExpr -> Prop :=
| NBT_Num :
    forall gamma omega n,
      NTcExp gamma omega (EConst n) TyNat [] ->
      NBackTriangle gamma omega (EConst n) EEmpty
| NBT_Bool :
    forall gamma omega b,
      NTcExp gamma omega (EBool b) TyBool [] ->
      NBackTriangle gamma omega (EBool b) EEmpty
| NBT_Var :
    forall gamma omega x ty,
      NTcExp gamma omega (EVar x) ty [] ->
      NBackTriangle gamma omega (EVar x) EEmpty
| NBT_Mu :
    forall gamma omega f x ec ee ty eff,
      NTcExp gamma omega (EMu f x ec ee) ty eff ->
      NBackTriangle gamma omega (EMu f x ec ee) EEmpty
| NBT_LambdaRgn :
    forall gamma omega x e ty eff,
      NTcExp gamma omega (ELambdaRgn x e) ty eff ->
      NBackTriangle gamma omega (ELambdaRgn x e) EEmpty
| NBT_App :
    forall gamma omega ef ea ty_mu eff_mu eff_eff
      ty_ef ty_ea eff_ef eff_ea,
      NTcExp gamma omega (EMuApp ef ea) ty_mu eff_mu ->
      NTcExp gamma omega (EEffApp ef ea) TyEffect eff_eff ->
      NTcExp gamma omega ef ty_ef eff_ef ->
      NTcExp gamma omega ea ty_ea eff_ea ->
      static_readonly eff_eff ->
      static_readonly eff_ef ->
      static_readonly eff_ea ->
      NBackTriangle gamma omega ef (EEffApp ef ea) ->
      NBackTriangle gamma omega ea (EEffApp ef ea) ->
      NBackTriangle gamma omega (EMuApp ef ea) (EEffApp ef ea)
| NBT_RgnApp :
    forall gamma omega er r ty eff ty_app eff_app,
      NTcExp gamma omega er ty eff ->
      NTcExp gamma omega (ERgnApp er r) ty_app eff_app ->
      NBackTriangle gamma omega er EEmpty ->
      NBackTriangle gamma omega (ERgnApp er r) EEmpty
| NBT_Cond :
    forall gamma omega e et ef efft efff ty ty_t ty_f
      eff_e eff_et eff_ef,
      NTcExp gamma omega e TyBool eff_e ->
      NTcExp gamma omega et ty_t eff_et ->
      NTcExp gamma omega ef ty_f eff_ef ->
      NTcExp gamma omega (ECond e et ef) ty
        (static_union eff_e (static_union eff_et eff_ef)) ->
      static_readonly eff_e ->
      NBackTriangle gamma omega e EEmpty ->
      NBackTriangle gamma omega et efft ->
      NBackTriangle gamma omega ef efff ->
      NBackTriangle gamma omega (ECond e et ef) (ECond e efft efff)
| NBT_Ref :
    forall gamma omega r e eff ty static ty_ref eff_ref,
      NTcExp gamma omega e ty static ->
      NTcExp gamma omega (ERef r e) ty_ref eff_ref ->
      NBackTriangle gamma omega e eff ->
      NBackTriangle gamma omega (ERef r e) (EConcat eff (EAllocAbs r))
| NBT_Deref :
    forall gamma omega r e eff ty static ty_deref eff_deref,
      NTcExp gamma omega e ty static ->
      NTcExp gamma omega (EDeref r e) ty_deref eff_deref ->
      NBackTriangle gamma omega e eff ->
      NBackTriangle gamma omega (EDeref r e) (EConcat eff (EReadAbs r))
| NBT_Assign :
    forall gamma omega r e1 e2 eff1 eff2 ty static ty_assign eff_assign,
      NTcExp gamma omega e1 ty static ->
      NTcExp gamma omega (EAssign r e1 e2) ty_assign eff_assign ->
      static_readonly static ->
      NBackTriangle gamma omega e1 eff1 ->
      NBackTriangle gamma omega e2 eff2 ->
      NBackTriangle gamma omega
        (EAssign r e1 e2)
        (EConcat eff1 (EConcat eff2 (EWriteAbs r)))
| NBT_Plus :
    forall gamma omega e1 e2 eff1 eff2 eff_static,
      NTcExp gamma omega (EPlus e1 e2) TyNat eff_static ->
      NBackTriangle gamma omega e1 eff1 ->
      NBackTriangle gamma omega e2 eff2 ->
      NBackTriangle gamma omega (EPlus e1 e2) (EConcat eff1 eff2)
| NBT_Minus :
    forall gamma omega e1 e2 eff1 eff2 eff_static,
      NTcExp gamma omega (EMinus e1 e2) TyNat eff_static ->
      NBackTriangle gamma omega e1 eff1 ->
      NBackTriangle gamma omega e2 eff2 ->
      NBackTriangle gamma omega (EMinus e1 e2) (EConcat eff1 eff2)
| NBT_Times :
    forall gamma omega e1 e2 eff1 eff2 eff_static,
      NTcExp gamma omega (ETimes e1 e2) TyNat eff_static ->
      NBackTriangle gamma omega e1 eff1 ->
      NBackTriangle gamma omega e2 eff2 ->
      NBackTriangle gamma omega (ETimes e1 e2) (EConcat eff1 eff2)
| NBT_Eq :
    forall gamma omega e1 e2 eff1 eff2 eff_static,
      NTcExp gamma omega (EEq e1 e2) TyBool eff_static ->
      NBackTriangle gamma omega e1 eff1 ->
      NBackTriangle gamma omega e2 eff2 ->
      NBackTriangle gamma omega (EEq e1 e2) (EConcat eff1 eff2)
| NBT_Top :
    forall gamma omega e ty eff,
      NTcExp gamma omega e ty eff ->
      NBackTriangle gamma omega e ETop.
