From Stdlib Require Import List.
From Stdlib Require Import String.

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
      if String.eqb x y then Some ty else ctx_lookup x gamma'
  end.

Definition ctx_binds (x : VarId) (ty : NTy) (gamma : NCtx) : Prop :=
  ctx_lookup x gamma = Some ty.

Definition static_union (eff1 eff2 : StaticEffect) : StaticEffect :=
  eff1 ++ eff2.

Definition static_readonly (eff : StaticEffect) : Prop :=
  forall r, ~ In (SWrite r) eff.

Definition region_expr_wf (omega : NRgnCtx) (rgn : RegionExpr) : Prop :=
  match rgn with
  | RConst _ => True
  | RVar x => In x omega
  end.

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
      NTcExp gamma (x :: omega) e ty eff ->
      NTcExp gamma omega (ELambdaRgn x e) (TyForallRgn x ty) []
| NT_MuApp :
    forall gamma omega ef ea ty_arg ty_body eff_body eff_summary eff_f eff_a,
      NTcExp gamma omega ef
        (TyArrow ty_arg eff_body ty_body eff_summary) eff_f ->
      NTcExp gamma omega ea ty_arg eff_a ->
      NTcExp gamma omega (EMuApp ef ea) ty_body
        (static_union eff_f (static_union eff_a eff_body))
| NT_RgnApp :
    forall gamma omega er r x ty eff_f,
      region_expr_wf omega r ->
      NTcExp gamma omega er (TyForallRgn x ty) eff_f ->
      NTcExp gamma omega (ERgnApp er r) ty eff_f
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
      NTcExp gamma omega (ERef r e) (TyRef r ty)
        (SAlloc 0 :: eff)
| NT_Deref :
    forall gamma omega r e ty eff,
      region_expr_wf omega r ->
      NTcExp gamma omega e (TyRef r ty) eff ->
      NTcExp gamma omega (EDeref r e) ty
        (SRead 0 :: eff)
| NT_Assign :
    forall gamma omega r ea ev ty eff_a eff_v,
      region_expr_wf omega r ->
      NTcExp gamma omega ea (TyRef r ty) eff_a ->
      NTcExp gamma omega ev ty eff_v ->
      NTcExp gamma omega (EAssign r ea ev) TyUnit
        (SWrite 0 :: static_union eff_a eff_v)
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
      NTcExp gamma omega EEmpty TyEffect [].
