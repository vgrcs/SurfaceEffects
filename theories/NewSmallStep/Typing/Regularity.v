From Stdlib Require Import List.
From Stdlib Require Import Ascii.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Typing.Judgments.
Require Import theories.NewSmallStep.Typing.Resolve.
Require Import theories.NewSmallStep.Typing.Types.

Import ListNotations.
Open Scope char_scope.

Definition NRgnCtxWF (omega : NRgnCtx) : Prop :=
  NoDup omega.

Record NRegularTcExp
    (gamma : NCtx) (omega : NRgnCtx)
    (e : NExpr) (ty : NTy) (eff : StaticEffect) : Prop := {
  NRegularTcExp_typed :
    NTcExp gamma omega e ty eff;
  NRegularTcExp_rgn_ctx_wf :
    NRgnCtxWF omega;
  NRegularTcExp_ctx_wf :
    NCtxWF omega gamma;
  NRegularTcExp_ty_wf :
    NTyWF omega ty;
  NRegularTcExp_eff_wf :
    NStaticEffectWF omega eff
}.

Record NRegularRegionBody
    (x : VarId) (gamma : NCtx) (omega : NRgnCtx)
    (e : NExpr) (ty : NTy) (eff : StaticEffect) : Prop := {
  NRegularRegionBody_typed :
    NTcExp gamma (x :: omega) e ty eff;
  NRegularRegionBody_rgn_ctx_wf :
    NRgnCtxWF (x :: omega);
  NRegularRegionBody_fresh :
    ~ In x omega;
  NRegularRegionBody_ctx_wf :
    NCtxWF omega gamma;
  NRegularRegionBody_ty_wf :
    NTyWFAt 0 (x :: omega) ty;
  NRegularRegionBody_eff_wf :
    NStaticEffectWFAt 0 (x :: omega) eff
}.

Inductive NCheckedTcExp :
    NCtx -> NRgnCtx -> NExpr -> NTy -> StaticEffect -> Prop :=
| NCheckedTcExp_intro :
    forall gamma omega e ty eff,
    NTcExp gamma omega e ty eff ->
    NRgnCtxWF omega ->
    NCtxWF omega gamma ->
    NTyWF omega ty ->
    NStaticEffectWF omega eff ->
    NCheckedTcExpShape gamma omega e ty eff ->
    NCheckedTcExp gamma omega e ty eff
with NCheckedTcExpShape :
    NCtx -> NRgnCtx -> NExpr -> NTy -> StaticEffect -> Prop :=
| NCTS_Const :
    forall gamma omega n,
      NCheckedTcExpShape gamma omega (EConst n) TyNat []
| NCTS_Bool :
    forall gamma omega b,
      NCheckedTcExpShape gamma omega (EBool b) TyBool []
| NCTS_Var :
    forall gamma omega x ty,
      ctx_binds x ty gamma ->
      NCheckedTcExpShape gamma omega (EVar x) ty []
| NCTS_Mu :
    forall gamma omega f x ec ee ty_arg ty_body eff_body eff_summary,
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      NCheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ee ->
      NCheckedTcExpShape gamma omega (EMu f x ec ee)
        (TyArrow ty_arg eff_body ty_body eff_summary) []
| NCTS_LambdaRgn :
    forall gamma omega x e ty eff,
      ~ In x omega ->
      NCtxWF omega gamma ->
      NCheckedBackTriangle gamma (x :: omega) e EEmpty ->
      NCheckedTcExp gamma (x :: omega) e ty eff ->
      NCheckedTcExpShape gamma omega (ELambdaRgn x e)
        (TyForallRgn (close_static_effect x eff) (close_ty x ty)) []
| NCTS_MuApp :
    forall gamma omega ef ea ty_arg ty_body eff_body eff_summary eff_f eff_a,
      NCheckedTcExp gamma omega ef
        (TyArrow ty_arg eff_body ty_body eff_summary) eff_f ->
      NCheckedTcExp gamma omega ea ty_arg eff_a ->
      NCheckedTcExpShape gamma omega (EMuApp ef ea) ty_body
        (static_union eff_f (static_union eff_a eff_body))
| NCTS_RgnApp :
    forall gamma omega er r ty eff_body eff_f,
      region_expr_wf omega r ->
      NCheckedTcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
      NCheckedTcExpShape gamma omega (ERgnApp er r) (open_ty r ty)
        (static_union eff_f (open_static_effect r eff_body))
| NCTS_EffApp :
    forall gamma omega ef ea ty_arg ty_body eff_body eff_summary eff_f eff_a,
      NCheckedTcExp gamma omega ef
        (TyArrow ty_arg eff_body ty_body eff_summary) eff_f ->
      NCheckedTcExp gamma omega ea ty_arg eff_a ->
      NCheckedTcExpShape gamma omega (EEffApp ef ea) TyEffect
        (static_union eff_f (static_union eff_a eff_summary))
| NCTS_PairPar :
    forall gamma omega ef1 ea1 ef2 ea2 ty1 ty2 eff1 eff2
      eff_summary1 eff_summary2,
      NCheckedTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 ->
      NCheckedTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
      NCheckedTcExp gamma omega (EEffApp ef1 ea1) TyEffect eff_summary1 ->
      NCheckedTcExp gamma omega (EEffApp ef2 ea2) TyEffect eff_summary2 ->
      static_noalloc eff1 ->
      static_noalloc eff2 ->
      NCheckedTcExpShape gamma omega
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
        (TyPair ty1 ty2)
        (static_union (static_union eff_summary1 eff_summary2)
          (static_union eff1 eff2))
| NCTS_Cond :
    forall gamma omega e et ef ty eff_e eff_t eff_f,
      NCheckedTcExp gamma omega e TyBool eff_e ->
      NCheckedTcExp gamma omega et ty eff_t ->
      NCheckedTcExp gamma omega ef ty eff_f ->
      NCheckedTcExpShape gamma omega (ECond e et ef) ty
        (static_union eff_e (static_union eff_t eff_f))
| NCTS_Ref :
    forall gamma omega r e ty eff,
      region_expr_wf omega r ->
      NCheckedTcExp gamma omega e ty eff ->
      NCheckedTcExpShape gamma omega (ERef r e)
        (TyRef (region_expr_to_type r) ty)
        (SAlloc (region_expr_to_type r) :: eff)
| NCTS_Deref :
    forall gamma omega r e ty eff,
      region_expr_wf omega r ->
      NCheckedTcExp gamma omega e
        (TyRef (region_expr_to_type r) ty) eff ->
      NCheckedTcExpShape gamma omega (EDeref r e) ty
        (SRead (region_expr_to_type r) :: eff)
| NCTS_Assign :
    forall gamma omega r ea ev ty eff_a eff_v,
      region_expr_wf omega r ->
      NCheckedTcExp gamma omega ea
        (TyRef (region_expr_to_type r) ty) eff_a ->
      NCheckedTcExp gamma omega ev ty eff_v ->
      NCheckedTcExpShape gamma omega (EAssign r ea ev) TyUnit
        (SWrite (region_expr_to_type r) :: static_union eff_a eff_v)
| NCTS_Plus :
    forall gamma omega e1 e2 eff1 eff2,
      NCheckedTcExp gamma omega e1 TyNat eff1 ->
      NCheckedTcExp gamma omega e2 TyNat eff2 ->
      NCheckedTcExpShape gamma omega (EPlus e1 e2) TyNat
        (static_union eff1 eff2)
| NCTS_Minus :
    forall gamma omega e1 e2 eff1 eff2,
      NCheckedTcExp gamma omega e1 TyNat eff1 ->
      NCheckedTcExp gamma omega e2 TyNat eff2 ->
      NCheckedTcExpShape gamma omega (EMinus e1 e2) TyNat
        (static_union eff1 eff2)
| NCTS_Times :
    forall gamma omega e1 e2 eff1 eff2,
      NCheckedTcExp gamma omega e1 TyNat eff1 ->
      NCheckedTcExp gamma omega e2 TyNat eff2 ->
      NCheckedTcExpShape gamma omega (ETimes e1 e2) TyNat
        (static_union eff1 eff2)
| NCTS_Eq :
    forall gamma omega e1 e2 eff1 eff2,
      NCheckedTcExp gamma omega e1 TyNat eff1 ->
      NCheckedTcExp gamma omega e2 TyNat eff2 ->
      NCheckedTcExpShape gamma omega (EEq e1 e2) TyBool
        (static_union eff1 eff2)
| NCTS_AllocAbs :
    forall gamma omega r,
      region_expr_wf omega r ->
      NCheckedTcExpShape gamma omega (EAllocAbs r) TyEffect []
| NCTS_ReadAbs :
    forall gamma omega r,
      region_expr_wf omega r ->
      NCheckedTcExpShape gamma omega (EReadAbs r) TyEffect []
| NCTS_WriteAbs :
    forall gamma omega r,
      region_expr_wf omega r ->
      NCheckedTcExpShape gamma omega (EWriteAbs r) TyEffect []
| NCTS_ReadConc :
    forall gamma omega e r ty eff,
      NCheckedTcExp gamma omega e (TyRef r ty) eff ->
      NCheckedTcExpShape gamma omega (EReadConc e) TyEffect eff
| NCTS_WriteConc :
    forall gamma omega e r ty eff,
      NCheckedTcExp gamma omega e (TyRef r ty) eff ->
      NCheckedTcExpShape gamma omega (EWriteConc e) TyEffect eff
| NCTS_Concat :
    forall gamma omega e1 e2 eff1 eff2,
      NCheckedTcExp gamma omega e1 TyEffect eff1 ->
      NCheckedTcExp gamma omega e2 TyEffect eff2 ->
      NCheckedTcExpShape gamma omega (EConcat e1 e2) TyEffect
        (static_union eff1 eff2)
| NCTS_Top :
    forall gamma omega,
      NCheckedTcExpShape gamma omega ETop TyEffect []
| NCTS_Empty :
    forall gamma omega,
      NCheckedTcExpShape gamma omega EEmpty TyEffect []
with NCheckedBackTriangle :
    NCtx -> NRgnCtx -> NExpr -> NExpr -> Prop :=
| NCBT_Num :
    forall gamma omega n,
      NCheckedTcExp gamma omega (EConst n) TyNat [] ->
      NCheckedBackTriangle gamma omega (EConst n) EEmpty
| NCBT_Bool :
    forall gamma omega b,
      NCheckedTcExp gamma omega (EBool b) TyBool [] ->
      NCheckedBackTriangle gamma omega (EBool b) EEmpty
| NCBT_Var :
    forall gamma omega x ty,
      NCheckedTcExp gamma omega (EVar x) ty [] ->
      NCheckedBackTriangle gamma omega (EVar x) EEmpty
| NCBT_Mu :
    forall gamma omega f x ec ee ty eff,
      NCheckedTcExp gamma omega (EMu f x ec ee) ty eff ->
      NCheckedBackTriangle gamma omega (EMu f x ec ee) EEmpty
| NCBT_LambdaRgn :
    forall gamma omega x e ty eff,
      NCheckedTcExp gamma omega (ELambdaRgn x e) ty eff ->
      NCheckedBackTriangle gamma omega (ELambdaRgn x e) EEmpty
| NCBT_App :
    forall gamma omega ef ea ty_mu eff_mu eff_eff
      ty_ef ty_ea eff_ef eff_ea,
      NCheckedTcExp gamma omega (EMuApp ef ea) ty_mu eff_mu ->
      NCheckedTcExp gamma omega (EEffApp ef ea) TyEffect eff_eff ->
      NCheckedTcExp gamma omega ef ty_ef eff_ef ->
      NCheckedTcExp gamma omega ea ty_ea eff_ea ->
      static_heap_neutral eff_eff ->
      static_heap_neutral eff_ef ->
      static_heap_neutral eff_ea ->
      NCheckedBackTriangle gamma omega ef (EEffApp ef ea) ->
      NCheckedBackTriangle gamma omega ea (EEffApp ef ea) ->
      NCheckedBackTriangle gamma omega (EMuApp ef ea) (EEffApp ef ea)
| NCBT_PairPar :
    forall gamma omega ef1 ea1 ef2 ea2 ty1 ty2 eff1 eff2
      eff_summary1 eff_summary2,
      NCheckedTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 ->
      NCheckedTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
      NCheckedTcExp gamma omega (EEffApp ef1 ea1) TyEffect eff_summary1 ->
      NCheckedTcExp gamma omega (EEffApp ef2 ea2) TyEffect eff_summary2 ->
      static_heap_neutral eff_summary1 ->
      static_heap_neutral eff_summary2 ->
      static_noalloc eff1 ->
      static_noalloc eff2 ->
      NCheckedBackTriangle gamma omega
        (EMuApp ef1 ea1) (EEffApp ef1 ea1) ->
      NCheckedBackTriangle gamma omega
        (EMuApp ef2 ea2) (EEffApp ef2 ea2) ->
      NCheckedBackTriangle gamma omega
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
        (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
| NCBT_RgnApp :
    forall gamma omega er r ty eff ty_app eff_app,
      NCheckedTcExp gamma omega er ty eff ->
      NCheckedTcExp gamma omega (ERgnApp er r) ty_app eff_app ->
      NCheckedBackTriangle gamma omega er EEmpty ->
      NCheckedBackTriangle gamma omega (ERgnApp er r) EEmpty
| NCBT_Cond :
    forall gamma omega e et ef efft efff ty ty_t ty_f
      eff_e eff_et eff_ef,
      NCheckedTcExp gamma omega e TyBool eff_e ->
      NCheckedTcExp gamma omega et ty_t eff_et ->
      NCheckedTcExp gamma omega ef ty_f eff_ef ->
      NCheckedTcExp gamma omega (ECond e et ef) ty
        (static_union eff_e (static_union eff_et eff_ef)) ->
      static_heap_neutral eff_e ->
      NCheckedBackTriangle gamma omega e EEmpty ->
      NCheckedBackTriangle gamma omega et efft ->
      NCheckedBackTriangle gamma omega ef efff ->
      NCheckedBackTriangle gamma omega (ECond e et ef) (ECond e efft efff)
| NCBT_Ref :
    forall gamma omega r e eff ty static ty_ref eff_ref,
      NCheckedTcExp gamma omega e ty static ->
      NCheckedTcExp gamma omega (ERef r e) ty_ref eff_ref ->
      NCheckedBackTriangle gamma omega e eff ->
      NCheckedBackTriangle gamma omega (ERef r e)
        (EConcat eff (EAllocAbs r))
| NCBT_Deref :
    forall gamma omega r e eff ty static ty_deref eff_deref,
      NCheckedTcExp gamma omega e ty static ->
      NCheckedTcExp gamma omega (EDeref r e) ty_deref eff_deref ->
      NCheckedBackTriangle gamma omega e eff ->
      NCheckedBackTriangle gamma omega (EDeref r e)
        (EConcat eff (EReadAbs r))
| NCBT_Assign :
    forall gamma omega r e1 e2 eff1 eff2 ty static ty_assign eff_assign,
      NCheckedTcExp gamma omega e1 ty static ->
      NCheckedTcExp gamma omega (EAssign r e1 e2) ty_assign eff_assign ->
      static_heap_neutral static ->
      NCheckedBackTriangle gamma omega e1 eff1 ->
      NCheckedBackTriangle gamma omega e2 eff2 ->
      NCheckedBackTriangle gamma omega
        (EAssign r e1 e2)
        (EConcat eff1 (EConcat eff2 (EWriteAbs r)))
| NCBT_Plus :
    forall gamma omega e1 e2 eff1 eff2 eff_static eff_e1,
      NCheckedTcExp gamma omega (EPlus e1 e2) TyNat eff_static ->
      NCheckedTcExp gamma omega e1 TyNat eff_e1 ->
      static_heap_neutral eff_e1 ->
      NCheckedBackTriangle gamma omega e1 eff1 ->
      NCheckedBackTriangle gamma omega e2 eff2 ->
      NCheckedBackTriangle gamma omega (EPlus e1 e2) (EConcat eff1 eff2)
| NCBT_Minus :
    forall gamma omega e1 e2 eff1 eff2 eff_static eff_e1,
      NCheckedTcExp gamma omega (EMinus e1 e2) TyNat eff_static ->
      NCheckedTcExp gamma omega e1 TyNat eff_e1 ->
      static_heap_neutral eff_e1 ->
      NCheckedBackTriangle gamma omega e1 eff1 ->
      NCheckedBackTriangle gamma omega e2 eff2 ->
      NCheckedBackTriangle gamma omega (EMinus e1 e2) (EConcat eff1 eff2)
| NCBT_Times :
    forall gamma omega e1 e2 eff1 eff2 eff_static eff_e1,
      NCheckedTcExp gamma omega (ETimes e1 e2) TyNat eff_static ->
      NCheckedTcExp gamma omega e1 TyNat eff_e1 ->
      static_heap_neutral eff_e1 ->
      NCheckedBackTriangle gamma omega e1 eff1 ->
      NCheckedBackTriangle gamma omega e2 eff2 ->
      NCheckedBackTriangle gamma omega (ETimes e1 e2) (EConcat eff1 eff2)
| NCBT_Eq :
    forall gamma omega e1 e2 eff1 eff2 eff_static eff_e1,
      NCheckedTcExp gamma omega (EEq e1 e2) TyBool eff_static ->
      NCheckedTcExp gamma omega e1 TyNat eff_e1 ->
      static_heap_neutral eff_e1 ->
      NCheckedBackTriangle gamma omega e1 eff1 ->
      NCheckedBackTriangle gamma omega e2 eff2 ->
      NCheckedBackTriangle gamma omega (EEq e1 e2) (EConcat eff1 eff2)
| NCBT_Top :
    forall gamma omega e ty eff,
      NCheckedTcExp gamma omega e ty eff ->
      NCheckedBackTriangle gamma omega e ETop.

Lemma NRegionTypeWFAt_weaken_cons :
  forall depth omega x rgn,
    NRegionTypeWFAt depth omega rgn ->
    NRegionTypeWFAt depth (x :: omega) rgn.
Proof.
  intros depth omega x rgn HWF.
  inversion HWF; subst; constructor; simpl; auto.
Qed.

Lemma NStaticActionWFAt_weaken_cons :
  forall depth omega x action,
    NStaticActionWFAt depth omega action ->
    NStaticActionWFAt depth (x :: omega) action.
Proof.
  intros depth omega x action HWF.
  inversion HWF; subst; constructor;
    eauto using NRegionTypeWFAt_weaken_cons.
Qed.

Lemma NStaticEffectWFAt_weaken_cons :
  forall depth omega x eff,
    NStaticEffectWFAt depth omega eff ->
    NStaticEffectWFAt depth (x :: omega) eff.
Proof.
  intros depth omega x eff HWF.
  induction HWF as [| action eff HAction _ IH].
  - constructor.
  - constructor; eauto using NStaticActionWFAt_weaken_cons.
Qed.

Lemma NTyWFAt_weaken_cons :
  forall depth omega x ty,
    NTyWFAt depth omega ty ->
    NTyWFAt depth (x :: omega) ty.
Proof.
  intros depth omega x ty HWF.
  induction HWF; constructor;
    eauto using
      NRegionTypeWFAt_weaken_cons,
      NStaticEffectWFAt_weaken_cons.
Qed.

Lemma NCtxWF_weaken_cons :
  forall omega x gamma,
    NCtxWF omega gamma ->
    NCtxWF (x :: omega) gamma.
Proof.
  intros omega x gamma HWF.
  unfold NCtxWF, NTyWF in *.
  induction HWF as [| binding gamma HBinding _ IH].
  - constructor.
  - constructor; simpl in *; eauto using NTyWFAt_weaken_cons.
Qed.

Lemma NRegularTcExp_to_NTcExp :
  forall gamma omega e ty eff,
    NRegularTcExp gamma omega e ty eff ->
    NTcExp gamma omega e ty eff.
Proof.
  intros gamma omega e ty eff HReg.
  exact (NRegularTcExp_typed _ _ _ _ _ HReg).
Qed.

Lemma NCheckedTcExp_to_NTcExp :
  forall gamma omega e ty eff,
    NCheckedTcExp gamma omega e ty eff ->
    NTcExp gamma omega e ty eff.
Proof.
  intros gamma omega e ty eff HChecked.
  inversion HChecked; subst.
  assumption.
Qed.

Lemma NCheckedTcExp_shape :
  forall gamma omega e ty eff,
    NCheckedTcExp gamma omega e ty eff ->
    NCheckedTcExpShape gamma omega e ty eff.
Proof.
  intros gamma omega e ty eff HChecked.
  inversion HChecked; subst.
  assumption.
Qed.

Lemma NCheckedTcExp_rgn_ctx_wf :
  forall gamma omega e ty eff,
    NCheckedTcExp gamma omega e ty eff ->
    NRgnCtxWF omega.
Proof.
  intros gamma omega e ty eff HChecked.
  inversion HChecked; subst.
  assumption.
Qed.

Lemma NCheckedTcExp_ctx_wf :
  forall gamma omega e ty eff,
    NCheckedTcExp gamma omega e ty eff ->
    NCtxWF omega gamma.
Proof.
  intros gamma omega e ty eff HChecked.
  inversion HChecked; subst.
  assumption.
Qed.

Lemma NCheckedTcExp_ty_wf :
  forall gamma omega e ty eff,
    NCheckedTcExp gamma omega e ty eff ->
    NTyWF omega ty.
Proof.
  intros gamma omega e ty eff HChecked.
  inversion HChecked; subst.
  assumption.
Qed.

Lemma NCheckedTcExp_eff_wf :
  forall gamma omega e ty eff,
    NCheckedTcExp gamma omega e ty eff ->
    NStaticEffectWF omega eff.
Proof.
  intros gamma omega e ty eff HChecked.
  inversion HChecked; subst.
  assumption.
Qed.

Lemma NCheckedTcExp_to_regular :
  forall gamma omega e ty eff,
    NCheckedTcExp gamma omega e ty eff ->
    NRegularTcExp gamma omega e ty eff.
Proof.
  intros gamma omega e ty eff HChecked.
  constructor.
  - eapply NCheckedTcExp_to_NTcExp; eauto.
  - eapply NCheckedTcExp_rgn_ctx_wf; eauto.
  - eapply NCheckedTcExp_ctx_wf; eauto.
  - eapply NCheckedTcExp_ty_wf; eauto.
  - eapply NCheckedTcExp_eff_wf; eauto.
Qed.

Lemma NRegularRegionBody_to_regular_tcexp :
  forall x gamma omega e ty eff,
    NRegularRegionBody x gamma omega e ty eff ->
    NRegularTcExp gamma (x :: omega) e ty eff.
Proof.
  intros x gamma omega e ty eff HReg.
  destruct HReg as [HTyped HRgnCtxWF _ HCtxWF HTyWF HEffWF].
  constructor; eauto using NCtxWF_weaken_cons.
Qed.

Record NCheckedRegionBody
    (x : VarId) (gamma : NCtx) (omega : NRgnCtx)
    (e : NExpr) (ty : NTy) (eff : StaticEffect) : Prop := {
  NCheckedRegionBody_checked :
    NCheckedTcExp gamma (x :: omega) e ty eff;
  NCheckedRegionBody_backtriangle :
    NCheckedBackTriangle gamma (x :: omega) e EEmpty;
  NCheckedRegionBody_fresh :
    ~ In x omega;
  NCheckedRegionBody_ctx_wf :
    NCtxWF omega gamma
}.

Lemma NCheckedRegionBody_to_regular_region_body :
  forall x gamma omega e ty eff,
    NCheckedRegionBody x gamma omega e ty eff ->
    NRegularRegionBody x gamma omega e ty eff.
Proof.
  intros x gamma omega e ty eff HChecked.
  destruct HChecked as [HBody _ HFresh HCtxWF].
  constructor.
  - eapply NCheckedTcExp_to_NTcExp; eauto.
  - eapply NCheckedTcExp_rgn_ctx_wf; eauto.
  - exact HFresh.
  - exact HCtxWF.
  - eapply NCheckedTcExp_ty_wf; eauto.
  - eapply NCheckedTcExp_eff_wf; eauto.
Qed.

Lemma NCheckedRegionBody_to_NTcExp :
  forall x gamma omega e ty eff,
    NCheckedRegionBody x gamma omega e ty eff ->
    NTcExp gamma (x :: omega) e ty eff.
Proof.
  intros x gamma omega e ty eff HChecked.
  destruct HChecked as [HBody _ _ _].
  eapply NCheckedTcExp_to_NTcExp; eauto.
Qed.

Lemma NRegularTcExp_arrow_wf :
  forall gamma omega e ty_arg eff_body ty_body eff_summary eff_f,
    NRegularTcExp gamma omega e
      (TyArrow ty_arg eff_body ty_body eff_summary)
      eff_f ->
    NTyWF omega ty_arg /\
    NStaticEffectWF omega eff_body /\
    NTyWF omega ty_body /\
    NStaticEffectWF omega eff_summary.
Proof.
  intros gamma omega e ty_arg eff_body ty_body eff_summary eff_f HReg.
  destruct HReg as [_ _ _ HTyWF _].
  inversion HTyWF; subst.
  repeat split; assumption.
Qed.

Lemma NRegularTcExp_forall_wf :
  forall gamma omega e eff_body ty eff_f,
    NRegularTcExp gamma omega e (TyForallRgn eff_body ty) eff_f ->
    NStaticEffectWFAt 1 omega eff_body /\
    NTyWFAt 1 omega ty.
Proof.
  intros gamma omega e eff_body ty eff_f HReg.
  destruct HReg as [_ _ _ HTyWF _].
  inversion HTyWF; subst.
  split; assumption.
Qed.

Lemma NRegularTcExp_ref_wf :
  forall gamma omega e rgn ty eff,
    NRegularTcExp gamma omega e (TyRef rgn ty) eff ->
    NRegionTypeWF omega rgn /\ NTyWF omega ty.
Proof.
  intros gamma omega e rgn ty eff HReg.
  destruct HReg as [_ _ _ HTyWF _].
  inversion HTyWF; subst.
  split; assumption.
Qed.

Lemma NRegularRegionBody_wf :
  forall x gamma omega e ty eff,
    NRegularRegionBody x gamma omega e ty eff ->
    ~ In x omega /\ NCtxWF omega gamma /\
    NTyWFAt 0 (x :: omega) ty.
Proof.
  intros x gamma omega e ty eff HReg.
  destruct HReg as [_ _ HFresh HCtxWF HTyWF _].
  repeat split; assumption.
Qed.

Record NTypingRegularity : Prop := {
  NTypingRegularity_expr_wf :
    forall gamma omega e ty eff,
      NTcExp gamma omega e ty eff ->
      NTyWF omega ty /\ NStaticEffectWF omega eff;

  NTypingRegularity_arrow_wf :
    forall ef gamma omega ty_arg eff_body ty_body eff_summary eff_f,
      NTcExp gamma omega ef
        (TyArrow ty_arg eff_body ty_body eff_summary)
        eff_f ->
      NTyWF omega ty_arg /\
      NStaticEffectWF omega eff_body /\
      NTyWF omega ty_body /\
      NStaticEffectWF omega eff_summary;

  NTypingRegularity_forall_wf :
    forall er gamma omega eff_body ty eff_f,
      NTcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
      NStaticEffectWFAt 1 omega eff_body /\
      NTyWFAt 1 omega ty;

  NTypingRegularity_region_body_wf :
    forall x e gamma omega ty eff,
      NTcExp gamma (x :: omega) e ty eff ->
      ~ In x omega /\ NCtxWF omega gamma /\
      NTyWFAt 0 (x :: omega) ty;

  NTypingRegularity_region_body_effect_wf :
    forall x e gamma omega ty eff,
      NTcExp gamma (x :: omega) e ty eff ->
      NStaticEffectWFAt 0 (x :: omega) eff;

  NTypingRegularity_ref_wf :
    forall e gamma omega rgn ty eff,
      NTcExp gamma omega e (TyRef rgn ty) eff ->
      NRegionTypeWF omega rgn /\ NTyWF omega ty
}.

Lemma NTypingRegularity_as_stated_uninhabited :
  NTypingRegularity -> False.
Proof.
  intros HRegular.
  set (x := "x"%char).
  set (bad_ty := TyRef (Rgn_FVar true true x) TyNat).
  assert (HTyped : NTcExp [(x, bad_ty)] [] (EVar x) bad_ty []).
  {
    apply NT_Var.
    reflexivity.
  }
  destruct
    (NTypingRegularity_expr_wf
      HRegular [(x, bad_ty)] [] (EVar x) bad_ty [] HTyped)
    as (HTyWF & _).
  unfold bad_ty in HTyWF.
  inversion HTyWF; subst.
  match goal with
  | HRegionWF : NRegionTypeWFAt 0 [] (Rgn_FVar true true x) |- _ =>
      inversion HRegionWF; subst; simpl in *; contradiction
  end.
Qed.

Lemma NRegularTcExp_from_typed :
  forall gamma omega e ty eff,
    NTypingRegularity ->
    NRgnCtxWF omega ->
    NCtxWF omega gamma ->
    NTcExp gamma omega e ty eff ->
    NRegularTcExp gamma omega e ty eff.
Proof.
  intros gamma omega e ty eff HRegular HRgnCtx HCtx HTyped.
  destruct (NTypingRegularity_expr_wf HRegular gamma omega e ty eff HTyped)
    as (HTyWF & HEffWF).
  constructor; assumption.
Qed.

Lemma NRegularRegionBody_from_typed :
  forall x gamma omega e ty eff,
    NTypingRegularity ->
    NRgnCtxWF omega ->
    NTcExp gamma (x :: omega) e ty eff ->
    NRegularRegionBody x gamma omega e ty eff.
Proof.
  intros x gamma omega e ty eff HRegular HRgnCtx HTyped.
  destruct
    (NTypingRegularity_region_body_wf
      HRegular x e gamma omega ty eff HTyped)
    as (HFresh & HCtxWF & HTyWF).
  pose proof
    (NTypingRegularity_region_body_effect_wf
      HRegular x e gamma omega ty eff HTyped)
    as HEffWF.
  constructor; try assumption.
  constructor; assumption.
Qed.
