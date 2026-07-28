From Stdlib Require Import List.
From Stdlib Require Import Ascii.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Typing.Judgments.
Require Import theories.SmallStep.Typing.Resolve.
Require Import theories.SmallStep.Typing.Types.

Import ListNotations.
Open Scope char_scope.

Definition RgnCtxWF (omega : RgnCtx) : Prop :=
  NoDup omega.

Record RegularTcExp
    (gamma : Ctx) (omega : RgnCtx)
    (e : Expr) (ty : Ty) (eff : StaticEffect) : Prop := {
  RegularTcExp_typed :
    TcExp gamma omega e ty eff;
  RegularTcExp_rgn_ctx_wf :
    RgnCtxWF omega;
  RegularTcExp_ctx_wf :
    CtxWF omega gamma;
  RegularTcExp_ty_wf :
    TyWF omega ty;
  RegularTcExp_eff_wf :
    StaticEffectWF omega eff
}.

Record RegularRegionBody
    (x : VarId) (gamma : Ctx) (omega : RgnCtx)
    (e : Expr) (ty : Ty) (eff : StaticEffect) : Prop := {
  RegularRegionBody_typed :
    TcExp gamma (x :: omega) e ty eff;
  RegularRegionBody_rgn_ctx_wf :
    RgnCtxWF (x :: omega);
  RegularRegionBody_fresh :
    ~ In x omega;
  RegularRegionBody_ctx_wf :
    CtxWF omega gamma;
  RegularRegionBody_ty_wf :
    TyWFAt 0 (x :: omega) ty;
  RegularRegionBody_eff_wf :
    StaticEffectWFAt 0 (x :: omega) eff
}.

Inductive CheckedTcExp :
    Ctx -> RgnCtx -> Expr -> Ty -> StaticEffect -> Prop :=
| CheckedTcExp_intro :
    forall gamma omega e ty eff,
    TcExp gamma omega e ty eff ->
    RgnCtxWF omega ->
    CtxWF omega gamma ->
    TyWF omega ty ->
    StaticEffectWF omega eff ->
    CheckedTcExpShape gamma omega e ty eff ->
    CheckedTcExp gamma omega e ty eff
with CheckedTcExpShape :
    Ctx -> RgnCtx -> Expr -> Ty -> StaticEffect -> Prop :=
| CTS_Const :
    forall gamma omega n,
      CheckedTcExpShape gamma omega (EConst n) TyNat []
| CTS_Bool :
    forall gamma omega b,
      CheckedTcExpShape gamma omega (EBool b) TyBool []
| CTS_Var :
    forall gamma omega x ty,
      ctx_binds x ty gamma ->
      CheckedTcExpShape gamma omega (EVar x) ty []
| CTS_Mu :
    forall gamma omega f x ec ee ty_arg ty_body eff_body eff_summary,
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      CheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ee ->
      CheckedTcExpShape gamma omega (EMu f x ec ee)
        (TyArrow ty_arg eff_body ty_body eff_summary) []
| CTS_LambdaRgn :
    forall gamma omega x e ty eff,
      ~ In x omega ->
      CtxWF omega gamma ->
      CheckedBackTriangle gamma (x :: omega) e EEmpty ->
      CheckedTcExp gamma (x :: omega) e ty eff ->
      CheckedTcExpShape gamma omega (ELambdaRgn x e)
        (TyForallRgn (close_static_effect x eff) (close_ty x ty)) []
| CTS_MuApp :
    forall gamma omega ef ea ty_arg ty_body eff_body eff_summary eff_f eff_a,
      CheckedTcExp gamma omega ef
        (TyArrow ty_arg eff_body ty_body eff_summary) eff_f ->
      CheckedTcExp gamma omega ea ty_arg eff_a ->
      CheckedTcExpShape gamma omega (EMuApp ef ea) ty_body
        (static_union eff_f (static_union eff_a eff_body))
| CTS_RgnApp :
    forall gamma omega er r ty eff_body eff_f,
      region_expr_wf omega r ->
      CheckedTcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
      CheckedTcExpShape gamma omega (ERgnApp er r) (open_ty r ty)
        (static_union eff_f (open_static_effect r eff_body))
| CTS_EffApp :
    forall gamma omega ef ea ty_arg ty_body eff_body eff_summary eff_f eff_a,
      CheckedTcExp gamma omega ef
        (TyArrow ty_arg eff_body ty_body eff_summary) eff_f ->
      CheckedTcExp gamma omega ea ty_arg eff_a ->
      CheckedTcExpShape gamma omega (EEffApp ef ea) TyEffect
        (static_union eff_f (static_union eff_a eff_summary))
| CTS_PairPar :
    forall gamma omega ef1 ea1 ef2 ea2 ty1 ty2 eff1 eff2
      eff_summary1 eff_summary2,
      CheckedTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 ->
      CheckedTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
      CheckedTcExp gamma omega (EEffApp ef1 ea1) TyEffect eff_summary1 ->
      CheckedTcExp gamma omega (EEffApp ef2 ea2) TyEffect eff_summary2 ->
      static_noalloc eff1 ->
      static_noalloc eff2 ->
      CheckedTcExpShape gamma omega
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
        (TyPair ty1 ty2)
        (static_union (static_union eff_summary1 eff_summary2)
          (static_union eff1 eff2))
| CTS_Cond :
    forall gamma omega e et ef ty eff_e eff_t eff_f,
      CheckedTcExp gamma omega e TyBool eff_e ->
      CheckedTcExp gamma omega et ty eff_t ->
      CheckedTcExp gamma omega ef ty eff_f ->
      CheckedTcExpShape gamma omega (ECond e et ef) ty
        (static_union eff_e (static_union eff_t eff_f))
| CTS_Ref :
    forall gamma omega r e ty eff,
      region_expr_wf omega r ->
      CheckedTcExp gamma omega e ty eff ->
      CheckedTcExpShape gamma omega (ERef r e)
        (TyRef (region_expr_to_type r) ty)
        (SAlloc (region_expr_to_type r) :: eff)
| CTS_Deref :
    forall gamma omega r e ty eff,
      region_expr_wf omega r ->
      CheckedTcExp gamma omega e
        (TyRef (region_expr_to_type r) ty) eff ->
      CheckedTcExpShape gamma omega (EDeref r e) ty
        (SRead (region_expr_to_type r) :: eff)
| CTS_Assign :
    forall gamma omega r ea ev ty eff_a eff_v,
      region_expr_wf omega r ->
      CheckedTcExp gamma omega ea
        (TyRef (region_expr_to_type r) ty) eff_a ->
      CheckedTcExp gamma omega ev ty eff_v ->
      CheckedTcExpShape gamma omega (EAssign r ea ev) TyUnit
        (SWrite (region_expr_to_type r) :: static_union eff_a eff_v)
| CTS_Plus :
    forall gamma omega e1 e2 eff1 eff2,
      CheckedTcExp gamma omega e1 TyNat eff1 ->
      CheckedTcExp gamma omega e2 TyNat eff2 ->
      CheckedTcExpShape gamma omega (EPlus e1 e2) TyNat
        (static_union eff1 eff2)
| CTS_Minus :
    forall gamma omega e1 e2 eff1 eff2,
      CheckedTcExp gamma omega e1 TyNat eff1 ->
      CheckedTcExp gamma omega e2 TyNat eff2 ->
      CheckedTcExpShape gamma omega (EMinus e1 e2) TyNat
        (static_union eff1 eff2)
| CTS_Times :
    forall gamma omega e1 e2 eff1 eff2,
      CheckedTcExp gamma omega e1 TyNat eff1 ->
      CheckedTcExp gamma omega e2 TyNat eff2 ->
      CheckedTcExpShape gamma omega (ETimes e1 e2) TyNat
        (static_union eff1 eff2)
| CTS_Eq :
    forall gamma omega e1 e2 eff1 eff2,
      CheckedTcExp gamma omega e1 TyNat eff1 ->
      CheckedTcExp gamma omega e2 TyNat eff2 ->
      CheckedTcExpShape gamma omega (EEq e1 e2) TyBool
        (static_union eff1 eff2)
| CTS_AllocAbs :
    forall gamma omega r,
      region_expr_wf omega r ->
      CheckedTcExpShape gamma omega (EAllocAbs r) TyEffect []
| CTS_ReadAbs :
    forall gamma omega r,
      region_expr_wf omega r ->
      CheckedTcExpShape gamma omega (EReadAbs r) TyEffect []
| CTS_WriteAbs :
    forall gamma omega r,
      region_expr_wf omega r ->
      CheckedTcExpShape gamma omega (EWriteAbs r) TyEffect []
| CTS_ReadConc :
    forall gamma omega e r ty eff,
      CheckedTcExp gamma omega e (TyRef r ty) eff ->
      CheckedTcExpShape gamma omega (EReadConc e) TyEffect eff
| CTS_WriteConc :
    forall gamma omega e r ty eff,
      CheckedTcExp gamma omega e (TyRef r ty) eff ->
      CheckedTcExpShape gamma omega (EWriteConc e) TyEffect eff
| CTS_Concat :
    forall gamma omega e1 e2 eff1 eff2,
      CheckedTcExp gamma omega e1 TyEffect eff1 ->
      CheckedTcExp gamma omega e2 TyEffect eff2 ->
      CheckedTcExpShape gamma omega (EConcat e1 e2) TyEffect
        (static_union eff1 eff2)
| CTS_Top :
    forall gamma omega,
      CheckedTcExpShape gamma omega ETop TyEffect []
| CTS_Empty :
    forall gamma omega,
      CheckedTcExpShape gamma omega EEmpty TyEffect []
with CheckedBackTriangle :
    Ctx -> RgnCtx -> Expr -> Expr -> Prop :=
| CBT_Num :
    forall gamma omega n,
      CheckedTcExp gamma omega (EConst n) TyNat [] ->
      CheckedBackTriangle gamma omega (EConst n) EEmpty
| CBT_Bool :
    forall gamma omega b,
      CheckedTcExp gamma omega (EBool b) TyBool [] ->
      CheckedBackTriangle gamma omega (EBool b) EEmpty
| CBT_Var :
    forall gamma omega x ty,
      CheckedTcExp gamma omega (EVar x) ty [] ->
      CheckedBackTriangle gamma omega (EVar x) EEmpty
| CBT_Mu :
    forall gamma omega f x ec ee ty eff,
      CheckedTcExp gamma omega (EMu f x ec ee) ty eff ->
      CheckedBackTriangle gamma omega (EMu f x ec ee) EEmpty
| CBT_LambdaRgn :
    forall gamma omega x e ty eff,
      CheckedTcExp gamma omega (ELambdaRgn x e) ty eff ->
      CheckedBackTriangle gamma omega (ELambdaRgn x e) EEmpty
| CBT_App :
    forall gamma omega ef ea ty_mu eff_mu eff_eff
      ty_ef ty_ea eff_ef eff_ea,
      CheckedTcExp gamma omega (EMuApp ef ea) ty_mu eff_mu ->
      CheckedTcExp gamma omega (EEffApp ef ea) TyEffect eff_eff ->
      CheckedTcExp gamma omega ef ty_ef eff_ef ->
      CheckedTcExp gamma omega ea ty_ea eff_ea ->
      static_heap_neutral eff_eff ->
      static_heap_neutral eff_ef ->
      static_heap_neutral eff_ea ->
      CheckedBackTriangle gamma omega ef (EEffApp ef ea) ->
      CheckedBackTriangle gamma omega ea (EEffApp ef ea) ->
      CheckedBackTriangle gamma omega (EMuApp ef ea) (EEffApp ef ea)
| CBT_PairPar :
    forall gamma omega ef1 ea1 ef2 ea2 ty1 ty2 eff1 eff2
      eff_summary1 eff_summary2,
      CheckedTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 ->
      CheckedTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
      CheckedTcExp gamma omega (EEffApp ef1 ea1) TyEffect eff_summary1 ->
      CheckedTcExp gamma omega (EEffApp ef2 ea2) TyEffect eff_summary2 ->
      static_heap_neutral eff_summary1 ->
      static_heap_neutral eff_summary2 ->
      static_noalloc eff1 ->
      static_noalloc eff2 ->
      CheckedBackTriangle gamma omega
        (EMuApp ef1 ea1) (EEffApp ef1 ea1) ->
      CheckedBackTriangle gamma omega
        (EMuApp ef2 ea2) (EEffApp ef2 ea2) ->
      CheckedBackTriangle gamma omega
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
        (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2))
| CBT_RgnApp :
    forall gamma omega er r ty eff ty_app eff_app,
      CheckedTcExp gamma omega er ty eff ->
      CheckedTcExp gamma omega (ERgnApp er r) ty_app eff_app ->
      CheckedBackTriangle gamma omega er EEmpty ->
      CheckedBackTriangle gamma omega (ERgnApp er r) EEmpty
| CBT_Cond :
    forall gamma omega e et ef efft efff ty ty_t ty_f
      eff_e eff_et eff_ef,
      CheckedTcExp gamma omega e TyBool eff_e ->
      CheckedTcExp gamma omega et ty_t eff_et ->
      CheckedTcExp gamma omega ef ty_f eff_ef ->
      CheckedTcExp gamma omega (ECond e et ef) ty
        (static_union eff_e (static_union eff_et eff_ef)) ->
      static_heap_neutral eff_e ->
      CheckedBackTriangle gamma omega e EEmpty ->
      CheckedBackTriangle gamma omega et efft ->
      CheckedBackTriangle gamma omega ef efff ->
      CheckedBackTriangle gamma omega (ECond e et ef) (ECond e efft efff)
| CBT_Ref :
    forall gamma omega r e eff ty static ty_ref eff_ref,
      CheckedTcExp gamma omega e ty static ->
      CheckedTcExp gamma omega (ERef r e) ty_ref eff_ref ->
      CheckedBackTriangle gamma omega e eff ->
      CheckedBackTriangle gamma omega (ERef r e)
        (EConcat eff (EAllocAbs r))
| CBT_Deref :
    forall gamma omega r e eff ty static ty_deref eff_deref,
      CheckedTcExp gamma omega e ty static ->
      CheckedTcExp gamma omega (EDeref r e) ty_deref eff_deref ->
      CheckedBackTriangle gamma omega e eff ->
      CheckedBackTriangle gamma omega (EDeref r e)
        (EConcat eff (EReadAbs r))
| CBT_Assign :
    forall gamma omega r e1 e2 eff1 eff2 ty static ty_assign eff_assign,
      CheckedTcExp gamma omega e1 ty static ->
      CheckedTcExp gamma omega (EAssign r e1 e2) ty_assign eff_assign ->
      static_heap_neutral static ->
      CheckedBackTriangle gamma omega e1 eff1 ->
      CheckedBackTriangle gamma omega e2 eff2 ->
      CheckedBackTriangle gamma omega
        (EAssign r e1 e2)
        (EConcat eff1 (EConcat eff2 (EWriteAbs r)))
| CBT_Plus :
    forall gamma omega e1 e2 eff1 eff2 eff_static eff_e1,
      CheckedTcExp gamma omega (EPlus e1 e2) TyNat eff_static ->
      CheckedTcExp gamma omega e1 TyNat eff_e1 ->
      static_heap_neutral eff_e1 ->
      CheckedBackTriangle gamma omega e1 eff1 ->
      CheckedBackTriangle gamma omega e2 eff2 ->
      CheckedBackTriangle gamma omega (EPlus e1 e2) (EConcat eff1 eff2)
| CBT_Minus :
    forall gamma omega e1 e2 eff1 eff2 eff_static eff_e1,
      CheckedTcExp gamma omega (EMinus e1 e2) TyNat eff_static ->
      CheckedTcExp gamma omega e1 TyNat eff_e1 ->
      static_heap_neutral eff_e1 ->
      CheckedBackTriangle gamma omega e1 eff1 ->
      CheckedBackTriangle gamma omega e2 eff2 ->
      CheckedBackTriangle gamma omega (EMinus e1 e2) (EConcat eff1 eff2)
| CBT_Times :
    forall gamma omega e1 e2 eff1 eff2 eff_static eff_e1,
      CheckedTcExp gamma omega (ETimes e1 e2) TyNat eff_static ->
      CheckedTcExp gamma omega e1 TyNat eff_e1 ->
      static_heap_neutral eff_e1 ->
      CheckedBackTriangle gamma omega e1 eff1 ->
      CheckedBackTriangle gamma omega e2 eff2 ->
      CheckedBackTriangle gamma omega (ETimes e1 e2) (EConcat eff1 eff2)
| CBT_Eq :
    forall gamma omega e1 e2 eff1 eff2 eff_static eff_e1,
      CheckedTcExp gamma omega (EEq e1 e2) TyBool eff_static ->
      CheckedTcExp gamma omega e1 TyNat eff_e1 ->
      static_heap_neutral eff_e1 ->
      CheckedBackTriangle gamma omega e1 eff1 ->
      CheckedBackTriangle gamma omega e2 eff2 ->
      CheckedBackTriangle gamma omega (EEq e1 e2) (EConcat eff1 eff2)
| CBT_Top :
    forall gamma omega e ty eff,
      CheckedTcExp gamma omega e ty eff ->
      CheckedBackTriangle gamma omega e ETop.

Lemma RegionTypeWFAt_weaken_cons :
  forall depth omega x rgn,
    RegionTypeWFAt depth omega rgn ->
    RegionTypeWFAt depth (x :: omega) rgn.
Proof.
  intros depth omega x rgn HWF.
  inversion HWF; subst; constructor; simpl; auto.
Qed.

Lemma StaticActionWFAt_weaken_cons :
  forall depth omega x action,
    StaticActionWFAt depth omega action ->
    StaticActionWFAt depth (x :: omega) action.
Proof.
  intros depth omega x action HWF.
  inversion HWF; subst; constructor;
    eauto using RegionTypeWFAt_weaken_cons.
Qed.

Lemma StaticEffectWFAt_weaken_cons :
  forall depth omega x eff,
    StaticEffectWFAt depth omega eff ->
    StaticEffectWFAt depth (x :: omega) eff.
Proof.
  intros depth omega x eff HWF.
  induction HWF as [| action eff HAction _ IH].
  - constructor.
  - constructor; eauto using StaticActionWFAt_weaken_cons.
Qed.

Lemma TyWFAt_weaken_cons :
  forall depth omega x ty,
    TyWFAt depth omega ty ->
    TyWFAt depth (x :: omega) ty.
Proof.
  intros depth omega x ty HWF.
  induction HWF; constructor;
    eauto using
      RegionTypeWFAt_weaken_cons,
      StaticEffectWFAt_weaken_cons.
Qed.

Lemma CtxWF_weaken_cons :
  forall omega x gamma,
    CtxWF omega gamma ->
    CtxWF (x :: omega) gamma.
Proof.
  intros omega x gamma HWF.
  unfold CtxWF, TyWF in *.
  induction HWF as [| binding gamma HBinding _ IH].
  - constructor.
  - constructor; simpl in *; eauto using TyWFAt_weaken_cons.
Qed.

Lemma RegularTcExp_to_TcExp :
  forall gamma omega e ty eff,
    RegularTcExp gamma omega e ty eff ->
    TcExp gamma omega e ty eff.
Proof.
  intros gamma omega e ty eff HReg.
  exact (RegularTcExp_typed _ _ _ _ _ HReg).
Qed.

Lemma CheckedTcExp_to_TcExp :
  forall gamma omega e ty eff,
    CheckedTcExp gamma omega e ty eff ->
    TcExp gamma omega e ty eff.
Proof.
  intros gamma omega e ty eff HChecked.
  inversion HChecked; subst.
  assumption.
Qed.

Lemma CheckedTcExp_shape :
  forall gamma omega e ty eff,
    CheckedTcExp gamma omega e ty eff ->
    CheckedTcExpShape gamma omega e ty eff.
Proof.
  intros gamma omega e ty eff HChecked.
  inversion HChecked; subst.
  assumption.
Qed.

Lemma CheckedTcExp_rgn_ctx_wf :
  forall gamma omega e ty eff,
    CheckedTcExp gamma omega e ty eff ->
    RgnCtxWF omega.
Proof.
  intros gamma omega e ty eff HChecked.
  inversion HChecked; subst.
  assumption.
Qed.

Lemma CheckedTcExp_ctx_wf :
  forall gamma omega e ty eff,
    CheckedTcExp gamma omega e ty eff ->
    CtxWF omega gamma.
Proof.
  intros gamma omega e ty eff HChecked.
  inversion HChecked; subst.
  assumption.
Qed.

Lemma CheckedTcExp_ty_wf :
  forall gamma omega e ty eff,
    CheckedTcExp gamma omega e ty eff ->
    TyWF omega ty.
Proof.
  intros gamma omega e ty eff HChecked.
  inversion HChecked; subst.
  assumption.
Qed.

Lemma CheckedTcExp_eff_wf :
  forall gamma omega e ty eff,
    CheckedTcExp gamma omega e ty eff ->
    StaticEffectWF omega eff.
Proof.
  intros gamma omega e ty eff HChecked.
  inversion HChecked; subst.
  assumption.
Qed.

Lemma CheckedTcExp_to_regular :
  forall gamma omega e ty eff,
    CheckedTcExp gamma omega e ty eff ->
    RegularTcExp gamma omega e ty eff.
Proof.
  intros gamma omega e ty eff HChecked.
  constructor.
  - eapply CheckedTcExp_to_TcExp; eauto.
  - eapply CheckedTcExp_rgn_ctx_wf; eauto.
  - eapply CheckedTcExp_ctx_wf; eauto.
  - eapply CheckedTcExp_ty_wf; eauto.
  - eapply CheckedTcExp_eff_wf; eauto.
Qed.

Lemma RegularRegionBody_to_regular_tcexp :
  forall x gamma omega e ty eff,
    RegularRegionBody x gamma omega e ty eff ->
    RegularTcExp gamma (x :: omega) e ty eff.
Proof.
  intros x gamma omega e ty eff HReg.
  destruct HReg as [HTyped HRgnCtxWF _ HCtxWF HTyWF HEffWF].
  constructor; eauto using CtxWF_weaken_cons.
Qed.

Record CheckedRegionBody
    (x : VarId) (gamma : Ctx) (omega : RgnCtx)
    (e : Expr) (ty : Ty) (eff : StaticEffect) : Prop := {
  CheckedRegionBody_checked :
    CheckedTcExp gamma (x :: omega) e ty eff;
  CheckedRegionBody_backtriangle :
    CheckedBackTriangle gamma (x :: omega) e EEmpty;
  CheckedRegionBody_fresh :
    ~ In x omega;
  CheckedRegionBody_ctx_wf :
    CtxWF omega gamma
}.

Lemma CheckedRegionBody_to_regular_region_body :
  forall x gamma omega e ty eff,
    CheckedRegionBody x gamma omega e ty eff ->
    RegularRegionBody x gamma omega e ty eff.
Proof.
  intros x gamma omega e ty eff HChecked.
  destruct HChecked as [HBody _ HFresh HCtxWF].
  constructor.
  - eapply CheckedTcExp_to_TcExp; eauto.
  - eapply CheckedTcExp_rgn_ctx_wf; eauto.
  - exact HFresh.
  - exact HCtxWF.
  - eapply CheckedTcExp_ty_wf; eauto.
  - eapply CheckedTcExp_eff_wf; eauto.
Qed.

Lemma CheckedRegionBody_to_TcExp :
  forall x gamma omega e ty eff,
    CheckedRegionBody x gamma omega e ty eff ->
    TcExp gamma (x :: omega) e ty eff.
Proof.
  intros x gamma omega e ty eff HChecked.
  destruct HChecked as [HBody _ _ _].
  eapply CheckedTcExp_to_TcExp; eauto.
Qed.

Lemma RegularTcExp_arrow_wf :
  forall gamma omega e ty_arg eff_body ty_body eff_summary eff_f,
    RegularTcExp gamma omega e
      (TyArrow ty_arg eff_body ty_body eff_summary)
      eff_f ->
    TyWF omega ty_arg /\
    StaticEffectWF omega eff_body /\
    TyWF omega ty_body /\
    StaticEffectWF omega eff_summary.
Proof.
  intros gamma omega e ty_arg eff_body ty_body eff_summary eff_f HReg.
  destruct HReg as [_ _ _ HTyWF _].
  inversion HTyWF; subst.
  repeat split; assumption.
Qed.

Lemma RegularTcExp_forall_wf :
  forall gamma omega e eff_body ty eff_f,
    RegularTcExp gamma omega e (TyForallRgn eff_body ty) eff_f ->
    StaticEffectWFAt 1 omega eff_body /\
    TyWFAt 1 omega ty.
Proof.
  intros gamma omega e eff_body ty eff_f HReg.
  destruct HReg as [_ _ _ HTyWF _].
  inversion HTyWF; subst.
  split; assumption.
Qed.

Lemma RegularTcExp_ref_wf :
  forall gamma omega e rgn ty eff,
    RegularTcExp gamma omega e (TyRef rgn ty) eff ->
    RegionTypeWF omega rgn /\ TyWF omega ty.
Proof.
  intros gamma omega e rgn ty eff HReg.
  destruct HReg as [_ _ _ HTyWF _].
  inversion HTyWF; subst.
  split; assumption.
Qed.

Lemma RegularRegionBody_wf :
  forall x gamma omega e ty eff,
    RegularRegionBody x gamma omega e ty eff ->
    ~ In x omega /\ CtxWF omega gamma /\
    TyWFAt 0 (x :: omega) ty.
Proof.
  intros x gamma omega e ty eff HReg.
  destruct HReg as [_ _ HFresh HCtxWF HTyWF _].
  repeat split; assumption.
Qed.

Record TypingRegularity : Prop := {
  TypingRegularity_expr_wf :
    forall gamma omega e ty eff,
      TcExp gamma omega e ty eff ->
      TyWF omega ty /\ StaticEffectWF omega eff;

  TypingRegularity_arrow_wf :
    forall ef gamma omega ty_arg eff_body ty_body eff_summary eff_f,
      TcExp gamma omega ef
        (TyArrow ty_arg eff_body ty_body eff_summary)
        eff_f ->
      TyWF omega ty_arg /\
      StaticEffectWF omega eff_body /\
      TyWF omega ty_body /\
      StaticEffectWF omega eff_summary;

  TypingRegularity_forall_wf :
    forall er gamma omega eff_body ty eff_f,
      TcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
      StaticEffectWFAt 1 omega eff_body /\
      TyWFAt 1 omega ty;

  TypingRegularity_region_body_wf :
    forall x e gamma omega ty eff,
      TcExp gamma (x :: omega) e ty eff ->
      ~ In x omega /\ CtxWF omega gamma /\
      TyWFAt 0 (x :: omega) ty;

  TypingRegularity_region_body_effect_wf :
    forall x e gamma omega ty eff,
      TcExp gamma (x :: omega) e ty eff ->
      StaticEffectWFAt 0 (x :: omega) eff;

  TypingRegularity_ref_wf :
    forall e gamma omega rgn ty eff,
      TcExp gamma omega e (TyRef rgn ty) eff ->
      RegionTypeWF omega rgn /\ TyWF omega ty
}.

Lemma TypingRegularity_as_stated_uninhabited :
  TypingRegularity -> False.
Proof.
  intros HRegular.
  set (x := "x"%char).
  set (bad_ty := TyRef (Rgn_FVar true true x) TyNat).
  assert (HTyped : TcExp [(x, bad_ty)] [] (EVar x) bad_ty []).
  {
    apply T_Var.
    reflexivity.
  }
  destruct
    (TypingRegularity_expr_wf
      HRegular [(x, bad_ty)] [] (EVar x) bad_ty [] HTyped)
    as (HTyWF & _).
  unfold bad_ty in HTyWF.
  inversion HTyWF; subst.
  match goal with
  | HRegionWF : RegionTypeWFAt 0 [] (Rgn_FVar true true x) |- _ =>
      inversion HRegionWF; subst; simpl in *; contradiction
  end.
Qed.

Lemma RegularTcExp_from_typed :
  forall gamma omega e ty eff,
    TypingRegularity ->
    RgnCtxWF omega ->
    CtxWF omega gamma ->
    TcExp gamma omega e ty eff ->
    RegularTcExp gamma omega e ty eff.
Proof.
  intros gamma omega e ty eff HRegular HRgnCtx HCtx HTyped.
  destruct (TypingRegularity_expr_wf HRegular gamma omega e ty eff HTyped)
    as (HTyWF & HEffWF).
  constructor; assumption.
Qed.

Lemma RegularRegionBody_from_typed :
  forall x gamma omega e ty eff,
    TypingRegularity ->
    RgnCtxWF omega ->
    TcExp gamma (x :: omega) e ty eff ->
    RegularRegionBody x gamma omega e ty eff.
Proof.
  intros x gamma omega e ty eff HRegular HRgnCtx HTyped.
  destruct
    (TypingRegularity_region_body_wf
      HRegular x e gamma omega ty eff HTyped)
    as (HFresh & HCtxWF & HTyWF).
  pose proof
    (TypingRegularity_region_body_effect_wf
      HRegular x e gamma omega ty eff HTyped)
    as HEffWF.
  constructor; try assumption.
  constructor; assumption.
Qed.
