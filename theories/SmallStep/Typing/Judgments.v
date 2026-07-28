From Stdlib Require Import List.
From Stdlib Require Import Ascii.
From Stdlib Require Import Program.Equality.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Typing.Types.

Import ListNotations.

Definition Ctx := list (VarId * Ty).
Definition RgnCtx := list VarId.

Fixpoint ctx_lookup (x : VarId) (gamma : Ctx) : option Ty :=
  match gamma with
  | [] => None
  | (y, ty) :: gamma' =>
      if ascii_dec x y then Some ty else ctx_lookup x gamma'
  end.

Definition ctx_binds (x : VarId) (ty : Ty) (gamma : Ctx) : Prop :=
  ctx_lookup x gamma = Some ty.

Definition static_union (eff1 eff2 : StaticEffect) : StaticEffect :=
  eff1 ++ eff2.

Definition static_readonly (eff : StaticEffect) : Prop :=
  forall r, ~ In (SWrite r) eff.

Definition static_noalloc (eff : StaticEffect) : Prop :=
  forall r, ~ In (SAlloc r) eff.

Definition static_heap_neutral (eff : StaticEffect) : Prop :=
  static_noalloc eff /\ static_readonly eff.

Lemma static_noalloc_nil :
  static_noalloc [].
Proof.
  unfold static_noalloc.
  intros r HIn. inversion HIn.
Qed.

Lemma static_readonly_nil :
  static_readonly [].
Proof.
  unfold static_readonly.
  intros r HIn. inversion HIn.
Qed.

Lemma static_heap_neutral_nil :
  static_heap_neutral [].
Proof.
  split.
  - apply static_noalloc_nil.
  - apply static_readonly_nil.
Qed.

Lemma static_noalloc_app :
  forall eff1 eff2,
    static_noalloc eff1 ->
    static_noalloc eff2 ->
    static_noalloc (static_union eff1 eff2).
Proof.
  unfold static_noalloc, static_union.
  intros eff1 eff2 HNoAlloc1 HNoAlloc2 r HIn.
  apply in_app_or in HIn.
  destruct HIn as [HIn | HIn].
  - eapply HNoAlloc1; eauto.
  - eapply HNoAlloc2; eauto.
Qed.

Lemma static_noalloc_app_l :
  forall eff1 eff2,
    static_noalloc (static_union eff1 eff2) ->
    static_noalloc eff1.
Proof.
  unfold static_noalloc, static_union.
  intros eff1 eff2 HNoAlloc r HIn.
  eapply HNoAlloc.
  apply in_or_app.
  left. exact HIn.
Qed.

Lemma static_noalloc_app_r :
  forall eff1 eff2,
    static_noalloc (static_union eff1 eff2) ->
    static_noalloc eff2.
Proof.
  unfold static_noalloc, static_union.
  intros eff1 eff2 HNoAlloc r HIn.
  eapply HNoAlloc.
  apply in_or_app.
  right. exact HIn.
Qed.

Lemma static_readonly_app :
  forall eff1 eff2,
    static_readonly eff1 ->
    static_readonly eff2 ->
    static_readonly (static_union eff1 eff2).
Proof.
  unfold static_readonly, static_union.
  intros eff1 eff2 HReadOnly1 HReadOnly2 r HIn.
  apply in_app_or in HIn.
  destruct HIn as [HIn | HIn].
  - eapply HReadOnly1; eauto.
  - eapply HReadOnly2; eauto.
Qed.

Lemma static_readonly_app_l :
  forall eff1 eff2,
    static_readonly (static_union eff1 eff2) ->
    static_readonly eff1.
Proof.
  unfold static_readonly, static_union.
  intros eff1 eff2 HReadOnly r HIn.
  eapply HReadOnly.
  apply in_or_app.
  left. exact HIn.
Qed.

Lemma static_readonly_app_r :
  forall eff1 eff2,
    static_readonly (static_union eff1 eff2) ->
    static_readonly eff2.
Proof.
  unfold static_readonly, static_union.
  intros eff1 eff2 HReadOnly r HIn.
  eapply HReadOnly.
  apply in_or_app.
  right. exact HIn.
Qed.

Lemma static_heap_neutral_app :
  forall eff1 eff2,
    static_heap_neutral eff1 ->
    static_heap_neutral eff2 ->
    static_heap_neutral (static_union eff1 eff2).
Proof.
  intros eff1 eff2 [HNoAlloc1 HReadOnly1] [HNoAlloc2 HReadOnly2].
  split.
  - eapply static_noalloc_app; eauto.
  - eapply static_readonly_app; eauto.
Qed.

Lemma static_heap_neutral_app_l :
  forall eff1 eff2,
    static_heap_neutral (static_union eff1 eff2) ->
    static_heap_neutral eff1.
Proof.
  intros eff1 eff2 [HNoAlloc HReadOnly].
  split.
  - eapply static_noalloc_app_l; eauto.
  - eapply static_readonly_app_l; eauto.
Qed.

Lemma static_heap_neutral_app_r :
  forall eff1 eff2,
    static_heap_neutral (static_union eff1 eff2) ->
    static_heap_neutral eff2.
Proof.
  intros eff1 eff2 [HNoAlloc HReadOnly].
  split.
  - eapply static_noalloc_app_r; eauto.
  - eapply static_readonly_app_r; eauto.
Qed.

Inductive region_expr_wf : RgnCtx -> RegionExpr -> Prop :=
| REWF_Const :
    forall omega r,
      region_expr_wf omega (region_const_expr r)
| REWF_FVar :
    forall omega x,
      In x omega ->
      region_expr_wf omega (region_var_expr x).

Inductive TcExp : Ctx -> RgnCtx -> Expr -> Ty -> StaticEffect -> Prop :=
| T_Const :
    forall gamma omega n,
      TcExp gamma omega (EConst n) TyNat []
| T_Bool :
    forall gamma omega b,
      TcExp gamma omega (EBool b) TyBool []
| T_Var :
    forall gamma omega x ty,
      ctx_binds x ty gamma ->
      TcExp gamma omega (EVar x) ty []
| T_Mu :
    forall gamma omega f x ec ee ty_arg ty_body eff_body eff_summary,
      TcExp
        ((x, ty_arg) :: (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      TcExp
        ((x, ty_arg) :: (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      TcExp gamma omega (EMu f x ec ee)
        (TyArrow ty_arg eff_body ty_body eff_summary) []
| T_LambdaRgn :
    forall gamma omega x e ty eff,
      TcExp gamma (x :: omega) e ty eff ->
      TcExp gamma omega (ELambdaRgn x e)
        (TyForallRgn (close_static_effect x eff) (close_ty x ty)) []
| T_MuApp :
    forall gamma omega ef ea ty_arg ty_body eff_body eff_summary eff_f eff_a,
      TcExp gamma omega ef
        (TyArrow ty_arg eff_body ty_body eff_summary) eff_f ->
      TcExp gamma omega ea ty_arg eff_a ->
      TcExp gamma omega (EMuApp ef ea) ty_body
        (static_union eff_f (static_union eff_a eff_body))
| T_RgnApp :
    forall gamma omega er r ty eff_body eff_f,
      region_expr_wf omega r ->
      TcExp gamma omega er (TyForallRgn eff_body ty) eff_f ->
      TcExp gamma omega (ERgnApp er r) (open_ty r ty)
        (static_union eff_f (open_static_effect r eff_body))
| T_EffApp :
    forall gamma omega ef ea ty_arg ty_body eff_body eff_summary eff_f eff_a,
      TcExp gamma omega ef
        (TyArrow ty_arg eff_body ty_body eff_summary) eff_f ->
      TcExp gamma omega ea ty_arg eff_a ->
      TcExp gamma omega (EEffApp ef ea) TyEffect
        (static_union eff_f (static_union eff_a eff_summary))
| T_PairPar :
    forall gamma omega ef1 ea1 ef2 ea2 ty1 ty2 eff1 eff2
      eff_summary1 eff_summary2,
      TcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 ->
      TcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
      TcExp gamma omega (EEffApp ef1 ea1) TyEffect eff_summary1 ->
      TcExp gamma omega (EEffApp ef2 ea2) TyEffect eff_summary2 ->
      TcExp gamma omega
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
        (TyPair ty1 ty2)
        (static_union (static_union eff_summary1 eff_summary2)
          (static_union eff1 eff2))
| T_Cond :
    forall gamma omega e et ef ty eff_e eff_t eff_f,
      TcExp gamma omega e TyBool eff_e ->
      TcExp gamma omega et ty eff_t ->
      TcExp gamma omega ef ty eff_f ->
      TcExp gamma omega (ECond e et ef) ty
        (static_union eff_e (static_union eff_t eff_f))
| T_Ref :
    forall gamma omega r e ty eff,
      region_expr_wf omega r ->
      TcExp gamma omega e ty eff ->
      TcExp gamma omega (ERef r e) (TyRef (region_expr_to_type r) ty)
        (SAlloc (region_expr_to_type r) :: eff)
| T_Deref :
    forall gamma omega r e ty eff,
      region_expr_wf omega r ->
      TcExp gamma omega e (TyRef (region_expr_to_type r) ty) eff ->
      TcExp gamma omega (EDeref r e) ty
        (SRead (region_expr_to_type r) :: eff)
| T_Assign :
    forall gamma omega r ea ev ty eff_a eff_v,
      region_expr_wf omega r ->
      TcExp gamma omega ea (TyRef (region_expr_to_type r) ty) eff_a ->
      TcExp gamma omega ev ty eff_v ->
      TcExp gamma omega (EAssign r ea ev) TyUnit
        (SWrite (region_expr_to_type r) :: static_union eff_a eff_v)
| T_Plus :
    forall gamma omega e1 e2 eff1 eff2,
      TcExp gamma omega e1 TyNat eff1 ->
      TcExp gamma omega e2 TyNat eff2 ->
      TcExp gamma omega (EPlus e1 e2) TyNat (static_union eff1 eff2)
| T_Minus :
    forall gamma omega e1 e2 eff1 eff2,
      TcExp gamma omega e1 TyNat eff1 ->
      TcExp gamma omega e2 TyNat eff2 ->
      TcExp gamma omega (EMinus e1 e2) TyNat (static_union eff1 eff2)
| T_Times :
    forall gamma omega e1 e2 eff1 eff2,
      TcExp gamma omega e1 TyNat eff1 ->
      TcExp gamma omega e2 TyNat eff2 ->
      TcExp gamma omega (ETimes e1 e2) TyNat (static_union eff1 eff2)
| T_Eq :
    forall gamma omega e1 e2 eff1 eff2,
      TcExp gamma omega e1 TyNat eff1 ->
      TcExp gamma omega e2 TyNat eff2 ->
      TcExp gamma omega (EEq e1 e2) TyBool (static_union eff1 eff2)
| T_AllocAbs :
    forall gamma omega r,
      region_expr_wf omega r ->
      TcExp gamma omega (EAllocAbs r) TyEffect []
| T_ReadAbs :
    forall gamma omega r,
      region_expr_wf omega r ->
      TcExp gamma omega (EReadAbs r) TyEffect []
| T_WriteAbs :
    forall gamma omega r,
      region_expr_wf omega r ->
      TcExp gamma omega (EWriteAbs r) TyEffect []
| T_ReadConc :
    forall gamma omega e r ty eff,
      TcExp gamma omega e (TyRef r ty) eff ->
      TcExp gamma omega (EReadConc e) TyEffect eff
| T_WriteConc :
    forall gamma omega e r ty eff,
      TcExp gamma omega e (TyRef r ty) eff ->
      TcExp gamma omega (EWriteConc e) TyEffect eff
| T_Concat :
    forall gamma omega e1 e2 eff1 eff2,
      TcExp gamma omega e1 TyEffect eff1 ->
      TcExp gamma omega e2 TyEffect eff2 ->
      TcExp gamma omega (EConcat e1 e2) TyEffect
        (static_union eff1 eff2)
| T_Top :
    forall gamma omega,
      TcExp gamma omega ETop TyEffect []
| T_Empty :
    forall gamma omega,
      TcExp gamma omega EEmpty TyEffect [].

Lemma TcExp_EMuApp_static_heap_neutral_inv :
  forall gamma omega ef ea ty eff,
    TcExp gamma omega (EMuApp ef ea) ty eff ->
    static_heap_neutral eff ->
    exists ty_arg eff_body eff_summary eff_f eff_a,
      TcExp gamma omega ef
        (TyArrow ty_arg eff_body ty eff_summary) eff_f /\
      TcExp gamma omega ea ty_arg eff_a /\
      eff = static_union eff_f (static_union eff_a eff_body) /\
      static_heap_neutral eff_f /\
      static_heap_neutral eff_a /\
      static_heap_neutral eff_body.
Proof.
  intros gamma omega ef ea ty eff HTyped HNeutral.
  inversion HTyped; subst.
  exists ty_arg, eff_body, eff_summary, eff_f, eff_a.
  split; [assumption |].
  split; [assumption |].
  split; [reflexivity |].
  split.
  - eapply static_heap_neutral_app_l. exact HNeutral.
  - split.
    + eapply static_heap_neutral_app_l.
      eapply static_heap_neutral_app_r. exact HNeutral.
    + eapply static_heap_neutral_app_r.
      eapply static_heap_neutral_app_r. exact HNeutral.
Qed.

Lemma TcExp_EEffApp_static_heap_neutral_inv :
  forall gamma omega ef ea eff,
    TcExp gamma omega (EEffApp ef ea) TyEffect eff ->
    static_heap_neutral eff ->
    exists ty_arg ty_body eff_body eff_summary eff_f eff_a,
      TcExp gamma omega ef
        (TyArrow ty_arg eff_body ty_body eff_summary) eff_f /\
      TcExp gamma omega ea ty_arg eff_a /\
      eff = static_union eff_f (static_union eff_a eff_summary) /\
      static_heap_neutral eff_f /\
      static_heap_neutral eff_a /\
      static_heap_neutral eff_summary.
Proof.
  intros gamma omega ef ea eff HTyped HNeutral.
  inversion HTyped; subst.
  exists ty_arg, ty_body, eff_body, eff_summary, eff_f, eff_a.
  split; [assumption |].
  split; [assumption |].
  split; [reflexivity |].
  split.
  - eapply static_heap_neutral_app_l. exact HNeutral.
  - split.
    + eapply static_heap_neutral_app_l.
      eapply static_heap_neutral_app_r. exact HNeutral.
    + eapply static_heap_neutral_app_r.
      eapply static_heap_neutral_app_r. exact HNeutral.
Qed.
