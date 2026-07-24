From Stdlib Require Import List.

Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Typing.Judgments.
Require Import theories.NewSmallStep.Typing.Types.

Import ListNotations.

Inductive NBackTriangle : NCtx -> NRgnCtx -> NExpr -> NExpr -> Prop :=
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

Theorem NBackTriangle_typing :
  forall gamma omega e summary,
    NBackTriangle gamma omega e summary ->
    exists ty eff eff_summary,
      NTcExp gamma omega e ty eff /\
      NTcExp gamma omega summary TyEffect eff_summary.
Proof.
  intros gamma omega e summary HBack.
  induction HBack.
  - exists TyNat, [], []. split; assumption || constructor.
  - exists TyBool, [], []. split; assumption || constructor.
  - exists ty, [], []. split; assumption || constructor.
  - exists ty, eff, []. split; assumption || constructor.
  - exists ty, eff, []. split; assumption || constructor.
  - exists ty_mu, eff_mu, eff_eff. split; assumption.
  - exists ty_app, eff_app, []. split; assumption || constructor.
  - destruct IHHBack2 as (ty_eff_t & static_eff_t & summary_eff_t & _ & HTypedT).
    destruct IHHBack3 as (ty_eff_f & static_eff_f & summary_eff_f & _ & HTypedF).
    exists ty, (static_union eff_e (static_union eff_et eff_ef)),
      (static_union eff_e (static_union summary_eff_t summary_eff_f)).
    split.
    + assumption.
    + eapply NT_Cond; eauto.
  - destruct IHHBack as
      (ty_eff & static_eff & summary_eff & _ & HTypedSummary).
    exists ty_ref, eff_ref, (static_union summary_eff []).
    split.
    + assumption.
    + eapply NT_Concat.
      * exact HTypedSummary.
      * eapply NT_AllocAbs.
        match goal with
        | HRef : NTcExp gamma omega (ERef r e) _ _ |- _ =>
            inversion HRef; subst; assumption
        end.
  - destruct IHHBack as
      (ty_eff & static_eff & summary_eff & _ & HTypedSummary).
    exists ty_deref, eff_deref, (static_union summary_eff []).
    split.
    + assumption.
    + eapply NT_Concat.
      * exact HTypedSummary.
      * eapply NT_ReadAbs.
        match goal with
        | HDeref : NTcExp gamma omega (EDeref r e) _ _ |- _ =>
            inversion HDeref; subst; assumption
        end.
  - destruct IHHBack1 as
      (ty_eff1 & static_eff1 & summary_eff1 & _ & HTypedSummary1).
    destruct IHHBack2 as
      (ty_eff2 & static_eff2 & summary_eff2 & _ & HTypedSummary2).
    exists ty_assign, eff_assign,
      (static_union summary_eff1 (static_union summary_eff2 [])).
    split.
    + assumption.
    + eapply NT_Concat; eauto.
      eapply NT_Concat.
      * exact HTypedSummary2.
      * eapply NT_WriteAbs.
        match goal with
        | HAssign : NTcExp gamma omega (EAssign r e1 e2) _ _ |- _ =>
            inversion HAssign; subst; assumption
        end.
  - destruct IHHBack1 as
      (ty_eff1 & static_eff1 & summary_eff1 & _ & HTypedSummary1).
    destruct IHHBack2 as
      (ty_eff2 & static_eff2 & summary_eff2 & _ & HTypedSummary2).
    exists TyNat, eff_static, (static_union summary_eff1 summary_eff2).
    split.
    + assumption.
    + eapply NT_Concat; eauto.
  - destruct IHHBack1 as
      (ty_eff1 & static_eff1 & summary_eff1 & _ & HTypedSummary1).
    destruct IHHBack2 as
      (ty_eff2 & static_eff2 & summary_eff2 & _ & HTypedSummary2).
    exists TyNat, eff_static, (static_union summary_eff1 summary_eff2).
    split.
    + assumption.
    + eapply NT_Concat; eauto.
  - destruct IHHBack1 as
      (ty_eff1 & static_eff1 & summary_eff1 & _ & HTypedSummary1).
    destruct IHHBack2 as
      (ty_eff2 & static_eff2 & summary_eff2 & _ & HTypedSummary2).
    exists TyNat, eff_static, (static_union summary_eff1 summary_eff2).
    split.
    + assumption.
    + eapply NT_Concat; eauto.
  - destruct IHHBack1 as
      (ty_eff1 & static_eff1 & summary_eff1 & _ & HTypedSummary1).
    destruct IHHBack2 as
      (ty_eff2 & static_eff2 & summary_eff2 & _ & HTypedSummary2).
    exists TyBool, eff_static, (static_union summary_eff1 summary_eff2).
    split.
    + assumption.
    + eapply NT_Concat; eauto.
  - exists ty, eff, []. split; assumption || constructor.
Qed.
