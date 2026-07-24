From Stdlib Require Import List.

Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Typing.Judgments.
Require Import theories.NewSmallStep.Typing.Types.

Import ListNotations.

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
