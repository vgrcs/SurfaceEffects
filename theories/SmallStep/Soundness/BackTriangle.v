From Stdlib Require Import List.

Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Typing.Judgments.
Require Import theories.SmallStep.Typing.Regularity.
Require Import theories.SmallStep.Typing.Resolve.
Require Import theories.SmallStep.Typing.Types.

Import ListNotations.

Lemma StaticEffectWF_static_union :
  forall omega eff1 eff2,
    StaticEffectWF omega eff1 ->
    StaticEffectWF omega eff2 ->
    StaticEffectWF omega (static_union eff1 eff2).
Proof.
  intros omega eff1 eff2 HWF1 HWF2.
  unfold StaticEffectWF, static_union in *.
  apply Forall_app. split; assumption.
Qed.

Lemma CheckedTcExp_empty_from :
  forall gamma omega e ty eff,
    CheckedTcExp gamma omega e ty eff ->
    CheckedTcExp gamma omega EEmpty TyEffect [].
Proof.
  intros gamma omega e ty eff HChecked.
  eapply CheckedTcExp_intro.
  - constructor.
  - eapply CheckedTcExp_rgn_ctx_wf; eauto.
  - eapply CheckedTcExp_ctx_wf; eauto.
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma CheckedTcExp_top_from :
  forall gamma omega e ty eff,
    CheckedTcExp gamma omega e ty eff ->
    CheckedTcExp gamma omega ETop TyEffect [].
Proof.
  intros gamma omega e ty eff HChecked.
  eapply CheckedTcExp_intro.
  - constructor.
  - eapply CheckedTcExp_rgn_ctx_wf; eauto.
  - eapply CheckedTcExp_ctx_wf; eauto.
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma CheckedTcExp_concat :
  forall gamma omega e1 e2 eff1 eff2,
    CheckedTcExp gamma omega e1 TyEffect eff1 ->
    CheckedTcExp gamma omega e2 TyEffect eff2 ->
    CheckedTcExp gamma omega
      (EConcat e1 e2) TyEffect (static_union eff1 eff2).
Proof.
  intros gamma omega e1 e2 eff1 eff2 HChecked1 HChecked2.
  eapply CheckedTcExp_intro.
  - eapply T_Concat; eauto using CheckedTcExp_to_TcExp.
  - eapply CheckedTcExp_rgn_ctx_wf; eauto.
  - eapply CheckedTcExp_ctx_wf; eauto.
  - constructor.
  - eapply StaticEffectWF_static_union;
      eapply CheckedTcExp_eff_wf; eauto.
  - econstructor; eauto.
Qed.

Lemma CheckedTcExp_cond_effect :
  forall gamma omega e et ef eff_e eff_t eff_f,
    CheckedTcExp gamma omega e TyBool eff_e ->
    CheckedTcExp gamma omega et TyEffect eff_t ->
    CheckedTcExp gamma omega ef TyEffect eff_f ->
    CheckedTcExp gamma omega
      (ECond e et ef) TyEffect
      (static_union eff_e (static_union eff_t eff_f)).
Proof.
  intros gamma omega e et ef eff_e eff_t eff_f
    HChecked HCheckedT HCheckedF.
  eapply CheckedTcExp_intro.
  - eapply T_Cond; eauto using CheckedTcExp_to_TcExp.
  - eapply CheckedTcExp_rgn_ctx_wf; eauto.
  - eapply CheckedTcExp_ctx_wf; eauto.
  - constructor.
  - eapply StaticEffectWF_static_union.
    + eapply CheckedTcExp_eff_wf; eauto.
    + eapply StaticEffectWF_static_union;
        eapply CheckedTcExp_eff_wf; eauto.
  - econstructor; eauto.
Qed.

Lemma CheckedTcExp_alloc_abs_from_ref :
  forall gamma omega r e ty eff,
    CheckedTcExp gamma omega (ERef r e) ty eff ->
    CheckedTcExp gamma omega (EAllocAbs r) TyEffect [].
Proof.
  intros gamma omega r e ty eff HChecked.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HShape; subst.
  eapply CheckedTcExp_intro.
  - constructor; assumption.
  - eapply CheckedTcExp_rgn_ctx_wf; eauto.
  - eapply CheckedTcExp_ctx_wf; eauto.
  - constructor.
  - constructor.
  - constructor; assumption.
Qed.

Lemma CheckedTcExp_read_abs_from_deref :
  forall gamma omega r e ty eff,
    CheckedTcExp gamma omega (EDeref r e) ty eff ->
    CheckedTcExp gamma omega (EReadAbs r) TyEffect [].
Proof.
  intros gamma omega r e ty eff HChecked.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HShape; subst.
  eapply CheckedTcExp_intro.
  - constructor; assumption.
  - eapply CheckedTcExp_rgn_ctx_wf; eauto.
  - eapply CheckedTcExp_ctx_wf; eauto.
  - constructor.
  - constructor.
  - constructor; assumption.
Qed.

Lemma CheckedTcExp_write_abs_from_assign :
  forall gamma omega r e1 e2 ty eff,
    CheckedTcExp gamma omega (EAssign r e1 e2) ty eff ->
    CheckedTcExp gamma omega (EWriteAbs r) TyEffect [].
Proof.
  intros gamma omega r e1 e2 ty eff HChecked.
  pose proof (CheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HShape; subst.
  eapply CheckedTcExp_intro.
  - constructor; assumption.
  - eapply CheckedTcExp_rgn_ctx_wf; eauto.
  - eapply CheckedTcExp_ctx_wf; eauto.
  - constructor.
  - constructor.
  - constructor; assumption.
Qed.

Lemma CheckedTcExp_pair_par :
  forall gamma omega ef1 ea1 ef2 ea2 ty1 ty2 eff1 eff2
    eff_summary1 eff_summary2,
    CheckedTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 ->
    CheckedTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
    CheckedTcExp gamma omega (EEffApp ef1 ea1) TyEffect
      eff_summary1 ->
    CheckedTcExp gamma omega (EEffApp ef2 ea2) TyEffect
      eff_summary2 ->
    static_noalloc eff1 ->
    static_noalloc eff2 ->
    CheckedTcExp gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (TyPair ty1 ty2)
      (static_union (static_union eff_summary1 eff_summary2)
        (static_union eff1 eff2)).
Proof.
  intros gamma omega ef1 ea1 ef2 ea2 ty1 ty2 eff1 eff2
    eff_summary1 eff_summary2 HMu1 HMu2 HSummary1 HSummary2
    HNoAlloc1 HNoAlloc2.
  eapply CheckedTcExp_intro.
  - eapply T_PairPar; eauto using CheckedTcExp_to_TcExp.
  - eapply CheckedTcExp_rgn_ctx_wf; eauto.
  - eapply CheckedTcExp_ctx_wf; eauto.
  - constructor;
      eapply CheckedTcExp_ty_wf; eauto.
  - eapply StaticEffectWF_static_union.
    + eapply StaticEffectWF_static_union;
        eapply CheckedTcExp_eff_wf; eauto.
    + eapply StaticEffectWF_static_union;
        eapply CheckedTcExp_eff_wf; eauto.
  - econstructor; eauto.
Qed.

Theorem CheckedBackTriangle_typing :
  forall gamma omega e summary,
    CheckedBackTriangle gamma omega e summary ->
    exists ty eff eff_summary,
      CheckedTcExp gamma omega e ty eff /\
      CheckedTcExp gamma omega summary TyEffect eff_summary.
Proof.
  intros gamma omega e summary HBack.
  induction HBack.
  - exists TyNat, [], []. split.
    + assumption.
    + eapply CheckedTcExp_empty_from; eauto.
  - exists TyBool, [], []. split.
    + assumption.
    + eapply CheckedTcExp_empty_from; eauto.
  - exists ty, [], []. split.
    + assumption.
    + eapply CheckedTcExp_empty_from; eauto.
  - exists ty, eff, []. split.
    + assumption.
    + eapply CheckedTcExp_empty_from; eauto.
  - exists ty, eff, []. split.
    + assumption.
    + eapply CheckedTcExp_empty_from; eauto.
  - exists ty_mu, eff_mu, eff_eff. split; assumption.
  - exists (TyPair ty1 ty2),
      (static_union (static_union eff_summary1 eff_summary2)
        (static_union eff1 eff2)),
      (static_union eff_summary1 eff_summary2).
    split.
    + eapply CheckedTcExp_pair_par; eauto; assumption.
    + eapply CheckedTcExp_concat; eauto.
  - exists ty_app, eff_app, []. split.
    + assumption.
    + eapply CheckedTcExp_empty_from; eauto.
  - destruct IHHBack2 as
      (ty_eff_t & static_eff_t & summary_eff_t & _ & HCheckedT).
    destruct IHHBack3 as
      (ty_eff_f & static_eff_f & summary_eff_f & _ & HCheckedF).
    exists ty, (static_union eff_e (static_union eff_et eff_ef)),
      (static_union eff_e (static_union summary_eff_t summary_eff_f)).
    split.
    + assumption.
    + eapply CheckedTcExp_cond_effect; eauto.
  - destruct IHHBack as
      (ty_eff & static_eff & summary_eff & _ & HCheckedSummary).
    exists ty_ref, eff_ref, (static_union summary_eff []).
    split.
    + assumption.
    + eapply CheckedTcExp_concat.
      * exact HCheckedSummary.
      * eapply CheckedTcExp_alloc_abs_from_ref; eauto.
  - destruct IHHBack as
      (ty_eff & static_eff & summary_eff & _ & HCheckedSummary).
    exists ty_deref, eff_deref, (static_union summary_eff []).
    split.
    + assumption.
    + eapply CheckedTcExp_concat.
      * exact HCheckedSummary.
      * eapply CheckedTcExp_read_abs_from_deref; eauto.
  - destruct IHHBack1 as
      (ty_eff1 & static_eff1 & summary_eff1 & _ & HCheckedSummary1).
    destruct IHHBack2 as
      (ty_eff2 & static_eff2 & summary_eff2 & _ & HCheckedSummary2).
    exists ty_assign, eff_assign,
      (static_union summary_eff1 (static_union summary_eff2 [])).
    split.
    + assumption.
    + eapply CheckedTcExp_concat.
      * exact HCheckedSummary1.
      * eapply CheckedTcExp_concat.
        -- exact HCheckedSummary2.
        -- eapply CheckedTcExp_write_abs_from_assign; eauto.
  - destruct IHHBack1 as
      (ty_eff1 & static_eff1 & summary_eff1 & _ & HCheckedSummary1).
    destruct IHHBack2 as
      (ty_eff2 & static_eff2 & summary_eff2 & _ & HCheckedSummary2).
    exists TyNat, eff_static, (static_union summary_eff1 summary_eff2).
    split.
    + assumption.
    + eapply CheckedTcExp_concat; eauto.
  - destruct IHHBack1 as
      (ty_eff1 & static_eff1 & summary_eff1 & _ & HCheckedSummary1).
    destruct IHHBack2 as
      (ty_eff2 & static_eff2 & summary_eff2 & _ & HCheckedSummary2).
    exists TyNat, eff_static, (static_union summary_eff1 summary_eff2).
    split.
    + assumption.
    + eapply CheckedTcExp_concat; eauto.
  - destruct IHHBack1 as
      (ty_eff1 & static_eff1 & summary_eff1 & _ & HCheckedSummary1).
    destruct IHHBack2 as
      (ty_eff2 & static_eff2 & summary_eff2 & _ & HCheckedSummary2).
    exists TyNat, eff_static, (static_union summary_eff1 summary_eff2).
    split.
    + assumption.
    + eapply CheckedTcExp_concat; eauto.
  - destruct IHHBack1 as
      (ty_eff1 & static_eff1 & summary_eff1 & _ & HCheckedSummary1).
    destruct IHHBack2 as
      (ty_eff2 & static_eff2 & summary_eff2 & _ & HCheckedSummary2).
    exists TyBool, eff_static, (static_union summary_eff1 summary_eff2).
    split.
    + assumption.
    + eapply CheckedTcExp_concat; eauto.
	  - exists ty, eff, []. split.
	    + assumption.
	    + eapply CheckedTcExp_top_from; eauto.
Qed.

Theorem CheckedBackTriangle_summary_checked_heap_neutral :
  forall gamma omega e summary,
    CheckedBackTriangle gamma omega e summary ->
    exists eff_summary,
      CheckedTcExp gamma omega summary TyEffect eff_summary /\
      static_heap_neutral eff_summary.
Proof.
  intros gamma omega e summary HBack.
  induction HBack.
  - exists []. split; eauto using
      CheckedTcExp_empty_from, static_heap_neutral_nil.
  - exists []. split; eauto using
      CheckedTcExp_empty_from, static_heap_neutral_nil.
  - exists []. split; eauto using
      CheckedTcExp_empty_from, static_heap_neutral_nil.
  - exists []. split; eauto using
      CheckedTcExp_empty_from, static_heap_neutral_nil.
  - exists []. split; eauto using
      CheckedTcExp_empty_from, static_heap_neutral_nil.
  - exists eff_eff. split; assumption.
  - exists (static_union eff_summary1 eff_summary2).
    split.
    + eapply CheckedTcExp_concat; eauto.
    + eapply static_heap_neutral_app; eauto.
  - exists []. split; eauto using
      CheckedTcExp_empty_from, static_heap_neutral_nil.
  - destruct IHHBack2 as (eff_summary_t & HCheckedT & HNeutralT).
    destruct IHHBack3 as (eff_summary_f & HCheckedF & HNeutralF).
    exists (static_union eff_e (static_union eff_summary_t eff_summary_f)).
    split.
    + eapply CheckedTcExp_cond_effect; eauto.
    + eapply static_heap_neutral_app; eauto.
      eapply static_heap_neutral_app; eauto.
  - destruct IHHBack as (eff_summary & HCheckedSummary & HNeutralSummary).
    exists (static_union eff_summary []).
    split.
    + eapply CheckedTcExp_concat.
      * exact HCheckedSummary.
      * eapply CheckedTcExp_alloc_abs_from_ref; eauto.
    + eapply static_heap_neutral_app; eauto using static_heap_neutral_nil.
  - destruct IHHBack as (eff_summary & HCheckedSummary & HNeutralSummary).
    exists (static_union eff_summary []).
    split.
    + eapply CheckedTcExp_concat.
      * exact HCheckedSummary.
      * eapply CheckedTcExp_read_abs_from_deref; eauto.
    + eapply static_heap_neutral_app; eauto using static_heap_neutral_nil.
  - destruct IHHBack1 as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
    destruct IHHBack2 as (eff_summary2 & HCheckedSummary2 & HNeutralSummary2).
    exists (static_union eff_summary1 (static_union eff_summary2 [])).
    split.
    + eapply CheckedTcExp_concat.
      * exact HCheckedSummary1.
      * eapply CheckedTcExp_concat.
        -- exact HCheckedSummary2.
        -- eapply CheckedTcExp_write_abs_from_assign; eauto.
    + eapply static_heap_neutral_app; eauto.
      eapply static_heap_neutral_app; eauto using static_heap_neutral_nil.
  - destruct IHHBack1 as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
    destruct IHHBack2 as (eff_summary2 & HCheckedSummary2 & HNeutralSummary2).
    exists (static_union eff_summary1 eff_summary2).
    split.
    + eapply CheckedTcExp_concat; eauto.
    + eapply static_heap_neutral_app; eauto.
  - destruct IHHBack1 as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
    destruct IHHBack2 as (eff_summary2 & HCheckedSummary2 & HNeutralSummary2).
    exists (static_union eff_summary1 eff_summary2).
    split.
    + eapply CheckedTcExp_concat; eauto.
    + eapply static_heap_neutral_app; eauto.
  - destruct IHHBack1 as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
    destruct IHHBack2 as (eff_summary2 & HCheckedSummary2 & HNeutralSummary2).
    exists (static_union eff_summary1 eff_summary2).
    split.
    + eapply CheckedTcExp_concat; eauto.
    + eapply static_heap_neutral_app; eauto.
  - destruct IHHBack1 as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
    destruct IHHBack2 as (eff_summary2 & HCheckedSummary2 & HNeutralSummary2).
    exists (static_union eff_summary1 eff_summary2).
    split.
    + eapply CheckedTcExp_concat; eauto.
    + eapply static_heap_neutral_app; eauto.
  - exists []. split; eauto using
      CheckedTcExp_top_from, static_heap_neutral_nil.
Qed.
