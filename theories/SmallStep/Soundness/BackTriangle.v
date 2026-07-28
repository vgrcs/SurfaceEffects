From Stdlib Require Import List.

Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Typing.Judgments.
Require Import theories.SmallStep.Typing.Regularity.
Require Import theories.SmallStep.Typing.Resolve.
Require Import theories.SmallStep.Typing.Types.

Import ListNotations.

Lemma NStaticEffectWF_static_union :
  forall omega eff1 eff2,
    NStaticEffectWF omega eff1 ->
    NStaticEffectWF omega eff2 ->
    NStaticEffectWF omega (static_union eff1 eff2).
Proof.
  intros omega eff1 eff2 HWF1 HWF2.
  unfold NStaticEffectWF, static_union in *.
  apply Forall_app. split; assumption.
Qed.

Lemma NCheckedTcExp_empty_from :
  forall gamma omega e ty eff,
    NCheckedTcExp gamma omega e ty eff ->
    NCheckedTcExp gamma omega EEmpty TyEffect [].
Proof.
  intros gamma omega e ty eff HChecked.
  eapply NCheckedTcExp_intro.
  - constructor.
  - eapply NCheckedTcExp_rgn_ctx_wf; eauto.
  - eapply NCheckedTcExp_ctx_wf; eauto.
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma NCheckedTcExp_top_from :
  forall gamma omega e ty eff,
    NCheckedTcExp gamma omega e ty eff ->
    NCheckedTcExp gamma omega ETop TyEffect [].
Proof.
  intros gamma omega e ty eff HChecked.
  eapply NCheckedTcExp_intro.
  - constructor.
  - eapply NCheckedTcExp_rgn_ctx_wf; eauto.
  - eapply NCheckedTcExp_ctx_wf; eauto.
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma NCheckedTcExp_concat :
  forall gamma omega e1 e2 eff1 eff2,
    NCheckedTcExp gamma omega e1 TyEffect eff1 ->
    NCheckedTcExp gamma omega e2 TyEffect eff2 ->
    NCheckedTcExp gamma omega
      (EConcat e1 e2) TyEffect (static_union eff1 eff2).
Proof.
  intros gamma omega e1 e2 eff1 eff2 HChecked1 HChecked2.
  eapply NCheckedTcExp_intro.
  - eapply NT_Concat; eauto using NCheckedTcExp_to_NTcExp.
  - eapply NCheckedTcExp_rgn_ctx_wf; eauto.
  - eapply NCheckedTcExp_ctx_wf; eauto.
  - constructor.
  - eapply NStaticEffectWF_static_union;
      eapply NCheckedTcExp_eff_wf; eauto.
  - econstructor; eauto.
Qed.

Lemma NCheckedTcExp_cond_effect :
  forall gamma omega e et ef eff_e eff_t eff_f,
    NCheckedTcExp gamma omega e TyBool eff_e ->
    NCheckedTcExp gamma omega et TyEffect eff_t ->
    NCheckedTcExp gamma omega ef TyEffect eff_f ->
    NCheckedTcExp gamma omega
      (ECond e et ef) TyEffect
      (static_union eff_e (static_union eff_t eff_f)).
Proof.
  intros gamma omega e et ef eff_e eff_t eff_f
    HChecked HCheckedT HCheckedF.
  eapply NCheckedTcExp_intro.
  - eapply NT_Cond; eauto using NCheckedTcExp_to_NTcExp.
  - eapply NCheckedTcExp_rgn_ctx_wf; eauto.
  - eapply NCheckedTcExp_ctx_wf; eauto.
  - constructor.
  - eapply NStaticEffectWF_static_union.
    + eapply NCheckedTcExp_eff_wf; eauto.
    + eapply NStaticEffectWF_static_union;
        eapply NCheckedTcExp_eff_wf; eauto.
  - econstructor; eauto.
Qed.

Lemma NCheckedTcExp_alloc_abs_from_ref :
  forall gamma omega r e ty eff,
    NCheckedTcExp gamma omega (ERef r e) ty eff ->
    NCheckedTcExp gamma omega (EAllocAbs r) TyEffect [].
Proof.
  intros gamma omega r e ty eff HChecked.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HShape; subst.
  eapply NCheckedTcExp_intro.
  - constructor; assumption.
  - eapply NCheckedTcExp_rgn_ctx_wf; eauto.
  - eapply NCheckedTcExp_ctx_wf; eauto.
  - constructor.
  - constructor.
  - constructor; assumption.
Qed.

Lemma NCheckedTcExp_read_abs_from_deref :
  forall gamma omega r e ty eff,
    NCheckedTcExp gamma omega (EDeref r e) ty eff ->
    NCheckedTcExp gamma omega (EReadAbs r) TyEffect [].
Proof.
  intros gamma omega r e ty eff HChecked.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HShape; subst.
  eapply NCheckedTcExp_intro.
  - constructor; assumption.
  - eapply NCheckedTcExp_rgn_ctx_wf; eauto.
  - eapply NCheckedTcExp_ctx_wf; eauto.
  - constructor.
  - constructor.
  - constructor; assumption.
Qed.

Lemma NCheckedTcExp_write_abs_from_assign :
  forall gamma omega r e1 e2 ty eff,
    NCheckedTcExp gamma omega (EAssign r e1 e2) ty eff ->
    NCheckedTcExp gamma omega (EWriteAbs r) TyEffect [].
Proof.
  intros gamma omega r e1 e2 ty eff HChecked.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HShape; subst.
  eapply NCheckedTcExp_intro.
  - constructor; assumption.
  - eapply NCheckedTcExp_rgn_ctx_wf; eauto.
  - eapply NCheckedTcExp_ctx_wf; eauto.
  - constructor.
  - constructor.
  - constructor; assumption.
Qed.

Lemma NCheckedTcExp_pair_par :
  forall gamma omega ef1 ea1 ef2 ea2 ty1 ty2 eff1 eff2
    eff_summary1 eff_summary2,
    NCheckedTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 ->
    NCheckedTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
    NCheckedTcExp gamma omega (EEffApp ef1 ea1) TyEffect
      eff_summary1 ->
    NCheckedTcExp gamma omega (EEffApp ef2 ea2) TyEffect
      eff_summary2 ->
    static_noalloc eff1 ->
    static_noalloc eff2 ->
    NCheckedTcExp gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (TyPair ty1 ty2)
      (static_union (static_union eff_summary1 eff_summary2)
        (static_union eff1 eff2)).
Proof.
  intros gamma omega ef1 ea1 ef2 ea2 ty1 ty2 eff1 eff2
    eff_summary1 eff_summary2 HMu1 HMu2 HSummary1 HSummary2
    HNoAlloc1 HNoAlloc2.
  eapply NCheckedTcExp_intro.
  - eapply NT_PairPar; eauto using NCheckedTcExp_to_NTcExp.
  - eapply NCheckedTcExp_rgn_ctx_wf; eauto.
  - eapply NCheckedTcExp_ctx_wf; eauto.
  - constructor;
      eapply NCheckedTcExp_ty_wf; eauto.
  - eapply NStaticEffectWF_static_union.
    + eapply NStaticEffectWF_static_union;
        eapply NCheckedTcExp_eff_wf; eauto.
    + eapply NStaticEffectWF_static_union;
        eapply NCheckedTcExp_eff_wf; eauto.
  - econstructor; eauto.
Qed.

Theorem NCheckedBackTriangle_typing :
  forall gamma omega e summary,
    NCheckedBackTriangle gamma omega e summary ->
    exists ty eff eff_summary,
      NCheckedTcExp gamma omega e ty eff /\
      NCheckedTcExp gamma omega summary TyEffect eff_summary.
Proof.
  intros gamma omega e summary HBack.
  induction HBack.
  - exists TyNat, [], []. split.
    + assumption.
    + eapply NCheckedTcExp_empty_from; eauto.
  - exists TyBool, [], []. split.
    + assumption.
    + eapply NCheckedTcExp_empty_from; eauto.
  - exists ty, [], []. split.
    + assumption.
    + eapply NCheckedTcExp_empty_from; eauto.
  - exists ty, eff, []. split.
    + assumption.
    + eapply NCheckedTcExp_empty_from; eauto.
  - exists ty, eff, []. split.
    + assumption.
    + eapply NCheckedTcExp_empty_from; eauto.
  - exists ty_mu, eff_mu, eff_eff. split; assumption.
  - exists (TyPair ty1 ty2),
      (static_union (static_union eff_summary1 eff_summary2)
        (static_union eff1 eff2)),
      (static_union eff_summary1 eff_summary2).
    split.
    + eapply NCheckedTcExp_pair_par; eauto; assumption.
    + eapply NCheckedTcExp_concat; eauto.
  - exists ty_app, eff_app, []. split.
    + assumption.
    + eapply NCheckedTcExp_empty_from; eauto.
  - destruct IHHBack2 as
      (ty_eff_t & static_eff_t & summary_eff_t & _ & HCheckedT).
    destruct IHHBack3 as
      (ty_eff_f & static_eff_f & summary_eff_f & _ & HCheckedF).
    exists ty, (static_union eff_e (static_union eff_et eff_ef)),
      (static_union eff_e (static_union summary_eff_t summary_eff_f)).
    split.
    + assumption.
    + eapply NCheckedTcExp_cond_effect; eauto.
  - destruct IHHBack as
      (ty_eff & static_eff & summary_eff & _ & HCheckedSummary).
    exists ty_ref, eff_ref, (static_union summary_eff []).
    split.
    + assumption.
    + eapply NCheckedTcExp_concat.
      * exact HCheckedSummary.
      * eapply NCheckedTcExp_alloc_abs_from_ref; eauto.
  - destruct IHHBack as
      (ty_eff & static_eff & summary_eff & _ & HCheckedSummary).
    exists ty_deref, eff_deref, (static_union summary_eff []).
    split.
    + assumption.
    + eapply NCheckedTcExp_concat.
      * exact HCheckedSummary.
      * eapply NCheckedTcExp_read_abs_from_deref; eauto.
  - destruct IHHBack1 as
      (ty_eff1 & static_eff1 & summary_eff1 & _ & HCheckedSummary1).
    destruct IHHBack2 as
      (ty_eff2 & static_eff2 & summary_eff2 & _ & HCheckedSummary2).
    exists ty_assign, eff_assign,
      (static_union summary_eff1 (static_union summary_eff2 [])).
    split.
    + assumption.
    + eapply NCheckedTcExp_concat.
      * exact HCheckedSummary1.
      * eapply NCheckedTcExp_concat.
        -- exact HCheckedSummary2.
        -- eapply NCheckedTcExp_write_abs_from_assign; eauto.
  - destruct IHHBack1 as
      (ty_eff1 & static_eff1 & summary_eff1 & _ & HCheckedSummary1).
    destruct IHHBack2 as
      (ty_eff2 & static_eff2 & summary_eff2 & _ & HCheckedSummary2).
    exists TyNat, eff_static, (static_union summary_eff1 summary_eff2).
    split.
    + assumption.
    + eapply NCheckedTcExp_concat; eauto.
  - destruct IHHBack1 as
      (ty_eff1 & static_eff1 & summary_eff1 & _ & HCheckedSummary1).
    destruct IHHBack2 as
      (ty_eff2 & static_eff2 & summary_eff2 & _ & HCheckedSummary2).
    exists TyNat, eff_static, (static_union summary_eff1 summary_eff2).
    split.
    + assumption.
    + eapply NCheckedTcExp_concat; eauto.
  - destruct IHHBack1 as
      (ty_eff1 & static_eff1 & summary_eff1 & _ & HCheckedSummary1).
    destruct IHHBack2 as
      (ty_eff2 & static_eff2 & summary_eff2 & _ & HCheckedSummary2).
    exists TyNat, eff_static, (static_union summary_eff1 summary_eff2).
    split.
    + assumption.
    + eapply NCheckedTcExp_concat; eauto.
  - destruct IHHBack1 as
      (ty_eff1 & static_eff1 & summary_eff1 & _ & HCheckedSummary1).
    destruct IHHBack2 as
      (ty_eff2 & static_eff2 & summary_eff2 & _ & HCheckedSummary2).
    exists TyBool, eff_static, (static_union summary_eff1 summary_eff2).
    split.
    + assumption.
    + eapply NCheckedTcExp_concat; eauto.
	  - exists ty, eff, []. split.
	    + assumption.
	    + eapply NCheckedTcExp_top_from; eauto.
Qed.

Theorem NCheckedBackTriangle_summary_checked_heap_neutral :
  forall gamma omega e summary,
    NCheckedBackTriangle gamma omega e summary ->
    exists eff_summary,
      NCheckedTcExp gamma omega summary TyEffect eff_summary /\
      static_heap_neutral eff_summary.
Proof.
  intros gamma omega e summary HBack.
  induction HBack.
  - exists []. split; eauto using
      NCheckedTcExp_empty_from, static_heap_neutral_nil.
  - exists []. split; eauto using
      NCheckedTcExp_empty_from, static_heap_neutral_nil.
  - exists []. split; eauto using
      NCheckedTcExp_empty_from, static_heap_neutral_nil.
  - exists []. split; eauto using
      NCheckedTcExp_empty_from, static_heap_neutral_nil.
  - exists []. split; eauto using
      NCheckedTcExp_empty_from, static_heap_neutral_nil.
  - exists eff_eff. split; assumption.
  - exists (static_union eff_summary1 eff_summary2).
    split.
    + eapply NCheckedTcExp_concat; eauto.
    + eapply static_heap_neutral_app; eauto.
  - exists []. split; eauto using
      NCheckedTcExp_empty_from, static_heap_neutral_nil.
  - destruct IHHBack2 as (eff_summary_t & HCheckedT & HNeutralT).
    destruct IHHBack3 as (eff_summary_f & HCheckedF & HNeutralF).
    exists (static_union eff_e (static_union eff_summary_t eff_summary_f)).
    split.
    + eapply NCheckedTcExp_cond_effect; eauto.
    + eapply static_heap_neutral_app; eauto.
      eapply static_heap_neutral_app; eauto.
  - destruct IHHBack as (eff_summary & HCheckedSummary & HNeutralSummary).
    exists (static_union eff_summary []).
    split.
    + eapply NCheckedTcExp_concat.
      * exact HCheckedSummary.
      * eapply NCheckedTcExp_alloc_abs_from_ref; eauto.
    + eapply static_heap_neutral_app; eauto using static_heap_neutral_nil.
  - destruct IHHBack as (eff_summary & HCheckedSummary & HNeutralSummary).
    exists (static_union eff_summary []).
    split.
    + eapply NCheckedTcExp_concat.
      * exact HCheckedSummary.
      * eapply NCheckedTcExp_read_abs_from_deref; eauto.
    + eapply static_heap_neutral_app; eauto using static_heap_neutral_nil.
  - destruct IHHBack1 as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
    destruct IHHBack2 as (eff_summary2 & HCheckedSummary2 & HNeutralSummary2).
    exists (static_union eff_summary1 (static_union eff_summary2 [])).
    split.
    + eapply NCheckedTcExp_concat.
      * exact HCheckedSummary1.
      * eapply NCheckedTcExp_concat.
        -- exact HCheckedSummary2.
        -- eapply NCheckedTcExp_write_abs_from_assign; eauto.
    + eapply static_heap_neutral_app; eauto.
      eapply static_heap_neutral_app; eauto using static_heap_neutral_nil.
  - destruct IHHBack1 as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
    destruct IHHBack2 as (eff_summary2 & HCheckedSummary2 & HNeutralSummary2).
    exists (static_union eff_summary1 eff_summary2).
    split.
    + eapply NCheckedTcExp_concat; eauto.
    + eapply static_heap_neutral_app; eauto.
  - destruct IHHBack1 as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
    destruct IHHBack2 as (eff_summary2 & HCheckedSummary2 & HNeutralSummary2).
    exists (static_union eff_summary1 eff_summary2).
    split.
    + eapply NCheckedTcExp_concat; eauto.
    + eapply static_heap_neutral_app; eauto.
  - destruct IHHBack1 as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
    destruct IHHBack2 as (eff_summary2 & HCheckedSummary2 & HNeutralSummary2).
    exists (static_union eff_summary1 eff_summary2).
    split.
    + eapply NCheckedTcExp_concat; eauto.
    + eapply static_heap_neutral_app; eauto.
  - destruct IHHBack1 as (eff_summary1 & HCheckedSummary1 & HNeutralSummary1).
    destruct IHHBack2 as (eff_summary2 & HCheckedSummary2 & HNeutralSummary2).
    exists (static_union eff_summary1 eff_summary2).
    split.
    + eapply NCheckedTcExp_concat; eauto.
    + eapply static_heap_neutral_app; eauto.
  - exists []. split; eauto using
      NCheckedTcExp_top_from, static_heap_neutral_nil.
Qed.
