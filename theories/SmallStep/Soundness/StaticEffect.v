From Stdlib Require Import List.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Typing.Judgments.
Require Import theories.SmallStep.Typing.Resolve.

Import ListNotations.

Inductive DynamicActionCoveredByStatic :
    DynamicAction -> StaticAction -> Prop :=
| DACBS_Alloc :
    forall r l,
      DynamicActionCoveredByStatic
        (DAlloc r l)
        (SAlloc (region_const_type r))
| DACBS_Read :
    forall r l,
      DynamicActionCoveredByStatic
        (DRead r l)
        (SRead (region_const_type r))
| DACBS_Write :
    forall r l,
      DynamicActionCoveredByStatic
        (DWrite r l)
        (SWrite (region_const_type r)).

Definition TraceCoveredByStaticEffect
    (phi : Trace) (eff : StaticEffect) : Prop :=
  forall da,
    In da phi ->
    exists sa,
      In sa eff /\ DynamicActionCoveredByStatic da sa.

Definition dynamic_action_static_action (da : DynamicAction) : StaticAction :=
  match da with
  | DAlloc r _ => SAlloc (region_const_type r)
  | DRead r _ => SRead (region_const_type r)
  | DWrite r _ => SWrite (region_const_type r)
  end.

Definition dynamic_action_static_effect (da : DynamicAction) : StaticEffect :=
  [dynamic_action_static_action da].

Fixpoint trace_static_effect (phi : Trace) : StaticEffect :=
  match phi with
  | [] => []
  | da :: phi' =>
      static_union (dynamic_action_static_effect da)
        (trace_static_effect phi')
  end.

Definition label_static_effect (label : NLabel) : StaticEffect :=
  match label with
  | LSilent => []
  | LAction da => dynamic_action_static_effect da
  end.

Definition StaticEffectIncluded (eff1 eff2 : StaticEffect) : Prop :=
  forall sa,
    In sa eff1 ->
    In sa eff2.

Lemma StaticEffectIncluded_refl :
  forall eff,
    StaticEffectIncluded eff eff.
Proof.
  unfold StaticEffectIncluded.
  auto.
Qed.

Lemma StaticEffectIncluded_trans :
  forall eff1 eff2 eff3,
    StaticEffectIncluded eff1 eff2 ->
    StaticEffectIncluded eff2 eff3 ->
    StaticEffectIncluded eff1 eff3.
Proof.
  unfold StaticEffectIncluded.
  eauto.
Qed.

Lemma StaticEffectIncluded_nil_l :
  forall eff,
    StaticEffectIncluded [] eff.
Proof.
  unfold StaticEffectIncluded.
  intros eff sa HIn.
  contradiction.
Qed.

Lemma StaticEffectIncluded_app_l :
  forall eff1 eff2,
    StaticEffectIncluded eff1 (static_union eff1 eff2).
Proof.
  unfold StaticEffectIncluded, static_union.
  intros eff1 eff2 sa HIn.
  apply in_or_app.
  left. exact HIn.
Qed.

Lemma StaticEffectIncluded_app_r :
  forall eff1 eff2,
    StaticEffectIncluded eff2 (static_union eff1 eff2).
Proof.
  unfold StaticEffectIncluded, static_union.
  intros eff1 eff2 sa HIn.
  apply in_or_app.
  right. exact HIn.
Qed.

Lemma StaticEffectIncluded_app_comm :
  forall eff1 eff2,
    StaticEffectIncluded
      (static_union eff1 eff2)
      (static_union eff2 eff1).
Proof.
  unfold StaticEffectIncluded, static_union.
  intros eff1 eff2 sa HIn.
  apply in_app_or in HIn.
  apply in_or_app.
  destruct HIn as [HIn | HIn].
  - right. exact HIn.
  - left. exact HIn.
Qed.

Lemma StaticEffectIncluded_app_assoc_lr :
  forall eff1 eff2 eff3,
    StaticEffectIncluded
      (static_union (static_union eff1 eff2) eff3)
      (static_union eff1 (static_union eff2 eff3)).
Proof.
  unfold StaticEffectIncluded, static_union.
  intros eff1 eff2 eff3 sa HIn.
  repeat rewrite in_app_iff in *.
  destruct HIn as [[HIn | HIn] | HIn]; auto.
Qed.

Lemma StaticEffectIncluded_app_assoc_rl :
  forall eff1 eff2 eff3,
    StaticEffectIncluded
      (static_union eff1 (static_union eff2 eff3))
      (static_union (static_union eff1 eff2) eff3).
Proof.
  unfold StaticEffectIncluded, static_union.
  intros eff1 eff2 eff3 sa HIn.
  repeat rewrite in_app_iff in *.
  destruct HIn as [HIn | [HIn | HIn]]; auto.
Qed.

Lemma StaticEffectIncluded_app_singleton_front :
  forall eff action,
    StaticEffectIncluded
      (static_union eff [action])
      (action :: eff).
Proof.
  unfold StaticEffectIncluded, static_union.
  intros eff action sa HIn.
  rewrite in_app_iff in HIn.
  simpl.
  destruct HIn as [HIn | [HIn | HIn]].
  - right. exact HIn.
  - left. exact HIn.
  - contradiction.
Qed.

Lemma StaticEffectIncluded_app3_singleton_front :
  forall eff1 eff2 action,
    StaticEffectIncluded
      (static_union eff1 (static_union eff2 [action]))
      (action :: static_union eff1 eff2).
Proof.
  unfold StaticEffectIncluded, static_union.
  intros eff1 eff2 action sa HIn.
  repeat rewrite in_app_iff in HIn.
  simpl.
  destruct HIn as [HIn | [HIn | HIn]].
  - right. apply in_or_app. left. exact HIn.
  - right. apply in_or_app. right. exact HIn.
  - destruct HIn as [HIn | HIn].
    + left. exact HIn.
    + contradiction.
Qed.

Lemma StaticEffectIncluded_app :
  forall eff1 eff1' eff2 eff2',
    StaticEffectIncluded eff1 eff1' ->
    StaticEffectIncluded eff2 eff2' ->
    StaticEffectIncluded
      (static_union eff1 eff2)
      (static_union eff1' eff2').
Proof.
  unfold StaticEffectIncluded, static_union.
  intros eff1 eff1' eff2 eff2' HIncl1 HIncl2 sa HIn.
  apply in_app_or in HIn.
  destruct HIn as [HIn | HIn].
  - apply in_or_app. left. apply HIncl1. exact HIn.
  - apply in_or_app. right. apply HIncl2. exact HIn.
Qed.

Lemma StaticEffectIncluded_join :
  forall eff1 eff2 eff,
    StaticEffectIncluded eff1 eff ->
    StaticEffectIncluded eff2 eff ->
    StaticEffectIncluded (static_union eff1 eff2) eff.
Proof.
  unfold StaticEffectIncluded, static_union.
  intros eff1 eff2 eff HIncl1 HIncl2 sa HIn.
  apply in_app_or in HIn.
  destruct HIn as [HIn | HIn].
  - apply HIncl1. exact HIn.
  - apply HIncl2. exact HIn.
Qed.

Lemma trace_static_effect_app :
  forall phi1 phi2,
    trace_static_effect (phi1 ++ phi2) =
    static_union (trace_static_effect phi1) (trace_static_effect phi2).
Proof.
  induction phi1 as [| da phi1 IH]; intros phi2; simpl.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma trace_static_effect_app_included :
  forall phi1 phi2 eff1 eff2,
    StaticEffectIncluded (trace_static_effect phi1) eff1 ->
    StaticEffectIncluded (trace_static_effect phi2) eff2 ->
    StaticEffectIncluded
      (trace_static_effect (phi1 ++ phi2))
      (static_union eff1 eff2).
Proof.
  intros phi1 phi2 eff1 eff2 HIncl1 HIncl2.
  rewrite trace_static_effect_app.
  apply StaticEffectIncluded_app; assumption.
Qed.

Lemma trace_static_effect_app3_included :
  forall phi1 phi2 phi3 eff1 eff2 eff3,
    StaticEffectIncluded (trace_static_effect phi1) eff1 ->
    StaticEffectIncluded (trace_static_effect phi2) eff2 ->
    StaticEffectIncluded (trace_static_effect phi3) eff3 ->
    StaticEffectIncluded
      (trace_static_effect (phi1 ++ phi2 ++ phi3))
      (static_union eff1 (static_union eff2 eff3)).
Proof.
  intros phi1 phi2 phi3 eff1 eff2 eff3 HIncl1 HIncl2 HIncl3.
  rewrite trace_static_effect_app.
  apply StaticEffectIncluded_app.
  - exact HIncl1.
  - rewrite trace_static_effect_app.
    apply StaticEffectIncluded_app; assumption.
Qed.

Lemma label_static_effect_trace_static_effect :
  forall label,
    label_static_effect label = trace_static_effect (label_trace label).
Proof.
  intros [| da]; reflexivity.
Qed.

Lemma dynamic_action_static_action_covers :
  forall da,
    DynamicActionCoveredByStatic da (dynamic_action_static_action da).
Proof.
  intros [r l | r l | r l]; constructor.
Qed.

Lemma TraceCoveredByStaticEffect_nil :
  forall eff,
    TraceCoveredByStaticEffect [] eff.
Proof.
  unfold TraceCoveredByStaticEffect.
  intros eff da HIn.
  contradiction.
Qed.

Lemma TraceCoveredByStaticEffect_singleton :
  forall da,
    TraceCoveredByStaticEffect
      [da]
      (dynamic_action_static_effect da).
Proof.
  unfold TraceCoveredByStaticEffect, dynamic_action_static_effect.
  intros da da' HIn.
  simpl in HIn.
  destruct HIn as [HIn | HIn].
  - subst da'.
    exists (dynamic_action_static_action da).
    split.
    + simpl. left. reflexivity.
    + apply dynamic_action_static_action_covers.
  - contradiction.
Qed.

Lemma TraceCoveredByStaticEffect_label :
  forall label,
    TraceCoveredByStaticEffect
      (label_trace label)
      (label_static_effect label).
Proof.
  intros [| da]; simpl.
  - apply TraceCoveredByStaticEffect_nil.
  - apply TraceCoveredByStaticEffect_singleton.
Qed.

Lemma TraceCoveredByStaticEffect_trace_static_effect :
  forall phi,
    TraceCoveredByStaticEffect phi (trace_static_effect phi).
Proof.
  unfold TraceCoveredByStaticEffect.
  induction phi as [| da phi IH]; simpl.
  - intros da HIn. contradiction.
  - intros da' HIn.
    destruct HIn as [HHead | HTail].
    + subst da'.
      exists (dynamic_action_static_action da).
      split.
      * simpl. left. reflexivity.
      * apply dynamic_action_static_action_covers.
    + destruct (IH da' HTail) as (sa & HSaIn & HCover).
      exists sa.
      split.
      * simpl. right. exact HSaIn.
      * exact HCover.
Qed.

Lemma TraceCoveredByStaticEffect_weaken :
  forall phi eff eff',
    TraceCoveredByStaticEffect phi eff ->
    StaticEffectIncluded eff eff' ->
    TraceCoveredByStaticEffect phi eff'.
Proof.
  unfold TraceCoveredByStaticEffect.
  intros phi eff eff' HCovered HIncl da HIn.
  destruct (HCovered da HIn) as (sa & HSaIn & HCover).
  exists sa.
  split; [apply HIncl |]; assumption.
Qed.

Lemma TraceCoveredByStaticEffect_app :
  forall phi1 phi2 eff1 eff2,
    TraceCoveredByStaticEffect phi1 eff1 ->
    TraceCoveredByStaticEffect phi2 eff2 ->
    TraceCoveredByStaticEffect (phi1 ++ phi2) (static_union eff1 eff2).
Proof.
  unfold TraceCoveredByStaticEffect, static_union.
  intros phi1 phi2 eff1 eff2 HCovered1 HCovered2 da HIn.
  apply in_app_or in HIn.
  destruct HIn as [HIn | HIn].
  - destruct (HCovered1 da HIn) as (sa & HSaIn & HCover).
    exists sa.
    split; [apply in_or_app; left |]; assumption.
  - destruct (HCovered2 da HIn) as (sa & HSaIn & HCover).
    exists sa.
    split; [apply in_or_app; right |]; assumption.
Qed.

Lemma TraceCoveredByStaticEffect_app3 :
  forall phi1 phi2 phi3 eff1 eff2 eff3,
    TraceCoveredByStaticEffect phi1 eff1 ->
    TraceCoveredByStaticEffect phi2 eff2 ->
    TraceCoveredByStaticEffect phi3 eff3 ->
    TraceCoveredByStaticEffect
      (phi1 ++ phi2 ++ phi3)
      (static_union eff1 (static_union eff2 eff3)).
Proof.
  intros phi1 phi2 phi3 eff1 eff2 eff3 H1 H2 H3.
  replace (phi1 ++ phi2 ++ phi3)
    with (phi1 ++ (phi2 ++ phi3))
    by reflexivity.
  apply TraceCoveredByStaticEffect_app.
  - exact H1.
  - apply TraceCoveredByStaticEffect_app; assumption.
Qed.

Lemma TraceCoveredByStaticEffect_app4 :
  forall phi1 phi2 phi3 phi4 eff1 eff2 eff3 eff4,
    TraceCoveredByStaticEffect phi1 eff1 ->
    TraceCoveredByStaticEffect phi2 eff2 ->
    TraceCoveredByStaticEffect phi3 eff3 ->
    TraceCoveredByStaticEffect phi4 eff4 ->
    TraceCoveredByStaticEffect
      (phi1 ++ phi2 ++ phi3 ++ phi4)
      (static_union (static_union eff1 eff2)
        (static_union eff3 eff4)).
Proof.
  intros phi1 phi2 phi3 phi4 eff1 eff2 eff3 eff4 H1 H2 H3 H4.
  replace (phi1 ++ phi2 ++ phi3 ++ phi4)
    with ((phi1 ++ phi2) ++ (phi3 ++ phi4)).
  - apply TraceCoveredByStaticEffect_app;
      apply TraceCoveredByStaticEffect_app; assumption.
  - repeat rewrite app_assoc.
    reflexivity.
Qed.

Lemma TraceCoveredByStaticEffect_app_l :
  forall phi1 phi2 eff,
    TraceCoveredByStaticEffect (phi1 ++ phi2) eff ->
    TraceCoveredByStaticEffect phi1 eff.
Proof.
  unfold TraceCoveredByStaticEffect.
  intros phi1 phi2 eff HCovered da HIn.
  apply HCovered.
  apply in_or_app.
  left. exact HIn.
Qed.

Lemma TraceCoveredByStaticEffect_app_r :
  forall phi1 phi2 eff,
    TraceCoveredByStaticEffect (phi1 ++ phi2) eff ->
    TraceCoveredByStaticEffect phi2 eff.
Proof.
  unfold TraceCoveredByStaticEffect.
  intros phi1 phi2 eff HCovered da HIn.
  apply HCovered.
  apply in_or_app.
  right. exact HIn.
Qed.

Lemma TraceCoveredByStaticEffect_no_alloc :
  forall phi eff,
    TraceCoveredByStaticEffect phi eff ->
    static_noalloc eff ->
    NoAllocTrace phi.
Proof.
  unfold TraceCoveredByStaticEffect, static_noalloc, NoAllocTrace.
  intros phi eff HCovered HNoAlloc r l HIn.
  destruct (HCovered (DAlloc r l) HIn) as (sa & HSaIn & HCover).
  inversion HCover; subst.
  eapply HNoAlloc; eauto.
Qed.

Lemma TraceCoveredByStaticEffect_read_only :
  forall phi eff,
    TraceCoveredByStaticEffect phi eff ->
    static_readonly eff ->
    ReadOnlyTrace phi.
Proof.
  unfold TraceCoveredByStaticEffect, static_readonly, ReadOnlyTrace.
  intros phi eff HCovered HReadOnly r l HIn.
  destruct (HCovered (DWrite r l) HIn) as (sa & HSaIn & HCover).
  inversion HCover; subst.
  eapply HReadOnly; eauto.
Qed.

Theorem TraceCoveredByStaticEffect_heap_neutral :
  forall phi eff,
    TraceCoveredByStaticEffect phi eff ->
    static_heap_neutral eff ->
    HeapNeutralTrace phi.
Proof.
  intros phi eff HCovered [HNoAlloc HReadOnly].
  split.
  - eapply TraceCoveredByStaticEffect_no_alloc; eauto.
  - eapply TraceCoveredByStaticEffect_read_only; eauto.
Qed.

Theorem TraceStaticEffect_heap_neutral :
  forall phi,
    static_heap_neutral (trace_static_effect phi) ->
    HeapNeutralTrace phi.
Proof.
  intros phi HNeutral.
  eapply TraceCoveredByStaticEffect_heap_neutral; eauto.
  apply TraceCoveredByStaticEffect_trace_static_effect.
Qed.

Theorem TraceStaticEffect_included_heap_neutral :
  forall phi eff,
    StaticEffectIncluded (trace_static_effect phi) eff ->
    static_heap_neutral eff ->
    HeapNeutralTrace phi.
Proof.
  intros phi eff HIncl HNeutral.
  eapply TraceCoveredByStaticEffect_heap_neutral.
  - eapply TraceCoveredByStaticEffect_weaken.
    + apply TraceCoveredByStaticEffect_trace_static_effect.
    + exact HIncl.
  - exact HNeutral.
Qed.

Theorem TraceCoveredByResolvedStaticEffect_heap_neutral :
  forall rho phi eff eff_res,
    NResolveStaticEffect rho eff eff_res ->
    TraceCoveredByStaticEffect phi eff_res ->
    static_heap_neutral eff ->
    HeapNeutralTrace phi.
Proof.
  intros rho phi eff eff_res HResolve HCovered HNeutral.
  eapply TraceCoveredByStaticEffect_heap_neutral; eauto.
  eapply NResolveStaticEffect_static_heap_neutral; eauto.
Qed.
