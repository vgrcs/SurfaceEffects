From Stdlib Require Import List.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Ascii.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Program.Equality.
Require Export theories.Core.Regions.

Import ListNotations.

Definition VarId := RgnName.
Definition RegionId := RgnVal.
Definition Location := nat.
Definition RegionExpr := Region_in_Expr.
Definition RegionType := Region_in_Type.

Definition region_to_type {idx : bool * bool * bool}
    (rgn : Region idx) : RegionType :=
  match rgn with
  | Rgn_Const _ _ r => Rgn_Const true true r
  | Rgn_FVar _ _ x => Rgn_FVar true true x
  | Rgn_BVar _ _ n => Rgn_BVar true true n
  end.

Definition region_expr_to_type (rgn : RegionExpr) : RegionType :=
  region_to_type rgn.

Definition region_const_expr (r : RegionId) : RegionExpr :=
  Rgn_Const true false r.

Definition region_const_type (r : RegionId) : RegionType :=
  Rgn_Const true true r.

Definition region_var_expr (x : VarId) : RegionExpr :=
  Rgn_FVar true false x.

Inductive StaticAction :=
| SAlloc : RegionType -> StaticAction
| SRead : RegionType -> StaticAction
| SWrite : RegionType -> StaticAction.

Definition StaticEffect := list StaticAction.

Definition open_region_type_at
    (k : nat) (u : RegionType) (rgn : RegionType) : RegionType :=
  match rgn with
  | Rgn_Const _ _ r => Rgn_Const true true r
  | Rgn_FVar _ _ x => Rgn_FVar true true x
  | Rgn_BVar _ _ n =>
      if Nat.eqb n k then u else Rgn_BVar true true n
  end.

Definition open_static_action_at
    (k : nat) (u : RegionType) (action : StaticAction) : StaticAction :=
  match action with
  | SAlloc rgn => SAlloc (open_region_type_at k u rgn)
  | SRead rgn => SRead (open_region_type_at k u rgn)
  | SWrite rgn => SWrite (open_region_type_at k u rgn)
  end.

Definition open_static_effect_at
    (k : nat) (u : RegionType) (eff : StaticEffect) : StaticEffect :=
  List.map (open_static_action_at k u) eff.

Definition open_static_effect_type
    (u : RegionType) (eff : StaticEffect) : StaticEffect :=
  open_static_effect_at 0 u eff.

Definition open_static_effect
    (rgn : RegionExpr) (eff : StaticEffect) : StaticEffect :=
  open_static_effect_type (region_expr_to_type rgn) eff.

Definition close_region_type_at
    (k : nat) (x : VarId) (rgn : RegionType) : RegionType :=
  match rgn with
  | Rgn_Const _ _ r => Rgn_Const true true r
  | Rgn_FVar _ _ y =>
      if ascii_dec y x then Rgn_BVar true true k else Rgn_FVar true true y
  | Rgn_BVar _ _ n => Rgn_BVar true true n
  end.

Definition close_static_action_at
    (k : nat) (x : VarId) (action : StaticAction) : StaticAction :=
  match action with
  | SAlloc rgn => SAlloc (close_region_type_at k x rgn)
  | SRead rgn => SRead (close_region_type_at k x rgn)
  | SWrite rgn => SWrite (close_region_type_at k x rgn)
  end.

Definition close_static_effect_at
    (k : nat) (x : VarId) (eff : StaticEffect) : StaticEffect :=
  List.map (close_static_action_at k x) eff.

Definition close_static_effect
    (x : VarId) (eff : StaticEffect) : StaticEffect :=
  close_static_effect_at 0 x eff.

Inductive DynamicAction :=
| DAlloc : RegionId -> Location -> DynamicAction
| DRead : RegionId -> Location -> DynamicAction
| DWrite : RegionId -> Location -> DynamicAction.

Definition Trace := list DynamicAction.

Inductive ComputedAction :=
| CAllocAbs : RegionId -> ComputedAction
| CReadAbs : RegionId -> ComputedAction
| CWriteAbs : RegionId -> ComputedAction
| CAllocConc : RegionId -> Location -> ComputedAction
| CReadConc : RegionId -> Location -> ComputedAction
| CWriteConc : RegionId -> Location -> ComputedAction.

Inductive Summary :=
| SummaryTop : Summary
| SummarySet : list ComputedAction -> Summary.

Definition summary_union (theta1 theta2 : Summary) : Summary :=
  match theta1, theta2 with
  | SummaryTop, _ => SummaryTop
  | _, SummaryTop => SummaryTop
  | SummarySet xs, SummarySet ys => SummarySet (xs ++ ys)
  end.

Definition same_locationb
    (r1 : RegionId) (l1 : Location)
    (r2 : RegionId) (l2 : Location) : bool :=
  Nat.eqb r1 r2 && Nat.eqb l1 l2.

Definition computed_conflictb
    (ca1 ca2 : ComputedAction) : bool :=
  match ca1, ca2 with
  | CReadAbs r1, CWriteAbs r2 => Nat.eqb r1 r2
  | CReadAbs r1, CWriteConc r2 _ => Nat.eqb r1 r2
  | CReadConc r1 l1, CWriteAbs r2 => Nat.eqb r1 r2
  | CReadConc r1 l1, CWriteConc r2 l2 =>
      same_locationb r1 l1 r2 l2
  | CWriteAbs r1, CReadAbs r2 => Nat.eqb r1 r2
  | CWriteAbs r1, CReadConc r2 _ => Nat.eqb r1 r2
  | CWriteAbs r1, CWriteAbs r2 => Nat.eqb r1 r2
  | CWriteAbs r1, CWriteConc r2 _ => Nat.eqb r1 r2
  | CWriteConc r1 _, CReadAbs r2 => Nat.eqb r1 r2
  | CWriteConc r1 l1, CReadConc r2 l2 =>
      same_locationb r1 l1 r2 l2
  | CWriteConc r1 _, CWriteAbs r2 => Nat.eqb r1 r2
  | CWriteConc r1 l1, CWriteConc r2 l2 =>
      same_locationb r1 l1 r2 l2
  | _, _ => false
  end.

Fixpoint no_computed_conflicts_with
    (ca : ComputedAction) (acts : list ComputedAction) : bool :=
  match acts with
  | [] => true
  | ca' :: acts' =>
      negb (computed_conflictb ca ca') &&
      no_computed_conflicts_with ca acts'
  end.

Fixpoint computed_actions_disjointb
    (acts1 acts2 : list ComputedAction) : bool :=
  match acts1 with
  | [] => true
  | ca :: acts1' =>
      no_computed_conflicts_with ca acts2 &&
      computed_actions_disjointb acts1' acts2
  end.

Definition summary_disjointb (theta1 theta2 : Summary) : bool :=
  match theta1, theta2 with
  | SummarySet acts1, SummarySet acts2 =>
      computed_actions_disjointb acts1 acts2
  | _, _ => false
  end.

Definition SummaryDisjoint (theta1 theta2 : Summary) : Prop :=
  summary_disjointb theta1 theta2 = true.

Definition SummaryCheckFails (theta1 theta2 : Summary) : Prop :=
  summary_disjointb theta1 theta2 = false.

Definition same_location (r1 : RegionId) (l1 : Location)
    (r2 : RegionId) (l2 : Location) : Prop :=
  r1 = r2 /\ l1 = l2.

Inductive dynamic_conflict : DynamicAction -> DynamicAction -> Prop :=
| ConflictReadWrite :
    forall r1 l1 r2 l2,
      same_location r1 l1 r2 l2 ->
      dynamic_conflict (DRead r1 l1) (DWrite r2 l2)
| ConflictWriteRead :
    forall r1 l1 r2 l2,
      same_location r1 l1 r2 l2 ->
      dynamic_conflict (DWrite r1 l1) (DRead r2 l2)
| ConflictWriteWrite :
    forall r1 l1 r2 l2,
      same_location r1 l1 r2 l2 ->
      dynamic_conflict (DWrite r1 l1) (DWrite r2 l2).

Definition dynamic_conflictb
    (a1 a2 : DynamicAction) : bool :=
  match a1, a2 with
  | DRead r1 l1, DWrite r2 l2 =>
      same_locationb r1 l1 r2 l2
  | DWrite r1 l1, DRead r2 l2 =>
      same_locationb r1 l1 r2 l2
  | DWrite r1 l1, DWrite r2 l2 =>
      same_locationb r1 l1 r2 l2
  | _, _ => false
  end.

Fixpoint no_dynamic_conflicts_with
    (a : DynamicAction) (phi : Trace) : bool :=
  match phi with
  | [] => true
  | a' :: phi' =>
      negb (dynamic_conflictb a a') &&
      no_dynamic_conflicts_with a phi'
  end.

Fixpoint trace_disjointb (phi1 phi2 : Trace) : bool :=
  match phi1 with
  | [] => true
  | a :: phi1' =>
      no_dynamic_conflicts_with a phi2 &&
      trace_disjointb phi1' phi2
  end.

Definition TraceCheckPasses (phi1 phi2 : Trace) : Prop :=
  trace_disjointb phi1 phi2 = true.

Definition TraceCheckFails (phi1 phi2 : Trace) : Prop :=
  trace_disjointb phi1 phi2 = false.

Definition TraceDisjoint (phi1 phi2 : Trace) : Prop :=
  forall a1 a2,
    In a1 phi1 ->
    In a2 phi2 ->
    ~ dynamic_conflict a1 a2.

Lemma TraceDisjoint_app_l :
  forall phi1 phi2 phi3,
    TraceDisjoint (phi1 ++ phi2) phi3 ->
    TraceDisjoint phi1 phi3 /\ TraceDisjoint phi2 phi3.
Proof.
  intros phi1 phi2 phi3 HDisjoint.
  split; intros a1 a2 HIn1 HIn2;
    eapply HDisjoint; eauto; apply in_or_app;
    [left | right]; assumption.
Qed.

Lemma TraceDisjoint_app_r :
  forall phi1 phi2 phi3,
    TraceDisjoint phi1 (phi2 ++ phi3) ->
    TraceDisjoint phi1 phi2 /\ TraceDisjoint phi1 phi3.
Proof.
  intros phi1 phi2 phi3 HDisjoint.
  split; intros a1 a2 HIn1 HIn2;
    eapply HDisjoint; eauto; apply in_or_app;
    [left | right]; assumption.
Qed.

Lemma dynamic_conflictb_true_from_conflict :
  forall a1 a2,
    dynamic_conflict a1 a2 ->
    dynamic_conflictb a1 a2 = true.
Proof.
  intros a1 a2 HConflict.
  inversion HConflict; subst;
    match goal with
    | HSame : same_location _ _ _ _ |- _ =>
        destruct HSame as [-> ->]
    end;
    cbn [dynamic_conflictb];
    unfold same_locationb;
    repeat rewrite Nat.eqb_refl;
    reflexivity.
Qed.

Lemma dynamic_conflictb_false_no_conflict :
  forall a1 a2,
    dynamic_conflictb a1 a2 = false ->
    ~ dynamic_conflict a1 a2.
Proof.
  intros a1 a2 HFalse HConflict.
  pose proof
    (dynamic_conflictb_true_from_conflict a1 a2 HConflict)
    as HTrue.
  rewrite HFalse in HTrue.
  discriminate.
Qed.

Lemma no_dynamic_conflicts_with_true_no_conflict :
  forall a phi a',
    no_dynamic_conflicts_with a phi = true ->
    In a' phi ->
    ~ dynamic_conflict a a'.
Proof.
  intros a phi.
  induction phi as [| head phi IH]; intros a' HNo HIn.
  - contradiction.
  - simpl in HNo.
    apply andb_true_iff in HNo.
    destruct HNo as (HHead & HTail).
    apply negb_true_iff in HHead.
    destruct HIn as [HIn | HIn].
    + subst a'.
      apply dynamic_conflictb_false_no_conflict.
      exact HHead.
    + eapply IH; eauto.
Qed.

Lemma trace_disjointb_true_disjoint :
  forall phi1 phi2,
    trace_disjointb phi1 phi2 = true ->
    TraceDisjoint phi1 phi2.
Proof.
  intros phi1.
  induction phi1 as [| head phi1 IH]; intros phi2 HDisjoint.
  - intros a1 a2 HIn1 _.
    contradiction.
  - simpl in HDisjoint.
    apply andb_true_iff in HDisjoint.
    destruct HDisjoint as (HHead & HTail).
    intros a1 a2 HIn1 HIn2.
    destruct HIn1 as [HIn1 | HIn1].
    + subst a1.
      eapply no_dynamic_conflicts_with_true_no_conflict; eauto.
    + eapply IH; eauto.
Qed.

Inductive dynamic_action_covered :
    DynamicAction -> ComputedAction -> Prop :=
| CoverAllocAbs :
    forall r l,
      dynamic_action_covered (DAlloc r l) (CAllocAbs r)
| CoverReadAbs :
    forall r l,
      dynamic_action_covered (DRead r l) (CReadAbs r)
| CoverWriteAbs :
    forall r l,
      dynamic_action_covered (DWrite r l) (CWriteAbs r)
| CoverAllocConc :
    forall r l,
      dynamic_action_covered (DAlloc r l) (CAllocConc r l)
| CoverReadConc :
    forall r l,
      dynamic_action_covered (DRead r l) (CReadConc r l)
| CoverWriteConc :
    forall r l,
      dynamic_action_covered (DWrite r l) (CWriteConc r l).

Definition TraceCoveredBySummary (phi : Trace) (theta : Summary) : Prop :=
  match theta with
  | SummaryTop => True
  | SummarySet acts =>
      forall da,
        In da phi ->
        exists ca,
          In ca acts /\ dynamic_action_covered da ca
  end.

Lemma computed_conflictb_true_from_covered_dynamic_conflict :
  forall da1 da2 ca1 ca2,
    dynamic_action_covered da1 ca1 ->
    dynamic_action_covered da2 ca2 ->
    dynamic_conflict da1 da2 ->
    computed_conflictb ca1 ca2 = true.
Proof.
  intros da1 da2 ca1 ca2 HCovered1 HCovered2 HConflict.
  destruct HCovered1; destruct HCovered2; inversion HConflict; subst;
    match goal with
    | HSame : same_location _ _ _ _ |- _ =>
        destruct HSame as [-> ->]
    end;
    cbn [computed_conflictb];
    unfold same_locationb;
    repeat rewrite Nat.eqb_refl;
    reflexivity.
Qed.

Lemma no_computed_conflicts_with_true_no_conflict :
  forall ca acts ca',
    no_computed_conflicts_with ca acts = true ->
    In ca' acts ->
    computed_conflictb ca ca' = false.
Proof.
  intros ca acts.
  induction acts as [| head acts IH]; intros ca' HNo HIn.
  - contradiction.
  - simpl in HNo.
    apply andb_true_iff in HNo.
    destruct HNo as (HHead & HTail).
    apply negb_true_iff in HHead.
    destruct HIn as [HIn | HIn].
    + subst ca'. exact HHead.
    + eapply IH; eauto.
Qed.

Lemma computed_actions_disjointb_true_no_conflict :
  forall acts1 acts2 ca1 ca2,
    computed_actions_disjointb acts1 acts2 = true ->
    In ca1 acts1 ->
    In ca2 acts2 ->
    computed_conflictb ca1 ca2 = false.
Proof.
  intros acts1.
  induction acts1 as [| head acts1 IH];
    intros acts2 ca1 ca2 HDisjoint HIn1 HIn2.
  - contradiction.
  - simpl in HDisjoint.
    apply andb_true_iff in HDisjoint.
    destruct HDisjoint as (HHead & HTail).
    destruct HIn1 as [HIn1 | HIn1].
    + subst ca1.
      eapply no_computed_conflicts_with_true_no_conflict; eauto.
    + eapply IH; eauto.
Qed.

Lemma summary_disjoint_covered_trace_disjoint :
  forall phi1 phi2 theta1 theta2,
    summary_disjointb theta1 theta2 = true ->
    TraceCoveredBySummary phi1 theta1 ->
    TraceCoveredBySummary phi2 theta2 ->
    TraceDisjoint phi1 phi2.
Proof.
  intros phi1 phi2 theta1 theta2 HDisjoint HCovered1 HCovered2.
  destruct theta1 as [| acts1], theta2 as [| acts2];
    simpl in HDisjoint; try discriminate.
  intros da1 da2 HIn1 HIn2 HConflict.
  destruct (HCovered1 da1 HIn1) as (ca1 & HCa1 & HCover1).
  destruct (HCovered2 da2 HIn2) as (ca2 & HCa2 & HCover2).
  pose proof
    (computed_actions_disjointb_true_no_conflict
      acts1 acts2 ca1 ca2 HDisjoint HCa1 HCa2)
    as HComputedFalse.
  pose proof
    (computed_conflictb_true_from_covered_dynamic_conflict
      da1 da2 ca1 ca2 HCover1 HCover2 HConflict)
    as HComputedTrue.
  rewrite HComputedFalse in HComputedTrue.
  discriminate.
Qed.

Definition ReadOnlyTrace (phi : Trace) : Prop :=
  forall r l,
    ~ In (DWrite r l) phi.

Definition TraceDoesNotWrite (r : RegionId) (l : Location)
    (phi : Trace) : Prop :=
  ~ In (DWrite r l) phi.

Definition NoAllocTrace (phi : Trace) : Prop :=
  forall r l,
    ~ In (DAlloc r l) phi.

Definition HeapNeutralTrace (phi : Trace) : Prop :=
  NoAllocTrace phi /\ ReadOnlyTrace phi.

Lemma no_alloc_trace_nil :
  NoAllocTrace [].
Proof.
  intros r l HIn.
  inversion HIn.
Qed.

Lemma read_only_trace_nil :
  ReadOnlyTrace [].
Proof.
  intros r l HIn.
  inversion HIn.
Qed.

Lemma trace_does_not_write_nil :
  forall r l,
    TraceDoesNotWrite r l [].
Proof.
  intros r l HIn.
  inversion HIn.
Qed.

Lemma heap_neutral_trace_nil :
  HeapNeutralTrace [].
Proof.
  split.
  - apply no_alloc_trace_nil.
  - apply read_only_trace_nil.
Qed.

Lemma no_alloc_trace_app :
  forall phi1 phi2,
    NoAllocTrace phi1 ->
    NoAllocTrace phi2 ->
    NoAllocTrace (phi1 ++ phi2).
Proof.
  intros phi1 phi2 HNoAlloc1 HNoAlloc2 r l HIn.
  apply in_app_or in HIn.
  destruct HIn as [HIn | HIn].
  - eapply HNoAlloc1; eauto.
  - eapply HNoAlloc2; eauto.
Qed.

Lemma no_alloc_trace_app_l :
  forall phi1 phi2,
    NoAllocTrace (phi1 ++ phi2) ->
    NoAllocTrace phi1.
Proof.
  intros phi1 phi2 HNoAlloc r l HIn.
  eapply HNoAlloc.
  apply in_or_app.
  left. exact HIn.
Qed.

Lemma no_alloc_trace_app_r :
  forall phi1 phi2,
    NoAllocTrace (phi1 ++ phi2) ->
    NoAllocTrace phi2.
Proof.
  intros phi1 phi2 HNoAlloc r l HIn.
  eapply HNoAlloc.
  apply in_or_app.
  right. exact HIn.
Qed.

Lemma read_only_trace_app :
  forall phi1 phi2,
    ReadOnlyTrace phi1 ->
    ReadOnlyTrace phi2 ->
    ReadOnlyTrace (phi1 ++ phi2).
Proof.
  intros phi1 phi2 HReadOnly1 HReadOnly2 r l HIn.
  apply in_app_or in HIn.
  destruct HIn as [HIn | HIn].
  - eapply HReadOnly1; eauto.
  - eapply HReadOnly2; eauto.
Qed.

Lemma read_only_trace_app_l :
  forall phi1 phi2,
    ReadOnlyTrace (phi1 ++ phi2) ->
    ReadOnlyTrace phi1.
Proof.
  intros phi1 phi2 HReadOnly r l HIn.
  eapply HReadOnly.
  apply in_or_app.
  left. exact HIn.
Qed.

Lemma read_only_trace_app_r :
  forall phi1 phi2,
    ReadOnlyTrace (phi1 ++ phi2) ->
    ReadOnlyTrace phi2.
Proof.
  intros phi1 phi2 HReadOnly r l HIn.
  eapply HReadOnly.
  apply in_or_app.
  right. exact HIn.
Qed.

Lemma trace_does_not_write_app :
  forall r l phi1 phi2,
    TraceDoesNotWrite r l phi1 ->
    TraceDoesNotWrite r l phi2 ->
    TraceDoesNotWrite r l (phi1 ++ phi2).
Proof.
  intros r l phi1 phi2 HNoWrite1 HNoWrite2 HIn.
  apply in_app_or in HIn.
  destruct HIn as [HIn | HIn].
  - eapply HNoWrite1; eauto.
  - eapply HNoWrite2; eauto.
Qed.

Lemma trace_does_not_write_app_l :
  forall r l phi1 phi2,
    TraceDoesNotWrite r l (phi1 ++ phi2) ->
    TraceDoesNotWrite r l phi1.
Proof.
  intros r l phi1 phi2 HNoWrite HIn.
  eapply HNoWrite.
  apply in_or_app.
  left. exact HIn.
Qed.

Lemma trace_does_not_write_app_r :
  forall r l phi1 phi2,
    TraceDoesNotWrite r l (phi1 ++ phi2) ->
    TraceDoesNotWrite r l phi2.
Proof.
  intros r l phi1 phi2 HNoWrite HIn.
  eapply HNoWrite.
  apply in_or_app.
  right. exact HIn.
Qed.

Lemma TraceDisjoint_right_read_no_left_write :
  forall phi_left phi_right r l,
    TraceDisjoint phi_left phi_right ->
    In (DRead r l) phi_right ->
    TraceDoesNotWrite r l phi_left.
Proof.
  intros phi_left phi_right r l HDisjoint HRead HWrite.
  eapply HDisjoint; eauto.
  constructor.
  split; reflexivity.
Qed.

Lemma heap_neutral_trace_app :
  forall phi1 phi2,
    HeapNeutralTrace phi1 ->
    HeapNeutralTrace phi2 ->
    HeapNeutralTrace (phi1 ++ phi2).
Proof.
  intros phi1 phi2 [HNoAlloc1 HReadOnly1] [HNoAlloc2 HReadOnly2].
  split.
  - eapply no_alloc_trace_app; eauto.
  - eapply read_only_trace_app; eauto.
Qed.

Lemma heap_neutral_trace_app_l :
  forall phi1 phi2,
    HeapNeutralTrace (phi1 ++ phi2) ->
    HeapNeutralTrace phi1.
Proof.
  intros phi1 phi2 [HNoAlloc HReadOnly].
  split.
  - eapply no_alloc_trace_app_l; eauto.
  - eapply read_only_trace_app_l; eauto.
Qed.

Lemma heap_neutral_trace_app_r :
  forall phi1 phi2,
    HeapNeutralTrace (phi1 ++ phi2) ->
    HeapNeutralTrace phi2.
Proof.
  intros phi1 phi2 [HNoAlloc HReadOnly].
  split.
  - eapply no_alloc_trace_app_r; eauto.
  - eapply read_only_trace_app_r; eauto.
Qed.

Lemma trace_covered_top :
  forall phi,
    TraceCoveredBySummary phi SummaryTop.
Proof.
  intros phi. exact I.
Qed.

Lemma trace_covered_nil :
  forall theta,
    TraceCoveredBySummary [] theta.
Proof.
  intros [| acts]; simpl; auto.
  intros da HIn. contradiction.
Qed.

Lemma trace_covered_empty_summary_nil :
  forall phi,
    TraceCoveredBySummary phi (SummarySet []) ->
    phi = [].
Proof.
  intros phi HCovered.
  destruct phi as [| da phi].
  - reflexivity.
  - exfalso.
    destruct (HCovered da (or_introl eq_refl)) as
      (ca & HIn & _).
    inversion HIn.
Qed.

Lemma trace_covered_app_same :
  forall phi1 phi2 theta,
    TraceCoveredBySummary phi1 theta ->
    TraceCoveredBySummary phi2 theta ->
    TraceCoveredBySummary (phi1 ++ phi2) theta.
Proof.
  intros phi1 phi2 [| acts] HCovered1 HCovered2; simpl in *; auto.
  intros da HIn.
  apply in_app_or in HIn.
  destruct HIn as [HIn | HIn].
  - apply HCovered1. assumption.
  - apply HCovered2. assumption.
Qed.

Lemma trace_covered_summary_union_l :
  forall phi theta1 theta2,
    TraceCoveredBySummary phi theta1 ->
    TraceCoveredBySummary phi (summary_union theta1 theta2).
Proof.
  intros phi theta1 theta2 HCovered.
  destruct theta1 as [| xs], theta2 as [| ys]; simpl in *; auto.
  intros da HIn.
  destruct (HCovered da HIn) as (ca & HCaIn & HCover).
  exists ca. split; [apply in_or_app; left |]; assumption.
Qed.

Lemma trace_covered_summary_union_r :
  forall phi theta1 theta2,
    TraceCoveredBySummary phi theta2 ->
    TraceCoveredBySummary phi (summary_union theta1 theta2).
Proof.
  intros phi theta1 theta2 HCovered.
  destruct theta1 as [| xs], theta2 as [| ys]; simpl in *; auto.
  intros da HIn.
  destruct (HCovered da HIn) as (ca & HCaIn & HCover).
  exists ca. split; [apply in_or_app; right |]; assumption.
Qed.

Lemma trace_covered_app_summary_union :
  forall phi1 phi2 theta1 theta2,
    TraceCoveredBySummary phi1 theta1 ->
    TraceCoveredBySummary phi2 theta2 ->
    TraceCoveredBySummary (phi1 ++ phi2) (summary_union theta1 theta2).
Proof.
  intros phi1 phi2 theta1 theta2 HCovered1 HCovered2.
  apply trace_covered_app_same.
  - apply trace_covered_summary_union_l. assumption.
  - apply trace_covered_summary_union_r. assumption.
Qed.
