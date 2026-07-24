From Stdlib Require Import List.
From Stdlib Require Import Bool.Bool.

Import ListNotations.

Definition RegionId := nat.
Definition Location := nat.

Inductive StaticAction :=
| SAlloc : RegionId -> StaticAction
| SRead : RegionId -> StaticAction
| SWrite : RegionId -> StaticAction.

Definition StaticEffect := list StaticAction.

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

Definition TraceDisjoint (phi1 phi2 : Trace) : Prop :=
  forall a1 a2,
    In a1 phi1 ->
    In a2 phi2 ->
    ~ dynamic_conflict a1 a2.

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

Definition ReadOnlyTrace (phi : Trace) : Prop :=
  forall r l,
    ~ In (DWrite r l) phi.

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
