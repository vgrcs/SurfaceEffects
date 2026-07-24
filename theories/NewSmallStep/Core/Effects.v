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

Definition subst_region_type
    (x : VarId) (replacement : RegionExpr) (rgn : RegionType) : RegionType :=
  match rgn with
  | Rgn_Const _ _ r => Rgn_Const true true r
  | Rgn_FVar _ _ y =>
      if ascii_dec x y
      then region_expr_to_type replacement
      else Rgn_FVar true true y
  | Rgn_BVar _ _ n => Rgn_BVar true true n
  end.

Definition subst_static_action
    (x : VarId) (replacement : RegionExpr)
    (action : StaticAction) : StaticAction :=
  match action with
  | SAlloc rgn => SAlloc (subst_region_type x replacement rgn)
  | SRead rgn => SRead (subst_region_type x replacement rgn)
  | SWrite rgn => SWrite (subst_region_type x replacement rgn)
  end.

Definition subst_static_effect
    (x : VarId) (replacement : RegionExpr)
    (eff : StaticEffect) : StaticEffect :=
  List.map (subst_static_action x replacement) eff.

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
