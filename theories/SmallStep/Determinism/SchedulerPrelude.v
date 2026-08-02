From Stdlib Require Import List.
From stdpp Require Import list.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Core.Values.
Require Import theories.SmallStep.Runtime.HeapFacts.
Require Import theories.SmallStep.Runtime.HeapNeutral.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Runtime.Trace.
Require Import theories.SmallStep.Runtime.TraceView.
Require Import theories.SmallStep.Determinism.Terminal.

Import ListNotations.

(** Common trace-view and heap-footprint facts used by the scheduler proofs.
    The scheduler files keep trace views as their public representation and use
    flattening only at this boundary. *)

Definition StateNotError (state : State) : Prop :=
  match state with
  | StError _ => False
  | _ => True
  end.

Definition TracePermutation (phi1 phi2 : Trace) : Prop :=
  phi1 ≡ₚ phi2.

Definition NoAllocTraceView (view : TraceView) : Prop :=
  NoAllocTrace (trace_view_flatten view).

Definition HeapNeutralTraceView (view : TraceView) : Prop :=
  HeapNeutralTrace (trace_view_flatten view).

Definition HeapFootprint : Type :=
  RegionId -> Location -> Prop.

Definition HeapEqOn
    (footprint : HeapFootprint) (heap1 heap2 : Heap) : Prop :=
  forall r l,
    footprint r l ->
    heap_lookup r l heap1 = heap_lookup r l heap2.

Definition TraceReads (phi : Trace) : HeapFootprint :=
  fun r l => In (DRead r l) phi.

Definition TraceWrites (phi : Trace) : HeapFootprint :=
  fun r l => In (DWrite r l) phi.

Definition TraceTouches (phi : Trace) : HeapFootprint :=
  fun r l =>
    In (DAlloc r l) phi \/
    In (DRead r l) phi \/
    In (DWrite r l) phi.

Definition HeapEqOnTrace (phi : Trace) : Heap -> Heap -> Prop :=
  HeapEqOn (TraceTouches phi).

Definition HeapEqOnTraceView
    (view : TraceView) : Heap -> Heap -> Prop :=
  HeapEqOnTrace (trace_view_flatten view).

Lemma HeapEqOn_refl :
  forall footprint heap,
    HeapEqOn footprint heap heap.
Proof.
  intros footprint heap r l _HIn.
  reflexivity.
Qed.

Lemma HeapEqOn_sym :
  forall footprint heap1 heap2,
    HeapEqOn footprint heap1 heap2 ->
    HeapEqOn footprint heap2 heap1.
Proof.
  intros footprint heap1 heap2 HEq r l HIn.
  symmetry.
  apply HEq.
  exact HIn.
Qed.

Lemma HeapEqOn_trans :
  forall footprint heap1 heap2 heap3,
    HeapEqOn footprint heap1 heap2 ->
    HeapEqOn footprint heap2 heap3 ->
    HeapEqOn footprint heap1 heap3.
Proof.
  intros footprint heap1 heap2 heap3 HEq12 HEq23 r l HIn.
  rewrite HEq12 by exact HIn.
  apply HEq23.
  exact HIn.
Qed.

Lemma HeapEqOn_weaken :
  forall footprint_small footprint_big heap1 heap2,
    (forall r l, footprint_small r l -> footprint_big r l) ->
    HeapEqOn footprint_big heap1 heap2 ->
    HeapEqOn footprint_small heap1 heap2.
Proof.
  intros footprint_small footprint_big heap1 heap2 HIncl HEq r l HIn.
  apply HEq.
  eapply HIncl.
  exact HIn.
Qed.

Lemma HeapEqOn_from_heap_eq :
  forall footprint heap1 heap2,
    heap1 = heap2 ->
    HeapEqOn footprint heap1 heap2.
Proof.
  intros footprint heap1 heap2 HHeap.
  subst heap2.
  apply HeapEqOn_refl.
Qed.

Corollary Steps_error_heap_footprint_deterministic :
  forall footprint state phi1 heap1 phi2 heap2,
    Steps state phi1 (StError heap1) ->
    Steps state phi2 (StError heap2) ->
    phi1 = phi2 /\ HeapEqOn footprint heap1 heap2.
Proof.
  intros footprint state phi1 heap1 phi2 heap2 HSteps1 HSteps2.
  destruct
    (Steps_error_trace_deterministic
      state phi1 heap1 phi2 heap2 HSteps1 HSteps2)
    as (HPhi & HHeap).
  subst heap2.
  split.
  - exact HPhi.
  - apply HeapEqOn_refl.
Qed.

Corollary Steps_error_heap_trace_footprint_deterministic :
  forall state phi1 heap1 phi2 heap2,
    Steps state phi1 (StError heap1) ->
    Steps state phi2 (StError heap2) ->
    phi1 = phi2 /\ HeapEqOnTrace phi1 heap1 heap2.
Proof.
  intros state phi1 heap1 phi2 heap2 HSteps1 HSteps2.
  eapply Steps_error_heap_footprint_deterministic; eauto.
Qed.

Definition SchedulerTraceRepresentsViews
    (phi : Trace) (view_left view_right : TraceView) : Prop :=
  TracePermutation phi (trace_view_flatten (TracePar view_left view_right)).

Lemma TracePar_flatten_canonical :
  forall view_left view_right,
    trace_view_flatten (TracePar view_left view_right) =
    trace_view_flatten view_left ++ trace_view_flatten view_right.
Proof.
  reflexivity.
Qed.

Lemma SchedulerTraceRepresentsViews_canonical :
  forall view_left view_right,
    SchedulerTraceRepresentsViews
      (trace_view_flatten view_left ++ trace_view_flatten view_right)
      view_left
      view_right.
Proof.
  intros view_left view_right.
  unfold SchedulerTraceRepresentsViews, TracePermutation.
  simpl.
  reflexivity.
Qed.
