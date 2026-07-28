From Stdlib Require Import List.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Runtime.Trace.

Import ListNotations.

Inductive TraceView :=
| TraceEmpty : TraceView
| TraceAction : DynamicAction -> TraceView
| TraceSeq : TraceView -> TraceView -> TraceView
| TracePar : TraceView -> TraceView -> TraceView.

Fixpoint trace_view_flatten (view : TraceView) : Trace :=
  match view with
  | TraceEmpty => []
  | TraceAction action => [action]
  | TraceSeq view1 view2 =>
      trace_view_flatten view1 ++ trace_view_flatten view2
  | TracePar view1 view2 =>
      trace_view_flatten view1 ++ trace_view_flatten view2
  end.

Definition TraceViewRepresents (view : TraceView) (phi : Trace) : Prop :=
  trace_view_flatten view = phi.

Definition TraceViewCoveredBySummary
    (view : TraceView) (theta : Summary) : Prop :=
  TraceCoveredBySummary (trace_view_flatten view) theta.

Definition ReadOnlyTraceView (view : TraceView) : Prop :=
  ReadOnlyTrace (trace_view_flatten view).

Definition label_view (label : Label) : TraceView :=
  match label with
  | LSilent => TraceEmpty
  | LAction action => TraceAction action
  end.

Lemma label_view_flatten :
  forall label,
    trace_view_flatten (label_view label) = label_trace label.
Proof.
  intros [| action]; reflexivity.
Qed.

Inductive StepsView : State -> TraceView -> State -> Prop :=
| StepsViewRefl :
    forall state,
      StepsView state TraceEmpty state
| StepsViewStep :
    forall state label state' view state'',
      Step state label state' ->
      StepsView state' view state'' ->
      StepsView state (TraceSeq (label_view label) view) state''.

Lemma StepsView_to_Steps :
  forall state view state',
    StepsView state view state' ->
    Steps state (trace_view_flatten view) state'.
Proof.
  intros state view state' HSteps.
  induction HSteps.
  - constructor.
  - simpl.
    rewrite label_view_flatten.
    eapply StepsStep; eauto.
Qed.

Lemma Steps_to_StepsView :
  forall state phi state',
    Steps state phi state' ->
    exists view,
      StepsView state view state' /\
      TraceViewRepresents view phi.
Proof.
  intros state phi state' HSteps.
  induction HSteps as
    [state | state label state' phi state'' HStep _ IH].
  - exists TraceEmpty.
    split; [constructor | reflexivity].
  - destruct IH as (view & HViewSteps & HView).
    exists (TraceSeq (label_view label) view).
    split.
    + eapply StepsViewStep; eauto.
    + unfold TraceViewRepresents in *.
      simpl.
      rewrite label_view_flatten, HView.
      reflexivity.
Qed.

Lemma StepsN_to_StepsView :
  forall n state phi state',
    StepsN n state phi state' ->
    exists view,
      StepsView state view state' /\
      TraceViewRepresents view phi.
Proof.
  intros n state phi state' HStepsN.
  apply Steps_to_StepsView.
  eapply StepsN_to_Steps; eauto.
Qed.

Lemma trace_view_covered_top :
  forall view,
    TraceViewCoveredBySummary view SummaryTop.
Proof.
  intros view.
  unfold TraceViewCoveredBySummary.
  apply trace_covered_top.
Qed.

Lemma trace_view_covered_empty :
  forall theta,
    TraceViewCoveredBySummary TraceEmpty theta.
Proof.
  intros theta.
  unfold TraceViewCoveredBySummary.
  simpl.
  apply trace_covered_nil.
Qed.

Lemma trace_view_covered_seq_summary_union :
  forall view1 view2 theta1 theta2,
    TraceViewCoveredBySummary view1 theta1 ->
    TraceViewCoveredBySummary view2 theta2 ->
    TraceViewCoveredBySummary
      (TraceSeq view1 view2)
      (summary_union theta1 theta2).
Proof.
  intros view1 view2 theta1 theta2 HCovered1 HCovered2.
  unfold TraceViewCoveredBySummary in *.
  simpl.
  apply trace_covered_app_summary_union; assumption.
Qed.

Lemma trace_view_covered_par_summary_union :
  forall view1 view2 theta1 theta2,
    TraceViewCoveredBySummary view1 theta1 ->
    TraceViewCoveredBySummary view2 theta2 ->
    TraceViewCoveredBySummary
      (TracePar view1 view2)
      (summary_union theta1 theta2).
Proof.
  intros view1 view2 theta1 theta2 HCovered1 HCovered2.
  unfold TraceViewCoveredBySummary in *.
  simpl.
  apply trace_covered_app_summary_union; assumption.
Qed.
