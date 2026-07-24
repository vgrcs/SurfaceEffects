From Stdlib Require Import List.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.Trace.

Import ListNotations.

Inductive NTraceView :=
| NTraceEmpty : NTraceView
| NTraceAction : DynamicAction -> NTraceView
| NTraceSeq : NTraceView -> NTraceView -> NTraceView.

Fixpoint trace_view_flatten (view : NTraceView) : Trace :=
  match view with
  | NTraceEmpty => []
  | NTraceAction action => [action]
  | NTraceSeq view1 view2 =>
      trace_view_flatten view1 ++ trace_view_flatten view2
  end.

Definition TraceViewRepresents (view : NTraceView) (phi : Trace) : Prop :=
  trace_view_flatten view = phi.

Definition TraceViewCoveredBySummary
    (view : NTraceView) (theta : Summary) : Prop :=
  TraceCoveredBySummary (trace_view_flatten view) theta.

Definition ReadOnlyTraceView (view : NTraceView) : Prop :=
  ReadOnlyTrace (trace_view_flatten view).

Definition label_view (label : NLabel) : NTraceView :=
  match label with
  | LSilent => NTraceEmpty
  | LAction action => NTraceAction action
  end.

Lemma label_view_flatten :
  forall label,
    trace_view_flatten (label_view label) = label_trace label.
Proof.
  intros [| action]; reflexivity.
Qed.

Inductive NStepsView : NState -> NTraceView -> NState -> Prop :=
| StepsViewRefl :
    forall state,
      NStepsView state NTraceEmpty state
| StepsViewStep :
    forall state label state' view state'',
      NStep state label state' ->
      NStepsView state' view state'' ->
      NStepsView state (NTraceSeq (label_view label) view) state''.

Lemma NStepsView_to_NSteps :
  forall state view state',
    NStepsView state view state' ->
    NSteps state (trace_view_flatten view) state'.
Proof.
  intros state view state' HSteps.
  induction HSteps.
  - constructor.
  - simpl.
    rewrite label_view_flatten.
    eapply StepsStep; eauto.
Qed.

Lemma NSteps_to_NStepsView :
  forall state phi state',
    NSteps state phi state' ->
    exists view,
      NStepsView state view state' /\
      TraceViewRepresents view phi.
Proof.
  intros state phi state' HSteps.
  induction HSteps as
    [state | state label state' phi state'' HStep _ IH].
  - exists NTraceEmpty.
    split; [constructor | reflexivity].
  - destruct IH as (view & HViewSteps & HView).
    exists (NTraceSeq (label_view label) view).
    split.
    + eapply StepsViewStep; eauto.
    + unfold TraceViewRepresents in *.
      simpl.
      rewrite label_view_flatten, HView.
      reflexivity.
Qed.

Lemma NStepsN_to_NStepsView :
  forall n state phi state',
    NStepsN n state phi state' ->
    exists view,
      NStepsView state view state' /\
      TraceViewRepresents view phi.
Proof.
  intros n state phi state' HStepsN.
  apply NSteps_to_NStepsView.
  eapply NStepsN_to_NSteps; eauto.
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
    TraceViewCoveredBySummary NTraceEmpty theta.
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
      (NTraceSeq view1 view2)
      (summary_union theta1 theta2).
Proof.
  intros view1 view2 theta1 theta2 HCovered1 HCovered2.
  unfold TraceViewCoveredBySummary in *.
  simpl.
  apply trace_covered_app_summary_union; assumption.
Qed.
