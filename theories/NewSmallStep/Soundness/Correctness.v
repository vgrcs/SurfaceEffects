From Stdlib Require Import Lia.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.Trace.
Require Import theories.NewSmallStep.Runtime.TraceView.
Require Import theories.NewSmallStep.Soundness.BackTriangle.

Definition SummaryEvaluation (heap : Heap) (env : NEnv) (rho : Rho)
    (summary_expr : NExpr) (phi_summary : Trace)
    (heap_summary : Heap) (theta : Summary) : Prop :=
  NSteps
    (NInitialState heap env rho summary_expr)
    phi_summary
    (StDone heap_summary (VSummary theta)).

Definition ComputationEvaluation (heap : Heap) (env : NEnv) (rho : Rho)
    (expr : NExpr) (phi : Trace) (heap' : Heap) (v : NVal) : Prop :=
  NSteps
    (NInitialState heap env rho expr)
    phi
    (StDone heap' v).

Definition CountedComputationEvaluation (n : nat)
    (heap : Heap) (env : NEnv) (rho : Rho)
    (expr : NExpr) (phi : Trace) (heap' : Heap) (v : NVal) : Prop :=
  NStepsN n
    (NInitialState heap env rho expr)
    phi
    (StDone heap' v).

Definition StructuredSummaryEvaluation
    (heap : Heap) (env : NEnv) (rho : Rho)
    (summary_expr : NExpr) (view_summary : NTraceView)
    (heap_summary : Heap) (theta : Summary) : Prop :=
  NStepsView
    (NInitialState heap env rho summary_expr)
    view_summary
    (StDone heap_summary (VSummary theta)).

Definition StructuredComputationEvaluation
    (heap : Heap) (env : NEnv) (rho : Rho)
    (expr : NExpr) (view : NTraceView)
    (heap' : Heap) (v : NVal) : Prop :=
  NStepsView
    (NInitialState heap env rho expr)
    view
    (StDone heap' v).

Definition TerminalCorrectnessGoal : Prop :=
  forall gamma omega heap env rho expr summary_expr phi heap' v
    phi_summary heap_summary theta,
    NBackTriangle gamma omega expr summary_expr ->
    ComputationEvaluation heap env rho expr phi heap' v ->
    SummaryEvaluation heap env rho summary_expr
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.

Definition StructuredTerminalCorrectnessGoal : Prop :=
  forall gamma omega heap env rho expr summary_expr view heap' v
    view_summary heap_summary theta,
    NBackTriangle gamma omega expr summary_expr ->
    StructuredComputationEvaluation heap env rho expr view heap' v ->
    StructuredSummaryEvaluation heap env rho summary_expr
      view_summary heap_summary theta ->
    TraceViewCoveredBySummary view theta.

Definition SmallStepCorrectnessBelow (n : nat) : Prop :=
  forall n_child gamma omega heap env rho expr summary_expr phi heap' v
    phi_summary heap_summary theta,
    n_child < n ->
    NBackTriangle gamma omega expr summary_expr ->
    CountedComputationEvaluation n_child heap env rho expr phi heap' v ->
    SummaryEvaluation heap env rho summary_expr
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.

Theorem terminal_correctness_from_below :
  (forall n, SmallStepCorrectnessBelow n) ->
  TerminalCorrectnessGoal.
Proof.
  unfold TerminalCorrectnessGoal.
  intros HBelow gamma omega heap env rho expr summary_expr phi heap' v
    phi_summary heap_summary theta HBack HComp HSummary.
  destruct
    (NSteps_to_NStepsN
      (NInitialState heap env rho expr)
      phi
      (StDone heap' v)
      HComp)
    as (n & HCompN).
  eapply (HBelow (S n) n); eauto; lia.
Qed.

Definition TerminalCorrectnessWithTop : Prop :=
  forall phi,
    TraceCoveredBySummary phi SummaryTop.

Theorem terminal_correctness_with_top :
  TerminalCorrectnessWithTop.
Proof.
  unfold TerminalCorrectnessWithTop.
  apply trace_covered_top.
Qed.

Theorem structured_terminal_correctness_from_raw :
  TerminalCorrectnessGoal ->
  StructuredTerminalCorrectnessGoal.
Proof.
  unfold TerminalCorrectnessGoal, StructuredTerminalCorrectnessGoal.
  intros HRaw gamma omega heap env rho expr summary_expr view heap' v
    view_summary heap_summary theta HBack HComp HSummary.
  unfold StructuredComputationEvaluation in HComp.
  unfold StructuredSummaryEvaluation in HSummary.
  unfold TraceViewCoveredBySummary.
  eapply HRaw; eauto;
    eapply NStepsView_to_NSteps; eauto.
Qed.

Theorem structured_terminal_correctness_from_below :
  (forall n, SmallStepCorrectnessBelow n) ->
  StructuredTerminalCorrectnessGoal.
Proof.
  intros HBelow.
  apply structured_terminal_correctness_from_raw.
  apply terminal_correctness_from_below.
  exact HBelow.
Qed.
