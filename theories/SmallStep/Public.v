Require Export theories.SmallStep.Core.Syntax.
Require Export theories.SmallStep.Typing.Judgments.
Require Export theories.SmallStep.Runtime.Machine.
Require Export theories.SmallStep.Runtime.Trace.
Require Export theories.SmallStep.Runtime.TraceView.
Require Export theories.SmallStep.Runtime.Progress.
Require Export theories.SmallStep.Runtime.PreservationPublic.
Require Export theories.SmallStep.Determinism.Terminal.
Require Export theories.SmallStep.Determinism.SchedulerPublic.
Require Import theories.SmallStep.Soundness.Dispatcher.
Require Import theories.SmallStep.Soundness.PairPar.
Require Import theories.SmallStep.Soundness.PairParFallback.

(** Public proof endpoints for the small-step development.

    Import this file when a client wants the theorem surface rather than the
    supporting proof library.  The underlying modules remain available for
    proof engineering work. *)

Definition SmallStep_static_effect_soundness :=
  checked_store_computation_trace_soundness.

Definition SmallStep_checked_terminal_correctness :=
  checked_execution_store_context_terminal_correctness_from_store_dispatch.

Definition SmallStep_terminal_trace_deterministic :=
  Steps_terminal_trace_deterministic.

Definition SmallStep_terminal_deterministic :=
  Steps_terminal_deterministic.

Definition SmallStep_pairpar_dispatcher_case :=
  EPairPar_checked_store_context_case_from_below.

Definition SmallStep_pairpar_fallback_run :=
  PairParFallbackRun.

Definition SmallStep_pairpar_checked_reject_run :=
  PairParCheckedRejectRun.

Definition SmallStep_pairpar_checked_pass_fallback_embeds_steps :=
  PairParFallbackRun_checked_pass.

Definition SmallStep_pairpar_precheck_rejection_falls_back_sequentially :=
  PairParFallbackRun_check_fallback_sequential.

Definition SmallStep_pairpar_checked_components_fallback :=
  PairParFallbackRun_checked_components.

Definition SmallStep_pairpar_static_summary_noalloc :=
  CBT_PairPar_summary_static_noalloc.

Definition SmallStep_pairpar_static_summary_readonly :=
  CBT_PairPar_summary_static_readonly.

Definition SmallStep_scheduler_checked_left_then_right_embeds :=
  ScheduledPairParRun_checked_pairpar_left_then_right_embeds.

Definition SmallStep_scheduler_checked_nsteps_embeds :=
  ScheduledPairParRun_checked_pairpar_nsteps_embeds.

Definition SmallStep_scheduler_checked_success_join_deterministic :=
  ScheduledPairParRun_checked_pairpar_success_join_deterministic.

Definition
  SmallStep_scheduler_checked_success_continuation_deterministic :=
  ScheduledPairParRun_checked_pairpar_success_continuation_deterministic.

Definition SmallStep_scheduler_checked_error_classifies :=
  ScheduledPairParRun_checked_pairpar_error_classifies.

Definition SmallStep_scheduler_checked_error_same_cause :=
  ScheduledPairParRun_checked_pairpar_error_same_cause.

Definition SmallStep_scheduler_checked_success_error_disjoint :=
  ScheduledPairParRun_checked_pairpar_success_error_disjoint.

Definition SmallStep_scheduler_checked_terminal_outcomes_deterministic :=
  ScheduledPairParRun_checked_pairpar_terminal_outcomes_deterministic.
