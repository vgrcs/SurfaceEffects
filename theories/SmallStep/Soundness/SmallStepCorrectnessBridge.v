Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepStructuredTrace.
Require Import theories.Runtime.SmallStepCorrectness.
Require Import theories.Runtime.Semantics.
Require Import theories.Core.DynamicActions.
Require Import theories.Core.Values.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.TraceTypingFacts.
Require Import theories.Soundness.Correctness.

Theorem small_step_structured_correctness_from_big_step_traces :
  forall heap heap_body heap_summary env rho ea ee
    phi_body phi_summary v theta stty ctxt rgns ty static,
    StepsPhi
      (initial_state heap env rho ea)
      phi_body
      (StDone heap_body v) ->
    StepsPhi
      (initial_state heap env rho ee)
      phi_summary
      (StDone heap_summary (Eff theta)) ->
    (heap, env, rho, ea) ⇓ (heap_body, v, phi_body) ->
    (heap, env, rho, ee) ⇓ (heap_summary, Eff theta, phi_summary) ->
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    phi_body ⋞ theta.
Proof.
  intros heap heap_body heap_summary env rho ea ee
    phi_body phi_summary v theta stty ctxt rgns ty static
    _ _ HBigBody HBigSummary HBack HReadOnly
    HTcHeap HTcRho HTcInc HTcEnv HTcExp.
  eapply Correctness_soundness_ext with
    (h_ := heap)
    (h'_ := heap_body)
    (v_ := v)
    (p_ := phi_body)
    (static := static)
    (ty := ty);
    eauto.
Qed.

Theorem small_step_list_correctness_from_big_step_traces :
  forall heap heap_body heap_summary env rho ea ee
    trace_body trace_summary v theta stty ctxt rgns ty static,
    Steps
      (initial_state heap env rho ea)
      trace_body
      (StDone heap_body v) ->
    Steps
      (initial_state heap env rho ee)
      trace_summary
      (StDone heap_summary (Eff theta)) ->
    (heap, env, rho, ea) ⇓
      (heap_body, v, trace_as_phi trace_body) ->
    (heap, env, rho, ee) ⇓
      (heap_summary, Eff theta, trace_as_phi trace_summary) ->
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    ReadOnlyPhi (trace_as_phi trace_summary) ->
    TcHeap (heap, stty) ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    trace_as_phi trace_body ⋞ theta.
Proof.
  intros heap heap_body heap_summary env rho ea ee
    trace_body trace_summary v theta stty ctxt rgns ty static
    _ _ HBigBody HBigSummary HBack HReadOnly
    HTcHeap HTcRho HTcInc HTcEnv HTcExp.
  eapply Correctness_soundness_ext with
    (h_ := heap)
    (h'_ := heap_body)
    (v_ := v)
    (p_ := trace_as_phi trace_body)
    (static := static)
    (ty := ty);
    eauto.
Qed.

Theorem small_step_structured_correctness_from_big_step_normalized_traces :
  forall heap heap_body heap_summary env rho ea ee
    phi_body phi_summary v theta stty ctxt rgns ty static,
    StepsPhi
      (initial_state heap env rho ea)
      phi_body
      (StDone heap_body v) ->
    StepsPhi
      (initial_state heap env rho ee)
      phi_summary
      (StDone heap_summary (Eff theta)) ->
    (heap, env, rho, ea) ⇓
      (heap_body, v, trace_as_phi (phi_as_list phi_body)) ->
    (heap, env, rho, ee) ⇓
      (heap_summary, Eff theta, trace_as_phi (phi_as_list phi_summary)) ->
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    phi_body ⋞ theta.
Proof.
  intros heap heap_body heap_summary env rho ea ee
    phi_body phi_summary v theta stty ctxt rgns ty static
    HStepsBody HStepsSummary HBigBody HBigSummary HBack HReadOnly
    HTcHeap HTcRho HTcInc HTcEnv HTcExp.
  apply Phi_Theta_Soundness_of_trace_as_phi_phi_as_list.
  eapply small_step_list_correctness_from_big_step_traces; eauto.
  - eapply StepsPhi_as_steps; eauto.
  - eapply StepsPhi_as_steps; eauto.
  - apply ReadOnlyPhi_trace_as_phi_phi_as_list.
    exact HReadOnly.
Qed.
