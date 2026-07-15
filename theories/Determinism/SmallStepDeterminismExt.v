From stdpp Require Import gmap.
From Stdlib Require Import Sets.Ensembles.

Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.DynamicActions.
Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepStructuredTrace.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.HeapFacts.

Theorem SmallStepDynamicDeterminism_ext :
  forall heap_a heap_b env rho exp heap1 heap2 val1 val2 trace1 trace2,
    heap_a ≡@{Heap} heap_b ->
    Steps (initial_state heap_a env rho exp) trace1
      (StDone heap1 val1) ->
    Steps (initial_state heap_b env rho exp) trace2
      (StDone heap2 val2) ->
    forall stty ctxt rgns ty static,
      TcHeap (heap_a, stty) ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, exp, ty, static) ->
      heap1 ≡@{Heap} heap2 /\ val1 = val2 /\ trace1 = trace2.
Proof.
  intros heap_a heap_b env rho exp heap1 heap2 val1 val2 trace1 trace2
    HHeapEq HSteps1 HSteps2 stty ctxt rgns ty static
    _ _ _ _ _.
  unfold equiv, heap_equiv in HHeapEq.
  subst heap_b.
  destruct
    (Steps_terminal_deterministic
      (initial_state heap_a env rho exp)
      trace1 heap1 val1 trace2 heap2 val2 HSteps1 HSteps2)
    as (HTrace & HHeap & HVal).
  subst.
  repeat split; reflexivity.
Qed.

Theorem SmallStepStructuredDynamicDeterminism_ext :
  forall heap_a heap_b env rho exp heap1 heap2 val1 val2 phi1 phi2,
    heap_a ≡@{Heap} heap_b ->
    StepsPhi (initial_state heap_a env rho exp) phi1
      (StDone heap1 val1) ->
    StepsPhi (initial_state heap_b env rho exp) phi2
      (StDone heap2 val2) ->
    forall stty ctxt rgns ty static,
      TcHeap (heap_a, stty) ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, exp, ty, static) ->
      heap1 ≡@{Heap} heap2 /\
      val1 = val2 /\
      phi_as_list phi1 = phi_as_list phi2.
Proof.
  intros heap_a heap_b env rho exp heap1 heap2 val1 val2 phi1 phi2
    HHeapEq HSteps1 HSteps2 stty ctxt rgns ty static
    HTcHeap HTcRho HTcInc HTcEnv HTcExp.
  eapply SmallStepDynamicDeterminism_ext; eauto;
    eapply StepsPhi_as_steps; eauto.
Qed.

Theorem SmallStepDeterminism :
  forall exp heap1 heap2 val1 val2 trace1 trace2,
    Steps (initial_state ∅ ∅ ∅ exp) trace1
      (StDone heap1 val1) ->
    Steps (initial_state ∅ ∅ ∅ exp) trace2
      (StDone heap2 val2) ->
    forall ty eff,
      TcExp (∅, Empty_set VarId, exp, ty, eff) ->
      heap1 ≡@{Heap} heap2 /\ val1 = val2 /\ trace1 = trace2.
Proof.
  intros exp heap1 heap2 val1 val2 trace1 trace2
    HSteps1 HSteps2 ty eff HTcExp.
  eapply SmallStepDynamicDeterminism_ext with (ctxt := ∅); eauto.
  - apply TcHeapEmpty.
    + reflexivity.
    + econstructor.
  - constructor. intros r. split.
    + intro HLookup. exfalso. apply HLookup. apply lookup_empty.
    + intro HIn. inversion HIn.
  - constructor. intros x t HFind y HIn.
    replace (find_T x ∅) with (None : option Tau) in HFind
      by (unfold find_T; symmetry; apply lookup_empty).
    discriminate.
  - constructor.
    + intros x v HFindE.
      replace (find_E x ∅) with (None : option Val) in HFindE
        by (unfold find_E; symmetry; apply lookup_empty).
      discriminate.
    + intros x t HFindT.
      replace (find_T x ∅) with (None : option Tau) in HFindT
        by (unfold find_T; symmetry; apply lookup_empty).
      discriminate.
    + intros x v t HFindE HFindT.
      replace (find_E x ∅) with (None : option Val) in HFindE
        by (unfold find_E; symmetry; apply lookup_empty).
      discriminate.
Qed.

Theorem SmallStepStructuredDeterminism :
  forall exp heap1 heap2 val1 val2 phi1 phi2,
    StepsPhi (initial_state ∅ ∅ ∅ exp) phi1
      (StDone heap1 val1) ->
    StepsPhi (initial_state ∅ ∅ ∅ exp) phi2
      (StDone heap2 val2) ->
    forall ty eff,
      TcExp (∅, Empty_set VarId, exp, ty, eff) ->
      heap1 ≡@{Heap} heap2 /\
      val1 = val2 /\
      phi_as_list phi1 = phi_as_list phi2.
Proof.
  intros exp heap1 heap2 val1 val2 phi1 phi2
    HSteps1 HSteps2 ty eff HTcExp.
  eapply SmallStepStructuredDynamicDeterminism_ext with (ctxt := ∅); eauto.
  - apply TcHeapEmpty.
    + reflexivity.
    + econstructor.
  - constructor. intros r. split.
    + intro HLookup. exfalso. apply HLookup. apply lookup_empty.
    + intro HIn. inversion HIn.
  - constructor. intros x t HFind y HIn.
    replace (find_T x ∅) with (None : option Tau) in HFind
      by (unfold find_T; symmetry; apply lookup_empty).
    discriminate.
  - constructor.
    + intros x v HFindE.
      replace (find_E x ∅) with (None : option Val) in HFindE
        by (unfold find_E; symmetry; apply lookup_empty).
      discriminate.
    + intros x t HFindT.
      replace (find_T x ∅) with (None : option Tau) in HFindT
        by (unfold find_T; symmetry; apply lookup_empty).
      discriminate.
    + intros x v t HFindE HFindT.
      replace (find_E x ∅) with (None : option Val) in HFindE
        by (unfold find_E; symmetry; apply lookup_empty).
      discriminate.
Qed.
