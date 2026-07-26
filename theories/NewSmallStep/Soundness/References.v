From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Program.Equality.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.Continuation.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.RegularStateShape.
Require Import theories.NewSmallStep.Runtime.Trace.
Require Import theories.NewSmallStep.Soundness.BackTriangle.
Require Import theories.NewSmallStep.Soundness.Correctness.
Require Import theories.NewSmallStep.Soundness.Summary.
Require Import theories.NewSmallStep.Typing.Judgments.
Require Import theories.NewSmallStep.Typing.Regularity.
Require Import theories.NewSmallStep.Typing.Resolve.
Require Import theories.NewSmallStep.Typing.Types.
Require Import theories.NewSmallStep.Determinism.Terminal.

Import ListNotations.

Lemma ERef_terminal_first_step :
  forall heap env rho r e phi heap_final v_final,
    NSteps
      (NInitialState heap env rho (ERef r e))
      phi
      (StDone heap_final v_final) ->
    exists r_val phi_tail,
      eval_region rho r = Some r_val /\
      NSteps
        (StEval heap env rho e (KRef r_val KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap env rho r e phi heap_final v_final HSteps.
  remember (NInitialState heap env rho (ERef r e)) as start
    eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    exists r_val, phi0.
    repeat split; assumption || reflexivity.
Qed.

Lemma ERef_terminal_first_step_N :
  forall n heap env rho r e phi heap_final v_final,
    NStepsN n
      (NInitialState heap env rho (ERef r e))
      phi
      (StDone heap_final v_final) ->
    exists r_val n_tail phi_tail,
      eval_region rho r = Some r_val /\
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho e (KRef r_val KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap env rho r e phi heap_final v_final HSteps.
  remember (NInitialState heap env rho (ERef r e)) as start
    eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as
    [state
    | n_tail state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    exists r_val, n_tail, phi0.
    repeat split; assumption || reflexivity.
Qed.

Lemma KRef_terminal_alloc_result :
  forall heap v r_val phi heap_final v_final,
    NSteps
      (StReturn heap v (KRef r_val KDone))
      phi
      (StDone heap_final v_final) ->
    exists l,
      heap_alloc r_val v heap = (l, heap_final) /\
      v_final = VLoc r_val l /\
      phi = [DAlloc r_val l].
Proof.
  intros heap v r_val phi heap_final v_final HSteps.
  remember
    (StReturn heap v (KRef r_val KDone))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (NSteps_known_first_step_terminal_inv
        (StReturn heap' (VLoc r_val l) KDone)
        LSilent
        (StDone heap' (VLoc r_val l))
        phi0
        heap_final
        v_final
        (StepReturnDone heap' (VLoc r_val l))
        HTail)
      as (phi_done & HDone & HTraceTail).
    destruct
      (NSteps_done_inv
        heap'
        (VLoc r_val l)
        phi_done
        (StDone heap_final v_final)
        HDone)
      as (HTraceDone & HFinalState).
    simpl in *.
    subst phi_done phi0.
    inversion HFinalState; subst.
    exists l.
    repeat split; reflexivity || assumption.
Qed.

Definition ERefDecompositionGoal : Prop :=
  forall heap env rho r e phi heap_final loc,
    NSteps
      (NInitialState heap env rho (ERef r e))
      phi
      (StDone heap_final loc) ->
    exists phi_e heap_e v r_val l,
      eval_region rho r = Some r_val /\
      NSteps
        (NInitialState heap env rho e)
        phi_e
        (StDone heap_e v) /\
      heap_alloc r_val v heap_e = (l, heap_final) /\
      loc = VLoc r_val l /\
      phi = phi_e ++ [DAlloc r_val l].

Definition ERefCountedDecompositionGoal : Prop :=
  forall n heap env rho r e phi heap_final loc,
    NStepsN n
      (NInitialState heap env rho (ERef r e))
      phi
      (StDone heap_final loc) ->
    exists n_e phi_e heap_e v r_val l,
      eval_region rho r = Some r_val /\
      NStepsN n_e
        (NInitialState heap env rho e)
        phi_e
        (StDone heap_e v) /\
      heap_alloc r_val v heap_e = (l, heap_final) /\
      loc = VLoc r_val l /\
      phi = phi_e ++ [DAlloc r_val l] /\
      n_e < n.

Theorem ERef_decomposition :
  ERefDecompositionGoal.
Proof.
  unfold ERefDecompositionGoal.
  intros heap env rho r e phi heap_final loc HSteps.
  destruct
    (ERef_terminal_first_step
      heap env rho r e phi heap_final loc HSteps)
    as (r_val & phi_tail & HRgn & HExprWithKont & HTraceStart).
  destruct
    (NSteps_to_NStepsN
      (StEval heap env rho e (KRef r_val KDone))
      phi_tail
      (StDone heap_final loc)
      HExprWithKont)
    as (n_expr & HExprWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_expr
      (StEval heap env rho e (KRef r_val KDone))
      phi_tail
      heap_final
      loc
      HExprWithKontN
      (NInitialState heap env rho e)
      (KRef r_val KDone)
      eq_refl)
    as (phi_e & heap_e & v & phi_after_expr &
      HExpr & HAfterExpr & HTraceExpr).
  destruct
    (KRef_terminal_alloc_result
      heap_e v r_val phi_after_expr heap_final loc HAfterExpr)
    as (l & HAlloc & HLoc & HTraceAfterExpr).
  subst loc phi_after_expr.
  exists phi_e, heap_e, v, r_val, l.
  repeat split; try assumption.
  rewrite HTraceStart, HTraceExpr.
  reflexivity.
Qed.

Theorem ERef_counted_decomposition :
  ERefCountedDecompositionGoal.
Proof.
  unfold ERefCountedDecompositionGoal.
  intros n heap env rho r e phi heap_final loc HSteps.
  destruct
    (ERef_terminal_first_step_N
      n heap env rho r e phi heap_final loc HSteps)
    as (r_val & n_expr_tail & phi_tail & HRgn & HnStart &
      HExprWithKont & HTraceStart).
  destruct
    (NStepsN_append_kont_terminal_split_counted
      n_expr_tail
      (StEval heap env rho e (KRef r_val KDone))
      phi_tail
      heap_final
      loc
      HExprWithKont
      (NInitialState heap env rho e)
      (KRef r_val KDone)
      eq_refl)
    as (n_e & n_after_expr & phi_e & heap_e & v &
      phi_after_expr & HExpr & HAfterExpr & HCountExpr &
      HTraceExpr).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KRef_terminal_alloc_result
        heap_e v r_val phi_after_expr heap_final loc
        (NStepsN_to_NSteps
          n_after_expr
          (StReturn heap_e v (KRef r_val KDone))
          phi_after_expr
          (StDone heap_final loc)
          HAfterExpr))
      as (l & HAlloc & HLoc & HTraceAfterExpr).
    subst loc phi_after_expr.
    assert (HAfterExprPositive : 0 < n_after_expr).
    { destruct n_after_expr; [inversion HAfterExpr | lia]. }
    exists n_e, phi_e, heap_e, v, r_val, l.
    repeat split; try assumption.
    + rewrite HTraceStart, HTraceExpr.
      reflexivity.
    + lia.
Qed.

Lemma EDeref_terminal_first_step :
  forall heap env rho r e phi heap_final v_final,
    NSteps
      (NInitialState heap env rho (EDeref r e))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho e (KDeref r KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap env rho r e phi heap_final v_final HSteps.
  remember (NInitialState heap env rho (EDeref r e)) as start
    eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StEval heap env rho (EDeref r e) KDone)
        LSilent
        (StEval heap env rho e (KDeref r KDone))
        label state'
        (StepDeref heap env rho r e KDone)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma EDeref_terminal_first_step_N :
  forall n heap env rho r e phi heap_final v_final,
    NStepsN n
      (NInitialState heap env rho (EDeref r e))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho e (KDeref r KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap env rho r e phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (NInitialState heap env rho (EDeref r e))
      LSilent
      (StEval heap env rho e (KDeref r KDone))
      phi heap_final v_final
      (StepDeref heap env rho r e KDone)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
Qed.

Lemma KDeref_terminal_value_is_loc :
  forall heap v r_static k phi heap_final v_final,
    NSteps
      (StReturn heap v (KDeref r_static k))
      phi
      (StDone heap_final v_final) ->
    exists r l,
      v = VLoc r l.
Proof.
  intros heap v r_static k phi heap_final v_final HSteps.
  remember
    (StReturn heap v (KDeref r_static k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    repeat eexists.
Qed.

Lemma KDeref_loc_terminal_read_result :
  forall heap r_static r l phi heap_final v_final,
    NSteps
      (StReturn heap (VLoc r l) (KDeref r_static KDone))
      phi
      (StDone heap_final v_final) ->
    heap_lookup r l heap = Some v_final /\
    heap_final = heap /\
    phi = [DRead r l].
Proof.
  intros heap r_static r l phi heap_final v_final HSteps.
  remember
    (StReturn heap (VLoc r l) (KDeref r_static KDone))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (NSteps_known_first_step_terminal_inv
        (StReturn heap v KDone)
        LSilent
        (StDone heap v)
        phi0
        heap_final
        v_final
        (StepReturnDone heap v)
        HTail)
      as (phi_done & HDone & HTraceTail).
    destruct
      (NSteps_done_inv
        heap
        v
        phi_done
        (StDone heap_final v_final)
        HDone)
      as (HTraceDone & HFinalState).
    simpl in *.
    subst phi_done phi0.
    inversion HFinalState; subst.
    repeat split; reflexivity || assumption.
Qed.

Definition EDerefDecompositionGoal : Prop :=
  forall heap env rho r_static e phi heap_final v_final,
    NSteps
      (NInitialState heap env rho (EDeref r_static e))
      phi
      (StDone heap_final v_final) ->
    exists phi_e heap_e r l,
      NSteps
        (NInitialState heap env rho e)
        phi_e
        (StDone heap_e (VLoc r l)) /\
      heap_lookup r l heap_e = Some v_final /\
      heap_final = heap_e /\
      phi = phi_e ++ [DRead r l].

Definition EDerefCountedDecompositionGoal : Prop :=
  forall n heap env rho r_static e phi heap_final v_final,
    NStepsN n
      (NInitialState heap env rho (EDeref r_static e))
      phi
      (StDone heap_final v_final) ->
    exists n_e phi_e heap_e r l,
      NStepsN n_e
        (NInitialState heap env rho e)
        phi_e
        (StDone heap_e (VLoc r l)) /\
      heap_lookup r l heap_e = Some v_final /\
      heap_final = heap_e /\
      phi = phi_e ++ [DRead r l] /\
      n_e < n.

Theorem EDeref_decomposition :
  EDerefDecompositionGoal.
Proof.
  unfold EDerefDecompositionGoal.
  intros heap env rho r_static e phi heap_final v_final HSteps.
  destruct
    (EDeref_terminal_first_step
      heap env rho r_static e phi heap_final v_final HSteps)
    as (phi_tail & HExprWithKont & HTraceStart).
  destruct
    (NSteps_to_NStepsN
      (StEval heap env rho e (KDeref r_static KDone))
      phi_tail
      (StDone heap_final v_final)
      HExprWithKont)
    as (n_expr & HExprWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_expr
      (StEval heap env rho e (KDeref r_static KDone))
      phi_tail
      heap_final
      v_final
      HExprWithKontN
      (NInitialState heap env rho e)
      (KDeref r_static KDone)
      eq_refl)
    as (phi_e & heap_e & v_loc & phi_after_expr &
      HExpr & HAfterExpr & HTraceExpr).
  destruct
    (KDeref_terminal_value_is_loc
      heap_e v_loc r_static KDone
      phi_after_expr heap_final v_final HAfterExpr)
    as (r & l & HLoc).
  subst v_loc.
  destruct
    (KDeref_loc_terminal_read_result
      heap_e r_static r l phi_after_expr heap_final v_final HAfterExpr)
    as (HLookup & HHeap & HTraceAfterExpr).
  subst heap_final phi_after_expr.
  exists phi_e, heap_e, r, l.
  repeat split; try assumption.
  rewrite HTraceStart, HTraceExpr.
  reflexivity.
Qed.

Theorem EDeref_counted_decomposition :
  EDerefCountedDecompositionGoal.
Proof.
  unfold EDerefCountedDecompositionGoal.
  intros n heap env rho r_static e phi heap_final v_final HSteps.
  destruct
    (EDeref_terminal_first_step_N
      n heap env rho r_static e phi heap_final v_final HSteps)
    as (n_expr_tail & phi_tail & HnStart &
      HExprWithKont & HTraceStart).
  destruct
    (NStepsN_append_kont_terminal_split_counted
      n_expr_tail
      (StEval heap env rho e (KDeref r_static KDone))
      phi_tail
      heap_final
      v_final
      HExprWithKont
      (NInitialState heap env rho e)
      (KDeref r_static KDone)
      eq_refl)
    as (n_e & n_after_expr & phi_e & heap_e & v_loc &
      phi_after_expr & HExpr & HAfterExpr & HCountExpr &
      HTraceExpr).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KDeref_terminal_value_is_loc
        heap_e v_loc r_static KDone
        phi_after_expr heap_final v_final
        (NStepsN_to_NSteps
          n_after_expr
          (StReturn heap_e v_loc (KDeref r_static KDone))
          phi_after_expr
          (StDone heap_final v_final)
          HAfterExpr))
      as (r & l & HLoc).
    subst v_loc.
    destruct
      (KDeref_loc_terminal_read_result
        heap_e r_static r l phi_after_expr heap_final v_final
        (NStepsN_to_NSteps
          n_after_expr
          (StReturn heap_e (VLoc r l) (KDeref r_static KDone))
          phi_after_expr
          (StDone heap_final v_final)
          HAfterExpr))
      as (HLookup & HHeap & HTraceAfterExpr).
    subst heap_final phi_after_expr.
    assert (HAfterExprPositive : 0 < n_after_expr).
    { destruct n_after_expr; [inversion HAfterExpr | lia]. }
    exists n_e, phi_e, heap_e, r, l.
    repeat split; try assumption.
    + rewrite HTraceStart, HTraceExpr.
      reflexivity.
    + lia.
Qed.

Lemma EAssign_terminal_first_step :
  forall heap env rho r ea ev phi heap_final v_final,
    NSteps
      (NInitialState heap env rho (EAssign r ea ev))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho ea (KAssignLoc r ev env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap env rho r ea ev phi heap_final v_final HSteps.
  remember (NInitialState heap env rho (EAssign r ea ev)) as start
    eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StEval heap env rho (EAssign r ea ev) KDone)
        LSilent
        (StEval heap env rho ea (KAssignLoc r ev env rho KDone))
        label state'
        (StepAssign heap env rho r ea ev KDone)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma EAssign_terminal_first_step_N :
  forall n heap env rho r ea ev phi heap_final v_final,
    NStepsN n
      (NInitialState heap env rho (EAssign r ea ev))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho ea
          (KAssignLoc r ev env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap env rho r ea ev phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (NInitialState heap env rho (EAssign r ea ev))
      LSilent
      (StEval heap env rho ea (KAssignLoc r ev env rho KDone))
      phi heap_final v_final
      (StepAssign heap env rho r ea ev KDone)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
Qed.

Lemma KAssignLoc_terminal_value_is_loc :
  forall heap v r_static ev env rho k phi heap_final v_final,
    NSteps
      (StReturn heap v (KAssignLoc r_static ev env rho k))
      phi
      (StDone heap_final v_final) ->
    exists r l,
      v = VLoc r l.
Proof.
  intros heap v r_static ev env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap v (KAssignLoc r_static ev env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    repeat eexists.
Qed.

Lemma KAssignLoc_loc_terminal_first_step :
  forall heap r_static ev env rho r l k phi heap_final v_final,
    NSteps
      (StReturn heap (VLoc r l) (KAssignLoc r_static ev env rho k))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho ev
          (KAssignVal r_static (VLoc r l) k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap r_static ev env rho r l k phi heap_final v_final HSteps.
  remember
    (StReturn heap (VLoc r l)
      (KAssignLoc r_static ev env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StReturn heap (VLoc r l)
          (KAssignLoc r_static ev env rho k))
        LSilent
        (StEval heap env rho ev
          (KAssignVal r_static (VLoc r l) k))
        label state'
        (StepAssignLoc heap r_static ev env rho r l k)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KAssignLoc_loc_terminal_first_step_N :
  forall n_steps heap r_static ev env rho r l k phi
    heap_final v_final,
    NStepsN n_steps
      (StReturn heap (VLoc r l)
        (KAssignLoc r_static ev env rho k))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n_steps = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho ev
          (KAssignVal r_static (VLoc r l) k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n_steps heap r_static ev env rho r l k phi
    heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n_steps
      (StReturn heap (VLoc r l)
        (KAssignLoc r_static ev env rho k))
      LSilent
      (StEval heap env rho ev
        (KAssignVal r_static (VLoc r l) k))
      phi heap_final v_final
      (StepAssignLoc heap r_static ev env rho r l k)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
Qed.

Lemma KAssignVal_terminal_write_result :
  forall heap v r_static r l phi heap_final v_final,
    NSteps
      (StReturn heap v (KAssignVal r_static (VLoc r l) KDone))
      phi
      (StDone heap_final v_final) ->
    heap_final = heap_update r l v heap /\
    v_final = VUnit /\
    phi = [DWrite r l].
Proof.
  intros heap v r_static r l phi heap_final v_final HSteps.
  remember
    (StReturn heap v (KAssignVal r_static (VLoc r l) KDone))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (NSteps_known_first_step_terminal_inv
        (StReturn (heap_update r l v heap) VUnit KDone)
        LSilent
        (StDone (heap_update r l v heap) VUnit)
        phi0
        heap_final
        v_final
        (StepReturnDone (heap_update r l v heap) VUnit)
        HTail)
      as (phi_done & HDone & HTraceTail).
    destruct
      (NSteps_done_inv
        (heap_update r l v heap)
        VUnit
        phi_done
        (StDone heap_final v_final)
        HDone)
      as (HTraceDone & HFinalState).
    simpl in *.
    subst phi_done phi0.
    inversion HFinalState; subst.
    repeat split; reflexivity.
Qed.

Definition EAssignDecompositionGoal : Prop :=
  forall heap env rho r_static ea ev phi heap_final v_final,
    NSteps
      (NInitialState heap env rho (EAssign r_static ea ev))
      phi
      (StDone heap_final v_final) ->
    exists phi_addr phi_val heap_addr heap_val r l v,
      NSteps
        (NInitialState heap env rho ea)
        phi_addr
        (StDone heap_addr (VLoc r l)) /\
      NSteps
        (NInitialState heap_addr env rho ev)
        phi_val
        (StDone heap_val v) /\
      heap_final = heap_update r l v heap_val /\
      v_final = VUnit /\
      phi = phi_addr ++ phi_val ++ [DWrite r l].

Definition EAssignCountedDecompositionGoal : Prop :=
  forall n heap env rho r_static ea ev phi heap_final v_final,
    NStepsN n
      (NInitialState heap env rho (EAssign r_static ea ev))
      phi
      (StDone heap_final v_final) ->
    exists n_addr n_val phi_addr phi_val heap_addr heap_val r l v,
      NStepsN n_addr
        (NInitialState heap env rho ea)
        phi_addr
        (StDone heap_addr (VLoc r l)) /\
      NStepsN n_val
        (NInitialState heap_addr env rho ev)
        phi_val
        (StDone heap_val v) /\
      heap_final = heap_update r l v heap_val /\
      v_final = VUnit /\
      phi = phi_addr ++ phi_val ++ [DWrite r l] /\
      n_addr < n /\
      n_val < n.

Theorem EAssign_decomposition :
  EAssignDecompositionGoal.
Proof.
  unfold EAssignDecompositionGoal.
  intros heap env rho r_static ea ev phi heap_final v_final HSteps.
  destruct
    (EAssign_terminal_first_step
      heap env rho r_static ea ev phi heap_final v_final HSteps)
    as (phi_tail & HAddrWithKont & HTraceStart).
  destruct
    (NSteps_to_NStepsN
      (StEval heap env rho ea
        (KAssignLoc r_static ev env rho KDone))
      phi_tail
      (StDone heap_final v_final)
      HAddrWithKont)
    as (n_addr & HAddrWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_addr
      (StEval heap env rho ea
        (KAssignLoc r_static ev env rho KDone))
      phi_tail
      heap_final
      v_final
      HAddrWithKontN
      (NInitialState heap env rho ea)
      (KAssignLoc r_static ev env rho KDone)
      eq_refl)
    as (phi_addr & heap_addr & v_addr & phi_after_addr &
      HAddr & HAfterAddr & HTraceAddr).
  destruct
    (KAssignLoc_terminal_value_is_loc
      heap_addr v_addr r_static ev env rho KDone
      phi_after_addr heap_final v_final HAfterAddr)
    as (r & l & HLoc).
  subst v_addr.
  destruct
    (KAssignLoc_loc_terminal_first_step
      heap_addr r_static ev env rho r l KDone
      phi_after_addr heap_final v_final HAfterAddr)
    as (phi_val_tail & HValWithKont & HTraceAfterAddr).
  destruct
    (NSteps_to_NStepsN
      (StEval heap_addr env rho ev
        (KAssignVal r_static (VLoc r l) KDone))
      phi_val_tail
      (StDone heap_final v_final)
      HValWithKont)
    as (n_val & HValWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_val
      (StEval heap_addr env rho ev
        (KAssignVal r_static (VLoc r l) KDone))
      phi_val_tail
      heap_final
      v_final
      HValWithKontN
      (NInitialState heap_addr env rho ev)
      (KAssignVal r_static (VLoc r l) KDone)
      eq_refl)
    as (phi_val & heap_val & v & phi_after_val &
      HVal & HAfterVal & HTraceVal).
  destruct
    (KAssignVal_terminal_write_result
      heap_val v r_static r l phi_after_val heap_final v_final
      HAfterVal)
    as (HHeap & HUnit & HTraceAfterVal).
  exists phi_addr, phi_val, heap_addr, heap_val, r, l, v.
  repeat split; try assumption.
  rewrite HTraceStart, HTraceAddr, HTraceAfterAddr, HTraceVal.
  rewrite HTraceAfterVal.
  reflexivity.
Qed.

Theorem EAssign_counted_decomposition :
  EAssignCountedDecompositionGoal.
Proof.
  unfold EAssignCountedDecompositionGoal.
  intros n heap env rho r_static ea ev phi heap_final v_final HSteps.
  destruct
    (EAssign_terminal_first_step_N
      n heap env rho r_static ea ev phi heap_final v_final HSteps)
    as (n_addr_tail & phi_tail & HnStart & HAddrWithKont &
      HTraceStart).
  destruct
    (NStepsN_append_kont_terminal_split_counted
      n_addr_tail
      (StEval heap env rho ea
        (KAssignLoc r_static ev env rho KDone))
      phi_tail
      heap_final
      v_final
      HAddrWithKont
      (NInitialState heap env rho ea)
      (KAssignLoc r_static ev env rho KDone)
      eq_refl)
    as (n_addr & n_after_addr & phi_addr & heap_addr & v_addr &
      phi_after_addr & HAddr & HAfterAddr & HCountAddr &
      HTraceAddr).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KAssignLoc_terminal_value_is_loc
        heap_addr v_addr r_static ev env rho KDone
        phi_after_addr heap_final v_final
        (NStepsN_to_NSteps
          n_after_addr
          (StReturn heap_addr v_addr
            (KAssignLoc r_static ev env rho KDone))
          phi_after_addr
          (StDone heap_final v_final)
          HAfterAddr))
      as (r & l & HLoc).
    subst v_addr.
    destruct
      (KAssignLoc_loc_terminal_first_step_N
        n_after_addr heap_addr r_static ev env rho r l KDone
        phi_after_addr heap_final v_final HAfterAddr)
      as (n_val_tail & phi_val_tail & HCountAfterAddr &
        HValWithKont & HTraceAfterAddr).
    destruct
      (NStepsN_append_kont_terminal_split_counted
        n_val_tail
        (StEval heap_addr env rho ev
          (KAssignVal r_static (VLoc r l) KDone))
        phi_val_tail
        heap_final
        v_final
        HValWithKont
        (NInitialState heap_addr env rho ev)
        (KAssignVal r_static (VLoc r l) KDone)
        eq_refl)
      as (n_val & n_after_val & phi_val & heap_val & v &
        phi_after_val & HVal & HAfterVal & HCountVal &
        HTraceVal).
    + intros heap_done v_done HDone. inversion HDone.
    + destruct
        (KAssignVal_terminal_write_result
          heap_val v r_static r l phi_after_val heap_final v_final
          (NStepsN_to_NSteps
            n_after_val
            (StReturn heap_val v
              (KAssignVal r_static (VLoc r l) KDone))
            phi_after_val
            (StDone heap_final v_final)
            HAfterVal))
        as (HHeap & HUnit & HTraceAfterVal).
      assert (HAfterValPositive : 0 < n_after_val).
      { destruct n_after_val; [inversion HAfterVal | lia]. }
      exists n_addr, n_val, phi_addr, phi_val,
        heap_addr, heap_val, r, l, v.
      repeat split; try assumption.
      * rewrite HTraceStart, HTraceAddr, HTraceAfterAddr, HTraceVal.
        rewrite HTraceAfterVal.
        reflexivity.
      * lia.
      * lia.
Qed.

Lemma trace_covered_single_alloc_abs :
  forall r l,
    TraceCoveredBySummary [DAlloc r l] (SummarySet [CAllocAbs r]).
Proof.
  intros r l da HIn.
  destruct HIn as [HIn | HIn]; [subst da | contradiction].
  exists (CAllocAbs r).
  split; [simpl; auto | constructor].
Qed.

Lemma trace_covered_single_read_abs :
  forall r l,
    TraceCoveredBySummary [DRead r l] (SummarySet [CReadAbs r]).
Proof.
  intros r l da HIn.
  destruct HIn as [HIn | HIn]; [subst da | contradiction].
  exists (CReadAbs r).
  split; [simpl; auto | constructor].
Qed.

Lemma trace_covered_single_write_abs :
  forall r l,
    TraceCoveredBySummary [DWrite r l] (SummarySet [CWriteAbs r]).
Proof.
  intros r l da HIn.
  destruct HIn as [HIn | HIn]; [subst da | contradiction].
  exists (CWriteAbs r).
  split; [simpl; auto | constructor].
Qed.

Lemma NCheckedTcExp_deref_child_ref_from_deref :
  forall gamma omega r e ty eff,
    NCheckedTcExp gamma omega (EDeref r e) ty eff ->
    exists ty_cell eff_child,
      NCheckedTcExp gamma omega e
        (TyRef (region_expr_to_type r) ty_cell) eff_child.
Proof.
  intros gamma omega r e ty eff HChecked.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HShape; subst.
  match goal with
  | HChild : NCheckedTcExp gamma omega e
      (TyRef (region_expr_to_type r) ?ty_cell) ?eff_child |- _ =>
      exists ty_cell, eff_child; exact HChild
  end.
Qed.

Lemma NCheckedTcExp_assign_children_from_assign :
  forall gamma omega r ea ev ty eff,
    NCheckedTcExp gamma omega (EAssign r ea ev) ty eff ->
    exists ty_cell eff_addr eff_val,
      NCheckedTcExp gamma omega ea
        (TyRef (region_expr_to_type r) ty_cell) eff_addr /\
      NCheckedTcExp gamma omega ev ty_cell eff_val.
Proof.
  intros gamma omega r ea ev ty eff HChecked.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HShape; subst.
  match goal with
  | HAddr : NCheckedTcExp gamma omega ea
      (TyRef (region_expr_to_type r) ?ty_cell) ?eff_addr,
    HVal : NCheckedTcExp gamma omega ev ?ty_cell ?eff_val |- _ =>
      exists ty_cell, eff_addr, eff_val; split; assumption
  end.
Qed.

Lemma NStoreResolvedValShape_loc_ref_region :
  forall store rho r_static ty ty_res r l,
    NResolveTy rho (TyRef (region_expr_to_type r_static) ty) ty_res ->
    NStoreResolvedValShape store (VLoc r l) ty_res ->
    eval_region rho r_static = Some r.
Proof.
  intros store rho r_static ty ty_res r l HResolve HVal.
  inversion HVal; subst.
  rewrite <- eval_region_type_region_expr_to_type.
  eapply NResolveTy_ref_same_region.
  exact HResolve.
Qed.

Lemma NCBT_Ref_components :
  forall gamma omega r e eff,
    NCheckedBackTriangle gamma omega
      (ERef r e) (EConcat eff (EAllocAbs r)) ->
    exists ty static ty_ref eff_ref,
      NCheckedTcExp gamma omega e ty static /\
      NCheckedTcExp gamma omega (ERef r e) ty_ref eff_ref /\
      NCheckedBackTriangle gamma omega e eff.
Proof.
  intros gamma omega r e eff HBack.
  inversion HBack; subst; try discriminate.
  exists ty, static, ty_ref, eff_ref.
  split; [exact H4 |].
  split; [exact H5 |].
  exact H6.
Qed.

Theorem ERef_checked_store_context_case_from_below :
  forall n gamma omega heap env rho r e eff
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega
      (ERef r e) (EConcat eff (EAllocAbs r)) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (ERef r e) phi heap_final v_final ->
    SummaryEvaluation heap env rho (EConcat eff (EAllocAbs r))
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho r e eff
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext _HComputationTraceSound HComp HSummary.
  destruct
    (NCBT_Ref_components gamma omega r e eff HBack)
    as (_ty & _static & _ty_ref & _eff_ref &
      _HCheckedExpr & _HCheckedRef & HBackExpr).
  unfold CountedComputationEvaluation in HComp.
  destruct
    (ERef_counted_decomposition
      n heap env rho r e phi heap_final v_final HComp)
    as (n_e & phi_e & heap_e & v & r_val & l & HRgn &
      HExpr & _HAlloc & HLoc & HTrace & HCountExpr).
  subst v_final phi.
  unfold SummaryEvaluation in HSummary.
  destruct
    (EConcat_decomposition
      heap env rho eff (EAllocAbs r)
      phi_summary heap_summary theta HSummary)
    as (phi_summary_e & phi_summary_alloc & theta_e & theta_alloc &
      heap_summary_e & heap_summary_alloc & HSummaryExpr &
      HSummaryAlloc & HTheta & _HHeapSummary & _HTraceSummary).
  destruct
    (EAllocAbs_terminal_summary
      heap_summary_e env rho r phi_summary_alloc
      heap_summary_alloc theta_alloc HSummaryAlloc)
    as (r_summary & HRgnSummary & _HHeapAlloc & HThetaAlloc &
      _HTraceAlloc).
  rewrite HRgn in HRgnSummary.
  inversion HRgnSummary; subst r_summary.
  subst theta_alloc theta.
  assert (HCoveredExpr : TraceCoveredBySummary phi_e theta_e).
  {
    eapply
      (HBelow n_e gamma omega heap env rho e eff
        phi_e heap_e v phi_summary_e heap_summary_e theta_e).
    - exact HCountExpr.
    - exact HBackExpr.
    - exact HContext.
    - unfold CountedComputationEvaluation. exact HExpr.
    - unfold SummaryEvaluation. exact HSummaryExpr.
  }
  eapply trace_covered_app_summary_union; eauto.
  apply trace_covered_single_alloc_abs.
Qed.

Lemma NCBT_Deref_components :
  forall gamma omega r e eff,
    NCheckedBackTriangle gamma omega
      (EDeref r e) (EConcat eff (EReadAbs r)) ->
    exists ty static ty_deref eff_deref,
      NCheckedTcExp gamma omega e ty static /\
      NCheckedTcExp gamma omega (EDeref r e) ty_deref eff_deref /\
      NCheckedBackTriangle gamma omega e eff.
Proof.
  intros gamma omega r e eff HBack.
  inversion HBack; subst; try discriminate.
  exists ty, static, ty_deref, eff_deref.
  split; [exact H4 |].
  split; [exact H5 |].
  exact H6.
Qed.

Theorem EDeref_checked_store_context_case_from_below :
  forall n gamma omega heap env rho r e eff
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EDeref r e) (EConcat eff (EReadAbs r)) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EDeref r e) phi heap_final v_final ->
    SummaryEvaluation heap env rho (EConcat eff (EReadAbs r))
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho r e eff
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext _HComputationTraceSound HComp HSummary.
  destruct
    (NCBT_Deref_components gamma omega r e eff HBack)
    as (_ty & _static & ty_deref & eff_deref &
      _HCheckedExpr & HCheckedDeref & HBackExpr).
  destruct
    (NCheckedTcExp_deref_child_ref_from_deref
      gamma omega r e ty_deref eff_deref HCheckedDeref)
    as (ty_cell & eff_child & HCheckedChildRef).
  unfold CountedComputationEvaluation in HComp.
  destruct
    (EDeref_counted_decomposition
      n heap env rho r e phi heap_final v_final HComp)
    as (n_e & phi_e & heap_e & r_loc & l & HExpr &
      _HLookup & HHeapFinal & HTrace & HCountExpr).
  subst heap_final phi.
  assert (HExprForShape := HExpr).
  destruct
    (checked_store_counted_computation_store_value_shape_resolved
      n_e gamma omega heap env rho e
      (TyRef (region_expr_to_type r) ty_cell) eff_child
      phi_e heap_e (VLoc r_loc l) HContext HCheckedChildRef
      HExprForShape)
    as (store_e & ty_res & HResolveChild & _HBoundedExpr &
      _HHeapExpr & HValLoc).
  pose proof
    (NStoreResolvedValShape_loc_ref_region
      store_e rho r ty_cell ty_res r_loc l
      HResolveChild HValLoc)
    as HRegionLoc.
  unfold SummaryEvaluation in HSummary.
  destruct
    (EConcat_decomposition
      heap env rho eff (EReadAbs r)
      phi_summary heap_summary theta HSummary)
    as (phi_summary_e & phi_summary_read & theta_e & theta_read &
      heap_summary_e & heap_summary_read & HSummaryExpr &
      HSummaryRead & HTheta & _HHeapSummary & _HTraceSummary).
  destruct
    (EReadAbs_terminal_summary
      heap_summary_e env rho r phi_summary_read
      heap_summary_read theta_read HSummaryRead)
    as (r_summary & HRgnSummary & _HHeapRead & HThetaRead &
      _HTraceRead).
  rewrite HRegionLoc in HRgnSummary.
  inversion HRgnSummary; subst r_summary.
  subst theta_read theta.
  assert (HCoveredExpr : TraceCoveredBySummary phi_e theta_e).
  {
    eapply
      (HBelow n_e gamma omega heap env rho e eff
        phi_e heap_e (VLoc r_loc l)
        phi_summary_e heap_summary_e theta_e).
    - exact HCountExpr.
    - exact HBackExpr.
    - exact HContext.
    - unfold CountedComputationEvaluation. exact HExpr.
    - unfold SummaryEvaluation. exact HSummaryExpr.
  }
  eapply trace_covered_app_summary_union; eauto.
  apply trace_covered_single_read_abs.
Qed.

Lemma NCBT_Assign_components :
  forall gamma omega r e1 e2 eff1 eff2,
    NCheckedBackTriangle gamma omega
      (EAssign r e1 e2) (EConcat eff1 (EConcat eff2 (EWriteAbs r))) ->
    exists ty static ty_assign eff_assign,
      NCheckedTcExp gamma omega e1 ty static /\
      NCheckedTcExp gamma omega (EAssign r e1 e2) ty_assign eff_assign /\
      static_heap_neutral static /\
      NCheckedBackTriangle gamma omega e1 eff1 /\
      NCheckedBackTriangle gamma omega e2 eff2.
Proof.
  intros gamma omega r e1 e2 eff1 eff2 HBack.
  inversion HBack; subst; try discriminate.
  exists ty, static, ty_assign, eff_assign.
  split; [exact H6 |].
  split; [exact H7 |].
  split; [exact H8 |].
  split; assumption.
Qed.

Theorem EAssign_checked_store_context_case_from_below :
  forall n gamma omega heap env rho r e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega
      (EAssign r e1 e2) (EConcat eff1 (EConcat eff2 (EWriteAbs r))) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EAssign r e1 e2) phi heap_final v_final ->
    SummaryEvaluation heap env rho
      (EConcat eff1 (EConcat eff2 (EWriteAbs r)))
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho r e1 e2 eff1 eff2
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext HComputationTraceSound HComp HSummary.
  destruct
    (NCBT_Assign_components gamma omega r e1 e2 eff1 eff2 HBack)
    as (ty_addr & static_addr & ty_assign & eff_assign &
      HCheckedAddr & HCheckedAssign & HNeutralAddr &
      HBackAddr & HBackVal).
  destruct
    (NCheckedTcExp_assign_children_from_assign
      gamma omega r e1 e2 ty_assign eff_assign HCheckedAssign)
    as (ty_cell & eff_addr_ref & _eff_val &
      HCheckedAddrRef & _HCheckedVal).
  unfold CountedComputationEvaluation in HComp.
  destruct
    (EAssign_counted_decomposition
      n heap env rho r e1 e2 phi heap_final v_final HComp)
    as (n_addr & n_val & phi_addr & phi_val &
      heap_addr & heap_val & r_loc & l & v &
      HAddr & HVal & HHeapFinal & HUnit & HTrace &
      HCountAddr & HCountVal).
  subst heap_final v_final phi.
  destruct
    (checked_store_counted_computation_heap_neutral
      n_addr gamma omega heap env rho e1 ty_addr static_addr
      phi_addr heap_addr (VLoc r_loc l)
      HContext HComputationTraceSound HCheckedAddr HNeutralAddr)
    as (HHeapAddr & _HAddrNeutralTrace).
  {
    unfold CountedComputationEvaluation.
    exact HAddr.
  }
  subst heap_addr.
  assert (HAddrForShape := HAddr).
  destruct
    (checked_store_counted_computation_store_value_shape_resolved
      n_addr gamma omega heap env rho e1
      (TyRef (region_expr_to_type r) ty_cell) eff_addr_ref
      phi_addr heap (VLoc r_loc l) HContext HCheckedAddrRef
      HAddrForShape)
    as (store_addr & ty_res_addr & HResolveAddr & _HBoundedAddr &
      _HHeapAddr & HValLoc).
  pose proof
    (NStoreResolvedValShape_loc_ref_region
      store_addr rho r ty_cell ty_res_addr r_loc l
      HResolveAddr HValLoc)
    as HRegionLoc.
  unfold SummaryEvaluation in HSummary.
  destruct
    (EConcat_decomposition
      heap env rho eff1 (EConcat eff2 (EWriteAbs r))
      phi_summary heap_summary theta HSummary)
    as (phi_summary_addr & phi_summary_rest &
      theta_addr & theta_rest & heap_summary_addr &
      heap_summary_rest & HSummaryAddr & HSummaryRest &
      HTheta & _HHeapSummary & _HTraceSummary).
  destruct
    (NCheckedBackTriangle_summary_checked_heap_neutral
      gamma omega e1 eff1 HBackAddr)
    as (eff_summary_addr & HCheckedSummaryAddr &
      HNeutralSummaryAddr).
  destruct
    (NSteps_to_NStepsN
      (NInitialState heap env rho eff1)
      phi_summary_addr
      (StDone heap_summary_addr (VSummary theta_addr))
      HSummaryAddr)
    as (n_summary_addr & HSummaryAddrN).
  destruct
    (checked_store_counted_computation_heap_neutral
      n_summary_addr gamma omega heap env rho eff1
      TyEffect eff_summary_addr
      phi_summary_addr heap_summary_addr (VSummary theta_addr)
      HContext HComputationTraceSound HCheckedSummaryAddr
      HNeutralSummaryAddr)
    as (HHeapSummaryAddr & _HSummaryAddrNeutralTrace).
  {
    unfold CountedComputationEvaluation.
    exact HSummaryAddrN.
  }
  subst heap_summary_addr.
  destruct
    (EConcat_decomposition
      heap env rho eff2 (EWriteAbs r)
      phi_summary_rest heap_summary_rest theta_rest HSummaryRest)
    as (phi_summary_val & phi_summary_write &
      theta_val & theta_write & heap_summary_val &
      heap_summary_write & HSummaryVal & HSummaryWrite &
      HThetaRest & _HHeapSummaryRest & _HTraceSummaryRest).
  destruct
    (EWriteAbs_terminal_summary
      heap_summary_val env rho r phi_summary_write
      heap_summary_write theta_write HSummaryWrite)
    as (r_summary & HRgnSummary & _HHeapWrite & HThetaWrite &
      _HTraceWrite).
  rewrite HRegionLoc in HRgnSummary.
  inversion HRgnSummary; subst r_summary.
  subst theta_write theta_rest theta.
  assert (HCoveredAddr : TraceCoveredBySummary phi_addr theta_addr).
  {
    eapply
      (HBelow n_addr gamma omega heap env rho e1 eff1
        phi_addr heap (VLoc r_loc l)
        phi_summary_addr heap theta_addr).
    - exact HCountAddr.
    - exact HBackAddr.
    - exact HContext.
    - unfold CountedComputationEvaluation. exact HAddr.
    - unfold SummaryEvaluation. exact HSummaryAddr.
  }
  assert (HCoveredVal : TraceCoveredBySummary phi_val theta_val).
  {
    eapply
      (HBelow n_val gamma omega heap env rho e2 eff2
        phi_val heap_val v
        phi_summary_val heap_summary_val theta_val).
    - exact HCountVal.
    - exact HBackVal.
    - exact HContext.
    - unfold CountedComputationEvaluation. exact HVal.
    - unfold SummaryEvaluation. exact HSummaryVal.
  }
  eapply trace_covered_app_summary_union; eauto.
  eapply trace_covered_app_summary_union; eauto.
  apply trace_covered_single_write_abs.
Qed.
