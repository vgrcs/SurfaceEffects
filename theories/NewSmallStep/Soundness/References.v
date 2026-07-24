From Stdlib Require Import List.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.Continuation.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.Trace.
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
