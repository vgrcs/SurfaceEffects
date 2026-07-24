From Stdlib Require Import List.

Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.Continuation.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.Trace.
Require Import theories.NewSmallStep.Determinism.Terminal.

Import ListNotations.

Lemma ECond_terminal_first_step :
  forall heap env rho e et ef phi heap_final v_final,
    NSteps
      (NInitialState heap env rho (ECond e et ef))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho e (KCond et ef env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap env rho e et ef phi heap_final v_final HSteps.
  remember (NInitialState heap env rho (ECond e et ef))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StEval heap env rho (ECond e et ef) KDone)
        LSilent
        (StEval heap env rho e (KCond et ef env rho KDone))
        label state'
        (StepCond heap env rho e et ef KDone)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KCond_terminal_value_is_bool :
  forall heap v et ef env rho k phi heap_final v_final,
    NSteps
      (StReturn heap v (KCond et ef env rho k))
      phi
      (StDone heap_final v_final) ->
    exists b,
      v = VBool b.
Proof.
  intros heap v et ef env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap v (KCond et ef env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst; eexists; reflexivity.
Qed.

Lemma KCond_bool_terminal_first_step :
  forall heap b et ef env rho k phi heap_final v_final,
    NSteps
      (StReturn heap (VBool b) (KCond et ef env rho k))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho (if b then et else ef) k)
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap b et ef env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap (VBool b) (KCond et ef env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct b.
    + destruct
        (NStep_deterministic
          (StReturn heap (VBool true) (KCond et ef env rho k))
          LSilent
          (StEval heap env rho et k)
          label state'
          (StepCondTrue heap et ef env rho k)
          HStep)
        as [HLabel HState].
      subst label state'.
      exists phi0.
      split; [assumption | reflexivity].
    + destruct
        (NStep_deterministic
          (StReturn heap (VBool false) (KCond et ef env rho k))
          LSilent
          (StEval heap env rho ef k)
          label state'
          (StepCondFalse heap et ef env rho k)
          HStep)
        as [HLabel HState].
      subst label state'.
      exists phi0.
      split; [assumption | reflexivity].
Qed.

Definition ECondDecompositionGoal : Prop :=
  forall heap env rho e et ef phi heap_final v_final,
    NSteps
      (NInitialState heap env rho (ECond e et ef))
      phi
      (StDone heap_final v_final) ->
    exists phi_cond b heap_cond phi_branch,
      NSteps
        (NInitialState heap env rho e)
        phi_cond
        (StDone heap_cond (VBool b)) /\
      NSteps
        (NInitialState heap_cond env rho (if b then et else ef))
        phi_branch
        (StDone heap_final v_final) /\
      phi = phi_cond ++ phi_branch.

Theorem ECond_decomposition :
  ECondDecompositionGoal.
Proof.
  unfold ECondDecompositionGoal.
  intros heap env rho e et ef phi heap_final v_final HSteps.
  destruct
    (ECond_terminal_first_step
      heap env rho e et ef phi heap_final v_final HSteps)
    as (phi_tail & HCondWithKont & HTraceStart).
  destruct
    (NSteps_to_NStepsN
      (StEval heap env rho e (KCond et ef env rho KDone))
      phi_tail
      (StDone heap_final v_final)
      HCondWithKont)
    as (n_cond & HCondWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_cond
      (StEval heap env rho e (KCond et ef env rho KDone))
      phi_tail
      heap_final
      v_final
      HCondWithKontN
      (NInitialState heap env rho e)
      (KCond et ef env rho KDone)
      eq_refl)
    as (phi_cond & heap_cond & v_cond & phi_after_cond &
      HCond & HAfterCond & HTraceCond).
  destruct
    (KCond_terminal_value_is_bool
      heap_cond v_cond et ef env rho KDone
      phi_after_cond heap_final v_final HAfterCond)
    as (b & HBool).
  subst v_cond.
  destruct
    (KCond_bool_terminal_first_step
      heap_cond b et ef env rho KDone
      phi_after_cond heap_final v_final HAfterCond)
    as (phi_branch & HBranch & HTraceAfterCond).
  exists phi_cond, b, heap_cond, phi_branch.
  repeat split; try assumption.
  rewrite HTraceStart, HTraceCond, HTraceAfterCond.
  reflexivity.
Qed.
