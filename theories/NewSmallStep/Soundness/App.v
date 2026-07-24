From Stdlib Require Import List.

Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.Continuation.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.Trace.
Require Import theories.NewSmallStep.Determinism.Terminal.

Import ListNotations.

Lemma EMuApp_terminal_first_step :
  forall heap env rho ef ea phi heap_final v_final,
    NSteps
      (NInitialState heap env rho (EMuApp ef ea))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho ef (KMuAppFun ea env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap env rho ef ea phi heap_final v_final HSteps.
  remember (NInitialState heap env rho (EMuApp ef ea)) as start
    eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StEval heap env rho (EMuApp ef ea) KDone)
        LSilent
        (StEval heap env rho ef (KMuAppFun ea env rho KDone))
        label state'
        (StepMuApp heap env rho ef ea KDone)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma EMuApp_terminal_first_step_N :
  forall n heap env rho ef ea phi heap_final v_final,
    NStepsN n
      (NInitialState heap env rho (EMuApp ef ea))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho ef (KMuAppFun ea env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap env rho ef ea phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (NInitialState heap env rho (EMuApp ef ea))
      LSilent
      (StEval heap env rho ef (KMuAppFun ea env rho KDone))
      phi heap_final v_final
      (StepMuApp heap env rho ef ea KDone)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
Qed.

Lemma EEffApp_terminal_first_step :
  forall heap env rho ef ea phi heap_final v_final,
    NSteps
      (NInitialState heap env rho (EEffApp ef ea))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho ef (KEffAppFun ea env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap env rho ef ea phi heap_final v_final HSteps.
  remember (NInitialState heap env rho (EEffApp ef ea)) as start
    eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StEval heap env rho (EEffApp ef ea) KDone)
        LSilent
        (StEval heap env rho ef (KEffAppFun ea env rho KDone))
        label state'
        (StepEffApp heap env rho ef ea KDone)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma EEffApp_terminal_first_step_N :
  forall n heap env rho ef ea phi heap_final v_final,
    NStepsN n
      (NInitialState heap env rho (EEffApp ef ea))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho ef (KEffAppFun ea env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap env rho ef ea phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (NInitialState heap env rho (EEffApp ef ea))
      LSilent
      (StEval heap env rho ef (KEffAppFun ea env rho KDone))
      phi heap_final v_final
      (StepEffApp heap env rho ef ea KDone)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
Qed.

Lemma KMuAppFun_closure_terminal_first_step :
  forall heap env rho ea k closure_env closure_rho f x ec ee
    phi heap_final v_final,
    NSteps
      (StReturn heap (VClosure closure_env closure_rho f x ec ee)
        (KMuAppFun ea env rho k))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho ea
          (KMuAppArg closure_env closure_rho f x ec ee k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap env rho ea k closure_env closure_rho f x ec ee
    phi heap_final v_final HSteps.
  remember
    (StReturn heap (VClosure closure_env closure_rho f x ec ee)
      (KMuAppFun ea env rho k)) as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StReturn heap (VClosure closure_env closure_rho f x ec ee)
          (KMuAppFun ea env rho k))
        LSilent
        (StEval heap env rho ea
          (KMuAppArg closure_env closure_rho f x ec ee k))
        label state'
        (StepMuAppFun heap env rho ea k closure_env closure_rho f x ec ee)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KMuAppFun_closure_terminal_first_step_N :
  forall n heap env rho ea k closure_env closure_rho f x ec ee
    phi heap_final v_final,
    NStepsN n
      (StReturn heap (VClosure closure_env closure_rho f x ec ee)
        (KMuAppFun ea env rho k))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho ea
          (KMuAppArg closure_env closure_rho f x ec ee k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap env rho ea k closure_env closure_rho f x ec ee
    phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (StReturn heap (VClosure closure_env closure_rho f x ec ee)
        (KMuAppFun ea env rho k))
      LSilent
      (StEval heap env rho ea
        (KMuAppArg closure_env closure_rho f x ec ee k))
      phi heap_final v_final
      (StepMuAppFun heap env rho ea k closure_env closure_rho f x ec ee)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
Qed.

Lemma KEffAppFun_closure_terminal_first_step :
  forall heap env rho ea k closure_env closure_rho f x ec ee
    phi heap_final v_final,
    NSteps
      (StReturn heap (VClosure closure_env closure_rho f x ec ee)
        (KEffAppFun ea env rho k))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap env rho ea
          (KEffAppArg closure_env closure_rho f x ec ee k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap env rho ea k closure_env closure_rho f x ec ee
    phi heap_final v_final HSteps.
  remember
    (StReturn heap (VClosure closure_env closure_rho f x ec ee)
      (KEffAppFun ea env rho k)) as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StReturn heap (VClosure closure_env closure_rho f x ec ee)
          (KEffAppFun ea env rho k))
        LSilent
        (StEval heap env rho ea
          (KEffAppArg closure_env closure_rho f x ec ee k))
        label state'
        (StepEffAppFun heap env rho ea k closure_env closure_rho f x ec ee)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KEffAppFun_closure_terminal_first_step_N :
  forall n heap env rho ea k closure_env closure_rho f x ec ee
    phi heap_final v_final,
    NStepsN n
      (StReturn heap (VClosure closure_env closure_rho f x ec ee)
        (KEffAppFun ea env rho k))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho ea
          (KEffAppArg closure_env closure_rho f x ec ee k))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap env rho ea k closure_env closure_rho f x ec ee
    phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (StReturn heap (VClosure closure_env closure_rho f x ec ee)
        (KEffAppFun ea env rho k))
      LSilent
      (StEval heap env rho ea
        (KEffAppArg closure_env closure_rho f x ec ee k))
      phi heap_final v_final
      (StepEffAppFun heap env rho ea k closure_env closure_rho f x ec ee)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
Qed.

Lemma KMuAppArg_terminal_first_step :
  forall heap v_arg closure_env closure_rho f x ec ee k
    phi heap_final v_final,
    NSteps
      (StReturn heap v_arg
        (KMuAppArg closure_env closure_rho f x ec ee k))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap
          (env_extend x v_arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ec k)
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap v_arg closure_env closure_rho f x ec ee k
    phi heap_final v_final HSteps.
  remember
    (StReturn heap v_arg
      (KMuAppArg closure_env closure_rho f x ec ee k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StReturn heap v_arg
          (KMuAppArg closure_env closure_rho f x ec ee k))
        LSilent
        (StEval heap
          (env_extend x v_arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ec k)
        label state'
        (StepMuAppArg heap v_arg closure_env closure_rho f x ec ee k)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KMuAppArg_terminal_first_step_N :
  forall n heap v_arg closure_env closure_rho f x ec ee k
    phi heap_final v_final,
    NStepsN n
      (StReturn heap v_arg
        (KMuAppArg closure_env closure_rho f x ec ee k))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap
          (env_extend x v_arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ec k)
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap v_arg closure_env closure_rho f x ec ee k
    phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (StReturn heap v_arg
        (KMuAppArg closure_env closure_rho f x ec ee k))
      LSilent
      (StEval heap
        (env_extend x v_arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho ec k)
      phi heap_final v_final
      (StepMuAppArg heap v_arg closure_env closure_rho f x ec ee k)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
Qed.

Lemma KEffAppArg_terminal_first_step :
  forall heap v_arg closure_env closure_rho f x ec ee k
    phi heap_final v_final,
    NSteps
      (StReturn heap v_arg
        (KEffAppArg closure_env closure_rho f x ec ee k))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      NSteps
        (StEval heap
          (env_extend x v_arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ee k)
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros heap v_arg closure_env closure_rho f x ec ee k
    phi heap_final v_final HSteps.
  remember
    (StReturn heap v_arg
      (KEffAppArg closure_env closure_rho f x ec ee k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    destruct
      (NStep_deterministic
        (StReturn heap v_arg
          (KEffAppArg closure_env closure_rho f x ec ee k))
        LSilent
        (StEval heap
          (env_extend x v_arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ee k)
        label state'
        (StepEffAppArg heap v_arg closure_env closure_rho f x ec ee k)
        HStep)
      as [HLabel HState].
    subst label state'.
    exists phi0.
    split; [assumption | reflexivity].
Qed.

Lemma KEffAppArg_terminal_first_step_N :
  forall n heap v_arg closure_env closure_rho f x ec ee k
    phi heap_final v_final,
    NStepsN n
      (StReturn heap v_arg
        (KEffAppArg closure_env closure_rho f x ec ee k))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap
          (env_extend x v_arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ee k)
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap v_arg closure_env closure_rho f x ec ee k
    phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (StReturn heap v_arg
        (KEffAppArg closure_env closure_rho f x ec ee k))
      LSilent
      (StEval heap
        (env_extend x v_arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho ee k)
      phi heap_final v_final
      (StepEffAppArg heap v_arg closure_env closure_rho f x ec ee k)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
Qed.

Lemma KMuAppFun_terminal_value_is_closure :
  forall heap v ea env rho k phi heap_final v_final,
    NSteps
      (StReturn heap v (KMuAppFun ea env rho k))
      phi
      (StDone heap_final v_final) ->
    exists closure_env closure_rho f x ec ee,
      v = VClosure closure_env closure_rho f x ec ee.
Proof.
  intros heap v ea env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap v (KMuAppFun ea env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    repeat eexists.
Qed.

Lemma KEffAppFun_terminal_value_is_closure :
  forall heap v ea env rho k phi heap_final v_final,
    NSteps
      (StReturn heap v (KEffAppFun ea env rho k))
      phi
      (StDone heap_final v_final) ->
    exists closure_env closure_rho f x ec ee,
      v = VClosure closure_env closure_rho f x ec ee.
Proof.
  intros heap v ea env rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap v (KEffAppFun ea env rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    repeat eexists.
Qed.

Definition EMuAppDecompositionGoal : Prop :=
  forall heap env rho ef ea phi heap_final v_final,
    NSteps
      (NInitialState heap env rho (EMuApp ef ea))
      phi
      (StDone heap_final v_final) ->
    exists phi_fun phi_arg phi_body
      closure_env closure_rho f x ec ee arg heap_arg,
    exists heap_fun,
      NSteps
        (NInitialState heap env rho ef)
        phi_fun
        (StDone heap_fun (VClosure closure_env closure_rho f x ec ee)) /\
      NSteps
        (NInitialState heap_fun env rho ea)
        phi_arg
        (StDone heap_arg arg) /\
      NSteps
        (NInitialState heap_arg
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ec)
        phi_body
        (StDone heap_final v_final).

Theorem EMuApp_decomposition :
  EMuAppDecompositionGoal.
Proof.
  unfold EMuAppDecompositionGoal.
  intros heap env rho ef ea phi heap_final v_final HSteps.
  destruct
    (EMuApp_terminal_first_step
      heap env rho ef ea phi heap_final v_final HSteps)
    as (phi_fun_tail & HFunWithKont & _).
  destruct
    (NSteps_to_NStepsN
      (StEval heap env rho ef (KMuAppFun ea env rho KDone))
      phi_fun_tail
      (StDone heap_final v_final)
      HFunWithKont)
    as (n_fun & HFunWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_fun
      (StEval heap env rho ef (KMuAppFun ea env rho KDone))
      phi_fun_tail
      heap_final v_final
      HFunWithKontN
      (NInitialState heap env rho ef)
      (KMuAppFun ea env rho KDone)
      eq_refl)
    as (phi_fun & heap_fun & v_fun & phi_after_fun &
      HFun & HAfterFun & _).
  destruct
    (KMuAppFun_terminal_value_is_closure
      heap_fun v_fun ea env rho KDone
      phi_after_fun heap_final v_final HAfterFun)
    as (closure_env & closure_rho & f & x & ec & ee & HClosure).
  subst v_fun.
  destruct
    (KMuAppFun_closure_terminal_first_step
      heap_fun env rho ea KDone closure_env closure_rho f x ec ee
      phi_after_fun heap_final v_final HAfterFun)
    as (phi_arg_tail & HArgWithKont & _).
  destruct
    (NSteps_to_NStepsN
      (StEval heap_fun env rho ea
        (KMuAppArg closure_env closure_rho f x ec ee KDone))
      phi_arg_tail
      (StDone heap_final v_final)
      HArgWithKont)
    as (n_arg & HArgWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_arg
      (StEval heap_fun env rho ea
        (KMuAppArg closure_env closure_rho f x ec ee KDone))
      phi_arg_tail
      heap_final v_final
      HArgWithKontN
      (NInitialState heap_fun env rho ea)
      (KMuAppArg closure_env closure_rho f x ec ee KDone)
      eq_refl)
    as (phi_arg & heap_arg & arg & phi_after_arg &
      HArg & HAfterArg & _).
  destruct
    (KMuAppArg_terminal_first_step
      heap_arg arg closure_env closure_rho f x ec ee KDone
      phi_after_arg heap_final v_final HAfterArg)
    as (phi_body & HBody & _).
  exists phi_fun, phi_arg, phi_body, closure_env, closure_rho,
    f, x, ec, ee, arg, heap_arg, heap_fun.
  repeat split; assumption.
Qed.

Definition EEffAppDecompositionGoal : Prop :=
  forall heap env rho ef ea phi heap_final theta,
    NSteps
      (NInitialState heap env rho (EEffApp ef ea))
      phi
      (StDone heap_final (VSummary theta)) ->
    exists phi_fun phi_arg phi_summary
      closure_env closure_rho f x ec ee arg heap_arg,
    exists heap_fun,
      NSteps
        (NInitialState heap env rho ef)
        phi_fun
        (StDone heap_fun (VClosure closure_env closure_rho f x ec ee)) /\
      NSteps
        (NInitialState heap_fun env rho ea)
        phi_arg
        (StDone heap_arg arg) /\
      NSteps
        (NInitialState heap_arg
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ee)
        phi_summary
        (StDone heap_final (VSummary theta)).

Theorem EEffApp_decomposition :
  EEffAppDecompositionGoal.
Proof.
  unfold EEffAppDecompositionGoal.
  intros heap env rho ef ea phi heap_final theta HSteps.
  destruct
    (EEffApp_terminal_first_step
      heap env rho ef ea phi heap_final (VSummary theta) HSteps)
    as (phi_fun_tail & HFunWithKont & _).
  destruct
    (NSteps_to_NStepsN
      (StEval heap env rho ef (KEffAppFun ea env rho KDone))
      phi_fun_tail
      (StDone heap_final (VSummary theta))
      HFunWithKont)
    as (n_fun & HFunWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_fun
      (StEval heap env rho ef (KEffAppFun ea env rho KDone))
      phi_fun_tail
      heap_final (VSummary theta)
      HFunWithKontN
      (NInitialState heap env rho ef)
      (KEffAppFun ea env rho KDone)
      eq_refl)
    as (phi_fun & heap_fun & v_fun & phi_after_fun &
      HFun & HAfterFun & _).
  destruct
    (KEffAppFun_terminal_value_is_closure
      heap_fun v_fun ea env rho KDone
      phi_after_fun heap_final (VSummary theta) HAfterFun)
    as (closure_env & closure_rho & f & x & ec & ee & HClosure).
  subst v_fun.
  destruct
    (KEffAppFun_closure_terminal_first_step
      heap_fun env rho ea KDone closure_env closure_rho f x ec ee
      phi_after_fun heap_final (VSummary theta) HAfterFun)
    as (phi_arg_tail & HArgWithKont & _).
  destruct
    (NSteps_to_NStepsN
      (StEval heap_fun env rho ea
        (KEffAppArg closure_env closure_rho f x ec ee KDone))
      phi_arg_tail
      (StDone heap_final (VSummary theta))
      HArgWithKont)
    as (n_arg & HArgWithKontN).
  destruct
    (NStepsN_append_kont_terminal_split
      n_arg
      (StEval heap_fun env rho ea
        (KEffAppArg closure_env closure_rho f x ec ee KDone))
      phi_arg_tail
      heap_final (VSummary theta)
      HArgWithKontN
      (NInitialState heap_fun env rho ea)
      (KEffAppArg closure_env closure_rho f x ec ee KDone)
      eq_refl)
    as (phi_arg & heap_arg & arg & phi_after_arg &
      HArg & HAfterArg & _).
  destruct
    (KEffAppArg_terminal_first_step
      heap_arg arg closure_env closure_rho f x ec ee KDone
      phi_after_arg heap_final (VSummary theta) HAfterArg)
    as (phi_summary & HSummary & _).
  exists phi_fun, phi_arg, phi_summary, closure_env, closure_rho,
    f, x, ec, ee, arg, heap_arg, heap_fun.
  repeat split; assumption.
Qed.
