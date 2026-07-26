From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Program.Equality.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.Continuation.
Require Import theories.NewSmallStep.Runtime.HeapNeutral.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.RegularStateShape.
Require Import theories.NewSmallStep.Runtime.Trace.
Require Import theories.NewSmallStep.Runtime.Typing.
Require Import theories.NewSmallStep.Soundness.BackTriangle.
Require Import theories.NewSmallStep.Soundness.Correctness.
Require Import theories.NewSmallStep.Determinism.Terminal.
Require Import theories.NewSmallStep.Typing.Judgments.
Require Import theories.NewSmallStep.Typing.Regularity.
Require Import theories.NewSmallStep.Typing.Resolve.
Require Import theories.NewSmallStep.Typing.Types.

Import ListNotations.

Lemma NCBT_App_components :
  forall gamma omega ef ea,
    NCheckedBackTriangle gamma omega
      (EMuApp ef ea) (EEffApp ef ea) ->
    exists ty_mu eff_mu eff_eff ty_ef ty_ea eff_ef eff_ea,
      NCheckedTcExp gamma omega (EMuApp ef ea) ty_mu eff_mu /\
      NCheckedTcExp gamma omega (EEffApp ef ea) TyEffect eff_eff /\
      NCheckedTcExp gamma omega ef ty_ef eff_ef /\
      NCheckedTcExp gamma omega ea ty_ea eff_ea /\
      static_heap_neutral eff_eff /\
      static_heap_neutral eff_ef /\
      static_heap_neutral eff_ea /\
      NCheckedBackTriangle gamma omega ef (EEffApp ef ea) /\
      NCheckedBackTriangle gamma omega ea (EEffApp ef ea).
Proof.
  intros gamma omega ef ea HBack.
  inversion HBack; subst; try discriminate.
  exists ty_mu, eff_mu, eff_eff, ty_ef, ty_ea, eff_ef, eff_ea.
  split; [exact H1 |].
  split; [exact H2 |].
  split; [exact H3 |].
  split; [exact H4 |].
  split; [exact H5 |].
  split; [exact H6 |].
  split; [exact H7 |].
  split; [exact H10 | exact H11].
Qed.

Lemma NCheckedTcExp_EEffApp_inv :
  forall gamma omega ef ea eff,
    NCheckedTcExp gamma omega (EEffApp ef ea) TyEffect eff ->
    exists ty_arg ty_body eff_body eff_summary eff_f eff_a,
      NCheckedTcExp gamma omega ef
        (TyArrow ty_arg eff_body ty_body eff_summary) eff_f /\
      NCheckedTcExp gamma omega ea ty_arg eff_a /\
      eff = static_union eff_f (static_union eff_a eff_summary).
Proof.
  intros gamma omega ef ea eff HChecked.
  inversion HChecked as
    [gamma0 omega0 e0 ty0 eff0
      _ _ _ _ _ HShape];
    subst; clear HChecked.
  inversion HShape; subst.
  exists ty_arg, ty_body, eff_body, eff_summary, eff_f, eff_a.
  split; [assumption |].
  split; [assumption |].
  reflexivity.
Qed.

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
        (StDone heap_final v_final) /\
      phi = phi_fun ++ phi_arg ++ phi_body.

Theorem EMuApp_decomposition :
  EMuAppDecompositionGoal.
Proof.
  unfold EMuAppDecompositionGoal.
  intros heap env rho ef ea phi heap_final v_final HSteps.
  destruct
    (EMuApp_terminal_first_step
      heap env rho ef ea phi heap_final v_final HSteps)
    as (phi_fun_tail & HFunWithKont & HTraceStart).
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
      HFun & HAfterFun & HTraceFun).
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
    as (phi_arg_tail & HArgWithKont & HTraceAfterFun).
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
      HArg & HAfterArg & HTraceArg).
  destruct
    (KMuAppArg_terminal_first_step
      heap_arg arg closure_env closure_rho f x ec ee KDone
      phi_after_arg heap_final v_final HAfterArg)
    as (phi_body & HBody & HTraceAfterArg).
  exists phi_fun, phi_arg, phi_body, closure_env, closure_rho,
    f, x, ec, ee, arg, heap_arg, heap_fun.
  repeat split; try assumption.
  rewrite HTraceStart, HTraceFun, HTraceAfterFun, HTraceArg,
    HTraceAfterArg.
  reflexivity.
Qed.

Definition EMuAppCountedDecompositionGoal : Prop :=
  forall n heap env rho ef ea phi heap_final v_final,
    NStepsN n
      (NInitialState heap env rho (EMuApp ef ea))
      phi
      (StDone heap_final v_final) ->
    exists n_fun n_arg n_body
      phi_fun phi_arg phi_body
      closure_env closure_rho f x ec ee arg heap_arg,
    exists heap_fun,
      NStepsN n_fun
        (NInitialState heap env rho ef)
        phi_fun
        (StDone heap_fun (VClosure closure_env closure_rho f x ec ee)) /\
      NStepsN n_arg
        (NInitialState heap_fun env rho ea)
        phi_arg
        (StDone heap_arg arg) /\
      NStepsN n_body
        (NInitialState heap_arg
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ec)
        phi_body
        (StDone heap_final v_final) /\
      n_fun < n /\
      n_arg < n /\
      n_body < n /\
      phi = phi_fun ++ phi_arg ++ phi_body.

Theorem EMuApp_counted_decomposition :
  EMuAppCountedDecompositionGoal.
Proof.
  unfold EMuAppCountedDecompositionGoal.
  intros n heap env rho ef ea phi heap_final v_final HSteps.
  destruct
    (EMuApp_terminal_first_step_N
      n heap env rho ef ea phi heap_final v_final HSteps)
    as (n_fun_tail & phi_fun_tail & HnStart &
      HFunWithKont & HTraceStart).
  destruct
    (NStepsN_append_kont_terminal_split_counted
      n_fun_tail
      (StEval heap env rho ef (KMuAppFun ea env rho KDone))
      phi_fun_tail
      heap_final v_final
      HFunWithKont
      (NInitialState heap env rho ef)
      (KMuAppFun ea env rho KDone)
      eq_refl)
    as (n_fun & n_after_fun & phi_fun & heap_fun & v_fun &
      phi_after_fun & HFun & HAfterFun & HCountFun & HTraceFun).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KMuAppFun_terminal_value_is_closure
        heap_fun v_fun ea env rho KDone
        phi_after_fun heap_final v_final
        (NStepsN_to_NSteps
          n_after_fun
          (StReturn heap_fun v_fun (KMuAppFun ea env rho KDone))
          phi_after_fun
          (StDone heap_final v_final)
          HAfterFun))
      as (closure_env & closure_rho & f & x & ec & ee & HClosure).
    subst v_fun.
    destruct
      (KMuAppFun_closure_terminal_first_step_N
        n_after_fun heap_fun env rho ea KDone
        closure_env closure_rho f x ec ee
        phi_after_fun heap_final v_final HAfterFun)
      as (n_arg_tail & phi_arg_tail & HCountAfterFun &
        HArgWithKont & HTraceAfterFun).
    destruct
      (NStepsN_append_kont_terminal_split_counted
        n_arg_tail
        (StEval heap_fun env rho ea
          (KMuAppArg closure_env closure_rho f x ec ee KDone))
        phi_arg_tail
        heap_final v_final
        HArgWithKont
        (NInitialState heap_fun env rho ea)
        (KMuAppArg closure_env closure_rho f x ec ee KDone)
        eq_refl)
      as (n_arg & n_after_arg & phi_arg & heap_arg & arg &
        phi_after_arg & HArg & HAfterArg & HCountArg & HTraceArg).
    + intros heap_done v_done HDone. inversion HDone.
    + destruct
        (KMuAppArg_terminal_first_step_N
          n_after_arg heap_arg arg closure_env closure_rho f x ec ee KDone
          phi_after_arg heap_final v_final HAfterArg)
        as (n_body & phi_body & HCountAfterArg &
          HBody & HTraceAfterArg).
      exists n_fun, n_arg, n_body,
        phi_fun, phi_arg, phi_body,
        closure_env, closure_rho, f, x, ec, ee, arg, heap_arg, heap_fun.
      repeat split; try assumption.
      * lia.
      * lia.
      * lia.
      * rewrite HTraceStart, HTraceFun, HTraceAfterFun,
          HTraceArg, HTraceAfterArg.
        reflexivity.
Qed.

Lemma NCBT_RgnApp_components :
  forall gamma omega er r,
    NCheckedBackTriangle gamma omega (ERgnApp er r) EEmpty ->
    exists ty_er eff_er ty_app eff_app,
      NCheckedTcExp gamma omega er ty_er eff_er /\
      NCheckedTcExp gamma omega (ERgnApp er r) ty_app eff_app /\
      NCheckedBackTriangle gamma omega er EEmpty.
Proof.
  intros gamma omega er r HBack.
  dependent destruction HBack.
  exists ty, eff, ty_app, eff_app.
  split; [assumption |].
  split; assumption.
Qed.

Lemma ERgnApp_terminal_first_step_N :
  forall n heap env rho er r phi heap_final v_final,
    NStepsN n
      (NInitialState heap env rho (ERgnApp er r))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap env rho er (KRgnApp r rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap env rho er r phi heap_final v_final HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (NInitialState heap env rho (ERgnApp er r))
      LSilent
      (StEval heap env rho er (KRgnApp r rho KDone))
      phi heap_final v_final
      (StepRgnApp heap env rho er r KDone)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
Qed.

Lemma KRgnApp_terminal_value_is_region_closure :
  forall heap v r arg_rho k phi heap_final v_final,
    NSteps
      (StReturn heap v (KRgnApp r arg_rho k))
      phi
      (StDone heap_final v_final) ->
    exists closure_env closure_rho x e,
      v = VRegionClosure closure_env closure_rho x e.
Proof.
  intros heap v r arg_rho k phi heap_final v_final HSteps.
  remember
    (StReturn heap v (KRgnApp r arg_rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    repeat eexists.
Qed.

Lemma KRgnApp_region_closure_terminal_region :
  forall heap closure_env closure_rho x e r arg_rho k
    phi heap_final v_final,
    NSteps
      (StReturn heap
        (VRegionClosure closure_env closure_rho x e)
        (KRgnApp r arg_rho k))
      phi
      (StDone heap_final v_final) ->
    exists r_val,
      eval_region arg_rho r = Some r_val.
Proof.
  intros heap closure_env closure_rho x e r arg_rho k
    phi heap_final v_final HSteps.
  remember
    (StReturn heap
      (VRegionClosure closure_env closure_rho x e)
      (KRgnApp r arg_rho k))
    as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    eexists. eassumption.
Qed.

Lemma KRgnApp_region_closure_terminal_first_step_N :
  forall n heap closure_env closure_rho x e r arg_rho r_val k
    phi heap_final v_final,
    eval_region arg_rho r = Some r_val ->
    NStepsN n
      (StReturn heap
        (VRegionClosure closure_env closure_rho x e)
        (KRgnApp r arg_rho k))
      phi
      (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      NStepsN n_tail
        (StEval heap closure_env
          (rho_extend x r_val closure_rho)
          e k)
        phi_tail
        (StDone heap_final v_final) /\
      phi = phi_tail.
Proof.
  intros n heap closure_env closure_rho x e r arg_rho r_val k
    phi heap_final v_final HRgn HSteps.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (StReturn heap
        (VRegionClosure closure_env closure_rho x e)
        (KRgnApp r arg_rho k))
      LSilent
      (StEval heap closure_env
        (rho_extend x r_val closure_rho)
        e k)
      phi heap_final v_final
      (StepRgnAppReturn heap closure_env closure_rho arg_rho
        x e r r_val k HRgn)
      HSteps)
    as (n_tail & phi_tail & Hn & HTail & HTrace).
  simpl in HTrace.
  exists n_tail, phi_tail.
  repeat split; assumption.
Qed.

Definition ERgnAppCountedDecompositionGoal : Prop :=
  forall n heap env rho er r phi heap_final v_final,
    NStepsN n
      (NInitialState heap env rho (ERgnApp er r))
      phi
      (StDone heap_final v_final) ->
    exists n_fun n_body phi_fun phi_body
      closure_env closure_rho x e heap_fun r_val,
      eval_region rho r = Some r_val /\
      NStepsN n_fun
        (NInitialState heap env rho er)
        phi_fun
        (StDone heap_fun
          (VRegionClosure closure_env closure_rho x e)) /\
      NStepsN n_body
        (NInitialState heap_fun closure_env
          (rho_extend x r_val closure_rho)
          e)
        phi_body
        (StDone heap_final v_final) /\
      n_fun < n /\
      n_body < n /\
      phi = phi_fun ++ phi_body.

Theorem ERgnApp_counted_decomposition :
  ERgnAppCountedDecompositionGoal.
Proof.
  unfold ERgnAppCountedDecompositionGoal.
  intros n heap env rho er r phi heap_final v_final HSteps.
  destruct
    (ERgnApp_terminal_first_step_N
      n heap env rho er r phi heap_final v_final HSteps)
    as (n_fun_tail & phi_fun_tail & HnStart &
      HFunWithKont & HTraceStart).
  destruct
    (NStepsN_append_kont_terminal_split_counted
      n_fun_tail
      (StEval heap env rho er (KRgnApp r rho KDone))
      phi_fun_tail
      heap_final v_final
      HFunWithKont
      (NInitialState heap env rho er)
      (KRgnApp r rho KDone)
      eq_refl)
    as (n_fun & n_after_fun & phi_fun & heap_fun & v_fun &
      phi_after_fun & HFun & HAfterFun & HCountFun & HTraceFun).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KRgnApp_terminal_value_is_region_closure
        heap_fun v_fun r rho KDone
        phi_after_fun heap_final v_final
        (NStepsN_to_NSteps
          n_after_fun
          (StReturn heap_fun v_fun (KRgnApp r rho KDone))
          phi_after_fun
          (StDone heap_final v_final)
          HAfterFun))
      as (closure_env & closure_rho & x & e & HClosure).
    subst v_fun.
    destruct
      (KRgnApp_region_closure_terminal_region
        heap_fun closure_env closure_rho x e r rho KDone
        phi_after_fun heap_final v_final
        (NStepsN_to_NSteps
          n_after_fun
          (StReturn heap_fun
            (VRegionClosure closure_env closure_rho x e)
            (KRgnApp r rho KDone))
          phi_after_fun
          (StDone heap_final v_final)
          HAfterFun))
      as (r_val & HRgn).
    destruct
      (KRgnApp_region_closure_terminal_first_step_N
        n_after_fun heap_fun closure_env closure_rho x e
        r rho r_val KDone
        phi_after_fun heap_final v_final HRgn HAfterFun)
      as (n_body & phi_body & HCountAfterFun &
        HBody & HTraceAfterFun).
    exists n_fun, n_body, phi_fun, phi_body,
      closure_env, closure_rho, x, e, heap_fun, r_val.
    repeat split; try assumption.
    * lia.
    * lia.
    * rewrite HTraceStart, HTraceFun, HTraceAfterFun.
      reflexivity.
Qed.

Lemma App_EEmpty_summary_evaluation :
  forall heap env rho,
    SummaryEvaluation heap env rho EEmpty
      ([] : Trace) heap (SummarySet ([] : list ComputedAction)).
Proof.
  intros heap env rho.
  unfold SummaryEvaluation, NInitialState.
  eapply StepsStep
    with
      (label := LSilent)
      (state' := StReturn heap
        (VSummary (SummarySet ([] : list ComputedAction))) KDone).
  - apply StepEmpty.
  - eapply StepsStep
      with
        (label := LSilent)
        (state' := StDone heap
          (VSummary (SummarySet ([] : list ComputedAction)))).
    + apply StepReturnDone.
    + constructor.
Qed.

Theorem ERgnApp_checked_store_context_case_from_below :
  forall n gamma omega heap env rho er r
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega (ERgnApp er r) EEmpty ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (ERgnApp er r) phi heap_final v_final ->
    SummaryEvaluation heap env rho EEmpty
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho er r
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext HComp _HSummary.
  destruct
    (NCBT_RgnApp_components gamma omega er r HBack)
    as (ty_er & eff_er & _ty_app & _eff_app &
      HCheckedEr & _HCheckedApp & HBackEr).
  unfold CountedComputationEvaluation in HComp.
  destruct
    (ERgnApp_counted_decomposition
      n heap env rho er r phi heap_final v_final HComp)
    as (n_fun & n_body & phi_fun & phi_body &
      closure_env & closure_rho & x & e & heap_fun & r_val &
      HRgn & HFun & HBody & HCountFun & HCountBody & HTrace).
  assert
    (HFunCovered :
      TraceCoveredBySummary phi_fun
        (SummarySet ([] : list ComputedAction))).
  {
    eapply
      (HBelow n_fun gamma omega heap env rho er EEmpty
        phi_fun heap_fun
        (VRegionClosure closure_env closure_rho x e)
        ([] : Trace) heap
        (SummarySet ([] : list ComputedAction))).
    - exact HCountFun.
    - exact HBackEr.
    - exact HContext.
    - unfold CountedComputationEvaluation. exact HFun.
    - apply App_EEmpty_summary_evaluation.
  }
  pose proof
    (trace_covered_empty_summary_nil phi_fun HFunCovered)
    as HFunNil.
  assert
    (HFunComp :
      CountedComputationEvaluation n_fun heap env rho er
        phi_fun heap_fun
        (VRegionClosure closure_env closure_rho x e)).
  {
    unfold CountedComputationEvaluation.
    exact HFun.
  }
  destruct
    (checked_store_counted_computation_store_value_shape
      n_fun gamma omega heap env rho er ty_er eff_er
      phi_fun heap_fun
      (VRegionClosure closure_env closure_rho x e)
      HContext HCheckedEr HFunComp)
    as (store_fun & ty_fun_res & HBoundedFun & HHeapFun & HValFun).
  destruct
    (NStoreResolvedValShape_region_closure_inv
      store_fun closure_env closure_rho x e ty_fun_res HValFun)
    as (gamma_body & omega_body & ty_body & _ty_body_res &
      eff_body & _eff_body_res & _HTyFun & HEnvBody &
      HRhoBody & _HEffResolveBody & _HTyResolveBody & HBodyChecked).
  assert
    (HBodyContext :
      CheckedStoreRuntimeContext gamma_body (x :: omega_body)
        heap_fun closure_env
        (rho_extend x r_val closure_rho)).
  {
    split.
    - exists store_fun.
      unfold NStoreResolvedRuntimeShape.
      split; [exact HBoundedFun |].
      split; [exact HHeapFun |].
      eapply NStoreResolvedEnvShape_extend_fresh;
        eauto using
          NCheckedRegionBody_fresh,
          NCheckedRegionBody_ctx_wf.
    - eapply NRhoModels_extend; eauto.
  }
  assert
    (HBodyCovered :
      TraceCoveredBySummary phi_body
        (SummarySet ([] : list ComputedAction))).
  {
    eapply
      (HBelow n_body gamma_body (x :: omega_body)
        heap_fun closure_env
        (rho_extend x r_val closure_rho)
        e EEmpty phi_body heap_final v_final
        ([] : Trace) heap_fun
        (SummarySet ([] : list ComputedAction))).
    - exact HCountBody.
    - exact
        (NCheckedRegionBody_backtriangle
          x gamma_body omega_body e ty_body eff_body HBodyChecked).
    - exact HBodyContext.
    - unfold CountedComputationEvaluation. exact HBody.
    - apply App_EEmpty_summary_evaluation.
  }
  pose proof
    (trace_covered_empty_summary_nil phi_body HBodyCovered)
    as HBodyNil.
  subst phi.
  rewrite HFunNil, HBodyNil.
  simpl.
  apply trace_covered_nil.
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
        (StDone heap_final (VSummary theta)) /\
      phi = phi_fun ++ phi_arg ++ phi_summary.

Theorem EEffApp_decomposition :
  EEffAppDecompositionGoal.
Proof.
  unfold EEffAppDecompositionGoal.
  intros heap env rho ef ea phi heap_final theta HSteps.
  destruct
    (EEffApp_terminal_first_step
      heap env rho ef ea phi heap_final (VSummary theta) HSteps)
    as (phi_fun_tail & HFunWithKont & HTraceStart).
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
      HFun & HAfterFun & HTraceFun).
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
    as (phi_arg_tail & HArgWithKont & HTraceAfterFun).
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
      HArg & HAfterArg & HTraceArg).
  destruct
    (KEffAppArg_terminal_first_step
      heap_arg arg closure_env closure_rho f x ec ee KDone
      phi_after_arg heap_final (VSummary theta) HAfterArg)
    as (phi_summary & HSummary & HTraceAfterArg).
  exists phi_fun, phi_arg, phi_summary, closure_env, closure_rho,
    f, x, ec, ee, arg, heap_arg, heap_fun.
  repeat split; try assumption.
  rewrite HTraceStart, HTraceFun, HTraceAfterFun, HTraceArg,
    HTraceAfterArg.
  reflexivity.
Qed.

Theorem EEffApp_summary_trace_covered_from_components :
  forall heap env rho ef ea phi heap_final theta,
    NSteps
      (NInitialState heap env rho (EEffApp ef ea))
      phi
      (StDone heap_final (VSummary theta)) ->
    (forall phi_fun heap_fun
      (closure_env : NEnv) (closure_rho : Rho)
      (f x : VarId) (ec ee : NExpr),
      NSteps
        (NInitialState heap env rho ef)
        phi_fun
        (StDone heap_fun
          (VClosure closure_env closure_rho f x ec ee)) ->
      TraceCoveredBySummary phi_fun theta) ->
    (forall phi_arg heap_fun
      (closure_env : NEnv) (closure_rho : Rho)
      (f x : VarId) (ec ee : NExpr)
      (arg : NVal) heap_arg,
      NSteps
        (NInitialState heap_fun env rho ea)
        phi_arg
        (StDone heap_arg arg) ->
      TraceCoveredBySummary phi_arg theta) ->
    (forall phi_summary heap_arg
      (closure_env : NEnv) (closure_rho : Rho)
      (f x : VarId) (ec ee : NExpr) (arg : NVal),
      NSteps
        (NInitialState heap_arg
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ee)
        phi_summary
        (StDone heap_final (VSummary theta)) ->
      TraceCoveredBySummary phi_summary theta) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros heap env rho ef ea phi heap_final theta
    HSummary HCoveredFun HCoveredArg HCoveredSummary.
  destruct
    (EEffApp_decomposition
      heap env rho ef ea phi heap_final theta HSummary)
    as (phi_fun & phi_arg & phi_summary &
      closure_env & closure_rho & f & x & ec & ee & arg & heap_arg &
      heap_fun & HFun & HArg & HBody & HTrace).
  subst phi.
  apply trace_covered_app_same.
  - eapply HCoveredFun; eauto.
  - apply trace_covered_app_same.
    + eapply HCoveredArg; eauto.
    + eapply HCoveredSummary; eauto.
Qed.

Definition EEffAppCountedDecompositionGoal : Prop :=
  forall n heap env rho ef ea phi heap_final theta,
    NStepsN n
      (NInitialState heap env rho (EEffApp ef ea))
      phi
      (StDone heap_final (VSummary theta)) ->
    exists n_fun n_arg n_summary
      phi_fun phi_arg phi_summary
      closure_env closure_rho f x ec ee arg heap_arg,
    exists heap_fun,
      NStepsN n_fun
        (NInitialState heap env rho ef)
        phi_fun
        (StDone heap_fun (VClosure closure_env closure_rho f x ec ee)) /\
      NStepsN n_arg
        (NInitialState heap_fun env rho ea)
        phi_arg
        (StDone heap_arg arg) /\
      NStepsN n_summary
        (NInitialState heap_arg
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ee)
        phi_summary
        (StDone heap_final (VSummary theta)) /\
      n_fun < n /\
      n_arg < n /\
      n_summary < n /\
      phi = phi_fun ++ phi_arg ++ phi_summary.

Theorem EEffApp_counted_decomposition :
  EEffAppCountedDecompositionGoal.
Proof.
  unfold EEffAppCountedDecompositionGoal.
  intros n heap env rho ef ea phi heap_final theta HSteps.
  destruct
    (EEffApp_terminal_first_step_N
      n heap env rho ef ea phi heap_final (VSummary theta) HSteps)
    as (n_fun_tail & phi_fun_tail & HnStart &
      HFunWithKont & HTraceStart).
  destruct
    (NStepsN_append_kont_terminal_split_counted
      n_fun_tail
      (StEval heap env rho ef (KEffAppFun ea env rho KDone))
      phi_fun_tail
      heap_final (VSummary theta)
      HFunWithKont
      (NInitialState heap env rho ef)
      (KEffAppFun ea env rho KDone)
      eq_refl)
    as (n_fun & n_after_fun & phi_fun & heap_fun & v_fun &
      phi_after_fun & HFun & HAfterFun & HCountFun & HTraceFun).
  - intros heap_done v_done HDone. inversion HDone.
  - destruct
      (KEffAppFun_terminal_value_is_closure
        heap_fun v_fun ea env rho KDone
        phi_after_fun heap_final (VSummary theta)
        (NStepsN_to_NSteps
          n_after_fun
          (StReturn heap_fun v_fun (KEffAppFun ea env rho KDone))
          phi_after_fun
          (StDone heap_final (VSummary theta))
          HAfterFun))
      as (closure_env & closure_rho & f & x & ec & ee & HClosure).
    subst v_fun.
    destruct
      (KEffAppFun_closure_terminal_first_step_N
        n_after_fun heap_fun env rho ea KDone
        closure_env closure_rho f x ec ee
        phi_after_fun heap_final (VSummary theta) HAfterFun)
      as (n_arg_tail & phi_arg_tail & HCountAfterFun &
        HArgWithKont & HTraceAfterFun).
    destruct
      (NStepsN_append_kont_terminal_split_counted
        n_arg_tail
        (StEval heap_fun env rho ea
          (KEffAppArg closure_env closure_rho f x ec ee KDone))
        phi_arg_tail
        heap_final (VSummary theta)
        HArgWithKont
        (NInitialState heap_fun env rho ea)
        (KEffAppArg closure_env closure_rho f x ec ee KDone)
        eq_refl)
      as (n_arg & n_after_arg & phi_arg & heap_arg & arg &
        phi_after_arg & HArg & HAfterArg & HCountArg & HTraceArg).
    + intros heap_done v_done HDone. inversion HDone.
    + destruct
        (KEffAppArg_terminal_first_step_N
          n_after_arg heap_arg arg closure_env closure_rho f x ec ee KDone
          phi_after_arg heap_final (VSummary theta) HAfterArg)
        as (n_summary & phi_summary & HCountAfterArg &
          HSummary & HTraceAfterArg).
      exists n_fun, n_arg, n_summary,
        phi_fun, phi_arg, phi_summary,
        closure_env, closure_rho, f, x, ec, ee, arg, heap_arg, heap_fun.
      repeat split; try assumption.
      * lia.
      * lia.
      * lia.
      * rewrite HTraceStart, HTraceFun, HTraceAfterFun,
          HTraceArg, HTraceAfterArg.
        reflexivity.
Qed.

Theorem EEffApp_counted_checked_summary_heap_neutral_decomposition :
  forall n gamma omega heap env rho ef ea phi heap_final theta,
    NCheckedBackTriangle gamma omega
      (EMuApp ef ea) (EEffApp ef ea) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EEffApp ef ea) phi heap_final (VSummary theta) ->
    exists n_fun n_arg n_summary
      phi_fun phi_arg phi_summary
      closure_env closure_rho f x ec ee arg,
      NStepsN n_fun
        (NInitialState heap env rho ef)
        phi_fun
        (StDone heap (VClosure closure_env closure_rho f x ec ee)) /\
      NStepsN n_arg
        (NInitialState heap env rho ea)
        phi_arg
        (StDone heap arg) /\
      NStepsN n_summary
        (NInitialState heap
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ee)
        phi_summary
        (StDone heap (VSummary theta)) /\
      n_fun < n /\
      n_arg < n /\
      n_summary < n /\
      HeapNeutralTrace phi /\
      phi = phi_fun ++ phi_arg ++ phi_summary.
Proof.
  intros n gamma omega heap env rho ef ea phi heap_final theta
    HBack HContext HSummaryTraceSound HComp.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (EEffApp_counted_decomposition
      n heap env rho ef ea phi heap_final theta HComp)
    as (n_fun & n_arg & n_summary &
      phi_fun & phi_arg & phi_summary &
      closure_env & closure_rho & f & x & ec & ee & arg & heap_arg &
      heap_fun & HFun & HArg & HBody & HCountFun & HCountArg &
      HCountSummary & HTrace).
  destruct
    (NCBT_App_components gamma omega ef ea HBack)
    as (_ & _ & eff_eff & _ & _ & _ & _ &
      _ & HCheckedEffApp & _ & _ & HStaticEff & _ & _ & _ & _).
  pose proof
    (CheckedStoreRuntimeContext_to_rho_models
      gamma omega heap env rho
      (CheckedRuntimeContext_to_store_context
        gamma omega heap env rho HContext))
    as HRho.
  pose proof
    (NCheckedTcExp_eff_wf
      gamma omega (EEffApp ef ea) TyEffect eff_eff HCheckedEffApp)
    as HEffWF.
  destruct
    (NResolveStaticEffect_exists 0 omega rho eff_eff HRho HEffWF)
    as (eff_eff_res & HResolveEff).
  assert
    (HSummary :
      SummaryEvaluation heap env rho (EEffApp ef ea)
        phi heap_final theta).
  {
    unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps.
    exact HComp.
  }
  pose proof
    (HSummaryTraceSound
      (EEffApp ef ea) eff_eff phi heap_final theta eff_eff_res
      HCheckedEffApp HSummary HResolveEff)
    as HCoveredStatic.
  destruct
    (summary_static_heap_neutral
      heap env rho (EEffApp ef ea)
      phi heap_final theta eff_eff eff_eff_res
      HSummary HResolveEff HCoveredStatic HStaticEff)
    as (HHeapFinal & HNeutral).
  assert
    (HNeutralDecomp :
      HeapNeutralTrace (phi_fun ++ phi_arg ++ phi_summary)).
  {
    rewrite <- HTrace.
    exact HNeutral.
  }
  assert
    (HNeutralFun : HeapNeutralTrace phi_fun).
  {
    eapply heap_neutral_trace_app_l.
    exact HNeutralDecomp.
  }
  assert
    (HHeapFun : heap_fun = heap).
  {
    eapply NSteps_heap_neutral_initial_heap.
    - eapply NStepsN_to_NSteps.
      exact HFun.
    - exact HNeutralFun.
  }
  subst heap_fun.
  assert
    (HNeutralTail : HeapNeutralTrace (phi_arg ++ phi_summary)).
  {
    eapply heap_neutral_trace_app_r.
    exact HNeutralDecomp.
  }
  assert
    (HNeutralArg : HeapNeutralTrace phi_arg).
  {
    eapply heap_neutral_trace_app_l.
    exact HNeutralTail.
  }
  assert
    (HHeapArg : heap_arg = heap).
  {
    eapply NSteps_heap_neutral_initial_heap.
    - eapply NStepsN_to_NSteps.
      exact HArg.
    - exact HNeutralArg.
  }
  subst heap_arg.
  subst heap_final.
  exists n_fun, n_arg, n_summary,
    phi_fun, phi_arg, phi_summary,
    closure_env, closure_rho, f, x, ec, ee, arg.
  split; [exact HFun |].
  split; [exact HArg |].
  split; [exact HBody |].
  split; [exact HCountFun |].
  split; [exact HCountArg |].
  split; [exact HCountSummary |].
  split; [exact HNeutral |].
  exact HTrace.
Qed.

Theorem EEffApp_counted_checked_store_summary_heap_neutral_decomposition :
  forall n gamma omega heap env rho ef ea phi heap_final theta,
    NCheckedBackTriangle gamma omega
      (EMuApp ef ea) (EEffApp ef ea) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EEffApp ef ea) phi heap_final (VSummary theta) ->
    exists n_fun n_arg n_summary
      phi_fun phi_arg phi_summary
      closure_env closure_rho f x ec ee arg,
      NStepsN n_fun
        (NInitialState heap env rho ef)
        phi_fun
        (StDone heap (VClosure closure_env closure_rho f x ec ee)) /\
      NStepsN n_arg
        (NInitialState heap env rho ea)
        phi_arg
        (StDone heap arg) /\
      NStepsN n_summary
        (NInitialState heap
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ee)
        phi_summary
        (StDone heap (VSummary theta)) /\
      n_fun < n /\
      n_arg < n /\
      n_summary < n /\
      HeapNeutralTrace phi /\
      phi = phi_fun ++ phi_arg ++ phi_summary.
Proof.
  intros n gamma omega heap env rho ef ea phi heap_final theta
    HBack HContext HSummaryTraceSound HComp.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (EEffApp_counted_decomposition
      n heap env rho ef ea phi heap_final theta HComp)
    as (n_fun & n_arg & n_summary &
      phi_fun & phi_arg & phi_summary &
      closure_env & closure_rho & f & x & ec & ee & arg & heap_arg &
      heap_fun & HFun & HArg & HBody & HCountFun & HCountArg &
      HCountSummary & HTrace).
  destruct
    (NCBT_App_components gamma omega ef ea HBack)
    as (_ & _ & eff_eff & _ & _ & _ & _ &
      _ & HCheckedEffApp & _ & _ & HStaticEff & _ & _ & _ & _).
  pose proof
    (CheckedStoreRuntimeContext_to_rho_models
      gamma omega heap env rho HContext)
    as HRho.
  pose proof
    (NCheckedTcExp_eff_wf
      gamma omega (EEffApp ef ea) TyEffect eff_eff HCheckedEffApp)
    as HEffWF.
  destruct
    (NResolveStaticEffect_exists 0 omega rho eff_eff HRho HEffWF)
    as (eff_eff_res & HResolveEff).
  assert
    (HSummary :
      SummaryEvaluation heap env rho (EEffApp ef ea)
        phi heap_final theta).
  {
    unfold SummaryEvaluation.
    eapply NStepsN_to_NSteps.
    exact HComp.
  }
  pose proof
    (HSummaryTraceSound
      (EEffApp ef ea) eff_eff phi heap_final theta eff_eff_res
      HCheckedEffApp HSummary HResolveEff)
    as HCoveredStatic.
  destruct
    (summary_static_heap_neutral
      heap env rho (EEffApp ef ea)
      phi heap_final theta eff_eff eff_eff_res
      HSummary HResolveEff HCoveredStatic HStaticEff)
    as (HHeapFinal & HNeutral).
  assert
    (HNeutralDecomp :
      HeapNeutralTrace (phi_fun ++ phi_arg ++ phi_summary)).
  {
    rewrite <- HTrace.
    exact HNeutral.
  }
  assert
    (HNeutralFun : HeapNeutralTrace phi_fun).
  {
    eapply heap_neutral_trace_app_l.
    exact HNeutralDecomp.
  }
  assert
    (HHeapFun : heap_fun = heap).
  {
    eapply NSteps_heap_neutral_initial_heap.
    - eapply NStepsN_to_NSteps.
      exact HFun.
    - exact HNeutralFun.
  }
  subst heap_fun.
  assert
    (HNeutralTail : HeapNeutralTrace (phi_arg ++ phi_summary)).
  {
    eapply heap_neutral_trace_app_r.
    exact HNeutralDecomp.
  }
  assert
    (HNeutralArg : HeapNeutralTrace phi_arg).
  {
    eapply heap_neutral_trace_app_l.
    exact HNeutralTail.
  }
  assert
    (HHeapArg : heap_arg = heap).
  {
    eapply NSteps_heap_neutral_initial_heap.
    - eapply NStepsN_to_NSteps.
      exact HArg.
    - exact HNeutralArg.
  }
  subst heap_arg.
  subst heap_final.
  exists n_fun, n_arg, n_summary,
    phi_fun, phi_arg, phi_summary,
    closure_env, closure_rho, f, x, ec, ee, arg.
  split; [exact HFun |].
  split; [exact HArg |].
  split; [exact HBody |].
  split; [exact HCountFun |].
  split; [exact HCountArg |].
  split; [exact HCountSummary |].
  split; [exact HNeutral |].
  exact HTrace.
Qed.

Theorem EEffApp_checked_summary_body_store_context_from_prefixes :
  forall gamma omega heap env rho ef ea
    n_fun n_arg phi_fun phi_arg closure_env closure_rho f x ec ee arg,
    NCheckedBackTriangle gamma omega
      (EMuApp ef ea) (EEffApp ef ea) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    NStepsN n_fun
      (NInitialState heap env rho ef)
      phi_fun
      (StDone heap (VClosure closure_env closure_rho f x ec ee)) ->
    NStepsN n_arg
      (NInitialState heap env rho ea)
      phi_arg
      (StDone heap arg) ->
    exists gamma_closure omega_closure
      ty_arg ty_body eff_body eff_summary,
      CheckedStoreRuntimeContext
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) ::
          gamma_closure)
        omega_closure
        heap
        (env_extend x arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho /\
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) ::
          gamma_closure)
        omega_closure ec ty_body eff_body /\
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) ::
          gamma_closure)
        omega_closure ee TyEffect eff_summary /\
      NCheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) ::
          gamma_closure)
        omega_closure ec ee.
Proof.
  intros gamma omega heap env rho ef ea
    n_fun n_arg phi_fun phi_arg closure_env closure_rho f x ec ee arg
    HBack HContext HFun HArg.
  destruct
    (NCBT_App_components gamma omega ef ea HBack)
    as (_ & _ & eff_eff & _ & _ & _ & _ &
      _ & HCheckedEffApp & _ & _ & _ & _ & _ & _ & _).
  destruct
    (NCheckedTcExp_EEffApp_inv
      gamma omega ef ea eff_eff HCheckedEffApp)
    as (ty_arg_app & ty_body_app & eff_body_app &
      eff_summary_app & eff_f & eff_a &
      HCheckedFun & HCheckedArg & _).
  assert
    (HFunComp :
      ComputationEvaluation heap env rho ef phi_fun heap
        (VClosure closure_env closure_rho f x ec ee)).
  {
    unfold ComputationEvaluation.
    eapply NStepsN_to_NSteps.
    exact HFun.
  }
  assert
    (HArgComp :
      ComputationEvaluation heap env rho ea phi_arg heap arg).
  {
    unfold ComputationEvaluation.
    eapply NStepsN_to_NSteps.
    exact HArg.
  }
  destruct
    (checked_store_sequential_computations_store_value_shapes
      gamma omega heap env rho
      ef (TyArrow ty_arg_app eff_body_app ty_body_app eff_summary_app)
        eff_f phi_fun heap
        (VClosure closure_env closure_rho f x ec ee)
      ea ty_arg_app eff_a phi_arg heap arg
      HContext HCheckedFun HCheckedArg HFunComp HArgComp)
    as (store & ty_fun_res & ty_arg_res &
      HResolveFun & HResolveArg & HBounded & HHeap &
      HValFun & HValArg).
  destruct
    (NStoreResolvedValShape_closure_inv
      store closure_env closure_rho f x ec ee ty_fun_res HValFun)
    as
      (gamma_closure & omega_closure &
        ty_arg_closure & ty_arg_closure_res &
        ty_body_closure & ty_body_closure_res &
        eff_body_closure & eff_body_closure_res &
        eff_summary_closure & eff_summary_closure_res &
        HTyFun & HEnvClosure & HRhoClosure &
        HResolveClosureArg & HResolveClosureBodyEff &
        HResolveClosureBodyTy & HResolveClosureSummaryEff &
        HCheckedBody & HCheckedSummary & HBodyBack).
  assert
    (HArgResEq : ty_arg_res = ty_arg_closure_res).
  {
    rewrite HTyFun in HResolveFun.
    inversion HResolveFun; subst.
    eapply NResolveTy_deterministic; eauto.
  }
  assert
    (HValFunArrow :
      NStoreResolvedValShape store
        (VClosure closure_env closure_rho f x ec ee)
        (TyArrow ty_arg_closure_res eff_body_closure_res
          ty_body_closure_res eff_summary_closure_res)).
  {
    rewrite <- HTyFun.
    exact HValFun.
  }
  exists gamma_closure, omega_closure,
    ty_arg_closure, ty_body_closure,
    eff_body_closure, eff_summary_closure.
  split.
  - split.
    + exists store.
      unfold NStoreResolvedRuntimeShape.
      split; [exact HBounded |].
      split; [exact HHeap |].
      eapply NStoreResolvedEnvShape_extend with
        (ty_res := ty_arg_closure_res).
      * exact HResolveClosureArg.
      * rewrite <- HArgResEq. exact HValArg.
      * eapply NStoreResolvedEnvShape_extend with
          (ty_res :=
            TyArrow ty_arg_closure_res eff_body_closure_res
              ty_body_closure_res eff_summary_closure_res).
        -- eapply NResolve_Arrow; eauto.
        -- exact HValFunArrow.
        -- exact HEnvClosure.
    + exact HRhoClosure.
  - split; [exact HCheckedBody |].
    split; [exact HCheckedSummary |].
    exact HBodyBack.
Qed.

Theorem EMuApp_checked_store_context_case_from_below :
  forall n gamma omega heap env rho ef ea
    phi heap_final v_final phi_summary heap_summary theta,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    NCheckedBackTriangle gamma omega (EMuApp ef ea) (EEffApp ef ea) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n heap env rho
      (EMuApp ef ea) phi heap_final v_final ->
    SummaryEvaluation heap env rho (EEffApp ef ea)
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n gamma omega heap env rho ef ea
    phi heap_final v_final phi_summary heap_summary theta
    HBelow HBack HContext HComputationTraceSound HComp HSummary.
  destruct
    (NCBT_App_components gamma omega ef ea HBack)
    as (ty_mu & eff_mu & eff_eff & ty_ef & ty_ea & eff_ef &
      eff_ea & HCheckedApp & HCheckedEffApp & HCheckedFun &
      HCheckedArg & _HStaticEff & HStaticFun & HStaticArg &
      HBackFun & HBackArg).
  unfold CountedComputationEvaluation in HComp.
  destruct
    (EMuApp_counted_decomposition
      n heap env rho ef ea phi heap_final v_final HComp)
    as (n_fun & n_arg & n_body &
      phi_fun & phi_arg & phi_body &
      closure_env & closure_rho & f & x & ec & ee & arg &
      heap_arg & heap_fun &
      HFun & HArg & HBody &
      HCountFun & HCountArg & HCountBody & HTrace).
  assert (HFunComp :
    CountedComputationEvaluation n_fun heap env rho ef
      phi_fun heap_fun (VClosure closure_env closure_rho f x ec ee)).
  {
    unfold CountedComputationEvaluation.
    exact HFun.
  }
  destruct
    (checked_store_counted_computation_heap_neutral
      n_fun gamma omega heap env rho ef ty_ef eff_ef
      phi_fun heap_fun (VClosure closure_env closure_rho f x ec ee)
      HContext HComputationTraceSound HCheckedFun HStaticFun HFunComp)
    as (HHeapFun & _HNeutralFun).
  subst heap_fun.
  assert (HArgComp :
    CountedComputationEvaluation n_arg heap env rho ea
      phi_arg heap_arg arg).
  {
    unfold CountedComputationEvaluation.
    exact HArg.
  }
  destruct
    (checked_store_counted_computation_heap_neutral
      n_arg gamma omega heap env rho ea ty_ea eff_ea
      phi_arg heap_arg arg
      HContext HComputationTraceSound HCheckedArg HStaticArg HArgComp)
    as (HHeapArg & _HNeutralArg).
  subst heap_arg.
  destruct
    (EEffApp_decomposition
      heap env rho ef ea phi_summary heap_summary theta HSummary)
    as (phi_fun_summary & phi_arg_summary & phi_body_summary &
      closure_env_summary & closure_rho_summary &
      f_summary & x_summary & ec_summary & ee_summary &
      arg_summary & heap_arg_summary & heap_fun_summary &
      HFunSummary & HArgSummary & HBodySummary & _HSummaryTrace).
  destruct
    (NSteps_terminal_trace_deterministic
      (NInitialState heap env rho ef)
      phi_fun heap (VClosure closure_env closure_rho f x ec ee)
      phi_fun_summary heap_fun_summary
      (VClosure closure_env_summary closure_rho_summary
        f_summary x_summary ec_summary ee_summary))
    as (_HTraceFunEq & HHeapFunSummaryEq & HClosureEq).
  - eapply NStepsN_to_NSteps.
    exact HFun.
  - exact HFunSummary.
  - subst heap_fun_summary.
    inversion HClosureEq; subst
      closure_env_summary closure_rho_summary
      f_summary x_summary ec_summary ee_summary.
    destruct
      (NSteps_terminal_trace_deterministic
        (NInitialState heap env rho ea)
        phi_arg heap arg
        phi_arg_summary heap_arg_summary arg_summary)
      as (_HTraceArgEq & HHeapArgSummaryEq & HArgEq).
    + eapply NStepsN_to_NSteps.
      exact HArg.
    + exact HArgSummary.
    + subst heap_arg_summary arg_summary.
      destruct
        (EEffApp_checked_summary_body_store_context_from_prefixes
          gamma omega heap env rho ef ea
          n_fun n_arg phi_fun phi_arg
          closure_env closure_rho f x ec ee arg
          HBack HContext HFun HArg)
        as (gamma_body & omega_body &
          ty_arg_body & ty_body & eff_body & eff_summary &
          HBodyContext & _HCheckedBody & _HCheckedSummary &
          HBodyBack).
      assert (HCoveredFun : TraceCoveredBySummary phi_fun theta).
      {
        eapply
          (HBelow n_fun gamma omega heap env rho
            ef (EEffApp ef ea)
            phi_fun heap (VClosure closure_env closure_rho f x ec ee)
            phi_summary heap_summary theta);
          eauto; lia.
      }
      assert (HCoveredArg : TraceCoveredBySummary phi_arg theta).
      {
        eapply
          (HBelow n_arg gamma omega heap env rho
            ea (EEffApp ef ea)
            phi_arg heap arg
            phi_summary heap_summary theta);
          eauto; lia.
      }
      assert (HBodySummaryEval :
        SummaryEvaluation heap
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ee
          phi_body_summary heap_summary theta).
      {
        unfold SummaryEvaluation.
        exact HBodySummary.
      }
      assert (HBodyComp :
        CountedComputationEvaluation n_body heap
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ec phi_body heap_final v_final).
      {
        unfold CountedComputationEvaluation.
        exact HBody.
      }
      assert (HCoveredBody : TraceCoveredBySummary phi_body theta).
      {
        eapply
          (HBelow n_body
            ((x, ty_arg_body) ::
              (f, TyArrow ty_arg_body eff_body ty_body eff_summary) ::
              gamma_body)
            omega_body heap
            (env_extend x arg
              (env_extend f
                (VClosure closure_env closure_rho f x ec ee)
                closure_env))
            closure_rho ec ee
            phi_body heap_final v_final
            phi_body_summary heap_summary theta).
        - exact HCountBody.
        - exact HBodyBack.
        - exact HBodyContext.
        - exact HBodyComp.
        - exact HBodySummaryEval.
      }
      subst phi.
      apply trace_covered_app_same.
      * exact HCoveredFun.
      * apply trace_covered_app_same.
        -- exact HCoveredArg.
        -- exact HCoveredBody.
Qed.

Theorem EEffApp_counted_checked_summary_trace_covered_from_store_below_body :
  forall n_bound n_eval gamma omega heap env rho ef ea phi theta,
    CheckedStoreContextSmallStepCorrectnessBelow n_bound ->
    n_eval < n_bound ->
    NCheckedBackTriangle gamma omega
      (EMuApp ef ea) (EEffApp ef ea) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n_eval heap env rho
      (EEffApp ef ea) phi heap (VSummary theta) ->
    (forall n_summary phi_summary
      closure_env closure_rho f x ec ee arg,
      n_summary < n_bound ->
      NStepsN n_summary
        (NInitialState heap
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ee)
        phi_summary
        (StDone heap (VSummary theta)) ->
      TraceCoveredBySummary phi_summary theta) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n_bound n_eval gamma omega heap env rho ef ea phi theta
    HBelow HCountEval HBack HContext HSummaryTraceSound
    HComp HCoveredBody.
  destruct
    (EEffApp_counted_checked_summary_heap_neutral_decomposition
      n_eval gamma omega heap env rho ef ea phi heap theta
      HBack HContext HSummaryTraceSound HComp)
    as (n_fun & n_arg & n_summary &
      phi_fun & phi_arg & phi_summary &
      closure_env & closure_rho & f & x & ec & ee & arg &
      HFun & HArg & HBody & HCountFun & HCountArg &
      HCountSummary & _ & HTrace).
  destruct
    (NCBT_App_components gamma omega ef ea HBack)
    as (_ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & _ & HBackFun & HBackArg).
  assert
    (HSummary :
      SummaryEvaluation heap env rho (EEffApp ef ea)
        phi heap theta).
  {
    unfold SummaryEvaluation, CountedComputationEvaluation in *.
    eapply NStepsN_to_NSteps.
    exact HComp.
  }
  assert
    (HStoreContext :
      CheckedStoreRuntimeContext gamma omega heap env rho).
  {
    eapply CheckedRuntimeContext_to_store_context; eauto.
  }
  assert
    (HFunComp :
      CountedComputationEvaluation n_fun heap env rho ef
        phi_fun heap (VClosure closure_env closure_rho f x ec ee)).
  {
    unfold CountedComputationEvaluation.
    exact HFun.
  }
  assert
    (HArgComp :
      CountedComputationEvaluation n_arg heap env rho ea
        phi_arg heap arg).
  {
    unfold CountedComputationEvaluation.
    exact HArg.
  }
  assert
    (HCoveredFun : TraceCoveredBySummary phi_fun theta).
  {
    eapply
      (HBelow
        n_fun gamma omega heap env rho
        ef (EEffApp ef ea)
        phi_fun heap
        (VClosure closure_env closure_rho f x ec ee)
        phi heap theta);
      eauto; lia.
  }
  assert
    (HCoveredArg : TraceCoveredBySummary phi_arg theta).
  {
    eapply
      (HBelow
        n_arg gamma omega heap env rho
        ea (EEffApp ef ea)
        phi_arg heap arg
        phi heap theta);
      eauto; lia.
  }
  subst phi.
  apply trace_covered_app_same.
  - exact HCoveredFun.
  - apply trace_covered_app_same.
    + exact HCoveredArg.
    + eapply
        (HCoveredBody
          n_summary phi_summary closure_env closure_rho
          f x ec ee arg);
        eauto; lia.
Qed.

Theorem EEffApp_counted_checked_summary_trace_covered_from_store_below_body_context :
  forall n_bound n_eval gamma omega heap env rho ef ea phi theta,
    CheckedStoreContextSmallStepCorrectnessBelow n_bound ->
    n_eval < n_bound ->
    NCheckedBackTriangle gamma omega
      (EMuApp ef ea) (EEffApp ef ea) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n_eval heap env rho
      (EEffApp ef ea) phi heap (VSummary theta) ->
    (forall n_summary phi_summary
      closure_env closure_rho f x ec ee arg
      gamma_body omega_body ty_body eff_body eff_summary,
      n_summary < n_bound ->
      CheckedStoreRuntimeContext gamma_body omega_body
        heap
        (env_extend x arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho ->
      NCheckedTcExp gamma_body omega_body ec ty_body eff_body ->
      NCheckedTcExp gamma_body omega_body ee TyEffect eff_summary ->
	      NCheckedBackTriangle gamma_body omega_body ec ee ->
      NStepsN n_summary
        (NInitialState heap
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ee)
        phi_summary
        (StDone heap (VSummary theta)) ->
      TraceCoveredBySummary phi_summary theta) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n_bound n_eval gamma omega heap env rho ef ea phi theta
    HBelow HCountEval HBack HContext HSummaryTraceSound
    HComp HCoveredBody.
  destruct
    (EEffApp_counted_checked_summary_heap_neutral_decomposition
      n_eval gamma omega heap env rho ef ea phi heap theta
      HBack HContext HSummaryTraceSound HComp)
    as (n_fun & n_arg & n_summary &
      phi_fun & phi_arg & phi_summary &
      closure_env & closure_rho & f & x & ec & ee & arg &
      HFun & HArg & HBody & HCountFun & HCountArg &
      HCountSummary & _ & HTrace).
  destruct
    (NCBT_App_components gamma omega ef ea HBack)
    as (_ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & _ & HBackFun & HBackArg).
  assert
    (HSummary :
      SummaryEvaluation heap env rho (EEffApp ef ea)
        phi heap theta).
  {
    unfold SummaryEvaluation, CountedComputationEvaluation in *.
    eapply NStepsN_to_NSteps.
    exact HComp.
  }
  assert
    (HStoreContext :
      CheckedStoreRuntimeContext gamma omega heap env rho).
  {
    eapply CheckedRuntimeContext_to_store_context; eauto.
  }
  destruct
    (EEffApp_checked_summary_body_store_context_from_prefixes
      gamma omega heap env rho ef ea
      n_fun n_arg phi_fun phi_arg
      closure_env closure_rho f x ec ee arg
      HBack HStoreContext HFun HArg)
    as (gamma_body & omega_body & ty_body & ty_result &
      eff_body & eff_summary &
      HBodyContext & HCheckedBody & HCheckedSummary &
      HRawBodyBack).
  assert
    (HCoveredFun : TraceCoveredBySummary phi_fun theta).
  {
    eapply
      (HBelow
        n_fun gamma omega heap env rho
        ef (EEffApp ef ea)
        phi_fun heap
        (VClosure closure_env closure_rho f x ec ee)
        phi heap theta);
      eauto; lia.
  }
  assert
    (HCoveredArg : TraceCoveredBySummary phi_arg theta).
  {
    eapply
      (HBelow
        n_arg gamma omega heap env rho
        ea (EEffApp ef ea)
        phi_arg heap arg
        phi heap theta);
      eauto; lia.
  }
  subst phi.
  apply trace_covered_app_same.
  - exact HCoveredFun.
  - apply trace_covered_app_same.
    + exact HCoveredArg.
    + eapply
        (HCoveredBody
          n_summary phi_summary closure_env closure_rho
          f x ec ee arg
          ((x, ty_body) ::
            (f, TyArrow ty_body eff_body ty_result eff_summary) ::
            gamma_body)
          omega_body
          ty_result eff_body eff_summary).
      * lia.
      * exact HBodyContext.
      * exact HCheckedBody.
      * exact HCheckedSummary.
      * exact HRawBodyBack.
      * exact HBody.
Qed.

Theorem EEffApp_counted_checked_summary_trace_covered_from_store_entry_below_body_context :
  forall n_bound n_eval gamma omega heap env rho ef ea phi theta,
    CheckedStoreContextSmallStepCorrectnessBelow n_bound ->
    n_eval < n_bound ->
    NCheckedBackTriangle gamma omega
      (EMuApp ef ea) (EEffApp ef ea) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n_eval heap env rho
      (EEffApp ef ea) phi heap (VSummary theta) ->
    (forall n_summary phi_summary
      closure_env closure_rho f x ec ee arg
      gamma_body omega_body ty_body eff_body eff_summary,
      n_summary < n_bound ->
      CheckedStoreRuntimeContext gamma_body omega_body
        heap
        (env_extend x arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho ->
      NCheckedTcExp gamma_body omega_body ec ty_body eff_body ->
      NCheckedTcExp gamma_body omega_body ee TyEffect eff_summary ->
	      NCheckedBackTriangle gamma_body omega_body ec ee ->
      NStepsN n_summary
        (NInitialState heap
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ee)
        phi_summary
        (StDone heap (VSummary theta)) ->
      TraceCoveredBySummary phi_summary theta) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n_bound n_eval gamma omega heap env rho ef ea phi theta
    HBelow HCountEval HBack HContext HSummaryTraceSound
    HComp HCoveredBody.
  destruct
    (EEffApp_counted_checked_store_summary_heap_neutral_decomposition
      n_eval gamma omega heap env rho ef ea phi heap theta
      HBack HContext HSummaryTraceSound HComp)
    as (n_fun & n_arg & n_summary &
      phi_fun & phi_arg & phi_summary &
      closure_env & closure_rho & f & x & ec & ee & arg &
      HFun & HArg & HBody & HCountFun & HCountArg &
      HCountSummary & _ & HTrace).
  destruct
    (NCBT_App_components gamma omega ef ea HBack)
    as (_ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & _ & HBackFun & HBackArg).
  assert
    (HSummary :
      SummaryEvaluation heap env rho (EEffApp ef ea)
        phi heap theta).
  {
    unfold SummaryEvaluation, CountedComputationEvaluation in *.
    eapply NStepsN_to_NSteps.
    exact HComp.
  }
  destruct
    (EEffApp_checked_summary_body_store_context_from_prefixes
      gamma omega heap env rho ef ea
      n_fun n_arg phi_fun phi_arg
      closure_env closure_rho f x ec ee arg
      HBack HContext HFun HArg)
    as (gamma_body & omega_body & ty_body & ty_result &
      eff_body & eff_summary &
      HBodyContext & HCheckedBody & HCheckedSummary &
      HRawBodyBack).
  assert
    (HCoveredFun : TraceCoveredBySummary phi_fun theta).
  {
    eapply
      (HBelow
        n_fun gamma omega heap env rho
        ef (EEffApp ef ea)
        phi_fun heap
        (VClosure closure_env closure_rho f x ec ee)
        phi heap theta);
      eauto; lia.
  }
  assert
    (HCoveredArg : TraceCoveredBySummary phi_arg theta).
  {
    eapply
      (HBelow
        n_arg gamma omega heap env rho
        ea (EEffApp ef ea)
        phi_arg heap arg
        phi heap theta);
      eauto; lia.
  }
  subst phi.
  apply trace_covered_app_same.
  - exact HCoveredFun.
  - apply trace_covered_app_same.
    + exact HCoveredArg.
    + eapply
        (HCoveredBody
          n_summary phi_summary closure_env closure_rho
          f x ec ee arg
          ((x, ty_body) ::
            (f, TyArrow ty_body eff_body ty_result eff_summary) ::
            gamma_body)
          omega_body
          ty_result eff_body eff_summary).
      * lia.
      * exact HBodyContext.
      * exact HCheckedBody.
      * exact HCheckedSummary.
      * exact HRawBodyBack.
      * exact HBody.
Qed.

Theorem EEffApp_counted_checked_summary_trace_covered_from_store_below_summary_value :
  forall n_bound n_eval gamma omega heap env rho ef ea phi theta,
    CheckedStoreContextSmallStepCorrectnessBelow n_bound ->
    CheckedStoreSummaryValueSoundnessBelow n_bound ->
    n_eval < n_bound ->
    NCheckedBackTriangle gamma omega
      (EMuApp ef ea) (EEffApp ef ea) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n_eval heap env rho
      (EEffApp ef ea) phi heap (VSummary theta) ->
    (forall closure_env closure_rho f x ec ee arg
      gamma_body omega_body ty_body eff_body eff_summary,
      CheckedStoreRuntimeContext gamma_body omega_body
        heap
        (env_extend x arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho ->
      NCheckedTcExp gamma_body omega_body ec ty_body eff_body ->
      NCheckedTcExp gamma_body omega_body ee TyEffect eff_summary ->
      NCheckedBackTriangle gamma_body omega_body ec ee) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n_bound n_eval gamma omega heap env rho ef ea phi theta
    HBelow HSummaryValueBelow HCountEval HBack HContext
    HSummaryTraceSound HComp HBodyBack.
  eapply
    (EEffApp_counted_checked_summary_trace_covered_from_store_below_body_context
      n_bound n_eval gamma omega heap env rho ef ea phi theta).
  - exact HBelow.
  - exact HCountEval.
  - exact HBack.
  - exact HContext.
  - exact HSummaryTraceSound.
  - exact HComp.
  - intros n_summary phi_summary closure_env closure_rho
      f x ec ee arg gamma_body omega_body
      ty_body eff_body eff_summary HCountSummary
      HBodyContext HCheckedBody HCheckedSummary _HRawBodyBack HBody.
  pose proof
    (HBodyBack closure_env closure_rho f x ec ee arg
      gamma_body omega_body ty_body eff_body eff_summary
      HBodyContext HCheckedBody HCheckedSummary)
    as HBackBody.
  eapply
    (HSummaryValueBelow
      n_summary gamma_body omega_body heap
      (env_extend x arg
        (env_extend f
          (VClosure closure_env closure_rho f x ec ee)
          closure_env))
      closure_rho ec ee eff_summary phi_summary heap theta).
  + exact HCountSummary.
  + exact HBackBody.
  + exact HCheckedSummary.
  + exact HBodyContext.
  + unfold CountedComputationEvaluation.
    exact HBody.
Qed.

Theorem EEffApp_counted_checked_summary_trace_covered_from_store_entry_below_summary_value :
  forall n_bound n_eval gamma omega heap env rho ef ea phi theta,
    CheckedStoreContextSmallStepCorrectnessBelow n_bound ->
    CheckedStoreSummaryValueSoundnessBelow n_bound ->
    n_eval < n_bound ->
    NCheckedBackTriangle gamma omega
      (EMuApp ef ea) (EEffApp ef ea) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n_eval heap env rho
      (EEffApp ef ea) phi heap (VSummary theta) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n_bound n_eval gamma omega heap env rho ef ea phi theta
    HBelow HSummaryValueBelow HCountEval HBack HContext
    HSummaryTraceSound HComp.
  eapply
    (EEffApp_counted_checked_summary_trace_covered_from_store_entry_below_body_context
      n_bound n_eval gamma omega heap env rho ef ea phi theta).
  - exact HBelow.
  - exact HCountEval.
  - exact HBack.
  - exact HContext.
  - exact HSummaryTraceSound.
  - exact HComp.
  - intros n_summary phi_summary closure_env closure_rho
      f x ec ee arg gamma_body omega_body
      ty_body eff_body eff_summary HCountSummary
      HBodyContext _ HCheckedSummary HBodyBack HBody.
    eapply
      (HSummaryValueBelow
        n_summary gamma_body omega_body heap
        (env_extend x arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
        closure_env))
        closure_rho ec ee eff_summary phi_summary heap theta).
    + exact HCountSummary.
    + exact HBodyBack.
    + exact HCheckedSummary.
    + exact HBodyContext.
    + unfold CountedComputationEvaluation.
      exact HBody.
Qed.

Theorem EEffApp_counted_checked_summary_trace_covered_from_store_entry_at :
  forall n_eval gamma omega heap env rho ef ea phi theta,
    CheckedStoreContextSmallStepCorrectnessBelow n_eval ->
    CheckedStoreSummaryValueSoundnessBelow n_eval ->
    NCheckedBackTriangle gamma omega
      (EMuApp ef ea) (EEffApp ef ea) ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n_eval heap env rho
      (EEffApp ef ea) phi heap (VSummary theta) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n_eval gamma omega heap env rho ef ea phi theta
    HBelow HSummaryValueBelow HBack HContext
    HSummaryTraceSound HComp.
  destruct
    (EEffApp_counted_checked_store_summary_heap_neutral_decomposition
      n_eval gamma omega heap env rho ef ea phi heap theta
      HBack HContext HSummaryTraceSound HComp)
    as (n_fun & n_arg & n_summary &
      phi_fun & phi_arg & phi_summary &
      closure_env & closure_rho & f & x & ec & ee & arg &
      HFun & HArg & HBody & HCountFun & HCountArg &
      HCountSummary & _ & HTrace).
  destruct
    (NCBT_App_components gamma omega ef ea HBack)
    as (_ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & _ & HBackFun & HBackArg).
  destruct
    (EEffApp_checked_summary_body_store_context_from_prefixes
      gamma omega heap env rho ef ea
      n_fun n_arg phi_fun phi_arg
      closure_env closure_rho f x ec ee arg
      HBack HContext HFun HArg)
    as (gamma_body & omega_body & ty_body & ty_result &
      eff_body & eff_summary &
      HBodyContext & HCheckedBody & HCheckedSummary &
      HBodyBack).
  assert (HCoveredFun : TraceCoveredBySummary phi_fun theta).
  {
    eapply
      (HBelow
        n_fun gamma omega heap env rho
        ef (EEffApp ef ea)
        phi_fun heap
        (VClosure closure_env closure_rho f x ec ee)
        phi heap theta).
    - exact HCountFun.
    - exact HBackFun.
    - exact HContext.
    - unfold CountedComputationEvaluation. exact HFun.
    - unfold SummaryEvaluation, CountedComputationEvaluation in *.
      eapply NStepsN_to_NSteps. exact HComp.
  }
  assert (HCoveredArg : TraceCoveredBySummary phi_arg theta).
  {
    eapply
      (HBelow
        n_arg gamma omega heap env rho
        ea (EEffApp ef ea)
        phi_arg heap arg
        phi heap theta).
    - exact HCountArg.
    - exact HBackArg.
    - exact HContext.
    - unfold CountedComputationEvaluation. exact HArg.
    - unfold SummaryEvaluation, CountedComputationEvaluation in *.
      eapply NStepsN_to_NSteps. exact HComp.
  }
  assert (HCoveredSummary : TraceCoveredBySummary phi_summary theta).
  {
    eapply
      (HSummaryValueBelow
        n_summary
        ((x, ty_body) ::
          (f, TyArrow ty_body eff_body ty_result eff_summary) ::
          gamma_body)
        omega_body heap
        (env_extend x arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho ec ee eff_summary
        phi_summary heap theta).
    - exact HCountSummary.
    - exact HBodyBack.
    - exact HCheckedSummary.
    - exact HBodyContext.
    - unfold CountedComputationEvaluation.
      exact HBody.
  }
  subst phi.
  apply trace_covered_app_same.
  - exact HCoveredFun.
  - apply trace_covered_app_same; assumption.
Qed.

Theorem EEffApp_counted_summary_trace_covered_from_components :
  forall n heap env rho ef ea phi heap_final theta,
    NStepsN n
      (NInitialState heap env rho (EEffApp ef ea))
      phi
      (StDone heap_final (VSummary theta)) ->
    (forall n_fun phi_fun heap_fun
      (closure_env : NEnv) (closure_rho : Rho)
      (f x : VarId) (ec ee : NExpr),
      n_fun < n ->
      NStepsN n_fun
        (NInitialState heap env rho ef)
        phi_fun
        (StDone heap_fun
          (VClosure closure_env closure_rho f x ec ee)) ->
      TraceCoveredBySummary phi_fun theta) ->
    (forall n_arg phi_arg heap_fun
      (closure_env : NEnv) (closure_rho : Rho)
      (f x : VarId) (ec ee : NExpr)
      (arg : NVal) heap_arg,
      n_arg < n ->
      NStepsN n_arg
        (NInitialState heap_fun env rho ea)
        phi_arg
        (StDone heap_arg arg) ->
      TraceCoveredBySummary phi_arg theta) ->
    (forall n_summary phi_summary heap_arg
      (closure_env : NEnv) (closure_rho : Rho)
      (f x : VarId) (ec ee : NExpr) (arg : NVal),
      n_summary < n ->
      NStepsN n_summary
        (NInitialState heap_arg
          (env_extend x arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho ee)
        phi_summary
        (StDone heap_final (VSummary theta)) ->
      TraceCoveredBySummary phi_summary theta) ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n heap env rho ef ea phi heap_final theta
    HSummary HCoveredFun HCoveredArg HCoveredSummary.
  destruct
    (EEffApp_counted_decomposition
      n heap env rho ef ea phi heap_final theta HSummary)
    as (n_fun & n_arg & n_summary &
      phi_fun & phi_arg & phi_summary &
      closure_env & closure_rho & f & x & ec & ee & arg & heap_arg &
      heap_fun & HFun & HArg & HBody & HCountFun & HCountArg &
      HCountSummary & HTrace).
  subst phi.
  apply trace_covered_app_same.
  - eapply (HCoveredFun n_fun phi_fun heap_fun closure_env closure_rho
      f x ec ee);
      eauto.
  - apply trace_covered_app_same.
    + eapply (HCoveredArg n_arg phi_arg heap_fun closure_env closure_rho
        f x ec ee arg heap_arg);
        eauto.
    + eapply (HCoveredSummary n_summary phi_summary heap_arg
        closure_env closure_rho f x ec ee arg);
        eauto.
Qed.
