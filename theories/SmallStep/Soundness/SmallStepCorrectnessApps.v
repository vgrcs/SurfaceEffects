From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Wf_nat.

(* Application and effect-application correctness lemmas. *)

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepPairParDispatch.
Require Import theories.Runtime.SmallStepTraceSafety.
Require Import theories.Runtime.SmallStepStructuredTrace.
Require Import theories.Runtime.SmallStepCorrectness.
Require Import theories.Runtime.SmallStepEffectSoundness.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.DynamicActions.
Require Import theories.Core.Expressions.
Require Import theories.Core.StaticActions.
Require Import theories.Core.Values.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.EffectFacts.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.TraceTypingFacts.
Require Import theories.Meta.TypingWeakeningFacts.
Require Import theories.Meta.TypeFacts.


Require Export theories.Soundness.SmallStepCorrectnessBase.

Lemma ScheduledMuAppTerminalFirstStep :
  forall heap env rho ef ea phi heap_final v_final,
    ScheduledStepsPhi
      (initial_state heap env rho (Mu_App ef ea))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      ScheduledStepsPhi
        (StEval heap env rho ef (KMuAppFun ea env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi_as_list phi = label_trace Silent ++ phi_as_list phi_tail.
Proof.
  intros heap env rho ef ea phi heap_final v_final HSteps.
  eapply ScheduledStepsPhi_known_step_terminal_inv; eauto.
  - simpl. exact I.
  - constructor.
Qed.

Lemma ScheduledEffAppTerminalFirstStep :
  forall heap env rho ef ea phi heap_final v_final,
    ScheduledStepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi
      (StDone heap_final v_final) ->
    exists phi_tail,
      ScheduledStepsPhi
        (StEval heap env rho ef (KEffAppFun ea env rho KDone))
        phi_tail
        (StDone heap_final v_final) /\
      phi_as_list phi = label_trace Silent ++ phi_as_list phi_tail.
Proof.
  intros heap env rho ef ea phi heap_final v_final HSteps.
  eapply ScheduledStepsPhi_known_step_terminal_inv; eauto.
  - simpl. exact I.
  - constructor.
Qed.

Lemma ScheduledCheckedTerminal_known_step_inv :
  forall state label state' phi heap_done v_done,
    NotPairParEvalState state ->
    Step state label state' ->
    ScheduledCheckedTerminal state phi heap_done v_done ->
    exists phi_tail,
      ScheduledCheckedTerminal state' phi_tail heap_done v_done /\
      phi_as_list phi = label_trace label ++ phi_as_list phi_tail.
Proof.
  intros state label state' phi heap_done v_done
    HNotPair HStep HRun.
  inversion HRun; subst.
  - exfalso. eapply done_no_step; eauto.
  - destruct
      (step_deterministic
        state label state' label0 state'0
        (NotPairParEvalState_non_pairpar_run state HNotPair)
        HStep H0)
      as (HLabel & HState).
    subst.
    exists phi0.
    split; [assumption |].
    simpl. now rewrite phi_as_list_label_phi.
	  - simpl in HNotPair. contradiction.
Qed.

Lemma ScheduledCheckedTerminal_nonpair_terminal_inv_step :
  forall state phi heap_done v_done,
    NotPairParEvalState state ->
    ~ Terminal state ->
    ScheduledCheckedTerminal state phi heap_done v_done ->
    exists label state' phi_tail,
      Step state label state' /\
      ScheduledCheckedTerminal state' phi_tail heap_done v_done /\
      phi_as_list phi = label_trace label ++ phi_as_list phi_tail.
Proof.
  intros state phi heap_done v_done HNotPair HNotTerminal HRun.
  inversion HRun; subst.
  - exfalso. apply HNotTerminal. constructor.
  - exists label, state', phi0.
    repeat split; eauto.
    simpl. now rewrite phi_as_list_label_phi.
  - simpl in HNotPair. contradiction.
Qed.

Lemma PairParLoosePackedStepsPhi_strip_return_kont :
  forall left right k tail phi_sched phi_left phi_right heap v_left v_right,
    PairParLoosePackedStepsPhi
      (PPS_Run left right (kont_append k tail))
      phi_sched
      Phi_Nil
      phi_left
      phi_right
      (PPS_State
        (StReturn heap (Pair (v_left, v_right)) (kont_append k tail))) ->
    PairParLoosePackedStepsPhi
      (PPS_Run left right k)
      phi_sched
      Phi_Nil
      phi_left
      phi_right
      (PPS_State
        (StReturn heap (Pair (v_left, v_right)) k)).
Proof.
	  intros left right k tail phi_sched phi_left phi_right
	    heap v_left v_right HSteps.
	  dependent induction HSteps.
	  - eapply PairParLoosePackedStepsPhi_Left; eauto.
	  - eapply PairParLoosePackedStepsPhi_Right; eauto.
	  - apply PairParLoosePackedStepsPhi_Done.
	    dependent destruction HSteps.
	    constructor.
Qed.

Lemma ScheduledCheckedTerminal_return_kdone :
  forall heap v,
    ScheduledCheckedTerminal
      (StReturn heap v KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      heap
      v.
Proof.
  intros heap v.
  eapply ScheduledCheckedTerminal_Step.
  - simpl. exact I.
  - constructor.
  - constructor.
Qed.

Lemma ScheduledCheckedTerminal_return_kdone_trace_nil :
  forall heap v phi heap_final v_final,
    ScheduledCheckedTerminal
      (StReturn heap v KDone)
      phi
      heap_final
      v_final ->
    phi_as_list phi = nil.
Proof.
  intros heap v phi heap_final v_final HRun.
  inversion HRun; subst; try discriminate.
  - match goal with
    | HStep : Step (StReturn heap v KDone) _ _ |- _ =>
        inversion HStep; subst
    end.
    match goal with
    | HTail : ScheduledCheckedTerminal (StDone heap v) _ _ _ |- _ =>
        inversion HTail; subst; try solve [exfalso; eapply done_no_step; eauto]
    end.
    reflexivity.
Qed.

Lemma ScheduledCheckedTerminal_append_kont_terminal_decompose :
  forall app phi heap_final v_final,
    ScheduledCheckedTerminal app phi heap_final v_final ->
    forall state tail,
      app = state_append_kont state tail ->
      ~ Terminal state ->
      exists heap_mid v_mid phi_state phi_tail,
        ScheduledCheckedTerminal state phi_state heap_mid v_mid /\
        ScheduledCheckedTerminal
          (StReturn heap_mid v_mid tail)
          phi_tail
          heap_final
          v_final /\
        phi_as_list phi =
          phi_as_list phi_state ++ phi_as_list phi_tail.
Proof.
  intros app phi heap_final v_final HRun.
  induction HRun as
	    [heap v
	    | app label app' phi_tail heap_final v_final
	        HNotPair HStep HRunTail IH
    | heap env rho ef1 ea1 ef2 ea2 k
        phi_eff1 phi_eff2 phi_pair phi_tail phi_left phi_right
        heap_eff1 heap_eff2 theta1 theta2
        heap_right v_right heap_left v_left
        heap_final v_final
        HSummary1 IHSummary1
        HSummary2 IHSummary2
        HPass HLoose
        HRight IHRight
        HLeft IHLeft
        HTail IHTail];
	    intros state tail HApp HNotTerminal.
	  - destruct state as
	      [heap0 env0 rho0 e0 k0 | heap0 v0 k0 | heap0 v0 | left right k0];
	      simpl in HApp; try discriminate.
	  - subst app.
    destruct
      (Step_append_kont_inv state tail label app' HNotTerminal HStep)
      as [(state0 & HStepState & HApp' & HNotTerminal0) |
          (heap_mid & v_mid & HState & HStepTail)].
    + destruct (IH state0 tail HApp' HNotTerminal0)
        as (heap_mid & v_mid & phi_state & phi_tail_final &
            HStateRun & HTailRun & HTrace).
      exists heap_mid, v_mid,
        (Phi_Seq (label_phi label) phi_state), phi_tail_final.
      split.
      * eapply ScheduledCheckedTerminal_Step.
        -- eapply NotPairParEvalState_append_kont_inv; eauto.
        -- exact HStepState.
        -- exact HStateRun.
      * split; [exact HTailRun |].
        simpl. rewrite phi_as_list_label_phi.
        rewrite HTrace.
        rewrite app_assoc.
        reflexivity.
    + subst state.
      exists heap_mid, v_mid,
        (Phi_Seq (label_phi Silent) Phi_Nil),
        (Phi_Seq (label_phi label) phi_tail).
      split.
      * apply ScheduledCheckedTerminal_return_kdone.
      * split.
        -- eapply ScheduledCheckedTerminal_Step.
	           ++ simpl. exact I.
	           ++ exact HStepTail.
	           ++ exact HRunTail.
        -- simpl. rewrite phi_as_list_label_phi. reflexivity.
	  - destruct state as
	      [heap0 env0 rho0 e0 k0 | heap0 v0 k0 | heap0 v0 | left right k0];
      simpl in HApp; try discriminate.
    inversion HApp; subst.
    destruct
      (IHTail (StReturn heap_left (Pair (v_left, v_right)) k0) tail)
      as (heap_mid & v_mid & phi_tail_state & phi_tail_final &
          HTailState & HTailFinal & HTraceTail).
    + reflexivity.
    + intros HTerminal. inversion HTerminal.
    + pose proof
        (PairParLoosePackedStepsPhi_strip_return_kont
          (initial_state heap_eff2 env0 rho0 (Mu_App ef1 ea1))
          (initial_state heap_eff2 env0 rho0 (Mu_App ef2 ea2))
          k0 tail phi_pair phi_left phi_right
          heap_left v_left v_right HLoose)
        as HLooseBase.
      exists heap_mid, v_mid,
        (pairpar_checked_packed_structured_trace
          phi_eff1 phi_eff2 (Phi_Seq phi_pair phi_tail_state)),
        phi_tail_final.
      split.
      * eapply ScheduledCheckedTerminal_CheckedPairPar; eauto.
      * split; [exact HTailFinal |].
        unfold pairpar_checked_packed_structured_trace.
        simpl.
        rewrite HTraceTail.
        repeat rewrite app_assoc.
        reflexivity.
Qed.

Lemma ScheduledCheckedTerminal_initial_with_kont_terminal_decompose :
  forall heap env rho e tail phi heap_final v_final,
    ScheduledCheckedTerminal
      (StEval heap env rho e tail)
      phi
      heap_final
      v_final ->
    exists heap_mid v_mid phi_expr phi_tail,
      ScheduledCheckedTerminal
        (initial_state heap env rho e)
        phi_expr
        heap_mid
        v_mid /\
      ScheduledCheckedTerminal
        (StReturn heap_mid v_mid tail)
        phi_tail
        heap_final
        v_final /\
      phi_as_list phi =
        phi_as_list phi_expr ++ phi_as_list phi_tail.
Proof.
  intros heap env rho e tail phi heap_final v_final HRun.
  eapply
    (ScheduledCheckedTerminal_append_kont_terminal_decompose
      (StEval heap env rho e tail)
      phi heap_final v_final HRun
      (StEval heap env rho e KDone) tail).
  - reflexivity.
  - intros HTerminal. inversion HTerminal.
Qed.

Lemma ScheduledCheckedTerminal_as_stepsphi_exists :
  forall state phi heap v,
    ScheduledCheckedTerminal state phi heap v ->
    exists phi_steps,
      StepsPhi state phi_steps (StDone heap v) /\
      phi_as_list phi_steps = phi_as_list phi.
Proof.
  intros state phi heap v HRun.
  destruct
    (Steps_as_StepsPhi_exists
      state (phi_as_list phi) (StDone heap v))
    as (phi_steps & HStepsPhi & HTrace).
  - eapply ScheduledCheckedTerminal_as_steps; eauto.
  - exists phi_steps.
    split; assumption.
Qed.

Lemma ScheduledCheckedTerminal_empty_summary_theta :
  forall heap env rho phi heap_summary theta,
    ScheduledCheckedTerminal
      (initial_state heap env rho Empty)
      phi
      heap_summary
      (Eff theta) ->
    theta = Theta_Empty.
Proof.
  intros heap env rho phi heap_summary theta HRun.
  destruct
    (ScheduledCheckedTerminal_as_stepsphi_exists
      (initial_state heap env rho Empty)
      phi heap_summary (Eff theta) HRun)
    as (phi_steps & HSteps & _HTrace).
  eapply StepsPhi_empty_summary_theta; eauto.
Qed.

Lemma ScheduledCheckedTerminal_top_summary_theta :
  forall heap env rho phi heap_summary theta,
    ScheduledCheckedTerminal
      (initial_state heap env rho Top)
      phi
      heap_summary
      (Eff theta) ->
    theta = Theta_Top.
Proof.
  intros heap env rho phi heap_summary theta HRun.
  destruct
    (ScheduledCheckedTerminal_as_stepsphi_exists
      (initial_state heap env rho Top)
      phi heap_summary (Eff theta) HRun)
    as (phi_steps & HSteps & _HTrace).
  eapply StepsPhi_top_summary_theta; eauto.
Qed.

Inductive ScheduledCheckedTerminalN :
  nat -> State -> Phi -> Heap -> Val -> Prop :=
| ScheduledCheckedTerminalN_Done :
    forall heap v,
      ScheduledCheckedTerminalN 0 (StDone heap v) Phi_Nil heap v
| ScheduledCheckedTerminalN_Step :
    forall n state label state' phi heap_final v_final,
      NotPairParEvalState state ->
      Step state label state' ->
      ScheduledCheckedTerminalN n state' phi heap_final v_final ->
      ScheduledCheckedTerminalN
        (S n)
        state
        (Phi_Seq (label_phi label) phi)
        heap_final
        v_final
| ScheduledCheckedTerminalN_CheckedPairPar :
    forall n_eff1 n_eff2 n_right n_left n_tail
      heap env rho ef1 ea1 ef2 ea2 k
      phi_eff1 phi_eff2 phi_pair phi_tail phi_left phi_right
      heap_eff1 heap_eff2 theta1 theta2
      heap_right v_right heap_left v_left
      heap_final v_final,
      ScheduledCheckedTerminalN n_eff1
        (initial_state heap env rho (Eff_App ef1 ea1))
        phi_eff1
        heap_eff1
        (Eff theta1) ->
      ScheduledCheckedTerminalN n_eff2
        (initial_state heap_eff1 env rho (Eff_App ef2 ea2))
        phi_eff2
        heap_eff2
        (Eff theta2) ->
      PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 ->
      PairParLoosePackedStepsPhi
        (pairpar_checked_start heap_eff2 env rho ef1 ea1 ef2 ea2 k)
        phi_pair
        Phi_Nil
        phi_left
        phi_right
        (PPS_State
          (StReturn heap_left (Pair (v_left, v_right)) k)) ->
      ScheduledCheckedTerminalN n_right
        (initial_state heap_eff2 env rho (Mu_App ef2 ea2))
        phi_right
        heap_right
        v_right ->
      ScheduledCheckedTerminalN n_left
        (with_state_heap heap_right
          (initial_state heap_eff2 env rho (Mu_App ef1 ea1)))
        phi_left
        heap_left
        v_left ->
      ScheduledCheckedTerminalN n_tail
        (StReturn heap_left (Pair (v_left, v_right)) k)
        phi_tail
        heap_final
        v_final ->
      ScheduledCheckedTerminalN
        (S (n_eff1 + n_eff2 + n_right + n_left + n_tail))
        (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
        (pairpar_checked_packed_structured_trace
          phi_eff1 phi_eff2 (Phi_Seq phi_pair phi_tail))
        heap_final
        v_final.

Lemma ScheduledCheckedTerminalN_to_terminal :
  forall n state phi heap v,
    ScheduledCheckedTerminalN n state phi heap v ->
    ScheduledCheckedTerminal state phi heap v.
Proof.
  intros n state phi heap v HRun.
  induction HRun.
  - constructor.
  - eapply ScheduledCheckedTerminal_Step; eauto.
  - eapply ScheduledCheckedTerminal_CheckedPairPar; eauto.
Qed.

Lemma ScheduledCheckedTerminalN_as_stepsphi_exists :
  forall n state phi heap v,
    ScheduledCheckedTerminalN n state phi heap v ->
    exists phi_steps,
      StepsPhi state phi_steps (StDone heap v) /\
      phi_as_list phi_steps = phi_as_list phi.
Proof.
  intros n state phi heap v HRun.
  eapply ScheduledCheckedTerminal_as_stepsphi_exists.
  eapply ScheduledCheckedTerminalN_to_terminal; eauto.
Qed.

Lemma ScheduledCheckedTerminalN_empty_static_terminal_sound :
  forall n heap env rho e phi heap' v stty ctxt rgns ty,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty, Empty_Static_Action) ->
    ScheduledCheckedTerminalN n
      (initial_state heap env rho e)
      phi heap' v ->
    phi ⋞ Theta_Empty.
Proof.
  intros n heap env rho e phi heap' v stty ctxt rgns ty
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HRun.
  destruct
    (ScheduledCheckedTerminalN_as_stepsphi_exists
      n (initial_state heap env rho e) phi heap' v HRun)
    as (phi_steps & HSteps & HTrace).
  eapply Phi_Theta_Soundness_of_phi_as_list_eq.
  - symmetry. exact HTrace.
  - eapply SmallStep_empty_static_terminal_sound; eauto.
Qed.

Lemma ScheduledCheckedTerminalN_empty_static_terminal_empty_summary_sound :
  forall n heap env rho e phi heap' v
    phi_summary heap_summary theta stty ctxt rgns ty,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty, Empty_Static_Action) ->
    ScheduledCheckedTerminalN n
      (initial_state heap env rho e)
      phi heap' v ->
    ScheduledCheckedTerminal
      (initial_state heap env rho Empty)
      phi_summary
      heap_summary
      (Eff theta) ->
    phi ⋞ theta.
Proof.
  intros n heap env rho e phi heap' v
    phi_summary heap_summary theta stty ctxt rgns ty
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp HRun HSummary.
  pose proof
    (ScheduledCheckedTerminal_empty_summary_theta
      heap env rho phi_summary heap_summary theta HSummary)
    as HTheta.
  subst theta.
  eapply ScheduledCheckedTerminalN_empty_static_terminal_sound; eauto.
Qed.

Lemma ScheduledCheckedTerminalN_terminal_top_summary_sound :
  forall n heap env rho e phi heap' v
    phi_summary heap_summary theta,
    ScheduledCheckedTerminalN n
      (initial_state heap env rho e)
      phi heap' v ->
    ScheduledCheckedTerminal
      (initial_state heap env rho Top)
      phi_summary
      heap_summary
      (Eff theta) ->
    phi ⋞ theta.
Proof.
  intros n heap env rho e phi heap' v
    phi_summary heap_summary theta _HRun HSummary.
  pose proof
    (ScheduledCheckedTerminal_top_summary_theta
      heap env rho phi_summary heap_summary theta HSummary)
    as HTheta.
  subst theta.
  apply PhiInThetaTop.
Qed.

Lemma ScheduledCheckedTerminal_to_N :
  forall state phi heap v,
    ScheduledCheckedTerminal state phi heap v ->
    exists n, ScheduledCheckedTerminalN n state phi heap v.
Proof.
  intros state phi heap v HRun.
  induction HRun as
    [heap v
    | state label state' phi heap_final v_final
        HNotPair HStep _ IH
    | heap env rho ef1 ea1 ef2 ea2 k
        phi_eff1 phi_eff2 phi_pair phi_tail phi_left phi_right
        heap_eff1 heap_eff2 theta1 theta2
        heap_right v_right heap_left v_left
        heap_final v_final
        _ IHSummary1 _ IHSummary2 HObserved HLoose
        _ IHRight _ IHLeft _ IHTail].
  - exists 0. constructor.
  - destruct IH as (n & HRunN).
    exists (S n).
    eapply ScheduledCheckedTerminalN_Step; eauto.
  - destruct IHSummary1 as (n_eff1 & HSummary1N).
    destruct IHSummary2 as (n_eff2 & HSummary2N).
    destruct IHRight as (n_right & HRightN).
    destruct IHLeft as (n_left & HLeftN).
    destruct IHTail as (n_tail & HTailN).
    exists (S (n_eff1 + n_eff2 + n_right + n_left + n_tail)).
    eapply ScheduledCheckedTerminalN_CheckedPairPar; eauto.
Qed.

Lemma ScheduledCheckedTerminalN_return_kdone :
  forall heap v,
    ScheduledCheckedTerminalN 1
      (StReturn heap v KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      heap
      v.
Proof.
  intros heap v.
  eapply ScheduledCheckedTerminalN_Step.
  - simpl. exact I.
  - constructor.
  - constructor.
Qed.

Lemma ScheduledCheckedTerminalN_nonpair_terminal_inv_step :
  forall n state phi heap_done v_done,
    NotPairParEvalState state ->
    ~ Terminal state ->
    ScheduledCheckedTerminalN n state phi heap_done v_done ->
    exists n_tail label state' phi_tail,
      n = S n_tail /\
      Step state label state' /\
      ScheduledCheckedTerminalN n_tail state' phi_tail heap_done v_done /\
      phi_as_list phi = label_trace label ++ phi_as_list phi_tail.
Proof.
  intros n state phi heap_done v_done HNotPair HNotTerminal HRun.
  inversion HRun; subst.
  - exfalso. apply HNotTerminal. constructor.
  - exists n0, label, state', phi0.
    repeat split; eauto.
    simpl. now rewrite phi_as_list_label_phi.
  - simpl in HNotPair. contradiction.
Qed.

Lemma ScheduledCheckedTerminalN_append_kont_terminal_decompose :
  forall n app phi heap_final v_final,
    ScheduledCheckedTerminalN n app phi heap_final v_final ->
    forall state tail,
      app = state_append_kont state tail ->
      ~ Terminal state ->
      exists n_state n_tail heap_mid v_mid phi_state phi_tail,
        ScheduledCheckedTerminalN
          n_state state phi_state heap_mid v_mid /\
        ScheduledCheckedTerminalN
          n_tail
          (StReturn heap_mid v_mid tail)
          phi_tail
          heap_final
          v_final /\
        n_state <= n /\
        n_tail <= n /\
        phi_as_list phi =
          phi_as_list phi_state ++ phi_as_list phi_tail.
Proof.
  intros n app phi heap_final v_final HRun.
  induction HRun as
    [heap v
    | n app label app' phi_tail heap_final v_final
        HNotPair HStep HRunTail IH
    | n_eff1 n_eff2 n_right n_left n_tail
        heap env rho ef1 ea1 ef2 ea2 k
        phi_eff1 phi_eff2 phi_pair phi_tail phi_left phi_right
        heap_eff1 heap_eff2 theta1 theta2
        heap_right v_right heap_left v_left
        heap_final v_final
        HSummary1 IHSummary1
        HSummary2 IHSummary2
        HObserved HLoose
        HRight IHRight
        HLeft IHLeft
        HTail IHTail];
    intros state tail HApp HNotTerminal.
  - destruct state as
      [heap0 env0 rho0 e0 k0 | heap0 v0 k0 | heap0 v0 | left right k0];
      simpl in HApp; try discriminate.
  - subst app.
    destruct
      (Step_append_kont_inv state tail label app' HNotTerminal HStep)
      as [(state0 & HStepState & HApp' & HNotTerminal0) |
          (heap_mid & v_mid & HState & HStepTail)].
    + destruct (IH state0 tail HApp' HNotTerminal0)
        as (n_state & n_tail & heap_mid & v_mid &
            phi_state & phi_tail_final &
            HStateRun & HTailRun & HStateLe & HTailLe & HTrace).
      exists (S n_state), n_tail, heap_mid, v_mid,
        (Phi_Seq (label_phi label) phi_state), phi_tail_final.
      split.
      * eapply ScheduledCheckedTerminalN_Step.
        -- eapply NotPairParEvalState_append_kont_inv; eauto.
        -- exact HStepState.
        -- exact HStateRun.
      * split; [exact HTailRun |].
        split; [lia |].
        split; [lia |].
        simpl. rewrite phi_as_list_label_phi.
        rewrite HTrace.
        rewrite app_assoc.
        reflexivity.
    + subst state.
      exists 1, (S n), heap_mid, v_mid,
        (Phi_Seq (label_phi Silent) Phi_Nil),
        (Phi_Seq (label_phi label) phi_tail).
      split.
      * apply ScheduledCheckedTerminalN_return_kdone.
      * split.
        -- eapply ScheduledCheckedTerminalN_Step.
           ++ simpl. exact I.
           ++ exact HStepTail.
           ++ exact HRunTail.
        -- split; [lia |].
           split; [lia |].
           simpl. rewrite phi_as_list_label_phi. reflexivity.
  - destruct state as
      [heap0 env0 rho0 e0 k0 | heap0 v0 k0 | heap0 v0 | left right k0];
      simpl in HApp; try discriminate.
    inversion HApp; subst.
    destruct
      (IHTail (StReturn heap_left (Pair (v_left, v_right)) k0) tail)
      as (n_tail_state & n_tail_final &
          heap_mid & v_mid & phi_tail_state & phi_tail_final &
          HTailState & HTailFinal & HTailStateLe &
          HTailFinalLe & HTraceTail).
    + reflexivity.
    + intros HTerminal. inversion HTerminal.
    + pose proof
        (PairParLoosePackedStepsPhi_strip_return_kont
          (initial_state heap_eff2 env0 rho0 (Mu_App ef1 ea1))
          (initial_state heap_eff2 env0 rho0 (Mu_App ef2 ea2))
          k0 tail phi_pair phi_left phi_right
          heap_left v_left v_right HLoose)
        as HLooseBase.
      exists
        (S (n_eff1 + n_eff2 + n_right + n_left + n_tail_state)),
        n_tail_final,
        heap_mid,
        v_mid,
        (pairpar_checked_packed_structured_trace
          phi_eff1 phi_eff2 (Phi_Seq phi_pair phi_tail_state)),
        phi_tail_final.
      split.
      * eapply ScheduledCheckedTerminalN_CheckedPairPar; eauto.
      * split; [exact HTailFinal |].
        split; [lia |].
        split; [lia |].
        unfold pairpar_checked_packed_structured_trace.
        simpl.
        rewrite HTraceTail.
        repeat rewrite app_assoc.
        reflexivity.
Qed.

Lemma ScheduledCheckedTerminalN_initial_with_kont_terminal_decompose :
  forall n heap env rho e tail phi heap_final v_final,
    ScheduledCheckedTerminalN n
      (StEval heap env rho e tail)
      phi
      heap_final
      v_final ->
    exists n_expr n_tail heap_mid v_mid phi_expr phi_tail,
      ScheduledCheckedTerminalN n_expr
        (initial_state heap env rho e)
        phi_expr
        heap_mid
        v_mid /\
      ScheduledCheckedTerminalN n_tail
        (StReturn heap_mid v_mid tail)
        phi_tail
        heap_final
        v_final /\
      n_expr <= n /\
      n_tail <= n /\
      phi_as_list phi =
        phi_as_list phi_expr ++ phi_as_list phi_tail.
Proof.
  intros n heap env rho e tail phi heap_final v_final HRun.
  eapply
    (ScheduledCheckedTerminalN_append_kont_terminal_decompose
      n (StEval heap env rho e tail)
      phi heap_final v_final HRun
      (StEval heap env rho e KDone) tail).
  - reflexivity.
  - intros HTerminal. inversion HTerminal.
Qed.

Theorem ScheduledCheckedMuAppTerminalDecomposeN :
  forall n heap env rho ef ea phi heap_final v_final,
    ScheduledCheckedTerminalN n
      (initial_state heap env rho (Mu_App ef ea))
      phi
      heap_final
      v_final ->
    exists n_fun n_arg n_body
      phi_fun phi_arg phi_body
      heap_fun heap_arg env_closure rho_closure f x ec ee v_arg,
      n_fun < n /\
      n_arg < n /\
      n_body < n /\
      ScheduledCheckedTerminalN n_fun
        (initial_state heap env rho ef)
        phi_fun
        heap_fun
        (Cls (env_closure, rho_closure, Mu f x ec ee)) /\
      ScheduledCheckedTerminalN n_arg
        (initial_state heap_fun env rho ea)
        phi_arg
        heap_arg
        v_arg /\
      ScheduledCheckedTerminalN n_body
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body
        heap_final
        v_final /\
      phi_as_list phi =
        phi_as_list phi_fun ++
        phi_as_list phi_arg ++
        phi_as_list phi_body.
Proof.
  intros n heap env rho ef ea phi heap_final v_final HRun.
  destruct
    (ScheduledCheckedTerminalN_nonpair_terminal_inv_step
      n
      (initial_state heap env rho (Mu_App ef ea))
      phi heap_final v_final)
    as (n_tail & label_mu & state_mu & phi_tail &
        Hn & HStepMu & HRunTail & HTraceFirst).
  - simpl. exact I.
  - intros HTerminal. inversion HTerminal.
  - exact HRun.
  - {
    subst n.
    inversion HStepMu; subst.
    destruct
      (ScheduledCheckedTerminalN_initial_with_kont_terminal_decompose
        n_tail heap env rho ef (KMuAppFun ea env rho KDone)
        phi_tail heap_final v_final HRunTail)
      as (n_fun & n_after_fun & heap_fun & v_fun &
          phi_fun & phi_after_fun &
          HFun & HAfterFun & HFunLe & HAfterFunLe & HTraceFun).
  destruct
    (ScheduledCheckedTerminalN_nonpair_terminal_inv_step
      n_after_fun
      (StReturn heap_fun v_fun (KMuAppFun ea env rho KDone))
      phi_after_fun heap_final v_final)
    as (n_after_arg_start & label_arg & state_arg & phi_after_arg_start &
        HAfterFunEq & HStepArg & HAfterArgStart & HTraceArgStep).
  - simpl. exact I.
  - intros HTerminal. inversion HTerminal.
  - exact HAfterFun.
  - inversion HStepArg; subst.
    destruct
      (ScheduledCheckedTerminalN_initial_with_kont_terminal_decompose
        n_after_arg_start heap_fun env rho ea
        (KMuAppArg env' rho' f x ec ee KDone)
        phi_after_arg_start heap_final v_final HAfterArgStart)
      as (n_arg & n_after_arg & heap_arg & v_arg &
          phi_arg & phi_after_arg &
          HArg & HAfterArg & HArgLe & HAfterArgLe & HTraceArg).
    destruct
      (ScheduledCheckedTerminalN_nonpair_terminal_inv_step
        n_after_arg
        (StReturn heap_arg v_arg
          (KMuAppArg env' rho' f x ec ee KDone))
        phi_after_arg heap_final v_final)
      as (n_body & label_body & state_body & phi_body &
          HAfterArgEq & HStepBody & HBody & HTraceBodyStep).
    + simpl. exact I.
    + intros HTerminal. inversion HTerminal.
    + exact HAfterArg.
    + inversion HStepBody; subst.
      exists n_fun, n_arg, n_body.
      exists phi_fun, phi_arg, phi_body.
      exists heap_fun, heap_arg, env', rho', f, x, ec, ee, v_arg.
      repeat split; try assumption; try lia.
      simpl.
      rewrite HTraceFirst, HTraceFun, HTraceArgStep, HTraceArg, HTraceBodyStep.
      repeat rewrite app_nil_l.
      repeat rewrite app_nil_r.
      rewrite app_assoc.
      reflexivity.
    }
Qed.

Lemma DA_in_Phi_of_phi_as_list_eq :
  forall phi1 phi2 da,
    phi_as_list phi1 = phi_as_list phi2 ->
    DA_in_Phi da phi1 ->
    DA_in_Phi da phi2.
Proof.
  intros phi1 phi2 da HTrace HIn.
  apply In_phi_as_list_DA_in.
  pose proof (DA_in_Phi_in_phi_as_list da phi1 HIn) as HList.
  now rewrite HTrace in HList.
Qed.

Lemma ReadOnlyPhi_of_phi_as_list_eq :
  forall phi1 phi2,
    phi_as_list phi1 = phi_as_list phi2 ->
    ReadOnlyPhi phi1 ->
    ReadOnlyPhi phi2.
Proof.
  intros phi1 phi2 HTrace HReadOnly.
  apply ReadOnlyPhi_of_da_in_read.
  intros da HIn.
  eapply ReadOnlyPhi_da_in_read; eauto.
  eapply DA_in_Phi_of_phi_as_list_eq.
  - symmetry. exact HTrace.
  - exact HIn.
Qed.

Lemma PhiReadsSafe_of_phi_as_list_eq :
  forall heap phi1 phi2,
    phi_as_list phi1 = phi_as_list phi2 ->
    PhiReadsSafe heap phi1 ->
    PhiReadsSafe heap phi2.
Proof.
  unfold PhiReadsSafe.
  intros heap phi1 phi2 HTrace HSafe r l v HRead.
  apply HSafe.
  eapply DA_in_Phi_of_phi_as_list_eq.
  - symmetry. exact HTrace.
  - exact HRead.
Qed.

Lemma PhiWritesDisjointPhiReads_of_phi_as_list_eq_l :
  forall phi_write1 phi_write2 phi_read,
    phi_as_list phi_write1 = phi_as_list phi_write2 ->
    PhiWritesDisjointPhiReads phi_write1 phi_read ->
    PhiWritesDisjointPhiReads phi_write2 phi_read.
Proof.
  unfold PhiWritesDisjointPhiReads.
  intros phi_write1 phi_write2 phi_read HTrace HDisjoint
    r_write l_write v_write r_read l_read v_read HWrite HRead.
  eapply HDisjoint; eauto.
  eapply DA_in_Phi_of_phi_as_list_eq.
  - symmetry. exact HTrace.
  - exact HWrite.
Qed.

Theorem ScheduledCheckedEffectSummary_readonly_from_small_step_sound :
  forall heap env rho e stty ctxt rgns static_eff phi heap' theta,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, Ty_Effect, static_eff) ->
    ScheduledCheckedTerminal
      (initial_state heap env rho e)
      phi
      heap'
      (Eff theta) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff) ->
    ReadOnlyPhi phi.
Proof.
  intros heap env rho e stty ctxt rgns static_eff phi heap' theta
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff
    HRun HReadOnlyStatic.
  eapply effect_summary_trace_readonly_from_static_soundness; eauto.
  apply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
  eapply small_step_effect_summary_eff_sound; eauto.
  eapply ScheduledCheckedTerminal_as_steps; eauto.
Qed.

Theorem ScheduledCheckedEffectSummary_heap_neutral_from_small_step_sound :
  forall heap env rho e stty ctxt rgns static_eff phi heap' theta,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, Ty_Effect, static_eff) ->
    ScheduledCheckedTerminal
      (initial_state heap env rho e)
      phi
      heap'
      (Eff theta) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff) ->
    heap' = heap.
Proof.
  intros heap env rho e stty ctxt rgns static_eff phi heap' theta
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff
    HRun HReadOnlyStatic.
  pose proof
    (ScheduledCheckedEffectSummary_readonly_from_small_step_sound
      heap env rho e stty ctxt rgns static_eff phi heap' theta
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff
      HRun HReadOnlyStatic)
    as HReadOnly.
  destruct
    (ScheduledCheckedTerminal_as_stepsphi_exists
      (initial_state heap env rho e) phi heap' (Eff theta) HRun)
    as (phi_steps & HSteps & HTrace).
  assert (HReadOnlySteps : ReadOnlyPhi phi_steps).
  {
    eapply ReadOnlyPhi_of_phi_as_list_eq.
    - symmetry. exact HTrace.
    - exact HReadOnly.
  }
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho e)
      phi_steps
      (StDone heap' (Eff theta))
      HSteps HReadOnlySteps)
    as HHeap.
  simpl in HHeap.
  now symmetry.
Qed.

Definition with_pairpar_state_heap
    (heap : Heap) (state : PairParState) : PairParState :=
  match state with
  | PPS_State state => PPS_State (with_state_heap heap state)
  | PPS_Run left_state right_state k =>
      PPS_Run
        (with_state_heap heap left_state)
        (with_state_heap heap right_state)
        k
  end.

Lemma pairpar_state_heap_with_pairpar_state_heap :
  forall heap state,
    pairpar_state_heap (with_pairpar_state_heap heap state) = heap.
Proof.
  intros heap state.
  destruct state; simpl; apply state_heap_with_state_heap.
Qed.

Lemma PairParRunHeapsAgree_with_pairpar_state_heap :
  forall heap state,
    PairParRunHeapsAgree state ->
    PairParRunHeapsAgree (with_pairpar_state_heap heap state).
Proof.
  intros heap state HAgree.
  destruct state as [state | left right k]; simpl in *.
  - apply StateRunHeapsAgree_with_state_heap. exact HAgree.
  - destruct HAgree as [_ [HLeft HRight]].
    split.
    + repeat rewrite state_heap_with_state_heap. reflexivity.
    + split; apply StateRunHeapsAgree_with_state_heap; assumption.
Qed.

Lemma PairParRunHeapsAgree_pairpar_state_of_state :
  forall state,
    StateRunHeapsAgree state ->
    PairParRunHeapsAgree (pairpar_state_of_state state).
Proof.
  intros state HAgree.
  destruct state; simpl in *; assumption.
Qed.

Lemma NotPairParEvalState_with_state_heap :
  forall heap state,
    NotPairParEvalState state ->
    NotPairParEvalState (with_state_heap heap state).
Proof.
  intros heap state HNotPair.
  destruct state as
    [heap0 env rho e k | heap0 v k | heap0 v | left right k];
    simpl in *; try exact I; try contradiction.
  destruct e; simpl in *; assumption.
Qed.

Lemma with_pairpar_state_heap_pairpar_state_of_state :
  forall heap state,
    with_pairpar_state_heap heap (pairpar_state_of_state state) =
    pairpar_state_of_state (with_state_heap heap state).
Proof.
  intros heap state.
  destruct state; reflexivity.
Qed.

Lemma PairParLoosePackedStepsPhi_readonly_rebase_agree :
  forall state phi_sched phi_state phi_left phi_right state' heap,
    PairParLoosePackedStepsPhi
      state phi_sched phi_state phi_left phi_right state' ->
    PairParRunHeapsAgree state ->
    ReadOnlyPhi phi_sched ->
    PhiReadsSafe heap phi_sched ->
    PairParLoosePackedStepsPhi
      (with_pairpar_state_heap heap state)
      phi_sched phi_state phi_left phi_right
      (with_pairpar_state_heap heap state').
Proof.
  intros state phi_sched phi_state phi_left phi_right state' heap HSteps.
  revert heap.
  induction HSteps as
    [state
    | state label state' phi_sched phi_state phi_left phi_right state''
        HStep _ IH
    | left right k label left' phi_sched phi_state phi_left phi_right state''
        HStep _ IH
    | left right k label right' phi_sched phi_state phi_left phi_right state''
        HStep _ IH
    | heap0 v1 v2 k phi_sched phi_state phi_left phi_right state'' _ IH];
    intros heap HAgree HReadOnly HSafe.
  - constructor.
  - inversion HReadOnly as
      [| | phi_label phi_tail HReadOnlyLabel HReadOnlyTail |];
      subst.
    pose proof
      (LabelHeapSafe_of_readonly_label_reads_safe
        label heap phi_sched HReadOnlyLabel HSafe)
      as HLabelSafe.
    pose proof
      (Step_rebase_with_safe_label_agree
        state label state' heap HAgree HStep HLabelSafe)
      as HStepRebased.
    rewrite
      (label_result_heap_readonly label heap HReadOnlyLabel)
      in HStepRebased.
    eapply PairParLoosePackedStepsPhi_State.
    + exact HStepRebased.
    + rewrite <- with_pairpar_state_heap_pairpar_state_of_state.
      eapply IH.
      * eapply pairpar_step_preserves_heap_agreement.
        -- apply PairParRunHeapsAgree_pairpar_state_of_state.
           exact HAgree.
        -- apply pairpar_step_of_step. exact HStep.
      * exact HReadOnlyTail.
      * eapply PhiReadsSafe_seq_inv_r; eauto.
  - inversion HReadOnly as
      [| | phi_label phi_tail HReadOnlyLabel HReadOnlyTail |];
      subst.
    destruct HAgree as [HHeapAgree [HLeftAgree HRightAgree]].
    pose proof
      (LabelHeapSafe_of_readonly_label_reads_safe
        label heap phi_sched HReadOnlyLabel HSafe)
      as HLabelSafe.
    pose proof
      (Step_rebase_with_safe_label_agree
        left label left' heap HLeftAgree HStep HLabelSafe)
      as HStepRebased.
    rewrite
      (label_result_heap_readonly label heap HReadOnlyLabel)
      in HStepRebased.
    eapply PairParLoosePackedStepsPhi_Left.
    + exact HStepRebased.
    + replace
        (PPS_Run (with_state_heap heap left')
           (with_state_heap
             (state_heap (with_state_heap heap left'))
             (with_state_heap heap right)) k)
        with
        (with_pairpar_state_heap heap
          (PPS_Run left' (with_state_heap (state_heap left') right) k)).
      * eapply IH.
        -- simpl.
           split.
           ++ rewrite state_heap_with_state_heap.
              reflexivity.
           ++ split.
              ** eapply step_preserves_state_run_heaps_agree;
                   [exact HLeftAgree | exact HStep].
              ** apply StateRunHeapsAgree_with_state_heap.
                 exact HRightAgree.
        -- exact HReadOnlyTail.
        -- eapply PhiReadsSafe_seq_inv_r; eauto.
      * simpl.
        repeat rewrite with_state_heap_overwrite.
        rewrite state_heap_with_state_heap.
        reflexivity.
  - inversion HReadOnly as
      [| | phi_label phi_tail HReadOnlyLabel HReadOnlyTail |];
      subst.
    destruct HAgree as [HHeapAgree [HLeftAgree HRightAgree]].
    pose proof
      (LabelHeapSafe_of_readonly_label_reads_safe
        label heap phi_sched HReadOnlyLabel HSafe)
      as HLabelSafe.
    pose proof
      (Step_rebase_with_safe_label_agree
        right label right' heap HRightAgree HStep HLabelSafe)
      as HStepRebased.
    rewrite
      (label_result_heap_readonly label heap HReadOnlyLabel)
      in HStepRebased.
    eapply PairParLoosePackedStepsPhi_Right.
    + exact HStepRebased.
    + replace
        (PPS_Run
           (with_state_heap
             (state_heap (with_state_heap heap right'))
             (with_state_heap heap left))
           (with_state_heap heap right') k)
        with
        (with_pairpar_state_heap heap
          (PPS_Run (with_state_heap (state_heap right') left) right' k)).
      * eapply IH.
        -- simpl.
           split.
           ++ rewrite state_heap_with_state_heap.
              reflexivity.
           ++ split.
              ** apply StateRunHeapsAgree_with_state_heap.
                 exact HLeftAgree.
              ** eapply step_preserves_state_run_heaps_agree;
                   [exact HRightAgree | exact HStep].
        -- exact HReadOnlyTail.
        -- eapply PhiReadsSafe_seq_inv_r; eauto.
      * simpl.
        repeat rewrite with_state_heap_overwrite.
        rewrite state_heap_with_state_heap.
        reflexivity.
  - inversion HReadOnly as
      [| | phi_label phi_tail HReadOnlyLabel HReadOnlyTail |];
      subst.
    eapply PairParLoosePackedStepsPhi_Done.
    eapply IH.
    + simpl. exact I.
    + exact HReadOnlyTail.
    + eapply PhiReadsSafe_seq_inv_r; eauto.
Qed.

Lemma PhiReadsSafe_par_inv_l :
  forall heap phi1 phi2,
    PhiReadsSafe heap (Phi_Par phi1 phi2) ->
    PhiReadsSafe heap phi1.
Proof.
  unfold PhiReadsSafe.
  intros heap phi1 phi2 HSafe r l v HRead.
  apply HSafe.
  apply DAP_Par.
  now left.
Qed.

Lemma PhiReadsSafe_par_inv_r :
  forall heap phi1 phi2,
    PhiReadsSafe heap (Phi_Par phi1 phi2) ->
    PhiReadsSafe heap phi2.
Proof.
  unfold PhiReadsSafe.
  intros heap phi1 phi2 HSafe r l v HRead.
  apply HSafe.
  apply DAP_Par.
  now right.
Qed.

Lemma PairParLoosePackedStepsPhi_readonly_projections :
  forall state phi_sched phi_state phi_left phi_right state',
    PairParLoosePackedStepsPhi
      state phi_sched phi_state phi_left phi_right state' ->
    ReadOnlyPhi phi_sched ->
    ReadOnlyPhi phi_state /\
    ReadOnlyPhi phi_left /\
    ReadOnlyPhi phi_right.
Proof.
  intros state phi_sched phi_state phi_left phi_right state' HSteps.
  induction HSteps as
    [state
    | state label state' phi_sched phi_state phi_left phi_right state''
        _ _ IH
    | left right k label left' phi_sched phi_state phi_left phi_right state''
        _ _ IH
    | left right k label right' phi_sched phi_state phi_left phi_right state''
        _ _ IH
    | heap v1 v2 k phi_sched phi_state phi_left phi_right state'' _ IH];
    intros HReadOnly.
  - repeat split; constructor.
  - inversion HReadOnly as
      [| | phi_label phi_tail HReadOnlyLabel HReadOnlyTail |];
      subst.
    destruct (IH HReadOnlyTail) as (HStateRO & HLeftRO & HRightRO).
    repeat split; try assumption.
    constructor; assumption.
  - inversion HReadOnly as
      [| | phi_label phi_tail HReadOnlyLabel HReadOnlyTail |];
      subst.
    destruct (IH HReadOnlyTail) as (HStateRO & HLeftRO & HRightRO).
    repeat split; try assumption.
    constructor; assumption.
  - inversion HReadOnly as
      [| | phi_label phi_tail HReadOnlyLabel HReadOnlyTail |];
      subst.
    destruct (IH HReadOnlyTail) as (HStateRO & HLeftRO & HRightRO).
    repeat split; try assumption.
    constructor; assumption.
  - inversion HReadOnly as
      [| | phi_label phi_tail HReadOnlyLabel HReadOnlyTail |];
      subst.
    destruct (IH HReadOnlyTail) as (HStateRO & HLeftRO & HRightRO).
    repeat split; assumption.
Qed.

Lemma PairParLoosePackedStepsPhi_reads_safe_projections :
  forall heap state phi_sched phi_state phi_left phi_right state',
    PairParLoosePackedStepsPhi
      state phi_sched phi_state phi_left phi_right state' ->
    PhiReadsSafe heap phi_sched ->
    PhiReadsSafe heap phi_state /\
    PhiReadsSafe heap phi_left /\
    PhiReadsSafe heap phi_right.
Proof.
  intros heap state phi_sched phi_state phi_left phi_right state' HSteps.
  induction HSteps as
    [state
    | state label state' phi_sched phi_state phi_left phi_right state''
        _ _ IH
    | left right k label left' phi_sched phi_state phi_left phi_right state''
        _ _ IH
    | left right k label right' phi_sched phi_state phi_left phi_right state''
        _ _ IH
    | heap0 v1 v2 k phi_sched phi_state phi_left phi_right state'' _ IH];
    intros HSafe.
  - repeat split; unfold PhiReadsSafe; intros r l v HRead; inversion HRead.
  - destruct (IH (PhiReadsSafe_seq_inv_r _ _ _ HSafe))
      as (HStateSafe & HLeftSafe & HRightSafe).
    repeat split; try assumption.
    unfold PhiReadsSafe.
    intros r l v HRead.
    inversion HRead as [| | da phi_label phi_state_tail [HInLabel | HInTail]];
      subst.
    + eapply (PhiReadsSafe_seq_inv_l heap (label_phi label) phi_sched);
        eauto.
    + apply HStateSafe. exact HInTail.
  - destruct (IH (PhiReadsSafe_seq_inv_r _ _ _ HSafe))
      as (HStateSafe & HLeftSafe & HRightSafe).
    repeat split; try assumption.
    unfold PhiReadsSafe.
    intros r l v HRead.
    inversion HRead as [| | da phi_label phi_left_tail [HInLabel | HInTail]];
      subst.
    + eapply (PhiReadsSafe_seq_inv_l heap (label_phi label) phi_sched);
        eauto.
    + apply HLeftSafe. exact HInTail.
  - destruct (IH (PhiReadsSafe_seq_inv_r _ _ _ HSafe))
      as (HStateSafe & HLeftSafe & HRightSafe).
    repeat split; try assumption.
    unfold PhiReadsSafe.
    intros r l v HRead.
    inversion HRead as [| | da phi_label phi_right_tail [HInLabel | HInTail]];
      subst.
    + eapply (PhiReadsSafe_seq_inv_l heap (label_phi label) phi_sched);
        eauto.
    + apply HRightSafe. exact HInTail.
  - destruct (IH (PhiReadsSafe_seq_inv_r _ _ _ HSafe))
      as (HStateSafe & HLeftSafe & HRightSafe).
    repeat split; assumption.
Qed.

Theorem ScheduledCheckedTerminal_readonly_rebase_agree :
  forall state phi heap_final v_final heap,
    ScheduledCheckedTerminal state phi heap_final v_final ->
    StateRunHeapsAgree state ->
    ReadOnlyPhi phi ->
    PhiReadsSafe heap phi ->
    ScheduledCheckedTerminal
      (with_state_heap heap state)
      phi
      heap
      v_final.
Proof.
  intros state phi heap_final v_final heap HRun.
  revert heap.
  induction HRun as
    [heap0 v
    | state label state' phi heap_final v_final
        HNotPair HStep _ IH
    | heap0 env rho ef1 ea1 ef2 ea2 k
        phi_eff1 phi_eff2 phi_pair phi_tail phi_left phi_right
        heap_eff1 heap_eff2 theta1 theta2
        heap_right v_right heap_left v_left
        heap_final v_final
        HSummary1 IHSummary1
        HSummary2 IHSummary2
        HPass HLoose
        HRight IHRight
        HLeft IHLeft
        HTail IHTail];
    intros heap HAgree HReadOnly HSafe.
  - simpl.
    constructor.
  - inversion HReadOnly as
      [| | phi_label phi_tail HReadOnlyLabel HReadOnlyTail |];
      subst.
    pose proof
      (LabelHeapSafe_of_readonly_label_reads_safe
        label heap phi HReadOnlyLabel HSafe)
      as HLabelSafe.
    pose proof
      (Step_rebase_with_safe_label_agree
        state label state' heap HAgree HStep HLabelSafe)
      as HStepRebased.
    rewrite
      (label_result_heap_readonly label heap HReadOnlyLabel)
      in HStepRebased.
    eapply ScheduledCheckedTerminal_Step.
    + apply NotPairParEvalState_with_state_heap. exact HNotPair.
    + exact HStepRebased.
    + eapply IH.
      * eapply step_preserves_state_run_heaps_agree;
          [exact HAgree | exact HStep].
      * exact HReadOnlyTail.
      * eapply PhiReadsSafe_seq_inv_r; eauto.
  - destruct (ReadOnlyPhi_Seq_inv _ _ HReadOnly)
      as (HReadOnlyEffs & HReadOnlyRest).
    destruct (ReadOnlyPhi_Par_inv _ _ HReadOnlyEffs)
      as (HReadOnlyEff1 & HReadOnlyEff2).
    destruct (ReadOnlyPhi_Seq_inv _ _ HReadOnlyRest)
      as (HReadOnlyPair & HReadOnlyTail).
    pose proof (PhiReadsSafe_seq_inv_l _ _ _ HSafe) as HSafeEffs.
    pose proof (PhiReadsSafe_seq_inv_r _ _ _ HSafe) as HSafeRest.
    pose proof (PhiReadsSafe_par_inv_l _ _ _ HSafeEffs) as HSafeEff1.
    pose proof (PhiReadsSafe_par_inv_r _ _ _ HSafeEffs) as HSafeEff2.
    pose proof (PhiReadsSafe_seq_inv_l _ _ _ HSafeRest) as HSafePair.
    pose proof (PhiReadsSafe_seq_inv_r _ _ _ HSafeRest) as HSafeTail.
    destruct
      (PairParLoosePackedStepsPhi_readonly_projections
        (pairpar_checked_start heap_eff2 env rho ef1 ea1 ef2 ea2 k)
        phi_pair Phi_Nil phi_left phi_right
        (PPS_State (StReturn heap_left (Pair (v_left, v_right)) k))
        HLoose HReadOnlyPair)
      as (_HStateRO & HLeftRO & HRightRO).
    destruct
      (PairParLoosePackedStepsPhi_reads_safe_projections
        heap
        (pairpar_checked_start heap_eff2 env rho ef1 ea1 ef2 ea2 k)
        phi_pair Phi_Nil phi_left phi_right
        (PPS_State (StReturn heap_left (Pair (v_left, v_right)) k))
        HLoose HSafePair)
      as (_HStateSafe & HLeftSafe & HRightSafe).
    pose proof
      (PairParLoosePackedStepsPhi_readonly_rebase_agree
        (pairpar_checked_start heap_eff2 env rho ef1 ea1 ef2 ea2 k)
        phi_pair Phi_Nil phi_left phi_right
        (PPS_State (StReturn heap_left (Pair (v_left, v_right)) k))
        heap
        HLoose
        (pairpar_checked_initial_heaps_agree
          heap_eff2 env rho ef1 ea1 ef2 ea2 k)
        HReadOnlyPair HSafePair)
      as HLooseRebased.
    simpl in HLooseRebased.
    repeat rewrite with_state_heap_overwrite in HLooseRebased.
    eapply ScheduledCheckedTerminal_CheckedPairPar.
    + exact
        (IHSummary1 heap I HReadOnlyEff1 HSafeEff1).
    + exact
        (IHSummary2 heap I HReadOnlyEff2 HSafeEff2).
    + exact HPass.
    + exact HLooseRebased.
    + exact
        (IHRight heap I HRightRO HRightSafe).
    + exact
        (IHLeft heap
          (StateRunHeapsAgree_with_state_heap
            heap_right (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) I)
          HLeftRO HLeftSafe).
    + exact
        (IHTail heap I HReadOnlyTail HSafeTail).
Qed.

Lemma ScheduledCheckedMuAppTerminalFirstStep :
  forall heap env rho ef ea phi heap_final v_final,
    ScheduledCheckedTerminal
      (initial_state heap env rho (Mu_App ef ea))
      phi heap_final v_final ->
    exists phi_tail,
      ScheduledCheckedTerminal
        (StEval heap env rho ef (KMuAppFun ea env rho KDone))
        phi_tail heap_final v_final /\
      phi_as_list phi = label_trace Silent ++ phi_as_list phi_tail.
Proof.
  intros heap env rho ef ea phi heap_final v_final HRun.
  eapply ScheduledCheckedTerminal_known_step_inv; eauto.
  - simpl. exact I.
  - constructor.
Qed.

Lemma ScheduledCheckedEffAppTerminalFirstStep :
  forall heap env rho ef ea phi heap_final v_final,
    ScheduledCheckedTerminal
      (initial_state heap env rho (Eff_App ef ea))
      phi heap_final v_final ->
    exists phi_tail,
      ScheduledCheckedTerminal
        (StEval heap env rho ef (KEffAppFun ea env rho KDone))
        phi_tail heap_final v_final /\
      phi_as_list phi = label_trace Silent ++ phi_as_list phi_tail.
Proof.
  intros heap env rho ef ea phi heap_final v_final HRun.
  eapply ScheduledCheckedTerminal_known_step_inv; eauto.
  - simpl. exact I.
  - constructor.
Qed.

Theorem MuAppTerminalDecompose :
  forall heap env rho ef ea phi heap_final v_final,
    StepsPhi
      (initial_state heap env rho (Mu_App ef ea))
      phi
      (StDone heap_final v_final) ->
    exists phi_fun phi_arg phi_body
      heap_fun heap_arg env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun
        (StDone heap_fun
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap_fun env rho ea)
        phi_arg
        (StDone heap_arg v_arg) /\
      StepsPhi
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body
        (StDone heap_final v_final) /\
      phi_as_list phi =
        phi_as_list phi_fun ++
        phi_as_list phi_arg ++
        phi_as_list phi_body.
Proof.
  intros heap env rho ef ea phi heap_final v_final HSteps.
  pose proof
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Mu_App ef ea))
      Silent
      (StEval heap env rho ef (KMuAppFun ea env rho KDone))
      phi heap_final v_final)
    as HFirst.
	  specialize
	    (HFirst I (Step_MuApp_EvalFun heap env rho KDone ef ea) HSteps).
  destruct HFirst as (phi_after_fun & HAfterFun & HTraceStart).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho ef (KMuAppFun ea env rho KDone)
      phi_after_fun heap_final v_final HAfterFun)
    as (heap_fun & v_fun & phi_fun & phi_after_kfun &
        HFun & HAfterKFun & HTraceFun).
  destruct
    (StepsPhi_nonterminal_terminal_inv_step
      (StReturn heap_fun v_fun (KMuAppFun ea env rho KDone))
      phi_after_kfun heap_final v_final)
    as (label_arg & state_arg & phi_after_arg &
        HStepArg & HAfterArg & HTraceArgStep).
  - intros HTerminal. inversion HTerminal.
  - exact HAfterKFun.
  - inversion HStepArg; subst.
    destruct
      (StepsPhi_initial_with_kont_terminal_decompose
        heap_fun env rho ea (KMuAppArg env' rho' f x ec ee KDone)
        phi_after_arg heap_final v_final HAfterArg)
      as (heap_arg & v_arg & phi_arg & phi_after_karg &
          HArg & HAfterKArg & HTraceArg).
    destruct
      (StepsPhi_nonterminal_terminal_inv_step
        (StReturn heap_arg v_arg
          (KMuAppArg env' rho' f x ec ee KDone))
        phi_after_karg heap_final v_final)
      as (label_body & state_body & phi_body &
          HStepBody & HBody & HTraceBodyStep).
    + intros HTerminal. inversion HTerminal.
    + exact HAfterKArg.
    + inversion HStepBody; subst.
      exists phi_fun, phi_arg, phi_body,
        heap_fun, heap_arg, env', rho', f, x, ec, ee, v_arg.
      split; [exact HFun |].
      split; [exact HArg |].
      split; [exact HBody |].
      rewrite HTraceStart, HTraceFun, HTraceArgStep,
        HTraceArg, HTraceBodyStep.
      simpl.
      repeat rewrite app_nil_l.
      repeat rewrite app_nil_r.
      rewrite app_assoc.
      reflexivity.
Qed.

Theorem EffAppTerminalDecompose :
  forall heap env rho ef ea phi heap_final v_final,
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi
      (StDone heap_final v_final) ->
    exists phi_fun phi_arg phi_body
      heap_fun heap_arg env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun
        (StDone heap_fun
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap_fun env rho ea)
        phi_arg
        (StDone heap_arg v_arg) /\
      StepsPhi
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body
        (StDone heap_final v_final) /\
      phi_as_list phi =
        phi_as_list phi_fun ++
        phi_as_list phi_arg ++
        phi_as_list phi_body.
Proof.
  intros heap env rho ef ea phi heap_final v_final HSteps.
  pose proof
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Eff_App ef ea))
      Silent
      (StEval heap env rho ef (KEffAppFun ea env rho KDone))
      phi heap_final v_final)
    as HFirst.
	  specialize
	    (HFirst I (Step_EffApp_EvalFun heap env rho KDone ef ea) HSteps).
  destruct HFirst as (phi_after_fun & HAfterFun & HTraceStart).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho ef (KEffAppFun ea env rho KDone)
      phi_after_fun heap_final v_final HAfterFun)
    as (heap_fun & v_fun & phi_fun & phi_after_kfun &
        HFun & HAfterKFun & HTraceFun).
  destruct
    (StepsPhi_nonterminal_terminal_inv_step
      (StReturn heap_fun v_fun (KEffAppFun ea env rho KDone))
      phi_after_kfun heap_final v_final)
    as (label_arg & state_arg & phi_after_arg &
        HStepArg & HAfterArg & HTraceArgStep).
  - intros HTerminal. inversion HTerminal.
  - exact HAfterKFun.
  - inversion HStepArg; subst.
    destruct
      (StepsPhi_initial_with_kont_terminal_decompose
        heap_fun env rho ea (KEffAppArg env' rho' f x ec ee KDone)
        phi_after_arg heap_final v_final HAfterArg)
      as (heap_arg & v_arg & phi_arg & phi_after_karg &
          HArg & HAfterKArg & HTraceArg).
    destruct
      (StepsPhi_nonterminal_terminal_inv_step
        (StReturn heap_arg v_arg
          (KEffAppArg env' rho' f x ec ee KDone))
        phi_after_karg heap_final v_final)
      as (label_body & state_body & phi_body &
          HStepBody & HBody & HTraceBodyStep).
    + intros HTerminal. inversion HTerminal.
    + exact HAfterKArg.
    + inversion HStepBody; subst.
      exists phi_fun, phi_arg, phi_body,
        heap_fun, heap_arg, env', rho', f, x, ec, ee, v_arg.
      split; [exact HFun |].
      split; [exact HArg |].
      split; [exact HBody |].
      rewrite HTraceStart, HTraceFun, HTraceArgStep,
        HTraceArg, HTraceBodyStep.
      simpl.
      repeat rewrite app_nil_l.
      repeat rewrite app_nil_r.
      rewrite app_assoc.
      reflexivity.
Qed.

Theorem ScheduledCheckedMuAppTerminalDecompose :
  forall heap env rho ef ea phi heap_final v_final,
    ScheduledCheckedTerminal
      (initial_state heap env rho (Mu_App ef ea))
      phi heap_final v_final ->
    exists phi_fun phi_arg phi_body
      heap_fun heap_arg env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun
        (StDone heap_fun
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap_fun env rho ea)
        phi_arg
        (StDone heap_arg v_arg) /\
      StepsPhi
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body
        (StDone heap_final v_final) /\
      phi_as_list phi =
        phi_as_list phi_fun ++
        phi_as_list phi_arg ++
        phi_as_list phi_body.
Proof.
  intros heap env rho ef ea phi heap_final v_final HRun.
  destruct
    (ScheduledCheckedTerminal_as_stepsphi_exists
      (initial_state heap env rho (Mu_App ef ea))
      phi heap_final v_final HRun)
    as (phi_steps & HStepsPhi & HTrace).
  destruct
    (MuAppTerminalDecompose
      heap env rho ef ea phi_steps heap_final v_final HStepsPhi)
    as (phi_fun & phi_arg & phi_body &
        heap_fun & heap_arg & env_closure & rho_closure &
        f & x & ec & ee & v_arg &
        HFun & HArg & HBody & HTraceDecomp).
  exists phi_fun, phi_arg, phi_body.
  exists heap_fun, heap_arg, env_closure, rho_closure, f, x, ec, ee, v_arg.
  repeat split; try assumption.
  rewrite <- HTrace.
  exact HTraceDecomp.
Qed.

Theorem ScheduledCheckedEffAppTerminalDecompose :
  forall heap env rho ef ea phi heap_final v_final,
    ScheduledCheckedTerminal
      (initial_state heap env rho (Eff_App ef ea))
      phi heap_final v_final ->
    exists phi_fun phi_arg phi_body
      heap_fun heap_arg env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun
        (StDone heap_fun
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap_fun env rho ea)
        phi_arg
        (StDone heap_arg v_arg) /\
      StepsPhi
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body
        (StDone heap_final v_final) /\
      phi_as_list phi =
        phi_as_list phi_fun ++
        phi_as_list phi_arg ++
        phi_as_list phi_body.
Proof.
  intros heap env rho ef ea phi heap_final v_final HRun.
  destruct
    (ScheduledCheckedTerminal_as_stepsphi_exists
      (initial_state heap env rho (Eff_App ef ea))
      phi heap_final v_final HRun)
    as (phi_steps & HStepsPhi & HTrace).
  destruct
    (EffAppTerminalDecompose
      heap env rho ef ea phi_steps heap_final v_final HStepsPhi)
    as (phi_fun & phi_arg & phi_body &
        heap_fun & heap_arg & env_closure & rho_closure &
        f & x & ec & ee & v_arg &
        HFun & HArg & HBody & HTraceDecomp).
  exists phi_fun, phi_arg, phi_body.
  exists heap_fun, heap_arg, env_closure, rho_closure, f, x, ec, ee, v_arg.
  repeat split; try assumption.
	  rewrite <- HTrace.
	  exact HTraceDecomp.
Qed.

Theorem ScheduledCheckedMuAppTerminalDecompose_scheduled :
  forall heap env rho ef ea phi heap_final v_final,
    ScheduledCheckedTerminal
      (initial_state heap env rho (Mu_App ef ea))
      phi heap_final v_final ->
    exists phi_fun phi_arg phi_body
      heap_fun heap_arg env_closure rho_closure f x ec ee v_arg,
      ScheduledCheckedTerminal
        (initial_state heap env rho ef)
        phi_fun
        heap_fun
        (Cls (env_closure, rho_closure, Mu f x ec ee)) /\
      ScheduledCheckedTerminal
        (initial_state heap_fun env rho ea)
        phi_arg
        heap_arg
        v_arg /\
      ScheduledCheckedTerminal
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body
        heap_final
        v_final /\
      phi_as_list phi =
        phi_as_list phi_fun ++
        phi_as_list phi_arg ++
        phi_as_list phi_body.
Proof.
  intros heap env rho ef ea phi heap_final v_final HRun.
  destruct
    (ScheduledCheckedMuAppTerminalFirstStep
      heap env rho ef ea phi heap_final v_final HRun)
    as (phi_after_fun & HAfterFun & HTraceStart).
  destruct
    (ScheduledCheckedTerminal_initial_with_kont_terminal_decompose
      heap env rho ef (KMuAppFun ea env rho KDone)
      phi_after_fun heap_final v_final HAfterFun)
    as (heap_fun & v_fun & phi_fun & phi_after_kfun &
        HFun & HAfterKFun & HTraceFun).
  destruct
    (ScheduledCheckedTerminal_nonpair_terminal_inv_step
      (StReturn heap_fun v_fun (KMuAppFun ea env rho KDone))
      phi_after_kfun heap_final v_final)
    as (label_arg & state_arg & phi_after_arg &
        HStepArg & HAfterArg & HTraceArgStep).
  - simpl. exact I.
  - intros HTerminal. inversion HTerminal.
  - exact HAfterKFun.
  - inversion HStepArg; subst.
    destruct
      (ScheduledCheckedTerminal_initial_with_kont_terminal_decompose
        heap_fun env rho ea (KMuAppArg env' rho' f x ec ee KDone)
        phi_after_arg heap_final v_final HAfterArg)
      as (heap_arg & v_arg & phi_arg & phi_after_karg &
          HArg & HAfterKArg & HTraceArg).
    destruct
      (ScheduledCheckedTerminal_nonpair_terminal_inv_step
        (StReturn heap_arg v_arg
          (KMuAppArg env' rho' f x ec ee KDone))
        phi_after_karg heap_final v_final)
      as (label_body & state_body & phi_body &
          HStepBody & HBody & HTraceBodyStep).
    + simpl. exact I.
    + intros HTerminal. inversion HTerminal.
    + exact HAfterKArg.
    + inversion HStepBody; subst.
      exists phi_fun, phi_arg, phi_body,
        heap_fun, heap_arg, env', rho', f, x, ec, ee, v_arg.
      split; [exact HFun |].
      split; [exact HArg |].
      split; [exact HBody |].
      rewrite HTraceStart, HTraceFun, HTraceArgStep,
        HTraceArg, HTraceBodyStep.
      simpl.
      repeat rewrite app_nil_l.
      repeat rewrite app_nil_r.
      rewrite app_assoc.
      reflexivity.
Qed.

Theorem ScheduledCheckedEffAppTerminalDecompose_scheduled :
  forall heap env rho ef ea phi heap_final v_final,
    ScheduledCheckedTerminal
      (initial_state heap env rho (Eff_App ef ea))
      phi heap_final v_final ->
    exists phi_fun phi_arg phi_body
      heap_fun heap_arg env_closure rho_closure f x ec ee v_arg,
      ScheduledCheckedTerminal
        (initial_state heap env rho ef)
        phi_fun
        heap_fun
        (Cls (env_closure, rho_closure, Mu f x ec ee)) /\
      ScheduledCheckedTerminal
        (initial_state heap_fun env rho ea)
        phi_arg
        heap_arg
        v_arg /\
      ScheduledCheckedTerminal
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body
        heap_final
        v_final /\
      phi_as_list phi =
        phi_as_list phi_fun ++
        phi_as_list phi_arg ++
        phi_as_list phi_body.
Proof.
  intros heap env rho ef ea phi heap_final v_final HRun.
  destruct
    (ScheduledCheckedEffAppTerminalFirstStep
      heap env rho ef ea phi heap_final v_final HRun)
    as (phi_after_fun & HAfterFun & HTraceStart).
  destruct
    (ScheduledCheckedTerminal_initial_with_kont_terminal_decompose
      heap env rho ef (KEffAppFun ea env rho KDone)
      phi_after_fun heap_final v_final HAfterFun)
    as (heap_fun & v_fun & phi_fun & phi_after_kfun &
        HFun & HAfterKFun & HTraceFun).
  destruct
    (ScheduledCheckedTerminal_nonpair_terminal_inv_step
      (StReturn heap_fun v_fun (KEffAppFun ea env rho KDone))
      phi_after_kfun heap_final v_final)
    as (label_arg & state_arg & phi_after_arg &
        HStepArg & HAfterArg & HTraceArgStep).
  - simpl. exact I.
  - intros HTerminal. inversion HTerminal.
  - exact HAfterKFun.
  - inversion HStepArg; subst.
    destruct
      (ScheduledCheckedTerminal_initial_with_kont_terminal_decompose
        heap_fun env rho ea (KEffAppArg env' rho' f x ec ee KDone)
        phi_after_arg heap_final v_final HAfterArg)
      as (heap_arg & v_arg & phi_arg & phi_after_karg &
          HArg & HAfterKArg & HTraceArg).
    destruct
      (ScheduledCheckedTerminal_nonpair_terminal_inv_step
        (StReturn heap_arg v_arg
          (KEffAppArg env' rho' f x ec ee KDone))
        phi_after_karg heap_final v_final)
      as (label_body & state_body & phi_body &
          HStepBody & HBody & HTraceBodyStep).
    + simpl. exact I.
    + intros HTerminal. inversion HTerminal.
    + exact HAfterKArg.
    + inversion HStepBody; subst.
      exists phi_fun, phi_arg, phi_body,
        heap_fun, heap_arg, env', rho', f, x, ec, ee, v_arg.
      split; [exact HFun |].
      split; [exact HArg |].
      split; [exact HBody |].
      rewrite HTraceStart, HTraceFun, HTraceArgStep,
        HTraceArg, HTraceBodyStep.
      simpl.
      repeat rewrite app_nil_l.
      repeat rewrite app_nil_r.
      rewrite app_assoc.
      reflexivity.
Qed.

Theorem ScheduledCheckedConcatTerminalDecompose :
  forall heap env rho e1 e2 phi heap_final theta,
    ScheduledCheckedTerminal
      (initial_state heap env rho (Concat e1 e2))
      phi
      heap_final
      (Eff theta) ->
    exists phi1 phi2 heap1 theta1 heap2 theta2,
      ScheduledCheckedTerminal
        (initial_state heap env rho e1)
        phi1
        heap1
        (Eff theta1) /\
      ScheduledCheckedTerminal
        (initial_state heap1 env rho e2)
        phi2
        heap2
        (Eff theta2) /\
      heap_final = heap2 /\
      theta = Union_Theta theta1 theta2 /\
      phi_as_list phi =
        phi_as_list phi1 ++ phi_as_list phi2.
Proof.
  intros heap env rho e1 e2 phi heap_final theta HRun.
  destruct
    (ScheduledCheckedTerminal_known_step_inv
      (initial_state heap env rho (Concat e1 e2))
      Silent
      (StEval heap env rho e1 (KConcatL e2 env rho KDone))
      phi heap_final (Eff theta))
    as (phi_after_e1 & HAfterE1 & HTraceStart).
  - simpl. exact I.
  - constructor.
  - exact HRun.
  - destruct
      (ScheduledCheckedTerminal_initial_with_kont_terminal_decompose
        heap env rho e1 (KConcatL e2 env rho KDone)
        phi_after_e1 heap_final (Eff theta) HAfterE1)
      as (heap1 & v1 & phi1 & phi_after_k1 &
          HE1 & HAfterK1 & HTraceE1).
    destruct
      (ScheduledCheckedTerminal_nonpair_terminal_inv_step
        (StReturn heap1 v1 (KConcatL e2 env rho KDone))
        phi_after_k1 heap_final (Eff theta))
      as (label_k1 & state_k1 & phi_after_e2 &
          HStepK1 & HAfterE2 & HTraceK1).
    + simpl. exact I.
    + intros HTerminal. inversion HTerminal.
    + exact HAfterK1.
    + inversion HStepK1; subst.
      destruct
        (ScheduledCheckedTerminal_initial_with_kont_terminal_decompose
          heap1 env rho e2 (KConcatR theta0 KDone)
          phi_after_e2 heap_final (Eff theta) HAfterE2)
        as (heap2 & v2 & phi2 & phi_after_k2 &
            HE2 & HAfterK2 & HTraceE2).
      destruct
        (ScheduledCheckedTerminal_nonpair_terminal_inv_step
          (StReturn heap2 v2 (KConcatR theta0 KDone))
          phi_after_k2 heap_final (Eff theta))
        as (label_k2 & state_k2 & phi_after_done &
            HStepK2 & HAfterDone & HTraceK2).
      * simpl. exact I.
      * intros HTerminal. inversion HTerminal.
      * exact HAfterK2.
      * inversion HStepK2; subst.
        pose proof
          (ScheduledCheckedTerminal_deterministic
            (StReturn heap2 (Eff (Union_Theta theta0 theta2)) KDone)
            (Phi_Seq (label_phi Silent) Phi_Nil)
            heap2 (Eff (Union_Theta theta0 theta2))
            phi_after_done heap_final (Eff theta)
            (ScheduledCheckedTerminal_return_kdone
              heap2 (Eff (Union_Theta theta0 theta2)))
            HAfterDone)
          as (HHeapFinal & HValFinal).
        inversion HValFinal; subst theta.
        pose proof
          (ScheduledCheckedTerminal_return_kdone_trace_nil
            heap2 (Eff (Union_Theta theta0 theta2))
            phi_after_done heap_final
            (Eff (Union_Theta theta0 theta2))
            HAfterDone)
          as HTraceDone.
        exists phi1, phi2, heap1, theta0, heap2, theta2.
        split; [exact HE1 |].
        split; [exact HE2 |].
        split; [symmetry; exact HHeapFinal |].
        split; [reflexivity |].
        rewrite HTraceStart, HTraceE1, HTraceK1, HTraceE2,
          HTraceK2.
        simpl.
        rewrite HTraceDone.
        repeat rewrite app_nil_l.
        repeat rewrite app_nil_r.
        repeat rewrite app_assoc.
        reflexivity.
Qed.

Lemma StepsPhiN_mu_app_terminal_decompose_counts :
  forall n heap env rho ef ea phi heap_final v_final,
    StepsPhiN n (initial_state heap env rho (Mu_App ef ea)) phi
      (StDone heap_final v_final) ->
    exists env_fun rho_fun f x ec ee
      n_fun phi_fun heap_fun
      n_arg phi_arg heap_arg v_arg
      n_body phi_body,
      n_fun < n /\
      n_arg < n /\
      n_body < n /\
      StepsPhiN n_fun (initial_state heap env rho ef) phi_fun
        (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) /\
      StepsPhiN n_arg (initial_state heap_fun env rho ea) phi_arg
        (StDone heap_arg v_arg) /\
      StepsPhiN n_body
        (initial_state heap_arg
          (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
            (x, v_arg) env_fun)
          rho_fun ec) phi_body
        (StDone heap_final v_final) /\
      phi_as_list phi =
        phi_as_list phi_fun ++ phi_as_list phi_arg ++ phi_as_list phi_body.
Proof.
  intros n heap env rho ef ea phi heap_final v_final HApp.
  assert
    (HFirst :
      Step (initial_state heap env rho (Mu_App ef ea)) Silent
        (StEval heap env rho ef (KMuAppFun ea env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhiN_terminal_inv_step
      n
	      (initial_state heap env rho (Mu_App ef ea))
	      Silent
	      (StEval heap env rho ef (KMuAppFun ea env rho KDone))
	      phi heap_final v_final I HFirst HApp)
    as (n_after_fun & phi_after_fun & HNAfterFun &
        HAfterFun & HTraceStart).
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_fun heap env rho ef (KMuAppFun ea env rho KDone)
      phi_after_fun heap_final v_final HAfterFun)
    as (n_fun & n_after_arg & heap_fun & v_fun &
        phi_fun & phi_after_arg &
        HLeFun & HLeAfterArg & HFun & HAfterArg & HTraceFun).
  inversion HAfterArg as
    [| n_after_arg_tail state_arg label_arg state_after_arg
       phi_after_arg_tail final_arg HStepArg HAfterArgTail];
    subst; try discriminate.
  inversion HStepArg; subst.
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_arg_tail heap_fun env rho ea
      (KMuAppArg env' rho' f x ec ee KDone)
      phi_after_arg_tail heap_final v_final HAfterArgTail)
    as (n_arg & n_after_body & heap_arg & v_arg &
        phi_arg & phi_after_body &
        HLeArg & HLeAfterBody & HArg & HAfterBody & HTraceArg).
  inversion HAfterBody as
    [| n_body state_body label_body state_after_body
       phi_body final_body HStepBody HBody];
    subst; try discriminate.
  inversion HStepBody; subst.
  exists env', rho', f, x, ec, ee,
    n_fun, phi_fun, heap_fun,
    n_arg, phi_arg, heap_arg, v_arg,
    n_body, phi_body.
  repeat split; try lia; try assumption.
  rewrite HTraceStart.
  simpl.
  rewrite HTraceFun.
  simpl.
  rewrite HTraceArg.
  simpl.
  repeat rewrite app_assoc.
  reflexivity.
Qed.

Lemma StepsPhiN_eff_app_terminal_decompose_counts :
  forall n heap env rho ef ea phi heap_final v_final,
    StepsPhiN n (initial_state heap env rho (Eff_App ef ea)) phi
      (StDone heap_final v_final) ->
    exists env_fun rho_fun f x ec ee
      n_fun phi_fun heap_fun
      n_arg phi_arg heap_arg v_arg
      n_body phi_body,
      n_fun < n /\
      n_arg < n /\
      n_body < n /\
      StepsPhiN n_fun (initial_state heap env rho ef) phi_fun
        (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) /\
      StepsPhiN n_arg (initial_state heap_fun env rho ea) phi_arg
        (StDone heap_arg v_arg) /\
      StepsPhiN n_body
        (initial_state heap_arg
          (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
            (x, v_arg) env_fun)
          rho_fun ee) phi_body
        (StDone heap_final v_final) /\
      phi_as_list phi =
        phi_as_list phi_fun ++ phi_as_list phi_arg ++ phi_as_list phi_body.
Proof.
  intros n heap env rho ef ea phi heap_final v_final HApp.
  assert
    (HFirst :
      Step (initial_state heap env rho (Eff_App ef ea)) Silent
        (StEval heap env rho ef (KEffAppFun ea env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhiN_terminal_inv_step
      n
	      (initial_state heap env rho (Eff_App ef ea))
	      Silent
	      (StEval heap env rho ef (KEffAppFun ea env rho KDone))
	      phi heap_final v_final I HFirst HApp)
    as (n_after_fun & phi_after_fun & HNAfterFun &
        HAfterFun & HTraceStart).
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_fun heap env rho ef (KEffAppFun ea env rho KDone)
      phi_after_fun heap_final v_final HAfterFun)
    as (n_fun & n_after_arg & heap_fun & v_fun &
        phi_fun & phi_after_arg &
        HLeFun & HLeAfterArg & HFun & HAfterArg & HTraceFun).
  inversion HAfterArg as
    [| n_after_arg_tail state_arg label_arg state_after_arg
       phi_after_arg_tail final_arg HStepArg HAfterArgTail];
    subst; try discriminate.
  inversion HStepArg; subst.
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_arg_tail heap_fun env rho ea
      (KEffAppArg env' rho' f x ec ee KDone)
      phi_after_arg_tail heap_final v_final HAfterArgTail)
    as (n_arg & n_after_body & heap_arg & v_arg &
        phi_arg & phi_after_body &
        HLeArg & HLeAfterBody & HArg & HAfterBody & HTraceArg).
  inversion HAfterBody as
    [| n_body state_body label_body state_after_body
       phi_body final_body HStepBody HBody];
    subst; try discriminate.
  inversion HStepBody; subst.
  exists env', rho', f, x, ec, ee,
    n_fun, phi_fun, heap_fun,
    n_arg, phi_arg, heap_arg, v_arg,
    n_body, phi_body.
  repeat split; try lia; try assumption.
  rewrite HTraceStart.
  simpl.
  rewrite HTraceFun.
  simpl.
  rewrite HTraceArg.
  simpl.
  repeat rewrite app_assoc.
  reflexivity.
Qed.

Definition SmallStepCorrectnessBelow (n : nat) : Prop :=
  forall n_child heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static,
    n_child < n ->
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhiN n_child (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    phi ⋞ theta_summary.

Theorem MuEffAppTerminalAlignedBodyDecompose :
  forall heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta,
    StepsPhi
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      (StDone heap_mu v_mu) ->
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      (StDone heap_eff (Eff theta)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea)) ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      heap_fun heap_arg env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_mu
        (StDone heap_fun
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_eff
        (StDone heap_fun
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap_fun env rho ea)
        phi_arg_mu
        (StDone heap_arg v_arg) /\
      StepsPhi
        (initial_state heap_fun env rho ea)
        phi_arg_eff
        (StDone heap_arg v_arg) /\
      StepsPhi
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu v_mu) /\
      StepsPhi
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff (Eff theta)) /\
      phi_as_list phi_mu =
        phi_as_list phi_fun_mu ++
        phi_as_list phi_arg_mu ++
        phi_as_list phi_body_mu /\
      phi_as_list phi_eff =
        phi_as_list phi_fun_eff ++
        phi_as_list phi_arg_eff ++
        phi_as_list phi_body_eff /\
      phi_as_list phi_fun_mu = phi_as_list phi_fun_eff /\
      phi_as_list phi_arg_mu = phi_as_list phi_arg_eff.
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    HMu HEff HStayFun HStayArg.
  destruct
    (MuAppTerminalDecompose
      heap env rho ef ea phi_mu heap_mu v_mu HMu)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        heap_fun_mu & heap_arg_mu & env_mu & rho_mu &
        f_mu & x_mu & ec_mu & ee_mu & v_arg_mu &
        HFunMu & HArgMu & HBodyMu & HTraceMu).
  destruct
    (EffAppTerminalDecompose
      heap env rho ef ea phi_eff heap_eff (Eff theta) HEff)
    as (phi_fun_eff & phi_arg_eff & phi_body_eff &
        heap_fun_eff & heap_arg_eff & env_eff & rho_eff &
        f_eff & x_eff & ec_eff & ee_eff & v_arg_eff &
        HFunEff & HArgEff & HBodyEff & HTraceEff).
  destruct
    (StepsPhi_terminal_deterministic
      (initial_state heap env rho ef)
      phi_fun_mu heap_fun_mu
      (Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu))
		      phi_fun_eff heap_fun_eff
		      (Cls (env_eff, rho_eff, Mu f_eff x_eff ec_eff ee_eff))
		      HStayFun
		      HFunMu HFunEff)
    as (HFunTrace & HHeapFun & HClosureEq).
  subst heap_fun_eff.
  symmetry in HClosureEq.
  inversion HClosureEq; subst.
  destruct
    (StepsPhi_terminal_deterministic
		      (initial_state heap_fun_mu env rho ea)
		      phi_arg_mu heap_arg_mu v_arg_mu
		      phi_arg_eff heap_arg_eff v_arg_eff
		      (HStayArg heap_fun_mu)
		      HArgMu HArgEff)
    as (HArgTrace & HHeapArg & HArgVal).
  subst heap_arg_eff.
  subst v_arg_eff.
  exists phi_fun_mu, phi_arg_mu, phi_body_mu,
    phi_fun_eff, phi_arg_eff, phi_body_eff,
    heap_fun_mu, heap_arg_mu, env_mu, rho_mu,
    f_mu, x_mu, ec_mu, ee_mu, v_arg_mu.
	  repeat split; try assumption.
Qed.

Theorem MuEffAppTerminalScheduledAlignedBodyDecompose :
  forall heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta,
    ScheduledCheckedTerminal
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      heap_mu
      v_mu ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      heap_eff
      (Eff theta) ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      heap_fun heap_arg env_closure rho_closure f x ec ee v_arg,
      ScheduledCheckedTerminal
        (initial_state heap env rho ef)
        phi_fun_mu
        heap_fun
        (Cls (env_closure, rho_closure, Mu f x ec ee)) /\
      ScheduledCheckedTerminal
        (initial_state heap env rho ef)
        phi_fun_eff
        heap_fun
        (Cls (env_closure, rho_closure, Mu f x ec ee)) /\
      ScheduledCheckedTerminal
        (initial_state heap_fun env rho ea)
        phi_arg_mu
        heap_arg
        v_arg /\
      ScheduledCheckedTerminal
        (initial_state heap_fun env rho ea)
        phi_arg_eff
        heap_arg
        v_arg /\
      ScheduledCheckedTerminal
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        heap_mu
        v_mu /\
      ScheduledCheckedTerminal
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        heap_eff
        (Eff theta) /\
      phi_as_list phi_mu =
        phi_as_list phi_fun_mu ++
        phi_as_list phi_arg_mu ++
        phi_as_list phi_body_mu /\
      phi_as_list phi_eff =
        phi_as_list phi_fun_eff ++
        phi_as_list phi_arg_eff ++
        phi_as_list phi_body_eff.
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    HMu HEff.
  destruct
    (ScheduledCheckedMuAppTerminalDecompose_scheduled
      heap env rho ef ea phi_mu heap_mu v_mu HMu)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        heap_fun_mu & heap_arg_mu & env_mu & rho_mu &
        f_mu & x_mu & ec_mu & ee_mu & v_arg_mu &
        HFunMu & HArgMu & HBodyMu & HTraceMu).
  destruct
    (ScheduledCheckedEffAppTerminalDecompose_scheduled
      heap env rho ef ea phi_eff heap_eff (Eff theta) HEff)
    as (phi_fun_eff & phi_arg_eff & phi_body_eff &
        heap_fun_eff & heap_arg_eff & env_eff & rho_eff &
        f_eff & x_eff & ec_eff & ee_eff & v_arg_eff &
        HFunEff & HArgEff & HBodyEff & HTraceEff).
  destruct
    (ScheduledCheckedTerminal_deterministic
      (initial_state heap env rho ef)
      phi_fun_mu heap_fun_mu
      (Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu))
      phi_fun_eff heap_fun_eff
      (Cls (env_eff, rho_eff, Mu f_eff x_eff ec_eff ee_eff))
      HFunMu HFunEff)
    as (HHeapFun & HClosureEq).
  subst heap_fun_eff.
  symmetry in HClosureEq.
  inversion HClosureEq; subst.
  destruct
    (ScheduledCheckedTerminal_deterministic
      (initial_state heap_fun_mu env rho ea)
      phi_arg_mu heap_arg_mu v_arg_mu
      phi_arg_eff heap_arg_eff v_arg_eff
      HArgMu HArgEff)
    as (HHeapArg & HArgVal).
  subst heap_arg_eff.
  subst v_arg_eff.
  exists phi_fun_mu, phi_arg_mu, phi_body_mu.
  exists phi_fun_eff, phi_arg_eff, phi_body_eff.
  exists heap_fun_mu, heap_arg_mu.
  exists env_mu, rho_mu, f_mu, x_mu, ec_mu, ee_mu, v_arg_mu.
  repeat split; try assumption.
Qed.

Lemma BackTriangle_mu_app_eff_app_inv :
  forall ctxt rgns rho ef ea,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    exists ty_mu ty_eff ty_ef ty_ea
      static_ef static_ea static_mu static_ee,
      TcExp (ctxt, rgns, Mu_App ef ea, ty_mu, static_mu) /\
      TcExp (ctxt, rgns, Eff_App ef ea, ty_eff, static_ee) /\
      ReadOnlyStatic (fold_subst_eps rho static_ee) /\
      TcExp (ctxt, rgns, ef, ty_ef, static_ef) /\
      TcExp (ctxt, rgns, ea, ty_ea, static_ea) /\
      BackTriangle (ctxt, rgns, rho, ef, Eff_App ef ea) /\
      BackTriangle (ctxt, rgns, rho, ea, Eff_App ef ea) /\
      ReadOnlyStatic (fold_subst_eps rho static_ef) /\
      ReadOnlyStatic (fold_subst_eps rho static_ea).
Proof.
  intros ctxt rgns rho ef ea HBack.
  inversion HBack; subst; try discriminate.
	  repeat eexists; eauto.
Qed.

Theorem MuEffAppScheduledAlignedPrefixes_readonly_heap_neutral :
  forall heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      heap_mu
      v_mu ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      heap_eff
      (Eff theta) ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      env_closure rho_closure f x ec ee v_arg,
      ScheduledCheckedTerminal
        (initial_state heap env rho ef)
        phi_fun_mu
        heap
        (Cls (env_closure, rho_closure, Mu f x ec ee)) /\
      ScheduledCheckedTerminal
        (initial_state heap env rho ef)
        phi_fun_eff
        heap
        (Cls (env_closure, rho_closure, Mu f x ec ee)) /\
      ScheduledCheckedTerminal
        (initial_state heap env rho ea)
        phi_arg_mu
        heap
        v_arg /\
      ScheduledCheckedTerminal
        (initial_state heap env rho ea)
        phi_arg_eff
        heap
        v_arg /\
      ScheduledCheckedTerminal
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        heap_mu
        v_mu /\
      ScheduledCheckedTerminal
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        heap_eff
        (Eff theta) /\
      phi_as_list phi_mu =
        phi_as_list phi_fun_mu ++
        phi_as_list phi_arg_mu ++
        phi_as_list phi_body_mu /\
      phi_as_list phi_eff =
        phi_as_list phi_fun_eff ++
        phi_as_list phi_arg_eff ++
        phi_as_list phi_body_eff /\
      ReadOnlyPhi phi_fun_mu /\
      ReadOnlyPhi phi_arg_mu.
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff.
  destruct
    (BackTriangle_mu_app_eff_app_inv ctxt rgns rho ef ea HBack)
    as (_ty_mu & _ty_eff & ty_ef & ty_ea &
        static_ef & static_ea & _static_mu & _static_ee &
        _HTcMu & _HTcEff & _HReadOnlyEff &
        HTcEf & HTcEa & _HBackEf & _HBackEa &
        HReadOnlyEf & HReadOnlyEa).
  destruct
    (MuEffAppTerminalScheduledAlignedBodyDecompose
      heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      HMu HEff)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        phi_fun_eff & phi_arg_eff & phi_body_eff &
        heap_fun & heap_arg & env_closure & rho_closure &
        f & x & ec & ee & v_arg &
        HFunMu & HFunEff & HArgMu & HArgEff & HBodyMu & HBodyEff &
        HTraceMu & HTraceEff).
  assert (HFunStaticSound :
    Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, phi_fun_mu)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_eff_sound with
      (t := ty_ef) (eff := static_ef)
      (heap' := heap_fun)
      (v := Cls (env_closure, rho_closure, Mu f x ec ee));
      eauto.
    eapply ScheduledCheckedTerminal_as_steps; eauto.
  }
  assert (HFunRO : ReadOnlyPhi phi_fun_mu).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ef)
        phi_fun_mu
        HReadOnlyEf
        HFunStaticSound).
  }
  destruct
    (ScheduledCheckedTerminal_as_stepsphi_exists
      (initial_state heap env rho ef)
      phi_fun_mu heap_fun
      (Cls (env_closure, rho_closure, Mu f x ec ee))
      HFunMu)
    as (phi_fun_mu_steps & HFunMuSteps & HFunMuTrace).
  assert (HFunStepsStaticSound :
    Epsilon_Phi_Soundness
      (fold_subst_eps rho static_ef, phi_fun_mu_steps)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    rewrite HFunMuTrace.
    eapply small_step_eff_sound with
      (t := ty_ef) (eff := static_ef)
      (heap' := heap_fun)
      (v := Cls (env_closure, rho_closure, Mu f x ec ee));
      eauto.
    eapply ScheduledCheckedTerminal_as_steps; eauto.
  }
  assert (HFunStepsRO : ReadOnlyPhi phi_fun_mu_steps).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ef)
        phi_fun_mu_steps
        HReadOnlyEf
        HFunStepsStaticSound).
  }
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho ef)
      phi_fun_mu_steps
      (StDone heap_fun
        (Cls (env_closure, rho_closure, Mu f x ec ee)))
      HFunMuSteps HFunStepsRO)
    as HHeapFun.
  simpl in HHeapFun.
  symmetry in HHeapFun.
  subst heap_fun.
  assert (HArgStaticSound :
    Epsilon_Phi_Soundness (fold_subst_eps rho static_ea, phi_arg_mu)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_eff_sound with
      (t := ty_ea) (eff := static_ea)
      (heap' := heap_arg) (v := v_arg);
      eauto.
    eapply ScheduledCheckedTerminal_as_steps; eauto.
  }
  assert (HArgRO : ReadOnlyPhi phi_arg_mu).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ea)
        phi_arg_mu
        HReadOnlyEa
        HArgStaticSound).
  }
  destruct
    (ScheduledCheckedTerminal_as_stepsphi_exists
      (initial_state heap env rho ea)
      phi_arg_mu heap_arg v_arg HArgMu)
    as (phi_arg_mu_steps & HArgMuSteps & HArgMuTrace).
  assert (HArgStepsStaticSound :
    Epsilon_Phi_Soundness
      (fold_subst_eps rho static_ea, phi_arg_mu_steps)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    rewrite HArgMuTrace.
    eapply small_step_eff_sound with
      (t := ty_ea) (eff := static_ea)
      (heap' := heap_arg) (v := v_arg);
      eauto.
    eapply ScheduledCheckedTerminal_as_steps; eauto.
  }
  assert (HArgStepsRO : ReadOnlyPhi phi_arg_mu_steps).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ea)
        phi_arg_mu_steps
        HReadOnlyEa
        HArgStepsStaticSound).
  }
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho ea)
      phi_arg_mu_steps
      (StDone heap_arg v_arg)
      HArgMuSteps HArgStepsRO)
    as HHeapArg.
  simpl in HHeapArg.
  symmetry in HHeapArg.
  subst heap_arg.
  exists phi_fun_mu, phi_arg_mu, phi_body_mu.
  exists phi_fun_eff, phi_arg_eff, phi_body_eff.
  exists env_closure, rho_closure, f, x, ec, ee, v_arg.
	  repeat split; try assumption.
Qed.

Theorem MuEffAppScheduledAlignedPrefixes_readonly_heap_neutral_N :
  forall n heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    ScheduledCheckedTerminalN n
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      heap_mu
      v_mu ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      heap_eff
      (Eff theta) ->
    exists n_fun n_arg n_body
      phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      env_closure rho_closure f x ec ee v_arg,
      n_fun < n /\
      n_arg < n /\
      n_body < n /\
      ScheduledCheckedTerminalN n_fun
        (initial_state heap env rho ef)
        phi_fun_mu
        heap
        (Cls (env_closure, rho_closure, Mu f x ec ee)) /\
      ScheduledCheckedTerminal
        (initial_state heap env rho ef)
        phi_fun_eff
        heap
        (Cls (env_closure, rho_closure, Mu f x ec ee)) /\
      ScheduledCheckedTerminalN n_arg
        (initial_state heap env rho ea)
        phi_arg_mu
        heap
        v_arg /\
      ScheduledCheckedTerminal
        (initial_state heap env rho ea)
        phi_arg_eff
        heap
        v_arg /\
      ScheduledCheckedTerminalN n_body
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        heap_mu
        v_mu /\
      ScheduledCheckedTerminal
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        heap_eff
        (Eff theta) /\
      phi_as_list phi_mu =
        phi_as_list phi_fun_mu ++
        phi_as_list phi_arg_mu ++
        phi_as_list phi_body_mu /\
      phi_as_list phi_eff =
        phi_as_list phi_fun_eff ++
        phi_as_list phi_arg_eff ++
        phi_as_list phi_body_eff /\
      ReadOnlyPhi phi_fun_mu /\
      ReadOnlyPhi phi_arg_mu.
Proof.
  intros n heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff.
  destruct
    (BackTriangle_mu_app_eff_app_inv ctxt rgns rho ef ea HBack)
    as (_ty_mu & _ty_eff & ty_ef & ty_ea &
        static_ef & static_ea & _static_mu & _static_ee &
        _HTcMu & _HTcEff & _HReadOnlyEff &
        HTcEf & HTcEa & _HBackEf & _HBackEa &
        HReadOnlyEf & HReadOnlyEa).
  destruct
    (ScheduledCheckedMuAppTerminalDecomposeN
      n heap env rho ef ea phi_mu heap_mu v_mu HMu)
    as (n_fun & n_arg & n_body &
        phi_fun_mu & phi_arg_mu & phi_body_mu &
        heap_fun_mu & heap_arg_mu & env_mu & rho_mu &
        f_mu & x_mu & ec_mu & ee_mu & v_arg_mu &
        HNFun & HNArg & HNBody &
        HFunMuN & HArgMuN & HBodyMuN & HTraceMu).
  destruct
    (ScheduledCheckedEffAppTerminalDecompose_scheduled
      heap env rho ef ea phi_eff heap_eff (Eff theta) HEff)
    as (phi_fun_eff & phi_arg_eff & phi_body_eff &
        heap_fun_eff & heap_arg_eff & env_eff & rho_eff &
        f_eff & x_eff & ec_eff & ee_eff & v_arg_eff &
        HFunEff & HArgEff & HBodyEff & HTraceEff).
  pose proof
    (ScheduledCheckedTerminalN_to_terminal
      n_fun
      (initial_state heap env rho ef)
      phi_fun_mu heap_fun_mu
      (Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu))
      HFunMuN)
    as HFunMu.
  destruct
    (ScheduledCheckedTerminal_deterministic
      (initial_state heap env rho ef)
      phi_fun_mu heap_fun_mu
      (Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu))
      phi_fun_eff heap_fun_eff
      (Cls (env_eff, rho_eff, Mu f_eff x_eff ec_eff ee_eff))
      HFunMu HFunEff)
    as (HHeapFun & HClosureEq).
  subst heap_fun_eff.
  symmetry in HClosureEq.
  inversion HClosureEq; subst.
  pose proof
    (ScheduledCheckedTerminalN_to_terminal
      n_arg
      (initial_state heap_fun_mu env rho ea)
      phi_arg_mu heap_arg_mu v_arg_mu
      HArgMuN)
    as HArgMu.
  destruct
    (ScheduledCheckedTerminal_deterministic
      (initial_state heap_fun_mu env rho ea)
      phi_arg_mu heap_arg_mu v_arg_mu
      phi_arg_eff heap_arg_eff v_arg_eff
      HArgMu HArgEff)
    as (HHeapArg & HArgVal).
  subst heap_arg_eff.
  subst v_arg_eff.
  assert (HFunStaticSound :
    Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, phi_fun_mu)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_eff_sound with
      (t := ty_ef) (eff := static_ef)
      (heap' := heap_fun_mu)
      (v := Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu));
      eauto.
    eapply ScheduledCheckedTerminal_as_steps; eauto.
  }
  assert (HFunRO : ReadOnlyPhi phi_fun_mu).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ef)
        phi_fun_mu
        HReadOnlyEf
        HFunStaticSound).
  }
  destruct
    (ScheduledCheckedTerminal_as_stepsphi_exists
      (initial_state heap env rho ef)
      phi_fun_mu heap_fun_mu
      (Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu))
      HFunMu)
    as (phi_fun_mu_steps & HFunMuSteps & HFunMuTrace).
  assert (HFunStepsStaticSound :
    Epsilon_Phi_Soundness
      (fold_subst_eps rho static_ef, phi_fun_mu_steps)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    rewrite HFunMuTrace.
    eapply small_step_eff_sound with
      (t := ty_ef) (eff := static_ef)
      (heap' := heap_fun_mu)
      (v := Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu));
      eauto.
    eapply ScheduledCheckedTerminal_as_steps; eauto.
  }
  assert (HFunStepsRO : ReadOnlyPhi phi_fun_mu_steps).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ef)
        phi_fun_mu_steps
        HReadOnlyEf
        HFunStepsStaticSound).
  }
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho ef)
      phi_fun_mu_steps
      (StDone heap_fun_mu
        (Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu)))
      HFunMuSteps HFunStepsRO)
    as HHeapFunRO.
  simpl in HHeapFunRO.
  symmetry in HHeapFunRO.
  subst heap_fun_mu.
  assert (HArgStaticSound :
    Epsilon_Phi_Soundness (fold_subst_eps rho static_ea, phi_arg_mu)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_eff_sound with
      (t := ty_ea) (eff := static_ea)
      (heap' := heap_arg_mu) (v := v_arg_mu);
      eauto.
    eapply ScheduledCheckedTerminal_as_steps; eauto.
  }
  assert (HArgRO : ReadOnlyPhi phi_arg_mu).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ea)
        phi_arg_mu
        HReadOnlyEa
        HArgStaticSound).
  }
  destruct
    (ScheduledCheckedTerminal_as_stepsphi_exists
      (initial_state heap env rho ea)
      phi_arg_mu heap_arg_mu v_arg_mu HArgMu)
    as (phi_arg_mu_steps & HArgMuSteps & HArgMuTrace).
  assert (HArgStepsStaticSound :
    Epsilon_Phi_Soundness
      (fold_subst_eps rho static_ea, phi_arg_mu_steps)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    rewrite HArgMuTrace.
    eapply small_step_eff_sound with
      (t := ty_ea) (eff := static_ea)
      (heap' := heap_arg_mu) (v := v_arg_mu);
      eauto.
    eapply ScheduledCheckedTerminal_as_steps; eauto.
  }
  assert (HArgStepsRO : ReadOnlyPhi phi_arg_mu_steps).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ea)
        phi_arg_mu_steps
        HReadOnlyEa
        HArgStepsStaticSound).
  }
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho ea)
      phi_arg_mu_steps
      (StDone heap_arg_mu v_arg_mu)
      HArgMuSteps HArgStepsRO)
    as HHeapArgRO.
  simpl in HHeapArgRO.
  symmetry in HHeapArgRO.
  subst heap_arg_mu.
  exists n_fun, n_arg, n_body.
  exists phi_fun_mu, phi_arg_mu, phi_body_mu.
  exists phi_fun_eff, phi_arg_eff, phi_body_eff.
  exists env_mu, rho_mu, f_mu, x_mu, ec_mu, ee_mu, v_arg_mu.
  repeat split; try assumption.
Qed.

Lemma TcExp_mu_app_inv :
  forall ctxt rgns ef ea ty static,
    TcExp (ctxt, rgns, Mu_App ef ea, ty, static) ->
    exists tya effc tyc effe efff effa,
      TcExp (ctxt, rgns, ef,
        Ty_Arrow tya effc tyc effe Ty_Effect, efff) /\
      TcExp (ctxt, rgns, ea, tya, effa).
Proof.
  intros ctxt rgns ef ea ty static HTc.
  inversion HTc; subst; repeat eexists; eauto.
Qed.

Lemma MuAppBodyRuntimeTyping_from_prefixes :
  forall heap env rho ef ea
    phi_fun phi_arg env_closure rho_closure f x ec ee v_arg
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    StepsPhi
      (initial_state heap env rho ef)
      phi_fun
      (StDone heap
        (Cls (env_closure, rho_closure, Mu f x ec ee))) ->
    StepsPhi
      (initial_state heap env rho ea)
      phi_arg
      (StDone heap v_arg) ->
    exists stty_body ctxt_body rgns_body tyx effc tyc effe,
      TcHeap (heap, stty_body) /\
      RuntimeHeapShape heap stty_body /\
      TcRho (rho_closure, rgns_body) /\
      TcInc
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body) /\
      TcEnv
        (stty_body, rho_closure,
         update_rec_E
           (f, Cls (env_closure, rho_closure, Mu f x ec ee))
           (x, v_arg) env_closure,
         update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
           (x, tyx) ctxt_body) /\
      RuntimeEnvShape stty_body rho_closure
        (update_rec_E
          (f, Cls (env_closure, rho_closure, Mu f x ec ee))
          (x, v_arg) env_closure)
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body) /\
      BackTriangle
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, rho_closure, ec, ee) /\
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, ec, tyc, effc) /\
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, ee, Ty_Effect, effe).
Proof.
  intros heap env rho ef ea
    phi_fun phi_arg env_closure rho_closure f x ec ee v_arg
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HFun HArg.
  destruct
    (BackTriangle_mu_app_eff_app_inv ctxt rgns rho ef ea HBack)
    as (_ty_mu & _ty_eff & _ty_ef & _ty_ea &
        _static_ef & _static_ea & _static_mu & _static_ee &
        HTcMu & _HTcEff & _HReadOnlyEff &
        _HTcEf & _HTcEa & _HBackEf & _HBackEa &
        _HReadOnlyEf & _HReadOnlyEa).
  destruct (TcExp_mu_app_inv ctxt rgns ef ea _ _ HTcMu)
    as (tya & effc_top & tyc_top & effe_top & efff & effa &
        HTcFun & HTcArg).
  destruct
    (initial_state_terminal_value_with_trace
      heap env rho ef stty ctxt rgns
      (Ty_Arrow tya effc_top tyc_top effe_top Ty_Effect)
      efff
      (phi_as_list phi_fun) heap
      (Cls (env_closure, rho_closure, Mu f x ec ee))
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcFun)
    as (stty_fun & HExtFun & HTcHeapFun & HHeapShapeFun &
        _HTcFunVal & HFunShape & _HTcPhiFun).
  {
    eapply StepsPhi_as_steps; eauto.
  }
  destruct
    (RuntimeValShape_mu_closure_inv
      stty_fun
      (subst_rho rho
        (Ty_Arrow tya effc_top tyc_top effe_top Ty_Effect))
      env_closure rho_closure f x ec ee HFunShape)
    as (rgns_body & ctxt_body & tyx & effc & tyc & effe &
        HClosureTy & HTcRhoBody & HTcIncClosure &
        HTcEnvClosure & HEnvShapeClosure & HTcClosure).
  destruct
    (initial_state_terminal_value_with_trace
      heap env rho ea stty_fun ctxt rgns tya effa
      (phi_as_list phi_arg) heap v_arg
      HTcHeapFun HHeapShapeFun HTcRho HTcInc
      (ext_stores__env stty stty_fun HExtFun rho env ctxt HTcEnv)
      (RuntimeEnvShape_store_ext
        stty rho env ctxt HEnvShape stty_fun HExtFun)
      HTcArg)
    as (stty_arg & HExtArg & HTcHeapArg & HHeapShapeArg &
        HArgVal & HArgShape & _HTcPhiArg).
  {
    eapply StepsPhi_as_steps; eauto.
  }
  inversion HTcClosure; subst.
  match goal with
  | HBodyBackAll : forall rho0,
      BackTriangle
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, rho0, ec, ee) |- _ =>
      pose proof (HBodyBackAll rho_closure) as HBodyBack
  end.
  match goal with
  | HFindX : find_T x ctxt_body = Some tyx,
    HFindF : find_T f ctxt_body =
      Some (Ty_Arrow tyx effc tyc effe Ty_Effect) |- _ =>
      assert
        (HTcIncBody :
          TcInc
            (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
              (x, tyx) ctxt_body,
             rgns_body))
      by
        (eapply ExtendedTcInv_2; eauto;
         inversion HTcIncClosure as [? ? HFrv]; subst;
         eapply HFrv; eauto)
  end.
  assert
    (HArgTyEq :
      subst_rho rho tya = subst_rho rho_closure tyx).
  {
    eapply subst_rho_arrow_arg_eq.
    exact HClosureTy.
  }
  assert
    (HClosureValArg :
      TcVal
        (stty_arg, Cls (env_closure, rho_closure, Mu f x ec ee),
         subst_rho rho_closure
           (Ty_Arrow tyx effc tyc effe Ty_Effect))).
  {
    eapply TC_Cls with (rgns := rgns_body) (ctxt := ctxt_body); eauto.
    eapply ext_stores__env; eauto.
  }
  assert
    (HClosureShapeArg :
      RuntimeValShape stty_arg
        (subst_rho rho_closure
          (Ty_Arrow tyx effc tyc effe Ty_Effect))
        (Cls (env_closure, rho_closure, Mu f x ec ee))).
  {
    eapply RVS_Arrow with (rgns := rgns_body) (ctxt := ctxt_body); eauto.
    - eapply ext_stores__env; eauto.
    - intros y vy tty HFindE HFindT.
      eapply RuntimeEnvShape_store_ext; eauto.
  }
  assert
    (HArgValBody :
      TcVal (stty_arg, v_arg, subst_rho rho_closure tyx)).
  {
    rewrite <- HArgTyEq.
    exact HArgVal.
  }
  assert
    (HArgShapeBody :
      RuntimeValShape stty_arg (subst_rho rho_closure tyx) v_arg).
  {
    rewrite <- HArgTyEq.
    exact HArgShape.
  }
  exists stty_arg, ctxt_body, rgns_body, tyx, effc, tyc, effe.
  split; [exact HTcHeapArg |].
  split; [exact HHeapShapeArg |].
  split; [exact HTcRhoBody |].
  split; [exact HTcIncBody |].
  split.
  - eapply TcEnv_update_rec; eauto.
    eapply ext_stores__env; eauto.
  - split.
    + eapply RuntimeEnvShape_update_rec; eauto.
      eapply RuntimeEnvShape_store_ext; eauto.
    + split; [exact HBodyBack |].
      split; assumption.
Qed.

Definition ScheduledSmallStepCorrectnessBelow (n : nat) : Prop :=
  forall n_child heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static,
    n_child < n ->
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    ScheduledCheckedTerminalN n_child
      (initial_state heap env rho ea)
      phi
      heap'
      v ->
    ScheduledCheckedTerminal
      (initial_state heap env rho ee)
      phi_summary
      heap_summary
      (Eff theta_summary) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    phi ⋞ theta_summary.

Lemma ScheduledSmallStepCorrectnessBelow_mono :
  forall n m,
    m <= n ->
    ScheduledSmallStepCorrectnessBelow n ->
    ScheduledSmallStepCorrectnessBelow m.
Proof.
  unfold ScheduledSmallStepCorrectnessBelow.
  intros n m HLe HBelow n_child heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HLt HBack HRun HSummary HTcHeap HHeapShape HTcRho HTcInc
    HTcEnv HEnvShape HTcExp.
  eapply HBelow; eauto; lia.
Qed.

Theorem MuAppEffAppTerminalSound_scheduled_from_body_soundness :
  forall heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      heap_mu
      v_mu ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      heap_eff
      (Eff theta) ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      env_closure rho_closure f x ec ee v_arg,
      ScheduledCheckedTerminal
        (initial_state heap env rho ef)
        phi_fun_mu
        heap
        (Cls (env_closure, rho_closure, Mu f x ec ee)) /\
      ScheduledCheckedTerminal
        (initial_state heap env rho ef)
        phi_fun_eff
        heap
        (Cls (env_closure, rho_closure, Mu f x ec ee)) /\
      ScheduledCheckedTerminal
        (initial_state heap env rho ea)
        phi_arg_mu
        heap
        v_arg /\
      ScheduledCheckedTerminal
        (initial_state heap env rho ea)
        phi_arg_eff
        heap
        v_arg /\
      ScheduledCheckedTerminal
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        heap_mu
        v_mu /\
      ScheduledCheckedTerminal
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        heap_eff
        (Eff theta) /\
      ReadOnlyPhi phi_fun_mu /\
      ReadOnlyPhi phi_arg_mu /\
      (phi_body_mu ⋞ theta ->
       phi_mu ⋞ Theta_Top).
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff.
  destruct
    (MuEffAppScheduledAlignedPrefixes_readonly_heap_neutral
      heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu HEff)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        phi_fun_eff & phi_arg_eff & phi_body_eff &
        env_closure & rho_closure & f & x & ec & ee & v_arg &
        HFunMu & HFunEff & HArgMu & HArgEff &
        HBodyMu & HBodyEff & HTraceMu & _HTraceEff &
        HFunRO & HArgRO).
  exists phi_fun_mu, phi_arg_mu, phi_body_mu.
  exists phi_fun_eff, phi_arg_eff, phi_body_eff.
  exists env_closure, rho_closure, f, x, ec, ee, v_arg.
  repeat split; try assumption.
  intros _.
  apply PhiInThetaTop.
Qed.

Lemma MuAppFunctionPrefix_body_backtriangle :
  forall heap env rho ef ea
    phi_fun env_closure rho_closure f x ec ee
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    StepsPhi
      (initial_state heap env rho ef)
      phi_fun
      (StDone heap
        (Cls (env_closure, rho_closure, Mu f x ec ee))) ->
    exists stty_cl ctxt_cl rgns_cl tyx effc tyc effe,
      StoreExtends stty stty_cl /\
      TcHeap (heap, stty_cl) /\
      RuntimeHeapShape heap stty_cl /\
      TcRho (rho_closure, rgns_cl) /\
      TcInc (ctxt_cl, rgns_cl) /\
      TcEnv (stty_cl, rho_closure, env_closure, ctxt_cl) /\
      RuntimeEnvShape stty_cl rho_closure env_closure ctxt_cl /\
      TcExp
        (ctxt_cl, rgns_cl, Mu f x ec ee,
          Ty_Arrow tyx effc tyc effe Ty_Effect,
          Empty_Static_Action) /\
      BackTriangle
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_cl,
         rgns_cl, rho_closure, ec, ee) /\
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_cl,
         rgns_cl, ec, tyc, effc) /\
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_cl,
         rgns_cl, ee, Ty_Effect, effe).
Proof.
  intros heap env rho ef ea
    phi_fun env_closure rho_closure f x ec ee
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HFun.
  destruct
    (BackTriangle_mu_app_eff_app_inv ctxt rgns rho ef ea HBack)
    as (_ty_mu & _ty_eff & ty_ef & _ty_ea &
        static_ef & _static_ea & _static_mu & _static_ee &
        _HTcMu & _HTcEff & _HReadOnlyEff &
        HTcEf & _HTcEa & _HBackEf & _HBackEa &
        _HReadOnlyEf & _HReadOnlyEa).
  destruct
    (initial_state_terminal_value_with_trace
      heap env rho ef stty ctxt rgns ty_ef static_ef
      (phi_as_list phi_fun) heap
      (Cls (env_closure, rho_closure, Mu f x ec ee))
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEf)
    as (stty_cl & HExt & HTcHeapCl & HHeapShapeCl &
        _HTcValCl & HValShapeCl & _HTcPhiFun).
  {
    eapply StepsPhi_as_steps; eauto.
  }
  destruct
    (RuntimeValShape_mu_closure_inv
      stty_cl (subst_rho rho ty_ef)
      env_closure rho_closure f x ec ee HValShapeCl)
    as (rgns_cl & ctxt_cl & tyx & effc & tyc & effe &
        _HClosureTy & HTcRhoCl & HTcIncCl & HTcEnvCl &
        HEnvShapeCl & HTcAbsCl).
  inversion HTcAbsCl; subst.
  match goal with
  | HBodyBackAll : forall rho0,
      BackTriangle
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_cl,
         rgns_cl, rho0, ec, ee) |- _ =>
      pose proof (HBodyBackAll rho_closure) as HBodyBack
  end.
  match goal with
  | HTcBodyMu : TcExp
      (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
        (x, tyx) ctxt_cl,
       rgns_cl, ec, tyc, effc),
    HTcBodyEff : TcExp
      (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
        (x, tyx) ctxt_cl,
       rgns_cl, ee, Ty_Effect, effe) |- _ =>
      pose proof HTcBodyMu as HBodyMuTc;
      pose proof HTcBodyEff as HBodyEffTc
  end.
  exists stty_cl, ctxt_cl, rgns_cl, tyx, effc, tyc, effe.
  split; [exact HExt |].
  split; [exact HTcHeapCl |].
  split; [exact HHeapShapeCl |].
  split; [exact HTcRhoCl |].
  split; [exact HTcIncCl |].
  split; [exact HTcEnvCl |].
  split; [exact HEnvShapeCl |].
  split; [exact HTcAbsCl |].
  split; [exact HBodyBack |].
	  split; [exact HBodyMuTc | exact HBodyEffTc].
Qed.

Theorem MuAppEffAppTerminalSound_scheduled_with_body_reasoning :
  forall heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      heap_mu
      v_mu ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      heap_eff
      (Eff theta) ->
    (forall stty_body ctxt_body rgns_body tyx effc tyc effe
       env_closure rho_closure f x ec ee v_arg
       phi_body_mu phi_body_eff,
      StoreExtends stty stty_body ->
      TcHeap (heap, stty_body) ->
      RuntimeHeapShape heap stty_body ->
      TcRho (rho_closure, rgns_body) ->
      TcInc (ctxt_body, rgns_body) ->
      TcEnv (stty_body, rho_closure, env_closure, ctxt_body) ->
      RuntimeEnvShape stty_body rho_closure env_closure ctxt_body ->
      TcExp
        (ctxt_body, rgns_body, Mu f x ec ee,
          Ty_Arrow tyx effc tyc effe Ty_Effect,
          Empty_Static_Action) ->
      BackTriangle
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, rho_closure, ec, ee) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, ec, tyc, effc) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, ee, Ty_Effect, effe) ->
      ScheduledCheckedTerminal
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        heap_mu
        v_mu ->
      ScheduledCheckedTerminal
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        heap_eff
        (Eff theta) ->
      phi_body_mu ⋞ theta) ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      env_closure rho_closure f x ec ee v_arg,
      ScheduledCheckedTerminal
        (initial_state heap env rho ef)
        phi_fun_mu
        heap
        (Cls (env_closure, rho_closure, Mu f x ec ee)) /\
      ScheduledCheckedTerminal
        (initial_state heap env rho ef)
        phi_fun_eff
        heap
        (Cls (env_closure, rho_closure, Mu f x ec ee)) /\
      ScheduledCheckedTerminal
        (initial_state heap env rho ea)
        phi_arg_mu
        heap
        v_arg /\
      ScheduledCheckedTerminal
        (initial_state heap env rho ea)
        phi_arg_eff
        heap
        v_arg /\
      ScheduledCheckedTerminal
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        heap_mu
        v_mu /\
      ScheduledCheckedTerminal
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        heap_eff
        (Eff theta) /\
      ReadOnlyPhi phi_fun_mu /\
      ReadOnlyPhi phi_arg_mu /\
      phi_mu ⋞ Theta_Top.
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HBodyReasoning.
  destruct
    (MuAppEffAppTerminalSound_scheduled_from_body_soundness
      heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu HEff)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        phi_fun_eff & phi_arg_eff & phi_body_eff &
        env_closure & rho_closure & f & x & ec & ee & v_arg &
        HFunMu & HFunEff & HArgMu & HArgEff &
        HBodyMu & HBodyEff & HFunRO & HArgRO & HAssemble).
  destruct
    (ScheduledCheckedTerminal_as_stepsphi_exists
      (initial_state heap env rho ef)
      phi_fun_mu heap
      (Cls (env_closure, rho_closure, Mu f x ec ee))
      HFunMu)
    as (phi_fun_steps & HFunSteps & _HFunTrace).
  destruct
    (MuAppFunctionPrefix_body_backtriangle
      heap env rho ef ea
      phi_fun_steps env_closure rho_closure f x ec ee
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HFunSteps)
    as (stty_body & ctxt_body & rgns_body &
        tyx & effc & tyc & effe &
        HExt & HTcHeapBody & HHeapShapeBody &
        HTcRhoBody & HTcIncBody & HTcEnvBody & HEnvShapeBody &
        HTcClosureBody & HBackBody & HTcBodyMu & HTcBodyEff).
  pose proof
    (HBodyReasoning
      stty_body ctxt_body rgns_body tyx effc tyc effe
      env_closure rho_closure f x ec ee v_arg
      phi_body_mu phi_body_eff
      HExt HTcHeapBody HHeapShapeBody HTcRhoBody HTcIncBody
      HTcEnvBody HEnvShapeBody HTcClosureBody HBackBody
      HTcBodyMu HTcBodyEff HBodyMu HBodyEff)
    as HBodySound.
  exists phi_fun_mu, phi_arg_mu, phi_body_mu.
  exists phi_fun_eff, phi_arg_eff, phi_body_eff.
  exists env_closure, rho_closure, f, x, ec, ee, v_arg.
  repeat split; try assumption.
  exact (HAssemble HBodySound).
Qed.

Theorem MuAppEffAppTerminalSound_scheduled_raw_from_component_soundness :
  forall heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      heap_mu
      v_mu ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      heap_eff
      (Eff theta) ->
    (forall ty_ef static_ef phi_fun heap_fun v_fun,
      TcExp (ctxt, rgns, ef, ty_ef, static_ef) ->
      BackTriangle (ctxt, rgns, rho, ef, Eff_App ef ea) ->
      ScheduledCheckedTerminal
        (initial_state heap env rho ef)
        phi_fun
        heap_fun
        v_fun ->
      ScheduledCheckedTerminal
        (initial_state heap env rho (Eff_App ef ea))
        phi_eff
        heap_eff
        (Eff theta) ->
      phi_fun ⋞ theta) ->
    (forall ty_ea static_ea phi_arg heap_arg v_arg,
      TcExp (ctxt, rgns, ea, ty_ea, static_ea) ->
      BackTriangle (ctxt, rgns, rho, ea, Eff_App ef ea) ->
      ScheduledCheckedTerminal
        (initial_state heap env rho ea)
        phi_arg
        heap_arg
        v_arg ->
      ScheduledCheckedTerminal
        (initial_state heap env rho (Eff_App ef ea))
        phi_eff
        heap_eff
        (Eff theta) ->
      phi_arg ⋞ theta) ->
    (forall stty_body ctxt_body rgns_body tyx effc tyc effe
       env_closure rho_closure f x ec ee v_arg
       phi_body_mu phi_body_eff,
      StoreExtends stty stty_body ->
      TcHeap (heap, stty_body) ->
      RuntimeHeapShape heap stty_body ->
      TcRho (rho_closure, rgns_body) ->
      TcInc (ctxt_body, rgns_body) ->
      TcEnv (stty_body, rho_closure, env_closure, ctxt_body) ->
      RuntimeEnvShape stty_body rho_closure env_closure ctxt_body ->
      TcExp
        (ctxt_body, rgns_body, Mu f x ec ee,
          Ty_Arrow tyx effc tyc effe Ty_Effect,
          Empty_Static_Action) ->
      BackTriangle
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, rho_closure, ec, ee) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, ec, tyc, effc) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, ee, Ty_Effect, effe) ->
      ScheduledCheckedTerminal
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        heap_mu
        v_mu ->
      ScheduledCheckedTerminal
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        heap_eff
        (Eff theta) ->
      phi_body_mu ⋞ theta) ->
    phi_mu ⋞ theta.
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HFunReasoning HArgReasoning HBodyReasoning.
  destruct
    (BackTriangle_mu_app_eff_app_inv ctxt rgns rho ef ea HBack)
    as (_ty_mu & _ty_eff & ty_ef & ty_ea &
        static_ef & static_ea & _static_mu & _static_ee &
        _HTcMu & _HTcEff & _HReadOnlyEff &
        HTcEf & HTcEa & HBackEf & HBackEa &
        _HReadOnlyEf & _HReadOnlyEa).
  destruct
    (MuEffAppScheduledAlignedPrefixes_readonly_heap_neutral
      heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu HEff)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        phi_fun_eff & phi_arg_eff & phi_body_eff &
        env_closure & rho_closure & f & x & ec & ee & v_arg &
        HFunMu & _HFunEff & HArgMu & _HArgEff &
        HBodyMu & HBodyEff & HTraceMu & _HTraceEff &
        _HFunRO & _HArgRO).
  destruct
    (ScheduledCheckedTerminal_as_stepsphi_exists
      (initial_state heap env rho ef)
      phi_fun_mu heap
      (Cls (env_closure, rho_closure, Mu f x ec ee))
      HFunMu)
    as (phi_fun_steps & HFunSteps & _HFunTrace).
  destruct
    (MuAppFunctionPrefix_body_backtriangle
      heap env rho ef ea
      phi_fun_steps env_closure rho_closure f x ec ee
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HFunSteps)
    as (stty_body & ctxt_body & rgns_body &
        tyx & effc & tyc & effe &
        HExt & HTcHeapBody & HHeapShapeBody &
        HTcRhoBody & HTcIncBody & HTcEnvBody & HEnvShapeBody &
        HTcClosureBody & HBackBody & HTcBodyMu & HTcBodyEff).
  pose proof
    (HFunReasoning
      ty_ef static_ef phi_fun_mu heap
      (Cls (env_closure, rho_closure, Mu f x ec ee))
      HTcEf HBackEf HFunMu HEff)
    as HFunSound.
  pose proof
    (HArgReasoning
      ty_ea static_ea phi_arg_mu heap v_arg
      HTcEa HBackEa HArgMu HEff)
    as HArgSound.
  pose proof
    (HBodyReasoning
      stty_body ctxt_body rgns_body tyx effc tyc effe
      env_closure rho_closure f x ec ee v_arg
      phi_body_mu phi_body_eff
      HExt HTcHeapBody HHeapShapeBody HTcRhoBody HTcIncBody
      HTcEnvBody HEnvShapeBody HTcClosureBody HBackBody
      HTcBodyMu HTcBodyEff HBodyMu HBodyEff)
    as HBodySound.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with
      (phi2 := Phi_Seq phi_fun_mu (Phi_Seq phi_arg_mu phi_body_mu)).
  - simpl. exact HTraceMu.
  - apply PTS_Seq.
    + exact HFunSound.
    + apply PTS_Seq; assumption.
Qed.

Theorem MuAppEffAppTerminalSound_scheduled_raw_from_below_N :
  forall n heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    ScheduledCheckedTerminalN n
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      heap_mu
      v_mu ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      heap_eff
      (Eff theta) ->
    ScheduledSmallStepCorrectnessBelow n ->
    phi_mu ⋞ theta.
Proof.
  intros n heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HBelow.
  destruct
    (BackTriangle_mu_app_eff_app_inv ctxt rgns rho ef ea HBack)
    as (_ty_mu & _ty_eff & ty_ef & ty_ea &
        static_ef & static_ea & _static_mu & _static_ee &
        _HTcMu & _HTcEff & _HReadOnlyEff &
        HTcEf & HTcEa & HBackEf & HBackEa &
        _HReadOnlyEf & _HReadOnlyEa).
  destruct
    (MuEffAppScheduledAlignedPrefixes_readonly_heap_neutral_N
      n heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu HEff)
    as (n_fun & n_arg & n_body &
        phi_fun_mu & phi_arg_mu & phi_body_mu &
        phi_fun_eff & phi_arg_eff & phi_body_eff &
        env_closure & rho_closure & f & x & ec & ee & v_arg &
        HNFun & HNArg & HNBody &
        HFunMuN & _HFunEff & HArgMuN & _HArgEff &
        HBodyMuN & HBodyEff & HTraceMu & _HTraceEff &
        _HFunRO & _HArgRO).
  pose proof
    (ScheduledCheckedTerminalN_to_terminal
      n_fun
      (initial_state heap env rho ef)
      phi_fun_mu heap
      (Cls (env_closure, rho_closure, Mu f x ec ee))
      HFunMuN)
    as HFunMu.
  pose proof
    (ScheduledCheckedTerminalN_to_terminal
      n_arg
      (initial_state heap env rho ea)
      phi_arg_mu heap v_arg
      HArgMuN)
    as HArgMu.
  destruct
    (ScheduledCheckedTerminal_as_stepsphi_exists
      (initial_state heap env rho ef)
      phi_fun_mu heap
      (Cls (env_closure, rho_closure, Mu f x ec ee))
      HFunMu)
    as (phi_fun_steps & HFunSteps & _HFunTrace).
  destruct
    (ScheduledCheckedTerminal_as_stepsphi_exists
      (initial_state heap env rho ea)
      phi_arg_mu heap v_arg
      HArgMu)
    as (phi_arg_steps & HArgSteps & _HArgTrace).
  destruct
    (MuAppBodyRuntimeTyping_from_prefixes
      heap env rho ef ea
      phi_fun_steps phi_arg_steps
      env_closure rho_closure f x ec ee v_arg
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HFunSteps HArgSteps)
    as (stty_body & ctxt_body & rgns_body & tyx & effc & tyc & effe &
        HTcHeapBody & HHeapShapeBody & HTcRhoBody & HTcIncBody &
        HTcEnvBody & HEnvShapeBody & HBackBody &
        HTcBodyMu & _HTcBodyEff).
  pose proof
    (HBelow n_fun heap env rho ef (Eff_App ef ea)
      phi_fun_mu heap
      (Cls (env_closure, rho_closure, Mu f x ec ee))
      phi_eff heap_eff theta
      stty ctxt rgns ty_ef static_ef
      HNFun HBackEf HFunMuN HEff
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEf)
    as HFunSound.
  pose proof
    (HBelow n_arg heap env rho ea (Eff_App ef ea)
      phi_arg_mu heap v_arg
      phi_eff heap_eff theta
      stty ctxt rgns ty_ea static_ea
      HNArg HBackEa HArgMuN HEff
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEa)
    as HArgSound.
  pose proof
    (HBelow n_body heap
      (update_rec_E
        (f, Cls (env_closure, rho_closure, Mu f x ec ee))
        (x, v_arg) env_closure)
      rho_closure ec ee
      phi_body_mu heap_mu v_mu
      phi_body_eff heap_eff theta
      stty_body
      (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
        (x, tyx) ctxt_body)
      rgns_body tyc effc
      HNBody HBackBody HBodyMuN HBodyEff
      HTcHeapBody HHeapShapeBody HTcRhoBody HTcIncBody
      HTcEnvBody HEnvShapeBody HTcBodyMu)
    as HBodySound.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with
      (phi2 := Phi_Seq phi_fun_mu (Phi_Seq phi_arg_mu phi_body_mu)).
  - simpl. exact HTraceMu.
  - apply PTS_Seq.
    + exact HFunSound.
    + apply PTS_Seq; assumption.
Qed.

Theorem MuEffAppAlignedPrefixes_readonly_heap_neutral :
  forall heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      (StDone heap_mu v_mu) ->
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      (StDone heap_eff (Eff theta)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea)) ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_mu
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_eff
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_mu
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_eff
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu v_mu) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff (Eff theta)) /\
      phi_as_list phi_mu =
        phi_as_list phi_fun_mu ++
        phi_as_list phi_arg_mu ++
        phi_as_list phi_body_mu /\
      phi_as_list phi_eff =
        phi_as_list phi_fun_eff ++
        phi_as_list phi_arg_eff ++
        phi_as_list phi_body_eff /\
      phi_as_list phi_fun_mu = phi_as_list phi_fun_eff /\
      phi_as_list phi_arg_mu = phi_as_list phi_arg_eff /\
      ReadOnlyPhi phi_fun_mu /\
      ReadOnlyPhi phi_arg_mu.
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HStayFun HStayArg.
  destruct
    (BackTriangle_mu_app_eff_app_inv ctxt rgns rho ef ea HBack)
    as (ty_mu & ty_eff & ty_ef & ty_ea &
        static_ef & static_ea & static_mu & static_ee &
        _HTcMu & _HTcEff & _HReadOnlyEff &
        HTcEf & HTcEa & _HBackEf & _HBackEa &
        HReadOnlyEf & HReadOnlyEa).
  destruct
    (MuEffAppTerminalAlignedBodyDecompose
      heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      HMu HEff HStayFun HStayArg)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        phi_fun_eff & phi_arg_eff & phi_body_eff &
        heap_fun & heap_arg & env_closure & rho_closure &
        f & x & ec & ee & v_arg &
        HFunMu & HFunEff & HArgMu & HArgEff & HBodyMu & HBodyEff &
        HTraceMu & HTraceEff & HFunTrace & HArgTrace).
  assert (HFunStaticSound :
    Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, phi_fun_mu)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_eff_sound with
      (t := ty_ef) (eff := static_ef)
      (heap' := heap_fun)
      (v := Cls (env_closure, rho_closure, Mu f x ec ee));
      eauto.
    eapply StepsPhi_as_steps; eauto.
  }
  assert (HFunRO : ReadOnlyPhi phi_fun_mu).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ef)
        phi_fun_mu
        HReadOnlyEf
        HFunStaticSound).
  }
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho ef)
      phi_fun_mu
      (StDone heap_fun
        (Cls (env_closure, rho_closure, Mu f x ec ee)))
      HFunMu HFunRO)
    as HHeapFun.
  simpl in HHeapFun.
  symmetry in HHeapFun.
  subst heap_fun.
  assert (HArgStaticSound :
    Epsilon_Phi_Soundness (fold_subst_eps rho static_ea, phi_arg_mu)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_eff_sound with
      (t := ty_ea) (eff := static_ea)
      (heap' := heap_arg) (v := v_arg);
      eauto.
    eapply StepsPhi_as_steps; eauto.
  }
  assert (HArgRO : ReadOnlyPhi phi_arg_mu).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ea)
        phi_arg_mu
        HReadOnlyEa
        HArgStaticSound).
  }
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho ea)
      phi_arg_mu
      (StDone heap_arg v_arg)
      HArgMu HArgRO)
    as HHeapArg.
  simpl in HHeapArg.
  symmetry in HHeapArg.
  subst heap_arg.
  exists phi_fun_mu, phi_arg_mu, phi_body_mu,
    phi_fun_eff, phi_arg_eff, phi_body_eff,
    env_closure, rho_closure, f, x, ec, ee, v_arg.
  repeat split; try assumption.
Qed.

Theorem MuAppEffAppTerminalSound_with_readonly_prefixes_from_body_soundness :
  forall heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      (StDone heap_mu v_mu) ->
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      (StDone heap_eff (Eff theta)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea)) ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_mu
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_eff
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_mu
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_eff
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu v_mu) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff (Eff theta)) /\
      phi_as_list phi_fun_mu = phi_as_list phi_fun_eff /\
      phi_as_list phi_arg_mu = phi_as_list phi_arg_eff /\
      ReadOnlyPhi phi_fun_mu /\
      ReadOnlyPhi phi_arg_mu /\
      (phi_body_mu ⋞ theta ->
       phi_mu ⋞ Theta_Top).
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HStayFun HStayArg.
  destruct
    (MuEffAppAlignedPrefixes_readonly_heap_neutral
      heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu HEff HStayFun HStayArg)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        phi_fun_eff & phi_arg_eff & phi_body_eff &
        env_closure & rho_closure & f & x & ec & ee & v_arg &
        HFunMu & HFunEff & HArgMu & HArgEff &
        HBodyMu & HBodyEff & HTraceMu & _HTraceEff &
        HFunTrace & HArgTrace & HFunRO & HArgRO).
  exists phi_fun_mu, phi_arg_mu, phi_body_mu.
  exists phi_fun_eff, phi_arg_eff, phi_body_eff.
  exists env_closure, rho_closure, f, x, ec, ee, v_arg.
  repeat split; try assumption.
  intros _.
  apply PhiInThetaTop.
Qed.

Theorem MuEffAppAlignedPrefixes_readonly_heap_neutral_counted :
  forall n heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    StepsPhiN n
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      (StDone heap_mu v_mu) ->
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      (StDone heap_eff (Eff theta)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea)) ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      env_closure rho_closure f x ec ee v_arg n_body,
      n_body < n /\
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_mu
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_eff
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_mu
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_eff
        (StDone heap v_arg) /\
      StepsPhiN n_body
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu v_mu) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff (Eff theta)) /\
      phi_as_list phi_mu =
        phi_as_list phi_fun_mu ++
        phi_as_list phi_arg_mu ++
        phi_as_list phi_body_mu /\
      phi_as_list phi_eff =
        phi_as_list phi_fun_eff ++
        phi_as_list phi_arg_eff ++
        phi_as_list phi_body_eff /\
      phi_as_list phi_fun_mu = phi_as_list phi_fun_eff /\
      phi_as_list phi_arg_mu = phi_as_list phi_arg_eff /\
      ReadOnlyPhi phi_fun_mu /\
      ReadOnlyPhi phi_arg_mu.
Proof.
  intros n heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HStayFun HStayArg.
  destruct
    (BackTriangle_mu_app_eff_app_inv ctxt rgns rho ef ea HBack)
    as (ty_mu & ty_eff & ty_ef & ty_ea &
        static_ef & static_ea & static_mu & static_ee &
        _HTcMu & _HTcEff & _HReadOnlyEff &
        HTcEf & HTcEa & _HBackEf & _HBackEa &
        HReadOnlyEf & HReadOnlyEa).
  destruct
    (StepsPhiN_mu_app_terminal_decompose_counts
      n heap env rho ef ea phi_mu heap_mu v_mu HMu)
    as (env_mu & rho_mu & f_mu & x_mu & ec_mu & ee_mu &
        n_fun_mu & phi_fun_mu & heap_fun_mu &
        n_arg_mu & phi_arg_mu & heap_arg_mu & v_arg_mu &
        n_body_mu & phi_body_mu &
        HNFun & HNArg & HNBody &
        HFunMuN & HArgMuN & HBodyMuN & HTraceMu).
  pose proof (StepsPhiN_to_StepsPhi _ _ _ _ HFunMuN) as HFunMu.
  pose proof (StepsPhiN_to_StepsPhi _ _ _ _ HArgMuN) as HArgMu.
  pose proof (StepsPhiN_to_StepsPhi _ _ _ _ HBodyMuN) as HBodyMu.
  destruct
    (EffAppTerminalDecompose
      heap env rho ef ea phi_eff heap_eff (Eff theta) HEff)
    as (phi_fun_eff & phi_arg_eff & phi_body_eff &
        heap_fun_eff & heap_arg_eff & env_eff & rho_eff &
        f_eff & x_eff & ec_eff & ee_eff & v_arg_eff &
        HFunEff & HArgEff & HBodyEff & HTraceEff).
  destruct
    (StepsPhi_terminal_deterministic
      (initial_state heap env rho ef)
      phi_fun_mu heap_fun_mu
      (Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu))
		      phi_fun_eff heap_fun_eff
		      (Cls (env_eff, rho_eff, Mu f_eff x_eff ec_eff ee_eff))
		      HStayFun
		      HFunMu HFunEff)
    as (HFunTrace & HHeapFunEq & HClosureEq).
  subst heap_fun_eff.
  symmetry in HClosureEq.
  inversion HClosureEq; subst.
  destruct
    (StepsPhi_terminal_deterministic
		      (initial_state heap_fun_mu env rho ea)
		      phi_arg_mu heap_arg_mu v_arg_mu
		      phi_arg_eff heap_arg_eff v_arg_eff
		      (HStayArg heap_fun_mu)
		      HArgMu HArgEff)
    as (HArgTrace & HHeapArgEq & HArgValEq).
  subst heap_arg_eff.
  subst v_arg_eff.
  assert (HFunStaticSound :
    Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, phi_fun_mu)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_eff_sound with
      (t := ty_ef) (eff := static_ef)
      (heap' := heap_fun_mu)
      (v := Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu));
      eauto.
    eapply StepsPhi_as_steps; eauto.
  }
  assert (HFunRO : ReadOnlyPhi phi_fun_mu).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ef)
        phi_fun_mu
        HReadOnlyEf
        HFunStaticSound).
  }
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho ef)
      phi_fun_mu
      (StDone heap_fun_mu
        (Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu)))
      HFunMu HFunRO)
    as HHeapFun.
  simpl in HHeapFun.
  symmetry in HHeapFun.
  subst heap_fun_mu.
  assert (HArgStaticSound :
    Epsilon_Phi_Soundness (fold_subst_eps rho static_ea, phi_arg_mu)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_eff_sound with
      (t := ty_ea) (eff := static_ea)
      (heap' := heap_arg_mu) (v := v_arg_mu);
      eauto.
    eapply StepsPhi_as_steps; eauto.
  }
  assert (HArgRO : ReadOnlyPhi phi_arg_mu).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ea)
        phi_arg_mu
        HReadOnlyEa
        HArgStaticSound).
  }
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho ea)
      phi_arg_mu
      (StDone heap_arg_mu v_arg_mu)
      HArgMu HArgRO)
    as HHeapArg.
  simpl in HHeapArg.
  symmetry in HHeapArg.
  subst heap_arg_mu.
  exists phi_fun_mu, phi_arg_mu, phi_body_mu.
  exists phi_fun_eff, phi_arg_eff, phi_body_eff.
  exists env_mu, rho_mu, f_mu, x_mu, ec_mu, ee_mu, v_arg_mu, n_body_mu.
  repeat split; try assumption.
Qed.

Theorem MuAppEffAppTerminalSound_with_readonly_prefixes_from_below :
  forall n heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    StepsPhiN n
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      (StDone heap_mu v_mu) ->
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      (StDone heap_eff (Eff theta)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea)) ->
    SmallStepCorrectnessBelow n ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_mu
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_eff
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_mu
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_eff
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu v_mu) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff (Eff theta)) /\
      ReadOnlyPhi phi_fun_mu /\
      ReadOnlyPhi phi_arg_mu /\
      phi_mu ⋞ Theta_Top.
Proof.
  intros n heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HStayFun HStayArg HBelow.
  destruct
    (MuEffAppAlignedPrefixes_readonly_heap_neutral_counted
      n heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu HEff HStayFun HStayArg)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        phi_fun_eff & phi_arg_eff & phi_body_eff &
        env_closure & rho_closure & f & x & ec & ee & v_arg &
        n_body & HNBody & HFunMu & HFunEff & HArgMu & HArgEff &
        HBodyMuN & HBodyEff & HTraceMu & _HTraceEff &
        _HFunTrace & _HArgTrace & HFunRO & HArgRO).
  destruct
    (MuAppBodyRuntimeTyping_from_prefixes
      heap env rho ef ea
      phi_fun_mu phi_arg_mu
      env_closure rho_closure f x ec ee v_arg
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HFunMu HArgMu)
    as (stty_body & ctxt_body & rgns_body & tyx & effc & tyc & effe &
        HTcHeapBody & HHeapShapeBody & HTcRhoBody & HTcIncBody &
        HTcEnvBody & HEnvShapeBody & HBackBody &
        HTcBodyMu & HTcBodyEff).
  pose proof
    (HBelow
      n_body heap
      (update_rec_E
        (f, Cls (env_closure, rho_closure, Mu f x ec ee))
        (x, v_arg) env_closure)
      rho_closure ec ee
      phi_body_mu heap_mu v_mu
      phi_body_eff heap_eff theta
      stty_body
      (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
        (x, tyx) ctxt_body)
      rgns_body tyc effc
      HNBody HBackBody HBodyMuN HBodyEff
      HTcHeapBody HHeapShapeBody HTcRhoBody HTcIncBody
      HTcEnvBody HEnvShapeBody HTcBodyMu)
    as HBodySound.
  exists phi_fun_mu, phi_arg_mu, phi_body_mu.
  exists phi_fun_eff, phi_arg_eff, phi_body_eff.
  exists env_closure, rho_closure, f, x, ec, ee, v_arg.
  repeat split; try assumption.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HBodyMuN).
  - apply PhiInThetaTop.
Qed.

Theorem MuAppEffAppTerminalSound_raw_from_below :
  forall n heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    StepsPhiN n
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      (StDone heap_mu v_mu) ->
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      (StDone heap_eff (Eff theta)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea)) ->
    SmallStepCorrectnessBelow n ->
    phi_mu ⋞ theta.
Proof.
  intros n heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HStayFun HStayArg HBelow.
  destruct
    (BackTriangle_mu_app_eff_app_inv ctxt rgns rho ef ea HBack)
    as (_ty_mu & _ty_eff & ty_ef & ty_ea &
        static_ef & static_ea & _static_mu & _static_ee &
        _HTcMu & _HTcEff & _HReadOnlyEff &
        HTcEf & HTcEa & HBackEf & HBackEa &
        HReadOnlyEf & HReadOnlyEa).
  destruct
    (StepsPhiN_mu_app_terminal_decompose_counts
      n heap env rho ef ea phi_mu heap_mu v_mu HMu)
    as (env_mu & rho_mu & f_mu & x_mu & ec_mu & ee_mu &
        n_fun_mu & phi_fun_mu & heap_fun_mu &
        n_arg_mu & phi_arg_mu & heap_arg_mu & v_arg_mu &
        n_body_mu & phi_body_mu &
        HNFun & HNArg & HNBody &
        HFunMuN & HArgMuN & HBodyMuN & HTraceMu).
  pose proof (StepsPhiN_to_StepsPhi _ _ _ _ HFunMuN) as HFunMu.
  pose proof (StepsPhiN_to_StepsPhi _ _ _ _ HArgMuN) as HArgMu.
  destruct
    (EffAppTerminalDecompose
      heap env rho ef ea phi_eff heap_eff (Eff theta) HEff)
    as (phi_fun_eff & phi_arg_eff & phi_body_eff &
        heap_fun_eff & heap_arg_eff & env_eff & rho_eff &
        f_eff & x_eff & ec_eff & ee_eff & v_arg_eff &
        HFunEff & HArgEff & HBodyEff & _HTraceEff).
  destruct
    (StepsPhi_terminal_deterministic
      (initial_state heap env rho ef)
      phi_fun_mu heap_fun_mu
      (Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu))
		      phi_fun_eff heap_fun_eff
		      (Cls (env_eff, rho_eff, Mu f_eff x_eff ec_eff ee_eff))
		      HStayFun
		      HFunMu HFunEff)
    as (_HFunTrace & HHeapFunEq & HClosureEq).
  subst heap_fun_eff.
  symmetry in HClosureEq.
  inversion HClosureEq; subst.
  assert (HFunStaticSound :
    Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, phi_fun_mu)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_eff_sound with
      (t := ty_ef) (eff := static_ef)
      (heap' := heap_fun_mu)
      (v := Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu));
      eauto.
    eapply StepsPhi_as_steps; eauto.
  }
  assert (HFunRO : ReadOnlyPhi phi_fun_mu).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ef)
        phi_fun_mu
        HReadOnlyEf
        HFunStaticSound).
  }
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho ef)
      phi_fun_mu
      (StDone heap_fun_mu
        (Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu)))
      HFunMu HFunRO)
    as HHeapFun.
  simpl in HHeapFun.
  symmetry in HHeapFun.
  subst heap_fun_mu.
  destruct
    (StepsPhi_terminal_deterministic
		      (initial_state heap env rho ea)
		      phi_arg_mu heap_arg_mu v_arg_mu
		      phi_arg_eff heap_arg_eff v_arg_eff
		      (HStayArg heap)
		      HArgMu HArgEff)
    as (_HArgTrace & HHeapArgEq & HArgValEq).
  subst heap_arg_eff.
  subst v_arg_eff.
  assert (HArgStaticSound :
    Epsilon_Phi_Soundness (fold_subst_eps rho static_ea, phi_arg_mu)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_eff_sound with
      (t := ty_ea) (eff := static_ea)
      (heap' := heap_arg_mu) (v := v_arg_mu);
      eauto.
    eapply StepsPhi_as_steps; eauto.
  }
  assert (HArgRO : ReadOnlyPhi phi_arg_mu).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ea)
        phi_arg_mu
        HReadOnlyEa
        HArgStaticSound).
  }
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho ea)
      phi_arg_mu
      (StDone heap_arg_mu v_arg_mu)
      HArgMu HArgRO)
    as HHeapArg.
  simpl in HHeapArg.
  symmetry in HHeapArg.
  subst heap_arg_mu.
  destruct
    (MuAppBodyRuntimeTyping_from_prefixes
      heap env rho ef ea
      phi_fun_mu phi_arg_mu
      env_mu rho_mu f_mu x_mu ec_mu ee_mu v_arg_mu
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HFunMu HArgMu)
    as (stty_body & ctxt_body & rgns_body & tyx & effc & tyc & effe &
        HTcHeapBody & HHeapShapeBody & HTcRhoBody & HTcIncBody &
        HTcEnvBody & HEnvShapeBody & HBackBody &
        HTcBodyMu & _HTcBodyEff).
  pose proof
    (HBelow n_fun_mu heap env rho ef (Eff_App ef ea)
      phi_fun_mu heap
      (Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu))
      phi_eff heap_eff theta
      stty ctxt rgns ty_ef static_ef
      HNFun HBackEf HFunMuN HEff
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEf)
    as HFunSound.
  pose proof
    (HBelow n_arg_mu heap env rho ea (Eff_App ef ea)
      phi_arg_mu heap v_arg_mu
      phi_eff heap_eff theta
      stty ctxt rgns ty_ea static_ea
      HNArg HBackEa HArgMuN HEff
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEa)
    as HArgSound.
  pose proof
    (HBelow n_body_mu heap
      (update_rec_E
        (f_mu, Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu))
        (x_mu, v_arg_mu) env_mu)
      rho_mu ec_mu ee_mu
      phi_body_mu heap_mu v_mu
      phi_body_eff heap_eff theta
      stty_body
      (update_rec_T (f_mu, Ty_Arrow tyx effc tyc effe Ty_Effect)
        (x_mu, tyx) ctxt_body)
      rgns_body tyc effc
      HNBody HBackBody HBodyMuN HBodyEff
      HTcHeapBody HHeapShapeBody HTcRhoBody HTcIncBody
      HTcEnvBody HEnvShapeBody HTcBodyMu)
    as HBodySound.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with (phi2 := Phi_Seq phi_fun_mu (Phi_Seq phi_arg_mu phi_body_mu)).
  - simpl. exact HTraceMu.
  - apply PTS_Seq.
    + exact HFunSound.
    + apply PTS_Seq; assumption.
Qed.

Theorem MuAppEffAppTerminalSound_with_readonly_prefixes_with_body_reasoning :
  forall heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      (StDone heap_mu v_mu) ->
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      (StDone heap_eff (Eff theta)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea)) ->
    (forall stty_body ctxt_body rgns_body tyx effc tyc effe
       env_closure rho_closure f x ec ee v_arg
       phi_body_mu phi_body_eff,
      StoreExtends stty stty_body ->
      TcHeap (heap, stty_body) ->
      RuntimeHeapShape heap stty_body ->
      TcRho (rho_closure, rgns_body) ->
      TcInc (ctxt_body, rgns_body) ->
      TcEnv (stty_body, rho_closure, env_closure, ctxt_body) ->
      RuntimeEnvShape stty_body rho_closure env_closure ctxt_body ->
      TcExp
        (ctxt_body, rgns_body, Mu f x ec ee,
          Ty_Arrow tyx effc tyc effe Ty_Effect,
          Empty_Static_Action) ->
      BackTriangle
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, rho_closure, ec, ee) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, ec, tyc, effc) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, ee, Ty_Effect, effe) ->
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu v_mu) ->
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff (Eff theta)) ->
      phi_body_mu ⋞ theta) ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_mu
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_eff
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_mu
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_eff
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu v_mu) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff (Eff theta)) /\
      ReadOnlyPhi phi_fun_mu /\
      ReadOnlyPhi phi_arg_mu /\
      phi_mu ⋞ Theta_Top.
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HStayFun HStayArg HBodyReasoning.
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_from_body_soundness
      heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu HEff HStayFun HStayArg)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        phi_fun_eff & phi_arg_eff & phi_body_eff &
        env_closure & rho_closure & f & x & ec & ee & v_arg &
        HFunMu & HFunEff & HArgMu & HArgEff &
        HBodyMu & HBodyEff & _HFunTrace & _HArgTrace &
        HFunRO & HArgRO & HAssemble).
  destruct
    (MuAppFunctionPrefix_body_backtriangle
      heap env rho ef ea
      phi_fun_mu env_closure rho_closure f x ec ee
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HFunMu)
    as (stty_body & ctxt_body & rgns_body &
        tyx & effc & tyc & effe &
        HExt & HTcHeapBody & HHeapShapeBody &
        HTcRhoBody & HTcIncBody & HTcEnvBody & HEnvShapeBody &
        HTcClosureBody & HBackBody & HTcBodyMu & HTcBodyEff).
  pose proof
    (HBodyReasoning
      stty_body ctxt_body rgns_body tyx effc tyc effe
      env_closure rho_closure f x ec ee v_arg
      phi_body_mu phi_body_eff
      HExt HTcHeapBody HHeapShapeBody HTcRhoBody HTcIncBody
      HTcEnvBody HEnvShapeBody HTcClosureBody HBackBody
      HTcBodyMu HTcBodyEff HBodyMu HBodyEff)
    as HBodySound.
  exists phi_fun_mu, phi_arg_mu, phi_body_mu.
  exists phi_fun_eff, phi_arg_eff, phi_body_eff.
  exists env_closure, rho_closure, f, x, ec, ee, v_arg.
  repeat split; try assumption.
  exact (HAssemble HBodySound).
Qed.

Theorem MuAppEffAppTerminalSound_reduces_to_component_soundness :
  forall heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta,
    StepsPhi
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      (StDone heap_mu v_mu) ->
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      (StDone heap_eff (Eff theta)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea)) ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      heap_fun heap_arg env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_mu
        (StDone heap_fun
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_eff
        (StDone heap_fun
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap_fun env rho ea)
        phi_arg_mu
        (StDone heap_arg v_arg) /\
      StepsPhi
        (initial_state heap_fun env rho ea)
        phi_arg_eff
        (StDone heap_arg v_arg) /\
      StepsPhi
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu v_mu) /\
      StepsPhi
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff (Eff theta)) /\
      phi_as_list phi_fun_mu = phi_as_list phi_fun_eff /\
      phi_as_list phi_arg_mu = phi_as_list phi_arg_eff /\
      (phi_fun_mu ⋞ theta ->
       phi_arg_mu ⋞ theta ->
       phi_body_mu ⋞ theta ->
       phi_mu ⋞ theta).
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    HMu HEff HStayFun HStayArg.
  destruct
    (MuEffAppTerminalAlignedBodyDecompose
      heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      HMu HEff HStayFun HStayArg)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        phi_fun_eff & phi_arg_eff & phi_body_eff &
        heap_fun & heap_arg & env_closure & rho_closure &
        f & x & ec & ee & v_arg &
        HFunMu & HFunEff & HArgMu & HArgEff & HBodyMu & HBodyEff &
        HTraceMu & _ & HFunTrace & HArgTrace).
  exists phi_fun_mu, phi_arg_mu, phi_body_mu,
    phi_fun_eff, phi_arg_eff, phi_body_eff,
    heap_fun, heap_arg, env_closure, rho_closure,
    f, x, ec, ee, v_arg.
  repeat split; try assumption.
  intros HFunSound HArgSound HBodySound.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with
      (phi2 := Phi_Seq phi_fun_mu (Phi_Seq phi_arg_mu phi_body_mu)).
  - simpl. exact HTraceMu.
  - apply PTS_Seq.
    + exact HFunSound.
    + apply PTS_Seq; assumption.
Qed.
