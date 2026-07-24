From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Wf_nat.
From Stdlib Require Import Program.Equality.

(* Shared terminal-run decompositions and small-step correctness utilities. *)

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
Require Import theories.Determinism.SmallStepPairParScheduleDeterminism.

Inductive StepsPhiN : nat -> State -> Phi -> State -> Prop :=
| StepsPhiN_Refl :
    forall state,
      StepsPhiN 0 state Phi_Nil state
| StepsPhiN_Step :
    forall n state label state' phi state'',
      Step state label state' ->
      StepsPhiN n state' phi state'' ->
      StepsPhiN (S n) state (Phi_Seq (label_phi label) phi) state''.

Lemma StepsPhiN_to_StepsPhi :
  forall n state phi state',
    StepsPhiN n state phi state' ->
    StepsPhi state phi state'.
Proof.
  intros n state phi state' HSteps.
  induction HSteps.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma StepsPhi_to_StepsPhiN :
  forall state phi state',
    StepsPhi state phi state' ->
    exists n, StepsPhiN n state phi state'.
Proof.
  intros state phi state' HSteps.
  induction HSteps as [state | state label state1 phi state2 HStep _ IH].
  - exists 0. constructor.
  - destruct IH as [n HStepsN].
    exists (S n).
    econstructor; eauto.
Qed.

Lemma StepsPhiN_terminal_inv_step :
  forall n state label state' phi heap_done v_done,
    NonPairParRunState state ->
    Step state label state' ->
    StepsPhiN n state phi (StDone heap_done v_done) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      StepsPhiN n_tail state' phi_tail (StDone heap_done v_done) /\
      phi_as_list phi = label_trace label ++ phi_as_list phi_tail.
Proof.
  intros n state label state' phi heap_done v_done HNonPair HStep HSteps.
  inversion HSteps; subst.
  - exfalso. eapply done_no_step; eauto.
  - destruct (step_deterministic _ _ _ _ _ HNonPair HStep H)
      as (HLabel & HState).
    subst.
    exists n0, phi0.
    repeat split; eauto.
    simpl. now rewrite phi_as_list_label_phi.
Qed.

Lemma StepsPhiN_from_done_inv :
  forall n heap v phi state',
    StepsPhiN n (StDone heap v) phi state' ->
    n = 0 /\ phi = Phi_Nil /\ state' = StDone heap v.
Proof.
  intros n heap v phi state' HSteps.
  inversion HSteps; subst.
  - repeat split; reflexivity.
  - exfalso. eapply done_no_step; eauto.
Qed.

Lemma fold_subst_eps_empty_static :
  forall rho,
    fold_subst_eps rho Empty_Static_Action = Empty_Static_Action.
Proof.
  intros rho.
  apply Extensionality_Ensembles.
  unfold Same_set, Included.
  split; intros sa HIn; unfold Ensembles.In in *.
  - destruct HIn as [sa0 [HIn _]].
    inversion HIn.
  - inversion HIn.
Qed.

Lemma Epsilon_Phi_Soundness_empty_phi_as_list :
  forall phi,
    Epsilon_Phi_Soundness (Empty_Static_Action, phi) ->
    phi_as_list phi = nil.
Proof.
  intros phi HSound.
  induction phi as [| da | phi1 IH1 phi2 IH2
                   | phi1 IH1 phi2 IH2]; simpl.
  - reflexivity.
  - exfalso.
    inversion HSound as [? ? HDA]; subst.
    destruct (HDA da) as (sa & HInSa & _).
    + constructor.
    + inversion HInSa.
  - assert (HSound1 : Epsilon_Phi_Soundness (Empty_Static_Action, phi1)).
    {
      inversion HSound as [? ? HDA]; subst.
      constructor.
      intros da HIn.
      apply HDA.
      apply DAP_Par.
      left. exact HIn.
    }
    assert (HSound2 : Epsilon_Phi_Soundness (Empty_Static_Action, phi2)).
    {
      inversion HSound as [? ? HDA]; subst.
      constructor.
      intros da HIn.
      apply HDA.
      apply DAP_Par.
      right. exact HIn.
    }
    pose proof (IH1 HSound1) as HNil1.
    pose proof (IH2 HSound2) as HNil2.
    rewrite HNil1, HNil2.
    reflexivity.
  - assert (HSound1 : Epsilon_Phi_Soundness (Empty_Static_Action, phi1)).
    {
      inversion HSound as [? ? HDA]; subst.
      constructor.
      intros da HIn.
      apply HDA.
      apply DAP_Seq.
      left. exact HIn.
    }
    assert (HSound2 : Epsilon_Phi_Soundness (Empty_Static_Action, phi2)).
    {
      inversion HSound as [? ? HDA]; subst.
      constructor.
      intros da HIn.
      apply HDA.
      apply DAP_Seq.
      right. exact HIn.
    }
    pose proof (IH1 HSound1) as HNil1.
    pose proof (IH2 HSound2) as HNil2.
    rewrite HNil1, HNil2.
    reflexivity.
Qed.

Lemma SmallStep_empty_static_terminal_sound :
  forall heap env rho e phi heap' v stty ctxt rgns ty,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty, Empty_Static_Action) ->
    StepsPhi (initial_state heap env rho e) phi (StDone heap' v) ->
    phi ⋞ Theta_Empty.
Proof.
  intros heap env rho e phi heap' v stty ctxt rgns ty
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps.
  apply Phi_Theta_Soundness_of_phi_as_list_nil.
  assert (HSound :
    Epsilon_Phi_Soundness
      (fold_subst_eps rho Empty_Static_Action,
       trace_as_phi (phi_as_list phi))).
  {
    eapply small_step_eff_sound with
      (heap' := heap') (v := v) (t := ty);
      eauto.
    eapply StepsPhi_as_steps; eauto.
  }
  rewrite fold_subst_eps_empty_static in HSound.
  apply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list in HSound.
  now apply Epsilon_Phi_Soundness_empty_phi_as_list.
Qed.

Lemma SmallStepN_empty_static_terminal_sound :
  forall n heap env rho e phi heap' v stty ctxt rgns ty,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty, Empty_Static_Action) ->
    StepsPhiN n (initial_state heap env rho e) phi (StDone heap' v) ->
    phi ⋞ Theta_Empty.
Proof.
  intros n heap env rho e phi heap' v stty ctxt rgns ty
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps.
  eapply SmallStep_empty_static_terminal_sound; eauto.
  eapply StepsPhiN_to_StepsPhi; eauto.
Qed.

Lemma StepsStayNonPairParRun_empty_summary :
  forall heap env rho,
    StepsStayNonPairParRun (initial_state heap env rho Empty).
Proof.
  unfold StepsStayNonPairParRun, initial_state.
  intros heap env rho trace state' HSteps.
  dependent destruction HSteps; simpl; auto.
  dependent destruction H; simpl.
  dependent destruction HSteps; simpl; auto.
  dependent destruction H; simpl.
  dependent destruction HSteps; simpl; auto.
  dependent destruction H.
Qed.

Lemma StepsStayNonPairParRun_top_summary :
  forall heap env rho,
    StepsStayNonPairParRun (initial_state heap env rho Top).
Proof.
  unfold StepsStayNonPairParRun, initial_state.
  intros heap env rho trace state' HSteps.
  dependent destruction HSteps; simpl; auto.
  dependent destruction H; simpl.
  dependent destruction HSteps; simpl; auto.
  dependent destruction H; simpl.
  dependent destruction HSteps; simpl; auto.
  dependent destruction H.
Qed.

Lemma StepsPhi_empty_summary_theta :
  forall heap env rho phi heap_summary theta,
    StepsPhi (initial_state heap env rho Empty) phi
      (StDone heap_summary (Eff theta)) ->
    theta = Theta_Empty.
Proof.
  intros heap env rho phi heap_summary theta HSteps.
  assert (HCanonical :
    StepsPhi (initial_state heap env rho Empty)
      (Phi_Seq Phi_Nil (Phi_Seq Phi_Nil Phi_Nil))
      (StDone heap (Eff Theta_Empty))).
  {
    unfold initial_state.
    change (Phi_Seq Phi_Nil (Phi_Seq Phi_Nil Phi_Nil))
      with (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil)).
    econstructor.
    - apply Step_Empty.
    - econstructor.
      + apply Step_Done.
      + constructor.
  }
  destruct
    (StepsPhi_effect_terminal_deterministic
	      (initial_state heap env rho Empty)
	      (Phi_Seq Phi_Nil (Phi_Seq Phi_Nil Phi_Nil))
	      heap Theta_Empty phi heap_summary theta
	      (StepsStayNonPairParRun_empty_summary heap env rho)
	      HCanonical HSteps)
    as (_ & _ & HTheta).
  symmetry.
  exact HTheta.
Qed.

Lemma StepsPhi_top_summary_theta :
  forall heap env rho phi heap_summary theta,
    StepsPhi (initial_state heap env rho Top) phi
      (StDone heap_summary (Eff theta)) ->
    theta = Theta_Top.
Proof.
  intros heap env rho phi heap_summary theta HSteps.
  assert (HCanonical :
    StepsPhi (initial_state heap env rho Top)
      (Phi_Seq Phi_Nil (Phi_Seq Phi_Nil Phi_Nil))
      (StDone heap (Eff Theta_Top))).
  {
    unfold initial_state.
    change (Phi_Seq Phi_Nil (Phi_Seq Phi_Nil Phi_Nil))
      with (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil)).
    econstructor.
    - apply Step_Top.
    - econstructor.
      + apply Step_Done.
      + constructor.
  }
  destruct
    (StepsPhi_effect_terminal_deterministic
	      (initial_state heap env rho Top)
	      (Phi_Seq Phi_Nil (Phi_Seq Phi_Nil Phi_Nil))
	      heap Theta_Top phi heap_summary theta
	      (StepsStayNonPairParRun_top_summary heap env rho)
	      HCanonical HSteps)
    as (_ & _ & HTheta).
  symmetry.
  exact HTheta.
Qed.

Lemma ScheduledStepsPhi_empty_summary_theta :
  forall heap env rho phi heap_summary theta,
    ScheduledStepsPhi (initial_state heap env rho Empty) phi
      (StDone heap_summary (Eff theta)) ->
    theta = Theta_Empty.
Proof.
  intros heap env rho phi heap_summary theta HSteps.
  assert (HCanonical :
    ScheduledStepsPhi (initial_state heap env rho Empty)
      (Phi_Seq Phi_Nil (Phi_Seq Phi_Nil Phi_Nil))
      (StDone heap (Eff Theta_Empty))).
  {
    unfold initial_state.
    change (Phi_Seq Phi_Nil (Phi_Seq Phi_Nil Phi_Nil))
      with (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil)).
    eapply ScheduledStepsPhi_Step; simpl.
    - exact I.
    - apply Step_Empty.
    - change (Phi_Seq Phi_Nil Phi_Nil)
        with (Phi_Seq (label_phi Silent) Phi_Nil).
      eapply ScheduledStepsPhi_Step; simpl.
      + exact I.
      + apply Step_Done.
      + constructor.
  }
  destruct
    (ScheduledStepsPhi_terminal_deterministic
      (initial_state heap env rho Empty)
      (Phi_Seq Phi_Nil (Phi_Seq Phi_Nil Phi_Nil))
      heap (Eff Theta_Empty) phi heap_summary (Eff theta)
      HCanonical HSteps)
    as (_HHeap & HVal).
  inversion HVal.
  reflexivity.
Qed.

Lemma ScheduledStepsPhi_top_summary_theta :
  forall heap env rho phi heap_summary theta,
    ScheduledStepsPhi (initial_state heap env rho Top) phi
      (StDone heap_summary (Eff theta)) ->
    theta = Theta_Top.
Proof.
  intros heap env rho phi heap_summary theta HSteps.
  assert (HCanonical :
    ScheduledStepsPhi (initial_state heap env rho Top)
      (Phi_Seq Phi_Nil (Phi_Seq Phi_Nil Phi_Nil))
      (StDone heap (Eff Theta_Top))).
  {
    unfold initial_state.
    change (Phi_Seq Phi_Nil (Phi_Seq Phi_Nil Phi_Nil))
      with (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil)).
    eapply ScheduledStepsPhi_Step; simpl.
    - exact I.
    - apply Step_Top.
    - change (Phi_Seq Phi_Nil Phi_Nil)
        with (Phi_Seq (label_phi Silent) Phi_Nil).
      eapply ScheduledStepsPhi_Step; simpl.
      + exact I.
      + apply Step_Done.
      + constructor.
  }
  destruct
    (ScheduledStepsPhi_terminal_deterministic
      (initial_state heap env rho Top)
      (Phi_Seq Phi_Nil (Phi_Seq Phi_Nil Phi_Nil))
      heap (Eff Theta_Top) phi heap_summary (Eff theta)
      HCanonical HSteps)
    as (_HHeap & HVal).
  inversion HVal.
  reflexivity.
Qed.

Lemma SmallStep_empty_static_terminal_scheduled_empty_sound :
  forall heap env rho e phi heap' v
    phi_summary heap_summary theta stty ctxt rgns ty,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty, Empty_Static_Action) ->
    StepsPhi (initial_state heap env rho e) phi (StDone heap' v) ->
    ScheduledStepsPhi (initial_state heap env rho Empty) phi_summary
      (StDone heap_summary (Eff theta)) ->
    phi ⋞ theta.
Proof.
  intros heap env rho e phi heap' v
    phi_summary heap_summary theta stty ctxt rgns ty
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp HSteps HSummary.
  pose proof
    (ScheduledStepsPhi_empty_summary_theta
      heap env rho phi_summary heap_summary theta HSummary)
    as HTheta.
  subst theta.
  eapply SmallStep_empty_static_terminal_sound; eauto.
Qed.

Lemma SmallStep_terminal_scheduled_top_sound :
  forall heap env rho e phi heap' v
    phi_summary heap_summary theta,
    StepsPhi (initial_state heap env rho e) phi (StDone heap' v) ->
    ScheduledStepsPhi (initial_state heap env rho Top) phi_summary
      (StDone heap_summary (Eff theta)) ->
    phi ⋞ theta.
Proof.
  intros heap env rho e phi heap' v
    phi_summary heap_summary theta _HSteps HSummary.
  pose proof
    (ScheduledStepsPhi_top_summary_theta
      heap env rho phi_summary heap_summary theta HSummary)
    as HTheta.
  subst theta.
  apply PhiInThetaTop.
Qed.

Lemma ScheduledStepsPhi_known_step_terminal_inv :
  forall state label state' phi heap_done v_done,
    NotPairParEvalState state ->
    Step state label state' ->
    ScheduledStepsPhi state phi (StDone heap_done v_done) ->
    exists phi_tail,
      ScheduledStepsPhi state' phi_tail (StDone heap_done v_done) /\
      phi_as_list phi = label_trace label ++ phi_as_list phi_tail.
Proof.
  intros state label state' phi heap_done v_done
    HNotPair HStep HSteps.
  inversion HSteps; subst.
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

Lemma ScheduledStepsPhi_nonpair_terminal_inv_step :
  forall state phi heap_done v_done,
    NotPairParEvalState state ->
    ~ Terminal state ->
    ScheduledStepsPhi state phi (StDone heap_done v_done) ->
    exists label state' phi_tail,
      Step state label state' /\
      ScheduledStepsPhi state' phi_tail (StDone heap_done v_done) /\
      phi_as_list phi = label_trace label ++ phi_as_list phi_tail.
Proof.
  intros state phi heap_done v_done HNotPair HNotTerminal HSteps.
  inversion HSteps; subst.
  - exfalso. apply HNotTerminal. constructor.
  - exists label, state', phi0.
    repeat split; eauto.
    simpl. now rewrite phi_as_list_label_phi.
  - simpl in HNotPair. contradiction.
Qed.

Lemma ScheduledStepsPhi_from_done_inv :
  forall heap v phi state',
    ScheduledStepsPhi (StDone heap v) phi state' ->
    phi = Phi_Nil /\ state' = StDone heap v.
Proof.
  intros heap v phi state' HSteps.
  inversion HSteps; subst.
  - split; reflexivity.
  - exfalso. eapply done_no_step; eauto.
Qed.

Lemma NotPairParEvalState_append_kont_inv :
  forall state tail,
    NotPairParEvalState (state_append_kont state tail) ->
    NotPairParEvalState state.
Proof.
  intros state tail HNotPair.
  destruct state as
    [heap env rho e k | heap v k | heap v | left right k].
  - simpl in *.
    destruct e; simpl in *; auto.
  - simpl in *; auto.
  - simpl in *; auto.
  - simpl in *; auto.
Qed.

Lemma ScheduledStepsPhi_pairpar_terminal_inv :
  forall heap env rho ef1 ea1 ef2 ea2 k phi heap_done v_done,
    ScheduledStepsPhi
      (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
      phi
      (StDone heap_done v_done) ->
    exists phi_eff1 phi_eff2 phi_mu
      heap_eff1 heap_eff2 theta1 theta2,
      phi = pairpar_checked_packed_structured_trace
        phi_eff1 phi_eff2 phi_mu /\
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      PairParCheckPass theta1 theta2 /\
      PairParCheckedPackedStepsPhi theta1 theta2
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
        phi_mu
        (PPS_State (StDone heap_done v_done)).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k phi heap_done v_done
    HSteps.
  inversion HSteps; subst; simpl in *; try contradiction; try discriminate.
  exists phi_eff1, phi_eff2, phi_mu.
  exists heap_eff1, heap_eff2, theta1, theta2.
  split; [reflexivity |].
  split; [eassumption |].
  split.
  - match goal with
    | HObserved : PairParObservedCheckPass _ _ _ _ |- _ =>
        destruct HObserved as [HPass _];
        exact HPass
    end.
  - eassumption.
Qed.

Lemma ScheduledStepsPhi_pairpar_terminal_observed_inv :
  forall heap env rho ef1 ea1 ef2 ea2 k phi heap_done v_done,
    ScheduledStepsPhi
      (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
      phi
      (StDone heap_done v_done) ->
    exists phi_eff1 phi_eff2 phi_mu
      heap_eff1 heap_eff2 theta1 theta2,
      phi = pairpar_checked_packed_structured_trace
        phi_eff1 phi_eff2 phi_mu /\
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 /\
      PairParCheckedPackedStepsPhi theta1 theta2
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
        phi_mu
        (PPS_State (StDone heap_done v_done)).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k phi heap_done v_done
    HSteps.
  inversion HSteps; subst; simpl in *; try contradiction; try discriminate.
  exists phi_eff1, phi_eff2, phi_mu.
  exists heap_eff1, heap_eff2, theta1, theta2.
  split; [reflexivity |].
  split; [eassumption |].
  split; eassumption.
Qed.

Lemma StepsPhiN_append_kont_terminal_decompose :
  forall n app phi heap_final v_final,
    StepsPhiN n app phi (StDone heap_final v_final) ->
    forall state tail,
      app = state_append_kont state tail ->
      ~ Terminal state ->
      exists n_state n_tail heap_mid v_mid phi_state phi_tail,
        n_state <= n /\
        n_tail <= n /\
        StepsPhiN n_state state phi_state (StDone heap_mid v_mid) /\
        StepsPhiN n_tail (StReturn heap_mid v_mid tail) phi_tail
          (StDone heap_final v_final) /\
        phi_as_list phi =
          phi_as_list phi_state ++ phi_as_list phi_tail.
Proof.
  intros n app phi heap_final v_final HSteps.
  remember (StDone heap_final v_final) as final_state eqn:HFinal.
  revert heap_final v_final HFinal.
  induction HSteps as
    [app | n app label app' phi_tail app'' HStep HStepsTail IH];
    intros heap_final v_final HFinal state tail HApp HNotTerminal.
  - subst app.
    destruct state as
      [heap env rho e k | heap v k | heap v | left_state right_state k].
    + simpl in HApp. inversion HApp.
    + simpl in HApp. inversion HApp.
    + exfalso. apply HNotTerminal. constructor.
    + simpl in HApp. inversion HApp.
  - subst app.
    destruct
      (Step_append_kont_inv state tail label app' HNotTerminal HStep)
      as [(state0 & HStepState & HApp' & HNotTerminal0) |
          (heap_mid & v_mid & HState & HStepTail)].
    + subst app'.
      destruct (IH heap_final v_final HFinal state0 tail eq_refl HNotTerminal0)
        as (n_state0 & n_tail0 & heap_mid & v_mid &
            phi_state_tail & phi_tail_final &
            HLeState0 & HLeTail0 & HStateTail & HTailFinal & HTraceTail).
      exists (S n_state0), n_tail0, heap_mid, v_mid,
        (Phi_Seq (label_phi label) phi_state_tail), phi_tail_final.
      split; [lia |].
      split; [lia |].
      split.
      * eapply StepsPhiN_Step; eauto.
      * split; [exact HTailFinal |].
        simpl. rewrite HTraceTail.
        rewrite app_assoc. reflexivity.
    + subst state.
      exists 1, (S n), heap_mid, v_mid,
        (Phi_Seq (label_phi Silent) Phi_Nil),
        (Phi_Seq (label_phi label) phi_tail).
      split; [lia |].
      split; [lia |].
      split.
      * eapply StepsPhiN_Step.
        -- constructor.
        -- constructor.
      * split.
        -- eapply StepsPhiN_Step.
           ++ exact HStepTail.
           ++ exact HStepsTail.
        -- simpl. reflexivity.
Qed.

Lemma StepsPhiN_initial_with_kont_terminal_decompose :
  forall n heap env rho e tail phi heap_final v_final,
    StepsPhiN n (StEval heap env rho e tail) phi
      (StDone heap_final v_final) ->
    exists n_expr n_tail heap_mid v_mid phi_expr phi_tail,
      n_expr <= n /\
      n_tail <= n /\
      StepsPhiN n_expr (initial_state heap env rho e) phi_expr
        (StDone heap_mid v_mid) /\
      StepsPhiN n_tail (StReturn heap_mid v_mid tail) phi_tail
        (StDone heap_final v_final) /\
      phi_as_list phi =
        phi_as_list phi_expr ++ phi_as_list phi_tail.
Proof.
  intros n heap env rho e tail phi heap_final v_final HSteps.
  eapply (StepsPhiN_append_kont_terminal_decompose
    n (StEval heap env rho e tail) phi heap_final v_final HSteps
    (StEval heap env rho e KDone) tail).
  - reflexivity.
  - intros HTerminal. inversion HTerminal.
Qed.

Theorem ConcatTerminalDecompose :
  forall heap env rho e1 e2 phi heap_final theta,
    StepsPhi
      (initial_state heap env rho (Concat e1 e2))
      phi
      (StDone heap_final (Eff theta)) ->
    exists phi1 phi2 heap1 theta1 heap2 theta2,
      StepsPhi
        (initial_state heap env rho e1)
        phi1
        (StDone heap1 (Eff theta1)) /\
      StepsPhi
        (initial_state heap1 env rho e2)
        phi2
        (StDone heap2 (Eff theta2)) /\
      heap_final = heap2 /\
      theta = Union_Theta theta1 theta2 /\
      phi_as_list phi =
        phi_as_list phi1 ++ phi_as_list phi2.
Proof.
  intros heap env rho e1 e2 phi heap_final theta HSteps.
  pose proof
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Concat e1 e2))
      Silent
      (StEval heap env rho e1 (KConcatL e2 env rho KDone))
      phi heap_final (Eff theta))
    as HFirst.
	  specialize
	    (HFirst I (Step_Concat_EvalLeft heap env rho KDone e1 e2)
	      HSteps).
  destruct HFirst as (phi_after_e1 & HAfterE1 & HTraceStart).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho e1 (KConcatL e2 env rho KDone)
      phi_after_e1 heap_final (Eff theta) HAfterE1)
    as (heap1 & v1 & phi1 & phi_after_k1 &
        HE1 & HAfterK1 & HTraceE1).
  destruct
    (StepsPhi_nonterminal_terminal_inv_step
      (StReturn heap1 v1 (KConcatL e2 env rho KDone))
      phi_after_k1 heap_final (Eff theta))
    as (label_k1 & state_k1 & phi_after_e2 &
        HStepK1 & HAfterE2 & HTraceK1).
  - intros HTerminal. inversion HTerminal.
  - exact HAfterK1.
  - inversion HStepK1; subst.
    destruct
      (StepsPhi_initial_with_kont_terminal_decompose
        heap1 env rho e2 (KConcatR theta0 KDone)
        phi_after_e2 heap_final (Eff theta) HAfterE2)
      as (heap2 & v2 & phi2 & phi_after_k2 &
          HE2 & HAfterK2 & HTraceE2).
    destruct
      (StepsPhi_nonterminal_terminal_inv_step
        (StReturn heap2 v2 (KConcatR theta0 KDone))
        phi_after_k2 heap_final (Eff theta))
      as (label_k2 & state_k2 & phi_after_done &
          HStepK2 & HAfterDoneStep & HTraceK2).
    + intros HTerminal. inversion HTerminal.
    + exact HAfterK2.
    + destruct v2 as [w2 l2 | n2 | b2 | cl2 | theta2 | | p2];
        inversion HStepK2; subst.
      destruct
        (StepsPhi_nonterminal_terminal_inv_step
          (StReturn heap2 (Eff (Union_Theta theta0 theta2)) KDone)
          phi_after_done heap_final (Eff theta))
        as (label_done & state_done & phi_after_done_tail &
            HStepDone & HAfterDone & HTraceDone).
      * intros HTerminal. inversion HTerminal.
      * exact HAfterDoneStep.
      * inversion HStepDone; subst.
        destruct (StepsPhi_from_done_inv _ _ _ _ HAfterDone)
          as (HPhiDone & HFinal).
        inversion HFinal; subst.
        exists phi1, phi2, heap1, theta0, heap2, theta2.
        split; [exact HE1 |].
        split; [exact HE2 |].
        split; [reflexivity |].
        split; [reflexivity |].
        rewrite HTraceStart, HTraceE1, HTraceK1, HTraceE2,
          HTraceK2, HTraceDone.
        simpl.
        repeat rewrite app_nil_l.
        repeat rewrite app_nil_r.
        repeat rewrite app_assoc.
        reflexivity.
Qed.

Theorem PairParSourceTerminalCheckedRunDecompose :
  forall heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final,
    StepsPhi
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi
      (StDone heap_final v_final) ->
    exists phi_eff1 phi_eff2 phi_seq
      heap_eff1 theta1 heap_eff2 theta2,
      PairParSourceOrderedEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      PairParCheckPass theta1 theta2 /\
      StepsPhi
        (pairpar_checked_run_start heap_eff2 env rho ef1 ea1 ef2 ea2 KDone)
        phi_seq
        (StDone heap_final v_final) /\
      phi_as_list phi =
        phi_as_list phi_eff1 ++
        phi_as_list phi_eff2 ++
        phi_as_list phi_seq.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps.
  eapply PairParTerminalCheckedRunDecompose; eauto.
Qed.

Theorem PairParSourceTerminalCheckedFlatRunDecompose :
  forall heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final,
    StepsPhi
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi
      (StDone heap_final v_final) ->
    exists phi_eff1 phi_eff2 phi_seq
      heap_eff1 theta1 heap_eff2 theta2,
      PairParSourceOrderedEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      PairParCheckPass theta1 theta2 /\
      PairParFlatStepsPhi
        (pairpar_checked_start heap_eff2 env rho ef1 ea1 ef2 ea2 KDone)
        phi_seq
        (PPS_State (StDone heap_final v_final)) /\
      phi_as_list phi =
        phi_as_list phi_eff1 ++
        phi_as_list phi_eff2 ++
        phi_as_list phi_seq.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps.
  eapply PairParTerminalCheckedFlatRunDecompose; eauto.
Qed.

Theorem PairParSourceTerminalCheckedLooseRunDecompose :
  forall heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final,
    StepsPhi
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi
      (StDone heap_final v_final) ->
    exists phi_eff1 phi_eff2 phi_seq phi_mu_state phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2,
      PairParSourceOrderedEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      PairParCheckPass theta1 theta2 /\
      PairParLoosePackedStepsPhi
        (pairpar_checked_start heap_eff2 env rho ef1 ea1 ef2 ea2 KDone)
        phi_seq
        phi_mu_state
        phi_mu1
        phi_mu2
        (PPS_State (StDone heap_final v_final)) /\
      phi_as_list phi =
        phi_as_list phi_eff1 ++
        phi_as_list phi_eff2 ++
        phi_as_list phi_seq.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps.
  eapply PairParTerminalCheckedLooseRunDecompose; eauto.
Qed.

Lemma TcExp_mu_app_backtriangle :
  forall ctxt rgns rho ef ea ty static,
    TcExp (ctxt, rgns, Mu_App ef ea, ty, static) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea).
Proof.
  intros ctxt rgns rho ef ea ty static HTc.
  inversion HTc; subst; eauto.
Qed.

Lemma TcExp_pair_par_branch_backtriangles :
  forall ctxt rgns rho ef1 ea1 ef2 ea2 ty static,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    BackTriangle
      (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) /\
    BackTriangle
      (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2).
Proof.
  intros ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc.
  inversion HTc; subst.
  split; eapply TcExp_mu_app_backtriangle; eauto.
Qed.
