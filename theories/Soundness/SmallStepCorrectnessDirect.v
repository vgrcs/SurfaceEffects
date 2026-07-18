From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Wf_nat.

Require Export theories.Runtime.SmallStepPaperTheorems.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepSequentialSoundness.
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
Require Import theories.Soundness.SmallStepBackTriangle.

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
    Step state label state' ->
    StepsPhiN n state phi (StDone heap_done v_done) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      StepsPhiN n_tail state' phi_tail (StDone heap_done v_done) /\
      phi_as_list phi = label_trace label ++ phi_as_list phi_tail.
Proof.
  intros n state label state' phi heap_done v_done HStep HSteps.
  inversion HSteps; subst.
  - exfalso. eapply done_no_step; eauto.
  - destruct (step_deterministic _ _ _ _ _ HStep H)
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
      HCanonical HSteps)
    as (_ & _ & HTheta).
  symmetry.
  exact HTheta.
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
    destruct state as [heap env rho e k | heap v k | heap v].
    + simpl in HApp. inversion HApp.
    + simpl in HApp. inversion HApp.
    + exfalso. apply HNotTerminal. constructor.
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
    (HFirst (Step_Concat_EvalLeft heap env rho KDone e1 e2)
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

Theorem PairParSourceTerminalSequentialDecompose :
  forall heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final,
    StepsPhi
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi
      (StDone heap_final v_final) ->
    exists phi_eff1 phi_eff2 phi_seq
      heap_eff1 theta1 heap_eff2 theta2,
      PairParSequentialEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      PairParCheckPass theta1 theta2 /\
      StepsPhi
        (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 KDone)
        phi_seq
        (StDone heap_final v_final) /\
      phi_as_list phi =
        phi_as_list phi_eff1 ++
        phi_as_list phi_eff2 ++
        phi_as_list phi_seq.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps.
  pose proof
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      Silent
      (StEval heap env rho (Eff_App ef1 ea1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))
      phi heap_final v_final)
    as HFirst.
  specialize
    (HFirst (Step_PairPar_EvalEff1 heap env rho KDone ef1 ea1 ef2 ea2)
      HSteps).
  destruct HFirst as (phi_after_eff1 & HAfterEff1 & HTraceStart).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho (Eff_App ef1 ea1)
      (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone)
      phi_after_eff1 heap_final v_final HAfterEff1)
    as (heap_eff1 & v_eff1 & phi_eff1 & phi_after_k1 &
        HEff1 & HAfterK1 & HTraceEff1).
  destruct
    (StepsPhi_nonterminal_terminal_inv_step
      (StReturn heap_eff1 v_eff1
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))
      phi_after_k1 heap_final v_final)
    as (label_k1 & state_k1 & phi_after_eff2 &
        HStepK1 & HAfterEff2 & HTraceK1).
  - intros HTerminal. inversion HTerminal.
  - exact HAfterK1.
  - inversion HStepK1; subst.
    destruct
      (StepsPhi_initial_with_kont_terminal_decompose
        heap_eff1 env rho (Eff_App ef2 ea2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone)
        phi_after_eff2 heap_final v_final HAfterEff2)
      as (heap_eff2 & v_eff2 & phi_eff2 & phi_after_check &
          HEff2 & HAfterCheck & HTraceEff2).
    destruct
      (StepsPhi_nonterminal_terminal_inv_step
        (StReturn heap_eff2 v_eff2
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone))
        phi_after_check heap_final v_final)
      as (label_check & state_check & phi_seq &
          HStepCheck & HSeq & HTraceCheck).
    + intros HTerminal. inversion HTerminal.
    + exact HAfterCheck.
    + inversion HStepCheck; subst.
      exists phi_eff1, phi_eff2, phi_seq,
        heap_eff1, theta1, heap_eff2, theta2.
      split.
      * constructor; eauto.
      * split.
        -- split; assumption.
        -- split.
           ++ exact HSeq.
           ++ rewrite HTraceStart, HTraceEff1, HTraceK1,
                HTraceEff2, HTraceCheck.
              simpl.
              repeat rewrite app_nil_l.
              repeat rewrite app_nil_r.
              rewrite app_assoc.
              reflexivity.
Qed.

Theorem PairParSequentialPhaseTerminalDecompose :
  forall heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final,
    StepsPhi
      (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi
      (StDone heap_final v_final) ->
    exists phi_mu1 phi_mu2 heap_mu1 heap_mu2 v_mu1 v_mu2,
      StepsPhi
        (initial_state heap env rho (Mu_App ef1 ea1))
        phi_mu1
        (StDone heap_mu1 v_mu1) /\
      StepsPhi
        (initial_state heap_mu1 env rho (Mu_App ef2 ea2))
        phi_mu2
        (StDone heap_mu2 v_mu2) /\
      heap_final = heap_mu2 /\
      v_final = Pair (v_mu1, v_mu2) /\
      phi_as_list phi =
        phi_as_list phi_mu1 ++ phi_as_list phi_mu2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps.
  unfold pairpar_sequential_start in HSteps.
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho (Mu_App ef1 ea1)
      (KPairParMu1 ef2 ea2 env rho KDone)
      phi heap_final v_final HSteps)
    as (heap_mu1 & v_mu1 & phi_mu1 & phi_after_mu1 &
        HMu1 & HAfterMu1 & HTraceMu1).
  destruct
    (StepsPhi_nonterminal_terminal_inv_step
      (StReturn heap_mu1 v_mu1
        (KPairParMu1 ef2 ea2 env rho KDone))
      phi_after_mu1 heap_final v_final)
    as (label_mu1 & state_mu2 & phi_after_mu2 &
        HStepMu1 & HAfterMu2 & HTraceStepMu1).
  - intros HTerminal. inversion HTerminal.
  - exact HAfterMu1.
  - inversion HStepMu1; subst.
    destruct
      (StepsPhi_initial_with_kont_terminal_decompose
        heap_mu1 env rho (Mu_App ef2 ea2)
        (KPairParMu2 v_mu1 KDone)
        phi_after_mu2 heap_final v_final HAfterMu2)
      as (heap_mu2 & v_mu2 & phi_mu2 & phi_after_pair &
          HMu2 & HAfterPair & HTraceMu2).
    destruct
      (StepsPhi_nonterminal_terminal_inv_step
        (StReturn heap_mu2 v_mu2 (KPairParMu2 v_mu1 KDone))
        phi_after_pair heap_final v_final)
      as (label_pair & state_pair & phi_after_return &
          HStepPair & HAfterReturn & HTracePair).
    + intros HTerminal. inversion HTerminal.
    + exact HAfterPair.
    + inversion HStepPair; subst.
      destruct
        (StepsPhi_nonterminal_terminal_inv_step
          (StReturn heap_mu2 (Pair (v_mu1, v_mu2)) KDone)
          phi_after_return heap_final v_final)
        as (label_done & state_done & phi_after_done &
            HStepDone & HAfterDone & HTraceDone).
      * intros HTerminal. inversion HTerminal.
      * exact HAfterReturn.
      * inversion HStepDone; subst.
        destruct (StepsPhi_from_done_inv _ _ _ _ HAfterDone)
          as (HPhiDone & HFinal).
        inversion HFinal; subst.
        exists phi_mu1, phi_mu2, heap_mu1, heap_mu2, v_mu1, v_mu2.
        split; [exact HMu1 |].
        split; [exact HMu2 |].
        split; [reflexivity |].
        split; [reflexivity |].
        rewrite HTraceMu1, HTraceStepMu1, HTraceMu2,
          HTracePair, HTraceDone.
        simpl.
        repeat rewrite app_nil_l.
        repeat rewrite app_nil_r.
        reflexivity.
Qed.

Theorem PairParSourceTerminalFullSequentialDecompose :
  forall heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final,
    StepsPhi
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi
      (StDone heap_final v_final) ->
    exists phi_eff1 phi_eff2 phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2
      heap_mu1 heap_mu2 v_mu1 v_mu2,
      PairParSequentialEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      PairParCheckPass theta1 theta2 /\
      StepsPhi
        (initial_state heap_eff2 env rho (Mu_App ef1 ea1))
        phi_mu1
        (StDone heap_mu1 v_mu1) /\
      StepsPhi
        (initial_state heap_mu1 env rho (Mu_App ef2 ea2))
        phi_mu2
        (StDone heap_mu2 v_mu2) /\
      heap_final = heap_mu2 /\
      v_final = Pair (v_mu1, v_mu2) /\
      phi_as_list phi =
        phi_as_list phi_eff1 ++
        phi_as_list phi_eff2 ++
        phi_as_list phi_mu1 ++
        phi_as_list phi_mu2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps.
  destruct
    (PairParSourceTerminalSequentialDecompose
      heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps)
    as (phi_eff1 & phi_eff2 & phi_seq &
        heap_eff1 & theta1 & heap_eff2 & theta2 &
        HSummary & HPass & HSeq & HTraceSource).
  destruct
    (PairParSequentialPhaseTerminalDecompose
      heap_eff2 env rho ef1 ea1 ef2 ea2 phi_seq heap_final v_final HSeq)
    as (phi_mu1 & phi_mu2 & heap_mu1 & heap_mu2 & v_mu1 & v_mu2 &
        HMu1 & HMu2 & HHeapFinal & HValFinal & HTraceSeq).
  exists phi_eff1, phi_eff2, phi_mu1, phi_mu2,
    heap_eff1, theta1, heap_eff2, theta2,
    heap_mu1, heap_mu2, v_mu1, v_mu2.
  split; [exact HSummary |].
  split; [exact HPass |].
  split; [exact HMu1 |].
  split; [exact HMu2 |].
  split; [exact HHeapFinal |].
  split; [exact HValFinal |].
  rewrite HTraceSource, HTraceSeq.
  repeat rewrite app_assoc.
  reflexivity.
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
    (HFirst (Step_MuApp_EvalFun heap env rho KDone ef ea) HSteps).
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
    (HFirst (Step_EffApp_EvalFun heap env rho KDone ef ea) HSteps).
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
      phi heap_final v_final HFirst HApp)
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
      phi heap_final v_final HFirst HApp)
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
    phi_mu heap_mu v_mu phi_eff heap_eff theta HMu HEff.
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
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HMu HEff.
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
      phi_mu heap_mu v_mu phi_eff heap_eff theta HMu HEff)
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
       phi_mu ⋞ theta_with_phi_prefixes phi_fun_mu phi_arg_mu theta).
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HMu HEff.
  destruct
    (MuEffAppAlignedPrefixes_readonly_heap_neutral
      heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HMu HEff)
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
  intros HBodySound.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with
      (phi2 := Phi_Seq phi_fun_mu (Phi_Seq phi_arg_mu phi_body_mu)).
  - simpl. exact HTraceMu.
  - apply PTS_Seq.
    + apply theta_with_phi_prefixes_left_sound.
    + apply PTS_Seq.
      * apply theta_with_phi_prefixes_middle_sound.
      * apply theta_with_phi_prefixes_right_sound.
	        exact HBodySound.
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
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HMu HEff.
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
      phi_mu ⋞ theta_with_phi_prefixes phi_fun_mu phi_arg_mu theta.
Proof.
  intros n heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HBelow.
  destruct
    (MuEffAppAlignedPrefixes_readonly_heap_neutral_counted
      n heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HMu HEff)
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
  - eapply Phi_Theta_Soundness_of_phi_as_list_eq
      with
        (phi2 := Phi_Seq phi_fun_mu (Phi_Seq phi_arg_mu phi_body_mu)).
    + simpl. exact HTraceMu.
    + apply PTS_Seq.
      * apply theta_with_phi_prefixes_left_sound.
      * apply PTS_Seq.
        -- apply theta_with_phi_prefixes_middle_sound.
        -- apply theta_with_phi_prefixes_right_sound.
           exact HBodySound.
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
    SmallStepCorrectnessBelow n ->
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
      phi_mu ⋞ theta_with_phi_prefixes phi_fun_mu phi_arg_mu theta.
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HBodyReasoning.
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_from_body_soundness
      heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HMu HEff)
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

Theorem MuAppEffAppTerminalSound_with_readonly_prefixes_actual_body :
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
      phi_mu ⋞
        theta_with_phi_prefixes
          phi_fun_mu phi_arg_mu (theta_of_phi phi_body_mu).
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HMu HEff.
  destruct
    (MuEffAppAlignedPrefixes_readonly_heap_neutral
      heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HMu HEff)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        phi_fun_eff & phi_arg_eff & phi_body_eff &
        env_closure & rho_closure & f & x & ec & ee & v_arg &
        HFunMu & HFunEff & HArgMu & HArgEff &
        HBodyMu & HBodyEff & HTraceMu & _HTraceEff &
        _HFunTrace & _HArgTrace & _HFunRO & _HArgRO).
  exists phi_fun_mu, phi_arg_mu, phi_body_mu.
  exists phi_fun_eff, phi_arg_eff, phi_body_eff.
  exists env_closure, rho_closure, f, x, ec, ee, v_arg.
  repeat split; try assumption.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with
      (phi2 := Phi_Seq phi_fun_mu (Phi_Seq phi_arg_mu phi_body_mu)).
  - simpl. exact HTraceMu.
  - apply PTS_Seq.
    + apply theta_with_phi_prefixes_left_sound.
    + apply PTS_Seq.
      * apply theta_with_phi_prefixes_middle_sound.
      * apply theta_with_phi_prefixes_right_sound.
        apply theta_of_phi_sound.
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
    phi_mu heap_mu v_mu phi_eff heap_eff theta HMu HEff.
  destruct
    (MuEffAppTerminalAlignedBodyDecompose
      heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta HMu HEff)
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

Theorem PairParBackTriangleEffectSummaries_readonly_heap_neutral :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyPhi phi_eff1 /\
    ReadOnlyPhi phi_eff2 /\
    heap_eff1 = heap /\
    heap_eff2 = heap.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HSummary.
  inversion HBack; subst; try discriminate.
  match goal with
  | HLeft : TcExp (ctxt, rgns, Eff_App ef1 ea1, _, _),
    HRight : TcExp (ctxt, rgns, Eff_App ef2 ea2, _, _) |- _ =>
      inversion HLeft; subst; inversion HRight; subst
  end.
  match goal with
  | HTcEff1 : TcExp
      (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, ?static_eff1),
    HTcEff2 : TcExp
      (ctxt, rgns, Eff_App ef2 ea2, Ty_Effect, ?static_eff2),
    HReadOnly1 : ReadOnlyStatic (fold_subst_eps rho ?static_eff1),
    HReadOnly2 : ReadOnlyStatic (fold_subst_eps rho ?static_eff2) |- _ =>
      destruct
        (PairParEffectSummaryStepsPhi_readonly_from_small_step_sound
          heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
          phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
          static_eff1 static_eff2
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcEff1 HTcEff2 HSummary HReadOnly1 HReadOnly2)
        as [HReadOnlyPhi1 HReadOnlyPhi2];
      destruct
        (PairParEffectSummaryStepsPhi_readonly_heap_neutral_from_small_step_sound
          heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
          phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
          static_eff1 static_eff2
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcEff1 HTcEff2 HSummary HReadOnly1 HReadOnly2)
        as [HHeapEff1 HHeapEff2];
      repeat split; assumption
  end.
Qed.

Theorem PairParSourceTerminalSound_reduces_to_branch_soundness :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    phi heap_final v_final,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    StepsPhi
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi
      (StDone heap_final v_final) ->
    exists phi_eff1 phi_eff2 phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2
      heap_mu1 heap_mu2 v_mu1 v_mu2,
      PairParSequentialEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      PairParCheckPass theta1 theta2 /\
      StepsPhi
        (initial_state heap_eff2 env rho (Mu_App ef1 ea1))
        phi_mu1
        (StDone heap_mu1 v_mu1) /\
      StepsPhi
        (initial_state heap_mu1 env rho (Mu_App ef2 ea2))
        phi_mu2
        (StDone heap_mu2 v_mu2) /\
      heap_final = heap_mu2 /\
      v_final = Pair (v_mu1, v_mu2) /\
      (phi_mu1 ⋞ theta1 ->
       phi_mu2 ⋞ theta2 ->
       phi ⋞ theta_with_phi_prefixes
         phi_eff1 phi_eff2 (Union_Theta theta1 theta2)).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    phi heap_final v_final _ HSteps.
  destruct
    (PairParSourceTerminalFullSequentialDecompose
      heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps)
    as (phi_eff1 & phi_eff2 & phi_mu1 & phi_mu2 &
        heap_eff1 & theta1 & heap_eff2 & theta2 &
        heap_mu1 & heap_mu2 & v_mu1 & v_mu2 &
        HSummary & HPass & HMu1 & HMu2 & HHeapFinal &
        HValFinal & HTrace).
  exists phi_eff1, phi_eff2, phi_mu1, phi_mu2,
    heap_eff1, theta1, heap_eff2, theta2,
    heap_mu1, heap_mu2, v_mu1, v_mu2.
  split; [exact HSummary |].
  split; [exact HPass |].
  split; [exact HMu1 |].
  split; [exact HMu2 |].
  split; [exact HHeapFinal |].
  split; [exact HValFinal |].
  intros HSoundMu1 HSoundMu2.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with
      (phi2 :=
        Phi_Seq phi_eff1
          (Phi_Seq phi_eff2 (Phi_Seq phi_mu1 phi_mu2))).
  - simpl. exact HTrace.
  - apply PTS_Seq.
    + apply theta_with_phi_prefixes_left_sound.
    + apply PTS_Seq.
      * apply theta_with_phi_prefixes_middle_sound.
      * apply PTS_Seq.
        -- apply theta_with_phi_prefixes_right_sound.
           apply Theta_introl. exact HSoundMu1.
        -- apply theta_with_phi_prefixes_right_sound.
           apply Theta_intror. exact HSoundMu2.
Qed.

Theorem PairParCheckedParallelTopSound_reduces_to_same_heap_branch_soundness :
  forall heap env rho ef1 ea1 ef2 ea2
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v,
    phi =
      pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2 ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    phi_mu1 ⋞ theta1 ->
    phi_mu2 ⋞ theta2 ->
    phi ⋞ theta_with_phi_prefixes
      phi_eff1 phi_eff2 (Union_Theta theta1 theta2).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    HTrace HSummary HPass HSteps HSoundMu1 HSoundMu2.
  eapply PairParCheckedStructuredStepsPhi_top_sound; eauto.
Qed.

Theorem PairParCheckedParallelTopSound_reduces_to_augmented_branch_soundness :
  forall heap env rho ef1 ea1 ef2 ea2
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    branch_theta1 branch_theta2 heap' v,
    phi =
      pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2 ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    phi_mu1 ⋞ branch_theta1 ->
    phi_mu2 ⋞ branch_theta2 ->
    phi ⋞ theta_with_phi_prefixes
      phi_eff1 phi_eff2 (Union_Theta branch_theta1 branch_theta2).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    branch_theta1 branch_theta2 heap' v
    HTrace _ _ HSteps HSoundMu1 HSoundMu2.
  subst.
  unfold pairpar_checked_structured_trace.
  apply PTS_Seq.
  - apply PTS_Par.
    + apply theta_with_phi_prefixes_left_sound.
    + apply theta_with_phi_prefixes_middle_sound.
  - apply PTS_Seq.
    + apply theta_with_phi_prefixes_right_sound.
      apply PTS_Par.
      * apply Theta_introl. exact HSoundMu1.
      * apply Theta_intror. exact HSoundMu2.
    + apply Phi_Theta_Soundness_of_phi_as_list_nil.
	      eapply PairParStepsPhi_top_terminal_state_trace_nil; eauto.
Qed.

Theorem PairParCheckedParallelTopSound_actual_runtime_branches :
  forall heap env rho ef1 ea1 ef2 ea2
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v,
    phi =
      pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2 ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    phi ⋞ theta_with_phi_prefixes
      phi_eff1 phi_eff2
      (Union_Theta (theta_of_phi phi_mu1) (theta_of_phi phi_mu2)).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    HTrace HSummary HPass HSteps.
  eapply
    (PairParCheckedParallelTopSound_reduces_to_augmented_branch_soundness
      heap env rho ef1 ea1 ef2 ea2
      phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2
      (theta_of_phi phi_mu1)
      (theta_of_phi phi_mu2)
      heap' v);
    eauto using theta_of_phi_sound.
Qed.

Theorem PairParCheckedParallelCanonicalTopSound_reduces_to_branch_soundness :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    stty ctxt rgns
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    phi =
      pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2 ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    phi_mu1 ⋞ theta1 ->
    phi_mu2 ⋞ theta2 ->
    ReadOnlyPhi phi_eff1 /\
    ReadOnlyPhi phi_eff2 /\
    heap_eff1 = heap /\
    heap_eff2 = heap /\
    phi ⋞ theta_with_phi_prefixes
      phi_eff1 phi_eff2 (Union_Theta theta1 theta2).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    stty ctxt rgns
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTrace HSummary HPass HSteps HSoundMu1 HSoundMu2.
  destruct
    (PairParBackTriangleEffectSummaries_readonly_heap_neutral
      heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
      stty ctxt rgns
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HSummary)
    as (HReadOnlyEff1 & HReadOnlyEff2 & HHeapEff1 & HHeapEff2).
  repeat split; try assumption.
  eapply PairParCheckedParallelTopSound_reduces_to_same_heap_branch_soundness;
    eauto.
Qed.

Theorem PairParSourceTerminalSound_from_branch_runs :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    phi heap_final v_final,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    StepsPhi
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi
      (StDone heap_final v_final) ->
    (forall heap_start phi_mu1 heap_mu1 v_mu1 theta1,
      BackTriangle
        (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) ->
      StepsPhi
        (initial_state heap_start env rho (Mu_App ef1 ea1))
        phi_mu1
        (StDone heap_mu1 v_mu1) ->
      phi_mu1 ⋞ theta1) ->
    (forall heap_start phi_mu2 heap_mu2 v_mu2 theta2,
      BackTriangle
        (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) ->
      StepsPhi
        (initial_state heap_start env rho (Mu_App ef2 ea2))
        phi_mu2
        (StDone heap_mu2 v_mu2) ->
      phi_mu2 ⋞ theta2) ->
    exists phi_eff1 phi_eff2 phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2
      heap_mu1 heap_mu2 v_mu1 v_mu2,
      PairParSequentialEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      PairParCheckPass theta1 theta2 /\
      StepsPhi
        (initial_state heap_eff2 env rho (Mu_App ef1 ea1))
        phi_mu1
        (StDone heap_mu1 v_mu1) /\
      StepsPhi
        (initial_state heap_mu1 env rho (Mu_App ef2 ea2))
        phi_mu2
        (StDone heap_mu2 v_mu2) /\
      heap_final = heap_mu2 /\
      v_final = Pair (v_mu1, v_mu2) /\
      phi ⋞ theta_with_phi_prefixes
        phi_eff1 phi_eff2 (Union_Theta theta1 theta2).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    phi heap_final v_final HTc HSteps HSoundLeft HSoundRight.
  destruct
    (PairParSourceTerminalFullSequentialDecompose
      heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps)
    as (phi_eff1 & phi_eff2 & phi_mu1 & phi_mu2 &
        heap_eff1 & theta1 & heap_eff2 & theta2 &
        heap_mu1 & heap_mu2 & v_mu1 & v_mu2 &
        HSummary & HPass & HMu1 & HMu2 & HHeapFinal &
        HValFinal & HTrace).
  destruct
    (TcExp_pair_par_branch_backtriangles
      ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc)
    as (HBackLeft & HBackRight).
  pose proof
    (HSoundLeft heap_eff2 phi_mu1 heap_mu1 v_mu1 theta1
      HBackLeft HMu1)
    as HSoundMu1.
  pose proof
    (HSoundRight heap_mu1 phi_mu2 heap_mu2 v_mu2 theta2
      HBackRight HMu2)
    as HSoundMu2.
  exists phi_eff1, phi_eff2, phi_mu1, phi_mu2,
    heap_eff1, theta1, heap_eff2, theta2,
    heap_mu1, heap_mu2, v_mu1, v_mu2.
  split; [exact HSummary |].
  split; [exact HPass |].
  split; [exact HMu1 |].
  split; [exact HMu2 |].
  split; [exact HHeapFinal |].
  split; [exact HValFinal |].
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with
      (phi2 :=
        Phi_Seq phi_eff1
          (Phi_Seq phi_eff2 (Phi_Seq phi_mu1 phi_mu2))).
  - simpl. exact HTrace.
  - apply PTS_Seq.
    + apply theta_with_phi_prefixes_left_sound.
    + apply PTS_Seq.
      * apply theta_with_phi_prefixes_middle_sound.
      * apply PTS_Seq.
        -- apply theta_with_phi_prefixes_right_sound.
           apply Theta_introl. exact HSoundMu1.
        -- apply theta_with_phi_prefixes_right_sound.
           apply Theta_intror. exact HSoundMu2.
Qed.

Theorem PairParCheckedStructuredTopSound_from_typed_branch_soundness :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    phi =
      pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2 ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    (BackTriangle
      (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) ->
      phi_mu1 ⋞ theta1) ->
    (BackTriangle
      (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) ->
      phi_mu2 ⋞ theta2) ->
    phi ⋞ theta_with_phi_prefixes
      phi_eff1 phi_eff2 (Union_Theta theta1 theta2).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    HTc HTrace HSummary HPass HSteps HSoundLeft HSoundRight.
  destruct
    (TcExp_pair_par_branch_backtriangles
      ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc)
    as (HBackLeft & HBackRight).
  eapply PairParCheckedStructuredStepsPhi_top_sound; eauto.
Qed.

Theorem PairParCheckedStructuredTopSound_from_typed_branch_runs :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    phi =
      pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2 ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_mu1
      (StDone heap_mu1 v_mu1) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_mu2 v_mu2) ->
    (BackTriangle
      (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) ->
      StepsPhi
        (initial_state heap env rho (Mu_App ef1 ea1))
        phi_mu1
        (StDone heap_mu1 v_mu1) ->
      phi_mu1 ⋞ theta1) ->
    (BackTriangle
      (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) ->
      StepsPhi
        (initial_state heap env rho (Mu_App ef2 ea2))
        phi_mu2
        (StDone heap_mu2 v_mu2) ->
      phi_mu2 ⋞ theta2) ->
    phi ⋞ theta_with_phi_prefixes
      phi_eff1 phi_eff2 (Union_Theta theta1 theta2).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTrace HSummary HPass HSteps HStepsLeft HStepsRight
    HSoundLeft HSoundRight.
  assert
    (HLeft :
      BackTriangle
        (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) ->
      phi_mu1 ⋞ theta1).
  {
    intros HBackLeft. eapply HSoundLeft; eauto.
  }
  assert
    (HRight :
      BackTriangle
        (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) ->
      phi_mu2 ⋞ theta2).
  {
    intros HBackRight. eapply HSoundRight; eauto.
  }
	  eapply PairParCheckedStructuredTopSound_from_typed_branch_soundness;
	    eauto.
Qed.

Theorem PairParCheckedStructuredTopSound_from_typed_branch_runs_with_branch_reasoning :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    phi =
      pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2 ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_mu1
      (StDone heap_mu1 v_mu1) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_mu2 v_mu2) ->
    (BackTriangle
      (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) ->
      StepsPhi
        (initial_state heap env rho (Mu_App ef1 ea1))
        phi_mu1
        (StDone heap_mu1 v_mu1) ->
      StepsPhi
        (initial_state heap env rho (Eff_App ef1 ea1))
        phi_eff1
        (StDone heap_eff1 (Eff theta1)) ->
      phi_mu1 ⋞ theta1) ->
    (BackTriangle
      (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) ->
      StepsPhi
        (initial_state heap env rho (Mu_App ef2 ea2))
        phi_mu2
        (StDone heap_mu2 v_mu2) ->
      StepsPhi
        (initial_state heap env rho (Eff_App ef2 ea2))
        phi_eff2
        (StDone heap_eff2 (Eff theta2)) ->
      phi_mu2 ⋞ theta2) ->
    phi ⋞ theta_with_phi_prefixes
      phi_eff1 phi_eff2 (Union_Theta theta1 theta2).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTrace HSummary HPass HSteps HMu1 HMu2
    HSoundLeft HSoundRight.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HEff1 HEff2]; subst.
  destruct
    (TcExp_pair_par_branch_backtriangles
      ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc)
    as (HBackLeft & HBackRight).
  pose proof (HSoundLeft HBackLeft HMu1 HEff1) as HSoundMu1.
  pose proof (HSoundRight HBackRight HMu2 HEff2) as HSoundMu2.
  eapply PairParCheckedStructuredStepsPhi_top_sound; eauto.
Qed.

Theorem PairParCheckedStructuredTopSound_from_typed_app_body_runs :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    phi =
      pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2 ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_mu1
      (StDone heap_mu1 v_mu1) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_mu2 v_mu2) ->
    exists phi_fun_mu1 phi_arg_mu1 phi_body_mu1
      phi_fun_mu2 phi_arg_mu2 phi_body_mu2,
      ReadOnlyPhi phi_fun_mu1 /\
      ReadOnlyPhi phi_arg_mu1 /\
      ReadOnlyPhi phi_fun_mu2 /\
      ReadOnlyPhi phi_arg_mu2 /\
      (phi_body_mu1 ⋞ theta1 ->
       phi_body_mu2 ⋞ theta2 ->
       phi ⋞ theta_with_phi_prefixes
         phi_eff1 phi_eff2
         (Union_Theta
           (theta_with_phi_prefixes phi_fun_mu1 phi_arg_mu1 theta1)
           (theta_with_phi_prefixes phi_fun_mu2 phi_arg_mu2 theta2))).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTrace HSummary HPass HSteps HMu1 HMu2.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HEff1 HEff2]; subst.
  destruct
    (TcExp_pair_par_branch_backtriangles
      ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc)
    as (HBackLeft & HBackRight).
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_from_body_soundness
      heap env rho ef1 ea1
      phi_mu1 heap_mu1 v_mu1 phi_eff1 heap_eff1 theta1
      stty ctxt rgns
      HBackLeft HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu1 HEff1)
    as (phi_fun_mu1 & phi_arg_mu1 & phi_body_mu1 &
        phi_fun_eff1 & phi_arg_eff1 & phi_body_eff1 &
        env_closure1 & rho_closure1 & f1 & x1 & ec1 & ee1 & v_arg1 &
        _HFunMu1 & _HFunEff1 & _HArgMu1 & _HArgEff1 &
        _HBodyMu1 & _HBodyEff1 & _HFunTrace1 & _HArgTrace1 &
        HFunRO1 & HArgRO1 & HSoundLeft).
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_from_body_soundness
      heap env rho ef2 ea2
      phi_mu2 heap_mu2 v_mu2 phi_eff2 heap_eff2 theta2
      stty ctxt rgns
      HBackRight HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu2 HEff2)
    as (phi_fun_mu2 & phi_arg_mu2 & phi_body_mu2 &
        phi_fun_eff2 & phi_arg_eff2 & phi_body_eff2 &
        env_closure2 & rho_closure2 & f2 & x2 & ec2 & ee2 & v_arg2 &
        _HFunMu2 & _HFunEff2 & _HArgMu2 & _HArgEff2 &
        _HBodyMu2 & _HBodyEff2 & _HFunTrace2 & _HArgTrace2 &
        HFunRO2 & HArgRO2 & HSoundRight).
  exists phi_fun_mu1, phi_arg_mu1, phi_body_mu1.
  exists phi_fun_mu2, phi_arg_mu2, phi_body_mu2.
  repeat split; try assumption.
  intros HBodySound1 HBodySound2.
  pose proof (HSoundLeft HBodySound1) as HBranchSound1.
  pose proof (HSoundRight HBodySound2) as HBranchSound2.
  eapply
    (PairParCheckedParallelTopSound_reduces_to_augmented_branch_soundness
      heap env rho ef1 ea1 ef2 ea2
      (pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2)
      phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2
      (theta_with_phi_prefixes phi_fun_mu1 phi_arg_mu1 theta1)
      (theta_with_phi_prefixes phi_fun_mu2 phi_arg_mu2 theta2)
      heap' v);
	  eauto.
Qed.

Theorem PairParCheckedStructuredTopSound_from_typed_app_body_runs_with_body_reasoning :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    phi =
      pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2 ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_mu1
      (StDone heap_mu1 v_mu1) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_mu2 v_mu2) ->
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
        (StDone heap_mu1 v_mu1) ->
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff1 (Eff theta1)) ->
      phi_body_mu ⋞ theta1) ->
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
        (StDone heap_mu2 v_mu2) ->
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff2 (Eff theta2)) ->
      phi_body_mu ⋞ theta2) ->
    exists phi_fun_mu1 phi_arg_mu1 phi_fun_mu2 phi_arg_mu2,
      ReadOnlyPhi phi_fun_mu1 /\
      ReadOnlyPhi phi_arg_mu1 /\
      ReadOnlyPhi phi_fun_mu2 /\
      ReadOnlyPhi phi_arg_mu2 /\
      phi ⋞ theta_with_phi_prefixes
        phi_eff1 phi_eff2
        (Union_Theta
          (theta_with_phi_prefixes phi_fun_mu1 phi_arg_mu1 theta1)
          (theta_with_phi_prefixes phi_fun_mu2 phi_arg_mu2 theta2)).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTrace HSummary HPass HSteps HMu1 HMu2
    HBodyReasoningLeft HBodyReasoningRight.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HEff1 HEff2]; subst.
  destruct
    (TcExp_pair_par_branch_backtriangles
      ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc)
    as (HBackLeft & HBackRight).
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_with_body_reasoning
      heap env rho ef1 ea1
      phi_mu1 heap_mu1 v_mu1 phi_eff1 heap_eff1 theta1
      stty ctxt rgns
      HBackLeft HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu1 HEff1 HBodyReasoningLeft)
    as (phi_fun_mu1 & phi_arg_mu1 & phi_body_mu1 &
        phi_fun_eff1 & phi_arg_eff1 & phi_body_eff1 &
        env_closure1 & rho_closure1 & f1 & x1 & ec1 & ee1 & v_arg1 &
        _HFunMu1 & _HFunEff1 & _HArgMu1 & _HArgEff1 &
        _HBodyMu1 & _HBodyEff1 & HFunRO1 & HArgRO1 & HBranchSound1).
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_with_body_reasoning
      heap env rho ef2 ea2
      phi_mu2 heap_mu2 v_mu2 phi_eff2 heap_eff2 theta2
      stty ctxt rgns
      HBackRight HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu2 HEff2 HBodyReasoningRight)
    as (phi_fun_mu2 & phi_arg_mu2 & phi_body_mu2 &
        phi_fun_eff2 & phi_arg_eff2 & phi_body_eff2 &
        env_closure2 & rho_closure2 & f2 & x2 & ec2 & ee2 & v_arg2 &
        _HFunMu2 & _HFunEff2 & _HArgMu2 & _HArgEff2 &
        _HBodyMu2 & _HBodyEff2 & HFunRO2 & HArgRO2 & HBranchSound2).
  exists phi_fun_mu1, phi_arg_mu1, phi_fun_mu2, phi_arg_mu2.
  repeat split; try assumption.
  eapply
    (PairParCheckedParallelTopSound_reduces_to_augmented_branch_soundness
      heap env rho ef1 ea1 ef2 ea2
      (pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2)
      phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2
      (theta_with_phi_prefixes phi_fun_mu1 phi_arg_mu1 theta1)
      (theta_with_phi_prefixes phi_fun_mu2 phi_arg_mu2 theta2)
      heap' v);
	    eauto.
Qed.

Theorem PairParCheckedStructuredTopSound_from_typed_app_runs_from_below :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    phi =
      pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2 ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_mu1
      (StDone heap_mu1 v_mu1) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_mu2 v_mu2) ->
    (forall n, SmallStepCorrectnessBelow n) ->
    exists phi_fun_mu1 phi_arg_mu1 phi_fun_mu2 phi_arg_mu2,
      ReadOnlyPhi phi_fun_mu1 /\
      ReadOnlyPhi phi_arg_mu1 /\
      ReadOnlyPhi phi_fun_mu2 /\
      ReadOnlyPhi phi_arg_mu2 /\
      phi ⋞ theta_with_phi_prefixes
        phi_eff1 phi_eff2
        (Union_Theta
          (theta_with_phi_prefixes phi_fun_mu1 phi_arg_mu1 theta1)
          (theta_with_phi_prefixes phi_fun_mu2 phi_arg_mu2 theta2)).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTrace HSummary HPass HSteps HMu1 HMu2 HBelowAll.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HEff1 HEff2]; subst.
  destruct
    (TcExp_pair_par_branch_backtriangles
      ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc)
    as (HBackLeft & HBackRight).
  destruct (StepsPhi_to_StepsPhiN _ _ _ HMu1) as (n1 & HMu1N).
  destruct (StepsPhi_to_StepsPhiN _ _ _ HMu2) as (n2 & HMu2N).
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_from_below
      n1 heap env rho ef1 ea1
      phi_mu1 heap_mu1 v_mu1 phi_eff1 heap_eff1 theta1
      stty ctxt rgns
      HBackLeft HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu1N HEff1 (HBelowAll n1))
    as (phi_fun_mu1 & phi_arg_mu1 & phi_body_mu1 &
        phi_fun_eff1 & phi_arg_eff1 & phi_body_eff1 &
        env_closure1 & rho_closure1 & f1 & x1 & ec1 & ee1 & v_arg1 &
        _HFunMu1 & _HFunEff1 & _HArgMu1 & _HArgEff1 &
        _HBodyMu1 & _HBodyEff1 & HFunRO1 & HArgRO1 & HBranchSound1).
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_from_below
      n2 heap env rho ef2 ea2
      phi_mu2 heap_mu2 v_mu2 phi_eff2 heap_eff2 theta2
      stty ctxt rgns
      HBackRight HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu2N HEff2 (HBelowAll n2))
    as (phi_fun_mu2 & phi_arg_mu2 & phi_body_mu2 &
        phi_fun_eff2 & phi_arg_eff2 & phi_body_eff2 &
        env_closure2 & rho_closure2 & f2 & x2 & ec2 & ee2 & v_arg2 &
        _HFunMu2 & _HFunEff2 & _HArgMu2 & _HArgEff2 &
        _HBodyMu2 & _HBodyEff2 & HFunRO2 & HArgRO2 & HBranchSound2).
  exists phi_fun_mu1, phi_arg_mu1, phi_fun_mu2, phi_arg_mu2.
  repeat split; try assumption.
  eapply
    (PairParCheckedParallelTopSound_reduces_to_augmented_branch_soundness
      heap env rho ef1 ea1 ef2 ea2
      (pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2)
      phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2
      (theta_with_phi_prefixes phi_fun_mu1 phi_arg_mu1 theta1)
      (theta_with_phi_prefixes phi_fun_mu2 phi_arg_mu2 theta2)
      heap' v);
    eauto.
Qed.

Theorem PairParCheckedStructuredTopSound_same_abstraction_from_below :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    phi =
      pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2 ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_mu1
      (StDone heap_mu1 v_mu1) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_mu2 v_mu2) ->
    (forall n, SmallStepCorrectnessBelow n) ->
    phi ⋞ theta_with_phi_prefixes
      phi_eff1 phi_eff2 (Union_Theta theta1 theta2).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTrace HSummary HPass HSteps HMu1 HMu2 HBelowAll.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HEff1 HEff2]; subst.
  destruct
    (TcExp_pair_par_branch_backtriangles
      ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc)
    as (HBackLeft & HBackRight).
  destruct (StepsPhi_to_StepsPhiN _ _ _ HMu1) as (n1 & HMu1N).
  destruct (StepsPhi_to_StepsPhiN _ _ _ HMu2) as (n2 & HMu2N).
  pose proof
    (MuAppEffAppTerminalSound_raw_from_below
      n1 heap env rho ef1 ea1
      phi_mu1 heap_mu1 v_mu1 phi_eff1 heap_eff1 theta1
      stty ctxt rgns
      HBackLeft HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu1N HEff1 (HBelowAll n1))
    as HSoundLeft.
  pose proof
    (MuAppEffAppTerminalSound_raw_from_below
      n2 heap env rho ef2 ea2
      phi_mu2 heap_mu2 v_mu2 phi_eff2 heap_eff2 theta2
      stty ctxt rgns
      HBackRight HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu2N HEff2 (HBelowAll n2))
    as HSoundRight.
  eapply PairParCheckedParallelTopSound_reduces_to_same_heap_branch_soundness;
    eauto.
Qed.

Theorem PairParCheckedStructuredTopSound_from_typed_app_actual_body_runs :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    phi =
      pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2 ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_mu1
      (StDone heap_mu1 v_mu1) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_mu2 v_mu2) ->
    exists phi_fun_mu1 phi_arg_mu1 phi_body_mu1
      phi_fun_mu2 phi_arg_mu2 phi_body_mu2,
      ReadOnlyPhi phi_fun_mu1 /\
      ReadOnlyPhi phi_arg_mu1 /\
      ReadOnlyPhi phi_fun_mu2 /\
      ReadOnlyPhi phi_arg_mu2 /\
      phi ⋞ theta_with_phi_prefixes
        phi_eff1 phi_eff2
        (Union_Theta
          (theta_with_phi_prefixes
            phi_fun_mu1 phi_arg_mu1 (theta_of_phi phi_body_mu1))
          (theta_with_phi_prefixes
            phi_fun_mu2 phi_arg_mu2 (theta_of_phi phi_body_mu2))).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTrace HSummary HPass HSteps HMu1 HMu2.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HEff1 HEff2]; subst.
  destruct
    (TcExp_pair_par_branch_backtriangles
      ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc)
    as (HBackLeft & HBackRight).
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_actual_body
      heap env rho ef1 ea1
      phi_mu1 heap_mu1 v_mu1 phi_eff1 heap_eff1 theta1
      stty ctxt rgns
      HBackLeft HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu1 HEff1)
    as (phi_fun_mu1 & phi_arg_mu1 & phi_body_mu1 &
        phi_fun_eff1 & phi_arg_eff1 & phi_body_eff1 &
        env_closure1 & rho_closure1 & f1 & x1 & ec1 & ee1 & v_arg1 &
        _HFunMu1 & _HFunEff1 & _HArgMu1 & _HArgEff1 &
        _HBodyMu1 & _HBodyEff1 & HFunRO1 & HArgRO1 & HSoundLeft).
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_actual_body
      heap env rho ef2 ea2
      phi_mu2 heap_mu2 v_mu2 phi_eff2 heap_eff2 theta2
      stty ctxt rgns
      HBackRight HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu2 HEff2)
    as (phi_fun_mu2 & phi_arg_mu2 & phi_body_mu2 &
        phi_fun_eff2 & phi_arg_eff2 & phi_body_eff2 &
        env_closure2 & rho_closure2 & f2 & x2 & ec2 & ee2 & v_arg2 &
        _HFunMu2 & _HFunEff2 & _HArgMu2 & _HArgEff2 &
        _HBodyMu2 & _HBodyEff2 & HFunRO2 & HArgRO2 & HSoundRight).
  exists phi_fun_mu1, phi_arg_mu1, phi_body_mu1.
  exists phi_fun_mu2, phi_arg_mu2, phi_body_mu2.
  repeat split; try assumption.
  eapply
    (PairParCheckedParallelTopSound_reduces_to_augmented_branch_soundness
      heap env rho ef1 ea1 ef2 ea2
      (pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2)
      phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2
      (theta_with_phi_prefixes
        phi_fun_mu1 phi_arg_mu1 (theta_of_phi phi_body_mu1))
      (theta_with_phi_prefixes
        phi_fun_mu2 phi_arg_mu2 (theta_of_phi phi_body_mu2))
      heap' v);
    eauto.
Qed.
