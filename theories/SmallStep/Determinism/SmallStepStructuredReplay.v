From stdpp Require Import gmap.
From stdpp Require Import fin_maps.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Sets.Ensembles.

Require Import theories.Core.DynamicActions.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Regions.
Require Import theories.Core.StaticActions.
Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.TraceSemantics.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepPairParDispatch.
Require Import theories.Runtime.SmallStepStructuredTrace.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Meta.EffectFacts.
Require Import theories.Meta.TraceTypingFacts.
Require Import theories.Meta.StoreFacts.
Require Import theories.Determinism.Determinism.

Lemma Phi_Theta_Disjointness_disjoint_traces :
  forall phi1 phi2 theta1 theta2,
    phi1 ⋞ theta1 ->
    phi2 ⋞ theta2 ->
    Disjointness theta1 theta2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2).
Proof.
  intros phi1 phi2 theta1 theta2 HSound1 HSound2 HDisjoint.
  inversion HDisjoint as [acts1 acts2 HDisjointSets]; subst.
  constructor.
  intros p1 p2 HIn1 HIn2.
  eapply
    (Disjoint_computed_disjoint_dynamic_action
      acts1 acts2 phi1 phi2 p1 p2);
    eauto.
Qed.

Lemma Phi_Theta_Soundness_da_in_replay :
  forall phi theta da,
    phi ⋞ theta ->
    DA_in_Phi da phi ->
    DA_in_Theta da theta.
Proof.
  induction phi as [| da' | phi1 IHphi1 phi2 IHphi2
                   | phi1 IHphi1 phi2 IHphi2];
    intros theta da HSound HIn;
    inversion HSound; subst; inversion HIn; subst; eauto.
  - match goal with
    | H : DA_in_Phi da phi1 \/ DA_in_Phi da phi2 |- _ =>
        destruct H as [HLeft | HRight]
    end.
    + eapply IHphi1; eauto.
    + eapply IHphi2; eauto.
  - match goal with
    | H : DA_in_Phi da phi1 \/ DA_in_Phi da phi2 |- _ =>
        destruct H as [HLeft | HRight]
    end.
    + eapply IHphi1; eauto.
    + eapply IHphi2; eauto.
Qed.

Lemma DA_in_Theta_write_disjoint_dynamic_read :
  forall theta r_write l_write v_write r_read l_read,
    DA_in_Theta (DA_Write r_write l_write v_write) theta ->
    ThetaWritesDisjointDynamicRead theta r_read l_read ->
    (r_write, l_write) <> (r_read, l_read).
Proof.
  intros theta r_write l_write v_write r_read l_read HIn.
  dependent induction HIn; intros HDisjoint; simpl in HDisjoint;
    try contradiction.
  - match goal with
    | HActs : set_elem _ (CA_WriteAbs ?r) |- _ =>
        specialize (HDisjoint (CA_WriteAbs r) HActs)
    end.
    simpl in HDisjoint.
    intro HSame.
    inversion HSame; subst.
    contradiction.
  - match goal with
    | HActs : set_elem _ (CA_WriteConc ?r ?l) |- _ =>
        specialize (HDisjoint (CA_WriteConc r l) HActs)
    end.
    simpl in HDisjoint.
    exact HDisjoint.
  - eapply IHHIn.
    + reflexivity.
    + intros ca Hca.
      apply HDisjoint.
      apply Union_introl.
      exact Hca.
  - eapply IHHIn.
    + reflexivity.
    + intros ca Hca.
      apply HDisjoint.
      apply Union_intror.
      exact Hca.
Qed.

Theorem Phi_Theta_Soundness_writes_disjoint_phi_reads :
  forall phi_write theta_write phi_read,
    phi_write ⋞ theta_write ->
    ThetaWritesDisjointPhiReads theta_write phi_read ->
    PhiWritesDisjointPhiReads phi_write phi_read.
Proof.
  unfold PhiWritesDisjointPhiReads, ThetaWritesDisjointPhiReads.
  intros phi_write theta_write phi_read HSound HThetaReads
    r_write l_write v_write r_read l_read v_read HWrite HRead.
  eapply DA_in_Theta_write_disjoint_dynamic_read.
  - eapply Phi_Theta_Soundness_da_in_replay; eauto.
  - eapply HThetaReads; eauto.
Qed.

Theorem Disjointness_theta_writes_disjoint_phi_reads :
  forall theta_write theta_read phi_read,
    Disjointness theta_write theta_read ->
    phi_read ⋞ theta_read ->
    ThetaWritesDisjointPhiReads theta_write phi_read.
Proof.
  unfold ThetaWritesDisjointPhiReads.
  intros theta_write theta_read phi_read HDisjoint HSoundRead
    r_read l_read v_read HRead.
  inversion HDisjoint as [acts_write acts_read HDisjointSets]; subst.
  simpl.
  intros ca_write HCaWrite.
  destruct ca_write as
    [r_write l_write | r_write l_write | r_write
    | r_write | r_write];
    simpl; try exact I.
  - assert (HWriteTheta :
      DA_in_Theta
        (DA_Write r_write l_write v_read)
        (Some acts_write)).
    { apply DAT_Write_Conc. exact HCaWrite. }
    pose proof
      (Phi_Theta_Soundness_da_in_replay
        phi_read (Some acts_read)
        (DA_Read r_read l_read v_read)
        HSoundRead HRead) as HReadTheta.
    pose proof
      (Disjoint_da_in_theta
        acts_write acts_read
        (DA_Write r_write l_write v_read)
        (DA_Read r_read l_read v_read)
        HDisjointSets HWriteTheta HReadTheta) as HDynamic.
    inversion HDynamic; subst.
    match goal with
    | HNe : not (_ = _) |- _ =>
        intro HSame;
        apply HNe;
        destruct HSame;
        reflexivity
    end.
  - assert (HWriteTheta :
      DA_in_Theta
        (DA_Write r_write l_read v_read)
        (Some acts_write)).
    { apply DAT_Write_Abs. exact HCaWrite. }
    pose proof
      (Phi_Theta_Soundness_da_in_replay
        phi_read (Some acts_read)
        (DA_Read r_read l_read v_read)
        HSoundRead HRead) as HReadTheta.
    pose proof
      (Disjoint_da_in_theta
        acts_write acts_read
        (DA_Write r_write l_read v_read)
        (DA_Read r_read l_read v_read)
        HDisjointSets HWriteTheta HReadTheta) as HDynamic.
    inversion HDynamic; subst.
    match goal with
    | HNe : not (_ = _) |- _ =>
        intro HSameRegion;
        apply HNe;
        subst;
        reflexivity
    end.
Qed.

Theorem Epsilon_Phi_Soundness_theta_writes_disjoint_phi_reads :
  forall theta eps phi,
    Epsilon_Phi_Soundness (eps, phi) ->
    ThetaWritesDisjointStaticReads theta eps ->
    ThetaWritesDisjointPhiReads theta phi.
Proof.
  unfold ThetaWritesDisjointPhiReads, ThetaWritesDisjointStaticReads.
  intros theta eps phi HStaticSound HThetaStatic
    r l v HRead.
  inversion HStaticSound as [eps' phi' HAll]; subst.
  destruct (HAll (DA_Read r l v) HRead)
    as (sa & HInStatic & HStaticDynamic).
  inversion HStaticDynamic; subst.
  destruct theta as [acts |]; simpl in *; [| contradiction].
  intros ca Hca.
  pose proof (HThetaStatic ca r Hca HInStatic) as HDisjointRegion.
  destruct ca as
    [r_ca l_ca | r_ca l_ca | r_ca | r_ca | r_ca];
    simpl in *; try exact I.
  - intro HSame.
    inversion HSame; subst.
    contradiction.
  - exact HDisjointRegion.
Qed.

Theorem PairParStepsPhi_checked_theta_disjoint_branch_replay_join :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_state phi_left phi_right state'
    heap_left heap_right stty stty_left stty_right theta_left theta_right,
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi_state phi_left phi_right state' ->
    phi_left ⋞ theta_left ->
    phi_right ⋞ theta_right ->
    Disjointness theta_left theta_right ->
    (phi_left, heap) ==>* (Phi_Nil, heap_left) ->
    (phi_right, heap) ==>* (Phi_Nil, heap_right) ->
    TcPhi stty_left phi_left ->
    TcPhi stty_right phi_right ->
    TcHeap (heap, stty) ->
    StoreExtends stty stty_left ->
    StoreExtends stty stty_right ->
    TcHeap (heap_left, stty_left) ->
    TcHeap (heap_right, stty_right) ->
    exists heap_join,
      PairParBranchReplayWitness
        heap phi_left phi_right heap_left heap_right heap_join /\
      (phi_state, heap_join) ==>* (Phi_Nil, pairpar_state_heap state') /\
      TcHeap
        (heap_join, stty ∪ (stty_left ∖ stty ∪ stty_right ∖ stty)).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_state phi_left phi_right state'
    heap_left heap_right stty stty_left stty_right theta_left theta_right
    HSteps HSoundLeft HSoundRight HDisjoint HLeftReplay HRightReplay
    HTcLeft HTcRight HTcHeap HExtLeft HExtRight HTcHeapLeft HTcHeapRight.
  eapply PairParStepsPhi_checked_trace_disjoint_branch_replay_join; eauto.
  eapply Phi_Theta_Disjointness_disjoint_traces; eauto.
Qed.

Theorem PairParStepsPhi_checked_pass_sound_branch_replay_join :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_state phi_left phi_right state'
    heap_left heap_right stty stty_left stty_right theta_left theta_right,
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi_state phi_left phi_right state' ->
    phi_left ⋞ theta_left ->
    phi_right ⋞ theta_right ->
    PairParCheckPass theta_left theta_right ->
    (phi_left, heap) ==>* (Phi_Nil, heap_left) ->
    (phi_right, heap) ==>* (Phi_Nil, heap_right) ->
    TcPhi stty_left phi_left ->
    TcPhi stty_right phi_right ->
    TcHeap (heap, stty) ->
    StoreExtends stty stty_left ->
    StoreExtends stty stty_right ->
    TcHeap (heap_left, stty_left) ->
    TcHeap (heap_right, stty_right) ->
    exists heap_join,
      PairParBranchReplayWitness
        heap phi_left phi_right heap_left heap_right heap_join /\
      (phi_state, heap_join) ==>* (Phi_Nil, pairpar_state_heap state') /\
      TcHeap
        (heap_join, stty ∪ (stty_left ∖ stty ∪ stty_right ∖ stty)).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_state phi_left phi_right state'
    heap_left heap_right stty stty_left stty_right theta_left theta_right
    HSteps HSoundLeft HSoundRight [HDisjoint _] HLeftReplay HRightReplay
    HTcLeft HTcRight HTcHeap HExtLeft HExtRight HTcHeapLeft HTcHeapRight.
  eapply PairParStepsPhi_checked_theta_disjoint_branch_replay_join; eauto.
Qed.

Theorem PairParStepsPhi_checked_pass_sound_branch_steps_join :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_state phi_left phi_right state'
    heap_left heap_right v_left v_right
    stty stty_left stty_right theta_left theta_right,
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi_state phi_left phi_right state' ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_left
      (StDone heap_left v_left) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_right
      (StDone heap_right v_right) ->
    phi_left ⋞ theta_left ->
    phi_right ⋞ theta_right ->
    PairParCheckPass theta_left theta_right ->
    TcPhi stty_left phi_left ->
    TcPhi stty_right phi_right ->
    TcHeap (heap, stty) ->
    StoreExtends stty stty_left ->
    StoreExtends stty stty_right ->
    TcHeap (heap_left, stty_left) ->
    TcHeap (heap_right, stty_right) ->
    exists heap_join,
      PairParBranchReplayWitness
        heap phi_left phi_right heap_left heap_right heap_join /\
      (phi_state, heap_join) ==>* (Phi_Nil, pairpar_state_heap state') /\
      TcHeap
        (heap_join, stty ∪ (stty_left ∖ stty ∪ stty_right ∖ stty)).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_state phi_left phi_right state'
    heap_left heap_right v_left v_right
    stty stty_left stty_right theta_left theta_right
    HCheckedSteps HLeftSteps HRightSteps HSoundLeft HSoundRight HPass
    HTcLeft HTcRight HTcHeap HExtLeft HExtRight HTcHeapLeft HTcHeapRight.
  pose proof (StepsPhi_replays_heap _ _ _ HLeftSteps) as HLeftReplay.
  pose proof (StepsPhi_replays_heap _ _ _ HRightSteps) as HRightReplay.
  simpl in HLeftReplay, HRightReplay.
  eapply PairParStepsPhi_checked_pass_sound_branch_replay_join; eauto.
Qed.

Theorem PairPar_source_static_summary_checked_branch_join_exists :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1
    phi_state phi_left phi_right state'
    heap_left heap_right v_left v_right
    stty stty_left stty_right,
    PairParSourceOrderedEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    Epsilon_Phi_Soundness
      (fold_subst_eps rho static_eff1, phi_eff1) ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi_state phi_left phi_right state' ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_left
      (StDone heap_left v_left) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_right
      (StDone heap_right v_right) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    TcPhi stty_left phi_left ->
    TcPhi stty_right phi_right ->
    TcHeap (heap, stty) ->
    StoreExtends stty stty_left ->
    StoreExtends stty stty_right ->
    TcHeap (heap_left, stty_left) ->
    TcHeap (heap_right, stty_right) ->
    exists phi_source heap_join,
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      StepsPhi
        (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
        phi_source
        (pairpar_checked_run_start heap_eff2 env rho ef1 ea1 ef2 ea2 k) /\
      phi_as_list phi_source =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2 /\
      PairParBranchReplayWitness
        heap phi_left phi_right heap_left heap_right heap_join /\
      (phi_state, heap_join) ==>* (Phi_Nil, pairpar_state_heap state') /\
      TcHeap
        (heap_join, stty ∪ (stty_left ∖ stty ∪ stty_right ∖ stty)).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1
    phi_state phi_left phi_right state'
    heap_left heap_right v_left v_right
    stty stty_left stty_right
    HSummary HReadOnlyStatic HStaticSound HPass HCheckedSteps
    HLeftSteps HRightSteps HSoundLeft HSoundRight
    HTcLeft HTcRight HTcHeap HExtLeft HExtRight HTcHeapLeft HTcHeapRight.
  destruct
    (PairParSourceOrderedEffectSummaryStepsPhi_source_pass_static_sound_prefix
      heap env rho ef1 ea1 ef2 ea2 k
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1
      HSummary HReadOnlyStatic HStaticSound HPass)
    as (phi_source & HIndependentSummary & HSourcePrefix & HSourceTrace).
  destruct
    (PairParStepsPhi_checked_pass_sound_branch_steps_join
      heap env rho ef1 ea1 ef2 ea2 k
      phi_state phi_left phi_right state'
      heap_left heap_right v_left v_right
      stty stty_left stty_right theta1 theta2
      HCheckedSteps HLeftSteps HRightSteps HSoundLeft HSoundRight HPass
      HTcLeft HTcRight HTcHeap HExtLeft HExtRight HTcHeapLeft HTcHeapRight)
    as (heap_join & HWitness & HStateReplay & HTcJoin).
  exists phi_source, heap_join.
  split; [exact HIndependentSummary |].
  split; [exact HSourcePrefix |].
  split; [exact HSourceTrace |].
  split; [exact HWitness |].
  split; [exact HStateReplay | exact HTcJoin].
Qed.

Theorem PairPar_source_trace_static_summary_checked_branch_join_exists :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    phi_state phi_left phi_right state'
    heap_left heap_right v_left v_right
    stty stty_left stty_right,
    PairParSourceOrderedEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (Phi_Static_Effect phi_eff1) ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi_state phi_left phi_right state' ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_left
      (StDone heap_left v_left) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_right
      (StDone heap_right v_right) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    TcPhi stty_left phi_left ->
    TcPhi stty_right phi_right ->
    TcHeap (heap, stty) ->
    StoreExtends stty stty_left ->
    StoreExtends stty stty_right ->
    TcHeap (heap_left, stty_left) ->
    TcHeap (heap_right, stty_right) ->
    exists phi_source heap_join,
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      StepsPhi
        (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
        phi_source
        (pairpar_checked_run_start heap_eff2 env rho ef1 ea1 ef2 ea2 k) /\
      phi_as_list phi_source =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2 /\
      PairParBranchReplayWitness
        heap phi_left phi_right heap_left heap_right heap_join /\
      (phi_state, heap_join) ==>* (Phi_Nil, pairpar_state_heap state') /\
      TcHeap
        (heap_join, stty ∪ (stty_left ∖ stty ∪ stty_right ∖ stty)).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    phi_state phi_left phi_right state'
    heap_left heap_right v_left v_right
    stty stty_left stty_right
    HSummary HReadOnlyStatic HPass HCheckedSteps
    HLeftSteps HRightSteps HSoundLeft HSoundRight
    HTcLeft HTcRight HTcHeap HExtLeft HExtRight HTcHeapLeft HTcHeapRight.
  destruct
    (PairParSourceOrderedEffectSummaryStepsPhi_source_pass_trace_static_prefix
      heap env rho ef1 ea1 ef2 ea2 k
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
      HSummary HReadOnlyStatic HPass)
    as (phi_source & HIndependentSummary & HSourcePrefix & HSourceTrace).
  destruct
    (PairParStepsPhi_checked_pass_sound_branch_steps_join
      heap env rho ef1 ea1 ef2 ea2 k
      phi_state phi_left phi_right state'
      heap_left heap_right v_left v_right
      stty stty_left stty_right theta1 theta2
      HCheckedSteps HLeftSteps HRightSteps HSoundLeft HSoundRight HPass
      HTcLeft HTcRight HTcHeap HExtLeft HExtRight HTcHeapLeft HTcHeapRight)
    as (heap_join & HWitness & HStateReplay & HTcJoin).
  exists phi_source, heap_join.
  split; [exact HIndependentSummary |].
  split; [exact HSourcePrefix |].
  split; [exact HSourceTrace |].
  split; [exact HWitness |].
  split; [exact HStateReplay | exact HTcJoin].
Qed.

Theorem PairPar_source_static_included_summary_checked_branch_join_exists :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1
    phi_state phi_left phi_right state'
    heap_left heap_right v_left v_right
    stty stty_left stty_right,
    PairParSourceOrderedEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    Included StaticAction
      (Phi_Static_Effect phi_eff1)
      (fold_subst_eps rho static_eff1) ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi_state phi_left phi_right state' ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_left
      (StDone heap_left v_left) ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_right
      (StDone heap_right v_right) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    TcPhi stty_left phi_left ->
    TcPhi stty_right phi_right ->
    TcHeap (heap, stty) ->
    StoreExtends stty stty_left ->
    StoreExtends stty stty_right ->
    TcHeap (heap_left, stty_left) ->
    TcHeap (heap_right, stty_right) ->
    exists phi_source heap_join,
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      StepsPhi
        (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
        phi_source
        (pairpar_checked_run_start heap_eff2 env rho ef1 ea1 ef2 ea2 k) /\
      phi_as_list phi_source =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2 /\
      PairParBranchReplayWitness
        heap phi_left phi_right heap_left heap_right heap_join /\
      (phi_state, heap_join) ==>* (Phi_Nil, pairpar_state_heap state') /\
      TcHeap
        (heap_join, stty ∪ (stty_left ∖ stty ∪ stty_right ∖ stty)).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1
    phi_state phi_left phi_right state'
    heap_left heap_right v_left v_right
    stty stty_left stty_right
    HSummary HReadOnlyStatic HIncluded HPass HCheckedSteps
    HLeftSteps HRightSteps HSoundLeft HSoundRight
    HTcLeft HTcRight HTcHeap HExtLeft HExtRight HTcHeapLeft HTcHeapRight.
  destruct
    (PairParSourceOrderedEffectSummaryStepsPhi_source_pass_static_included_prefix
      heap env rho ef1 ea1 ef2 ea2 k
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1
      HSummary HReadOnlyStatic HIncluded HPass)
    as (phi_source & HIndependentSummary & HSourcePrefix & HSourceTrace).
  destruct
    (PairParStepsPhi_checked_pass_sound_branch_steps_join
      heap env rho ef1 ea1 ef2 ea2 k
      phi_state phi_left phi_right state'
      heap_left heap_right v_left v_right
      stty stty_left stty_right theta1 theta2
      HCheckedSteps HLeftSteps HRightSteps HSoundLeft HSoundRight HPass
      HTcLeft HTcRight HTcHeap HExtLeft HExtRight HTcHeapLeft HTcHeapRight)
    as (heap_join & HWitness & HStateReplay & HTcJoin).
  exists phi_source, heap_join.
  split; [exact HIndependentSummary |].
  split; [exact HSourcePrefix |].
  split; [exact HSourceTrace |].
  split; [exact HWitness |].
  split; [exact HStateReplay | exact HTcJoin].
Qed.
