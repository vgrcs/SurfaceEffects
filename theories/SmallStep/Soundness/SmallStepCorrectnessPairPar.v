From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Wf_nat.

(* Pair_Par-specific correctness lemmas over the checked structured runtime. *)

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepExplicitStoreBase.
Require Import theories.Runtime.SmallStepExplicitStoreTheorems.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepTyping.
Require Import theories.Runtime.SmallStepPairParDispatch.
Require Import theories.Runtime.TraceSemantics.
Require Import theories.Runtime.SmallStepTraceSafety.
Require Import theories.Runtime.SmallStepStructuredTrace.
Require Import theories.Runtime.SmallStepCorrectness.
Require Import theories.Runtime.SmallStepEffectSoundness.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.DynamicActions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Regions.
Require Import theories.Core.StaticActions.
Require Import theories.Core.Values.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.EffectFacts.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.TraceTypingFacts.
Require Import theories.Meta.TypingWeakeningFacts.
Require Import theories.Meta.TypeFacts.
Require Import theories.Determinism.SmallStepStructuredReplay.
Require Import theories.Determinism.SmallStepPairParScheduleDeterminism.


Require Export theories.Soundness.SmallStepCorrectnessApps.

Theorem ScheduledCheckedPairParTerminalDecompose :
  forall heap env rho ef1 ea1 ef2 ea2 k phi heap_final v_final,
    ScheduledCheckedTerminal
      (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
      phi
      heap_final
      v_final ->
    exists phi_eff1 phi_eff2 phi_pair phi_tail phi_left phi_right
      heap_eff1 heap_eff2 theta1 theta2
      heap_right v_right heap_left v_left,
      phi = pairpar_checked_packed_structured_trace
        phi_eff1 phi_eff2 (Phi_Seq phi_pair phi_tail) /\
      ScheduledCheckedTerminal
        (initial_state heap env rho (Eff_App ef1 ea1))
        phi_eff1
        heap_eff1
        (Eff theta1) /\
	      ScheduledCheckedTerminal
	        (initial_state heap_eff1 env rho (Eff_App ef2 ea2))
	        phi_eff2
	        heap_eff2
	        (Eff theta2) /\
	      PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 /\
	      PairParCheckPass theta1 theta2 /\
	      PairParLoosePackedStepsPhi
	        (pairpar_checked_start heap_eff2 env rho ef1 ea1 ef2 ea2 k)
        phi_pair
        Phi_Nil
        phi_left
        phi_right
        (PPS_State
          (StReturn heap_left (Pair (v_left, v_right)) k)) /\
      ScheduledCheckedTerminal
        (initial_state heap_eff2 env rho (Mu_App ef2 ea2))
        phi_right
        heap_right
        v_right /\
      ScheduledCheckedTerminal
        (with_state_heap heap_right
          (initial_state heap_eff2 env rho (Mu_App ef1 ea1)))
        phi_left
        heap_left
        v_left /\
      ScheduledCheckedTerminal
        (StReturn heap_left (Pair (v_left, v_right)) k)
        phi_tail
        heap_final
        v_final.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k phi heap_final v_final HRun.
  inversion HRun; subst; simpl in *; try contradiction; try discriminate.
  exists phi_eff1, phi_eff2, phi_pair, phi_tail, phi_left, phi_right.
  exists heap_eff1, heap_eff2, theta1, theta2.
  exists heap_right, v_right, heap_left, v_left.
  split; [reflexivity |].
  split; [eassumption |].
  split; [eassumption |].
  match goal with
  | HObserved : PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 |- _ =>
      split; [exact HObserved |];
      destruct HObserved as [HPass _];
      split; [exact HPass |]
  end.
  split; [eassumption |].
  split; [eassumption |].
  split; [eassumption |].
  eassumption.
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

Theorem PairParObservedCheckPass_implies_check_pass :
  forall theta1 theta2 phi_eff1 phi_eff2,
    PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 ->
    PairParCheckPass theta1 theta2.
Proof.
  intros theta1 theta2 phi_eff1 phi_eff2 HObserved.
  destruct HObserved as [HPass _].
  exact HPass.
Qed.

Theorem PairParObservedCheckPass_dynamic_write_read_disjoint :
  forall phi_mu1 phi_mu2 theta1 theta2 phi_eff1 phi_eff2,
    phi_mu1 ⋞ theta1 ->
    phi_mu2 ⋞ theta2 ->
    PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 ->
    PhiWritesDisjointPhiReads phi_mu1 phi_eff2 /\
    PhiWritesDisjointPhiReads phi_mu2 phi_eff1.
Proof.
  intros phi_mu1 phi_mu2 theta1 theta2 phi_eff1 phi_eff2
    HSound1 HSound2 HObserved.
  destruct HObserved as [_ [HProtect1 HProtect2]].
  split.
  - eapply Phi_Theta_Soundness_writes_disjoint_phi_reads; eauto.
  - eapply Phi_Theta_Soundness_writes_disjoint_phi_reads; eauto.
Qed.

Theorem PairParCoveredRightBranch_replays_left_summary :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    phi_right heap_right v_right,
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_right
      (StDone heap_right v_right) ->
    phi_right ⋞ theta2 ->
    ReadOnlyPhi phi_eff1 ->
    PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 ->
    (phi_eff1, heap_right) ==>* (Phi_Nil, heap_right).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    phi_right heap_right v_right
    HSummary HRightSteps HRightSound HReadOnlyLeftSummary HObserved.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HSummaryLeft _HSummaryRight]; subst.
  destruct HObserved as [_ [_ HRightWritesDisjointLeftReads]].
  eapply
    (StepsPhi_preserves_readonly_phi_replay_from_theta
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_right
      (StDone heap_right v_right)
      theta2
      (pairpar_effect_summary_state heap env rho ef1 ea1)
      phi_eff1
      (StDone heap_eff1 (Eff theta1)));
    eauto.
Qed.

Theorem PairParCoveredLeftBranch_replays_right_summary :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    phi_left heap_left v_left,
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_left
      (StDone heap_left v_left) ->
    phi_left ⋞ theta1 ->
    ReadOnlyPhi phi_eff2 ->
    PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 ->
    (phi_eff2, heap_left) ==>* (Phi_Nil, heap_left).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    phi_left heap_left v_left
    HSummary HLeftSteps HLeftSound HReadOnlyRightSummary HObserved.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      _HSummaryLeft _HSummaryRight]; subst.
  destruct HObserved as [_ [HLeftWritesDisjointRightReads _]].
  eapply
    (StepsPhi_preserves_readonly_phi_replay_from_theta
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_left
      (StDone heap_left v_left)
      theta1
      (pairpar_effect_summary_state heap env rho ef2 ea2)
      phi_eff2
      (StDone heap_eff2 (Eff theta2)));
    eauto.
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
	    phi ⋞ Theta_Top.
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
	    phi ⋞ Theta_Top.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    branch_theta1 branch_theta2 heap' v
    _ _ _ _ _ _.
  apply PhiInThetaTop.
Qed.

Theorem PairParCheckedLoosePackedTopSound_reduces_to_branch_soundness :
  forall heap env rho ef1 ea1 ef2 ea2
    phi phi_eff1 phi_eff2 phi_mu phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v,
    phi = pairpar_checked_packed_structured_trace phi_eff1 phi_eff2 phi_mu ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
	    PairParLoosePackedStepsPhi
	      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
	      phi_mu
	      phi_mu_state
	      phi_mu1
	      phi_mu2
	      (PPS_State (StDone heap' v)) ->
	    phi_mu1 ⋞ theta1 ->
	    phi_mu2 ⋞ theta2 ->
	    phi ⋞ Theta_Top.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi phi_eff1 phi_eff2 phi_mu phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    HTrace HSummary HPass HSteps HSoundMu1 HSoundMu2.
  subst.
  eapply PairParLoosePackedStepsPhi_top_sound_with_branch_summaries;
    eauto.
Qed.

Theorem PairParLoosePacked_branch_traces_disjoint_from_check :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_mu phi_mu_state phi_mu1 phi_mu2 heap' v theta1 theta2,
    PairParLoosePackedStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    phi_mu1 ⋞ theta1 ->
    phi_mu2 ⋞ theta2 ->
    PairParCheckPass theta1 theta2 ->
    Disjoint_Traces (phi_as_list phi_mu1) (phi_as_list phi_mu2).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_mu phi_mu_state phi_mu1 phi_mu2 heap' v theta1 theta2
    _ HSoundMu1 HSoundMu2 [HDisjoint _].
  eapply Phi_Theta_Disjointness_disjoint_traces; eauto.
Qed.

Hint Resolve PairParLoosePacked_branch_traces_disjoint_from_check
  : surface_effects.

Lemma OrdinaryStepsPhi_terminal_heap_runtime :
  forall state phi state',
    OrdinaryStepsPhi state phi state' ->
    forall tout stty heap' v,
      state' = StDone heap' v ->
      WTStateRuntimeHeapShapeAt state tout stty ->
      exists stty',
        StoreExtends stty stty' /\
        TcHeap (heap', stty') /\
        RuntimeHeapShape heap' stty'.
Proof.
  intros state phi state' HSteps.
  induction HSteps as
    [state
    | state label state_mid phi state_final
        _HNonPair _HNonPairMid HStep _ IH];
    intros tout stty heap' v HFinal HWT.
  - subst state.
	    destruct (WTStateRuntimeHeapShapeAt_done_value heap' v tout stty HWT)
	      as (HTcHeap & HHeapShape & _HTcVal & _HValShape).
	    exists stty.
	    split.
	    + apply StoreExtends_refl.
	    + split.
	      * exact HTcHeap.
	      * exact HHeapShape.
  - destruct
      (WTStateRuntimeHeapShapeAt_step_preservation
        state tout stty label state_mid HWT HStep)
      as (stty_mid & HWTMid & _HTcPhi & _HLabelSafe & HExtMid).
	    destruct (IH tout stty_mid heap' v HFinal HWTMid)
	      as (stty' & HExtTail & HTcHeap' & HHeapShape').
	    exists stty'.
	    split.
	    + eapply StoreExtends_trans; eauto.
	    + split.
	      * exact HTcHeap'.
	      * exact HHeapShape'.
Qed.

Theorem PairParLoosePacked_checked_replay_and_disjoint_from_check :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_mu phi_mu_state phi_mu1 phi_mu2 heap' v theta1 theta2,
    PairParLoosePackedStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    phi_mu1 ⋞ theta1 ->
    phi_mu2 ⋞ theta2 ->
    PairParCheckPass theta1 theta2 ->
    Disjoint_Traces (phi_as_list phi_mu1) (phi_as_list phi_mu2) /\
    exists heap_mid,
      (Phi_Par phi_mu1 phi_mu2, heap) ==>* (Phi_Nil, heap_mid) /\
      (phi_mu_state, heap_mid) ==>* (Phi_Nil, heap').
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_mu phi_mu_state phi_mu1 phi_mu2 heap' v theta1 theta2
    HSteps HSoundMu1 HSoundMu2 HPass.
  split.
  - eapply PairParLoosePacked_branch_traces_disjoint_from_check; eauto.
  - eapply PairParLoosePackedStepsPhi_checked_kdone_split_replays_heap;
      eauto.
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
    phi ⋞ Theta_Top.
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
    phi ⋞ Theta_Top.
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
    phi ⋞ Theta_Top.
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
    phi ⋞ Theta_Top.
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
    StepsStayNonPairParRun (initial_state heap env rho ef1) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea1)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef2) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea2)) ->
    exists phi_fun_mu1 phi_arg_mu1 phi_body_mu1
      phi_fun_mu2 phi_arg_mu2 phi_body_mu2,
      ReadOnlyPhi phi_fun_mu1 /\
      ReadOnlyPhi phi_arg_mu1 /\
      ReadOnlyPhi phi_fun_mu2 /\
	      ReadOnlyPhi phi_arg_mu2 /\
	      (phi_body_mu1 ⋞ theta1 ->
	       phi_body_mu2 ⋞ theta2 ->
	       phi ⋞ Theta_Top).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTrace HSummary HPass HSteps HMu1 HMu2
    HStayFun1 HStayArg1 HStayFun2 HStayArg2.
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
      HMu1 HEff1 HStayFun1 HStayArg1)
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
      HMu2 HEff2 HStayFun2 HStayArg2)
    as (phi_fun_mu2 & phi_arg_mu2 & phi_body_mu2 &
        phi_fun_eff2 & phi_arg_eff2 & phi_body_eff2 &
        env_closure2 & rho_closure2 & f2 & x2 & ec2 & ee2 & v_arg2 &
        _HFunMu2 & _HFunEff2 & _HArgMu2 & _HArgEff2 &
        _HBodyMu2 & _HBodyEff2 & _HFunTrace2 & _HArgTrace2 &
        HFunRO2 & HArgRO2 & HSoundRight).
	  exists phi_fun_mu1, phi_arg_mu1, phi_body_mu1.
	  exists phi_fun_mu2, phi_arg_mu2, phi_body_mu2.
	  repeat split; try assumption.
	  intros _ _.
	  apply PhiInThetaTop.
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
    StepsStayNonPairParRun (initial_state heap env rho ef1) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea1)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef2) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea2)) ->
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
	      phi ⋞ Theta_Top.
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTrace HSummary HPass HSteps HMu1 HMu2
    HStayFun1 HStayArg1 HStayFun2 HStayArg2
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
      HMu1 HEff1 HStayFun1 HStayArg1 HBodyReasoningLeft)
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
      HMu2 HEff2 HStayFun2 HStayArg2 HBodyReasoningRight)
    as (phi_fun_mu2 & phi_arg_mu2 & phi_body_mu2 &
        phi_fun_eff2 & phi_arg_eff2 & phi_body_eff2 &
        env_closure2 & rho_closure2 & f2 & x2 & ec2 & ee2 & v_arg2 &
        _HFunMu2 & _HFunEff2 & _HArgMu2 & _HArgEff2 &
        _HBodyMu2 & _HBodyEff2 & HFunRO2 & HArgRO2 & HBranchSound2).
	  exists phi_fun_mu1, phi_arg_mu1, phi_fun_mu2, phi_arg_mu2.
	  repeat split; try assumption.
	  apply PhiInThetaTop.
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
    StepsStayNonPairParRun (initial_state heap env rho ef1) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea1)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef2) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea2)) ->
    (forall n, SmallStepCorrectnessBelow n) ->
    exists phi_fun_mu1 phi_arg_mu1 phi_fun_mu2 phi_arg_mu2,
      ReadOnlyPhi phi_fun_mu1 /\
      ReadOnlyPhi phi_arg_mu1 /\
	      ReadOnlyPhi phi_fun_mu2 /\
	      ReadOnlyPhi phi_arg_mu2 /\
	      phi ⋞ Theta_Top.
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTrace HSummary HPass HSteps HMu1 HMu2
    HStayFun1 HStayArg1 HStayFun2 HStayArg2 HBelowAll.
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
      HMu1N HEff1 HStayFun1 HStayArg1 (HBelowAll n1))
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
      HMu2N HEff2 HStayFun2 HStayArg2 (HBelowAll n2))
    as (phi_fun_mu2 & phi_arg_mu2 & phi_body_mu2 &
        phi_fun_eff2 & phi_arg_eff2 & phi_body_eff2 &
        env_closure2 & rho_closure2 & f2 & x2 & ec2 & ee2 & v_arg2 &
        _HFunMu2 & _HFunEff2 & _HArgMu2 & _HArgEff2 &
        _HBodyMu2 & _HBodyEff2 & HFunRO2 & HArgRO2 & HBranchSound2).
	  exists phi_fun_mu1, phi_arg_mu1, phi_fun_mu2, phi_arg_mu2.
	  repeat split; try assumption.
	  apply PhiInThetaTop.
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
    StepsStayNonPairParRun (initial_state heap env rho ef1) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea1)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef2) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea2)) ->
    (forall n, SmallStepCorrectnessBelow n) ->
    phi ⋞ Theta_Top.
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2
    heap_mu1 heap_mu2 heap' v_mu1 v_mu2 v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTrace HSummary HPass HSteps HMu1 HMu2
    HStayFun1 HStayArg1 HStayFun2 HStayArg2 HBelowAll.
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
      HMu1N HEff1 HStayFun1 HStayArg1 (HBelowAll n1))
    as HSoundLeft.
  pose proof
    (MuAppEffAppTerminalSound_raw_from_below
      n2 heap env rho ef2 ea2
      phi_mu2 heap_mu2 v_mu2 phi_eff2 heap_eff2 theta2
      stty ctxt rgns
      HBackRight HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu2N HEff2 HStayFun2 HStayArg2 (HBelowAll n2))
    as HSoundRight.
  eapply PairParCheckedParallelTopSound_reduces_to_same_heap_branch_soundness;
    eauto.
Qed.

Theorem PairParRightThenLeftRightBranchSound_from_below :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParRightThenLeftStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef2) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea2)) ->
    (forall n, SmallStepCorrectnessBelow n) ->
    phi_mu2 ⋞ theta2.
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HSummary HSteps HStayFun2 HStayArg2 HBelowAll.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      _HEff1 HEff2]; subst.
  destruct
    (TcExp_pair_par_branch_backtriangles
      ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc)
    as (_HBackLeft & HBackRight).
  unfold pairpar_checked_start, pairpar_checked_initial in HSteps.
  destruct
    (PairParRightThenLeftStepsPhi_terminal_decompose_kdone
      (initial_state heap env rho (Mu_App ef1 ea1))
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu_state phi_mu1 phi_mu2 heap' v
      I I eq_refl HSteps)
    as (heap_right & v_right & _heap_left & _v_left &
        HRightSteps & _HLeftSteps & _HHeapFinal & _HValFinal).
  pose proof
    (OrdinaryStepsPhi_as_stepsphi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_right v_right)
      HRightSteps)
    as HRightStepsPhi.
  destruct (StepsPhi_to_StepsPhiN _ _ _ HRightStepsPhi)
    as (n_right & HRightStepsN).
  exact
    (MuAppEffAppTerminalSound_raw_from_below
      n_right heap env rho ef2 ea2
      phi_mu2 heap_right v_right phi_eff2 heap_eff2 theta2
      stty ctxt rgns
      HBackRight HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HRightStepsN HEff2 HStayFun2 HStayArg2 (HBelowAll n_right)).
Qed.

Theorem PairParRightThenLeftLeftSummaryReplay_from_below :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 ->
    PairParRightThenLeftStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef2) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea2)) ->
    (forall n, SmallStepCorrectnessBelow n) ->
    exists heap_right v_right,
      OrdinaryStepsPhi
        (initial_state heap env rho (Mu_App ef2 ea2))
        phi_mu2
        (StDone heap_right v_right) /\
      phi_mu2 ⋞ theta2 /\
      (phi_eff1, heap_right) ==>* (Phi_Nil, heap_right).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HSummary HObserved HSteps HStayFun2 HStayArg2 HBelowAll.
  destruct
    (PairParEffectSummaryStepsPhi_readonly_from_pairpar_typed
      heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns ty static
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTc HSummary)
    as (HReadOnlyEff1 & _HReadOnlyEff2).
  pose proof
    (PairParRightThenLeftRightBranchSound_from_below
      ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static stty
      phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2 heap' v
      HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HSummary HSteps HStayFun2 HStayArg2 HBelowAll)
    as HRightSound.
  unfold pairpar_checked_start, pairpar_checked_initial in HSteps.
  destruct
    (PairParRightThenLeftStepsPhi_terminal_decompose_kdone
      (initial_state heap env rho (Mu_App ef1 ea1))
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu_state phi_mu1 phi_mu2 heap' v
      I I eq_refl HSteps)
    as (heap_right & v_right & _heap_left & _v_left &
        HRightSteps & _HLeftSteps & _HHeapFinal & _HValFinal).
  pose proof
    (OrdinaryStepsPhi_as_stepsphi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_right v_right)
      HRightSteps)
    as HRightStepsPhi.
  exists heap_right, v_right.
  repeat split; try assumption.
  eapply PairParCoveredRightBranch_replays_left_summary; eauto.
Qed.

Theorem PairParCoveredRightBranch_rebases_left_summary :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    phi_right heap_right v_right,
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_right
      (StDone heap_right v_right) ->
    phi_right ⋞ theta2 ->
    ReadOnlyPhi phi_eff1 ->
    PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 ->
    StepsPhi
      (initial_state heap_right env rho (Eff_App ef1 ea1))
      phi_eff1
      (StDone heap_right (Eff theta1)).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    phi_right heap_right v_right
    HSummary HRightSteps HRightSound HReadOnlyLeftSummary HObserved.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HSummaryLeft _HSummaryRight]; subst.
  destruct HObserved as [_ [_ HRightWritesDisjointLeftReads]].
  assert (HDisjoint : PhiWritesDisjointPhiReads phi_right phi_eff1).
  {
    eapply Phi_Theta_Soundness_writes_disjoint_phi_reads; eauto.
  }
  assert (HStartSafe : PhiReadsSafe heap phi_eff1).
  {
    change heap with
      (state_heap (pairpar_effect_summary_state heap env rho ef1 ea1)).
    eapply StepsPhi_readonly_reads_safe; eauto.
  }
  assert (HSafe : PhiReadsSafe heap_right phi_eff1).
  {
    eapply
      (StepsPhi_preserves_phi_reads_safe
        (initial_state heap env rho (Mu_App ef2 ea2))
        phi_right
        (StDone heap_right v_right)
        phi_eff1);
      eauto.
  }
  pose proof
    (StepsPhi_readonly_rebase_agree
      (pairpar_effect_summary_state heap env rho ef1 ea1)
      phi_eff1
      (StDone heap_eff1 (Eff theta1))
      heap_right
      HSummaryLeft
      I
      HReadOnlyLeftSummary
      HSafe)
    as HRebased.
  simpl in HRebased.
  exact HRebased.
Qed.

Theorem ScheduledCheckedCoveredRightBranch_rebases_left_summary :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 theta2
    phi_right heap_right v_right,
    ScheduledCheckedTerminal
      (initial_state heap env rho (Eff_App ef1 ea1))
      phi_eff1
      heap_eff1
      (Eff theta1) ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_right
      heap_right
      v_right ->
    phi_right ⋞ theta2 ->
    ReadOnlyPhi phi_eff1 ->
    PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 ->
    ScheduledCheckedTerminal
      (initial_state heap_right env rho (Eff_App ef1 ea1))
      phi_eff1
      heap_right
      (Eff theta1).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 theta2
    phi_right heap_right v_right
    HSummaryLeft HRight HRightSound HReadOnlyLeftSummary HObserved.
  destruct HObserved as [_ [_ HRightWritesDisjointLeftReads]].
  assert (HDisjoint : PhiWritesDisjointPhiReads phi_right phi_eff1).
  {
    eapply Phi_Theta_Soundness_writes_disjoint_phi_reads; eauto.
  }
  destruct
    (ScheduledCheckedTerminal_as_stepsphi_exists
      (initial_state heap env rho (Eff_App ef1 ea1))
      phi_eff1 heap_eff1 (Eff theta1) HSummaryLeft)
    as (phi_eff1_steps & HSummaryLeftSteps & HTraceEff1).
  assert (HReadOnlyEff1Steps : ReadOnlyPhi phi_eff1_steps).
  {
    eapply ReadOnlyPhi_of_phi_as_list_eq.
    - symmetry. exact HTraceEff1.
    - exact HReadOnlyLeftSummary.
  }
  assert (HStartSafe : PhiReadsSafe heap phi_eff1).
  {
    eapply PhiReadsSafe_of_phi_as_list_eq.
    - exact HTraceEff1.
    - change heap with
        (state_heap (initial_state heap env rho (Eff_App ef1 ea1))).
      eapply StepsPhi_readonly_reads_safe; eauto.
  }
  destruct
    (ScheduledCheckedTerminal_as_stepsphi_exists
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_right heap_right v_right HRight)
    as (phi_right_steps & HRightSteps & HTraceRight).
  assert
    (HDisjointSteps :
      PhiWritesDisjointPhiReads phi_right_steps phi_eff1).
  {
    eapply PhiWritesDisjointPhiReads_of_phi_as_list_eq_l.
    - symmetry. exact HTraceRight.
    - exact HDisjoint.
  }
  assert (HLeftSummarySafeAtRightHeap :
    PhiReadsSafe heap_right phi_eff1).
  {
    change heap_right with (state_heap (StDone heap_right v_right)).
    eapply StepsPhi_preserves_phi_reads_safe; eauto.
  }
  pose proof
    (ScheduledCheckedTerminal_readonly_rebase_agree
      (initial_state heap env rho (Eff_App ef1 ea1))
      phi_eff1 heap_eff1 (Eff theta1)
      heap_right
      HSummaryLeft
      I
      HReadOnlyLeftSummary
      HLeftSummarySafeAtRightHeap)
    as HRebased.
  simpl in HRebased.
  exact HRebased.
Qed.

Lemma BackTriangle_pair_par_canonical_inv :
  forall ctxt rgns rho ef1 ea1 ef2 ea2 eff1 eff2,
    BackTriangle
      (ctxt, rgns, rho,
       Pair_Par ef1 ea1 ef2 ea2,
       Concat
         (Concat eff1 eff2)
         (Concat (Eff_App ef1 ea1) (Eff_App ef2 ea2))) ->
    exists ty_e static_ee_1 static_ee_2,
      TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_e, static_ee_1) /\
      ReadOnlyStatic (fold_subst_eps rho static_ee_1) /\
      TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_e, static_ee_2) /\
      ReadOnlyStatic (fold_subst_eps rho static_ee_2) /\
      BackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1) /\
      BackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2) /\
      BackTriangle
        (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) /\
      BackTriangle
        (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2).
Proof.
  intros ctxt rgns rho ef1 ea1 ef2 ea2 eff1 eff2 HBack.
  dependent destruction HBack; try discriminate.
  exists ty_e, static_ee_1, static_ee_2.
  repeat split; assumption.
Qed.

Theorem ScheduledCheckedPairParTerminalBranchSound_from_app_soundness :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final,
    BackTriangle
      (ctxt, rgns, rho,
       Pair_Par ef1 ea1 ef2 ea2,
       Concat
         (Concat eff1 eff2)
         (Concat (Eff_App ef1 ea1) (Eff_App ef2 ea2))) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi
      heap_final
      v_final ->
    (forall heap0 stty0 ef ea
       phi_mu heap_mu v_mu phi_eff heap_eff theta,
      BackTriangle
        (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
      TcHeap (heap0, stty0) ->
      RuntimeHeapShape heap0 stty0 ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty0, rho, env, ctxt) ->
      RuntimeEnvShape stty0 rho env ctxt ->
      ScheduledCheckedTerminal
        (initial_state heap0 env rho (Mu_App ef ea))
        phi_mu
        heap_mu
        v_mu ->
      ScheduledCheckedTerminal
        (initial_state heap0 env rho (Eff_App ef ea))
        phi_eff
        heap_eff
        (Eff theta) ->
      phi_mu ⋞ theta) ->
    exists phi_eff1 phi_eff2 phi_pair phi_tail phi_left phi_right
      theta1 theta2 heap_right v_right heap_left v_left,
      phi =
        pairpar_checked_packed_structured_trace
          phi_eff1 phi_eff2 (Phi_Seq phi_pair phi_tail) /\
      PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 /\
      PairParLoosePackedStepsPhi
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
        phi_pair
        Phi_Nil
        phi_left
        phi_right
        (PPS_State
          (StReturn heap_left (Pair (v_left, v_right)) KDone)) /\
      ScheduledCheckedTerminal
        (initial_state heap env rho (Mu_App ef2 ea2))
        phi_right
        heap_right
        v_right /\
      ScheduledCheckedTerminal
        (initial_state heap_right env rho (Mu_App ef1 ea1))
        phi_left
        heap_left
        v_left /\
      ScheduledCheckedTerminal
        (StReturn heap_left (Pair (v_left, v_right)) KDone)
        phi_tail
        heap_final
        v_final /\
      phi_left ⋞ theta1 /\
      phi_right ⋞ theta2.
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final
    HBackPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HRun HAppSound.
	  destruct
	    (BackTriangle_pair_par_canonical_inv
	      ctxt rgns rho ef1 ea1 ef2 ea2 eff1 eff2
	      HBackPair)
    as (ty_e & static_ee_1 & static_ee_2 &
        HTcEff1 & HReadOnlyEffStatic1 &
        HTcEff2 & HReadOnlyEffStatic2 &
        _HBackEff1 & _HBackEff2 & HBackMu1 & HBackMu2).
    assert (HTyE : ty_e = Ty_Effect).
	    {
	      inversion HTcEff1; reflexivity.
	    }
	    rewrite HTyE in HTcEff1, HTcEff2.
	    clear HTyE.
    destruct
      (ScheduledCheckedPairParTerminalDecompose
        heap env rho ef1 ea1 ef2 ea2 KDone
        phi heap_final v_final HRun)
      as (phi_eff1 & phi_eff2 & phi_pair & phi_tail &
          phi_left & phi_right &
          heap_eff1 & heap_eff2 & theta1 & theta2 &
          heap_right & v_right & heap_left & v_left &
          HTrace & HSummary1 & HSummary2 & HObserved &
          _HPass & HLoose & HRight & HLeft & HTail).
    pose proof
      (ScheduledCheckedEffectSummary_readonly_from_small_step_sound
        heap env rho (Eff_App ef1 ea1)
        stty ctxt rgns static_ee_1
        phi_eff1 heap_eff1 theta1
        HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
        HTcEff1 HSummary1 HReadOnlyEffStatic1)
      as HReadOnlyEff1.
    pose proof
      (ScheduledCheckedEffectSummary_heap_neutral_from_small_step_sound
        heap env rho (Eff_App ef1 ea1)
        stty ctxt rgns static_ee_1
        phi_eff1 heap_eff1 theta1
        HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
        HTcEff1 HSummary1 HReadOnlyEffStatic1)
      as HHeapEff1.
    subst heap_eff1.
    pose proof
      (ScheduledCheckedEffectSummary_heap_neutral_from_small_step_sound
        heap env rho (Eff_App ef2 ea2)
        stty ctxt rgns static_ee_2
        phi_eff2 heap_eff2 theta2
        HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
        HTcEff2 HSummary2 HReadOnlyEffStatic2)
      as HHeapEff2.
    subst heap_eff2.
    pose proof
      (HAppSound
        heap stty ef2 ea2
        phi_right heap_right v_right phi_eff2 heap theta2
        HBackMu2 HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
        HRight HSummary2)
      as HRightSound.
    pose proof
      (ScheduledCheckedCoveredRightBranch_rebases_left_summary
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap theta1 theta2
        phi_right heap_right v_right
        HSummary1 HRight HRightSound HReadOnlyEff1 HObserved)
      as HLeftSummaryRebased.
    destruct
      (BackTriangle_mu_app_eff_app_inv
        ctxt rgns rho ef2 ea2 HBackMu2)
      as (ty_mu2 & _ty_eff2 & _ty_ef2 & _ty_ea2 &
          _static_ef2 & _static_ea2 & static_mu2 & _static_ee2 &
          HTcMu2 & _HTcEff2 & _HROEff2 &
          _HTcEf2 & _HTcEa2 & _HBackEf2 & _HBackEa2 &
          _HROEf2 & _HROEa2).
    destruct
      (initial_state_terminal_value_with_trace
        heap env rho (Mu_App ef2 ea2)
        stty ctxt rgns ty_mu2 static_mu2
        (phi_as_list phi_right) heap_right v_right
        HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
        HTcMu2)
      as (stty_right & _HExtRight & HTcHeapRight &
          HHeapShapeRight & _HTcValRight & _HValShapeRight &
          _HTcPhiRight).
    {
      eapply ScheduledCheckedTerminal_as_steps; eauto.
    }
    assert (HTcEnvRight : TcEnv (stty_right, rho, env, ctxt)).
    {
      eapply ext_stores__env; eauto.
    }
    assert
      (HEnvShapeRight : RuntimeEnvShape stty_right rho env ctxt).
    {
      eapply RuntimeEnvShape_store_ext; eauto.
    }
    change
      (ScheduledCheckedTerminal
        (initial_state heap_right env rho (Mu_App ef1 ea1))
        phi_left heap_left v_left)
      in HLeft.
    pose proof
      (HAppSound
        heap_right stty_right ef1 ea1
        phi_left heap_left v_left phi_eff1 heap_right theta1
        HBackMu1 HTcHeapRight HHeapShapeRight HTcRho HTcInc
        HTcEnvRight HEnvShapeRight HLeft HLeftSummaryRebased)
      as HLeftSound.
    exists phi_eff1, phi_eff2, phi_pair, phi_tail, phi_left, phi_right.
    exists theta1, theta2, heap_right, v_right, heap_left, v_left.
    split; [exact HTrace |].
    split; [exact HObserved |].
    split; [exact HLoose |].
    split; [exact HRight |].
    split; [exact HLeft |].
    split; [exact HTail |].
    split; assumption.
Qed.

Theorem ScheduledCheckedPairParTerminalBranchSound_from_below_all :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final,
    BackTriangle
      (ctxt, rgns, rho,
       Pair_Par ef1 ea1 ef2 ea2,
       Concat
         (Concat eff1 eff2)
         (Concat (Eff_App ef1 ea1) (Eff_App ef2 ea2))) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi
      heap_final
      v_final ->
    (forall n, ScheduledSmallStepCorrectnessBelow n) ->
    exists phi_eff1 phi_eff2 phi_pair phi_tail phi_left phi_right
      theta1 theta2 heap_right v_right heap_left v_left,
      phi =
        pairpar_checked_packed_structured_trace
          phi_eff1 phi_eff2 (Phi_Seq phi_pair phi_tail) /\
      PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 /\
      PairParLoosePackedStepsPhi
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
        phi_pair
        Phi_Nil
        phi_left
        phi_right
        (PPS_State
          (StReturn heap_left (Pair (v_left, v_right)) KDone)) /\
      ScheduledCheckedTerminal
        (initial_state heap env rho (Mu_App ef2 ea2))
        phi_right
        heap_right
        v_right /\
      ScheduledCheckedTerminal
        (initial_state heap_right env rho (Mu_App ef1 ea1))
        phi_left
        heap_left
        v_left /\
      ScheduledCheckedTerminal
        (StReturn heap_left (Pair (v_left, v_right)) KDone)
        phi_tail
        heap_final
        v_final /\
      phi_left ⋞ theta1 /\
      phi_right ⋞ theta2.
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final
    HBackPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HRun HBelowAll.
  eapply ScheduledCheckedPairParTerminalBranchSound_from_app_soundness.
  - exact HBackPair.
  - exact HTcHeap.
  - exact HHeapShape.
  - exact HTcRho.
  - exact HTcInc.
  - exact HTcEnv.
  - exact HEnvShape.
  - exact HRun.
  - intros heap0 stty0 ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      HBack HTcHeap0 HHeapShape0 HTcRho0 HTcInc0 HTcEnv0 HEnvShape0
      HMu HEff.
    destruct (ScheduledCheckedTerminal_to_N _ _ _ _ HMu)
      as (n_mu & HMuN).
    exact
      (MuAppEffAppTerminalSound_scheduled_raw_from_below_N
        n_mu heap0 env rho ef ea
        phi_mu heap_mu v_mu phi_eff heap_eff theta
        stty0 ctxt rgns
        HBack HTcHeap0 HHeapShape0 HTcRho0 HTcInc0
        HTcEnv0 HEnvShape0 HMuN HEff (HBelowAll n_mu)).
Qed.

Theorem ScheduledCheckedPairParTerminalBranchSound_from_below_N :
  forall n ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final,
    BackTriangle
      (ctxt, rgns, rho,
       Pair_Par ef1 ea1 ef2 ea2,
       Concat
         (Concat eff1 eff2)
         (Concat (Eff_App ef1 ea1) (Eff_App ef2 ea2))) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    ScheduledCheckedTerminalN n
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi
      heap_final
      v_final ->
    ScheduledSmallStepCorrectnessBelow n ->
    exists phi_eff1 phi_eff2 phi_pair phi_tail phi_left phi_right
      theta1 theta2 heap_right v_right heap_left v_left,
      phi =
        pairpar_checked_packed_structured_trace
          phi_eff1 phi_eff2 (Phi_Seq phi_pair phi_tail) /\
      PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 /\
      PairParLoosePackedStepsPhi
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
        phi_pair
        Phi_Nil
        phi_left
        phi_right
        (PPS_State
          (StReturn heap_left (Pair (v_left, v_right)) KDone)) /\
      ScheduledCheckedTerminal
        (initial_state heap env rho (Mu_App ef2 ea2))
        phi_right
        heap_right
        v_right /\
      ScheduledCheckedTerminal
        (initial_state heap_right env rho (Mu_App ef1 ea1))
        phi_left
        heap_left
        v_left /\
      ScheduledCheckedTerminal
        (StReturn heap_left (Pair (v_left, v_right)) KDone)
        phi_tail
        heap_final
        v_final /\
      phi_left ⋞ theta1 /\
      phi_right ⋞ theta2.
Proof.
  intros n ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final
    HBackPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HRun HBelow.
	  destruct
	    (BackTriangle_pair_par_canonical_inv
	      ctxt rgns rho ef1 ea1 ef2 ea2 eff1 eff2
	      HBackPair)
    as (ty_e & static_ee_1 & static_ee_2 &
        HTcEff1 & HReadOnlyEffStatic1 &
        HTcEff2 & HReadOnlyEffStatic2 &
        _HBackEff1 & _HBackEff2 & HBackMu1 & HBackMu2).
    assert (HTyE : ty_e = Ty_Effect).
    {
      inversion HTcEff1; reflexivity.
    }
    rewrite HTyE in HTcEff1, HTcEff2.
    clear HTyE.
    dependent destruction HRun; try solve [simpl in *; contradiction].
      pose proof
        (ScheduledCheckedTerminalN_to_terminal
          n_eff1
          (initial_state heap env rho (Eff_App ef1 ea1))
          phi_eff1 heap_eff1 (Eff theta1)
          HRun1)
        as HSummary1.
      pose proof
        (ScheduledCheckedTerminalN_to_terminal
          n_eff2
          (initial_state heap_eff1 env rho (Eff_App ef2 ea2))
          phi_eff2 heap_eff2 (Eff theta2)
          HRun2)
        as HSummary2.
      pose proof
        (ScheduledCheckedTerminalN_to_terminal
          n_right
          (initial_state heap_eff2 env rho (Mu_App ef2 ea2))
          phi_right heap_right v_right
          HRun3)
        as HRight.
      pose proof
        (ScheduledCheckedTerminalN_to_terminal
          n_left
          (with_state_heap heap_right
            (initial_state heap_eff2 env rho (Mu_App ef1 ea1)))
          phi_left heap_left v_left
          HRun4)
        as HLeft.
      pose proof
        (ScheduledCheckedTerminalN_to_terminal
          n_tail
          (StReturn heap_left (Pair (v_left, v_right)) KDone)
          phi_tail heap_final v_final
          HRun5)
        as HTail.
      pose proof
        (ScheduledCheckedEffectSummary_readonly_from_small_step_sound
          heap env rho (Eff_App ef1 ea1)
          stty ctxt rgns static_ee_1
          phi_eff1 heap_eff1 theta1
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcEff1 HSummary1 HReadOnlyEffStatic1)
        as HReadOnlyEff1.
      pose proof
        (ScheduledCheckedEffectSummary_heap_neutral_from_small_step_sound
          heap env rho (Eff_App ef1 ea1)
          stty ctxt rgns static_ee_1
          phi_eff1 heap_eff1 theta1
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcEff1 HSummary1 HReadOnlyEffStatic1)
        as HHeapEff1.
      subst heap_eff1.
      pose proof
        (ScheduledCheckedEffectSummary_heap_neutral_from_small_step_sound
          heap env rho (Eff_App ef2 ea2)
          stty ctxt rgns static_ee_2
          phi_eff2 heap_eff2 theta2
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcEff2 HSummary2 HReadOnlyEffStatic2)
        as HHeapEff2.
      subst heap_eff2.
      assert (HBelowRight : ScheduledSmallStepCorrectnessBelow n_right).
      {
        unfold ScheduledSmallStepCorrectnessBelow in *.
        intros n_child heap0 env0 rho0 ea0 ee0 phi0 heap' v0
          phi_summary heap_summary theta_summary
          stty0 ctxt0 rgns0 ty0 static0
          HLt HBack0 HRun0 HSummary0 HTcHeap0 HHeapShape0
          HTcRho0 HTcInc0 HTcEnv0 HEnvShape0 HTcExp0.
        eapply
          (HBelow n_child heap0 env0 rho0 ea0 ee0 phi0 heap' v0
            phi_summary heap_summary theta_summary
            stty0 ctxt0 rgns0 ty0 static0);
          try assumption; lia.
      }
      pose proof
        (MuAppEffAppTerminalSound_scheduled_raw_from_below_N
          n_right heap env rho ef2 ea2
          phi_right heap_right v_right phi_eff2 heap theta2
          stty ctxt rgns
          HBackMu2 HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HRun3 HSummary2 HBelowRight)
        as HRightSound.
      match goal with
      | HObserved :
          PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 |- _ =>
          pose proof
            (ScheduledCheckedCoveredRightBranch_rebases_left_summary
              heap env rho ef1 ea1 ef2 ea2
              phi_eff1 phi_eff2 heap theta1 theta2
              phi_right heap_right v_right
              HSummary1 HRight HRightSound HReadOnlyEff1 HObserved)
            as HLeftSummaryRebased
      end.
      destruct
        (BackTriangle_mu_app_eff_app_inv
          ctxt rgns rho ef2 ea2 HBackMu2)
        as (ty_mu2 & _ty_eff2 & _ty_ef2 & _ty_ea2 &
            _static_ef2 & _static_ea2 & static_mu2 & _static_ee2 &
            HTcMu2 & _HTcEff2 & _HROEff2 &
            _HTcEf2 & _HTcEa2 & _HBackEf2 & _HBackEa2 &
            _HROEf2 & _HROEa2).
      destruct
        (initial_state_terminal_value_with_trace
          heap env rho (Mu_App ef2 ea2)
          stty ctxt rgns ty_mu2 static_mu2
          (phi_as_list phi_right) heap_right v_right
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcMu2)
        as (stty_right & _HExtRight & HTcHeapRight &
            HHeapShapeRight & _HTcValRight & _HValShapeRight &
            _HTcPhiRight).
      {
        eapply ScheduledCheckedTerminal_as_steps; eauto.
      }
      assert (HTcEnvRight : TcEnv (stty_right, rho, env, ctxt)).
      {
        eapply ext_stores__env; eauto.
      }
      assert
        (HEnvShapeRight : RuntimeEnvShape stty_right rho env ctxt).
      {
        eapply RuntimeEnvShape_store_ext; eauto.
      }
      change
        (ScheduledCheckedTerminalN n_left
          (initial_state heap_right env rho (Mu_App ef1 ea1))
          phi_left heap_left v_left)
        in HRun4.
      change
        (ScheduledCheckedTerminal
          (initial_state heap_right env rho (Mu_App ef1 ea1))
          phi_left heap_left v_left)
        in HLeft.
      assert (HBelowLeft : ScheduledSmallStepCorrectnessBelow n_left).
      {
        unfold ScheduledSmallStepCorrectnessBelow in *.
        intros n_child heap0 env0 rho0 ea0 ee0 phi0 heap' v0
          phi_summary heap_summary theta_summary
          stty0 ctxt0 rgns0 ty0 static0
          HLt HBack0 HRun0 HSummary0 HTcHeap0 HHeapShape0
          HTcRho0 HTcInc0 HTcEnv0 HEnvShape0 HTcExp0.
        eapply
          (HBelow n_child heap0 env0 rho0 ea0 ee0 phi0 heap' v0
            phi_summary heap_summary theta_summary
            stty0 ctxt0 rgns0 ty0 static0);
          try assumption; lia.
      }
      pose proof
        (MuAppEffAppTerminalSound_scheduled_raw_from_below_N
          n_left heap_right env rho ef1 ea1
          phi_left heap_left v_left phi_eff1 heap_right theta1
          stty_right ctxt rgns
          HBackMu1 HTcHeapRight HHeapShapeRight HTcRho HTcInc
          HTcEnvRight HEnvShapeRight HRun4 HLeftSummaryRebased
          HBelowLeft)
        as HLeftSound.
      exists phi_eff1, phi_eff2, phi_pair, phi_tail, phi_left, phi_right.
      exists theta1, theta2, heap_right, v_right, heap_left, v_left.
      split; [reflexivity |].
      match goal with
      | HObserved :
          PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 |- _ =>
          split; [exact HObserved |]
      end.
      match goal with
      | HLoose :
          PairParLoosePackedStepsPhi _ phi_pair Phi_Nil
            phi_left phi_right _ |- _ =>
          split; [exact HLoose |]
      end.
      split; [exact HRight |].
      split; [exact HLeft |].
      split; [exact HTail |].
      split; assumption.
Qed.

Theorem ScheduledCheckedPairParTerminalTopSound_from_app_soundness :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final,
    BackTriangle
      (ctxt, rgns, rho,
       Pair_Par ef1 ea1 ef2 ea2,
       Concat
         (Concat eff1 eff2)
         (Concat (Eff_App ef1 ea1) (Eff_App ef2 ea2))) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi
      heap_final
      v_final ->
    (forall heap0 stty0 ef ea
       phi_mu heap_mu v_mu phi_eff heap_eff theta,
      BackTriangle
        (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
      TcHeap (heap0, stty0) ->
      RuntimeHeapShape heap0 stty0 ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty0, rho, env, ctxt) ->
      RuntimeEnvShape stty0 rho env ctxt ->
      ScheduledCheckedTerminal
        (initial_state heap0 env rho (Mu_App ef ea))
        phi_mu
        heap_mu
        v_mu ->
      ScheduledCheckedTerminal
        (initial_state heap0 env rho (Eff_App ef ea))
        phi_eff
        heap_eff
        (Eff theta) ->
      phi_mu ⋞ theta) ->
	    exists (phi_eff1 : Phi) (phi_eff2 : Phi)
	      (theta1 : Theta) (theta2 : Theta),
	      phi ⋞ Theta_Top.
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final
    HBackPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HRun HAppSound.
  destruct
    (ScheduledCheckedPairParTerminalBranchSound_from_app_soundness
      ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
      stty phi heap_final v_final
      HBackPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HRun HAppSound)
    as (phi_eff1 & phi_eff2 & phi_pair & phi_tail &
        phi_left & phi_right & theta1 & theta2 &
        heap_right & v_right & heap_left & v_left &
        HTrace & _HObserved & HLoose & _HRight & _HLeft &
        HTail & HLeftSound & HRightSound).
	  exists phi_eff1, phi_eff2, theta1, theta2.
	  apply PhiInThetaTop.
Qed.

Theorem ScheduledCheckedPairParTerminalTopSound_from_below_all :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final,
    BackTriangle
      (ctxt, rgns, rho,
       Pair_Par ef1 ea1 ef2 ea2,
       Concat
         (Concat eff1 eff2)
         (Concat (Eff_App ef1 ea1) (Eff_App ef2 ea2))) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    ScheduledCheckedTerminal
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi
      heap_final
      v_final ->
    (forall n, ScheduledSmallStepCorrectnessBelow n) ->
	    exists (phi_eff1 : Phi) (phi_eff2 : Phi)
	      (theta1 : Theta) (theta2 : Theta),
	      phi ⋞ Theta_Top.
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final
    HBackPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HRun HBelowAll.
  destruct
    (ScheduledCheckedPairParTerminalBranchSound_from_below_all
      ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
      stty phi heap_final v_final
      HBackPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HRun HBelowAll)
    as (phi_eff1 & phi_eff2 & phi_pair & phi_tail &
        phi_left & phi_right & theta1 & theta2 &
        heap_right & v_right & heap_left & v_left &
        HTrace & _HObserved & HLoose & _HRight & _HLeft &
        HTail & HLeftSound & HRightSound).
	  exists phi_eff1, phi_eff2, theta1, theta2.
	  apply PhiInThetaTop.
Qed.

Theorem ScheduledCheckedPairParTerminalTopSound_from_below_N :
  forall n ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final,
    BackTriangle
      (ctxt, rgns, rho,
       Pair_Par ef1 ea1 ef2 ea2,
       Concat
         (Concat eff1 eff2)
         (Concat (Eff_App ef1 ea1) (Eff_App ef2 ea2))) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    ScheduledCheckedTerminalN n
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi
      heap_final
      v_final ->
    ScheduledSmallStepCorrectnessBelow n ->
	    exists (phi_eff1 : Phi) (phi_eff2 : Phi)
	      (theta1 : Theta) (theta2 : Theta),
	      phi ⋞ Theta_Top.
Proof.
  intros n ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
    stty phi heap_final v_final
    HBackPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HRun HBelow.
  destruct
    (ScheduledCheckedPairParTerminalBranchSound_from_below_N
      n ctxt rgns rho heap env ef1 ea1 ef2 ea2 eff1 eff2
      stty phi heap_final v_final
      HBackPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HRun HBelow)
    as (phi_eff1 & phi_eff2 & phi_pair & phi_tail &
        phi_left & phi_right & theta1 & theta2 &
        heap_right & v_right & heap_left & v_left &
        HTrace & _HObserved & HLoose & _HRight & _HLeft &
        HTail & HLeftSound & HRightSound).
	  exists phi_eff1, phi_eff2, theta1, theta2.
	  apply PhiInThetaTop.
Qed.

Theorem PairParRightThenLeftLeftSummarySteps_from_below :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 ->
    PairParRightThenLeftStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef2) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea2)) ->
    (forall n, SmallStepCorrectnessBelow n) ->
    exists heap_right v_right,
      OrdinaryStepsPhi
        (initial_state heap env rho (Mu_App ef2 ea2))
        phi_mu2
        (StDone heap_right v_right) /\
      phi_mu2 ⋞ theta2 /\
      StepsPhi
        (initial_state heap_right env rho (Eff_App ef1 ea1))
        phi_eff1
        (StDone heap_right (Eff theta1)).
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HSummary HObserved HSteps HStayFun2 HStayArg2 HBelowAll.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HEff1 _HEff2]; subst.
  destruct
    (PairParEffectSummaryStepsPhi_readonly_from_pairpar_typed
      heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns ty static
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTc HSummary)
    as (HReadOnlyEff1 & _HReadOnlyEff2).
  pose proof
    (PairParRightThenLeftRightBranchSound_from_below
      ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static stty
      phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2 heap' v
      HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HSummary HSteps HStayFun2 HStayArg2 HBelowAll)
    as HRightSound.
  unfold pairpar_checked_start, pairpar_checked_initial in HSteps.
  destruct
    (PairParRightThenLeftStepsPhi_terminal_decompose_kdone
      (initial_state heap env rho (Mu_App ef1 ea1))
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu_state phi_mu1 phi_mu2 heap' v
      I I eq_refl HSteps)
    as (heap_right & v_right & _heap_left & _v_left &
        HRightSteps & _HLeftSteps & _HHeapFinal & _HValFinal).
  pose proof
    (OrdinaryStepsPhi_as_stepsphi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_right v_right)
      HRightSteps)
    as HRightStepsPhi.
  assert (HRightWritesDisjointLeftReads :
    PhiWritesDisjointPhiReads phi_mu2 phi_eff1).
  {
    destruct HObserved as [_ [_ HThetaReads]].
    eapply Phi_Theta_Soundness_writes_disjoint_phi_reads; eauto.
  }
  assert (HLeftSummarySafeAtHeap :
    PhiReadsSafe heap phi_eff1).
  {
    change heap with
      (state_heap (initial_state heap env rho (Eff_App ef1 ea1))).
    eapply StepsPhi_readonly_reads_safe; eauto.
  }
  assert (HLeftSummarySafeAtRightHeap :
    PhiReadsSafe heap_right phi_eff1).
  {
    change heap_right with (state_heap (StDone heap_right v_right)).
    eapply StepsPhi_preserves_phi_reads_safe; eauto.
  }
  pose proof
    (StepsPhi_readonly_rebase_agree
      (initial_state heap env rho (Eff_App ef1 ea1))
      phi_eff1
      (StDone heap_eff1 (Eff theta1))
      heap_right
      HEff1
      I
      HReadOnlyEff1
      HLeftSummarySafeAtRightHeap)
    as HLeftSummaryRebased.
  simpl in HLeftSummaryRebased.
  exists heap_right, v_right.
  repeat split; try assumption.
Qed.

Theorem PairParRightThenLeftBranchSound_from_below :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v,
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 ->
    PairParRightThenLeftStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ef1)) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea1)) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ef2)) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea2)) ->
    (forall n, SmallStepCorrectnessBelow n) ->
    phi_mu1 ⋞ theta1 /\ phi_mu2 ⋞ theta2.
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HSummary HObserved HSteps
    HStayFun1 HStayArg1 HStayFun2 HStayArg2 HBelowAll.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      _HEff1 _HEff2]; subst.
  destruct
    (TcExp_pair_par_branch_backtriangles
      ctxt rgns rho ef1 ea1 ef2 ea2 ty static HTc)
    as (HBackLeft & HBackRight).
  destruct
    (PairParEffectSummaryStepsPhi_readonly_from_pairpar_typed
      heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns ty static
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTc HSummary)
    as (HReadOnlyEff1 & _HReadOnlyEff2).
  unfold pairpar_checked_start, pairpar_checked_initial in HSteps.
  destruct
    (PairParRightThenLeftStepsPhi_terminal_decompose_kdone
      (initial_state heap env rho (Mu_App ef1 ea1))
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu_state phi_mu1 phi_mu2 heap' v
      I I eq_refl HSteps)
    as (heap_right & v_right & heap_left & v_left &
        HRightSteps & HLeftSteps & _HHeapFinal & _HValFinal).
  pose proof
    (OrdinaryStepsPhi_as_stepsphi
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_mu2
      (StDone heap_right v_right)
      HRightSteps)
    as HRightStepsPhi.
  pose proof
    (OrdinaryStepsPhi_as_stepsphi
      (with_state_heap heap_right
        (initial_state heap env rho (Mu_App ef1 ea1)))
      phi_mu1
      (StDone heap_left v_left)
      HLeftSteps)
    as HLeftStepsPhi.
  simpl in HLeftStepsPhi.
  assert (HRightSound : phi_mu2 ⋞ theta2).
  {
    destruct (StepsPhi_to_StepsPhiN _ _ _ HRightStepsPhi)
      as (n_right & HRightStepsN).
    eapply
      (MuAppEffAppTerminalSound_raw_from_below
        n_right heap env rho ef2 ea2
        phi_mu2 heap_right v_right phi_eff2 heap_eff2 theta2
        stty ctxt rgns);
      eauto.
  }
  assert (HLeftSummaryRebased :
    StepsPhi
      (initial_state heap_right env rho (Eff_App ef1 ea1))
      phi_eff1
      (StDone heap_right (Eff theta1))).
  {
    eapply PairParCoveredRightBranch_rebases_left_summary; eauto.
  }
  assert (HBranchTypes :
    exists ty_left static_left ty_right static_right,
      TcExp (ctxt, rgns, Mu_App ef1 ea1, ty_left, static_left) /\
      TcExp (ctxt, rgns, Mu_App ef2 ea2, ty_right, static_right)).
  {
    inversion HTc; subst.
    repeat eexists; eauto.
  }
  destruct HBranchTypes as
    (ty_left & static_left & ty_right & static_right &
      HTcLeft & HTcRight).
  destruct
    (initial_state_terminal_value_with_trace
      heap env rho (Mu_App ef2 ea2)
      stty ctxt rgns ty_right static_right
      (phi_as_list phi_mu2) heap_right v_right
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcRight)
    as (stty_right & HExtRight & HTcHeapRight & HHeapShapeRight &
        _HTcValRight & _HValShapeRight & _HTcPhiRight).
  {
    eapply StepsPhi_as_steps; eauto.
  }
  assert (HTcEnvRight : TcEnv (stty_right, rho, env, ctxt)).
  {
    eapply ext_stores__env; eauto.
  }
  assert
    (HEnvShapeRight : RuntimeEnvShape stty_right rho env ctxt).
  {
    eapply RuntimeEnvShape_store_ext; eauto.
  }
  assert (HLeftSound : phi_mu1 ⋞ theta1).
  {
    destruct (StepsPhi_to_StepsPhiN _ _ _ HLeftStepsPhi)
      as (n_left & HLeftStepsN).
    eapply
      (MuAppEffAppTerminalSound_raw_from_below
        n_left heap_right env rho ef1 ea1
        phi_mu1 heap_left v_left phi_eff1 heap_right theta1
        stty_right ctxt rgns);
      eauto.
  }
  split; assumption.
Qed.

Theorem PairParRightThenLeftCheckedTopSound_from_below :
  forall ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v,
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
    PairParObservedCheckPass theta1 theta2 phi_eff1 phi_eff2 ->
    PairParRightThenLeftStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ef1)) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea1)) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ef2)) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea2)) ->
    (forall n, SmallStepCorrectnessBelow n) ->
    phi ⋞ Theta_Top.
Proof.
  intros ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
    stty
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTrace HSummary HObserved HSteps
    HStayFun1 HStayArg1 HStayFun2 HStayArg2 HBelowAll.
  destruct
    (PairParRightThenLeftBranchSound_from_below
      ctxt rgns rho heap env ef1 ea1 ef2 ea2 ty static
      stty
      phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2 heap' v
      HTc HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HSummary HObserved HSteps
      HStayFun1 HStayArg1 HStayFun2 HStayArg2 HBelowAll)
    as [HSoundLeft HSoundRight].
  eapply
    (PairParCheckedParallelTopSound_reduces_to_same_heap_branch_soundness
      heap env rho ef1 ea1 ef2 ea2
      phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
      heap_eff1 theta1 heap_eff2 theta2 heap' v).
  - exact HTrace.
  - exact HSummary.
  - exact
      (PairParObservedCheckPass_implies_check_pass
        theta1 theta2 phi_eff1 phi_eff2 HObserved).
  - exact
      (PairParRightThenLeftStepsPhi_as_pairpar_steps_phi
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
        phi_mu_state phi_mu1 phi_mu2
        (PPS_State (StDone heap' v))
        HSteps).
  - exact HSoundLeft.
  - exact HSoundRight.
Qed.
