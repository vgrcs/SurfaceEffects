From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Core.Values.
Require Import theories.SmallStep.Runtime.HeapFacts.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Runtime.Trace.

Import ListNotations.

Fixpoint NStateHeapsAligned (state : NState) : Prop :=
  match state with
  | StPairParRun left_state right_state _ _ _ =>
      NStateHeapsAligned left_state /\
      NStateHeapsAligned right_state /\
      state_heap left_state = state_heap right_state
  | _ => True
  end.

Definition TraceReadHeapAgreement
    (phi : Trace) (heap_from heap_to : Heap) : Prop :=
  forall r l cell,
    In (DRead r l) phi ->
    heap_lookup r l heap_from = Some cell ->
    heap_lookup r l heap_to = Some cell.

Lemma state_heap_with_state_heap :
  forall heap state,
    state_heap (with_state_heap heap state) = heap.
Proof.
  intros heap state.
  induction state as
    [heap0 env rho e k | heap0 v k | heap0 v
    | left_state IHLeft right_state IHRight phi_left phi_right k
    | heap0];
    simpl; try reflexivity.
  exact IHLeft.
Qed.

Lemma with_state_heap_twice :
  forall heap_outer heap_inner state,
    with_state_heap heap_outer (with_state_heap heap_inner state) =
    with_state_heap heap_outer state.
Proof.
  intros heap_outer heap_inner state.
  induction state as
    [heap env rho e k | heap v k | heap v
    | left_state IHLeft right_state IHRight phi_left phi_right k
    | heap];
    simpl; try reflexivity.
  rewrite IHLeft, IHRight.
  reflexivity.
Qed.

Lemma with_state_heap_aligned :
  forall heap state,
    NStateHeapsAligned state ->
    NStateHeapsAligned (with_state_heap heap state) /\
    state_heap (with_state_heap heap state) = heap.
Proof.
  intros heap state.
  induction state as
    [heap0 env rho e k | heap0 v k | heap0 v
    | left_state IHLeft right_state IHRight phi_left phi_right k
    | heap0];
    intros HAligned; simpl in *; try solve [split; exact I || reflexivity].
  destruct HAligned as (HAlignedLeft & HAlignedRight & _).
  destruct (IHLeft HAlignedLeft) as (HLeft & HHeapLeft).
  destruct (IHRight HAlignedRight) as (HRight & HHeapRight).
  split.
  - repeat split; try assumption.
    rewrite HHeapLeft, HHeapRight.
    reflexivity.
  - exact HHeapLeft.
Qed.

Lemma with_state_heap_state_heap_aligned :
  forall state,
    NStateHeapsAligned state ->
    with_state_heap (state_heap state) state = state.
Proof.
  intros state.
  induction state as
    [heap env rho e k | heap v k | heap v
    | left_state IHLeft right_state IHRight phi_left phi_right k
    | heap];
    intros HAligned; simpl in *; try reflexivity.
  destruct HAligned as (HAlignedLeft & HAlignedRight & HHeapAligned).
  rewrite IHLeft by assumption.
  rewrite HHeapAligned.
  rewrite IHRight by assumption.
  reflexivity.
Qed.

Lemma with_state_heap_aligned_same :
  forall heap state,
    NStateHeapsAligned state ->
    state_heap state = heap ->
    with_state_heap heap state = state.
Proof.
  intros heap state HAligned HHeap.
  rewrite <- HHeap.
  apply with_state_heap_state_heap_aligned.
  exact HAligned.
Qed.

Lemma NStep_preserves_alignment :
  forall state label state',
    NStep state label state' ->
    NStateHeapsAligned state ->
    NStateHeapsAligned state'.
Proof.
  intros state label state' HStep.
  induction HStep; intros HAligned; simpl in *;
    try solve [repeat split; try assumption; try reflexivity; exact I].
  - destruct HAligned as
      (HAlignedLeft & HAlignedRight & _).
    pose proof (IHHStep HAlignedLeft) as HAlignedLeft'.
    destruct
      (with_state_heap_aligned
        (state_heap left_state') right_state HAlignedRight)
      as (HAlignedRight' & HHeapRight').
    repeat split; try assumption.
    rewrite HHeapRight'.
    reflexivity.
  - destruct HAligned as
      (_ & HAlignedRight & _).
    pose proof (IHHStep HAlignedRight) as HAlignedRight'.
    destruct
      (with_state_heap_aligned
        (state_heap right_state') (StDone heap v1) I)
      as (HAlignedLeft' & HHeapLeft').
    repeat split; try assumption.
Qed.

Lemma NStep_preserves_heap_bounded_aligned :
  forall state label state',
    NStep state label state' ->
    NStateHeapsAligned state ->
    NHeapKeysBounded (state_heap state) ->
    NHeapKeysBounded (state_heap state').
Proof.
  intros state label state' HStep.
  induction HStep; intros HAligned HBounded; simpl in *;
    try solve [assumption].
  - destruct HAligned as
      (HAlignedLeft & _ & _).
    eapply IHHStep; eauto.
  - destruct HAligned as
      (_ & HAlignedRight & HHeapAligned).
    eapply IHHStep; eauto.
    rewrite <- HHeapAligned.
    exact HBounded.
  - destruct HAligned as (_ & _ & HHeapAligned).
    rewrite <- HHeapAligned.
    exact HBounded.
  - eapply heap_alloc_preserves_bounded; eauto.
  - eapply heap_update_preserves_bounded; eauto.
Qed.

Lemma NStepsN_preserves_heap_bounded_aligned :
  forall n state phi state',
    NStepsN n state phi state' ->
    NStateHeapsAligned state ->
    NHeapKeysBounded (state_heap state) ->
    NHeapKeysBounded (state_heap state').
Proof.
  intros n state phi state' HSteps.
  induction HSteps as
    [state | n state label state1 phi state2 HStep _ IH];
    intros HAligned HBounded.
  - exact HBounded.
  - eapply IH.
    + eapply NStep_preserves_alignment; eauto.
    + eapply NStep_preserves_heap_bounded_aligned; eauto.
Qed.

Lemma NStep_lookup_preserved_without_write_aligned :
  forall state label state' r_lookup l_lookup cell,
    NStep state label state' ->
    NStateHeapsAligned state ->
    NHeapKeysBounded (state_heap state) ->
    heap_lookup r_lookup l_lookup (state_heap state) = Some cell ->
    TraceDoesNotWrite r_lookup l_lookup (label_trace label) ->
    heap_lookup r_lookup l_lookup (state_heap state') = Some cell.
Proof.
  intros state label state' r_lookup l_lookup cell HStep.
  induction HStep; intros HAligned HBounded HLookup HNoWrite; simpl in *;
    try solve [assumption].
  - destruct HAligned as
      (HAlignedLeft & _ & _).
    eapply IHHStep; eauto.
  - destruct HAligned as
      (_ & HAlignedRight & HHeapAligned).
    eapply IHHStep; eauto.
    + rewrite <- HHeapAligned.
      exact HBounded.
    + rewrite <- HHeapAligned.
      exact HLookup.
  - destruct HAligned as (_ & _ & HHeapAligned).
    rewrite <- HHeapAligned.
    exact HLookup.
  - eapply heap_lookup_alloc_old; eauto.
  - destruct (Nat.eq_dec r r_lookup) as [-> | HRegionNeq].
    + destruct (Nat.eq_dec l l_lookup) as [-> | HLocationNeq].
      * exfalso.
        apply HNoWrite.
        simpl. left. reflexivity.
      * rewrite heap_update_lookup_other by (right; exact HLocationNeq).
        exact HLookup.
    + rewrite heap_update_lookup_other by (left; exact HRegionNeq).
      exact HLookup.
Qed.

Theorem NSteps_lookup_preserved_without_write_aligned :
  forall state phi state' r l cell,
    NSteps state phi state' ->
    NStateHeapsAligned state ->
    NHeapKeysBounded (state_heap state) ->
    heap_lookup r l (state_heap state) = Some cell ->
    TraceDoesNotWrite r l phi ->
    heap_lookup r l (state_heap state') = Some cell.
Proof.
  intros state phi state' r l cell HSteps.
  induction HSteps as
    [state | state label state1 phi state2 HStep _ IH];
    intros HAligned HBounded HLookup HNoWrite.
  - exact HLookup.
  - pose proof
      (trace_does_not_write_app_l
        r l (label_trace label) phi HNoWrite)
      as HNoWriteLabel.
    pose proof
      (trace_does_not_write_app_r
        r l (label_trace label) phi HNoWrite)
      as HNoWriteTail.
    pose proof
      (NStep_lookup_preserved_without_write_aligned
        state label state1 r l cell HStep
        HAligned HBounded HLookup HNoWriteLabel)
      as HLookup1.
    pose proof
      (NStep_preserves_alignment
        state label state1 HStep HAligned)
      as HAligned1.
    pose proof
      (NStep_preserves_heap_bounded_aligned
        state label state1 HStep HAligned HBounded)
      as HBounded1.
    eapply IH; eauto.
Qed.

Corollary NStepsN_lookup_preserved_without_write_aligned :
  forall n state phi state' r l cell,
    NStepsN n state phi state' ->
    NStateHeapsAligned state ->
    NHeapKeysBounded (state_heap state) ->
    heap_lookup r l (state_heap state) = Some cell ->
    TraceDoesNotWrite r l phi ->
    heap_lookup r l (state_heap state') = Some cell.
Proof.
  intros n state phi state' r l cell HSteps
    HAligned HBounded HLookup HNoWrite.
  eapply NSteps_lookup_preserved_without_write_aligned; eauto.
  eapply NStepsN_to_NSteps; eauto.
Qed.

Corollary NSteps_lookup_preserved_for_disjoint_right_read :
  forall state phi_left state' phi_right r l cell,
    NSteps state phi_left state' ->
    NStateHeapsAligned state ->
    NHeapKeysBounded (state_heap state) ->
    heap_lookup r l (state_heap state) = Some cell ->
    TraceDisjoint phi_left phi_right ->
    In (DRead r l) phi_right ->
    heap_lookup r l (state_heap state') = Some cell.
Proof.
  intros state phi_left state' phi_right r l cell HSteps
    HAligned HBounded HLookup HDisjoint HRead.
  eapply NSteps_lookup_preserved_without_write_aligned; eauto.
  eapply TraceDisjoint_right_read_no_left_write; eauto.
Qed.

Corollary NStepsN_lookup_preserved_for_disjoint_right_read :
  forall n state phi_left state' phi_right r l cell,
    NStepsN n state phi_left state' ->
    NStateHeapsAligned state ->
    NHeapKeysBounded (state_heap state) ->
    heap_lookup r l (state_heap state) = Some cell ->
    TraceDisjoint phi_left phi_right ->
    In (DRead r l) phi_right ->
    heap_lookup r l (state_heap state') = Some cell.
Proof.
  intros n state phi_left state' phi_right r l cell HSteps
    HAligned HBounded HLookup HDisjoint HRead.
  eapply NStepsN_lookup_preserved_without_write_aligned; eauto.
  eapply TraceDisjoint_right_read_no_left_write; eauto.
Qed.

Corollary NSteps_lookup_preserved_for_summary_disjoint_right_read :
  forall state phi_left state' phi_right theta_left theta_right
    r l cell,
    NSteps state phi_left state' ->
    NStateHeapsAligned state ->
    NHeapKeysBounded (state_heap state) ->
    heap_lookup r l (state_heap state) = Some cell ->
    summary_disjointb theta_left theta_right = true ->
    TraceCoveredBySummary phi_left theta_left ->
    TraceCoveredBySummary phi_right theta_right ->
    In (DRead r l) phi_right ->
    heap_lookup r l (state_heap state') = Some cell.
Proof.
  intros state phi_left state' phi_right theta_left theta_right
    r l cell HSteps HAligned HBounded HLookup HSummaryDisjoint
    HCoveredLeft HCoveredRight HRead.
  eapply NSteps_lookup_preserved_for_disjoint_right_read; eauto.
  eapply summary_disjoint_covered_trace_disjoint; eauto.
Qed.

Corollary NStepsN_lookup_preserved_for_summary_disjoint_right_read :
  forall n state phi_left state' phi_right theta_left theta_right
    r l cell,
    NStepsN n state phi_left state' ->
    NStateHeapsAligned state ->
    NHeapKeysBounded (state_heap state) ->
    heap_lookup r l (state_heap state) = Some cell ->
    summary_disjointb theta_left theta_right = true ->
    TraceCoveredBySummary phi_left theta_left ->
    TraceCoveredBySummary phi_right theta_right ->
    In (DRead r l) phi_right ->
    heap_lookup r l (state_heap state') = Some cell.
Proof.
  intros n state phi_left state' phi_right theta_left theta_right
    r l cell HSteps HAligned HBounded HLookup HSummaryDisjoint
    HCoveredLeft HCoveredRight HRead.
  eapply NStepsN_lookup_preserved_for_disjoint_right_read; eauto.
  eapply summary_disjoint_covered_trace_disjoint; eauto.
Qed.

Corollary NSteps_trace_read_heap_agreement_for_summary_disjoint :
  forall state phi_left state' phi_right theta_left theta_right,
    NSteps state phi_left state' ->
    NStateHeapsAligned state ->
    NHeapKeysBounded (state_heap state) ->
    summary_disjointb theta_left theta_right = true ->
    TraceCoveredBySummary phi_left theta_left ->
    TraceCoveredBySummary phi_right theta_right ->
    TraceReadHeapAgreement
      phi_right (state_heap state) (state_heap state').
Proof.
  intros state phi_left state' phi_right theta_left theta_right
    HSteps HAligned HBounded HSummaryDisjoint
    HCoveredLeft HCoveredRight r l cell HRead HLookup.
  eapply NSteps_lookup_preserved_for_summary_disjoint_right_read;
    eauto.
Qed.

Corollary NStepsN_trace_read_heap_agreement_for_summary_disjoint :
  forall n state phi_left state' phi_right theta_left theta_right,
    NStepsN n state phi_left state' ->
    NStateHeapsAligned state ->
    NHeapKeysBounded (state_heap state) ->
    summary_disjointb theta_left theta_right = true ->
    TraceCoveredBySummary phi_left theta_left ->
    TraceCoveredBySummary phi_right theta_right ->
    TraceReadHeapAgreement
      phi_right (state_heap state) (state_heap state').
Proof.
  intros n state phi_left state' phi_right theta_left theta_right
    HSteps HAligned HBounded HSummaryDisjoint
    HCoveredLeft HCoveredRight r l cell HRead HLookup.
  eapply NStepsN_lookup_preserved_for_summary_disjoint_right_read;
    eauto.
Qed.

Corollary NStepsN_trace_read_heap_agreement_for_read_only :
  forall n state phi_left state' phi_right,
    NStepsN n state phi_left state' ->
    NStateHeapsAligned state ->
    NHeapKeysBounded (state_heap state) ->
    ReadOnlyTrace phi_left ->
    TraceReadHeapAgreement
      phi_right (state_heap state) (state_heap state').
Proof.
  intros n state phi_left state' phi_right HSteps HAligned
    HBounded HReadOnly r l cell _HRead HLookup.
  eapply NStepsN_lookup_preserved_without_write_aligned; eauto.
  intros HWrite.
  eapply HReadOnly; eauto.
Qed.

Lemma NStep_heap_neutral_preserves_alignment :
  forall state label state',
    NStep state label state' ->
    NStateHeapsAligned state ->
    HeapNeutralTrace (label_trace label) ->
    NStateHeapsAligned state' /\
    state_heap state' = state_heap state.
Proof.
  intros state label state' HStep.
  induction HStep; intros HAligned HNeutral; simpl in *;
    try solve [split; exact I || reflexivity].
  - repeat split; exact I || reflexivity.
  - destruct HAligned as
      (HAlignedLeft & HAlignedRight & HHeapAligned).
    destruct (IHHStep HAlignedLeft HNeutral) as
      (HAlignedLeft' & HHeapLeft).
    destruct
      (with_state_heap_aligned
        (state_heap left_state') right_state HAlignedRight)
      as (HAlignedRight' & HHeapRight').
    simpl.
    split.
    + repeat split; try assumption.
      rewrite HHeapRight'.
      reflexivity.
    + exact HHeapLeft.
  - destruct HAligned as
      (_ & HAlignedRight & HHeapAligned).
    destruct (IHHStep HAlignedRight HNeutral) as
      (HAlignedRight' & HHeapRight).
    destruct
      (with_state_heap_aligned
        (state_heap right_state') (StDone heap v1) I)
      as (HAlignedLeft' & HHeapLeft').
    simpl.
    split.
    + repeat split; try assumption.
    + rewrite HHeapRight.
      symmetry. exact HHeapAligned.
  - destruct HAligned as (_ & _ & HHeapAligned).
    split; [exact I | symmetry; exact HHeapAligned].
  - destruct HNeutral as (HNoAlloc & _).
    exfalso. eapply HNoAlloc.
    simpl. left. reflexivity.
  - destruct HNeutral as (_ & HReadOnly).
    exfalso. eapply HReadOnly.
    simpl. left. reflexivity.
Qed.

Theorem NSteps_heap_neutral_preserves_alignment :
  forall state phi state',
    NSteps state phi state' ->
    NStateHeapsAligned state ->
    HeapNeutralTrace phi ->
    NStateHeapsAligned state' /\
    state_heap state' = state_heap state.
Proof.
  intros state phi state' HSteps.
  induction HSteps as
    [state | state label state1 phi state2 HStep _ IH];
    intros HAligned HNeutral.
  - split; [exact HAligned | reflexivity].
  - pose proof
      (heap_neutral_trace_app_l
        (label_trace label) phi HNeutral)
      as HNeutralLabel.
    pose proof
      (heap_neutral_trace_app_r
        (label_trace label) phi HNeutral)
      as HNeutralTail.
    destruct
      (NStep_heap_neutral_preserves_alignment
        state label state1 HStep HAligned HNeutralLabel)
      as (HAligned1 & HHeap1).
    destruct (IH HAligned1 HNeutralTail) as
      (HAligned2 & HHeap2).
    split; [exact HAligned2 |].
    rewrite HHeap2, HHeap1.
    reflexivity.
Qed.

Corollary NSteps_heap_neutral_initial_heap :
  forall heap env rho e phi heap_final v,
    NSteps
      (NInitialState heap env rho e)
      phi
      (StDone heap_final v) ->
    HeapNeutralTrace phi ->
    heap_final = heap.
Proof.
  intros heap env rho e phi heap_final v HSteps HNeutral.
  destruct
    (NSteps_heap_neutral_preserves_alignment
      (NInitialState heap env rho e)
      phi
      (StDone heap_final v)
      HSteps I HNeutral)
    as (_ & HHeap).
  simpl in HHeap.
  exact HHeap.
Qed.

Lemma NStep_heap_neutral_read_agreement_replay :
  forall state label state' heap',
    NStep state label state' ->
    NStateHeapsAligned state ->
    HeapNeutralTrace (label_trace label) ->
    TraceReadHeapAgreement (label_trace label) (state_heap state) heap' ->
    NStep
      (with_state_heap heap' state)
      label
      (with_state_heap heap' state').
Proof.
  intros state label state' heap' HStep.
  induction HStep; intros HAligned HNeutral HAgree; simpl in *;
    try solve [constructor; eauto].
  - destruct HAligned as (HAlignedLeft & _ & _).
    rewrite with_state_heap_twice.
    replace
      (StPairParRun
        (with_state_heap heap' left_state')
        (with_state_heap heap' right_state)
        (phi_left ++ label_trace label)
        phi_right
        k)
      with
      (StPairParRun
        (with_state_heap heap' left_state')
        (with_state_heap
          (state_heap (with_state_heap heap' left_state'))
          (with_state_heap heap' right_state))
        (phi_left ++ label_trace label)
        phi_right
        k).
    + constructor.
      eapply IHHStep; eauto.
    + rewrite state_heap_with_state_heap.
      rewrite with_state_heap_twice.
      reflexivity.
  - destruct HAligned as (_ & HAlignedRight & HHeapAligned).
    replace
      (StPairParRun
        (StDone heap' v1)
        (with_state_heap heap' right_state')
        phi_left
        (phi_right ++ label_trace label)
        k)
      with
      (StPairParRun
        (with_state_heap
          (state_heap (with_state_heap heap' right_state'))
          (StDone heap' v1))
        (with_state_heap heap' right_state')
        phi_left
        (phi_right ++ label_trace label)
        k).
    + constructor.
      eapply IHHStep; eauto.
      intros r l cell HRead HLookup.
      eapply HAgree; eauto.
      rewrite HHeapAligned.
      exact HLookup.
    + rewrite state_heap_with_state_heap.
      reflexivity.
  - destruct HNeutral as (HNoAlloc & _).
    exfalso. eapply HNoAlloc.
    simpl. left. reflexivity.
  - eapply StepDerefReturn.
    eapply HAgree.
    + simpl. left. reflexivity.
    + exact H.
  - destruct HNeutral as (_ & HReadOnly).
    exfalso. eapply HReadOnly.
    simpl. left. reflexivity.
Qed.

Theorem NStepsN_heap_neutral_read_agreement_replay :
  forall n state phi state' heap',
    NStepsN n state phi state' ->
    NStateHeapsAligned state ->
    HeapNeutralTrace phi ->
    TraceReadHeapAgreement phi (state_heap state) heap' ->
    NStepsN n
      (with_state_heap heap' state)
      phi
      (with_state_heap heap' state').
Proof.
  intros n state phi state' heap' HSteps.
  induction HSteps as
    [state | n state label state1 phi state2 HStep _ IH];
    intros HAligned HNeutral HAgree.
  - constructor.
  - pose proof
      (heap_neutral_trace_app_l
        (label_trace label) phi HNeutral)
      as HNeutralLabel.
    pose proof
      (heap_neutral_trace_app_r
        (label_trace label) phi HNeutral)
      as HNeutralTail.
    pose proof
      (NStep_heap_neutral_preserves_alignment
        state label state1 HStep HAligned HNeutralLabel)
      as (HAligned1 & HHeap1).
    assert
      (HAgreeLabel :
        TraceReadHeapAgreement
          (label_trace label) (state_heap state) heap').
    {
      intros r l cell HRead HLookup.
      eapply HAgree.
      - apply in_or_app.
        left. exact HRead.
      - exact HLookup.
    }
    assert
      (HAgreeTail :
        TraceReadHeapAgreement phi (state_heap state1) heap').
    {
      intros r l cell HRead HLookup.
      eapply HAgree.
      - apply in_or_app.
        right. exact HRead.
      - rewrite HHeap1 in HLookup.
        exact HLookup.
    }
    eapply StepsNStep.
    + eapply NStep_heap_neutral_read_agreement_replay; eauto.
    + eapply IH; eauto.
Qed.
