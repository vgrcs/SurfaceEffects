From Stdlib Require Import List.
From stdpp Require Import list.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Core.Values.
Require Import theories.SmallStep.Runtime.HeapFacts.
Require Import theories.SmallStep.Runtime.HeapNeutral.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Runtime.NoAllocPreservation.
Require Import theories.SmallStep.Runtime.RegularPreservation.
Require Import theories.SmallStep.Runtime.RegularStateShape.
Require Import theories.SmallStep.Runtime.Trace.
Require Import theories.SmallStep.Runtime.TraceView.
Require Import theories.SmallStep.Runtime.Typing.
Require Import theories.SmallStep.Typing.Judgments.
Require Import theories.SmallStep.Typing.Regularity.
Require Import theories.SmallStep.Typing.Resolve.
Require Import theories.SmallStep.Typing.Types.
Require Import theories.SmallStep.Determinism.Terminal.
Require Import theories.SmallStep.Soundness.Correctness.
Require Import theories.SmallStep.Soundness.Dispatcher.
Require Import theories.SmallStep.Soundness.PairPar.
Require Import theories.SmallStep.Soundness.StaticEffect.

Import ListNotations.

Definition StateNotError (state : State) : Prop :=
  match state with
  | StError _ => False
  | _ => True
  end.

Definition TracePermutation (phi1 phi2 : Trace) : Prop :=
  phi1 ≡ₚ phi2.

Definition NoAllocTraceView (view : TraceView) : Prop :=
  NoAllocTrace (trace_view_flatten view).

Definition HeapNeutralTraceView (view : TraceView) : Prop :=
  HeapNeutralTrace (trace_view_flatten view).

Definition HeapFootprint : Type :=
  RegionId -> Location -> Prop.

Definition HeapEqOn
    (footprint : HeapFootprint) (heap1 heap2 : Heap) : Prop :=
  forall r l,
    footprint r l ->
    heap_lookup r l heap1 = heap_lookup r l heap2.

Definition TraceReads (phi : Trace) : HeapFootprint :=
  fun r l => In (DRead r l) phi.

Definition TraceWrites (phi : Trace) : HeapFootprint :=
  fun r l => In (DWrite r l) phi.

Definition TraceTouches (phi : Trace) : HeapFootprint :=
  fun r l =>
    In (DAlloc r l) phi \/
    In (DRead r l) phi \/
    In (DWrite r l) phi.

Definition HeapEqOnTrace (phi : Trace) : Heap -> Heap -> Prop :=
  HeapEqOn (TraceTouches phi).

Definition HeapEqOnTraceView
    (view : TraceView) : Heap -> Heap -> Prop :=
  HeapEqOnTrace (trace_view_flatten view).

Lemma HeapEqOn_refl :
  forall footprint heap,
    HeapEqOn footprint heap heap.
Proof.
  intros footprint heap r l _HIn.
  reflexivity.
Qed.

Lemma HeapEqOn_sym :
  forall footprint heap1 heap2,
    HeapEqOn footprint heap1 heap2 ->
    HeapEqOn footprint heap2 heap1.
Proof.
  intros footprint heap1 heap2 HEq r l HIn.
  symmetry.
  apply HEq.
  exact HIn.
Qed.

Lemma HeapEqOn_trans :
  forall footprint heap1 heap2 heap3,
    HeapEqOn footprint heap1 heap2 ->
    HeapEqOn footprint heap2 heap3 ->
    HeapEqOn footprint heap1 heap3.
Proof.
  intros footprint heap1 heap2 heap3 HEq12 HEq23 r l HIn.
  rewrite HEq12 by exact HIn.
  apply HEq23.
  exact HIn.
Qed.

Lemma HeapEqOn_weaken :
  forall footprint_small footprint_big heap1 heap2,
    (forall r l, footprint_small r l -> footprint_big r l) ->
    HeapEqOn footprint_big heap1 heap2 ->
    HeapEqOn footprint_small heap1 heap2.
Proof.
  intros footprint_small footprint_big heap1 heap2 HIncl HEq r l HIn.
  apply HEq.
  eapply HIncl.
  exact HIn.
Qed.

Lemma HeapEqOn_from_heap_eq :
  forall footprint heap1 heap2,
    heap1 = heap2 ->
    HeapEqOn footprint heap1 heap2.
Proof.
  intros footprint heap1 heap2 HHeap.
  subst heap2.
  apply HeapEqOn_refl.
Qed.

Corollary Steps_error_heap_footprint_deterministic :
  forall footprint state phi1 heap1 phi2 heap2,
    Steps state phi1 (StError heap1) ->
    Steps state phi2 (StError heap2) ->
    phi1 = phi2 /\ HeapEqOn footprint heap1 heap2.
Proof.
  intros footprint state phi1 heap1 phi2 heap2 HSteps1 HSteps2.
  destruct
    (Steps_error_trace_deterministic
      state phi1 heap1 phi2 heap2 HSteps1 HSteps2)
    as (HPhi & HHeap).
  subst heap2.
  split.
  - exact HPhi.
  - apply HeapEqOn_refl.
Qed.

Corollary Steps_error_heap_trace_footprint_deterministic :
  forall state phi1 heap1 phi2 heap2,
    Steps state phi1 (StError heap1) ->
    Steps state phi2 (StError heap2) ->
    phi1 = phi2 /\ HeapEqOnTrace phi1 heap1 heap2.
Proof.
  intros state phi1 heap1 phi2 heap2 HSteps1 HSteps2.
  eapply Steps_error_heap_footprint_deterministic; eauto.
Qed.


Definition SchedulerTraceRepresentsViews
    (phi : Trace) (view_left view_right : TraceView) : Prop :=
  TracePermutation phi (trace_view_flatten (TracePar view_left view_right)).

Lemma TracePar_flatten_canonical :
  forall view_left view_right,
    trace_view_flatten (TracePar view_left view_right) =
    trace_view_flatten view_left ++ trace_view_flatten view_right.
Proof.
  reflexivity.
Qed.

Lemma SchedulerTraceRepresentsViews_canonical :
  forall view_left view_right,
    SchedulerTraceRepresentsViews
      (trace_view_flatten view_left ++ trace_view_flatten view_right)
      view_left
      view_right.
Proof.
  intros view_left view_right.
  unfold SchedulerTraceRepresentsViews, TracePermutation.
  simpl.
  reflexivity.
Qed.

Lemma heap_update_update_commute_distinct :
  forall heap r1 l1 v1 r2 l2 v2,
    r1 <> r2 \/ l1 <> l2 ->
    heap_update r1 l1 v1 (heap_update r2 l2 v2 heap) =
    heap_update r2 l2 v2 (heap_update r1 l1 v1 heap).
Proof.
  induction heap as [| [[r0 l0] v0] heap IH];
    intros r1 l1 v1 r2 l2 v2 HDistinct; simpl.
  - reflexivity.
  - destruct (Nat.eqb r1 r0 && Nat.eqb l1 l0) eqn:H1;
      destruct (Nat.eqb r2 r0 && Nat.eqb l2 l0) eqn:H2; simpl.
    + exfalso.
      apply andb_true_iff in H1.
      apply andb_true_iff in H2.
      destruct H1 as (HR1 & HL1).
      destruct H2 as (HR2 & HL2).
      apply Nat.eqb_eq in HR1.
      apply Nat.eqb_eq in HL1.
      apply Nat.eqb_eq in HR2.
      apply Nat.eqb_eq in HL2.
      subst.
      destruct HDistinct as [HDistinct | HDistinct]; contradiction.
    + rewrite H1.
      simpl.
      rewrite H2.
      reflexivity.
    + rewrite H1.
      simpl.
      rewrite H2.
      reflexivity.
    + rewrite H1, H2.
      simpl.
      f_equal.
      apply IH.
      exact HDistinct.
Qed.

Lemma Step_noalloc_preserves_lookup_none_aligned :
  forall state label state' r_lookup l_lookup,
    Step state label state' ->
    StateHeapsAligned state ->
    NoAllocTrace (label_trace label) ->
    heap_lookup r_lookup l_lookup (state_heap state) = None ->
    heap_lookup r_lookup l_lookup (state_heap state') = None.
Proof.
  intros state label state' r_lookup l_lookup HStep.
  induction HStep; intros HAligned HNoAlloc HLookup; simpl in *;
    try solve [assumption].
  - destruct HAligned as (HAlignedLeft & _ & _).
    eapply IHHStep; eauto.
  - destruct HAligned as (_ & HAlignedRight & HHeapAligned).
    eapply IHHStep; eauto.
    rewrite <- HHeapAligned.
    exact HLookup.
  - destruct HAligned as (_ & _ & HHeapAligned).
    rewrite <- HHeapAligned.
    exact HLookup.
  - exfalso.
    eapply HNoAlloc.
    simpl. left. reflexivity.
  - destruct (Nat.eq_dec r r_lookup) as [-> | HRegionNeq].
    + destruct (Nat.eq_dec l l_lookup) as [-> | HLocationNeq].
      * clear HNoAlloc.
        induction heap as [| [[r0 l0] v0] heap IH]; simpl in *.
        -- reflexivity.
        -- destruct (Nat.eqb r_lookup r0 && Nat.eqb l_lookup l0)
             eqn:HEq; [discriminate |].
           simpl.
           rewrite HEq.
           exact (IH HLookup).
      * rewrite heap_update_lookup_other by (right; exact HLocationNeq).
        exact HLookup.
    + rewrite heap_update_lookup_other by (left; exact HRegionNeq).
        exact HLookup.
Qed.

Lemma Step_noalloc_lookup_preserved_without_write_aligned :
  forall state label state' r_lookup l_lookup,
    Step state label state' ->
    StateHeapsAligned state ->
    HeapKeysBounded (state_heap state) ->
    NoAllocTrace (label_trace label) ->
    TraceDoesNotWrite r_lookup l_lookup (label_trace label) ->
    heap_lookup r_lookup l_lookup (state_heap state') =
    heap_lookup r_lookup l_lookup (state_heap state).
Proof.
  intros state label state' r_lookup l_lookup
    HStep HAligned HBounded HNoAlloc HNoWrite.
  destruct
    (heap_lookup r_lookup l_lookup (state_heap state))
    as [cell |] eqn:HLookup.
  - eapply Step_lookup_preserved_without_write_aligned; eauto.
  - eapply Step_noalloc_preserves_lookup_none_aligned; eauto.
Qed.

Lemma Step_noalloc_heap_eq_on_unwritten_aligned :
  forall state label state',
    Step state label state' ->
    StateHeapsAligned state ->
    HeapKeysBounded (state_heap state) ->
    NoAllocTrace (label_trace label) ->
    HeapEqOn
      (fun r l => TraceDoesNotWrite r l (label_trace label))
      (state_heap state')
      (state_heap state).
Proof.
  intros state label state' HStep HAligned HBounded HNoAlloc
    r l HNoWrite.
  eapply Step_noalloc_lookup_preserved_without_write_aligned; eauto.
Qed.

Lemma Steps_noalloc_heap_eq_on_unwritten_aligned :
  forall state phi state',
    Steps state phi state' ->
    StateHeapsAligned state ->
    HeapKeysBounded (state_heap state) ->
    NoAllocTrace phi ->
    HeapEqOn
      (fun r l => TraceDoesNotWrite r l phi)
      (state_heap state')
      (state_heap state).
Proof.
  intros state phi state' HSteps.
  induction HSteps as
    [state | state label state1 phi state2 HStep _ IH];
    intros HAligned HBounded HNoAlloc r l HNoWrite.
  - reflexivity.
  - pose proof
      (no_alloc_trace_app_l
        (label_trace label) phi HNoAlloc)
      as HNoAllocLabel.
    pose proof
      (no_alloc_trace_app_r
        (label_trace label) phi HNoAlloc)
      as HNoAllocTail.
    pose proof
      (trace_does_not_write_app_l
        r l (label_trace label) phi HNoWrite)
      as HNoWriteLabel.
    pose proof
      (trace_does_not_write_app_r
        r l (label_trace label) phi HNoWrite)
      as HNoWriteTail.
    pose proof
      (Step_preserves_alignment
        state label state1 HStep HAligned)
      as HAligned1.
    pose proof
      (Step_preserves_heap_bounded_aligned
        state label state1 HStep HAligned HBounded)
      as HBounded1.
    rewrite
      (IH HAligned1 HBounded1 HNoAllocTail r l HNoWriteTail).
    eapply Step_noalloc_lookup_preserved_without_write_aligned; eauto.
Qed.

Lemma StepsN_noalloc_read_agreement_terminal_replay :
  forall n state phi heap_final value heap_replay,
    StepsN n state phi (StDone heap_final value) ->
    StateHeapsAligned state ->
    NoAllocTrace phi ->
    TraceReadHeapAgreement phi (state_heap state) heap_replay ->
    exists heap_final_replay,
      StepsN n
        (with_state_heap heap_replay state)
        phi
        (StDone heap_final_replay value).
Proof.
  assert
    (HStepReplay :
      forall state label state' heap_replay phi_tail,
        Step state label state' ->
        StateHeapsAligned state ->
        NoAllocTrace (label_trace label) ->
        TraceReadHeapAgreement
          (label_trace label ++ phi_tail)
          (state_heap state)
          heap_replay ->
        exists heap_replay',
          Step
            (with_state_heap heap_replay state)
            label
            (with_state_heap heap_replay' state') /\
          TraceReadHeapAgreement
            phi_tail
            (state_heap state')
            heap_replay').
  {
    intros state label state' heap_replay phi_tail HStep.
    induction HStep; intros HAligned HNoAlloc HAgree; simpl in *.
    all: try solve [
        exists heap_replay;
        split;
        [ econstructor; eauto
        | intros r l cell HRead HLookup;
          eapply HAgree;
          [ exact HRead
          | exact HLookup ] ] ].
    - destruct HAligned as (HAlignedLeft & _ & _).
      destruct
        (IHHStep HAlignedLeft HNoAlloc HAgree)
        as (heap_replay' & HStepReplayed & HAgreeTail).
      exists heap_replay'.
      split.
      + simpl.
        rewrite with_state_heap_twice.
        replace
          (with_state_heap heap_replay' right_state)
          with
          (with_state_heap
            (state_heap (with_state_heap heap_replay' left_state'))
            (with_state_heap heap_replay right_state)).
        * apply StepPairParRunLeft.
          exact HStepReplayed.
        * rewrite state_heap_with_state_heap.
          rewrite with_state_heap_twice.
          reflexivity.
      + exact HAgreeTail.
    - destruct HAligned as (_ & HAlignedRight & HHeapAligned).
      assert
        (HAgreeRight :
          TraceReadHeapAgreement
            (label_trace label ++ phi_tail)
            (state_heap right_state)
            heap_replay).
      {
        intros r l cell HRead HLookup.
        eapply HAgree.
        - exact HRead.
        - rewrite HHeapAligned.
          exact HLookup.
      }
      destruct
        (IHHStep HAlignedRight HNoAlloc HAgreeRight)
        as (heap_replay' & HStepReplayed & HAgreeTail).
      exists heap_replay'.
      split.
      + simpl.
        replace
          (StDone heap_replay' v1)
          with
          (with_state_heap
            (state_heap (with_state_heap heap_replay' right_state'))
            (StDone heap_replay v1)).
        * apply StepPairParRunRight.
          exact HStepReplayed.
        * rewrite state_heap_with_state_heap.
          reflexivity.
      + exact HAgreeTail.
    - destruct HAligned as (_ & _ & HHeapAligned).
      exists heap_replay.
      split.
      + simpl. apply StepPairParRunRightError.
      + intros r l cell HRead HLookup.
        eapply HAgree.
        * exact HRead.
        * rewrite HHeapAligned.
          exact HLookup.
    - exists heap_replay.
      split.
      + apply StepRgnApp.
      + exact HAgree.
    - exists heap_replay.
      split.
      + eapply StepRgnAppReturn.
        exact H.
      + exact HAgree.
    - exists heap_replay.
      split.
      + eapply StepRef.
        exact H.
      + exact HAgree.
    - exfalso.
      apply (HNoAlloc r_val l).
      simpl. auto.
    - exists heap_replay.
      split.
      + apply StepDeref.
      + exact HAgree.
    - exists heap_replay.
      split.
      + simpl.
        apply StepDerefReturn.
        eapply HAgree.
        * simpl. left. reflexivity.
        * exact H.
      + intros r0 l0 cell HRead HLookup.
        eapply HAgree.
        * simpl. right. exact HRead.
        * exact HLookup.
    - exists heap_replay.
      split.
      + apply StepAssign.
      + exact HAgree.
    - exists heap_replay.
      split.
      + apply StepAssignLoc.
      + exact HAgree.
    - exists (heap_update r l v heap_replay).
      split.
      + simpl. apply StepAssignVal.
      + intros r_read l_read cell HRead HLookup.
        destruct (Nat.eq_dec r r_read) as [HRegionEq | HRegionNeq].
        * destruct (Nat.eq_dec l l_read) as [HLocationEq | HLocationNeq].
          -- subst r_read l_read.
             destruct (heap_lookup r l heap) as [old |] eqn:HLookupBefore.
             ++ assert
                  (HReplayBefore :
                    heap_lookup r l heap_replay = Some old).
                {
                  eapply HAgree.
                  - simpl. right. exact HRead.
                  - exact HLookupBefore.
                }
                rewrite heap_update_lookup_same
                  by (rewrite HReplayBefore; discriminate).
                rewrite heap_update_lookup_same in HLookup
                  by (rewrite HLookupBefore; discriminate).
                inversion HLookup; subst.
                reflexivity.
             ++ pose proof
                  (Step_noalloc_preserves_lookup_none_aligned
                    (StReturn heap v (KAssignVal r_static (VLoc r l) k))
                    (LAction (DWrite r l))
                    (StReturn (heap_update r l v heap) VUnit k)
                    r
                    l
                    (StepAssignVal heap r_static r l v k)
                    I
                    HNoAlloc
                    HLookupBefore)
                  as HLookupAfterNone.
                simpl in HLookupAfterNone.
                rewrite HLookup in HLookupAfterNone.
                discriminate.
          -- rewrite heap_update_lookup_other
               by (right; exact HLocationNeq).
             rewrite heap_update_lookup_other in HLookup
               by (right; exact HLocationNeq).
             eapply HAgree.
             ++ simpl. right. exact HRead.
             ++ exact HLookup.
        * rewrite heap_update_lookup_other
             by (left; exact HRegionNeq).
          rewrite heap_update_lookup_other in HLookup
             by (left; exact HRegionNeq).
          eapply HAgree.
          -- simpl. right. exact HRead.
          -- exact HLookup.
    - exists heap_replay.
      split.
      + eapply StepAllocAbs.
        exact H.
      + exact HAgree.
    - exists heap_replay.
      split.
      + eapply StepReadAbs.
        exact H.
      + exact HAgree.
    - exists heap_replay.
      split.
      + eapply StepWriteAbs.
        exact H.
      + exact HAgree.
    - exists heap_replay.
      split.
      + apply StepReadConcReturn.
      + exact HAgree.
    - exists heap_replay.
      split.
      + apply StepWriteConcReturn.
      + exact HAgree.
    all: try solve [
      exists heap_replay;
      split;
      [ econstructor; eauto
      | exact HAgree ] ].
  }
  intros n state phi heap_final value heap_replay HSteps.
  remember (StDone heap_final value) as final_state eqn:HFinal.
  revert heap_final value heap_replay HFinal.
  induction HSteps as
    [state
    | n state label state1 phi state2 HStep _ IH];
    intros heap_final value heap_replay HFinal HAligned HNoAlloc HAgree.
  - inversion HFinal; subst.
    simpl.
    exists heap_replay.
    constructor.
  - pose proof
      (no_alloc_trace_app_l
        (label_trace label) phi HNoAlloc)
      as HNoAllocLabel.
    pose proof
      (no_alloc_trace_app_r
        (label_trace label) phi HNoAlloc)
      as HNoAllocTail.
    destruct
      (HStepReplay
        state label state1 heap_replay phi
        HStep HAligned HNoAllocLabel HAgree)
      as (heap_replay' & HStepReplayed & HAgreeTail).
    pose proof
      (Step_preserves_alignment
        state label state1 HStep HAligned)
      as HAligned1.
    destruct
      (IH heap_final value heap_replay' HFinal
        HAligned1 HNoAllocTail HAgreeTail)
      as (heap_final_replay & HStepsTail).
    exists heap_final_replay.
    eapply StepsNStep; eauto.
Qed.

Lemma Step_noalloc_disjoint_read_agreement_reverse :
  forall state label state' phi_read,
    Step state label state' ->
    StateHeapsAligned state ->
    HeapKeysBounded (state_heap state) ->
    NoAllocTrace (label_trace label) ->
    TraceDisjoint (label_trace label) phi_read ->
    TraceReadHeapAgreement
      phi_read (state_heap state') (state_heap state).
Proof.
  intros state label state' phi_read HStep.
  induction HStep; intros HAligned HBounded HNoAlloc HDisjoint
    r_read l_read cell HRead HLookup; simpl in *;
    try solve [exact HLookup].
  - destruct HAligned as (HAlignedLeft & _ & _).
    eapply IHHStep; eauto.
  - destruct HAligned as (_ & HAlignedRight & HHeapAligned).
    rewrite HHeapAligned.
    eapply IHHStep; eauto.
    rewrite <- HHeapAligned.
    exact HBounded.
  - destruct HAligned as (_ & _ & HHeapAligned).
    rewrite HHeapAligned.
    exact HLookup.
  - exfalso.
    eapply HNoAlloc.
    simpl. left. reflexivity.
  - destruct (Nat.eq_dec r r_read) as [-> | HRegionNeq].
    + destruct (Nat.eq_dec l l_read) as [-> | HLocationNeq].
      * exfalso.
        specialize
          (HDisjoint
            (DWrite r_read l_read)
            (DRead r_read l_read)
            (or_introl eq_refl)
            HRead).
        apply HDisjoint.
        constructor. split; reflexivity.
      * rewrite heap_update_lookup_other in HLookup
          by (right; exact HLocationNeq).
        exact HLookup.
    + rewrite heap_update_lookup_other in HLookup
        by (left; exact HRegionNeq).
      exact HLookup.
Qed.

Lemma Step_disjoint_noalloc_local_diamond_reheap :
  forall state label state' other other_label other',
    state_heap state = state_heap other ->
    StateHeapsAligned state ->
    StateHeapsAligned other ->
    HeapKeysBounded (state_heap state) ->
    Step state label state' ->
    Step other other_label other' ->
    NoAllocTrace (label_trace label) ->
    NoAllocTrace (label_trace other_label) ->
    TraceDisjoint (label_trace label) (label_trace other_label) ->
    TraceDisjoint (label_trace other_label) (label_trace label) ->
    exists heap_state_after heap_other_after,
      Step
        (with_state_heap (state_heap other') state)
        label
        (with_state_heap heap_state_after state') /\
      Step
        (with_state_heap (state_heap state') other)
        other_label
        (with_state_heap heap_other_after other') /\
      heap_state_after = heap_other_after.
Proof.
  assert
    (HHeapNeutralDiamond :
      forall state label state' other other_label other',
        state_heap state = state_heap other ->
        StateHeapsAligned state ->
        StateHeapsAligned other ->
        HeapKeysBounded (state_heap state) ->
        Step state label state' ->
        Step other other_label other' ->
        HeapNeutralTrace (label_trace label) ->
        TraceDisjoint (label_trace label) (label_trace other_label) ->
        TraceDisjoint (label_trace other_label) (label_trace label) ->
        exists heap_state_after heap_other_after,
          Step
            (with_state_heap (state_heap other') state)
            label
            (with_state_heap heap_state_after state') /\
          Step
            (with_state_heap (state_heap state') other)
            other_label
            (with_state_heap heap_other_after other') /\
          heap_state_after = heap_other_after).
  {
    intros state label state' other other_label other'
      HHeapAligned HAlignedState HAlignedOther HBounded
      HStep HOther HNeutral HDisjoint _HDisjointSym.
    assert
      (HReadAgreement :
        TraceReadHeapAgreement
          (label_trace label)
          (state_heap state)
          (state_heap other')).
    {
      intros r l cell HRead HLookup.
      eapply Step_lookup_preserved_without_write_aligned.
      - exact HOther.
      - exact HAlignedOther.
      - rewrite <- HHeapAligned.
        exact HBounded.
      - rewrite <- HHeapAligned.
        exact HLookup.
      - eapply TraceDisjoint_right_read_no_left_write; eauto.
    }
    pose proof
      (Step_heap_neutral_read_agreement_replay
        state label state' (state_heap other')
        HStep HAlignedState HNeutral HReadAgreement)
      as HReplayedState.
    destruct
      (Step_heap_neutral_preserves_alignment
        state label state' HStep HAlignedState HNeutral)
      as (_HAlignedState' & HHeapState').
    assert (HOtherSame :
      with_state_heap (state_heap state') other = other).
    {
      eapply with_state_heap_aligned_same.
      - exact HAlignedOther.
      - rewrite HHeapState'.
        symmetry. exact HHeapAligned.
    }
    pose proof
      (Step_preserves_alignment
        other other_label other' HOther HAlignedOther)
      as HAlignedOther'.
    exists (state_heap other'), (state_heap other').
    split; [exact HReplayedState |].
    split.
    - rewrite HOtherSame.
      rewrite (with_state_heap_state_heap_aligned other' HAlignedOther').
      exact HOther.
    - reflexivity.
  }
  assert
    (HWriteDiamond :
      forall state r_write l_write state' other other_label other',
        state_heap state = state_heap other ->
        StateHeapsAligned state ->
        StateHeapsAligned other ->
        HeapKeysBounded (state_heap state) ->
        Step state (LAction (DWrite r_write l_write)) state' ->
        Step other other_label other' ->
        NoAllocTrace (label_trace other_label) ->
        TraceDisjoint
          (label_trace (LAction (DWrite r_write l_write)))
          (label_trace other_label) ->
        TraceDisjoint
          (label_trace other_label)
          (label_trace (LAction (DWrite r_write l_write))) ->
        exists heap_state_after heap_other_after,
          Step
            (with_state_heap (state_heap other') state)
            (LAction (DWrite r_write l_write))
            (with_state_heap heap_state_after state') /\
          Step
            (with_state_heap (state_heap state') other)
            other_label
            (with_state_heap heap_other_after other') /\
          heap_state_after = heap_other_after).
  {
    intros state r_write l_write state' other other_label other'
      HHeapAligned HAlignedState HAlignedOther HBounded
      HStep.
    remember (LAction (DWrite r_write l_write)) as label
      eqn:HLabel.
    revert r_write l_write HLabel other other_label other'
      HHeapAligned HAlignedState HAlignedOther HBounded.
    induction HStep; intros r_write l_write HLabel other0 other_label0
      other'0 HHeapAligned HAlignedState HAlignedOther HBounded
      HOther HNoAllocOther HDisjoint HDisjointSym;
      inversion HLabel; subst; simpl in *.
    - destruct HAlignedState as
        (HAlignedLeft & HAlignedRight & HHeapLeftRight).
      destruct
        (IHHStep
          r_write l_write eq_refl
          other0 other_label0 other'0
          HHeapAligned
          HAlignedLeft
          HAlignedOther
          HBounded
          HOther
          HNoAllocOther
          HDisjoint
          HDisjointSym)
        as (heap_left_after & heap_other_after &
          HLeftAfter & HOtherAfter & HHeapAfter).
      exists heap_left_after, heap_other_after.
      split.
      + simpl.
        rewrite with_state_heap_twice.
        replace (with_state_heap heap_left_after right_state) with
          (with_state_heap
            (state_heap (with_state_heap heap_left_after left_state'))
            (with_state_heap (state_heap other'0) right_state))
          by (rewrite state_heap_with_state_heap, with_state_heap_twice;
              reflexivity).
        eapply StepPairParRunLeft.
        exact HLeftAfter.
      + split; [exact HOtherAfter |].
        exact HHeapAfter.
    - destruct HAlignedState as
        (_HAlignedDone & HAlignedRight & HHeapDoneRight).
      assert (HHeapRightOther : state_heap right_state = state_heap other0).
      {
        rewrite <- HHeapDoneRight.
        exact HHeapAligned.
      }
      assert (HBoundedRight : HeapKeysBounded (state_heap right_state)).
      {
        rewrite <- HHeapDoneRight.
        exact HBounded.
      }
      destruct
        (IHHStep
          r_write l_write eq_refl
          other0 other_label0 other'0
          HHeapRightOther
          HAlignedRight
          HAlignedOther
          HBoundedRight
          HOther
          HNoAllocOther
          HDisjoint
          HDisjointSym)
        as (heap_right_after & heap_other_after &
          HRightAfter & HOtherAfter & HHeapAfter).
      exists heap_right_after, heap_other_after.
      split.
      + simpl.
        replace (StDone heap_right_after v1) with
          (with_state_heap
            (state_heap (with_state_heap heap_right_after right_state'))
            (StDone (state_heap other'0) v1))
          by (rewrite state_heap_with_state_heap; reflexivity).
        eapply StepPairParRunRight.
        exact HRightAfter.
      + split; [exact HOtherAfter |].
        exact HHeapAfter.
    - destruct other_label0 as [| other_action].
      + destruct
          (HHeapNeutralDiamond
            other0 LSilent other'0
            (StReturn heap v (KAssignVal r_static (VLoc r_write l_write) k))
            (LAction (DWrite r_write l_write))
            (StReturn (heap_update r_write l_write v heap) VUnit k))
          as (heap_other_after & heap_state_after &
            HOtherAfter & HStateAfter & HHeapAfter).
        * symmetry. exact HHeapAligned.
        * exact HAlignedOther.
        * exact I.
        * rewrite <- HHeapAligned.
          exact HBounded.
        * exact HOther.
        * apply StepAssignVal.
        * split; simpl; intros ? ? HIn; contradiction.
        * exact HDisjointSym.
        * exact HDisjoint.
        * exists heap_state_after, heap_other_after.
          split; [exact HStateAfter |].
          split; [exact HOtherAfter |].
          symmetry. exact HHeapAfter.
      + destruct other_action as [r_alloc l_alloc | r_read l_read | r_other l_other].
        * exfalso.
          eapply HNoAllocOther.
          simpl. left. reflexivity.
        * assert (HOtherNeutral :
            HeapNeutralTrace (label_trace (LAction (DRead r_read l_read)))).
          {
            simpl.
            split.
            - intros r0 l0 HIn.
              destruct HIn as [HIn | HIn]; [inversion HIn | contradiction].
            - intros r0 l0 HIn.
              destruct HIn as [HIn | HIn]; [inversion HIn | contradiction].
          }
          destruct
            (HHeapNeutralDiamond
              other0
              (LAction (DRead r_read l_read))
              other'0
              (StReturn heap v (KAssignVal r_static (VLoc r_write l_write) k))
              (LAction (DWrite r_write l_write))
              (StReturn (heap_update r_write l_write v heap) VUnit k))
            as (heap_other_after & heap_state_after &
              HOtherAfter & HStateAfter & HHeapAfter).
          -- symmetry. exact HHeapAligned.
          -- exact HAlignedOther.
          -- exact I.
          -- rewrite <- HHeapAligned.
             exact HBounded.
          -- exact HOther.
          -- apply StepAssignVal.
          -- exact HOtherNeutral.
          -- exact HDisjointSym.
          -- exact HDisjoint.
          -- exists heap_state_after, heap_other_after.
             split; [exact HStateAfter |].
             split; [exact HOtherAfter |].
             symmetry. exact HHeapAfter.
        * assert
            (HOtherWrite :
              exists heap_state_after heap_other_after,
		                Step
		                  (with_state_heap (state_heap other'0)
		                    (StReturn heap v (KAssignVal r_static (VLoc r_write l_write) k)))
		                  (LAction (DWrite r_write l_write))
		                  (with_state_heap
                        heap_state_after
		                    (StReturn
                          (heap_update r_write l_write v heap)
                          VUnit
                          k)) /\
		                Step
		                  (with_state_heap
		                    (state_heap
		                      (StReturn (heap_update r_write l_write v heap) VUnit k))
		                    other0)
                  (LAction (DWrite r_other l_other))
                  (with_state_heap heap_other_after other'0) /\
                heap_state_after = heap_other_after).
          {
            remember (LAction (DWrite r_other l_other)) as other_write_label
              eqn:HOtherLabel.
            revert r_other l_other HOtherLabel HHeapAligned HAlignedOther
              HBounded HNoAllocOther HDisjoint HDisjointSym.
            induction HOther; intros r_other l_other HOtherLabel
              HHeapAligned0 HAlignedOther0 HBounded0 HNoAllocOther0
              HDisjoint0 HDisjointSym0;
              inversion HOtherLabel; subst; simpl in *.
            - destruct HAlignedOther0 as
                (HAlignedOtherLeft & HAlignedOtherRight & _).
              destruct
	                (IHHOther
	                  r_other l_other eq_refl
	                  ltac:(assumption || reflexivity || congruence)
	                  HAlignedOtherLeft
	                  HBounded0
	                  HNoAllocOther0
                  HDisjoint0
                  HDisjointSym0)
		                as (heap_state_after & heap_left_after &
		                  HStateAfter & HLeftAfter & HHeapAfter).
		              exists heap_state_after, heap_left_after.
	              split; [exact HStateAfter |].
	              split.
	              + simpl.
                  rewrite with_state_heap_twice.
                  replace (with_state_heap heap_left_after right_state) with
                    (with_state_heap
                      (state_heap (with_state_heap heap_left_after left_state'))
                      (with_state_heap
                        (heap_update
                          r_write
                          l_write
                          v
                          (state_heap left_state))
                        right_state))
                    by (rewrite state_heap_with_state_heap,
                          with_state_heap_twice; reflexivity).
                  eapply StepPairParRunLeft.
	                exact HLeftAfter.
	              + exact HHeapAfter.
	            - destruct HAlignedOther0 as
	                (_HAlignedOtherDone & HAlignedOtherRight &
	                  HHeapOtherDoneRight).
	              destruct
	                (IHHOther
	                  r_other l_other eq_refl
	                  HHeapOtherDoneRight
	                  HAlignedOtherRight
	                  HBounded0
	                  HNoAllocOther0
                  HDisjoint0
                  HDisjointSym0)
	                as (heap_state_after & heap_right_after &
	                  HStateAfter & HRightAfter & HHeapAfter).
	              exists heap_state_after, heap_right_after.
	              split; [exact HStateAfter |].
		              split.
		              + simpl.
	                  replace (StDone heap_right_after v1) with
                      (with_state_heap
                        (state_heap
                          (with_state_heap heap_right_after right_state'))
                        (StDone
                          (heap_update r_write l_write v heap0)
                          v1))
                      by (rewrite state_heap_with_state_heap; reflexivity).
	                  eapply StepPairParRunRight.
		                exact HRightAfter.
		              + exact HHeapAfter.
	            - assert
	                (HDistinct :
	                  r_write <> r_other \/ l_write <> l_other).
	              {
	                destruct (Nat.eq_dec r_write r_other)
	                  as [HRegionEq | HRegionNeq].
	                - destruct (Nat.eq_dec l_write l_other)
	                    as [HLocEq | HLocNeq].
	                  + exfalso.
	                    subst r_other l_other.
	                    specialize
	                      (HDisjoint0
	                        (DWrite r_write l_write)
	                        (DWrite r_write l_write)
	                        (or_introl eq_refl)
	                        (or_introl eq_refl)).
                    apply HDisjoint0.
                    constructor. split; reflexivity.
                  + right. exact HLocNeq.
                - left. exact HRegionNeq.
              }
		              exists
		                (heap_update
		                  r_write
		                  l_write
		                  v
		                  (heap_update r_other l_other v0 heap0)),
		                (heap_update
		                  r_other
		                  l_other
		                  v0
		                  (heap_update r_write l_write v heap0)).
              split.
              + simpl.
                apply StepAssignVal.
              + split.
                * simpl.
                  apply StepAssignVal.
	                * apply heap_update_update_commute_distinct.
                    exact HDistinct.
          }
          exact HOtherWrite.
  }
  intros state label state' other other_label other'
    HHeapAligned HAlignedState HAlignedOther HBounded
    HStep HOther HNoAlloc HNoAllocOther HDisjoint HDisjointSym.
  destruct label as [| action].
  - eapply HHeapNeutralDiamond; eauto.
    split; simpl; intros ? ? HIn; contradiction.
  - destruct action as [r_alloc l_alloc | r_read l_read | r_write l_write].
    + exfalso.
      eapply HNoAlloc.
      simpl. left. reflexivity.
    + assert (HNeutral :
        HeapNeutralTrace (label_trace (LAction (DRead r_read l_read)))).
      {
        simpl.
        split.
        - intros r l HIn.
          destruct HIn as [HIn | HIn]; [inversion HIn | contradiction].
        - intros r l HIn.
          destruct HIn as [HIn | HIn]; [inversion HIn | contradiction].
      }
      eapply HHeapNeutralDiamond; eauto.
    + eapply HWriteDiamond; eauto.
Qed.

Lemma StepsN_noalloc_disjoint_step_after_run :
  forall n left other other_label other'
    phi_left heap_after_other_left v_left,
    state_heap left = state_heap other ->
    StateHeapsAligned left ->
    StateHeapsAligned other ->
    HeapKeysBounded (state_heap left) ->
    Step other other_label other' ->
    StepsN n
      (with_state_heap (state_heap other') left)
      phi_left
      (StDone heap_after_other_left v_left) ->
    NoAllocTrace (label_trace other_label) ->
    NoAllocTrace phi_left ->
    TraceDisjoint (label_trace other_label) phi_left ->
    TraceDisjoint phi_left (label_trace other_label) ->
    exists heap_left heap_after_left_other,
      StepsN n left phi_left (StDone heap_left v_left) /\
      Step
        (with_state_heap heap_left other)
        other_label
        (with_state_heap heap_after_left_other other') /\
      heap_after_other_left = heap_after_left_other.
Proof.
  assert
    (HStepReadAgreementReplay :
      forall state label state' heap_replay,
        Step state label state' ->
        StateHeapsAligned state ->
        NoAllocTrace (label_trace label) ->
        TraceReadHeapAgreement
          (label_trace label)
          (state_heap state)
          heap_replay ->
        exists heap_replay',
          Step
            (with_state_heap heap_replay state)
            label
            (with_state_heap heap_replay' state')).
  {
    intros state label state' heap_replay HStep.
    induction HStep; intros HAligned HNoAlloc HAgree; simpl in *;
      try solve [
        exists heap_replay;
        econstructor; eauto ].
    - destruct HAligned as (HAlignedLeft & _ & _).
      destruct
        (IHHStep HAlignedLeft HNoAlloc HAgree)
        as (heap_replay' & HStepReplayed).
      exists heap_replay'.
      simpl.
      rewrite with_state_heap_twice.
      replace
        (with_state_heap heap_replay' right_state)
        with
        (with_state_heap
          (state_heap (with_state_heap heap_replay' left_state'))
          (with_state_heap heap_replay right_state)).
      + apply StepPairParRunLeft.
        exact HStepReplayed.
      + rewrite state_heap_with_state_heap.
        rewrite with_state_heap_twice.
        reflexivity.
    - destruct HAligned as (_ & HAlignedRight & HHeapAligned).
      assert
        (HAgreeRight :
          TraceReadHeapAgreement
            (label_trace label)
            (state_heap right_state)
            heap_replay).
      {
        intros r l cell HRead HLookup.
        eapply HAgree.
        - exact HRead.
        - rewrite HHeapAligned.
          exact HLookup.
      }
      destruct
        (IHHStep HAlignedRight HNoAlloc HAgreeRight)
        as (heap_replay' & HStepReplayed).
      exists heap_replay'.
      simpl.
      replace
        (StDone heap_replay' v1)
        with
        (with_state_heap
          (state_heap (with_state_heap heap_replay' right_state'))
          (StDone heap_replay v1)).
      + apply StepPairParRunRight.
        exact HStepReplayed.
      + rewrite state_heap_with_state_heap.
        reflexivity.
    - exfalso.
      eapply HNoAlloc.
      simpl. left. reflexivity.
    - exists heap_replay.
      simpl.
      apply StepDerefReturn.
      eapply HAgree.
      + simpl. left. reflexivity.
      + exact H.
    - exists (heap_update r l v heap_replay).
      simpl.
      apply StepAssignVal.
  }
  induction n as [| n IH];
    intros left other other_label other' phi_left
      heap_after_other_left v_left
      HHeapAligned HAlignedLeft HAlignedOther HBounded
      HOther HLeftAfterOther HNoAllocOther HNoAllocLeft
      HDisjointOtherLeft HDisjointLeftOther.
  - inversion HLeftAfterOther; subst.
    remember (state_heap left) as heap_left eqn:HHeapLeftState.
    destruct left as
      [heap env rho e k | heap v k | heap v
      | left_state right_state phi_left0 phi_right0 k | heap];
      simpl in *;
      match goal with
      | HDone : _ = StDone _ _ |- _ =>
          inversion HDone; subst heap_after_other_left v_left;
          clear HDone
      end.
    exists heap_left, (state_heap other').
    split.
    + rewrite HHeapLeftState.
      constructor.
    + split.
      * replace (with_state_heap heap_left other) with other.
        -- replace (with_state_heap (state_heap other') other') with other'.
           ++ exact HOther.
           ++ symmetry.
              apply with_state_heap_state_heap_aligned.
              eapply Step_preserves_alignment; eauto.
        -- symmetry.
           eapply with_state_heap_aligned_same.
           ++ exact HAlignedOther.
           ++ symmetry.
              exact HHeapAligned.
      * reflexivity.
  - inversion HLeftAfterOther; subst.
    match goal with
    | HStep : Step
        (with_state_heap (state_heap other') left) _ _ |- _ =>
        rename HStep into HStepScheduledHead
    end.
    match goal with
    | HTail : StepsN n _ _ (StDone heap_after_other_left v_left) |- _ =>
        rename HTail into HStepsTail
    end.
    pose proof
      (no_alloc_trace_app_l
        (label_trace label) phi HNoAllocLeft)
      as HNoAllocLabel.
    pose proof
      (no_alloc_trace_app_r
        (label_trace label) phi HNoAllocLeft)
      as HNoAllocTail.
    destruct
      (TraceDisjoint_app_r
        (label_trace other_label)
        (label_trace label)
        phi
        HDisjointOtherLeft)
      as (HDisjointOtherLabel & HDisjointOtherTail).
    destruct
      (TraceDisjoint_app_l
        (label_trace label)
        phi
        (label_trace other_label)
        HDisjointLeftOther)
      as (HDisjointLabelOther & HDisjointTailOther).
    assert
      (HAlignedStart :
        StateHeapsAligned
          (with_state_heap (state_heap other') left)).
    {
      destruct
        (with_state_heap_aligned
          (state_heap other') left HAlignedLeft)
        as (HAligned & _).
      exact HAligned.
    }
    assert
      (HReadBackLabel :
        TraceReadHeapAgreement
          (label_trace label)
          (state_heap
            (with_state_heap (state_heap other') left))
          (state_heap left)).
    {
      intros r l cell HRead HLookup.
      rewrite state_heap_with_state_heap in HLookup.
      rewrite HHeapAligned.
      eapply
        (Step_noalloc_disjoint_read_agreement_reverse
          other other_label other' (label_trace label)).
      - exact HOther.
      - exact HAlignedOther.
      - rewrite <- HHeapAligned.
        exact HBounded.
      - exact HNoAllocOther.
      - exact HDisjointOtherLabel.
      - exact HRead.
      - exact HLookup.
    }
    destruct
      (HStepReadAgreementReplay
        (with_state_heap (state_heap other') left)
        label
        state'
        (state_heap left)
        HStepScheduledHead
        HAlignedStart
        HNoAllocLabel
        HReadBackLabel)
      as (heap_left_head & HStepLeftReplayed).
    rewrite with_state_heap_twice in HStepLeftReplayed.
    rewrite (with_state_heap_state_heap_aligned left HAlignedLeft)
      in HStepLeftReplayed.
    set (left_head := with_state_heap heap_left_head state').
    assert (HStepLeft : Step left label left_head).
    {
      subst left_head.
      exact HStepLeftReplayed.
    }
    destruct
      (Step_disjoint_noalloc_local_diamond_reheap
        left label left_head other other_label other'
        HHeapAligned HAlignedLeft HAlignedOther HBounded
        HStepLeft HOther HNoAllocLabel HNoAllocOther
        HDisjointLabelOther HDisjointOtherLabel)
      as (heap_after_scheduled_head & heap_after_canonical_head &
        HStepScheduledDiamond & HStepOtherAfterHead & HHeapHead).
    subst heap_after_scheduled_head.
    destruct
      (Step_deterministic
        (with_state_heap (state_heap other') left)
        label
        state'
        label
        (with_state_heap heap_after_canonical_head left_head)
        HStepScheduledHead
        HStepScheduledDiamond)
      as (_ & HStateHead).
    rewrite HStateHead in HStepsTail.
    assert
      (HLeftTailAfterOtherHead' :
        StepsN n
          (with_state_heap
            (state_heap
              (with_state_heap heap_after_canonical_head other'))
            left_head)
          phi
          (StDone heap_after_other_left v_left)).
    {
      rewrite state_heap_with_state_heap.
      exact HStepsTail.
    }
    assert
      (HAlignedLeftHead : StateHeapsAligned left_head).
    {
      eapply Step_preserves_alignment; eauto.
    }
    assert
      (HBoundedLeftHead : HeapKeysBounded (state_heap left_head)).
    {
      eapply Step_preserves_heap_bounded_aligned; eauto.
    }
    assert
      (HAlignedOtherHead :
        StateHeapsAligned
          (with_state_heap (state_heap left_head) other)).
    {
      destruct
        (with_state_heap_aligned
          (state_heap left_head) other HAlignedOther)
        as (HAligned & _).
      exact HAligned.
    }
    destruct
      (IH
        left_head
        (with_state_heap (state_heap left_head) other)
        other_label
        (with_state_heap heap_after_canonical_head other')
        phi
        heap_after_other_left
        v_left)
      as (heap_left_tail & heap_after_left_other &
        HLeftTail & HOtherAfterTail & HHeapTail).
    + rewrite state_heap_with_state_heap.
      reflexivity.
    + exact HAlignedLeftHead.
    + exact HAlignedOtherHead.
    + exact HBoundedLeftHead.
    + exact HStepOtherAfterHead.
    + exact HLeftTailAfterOtherHead'.
    + exact HNoAllocOther.
    + exact HNoAllocTail.
    + exact HDisjointOtherTail.
    + exact HDisjointTailOther.
    + exists heap_left_tail, heap_after_left_other.
      split.
      * eapply StepsNStep.
        -- exact HStepLeft.
        -- exact HLeftTail.
	      * split.
	        -- repeat rewrite with_state_heap_twice in HOtherAfterTail.
	           exact HOtherAfterTail.
        -- exact HHeapTail.
Qed.

Lemma StepsN_noalloc_disjoint_step_after_run_error :
  forall n left other other_label other'
    phi_left heap_after_other_left,
    state_heap left = state_heap other ->
    StateHeapsAligned left ->
    StateHeapsAligned other ->
    HeapKeysBounded (state_heap left) ->
    Step other other_label other' ->
    StepsN n
      (with_state_heap (state_heap other') left)
      phi_left
      (StError heap_after_other_left) ->
    NoAllocTrace (label_trace other_label) ->
    NoAllocTrace phi_left ->
    TraceDisjoint (label_trace other_label) phi_left ->
    TraceDisjoint phi_left (label_trace other_label) ->
    exists heap_left_error heap_after_left_other,
      StepsN n left phi_left (StError heap_left_error) /\
      Step
        (with_state_heap heap_left_error other)
        other_label
        (with_state_heap heap_after_left_other other') /\
      heap_after_other_left = heap_after_left_other.
Proof.
  assert
    (HStepReadAgreementReplay :
      forall state label state' heap_replay,
        Step state label state' ->
        StateHeapsAligned state ->
        NoAllocTrace (label_trace label) ->
        TraceReadHeapAgreement
          (label_trace label)
          (state_heap state)
          heap_replay ->
        exists heap_replay',
          Step
            (with_state_heap heap_replay state)
            label
            (with_state_heap heap_replay' state')).
  {
    intros state label state' heap_replay HStep.
    induction HStep; intros HAligned HNoAlloc HAgree; simpl in *;
      try solve [
        exists heap_replay;
        econstructor; eauto ].
    - destruct HAligned as (HAlignedLeft & _ & _).
      destruct
        (IHHStep HAlignedLeft HNoAlloc HAgree)
        as (heap_replay' & HStepReplayed).
      exists heap_replay'.
      simpl.
      rewrite with_state_heap_twice.
      replace
        (with_state_heap heap_replay' right_state)
        with
        (with_state_heap
          (state_heap (with_state_heap heap_replay' left_state'))
          (with_state_heap heap_replay right_state)).
      + apply StepPairParRunLeft.
        exact HStepReplayed.
      + rewrite state_heap_with_state_heap.
        rewrite with_state_heap_twice.
        reflexivity.
    - destruct HAligned as (_ & HAlignedRight & HHeapAligned).
      assert
        (HAgreeRight :
          TraceReadHeapAgreement
            (label_trace label)
            (state_heap right_state)
            heap_replay).
      {
        intros r l cell HRead HLookup.
        eapply HAgree.
        - exact HRead.
        - rewrite HHeapAligned.
          exact HLookup.
      }
      destruct
        (IHHStep HAlignedRight HNoAlloc HAgreeRight)
        as (heap_replay' & HStepReplayed).
      exists heap_replay'.
      simpl.
      replace
        (StDone heap_replay' v1)
        with
        (with_state_heap
          (state_heap (with_state_heap heap_replay' right_state'))
          (StDone heap_replay v1)).
      + apply StepPairParRunRight.
        exact HStepReplayed.
      + rewrite state_heap_with_state_heap.
        reflexivity.
    - exfalso.
      eapply HNoAlloc.
      simpl. left. reflexivity.
    - exists heap_replay.
      simpl.
      apply StepDerefReturn.
      eapply HAgree.
      + simpl. left. reflexivity.
      + exact H.
    - exists (heap_update r l v heap_replay).
      simpl.
      apply StepAssignVal.
  }
  induction n as [| n IH];
    intros left other other_label other' phi_left
      heap_after_other_left
      HHeapAligned HAlignedLeft HAlignedOther HBounded
      HOther HLeftAfterOther HNoAllocOther HNoAllocLeft
      HDisjointOtherLeft HDisjointLeftOther.
  - inversion HLeftAfterOther; subst.
    remember (state_heap left) as heap_left eqn:HHeapLeftState.
    destruct left as
      [heap env rho e k | heap v k | heap v
      | left_state right_state phi_left0 phi_right0 k | heap];
      simpl in *;
      match goal with
      | HError : _ = StError _ |- _ =>
          inversion HError; subst heap_after_other_left;
          clear HError
      end.
    exists heap_left, (state_heap other').
    split.
    + rewrite HHeapLeftState.
      constructor.
    + split.
      * replace (with_state_heap heap_left other) with other.
        -- replace (with_state_heap (state_heap other') other') with other'.
           ++ exact HOther.
           ++ symmetry.
              apply with_state_heap_state_heap_aligned.
              eapply Step_preserves_alignment; eauto.
        -- symmetry.
           eapply with_state_heap_aligned_same.
           ++ exact HAlignedOther.
           ++ symmetry.
              exact HHeapAligned.
      * reflexivity.
  - inversion HLeftAfterOther; subst.
    match goal with
    | HStep : Step
        (with_state_heap (state_heap other') left) _ _ |- _ =>
        rename HStep into HStepScheduledHead
    end.
    match goal with
    | HTail : StepsN n _ _ (StError heap_after_other_left) |- _ =>
        rename HTail into HStepsTail
    end.
    pose proof
      (no_alloc_trace_app_l
        (label_trace label) phi HNoAllocLeft)
      as HNoAllocLabel.
    pose proof
      (no_alloc_trace_app_r
        (label_trace label) phi HNoAllocLeft)
      as HNoAllocTail.
    destruct
      (TraceDisjoint_app_r
        (label_trace other_label)
        (label_trace label)
        phi
        HDisjointOtherLeft)
      as (HDisjointOtherLabel & HDisjointOtherTail).
    destruct
      (TraceDisjoint_app_l
        (label_trace label)
        phi
        (label_trace other_label)
        HDisjointLeftOther)
      as (HDisjointLabelOther & HDisjointTailOther).
    assert
      (HAlignedStart :
        StateHeapsAligned
          (with_state_heap (state_heap other') left)).
    {
      destruct
        (with_state_heap_aligned
          (state_heap other') left HAlignedLeft)
        as (HAligned & _).
      exact HAligned.
    }
    assert
      (HReadBackLabel :
        TraceReadHeapAgreement
          (label_trace label)
          (state_heap
            (with_state_heap (state_heap other') left))
          (state_heap left)).
    {
      intros r l cell HRead HLookup.
      rewrite state_heap_with_state_heap in HLookup.
      rewrite HHeapAligned.
      eapply
        (Step_noalloc_disjoint_read_agreement_reverse
          other other_label other' (label_trace label)).
      - exact HOther.
      - exact HAlignedOther.
      - rewrite <- HHeapAligned.
        exact HBounded.
      - exact HNoAllocOther.
      - exact HDisjointOtherLabel.
      - exact HRead.
      - exact HLookup.
    }
    destruct
      (HStepReadAgreementReplay
        (with_state_heap (state_heap other') left)
        label
        state'
        (state_heap left)
        HStepScheduledHead
        HAlignedStart
        HNoAllocLabel
        HReadBackLabel)
      as (heap_left_head & HStepLeftReplayed).
    rewrite with_state_heap_twice in HStepLeftReplayed.
    rewrite (with_state_heap_state_heap_aligned left HAlignedLeft)
      in HStepLeftReplayed.
    set (left_head := with_state_heap heap_left_head state').
    assert (HStepLeft : Step left label left_head).
    {
      subst left_head.
      exact HStepLeftReplayed.
    }
    destruct
      (Step_disjoint_noalloc_local_diamond_reheap
        left label left_head other other_label other'
        HHeapAligned HAlignedLeft HAlignedOther HBounded
        HStepLeft HOther HNoAllocLabel HNoAllocOther
        HDisjointLabelOther HDisjointOtherLabel)
      as (heap_after_scheduled_head & heap_after_canonical_head &
        HStepScheduledDiamond & HStepOtherAfterHead & _HHeapHead).
    subst heap_after_scheduled_head.
    destruct
      (Step_deterministic
        (with_state_heap (state_heap other') left)
        label
        state'
        label
        (with_state_heap heap_after_canonical_head left_head)
        HStepScheduledHead
        HStepScheduledDiamond)
      as (_ & HStateHead).
    rewrite HStateHead in HStepsTail.
    assert
      (HLeftTailAfterOtherHead' :
        StepsN n
          (with_state_heap
            (state_heap
              (with_state_heap heap_after_canonical_head other'))
            left_head)
          phi
          (StError heap_after_other_left)).
    {
      rewrite state_heap_with_state_heap.
      exact HStepsTail.
    }
    assert
      (HAlignedLeftHead : StateHeapsAligned left_head).
    {
      eapply Step_preserves_alignment; eauto.
    }
    assert
      (HBoundedLeftHead : HeapKeysBounded (state_heap left_head)).
    {
      eapply Step_preserves_heap_bounded_aligned; eauto.
    }
    assert
      (HAlignedOtherHead :
        StateHeapsAligned
          (with_state_heap (state_heap left_head) other)).
    {
      destruct
        (with_state_heap_aligned
          (state_heap left_head) other HAlignedOther)
        as (HAligned & _).
      exact HAligned.
    }
    destruct
      (IH
        left_head
        (with_state_heap (state_heap left_head) other)
        other_label
        (with_state_heap heap_after_canonical_head other')
        phi
        heap_after_other_left)
      as (heap_left_error & heap_after_left_other &
        HLeftTail & HOtherAfterTail & HHeapTail).
    + rewrite state_heap_with_state_heap.
      reflexivity.
    + exact HAlignedLeftHead.
    + exact HAlignedOtherHead.
    + exact HBoundedLeftHead.
    + exact HStepOtherAfterHead.
    + exact HLeftTailAfterOtherHead'.
    + exact HNoAllocOther.
    + exact HNoAllocTail.
    + exact HDisjointOtherTail.
    + exact HDisjointTailOther.
    + exists heap_left_error, heap_after_left_other.
      split.
      * eapply StepsNStep.
        -- exact HStepLeft.
        -- exact HLeftTail.
      * split.
        -- repeat rewrite with_state_heap_twice in HOtherAfterTail.
           exact HOtherAfterTail.
        -- exact HHeapTail.
Qed.

Inductive ScheduledPairParRun :
    State -> TraceView -> TraceView -> State -> Prop :=
| SchedPairParRefl :
    forall state,
      ScheduledPairParRun state TraceEmpty TraceEmpty state
| SchedPairParRunLeft :
    forall left_state right_state phi_left phi_right k
      label left_state' view_left view_right state_final,
      StateNotError right_state ->
      Step left_state label left_state' ->
      ScheduledPairParRun
        (StPairParRun
          left_state'
          (with_state_heap (state_heap left_state') right_state)
          (phi_left ++ label_trace label)
          phi_right
          k)
        view_left
        view_right
        state_final ->
      ScheduledPairParRun
        (StPairParRun left_state right_state phi_left phi_right k)
        (TraceSeq (label_view label) view_left)
        view_right
        state_final
| SchedPairParRunRight :
    forall left_state right_state phi_left phi_right k
      label right_state' view_left view_right state_final,
      StateNotError left_state ->
      Step right_state label right_state' ->
      ScheduledPairParRun
        (StPairParRun
          (with_state_heap (state_heap right_state') left_state)
          right_state'
          phi_left
          (phi_right ++ label_trace label)
          k)
        view_left
        view_right
        state_final ->
      ScheduledPairParRun
        (StPairParRun left_state right_state phi_left phi_right k)
        view_left
        (TraceSeq (label_view label) view_right)
        state_final
| SchedPairParRunLeftError :
    forall heap right_state phi_left phi_right k,
      ScheduledPairParRun
        (StPairParRun (StError heap) right_state phi_left phi_right k)
        TraceEmpty
        TraceEmpty
        (StError heap)
| SchedPairParRunRightError :
    forall heap_left v_left heap_right phi_left phi_right k,
      ScheduledPairParRun
        (StPairParRun
          (StDone heap_left v_left)
          (StError heap_right)
          phi_left
          phi_right
          k)
        TraceEmpty
        TraceEmpty
        (StError heap_right)
| SchedPairParRunDonePass :
    forall heap v_left v_right phi_left phi_right k,
      trace_disjointb phi_left phi_right = true ->
      ScheduledPairParRun
        (StPairParRun
          (StDone heap v_left)
          (StDone heap v_right)
          phi_left
          phi_right
          k)
        TraceEmpty
        TraceEmpty
        (StReturn heap (VPair v_left v_right) k)
| SchedPairParRunDoneFail :
    forall heap v_left v_right phi_left phi_right k,
      trace_disjointb phi_left phi_right = false ->
      ScheduledPairParRun
        (StPairParRun
          (StDone heap v_left)
          (StDone heap v_right)
          phi_left
          phi_right
          k)
        TraceEmpty
        TraceEmpty
        (StError heap).

Lemma ScheduledPairParRun_success_accumulators_general :
  forall state view_left view_right heap value k,
    ScheduledPairParRun state view_left view_right
      (StReturn heap value k) ->
    forall left_state right_state phi_left phi_right,
      state = StPairParRun left_state right_state phi_left phi_right k ->
    exists v_left v_right phi_left_final phi_right_final,
      value = VPair v_left v_right /\
      phi_left_final = phi_left ++ trace_view_flatten view_left /\
      phi_right_final = phi_right ++ trace_view_flatten view_right /\
      trace_disjointb phi_left_final phi_right_final = true.
Proof.
  intros state view_left view_right heap value k HRun.
  remember (StReturn heap value k) as final_state eqn:HFinal.
  revert heap value k HFinal.
  induction HRun; intros heap0 value0 k0 HFinal
    left0 right0 phi_left0 phi_right0 HStart.
  - rewrite HStart in HFinal.
    inversion HFinal.
  - pose proof HFinal as HFinalTail.
    inversion HStart; subst.
    destruct
      (IHHRun
        heap0
        value0
        k0
        eq_refl
        left_state'
        (with_state_heap (state_heap left_state') right0)
        (phi_left0 ++ label_trace label)
        phi_right0
        eq_refl)
      as (v_left & v_right & phi_left_final & phi_right_final &
        HValue & HLeft & HRight & HDisjoint).
    exists v_left, v_right, phi_left_final, phi_right_final.
    split; [exact HValue |].
    split.
    + rewrite HLeft.
      simpl.
      rewrite label_view_flatten.
      rewrite app_assoc.
      reflexivity.
    + split; [exact HRight | exact HDisjoint].
  - pose proof HFinal as HFinalTail.
    inversion HStart; subst.
    destruct
      (IHHRun
        heap0
        value0
        k0
        eq_refl
        (with_state_heap (state_heap right_state') left0)
        right_state'
        phi_left0
        (phi_right0 ++ label_trace label)
        eq_refl)
      as (v_left & v_right & phi_left_final & phi_right_final &
        HValue & HLeft & HRight & HDisjoint).
    exists v_left, v_right, phi_left_final, phi_right_final.
    split; [exact HValue |].
    split; [exact HLeft |].
    split.
    + rewrite HRight.
      simpl.
      rewrite label_view_flatten.
      rewrite app_assoc.
      reflexivity.
    + exact HDisjoint.
  - discriminate.
  - discriminate.
  - inversion HFinal; subst.
    inversion HStart; subst.
    exists v_left, v_right, phi_left0, phi_right0.
    simpl.
    repeat rewrite app_nil_r.
    repeat split; assumption || reflexivity.
  - discriminate.
Qed.

Lemma ScheduledPairParRun_success_accumulators :
  forall left_state right_state phi_left phi_right k
    view_left view_right heap value,
    ScheduledPairParRun
      (StPairParRun left_state right_state phi_left phi_right k)
      view_left
      view_right
      (StReturn heap value k) ->
    exists v_left v_right phi_left_final phi_right_final,
      value = VPair v_left v_right /\
      phi_left_final = phi_left ++ trace_view_flatten view_left /\
      phi_right_final = phi_right ++ trace_view_flatten view_right /\
      trace_disjointb phi_left_final phi_right_final = true.
Proof.
  intros left_state right_state phi_left phi_right k
    view_left view_right heap value HRun.
  eapply ScheduledPairParRun_success_accumulators_general; eauto.
Qed.

Corollary ScheduledPairParRun_success_empty_accumulators :
  forall left_state right_state k view_left view_right heap value,
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left
      view_right
      (StReturn heap value k) ->
    exists v_left v_right phi_left_final phi_right_final,
      value = VPair v_left v_right /\
      phi_left_final = trace_view_flatten view_left /\
      phi_right_final = trace_view_flatten view_right /\
      trace_disjointb phi_left_final phi_right_final = true.
Proof.
  intros left_state right_state k view_left view_right heap value HRun.
  destruct
    (ScheduledPairParRun_success_accumulators
      left_state right_state [] [] k view_left view_right heap value HRun)
    as (v_left & v_right & phi_left_final & phi_right_final &
      HValue & HLeft & HRight & HDisjoint).
  exists v_left, v_right, phi_left_final, phi_right_final.
  simpl in HLeft, HRight.
  repeat split; assumption.
Qed.

Lemma ScheduledPairParRun_pairpar_accumulators :
  forall left_state right_state phi_left phi_right k
    view_left view_right left_final right_final
    phi_left_final phi_right_final,
    ScheduledPairParRun
      (StPairParRun left_state right_state phi_left phi_right k)
      view_left
      view_right
      (StPairParRun
        left_final right_final phi_left_final phi_right_final k) ->
    phi_left_final = phi_left ++ trace_view_flatten view_left /\
    phi_right_final = phi_right ++ trace_view_flatten view_right.
Proof.
  intros left_state right_state phi_left phi_right k
    view_left view_right left_final right_final
    phi_left_final phi_right_final HRun.
  remember
    (StPairParRun left_state right_state phi_left phi_right k)
    as state_start eqn:HStart.
  remember
    (StPairParRun left_final right_final
      phi_left_final phi_right_final k)
    as state_final eqn:HFinal.
  revert left_state right_state phi_left phi_right k
    left_final right_final phi_left_final phi_right_final
    HStart HFinal.
  induction HRun; intros left0 right0 phi_left0 phi_right0 k0
    left_final right_final phi_left_final phi_right_final
    HStart HFinal.
  - rewrite HStart in HFinal.
    inversion HFinal; subst.
    simpl.
    repeat rewrite app_nil_r.
    split; reflexivity.
  - pose proof HFinal as HFinalTail.
    inversion HStart; subst.
    destruct
      (IHHRun
        left_state'
        (with_state_heap (state_heap left_state') right0)
        (phi_left0 ++ label_trace label)
        phi_right0
        k0
        left_final
        right_final
        phi_left_final
        phi_right_final
        eq_refl
        HFinalTail)
      as (HLeft & HRight).
    split.
    + rewrite HLeft.
      simpl.
      rewrite label_view_flatten.
      rewrite app_assoc.
      reflexivity.
    + exact HRight.
  - pose proof HFinal as HFinalTail.
    inversion HStart; subst.
    destruct
      (IHHRun
        (with_state_heap (state_heap right_state') left0)
        right_state'
        phi_left0
        (phi_right0 ++ label_trace label)
        k0
        left_final
        right_final
        phi_left_final
        phi_right_final
        eq_refl
        HFinalTail)
      as (HLeft & HRight).
    split.
    + exact HLeft.
    + rewrite HRight.
      simpl.
      rewrite label_view_flatten.
      rewrite app_assoc.
      reflexivity.
  - discriminate HFinal.
  - discriminate HFinal.
  - discriminate HFinal.
  - discriminate HFinal.
Qed.

Corollary ScheduledPairParRun_pairpar_empty_accumulators :
  forall left_state right_state k view_left view_right
    left_final right_final phi_left_final phi_right_final,
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left
      view_right
      (StPairParRun
        left_final right_final phi_left_final phi_right_final k) ->
    phi_left_final = trace_view_flatten view_left /\
    phi_right_final = trace_view_flatten view_right.
Proof.
  intros left_state right_state k view_left view_right
    left_final right_final phi_left_final phi_right_final HRun.
  destruct
    (ScheduledPairParRun_pairpar_accumulators
      left_state right_state [] [] k view_left view_right
      left_final right_final phi_left_final phi_right_final HRun)
    as (HLeft & HRight).
  simpl in HLeft, HRight.
  split; assumption.
Qed.

Lemma ScheduledPairParRun_noalloc_disjoint_left_error_canonical :
  forall left_state right_state phi_left_acc phi_right_acc
    view_left view_right k heap_error right_final
    phi_left_final phi_right_final,
    StateHeapsAligned left_state ->
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    HeapKeysBounded (state_heap left_state) ->
    TraceDisjoint
      (phi_left_acc ++ trace_view_flatten view_left)
      (phi_right_acc ++ trace_view_flatten view_right) ->
    NoAllocTrace (trace_view_flatten view_left) ->
    NoAllocTrace (trace_view_flatten view_right) ->
    ScheduledPairParRun
      (StPairParRun left_state right_state phi_left_acc phi_right_acc k)
      view_left
      view_right
      (StPairParRun
        (StError heap_error)
        right_final
        phi_left_final
        phi_right_final
        k) ->
    exists heap_left_error,
      Steps left_state (trace_view_flatten view_left)
        (StError heap_left_error) /\
      HeapEqOn
        (fun r l =>
          TraceDoesNotWrite
            r l
            (phi_right_acc ++ trace_view_flatten view_right))
        heap_error
        heap_left_error.
Proof.
  assert
    (HTraceDisjointSym :
      forall phi1 phi2,
        TraceDisjoint phi1 phi2 ->
        TraceDisjoint phi2 phi1).
  {
    intros phi1 phi2 HDisjoint a2 a1 HIn2 HIn1 HConflict.
    apply (HDisjoint a1 a2 HIn1 HIn2).
    inversion HConflict; subst;
      match goal with
      | HSame : same_location _ _ _ _ |- _ =>
          destruct HSame as [-> ->]
      end;
      constructor; split; reflexivity.
  }
  intros left_state right_state phi_left_acc phi_right_acc
    view_left view_right k heap_error right_final
    phi_left_final phi_right_final
    HAlignedLeft HAlignedRight HHeapAligned HBounded
    HDisjointFinal HNoAllocLeft HNoAllocRight HRun.
  remember
    (StPairParRun left_state right_state phi_left_acc phi_right_acc k)
    as state_start eqn:HStart.
  remember
    (StPairParRun
      (StError heap_error)
      right_final
      phi_left_final
      phi_right_final
      k)
    as state_final eqn:HFinal.
  revert left_state right_state phi_left_acc phi_right_acc k
    heap_error right_final phi_left_final phi_right_final
    HAlignedLeft HAlignedRight HHeapAligned HBounded
    HDisjointFinal HNoAllocLeft HNoAllocRight
    HStart HFinal.
  induction HRun; intros left0 right0 phi_left0 phi_right0 k0
    heap_error0 right_final0 phi_left_final0 phi_right_final0
    HAlignedLeft HAlignedRight HHeapAligned HBounded
    HDisjointFinal HNoAllocLeft HNoAllocRight HStart HFinal.
  - rewrite HStart in HFinal.
    inversion HFinal; subst.
    simpl.
    exists heap_error0.
    split.
    + constructor.
    + apply HeapEqOn_refl.
  - pose proof HFinal as HFinalTail.
    inversion HStart; subst.
    simpl in HNoAllocLeft.
    rewrite label_view_flatten in HNoAllocLeft.
    pose proof
      (no_alloc_trace_app_l
        (label_trace label) (trace_view_flatten view_left)
        HNoAllocLeft)
      as HNoAllocLabel.
    pose proof
      (no_alloc_trace_app_r
        (label_trace label) (trace_view_flatten view_left)
        HNoAllocLeft)
      as HNoAllocLeftTail.
    assert
      (HDisjointTail :
        TraceDisjoint
          ((phi_left0 ++ label_trace label) ++
            trace_view_flatten view_left)
          (phi_right0 ++ trace_view_flatten view_right)).
    {
      simpl in HDisjointFinal.
      rewrite label_view_flatten in HDisjointFinal.
      rewrite app_assoc in HDisjointFinal.
      exact HDisjointFinal.
    }
    pose proof
      (Step_preserves_alignment
        left0 label left_state' H0 HAlignedLeft)
      as HAlignedLeft'.
    pose proof
      (Step_preserves_heap_bounded_aligned
        left0 label left_state' H0 HAlignedLeft HBounded)
      as HBoundedLeft'.
    assert
      (HAlignedRightRebased :
        StateHeapsAligned
          (with_state_heap (state_heap left_state') right0)).
    {
      destruct
        (with_state_heap_aligned
          (state_heap left_state') right0 HAlignedRight)
        as (HAligned & _).
      exact HAligned.
    }
    assert
      (HHeapTail :
        state_heap left_state' =
        state_heap (with_state_heap (state_heap left_state') right0)).
    {
      rewrite state_heap_with_state_heap.
      reflexivity.
    }
    destruct
      (IHHRun
        left_state'
        (with_state_heap (state_heap left_state') right0)
        (phi_left0 ++ label_trace label)
        phi_right0
        k0 heap_error0 right_final0
        phi_left_final0 phi_right_final0
        HAlignedLeft'
        HAlignedRightRebased
        HHeapTail
        HBoundedLeft'
        HDisjointTail
        HNoAllocLeftTail
        HNoAllocRight
        eq_refl
        HFinalTail)
      as (heap_left_error & HLeftTail & HEqTail).
    exists heap_left_error.
    split.
    + simpl.
      rewrite label_view_flatten.
      eapply StepsStep; eauto.
    + exact HEqTail.
  - pose proof HFinal as HFinalTail.
    inversion HStart; subst.
    simpl in HNoAllocRight.
    rewrite label_view_flatten in HNoAllocRight.
    pose proof
      (no_alloc_trace_app_l
        (label_trace label) (trace_view_flatten view_right)
        HNoAllocRight)
      as HNoAllocLabel.
    pose proof
      (no_alloc_trace_app_r
        (label_trace label) (trace_view_flatten view_right)
        HNoAllocRight)
      as HNoAllocRightTail.
    assert
      (HDisjointTail :
        TraceDisjoint
          (phi_left0 ++ trace_view_flatten view_left)
          ((phi_right0 ++ label_trace label) ++
            trace_view_flatten view_right)).
    {
      simpl in HDisjointFinal.
      rewrite label_view_flatten in HDisjointFinal.
      rewrite app_assoc in HDisjointFinal.
      exact HDisjointFinal.
    }
    assert
      (HDisjointLeftLabel :
        TraceDisjoint
          (trace_view_flatten view_left)
          (label_trace label)).
    {
      destruct
        (TraceDisjoint_app_l
          phi_left0
          (trace_view_flatten view_left)
          ((phi_right0 ++ label_trace label) ++
            trace_view_flatten view_right)
          HDisjointTail)
        as (_ & HLeftRemainingRightFinal).
      destruct
        (TraceDisjoint_app_r
          (trace_view_flatten view_left)
          (phi_right0 ++ label_trace label)
          (trace_view_flatten view_right)
          HLeftRemainingRightFinal)
        as (HLeftRemainingRightAccLabel & _).
      destruct
        (TraceDisjoint_app_r
          (trace_view_flatten view_left)
          phi_right0
          (label_trace label)
          HLeftRemainingRightAccLabel)
        as (_ & HLeftLabel).
      exact HLeftLabel.
    }
    pose proof
      (HTraceDisjointSym
        (trace_view_flatten view_left)
        (label_trace label)
        HDisjointLeftLabel)
      as HDisjointLabelLeft.
    pose proof
      (Step_preserves_alignment
        right0 label right_state' H0 HAlignedRight)
      as HAlignedRight'.
    assert
      (HAlignedLeftRebased :
        StateHeapsAligned
          (with_state_heap (state_heap right_state') left0)).
    {
      destruct
        (with_state_heap_aligned
          (state_heap right_state') left0 HAlignedLeft)
        as (HAligned & _).
      exact HAligned.
    }
    assert
      (HHeapTail :
        state_heap (with_state_heap (state_heap right_state') left0) =
        state_heap right_state').
    {
      rewrite state_heap_with_state_heap.
      reflexivity.
    }
    assert (HBoundedRight : HeapKeysBounded (state_heap right0)).
    {
      rewrite <- HHeapAligned.
      exact HBounded.
    }
    pose proof
      (Step_preserves_heap_bounded_aligned
        right0 label right_state' H0 HAlignedRight HBoundedRight)
      as HBoundedRight'.
    assert
      (HBoundedTail :
        HeapKeysBounded
          (state_heap
            (with_state_heap (state_heap right_state') left0))).
    {
      rewrite state_heap_with_state_heap.
      exact HBoundedRight'.
    }
    destruct
      (IHHRun
        (with_state_heap (state_heap right_state') left0)
        right_state'
        phi_left0
        (phi_right0 ++ label_trace label)
        k0 heap_error0 right_final0
        phi_left_final0 phi_right_final0
        HAlignedLeftRebased
        HAlignedRight'
        HHeapTail
        HBoundedTail
        HDisjointTail
        HNoAllocLeft
        HNoAllocRightTail
        eq_refl
        HFinalTail)
      as (heap_left_rebased_error & HLeftAfterRight & HEqTail).
    destruct
      (Steps_to_StepsN
        (with_state_heap (state_heap right_state') left0)
        (trace_view_flatten view_left)
        (StError heap_left_rebased_error)
        HLeftAfterRight)
      as (n_left & HLeftAfterRightN).
    destruct
      (StepsN_noalloc_disjoint_step_after_run_error
        n_left
        left0
        right0
        label
        right_state'
        (trace_view_flatten view_left)
        heap_left_rebased_error
        HHeapAligned
        HAlignedLeft
        HAlignedRight
        HBounded
        H0
        HLeftAfterRightN
        HNoAllocLabel
        HNoAllocLeft
        HDisjointLabelLeft
        HDisjointLeftLabel)
      as (heap_left_error & heap_after_left_right &
        HLeftCanonicalN & HRightAfterLeft & HHeapAfterLeftRight).
    subst heap_left_rebased_error.
    assert (HAlignedRightAfterLeftStart :
      StateHeapsAligned (with_state_heap heap_left_error right0)).
    {
      destruct
        (with_state_heap_aligned
          heap_left_error right0 HAlignedRight)
        as (HAligned & _).
      exact HAligned.
    }
    assert (HBoundedLeftError : HeapKeysBounded heap_left_error).
    {
      pose proof
        (StepsN_preserves_heap_bounded_aligned
          n_left
          left0
          (trace_view_flatten view_left)
          (StError heap_left_error)
          HLeftCanonicalN
          HAlignedLeft
          HBounded)
        as HBoundedError.
      exact HBoundedError.
    }
    exists heap_left_error.
    split.
    + eapply StepsN_to_Steps.
      exact HLeftCanonicalN.
    + intros r l HNoWriteFull.
      simpl in HNoWriteFull.
      rewrite label_view_flatten in HNoWriteFull.
      assert
        (HNoWriteTail :
          TraceDoesNotWrite
            r l
            ((phi_right0 ++ label_trace label) ++
              trace_view_flatten view_right)).
      {
        rewrite <- app_assoc.
        exact HNoWriteFull.
      }
      assert
        (HNoWriteLabelTail :
          TraceDoesNotWrite
            r l
            (label_trace label ++ trace_view_flatten view_right)).
      {
        eapply trace_does_not_write_app_r.
        exact HNoWriteFull.
      }
      assert
        (HNoWriteLabel :
          TraceDoesNotWrite r l (label_trace label)).
      {
        eapply trace_does_not_write_app_l.
        exact HNoWriteLabelTail.
      }
      rewrite HEqTail by exact HNoWriteTail.
      replace heap_after_left_right with
        (state_heap (with_state_heap heap_after_left_right right_state'))
        by (rewrite state_heap_with_state_heap; reflexivity).
      replace heap_left_error with
        (state_heap (with_state_heap heap_left_error right0))
        by (rewrite state_heap_with_state_heap; reflexivity).
      eapply Step_noalloc_lookup_preserved_without_write_aligned.
      * exact HRightAfterLeft.
      * exact HAlignedRightAfterLeftStart.
      * rewrite state_heap_with_state_heap.
        exact HBoundedLeftError.
      * exact HNoAllocLabel.
      * exact HNoWriteLabel.
  - discriminate HFinal.
  - discriminate HFinal.
  - discriminate HFinal.
  - discriminate HFinal.
Qed.

Lemma ScheduledPairParRun_noalloc_disjoint_right_error_canonical :
  forall left_state right_state phi_left_acc phi_right_acc
    view_left view_right k heap_left_done v_left_done heap_error
    phi_left_final phi_right_final,
    StateHeapsAligned left_state ->
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    HeapKeysBounded (state_heap left_state) ->
    TraceDisjoint
      (phi_left_acc ++ trace_view_flatten view_left)
      (phi_right_acc ++ trace_view_flatten view_right) ->
    NoAllocTrace (trace_view_flatten view_left) ->
    NoAllocTrace (trace_view_flatten view_right) ->
    ScheduledPairParRun
      (StPairParRun left_state right_state phi_left_acc phi_right_acc k)
      view_left
      view_right
      (StPairParRun
        (StDone heap_left_done v_left_done)
        (StError heap_error)
        phi_left_final
        phi_right_final
        k) ->
    exists heap_left v_left heap_right_error,
      Steps left_state (trace_view_flatten view_left)
        (StDone heap_left v_left) /\
      Steps
        (with_state_heap heap_left right_state)
        (trace_view_flatten view_right)
        (StError heap_right_error) /\
      heap_error = heap_right_error.
Proof.
  assert
    (HTraceDisjointSym :
      forall phi1 phi2,
        TraceDisjoint phi1 phi2 ->
        TraceDisjoint phi2 phi1).
  {
    intros phi1 phi2 HDisjoint a2 a1 HIn2 HIn1 HConflict.
    apply (HDisjoint a1 a2 HIn1 HIn2).
    inversion HConflict; subst;
      match goal with
      | HSame : same_location _ _ _ _ |- _ =>
          destruct HSame as [-> ->]
      end;
      constructor; split; reflexivity.
  }
  intros left_state right_state phi_left_acc phi_right_acc
    view_left view_right k heap_left_done v_left_done heap_error
    phi_left_final phi_right_final
    HAlignedLeft HAlignedRight HHeapAligned HBounded
    HDisjointFinal HNoAllocLeft HNoAllocRight HRun.
  remember
    (StPairParRun left_state right_state phi_left_acc phi_right_acc k)
    as state_start eqn:HStart.
  remember
    (StPairParRun
      (StDone heap_left_done v_left_done)
      (StError heap_error)
      phi_left_final
      phi_right_final
      k)
    as state_final eqn:HFinal.
  revert left_state right_state phi_left_acc phi_right_acc k
    heap_left_done v_left_done heap_error
    phi_left_final phi_right_final
    HAlignedLeft HAlignedRight HHeapAligned HBounded
    HDisjointFinal HNoAllocLeft HNoAllocRight
    HStart HFinal.
  induction HRun; intros left0 right0 phi_left0 phi_right0 k0
    heap_left_done0 v_left_done0 heap_error0
    phi_left_final0 phi_right_final0
    HAlignedLeft HAlignedRight HHeapAligned HBounded
    HDisjointFinal HNoAllocLeft HNoAllocRight HStart HFinal.
  - rewrite HStart in HFinal.
    inversion HFinal; subst.
    simpl.
    exists heap_left_done0, v_left_done0, heap_error0.
    split.
    + constructor.
    + split.
      * simpl in HHeapAligned.
        rewrite HHeapAligned.
        constructor.
      * reflexivity.
  - pose proof HFinal as HFinalTail.
    inversion HStart; subst.
    simpl in HNoAllocLeft.
    rewrite label_view_flatten in HNoAllocLeft.
    pose proof
      (no_alloc_trace_app_l
        (label_trace label) (trace_view_flatten view_left)
        HNoAllocLeft)
      as HNoAllocLabel.
    pose proof
      (no_alloc_trace_app_r
        (label_trace label) (trace_view_flatten view_left)
        HNoAllocLeft)
      as HNoAllocLeftTail.
    assert
      (HDisjointTail :
        TraceDisjoint
          ((phi_left0 ++ label_trace label) ++
            trace_view_flatten view_left)
          (phi_right0 ++ trace_view_flatten view_right)).
    {
      simpl in HDisjointFinal.
      rewrite label_view_flatten in HDisjointFinal.
      rewrite app_assoc in HDisjointFinal.
      exact HDisjointFinal.
    }
    pose proof
      (Step_preserves_alignment
        left0 label left_state' H0 HAlignedLeft)
      as HAlignedLeft'.
    pose proof
      (Step_preserves_heap_bounded_aligned
        left0 label left_state' H0 HAlignedLeft HBounded)
      as HBoundedLeft'.
    assert
      (HAlignedRightRebased :
        StateHeapsAligned
          (with_state_heap (state_heap left_state') right0)).
    {
      destruct
        (with_state_heap_aligned
          (state_heap left_state') right0 HAlignedRight)
        as (HAligned & _).
      exact HAligned.
    }
    assert
      (HHeapTail :
        state_heap left_state' =
        state_heap (with_state_heap (state_heap left_state') right0)).
    {
      rewrite state_heap_with_state_heap.
      reflexivity.
    }
    destruct
      (IHHRun
        left_state'
        (with_state_heap (state_heap left_state') right0)
        (phi_left0 ++ label_trace label)
        phi_right0
        k0 heap_left_done0 v_left_done0 heap_error0
        phi_left_final0 phi_right_final0
        HAlignedLeft'
        HAlignedRightRebased
        HHeapTail
        HBoundedLeft'
        HDisjointTail
        HNoAllocLeftTail
        HNoAllocRight
        eq_refl
        HFinalTail)
      as (heap_left & v_left & heap_right_error &
        HLeftTail & HRightCanonical & HHeapError).
    exists heap_left, v_left, heap_right_error.
    split.
    + simpl.
      rewrite label_view_flatten.
      eapply StepsStep; eauto.
    + split.
      * rewrite with_state_heap_twice in HRightCanonical.
        exact HRightCanonical.
      * exact HHeapError.
  - pose proof HFinal as HFinalTail.
    inversion HStart; subst.
    simpl in HNoAllocRight.
    rewrite label_view_flatten in HNoAllocRight.
    pose proof
      (no_alloc_trace_app_l
        (label_trace label) (trace_view_flatten view_right)
        HNoAllocRight)
      as HNoAllocLabel.
    pose proof
      (no_alloc_trace_app_r
        (label_trace label) (trace_view_flatten view_right)
        HNoAllocRight)
      as HNoAllocRightTail.
    assert
      (HDisjointTail :
        TraceDisjoint
          (phi_left0 ++ trace_view_flatten view_left)
          ((phi_right0 ++ label_trace label) ++
            trace_view_flatten view_right)).
    {
      simpl in HDisjointFinal.
      rewrite label_view_flatten in HDisjointFinal.
      rewrite app_assoc in HDisjointFinal.
      exact HDisjointFinal.
    }
    assert
      (HDisjointLeftLabel :
        TraceDisjoint
          (trace_view_flatten view_left)
          (label_trace label)).
    {
      destruct
        (TraceDisjoint_app_l
          phi_left0
          (trace_view_flatten view_left)
          ((phi_right0 ++ label_trace label) ++
            trace_view_flatten view_right)
          HDisjointTail)
        as (_ & HLeftRemainingRightFinal).
      destruct
        (TraceDisjoint_app_r
          (trace_view_flatten view_left)
          (phi_right0 ++ label_trace label)
          (trace_view_flatten view_right)
          HLeftRemainingRightFinal)
        as (HLeftRemainingRightAccLabel & _).
      destruct
        (TraceDisjoint_app_r
          (trace_view_flatten view_left)
          phi_right0
          (label_trace label)
          HLeftRemainingRightAccLabel)
        as (_ & HLeftLabel).
      exact HLeftLabel.
    }
    pose proof
      (HTraceDisjointSym
        (trace_view_flatten view_left)
        (label_trace label)
        HDisjointLeftLabel)
      as HDisjointLabelLeft.
    pose proof
      (Step_preserves_alignment
        right0 label right_state' H0 HAlignedRight)
      as HAlignedRight'.
    assert
      (HAlignedLeftRebased :
        StateHeapsAligned
          (with_state_heap (state_heap right_state') left0)).
    {
      destruct
        (with_state_heap_aligned
          (state_heap right_state') left0 HAlignedLeft)
        as (HAligned & _).
      exact HAligned.
    }
    assert
      (HHeapTail :
        state_heap (with_state_heap (state_heap right_state') left0) =
        state_heap right_state').
    {
      rewrite state_heap_with_state_heap.
      reflexivity.
    }
    assert (HBoundedRight : HeapKeysBounded (state_heap right0)).
    {
      rewrite <- HHeapAligned.
      exact HBounded.
    }
    pose proof
      (Step_preserves_heap_bounded_aligned
        right0 label right_state' H0 HAlignedRight HBoundedRight)
      as HBoundedRight'.
    assert
      (HBoundedTail :
        HeapKeysBounded
          (state_heap
            (with_state_heap (state_heap right_state') left0))).
    {
      rewrite state_heap_with_state_heap.
      exact HBoundedRight'.
    }
    destruct
      (IHHRun
        (with_state_heap (state_heap right_state') left0)
        right_state'
        phi_left0
        (phi_right0 ++ label_trace label)
        k0 heap_left_done0 v_left_done0 heap_error0
        phi_left_final0 phi_right_final0
        HAlignedLeftRebased
        HAlignedRight'
        HHeapTail
        HBoundedTail
        HDisjointTail
        HNoAllocLeft
        HNoAllocRightTail
        eq_refl
        HFinalTail)
      as (heap_left_after_right & v_left & heap_right_error &
        HLeftAfterRight & HRightTailScheduled & HHeapError).
    destruct
      (Steps_to_StepsN
        (with_state_heap (state_heap right_state') left0)
        (trace_view_flatten view_left)
        (StDone heap_left_after_right v_left)
        HLeftAfterRight)
      as (n_left & HLeftAfterRightN).
    destruct
      (StepsN_noalloc_disjoint_step_after_run
        n_left
        left0
        right0
        label
        right_state'
        (trace_view_flatten view_left)
        heap_left_after_right
        v_left
        HHeapAligned
        HAlignedLeft
        HAlignedRight
        HBounded
        H0
        HLeftAfterRightN
        HNoAllocLabel
        HNoAllocLeft
        HDisjointLabelLeft
        HDisjointLeftLabel)
      as (heap_left & heap_after_left_right &
        HLeftCanonicalN & HRightStepAfterLeft & HHeapCommute).
    subst heap_left_after_right.
    exists heap_left, v_left, heap_right_error.
    split.
    + eapply StepsN_to_Steps.
      exact HLeftCanonicalN.
    + split.
      * simpl.
        rewrite label_view_flatten.
        eapply StepsStep.
        -- exact HRightStepAfterLeft.
        -- exact HRightTailScheduled.
      * exact HHeapError.
  - discriminate HFinal.
  - discriminate HFinal.
  - discriminate HFinal.
  - discriminate HFinal.
Qed.

Corollary ScheduledPairParRun_noalloc_disjoint_left_error_footprint_deterministic :
  forall left_state right_state
    view_left1 view_right1 view_left2 view_right2
    k heap_error1 heap_error2
    right_final1 right_final2
    phi_left_final1 phi_right_final1
    phi_left_final2 phi_right_final2,
    StateHeapsAligned left_state ->
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    HeapKeysBounded (state_heap left_state) ->
    TraceDisjoint
      (trace_view_flatten view_left1)
      (trace_view_flatten view_right1) ->
    TraceDisjoint
      (trace_view_flatten view_left2)
      (trace_view_flatten view_right2) ->
    NoAllocTrace (trace_view_flatten view_left1) ->
    NoAllocTrace (trace_view_flatten view_right1) ->
    NoAllocTrace (trace_view_flatten view_left2) ->
    NoAllocTrace (trace_view_flatten view_right2) ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left1
      view_right1
      (StPairParRun
        (StError heap_error1)
        right_final1
        phi_left_final1
        phi_right_final1
        k) ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left2
      view_right2
      (StPairParRun
        (StError heap_error2)
        right_final2
        phi_left_final2
        phi_right_final2
        k) ->
    HeapEqOn
      (fun r l =>
        TraceDoesNotWrite r l (trace_view_flatten view_right1) /\
        TraceDoesNotWrite r l (trace_view_flatten view_right2))
      heap_error1
      heap_error2.
Proof.
  intros left_state right_state
    view_left1 view_right1 view_left2 view_right2
    k heap_error1 heap_error2
    right_final1 right_final2
    phi_left_final1 phi_right_final1
    phi_left_final2 phi_right_final2
    HAlignedLeft HAlignedRight HHeapAligned HBounded
    HDisjoint1 HDisjoint2
    HNoAllocLeft1 HNoAllocRight1 HNoAllocLeft2 HNoAllocRight2
    HRun1 HRun2.
  destruct
    (ScheduledPairParRun_noalloc_disjoint_left_error_canonical
      left_state right_state [] [] view_left1 view_right1
      k heap_error1 right_final1
      phi_left_final1 phi_right_final1
      HAlignedLeft HAlignedRight HHeapAligned HBounded
      HDisjoint1 HNoAllocLeft1 HNoAllocRight1 HRun1)
    as (heap_left_error1 & HLeftError1 & HEq1).
  destruct
    (ScheduledPairParRun_noalloc_disjoint_left_error_canonical
      left_state right_state [] [] view_left2 view_right2
      k heap_error2 right_final2
      phi_left_final2 phi_right_final2
      HAlignedLeft HAlignedRight HHeapAligned HBounded
      HDisjoint2 HNoAllocLeft2 HNoAllocRight2 HRun2)
    as (heap_left_error2 & HLeftError2 & HEq2).
  destruct
    (Steps_error_trace_deterministic
      left_state
      (trace_view_flatten view_left1)
      heap_left_error1
      (trace_view_flatten view_left2)
      heap_left_error2
      HLeftError1
      HLeftError2)
    as (_HTrace & HHeapLeftError).
  subst heap_left_error2.
  intros r l [HNoWriteRight1 HNoWriteRight2].
  simpl in HEq1, HEq2.
  rewrite HEq1 by exact HNoWriteRight1.
  rewrite HEq2 by exact HNoWriteRight2.
  reflexivity.
Qed.

Corollary
  ScheduledPairParRun_noalloc_disjoint_left_error_read_only_right_heap_lookup_deterministic :
  forall left_state right_state
    view_left1 view_right1 view_left2 view_right2
    k heap_error1 heap_error2
    right_final1 right_final2
    phi_left_final1 phi_right_final1
    phi_left_final2 phi_right_final2,
    StateHeapsAligned left_state ->
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    HeapKeysBounded (state_heap left_state) ->
    TraceDisjoint
      (trace_view_flatten view_left1)
      (trace_view_flatten view_right1) ->
    TraceDisjoint
      (trace_view_flatten view_left2)
      (trace_view_flatten view_right2) ->
    NoAllocTrace (trace_view_flatten view_left1) ->
    NoAllocTrace (trace_view_flatten view_right1) ->
    NoAllocTrace (trace_view_flatten view_left2) ->
    NoAllocTrace (trace_view_flatten view_right2) ->
    ReadOnlyTraceView view_right1 ->
    ReadOnlyTraceView view_right2 ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left1
      view_right1
      (StPairParRun
        (StError heap_error1)
        right_final1
        phi_left_final1
        phi_right_final1
        k) ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left2
      view_right2
      (StPairParRun
        (StError heap_error2)
        right_final2
        phi_left_final2
        phi_right_final2
        k) ->
    HeapEqOn (fun _ _ => True) heap_error1 heap_error2.
Proof.
  intros left_state right_state
    view_left1 view_right1 view_left2 view_right2
    k heap_error1 heap_error2
    right_final1 right_final2
    phi_left_final1 phi_right_final1
    phi_left_final2 phi_right_final2
    HAlignedLeft HAlignedRight HHeapAligned HBounded
    HDisjoint1 HDisjoint2
    HNoAllocLeft1 HNoAllocRight1 HNoAllocLeft2 HNoAllocRight2
    HReadOnlyRight1 HReadOnlyRight2 HRun1 HRun2.
  eapply
    (HeapEqOn_weaken
      (fun _ _ => True)
      (fun r l =>
        TraceDoesNotWrite r l (trace_view_flatten view_right1) /\
        TraceDoesNotWrite r l (trace_view_flatten view_right2))).
  - intros r l _HAny.
    split.
    + unfold ReadOnlyTraceView, ReadOnlyTrace,
        TraceDoesNotWrite in *.
      apply HReadOnlyRight1.
    + unfold ReadOnlyTraceView, ReadOnlyTrace,
        TraceDoesNotWrite in *.
      apply HReadOnlyRight2.
  - eapply
      (ScheduledPairParRun_noalloc_disjoint_left_error_footprint_deterministic
        left_state right_state
        view_left1 view_right1 view_left2 view_right2
        k heap_error1 heap_error2
        right_final1 right_final2
        phi_left_final1 phi_right_final1
        phi_left_final2 phi_right_final2);
      eauto.
Qed.

Corollary ScheduledPairParRun_noalloc_disjoint_right_error_heap_deterministic :
  forall left_state right_state
    view_left1 view_right1 view_left2 view_right2
    k heap_left_done1 heap_left_done2
    v_left_done1 v_left_done2
    heap_error1 heap_error2
    phi_left_final1 phi_right_final1
    phi_left_final2 phi_right_final2,
    StateHeapsAligned left_state ->
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    HeapKeysBounded (state_heap left_state) ->
    TraceDisjoint
      (trace_view_flatten view_left1)
      (trace_view_flatten view_right1) ->
    TraceDisjoint
      (trace_view_flatten view_left2)
      (trace_view_flatten view_right2) ->
    NoAllocTrace (trace_view_flatten view_left1) ->
    NoAllocTrace (trace_view_flatten view_right1) ->
    NoAllocTrace (trace_view_flatten view_left2) ->
    NoAllocTrace (trace_view_flatten view_right2) ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left1
      view_right1
      (StPairParRun
        (StDone heap_left_done1 v_left_done1)
        (StError heap_error1)
        phi_left_final1
        phi_right_final1
        k) ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left2
      view_right2
      (StPairParRun
        (StDone heap_left_done2 v_left_done2)
        (StError heap_error2)
        phi_left_final2
        phi_right_final2
        k) ->
    heap_error1 = heap_error2.
Proof.
  intros left_state right_state
    view_left1 view_right1 view_left2 view_right2
    k heap_left_done1 heap_left_done2
    v_left_done1 v_left_done2
    heap_error1 heap_error2
    phi_left_final1 phi_right_final1
    phi_left_final2 phi_right_final2
    HAlignedLeft HAlignedRight HHeapAligned HBounded
    HDisjoint1 HDisjoint2
    HNoAllocLeft1 HNoAllocRight1 HNoAllocLeft2 HNoAllocRight2
    HRun1 HRun2.
  destruct
    (ScheduledPairParRun_noalloc_disjoint_right_error_canonical
      left_state right_state [] [] view_left1 view_right1
      k heap_left_done1 v_left_done1 heap_error1
      phi_left_final1 phi_right_final1
      HAlignedLeft HAlignedRight HHeapAligned HBounded
      HDisjoint1 HNoAllocLeft1 HNoAllocRight1 HRun1)
    as (heap_left1 & v_left1 & heap_right_error1 &
      HLeft1 & HRight1 & HHeap1).
  destruct
    (ScheduledPairParRun_noalloc_disjoint_right_error_canonical
      left_state right_state [] [] view_left2 view_right2
      k heap_left_done2 v_left_done2 heap_error2
      phi_left_final2 phi_right_final2
      HAlignedLeft HAlignedRight HHeapAligned HBounded
      HDisjoint2 HNoAllocLeft2 HNoAllocRight2 HRun2)
    as (heap_left2 & v_left2 & heap_right_error2 &
      HLeft2 & HRight2 & HHeap2).
  destruct
    (Steps_terminal_deterministic
      left_state
      (trace_view_flatten view_left1)
      heap_left1
      v_left1
      (trace_view_flatten view_left2)
      heap_left2
      v_left2
      HLeft1
      HLeft2)
    as (HHeapLeft & HValueLeft).
  subst heap_left2 v_left2.
  destruct
    (Steps_error_trace_deterministic
      (with_state_heap heap_left1 right_state)
      (trace_view_flatten view_right1)
      heap_right_error1
      (trace_view_flatten view_right2)
      heap_right_error2
      HRight1
      HRight2)
    as (_HTraceRight & HHeapRightError).
  subst heap_right_error2.
  subst heap_error1 heap_error2.
  reflexivity.
Qed.

Corollary ScheduledPairParRun_noalloc_disjoint_left_right_error_impossible :
  forall left_state right_state
    view_left1 view_right1 view_left2 view_right2
    k heap_error_left right_final
    heap_left_done v_left_done heap_error_right
    phi_left_final1 phi_right_final1
    phi_left_final2 phi_right_final2,
    StateHeapsAligned left_state ->
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    HeapKeysBounded (state_heap left_state) ->
    TraceDisjoint
      (trace_view_flatten view_left1)
      (trace_view_flatten view_right1) ->
    TraceDisjoint
      (trace_view_flatten view_left2)
      (trace_view_flatten view_right2) ->
    NoAllocTrace (trace_view_flatten view_left1) ->
    NoAllocTrace (trace_view_flatten view_right1) ->
    NoAllocTrace (trace_view_flatten view_left2) ->
    NoAllocTrace (trace_view_flatten view_right2) ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left1
      view_right1
      (StPairParRun
        (StError heap_error_left)
        right_final
        phi_left_final1
        phi_right_final1
        k) ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left2
      view_right2
      (StPairParRun
        (StDone heap_left_done v_left_done)
        (StError heap_error_right)
        phi_left_final2
        phi_right_final2
        k) ->
    False.
Proof.
  intros left_state right_state
    view_left1 view_right1 view_left2 view_right2
    k heap_error_left right_final
    heap_left_done v_left_done heap_error_right
    phi_left_final1 phi_right_final1
    phi_left_final2 phi_right_final2
    HAlignedLeft HAlignedRight HHeapAligned HBounded
    HDisjoint1 HDisjoint2
    HNoAllocLeft1 HNoAllocRight1 HNoAllocLeft2 HNoAllocRight2
    HLeftErrorRun HRightErrorRun.
  destruct
    (ScheduledPairParRun_noalloc_disjoint_left_error_canonical
      left_state right_state [] [] view_left1 view_right1
      k heap_error_left right_final
      phi_left_final1 phi_right_final1
      HAlignedLeft HAlignedRight HHeapAligned HBounded
      HDisjoint1 HNoAllocLeft1 HNoAllocRight1 HLeftErrorRun)
    as (heap_left_error & HLeftError & _HEqLeftError).
  destruct
    (ScheduledPairParRun_noalloc_disjoint_right_error_canonical
      left_state right_state [] [] view_left2 view_right2
      k heap_left_done v_left_done heap_error_right
      phi_left_final2 phi_right_final2
      HAlignedLeft HAlignedRight HHeapAligned HBounded
      HDisjoint2 HNoAllocLeft2 HNoAllocRight2 HRightErrorRun)
    as (heap_left & v_left & heap_right_error &
      HLeftDone & _HRightError & _HHeapRightError).
  destruct
    (Steps_terminal_state_trace_deterministic
      left_state
      (trace_view_flatten view_left1)
      (StError heap_left_error)
      (trace_view_flatten view_left2)
      (StDone heap_left v_left)
      HLeftError
      (TerminalError heap_left_error)
      HLeftDone
      (TerminalDone heap_left v_left))
    as (_HTrace & HState).
  discriminate HState.
Qed.

Theorem TraceCoveredBySummary_disjoint_trace_check_no_fail :
  forall phi_left phi_right theta_left theta_right,
    summary_disjointb theta_left theta_right = true ->
    TraceCoveredBySummary phi_left theta_left ->
    TraceCoveredBySummary phi_right theta_right ->
    trace_disjointb phi_left phi_right = false ->
    False.
Proof.
  assert
    (HDynamicConflictFromBool :
      forall a1 a2,
        dynamic_conflictb a1 a2 = true ->
        dynamic_conflict a1 a2).
  {
    intros [r1 l1 | r1 l1 | r1 l1]
      [r2 l2 | r2 l2 | r2 l2] HConflict;
      simpl in HConflict; try discriminate;
      unfold same_locationb in HConflict;
      apply andb_true_iff in HConflict;
      destruct HConflict as (HRgn & HLoc);
      apply Nat.eqb_eq in HRgn;
      apply Nat.eqb_eq in HLoc;
      subst; constructor; split; reflexivity.
  }
  assert
    (HNoDynamicConflictsWith :
      forall action phi,
        (forall action',
          In action' phi ->
          ~ dynamic_conflict action action') ->
        no_dynamic_conflicts_with action phi = true).
  {
    intros action phi.
    induction phi as [| head tail IH];
      intros HNoConflict; simpl.
    - reflexivity.
    - apply andb_true_intro.
      split.
      + apply negb_true_iff.
        destruct (dynamic_conflictb action head) eqn:HConflictBool.
        * exfalso.
          eapply HNoConflict.
          -- simpl. left. reflexivity.
          -- eapply HDynamicConflictFromBool; eauto.
        * reflexivity.
      + apply IH.
        intros action' HIn HConflict.
        eapply HNoConflict.
        * simpl. right. exact HIn.
        * exact HConflict.
  }
  assert
    (HTraceDisjointBool :
      forall phi1 phi2,
        TraceDisjoint phi1 phi2 ->
        trace_disjointb phi1 phi2 = true).
  {
    intros phi1.
    induction phi1 as [| head tail IH];
      intros phi2 HDisjoint; simpl.
    - reflexivity.
    - apply andb_true_intro.
      split.
      + apply HNoDynamicConflictsWith.
        intros action' HIn.
        eapply HDisjoint.
        * simpl. left. reflexivity.
        * exact HIn.
      + apply IH.
        intros action_left action_right HInLeft HInRight.
        eapply HDisjoint.
        * simpl. right. exact HInLeft.
        * exact HInRight.
  }
  intros phi_left phi_right theta_left theta_right
    HSummaryDisjoint HCoveredLeft HCoveredRight HTraceFail.
  pose proof
    (summary_disjoint_covered_trace_disjoint
      phi_left phi_right theta_left theta_right
      HSummaryDisjoint HCoveredLeft HCoveredRight)
    as HTraceDisjoint.
  pose proof
    (HTraceDisjointBool
      phi_left phi_right HTraceDisjoint)
    as HTracePass.
  rewrite HTraceFail in HTracePass.
  discriminate.
Qed.

Corollary ScheduledPairParRun_done_fail_covered_summaries_impossible :
  forall heap_done heap_error v_left v_right phi_left phi_right
    theta_left theta_right k,
    summary_disjointb theta_left theta_right = true ->
    TraceCoveredBySummary phi_left theta_left ->
    TraceCoveredBySummary phi_right theta_right ->
    ScheduledPairParRun
      (StPairParRun
        (StDone heap_done v_left)
        (StDone heap_done v_right)
        phi_left
        phi_right
        k)
      TraceEmpty
      TraceEmpty
      (StError heap_error) ->
    False.
Proof.
  intros heap_done heap_error v_left v_right phi_left phi_right
    theta_left theta_right k
    HSummaryDisjoint HCoveredLeft HCoveredRight HRun.
  inversion HRun; subst; try discriminate.
  eapply TraceCoveredBySummary_disjoint_trace_check_no_fail; eauto.
Qed.

Corollary ScheduledPairParRun_done_fail_covered_views_impossible :
  forall left_state right_state heap_done heap_error
    v_left v_right phi_left phi_right
    view_left view_right theta_left theta_right k,
    summary_disjointb theta_left theta_right = true ->
    TraceViewCoveredBySummary view_left theta_left ->
    TraceViewCoveredBySummary view_right theta_right ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left
      view_right
      (StPairParRun
        (StDone heap_done v_left)
        (StDone heap_done v_right)
        phi_left
        phi_right
        k) ->
    ScheduledPairParRun
      (StPairParRun
        (StDone heap_done v_left)
        (StDone heap_done v_right)
        phi_left
        phi_right
        k)
      TraceEmpty
      TraceEmpty
      (StError heap_error) ->
    False.
Proof.
  intros left_state right_state heap_done heap_error
    v_left v_right phi_left phi_right
    view_left view_right theta_left theta_right k
    HSummaryDisjoint HCoveredLeft HCoveredRight
    HPrefix HFail.
  destruct
    (ScheduledPairParRun_pairpar_empty_accumulators
      left_state right_state k view_left view_right
      (StDone heap_done v_left)
      (StDone heap_done v_right)
      phi_left phi_right HPrefix)
    as (HLeftAcc & HRightAcc).
  subst phi_left phi_right.
  unfold TraceViewCoveredBySummary in *.
  eapply ScheduledPairParRun_done_fail_covered_summaries_impossible;
    eauto.
Qed.

Corollary ScheduledPairParRun_checked_pairpar_done_fail_impossible :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    heap_done heap_error v_left v_right
    phi_left phi_right view_left view_right theta_left theta_right k,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    summary_disjointb theta_left theta_right = true ->
    TraceViewCoveredBySummary view_left theta_left ->
    TraceViewCoveredBySummary view_right theta_right ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left
      view_right
      (StPairParRun
        (StDone heap_done v_left)
        (StDone heap_done v_right)
        phi_left
        phi_right
        k) ->
    ScheduledPairParRun
      (StPairParRun
        (StDone heap_done v_left)
        (StDone heap_done v_right)
        phi_left
        phi_right
        k)
      TraceEmpty
      TraceEmpty
      (StError heap_error) ->
    False.
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    heap_done heap_error v_left v_right
    phi_left phi_right view_left view_right theta_left theta_right k
    _HBack _HContext HSummaryDisjoint HCoveredLeft HCoveredRight
    HPrefix HFail.
  eapply
    (ScheduledPairParRun_done_fail_covered_views_impossible
      (InitialState heap env rho (EMuApp ef1 ea1))
      (InitialState heap env rho (EMuApp ef2 ea2))
      heap_done heap_error v_left v_right
      phi_left phi_right view_left view_right
      theta_left theta_right k);
    eauto.
Qed.

Lemma ScheduledPairParRun_error_base_classification :
  forall left_state right_state phi_left phi_right k
    view_left view_right heap_error,
    ScheduledPairParRun
      (StPairParRun left_state right_state phi_left phi_right k)
      view_left
      view_right
      (StError heap_error) ->
    (exists right_final phi_left_final phi_right_final,
      ScheduledPairParRun
        (StPairParRun left_state right_state phi_left phi_right k)
        view_left
        view_right
        (StPairParRun
          (StError heap_error)
          right_final
          phi_left_final
          phi_right_final
          k)) \/
    (exists heap_left v_left phi_left_final phi_right_final,
      ScheduledPairParRun
        (StPairParRun left_state right_state phi_left phi_right k)
        view_left
        view_right
        (StPairParRun
          (StDone heap_left v_left)
          (StError heap_error)
          phi_left_final
          phi_right_final
          k)) \/
    (exists heap_done v_left v_right phi_left_final phi_right_final,
      ScheduledPairParRun
        (StPairParRun left_state right_state phi_left phi_right k)
        view_left
        view_right
        (StPairParRun
          (StDone heap_done v_left)
          (StDone heap_done v_right)
          phi_left_final
          phi_right_final
          k) /\
      trace_disjointb phi_left_final phi_right_final = false /\
      heap_error = heap_done).
Proof.
  intros left_state right_state phi_left phi_right k
    view_left view_right heap_error HRun.
  remember
    (StPairParRun left_state right_state phi_left phi_right k)
    as state_start eqn:HStart.
  remember (StError heap_error) as state_error eqn:HError.
  revert left_state right_state phi_left phi_right k heap_error
    HStart HError.
  induction HRun; intros left0 right0 phi_left0 phi_right0 k0
    heap_error0 HStart HError.
  - rewrite HStart in HError.
    discriminate.
  - pose proof HError as HErrorTail.
    inversion HStart; subst.
    destruct
      (IHHRun
        left_state'
        (with_state_heap (state_heap left_state') right0)
        (phi_left0 ++ label_trace label)
        phi_right0
        k0
        heap_error0
        eq_refl
        HErrorTail)
      as [(right_final & phi_left_final & phi_right_final & HPrefix)
        | [(heap_left & v_left & phi_left_final & phi_right_final & HPrefix)
          | (heap_done & v_left & v_right &
             phi_left_final & phi_right_final &
             HPrefix & HFail & HHeap)]].
    + left.
      exists right_final, phi_left_final, phi_right_final.
      eapply SchedPairParRunLeft; eauto.
    + right. left.
      exists heap_left, v_left, phi_left_final, phi_right_final.
      eapply SchedPairParRunLeft; eauto.
    + right. right.
      exists heap_done, v_left, v_right, phi_left_final, phi_right_final.
      repeat split; try assumption.
      eapply SchedPairParRunLeft; eauto.
  - pose proof HError as HErrorTail.
    inversion HStart; subst.
    destruct
      (IHHRun
        (with_state_heap (state_heap right_state') left0)
        right_state'
        phi_left0
        (phi_right0 ++ label_trace label)
        k0
        heap_error0
        eq_refl
        HErrorTail)
      as [(right_final & phi_left_final & phi_right_final & HPrefix)
        | [(heap_left & v_left & phi_left_final & phi_right_final & HPrefix)
          | (heap_done & v_left & v_right &
             phi_left_final & phi_right_final &
             HPrefix & HFail & HHeap)]].
    + left.
      exists right_final, phi_left_final, phi_right_final.
      eapply SchedPairParRunRight; eauto.
    + right. left.
      exists heap_left, v_left, phi_left_final, phi_right_final.
      eapply SchedPairParRunRight; eauto.
    + right. right.
      exists heap_done, v_left, v_right, phi_left_final, phi_right_final.
      repeat split; try assumption.
      eapply SchedPairParRunRight; eauto.
  - inversion HStart; subst.
    inversion HError; subst.
    left.
    exists right0, phi_left0, phi_right0.
    constructor.
  - inversion HStart; subst.
    inversion HError; subst.
    right. left.
    exists heap_left, v_left, phi_left0, phi_right0.
    constructor.
  - inversion HStart; subst.
    discriminate.
  - inversion HStart; subst.
    inversion HError; subst.
    right. right.
    exists heap_error0, v_left, v_right, phi_left0, phi_right0.
    repeat split; try constructor; try assumption; reflexivity.
Qed.

Corollary ScheduledPairParRun_checked_pairpar_error_is_branch_error :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    heap_error view_left view_right theta_left theta_right k,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    summary_disjointb theta_left theta_right = true ->
    TraceViewCoveredBySummary view_left theta_left ->
    TraceViewCoveredBySummary view_right theta_right ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left
      view_right
      (StError heap_error) ->
    (exists right_final phi_left_final phi_right_final,
      ScheduledPairParRun
        (StPairParRun
          (InitialState heap env rho (EMuApp ef1 ea1))
          (InitialState heap env rho (EMuApp ef2 ea2))
          [] [] k)
        view_left
        view_right
        (StPairParRun
          (StError heap_error)
          right_final
          phi_left_final
          phi_right_final
          k)) \/
    (exists heap_left v_left phi_left_final phi_right_final,
      ScheduledPairParRun
        (StPairParRun
          (InitialState heap env rho (EMuApp ef1 ea1))
          (InitialState heap env rho (EMuApp ef2 ea2))
          [] [] k)
        view_left
        view_right
        (StPairParRun
          (StDone heap_left v_left)
          (StError heap_error)
          phi_left_final
          phi_right_final
          k)).
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    heap_error view_left view_right theta_left theta_right k
    _HBack _HContext HSummaryDisjoint HCoveredLeft HCoveredRight HRun.
  destruct
    (ScheduledPairParRun_error_base_classification
      (InitialState heap env rho (EMuApp ef1 ea1))
      (InitialState heap env rho (EMuApp ef2 ea2))
      [] [] k view_left view_right heap_error HRun)
    as [HLeftError | [HRightError | HDoneFail]].
  - left. exact HLeftError.
  - right. exact HRightError.
  - destruct HDoneFail as
      (heap_done & v_left & v_right &
        phi_left_final & phi_right_final &
        HPrefix & HFail & HHeap).
    subst heap_error.
    exfalso.
    eapply
      (ScheduledPairParRun_done_fail_covered_views_impossible
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        heap_done heap_done v_left v_right
        phi_left_final phi_right_final
        view_left view_right theta_left theta_right k);
      eauto.
    apply SchedPairParRunDoneFail.
    exact HFail.
Qed.

Lemma ScheduledPairParRun_noalloc_disjoint_canonical :
  forall left_state right_state phi_left_acc phi_right_acc
    view_left view_right k heap value,
    StateHeapsAligned left_state ->
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    HeapKeysBounded (state_heap left_state) ->
    TraceDisjoint
      (phi_left_acc ++ trace_view_flatten view_left)
      (phi_right_acc ++ trace_view_flatten view_right) ->
    NoAllocTrace (trace_view_flatten view_left) ->
    NoAllocTrace (trace_view_flatten view_right) ->
    ScheduledPairParRun
      (StPairParRun left_state right_state phi_left_acc phi_right_acc k)
      view_left
      view_right
      (StReturn heap value k) ->
    exists heap_left heap_canonical v_left v_right,
      value = VPair v_left v_right /\
      Steps left_state (trace_view_flatten view_left)
        (StDone heap_left v_left) /\
      Steps (with_state_heap heap_left right_state)
        (trace_view_flatten view_right)
        (StDone heap_canonical v_right) /\
      heap = heap_canonical.
Proof.
  assert
    (HTraceDisjointSym :
      forall phi1 phi2,
        TraceDisjoint phi1 phi2 ->
        TraceDisjoint phi2 phi1).
  {
    intros phi1 phi2 HDisjoint a2 a1 HIn2 HIn1 HConflict.
    apply (HDisjoint a1 a2 HIn1 HIn2).
    inversion HConflict; subst;
      match goal with
      | HSame : same_location _ _ _ _ |- _ =>
          destruct HSame as [-> ->]
      end;
      constructor; split; reflexivity.
  }
  intros left_state right_state phi_left_acc phi_right_acc
    view_left view_right k heap value
    HAlignedLeft HAlignedRight HHeapAligned HBounded HDisjointFinal
    HNoAllocLeft HNoAllocRight HRun.
  remember
    (StPairParRun left_state right_state phi_left_acc phi_right_acc k)
    as state_start eqn:HStart.
  remember (StReturn heap value k) as state_final eqn:HFinal.
  revert left_state right_state phi_left_acc phi_right_acc k heap value
    HAlignedLeft HAlignedRight HHeapAligned HBounded HDisjointFinal
    HNoAllocLeft HNoAllocRight
    HStart HFinal.
  induction HRun; intros left0 right0 phi_left0 phi_right0 k0 heap0 value0
    HAlignedLeft HAlignedRight HHeapAligned HBounded HDisjointFinal
    HNoAllocLeft HNoAllocRight
    HStart HFinal.
  - rewrite HStart in HFinal. inversion HFinal.
  - inversion HStart; subst.
    simpl in HNoAllocLeft.
    rewrite label_view_flatten in HNoAllocLeft.
    pose proof
      (no_alloc_trace_app_l
        (label_trace label) (trace_view_flatten view_left)
        HNoAllocLeft)
      as HNoAllocLabel.
    pose proof
      (no_alloc_trace_app_r
        (label_trace label) (trace_view_flatten view_left)
        HNoAllocLeft)
      as HNoAllocLeftTail.
    assert
      (HDisjointTail :
        TraceDisjoint
          ((phi_left0 ++ label_trace label) ++
            trace_view_flatten view_left)
          (phi_right0 ++ trace_view_flatten view_right)).
    {
      simpl in HDisjointFinal.
      rewrite label_view_flatten in HDisjointFinal.
      rewrite app_assoc in HDisjointFinal.
      exact HDisjointFinal.
    }
    pose proof
      (Step_preserves_alignment
        left0 label left_state' H0 HAlignedLeft)
      as HAlignedLeft'.
    pose proof
      (Step_preserves_heap_bounded_aligned
        left0 label left_state' H0 HAlignedLeft HBounded)
      as HBoundedLeft'.
    assert
      (HAlignedRightRebased :
        StateHeapsAligned
          (with_state_heap (state_heap left_state') right0)).
    {
      destruct
        (with_state_heap_aligned
          (state_heap left_state') right0 HAlignedRight)
        as (HAligned & _).
      exact HAligned.
    }
    assert
      (HHeapTail :
        state_heap left_state' =
        state_heap (with_state_heap (state_heap left_state') right0)).
    {
      rewrite state_heap_with_state_heap.
      reflexivity.
    }
    destruct
      (IHHRun
        left_state'
        (with_state_heap (state_heap left_state') right0)
        (phi_left0 ++ label_trace label)
        phi_right0
        k0 heap0 value0
        HAlignedLeft'
        HAlignedRightRebased
        HHeapTail
        HBoundedLeft'
        HDisjointTail
        HNoAllocLeftTail
        HNoAllocRight
        eq_refl
        eq_refl)
      as (heap_left & heap_canonical & v_left & v_right &
        HValue & HLeftTail & HRightCanonical & HHeap).
    exists heap_left, heap_canonical, v_left, v_right.
    split; [exact HValue |].
    split.
    + simpl.
      rewrite label_view_flatten.
      eapply StepsStep; eauto.
    + split.
      * rewrite with_state_heap_twice in HRightCanonical.
        exact HRightCanonical.
      * exact HHeap.
  - inversion HStart; subst.
    simpl in HNoAllocRight.
    rewrite label_view_flatten in HNoAllocRight.
    pose proof
      (no_alloc_trace_app_l
        (label_trace label) (trace_view_flatten view_right)
        HNoAllocRight)
      as HNoAllocLabel.
    pose proof
      (no_alloc_trace_app_r
        (label_trace label) (trace_view_flatten view_right)
        HNoAllocRight)
      as HNoAllocRightTail.
    assert
      (HDisjointTail :
        TraceDisjoint
          (phi_left0 ++ trace_view_flatten view_left)
          ((phi_right0 ++ label_trace label) ++
            trace_view_flatten view_right)).
    {
      simpl in HDisjointFinal.
      rewrite label_view_flatten in HDisjointFinal.
      rewrite app_assoc in HDisjointFinal.
      exact HDisjointFinal.
    }
    assert
      (HDisjointLeftLabel :
        TraceDisjoint
          (trace_view_flatten view_left)
          (label_trace label)).
    {
      destruct
        (TraceDisjoint_app_l
          phi_left0
          (trace_view_flatten view_left)
          ((phi_right0 ++ label_trace label) ++
            trace_view_flatten view_right)
          HDisjointTail)
        as (_ & HLeftRemainingRightFinal).
      destruct
        (TraceDisjoint_app_r
          (trace_view_flatten view_left)
          (phi_right0 ++ label_trace label)
          (trace_view_flatten view_right)
          HLeftRemainingRightFinal)
        as (HLeftRemainingRightAccLabel & _).
      destruct
        (TraceDisjoint_app_r
          (trace_view_flatten view_left)
          phi_right0
          (label_trace label)
          HLeftRemainingRightAccLabel)
        as (_ & HLeftLabel).
      exact HLeftLabel.
    }
    pose proof
      (HTraceDisjointSym
        (trace_view_flatten view_left)
        (label_trace label)
        HDisjointLeftLabel)
      as HDisjointLabelLeft.
    pose proof
      (Step_preserves_alignment
        right0 label right_state' H0 HAlignedRight)
      as HAlignedRight'.
    assert
      (HAlignedLeftRebased :
        StateHeapsAligned
          (with_state_heap (state_heap right_state') left0)).
    {
      destruct
        (with_state_heap_aligned
          (state_heap right_state') left0 HAlignedLeft)
        as (HAligned & _).
      exact HAligned.
    }
    assert
      (HHeapTail :
        state_heap (with_state_heap (state_heap right_state') left0) =
        state_heap right_state').
    {
      rewrite state_heap_with_state_heap.
      reflexivity.
    }
    assert (HBoundedRight : HeapKeysBounded (state_heap right0)).
    {
      rewrite <- HHeapAligned.
      exact HBounded.
    }
    pose proof
      (Step_preserves_heap_bounded_aligned
        right0 label right_state' H0 HAlignedRight HBoundedRight)
      as HBoundedRight'.
    assert
      (HBoundedTail :
        HeapKeysBounded
          (state_heap
            (with_state_heap (state_heap right_state') left0))).
    {
      rewrite state_heap_with_state_heap.
      exact HBoundedRight'.
    }
    destruct
      (IHHRun
        (with_state_heap (state_heap right_state') left0)
        right_state'
        phi_left0
        (phi_right0 ++ label_trace label)
        k0 heap0 value0
        HAlignedLeftRebased
        HAlignedRight'
        HHeapTail
        HBoundedTail
        HDisjointTail
        HNoAllocLeft
        HNoAllocRightTail
        eq_refl
        eq_refl)
      as (heap_after_right_left & heap_tail_scheduled &
        v_left & v_right &
        HValue & HLeftAfterRight & HRightTailScheduled &
        HHeapScheduledTail).
    destruct
      (Steps_to_StepsN
        (with_state_heap (state_heap right_state') left0)
        (trace_view_flatten view_left)
        (StDone heap_after_right_left v_left)
        HLeftAfterRight)
      as (n_left & HLeftAfterRightN).
    destruct
      (StepsN_noalloc_disjoint_step_after_run
        n_left
        left0
        right0
        label
        right_state'
        (trace_view_flatten view_left)
        heap_after_right_left
        v_left
        HHeapAligned
        HAlignedLeft
        HAlignedRight
        HBounded
        H0
        HLeftAfterRightN
        HNoAllocLabel
        HNoAllocLeft
        HDisjointLabelLeft
        HDisjointLeftLabel)
      as (heap_left & heap_after_left_right &
        HLeftCanonicalN & HRightStepAfterLeft & HHeapCommute).
    subst heap_after_right_left.
    destruct
      (Steps_to_StepsN
        (with_state_heap heap_after_left_right right_state')
        (trace_view_flatten view_right)
        (StDone heap_tail_scheduled v_right)
        HRightTailScheduled)
      as (n_right & HRightTailScheduledN).
    exists heap_left, heap_tail_scheduled, v_left, v_right.
    split; [exact HValue |].
    split.
    + eapply StepsN_to_Steps.
      exact HLeftCanonicalN.
    + split.
      * simpl.
        rewrite label_view_flatten.
        eapply StepsStep.
        -- exact HRightStepAfterLeft.
        -- eapply StepsN_to_Steps.
           exact HRightTailScheduledN.
      * exact HHeapScheduledTail.
  - discriminate.
  - discriminate.
  - inversion HStart; subst.
    inversion HFinal; subst.
    exists heap0, heap0, v_left, v_right.
    repeat split; try constructor; try reflexivity.
  - discriminate.
Qed.

Lemma ScheduledPairParRun_noalloc_checked_canonical :
  forall left_state right_state phi_left_acc phi_right_acc
    view_left view_right theta_left theta_right k heap value,
    StateHeapsAligned left_state ->
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    HeapKeysBounded (state_heap left_state) ->
    summary_disjointb theta_left theta_right = true ->
    TraceCoveredBySummary
      (phi_left_acc ++ trace_view_flatten view_left) theta_left ->
    TraceCoveredBySummary
      (phi_right_acc ++ trace_view_flatten view_right) theta_right ->
    NoAllocTrace (trace_view_flatten view_left) ->
    NoAllocTrace (trace_view_flatten view_right) ->
    ScheduledPairParRun
      (StPairParRun left_state right_state phi_left_acc phi_right_acc k)
      view_left
      view_right
      (StReturn heap value k) ->
    exists heap_left heap_canonical v_left v_right,
      value = VPair v_left v_right /\
      Steps left_state (trace_view_flatten view_left)
        (StDone heap_left v_left) /\
      Steps (with_state_heap heap_left right_state)
        (trace_view_flatten view_right)
        (StDone heap_canonical v_right) /\
      heap = heap_canonical.
Proof.
  intros left_state right_state phi_left_acc phi_right_acc
    view_left view_right theta_left theta_right k heap value
    HAlignedLeft HAlignedRight HHeapAligned HBounded HSummaryDisjoint
    HCoveredLeft HCoveredRight HNoAllocLeft HNoAllocRight HRun.
  eapply
    (ScheduledPairParRun_noalloc_disjoint_canonical
      left_state right_state phi_left_acc phi_right_acc
      view_left view_right k heap value); eauto.
  eapply summary_disjoint_covered_trace_disjoint; eauto.
Qed.

Lemma HeapNeutralTraceView_seq_label :
  forall label view,
    HeapNeutralTraceView (TraceSeq (label_view label) view) ->
    HeapNeutralTrace (label_trace label).
Proof.
  intros label view HNeutral.
  unfold HeapNeutralTraceView in HNeutral.
  simpl in HNeutral.
  rewrite label_view_flatten in HNeutral.
  eapply heap_neutral_trace_app_l; eauto.
Qed.

Lemma HeapNeutralTraceView_seq_tail :
  forall label view,
    HeapNeutralTraceView (TraceSeq (label_view label) view) ->
    HeapNeutralTraceView view.
Proof.
  intros label view HNeutral.
  unfold HeapNeutralTraceView in *.
  simpl in HNeutral.
  rewrite label_view_flatten in HNeutral.
  eapply heap_neutral_trace_app_r; eauto.
Qed.

Lemma NoAllocTraceView_empty :
  NoAllocTraceView TraceEmpty.
Proof.
  unfold NoAllocTraceView.
  simpl.
  apply no_alloc_trace_nil.
Qed.

Lemma NoAllocTraceView_seq :
  forall label view,
    NoAllocTrace (label_trace label) ->
    NoAllocTraceView view ->
    NoAllocTraceView (TraceSeq (label_view label) view).
Proof.
  intros label view HNoAllocLabel HNoAllocView.
  unfold NoAllocTraceView in *.
  simpl.
  rewrite label_view_flatten.
  eapply no_alloc_trace_app; eauto.
Qed.

Lemma ScheduledPairParRun_noalloc_views_from_shapes :
  forall left_state right_state phi_left phi_right k
    view_left view_right state_final store ty_left ty_right,
    NoAllocStateShape store left_state ty_left ->
    NoAllocStateShape store right_state ty_right ->
    state_heap left_state = state_heap right_state ->
    ScheduledPairParRun
      (StPairParRun left_state right_state phi_left phi_right k)
      view_left
      view_right
      state_final ->
    NoAllocTraceView view_left /\ NoAllocTraceView view_right.
Proof.
  intros left_state right_state phi_left phi_right k
    view_left view_right state_final store ty_left ty_right
    HLeft HRight HHeapAligned HRun.
  remember
    (StPairParRun left_state right_state phi_left phi_right k)
    as state_start eqn:HStart.
  revert left_state right_state phi_left phi_right k store ty_left ty_right
    HLeft HRight HHeapAligned HStart.
  induction HRun; intros left0 right0 phi_left0 phi_right0 k0
    store ty_left ty_right HLeft HRight HHeapAligned HStart.
  - inversion HStart; subst.
    split; apply NoAllocTraceView_empty.
  - inversion HStart; subst.
    destruct
      (NoAllocStateShape_step_preservation
        left0 label left_state' store ty_left H0 HLeft)
      as (HNoAllocLabel & HLeft' & HTransport).
    assert
      (HRight' :
        NoAllocStateShape store
          (with_state_heap (state_heap left_state') right0)
          ty_right).
    {
      eapply HTransport; eauto.
    }
    assert
      (HHeapTail :
        state_heap left_state' =
        state_heap
          (with_state_heap (state_heap left_state') right0)).
    {
      rewrite state_heap_with_state_heap.
      reflexivity.
    }
    destruct
      (IHHRun
        left_state'
        (with_state_heap (state_heap left_state') right0)
        (phi_left0 ++ label_trace label)
        phi_right0
        k0
        store
        ty_left
        ty_right
        HLeft'
        HRight'
        HHeapTail
        eq_refl)
      as (HNoAllocLeft & HNoAllocRight).
    split.
    + eapply NoAllocTraceView_seq; eauto.
    + exact HNoAllocRight.
  - inversion HStart; subst.
    destruct
      (NoAllocStateShape_step_preservation
        right0 label right_state' store ty_right H0 HRight)
      as (HNoAllocLabel & HRight' & HTransport).
    assert
      (HLeft' :
        NoAllocStateShape store
          (with_state_heap (state_heap right_state') left0)
          ty_left).
    {
      eapply HTransport.
      - exact HHeapAligned.
      - exact HLeft.
    }
    assert
      (HHeapTail :
        state_heap
          (with_state_heap (state_heap right_state') left0) =
        state_heap right_state').
    {
      rewrite state_heap_with_state_heap.
      reflexivity.
    }
    destruct
      (IHHRun
        (with_state_heap (state_heap right_state') left0)
        right_state'
        phi_left0
        (phi_right0 ++ label_trace label)
        k0
        store
        ty_left
        ty_right
        HLeft'
        HRight'
        HHeapTail
        eq_refl)
      as (HNoAllocLeft & HNoAllocRight).
    split.
    + exact HNoAllocLeft.
    + eapply NoAllocTraceView_seq; eauto.
  - inversion HStart; subst.
    split; apply NoAllocTraceView_empty.
  - inversion HStart; subst.
    split; apply NoAllocTraceView_empty.
  - inversion HStart; subst.
    split; apply NoAllocTraceView_empty.
  - inversion HStart; subst.
    split; apply NoAllocTraceView_empty.
Qed.

Corollary ScheduledPairParRun_checked_pairpar_noalloc_views :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left view_right state_final k,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left
      view_right
      state_final ->
    NoAllocTraceView view_left /\ NoAllocTraceView view_right.
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left view_right state_final k HBack HContext HRun.
  pose proof HContext as HContextFacts.
  destruct HContextFacts as
    (_HHeap & _HEnv & _HRegHeap & _HRegEnv &
      HStoreExists & HRho & _HBounded).
  destruct HStoreExists as (store & HStore).
  destruct
    (CBT_PairPar_components
      gamma omega ef1 ea1 ef2 ea2 HBack)
    as (ty_left & ty_right & eff_left & eff_right &
      _eff_summary_left & _eff_summary_right &
      HCheckedLeft & HCheckedRight &
      _HCheckedSummaryLeft & _HCheckedSummaryRight &
      _HNeutralSummaryLeft & _HNeutralSummaryRight &
      HNoAllocLeft & HNoAllocRight &
      _HBackLeft & _HBackRight).
  destruct
    (ResolveTy_exists
      0 omega rho ty_left HRho
      (CheckedTcExp_ty_wf
        gamma omega (EMuApp ef1 ea1) ty_left eff_left
        HCheckedLeft))
    as (ty_left_res & HResolveTyLeft).
  destruct
    (ResolveTy_exists
      0 omega rho ty_right HRho
      (CheckedTcExp_ty_wf
        gamma omega (EMuApp ef2 ea2) ty_right eff_right
        HCheckedRight))
    as (ty_right_res & HResolveTyRight).
  destruct
    (ResolveStaticEffect_exists
      0 omega rho eff_left HRho
      (CheckedTcExp_eff_wf
        gamma omega (EMuApp ef1 ea1) ty_left eff_left
        HCheckedLeft))
    as (eff_left_res & HResolveEffLeft).
  destruct
    (ResolveStaticEffect_exists
      0 omega rho eff_right HRho
      (CheckedTcExp_eff_wf
        gamma omega (EMuApp ef2 ea2) ty_right eff_right
        HCheckedRight))
    as (eff_right_res & HResolveEffRight).
  assert (HNoAllocLeftRes : static_noalloc eff_left_res).
  {
    eapply ResolveStaticEffect_static_noalloc; eauto.
  }
  assert (HNoAllocRightRes : static_noalloc eff_right_res).
  {
    eapply ResolveStaticEffect_static_noalloc; eauto.
  }
  assert
    (HLeftShape :
      NoAllocStateShape store
        (InitialState heap env rho (EMuApp ef1 ea1))
        ty_left_res).
  {
    unfold InitialState.
    eapply NAS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty_left) (eff := eff_left)
      (eff_res := eff_left_res);
      eauto.
    constructor.
  }
  assert
    (HRightShape :
      NoAllocStateShape store
        (InitialState heap env rho (EMuApp ef2 ea2))
        ty_right_res).
  {
    unfold InitialState.
    eapply NAS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty_right) (eff := eff_right)
      (eff_res := eff_right_res);
      eauto.
    constructor.
  }
  eapply
    (ScheduledPairParRun_noalloc_views_from_shapes
      (InitialState heap env rho (EMuApp ef1 ea1))
      (InitialState heap env rho (EMuApp ef2 ea2))
      [] [] k view_left view_right state_final
      store ty_left_res ty_right_res);
    eauto.
Qed.

Corollary
  ScheduledPairParRun_checked_pairpar_left_error_footprint_deterministic :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k
    heap_error1 heap_error2
    right_final1 right_final2
    phi_left_final1 phi_right_final1
    phi_left_final2 phi_right_final2,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    summary_disjointb theta_left theta_right = true ->
    TraceViewCoveredBySummary view_left1 theta_left ->
    TraceViewCoveredBySummary view_right1 theta_right ->
    TraceViewCoveredBySummary view_left2 theta_left ->
    TraceViewCoveredBySummary view_right2 theta_right ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left1
      view_right1
      (StPairParRun
        (StError heap_error1)
        right_final1
        phi_left_final1
        phi_right_final1
        k) ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left2
      view_right2
      (StPairParRun
        (StError heap_error2)
        right_final2
        phi_left_final2
        phi_right_final2
        k) ->
    HeapEqOn
      (fun r l =>
        TraceDoesNotWrite r l (trace_view_flatten view_right1) /\
        TraceDoesNotWrite r l (trace_view_flatten view_right2))
      heap_error1
      heap_error2.
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k
    heap_error1 heap_error2
    right_final1 right_final2
    phi_left_final1 phi_right_final1
    phi_left_final2 phi_right_final2
    HBack HContext HSummaryDisjoint
    HCoveredLeft1 HCoveredRight1 HCoveredLeft2 HCoveredRight2
    HRun1 HRun2.
  pose proof HContext as HContextFacts.
  destruct HContextFacts as
    (_HHeap & _HEnv & _HRegHeap & _HRegEnv &
      _HStore & _HRho & HBounded).
  destruct
    (ScheduledPairParRun_checked_pairpar_noalloc_views
      gamma omega rho heap env ef1 ea1 ef2 ea2
      view_left1 view_right1
      (StPairParRun
        (StError heap_error1)
        right_final1
        phi_left_final1
        phi_right_final1
        k)
      k HBack HContext HRun1)
    as (HNoAllocLeft1 & HNoAllocRight1).
  destruct
    (ScheduledPairParRun_checked_pairpar_noalloc_views
      gamma omega rho heap env ef1 ea1 ef2 ea2
      view_left2 view_right2
      (StPairParRun
        (StError heap_error2)
        right_final2
        phi_left_final2
        phi_right_final2
        k)
      k HBack HContext HRun2)
    as (HNoAllocLeft2 & HNoAllocRight2).
  pose proof
    (summary_disjoint_covered_trace_disjoint
      (trace_view_flatten view_left1)
      (trace_view_flatten view_right1)
      theta_left theta_right
      HSummaryDisjoint HCoveredLeft1 HCoveredRight1)
    as HDisjoint1.
  pose proof
    (summary_disjoint_covered_trace_disjoint
      (trace_view_flatten view_left2)
      (trace_view_flatten view_right2)
      theta_left theta_right
      HSummaryDisjoint HCoveredLeft2 HCoveredRight2)
    as HDisjoint2.
  eapply
    (ScheduledPairParRun_noalloc_disjoint_left_error_footprint_deterministic
      (InitialState heap env rho (EMuApp ef1 ea1))
      (InitialState heap env rho (EMuApp ef2 ea2))
      view_left1 view_right1 view_left2 view_right2
      k heap_error1 heap_error2
      right_final1 right_final2
      phi_left_final1 phi_right_final1
      phi_left_final2 phi_right_final2);
    simpl; eauto.
Qed.

Corollary
  ScheduledPairParRun_checked_pairpar_left_error_read_only_right_heap_lookup_deterministic :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k
    heap_error1 heap_error2
    right_final1 right_final2
    phi_left_final1 phi_right_final1
    phi_left_final2 phi_right_final2,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    summary_disjointb theta_left theta_right = true ->
    TraceViewCoveredBySummary view_left1 theta_left ->
    TraceViewCoveredBySummary view_right1 theta_right ->
    TraceViewCoveredBySummary view_left2 theta_left ->
    TraceViewCoveredBySummary view_right2 theta_right ->
    ReadOnlyTraceView view_right1 ->
    ReadOnlyTraceView view_right2 ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left1
      view_right1
      (StPairParRun
        (StError heap_error1)
        right_final1
        phi_left_final1
        phi_right_final1
        k) ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left2
      view_right2
      (StPairParRun
        (StError heap_error2)
        right_final2
        phi_left_final2
        phi_right_final2
        k) ->
    HeapEqOn (fun _ _ => True) heap_error1 heap_error2.
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k
    heap_error1 heap_error2
    right_final1 right_final2
    phi_left_final1 phi_right_final1
    phi_left_final2 phi_right_final2
    HBack HContext HSummaryDisjoint
    HCoveredLeft1 HCoveredRight1 HCoveredLeft2 HCoveredRight2
    HReadOnlyRight1 HReadOnlyRight2 HRun1 HRun2.
  eapply
    (HeapEqOn_weaken
      (fun _ _ => True)
      (fun r l =>
        TraceDoesNotWrite r l (trace_view_flatten view_right1) /\
        TraceDoesNotWrite r l (trace_view_flatten view_right2))).
  - intros r l _HAny.
    split.
    + unfold ReadOnlyTraceView, ReadOnlyTrace,
        TraceDoesNotWrite in *.
      apply HReadOnlyRight1.
    + unfold ReadOnlyTraceView, ReadOnlyTrace,
        TraceDoesNotWrite in *.
      apply HReadOnlyRight2.
  - eapply
      (ScheduledPairParRun_checked_pairpar_left_error_footprint_deterministic
        gamma omega rho heap env ef1 ea1 ef2 ea2
        view_left1 view_right1 view_left2 view_right2
        theta_left theta_right k
        heap_error1 heap_error2
        right_final1 right_final2
        phi_left_final1 phi_right_final1
        phi_left_final2 phi_right_final2);
      eauto.
Qed.

Corollary
  ScheduledPairParRun_checked_pairpar_right_error_heap_deterministic :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k
    heap_left_done1 heap_left_done2
    v_left_done1 v_left_done2
    heap_error1 heap_error2
    phi_left_final1 phi_right_final1
    phi_left_final2 phi_right_final2,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    summary_disjointb theta_left theta_right = true ->
    TraceViewCoveredBySummary view_left1 theta_left ->
    TraceViewCoveredBySummary view_right1 theta_right ->
    TraceViewCoveredBySummary view_left2 theta_left ->
    TraceViewCoveredBySummary view_right2 theta_right ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left1
      view_right1
      (StPairParRun
        (StDone heap_left_done1 v_left_done1)
        (StError heap_error1)
        phi_left_final1
        phi_right_final1
        k) ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left2
      view_right2
      (StPairParRun
        (StDone heap_left_done2 v_left_done2)
        (StError heap_error2)
        phi_left_final2
        phi_right_final2
        k) ->
    heap_error1 = heap_error2.
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k
    heap_left_done1 heap_left_done2
    v_left_done1 v_left_done2
    heap_error1 heap_error2
    phi_left_final1 phi_right_final1
    phi_left_final2 phi_right_final2
    HBack HContext HSummaryDisjoint
    HCoveredLeft1 HCoveredRight1 HCoveredLeft2 HCoveredRight2
    HRun1 HRun2.
  pose proof HContext as HContextFacts.
  destruct HContextFacts as
    (_HHeap & _HEnv & _HRegHeap & _HRegEnv &
      _HStore & _HRho & HBounded).
  destruct
    (ScheduledPairParRun_checked_pairpar_noalloc_views
      gamma omega rho heap env ef1 ea1 ef2 ea2
      view_left1 view_right1
      (StPairParRun
        (StDone heap_left_done1 v_left_done1)
        (StError heap_error1)
        phi_left_final1
        phi_right_final1
        k)
      k HBack HContext HRun1)
    as (HNoAllocLeft1 & HNoAllocRight1).
  destruct
    (ScheduledPairParRun_checked_pairpar_noalloc_views
      gamma omega rho heap env ef1 ea1 ef2 ea2
      view_left2 view_right2
      (StPairParRun
        (StDone heap_left_done2 v_left_done2)
        (StError heap_error2)
        phi_left_final2
        phi_right_final2
        k)
      k HBack HContext HRun2)
    as (HNoAllocLeft2 & HNoAllocRight2).
  pose proof
    (summary_disjoint_covered_trace_disjoint
      (trace_view_flatten view_left1)
      (trace_view_flatten view_right1)
      theta_left theta_right
      HSummaryDisjoint HCoveredLeft1 HCoveredRight1)
    as HDisjoint1.
  pose proof
    (summary_disjoint_covered_trace_disjoint
      (trace_view_flatten view_left2)
      (trace_view_flatten view_right2)
      theta_left theta_right
      HSummaryDisjoint HCoveredLeft2 HCoveredRight2)
    as HDisjoint2.
  eapply
    (ScheduledPairParRun_noalloc_disjoint_right_error_heap_deterministic
      (InitialState heap env rho (EMuApp ef1 ea1))
      (InitialState heap env rho (EMuApp ef2 ea2))
      view_left1 view_right1 view_left2 view_right2
      k heap_left_done1 heap_left_done2
      v_left_done1 v_left_done2
      heap_error1 heap_error2
      phi_left_final1 phi_right_final1
      phi_left_final2 phi_right_final2);
    simpl; eauto.
Qed.

Corollary ScheduledPairParRun_checked_pairpar_left_right_error_impossible :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k
    heap_error_left right_final
    heap_left_done v_left_done heap_error_right
    phi_left_final1 phi_right_final1
    phi_left_final2 phi_right_final2,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    summary_disjointb theta_left theta_right = true ->
    TraceViewCoveredBySummary view_left1 theta_left ->
    TraceViewCoveredBySummary view_right1 theta_right ->
    TraceViewCoveredBySummary view_left2 theta_left ->
    TraceViewCoveredBySummary view_right2 theta_right ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left1
      view_right1
      (StPairParRun
        (StError heap_error_left)
        right_final
        phi_left_final1
        phi_right_final1
        k) ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left2
      view_right2
      (StPairParRun
        (StDone heap_left_done v_left_done)
        (StError heap_error_right)
        phi_left_final2
        phi_right_final2
        k) ->
    False.
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k
    heap_error_left right_final
    heap_left_done v_left_done heap_error_right
    phi_left_final1 phi_right_final1
    phi_left_final2 phi_right_final2
    HBack HContext HSummaryDisjoint
    HCoveredLeft1 HCoveredRight1 HCoveredLeft2 HCoveredRight2
    HLeftErrorRun HRightErrorRun.
  pose proof HContext as HContextFacts.
  destruct HContextFacts as
    (_HHeap & _HEnv & _HRegHeap & _HRegEnv &
      _HStore & _HRho & HBounded).
  destruct
    (ScheduledPairParRun_checked_pairpar_noalloc_views
      gamma omega rho heap env ef1 ea1 ef2 ea2
      view_left1 view_right1
      (StPairParRun
        (StError heap_error_left)
        right_final
        phi_left_final1
        phi_right_final1
        k)
      k HBack HContext HLeftErrorRun)
    as (HNoAllocLeft1 & HNoAllocRight1).
  destruct
    (ScheduledPairParRun_checked_pairpar_noalloc_views
      gamma omega rho heap env ef1 ea1 ef2 ea2
      view_left2 view_right2
      (StPairParRun
        (StDone heap_left_done v_left_done)
        (StError heap_error_right)
        phi_left_final2
        phi_right_final2
        k)
      k HBack HContext HRightErrorRun)
    as (HNoAllocLeft2 & HNoAllocRight2).
  pose proof
    (summary_disjoint_covered_trace_disjoint
      (trace_view_flatten view_left1)
      (trace_view_flatten view_right1)
      theta_left theta_right
      HSummaryDisjoint HCoveredLeft1 HCoveredRight1)
    as HDisjoint1.
  pose proof
    (summary_disjoint_covered_trace_disjoint
      (trace_view_flatten view_left2)
      (trace_view_flatten view_right2)
      theta_left theta_right
      HSummaryDisjoint HCoveredLeft2 HCoveredRight2)
    as HDisjoint2.
  eapply
    (ScheduledPairParRun_noalloc_disjoint_left_right_error_impossible
      (InitialState heap env rho (EMuApp ef1 ea1))
      (InitialState heap env rho (EMuApp ef2 ea2))
      view_left1 view_right1 view_left2 view_right2
      k heap_error_left right_final
      heap_left_done v_left_done heap_error_right
      phi_left_final1 phi_right_final1
      phi_left_final2 phi_right_final2);
    simpl; eauto.
Qed.

Corollary ScheduledPairParRun_checked_pairpar_error_cause_deterministic :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k
    heap_error1 heap_error2,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    summary_disjointb theta_left theta_right = true ->
    TraceViewCoveredBySummary view_left1 theta_left ->
    TraceViewCoveredBySummary view_right1 theta_right ->
    TraceViewCoveredBySummary view_left2 theta_left ->
    TraceViewCoveredBySummary view_right2 theta_right ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left1
      view_right1
      (StError heap_error1) ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left2
      view_right2
      (StError heap_error2) ->
    ((exists right_final1 phi_left_final1 phi_right_final1,
        ScheduledPairParRun
          (StPairParRun
            (InitialState heap env rho (EMuApp ef1 ea1))
            (InitialState heap env rho (EMuApp ef2 ea2))
            [] [] k)
          view_left1
          view_right1
          (StPairParRun
            (StError heap_error1)
            right_final1
            phi_left_final1
            phi_right_final1
            k)) /\
      (exists right_final2 phi_left_final2 phi_right_final2,
        ScheduledPairParRun
          (StPairParRun
            (InitialState heap env rho (EMuApp ef1 ea1))
            (InitialState heap env rho (EMuApp ef2 ea2))
            [] [] k)
          view_left2
          view_right2
          (StPairParRun
            (StError heap_error2)
            right_final2
            phi_left_final2
            phi_right_final2
            k)) /\
      HeapEqOn
        (fun r l =>
          TraceDoesNotWrite r l (trace_view_flatten view_right1) /\
          TraceDoesNotWrite r l (trace_view_flatten view_right2))
        heap_error1
        heap_error2) \/
    ((exists heap_left1 v_left1 phi_left_final1 phi_right_final1,
        ScheduledPairParRun
          (StPairParRun
            (InitialState heap env rho (EMuApp ef1 ea1))
            (InitialState heap env rho (EMuApp ef2 ea2))
            [] [] k)
          view_left1
          view_right1
          (StPairParRun
            (StDone heap_left1 v_left1)
            (StError heap_error1)
            phi_left_final1
            phi_right_final1
            k)) /\
      (exists heap_left2 v_left2 phi_left_final2 phi_right_final2,
        ScheduledPairParRun
          (StPairParRun
            (InitialState heap env rho (EMuApp ef1 ea1))
            (InitialState heap env rho (EMuApp ef2 ea2))
            [] [] k)
          view_left2
          view_right2
          (StPairParRun
            (StDone heap_left2 v_left2)
            (StError heap_error2)
            phi_left_final2
            phi_right_final2
            k)) /\
      heap_error1 = heap_error2).
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k
    heap_error1 heap_error2
    HBack HContext HSummaryDisjoint
    HCoveredLeft1 HCoveredRight1 HCoveredLeft2 HCoveredRight2
    HRun1 HRun2.
  destruct
    (ScheduledPairParRun_checked_pairpar_error_is_branch_error
      gamma omega rho heap env ef1 ea1 ef2 ea2
      heap_error1 view_left1 view_right1 theta_left theta_right k
      HBack HContext HSummaryDisjoint
      HCoveredLeft1 HCoveredRight1 HRun1)
    as [HLeftError1 | HRightError1].
  - destruct
      (ScheduledPairParRun_checked_pairpar_error_is_branch_error
        gamma omega rho heap env ef1 ea1 ef2 ea2
        heap_error2 view_left2 view_right2 theta_left theta_right k
        HBack HContext HSummaryDisjoint
        HCoveredLeft2 HCoveredRight2 HRun2)
      as [HLeftError2 | HRightError2].
    + destruct HLeftError1 as
        (right_final1 & phi_left_final1 & phi_right_final1 & HPrefix1).
      destruct HLeftError2 as
        (right_final2 & phi_left_final2 & phi_right_final2 & HPrefix2).
      left.
      repeat split.
      * exists right_final1, phi_left_final1, phi_right_final1.
        exact HPrefix1.
      * exists right_final2, phi_left_final2, phi_right_final2.
        exact HPrefix2.
      * eapply
          (ScheduledPairParRun_checked_pairpar_left_error_footprint_deterministic
            gamma omega rho heap env ef1 ea1 ef2 ea2
            view_left1 view_right1 view_left2 view_right2
            theta_left theta_right k
            heap_error1 heap_error2
            right_final1 right_final2
            phi_left_final1 phi_right_final1
            phi_left_final2 phi_right_final2);
          eauto.
    + destruct HLeftError1 as
        (right_final1 & phi_left_final1 & phi_right_final1 & HPrefix1).
      destruct HRightError2 as
        (heap_left2 & v_left2 & phi_left_final2 &
          phi_right_final2 & HPrefix2).
      exfalso.
      eapply
        (ScheduledPairParRun_checked_pairpar_left_right_error_impossible
          gamma omega rho heap env ef1 ea1 ef2 ea2
          view_left1 view_right1 view_left2 view_right2
          theta_left theta_right k
          heap_error1 right_final1
          heap_left2 v_left2 heap_error2
          phi_left_final1 phi_right_final1
          phi_left_final2 phi_right_final2);
        eauto.
  - destruct
      (ScheduledPairParRun_checked_pairpar_error_is_branch_error
        gamma omega rho heap env ef1 ea1 ef2 ea2
        heap_error2 view_left2 view_right2 theta_left theta_right k
        HBack HContext HSummaryDisjoint
        HCoveredLeft2 HCoveredRight2 HRun2)
      as [HLeftError2 | HRightError2].
    + destruct HRightError1 as
        (heap_left1 & v_left1 & phi_left_final1 &
          phi_right_final1 & HPrefix1).
      destruct HLeftError2 as
        (right_final2 & phi_left_final2 & phi_right_final2 & HPrefix2).
      exfalso.
      eapply
        (ScheduledPairParRun_checked_pairpar_left_right_error_impossible
          gamma omega rho heap env ef1 ea1 ef2 ea2
          view_left2 view_right2 view_left1 view_right1
          theta_left theta_right k
          heap_error2 right_final2
          heap_left1 v_left1 heap_error1
          phi_left_final2 phi_right_final2
          phi_left_final1 phi_right_final1);
        eauto.
    + destruct HRightError1 as
        (heap_left1 & v_left1 & phi_left_final1 &
          phi_right_final1 & HPrefix1).
      destruct HRightError2 as
        (heap_left2 & v_left2 & phi_left_final2 &
          phi_right_final2 & HPrefix2).
      right.
      repeat split.
      * exists heap_left1, v_left1, phi_left_final1, phi_right_final1.
        exact HPrefix1.
      * exists heap_left2, v_left2, phi_left_final2, phi_right_final2.
        exact HPrefix2.
      * eapply
          (ScheduledPairParRun_checked_pairpar_right_error_heap_deterministic
            gamma omega rho heap env ef1 ea1 ef2 ea2
            view_left1 view_right1 view_left2 view_right2
            theta_left theta_right k
            heap_left1 heap_left2
            v_left1 v_left2
            heap_error1 heap_error2
            phi_left_final1 phi_right_final1
            phi_left_final2 phi_right_final2);
          eauto.
Qed.

Lemma ScheduledPairParRun_heap_neutral_success_branch_steps :
  forall left_state right_state phi_left phi_right k
    view_left view_right heap value,
    StateHeapsAligned left_state ->
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    HeapNeutralTraceView view_left ->
    HeapNeutralTraceView view_right ->
    ScheduledPairParRun
      (StPairParRun left_state right_state phi_left phi_right k)
      view_left
      view_right
      (StReturn heap value k) ->
    exists v_left v_right,
      value = VPair v_left v_right /\
      Steps left_state (trace_view_flatten view_left)
        (StDone heap v_left) /\
      Steps right_state (trace_view_flatten view_right)
        (StDone heap v_right).
Proof.
  intros left_state right_state phi_left phi_right k
    view_left view_right heap value HAlignedLeft HAlignedRight
    HHeapAligned HNeutralLeft HNeutralRight HRun.
  remember
    (StPairParRun left_state right_state phi_left phi_right k)
    as state_start eqn:HStart.
  remember (StReturn heap value k) as state_final eqn:HFinal.
  revert left_state right_state phi_left phi_right k heap value
    HAlignedLeft HAlignedRight HHeapAligned HNeutralLeft HNeutralRight
    HStart HFinal.
  induction HRun; intros left0 right0 phi_left0 phi_right0 k0 heap0 value0
    HAlignedLeft HAlignedRight HHeapAligned HNeutralLeft HNeutralRight
    HStart HFinal.
  - rewrite HStart in HFinal. inversion HFinal.
  - inversion HStart; subst.
    pose proof
      (HeapNeutralTraceView_seq_label label view_left HNeutralLeft)
      as HNeutralLabel.
    pose proof
      (HeapNeutralTraceView_seq_tail label view_left HNeutralLeft)
      as HNeutralLeftTail.
    destruct
      (Step_heap_neutral_preserves_alignment
        left0 label left_state' H0 HAlignedLeft HNeutralLabel)
      as (HAlignedLeft' & HHeapLeft').
    assert
      (HAlignedRightRebased :
        StateHeapsAligned
          (with_state_heap (state_heap left_state') right0)).
    {
      destruct
        (with_state_heap_aligned
          (state_heap left_state') right0 HAlignedRight)
        as (HAligned & _).
      exact HAligned.
    }
    assert
      (HHeapTail :
        state_heap left_state' =
        state_heap (with_state_heap (state_heap left_state') right0)).
    {
      rewrite state_heap_with_state_heap.
      reflexivity.
    }
    destruct
      (IHHRun
        left_state'
        (with_state_heap (state_heap left_state') right0)
        (phi_left0 ++ label_trace label)
        phi_right0
        k0
        heap0
        value0
        HAlignedLeft'
        HAlignedRightRebased
        HHeapTail
        HNeutralLeftTail
        HNeutralRight
        eq_refl
        eq_refl)
      as (v_left & v_right & HValue & HLeftStepsTail & HRightSteps).
    exists v_left, v_right.
    split; [exact HValue |].
    split.
    + simpl.
      rewrite label_view_flatten.
      eapply StepsStep; eauto.
    + assert
        (HRightRebase :
          with_state_heap (state_heap left_state') right0 = right0).
      {
        eapply with_state_heap_aligned_same.
        - exact HAlignedRight.
        - rewrite HHeapLeft', HHeapAligned.
          reflexivity.
      }
      rewrite HRightRebase in HRightSteps.
      exact HRightSteps.
  - inversion HStart; subst.
    pose proof
      (HeapNeutralTraceView_seq_label label view_right HNeutralRight)
      as HNeutralLabel.
    pose proof
      (HeapNeutralTraceView_seq_tail label view_right HNeutralRight)
      as HNeutralRightTail.
    destruct
      (Step_heap_neutral_preserves_alignment
        right0 label right_state' H0 HAlignedRight HNeutralLabel)
      as (HAlignedRight' & HHeapRight').
    assert
      (HAlignedLeftRebased :
        StateHeapsAligned
          (with_state_heap (state_heap right_state') left0)).
    {
      destruct
        (with_state_heap_aligned
          (state_heap right_state') left0 HAlignedLeft)
        as (HAligned & _).
      exact HAligned.
    }
    assert
      (HHeapTail :
        state_heap (with_state_heap (state_heap right_state') left0) =
        state_heap right_state').
    {
      rewrite state_heap_with_state_heap.
      reflexivity.
    }
    destruct
      (IHHRun
        (with_state_heap (state_heap right_state') left0)
        right_state'
        phi_left0
        (phi_right0 ++ label_trace label)
        k0
        heap0
        value0
        HAlignedLeftRebased
        HAlignedRight'
        HHeapTail
        HNeutralLeft
        HNeutralRightTail
        eq_refl
        eq_refl)
      as (v_left & v_right & HValue & HLeftSteps & HRightStepsTail).
    exists v_left, v_right.
    split; [exact HValue |].
    split.
    + assert
        (HLeftRebase :
          with_state_heap (state_heap right_state') left0 = left0).
      {
        eapply with_state_heap_aligned_same.
        - exact HAlignedLeft.
        - rewrite HHeapRight'.
          exact HHeapAligned.
      }
      rewrite HLeftRebase in HLeftSteps.
      exact HLeftSteps.
    + simpl.
      rewrite label_view_flatten.
      eapply StepsStep; eauto.
  - discriminate.
  - discriminate.
  - inversion HFinal; subst.
    inversion HStart; subst.
    exists v_left, v_right.
    simpl.
    repeat split; constructor.
  - discriminate.
Qed.

Theorem ScheduledPairParRun_heap_neutral_join_determinism :
  forall left_state right_state
    view_left1 view_right1 view_left2 view_right2
    k heap1 heap2 value1 value2,
    StateHeapsAligned left_state ->
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    HeapNeutralTraceView view_left1 ->
    HeapNeutralTraceView view_right1 ->
    HeapNeutralTraceView view_left2 ->
    HeapNeutralTraceView view_right2 ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left1
      view_right1
      (StReturn heap1 value1 k) ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left2
      view_right2
      (StReturn heap2 value2 k) ->
    heap1 = heap2 /\ value1 = value2.
Proof.
  intros left_state right_state
    view_left1 view_right1 view_left2 view_right2
    k heap1 heap2 value1 value2
    HAlignedLeft HAlignedRight HHeapAligned
    HNeutralLeft1 HNeutralRight1 HNeutralLeft2 HNeutralRight2
    HSchedule1 HSchedule2.
  destruct
    (ScheduledPairParRun_heap_neutral_success_branch_steps
      left_state right_state [] [] k
      view_left1 view_right1 heap1 value1
      HAlignedLeft HAlignedRight HHeapAligned
      HNeutralLeft1 HNeutralRight1 HSchedule1)
    as (v_left1 & v_right1 & HValue1 & HLeftSteps1 & HRightSteps1).
  destruct
    (ScheduledPairParRun_heap_neutral_success_branch_steps
      left_state right_state [] [] k
      view_left2 view_right2 heap2 value2
      HAlignedLeft HAlignedRight HHeapAligned
      HNeutralLeft2 HNeutralRight2 HSchedule2)
    as (v_left2 & v_right2 & HValue2 & HLeftSteps2 & HRightSteps2).
  destruct
    (Steps_terminal_deterministic
      left_state
      (trace_view_flatten view_left1)
      heap1
      v_left1
      (trace_view_flatten view_left2)
      heap2
      v_left2
      HLeftSteps1
      HLeftSteps2)
    as (HHeap & HLeftValue).
  destruct
    (Steps_terminal_deterministic
      right_state
      (trace_view_flatten view_right1)
      heap1
      v_right1
      (trace_view_flatten view_right2)
      heap2
      v_right2
      HRightSteps1
      HRightSteps2)
    as (_ & HRightValue).
  subst heap2 v_left2 v_right2.
  split; [reflexivity |].
  rewrite HValue1, HValue2.
  reflexivity.
Qed.

Theorem Step_PairParRun_embeds_scheduled :
  forall left_state right_state phi_left phi_right k label state',
    StateNotError right_state ->
    Step
      (StPairParRun left_state right_state phi_left phi_right k)
      label
      state' ->
    exists view_left view_right,
      ScheduledPairParRun
        (StPairParRun left_state right_state phi_left phi_right k)
        view_left
        view_right
        state'.
Proof.
  intros left_state right_state phi_left phi_right k label state'
    HRightNotError HStep.
  inversion HStep; subst.
  - exists (TraceSeq (label_view label) TraceEmpty), TraceEmpty.
    eapply SchedPairParRunLeft.
    + exact HRightNotError.
    + eassumption.
    + constructor.
  - exists TraceEmpty, (TraceSeq (label_view label) TraceEmpty).
    eapply SchedPairParRunRight.
    + simpl. exact I.
    + eassumption.
    + constructor.
  - exists TraceEmpty, TraceEmpty.
    apply SchedPairParRunLeftError.
  - exists TraceEmpty, TraceEmpty.
    apply SchedPairParRunRightError.
  - exists TraceEmpty, TraceEmpty.
    now apply SchedPairParRunDonePass.
  - exists TraceEmpty, TraceEmpty.
    now apply SchedPairParRunDoneFail.
Qed.

Theorem Step_PairParRunLeft_embeds_scheduled :
  forall left_state right_state phi_left phi_right k label left_state',
    StateNotError right_state ->
    Step left_state label left_state' ->
    ScheduledPairParRun
      (StPairParRun left_state right_state phi_left phi_right k)
      (TraceSeq (label_view label) TraceEmpty)
      TraceEmpty
      (StPairParRun
        left_state'
        (with_state_heap (state_heap left_state') right_state)
        (phi_left ++ label_trace label)
        phi_right
        k).
Proof.
  intros left_state right_state phi_left phi_right k label left_state'
    HRightNotError HStep.
  eapply SchedPairParRunLeft; eauto.
  constructor.
Qed.

Theorem Step_PairParRunRight_embeds_scheduled :
  forall left_state right_state phi_left phi_right k label right_state',
    StateNotError left_state ->
    Step right_state label right_state' ->
    ScheduledPairParRun
      (StPairParRun left_state right_state phi_left phi_right k)
      TraceEmpty
      (TraceSeq (label_view label) TraceEmpty)
      (StPairParRun
        (with_state_heap (state_heap right_state') left_state)
        right_state'
        phi_left
        (phi_right ++ label_trace label)
        k).
Proof.
  intros left_state right_state phi_left phi_right k label right_state'
    HLeftNotError HStep.
  eapply SchedPairParRunRight; eauto.
  constructor.
Qed.

Lemma StateNotError_with_state_heap :
  forall heap state,
    StateNotError state ->
    StateNotError (with_state_heap heap state).
Proof.
  intros heap state HNotError.
  destruct state; simpl in *; try exact I.
  contradiction.
Qed.

Lemma StepsView_left_branch_embeds_scheduled_tail :
  forall left_state right_state phi_left phi_right k
    view_left left_state' view_right state_final,
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    StateNotError right_state ->
    StepsView left_state view_left left_state' ->
    ScheduledPairParRun
      (StPairParRun
        left_state'
        (with_state_heap (state_heap left_state') right_state)
        (phi_left ++ trace_view_flatten view_left)
        phi_right
        k)
      TraceEmpty
      view_right
      state_final ->
    ScheduledPairParRun
      (StPairParRun left_state right_state phi_left phi_right k)
      view_left
      view_right
      state_final.
Proof.
  intros left_state right_state phi_left phi_right k
    view_left left_state' view_right state_final
    HAlignedRight HHeapAligned HRightNotError HSteps.
  revert right_state phi_left phi_right k view_right state_final
    HAlignedRight HHeapAligned HRightNotError.
  induction HSteps as
    [state | state label state' view state'' HStep _ IH];
    intros right_state phi_left phi_right k view_right state_final
      HAlignedRight HHeapAligned HRightNotError HTail.
  - simpl in HTail.
    rewrite app_nil_r in HTail.
    replace (with_state_heap (state_heap state) right_state)
      with right_state in HTail.
    + exact HTail.
    + symmetry.
      eapply with_state_heap_aligned_same.
      * exact HAlignedRight.
      * symmetry. exact HHeapAligned.
  - simpl in HTail.
    rewrite label_view_flatten in HTail.
    eapply SchedPairParRunLeft.
    + exact HRightNotError.
    + exact HStep.
    + eapply IH.
      * destruct
          (with_state_heap_aligned
            (state_heap state') right_state HAlignedRight)
          as (HAligned & _).
        exact HAligned.
      * rewrite state_heap_with_state_heap.
        reflexivity.
      * eapply StateNotError_with_state_heap.
        exact HRightNotError.
      * rewrite with_state_heap_twice.
        rewrite <- app_assoc.
        exact HTail.
Qed.

Lemma StepsView_right_branch_embeds_scheduled_tail :
  forall left_state right_state phi_left phi_right k
    view_right right_state' state_final,
    StateHeapsAligned left_state ->
    state_heap left_state = state_heap right_state ->
    StateNotError left_state ->
    StepsView right_state view_right right_state' ->
    ScheduledPairParRun
      (StPairParRun
        (with_state_heap (state_heap right_state') left_state)
        right_state'
        phi_left
        (phi_right ++ trace_view_flatten view_right)
        k)
      TraceEmpty
      TraceEmpty
      state_final ->
    ScheduledPairParRun
      (StPairParRun left_state right_state phi_left phi_right k)
      TraceEmpty
      view_right
      state_final.
Proof.
  intros left_state right_state phi_left phi_right k
    view_right right_state' state_final
    HAlignedLeft HHeapAligned HLeftNotError HSteps.
  revert left_state phi_left phi_right k state_final
    HAlignedLeft HHeapAligned HLeftNotError.
  induction HSteps as
    [state | state label state' view state'' HStep _ IH];
    intros left_state phi_left phi_right k state_final
      HAlignedLeft HHeapAligned HLeftNotError HTail.
  - simpl in HTail.
    rewrite app_nil_r in HTail.
    replace (with_state_heap (state_heap state) left_state)
      with left_state in HTail.
    + exact HTail.
    + symmetry.
      eapply with_state_heap_aligned_same.
      * exact HAlignedLeft.
      * exact HHeapAligned.
  - simpl in HTail.
    rewrite label_view_flatten in HTail.
    eapply SchedPairParRunRight.
    + exact HLeftNotError.
    + exact HStep.
    + eapply IH.
      * destruct
          (with_state_heap_aligned
            (state_heap state') left_state HAlignedLeft)
          as (HAligned & _).
        exact HAligned.
      * rewrite state_heap_with_state_heap.
        reflexivity.
      * eapply StateNotError_with_state_heap.
        exact HLeftNotError.
      * rewrite with_state_heap_twice.
        rewrite <- app_assoc.
        exact HTail.
Qed.

Theorem ScheduledPairParRun_left_then_right_success :
  forall left_state right_state phi_left_acc phi_right_acc
    view_left view_right k heap_left heap_right v_left v_right,
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    StateNotError right_state ->
    StepsView left_state view_left (StDone heap_left v_left) ->
    StepsView
      (with_state_heap heap_left right_state)
      view_right
      (StDone heap_right v_right) ->
    trace_disjointb
      (phi_left_acc ++ trace_view_flatten view_left)
      (phi_right_acc ++ trace_view_flatten view_right) = true ->
    ScheduledPairParRun
      (StPairParRun left_state right_state phi_left_acc phi_right_acc k)
      view_left
      view_right
      (StReturn heap_right (VPair v_left v_right) k).
Proof.
  intros left_state right_state phi_left_acc phi_right_acc
    view_left view_right k heap_left heap_right v_left v_right
    HAlignedRight HHeapAligned HRightNotError
    HLeftSteps HRightSteps HTraceDisjoint.
  eapply StepsView_left_branch_embeds_scheduled_tail.
  - exact HAlignedRight.
  - exact HHeapAligned.
  - exact HRightNotError.
  - exact HLeftSteps.
  - eapply StepsView_right_branch_embeds_scheduled_tail.
    + simpl. exact I.
    + rewrite state_heap_with_state_heap.
      reflexivity.
    + simpl. exact I.
    + exact HRightSteps.
    + simpl.
      eapply SchedPairParRunDonePass.
      exact HTraceDisjoint.
Qed.

Corollary Steps_PairParRun_left_then_right_success_embeds_scheduled :
  forall left_state right_state phi_left_acc phi_right_acc
    phi_left phi_right k heap_left heap_right v_left v_right,
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    StateNotError right_state ->
    Steps left_state phi_left (StDone heap_left v_left) ->
    Steps
      (with_state_heap heap_left right_state)
      phi_right
      (StDone heap_right v_right) ->
    trace_disjointb
      (phi_left_acc ++ phi_left)
      (phi_right_acc ++ phi_right) = true ->
    exists view_left view_right,
      ScheduledPairParRun
        (StPairParRun left_state right_state phi_left_acc phi_right_acc k)
        view_left
        view_right
        (StReturn heap_right (VPair v_left v_right) k) /\
      TraceViewRepresents view_left phi_left /\
      TraceViewRepresents view_right phi_right /\
      SchedulerTraceRepresentsViews (phi_left ++ phi_right)
        view_left view_right.
Proof.
  intros left_state right_state phi_left_acc phi_right_acc
    phi_left phi_right k heap_left heap_right v_left v_right
    HAlignedRight HHeapAligned HRightNotError
    HLeftSteps HRightSteps HTraceDisjoint.
  destruct (Steps_to_StepsView _ _ _ HLeftSteps)
    as (view_left & HLeftView & HLeftRep).
  destruct (Steps_to_StepsView _ _ _ HRightSteps)
    as (view_right & HRightView & HRightRep).
  exists view_left, view_right.
  unfold TraceViewRepresents in HLeftRep, HRightRep.
  split.
  - eapply ScheduledPairParRun_left_then_right_success; eauto.
    rewrite HLeftRep, HRightRep.
    exact HTraceDisjoint.
  - repeat split; try assumption.
    unfold SchedulerTraceRepresentsViews, TracePermutation.
    simpl.
    rewrite HLeftRep, HRightRep.
    reflexivity.
Qed.

Corollary ScheduledPairParRun_checked_pairpar_left_then_right_success :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left view_right heap_left heap_right v_left v_right k,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    StructuredComputationEvaluation
      heap env rho (EMuApp ef1 ea1)
      view_left heap_left v_left ->
    StructuredComputationEvaluation
      heap_left env rho (EMuApp ef2 ea2)
      view_right heap_right v_right ->
    trace_disjointb
      (trace_view_flatten view_left)
      (trace_view_flatten view_right) = true ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left
      view_right
      (StReturn heap_right (VPair v_left v_right) k).
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left view_right heap_left heap_right v_left v_right k
    _HBack _HContext HLeft HRight HTraceDisjoint.
  eapply ScheduledPairParRun_left_then_right_success.
  - simpl. exact I.
  - reflexivity.
  - simpl. exact I.
  - exact HLeft.
  - simpl. exact HRight.
  - simpl.
    exact HTraceDisjoint.
Qed.

Corollary Steps_checked_pairpar_left_then_right_success_embeds_scheduled :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    phi_left phi_right heap_left heap_right v_left v_right k,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    ComputationEvaluation
      heap env rho (EMuApp ef1 ea1)
      phi_left heap_left v_left ->
    ComputationEvaluation
      heap_left env rho (EMuApp ef2 ea2)
      phi_right heap_right v_right ->
    trace_disjointb phi_left phi_right = true ->
    exists view_left view_right,
      ScheduledPairParRun
        (StPairParRun
          (InitialState heap env rho (EMuApp ef1 ea1))
          (InitialState heap env rho (EMuApp ef2 ea2))
          [] [] k)
        view_left
        view_right
        (StReturn heap_right (VPair v_left v_right) k) /\
      TraceViewRepresents view_left phi_left /\
      TraceViewRepresents view_right phi_right /\
      SchedulerTraceRepresentsViews (phi_left ++ phi_right)
        view_left view_right.
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    phi_left phi_right heap_left heap_right v_left v_right k
    _HBack _HContext HLeft HRight HTraceDisjoint.
  unfold ComputationEvaluation in HLeft, HRight.
  destruct
    (Steps_PairParRun_left_then_right_success_embeds_scheduled
      (InitialState heap env rho (EMuApp ef1 ea1))
      (InitialState heap env rho (EMuApp ef2 ea2))
      [] []
      phi_left phi_right k heap_left heap_right v_left v_right)
    as (view_left & view_right &
      HSchedule & HLeftRep & HRightRep & HRepresents).
  - simpl. exact I.
  - reflexivity.
  - simpl. exact I.
  - exact HLeft.
  - simpl. exact HRight.
  - simpl.
    exact HTraceDisjoint.
  - exists view_left, view_right.
    repeat split; assumption.
Qed.

Corollary Steps_PairParRun_kdone_terminal_embeds_scheduled :
  forall heap env rho e_left e_right phi heap_final value_final,
    Steps
      (StPairParRun
        (InitialState heap env rho e_left)
        (InitialState heap env rho e_right)
        [] [] KDone)
      phi
      (StDone heap_final value_final) ->
    exists view_left view_right,
      ScheduledPairParRun
        (StPairParRun
          (InitialState heap env rho e_left)
          (InitialState heap env rho e_right)
          [] [] KDone)
        view_left
        view_right
        (StReturn heap_final value_final KDone) /\
      Steps
        (StReturn heap_final value_final KDone)
        []
        (StDone heap_final value_final) /\
      SchedulerTraceRepresentsViews phi view_left view_right.
Proof.
  intros heap env rho e_left e_right phi heap_final value_final HSteps.
  destruct
    (Steps_to_StepsN
      (StPairParRun
        (InitialState heap env rho e_left)
        (InitialState heap env rho e_right)
        [] [] KDone)
      phi
      (StDone heap_final value_final)
      HSteps)
    as (n & HStepsN).
  destruct
    (StPairParRun_initial_decomposition_N
      n heap env rho e_left e_right phi heap_final value_final HStepsN)
    as (phi_left & phi_right & heap_left & v_left &
      heap_right & v_right &
      HLeft & HRight & HTraceDisjoint &
      HHeap & HValue & HTrace).
  subst heap_final value_final phi.
  destruct
    (Steps_PairParRun_left_then_right_success_embeds_scheduled
      (InitialState heap env rho e_left)
      (InitialState heap env rho e_right)
      [] []
      phi_left phi_right KDone heap_left heap_right v_left v_right)
    as (view_left & view_right &
      HSchedule & _HLeftRep & _HRightRep & HRepresents).
  - simpl. exact I.
  - reflexivity.
  - simpl. exact I.
  - exact HLeft.
  - simpl.
    exact HRight.
  - simpl.
    exact HTraceDisjoint.
  - exists view_left, view_right.
    split; [exact HSchedule |].
    split.
    + change (@nil DynamicAction) with (label_trace LSilent ++ []).
      eapply StepsStep.
      * apply StepReturnDone.
      * constructor.
    + exact HRepresents.
Qed.

Corollary Steps_checked_pairpar_kdone_terminal_embeds_scheduled :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    phi heap_final value_final,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    Steps
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] KDone)
      phi
      (StDone heap_final value_final) ->
    exists view_left view_right,
      ScheduledPairParRun
        (StPairParRun
          (InitialState heap env rho (EMuApp ef1 ea1))
          (InitialState heap env rho (EMuApp ef2 ea2))
          [] [] KDone)
        view_left
        view_right
        (StReturn heap_final value_final KDone) /\
      Steps
        (StReturn heap_final value_final KDone)
        []
        (StDone heap_final value_final) /\
      SchedulerTraceRepresentsViews phi view_left view_right.
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    phi heap_final value_final _HBack _HContext HSteps.
  eapply Steps_PairParRun_kdone_terminal_embeds_scheduled.
  exact HSteps.
Qed.

Theorem ScheduledPairParRun_noalloc_join_determinism :
  forall left_state right_state
    view_left1 view_right1 view_left2 view_right2
    k heap1 heap2 value1 value2,
    StateHeapsAligned left_state ->
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    HeapKeysBounded (state_heap left_state) ->
    NoAllocTraceView view_left1 ->
    NoAllocTraceView view_right1 ->
    NoAllocTraceView view_left2 ->
    NoAllocTraceView view_right2 ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left1
      view_right1
      (StReturn heap1 value1 k) ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left2
      view_right2
      (StReturn heap2 value2 k) ->
    heap1 = heap2 /\ value1 = value2.
Proof.
  intros left_state right_state
    view_left1 view_right1 view_left2 view_right2
    k heap1 heap2 value1 value2
    HAlignedLeft HAlignedRight HHeapAligned HBounded
    HNoAllocLeft1 HNoAllocRight1 HNoAllocLeft2 HNoAllocRight2
    HSchedule1 HSchedule2.
  destruct
    (ScheduledPairParRun_success_empty_accumulators
      left_state right_state k view_left1 view_right1 heap1 value1
      HSchedule1)
    as (_v_left_acc1 & _v_right_acc1 &
      phi_left_final1 & phi_right_final1 &
      _HValueAcc1 & HLeftFinal1 & HRightFinal1 & HDisjointBool1).
  subst phi_left_final1 phi_right_final1.
  pose proof
    (trace_disjointb_true_disjoint
      (trace_view_flatten view_left1)
      (trace_view_flatten view_right1)
      HDisjointBool1)
    as HDisjoint1.
  destruct
    (ScheduledPairParRun_success_empty_accumulators
      left_state right_state k view_left2 view_right2 heap2 value2
      HSchedule2)
    as (_v_left_acc2 & _v_right_acc2 &
      phi_left_final2 & phi_right_final2 &
      _HValueAcc2 & HLeftFinal2 & HRightFinal2 & HDisjointBool2).
  subst phi_left_final2 phi_right_final2.
  pose proof
    (trace_disjointb_true_disjoint
      (trace_view_flatten view_left2)
      (trace_view_flatten view_right2)
      HDisjointBool2)
    as HDisjoint2.
  destruct
    (ScheduledPairParRun_noalloc_disjoint_canonical
      left_state right_state [] []
      view_left1 view_right1 k heap1 value1
      HAlignedLeft HAlignedRight HHeapAligned HBounded
      HDisjoint1 HNoAllocLeft1 HNoAllocRight1 HSchedule1)
    as (heap_left1 & heap_canonical1 & v_left1 & v_right1 &
      HValue1 & HLeft1 & HRight1 & HHeap1).
  destruct
    (ScheduledPairParRun_noalloc_disjoint_canonical
      left_state right_state [] []
      view_left2 view_right2 k heap2 value2
      HAlignedLeft HAlignedRight HHeapAligned HBounded
      HDisjoint2 HNoAllocLeft2 HNoAllocRight2 HSchedule2)
    as (heap_left2 & heap_canonical2 & v_left2 & v_right2 &
      HValue2 & HLeft2 & HRight2 & HHeap2).
  destruct
    (Steps_terminal_deterministic
      left_state
      (trace_view_flatten view_left1)
      heap_left1
      v_left1
      (trace_view_flatten view_left2)
      heap_left2
      v_left2
      HLeft1
      HLeft2)
    as (HHeapLeft & HValueLeft).
  subst heap_left2 v_left2.
  destruct
    (Steps_terminal_deterministic
      (with_state_heap heap_left1 right_state)
      (trace_view_flatten view_right1)
      heap_canonical1
      v_right1
      (trace_view_flatten view_right2)
      heap_canonical2
      v_right2
      HRight1
      HRight2)
    as (HHeapRight & HValueRight).
  subst heap_canonical2 v_right2.
  split.
  - congruence.
  - rewrite HValue1, HValue2.
    reflexivity.
Qed.

Theorem ScheduledPairParRun_checked_join_determinism :
  forall left_state right_state
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k heap1 heap2 value1 value2,
    StateHeapsAligned left_state ->
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    HeapKeysBounded (state_heap left_state) ->
    summary_disjointb theta_left theta_right = true ->
    NoAllocTraceView view_left1 ->
    NoAllocTraceView view_right1 ->
    NoAllocTraceView view_left2 ->
    NoAllocTraceView view_right2 ->
    TraceViewCoveredBySummary view_left1 theta_left ->
    TraceViewCoveredBySummary view_right1 theta_right ->
    TraceViewCoveredBySummary view_left2 theta_left ->
    TraceViewCoveredBySummary view_right2 theta_right ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left1
      view_right1
      (StReturn heap1 value1 k) ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left2
      view_right2
      (StReturn heap2 value2 k) ->
    heap1 = heap2 /\ value1 = value2.
Proof.
  intros left_state right_state
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k heap1 heap2 value1 value2
    HAlignedLeft HAlignedRight HHeapAligned HBounded
    _HSummaryDisjoint
    HNoAllocLeft1 HNoAllocRight1 HNoAllocLeft2 HNoAllocRight2
    _HCoveredLeft1 _HCoveredRight1 _HCoveredLeft2 _HCoveredRight2
    HSchedule1 HSchedule2.
  eapply
    (ScheduledPairParRun_noalloc_join_determinism
      left_state right_state
      view_left1 view_right1 view_left2 view_right2
      k heap1 heap2 value1 value2);
    eauto.
Qed.

Corollary ScheduledPairParRun_static_noalloc_join_determinism :
  forall rho left_state right_state
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right
    eff_left eff_left_res eff_right eff_right_res
    k heap1 heap2 value1 value2,
    StateHeapsAligned left_state ->
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    HeapKeysBounded (state_heap left_state) ->
    summary_disjointb theta_left theta_right = true ->
    static_noalloc eff_left ->
    static_noalloc eff_right ->
    ResolveStaticEffect rho eff_left eff_left_res ->
    ResolveStaticEffect rho eff_right eff_right_res ->
    TraceCoveredByStaticEffect
      (trace_view_flatten view_left1) eff_left_res ->
    TraceCoveredByStaticEffect
      (trace_view_flatten view_right1) eff_right_res ->
    TraceCoveredByStaticEffect
      (trace_view_flatten view_left2) eff_left_res ->
    TraceCoveredByStaticEffect
      (trace_view_flatten view_right2) eff_right_res ->
    TraceViewCoveredBySummary view_left1 theta_left ->
    TraceViewCoveredBySummary view_right1 theta_right ->
    TraceViewCoveredBySummary view_left2 theta_left ->
    TraceViewCoveredBySummary view_right2 theta_right ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left1
      view_right1
      (StReturn heap1 value1 k) ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left2
      view_right2
      (StReturn heap2 value2 k) ->
    heap1 = heap2 /\ value1 = value2.
Proof.
  intros rho left_state right_state
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right
    eff_left eff_left_res eff_right eff_right_res
    k heap1 heap2 value1 value2
    HAlignedLeft HAlignedRight HHeapAligned HBounded
    HSummaryDisjoint HNoAllocEffLeft HNoAllocEffRight
    HResolveLeft HResolveRight
    HStaticLeft1 HStaticRight1 HStaticLeft2 HStaticRight2
    HCoveredLeft1 HCoveredRight1 HCoveredLeft2 HCoveredRight2
    HSchedule1 HSchedule2.
  assert (HNoAllocLeftRes : static_noalloc eff_left_res).
  {
    eapply ResolveStaticEffect_static_noalloc; eauto.
  }
  assert (HNoAllocRightRes : static_noalloc eff_right_res).
  {
    eapply ResolveStaticEffect_static_noalloc; eauto.
  }
  assert (HNoAllocLeft1 : NoAllocTraceView view_left1).
  {
    unfold NoAllocTraceView.
    eapply TraceCoveredByStaticEffect_no_alloc; eauto.
  }
  assert (HNoAllocRight1 : NoAllocTraceView view_right1).
  {
    unfold NoAllocTraceView.
    eapply TraceCoveredByStaticEffect_no_alloc; eauto.
  }
  assert (HNoAllocLeft2 : NoAllocTraceView view_left2).
  {
    unfold NoAllocTraceView.
    eapply TraceCoveredByStaticEffect_no_alloc; eauto.
  }
  assert (HNoAllocRight2 : NoAllocTraceView view_right2).
  {
    unfold NoAllocTraceView.
    eapply TraceCoveredByStaticEffect_no_alloc; eauto.
  }
  eapply
    (ScheduledPairParRun_checked_join_determinism
      left_state right_state
      view_left1 view_right1 view_left2 view_right2
      theta_left theta_right k heap1 heap2 value1 value2);
    eauto.
Qed.

Corollary ScheduledPairParRun_pairpar_canonical_computations :
  forall heap env rho ef1 ea1 ef2 ea2
    view_left view_right theta_left theta_right k heap_join value_join,
    HeapKeysBounded heap ->
    summary_disjointb theta_left theta_right = true ->
    TraceViewCoveredBySummary view_left theta_left ->
    TraceViewCoveredBySummary view_right theta_right ->
    NoAllocTraceView view_left ->
    NoAllocTraceView view_right ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left
      view_right
      (StReturn heap_join value_join k) ->
    exists heap_left heap_right v_left v_right,
      value_join = VPair v_left v_right /\
      ComputationEvaluation
        heap env rho (EMuApp ef1 ea1)
        (trace_view_flatten view_left)
        heap_left v_left /\
      ComputationEvaluation
        heap_left env rho (EMuApp ef2 ea2)
        (trace_view_flatten view_right)
        heap_right v_right /\
      heap_join = heap_right.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    view_left view_right theta_left theta_right k heap_join value_join
    HBounded HSummaryDisjoint HCoveredLeft HCoveredRight
    HNoAllocLeft HNoAllocRight HSchedule.
  destruct
    (ScheduledPairParRun_noalloc_checked_canonical
      (InitialState heap env rho (EMuApp ef1 ea1))
      (InitialState heap env rho (EMuApp ef2 ea2))
      [] []
      view_left view_right theta_left theta_right k heap_join value_join)
    as (heap_left & heap_right & v_left & v_right &
      HValue & HLeft & HRight & HHeap).
  - simpl. exact I.
  - simpl. exact I.
  - reflexivity.
  - simpl. exact HBounded.
  - exact HSummaryDisjoint.
  - exact HCoveredLeft.
  - exact HCoveredRight.
  - exact HNoAllocLeft.
  - exact HNoAllocRight.
  - exact HSchedule.
  - exists heap_left, heap_right, v_left, v_right.
    split; [exact HValue |].
    split.
    + unfold ComputationEvaluation.
      exact HLeft.
    + split.
      * unfold ComputationEvaluation.
        exact HRight.
      * exact HHeap.
Qed.

Corollary ScheduledPairParRun_checked_pairpar_join_determinism :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right eff_left_res eff_right_res
    k heap1 heap2 value1 value2,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    HeapKeysBounded heap ->
    summary_disjointb theta_left theta_right = true ->
    (forall ty_left eff_left,
      CheckedTcExp gamma omega (EMuApp ef1 ea1) ty_left eff_left ->
      ResolveStaticEffect rho eff_left eff_left_res /\
      TraceCoveredByStaticEffect
        (trace_view_flatten view_left1) eff_left_res /\
      TraceCoveredByStaticEffect
        (trace_view_flatten view_left2) eff_left_res) ->
    (forall ty_right eff_right,
      CheckedTcExp gamma omega (EMuApp ef2 ea2) ty_right eff_right ->
      ResolveStaticEffect rho eff_right eff_right_res /\
      TraceCoveredByStaticEffect
        (trace_view_flatten view_right1) eff_right_res /\
      TraceCoveredByStaticEffect
        (trace_view_flatten view_right2) eff_right_res) ->
    TraceViewCoveredBySummary view_left1 theta_left ->
    TraceViewCoveredBySummary view_right1 theta_right ->
    TraceViewCoveredBySummary view_left2 theta_left ->
    TraceViewCoveredBySummary view_right2 theta_right ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left1
      view_right1
      (StReturn heap1 value1 k) ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left2
      view_right2
      (StReturn heap2 value2 k) ->
    heap1 = heap2 /\ value1 = value2.
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right eff_left_res eff_right_res
    k heap1 heap2 value1 value2
    HBack HBounded HSummaryDisjoint
    HStaticLeft HStaticRight
    HCoveredLeft1 HCoveredRight1 HCoveredLeft2 HCoveredRight2
    HSchedule1 HSchedule2.
  destruct
    (CBT_PairPar_components
      gamma omega ef1 ea1 ef2 ea2 HBack)
    as (_ty_left & _ty_right & eff_left & eff_right &
      _eff_summary_left & _eff_summary_right &
      HCheckedLeft & HCheckedRight &
      _HCheckedSummaryLeft & _HCheckedSummaryRight &
      _HNeutralSummaryLeft & _HNeutralSummaryRight &
      HNoAllocLeft & HNoAllocRight &
      _HBackLeft & _HBackRight).
  destruct (HStaticLeft _ _ HCheckedLeft)
    as (HResolveLeft & HStaticLeft1 & HStaticLeft2).
  destruct (HStaticRight _ _ HCheckedRight)
    as (HResolveRight & HStaticRight1 & HStaticRight2).
  eapply
    (ScheduledPairParRun_static_noalloc_join_determinism
      rho
      (InitialState heap env rho (EMuApp ef1 ea1))
      (InitialState heap env rho (EMuApp ef2 ea2))
      view_left1 view_right1 view_left2 view_right2
      theta_left theta_right
      eff_left eff_left_res eff_right eff_right_res
      k heap1 heap2 value1 value2);
	    simpl; eauto.
Qed.

Corollary ScheduledPairParRun_checked_pairpar_scheduled_join_determinism :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    k heap_join1 heap_join2 value_join1 value_join2,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left1
      view_right1
      (StReturn heap_join1 value_join1 k) ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left2
      view_right2
      (StReturn heap_join2 value_join2 k) ->
    heap_join1 = heap_join2 /\ value_join1 = value_join2.
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    k heap_join1 heap_join2 value_join1 value_join2
    HBack HContext HSchedule1 HSchedule2.
  pose proof HContext as HContextFacts.
  destruct HContextFacts as
    (_HHeap & _HEnv & _HRegHeap & _HRegEnv &
      _HStore & _HRho & HBounded).
  destruct
    (ScheduledPairParRun_checked_pairpar_noalloc_views
      gamma omega rho heap env ef1 ea1 ef2 ea2
      view_left1 view_right1
      (StReturn heap_join1 value_join1 k)
      k HBack HContext HSchedule1)
    as (HNoAllocLeft1 & HNoAllocRight1).
  destruct
    (ScheduledPairParRun_checked_pairpar_noalloc_views
      gamma omega rho heap env ef1 ea1 ef2 ea2
      view_left2 view_right2
      (StReturn heap_join2 value_join2 k)
      k HBack HContext HSchedule2)
    as (HNoAllocLeft2 & HNoAllocRight2).
  eapply
    (ScheduledPairParRun_noalloc_join_determinism
      (InitialState heap env rho (EMuApp ef1 ea1))
      (InitialState heap env rho (EMuApp ef2 ea2))
      view_left1 view_right1 view_left2 view_right2
      k heap_join1 heap_join2 value_join1 value_join2);
    simpl; eauto.
Qed.

Corollary ScheduledPairParRun_checked_pairpar_success_error_impossible :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left_success view_right_success
    view_left_error view_right_error
    theta_left theta_right k
    heap_join value_join heap_error,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    summary_disjointb theta_left theta_right = true ->
    TraceViewCoveredBySummary view_left_success theta_left ->
    TraceViewCoveredBySummary view_right_success theta_right ->
    TraceViewCoveredBySummary view_left_error theta_left ->
    TraceViewCoveredBySummary view_right_error theta_right ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left_success
      view_right_success
      (StReturn heap_join value_join k) ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left_error
      view_right_error
      (StError heap_error) ->
    False.
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left_success view_right_success
    view_left_error view_right_error
    theta_left theta_right k
    heap_join value_join heap_error
    HBack HContext HSummaryDisjoint
    HCoveredLeftSuccess HCoveredRightSuccess
    HCoveredLeftError HCoveredRightError
    HSuccess HError.
  pose proof HContext as HContextFacts.
  destruct HContextFacts as
    (_HHeap & _HEnv & _HRegHeap & _HRegEnv &
      _HStore & _HRho & HBounded).
  assert
    (HAlignedLeftStart :
      StateHeapsAligned
        (InitialState heap env rho (EMuApp ef1 ea1))).
  {
    simpl. exact I.
  }
  assert
    (HAlignedRightStart :
      StateHeapsAligned
        (InitialState heap env rho (EMuApp ef2 ea2))).
  {
    simpl. exact I.
  }
  assert
    (HHeapStart :
      state_heap (InitialState heap env rho (EMuApp ef1 ea1)) =
      state_heap (InitialState heap env rho (EMuApp ef2 ea2))).
  {
    reflexivity.
  }
  destruct
    (ScheduledPairParRun_checked_pairpar_noalloc_views
      gamma omega rho heap env ef1 ea1 ef2 ea2
      view_left_success view_right_success
      (StReturn heap_join value_join k)
      k HBack HContext HSuccess)
    as (HNoAllocLeftSuccess & HNoAllocRightSuccess).
  destruct
    (ScheduledPairParRun_checked_pairpar_noalloc_views
      gamma omega rho heap env ef1 ea1 ef2 ea2
      view_left_error view_right_error
      (StError heap_error)
      k HBack HContext HError)
    as (HNoAllocLeftError & HNoAllocRightError).
  pose proof
    (summary_disjoint_covered_trace_disjoint
      (trace_view_flatten view_left_error)
      (trace_view_flatten view_right_error)
      theta_left theta_right
      HSummaryDisjoint HCoveredLeftError HCoveredRightError)
    as HDisjointError.
  destruct
    (ScheduledPairParRun_noalloc_checked_canonical
      (InitialState heap env rho (EMuApp ef1 ea1))
      (InitialState heap env rho (EMuApp ef2 ea2))
      [] []
      view_left_success view_right_success
      theta_left theta_right k heap_join value_join
      HAlignedLeftStart HAlignedRightStart HHeapStart HBounded
      HSummaryDisjoint
      HCoveredLeftSuccess HCoveredRightSuccess
      HNoAllocLeftSuccess HNoAllocRightSuccess
      HSuccess)
    as (heap_left_success & heap_canonical_success &
      v_left_success & v_right_success &
      _HValueSuccess & HLeftSuccess &
      HRightSuccess & _HHeapSuccess).
  destruct
    (ScheduledPairParRun_checked_pairpar_error_is_branch_error
      gamma omega rho heap env ef1 ea1 ef2 ea2
      heap_error view_left_error view_right_error
      theta_left theta_right k
      HBack HContext HSummaryDisjoint
      HCoveredLeftError HCoveredRightError HError)
    as [HLeftError | HRightError].
  - destruct HLeftError as
      (right_final_error & phi_left_error &
        phi_right_error & HErrorPrefix).
    destruct
      (ScheduledPairParRun_noalloc_disjoint_left_error_canonical
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] []
        view_left_error view_right_error
        k heap_error right_final_error
        phi_left_error phi_right_error
        HAlignedLeftStart HAlignedRightStart HHeapStart HBounded
        HDisjointError
        HNoAllocLeftError HNoAllocRightError
        HErrorPrefix)
      as (heap_left_error & HLeftErrorSteps & _HHeapEq).
    destruct
      (Steps_terminal_state_trace_deterministic
        (InitialState heap env rho (EMuApp ef1 ea1))
        (trace_view_flatten view_left_success)
        (StDone heap_left_success v_left_success)
        (trace_view_flatten view_left_error)
        (StError heap_left_error)
        HLeftSuccess
        (TerminalDone heap_left_success v_left_success)
        HLeftErrorSteps
        (TerminalError heap_left_error))
      as (_HTraceLeft & HStateLeft).
    discriminate HStateLeft.
  - destruct HRightError as
      (heap_left_done_error & v_left_done_error &
        phi_left_error & phi_right_error & HErrorPrefix).
    destruct
      (ScheduledPairParRun_noalloc_disjoint_right_error_canonical
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] []
        view_left_error view_right_error
        k heap_left_done_error v_left_done_error heap_error
        phi_left_error phi_right_error
        HAlignedLeftStart HAlignedRightStart HHeapStart HBounded
        HDisjointError
        HNoAllocLeftError HNoAllocRightError
        HErrorPrefix)
      as (heap_left_error & v_left_error &
        heap_right_error & HLeftDoneError &
        HRightErrorSteps & _HHeapError).
    destruct
      (Steps_terminal_deterministic
        (InitialState heap env rho (EMuApp ef1 ea1))
        (trace_view_flatten view_left_success)
        heap_left_success
        v_left_success
        (trace_view_flatten view_left_error)
        heap_left_error
        v_left_error
        HLeftSuccess
        HLeftDoneError)
      as (HHeapLeft & HValueLeft).
    subst heap_left_error v_left_error.
    destruct
      (Steps_terminal_state_trace_deterministic
        (with_state_heap heap_left_success
          (InitialState heap env rho (EMuApp ef2 ea2)))
        (trace_view_flatten view_right_success)
        (StDone heap_canonical_success v_right_success)
        (trace_view_flatten view_right_error)
        (StError heap_right_error)
        HRightSuccess
        (TerminalDone heap_canonical_success v_right_success)
        HRightErrorSteps
        (TerminalError heap_right_error))
      as (_HTraceRight & HStateRight).
    discriminate HStateRight.
Qed.

Corollary ScheduledPairParRun_checked_pairpar_outcome_deterministic :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    summary_disjointb theta_left theta_right = true ->
    TraceViewCoveredBySummary view_left1 theta_left ->
    TraceViewCoveredBySummary view_right1 theta_right ->
    TraceViewCoveredBySummary view_left2 theta_left ->
    TraceViewCoveredBySummary view_right2 theta_right ->
    (forall heap_join1 heap_join2 value_join1 value_join2,
      ScheduledPairParRun
        (StPairParRun
          (InitialState heap env rho (EMuApp ef1 ea1))
          (InitialState heap env rho (EMuApp ef2 ea2))
          [] [] k)
        view_left1
        view_right1
        (StReturn heap_join1 value_join1 k) ->
      ScheduledPairParRun
        (StPairParRun
          (InitialState heap env rho (EMuApp ef1 ea1))
          (InitialState heap env rho (EMuApp ef2 ea2))
          [] [] k)
        view_left2
        view_right2
        (StReturn heap_join2 value_join2 k) ->
      heap_join1 = heap_join2 /\ value_join1 = value_join2) /\
    (forall heap_error1 heap_error2,
      ScheduledPairParRun
        (StPairParRun
          (InitialState heap env rho (EMuApp ef1 ea1))
          (InitialState heap env rho (EMuApp ef2 ea2))
          [] [] k)
        view_left1
        view_right1
        (StError heap_error1) ->
      ScheduledPairParRun
        (StPairParRun
          (InitialState heap env rho (EMuApp ef1 ea1))
          (InitialState heap env rho (EMuApp ef2 ea2))
          [] [] k)
        view_left2
        view_right2
        (StError heap_error2) ->
      ((exists right_final1 phi_left_final1 phi_right_final1,
          ScheduledPairParRun
            (StPairParRun
              (InitialState heap env rho (EMuApp ef1 ea1))
              (InitialState heap env rho (EMuApp ef2 ea2))
              [] [] k)
            view_left1
            view_right1
            (StPairParRun
              (StError heap_error1)
              right_final1
              phi_left_final1
              phi_right_final1
              k)) /\
        (exists right_final2 phi_left_final2 phi_right_final2,
          ScheduledPairParRun
            (StPairParRun
              (InitialState heap env rho (EMuApp ef1 ea1))
              (InitialState heap env rho (EMuApp ef2 ea2))
              [] [] k)
            view_left2
            view_right2
            (StPairParRun
              (StError heap_error2)
              right_final2
              phi_left_final2
              phi_right_final2
              k)) /\
        HeapEqOn
          (fun r l =>
            TraceDoesNotWrite r l (trace_view_flatten view_right1) /\
            TraceDoesNotWrite r l (trace_view_flatten view_right2))
          heap_error1
          heap_error2) \/
      ((exists heap_left1 v_left1 phi_left_final1 phi_right_final1,
          ScheduledPairParRun
            (StPairParRun
              (InitialState heap env rho (EMuApp ef1 ea1))
              (InitialState heap env rho (EMuApp ef2 ea2))
              [] [] k)
            view_left1
            view_right1
            (StPairParRun
              (StDone heap_left1 v_left1)
              (StError heap_error1)
              phi_left_final1
              phi_right_final1
              k)) /\
        (exists heap_left2 v_left2 phi_left_final2 phi_right_final2,
          ScheduledPairParRun
            (StPairParRun
              (InitialState heap env rho (EMuApp ef1 ea1))
              (InitialState heap env rho (EMuApp ef2 ea2))
              [] [] k)
            view_left2
            view_right2
            (StPairParRun
              (StDone heap_left2 v_left2)
              (StError heap_error2)
              phi_left_final2
              phi_right_final2
              k)) /\
        heap_error1 = heap_error2)) /\
    (forall heap_join1 value_join1 heap_error2,
      ScheduledPairParRun
        (StPairParRun
          (InitialState heap env rho (EMuApp ef1 ea1))
          (InitialState heap env rho (EMuApp ef2 ea2))
          [] [] k)
        view_left1
        view_right1
        (StReturn heap_join1 value_join1 k) ->
      ScheduledPairParRun
        (StPairParRun
          (InitialState heap env rho (EMuApp ef1 ea1))
          (InitialState heap env rho (EMuApp ef2 ea2))
          [] [] k)
        view_left2
        view_right2
        (StError heap_error2) ->
      False) /\
    (forall heap_error1 heap_join2 value_join2,
      ScheduledPairParRun
        (StPairParRun
          (InitialState heap env rho (EMuApp ef1 ea1))
          (InitialState heap env rho (EMuApp ef2 ea2))
          [] [] k)
        view_left1
        view_right1
        (StError heap_error1) ->
      ScheduledPairParRun
        (StPairParRun
          (InitialState heap env rho (EMuApp ef1 ea1))
          (InitialState heap env rho (EMuApp ef2 ea2))
          [] [] k)
        view_left2
        view_right2
        (StReturn heap_join2 value_join2 k) ->
      False).
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k
    HBack HContext HSummaryDisjoint
    HCoveredLeft1 HCoveredRight1 HCoveredLeft2 HCoveredRight2.
  split.
  - intros ? ? ? ? HRun1 HRun2.
    eapply
      (ScheduledPairParRun_checked_pairpar_scheduled_join_determinism
        gamma omega rho heap env ef1 ea1 ef2 ea2
        view_left1 view_right1 view_left2 view_right2);
      eauto.
  - split.
    + intros ? ? HRun1 HRun2.
      eapply
        (ScheduledPairParRun_checked_pairpar_error_cause_deterministic
          gamma omega rho heap env ef1 ea1 ef2 ea2
          view_left1 view_right1 view_left2 view_right2
          theta_left theta_right);
        eauto.
    + split.
      * intros ? ? ? HRun1 HRun2.
        eapply
          (ScheduledPairParRun_checked_pairpar_success_error_impossible
            gamma omega rho heap env ef1 ea1 ef2 ea2
            view_left1 view_right1 view_left2 view_right2
            theta_left theta_right);
          eauto.
      * intros ? ? ? HRun1 HRun2.
        eapply
          (ScheduledPairParRun_checked_pairpar_success_error_impossible
            gamma omega rho heap env ef1 ea1 ef2 ea2
            view_left2 view_right2 view_left1 view_right1
            theta_left theta_right);
          eauto.
Qed.

Corollary ScheduledPairParRun_checked_pairpar_computations_join_determinism :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    heap_left1 heap_left2 heap_right1 heap_right2
    v_left1 v_left2 v_right1 v_right2
    k heap_join1 heap_join2 value_join1 value_join2,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    StructuredComputationEvaluation
      heap env rho (EMuApp ef1 ea1)
      view_left1 heap_left1 v_left1 ->
    StructuredComputationEvaluation
      heap env rho (EMuApp ef1 ea1)
      view_left2 heap_left2 v_left2 ->
    StructuredComputationEvaluation
      heap env rho (EMuApp ef2 ea2)
      view_right1 heap_right1 v_right1 ->
    StructuredComputationEvaluation
      heap env rho (EMuApp ef2 ea2)
      view_right2 heap_right2 v_right2 ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left1
      view_right1
      (StReturn heap_join1 value_join1 k) ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left2
      view_right2
      (StReturn heap_join2 value_join2 k) ->
    heap_join1 = heap_join2 /\ value_join1 = value_join2.
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    heap_left1 heap_left2 heap_right1 heap_right2
    v_left1 v_left2 v_right1 v_right2
    k heap_join1 heap_join2 value_join1 value_join2
    HBack HContext
    _HCompLeft1 _HCompLeft2 _HCompRight1 _HCompRight2
    HSchedule1 HSchedule2.
  eapply
    (ScheduledPairParRun_checked_pairpar_scheduled_join_determinism
      gamma omega rho heap env ef1 ea1 ef2 ea2
      view_left1 view_right1 view_left2 view_right2
      k heap_join1 heap_join2 value_join1 value_join2);
    eauto.
Qed.

Corollary ScheduledPairParRun_checked_pairpar_scheduled_continuation_terminal_trace_deterministic :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    k heap_join1 heap_join2 value_join1 value_join2
    phi_tail1 phi_tail2 heap_final1 heap_final2 value_final1 value_final2,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left1
      view_right1
      (StReturn heap_join1 value_join1 k) ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left2
      view_right2
      (StReturn heap_join2 value_join2 k) ->
    Steps
      (StReturn heap_join1 value_join1 k)
      phi_tail1
      (StDone heap_final1 value_final1) ->
    Steps
      (StReturn heap_join2 value_join2 k)
      phi_tail2
      (StDone heap_final2 value_final2) ->
    heap_join1 = heap_join2 /\
    value_join1 = value_join2 /\
    phi_tail1 = phi_tail2 /\
    heap_final1 = heap_final2 /\
    value_final1 = value_final2.
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    k heap_join1 heap_join2 value_join1 value_join2
    phi_tail1 phi_tail2 heap_final1 heap_final2 value_final1 value_final2
    HBack HContext HSchedule1 HSchedule2 HTail1 HTail2.
  destruct
    (ScheduledPairParRun_checked_pairpar_scheduled_join_determinism
      gamma omega rho heap env ef1 ea1 ef2 ea2
      view_left1 view_right1 view_left2 view_right2
      k heap_join1 heap_join2 value_join1 value_join2
      HBack HContext HSchedule1 HSchedule2)
    as (HHeapJoin & HValueJoin).
  subst heap_join2 value_join2.
  destruct
    (Steps_terminal_trace_deterministic
      (StReturn heap_join1 value_join1 k)
      phi_tail1
      heap_final1
      value_final1
      phi_tail2
      heap_final2
      value_final2
      HTail1
      HTail2)
    as (HTailTrace & HHeapFinal & HValueFinal).
  repeat split; assumption || reflexivity.
Qed.

Corollary ScheduledPairParRun_checked_pairpar_evaluations_join_determinism :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    view_summary_left view_summary_right
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right
    heap_summary_left heap_summary_right
    heap_left1 heap_left2 heap_right1 heap_right2
    v_left1 v_left2 v_right1 v_right2
    k heap_join1 heap_join2 value_join1 value_join2,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    summary_disjointb theta_left theta_right = true ->
    StructuredSummaryEvaluation
      heap env rho (EEffApp ef1 ea1)
      view_summary_left heap_summary_left theta_left ->
    StructuredSummaryEvaluation
      heap env rho (EEffApp ef2 ea2)
      view_summary_right heap_summary_right theta_right ->
    StructuredComputationEvaluation
      heap env rho (EMuApp ef1 ea1)
      view_left1 heap_left1 v_left1 ->
    StructuredComputationEvaluation
      heap env rho (EMuApp ef1 ea1)
      view_left2 heap_left2 v_left2 ->
    StructuredComputationEvaluation
      heap env rho (EMuApp ef2 ea2)
      view_right1 heap_right1 v_right1 ->
    StructuredComputationEvaluation
      heap env rho (EMuApp ef2 ea2)
      view_right2 heap_right2 v_right2 ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left1
      view_right1
      (StReturn heap_join1 value_join1 k) ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left2
      view_right2
      (StReturn heap_join2 value_join2 k) ->
    heap_join1 = heap_join2 /\ value_join1 = value_join2.
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    view_summary_left view_summary_right
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right
    heap_summary_left heap_summary_right
    heap_left1 heap_left2 heap_right1 heap_right2
    v_left1 v_left2 v_right1 v_right2
    k heap_join1 heap_join2 value_join1 value_join2
    HBack HContext _HSummaryDisjoint
    _HSummaryLeft _HSummaryRight
    _HCompLeft1 _HCompLeft2 _HCompRight1 _HCompRight2
    HSchedule1 HSchedule2.
  eapply
    (ScheduledPairParRun_checked_pairpar_scheduled_join_determinism
      gamma omega rho heap env ef1 ea1 ef2 ea2
      view_left1 view_right1 view_left2 view_right2
      k heap_join1 heap_join2 value_join1 value_join2);
    eauto.
Qed.

Corollary ScheduledPairParRun_checked_pairpar_evaluations_continuation_terminal_trace_deterministic :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    view_summary_left view_summary_right
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right
    heap_summary_left heap_summary_right
    heap_left1 heap_left2 heap_right1 heap_right2
    v_left1 v_left2 v_right1 v_right2
    k heap_join1 heap_join2 value_join1 value_join2
    phi_tail1 phi_tail2 heap_final1 heap_final2 value_final1 value_final2,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    CheckedRuntimeContext gamma omega heap env rho ->
    summary_disjointb theta_left theta_right = true ->
    StructuredSummaryEvaluation
      heap env rho (EEffApp ef1 ea1)
      view_summary_left heap_summary_left theta_left ->
    StructuredSummaryEvaluation
      heap env rho (EEffApp ef2 ea2)
      view_summary_right heap_summary_right theta_right ->
    StructuredComputationEvaluation
      heap env rho (EMuApp ef1 ea1)
      view_left1 heap_left1 v_left1 ->
    StructuredComputationEvaluation
      heap env rho (EMuApp ef1 ea1)
      view_left2 heap_left2 v_left2 ->
    StructuredComputationEvaluation
      heap env rho (EMuApp ef2 ea2)
      view_right1 heap_right1 v_right1 ->
    StructuredComputationEvaluation
      heap env rho (EMuApp ef2 ea2)
      view_right2 heap_right2 v_right2 ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left1
      view_right1
      (StReturn heap_join1 value_join1 k) ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left2
      view_right2
      (StReturn heap_join2 value_join2 k) ->
    Steps
      (StReturn heap_join1 value_join1 k)
      phi_tail1
      (StDone heap_final1 value_final1) ->
    Steps
      (StReturn heap_join2 value_join2 k)
      phi_tail2
      (StDone heap_final2 value_final2) ->
    heap_join1 = heap_join2 /\
    value_join1 = value_join2 /\
    phi_tail1 = phi_tail2 /\
    heap_final1 = heap_final2 /\
    value_final1 = value_final2.
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    view_summary_left view_summary_right
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right
    heap_summary_left heap_summary_right
    heap_left1 heap_left2 heap_right1 heap_right2
    v_left1 v_left2 v_right1 v_right2
    k heap_join1 heap_join2 value_join1 value_join2
    phi_tail1 phi_tail2 heap_final1 heap_final2 value_final1 value_final2
    HBack HContext _HSummaryDisjoint
    _HSummaryLeft _HSummaryRight
    _HCompLeft1 _HCompLeft2 _HCompRight1 _HCompRight2
    HSchedule1 HSchedule2 HTail1 HTail2.
  eapply
    (ScheduledPairParRun_checked_pairpar_scheduled_continuation_terminal_trace_deterministic
      gamma omega rho heap env ef1 ea1 ef2 ea2
      view_left1 view_right1 view_left2 view_right2
      k heap_join1 heap_join2 value_join1 value_join2
      phi_tail1 phi_tail2 heap_final1 heap_final2
      value_final1 value_final2);
    eauto.
Qed.

Corollary ScheduledPairParRun_checked_pairpar_continuation_terminal_trace_deterministic :
  forall gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right eff_left_res eff_right_res
    k heap_join1 heap_join2 value_join1 value_join2
    phi_tail1 phi_tail2 heap_final1 heap_final2 value_final1 value_final2,
    CheckedBackTriangle gamma omega
      (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2))
      (EConcat (EEffApp ef1 ea1) (EEffApp ef2 ea2)) ->
    HeapKeysBounded heap ->
    summary_disjointb theta_left theta_right = true ->
    (forall ty_left eff_left,
      CheckedTcExp gamma omega (EMuApp ef1 ea1) ty_left eff_left ->
      ResolveStaticEffect rho eff_left eff_left_res /\
      TraceCoveredByStaticEffect
        (trace_view_flatten view_left1) eff_left_res /\
      TraceCoveredByStaticEffect
        (trace_view_flatten view_left2) eff_left_res) ->
    (forall ty_right eff_right,
      CheckedTcExp gamma omega (EMuApp ef2 ea2) ty_right eff_right ->
      ResolveStaticEffect rho eff_right eff_right_res /\
      TraceCoveredByStaticEffect
        (trace_view_flatten view_right1) eff_right_res /\
      TraceCoveredByStaticEffect
        (trace_view_flatten view_right2) eff_right_res) ->
    TraceViewCoveredBySummary view_left1 theta_left ->
    TraceViewCoveredBySummary view_right1 theta_right ->
    TraceViewCoveredBySummary view_left2 theta_left ->
    TraceViewCoveredBySummary view_right2 theta_right ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left1
      view_right1
      (StReturn heap_join1 value_join1 k) ->
    ScheduledPairParRun
      (StPairParRun
        (InitialState heap env rho (EMuApp ef1 ea1))
        (InitialState heap env rho (EMuApp ef2 ea2))
        [] [] k)
      view_left2
      view_right2
      (StReturn heap_join2 value_join2 k) ->
    Steps
      (StReturn heap_join1 value_join1 k)
      phi_tail1
      (StDone heap_final1 value_final1) ->
    Steps
      (StReturn heap_join2 value_join2 k)
      phi_tail2
      (StDone heap_final2 value_final2) ->
    heap_join1 = heap_join2 /\
    value_join1 = value_join2 /\
    phi_tail1 = phi_tail2 /\
    heap_final1 = heap_final2 /\
    value_final1 = value_final2.
Proof.
  intros gamma omega rho heap env ef1 ea1 ef2 ea2
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right eff_left_res eff_right_res
    k heap_join1 heap_join2 value_join1 value_join2
    phi_tail1 phi_tail2 heap_final1 heap_final2 value_final1 value_final2
    HBack HBounded HSummaryDisjoint
    HStaticLeft HStaticRight
    HCoveredLeft1 HCoveredRight1 HCoveredLeft2 HCoveredRight2
    HSchedule1 HSchedule2 HTail1 HTail2.
  destruct
    (ScheduledPairParRun_checked_pairpar_join_determinism
      gamma omega rho heap env ef1 ea1 ef2 ea2
      view_left1 view_right1 view_left2 view_right2
      theta_left theta_right eff_left_res eff_right_res
      k heap_join1 heap_join2 value_join1 value_join2
      HBack HBounded HSummaryDisjoint
      HStaticLeft HStaticRight
      HCoveredLeft1 HCoveredRight1 HCoveredLeft2 HCoveredRight2
      HSchedule1 HSchedule2)
    as (HHeapJoin & HValueJoin).
  subst heap_join2 value_join2.
  destruct
    (Steps_terminal_trace_deterministic
      (StReturn heap_join1 value_join1 k)
      phi_tail1
      heap_final1
      value_final1
      phi_tail2
      heap_final2
      value_final2
      HTail1
      HTail2)
    as (HTailTrace & HHeapFinal & HValueFinal).
  repeat split; assumption || reflexivity.
Qed.

Corollary ScheduledPairParRun_checked_continuation_terminal_trace_deterministic :
  forall left_state right_state
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k
    heap_join1 heap_join2 value_join1 value_join2
    phi_tail1 phi_tail2 heap_final1 heap_final2 value_final1 value_final2,
    StateHeapsAligned left_state ->
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    HeapKeysBounded (state_heap left_state) ->
    summary_disjointb theta_left theta_right = true ->
    NoAllocTraceView view_left1 ->
    NoAllocTraceView view_right1 ->
    NoAllocTraceView view_left2 ->
    NoAllocTraceView view_right2 ->
    TraceViewCoveredBySummary view_left1 theta_left ->
    TraceViewCoveredBySummary view_right1 theta_right ->
    TraceViewCoveredBySummary view_left2 theta_left ->
    TraceViewCoveredBySummary view_right2 theta_right ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left1
      view_right1
      (StReturn heap_join1 value_join1 k) ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left2
      view_right2
      (StReturn heap_join2 value_join2 k) ->
    Steps
      (StReturn heap_join1 value_join1 k)
      phi_tail1
      (StDone heap_final1 value_final1) ->
    Steps
      (StReturn heap_join2 value_join2 k)
      phi_tail2
      (StDone heap_final2 value_final2) ->
    heap_join1 = heap_join2 /\
    value_join1 = value_join2 /\
    phi_tail1 = phi_tail2 /\
    heap_final1 = heap_final2 /\
    value_final1 = value_final2.
Proof.
  intros left_state right_state
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k
    heap_join1 heap_join2 value_join1 value_join2
    phi_tail1 phi_tail2 heap_final1 heap_final2 value_final1 value_final2
    HAlignedLeft HAlignedRight HHeapAligned HBounded HSummaryDisjoint
    HNoAllocLeft1 HNoAllocRight1 HNoAllocLeft2 HNoAllocRight2
    HCoveredLeft1 HCoveredRight1 HCoveredLeft2 HCoveredRight2
    HSchedule1 HSchedule2 HTail1 HTail2.
  destruct
    (ScheduledPairParRun_checked_join_determinism
      left_state right_state
      view_left1 view_right1 view_left2 view_right2
      theta_left theta_right k heap_join1 heap_join2
      value_join1 value_join2
      HAlignedLeft HAlignedRight HHeapAligned HBounded
      HSummaryDisjoint
      HNoAllocLeft1 HNoAllocRight1 HNoAllocLeft2 HNoAllocRight2
      HCoveredLeft1 HCoveredRight1 HCoveredLeft2 HCoveredRight2
      HSchedule1 HSchedule2)
    as (HHeapJoin & HValueJoin).
  subst heap_join2 value_join2.
  destruct
    (Steps_terminal_trace_deterministic
      (StReturn heap_join1 value_join1 k)
      phi_tail1
      heap_final1
      value_final1
      phi_tail2
      heap_final2
      value_final2
      HTail1
      HTail2)
    as (HTailTrace & HHeapFinal & HValueFinal).
  repeat split; assumption || reflexivity.
Qed.

Corollary ScheduledPairParRun_checked_terminal_trace_deterministic :
  forall left_state right_state
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k heap1 heap2 value1 value2,
    StateHeapsAligned left_state ->
    StateHeapsAligned right_state ->
    state_heap left_state = state_heap right_state ->
    HeapKeysBounded (state_heap left_state) ->
    summary_disjointb theta_left theta_right = true ->
    NoAllocTraceView view_left1 ->
    NoAllocTraceView view_right1 ->
    NoAllocTraceView view_left2 ->
    NoAllocTraceView view_right2 ->
    TraceViewCoveredBySummary view_left1 theta_left ->
    TraceViewCoveredBySummary view_right1 theta_right ->
    TraceViewCoveredBySummary view_left2 theta_left ->
    TraceViewCoveredBySummary view_right2 theta_right ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left1
      view_right1
      (StReturn heap1 value1 k) ->
    ScheduledPairParRun
      (StPairParRun left_state right_state [] [] k)
      view_left2
      view_right2
      (StReturn heap2 value2 k) ->
    trace_view_flatten (TracePar view_left1 view_right1) =
    trace_view_flatten (TracePar view_left2 view_right2) /\
    heap1 = heap2 /\
    value1 = value2.
Proof.
  intros left_state right_state
    view_left1 view_right1 view_left2 view_right2
    theta_left theta_right k heap1 heap2 value1 value2
    HAlignedLeft HAlignedRight HHeapAligned HBounded
    HSummaryDisjoint
    HNoAllocLeft1 HNoAllocRight1 HNoAllocLeft2 HNoAllocRight2
    HCoveredLeft1 HCoveredRight1 HCoveredLeft2 HCoveredRight2
    HSchedule1 HSchedule2.
  destruct
    (ScheduledPairParRun_noalloc_checked_canonical
      left_state right_state [] []
      view_left1 view_right1 theta_left theta_right k heap1 value1
      HAlignedLeft HAlignedRight HHeapAligned HBounded
      HSummaryDisjoint HCoveredLeft1 HCoveredRight1
      HNoAllocLeft1 HNoAllocRight1 HSchedule1)
    as (heap_left1 & heap_canonical1 & v_left1 & v_right1 &
      HValue1 & HLeft1 & HRight1 & HHeap1).
  destruct
    (ScheduledPairParRun_noalloc_checked_canonical
      left_state right_state [] []
      view_left2 view_right2 theta_left theta_right k heap2 value2
      HAlignedLeft HAlignedRight HHeapAligned HBounded
      HSummaryDisjoint HCoveredLeft2 HCoveredRight2
      HNoAllocLeft2 HNoAllocRight2 HSchedule2)
    as (heap_left2 & heap_canonical2 & v_left2 & v_right2 &
      HValue2 & HLeft2 & HRight2 & HHeap2).
  destruct
    (Steps_terminal_trace_deterministic
      left_state
      (trace_view_flatten view_left1)
      heap_left1
      v_left1
      (trace_view_flatten view_left2)
      heap_left2
      v_left2
      HLeft1
      HLeft2)
    as (HTraceLeft & HHeapLeft & HValueLeft).
  subst heap_left2 v_left2.
  destruct
    (Steps_terminal_trace_deterministic
      (with_state_heap heap_left1 right_state)
      (trace_view_flatten view_right1)
      heap_canonical1
      v_right1
      (trace_view_flatten view_right2)
      heap_canonical2
      v_right2
      HRight1
      HRight2)
    as (HTraceRight & HHeapRight & HValueRight).
  subst heap_canonical2 v_right2.
  split.
  - repeat rewrite TracePar_flatten_canonical.
    rewrite HTraceLeft, HTraceRight.
    reflexivity.
  - split.
    + congruence.
    + rewrite HValue1, HValue2.
      reflexivity.
Qed.

(** Main exported names for the scheduler layer.  The detailed lemmas above
    keep their descriptive proof-oriented names; these aliases are the stable
    entry points for clients that only need the checked PairPar story. *)

Definition ScheduledPairParRun_checked_pairpar_left_then_right_embeds :=
  ScheduledPairParRun_checked_pairpar_left_then_right_success.

Definition ScheduledPairParRun_checked_pairpar_nsteps_embeds :=
  Steps_checked_pairpar_kdone_terminal_embeds_scheduled.

Definition ScheduledPairParRun_checked_pairpar_success_join_deterministic :=
  ScheduledPairParRun_checked_pairpar_scheduled_join_determinism.

Definition
  ScheduledPairParRun_checked_pairpar_success_continuation_deterministic :=
  ScheduledPairParRun_checked_pairpar_scheduled_continuation_terminal_trace_deterministic.

Definition ScheduledPairParRun_checked_pairpar_error_classifies :=
  ScheduledPairParRun_checked_pairpar_error_is_branch_error.

Definition ScheduledPairParRun_checked_pairpar_error_same_cause :=
  ScheduledPairParRun_checked_pairpar_error_cause_deterministic.

Definition
  ScheduledPairParRun_checked_pairpar_left_error_read_only_right_lookup :=
  ScheduledPairParRun_checked_pairpar_left_error_read_only_right_heap_lookup_deterministic.

Definition ScheduledPairParRun_checked_pairpar_success_error_disjoint :=
  ScheduledPairParRun_checked_pairpar_success_error_impossible.

Definition
  ScheduledPairParRun_checked_pairpar_terminal_outcomes_deterministic :=
  ScheduledPairParRun_checked_pairpar_outcome_deterministic.
