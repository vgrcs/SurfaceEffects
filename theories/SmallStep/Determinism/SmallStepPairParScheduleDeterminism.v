From Stdlib Require Import List.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Sets.Ensembles.
From stdpp Require Import gmap.

Require Import theories.Core.DynamicActions.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Runtime.Heap.
Require Import theories.Runtime.TraceSemantics.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepPairParDispatch.
Require Import theories.Runtime.SmallStepStructuredTrace.
Require Import theories.Runtime.SmallStepCorrectness.
Require Import theories.Meta.EffectFacts.
Require Import theories.Meta.HeapFacts.
Require Import theories.Determinism.Determinism.
Require Import theories.Determinism.SmallStepStructuredReplay.

Definition PairParRunBranchesOrdinary (state : PairParState) : Prop :=
  match state with
  | PPS_State _ => True
  | PPS_Run left_state right_state _ =>
      NonPairParRunState left_state /\ NonPairParRunState right_state
  end.

Lemma Det_Trace_of_phi_as_list_nil :
  forall phi,
    phi_as_list phi = nil ->
    Det_Trace phi.
Proof.
  induction phi as [| da | phi1 IHphi1 phi2 IHphi2
                   | phi1 IHphi1 phi2 IHphi2]; intros HNil; simpl in HNil.
  - constructor.
  - discriminate.
  - apply app_eq_nil in HNil as [HNil1 HNil2].
    constructor; [now apply IHphi1 | now apply IHphi2 |].
    split.
    + intro HConflict.
      inversion HConflict as [p1 p2 tr1 tr2 HIn1 _ _]; subst.
      rewrite HNil1 in HIn1.
      inversion HIn1.
    + constructor. intros p1 p2 HIn1 _.
      rewrite HNil1 in HIn1. inversion HIn1.
  - apply app_eq_nil in HNil as [HNil1 HNil2].
    constructor; [now apply IHphi1 | now apply IHphi2].
Qed.

Lemma Phi_Heap_Steps_empty_as_list_reaches_same_heap :
  forall phi heap,
    phi_as_list phi = nil ->
    (phi, heap) ==>* (Phi_Nil, heap).
Proof.
  induction phi as [| da | phi1 IHphi1 phi2 IHphi2
                   | phi1 IHphi1 phi2 IHphi2]; intros heap HNil; simpl in HNil.
  - exists 0. constructor.
  - discriminate.
  - apply app_eq_nil in HNil as [HNil1 HNil2].
    eapply structured_phi_par_steps.
    + now apply IHphi1.
    + now apply IHphi2.
  - apply app_eq_nil in HNil as [HNil1 HNil2].
    eapply structured_phi_seq_steps.
    + now apply IHphi1.
    + now apply IHphi2.
Qed.

Lemma Phi_Heap_Steps_empty_as_list_preserves_heap :
  forall phi heap heap',
    phi_as_list phi = nil ->
    (phi, heap) ==>* (Phi_Nil, heap') ->
    heap ≡@{Heap} heap'.
Proof.
  intros phi heap heap' HNil HSteps.
  eapply Diamond_Term_Walk.
  - eapply Phi_Heap_Steps_empty_as_list_reaches_same_heap; eauto.
  - exact HSteps.
  - now apply Det_Trace_of_phi_as_list_nil.
Qed.

Lemma Det_Trace_label_phi :
  forall label,
    Det_Trace (label_phi label).
Proof.
  intros [| da]; constructor.
Qed.

Lemma PairParStepsPhi_branch_det_traces :
  forall state phi_state phi_left phi_right state',
    PairParStepsPhi state phi_state phi_left phi_right state' ->
    Det_Trace phi_left /\ Det_Trace phi_right.
Proof.
  intros state phi_state phi_left phi_right state' HSteps.
	  induction HSteps as
	    [state
	    | state label state' phi_state phi_left phi_right state''
	        HNonRun HNonRun' HStep _ IH
	    | left right k label left' phi_state phi_left phi_right state''
	        HNonRunLeft HNonRunLeft' HStep _ IH
	    | left right k label right' phi_state phi_left phi_right state''
	        HNonRunRight HNonRunRight' HStep _ IH
    | heap v1 v2 k phi_state phi_left phi_right state'' _ IH].
  - split; constructor.
  - exact IH.
  - destruct IH as [HDetLeft HDetRight].
    split; [constructor; [apply Det_Trace_label_phi | exact HDetLeft] |
            exact HDetRight].
  - destruct IH as [HDetLeft HDetRight].
    split; [exact HDetLeft |
            constructor; [apply Det_Trace_label_phi | exact HDetRight]].
  - exact IH.
Qed.

Lemma PairParLoosePackedStepsPhi_branch_det_traces :
  forall state phi_sched phi_state phi_left phi_right state',
    PairParLoosePackedStepsPhi
      state phi_sched phi_state phi_left phi_right state' ->
    Det_Trace phi_left /\ Det_Trace phi_right.
Proof.
  intros state phi_sched phi_state phi_left phi_right state' HSteps.
  induction HSteps as
    [state
    | state label state' phi_sched phi_state phi_left phi_right state''
        HStep _ IH
    | left right k label left' phi_sched phi_state phi_left phi_right state''
        HStep _ IH
    | left right k label right' phi_sched phi_state phi_left phi_right state''
        HStep _ IH
    | heap v1 v2 k phi_sched phi_state phi_left phi_right state'' _ IH].
  - split; constructor.
  - exact IH.
  - destruct IH as [HDetLeft HDetRight].
    split; [constructor; [apply Det_Trace_label_phi | exact HDetLeft] |
            exact HDetRight].
  - destruct IH as [HDetLeft HDetRight].
    split; [exact HDetLeft |
            constructor; [apply Det_Trace_label_phi | exact HDetRight]].
  - exact IH.
Qed.

Lemma PairParStepsPhi_state_as_stepsphi :
  forall state phi_state phi_left phi_right state',
    PairParStepsPhi
      (PPS_State state) phi_state phi_left phi_right state' ->
    phi_left = Phi_Nil /\
    phi_right = Phi_Nil /\
    exists state_final,
      state' = PPS_State state_final /\
      StepsPhi state phi_state state_final.
Proof.
  intros state phi_state phi_left phi_right state' HSteps.
  dependent induction HSteps.
  - split; [reflexivity |].
    split; [reflexivity |].
    exists state. split; [reflexivity | constructor].
  - destruct (IHHSteps state' eq_refl)
      as (HLeftNil & HRightNil & state_final & HFinal & HStepsPhi).
    split; [exact HLeftNil |].
    split; [exact HRightNil |].
    exists state_final. split; [exact HFinal |].
    econstructor; eauto.
Qed.

Lemma PairParSteps_state_as_steps :
  forall state trace state',
    StepsStayNonPairParRun state ->
    PairParSteps (PPS_State state) trace state' ->
    exists state_final,
      state' = PPS_State state_final /\
      Steps state trace state_final.
Proof.
  intros state trace state' HStay HSteps.
  remember (PPS_State state) as pstate eqn:HPState.
  revert state HStay HPState.
  induction HSteps as
    [pstate
    | pstate label pstate1 trace pstate2 HStep HSteps IH];
    intros state0 HStay HPState; subst.
  - exists state0. split; [reflexivity | constructor].
  - inversion HStep; subst.
    assert (HOneStep : Steps state0 (label_trace label) state').
    {
      destruct label as [| da].
      - apply step_silent_steps. exact H1.
      - apply step_act_steps. exact H1.
    }
    assert (HNonRunTarget : NonPairParRunState state').
    {
      eapply HStay. exact HOneStep.
    }
    assert (HStayTarget : StepsStayNonPairParRun state').
    {
      eapply steps_stay_non_pairpar_run_tail; eauto.
    }
    destruct (IH state' HStayTarget
      (pairpar_state_of_state_non_pair state' HNonRunTarget))
      as (state_final & HFinal & HStepsState).
    exists state_final. split; [exact HFinal |].
    econstructor; eauto.
Qed.

Lemma StepsStayNonPairParRun_return_kdone :
  forall heap v,
    StepsStayNonPairParRun (StReturn heap v KDone).
Proof.
  intros heap v trace state HSteps.
  inversion HSteps; subst.
  - simpl. exact I.
  - match goal with
    | HStep : Step (StReturn heap v KDone) _ _ |- _ =>
        inversion HStep; subst
    end.
    match goal with
    | HTail : Steps (StDone heap v) ?trace_tail ?state_tail |- _ =>
        destruct
          (terminal_steps_refl
            (StDone heap v) trace_tail state_tail
            (Terminal_Done heap v) HTail)
          as [_ HState];
        subst; simpl; exact I
    end.
Qed.

Lemma PairParSteps_run_kdone_terminal_pair_value :
  forall left right trace heap v,
    PairParSteps
      (PPS_Run left right KDone)
      trace
      (PPS_State (StDone heap v)) ->
    exists v1 v2,
      v = Pair (v1, v2).
Proof.
  intros left right trace heap v HSteps.
  dependent induction HSteps generalizing left right.
  inversion H; subst; try solve [eapply IHHSteps; reflexivity].
  destruct
    (PairParSteps_state_as_steps
      (StReturn heap0 (Pair (v1, v2)) KDone)
      trace
      (PPS_State (StDone heap v))
      (StepsStayNonPairParRun_return_kdone heap0 (Pair (v1, v2)))
      HSteps)
    as (state_final & HFinal & HStepsState).
  inversion HFinal; subst.
  destruct
    (Steps_terminal_deterministic
      (StReturn heap0 (Pair (v1, v2)) KDone)
      trace heap v
      nil heap0 (Pair (v1, v2))
      (StepsStayNonPairParRun_return_kdone heap0 (Pair (v1, v2))))
    as (_ & _ & Hv).
  - exact HStepsState.
  - replace nil with (label_trace Silent ++ nil) by reflexivity.
    econstructor.
    + constructor.
    + constructor.
  - exists v1, v2. exact Hv.
Qed.

Lemma PairParStepsPhi_run_kdone_terminal_pair_value :
  forall left right phi_state phi_left phi_right heap v,
    PairParStepsPhi
      (PPS_Run left right KDone)
      phi_state phi_left phi_right
      (PPS_State (StDone heap v)) ->
    exists v1 v2,
      v = Pair (v1, v2).
Proof.
  intros left right phi_state phi_left phi_right heap v HSteps.
  destruct (PairParStepsPhi_as_pairpar_steps_exists _ _ _ _ _ HSteps)
    as (trace & HPairSteps).
  eapply PairParSteps_run_kdone_terminal_pair_value; eauto.
Qed.

Definition label_result_heap (label : Label) (heap : Heap) : Heap :=
  match label with
  | Silent => heap
  | Act (DA_Alloc r l v) => update_H ((r, l), v) heap
  | Act (DA_Read _ _ _) => heap
  | Act (DA_Write r l v) => update_H ((r, l), v) heap
  end.

Definition LabelHeapSafe (label : Label) (heap : Heap) : Prop :=
  match label with
  | Silent => True
  | Act (DA_Alloc r l _) => allocate_H heap r = l
  | Act (DA_Read r l v) => find_H (r, l) heap = Some v
  | Act (DA_Write r l _) => find_H (r, l) heap <> None
  end.

Lemma Step_label_heap_safe :
  forall state label state',
    Step state label state' ->
    LabelHeapSafe label (state_heap state).
Proof.
  intros state label state' HStep.
  induction HStep; simpl; auto.
  rewrite H. exact IHHStep.
Qed.

Lemma Step_rebase_with_safe_label :
  forall state label state' heap,
    NonPairParRunState state ->
    Step state label state' ->
    LabelHeapSafe label heap ->
    Step
      (with_state_heap heap state)
      label
      (with_state_heap (label_result_heap label heap) state').
Proof.
  intros state label state' heap HNonPair HStep HSafe.
  destruct state as
    [heap0 env rho e k | heap0 v k | heap0 v | left_state right_state k];
    simpl in HNonPair; try contradiction;
    inversion HStep; subst; simpl in *; try (constructor; eauto; fail).
Qed.

Lemma with_state_heap_overwrite :
  forall heap_outer heap_inner state,
    with_state_heap heap_outer (with_state_heap heap_inner state) =
    with_state_heap heap_outer state.
Proof.
  intros heap_outer heap_inner state.
  induction state; simpl; auto.
  now rewrite IHstate1, IHstate2.
Qed.

Lemma Step_rebase_with_safe_label_agree :
  forall state label state' heap,
    StateRunHeapsAgree state ->
    Step state label state' ->
    LabelHeapSafe label heap ->
    Step
      (with_state_heap heap state)
      label
      (with_state_heap (label_result_heap label heap) state').
Proof.
  intros state label state' heap HAgree HStep.
  revert heap HAgree.
  induction HStep; intros heap0 HAgree HSafe; simpl in *;
    try (constructor; eauto; fail).
  - destruct HAgree as [_ [HLeftAgree _HRightAgree]].
    simpl.
    rewrite with_state_heap_overwrite.
    replace
      (with_state_heap (label_result_heap label heap0) right_state)
      with
      (with_state_heap
        (state_heap
          (with_state_heap (label_result_heap label heap0) left_state'))
        (with_state_heap heap0 right_state)).
    + apply Step_PairParRun_Left.
      * repeat rewrite state_heap_with_state_heap. reflexivity.
      * apply IHHStep; assumption.
    + rewrite state_heap_with_state_heap.
      repeat rewrite with_state_heap_overwrite.
      reflexivity.
  - destruct HAgree as [_ [_HLeftAgree HRightAgree]].
    simpl.
    rewrite with_state_heap_overwrite.
    replace
      (with_state_heap (label_result_heap label heap0) left_state)
      with
      (with_state_heap
        (state_heap
          (with_state_heap (label_result_heap label heap0) right_state'))
        (with_state_heap heap0 left_state)).
    + apply Step_PairParRun_Right.
      * repeat rewrite state_heap_with_state_heap. reflexivity.
      * apply IHHStep; assumption.
    + rewrite state_heap_with_state_heap.
      repeat rewrite with_state_heap_overwrite.
      reflexivity.
Qed.

Lemma Step_unbase_with_safe_label :
  forall state heap label state',
    NonPairParRunState state ->
    Step (with_state_heap heap state) label state' ->
    LabelHeapSafe label (state_heap state) ->
    Step state label
      (with_state_heap (label_result_heap label (state_heap state)) state').
Proof.
  intros state heap label state' HNonPair HStep HSafe.
  destruct state as
    [heap0 env rho e k | heap0 v k | heap0 v | left_state right_state k];
    simpl in HNonPair; try contradiction; simpl in *;
    inversion HStep; subst; simpl in *; try (constructor; eauto; fail).
Qed.

Lemma Step_silent_preserves_heap :
  forall state state',
    Step state Silent state' ->
    state_heap state' = state_heap state.
Proof.
  intros state state' HStep.
  dependent induction HStep; subst; simpl; try reflexivity.
  - exact (IHHStep eq_refl).
  - rewrite state_heap_with_state_heap. rewrite H. exact (IHHStep eq_refl).
Qed.

Lemma Disjoint_Traces_single_inv :
  forall da1 da2,
    Disjoint_Traces (da1 :: nil) (da2 :: nil) ->
    Disjoint_Dynamic da1 da2.
Proof.
  intros da1 da2 HDisjoint.
  inversion HDisjoint as [tr1 tr2 HAll]; subst.
  apply HAll; simpl; auto.
Qed.

Lemma Disjoint_Dynamic_sym :
  forall da1 da2,
    Disjoint_Dynamic da1 da2 ->
    Disjoint_Dynamic da2 da1.
Proof.
  destruct da1 as [r1 l1 v1 | r1 l1 v1 | r1 l1 v1];
    destruct da2 as [r2 l2 v2 | r2 l2 v2 | r2 l2 v2];
    intro HDisjoint; inversion HDisjoint; subst; constructor;
    try assumption;
    match goal with
    | HNeq : ?x <> ?y |- ?y <> ?x =>
        intro HSame; apply HNeq; symmetry; exact HSame
    end.
Qed.

Lemma Disjoint_Traces_sym :
  forall trace1 trace2,
    Disjoint_Traces trace1 trace2 ->
    Disjoint_Traces trace2 trace1.
Proof.
  intros trace1 trace2 HDisjoint.
  inversion HDisjoint as [tr1 tr2 HAll]; subst.
  constructor.
  intros p2 p1 HIn2 HIn1.
  apply Disjoint_Dynamic_sym.
  eapply HAll; eauto.
Qed.

Lemma PairParCheckPass_sound_disjoint_traces :
  forall phi_left phi_right theta_left theta_right,
    phi_left ⋞ theta_left ->
    phi_right ⋞ theta_right ->
    PairParCheckPass theta_left theta_right ->
    Disjoint_Traces (phi_as_list phi_left) (phi_as_list phi_right).
Proof.
  intros phi_left phi_right theta_left theta_right
    HSoundLeft HSoundRight [HDisjoint _].
  eapply Phi_Theta_Disjointness_disjoint_traces; eauto.
Qed.

Lemma PairParCheckPass_sound_disjoint_traces_sym :
  forall phi_left phi_right theta_left theta_right,
    phi_left ⋞ theta_left ->
    phi_right ⋞ theta_right ->
    PairParCheckPass theta_left theta_right ->
    Disjoint_Traces (phi_as_list phi_right) (phi_as_list phi_left).
Proof.
  intros phi_left phi_right theta_left theta_right
    HSoundLeft HSoundRight HPass.
  apply Disjoint_Traces_sym.
  eapply PairParCheckPass_sound_disjoint_traces; eauto.
Qed.

Lemma LabelHeapSafe_alloc_preserved_by_alloc :
  forall heap r1 l1 v1 r2 l2 v2,
    allocate_H heap r1 = l1 ->
    allocate_H heap r2 = l2 ->
    Disjoint_Dynamic (DA_Alloc r1 l1 v1) (DA_Alloc r2 l2 v2) ->
    allocate_H (update_H ((r2, l2), v2) heap) r1 = l1.
Proof.
  intros heap r1 l1 v1 r2 l2 v2 HSafe HOther HDynamic.
  destruct (Nat.eq_dec r1 r2) as [HRegion | HRegion].
  - subst r1.
    assert (l1 = l2) by congruence.
    subst l1.
    inversion HDynamic; subst.
    match goal with
    | HNeq : (_, _) <> (_, _) |- _ =>
        exfalso; apply HNeq; reflexivity
    end.
  - rewrite allocate_H_update_fresh_different_region;
      [exact HSafe | intro H; apply HRegion; symmetry; exact H |].
    rewrite <- HOther.
    apply allocate_H_fresh.
Qed.

Lemma allocate_H_update_existing_nonnone :
  forall heap r k value,
    find_H k heap <> None ->
    allocate_H (update_H (k, value) heap) r = allocate_H heap r.
Proof.
  intros heap r k value HExists.
  destruct (find_H k heap) as [old |] eqn:HFind.
  - apply allocate_H_update_existing with (old_value := old).
    exact HFind.
  - contradiction.
Qed.

Lemma find_H_some_update_ne :
  forall heap k k_update v_update v,
    k <> k_update ->
    find_H k heap = Some v ->
    find_H k (update_H (k_update, v_update) heap) = Some v.
Proof.
  intros heap k k_update v_update v HNe HFind.
  apply H_diff_keys_2; [| exact HFind].
  intro HEq.
  apply HNe.
  symmetry.
  exact HEq.
Qed.

Lemma find_H_some_update_ne_reflect :
  forall heap k k_update v_update v,
    k <> k_update ->
    find_H k (update_H (k_update, v_update) heap) = Some v ->
    find_H k heap = Some v.
Proof.
  intros heap k k_update v_update v HNe HFind.
  eapply H_diff_keys_1; eauto.
Qed.

Lemma find_H_exists_update_preserved :
  forall heap k k_update v_update,
    find_H k heap <> None ->
    find_H k (update_H (k_update, v_update) heap) <> None.
Proof.
  intros heap k k_update v_update HExists HNone.
  unfold find_H, update_H in *.
  apply lookup_insert_None in HNone.
  destruct HNone as [HOldNone _].
  apply HExists.
  exact HOldNone.
Qed.

Lemma find_H_exists_update_reflected_ne :
  forall heap k k_update v_update,
    k <> k_update ->
    find_H k (update_H (k_update, v_update) heap) <> None ->
    find_H k heap <> None.
Proof.
  intros heap k k_update v_update HNe HExists HNone.
  apply HExists.
  unfold find_H, update_H in *.
  apply lookup_insert_None.
  split.
  - exact HNone.
  - intro HEq. apply HNe. symmetry. exact HEq.
Qed.

Lemma read_safe_preserved_by_disjoint_alloc :
  forall heap r1 l1 v1 r2 l2 v2,
    find_H (r1, l1) heap = Some v1 ->
    Disjoint_Dynamic (DA_Read r1 l1 v1) (DA_Alloc r2 l2 v2) ->
    find_H (r1, l1) (update_H ((r2, l2), v2) heap) = Some v1.
Proof.
  intros heap r1 l1 v1 r2 l2 v2 HFind HDynamic.
  inversion HDynamic; subst.
  apply find_H_some_update_ne; assumption.
Qed.

Lemma read_safe_reflected_by_disjoint_alloc :
  forall heap r1 l1 v1 r2 l2 v2,
    find_H (r1, l1) (update_H ((r2, l2), v2) heap) = Some v1 ->
    Disjoint_Dynamic (DA_Read r1 l1 v1) (DA_Alloc r2 l2 v2) ->
    find_H (r1, l1) heap = Some v1.
Proof.
  intros heap r1 l1 v1 r2 l2 v2 HFind HDynamic.
  inversion HDynamic; subst.
  apply find_H_some_update_ne_reflect with (k_update := (r2, l2)) (v_update := v2);
    assumption.
Qed.

Lemma read_safe_preserved_by_disjoint_write :
  forall heap r1 l1 v1 r2 l2 v2,
    find_H (r1, l1) heap = Some v1 ->
    Disjoint_Dynamic (DA_Read r1 l1 v1) (DA_Write r2 l2 v2) ->
    find_H (r1, l1) (update_H ((r2, l2), v2) heap) = Some v1.
Proof.
  intros heap r1 l1 v1 r2 l2 v2 HFind HDynamic.
  inversion HDynamic; subst.
  apply find_H_some_update_ne; assumption.
Qed.

Lemma read_safe_reflected_by_disjoint_write :
  forall heap r1 l1 v1 r2 l2 v2,
    find_H (r1, l1) (update_H ((r2, l2), v2) heap) = Some v1 ->
    Disjoint_Dynamic (DA_Read r1 l1 v1) (DA_Write r2 l2 v2) ->
    find_H (r1, l1) heap = Some v1.
Proof.
  intros heap r1 l1 v1 r2 l2 v2 HFind HDynamic.
  inversion HDynamic; subst.
  apply find_H_some_update_ne_reflect with (k_update := (r2, l2)) (v_update := v2);
    assumption.
Qed.

Definition LabelAllocReflectionStable (label other_label : Label) : Prop :=
  match label, other_label with
  | Act (DA_Alloc r1 _ _), Act (DA_Alloc r2 _ _) => r2 <> r1
  | _, _ => True
  end.

Lemma DA_alloc_in_theta_alloc_abs :
  forall r l v acts,
    DA_in_Theta (DA_Alloc r l v) (Some acts) ->
    set_elem acts (CA_AllocAbs r).
Proof.
  intros r l v acts HIn.
  dependent induction HIn; try discriminate; try solve [inversion x].
  - assumption.
  - unfold set_elem, set_union.
    apply Union_introl. eapply IHHIn; reflexivity.
  - unfold set_elem, set_union.
    apply Union_intror. eapply IHHIn; reflexivity.
Qed.

Lemma LabelAllocReflectionStable_from_theta :
  forall label_left label_right theta_left theta_right,
    label_phi label_left ⋞ theta_left ->
    label_phi label_right ⋞ theta_right ->
    Disjointness theta_left theta_right ->
    LabelAllocReflectionStable label_right label_left.
Proof.
  intros label_left label_right theta_left theta_right
    HSoundLeft HSoundRight HDisjoint.
  destruct label_right as [| da_right]; [exact I |].
  destruct label_left as [| da_left]; [destruct da_right; exact I |].
  destruct da_right as [rR lR vR | rR lR vR | rR lR vR];
    destruct da_left as [rL lL vL | rL lL vL | rL lL vL];
    simpl; try exact I.
  inversion HDisjoint as [acts_left acts_right HDisjointSets]; subst.
  assert (HLeftIn :
    DA_in_Theta (DA_Alloc rL lL vL) (Some acts_left)).
  {
    eapply Phi_Theta_Soundness_da_in; eauto.
    constructor.
  }
  assert (HRightIn :
    DA_in_Theta (DA_Alloc rR lR vR) (Some acts_right)).
  {
    eapply Phi_Theta_Soundness_da_in; eauto.
    constructor.
  }
  pose proof
    (DA_alloc_in_theta_alloc_abs rL lL vL acts_left HLeftIn)
    as HLeftAlloc.
  pose proof
    (DA_alloc_in_theta_alloc_abs rR lR vR acts_right HRightIn)
    as HRightAlloc.
  inversion HDisjointSets as [acts1 acts2 HAll]; subst.
  pose proof
    (HAll (CA_AllocAbs rL) (CA_AllocAbs rR)
      HLeftAlloc HRightAlloc)
    as HComputedDisjoint.
  inversion HComputedDisjoint; subst.
  exact H1.
Qed.

Lemma Step_state_heap_label_result :
  forall state label state',
    Step state label state' ->
    state_heap state' = label_result_heap label (state_heap state).
Proof.
  intros state label state' HStep.
  induction HStep; simpl; try reflexivity.
  - exact IHHStep.
  - rewrite state_heap_with_state_heap. rewrite H. exact IHHStep.
Qed.

Definition PhiReadsSafe (heap : Heap) (phi : Phi) : Prop :=
  forall r l v,
    DA_in_Phi (DA_Read r l v) phi ->
    find_H (r, l) heap = Some v.

Lemma ReadOnlyPhi_reads_safe_replay :
  forall phi heap,
    ReadOnlyPhi phi ->
    PhiReadsSafe heap phi ->
    (phi, heap) ==>* (Phi_Nil, heap).
Proof.
  intros phi heap HReadOnly.
  induction HReadOnly as
    [| r l v
    | phi1 phi2 HReadOnly1 IH1 HReadOnly2 IH2
    | phi1 phi2 HReadOnly1 IH1 HReadOnly2 IH2];
    intros HSafe.
  - exists 0. constructor.
  - exists 1. constructor.
    constructor.
    unfold PhiReadsSafe in HSafe.
    apply HSafe.
    constructor.
  - eapply structured_phi_seq_steps with (heap' := heap).
    + apply IH1.
      unfold PhiReadsSafe in *.
      intros r l v HIn.
      apply HSafe.
      apply DAP_Seq. now left.
    + apply IH2.
      unfold PhiReadsSafe in *.
      intros r l v HIn.
      apply HSafe.
      apply DAP_Seq. now right.
  - eapply structured_phi_par_steps with (heap' := heap).
    + apply IH1.
      unfold PhiReadsSafe in *.
      intros r l v HIn.
      apply HSafe.
      apply DAP_Par. now left.
    + apply IH2.
      unfold PhiReadsSafe in *.
      intros r l v HIn.
      apply HSafe.
      apply DAP_Par. now right.
Qed.

Lemma Step_readonly_label_preserves_heap :
  forall state label state',
    Step state label state' ->
    ReadOnlyPhi (label_phi label) ->
    state_heap state' = state_heap state.
Proof.
  intros state label state' HStep HReadOnly.
  rewrite (Step_state_heap_label_result _ _ _ HStep).
  destruct label as [| [r l v | r l v | r l v]]; simpl in *;
    try reflexivity; inversion HReadOnly.
Qed.

Lemma StepsPhi_readonly_reads_safe :
  forall state phi state',
    StepsPhi state phi state' ->
    ReadOnlyPhi phi ->
    PhiReadsSafe (state_heap state) phi.
Proof.
  intros state phi state' HSteps.
  induction HSteps as
    [state
    | state label state_mid phi_tail state_final HStep _ IH];
    intros HReadOnly.
  - unfold PhiReadsSafe.
    intros r l v HIn.
    inversion HIn.
  - inversion HReadOnly as
      [| | phi_label phi_tail' HReadOnlyLabel HReadOnlyTail |];
      subst.
    unfold PhiReadsSafe.
    intros r l v HIn.
    inversion HIn as
      [| | da phi_label' phi_tail'' [HInLabel | HInTail]];
      subst.
    + destruct label as [| [r_alloc l_alloc v_alloc
                          | r_read l_read v_read
                          | r_write l_write v_write]];
        simpl in HInLabel; inversion HInLabel; subst;
        simpl in HReadOnlyLabel; try inversion HReadOnlyLabel.
      pose proof (Step_label_heap_safe _ _ _ HStep) as HSafe.
      simpl in HSafe.
      exact HSafe.
    + pose proof (IH HReadOnlyTail) as HTailSafe.
      unfold PhiReadsSafe in HTailSafe.
      pose proof
        (Step_readonly_label_preserves_heap
          state label state_mid HStep HReadOnlyLabel)
        as HHeap.
      rewrite <- HHeap.
      apply HTailSafe.
      exact HInTail.
Qed.

Lemma PhiReadsSafe_seq_inv_l :
  forall heap phi1 phi2,
    PhiReadsSafe heap (Phi_Seq phi1 phi2) ->
    PhiReadsSafe heap phi1.
Proof.
  unfold PhiReadsSafe.
  intros heap phi1 phi2 HSafe r l v HRead.
  apply HSafe.
  apply DAP_Seq.
  now left.
Qed.

Lemma PhiReadsSafe_seq_inv_r :
  forall heap phi1 phi2,
    PhiReadsSafe heap (Phi_Seq phi1 phi2) ->
    PhiReadsSafe heap phi2.
Proof.
  unfold PhiReadsSafe.
  intros heap phi1 phi2 HSafe r l v HRead.
  apply HSafe.
  apply DAP_Seq.
  now right.
Qed.

Lemma label_result_heap_readonly :
  forall label heap,
    ReadOnlyPhi (label_phi label) ->
    label_result_heap label heap = heap.
Proof.
  intros label heap HReadOnly.
  destruct label as [| [r l v | r l v | r l v]];
    simpl in *; try reflexivity; inversion HReadOnly.
Qed.

Lemma LabelHeapSafe_of_readonly_label_reads_safe :
  forall label heap phi_tail,
    ReadOnlyPhi (label_phi label) ->
    PhiReadsSafe heap (Phi_Seq (label_phi label) phi_tail) ->
    LabelHeapSafe label heap.
Proof.
  intros label heap phi_tail HReadOnly HSafe.
  destruct label as [| [r l v | r l v | r l v]];
    simpl in *; try exact I; try inversion HReadOnly.
  unfold PhiReadsSafe in HSafe.
  apply HSafe.
  apply DAP_Seq.
  left.
  constructor.
Qed.

Theorem StepsPhi_readonly_rebase_agree :
  forall state phi state' heap,
    StepsPhi state phi state' ->
    StateRunHeapsAgree state ->
    ReadOnlyPhi phi ->
    PhiReadsSafe heap phi ->
    StepsPhi
      (with_state_heap heap state)
      phi
      (with_state_heap heap state').
Proof.
  intros state phi state' heap HSteps.
  revert heap.
  induction HSteps as
    [state
    | state label state_mid phi_tail state_final HStep _ IH];
    intros heap HAgree HReadOnly HSafe.
  - constructor.
  - inversion HReadOnly as
      [| | phi_label phi_tail' HReadOnlyLabel HReadOnlyTail |];
      subst.
    pose proof
      (LabelHeapSafe_of_readonly_label_reads_safe
        label heap phi_tail HReadOnlyLabel HSafe)
      as HLabelSafe.
    pose proof
      (Step_rebase_with_safe_label_agree
        state label state_mid heap HAgree HStep HLabelSafe)
      as HStepRebased.
    rewrite
      (label_result_heap_readonly label heap HReadOnlyLabel)
      in HStepRebased.
    eapply StepsPhi_Step.
    + exact HStepRebased.
    + eapply IH.
      * eapply step_preserves_state_run_heaps_agree; eauto.
      * exact HReadOnlyTail.
      * eapply PhiReadsSafe_seq_inv_r; eauto.
Qed.

Lemma Step_preserves_phi_reads_safe :
  forall state label state' phi,
    Step state label state' ->
    PhiWritesDisjointPhiReads (label_phi label) phi ->
    PhiReadsSafe (state_heap state) phi ->
    PhiReadsSafe (state_heap state') phi.
Proof.
  intros state label state' phi HStep HDisjoint HSafe.
  unfold PhiReadsSafe in *.
  intros r l v HRead.
  rewrite (Step_state_heap_label_result _ _ _ HStep).
  destruct label as [| [r_alloc l_alloc v_alloc
                      | r_read l_read v_read
                      | r_write l_write v_write]];
    simpl.
  - apply HSafe. exact HRead.
  - destruct (decide ((r, l) = (r_alloc, l_alloc))) as [HSame | HNe].
    + inversion HSame; subst.
      pose proof (Step_label_heap_safe _ _ _ HStep) as HLabelSafe.
      simpl in HLabelSafe.
      pose proof (HSafe r_alloc l_alloc v HRead) as HFind.
      rewrite <- HLabelSafe in HFind.
      rewrite allocate_H_fresh in HFind.
      discriminate.
    + apply find_H_some_update_ne; [exact HNe |].
      apply HSafe. exact HRead.
  - apply HSafe. exact HRead.
  - assert (HNe : (r, l) <> (r_write, l_write)).
    {
      intro HSame.
      apply
        (HDisjoint r_write l_write v_write r l v).
      - simpl. constructor.
      - exact HRead.
      - symmetry. exact HSame.
    }
    apply find_H_some_update_ne; [exact HNe |].
    apply HSafe. exact HRead.
Qed.

Theorem Step_preserves_readonly_phi_replay :
  forall state label state' phi,
    Step state label state' ->
    ReadOnlyPhi phi ->
    PhiWritesDisjointPhiReads (label_phi label) phi ->
    PhiReadsSafe (state_heap state) phi ->
    (phi, state_heap state') ==>* (Phi_Nil, state_heap state').
Proof.
  intros state label state' phi HStep HReadOnly HDisjoint HSafe.
  apply ReadOnlyPhi_reads_safe_replay.
  - exact HReadOnly.
  - eapply Step_preserves_phi_reads_safe; eauto.
Qed.

Theorem Step_preserves_readonly_stepsphi_replay :
  forall state label state' summary_state phi summary_final,
    Step state label state' ->
    StepsPhi summary_state phi summary_final ->
    state_heap summary_state = state_heap state ->
    ReadOnlyPhi phi ->
    PhiWritesDisjointPhiReads (label_phi label) phi ->
    (phi, state_heap state') ==>* (Phi_Nil, state_heap state').
Proof.
  intros state label state' summary_state phi summary_final
    HStep HSummarySteps HHeap HReadOnly HDisjoint.
  eapply Step_preserves_readonly_phi_replay; eauto.
  rewrite <- HHeap.
  eapply StepsPhi_readonly_reads_safe; eauto.
Qed.

Lemma PhiWritesDisjointPhiReads_seq_inv_l :
  forall phi1 phi2 phi_read,
    PhiWritesDisjointPhiReads (Phi_Seq phi1 phi2) phi_read ->
    PhiWritesDisjointPhiReads phi1 phi_read.
Proof.
  unfold PhiWritesDisjointPhiReads.
  intros phi1 phi2 phi_read HDisjoint
    r_write l_write v_write r_read l_read v_read HWrite HRead.
  eapply HDisjoint; eauto.
  apply DAP_Seq.
  left.
  exact HWrite.
Qed.

Lemma PhiWritesDisjointPhiReads_seq_inv_r :
  forall phi1 phi2 phi_read,
    PhiWritesDisjointPhiReads (Phi_Seq phi1 phi2) phi_read ->
    PhiWritesDisjointPhiReads phi2 phi_read.
Proof.
  unfold PhiWritesDisjointPhiReads.
  intros phi1 phi2 phi_read HDisjoint
    r_write l_write v_write r_read l_read v_read HWrite HRead.
  eapply HDisjoint; eauto.
  apply DAP_Seq.
  right.
  exact HWrite.
Qed.

Lemma StepsPhi_preserves_phi_reads_safe :
  forall state phi_write state' phi_read,
    StepsPhi state phi_write state' ->
    PhiWritesDisjointPhiReads phi_write phi_read ->
    PhiReadsSafe (state_heap state) phi_read ->
    PhiReadsSafe (state_heap state') phi_read.
Proof.
  intros state phi_write state' phi_read HSteps.
  induction HSteps as
    [state
    | state label state_mid phi_tail state_final HStep _ IH];
    intros HDisjoint HSafe.
  - exact HSafe.
  - eapply IH.
    + eapply PhiWritesDisjointPhiReads_seq_inv_r; eauto.
    + eapply Step_preserves_phi_reads_safe; eauto.
      eapply PhiWritesDisjointPhiReads_seq_inv_l; eauto.
Qed.

Theorem StepsPhi_preserves_readonly_phi_replay :
  forall state phi_write state' summary_state phi_read summary_final,
    StepsPhi state phi_write state' ->
    PhiWritesDisjointPhiReads phi_write phi_read ->
    StepsPhi summary_state phi_read summary_final ->
    state_heap summary_state = state_heap state ->
    ReadOnlyPhi phi_read ->
    (phi_read, state_heap state') ==>* (Phi_Nil, state_heap state').
Proof.
  intros state phi_write state' summary_state phi_read summary_final
    HWriteSteps HDisjoint HSummarySteps HHeap HReadOnly.
  apply ReadOnlyPhi_reads_safe_replay.
  - exact HReadOnly.
  - eapply StepsPhi_preserves_phi_reads_safe; eauto.
    rewrite <- HHeap.
    eapply StepsPhi_readonly_reads_safe; eauto.
Qed.

Theorem StepsPhi_preserves_readonly_phi_replay_from_theta :
  forall state phi_write state' theta_write
    summary_state phi_read summary_final,
    StepsPhi state phi_write state' ->
    phi_write ⋞ theta_write ->
    ThetaWritesDisjointPhiReads theta_write phi_read ->
    StepsPhi summary_state phi_read summary_final ->
    state_heap summary_state = state_heap state ->
    ReadOnlyPhi phi_read ->
    (phi_read, state_heap state') ==>* (Phi_Nil, state_heap state').
Proof.
  intros state phi_write state' theta_write
    summary_state phi_read summary_final
    HWriteSteps HSound HThetaReads HSummarySteps HHeap HReadOnly.
  eapply StepsPhi_preserves_readonly_phi_replay; eauto.
  eapply Phi_Theta_Soundness_writes_disjoint_phi_reads; eauto.
Qed.

Lemma LabelHeapSafe_preserved_by_disjoint_step_any :
  forall label other other_label other',
    Step other other_label other' ->
    LabelHeapSafe label (state_heap other) ->
    Disjoint_Traces (label_trace label) (label_trace other_label) ->
    LabelHeapSafe label (state_heap other').
Proof.
  intros label other other_label other' HStep HSafe HDisjoint.
  rewrite (Step_state_heap_label_result _ _ _ HStep).
  destruct label as [| da].
  - exact I.
  - destruct other_label as [| da_other].
    + exact HSafe.
    + pose proof (Disjoint_Traces_single_inv da da_other HDisjoint)
        as HDynamic.
      pose proof (Step_label_heap_safe _ _ _ HStep) as HOtherSafe.
      pose proof HSafe as HSafe0.
      destruct da_other as [rO lO vO | rO lO vO | rO lO vO].
      * destruct da as [rA lA vA | rA lA vA | rA lA vA]; simpl in *.
        -- eapply LabelHeapSafe_alloc_preserved_by_alloc; eauto.
        -- eapply read_safe_preserved_by_disjoint_alloc; eauto.
        -- apply find_H_exists_update_preserved.
           exact HSafe0.
      * exact HSafe0.
      * destruct da as [rA lA vA | rA lA vA | rA lA vA]; simpl in *.
        -- rewrite allocate_H_update_existing_nonnone.
           ++ exact HSafe0.
           ++ exact HOtherSafe.
        -- eapply read_safe_preserved_by_disjoint_write; eauto.
        -- apply find_H_exists_update_preserved.
           exact HSafe0.
Qed.

Lemma LabelHeapSafe_preserved_by_disjoint_step :
  forall label other other_label other',
    Step other other_label other' ->
    NonPairParRunState other ->
    LabelHeapSafe label (state_heap other) ->
    Disjoint_Traces (label_trace label) (label_trace other_label) ->
    LabelHeapSafe label (state_heap other').
Proof.
  intros label other other_label other' HStep _ HSafe HDisjoint.
  eapply LabelHeapSafe_preserved_by_disjoint_step_any; eauto.
Qed.

Lemma LabelHeapSafe_reflected_by_disjoint_step_any :
  forall label other other_label other',
    Step other other_label other' ->
    LabelAllocReflectionStable label other_label ->
    LabelHeapSafe label (state_heap other') ->
    Disjoint_Traces (label_trace label) (label_trace other_label) ->
    LabelHeapSafe label (state_heap other).
Proof.
  intros label other other_label other' HStep HStable HSafe HDisjoint.
  destruct label as [| da].
  - exact I.
  - destruct other_label as [| da_other].
    + pose proof (Step_silent_preserves_heap _ _ HStep) as HHeap.
      simpl in *. now rewrite <- HHeap.
    + pose proof (Disjoint_Traces_single_inv da da_other HDisjoint)
        as HDynamic.
      pose proof HSafe as HSafe0.
      pose proof (Step_state_heap_label_result _ _ _ HStep) as HHeapResult.
      pose proof (Step_label_heap_safe _ _ _ HStep) as HOtherSafe.
      destruct da_other as [rO lO vO | rO lO vO | rO lO vO].
      * simpl in HHeapResult, HOtherSafe.
        rewrite HHeapResult in HSafe0.
        simpl in HSafe0.
        destruct da as [rA lA vA | rA lA vA | rA lA vA]; simpl in *.
        -- rewrite <- (allocate_H_update_fresh_different_region
             (state_heap other) rA rO lO vO).
           ++ exact HSafe0.
           ++ exact HStable.
           ++ rewrite <- HOtherSafe. apply allocate_H_fresh.
        -- eapply read_safe_reflected_by_disjoint_alloc; eauto.
        -- inversion HDynamic; subst.
           eapply find_H_exists_update_reflected_ne; eauto.
      * simpl in HHeapResult.
        rewrite HHeapResult in HSafe0.
        exact HSafe0.
      * simpl in HHeapResult, HOtherSafe.
        rewrite HHeapResult in HSafe0.
        simpl in HSafe0.
        destruct da as [rA lA vA | rA lA vA | rA lA vA]; simpl in *.
        -- rewrite allocate_H_update_existing_nonnone in HSafe0.
           ++ exact HSafe0.
           ++ exact HOtherSafe.
        -- eapply read_safe_reflected_by_disjoint_write; eauto.
        -- inversion HDynamic; subst.
           eapply find_H_exists_update_reflected_ne; eauto.
Qed.

Lemma LabelHeapSafe_reflected_by_disjoint_step :
  forall label other other_label other',
    Step other other_label other' ->
    NonPairParRunState other ->
    LabelAllocReflectionStable label other_label ->
    LabelHeapSafe label (state_heap other') ->
    Disjoint_Traces (label_trace label) (label_trace other_label) ->
    LabelHeapSafe label (state_heap other).
Proof.
  intros label other other_label other' HStep _ HStable HSafe HDisjoint.
  eapply LabelHeapSafe_reflected_by_disjoint_step_any; eauto.
Qed.

Ltac solve_label_update_commute :=
  unfold update_H; simpl;
  apply insert_commute;
  match goal with
  | HNeq : ?k1 <> ?k2 |- ?k1 <> ?k2 =>
      exact HNeq
  | HNeq : ?k1 <> ?k2 |- ?k2 <> ?k1 =>
      let HSame := fresh "HSame" in
      intro HSame; apply HNeq; symmetry; exact HSame
  end.

Lemma label_result_heap_commute_disjoint :
  forall label1 label2 heap,
    Disjoint_Traces (label_trace label1) (label_trace label2) ->
    label_result_heap label2 (label_result_heap label1 heap) ≡@{Heap}
    label_result_heap label1 (label_result_heap label2 heap).
Proof.
  intros label1 label2 heap HDisjoint.
  destruct label1 as [| da1]; destruct label2 as [| da2];
    simpl in *; try reflexivity.
  pose proof (Disjoint_Traces_single_inv da1 da2 HDisjoint) as HDynamic.
  destruct da1 as [r1 l1 v1 | r1 l1 v1 | r1 l1 v1];
    destruct da2 as [r2 l2 v2 | r2 l2 v2 | r2 l2 v2];
    simpl in *; try reflexivity;
    inversion HDynamic; subst; solve_label_update_commute.
Qed.

Ltac solve_label_update_commute_eq :=
  unfold update_H; simpl;
  apply insert_commute;
  match goal with
  | HNeq : ?k1 <> ?k2 |- ?k1 <> ?k2 =>
      exact HNeq
  | HNeq : ?k1 <> ?k2 |- ?k2 <> ?k1 =>
      let HSame := fresh "HSame" in
      intro HSame; apply HNeq; symmetry; exact HSame
  end.

Lemma label_result_heap_commute_disjoint_eq :
  forall label1 label2 heap,
    Disjoint_Traces (label_trace label1) (label_trace label2) ->
    label_result_heap label2 (label_result_heap label1 heap) =
    label_result_heap label1 (label_result_heap label2 heap).
Proof.
  intros label1 label2 heap HDisjoint.
  destruct label1 as [| da1]; destruct label2 as [| da2];
    simpl in *; try reflexivity.
  pose proof (Disjoint_Traces_single_inv da1 da2 HDisjoint) as HDynamic.
  destruct da1 as [r1 l1 v1 | r1 l1 v1 | r1 l1 v1];
    destruct da2 as [r2 l2 v2 | r2 l2 v2 | r2 l2 v2];
    simpl in *; try reflexivity;
    inversion HDynamic; subst; solve_label_update_commute_eq.
Qed.

Lemma Step_rebase_after_disjoint_step :
  forall state label state' other other_label other',
    state_heap state = state_heap other ->
    NonPairParRunState state ->
    NonPairParRunState other ->
    Step state label state' ->
    Step other other_label other' ->
    Disjoint_Traces (label_trace label) (label_trace other_label) ->
    Step
      (with_state_heap (state_heap other') state)
      label
      (with_state_heap (label_result_heap label (state_heap other')) state').
Proof.
  intros state label state' other other_label other'
    HHeapAgree HNonPair HNonPairOther HStepState HStepOther HDisjoint.
  eapply Step_rebase_with_safe_label.
  - exact HNonPair.
  - exact HStepState.
  - eapply LabelHeapSafe_preserved_by_disjoint_step; eauto.
    rewrite <- HHeapAgree.
    eapply Step_label_heap_safe; eauto.
Qed.

Lemma PairParLeftRightStep_local_diamond :
  forall left right k label_left label_right left' right',
    state_heap left = state_heap right ->
    NonPairParRunState left ->
    NonPairParRunState right ->
    Step left label_left left' ->
    Step right label_right right' ->
    Disjoint_Traces (label_trace label_left) (label_trace label_right) ->
    Disjoint_Traces (label_trace label_right) (label_trace label_left) ->
    exists state_after,
      PairParStep
        (PPS_Run left' (with_state_heap (state_heap left') right) k)
        label_right
        state_after /\
      PairParStep
        (PPS_Run (with_state_heap (state_heap right') left) right' k)
        label_left
        state_after.
Proof.
  intros left right k label_left label_right left' right'
    HHeapAgree HNonPairLeft HNonPairRight
    HStepLeft HStepRight HDisjointLR HDisjointRL.
  set (heap_after :=
    label_result_heap label_right
      (label_result_heap label_left (state_heap left))).
  set (state_after :=
    PPS_Run
      (with_state_heap heap_after left')
      (with_state_heap heap_after right')
      k).
  exists state_after.
  split.
  - subst state_after.
    replace (with_state_heap heap_after left') with
      (with_state_heap
        (state_heap (with_state_heap heap_after right')) left')
      by (rewrite state_heap_with_state_heap; reflexivity).
    apply PPStep_Right.
    subst heap_after.
    rewrite <- (Step_state_heap_label_result _ _ _ HStepLeft).
    eapply (Step_rebase_after_disjoint_step
      right label_right right' left label_left left').
    + symmetry. exact HHeapAgree.
    + exact HNonPairRight.
    + exact HNonPairLeft.
    + exact HStepRight.
    + exact HStepLeft.
    + exact HDisjointRL.
  - subst state_after.
    replace (with_state_heap heap_after right') with
      (with_state_heap
        (state_heap (with_state_heap heap_after left')) right')
      by (rewrite state_heap_with_state_heap; reflexivity).
    apply PPStep_Left.
    subst heap_after.
    rewrite (label_result_heap_commute_disjoint_eq
      label_left label_right (state_heap left) HDisjointLR).
    rewrite HHeapAgree.
    rewrite <- (Step_state_heap_label_result _ _ _ HStepRight).
    eapply (Step_rebase_after_disjoint_step
      left label_left left' right label_right right').
    + exact HHeapAgree.
    + exact HNonPairLeft.
    + exact HNonPairRight.
    + exact HStepLeft.
    + exact HStepRight.
    + exact HDisjointLR.
Qed.

Lemma PairParLeftRightActualStep_local_diamond :
  forall left right label_left label_right left' right_after,
    state_heap left = state_heap right ->
    NonPairParRunState left ->
    NonPairParRunState right ->
    NonPairParRunState right_after ->
    Step left label_left left' ->
    Step (with_state_heap (state_heap left') right) label_right right_after ->
    LabelAllocReflectionStable label_right label_left ->
    Disjoint_Traces (label_trace label_left) (label_trace label_right) ->
    Disjoint_Traces (label_trace label_right) (label_trace label_left) ->
    exists right',
      Step right label_right right' /\
      Step
        (with_state_heap (state_heap right') left)
        label_left
        (with_state_heap (state_heap right_after) left') /\
      right_after = with_state_heap (state_heap right_after) right' /\
      NonPairParRunState right'.
Proof.
  intros left right label_left label_right left' right_after
    HHeapAgree HNonPairLeft HNonPairRight HNonPairRightAfter
    HStepLeft HStepRightAfter HStable HDisjointLR HDisjointRL.
  pose proof
    (Step_label_heap_safe _ _ _ HStepRightAfter)
    as HSafeAfter.
  rewrite state_heap_with_state_heap in HSafeAfter.
  pose proof
    (LabelHeapSafe_reflected_by_disjoint_step
      label_right left label_left left'
      HStepLeft HNonPairLeft HStable HSafeAfter HDisjointRL)
    as HSafeBefore.
  set (right' :=
    with_state_heap
      (label_result_heap label_right (state_heap right))
      right_after).
  assert (HStepRight : Step right label_right right').
  {
    subst right'.
    eapply Step_unbase_with_safe_label.
    - exact HNonPairRight.
    - exact HStepRightAfter.
    - rewrite <- HHeapAgree. exact HSafeBefore.
  }
  exists right'.
  split; [exact HStepRight |].
  split.
  - replace (state_heap right_after) with
      (label_result_heap label_left (state_heap right')).
    + eapply (Step_rebase_after_disjoint_step
        left label_left left' right label_right right').
      * exact HHeapAgree.
      * exact HNonPairLeft.
      * exact HNonPairRight.
      * exact HStepLeft.
      * exact HStepRight.
      * exact HDisjointLR.
    + rewrite (Step_state_heap_label_result _ _ _ HStepRightAfter).
	      rewrite (Step_state_heap_label_result _ _ _ HStepLeft).
	      rewrite (Step_state_heap_label_result _ _ _ HStepRight).
	      rewrite HHeapAgree.
	      rewrite state_heap_with_state_heap.
	      symmetry.
	      apply label_result_heap_commute_disjoint_eq.
      exact HDisjointLR.
		  - split.
		    + subst right'.
		      assert (HOverwrite :
		        forall state heap_inner,
		          with_state_heap (state_heap right_after)
		            (with_state_heap heap_inner state) =
		          with_state_heap (state_heap right_after) state).
		      {
		        intros state heap_inner.
		        induction state; simpl; auto.
		        now rewrite IHstate1, IHstate2.
		      }
		      rewrite HOverwrite.
		      rewrite with_state_heap_state_heap_agree.
		      * reflexivity.
		      * eapply step_preserves_state_run_heaps_agree.
		        -- apply StateRunHeapsAgree_with_state_heap.
		           apply NonPairParRunState_run_heaps_agree.
		           exact HNonPairRight.
		        -- exact HStepRightAfter.
		    + subst right'.
		      apply with_state_heap_non_pairpar.
		      exact HNonPairRightAfter.
Qed.

Lemma PairParStepsPhi_LeftRight_adjacent_swap :
  forall left right k label_left label_right left' right_after
    phi_state phi_left phi_right final_state,
    state_heap left = state_heap right ->
    NonPairParRunState left ->
    NonPairParRunState right ->
    NonPairParRunState left' ->
    NonPairParRunState right_after ->
    Step left label_left left' ->
    Step (with_state_heap (state_heap left') right) label_right right_after ->
    LabelAllocReflectionStable label_right label_left ->
    Disjoint_Traces (label_trace label_left) (label_trace label_right) ->
    Disjoint_Traces (label_trace label_right) (label_trace label_left) ->
    PairParStepsPhi
      (PPS_Run (with_state_heap (state_heap right_after) left') right_after k)
      phi_state phi_left phi_right final_state ->
    PairParStepsPhi
      (PPS_Run left right k)
      phi_state
      (Phi_Seq (label_phi label_left) phi_left)
      (Phi_Seq (label_phi label_right) phi_right)
      final_state.
Proof.
  intros left right k label_left label_right left' right_after
    phi_state phi_left phi_right final_state
    HHeapAgree HNonPairLeft HNonPairRight
    HNonPairLeft' HNonPairRightAfter
    HStepLeft HStepRightAfter HStable HDisjointLR HDisjointRL
    HRest.
  destruct
    (PairParLeftRightActualStep_local_diamond
      left right label_left label_right left' right_after
      HHeapAgree HNonPairLeft HNonPairRight HNonPairRightAfter
      HStepLeft HStepRightAfter HStable HDisjointLR HDisjointRL)
    as (right' & HStepRight & HStepLeftAfterRight &
        HRightAfterRebase & HNonPairRight').
	  eapply PairParStepsPhi_Right.
	  - exact HNonPairRight.
	  - exact HNonPairRight'.
	  - exact HStepRight.
	  - eapply PairParStepsPhi_Left.
	    + apply with_state_heap_non_pairpar. exact HNonPairLeft.
	    + apply with_state_heap_non_pairpar. exact HNonPairLeft'.
	    + exact HStepLeftAfterRight.
    + replace
        (PPS_Run (with_state_heap (state_heap right_after) left')
           (with_state_heap
             (state_heap (with_state_heap (state_heap right_after) left'))
             right') k)
        with
        (PPS_Run (with_state_heap (state_heap right_after) left')
           right_after k).
	      * exact HRest.
	      * rewrite state_heap_with_state_heap.
	        rewrite <- HRightAfterRebase.
	        reflexivity.
Qed.

Lemma PairParStepsPhi_LeftRight_adjacent_swap_checked :
  forall left right k label_left label_right left' right_after
    phi_state phi_left phi_right final_state theta_left theta_right,
    state_heap left = state_heap right ->
    NonPairParRunState left ->
    NonPairParRunState right ->
    NonPairParRunState left' ->
    NonPairParRunState right_after ->
    Step left label_left left' ->
    Step (with_state_heap (state_heap left') right) label_right right_after ->
    label_phi label_left ⋞ theta_left ->
    label_phi label_right ⋞ theta_right ->
    PairParCheckPass theta_left theta_right ->
    PairParStepsPhi
      (PPS_Run (with_state_heap (state_heap right_after) left') right_after k)
      phi_state phi_left phi_right final_state ->
    PairParStepsPhi
      (PPS_Run left right k)
      phi_state
      (Phi_Seq (label_phi label_left) phi_left)
      (Phi_Seq (label_phi label_right) phi_right)
      final_state.
Proof.
  intros left right k label_left label_right left' right_after
    phi_state phi_left phi_right final_state theta_left theta_right
    HHeapAgree HNonPairLeft HNonPairRight
    HNonPairLeft' HNonPairRightAfter HStepLeft HStepRightAfter
    HSoundLeft HSoundRight HPass HRest.
  eapply PairParStepsPhi_LeftRight_adjacent_swap.
  - exact HHeapAgree.
  - exact HNonPairLeft.
  - exact HNonPairRight.
  - exact HNonPairLeft'.
  - exact HNonPairRightAfter.
  - exact HStepLeft.
  - exact HStepRightAfter.
  - eapply LabelAllocReflectionStable_from_theta; eauto.
    destruct HPass as [HDisjoint _]. exact HDisjoint.
  - rewrite <- (phi_as_list_label_phi label_left).
    rewrite <- (phi_as_list_label_phi label_right).
    eapply PairParCheckPass_sound_disjoint_traces; eauto.
  - rewrite <- (phi_as_list_label_phi label_right).
    rewrite <- (phi_as_list_label_phi label_left).
    eapply PairParCheckPass_sound_disjoint_traces_sym; eauto.
  - exact HRest.
Qed.

Inductive PairParLeftOnlyStepsPhi :
  PairParState -> Phi -> Phi -> PairParState -> Prop :=
| PPLO_Refl :
    forall state,
      PairParLeftOnlyStepsPhi state Phi_Nil Phi_Nil state
| PPLO_State :
    forall state phi_state final_state,
      PairParStepsPhi
        (PPS_State state) phi_state Phi_Nil Phi_Nil final_state ->
      PairParLeftOnlyStepsPhi
        (PPS_State state) phi_state Phi_Nil final_state
| PPLO_Left :
    forall left right k label left' phi_state phi_left final_state,
      NonPairParRunState left ->
      NonPairParRunState left' ->
      Step left label left' ->
      PairParLeftOnlyStepsPhi
        (PPS_Run left' (with_state_heap (state_heap left') right) k)
        phi_state phi_left final_state ->
      PairParLeftOnlyStepsPhi
        (PPS_Run left right k)
        phi_state
        (Phi_Seq (label_phi label) phi_left)
        final_state
| PPLO_Done :
    forall heap v1 v2 k phi_state phi_left final_state,
      PairParLeftOnlyStepsPhi
        (PPS_State (StReturn heap (Pair (v1, v2)) k))
        phi_state phi_left final_state ->
      PairParLeftOnlyStepsPhi
        (PPS_Run (StDone heap v1) (StDone heap v2) k)
        phi_state phi_left final_state.

Inductive PairParRightThenLeftStepsPhi :
  PairParState -> Phi -> Phi -> Phi -> PairParState -> Prop :=
| PPRTL_LeftOnly :
    forall state phi_state phi_left final_state,
      PairParLeftOnlyStepsPhi state phi_state phi_left final_state ->
      PairParRightThenLeftStepsPhi
        state phi_state phi_left Phi_Nil final_state
| PPRTL_Right :
    forall left right k label right'
      phi_state phi_left phi_right final_state,
      NonPairParRunState right ->
      NonPairParRunState right' ->
      Step right label right' ->
      PairParRightThenLeftStepsPhi
        (PPS_Run (with_state_heap (state_heap right') left) right' k)
        phi_state phi_left phi_right final_state ->
      PairParRightThenLeftStepsPhi
        (PPS_Run left right k)
        phi_state
        phi_left
        (Phi_Seq (label_phi label) phi_right)
        final_state.

Lemma PairParLeftOnlyStepsPhi_as_pairpar_steps_phi :
  forall state phi_state phi_left final_state,
    PairParLeftOnlyStepsPhi state phi_state phi_left final_state ->
    PairParStepsPhi state phi_state phi_left Phi_Nil final_state.
Proof.
  intros state phi_state phi_left final_state HSteps.
  induction HSteps.
  - constructor.
  - exact H.
  - eapply PairParStepsPhi_Left; eauto.
  - eapply PairParStepsPhi_Done; eauto.
Qed.

Lemma PairParRightThenLeftStepsPhi_as_pairpar_steps_phi :
  forall state phi_state phi_left phi_right final_state,
    PairParRightThenLeftStepsPhi
      state phi_state phi_left phi_right final_state ->
    PairParStepsPhi state phi_state phi_left phi_right final_state.
Proof.
  intros state phi_state phi_left phi_right final_state HSteps.
  induction HSteps.
  - now apply PairParLeftOnlyStepsPhi_as_pairpar_steps_phi.
  - eapply PairParStepsPhi_Right; eauto.
Qed.

Lemma PairParLeftOnlyStepsPhi_state_as_stepsphi :
  forall state phi_state phi_left final_state,
    PairParLeftOnlyStepsPhi
      (PPS_State state) phi_state phi_left final_state ->
    phi_left = Phi_Nil /\
    exists state_final,
      final_state = PPS_State state_final /\
      StepsPhi state phi_state state_final.
Proof.
  intros state phi_state phi_left final_state HSteps.
  pose proof
    (PairParLeftOnlyStepsPhi_as_pairpar_steps_phi
      (PPS_State state) phi_state phi_left final_state HSteps)
    as HPairSteps.
  destruct
    (PairParStepsPhi_state_as_stepsphi
      state phi_state phi_left Phi_Nil final_state HPairSteps)
    as (HLeftNil & _ & state_final & HFinal & HStepsPhi).
  split; [exact HLeftNil |].
  exists state_final. split; assumption.
Qed.

Lemma StepsPhi_return_kdone :
  forall heap v,
    StepsPhi
      (StReturn heap v KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      (StDone heap v).
Proof.
  intros heap v.
  eapply StepsPhi_Step.
  - constructor.
  - constructor.
Qed.

Inductive OrdinaryStepsPhi : State -> Phi -> State -> Prop :=
| OrdinaryStepsPhi_Refl :
    forall state,
      OrdinaryStepsPhi state Phi_Nil state
| OrdinaryStepsPhi_Step :
    forall state label state' phi state'',
      NonPairParRunState state ->
      NonPairParRunState state' ->
      Step state label state' ->
      OrdinaryStepsPhi state' phi state'' ->
      OrdinaryStepsPhi state (Phi_Seq (label_phi label) phi) state''.

Lemma OrdinaryStepsPhi_as_stepsphi :
  forall state phi state',
    OrdinaryStepsPhi state phi state' ->
    StepsPhi state phi state'.
Proof.
  intros state phi state' HSteps.
  induction HSteps.
  - constructor.
  - econstructor; eauto.
Qed.

Theorem OrdinaryStepsPhi_terminal_deterministic :
  forall state phi1 heap1 v1 phi2 heap2 v2,
    OrdinaryStepsPhi state phi1 (StDone heap1 v1) ->
    OrdinaryStepsPhi state phi2 (StDone heap2 v2) ->
    phi_as_list phi1 = phi_as_list phi2 /\
    heap1 = heap2 /\
    v1 = v2.
Proof.
  intros state phi1 heap1 v1 phi2 heap2 v2 HSteps1.
  revert phi2 heap2 v2.
  dependent induction HSteps1; intros phi2 heap2 v2 HSteps2.
  - inversion HSteps2; subst.
    + split; [reflexivity | split; reflexivity].
    + exfalso. eapply terminal_no_step; eauto. constructor.
  - inversion HSteps2; subst.
    + exfalso. eapply terminal_no_step; eauto. constructor.
    + destruct
        (step_deterministic
          state label state' label0 state'0 H H1 H4)
        as [HLabel HState].
      subst.
      destruct (IHHSteps1 heap1 v1 eq_refl phi0 heap2 v2 H5)
        as (HTrace & HHeap & HVal).
      simpl. repeat rewrite phi_as_list_label_phi.
      split; [now rewrite HTrace | split; assumption].
Qed.

Lemma PairParStepsPhi_state_as_ordinary_stepsphi :
  forall state phi_state phi_left phi_right state',
    PairParStepsPhi
      (PPS_State state) phi_state phi_left phi_right state' ->
    phi_left = Phi_Nil /\
    phi_right = Phi_Nil /\
    exists state_final,
      state' = PPS_State state_final /\
      OrdinaryStepsPhi state phi_state state_final.
Proof.
  intros state phi_state phi_left phi_right state' HSteps.
  dependent induction HSteps.
  - split; [reflexivity |].
    split; [reflexivity |].
    exists state. split; [reflexivity | constructor].
  - destruct (IHHSteps state' eq_refl)
      as (HLeftNil & HRightNil & state_final & HFinal & HStepsPhi).
    split; [exact HLeftNil |].
    split; [exact HRightNil |].
    exists state_final. split; [exact HFinal |].
    econstructor; eauto.
Qed.

Lemma with_state_heap_done_inv :
  forall heap state heap' v,
    with_state_heap heap state = StDone heap' v ->
    exists heap0,
      state = StDone heap0 v /\ heap' = heap.
Proof.
  intros heap state heap' v HDone.
  destruct state; simpl in HDone; inversion HDone; subst.
  eexists. split; reflexivity.
Qed.

Lemma Step_unbase_with_safe_label_agree :
  forall state heap label state',
    StateRunHeapsAgree state ->
    Step (with_state_heap heap state) label state' ->
    LabelHeapSafe label (state_heap state) ->
    Step state label
      (with_state_heap
        (label_result_heap label (state_heap state))
        state').
Proof.
  induction state as
    [heap0 env rho e k
    | heap0 v k
    | heap0 v
    | left_state IHLeft right_state IHRight k];
    intros heap label state' HAgree HStep HSafe; simpl in *.
  - eapply Step_unbase_with_safe_label; eauto.
  - eapply Step_unbase_with_safe_label; eauto.
  - inversion HStep.
  - inversion HStep; subst; simpl in *.
    + destruct HAgree as [HHeapAgree [HLeftAgree HRightAgree]].
      simpl.
      replace
        (with_state_heap (label_result_heap label (state_heap left_state))
          (with_state_heap (state_heap left_state')
            (with_state_heap heap right_state)))
        with
        (with_state_heap
          (state_heap
            (with_state_heap
              (label_result_heap label (state_heap left_state))
              left_state'))
          right_state).
      * apply Step_PairParRun_Left.
        -- exact HHeapAgree.
        -- eapply IHLeft; eauto.
      * rewrite state_heap_with_state_heap.
        repeat rewrite with_state_heap_overwrite.
        reflexivity.
    + destruct HAgree as [HHeapAgree [HLeftAgree HRightAgree]].
      replace (label_result_heap label (state_heap left_state))
        with (label_result_heap label (state_heap right_state))
        by (rewrite HHeapAgree; reflexivity).
      simpl.
      replace
        (with_state_heap (label_result_heap label (state_heap right_state))
          (with_state_heap (state_heap right_state')
            (with_state_heap heap left_state)))
        with
        (with_state_heap
          (state_heap
            (with_state_heap
              (label_result_heap label (state_heap right_state))
              right_state'))
          left_state).
      * apply Step_PairParRun_Right.
        -- exact HHeapAgree.
        -- eapply IHRight; eauto.
           rewrite <- HHeapAgree. exact HSafe.
      * rewrite state_heap_with_state_heap.
        repeat rewrite with_state_heap_overwrite.
        reflexivity.
    + match goal with
      | H : with_state_heap heap left_state = StDone _ _ |- _ =>
          apply with_state_heap_done_inv in H
      | H : StDone _ _ = with_state_heap heap left_state |- _ =>
          symmetry in H; apply with_state_heap_done_inv in H
      end.
      match goal with
      | H : exists heap0, left_state = StDone heap0 _ /\ _ |- _ =>
          destruct H as (? & HLeftDone & HLeftHeap); subst
      end.
      match goal with
      | H : with_state_heap heap right_state = StDone _ _ |- _ =>
          apply with_state_heap_done_inv in H
      | H : StDone _ _ = with_state_heap heap right_state |- _ =>
          symmetry in H; apply with_state_heap_done_inv in H
      end.
      match goal with
      | H : exists heap0, right_state = StDone heap0 _ /\ _ |- _ =>
          destruct H as (? & HRightDone & HRightHeap); subst
      end.
      destruct HAgree as [HHeapAgree _].
      simpl in HHeapAgree. subst.
      constructor.
Qed.

Lemma Step_rebase_after_disjoint_step_agree :
  forall state label state' other other_label other',
    state_heap state = state_heap other ->
    StateRunHeapsAgree state ->
    Step state label state' ->
    Step other other_label other' ->
    Disjoint_Traces (label_trace label) (label_trace other_label) ->
    Step
      (with_state_heap (state_heap other') state)
      label
      (with_state_heap (label_result_heap label (state_heap other')) state').
Proof.
  intros state label state' other other_label other'
    HHeapAgree HStateAgree HStepState HStepOther HDisjoint.
  eapply Step_rebase_with_safe_label_agree.
  - exact HStateAgree.
  - exact HStepState.
  - eapply LabelHeapSafe_preserved_by_disjoint_step_any; eauto.
    rewrite <- HHeapAgree.
    eapply Step_label_heap_safe; eauto.
Qed.

Lemma PairParLeftRightStep_local_diamond_agree :
  forall left right k label_left label_right left' right',
    state_heap left = state_heap right ->
    StateRunHeapsAgree left ->
    StateRunHeapsAgree right ->
    Step left label_left left' ->
    Step right label_right right' ->
    Disjoint_Traces (label_trace label_left) (label_trace label_right) ->
    Disjoint_Traces (label_trace label_right) (label_trace label_left) ->
    exists state_after,
      PairParStep
        (PPS_Run left' (with_state_heap (state_heap left') right) k)
        label_right
        state_after /\
      PairParStep
        (PPS_Run (with_state_heap (state_heap right') left) right' k)
        label_left
        state_after.
Proof.
  intros left right k label_left label_right left' right'
    HHeapAgree HLeftAgree HRightAgree
    HStepLeft HStepRight HDisjointLR HDisjointRL.
  set (heap_after :=
    label_result_heap label_right
      (label_result_heap label_left (state_heap left))).
  set (state_after :=
    PPS_Run
      (with_state_heap heap_after left')
      (with_state_heap heap_after right')
      k).
  exists state_after.
  split.
  - subst state_after.
    replace (with_state_heap heap_after left') with
      (with_state_heap
        (state_heap (with_state_heap heap_after right')) left')
      by (rewrite state_heap_with_state_heap; reflexivity).
    apply PPStep_Right.
    subst heap_after.
    rewrite <- (Step_state_heap_label_result _ _ _ HStepLeft).
    eapply (Step_rebase_after_disjoint_step_agree
      right label_right right' left label_left left').
    + symmetry. exact HHeapAgree.
    + exact HRightAgree.
    + exact HStepRight.
    + exact HStepLeft.
    + exact HDisjointRL.
  - subst state_after.
    replace (with_state_heap heap_after right') with
      (with_state_heap
        (state_heap (with_state_heap heap_after left')) right')
      by (rewrite state_heap_with_state_heap; reflexivity).
    apply PPStep_Left.
    subst heap_after.
    rewrite (label_result_heap_commute_disjoint_eq
      label_left label_right (state_heap left) HDisjointLR).
    rewrite HHeapAgree.
    rewrite <- (Step_state_heap_label_result _ _ _ HStepRight).
    eapply (Step_rebase_after_disjoint_step_agree
      left label_left left' right label_right right').
    + exact HHeapAgree.
    + exact HLeftAgree.
    + exact HStepLeft.
    + exact HStepRight.
    + exact HDisjointLR.
Qed.

Lemma PairParLeftRightActualStep_local_diamond_agree :
  forall left right label_left label_right left' right_after,
    state_heap left = state_heap right ->
    StateRunHeapsAgree left ->
    StateRunHeapsAgree right ->
    Step left label_left left' ->
    Step (with_state_heap (state_heap left') right) label_right right_after ->
    LabelAllocReflectionStable label_right label_left ->
    Disjoint_Traces (label_trace label_left) (label_trace label_right) ->
    Disjoint_Traces (label_trace label_right) (label_trace label_left) ->
    exists right',
      Step right label_right right' /\
      Step
        (with_state_heap (state_heap right') left)
        label_left
        (with_state_heap (state_heap right_after) left') /\
      right_after = with_state_heap (state_heap right_after) right' /\
      StateRunHeapsAgree right'.
Proof.
  intros left right label_left label_right left' right_after
    HHeapAgree HLeftAgree HRightAgree HStepLeft HStepRightAfter
    HStable HDisjointLR HDisjointRL.
  pose proof
    (Step_label_heap_safe _ _ _ HStepRightAfter)
    as HSafeAfter.
  rewrite state_heap_with_state_heap in HSafeAfter.
  pose proof
    (LabelHeapSafe_reflected_by_disjoint_step_any
      label_right left label_left left'
      HStepLeft HStable HSafeAfter HDisjointRL)
    as HSafeBefore.
  pose proof
    (step_preserves_state_run_heaps_agree
      (with_state_heap (state_heap left') right)
      label_right right_after
      (StateRunHeapsAgree_with_state_heap
        (state_heap left') right HRightAgree)
      HStepRightAfter)
    as HRightAfterAgree.
  set (right' :=
    with_state_heap
      (label_result_heap label_right (state_heap right))
      right_after).
  assert (HStepRight : Step right label_right right').
  {
    subst right'.
    eapply Step_unbase_with_safe_label_agree.
    - exact HRightAgree.
    - exact HStepRightAfter.
    - rewrite <- HHeapAgree. exact HSafeBefore.
  }
  exists right'.
  split; [exact HStepRight |].
  split.
  - replace (state_heap right_after) with
      (label_result_heap label_left (state_heap right')).
    + eapply (Step_rebase_after_disjoint_step_agree
        left label_left left' right label_right right').
      * exact HHeapAgree.
      * exact HLeftAgree.
      * exact HStepLeft.
      * exact HStepRight.
      * exact HDisjointLR.
    + rewrite (Step_state_heap_label_result _ _ _ HStepRightAfter).
      rewrite (Step_state_heap_label_result _ _ _ HStepLeft).
      rewrite (Step_state_heap_label_result _ _ _ HStepRight).
      rewrite HHeapAgree.
      rewrite state_heap_with_state_heap.
      symmetry.
      apply label_result_heap_commute_disjoint_eq.
      exact HDisjointLR.
  - split.
    + subst right'.
      rewrite with_state_heap_overwrite.
      symmetry.
      apply with_state_heap_state_heap_agree.
      exact HRightAfterAgree.
    + subst right'.
      apply StateRunHeapsAgree_with_state_heap.
      exact HRightAfterAgree.
Qed.

Lemma PairParLoosePackedStepsPhi_LeftRight_adjacent_swap_checked :
  forall left right k label_left label_right left' right_after
    phi_sched phi_state phi_left phi_right final_state theta_left theta_right,
    state_heap left = state_heap right ->
    StateRunHeapsAgree left ->
    StateRunHeapsAgree right ->
    Step left label_left left' ->
    Step (with_state_heap (state_heap left') right) label_right right_after ->
    label_phi label_left ⋞ theta_left ->
    label_phi label_right ⋞ theta_right ->
    PairParCheckPass theta_left theta_right ->
    PairParLoosePackedStepsPhi
      (PPS_Run (with_state_heap (state_heap right_after) left')
        right_after k)
      phi_sched
      phi_state
      phi_left
      phi_right
      final_state ->
    exists phi_sched',
      PairParLoosePackedStepsPhi
        (PPS_Run left right k)
        phi_sched'
        phi_state
        (Phi_Seq (label_phi label_left) phi_left)
        (Phi_Seq (label_phi label_right) phi_right)
        final_state.
Proof.
  intros left right k label_left label_right left' right_after
    phi_sched phi_state phi_left phi_right final_state theta_left theta_right
    HHeapAgree HLeftAgree HRightAgree HStepLeft HStepRightAfter
    HSoundLeft HSoundRight HPass HRest.
  destruct HPass as [HDisjointTheta HNoConflictTheta].
  assert (HStable :
    LabelAllocReflectionStable label_right label_left).
  {
    eapply LabelAllocReflectionStable_from_theta; eauto.
  }
  assert (HDisjointLR :
    Disjoint_Traces (label_trace label_left) (label_trace label_right)).
  {
    rewrite <- (phi_as_list_label_phi label_left).
    rewrite <- (phi_as_list_label_phi label_right).
    eapply PairParCheckPass_sound_disjoint_traces; eauto.
    split; assumption.
  }
  assert (HDisjointRL :
    Disjoint_Traces (label_trace label_right) (label_trace label_left)).
  {
    rewrite <- (phi_as_list_label_phi label_right).
    rewrite <- (phi_as_list_label_phi label_left).
    eapply PairParCheckPass_sound_disjoint_traces_sym; eauto.
    split; assumption.
  }
  destruct
    (PairParLeftRightActualStep_local_diamond_agree
      left right label_left label_right left' right_after
      HHeapAgree HLeftAgree HRightAgree
      HStepLeft HStepRightAfter HStable HDisjointLR HDisjointRL)
    as (right' & HStepRight & HStepLeftAfterRight &
        HRightAfterRebase & _).
  exists
    (Phi_Seq (label_phi label_right)
      (Phi_Seq (label_phi label_left) phi_sched)).
  eapply PairParLoosePackedStepsPhi_Right.
  - exact HStepRight.
  - eapply PairParLoosePackedStepsPhi_Left.
    + exact HStepLeftAfterRight.
    + replace
        (with_state_heap
          (state_heap (with_state_heap (state_heap right_after) left'))
          right')
        with right_after.
      exact HRest.
      rewrite state_heap_with_state_heap.
      exact HRightAfterRebase.
Qed.

Inductive PairParLooseLeftOnlyStepsPhi :
  PairParState -> Phi -> Phi -> Phi -> PairParState -> Prop :=
| PPLLO_Refl :
    forall state,
      PairParLooseLeftOnlyStepsPhi
        state Phi_Nil Phi_Nil Phi_Nil state
| PPLLO_State :
    forall state label state' phi_sched phi_state phi_left final_state,
      Step state label state' ->
      PairParLooseLeftOnlyStepsPhi
        (pairpar_state_of_state state')
        phi_sched
        phi_state
        phi_left
        final_state ->
      PairParLooseLeftOnlyStepsPhi
        (PPS_State state)
        (Phi_Seq (label_phi label) phi_sched)
        (Phi_Seq (label_phi label) phi_state)
        phi_left
        final_state
| PPLLO_Left :
    forall left right k label left'
      phi_sched phi_state phi_left final_state,
      Step left label left' ->
      PairParLooseLeftOnlyStepsPhi
        (PPS_Run left' (with_state_heap (state_heap left') right) k)
        phi_sched
        phi_state
        phi_left
        final_state ->
      PairParLooseLeftOnlyStepsPhi
        (PPS_Run left right k)
        (Phi_Seq (label_phi label) phi_sched)
        phi_state
        (Phi_Seq (label_phi label) phi_left)
        final_state
| PPLLO_Done :
    forall heap v1 v2 k phi_sched phi_state phi_left final_state,
      PairParLooseLeftOnlyStepsPhi
        (PPS_State (StReturn heap (Pair (v1, v2)) k))
        phi_sched
        phi_state
        phi_left
        final_state ->
      PairParLooseLeftOnlyStepsPhi
        (PPS_Run (StDone heap v1) (StDone heap v2) k)
        (Phi_Seq (label_phi Silent) phi_sched)
        phi_state
        phi_left
        final_state.

Inductive PairParLooseRightThenLeftStepsPhi :
  PairParState -> Phi -> Phi -> Phi -> Phi -> PairParState -> Prop :=
| PPLRTL_LeftOnly :
    forall state phi_sched phi_state phi_left final_state,
      PairParLooseLeftOnlyStepsPhi
        state phi_sched phi_state phi_left final_state ->
      PairParLooseRightThenLeftStepsPhi
        state phi_sched phi_state phi_left Phi_Nil final_state
| PPLRTL_State :
    forall state label state' phi_sched phi_state phi_left phi_right
      final_state,
      Step state label state' ->
      PairParLooseRightThenLeftStepsPhi
        (pairpar_state_of_state state')
        phi_sched
        phi_state
        phi_left
        phi_right
        final_state ->
      PairParLooseRightThenLeftStepsPhi
        (PPS_State state)
        (Phi_Seq (label_phi label) phi_sched)
        (Phi_Seq (label_phi label) phi_state)
        phi_left
        phi_right
        final_state
| PPLRTL_Right :
    forall left right k label right'
      phi_sched phi_state phi_left phi_right final_state,
      Step right label right' ->
      PairParLooseRightThenLeftStepsPhi
        (PPS_Run (with_state_heap (state_heap right') left) right' k)
        phi_sched
        phi_state
        phi_left
        phi_right
        final_state ->
      PairParLooseRightThenLeftStepsPhi
        (PPS_Run left right k)
        (Phi_Seq (label_phi label) phi_sched)
        phi_state
        phi_left
        (Phi_Seq (label_phi label) phi_right)
        final_state.

Lemma PairParLooseLeftOnlyStepsPhi_as_loose_packed :
  forall state phi_sched phi_state phi_left final_state,
    PairParLooseLeftOnlyStepsPhi
      state phi_sched phi_state phi_left final_state ->
    PairParLoosePackedStepsPhi
      state phi_sched phi_state phi_left Phi_Nil final_state.
Proof.
  intros state phi_sched phi_state phi_left final_state HSteps.
  induction HSteps.
  - constructor.
  - eapply PairParLoosePackedStepsPhi_State; eauto.
  - eapply PairParLoosePackedStepsPhi_Left; eauto.
  - eapply PairParLoosePackedStepsPhi_Done; eauto.
Qed.

Lemma PairParLooseRightThenLeftStepsPhi_as_loose_packed :
  forall state phi_sched phi_state phi_left phi_right final_state,
    PairParLooseRightThenLeftStepsPhi
      state phi_sched phi_state phi_left phi_right final_state ->
    PairParLoosePackedStepsPhi
      state phi_sched phi_state phi_left phi_right final_state.
Proof.
  intros state phi_sched phi_state phi_left phi_right final_state HSteps.
  induction HSteps.
  - now apply PairParLooseLeftOnlyStepsPhi_as_loose_packed.
  - eapply PairParLoosePackedStepsPhi_State; eauto.
  - eapply PairParLoosePackedStepsPhi_Right; eauto.
Qed.

Lemma PairParLooseLeftOnlyStepsPhi_from_left_terminal :
  forall left phi_left heap_left v_left v_right,
    StepsPhi left phi_left (StDone heap_left v_left) ->
    exists phi_sched phi_state,
      PairParLooseLeftOnlyStepsPhi
        (PPS_Run left (StDone (state_heap left) v_right) KDone)
        phi_sched
        phi_state
        phi_left
        (PPS_State (StDone heap_left (Pair (v_left, v_right)))).
Proof.
  intros left phi_left heap_left v_left v_right HSteps.
  remember (StDone heap_left v_left) as final_state eqn:HFinal.
  revert heap_left v_left v_right HFinal.
  induction HSteps as
    [state
    | state label state' phi state'' HStep _ IH];
    intros heap_left v_left v_right HFinal; subst.
  - exists
      (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil)),
      (Phi_Seq (label_phi Silent) Phi_Nil).
    simpl.
    eapply PPLLO_Done.
    eapply PPLLO_State with
      (label := Silent)
      (state' := StDone heap_left (Pair (v_left, v_right))).
    + apply Step_Done.
    + constructor.
  - destruct (IH heap_left v_left v_right eq_refl)
      as (phi_sched & phi_state & HTail).
    exists (Phi_Seq (label_phi label) phi_sched), phi_state.
    eapply PPLLO_Left; eauto.
Qed.

Lemma PairParLooseRightThenLeftStepsPhi_from_branch_terminals :
  forall left right phi_right heap_right v_right phi_left heap_left v_left,
    StateRunHeapsAgree left ->
    StateRunHeapsAgree right ->
    state_heap left = state_heap right ->
    StepsPhi right phi_right (StDone heap_right v_right) ->
    StepsPhi
      (with_state_heap heap_right left)
      phi_left
      (StDone heap_left v_left) ->
    exists phi_sched phi_state,
      PairParLooseRightThenLeftStepsPhi
        (PPS_Run left right KDone)
        phi_sched
        phi_state
        phi_left
        phi_right
        (PPS_State (StDone heap_left (Pair (v_left, v_right)))).
Proof.
  intros left right phi_right heap_right v_right phi_left heap_left v_left
    HLeftAgree HRightAgree HHeapAgree HRightSteps HLeftSteps.
  revert left HLeftAgree HHeapAgree phi_left heap_left v_left HLeftSteps.
  dependent induction HRightSteps;
    intros left HLeftAgree HHeapAgree phi_left heap_left v_left HLeftSteps.
  - repeat match goal with
    | H : StDone _ _ = _ |- _ => symmetry in H; subst
    | H : _ = StDone _ _ |- _ => subst
    end.
    simpl in *.
    subst heap_right.
    rewrite with_state_heap_state_heap_agree in HLeftSteps by exact HLeftAgree.
    destruct
      (PairParLooseLeftOnlyStepsPhi_from_left_terminal
        left phi_left heap_left v_left v_right HLeftSteps)
      as (phi_sched & phi_state & HLeftOnly).
    exists phi_sched, phi_state.
    apply PPLRTL_LeftOnly.
    exact HLeftOnly.
  - destruct
      (IHHRightSteps
        heap_right
        v_right
        (step_preserves_state_run_heaps_agree
          state label state' HRightAgree H)
        eq_refl
        (with_state_heap (state_heap state') left)
        (StateRunHeapsAgree_with_state_heap (state_heap state') left HLeftAgree)
        ltac:(rewrite state_heap_with_state_heap; reflexivity)
        phi_left heap_left v_left)
      as (phi_sched & phi_state & HTail).
    {
      rewrite with_state_heap_overwrite.
      exact HLeftSteps.
    }
    exists (Phi_Seq (label_phi label) phi_sched), phi_state.
    eapply PPLRTL_Right.
    + exact H.
    + exact HTail.
Qed.

Lemma PairParLoosePackedStepsPhi_from_branch_terminals :
  forall left right phi_right heap_right v_right phi_left heap_left v_left,
    StateRunHeapsAgree left ->
    StateRunHeapsAgree right ->
    state_heap left = state_heap right ->
    StepsPhi right phi_right (StDone heap_right v_right) ->
    StepsPhi
      (with_state_heap heap_right left)
      phi_left
      (StDone heap_left v_left) ->
    exists phi_sched phi_state,
      PairParLoosePackedStepsPhi
        (PPS_Run left right KDone)
        phi_sched
        phi_state
        phi_left
        phi_right
        (PPS_State (StDone heap_left (Pair (v_left, v_right)))).
Proof.
  intros left right phi_right heap_right v_right phi_left heap_left v_left
    HLeftAgree HRightAgree HHeapAgree HRightSteps HLeftSteps.
  destruct
    (PairParLooseRightThenLeftStepsPhi_from_branch_terminals
      left right phi_right heap_right v_right phi_left heap_left v_left
      HLeftAgree HRightAgree HHeapAgree HRightSteps HLeftSteps)
    as (phi_sched & phi_state & HRTL).
  exists phi_sched, phi_state.
  now apply PairParLooseRightThenLeftStepsPhi_as_loose_packed.
Qed.

Lemma PairParLooseLeftOnlyStepsPhi_from_left_terminal_to_return :
  forall left phi_left heap_left v_left v_right k,
    StepsPhi left phi_left (StDone heap_left v_left) ->
    exists phi_sched,
      PairParLooseLeftOnlyStepsPhi
        (PPS_Run left (StDone (state_heap left) v_right) k)
        phi_sched
        Phi_Nil
        phi_left
        (PPS_State
          (StReturn heap_left (Pair (v_left, v_right)) k)).
Proof.
  intros left phi_left heap_left v_left v_right k HSteps.
  remember (StDone heap_left v_left) as left_final eqn:HFinal.
  revert heap_left v_left v_right k HFinal.
  induction HSteps as
    [state
    | state label state' phi_tail state'' HStep _ IH];
    intros heap_left v_left v_right k HFinal; subst.
  - exists (Phi_Seq (label_phi Silent) Phi_Nil).
    eapply PPLLO_Done.
    constructor.
  - destruct (IH heap_left v_left v_right k eq_refl)
      as (phi_sched & HLeftOnly).
    exists (Phi_Seq (label_phi label) phi_sched).
    eapply PPLLO_Left; eauto.
Qed.

Lemma PairParLooseRightThenLeftStepsPhi_from_branch_terminals_to_return :
  forall left right phi_right heap_right v_right phi_left heap_left v_left k,
    StateRunHeapsAgree left ->
    StateRunHeapsAgree right ->
    state_heap left = state_heap right ->
    StepsPhi right phi_right (StDone heap_right v_right) ->
    StepsPhi
      (with_state_heap heap_right left)
      phi_left
      (StDone heap_left v_left) ->
    exists phi_sched,
      PairParLooseRightThenLeftStepsPhi
        (PPS_Run left right k)
        phi_sched
        Phi_Nil
        phi_left
        phi_right
        (PPS_State
          (StReturn heap_left (Pair (v_left, v_right)) k)).
Proof.
  intros left right phi_right heap_right v_right phi_left heap_left v_left k
    HLeftAgree HRightAgree HHeapAgree HRightSteps HLeftSteps.
  revert left HLeftAgree HHeapAgree phi_left heap_left v_left HLeftSteps.
  dependent induction HRightSteps;
    intros left0 HLeftAgree HHeapAgree phi_left heap_left v_left HLeftSteps.
  - repeat match goal with
    | H : StDone _ _ = _ |- _ => symmetry in H; subst
    | H : _ = StDone _ _ |- _ => subst
    end.
    simpl in *.
    subst heap_right.
    rewrite with_state_heap_state_heap_agree in HLeftSteps by exact HLeftAgree.
    destruct
      (PairParLooseLeftOnlyStepsPhi_from_left_terminal_to_return
        left0 phi_left heap_left v_left v_right k HLeftSteps)
      as (phi_sched & HLeftOnly).
    exists phi_sched.
    apply PPLRTL_LeftOnly.
    exact HLeftOnly.
  - destruct
      (IHHRightSteps
        heap_right
        v_right
        (step_preserves_state_run_heaps_agree
          state label state' HRightAgree H)
        eq_refl
        (with_state_heap (state_heap state') left0)
        (StateRunHeapsAgree_with_state_heap
          (state_heap state') left0 HLeftAgree)
        ltac:(rewrite state_heap_with_state_heap; reflexivity)
        phi_left heap_left v_left)
      as (phi_sched & HRTL).
    {
      rewrite with_state_heap_overwrite.
      exact HLeftSteps.
    }
    exists (Phi_Seq (label_phi label) phi_sched).
    eapply PPLRTL_Right; eauto.
Qed.

Lemma PairParLoosePackedStepsPhi_from_branch_terminals_to_return :
  forall left right phi_right heap_right v_right phi_left heap_left v_left k,
    StateRunHeapsAgree left ->
    StateRunHeapsAgree right ->
    state_heap left = state_heap right ->
    StepsPhi right phi_right (StDone heap_right v_right) ->
    StepsPhi
      (with_state_heap heap_right left)
      phi_left
      (StDone heap_left v_left) ->
    exists phi_sched,
      PairParLoosePackedStepsPhi
        (PPS_Run left right k)
        phi_sched
        Phi_Nil
        phi_left
        phi_right
        (PPS_State
          (StReturn heap_left (Pair (v_left, v_right)) k)).
Proof.
  intros left right phi_right heap_right v_right phi_left heap_left v_left k
    HLeftAgree HRightAgree HHeapAgree HRightSteps HLeftSteps.
  destruct
    (PairParLooseRightThenLeftStepsPhi_from_branch_terminals_to_return
      left right phi_right heap_right v_right phi_left heap_left v_left k
      HLeftAgree HRightAgree HHeapAgree HRightSteps HLeftSteps)
    as (phi_sched & HRTL).
  exists phi_sched.
  now apply PairParLooseRightThenLeftStepsPhi_as_loose_packed.
Qed.

Lemma PairParLooseLeftOnlyStepsPhi_state_from_ordinary_stepsphi :
  forall state phi_state state',
    OrdinaryStepsPhi state phi_state state' ->
    exists phi_sched,
      PairParLooseLeftOnlyStepsPhi
        (PPS_State state)
        phi_sched
        phi_state
        Phi_Nil
        (PPS_State state').
Proof.
  intros state phi_state state' HSteps.
  induction HSteps as
    [state
    | state label state' phi_tail state''
        _ HNonTarget HStep _ IH].
  - exists Phi_Nil. constructor.
  - destruct IH as (phi_sched & HLoose).
    exists (Phi_Seq (label_phi label) phi_sched).
    eapply PPLLO_State.
    + exact HStep.
    + rewrite pairpar_state_of_state_non_pair; eauto.
Qed.

Lemma PairParLooseLeftOnlyStepsPhi_from_left_terminal_with_tail :
  forall left phi_left heap_left v_left v_right k
    phi_state heap_final v_final,
    StepsPhi left phi_left (StDone heap_left v_left) ->
    OrdinaryStepsPhi
      (StReturn heap_left (Pair (v_left, v_right)) k)
      phi_state
      (StDone heap_final v_final) ->
    exists phi_sched,
      PairParLooseLeftOnlyStepsPhi
        (PPS_Run left (StDone (state_heap left) v_right) k)
        phi_sched
        phi_state
        phi_left
        (PPS_State (StDone heap_final v_final)).
Proof.
  intros left phi_left heap_left v_left v_right k
    phi_state heap_final v_final HLeft HTail.
  remember (StDone heap_left v_left) as left_final eqn:HLeftFinal.
  revert heap_left v_left v_right k phi_state heap_final v_final
    HLeftFinal HTail.
  induction HLeft as
    [state
    | state label state' phi_tail state'' HStep _ IH];
    intros heap_left v_left v_right k phi_state heap_final v_final
      HLeftFinal HTail;
    subst.
  - destruct
      (PairParLooseLeftOnlyStepsPhi_state_from_ordinary_stepsphi
        (StReturn heap_left (Pair (v_left, v_right)) k)
        phi_state
        (StDone heap_final v_final)
        HTail)
      as (phi_sched & HState).
    exists (Phi_Seq (label_phi Silent) phi_sched).
    eapply PPLLO_Done.
    exact HState.
  - destruct
      (IH heap_left v_left v_right k phi_state heap_final v_final
        eq_refl HTail)
      as (phi_sched & HLoose).
    exists (Phi_Seq (label_phi label) phi_sched).
    eapply PPLLO_Left; eauto.
Qed.

Lemma PairParLooseRightThenLeftStepsPhi_from_branch_terminals_with_tail :
  forall left right phi_right heap_right v_right phi_left heap_left v_left
    k phi_state heap_final v_final,
    StateRunHeapsAgree left ->
    StateRunHeapsAgree right ->
    state_heap left = state_heap right ->
    StepsPhi right phi_right (StDone heap_right v_right) ->
    StepsPhi
      (with_state_heap heap_right left)
      phi_left
      (StDone heap_left v_left) ->
    OrdinaryStepsPhi
      (StReturn heap_left (Pair (v_left, v_right)) k)
      phi_state
      (StDone heap_final v_final) ->
    exists phi_sched,
      PairParLooseRightThenLeftStepsPhi
        (PPS_Run left right k)
        phi_sched
        phi_state
        phi_left
        phi_right
        (PPS_State (StDone heap_final v_final)).
Proof.
  intros left right phi_right heap_right v_right phi_left heap_left v_left
    k phi_state heap_final v_final
    HLeftAgree HRightAgree HHeapAgree HRight HLeft HTail.
  revert left HLeftAgree HHeapAgree phi_left heap_left v_left
    HLeft HTail.
  dependent induction HRight;
    intros left0 HLeftAgree HHeapAgree phi_left heap_left v_left
      HLeft HTail.
  - repeat match goal with
    | H : StDone _ _ = _ |- _ => symmetry in H; subst
    | H : _ = StDone _ _ |- _ => subst
    end.
    simpl in *.
    subst heap_right.
    rewrite with_state_heap_state_heap_agree in HLeft by exact HLeftAgree.
    destruct
      (PairParLooseLeftOnlyStepsPhi_from_left_terminal_with_tail
        left0 phi_left heap_left v_left v_right k
        phi_state heap_final v_final HLeft HTail)
      as (phi_sched & HLeftOnly).
    exists phi_sched.
    apply PPLRTL_LeftOnly.
    exact HLeftOnly.
  - destruct
      (IHHRight
        heap_right
        v_right
        (step_preserves_state_run_heaps_agree
          state label state' HRightAgree H)
        eq_refl
        (with_state_heap (state_heap state') left0)
        (StateRunHeapsAgree_with_state_heap
          (state_heap state') left0 HLeftAgree)
        ltac:(rewrite state_heap_with_state_heap; reflexivity)
        phi_left heap_left v_left)
      as (phi_sched & HRTL).
    + rewrite with_state_heap_overwrite.
      exact HLeft.
    + exact HTail.
    + exists (Phi_Seq (label_phi label) phi_sched).
      eapply PPLRTL_Right; eauto.
Qed.

Lemma PairParLoosePackedStepsPhi_from_branch_terminals_with_tail :
  forall left right phi_right heap_right v_right phi_left heap_left v_left
    k phi_state heap_final v_final,
    StateRunHeapsAgree left ->
    StateRunHeapsAgree right ->
    state_heap left = state_heap right ->
    StepsPhi right phi_right (StDone heap_right v_right) ->
    StepsPhi
      (with_state_heap heap_right left)
      phi_left
      (StDone heap_left v_left) ->
    OrdinaryStepsPhi
      (StReturn heap_left (Pair (v_left, v_right)) k)
      phi_state
      (StDone heap_final v_final) ->
    exists phi_sched,
      PairParLoosePackedStepsPhi
        (PPS_Run left right k)
        phi_sched
        phi_state
        phi_left
        phi_right
        (PPS_State (StDone heap_final v_final)).
Proof.
  intros left right phi_right heap_right v_right phi_left heap_left v_left
    k phi_state heap_final v_final
    HLeftAgree HRightAgree HHeapAgree HRight HLeft HTail.
  destruct
    (PairParLooseRightThenLeftStepsPhi_from_branch_terminals_with_tail
      left right phi_right heap_right v_right phi_left heap_left v_left
      k phi_state heap_final v_final
      HLeftAgree HRightAgree HHeapAgree HRight HLeft HTail)
    as (phi_sched & HRTL).
  exists phi_sched.
  now apply PairParLooseRightThenLeftStepsPhi_as_loose_packed.
Qed.

Lemma Phi_Theta_Soundness_seq_inv_l_loose :
  forall phi1 phi2 theta,
    Phi_Seq phi1 phi2 ⋞ theta ->
    phi1 ⋞ theta.
Proof.
  intros phi1 phi2 theta HSound.
  inversion HSound; subst; assumption.
Qed.

Lemma Phi_Theta_Soundness_seq_inv_r_loose :
  forall phi1 phi2 theta,
    Phi_Seq phi1 phi2 ⋞ theta ->
    phi2 ⋞ theta.
Proof.
  intros phi1 phi2 theta HSound.
  inversion HSound; subst; assumption.
Qed.

Lemma PairParLoosePackedStepsPhi_state_done_as_left_only :
  forall heap v phi_sched phi_state phi_left phi_right final_state,
    PairParLoosePackedStepsPhi
      (PPS_State (StDone heap v))
      phi_sched
      phi_state
      phi_left
      phi_right
      final_state ->
    phi_sched = Phi_Nil /\
    phi_state = Phi_Nil /\
    phi_left = Phi_Nil /\
    phi_right = Phi_Nil /\
    final_state = PPS_State (StDone heap v) /\
    PairParLooseLeftOnlyStepsPhi
      (PPS_State (StDone heap v))
      phi_sched
      phi_state
      Phi_Nil
      final_state.
Proof.
  intros heap v phi_sched phi_state phi_left phi_right final_state HSteps.
  remember (PPS_State (StDone heap v)) as start eqn:HStart.
  induction HSteps; inversion HStart; subst.
  - repeat split; try reflexivity.
    constructor.
  - exfalso. eapply done_no_step; eauto.
Qed.

Lemma PairParLoosePackedStepsPhi_state_return_kdone_as_left_only :
  forall heap v phi_sched phi_state phi_left phi_right final_state,
    PairParLoosePackedStepsPhi
      (PPS_State (StReturn heap v KDone))
      phi_sched
      phi_state
      phi_left
      phi_right
      final_state ->
    phi_left = Phi_Nil /\
    phi_right = Phi_Nil /\
    PairParLooseLeftOnlyStepsPhi
      (PPS_State (StReturn heap v KDone))
      phi_sched
      phi_state
      Phi_Nil
      final_state.
Proof.
  intros heap v phi_sched phi_state phi_left phi_right final_state HSteps.
  inversion HSteps; subst; try discriminate.
  - repeat split; constructor.
  - match goal with
    | HStep : Step _ _ _ |- _ => inversion HStep; subst
    end.
    change (pairpar_state_of_state (StDone heap v))
      with (PPS_State (StDone heap v)) in *.
    match goal with
    | HRest :
        PairParLoosePackedStepsPhi
          (PPS_State (StDone ?heap_done ?v_done))
          ?phi_sched_tail
          ?phi_state_tail
          ?phi_left_tail
          ?phi_right_tail
          ?final_tail |- _ =>
        destruct
          (PairParLoosePackedStepsPhi_state_done_as_left_only
            heap_done v_done phi_sched_tail phi_state_tail
            phi_left_tail phi_right_tail final_tail HRest)
          as (HSchedNil & HStateNil & HLeftNil & HRightNil &
              HFinal & HLeftOnly)
    end.
    subst.
    split; [reflexivity |].
    split; [reflexivity |].
    eapply PPLLO_State.
    + constructor.
    + exact HLeftOnly.
Qed.

Lemma PairParLooseRightThenLeftStepsPhi_prepend_left :
  forall left right k label left' phi_sched phi_state phi_left phi_right
    final_state theta_left theta_right,
    state_heap left = state_heap right ->
    StateRunHeapsAgree left ->
    StateRunHeapsAgree right ->
    Step left label left' ->
    label_phi label ⋞ theta_left ->
    phi_right ⋞ theta_right ->
    PairParCheckPass theta_left theta_right ->
    PairParLooseRightThenLeftStepsPhi
      (PPS_Run left' (with_state_heap (state_heap left') right) k)
      phi_sched
      phi_state
      phi_left
      phi_right
      final_state ->
    exists phi_sched',
      PairParLooseRightThenLeftStepsPhi
        (PPS_Run left right k)
        phi_sched'
        phi_state
        (Phi_Seq (label_phi label) phi_left)
        phi_right
        final_state.
Proof.
  intros left right k label left' phi_sched phi_state phi_left phi_right
    final_state theta_left theta_right HHeapAgree HLeftAgree HRightAgree
    HStepLeft HSoundLeft HSoundRight HPass HRTL.
  remember
    (PPS_Run left' (with_state_heap (state_heap left') right) k)
    as rest_start eqn:HRestStart.
  revert left right k label left'
    HHeapAgree HLeftAgree HRightAgree HStepLeft HSoundLeft HRestStart.
  induction HRTL;
    intros left0 right0 k0 label0 left0'
      HHeapAgree HLeftAgree HRightAgree HStepLeft HSoundLeft HRestStart;
    inversion HRestStart; subst.
  - exists (Phi_Seq (label_phi label0) phi_sched).
    apply PPLRTL_LeftOnly.
    eapply PPLLO_Left; eauto.
  - pose proof
      (Phi_Theta_Soundness_seq_inv_l_loose
        (label_phi label) phi_right theta_right HSoundRight)
      as HSoundRightHead.
    pose proof
      (Phi_Theta_Soundness_seq_inv_r_loose
        (label_phi label) phi_right theta_right HSoundRight)
      as HSoundRightTail.
    destruct HPass as [HDisjointTheta HNoConflictTheta].
    assert (HStable :
      LabelAllocReflectionStable label label0).
    {
      eapply LabelAllocReflectionStable_from_theta; eauto.
    }
    assert (HDisjointLR :
      Disjoint_Traces (label_trace label0) (label_trace label)).
    {
      rewrite <- (phi_as_list_label_phi label0).
      rewrite <- (phi_as_list_label_phi label).
      eapply PairParCheckPass_sound_disjoint_traces; eauto.
      split; assumption.
    }
    assert (HDisjointRL :
      Disjoint_Traces (label_trace label) (label_trace label0)).
    {
      rewrite <- (phi_as_list_label_phi label).
      rewrite <- (phi_as_list_label_phi label0).
      eapply PairParCheckPass_sound_disjoint_traces_sym; eauto.
      split; assumption.
    }
    destruct
      (PairParLeftRightActualStep_local_diamond_agree
        left0 right0 label0 label left0' right'
        HHeapAgree HLeftAgree HRightAgree
        HStepLeft H HStable HDisjointLR HDisjointRL)
      as (right0' & HStepRight0 & HStepLeftAfterRight &
          HRightAfterRebase & HRight0Agree).
    destruct
      (IHHRTL HSoundRightTail
        (with_state_heap (state_heap right0') left0)
        right0'
        k0
        label0
        (with_state_heap (state_heap right') left0'))
      as (phi_sched' & HNormTail).
    + rewrite state_heap_with_state_heap. reflexivity.
    + apply StateRunHeapsAgree_with_state_heap. exact HLeftAgree.
    + exact HRight0Agree.
    + exact HStepLeftAfterRight.
    + exact HSoundLeft.
    + rewrite state_heap_with_state_heap.
      rewrite <- HRightAfterRebase.
      reflexivity.
    + exists (Phi_Seq (label_phi label) phi_sched').
      eapply PPLRTL_Right.
      * exact HStepRight0.
      * exact HNormTail.
Qed.

Theorem PairParLoosePackedStepsPhi_normalize_right_then_left_kdone :
  forall left right phi_sched phi_state phi_left phi_right
    heap_final v_final theta_left theta_right,
    state_heap left = state_heap right ->
    StateRunHeapsAgree left ->
    StateRunHeapsAgree right ->
    PairParLoosePackedStepsPhi
      (PPS_Run left right KDone)
      phi_sched
      phi_state
      phi_left
      phi_right
      (PPS_State (StDone heap_final v_final)) ->
    phi_left ⋞ theta_left ->
    phi_right ⋞ theta_right ->
    PairParCheckPass theta_left theta_right ->
    exists phi_sched',
      PairParLooseRightThenLeftStepsPhi
        (PPS_Run left right KDone)
        phi_sched'
        phi_state
        phi_left
        phi_right
        (PPS_State (StDone heap_final v_final)).
Proof.
  intros left right phi_sched phi_state phi_left phi_right
    heap_final v_final theta_left theta_right
    HHeapAgree HLeftAgree HRightAgree HSteps
    HSoundLeft HSoundRight HPass.
  remember (PPS_Run left right KDone) as start eqn:HStart.
  remember (PPS_State (StDone heap_final v_final)) as final_state
    eqn:HFinal.
  revert left right heap_final v_final
    HHeapAgree HLeftAgree HRightAgree HSoundLeft HSoundRight
    HStart HFinal.
  induction HSteps;
    intros left0 right0 heap_final0 v_final0
      HHeapAgree HLeftAgree HRightAgree HSoundLeft HSoundRight
      HStart HFinal;
    inversion HStart; inversion HFinal; subst.
  - discriminate.
  - pose proof
      (Phi_Theta_Soundness_seq_inv_l_loose
        (label_phi label) phi_left theta_left HSoundLeft)
      as HSoundLeftHead.
    pose proof
      (Phi_Theta_Soundness_seq_inv_r_loose
        (label_phi label) phi_left theta_left HSoundLeft)
      as HSoundLeftTail.
    destruct
      (IHHSteps
        left'
        (with_state_heap (state_heap left') right0)
        heap_final0
        v_final0)
      as (phi_sched' & HNormTail).
    + rewrite state_heap_with_state_heap. reflexivity.
    + eapply step_preserves_state_run_heaps_agree.
      * exact HLeftAgree.
      * exact H.
    + apply StateRunHeapsAgree_with_state_heap. exact HRightAgree.
    + exact HSoundLeftTail.
    + exact HSoundRight.
    + reflexivity.
    + reflexivity.
    + eapply PairParLooseRightThenLeftStepsPhi_prepend_left.
      * exact HHeapAgree.
      * exact HLeftAgree.
      * exact HRightAgree.
      * exact H.
      * exact HSoundLeftHead.
      * exact HSoundRight.
      * exact HPass.
      * exact HNormTail.
  - pose proof
      (Phi_Theta_Soundness_seq_inv_l_loose
        (label_phi label) phi_right theta_right HSoundRight)
      as HSoundRightHead.
    pose proof
      (Phi_Theta_Soundness_seq_inv_r_loose
        (label_phi label) phi_right theta_right HSoundRight)
      as HSoundRightTail.
    destruct
      (IHHSteps
        (with_state_heap (state_heap right') left0)
        right'
        heap_final0
        v_final0)
      as (phi_sched' & HNormTail).
    + rewrite state_heap_with_state_heap. reflexivity.
    + apply StateRunHeapsAgree_with_state_heap. exact HLeftAgree.
    + eapply step_preserves_state_run_heaps_agree.
      * exact HRightAgree.
      * exact H.
    + exact HSoundLeft.
    + exact HSoundRightTail.
    + reflexivity.
    + reflexivity.
    + exists (Phi_Seq (label_phi label) phi_sched').
      eapply PPLRTL_Right.
      * exact H.
      * exact HNormTail.
  - destruct
      (PairParLoosePackedStepsPhi_state_return_kdone_as_left_only
        heap (Pair (v1, v2))
        phi_sched phi_state phi_left phi_right
        (PPS_State (StDone heap_final0 v_final0)) HSteps)
      as (HLeftNil & HRightNil & HLeftOnlyTail).
    subst.
    exists (Phi_Seq (label_phi Silent) phi_sched).
    apply PPLRTL_LeftOnly.
    eapply PPLLO_Done.
    exact HLeftOnlyTail.
Qed.

Lemma PairParLooseLeftOnlyStepsPhi_state_done_terminal_inv :
  forall heap v phi_sched phi_state phi_left heap_final v_final,
    PairParLooseLeftOnlyStepsPhi
      (PPS_State (StDone heap v))
      phi_sched
      phi_state
      phi_left
      (PPS_State (StDone heap_final v_final)) ->
    phi_sched = Phi_Nil /\
    phi_state = Phi_Nil /\
    phi_left = Phi_Nil /\
    heap_final = heap /\
    v_final = v.
Proof.
  intros heap v phi_sched phi_state phi_left heap_final v_final HSteps.
  inversion HSteps; subst; try discriminate.
  - repeat split; reflexivity.
  - exfalso. eapply done_no_step; eauto.
Qed.

Lemma PairParLooseLeftOnlyStepsPhi_state_return_kdone_terminal_steps :
  forall heap v phi_sched phi_state phi_left heap_final v_final,
    PairParLooseLeftOnlyStepsPhi
      (PPS_State (StReturn heap v KDone))
      phi_sched
      phi_state
      phi_left
      (PPS_State (StDone heap_final v_final)) ->
    phi_left = Phi_Nil /\
    StepsPhi
      (StReturn heap v KDone)
      phi_state
      (StDone heap_final v_final).
Proof.
  intros heap v phi_sched phi_state phi_left heap_final v_final HSteps.
  inversion HSteps; subst; try discriminate.
  - inversion H0; subst.
    change (pairpar_state_of_state (StDone heap v))
      with (PPS_State (StDone heap v)) in *.
    destruct
      (PairParLooseLeftOnlyStepsPhi_state_done_terminal_inv
        heap v phi_sched0 phi_state0 phi_left heap_final v_final H1)
      as (HSchedNil & HStateNil & HLeftNil & HHeapFinal & HValFinal).
    subst.
    split; [reflexivity |].
    eapply StepsPhi_Step.
    + constructor.
    + constructor.
Qed.

Lemma PairParLooseLeftOnlyStepsPhi_terminal_decompose_kdone :
  forall left v_right phi_sched phi_state phi_left heap_final v_final,
    PairParLooseLeftOnlyStepsPhi
      (PPS_Run left (StDone (state_heap left) v_right) KDone)
      phi_sched
      phi_state
      phi_left
      (PPS_State (StDone heap_final v_final)) ->
    exists heap_left v_left,
      StepsPhi left phi_left (StDone heap_left v_left) /\
      heap_final = heap_left /\
      v_final = Pair (v_left, v_right).
Proof.
  intros left v_right phi_sched phi_state phi_left heap_final v_final
    HSteps.
  dependent induction HSteps generalizing left v_right heap_final v_final.
  - destruct
      (IHHSteps left' v_right heap_final v_final)
      as (heap_left & v_left & HLeftSteps & HHeapFinal & HValFinal).
    + simpl. reflexivity.
    + reflexivity.
    + exists heap_left, v_left.
      split.
      * eapply StepsPhi_Step; eauto.
      * split; assumption.
  - destruct
      (PairParLooseLeftOnlyStepsPhi_state_return_kdone_terminal_steps
        (state_heap left) (Pair (v1, v_right))
        phi_sched phi_state phi_left
        heap_final v_final HSteps)
      as (HLeftNil & HStateSteps).
    destruct
      (StepsPhi_terminal_deterministic
        (StReturn (state_heap left) (Pair (v1, v_right)) KDone)
        phi_state heap_final v_final
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (state_heap left) (Pair (v1, v_right))
        (StepsStayNonPairParRun_return_kdone
          (state_heap left) (Pair (v1, v_right)))
        HStateSteps
        (StepsPhi_return_kdone
          (state_heap left) (Pair (v1, v_right))))
      as (_ & HHeapEq & HValEq).
    exists (state_heap left), v1.
    split.
    + rewrite HLeftNil.
      match goal with
      | HDone : StDone _ _ = left |- _ => rewrite <- HDone
      | HDone : left = StDone _ _ |- _ => rewrite HDone
      end.
      simpl. constructor.
    + split; assumption.
Qed.

Lemma PairParLooseLeftOnlyStepsPhi_terminal_decompose_kdone_agree :
  forall left right phi_sched phi_state phi_left heap_final v_final,
    state_heap left = state_heap right ->
    PairParLooseLeftOnlyStepsPhi
      (PPS_Run left right KDone)
      phi_sched
      phi_state
      phi_left
      (PPS_State (StDone heap_final v_final)) ->
    exists v_right heap_left v_left,
      right = StDone (state_heap left) v_right /\
      StepsPhi left phi_left (StDone heap_left v_left) /\
      heap_final = heap_left /\
      v_final = Pair (v_left, v_right).
Proof.
  intros left right phi_sched phi_state phi_left heap_final v_final
    HAgree HSteps.
  dependent induction HSteps generalizing left right heap_final v_final HAgree.
  - destruct
      (IHHSteps left' (with_state_heap (state_heap left') right)
        heap_final v_final)
      as (v_right & heap_left & v_left &
          HRightDoneEq & HLeftSteps & HHeapFinal & HValFinal).
    + rewrite state_heap_with_state_heap. reflexivity.
    + reflexivity.
    + reflexivity.
    + destruct right as
        [heap_right env_right rho_right e_right k_right
        | heap_right v_right0 k_right
        | heap_right v_right0
        | left_state right_state k_right];
        simpl in HRightDoneEq; inversion HRightDoneEq; subst.
      exists v_right, heap_left, v_left.
      split.
      * simpl in HAgree. subst heap_right. reflexivity.
      * split.
        -- eapply StepsPhi_Step; eauto.
        -- split; reflexivity.
  - destruct
      (PairParLooseLeftOnlyStepsPhi_state_return_kdone_terminal_steps
        heap (Pair (v1, v2))
        phi_sched phi_state phi_left
        heap_final v_final HSteps)
      as (HLeftNil & HStateSteps).
    destruct
      (StepsPhi_terminal_deterministic
        (StReturn heap (Pair (v1, v2)) KDone)
        phi_state heap_final v_final
        (Phi_Seq (label_phi Silent) Phi_Nil)
        heap (Pair (v1, v2))
        (StepsStayNonPairParRun_return_kdone heap (Pair (v1, v2)))
        HStateSteps
        (StepsPhi_return_kdone heap (Pair (v1, v2))))
      as (_ & HHeapEq & HValEq).
    exists v2, heap, v1.
    split.
    + reflexivity.
    + split.
      * rewrite HLeftNil. constructor.
      * split; assumption.
Qed.

Lemma PairParLooseRightThenLeftStepsPhi_terminal_decompose_kdone :
  forall left right phi_sched phi_state phi_left phi_right heap_final v_final,
    StateRunHeapsAgree left ->
    StateRunHeapsAgree right ->
    state_heap left = state_heap right ->
    PairParLooseRightThenLeftStepsPhi
      (PPS_Run left right KDone)
      phi_sched
      phi_state
      phi_left
      phi_right
      (PPS_State (StDone heap_final v_final)) ->
    exists heap_right v_right heap_left v_left,
      StepsPhi right phi_right (StDone heap_right v_right) /\
      StepsPhi
        (with_state_heap heap_right left)
        phi_left
        (StDone heap_left v_left) /\
      heap_final = heap_left /\
      v_final = Pair (v_left, v_right).
Proof.
  intros left right phi_sched phi_state phi_left phi_right heap_final v_final
    HLeftAgree HRightAgree HHeapAgree HSteps.
  dependent induction HSteps generalizing left right heap_final v_final
    HLeftAgree HRightAgree HHeapAgree.
  - destruct
      (PairParLooseLeftOnlyStepsPhi_terminal_decompose_kdone_agree
        left right phi_sched phi_state phi_left heap_final v_final
        HHeapAgree H)
      as (v_right & heap_left & v_left &
          HRightDone & HLeftSteps & HHeapFinal & HValFinal).
    exists (state_heap left), v_right, heap_left, v_left.
    split.
    + rewrite HRightDone. constructor.
    + split.
      * rewrite with_state_heap_state_heap_agree.
        -- exact HLeftSteps.
        -- exact HLeftAgree.
      * split; assumption.
  - destruct
      (IHHSteps
        (with_state_heap (state_heap right') left)
        right'
        heap_final
        v_final)
      as (heap_right & v_right & heap_left & v_left &
          HRightSteps & HLeftSteps & HHeapFinal & HValFinal).
    + apply StateRunHeapsAgree_with_state_heap. exact HLeftAgree.
    + eapply step_preserves_state_run_heaps_agree.
      * exact HRightAgree.
      * exact H.
    + rewrite state_heap_with_state_heap. reflexivity.
    + reflexivity.
    + reflexivity.
    + exists heap_right, v_right, heap_left, v_left.
      split.
      * eapply StepsPhi_Step; eauto.
      * split.
        -- rewrite with_state_heap_overwrite in HLeftSteps.
           exact HLeftSteps.
        -- split; assumption.
Qed.

Theorem PairParLoosePackedStepsPhi_terminal_decompose_kdone :
  forall left right phi_sched phi_state phi_left phi_right
    heap_final v_final theta_left theta_right,
    state_heap left = state_heap right ->
    StateRunHeapsAgree left ->
    StateRunHeapsAgree right ->
    PairParLoosePackedStepsPhi
      (PPS_Run left right KDone)
      phi_sched
      phi_state
      phi_left
      phi_right
      (PPS_State (StDone heap_final v_final)) ->
    phi_left ⋞ theta_left ->
    phi_right ⋞ theta_right ->
    PairParCheckPass theta_left theta_right ->
    exists heap_right v_right heap_left v_left,
      StepsPhi right phi_right (StDone heap_right v_right) /\
      StepsPhi
        (with_state_heap heap_right left)
        phi_left
        (StDone heap_left v_left) /\
      heap_final = heap_left /\
      v_final = Pair (v_left, v_right).
Proof.
  intros left right phi_sched phi_state phi_left phi_right
    heap_final v_final theta_left theta_right
    HHeapAgree HLeftAgree HRightAgree HSteps
    HSoundLeft HSoundRight HPass.
  destruct
    (PairParLoosePackedStepsPhi_normalize_right_then_left_kdone
      left right phi_sched phi_state phi_left phi_right
      heap_final v_final theta_left theta_right
      HHeapAgree HLeftAgree HRightAgree HSteps
      HSoundLeft HSoundRight HPass)
    as (phi_sched' & HNorm).
  eapply PairParLooseRightThenLeftStepsPhi_terminal_decompose_kdone;
    eauto.
Qed.

Theorem PairParLoosePackedCheckedTerminalBranchSteps :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_sched phi_state phi_left phi_right heap_final v_final
    theta_left theta_right,
    PairParLoosePackedStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_sched
      phi_state
      phi_left
      phi_right
      (PPS_State (StDone heap_final v_final)) ->
    phi_left ⋞ theta_left ->
    phi_right ⋞ theta_right ->
    PairParCheckPass theta_left theta_right ->
    exists heap_right v_right heap_left v_left,
      StepsPhi
        (initial_state heap env rho (Mu_App ef2 ea2))
        phi_right
        (StDone heap_right v_right) /\
      StepsPhi
        (with_state_heap heap_right
          (initial_state heap env rho (Mu_App ef1 ea1)))
        phi_left
        (StDone heap_left v_left) /\
      heap_final = heap_left /\
      v_final = Pair (v_left, v_right).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_sched phi_state phi_left phi_right heap_final v_final
    theta_left theta_right HSteps HSoundLeft HSoundRight HPass.
  unfold pairpar_checked_start, pairpar_checked_initial in HSteps.
  eapply PairParLoosePackedStepsPhi_terminal_decompose_kdone; eauto;
    simpl; try reflexivity; exact I.
Qed.

Lemma PairParLeftOnlyStepsPhi_terminal_decompose_kdone :
  forall left v_right phi_state phi_left heap_final v_final,
    PairParLeftOnlyStepsPhi
      (PPS_Run left (StDone (state_heap left) v_right) KDone)
      phi_state
      phi_left
	    (PPS_State (StDone heap_final v_final)) ->
	  exists heap_left v_left,
	      OrdinaryStepsPhi left phi_left (StDone heap_left v_left) /\
	      heap_final = heap_left /\
	      v_final = Pair (v_left, v_right).
Proof.
  intros left v_right phi_state phi_left heap_final v_final HSteps.
  dependent induction HSteps generalizing left v_right heap_final v_final.
  - destruct
      (IHHSteps left' v_right heap_final v_final)
      as (heap_left & v_left & HLeftSteps & HHeapFinal & HValFinal).
    + simpl. reflexivity.
    + reflexivity.
    + exists heap_left, v_left.
	      split.
	      * eapply OrdinaryStepsPhi_Step; eauto.
      * split; assumption.
  - destruct
	      (PairParLeftOnlyStepsPhi_state_as_stepsphi
	        (StReturn (state_heap left) (Pair (v1, v_right)) KDone)
	        phi_state phi_left
	        (PPS_State (StDone heap_final v_final)) HSteps)
		      as (HLeftNil & state_final & HStateFinal & HStateSteps).
    inversion HStateFinal; subst.
    destruct
      (StepsPhi_terminal_deterministic
        (StReturn (state_heap left) (Pair (v1, v_right)) KDone)
        phi_state heap_final v_final
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (state_heap left) (Pair (v1, v_right))
        (StepsStayNonPairParRun_return_kdone
          (state_heap left) (Pair (v1, v_right)))
        HStateSteps
        (StepsPhi_return_kdone
          (state_heap left) (Pair (v1, v_right))))
      as (_ & HHeapEq & HValEq).
    exists (state_heap left), v1.
    split.
    + rewrite <- x.
      constructor.
    + split; assumption.
Qed.

Lemma PairParLeftOnlyStepsPhi_terminal_decompose_kdone_agree :
  forall left right phi_state phi_left heap_final v_final,
    state_heap left = state_heap right ->
    PairParLeftOnlyStepsPhi
      (PPS_Run left right KDone)
      phi_state
      phi_left
      (PPS_State (StDone heap_final v_final)) ->
	    exists v_right heap_left v_left,
	      right = StDone (state_heap left) v_right /\
	      OrdinaryStepsPhi left phi_left (StDone heap_left v_left) /\
	      heap_final = heap_left /\
	      v_final = Pair (v_left, v_right).
Proof.
  intros left right phi_state phi_left heap_final v_final HAgree HSteps.
  dependent induction HSteps generalizing left right heap_final v_final HAgree.
  - destruct
      (IHHSteps left' (with_state_heap (state_heap left') right)
        heap_final v_final)
      as (v_right & heap_left & v_left &
          HRightDoneEq & HLeftSteps & HHeapFinal & HValFinal).
    + rewrite state_heap_with_state_heap. reflexivity.
    + reflexivity.
    + reflexivity.
    + destruct right as [heap_right env_right rho_right e_right k_right
                       | heap_right v_right0 k_right
                       | heap_right v_right0
                       | left_state right_state k_right].
      * simpl in HRightDoneEq. inversion HRightDoneEq.
      * simpl in HRightDoneEq. inversion HRightDoneEq.
      * simpl in HRightDoneEq. inversion HRightDoneEq; subst.
        exists v_right, heap_left, v_left.
        split.
        -- simpl in HAgree. subst heap_right. reflexivity.
	        -- split.
	           ++ eapply OrdinaryStepsPhi_Step; eauto.
           ++ split; reflexivity.
      * simpl in HRightDoneEq. inversion HRightDoneEq.
  - destruct
      (PairParLeftOnlyStepsPhi_state_as_stepsphi
        (StReturn heap (Pair (v1, v2)) KDone)
        phi_state phi_left
        (PPS_State (StDone heap_final v_final)) HSteps)
		      as (HLeftNil & state_final & HStateFinal & HStateSteps).
    inversion HStateFinal; subst.
    destruct
      (StepsPhi_terminal_deterministic
        (StReturn heap (Pair (v1, v2)) KDone)
        phi_state heap_final v_final
        (Phi_Seq (label_phi Silent) Phi_Nil)
        heap (Pair (v1, v2))
        (StepsStayNonPairParRun_return_kdone heap (Pair (v1, v2)))
        HStateSteps
        (StepsPhi_return_kdone
          heap (Pair (v1, v2))))
      as (_ & HHeapEq & HValEq).
    exists v2, heap, v1.
    split.
    + reflexivity.
    + split.
      * constructor.
      * split; assumption.
Qed.

Lemma PairParRightThenLeftStepsPhi_terminal_decompose_kdone :
  forall left right phi_state phi_left phi_right heap_final v_final,
    StateRunHeapsAgree left ->
    StateRunHeapsAgree right ->
    state_heap left = state_heap right ->
    PairParRightThenLeftStepsPhi
      (PPS_Run left right KDone)
      phi_state
      phi_left
      phi_right
      (PPS_State (StDone heap_final v_final)) ->
	  exists heap_right v_right heap_left v_left,
	      OrdinaryStepsPhi right phi_right (StDone heap_right v_right) /\
	      OrdinaryStepsPhi (with_state_heap heap_right left) phi_left
	        (StDone heap_left v_left) /\
	      heap_final = heap_left /\
	      v_final = Pair (v_left, v_right).
Proof.
  intros left right phi_state phi_left phi_right heap_final v_final
    HLeftAgree HRightAgree HAgree HSteps.
  dependent induction HSteps generalizing left right heap_final v_final
    HLeftAgree HRightAgree HAgree.
  - destruct
      (PairParLeftOnlyStepsPhi_terminal_decompose_kdone_agree
        left right phi_state phi_left heap_final v_final HAgree H)
      as (v_right & heap_left & v_left &
          HRightDone & HLeftSteps & HHeapFinal & HValFinal).
    exists (state_heap left), v_right, heap_left, v_left.
    split.
    + rewrite HRightDone. constructor.
    + split.
      * rewrite with_state_heap_state_heap_agree.
        -- exact HLeftSteps.
        -- exact HLeftAgree.
      * split; assumption.
  - destruct
      (IHHSteps
        (with_state_heap (state_heap right') left)
        right'
        heap_final
        v_final)
      as (heap_right & v_right & heap_left & v_left &
          HRightSteps & HLeftSteps & HHeapFinal & HValFinal).
    + apply StateRunHeapsAgree_with_state_heap. exact HLeftAgree.
    + eapply step_preserves_state_run_heaps_agree; eauto.
    + rewrite state_heap_with_state_heap. reflexivity.
    + reflexivity.
    + reflexivity.
    + exists heap_right, v_right, heap_left, v_left.
	      split.
	      * eapply OrdinaryStepsPhi_Step; eauto.
      * split.
        -- rewrite with_state_heap_overwrite in HLeftSteps.
           exact HLeftSteps.
        -- split; assumption.
Qed.

Lemma PairParLeftOnlyStepsPhi_terminal_decompose :
  forall left right k phi_state phi_left heap_final v_final,
    state_heap left = state_heap right ->
    PairParLeftOnlyStepsPhi
      (PPS_Run left right k)
      phi_state
      phi_left
      (PPS_State (StDone heap_final v_final)) ->
	    exists v_right heap_left v_left,
	      right = StDone (state_heap left) v_right /\
	      OrdinaryStepsPhi left phi_left (StDone heap_left v_left) /\
	      OrdinaryStepsPhi
	        (StReturn heap_left (Pair (v_left, v_right)) k)
        phi_state
        (StDone heap_final v_final).
Proof.
  intros left right k phi_state phi_left heap_final v_final HAgree HSteps.
  dependent induction HSteps generalizing left right k heap_final v_final HAgree.
  - destruct
      (IHHSteps left' (with_state_heap (state_heap left') right) k
        heap_final v_final)
      as (v_right & heap_left & v_left &
          HRightDoneEq & HLeftSteps & HTailSteps).
    + rewrite state_heap_with_state_heap. reflexivity.
    + reflexivity.
    + reflexivity.
    + destruct right as [heap_right env_right rho_right e_right k_right
                       | heap_right v_right0 k_right
                       | heap_right v_right0
                       | left_state right_state k_right].
      * simpl in HRightDoneEq. inversion HRightDoneEq.
      * simpl in HRightDoneEq. inversion HRightDoneEq.
      * simpl in HRightDoneEq. inversion HRightDoneEq; subst.
        exists v_right, heap_left, v_left.
        split.
        -- simpl in HAgree. subst heap_right. reflexivity.
	        -- split.
	           ++ eapply OrdinaryStepsPhi_Step; eauto.
           ++ exact HTailSteps.
      * simpl in HRightDoneEq. inversion HRightDoneEq.
  - destruct
		      (PairParStepsPhi_state_as_ordinary_stepsphi
		        (StReturn heap (Pair (v1, v2)) k)
		        phi_state phi_left Phi_Nil
			        (PPS_State (StDone heap_final v_final))
		        (PairParLeftOnlyStepsPhi_as_pairpar_steps_phi
		          (PPS_State (StReturn heap (Pair (v1, v2)) k))
		          phi_state phi_left
		          (PPS_State (StDone heap_final v_final)) HSteps))
	      as (HLeftNil & HRightNil & state_final & HStateFinal & HStateSteps).
    inversion HStateFinal; subst.
    exists v2, heap, v1.
    split.
    + reflexivity.
    + split.
      * constructor.
      * exact HStateSteps.
Qed.

Lemma PairParRightThenLeftStepsPhi_terminal_decompose :
  forall left right k phi_state phi_left phi_right heap_final v_final,
    StateRunHeapsAgree left ->
    StateRunHeapsAgree right ->
    state_heap left = state_heap right ->
    PairParRightThenLeftStepsPhi
      (PPS_Run left right k)
      phi_state
      phi_left
      phi_right
      (PPS_State (StDone heap_final v_final)) ->
	  exists heap_right v_right heap_left v_left,
	      OrdinaryStepsPhi right phi_right (StDone heap_right v_right) /\
	      OrdinaryStepsPhi (with_state_heap heap_right left) phi_left
	        (StDone heap_left v_left) /\
	      OrdinaryStepsPhi
	        (StReturn heap_left (Pair (v_left, v_right)) k)
        phi_state
        (StDone heap_final v_final).
Proof.
  intros left right k phi_state phi_left phi_right heap_final v_final
    HLeftAgree HRightAgree HAgree HSteps.
  dependent induction HSteps generalizing left right k heap_final v_final
    HLeftAgree HRightAgree HAgree.
  - destruct
      (PairParLeftOnlyStepsPhi_terminal_decompose
        left right k phi_state phi_left heap_final v_final HAgree H)
      as (v_right & heap_left & v_left &
          HRightDone & HLeftSteps & HTailSteps).
    exists (state_heap left), v_right, heap_left, v_left.
    split.
    + rewrite HRightDone. constructor.
    + split.
      * rewrite with_state_heap_state_heap_agree.
        -- exact HLeftSteps.
        -- exact HLeftAgree.
      * exact HTailSteps.
  - destruct
      (IHHSteps
        (with_state_heap (state_heap right') left)
        right'
        k
        heap_final
        v_final)
      as (heap_right & v_right & heap_left & v_left &
          HRightSteps & HLeftSteps & HTailSteps).
    + apply StateRunHeapsAgree_with_state_heap. exact HLeftAgree.
    + eapply step_preserves_state_run_heaps_agree; eauto.
    + rewrite state_heap_with_state_heap. reflexivity.
    + reflexivity.
    + reflexivity.
    + exists heap_right, v_right, heap_left, v_left.
	      split.
	      * eapply OrdinaryStepsPhi_Step; eauto.
      * split.
        -- rewrite with_state_heap_overwrite in HLeftSteps.
           exact HLeftSteps.
        -- exact HTailSteps.
Qed.

Lemma Phi_Theta_Soundness_seq_inv_l :
  forall phi1 phi2 theta,
    Phi_Seq phi1 phi2 ⋞ theta ->
    phi1 ⋞ theta.
Proof.
  intros phi1 phi2 theta HSound.
  inversion HSound; subst; assumption.
Qed.

Lemma Phi_Theta_Soundness_seq_inv_r :
  forall phi1 phi2 theta,
    Phi_Seq phi1 phi2 ⋞ theta ->
    phi2 ⋞ theta.
Proof.
  intros phi1 phi2 theta HSound.
  inversion HSound; subst; assumption.
Qed.

Lemma PairParRightThenLeftStepsPhi_prepend_left :
  forall left right k label left' phi_state phi_left phi_right final_state
    theta_left theta_right,
    state_heap left = state_heap right ->
    NonPairParRunState left ->
    NonPairParRunState right ->
    NonPairParRunState left' ->
    Step left label left' ->
    label_phi label ⋞ theta_left ->
    phi_right ⋞ theta_right ->
    PairParCheckPass theta_left theta_right ->
    PairParRightThenLeftStepsPhi
      (PPS_Run left' (with_state_heap (state_heap left') right) k)
      phi_state phi_left phi_right final_state ->
    PairParRightThenLeftStepsPhi
      (PPS_Run left right k)
      phi_state
      (Phi_Seq (label_phi label) phi_left)
      phi_right
      final_state.
Proof.
  intros left right k label left' phi_state phi_left phi_right final_state
    theta_left theta_right HHeapAgree HNonPairLeft HNonPairRight
    HNonPairLeft' HStepLeft HSoundLeft HSoundRight HPass HRTL.
  remember
    (PPS_Run left' (with_state_heap (state_heap left') right) k)
    as rest_start eqn:HRestStart.
  revert left right k label left'
    HHeapAgree HNonPairLeft HNonPairRight
    HNonPairLeft' HStepLeft HSoundLeft HRestStart.
  induction HRTL;
    intros left0 right0 k0 label0 left0'
      HHeapAgree HNonPairLeft HNonPairRight
      HNonPairLeft' HStepLeft HSoundLeft HRestStart;
    inversion HRestStart; subst.
	  - apply PPRTL_LeftOnly.
	    eapply PPLO_Left.
	    + exact HNonPairLeft.
	    + exact HNonPairLeft'.
	    + exact HStepLeft.
	    + assumption.
  - pose proof
      (Phi_Theta_Soundness_seq_inv_l
        (label_phi label) phi_right theta_right HSoundRight)
      as HSoundRightHead.
    pose proof
      (Phi_Theta_Soundness_seq_inv_r
        (label_phi label) phi_right theta_right HSoundRight)
      as HSoundRightTail.
    destruct HPass as [HDisjointTheta HNoConflictTheta].
    assert (HStable :
      LabelAllocReflectionStable label label0).
    {
      eapply LabelAllocReflectionStable_from_theta; eauto.
    }
    assert (HDisjointLR :
      Disjoint_Traces (label_trace label0) (label_trace label)).
    {
      rewrite <- (phi_as_list_label_phi label0).
      rewrite <- (phi_as_list_label_phi label).
      eapply PairParCheckPass_sound_disjoint_traces; eauto.
      split; assumption.
    }
    assert (HDisjointRL :
      Disjoint_Traces (label_trace label) (label_trace label0)).
    {
      rewrite <- (phi_as_list_label_phi label).
      rewrite <- (phi_as_list_label_phi label0).
      eapply PairParCheckPass_sound_disjoint_traces_sym; eauto.
      split; assumption.
    }
	    destruct
		      (PairParLeftRightActualStep_local_diamond
		        left0 right0 label0 label left0' right'
		        HHeapAgree HNonPairLeft HNonPairRight
		        H0 HStepLeft H1 HStable HDisjointLR HDisjointRL)
	      as (right0' & HStepRight0 & HStepLeftAfterRight &
	          HRightAfterRebase & HNonPairRight0').
		    apply PPRTL_Right with (right' := right0').
		    + exact HNonPairRight.
		    + exact HNonPairRight0'.
		    + exact HStepRight0.
	    + eapply
	        (IHHRTL HSoundRightTail
		          (with_state_heap (state_heap right0') left0)
		          right0' k0 label0
		          (with_state_heap (state_heap right') left0')).
	      * rewrite state_heap_with_state_heap. reflexivity.
	      * apply with_state_heap_non_pairpar. exact HNonPairLeft.
	      * exact HNonPairRight0'.
	      * apply with_state_heap_non_pairpar. exact HNonPairLeft'.
	      * exact HStepLeftAfterRight.
	      * exact HSoundLeft.
      * rewrite state_heap_with_state_heap.
        rewrite <- HRightAfterRebase.
        reflexivity.
Qed.

Lemma PairParStepsPhi_normalize_right_then_left :
  forall state phi_state phi_left phi_right final_state theta_left theta_right,
    PairParRunHeapsAgree state ->
    PairParRunBranchesOrdinary state ->
    PairParStepsPhi state phi_state phi_left phi_right final_state ->
    phi_left ⋞ theta_left ->
    phi_right ⋞ theta_right ->
    PairParCheckPass theta_left theta_right ->
    PairParRightThenLeftStepsPhi
      state phi_state phi_left phi_right final_state.
Proof.
  intros state phi_state phi_left phi_right final_state theta_left theta_right
    HAgree HOrdinary HSteps.
  induction HSteps;
    intros HSoundLeft HSoundRight HPass.
  - apply PPRTL_LeftOnly. constructor.
  - assert (HWhole :
      PairParStepsPhi
        (PPS_State state)
        (Phi_Seq (label_phi label) phi_state)
        phi_left
        phi_right
        state'').
    {
      eapply PairParStepsPhi_State; eauto.
    }
    pose proof
      (PairParStepsPhi_state_branches_nil
        state (Phi_Seq (label_phi label) phi_state)
        phi_left phi_right state'' HWhole)
      as [HLeftNil HRightNil].
    subst.
    apply PPRTL_LeftOnly.
    apply PPLO_State.
    exact HWhole.
  - pose proof
      (Phi_Theta_Soundness_seq_inv_l
        (label_phi label) phi_left theta_left HSoundLeft)
      as HSoundLabel.
	  pose proof
	      (Phi_Theta_Soundness_seq_inv_r
	        (label_phi label) phi_left theta_left HSoundLeft)
		      as HSoundLeftTail.
		    destruct HOrdinary as [HNonPairLeft HNonPairRight].
		    destruct HAgree as [HHeapAgree [HLeftAgree HRightAgree]].
		    eapply PairParRightThenLeftStepsPhi_prepend_left.
		    + exact HHeapAgree.
		    + exact HNonPairLeft.
		    + exact HNonPairRight.
		    + exact H0.
		    + exact H1.
		    + exact HSoundLabel.
		    + exact HSoundRight.
		    + exact HPass.
		    + apply IHHSteps.
		      * simpl.
		        split.
			        -- rewrite state_heap_with_state_heap. reflexivity.
			        -- split.
		           ++ eapply step_preserves_state_run_heaps_agree.
			              ** exact HLeftAgree.
			              ** exact H1.
			           ++ apply StateRunHeapsAgree_with_state_heap.
			              exact HRightAgree.
		      * split.
		        -- exact H0.
		        -- apply with_state_heap_non_pairpar. exact HNonPairRight.
		      * exact HSoundLeftTail.
		      * exact HSoundRight.
		      * exact HPass.
	  - eapply PPRTL_Right.
	    + exact H.
	    + exact H0.
	    + exact H1.
	    + apply IHHSteps.
	      * destruct HAgree as [HHeapAgree [HLeftAgree HRightAgree]].
	        simpl.
	        split.
		        -- rewrite state_heap_with_state_heap. reflexivity.
		        -- split.
		           ++ apply StateRunHeapsAgree_with_state_heap.
		              exact HLeftAgree.
			           ++ eapply step_preserves_state_run_heaps_agree.
			              ** exact HRightAgree.
			              ** exact H1.
		      * destruct HOrdinary as [HNonPairLeft HNonPairRight].
			        split.
			        -- apply with_state_heap_non_pairpar. exact HNonPairLeft.
			        -- exact H0.
	      * exact HSoundLeft.
	      * eapply Phi_Theta_Soundness_seq_inv_r; eauto.
      * exact HPass.
  - pose proof
      (PairParStepsPhi_state_branches_nil
        (StReturn heap (Pair (v1, v2)) k)
        phi_state phi_left phi_right state'' HSteps)
      as [HLeftNil HRightNil].
    subst.
    apply PPRTL_LeftOnly.
    eapply PPLO_Done.
    apply PPLO_State.
    exact HSteps.
Qed.

Theorem PairParCheckedArbitraryScheduleTerminalDeterminism :
	  forall heap env rho ef1 ea1 ef2 ea2
	    phi_state1 phi_left1 phi_right1
	    phi_state2 phi_left2 phi_right2
	    heap1 heap2 v1 v2
	    theta_left1 theta_right1 theta_left2 theta_right2,
	    PairParCheckPass theta_left1 theta_right1 ->
	    PairParCheckPass theta_left2 theta_right2 ->
	    phi_left1 ⋞ theta_left1 ->
	    phi_right1 ⋞ theta_right1 ->
	    phi_left2 ⋞ theta_left2 ->
	    phi_right2 ⋞ theta_right2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_state1
      phi_left1
      phi_right1
      (PPS_State (StDone heap1 v1)) ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_state2
      phi_left2
      phi_right2
      (PPS_State (StDone heap2 v2)) ->
    heap1 = heap2 /\ v1 = v2.
Proof.
	  intros heap env rho ef1 ea1 ef2 ea2
	    phi_state1 phi_left1 phi_right1
	    phi_state2 phi_left2 phi_right2
	    heap1 heap2 v1 v2
	    theta_left1 theta_right1 theta_left2 theta_right2
	    HPass1 HPass2 HSoundLeft1 HSoundRight1 HSoundLeft2 HSoundRight2
	    HSteps1 HSteps2.
	  assert (HAgreeStart :
	    PairParRunHeapsAgree
	      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)).
		  {
		    unfold pairpar_checked_start, pairpar_checked_initial.
		    simpl. split; [reflexivity | split; exact I].
		  }
	  assert (HOrdStart :
	    PairParRunBranchesOrdinary
	      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)).
	  {
	    unfold pairpar_checked_start, pairpar_checked_initial.
	    simpl. split; exact I.
	  }
	  pose proof
	    (PairParStepsPhi_normalize_right_then_left
	      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
		      phi_state1 phi_left1 phi_right1
		      (PPS_State (StDone heap1 v1))
		      theta_left1 theta_right1
		      HAgreeStart HOrdStart HSteps1 HSoundLeft1 HSoundRight1 HPass1)
    as HRTL1.
  pose proof
    (PairParStepsPhi_normalize_right_then_left
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
		      phi_state2 phi_left2 phi_right2
		      (PPS_State (StDone heap2 v2))
		      theta_left2 theta_right2
		      HAgreeStart HOrdStart HSteps2 HSoundLeft2 HSoundRight2 HPass2)
    as HRTL2.
  unfold pairpar_checked_start, pairpar_checked_initial in HRTL1, HRTL2.
  destruct
    (PairParRightThenLeftStepsPhi_terminal_decompose_kdone
	      (initial_state heap env rho (Mu_App ef1 ea1))
	      (initial_state heap env rho (Mu_App ef2 ea2))
	      phi_state1 phi_left1 phi_right1 heap1 v1
	      I I eq_refl HRTL1)
    as (heap_right1 & v_right1 & heap_left1 & v_left1 &
        HRightSteps1 & HLeftSteps1 & HHeapFinal1 & HValFinal1).
  destruct
    (PairParRightThenLeftStepsPhi_terminal_decompose_kdone
	      (initial_state heap env rho (Mu_App ef1 ea1))
	      (initial_state heap env rho (Mu_App ef2 ea2))
	      phi_state2 phi_left2 phi_right2 heap2 v2
	      I I eq_refl HRTL2)
    as (heap_right2 & v_right2 & heap_left2 & v_left2 &
        HRightSteps2 & HLeftSteps2 & HHeapFinal2 & HValFinal2).
	  destruct
	    (OrdinaryStepsPhi_terminal_deterministic
	      (initial_state heap env rho (Mu_App ef2 ea2))
	      phi_right1 heap_right1 v_right1
	      phi_right2 heap_right2 v_right2
	      HRightSteps1 HRightSteps2)
    as (_ & HRightHeapEq & HRightValEq).
  subst heap_right2 v_right2.
	  destruct
	    (OrdinaryStepsPhi_terminal_deterministic
	      (with_state_heap heap_right1
	        (initial_state heap env rho (Mu_App ef1 ea1)))
	      phi_left1 heap_left1 v_left1
	      phi_left2 heap_left2 v_left2
	      HLeftSteps1 HLeftSteps2)
    as (_ & HLeftHeapEq & HLeftValEq).
  subst heap_left2 v_left2.
  subst heap1 heap2 v1 v2.
  split; reflexivity.
Qed.

Theorem PairParCheckedArbitraryScheduleContinuationTerminalDeterminism :
	  forall heap env rho ef1 ea1 ef2 ea2 k
	    phi_state1 phi_left1 phi_right1
	    phi_state2 phi_left2 phi_right2
	    heap1 heap2 v1 v2
	    theta_left1 theta_right1 theta_left2 theta_right2,
	    PairParCheckPass theta_left1 theta_right1 ->
	    PairParCheckPass theta_left2 theta_right2 ->
	    phi_left1 ⋞ theta_left1 ->
	    phi_right1 ⋞ theta_right1 ->
	    phi_left2 ⋞ theta_left2 ->
	    phi_right2 ⋞ theta_right2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi_state1
      phi_left1
      phi_right1
      (PPS_State (StDone heap1 v1)) ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi_state2
      phi_left2
      phi_right2
      (PPS_State (StDone heap2 v2)) ->
    heap1 = heap2 /\ v1 = v2.
Proof.
	  intros heap env rho ef1 ea1 ef2 ea2 k
	    phi_state1 phi_left1 phi_right1
	    phi_state2 phi_left2 phi_right2
	    heap1 heap2 v1 v2
	    theta_left1 theta_right1 theta_left2 theta_right2
	    HPass1 HPass2 HSoundLeft1 HSoundRight1 HSoundLeft2 HSoundRight2
	    HSteps1 HSteps2.
	  assert (HAgreeStart :
	    PairParRunHeapsAgree
	      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)).
		  {
		    unfold pairpar_checked_start, pairpar_checked_initial.
		    simpl. split; [reflexivity | split; exact I].
		  }
	  assert (HOrdStart :
	    PairParRunBranchesOrdinary
	      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)).
	  {
	    unfold pairpar_checked_start, pairpar_checked_initial.
	    simpl. split; exact I.
	  }
	  pose proof
	    (PairParStepsPhi_normalize_right_then_left
	      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
		      phi_state1 phi_left1 phi_right1
		      (PPS_State (StDone heap1 v1))
		      theta_left1 theta_right1
		      HAgreeStart HOrdStart HSteps1 HSoundLeft1 HSoundRight1 HPass1)
    as HRTL1.
  pose proof
    (PairParStepsPhi_normalize_right_then_left
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
		      phi_state2 phi_left2 phi_right2
		      (PPS_State (StDone heap2 v2))
		      theta_left2 theta_right2
		      HAgreeStart HOrdStart HSteps2 HSoundLeft2 HSoundRight2 HPass2)
    as HRTL2.
  unfold pairpar_checked_start, pairpar_checked_initial in HRTL1, HRTL2.
  destruct
    (PairParRightThenLeftStepsPhi_terminal_decompose
	      (initial_state heap env rho (Mu_App ef1 ea1))
	      (initial_state heap env rho (Mu_App ef2 ea2))
	      k phi_state1 phi_left1 phi_right1 heap1 v1
	      I I eq_refl HRTL1)
    as (heap_right1 & v_right1 & heap_left1 & v_left1 &
        HRightSteps1 & HLeftSteps1 & HTailSteps1).
  destruct
    (PairParRightThenLeftStepsPhi_terminal_decompose
	      (initial_state heap env rho (Mu_App ef1 ea1))
	      (initial_state heap env rho (Mu_App ef2 ea2))
	      k phi_state2 phi_left2 phi_right2 heap2 v2
	      I I eq_refl HRTL2)
    as (heap_right2 & v_right2 & heap_left2 & v_left2 &
        HRightSteps2 & HLeftSteps2 & HTailSteps2).
	  destruct
	    (OrdinaryStepsPhi_terminal_deterministic
	      (initial_state heap env rho (Mu_App ef2 ea2))
	      phi_right1 heap_right1 v_right1
	      phi_right2 heap_right2 v_right2
	      HRightSteps1 HRightSteps2)
    as (_ & HRightHeapEq & HRightValEq).
  subst heap_right2 v_right2.
	  destruct
	    (OrdinaryStepsPhi_terminal_deterministic
	      (with_state_heap heap_right1
	        (initial_state heap env rho (Mu_App ef1 ea1)))
	      phi_left1 heap_left1 v_left1
	      phi_left2 heap_left2 v_left2
	      HLeftSteps1 HLeftSteps2)
    as (_ & HLeftHeapEq & HLeftValEq).
  subst heap_left2 v_left2.
	  destruct
	    (OrdinaryStepsPhi_terminal_deterministic
	      (StReturn heap_left1 (Pair (v_left1, v_right1)) k)
	      phi_state1 heap1 v1
	      phi_state2 heap2 v2
	      HTailSteps1 HTailSteps2)
    as (_ & HFinalHeapEq & HFinalValEq).
  split; assumption.
Qed.

Theorem PairParCheckedPackedArbitraryScheduleTerminalDeterminism :
  forall heap env rho ef1 ea1 ef2 ea2
    phi1 phi2 heap1 heap2 v1 v2
    theta_left1 theta_right1 theta_left2 theta_right2,
    PairParCheckPass theta_left1 theta_right1 ->
    PairParCheckPass theta_left2 theta_right2 ->
    PairParCheckedPackedStepsPhi theta_left1 theta_right1
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi1
      (PPS_State (StDone heap1 v1)) ->
    PairParCheckedPackedStepsPhi theta_left2 theta_right2
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi2
      (PPS_State (StDone heap2 v2)) ->
    heap1 = heap2 /\ v1 = v2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi1 phi2 heap1 heap2 v1 v2
    theta_left1 theta_right1 theta_left2 theta_right2
    HPass1 HPass2 HSteps1 HSteps2.
  destruct
    (PairParCheckedPackedStepsPhi_unpacked
      theta_left1 theta_right1
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi1
      (PPS_State (StDone heap1 v1)) HSteps1)
    as (phi_state1 & phi_left1 & phi_right1 &
        HRawSteps1 & _ & HSoundLeft1 & HSoundRight1).
  destruct
    (PairParCheckedPackedStepsPhi_unpacked
      theta_left2 theta_right2
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi2
      (PPS_State (StDone heap2 v2)) HSteps2)
    as (phi_state2 & phi_left2 & phi_right2 &
        HRawSteps2 & _ & HSoundLeft2 & HSoundRight2).
  eapply
    (PairParCheckedArbitraryScheduleTerminalDeterminism
      heap env rho ef1 ea1 ef2 ea2
      phi_state1 phi_left1 phi_right1
      phi_state2 phi_left2 phi_right2
      heap1 heap2 v1 v2
      theta_left1 theta_right1 theta_left2 theta_right2);
    eauto.
Qed.

Theorem PairParCheckedPackedArbitraryScheduleContinuationTerminalDeterminism :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi1 phi2 heap1 heap2 v1 v2
    theta_left1 theta_right1 theta_left2 theta_right2,
    PairParCheckPass theta_left1 theta_right1 ->
    PairParCheckPass theta_left2 theta_right2 ->
    PairParCheckedPackedStepsPhi theta_left1 theta_right1
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi1
      (PPS_State (StDone heap1 v1)) ->
    PairParCheckedPackedStepsPhi theta_left2 theta_right2
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi2
      (PPS_State (StDone heap2 v2)) ->
    heap1 = heap2 /\ v1 = v2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi1 phi2 heap1 heap2 v1 v2
    theta_left1 theta_right1 theta_left2 theta_right2
    HPass1 HPass2 HSteps1 HSteps2.
  destruct
    (PairParCheckedPackedStepsPhi_unpacked
      theta_left1 theta_right1
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi1
      (PPS_State (StDone heap1 v1)) HSteps1)
    as (phi_state1 & phi_left1 & phi_right1 &
        HRawSteps1 & _ & HSoundLeft1 & HSoundRight1).
  destruct
    (PairParCheckedPackedStepsPhi_unpacked
      theta_left2 theta_right2
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi2
      (PPS_State (StDone heap2 v2)) HSteps2)
    as (phi_state2 & phi_left2 & phi_right2 &
        HRawSteps2 & _ & HSoundLeft2 & HSoundRight2).
  eapply
    (PairParCheckedArbitraryScheduleContinuationTerminalDeterminism
      heap env rho ef1 ea1 ef2 ea2 k
      phi_state1 phi_left1 phi_right1
      phi_state2 phi_left2 phi_right2
      heap1 heap2 v1 v2
      theta_left1 theta_right1 theta_left2 theta_right2);
    eauto.
Qed.

Inductive ScheduledCheckedTerminal :
  State -> Phi -> Heap -> Val -> Prop :=
| ScheduledCheckedTerminal_Done :
    forall heap v,
      ScheduledCheckedTerminal (StDone heap v) Phi_Nil heap v
| ScheduledCheckedTerminal_Step :
    forall state label state' phi heap_final v_final,
      NotPairParEvalState state ->
      Step state label state' ->
      ScheduledCheckedTerminal state' phi heap_final v_final ->
      ScheduledCheckedTerminal
        state
        (Phi_Seq (label_phi label) phi)
        heap_final
        v_final
| ScheduledCheckedTerminal_CheckedPairPar :
    forall heap env rho ef1 ea1 ef2 ea2 k
      phi_eff1 phi_eff2 phi_pair phi_tail phi_left phi_right
      heap_eff1 heap_eff2 theta1 theta2
      heap_right v_right heap_left v_left
      heap_final v_final,
      ScheduledCheckedTerminal
        (initial_state heap env rho (Eff_App ef1 ea1))
        phi_eff1
        heap_eff1
        (Eff theta1) ->
	      ScheduledCheckedTerminal
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
      ScheduledCheckedTerminal
        (initial_state heap_eff2 env rho (Mu_App ef2 ea2))
        phi_right
        heap_right
        v_right ->
      ScheduledCheckedTerminal
        (with_state_heap heap_right
          (initial_state heap_eff2 env rho (Mu_App ef1 ea1)))
        phi_left
        heap_left
        v_left ->
      ScheduledCheckedTerminal
        (StReturn heap_left (Pair (v_left, v_right)) k)
        phi_tail
        heap_final
        v_final ->
      ScheduledCheckedTerminal
        (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
        (pairpar_checked_packed_structured_trace
          phi_eff1 phi_eff2 (Phi_Seq phi_pair phi_tail))
        heap_final
        v_final.

Lemma ScheduledCheckedTerminal_start_non_pairpar :
  forall state phi heap v,
    ScheduledCheckedTerminal state phi heap v ->
    NonPairParRunState state.
Proof.
  intros state phi heap v HRun.
  inversion HRun; subst; simpl; auto.
  eapply NotPairParEvalState_non_pairpar_run; eauto.
Qed.

Theorem ScheduledCheckedTerminal_as_steps :
  forall state phi heap v,
    ScheduledCheckedTerminal state phi heap v ->
    Steps state (phi_as_list phi) (StDone heap v).
Proof.
  intros state phi heap v HRun.
  induction HRun as
    [heap v
    | state label state' phi heap_final v_final
        _ HStep _ IH
    | heap env rho ef1 ea1 ef2 ea2 k
        phi_eff1 phi_eff2 phi_pair phi_tail phi_left phi_right
        heap_eff1 heap_eff2 theta1 theta2
        heap_right v_right heap_left v_left
        heap_final v_final
        HSummary1 IHSummary1
	        HSummary2 IHSummary2
	        HObserved HLoose
	        _ _ _ _ _ IHTail].
  - simpl. constructor.
  - simpl.
    rewrite phi_as_list_label_phi.
    econstructor; eauto.
  - assert
      (HSummary1Phi :
        exists phi_eff1_steps,
          StepsPhi
            (pairpar_effect_summary_state heap env rho ef1 ea1)
            phi_eff1_steps
            (StDone heap_eff1 (Eff theta1)) /\
          phi_as_list phi_eff1_steps = phi_as_list phi_eff1).
    {
      apply steps_as_StepsPhi. exact IHSummary1.
    }
    assert
      (HSummary2Phi :
        exists phi_eff2_steps,
          StepsPhi
            (pairpar_effect_summary_state heap_eff1 env rho ef2 ea2)
            phi_eff2_steps
            (StDone heap_eff2 (Eff theta2)) /\
          phi_as_list phi_eff2_steps = phi_as_list phi_eff2).
    {
      apply steps_as_StepsPhi. exact IHSummary2.
    }
    destruct HSummary1Phi as (phi_eff1_steps & HSummary1Steps & HTraceEff1).
    destruct HSummary2Phi as (phi_eff2_steps & HSummary2Steps & HTraceEff2).
    assert
      (HSummary :
        PairParSourceOrderedEffectSummaryStepsPhi
          heap env rho ef1 ea1 ef2 ea2
          phi_eff1_steps phi_eff2_steps
          heap_eff1 theta1 heap_eff2 theta2).
    {
      constructor.
      - exact HSummary1Steps.
      - exact HSummary2Steps.
    }
	    destruct
	      HObserved as [HPass _].
	    destruct
	      (PairParSourceOrderedEffectSummaryStepsPhi_source_pass_prefix
	        heap env rho ef1 ea1 ef2 ea2 k
	        phi_eff1_steps phi_eff2_steps
        heap_eff1 theta1 heap_eff2 theta2
        HSummary HPass)
      as (phi_source & HSource & HSourceTrace).
    pose proof
      (PairParLoosePackedStepsPhi_as_stepsphi
        (pairpar_checked_start heap_eff2 env rho ef1 ea1 ef2 ea2 k)
        phi_pair Phi_Nil phi_left phi_right
        (PPS_State
          (StReturn heap_left (Pair (v_left, v_right)) k))
        (pairpar_checked_initial_heaps_agree
          heap_eff2 env rho ef1 ea1 ef2 ea2 k)
        HLoose)
      as HPairStepsPhi.
    pose proof (StepsPhi_as_steps _ _ _ HSource) as HSourceSteps.
    pose proof (StepsPhi_as_steps _ _ _ HPairStepsPhi) as HPairSteps.
    unfold pairpar_checked_packed_structured_trace.
    simpl.
	    replace
	      ((phi_as_list phi_eff1 ++ phi_as_list phi_eff2) ++
	        (phi_as_list phi_pair ++ phi_as_list phi_tail))
	      with
	      (phi_as_list phi_source ++
	        (phi_as_list phi_pair ++ phi_as_list phi_tail)).
    + eapply
        (steps_trans
          (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
          (phi_as_list phi_source)
          (pairpar_checked_run_start
            heap_eff2 env rho ef1 ea1 ef2 ea2 k)
          (phi_as_list phi_pair ++ phi_as_list phi_tail)
          (StDone heap_final v_final)).
      * exact HSourceSteps.
      * eapply steps_trans.
        -- change
             (pairpar_checked_run_start
               heap_eff2 env rho ef1 ea1 ef2 ea2 k)
             with
             (pairpar_state_as_state
               (pairpar_checked_start
                 heap_eff2 env rho ef1 ea1 ef2 ea2 k)).
           exact HPairSteps.
        -- exact IHTail.
	    + rewrite HSourceTrace.
	      rewrite HTraceEff1.
	      rewrite HTraceEff2.
	      repeat rewrite app_assoc.
	      reflexivity.
Qed.

Theorem ScheduledCheckedTerminal_deterministic :
  forall state phi1 heap1 v1 phi2 heap2 v2,
    ScheduledCheckedTerminal state phi1 heap1 v1 ->
    ScheduledCheckedTerminal state phi2 heap2 v2 ->
    heap1 = heap2 /\ v1 = v2.
Proof.
  intros state phi1 heap1 v1 phi2 heap2 v2 HRun1.
  revert phi2 heap2 v2.
  induction HRun1 as
    [heap v
    | state label state' phi heap_final v_final
        HNotPair HStep _ IH
    | heap env rho ef1 ea1 ef2 ea2 k
        phi_eff1 phi_eff2 phi_mu phi_state phi_left phi_right
        heap_eff1 heap_eff2 theta1 theta2
        heap_right v_right heap_left v_left
        heap_final v_final
        HSummary1 IHSummary1
        HSummary2 IHSummary2
        _HPass _HLoose
        HRight IHRight
        HLeft IHLeft
        HTail IHTail];
    intros phi2 heap2 v2 HRun2.
  - inversion HRun2; subst.
    + split; reflexivity.
    + exfalso. eapply done_no_step; eauto.
  - inversion HRun2; subst; simpl in *.
    + exfalso. eapply done_no_step; eauto.
    + destruct
        (step_deterministic
          state label state' label0 state'0
          (NotPairParEvalState_non_pairpar_run state HNotPair)
          HStep H0)
        as (_ & HStateEq).
      subst.
      eapply IH; eauto.
    + contradiction.
  - inversion HRun2 as
      [heap_done2 v_done2
      | state2 label2 state2' phi_tail2 heap_final2 v_final2
          HNotPair2 HStep2 HRunTail2
      | heap_b env_b rho_b ef1_b ea1_b ef2_b ea2_b k_b
          phi_eff1_b phi_eff2_b phi_mu_b phi_state_b
          phi_left_b phi_right_b
          heap_eff1_b heap_eff2_b theta1_b theta2_b
          heap_right_b v_right_b heap_left_b v_left_b
          heap_final_b v_final_b
          HSummary1_b HSummary2_b _HPass_b _HLoose_b
          HRight_b HLeft_b HTail_b];
      subst; simpl in *; try contradiction.
    destruct
      (IHSummary1 phi_eff1_b heap_eff1_b (Eff theta1_b) HSummary1_b)
      as [HHeapEff1 HValEff1].
    inversion HValEff1; subst.
    destruct
      (IHSummary2 phi_eff2_b heap_eff2_b (Eff theta2_b) HSummary2_b)
      as [HHeapEff2 HValEff2].
    inversion HValEff2; subst.
    destruct
      (IHRight phi_right_b heap_right_b v_right_b HRight_b)
      as [HHeapRight HValRight].
    subst heap_right_b v_right_b.
    destruct
      (IHLeft phi_left_b heap_left_b v_left_b HLeft_b)
      as [HHeapLeft HValLeft].
    subst heap_left_b v_left_b.
    eapply IHTail; eauto.
Qed.

Theorem ScheduledStepsPhi_terminal_deterministic :
  forall state phi1 heap1 v1 phi2 heap2 v2,
    ScheduledStepsPhi state phi1 (StDone heap1 v1) ->
    ScheduledStepsPhi state phi2 (StDone heap2 v2) ->
    heap1 = heap2 /\ v1 = v2.
Proof.
  intros state phi1 heap1 v1 phi2 heap2 v2 HSteps1.
  remember (StDone heap1 v1) as done1 eqn:HDone1.
  revert heap1 v1 HDone1 phi2 heap2 v2.
  induction HSteps1 as
    [state
    | state label state' phi state'' HNotPair HStep _ IH
    | heap env rho ef1 ea1 ef2 ea2 k
        phi_eff1 phi_eff2 heap_eff1 heap_eff2 theta1 theta2
        phi_mu state' HSummary HPass HChecked].
  - intros heap1 v1 HDone1 phi2 heap2 v2 HSteps2.
    subst.
    inversion HSteps2; subst.
    + split; reflexivity.
    + exfalso. eapply done_no_step; eauto.
  - intros heap1 v1 HDone1 phi2 heap2 v2 HSteps2.
    subst.
    inversion HSteps2; subst; simpl in *.
    + exfalso. eapply done_no_step; eauto.
    + match goal with
	      | HStep2 : Step _ _ _ |- _ =>
	          destruct
	            (step_deterministic _ _ _ _ _
	              (NotPairParEvalState_non_pairpar_run _ HNotPair)
	              HStep HStep2)
	            as (_ & HStateEq);
          subst;
          eapply IH; eauto
      end.
    + contradiction.
  - intros heap1 v1 HDone1 phi2 heap2 v2 HSteps2.
    subst.
    dependent destruction HSteps2; simpl in *.
    + contradiction.
    + eapply
        (PairParCheckedPackedArbitraryScheduleContinuationTerminalDeterminism
          heap env rho ef1 ea1 ef2 ea2 k
          phi_mu phi_mu0 heap1 heap2 v1 v2
          theta1 theta2 theta0 theta3);
      repeat match goal with
      | HObserved : PairParObservedCheckPass _ _ _ _ |- _ =>
          destruct HObserved as [? _]
      end;
      eauto.
Qed.

Theorem ScheduledInitialState_terminal_deterministic :
  forall heap env rho e phi1 heap1 v1 phi2 heap2 v2,
    ScheduledStepsPhi
      (initial_state heap env rho e)
      phi1
      (StDone heap1 v1) ->
    ScheduledStepsPhi
      (initial_state heap env rho e)
      phi2
      (StDone heap2 v2) ->
    heap1 = heap2 /\ v1 = v2.
Proof.
  intros heap env rho e phi1 heap1 v1 phi2 heap2 v2 HSteps1 HSteps2.
  eapply ScheduledStepsPhi_terminal_deterministic; eauto.
Qed.

Lemma PairParLeftRightStep_local_commute :
  forall left right k label_left label_right left' right',
    state_heap left = state_heap right ->
    NonPairParRunState left ->
    NonPairParRunState right ->
    Step left label_left left' ->
    Step right label_right right' ->
    Disjoint_Traces (label_trace label_left) (label_trace label_right) ->
    Disjoint_Traces (label_trace label_right) (label_trace label_left) ->
    exists left_after right_after,
      PairParStep
        (PPS_Run left' (with_state_heap (state_heap left') right) k)
        label_right
        (PPS_Run (with_state_heap (state_heap right_after) left')
           right_after k) /\
      PairParStep
        (PPS_Run (with_state_heap (state_heap right') left) right' k)
        label_left
        (PPS_Run left_after
           (with_state_heap (state_heap left_after) right') k) /\
      state_heap right_after ≡@{Heap} state_heap left_after.
Proof.
  intros left right k label_left label_right left' right'
    HHeapAgree HNonPairLeft HNonPairRight
    HStepLeft HStepRight HDisjointLR HDisjointRL.
  pose
    (right_after :=
      with_state_heap
        (label_result_heap label_right (state_heap left'))
        right').
  pose
    (left_after :=
      with_state_heap
        (label_result_heap label_left (state_heap right'))
        left').
  exists left_after, right_after.
  repeat split.
  - subst right_after.
    apply PPStep_Right.
    eapply (Step_rebase_after_disjoint_step
      right label_right right' left label_left left').
    + symmetry. exact HHeapAgree.
    + exact HNonPairRight.
    + exact HNonPairLeft.
    + exact HStepRight.
    + exact HStepLeft.
    + exact HDisjointRL.
  - subst left_after.
    apply PPStep_Left.
    eapply (Step_rebase_after_disjoint_step
      left label_left left' right label_right right').
    + exact HHeapAgree.
    + exact HNonPairLeft.
    + exact HNonPairRight.
    + exact HStepLeft.
    + exact HStepRight.
    + exact HDisjointLR.
  - subst right_after left_after.
    repeat rewrite state_heap_with_state_heap.
    rewrite (Step_state_heap_label_result _ _ _ HStepLeft).
    rewrite (Step_state_heap_label_result _ _ _ HStepRight).
    rewrite <- HHeapAgree.
    apply label_result_heap_commute_disjoint.
    exact HDisjointLR.
Qed.

Theorem PairParCheckedSameProjectionScheduleHeapDeterminism :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_state1 phi_state2 phi_left phi_right
    heap1 heap2 v1 v2 theta_left theta_right,
    PairParCheckPass theta_left theta_right ->
    phi_left ⋞ theta_left ->
    phi_right ⋞ theta_right ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_state1
      phi_left
      phi_right
      (PPS_State (StDone heap1 v1)) ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_state2
      phi_left
      phi_right
      (PPS_State (StDone heap2 v2)) ->
    heap1 ≡@{Heap} heap2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_state1 phi_state2 phi_left phi_right
    heap1 heap2 v1 v2 theta_left theta_right
    HPass HSoundLeft HSoundRight HSteps1 HSteps2.
  destruct
    (PairParStepsPhi_branch_det_traces
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_state1 phi_left phi_right
      (PPS_State (StDone heap1 v1)) HSteps1)
    as (HDetLeft & HDetRight).
  pose proof
    (PairParStepsPhi_top_terminal_state_trace_nil
      heap env rho ef1 ea1 ef2 ea2
      phi_state1 phi_left phi_right heap1 v1 HSteps1)
    as HStateNil1.
  pose proof
    (PairParStepsPhi_top_terminal_state_trace_nil
      heap env rho ef1 ea1 ef2 ea2
      phi_state2 phi_left phi_right heap2 v2 HSteps2)
    as HStateNil2.
  unfold pairpar_checked_start, pairpar_checked_initial in HSteps1, HSteps2.
  destruct
    (PairParStepsPhi_run_split_replays_heap
      (initial_state heap env rho (Mu_App ef1 ea1))
      (initial_state heap env rho (Mu_App ef2 ea2))
      KDone phi_state1 phi_left phi_right
      (PPS_State (StDone heap1 v1))
      eq_refl HSteps1)
    as (heap_mid1 & HPar1 & HState1).
  destruct
    (PairParStepsPhi_run_split_replays_heap
      (initial_state heap env rho (Mu_App ef1 ea1))
      (initial_state heap env rho (Mu_App ef2 ea2))
      KDone phi_state2 phi_left phi_right
      (PPS_State (StDone heap2 v2))
      eq_refl HSteps2)
    as (heap_mid2 & HPar2 & HState2).
  simpl in HState1, HState2.
  pose proof
    (unique_heap
      heap heap_mid1 heap_mid2 phi_left phi_right theta_left theta_right
      HSoundLeft HSoundRight HPass HDetLeft HDetRight HPar2 HPar1)
    as HMidEq.
  pose proof
    (Phi_Heap_Steps_empty_as_list_preserves_heap
      phi_state1 heap_mid1 heap1 HStateNil1 HState1)
    as HFinal1.
  pose proof
    (Phi_Heap_Steps_empty_as_list_preserves_heap
      phi_state2 heap_mid2 heap2 HStateNil2 HState2)
    as HFinal2.
  transitivity heap_mid1.
  - symmetry. exact HFinal1.
  - transitivity heap_mid2; assumption.
Qed.

Theorem PairParLoosePackedSameProjectionScheduleHeapDeterminism :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_sched1 phi_sched2 phi_state1 phi_state2 phi_left phi_right
    heap1 heap2 v1 v2 theta_left theta_right,
    PairParCheckPass theta_left theta_right ->
    phi_left ⋞ theta_left ->
    phi_right ⋞ theta_right ->
    PairParLoosePackedStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_sched1
      phi_state1
      phi_left
      phi_right
      (PPS_State (StDone heap1 v1)) ->
    PairParLoosePackedStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_sched2
      phi_state2
      phi_left
      phi_right
      (PPS_State (StDone heap2 v2)) ->
    heap1 ≡@{Heap} heap2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_sched1 phi_sched2 phi_state1 phi_state2 phi_left phi_right
    heap1 heap2 v1 v2 theta_left theta_right
    HPass HSoundLeft HSoundRight HSteps1 HSteps2.
  destruct
    (PairParLoosePackedStepsPhi_branch_det_traces
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_sched1 phi_state1 phi_left phi_right
      (PPS_State (StDone heap1 v1)) HSteps1)
    as (HDetLeft & HDetRight).
  pose proof
    (PairParLoosePackedStepsPhi_top_terminal_state_trace_nil
      heap env rho ef1 ea1 ef2 ea2
      phi_sched1 phi_state1 phi_left phi_right heap1 v1 HSteps1)
    as HStateNil1.
  pose proof
    (PairParLoosePackedStepsPhi_top_terminal_state_trace_nil
      heap env rho ef1 ea1 ef2 ea2
      phi_sched2 phi_state2 phi_left phi_right heap2 v2 HSteps2)
    as HStateNil2.
  destruct
    (PairParLoosePackedStepsPhi_checked_kdone_split_replays_heap
      heap env rho ef1 ea1 ef2 ea2
      phi_sched1 phi_state1 phi_left phi_right heap1 v1 HSteps1)
    as (heap_mid1 & HPar1 & HState1).
  destruct
    (PairParLoosePackedStepsPhi_checked_kdone_split_replays_heap
      heap env rho ef1 ea1 ef2 ea2
      phi_sched2 phi_state2 phi_left phi_right heap2 v2 HSteps2)
    as (heap_mid2 & HPar2 & HState2).
  pose proof
    (unique_heap
      heap heap_mid1 heap_mid2 phi_left phi_right theta_left theta_right
      HSoundLeft HSoundRight HPass HDetLeft HDetRight HPar2 HPar1)
    as HMidEq.
  pose proof
    (Phi_Heap_Steps_empty_as_list_preserves_heap
      phi_state1 heap_mid1 heap1 HStateNil1 HState1)
    as HFinal1.
  pose proof
    (Phi_Heap_Steps_empty_as_list_preserves_heap
      phi_state2 heap_mid2 heap2 HStateNil2 HState2)
    as HFinal2.
  transitivity heap_mid1.
  - symmetry. exact HFinal1.
  - transitivity heap_mid2; assumption.
Qed.

Theorem PairParLoosePackedSameProjectionScheduleTerminalHeapAndPairShape :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_sched1 phi_sched2 phi_state1 phi_state2 phi_left phi_right
    heap1 heap2 v1 v2 theta_left theta_right,
    PairParCheckPass theta_left theta_right ->
    phi_left ⋞ theta_left ->
    phi_right ⋞ theta_right ->
    PairParLoosePackedStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_sched1
      phi_state1
      phi_left
      phi_right
      (PPS_State (StDone heap1 v1)) ->
    PairParLoosePackedStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_sched2
      phi_state2
      phi_left
      phi_right
      (PPS_State (StDone heap2 v2)) ->
    heap1 ≡@{Heap} heap2 /\
    (exists v1_left v1_right,
      v1 = Pair (v1_left, v1_right)) /\
    (exists v2_left v2_right,
      v2 = Pair (v2_left, v2_right)).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_sched1 phi_sched2 phi_state1 phi_state2 phi_left phi_right
    heap1 heap2 v1 v2 theta_left theta_right
    HPass HSoundLeft HSoundRight HSteps1 HSteps2.
  split.
  - eapply PairParLoosePackedSameProjectionScheduleHeapDeterminism; eauto.
  - split.
    + unfold pairpar_checked_start, pairpar_checked_initial in HSteps1.
      eapply PairParLoosePackedStepsPhi_run_kdone_terminal_pair_value;
        eauto.
    + unfold pairpar_checked_start, pairpar_checked_initial in HSteps2.
      eapply PairParLoosePackedStepsPhi_run_kdone_terminal_pair_value;
        eauto.
Qed.

Theorem PairParCheckedSameProjectionScheduleTerminalHeapAndPairShape :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_state1 phi_state2 phi_left phi_right
    heap1 heap2 v1 v2 theta_left theta_right,
    PairParCheckPass theta_left theta_right ->
    phi_left ⋞ theta_left ->
    phi_right ⋞ theta_right ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_state1
      phi_left
      phi_right
      (PPS_State (StDone heap1 v1)) ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_state2
      phi_left
      phi_right
      (PPS_State (StDone heap2 v2)) ->
    heap1 ≡@{Heap} heap2 /\
    (exists v1_left v1_right,
      v1 = Pair (v1_left, v1_right)) /\
    (exists v2_left v2_right,
      v2 = Pair (v2_left, v2_right)).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_state1 phi_state2 phi_left phi_right
    heap1 heap2 v1 v2 theta_left theta_right
    HPass HSoundLeft HSoundRight HSteps1 HSteps2.
  split.
  - eapply PairParCheckedSameProjectionScheduleHeapDeterminism; eauto.
  - split.
    + unfold pairpar_checked_start, pairpar_checked_initial in HSteps1.
      eapply PairParStepsPhi_run_kdone_terminal_pair_value; eauto.
    + unfold pairpar_checked_start, pairpar_checked_initial in HSteps2.
      eapply PairParStepsPhi_run_kdone_terminal_pair_value; eauto.
Qed.
