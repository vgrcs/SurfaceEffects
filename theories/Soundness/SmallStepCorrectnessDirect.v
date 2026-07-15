From Stdlib Require Import List.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Wf_nat.
From stdpp Require Import fin_maps.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.TraceSemantics.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepPreservationTheorems.
Require Import theories.Runtime.SmallStepStructuredTrace.
Require Import theories.Runtime.SmallStepSequentialSoundness.
Require Import theories.Runtime.SmallStepEffectSoundness.
Require Import theories.Runtime.SmallStepCorrectness.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.DynamicActions.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.EffectFacts.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.TypingWeakeningFacts.
Require Import theories.Meta.TypeFacts.
Require Import theories.Determinism.Determinism.
Require Import theories.Determinism.SmallStepStructuredReplay.

Lemma initial_silent_return_steps_done :
  forall heap env rho e v,
    Step (StEval heap env rho e KDone) Silent (StReturn heap v KDone) ->
    Steps (initial_state heap env rho e) nil (StDone heap v).
Proof.
  intros heap env rho e v HStep.
  unfold initial_state.
  replace (@nil DynamicAction) with (label_trace Silent ++ @nil DynamicAction)
    by reflexivity.
  econstructor; eauto.
  replace (@nil DynamicAction) with (label_trace Silent ++ @nil DynamicAction)
    by reflexivity.
  econstructor.
  - constructor.
  - constructor.
Qed.

Lemma StepsPhi_terminal_trace_nil_from_nil_steps :
  forall state phi heap_done v_done heap' v,
    Steps state nil (StDone heap_done v_done) ->
    StepsPhi state phi (StDone heap' v) ->
    phi_as_list phi = nil.
Proof.
  intros state phi heap_done v_done heap' v HNilSteps HStepsPhi.
  pose proof (StepsPhi_as_steps _ _ _ HStepsPhi) as HSteps.
  destruct
    (Steps_terminal_deterministic
      state nil heap_done v_done
      (phi_as_list phi) heap' v HNilSteps HSteps)
    as [HTrace _].
  now symmetry.
Qed.

Lemma StepsPhi_terminal_inv_step :
  forall state label state' phi heap_done v_done,
    Step state label state' ->
    StepsPhi state phi (StDone heap_done v_done) ->
    exists phi_tail,
      StepsPhi state' phi_tail (StDone heap_done v_done) /\
      phi_as_list phi = label_trace label ++ phi_as_list phi_tail.
Proof.
  intros state label state' phi heap_done v_done HStep HSteps.
  inversion HSteps; subst.
  - inversion HStep.
  - destruct (step_deterministic _ _ _ _ _ HStep H)
      as [HLabel HState].
    subst.
    exists phi0.
    split; [assumption |].
    simpl. now rewrite phi_as_list_label_phi.
Qed.

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
  - exfalso.
    eapply done_no_step; eauto.
  - destruct (step_deterministic _ _ _ _ _ HStep H)
      as [HLabel HState].
    subst.
    exists n0, phi0.
    repeat split; eauto.
    simpl. now rewrite phi_as_list_label_phi.
Qed.

Lemma StepsPhiN_trans_exists :
  forall n1 state phi1 state' n2 phi2 state'',
    StepsPhiN n1 state phi1 state' ->
    StepsPhiN n2 state' phi2 state'' ->
    exists phi,
      StepsPhiN (n1 + n2) state phi state'' /\
      phi_as_list phi = phi_as_list phi1 ++ phi_as_list phi2.
Proof.
  intros n1 state phi1 state' n2 phi2 state'' HSteps1 HSteps2.
  induction HSteps1 as
    [state | n state label state1 phi1 state_mid HStep _ IH].
  - simpl.
    exists phi2.
    split; [assumption | reflexivity].
  - destruct (IH HSteps2) as (phi_tail & HSteps & HTrace).
    exists (Phi_Seq (label_phi label) phi_tail).
    split.
    + simpl.
      econstructor; eauto.
    + simpl.
      rewrite phi_as_list_label_phi.
      rewrite HTrace.
      now rewrite app_assoc.
Qed.

Theorem StepsPhiN_terminal_deterministic :
  forall n1 state phi1 heap1 v1 n2 phi2 heap2 v2,
    StepsPhiN n1 state phi1 (StDone heap1 v1) ->
    StepsPhiN n2 state phi2 (StDone heap2 v2) ->
    n1 = n2 /\
    phi_as_list phi1 = phi_as_list phi2 /\
    heap1 = heap2 /\
    v1 = v2.
Proof.
  intros n1.
  induction n1 as [| n1 IH];
    intros state phi1 heap1 v1 n2 phi2 heap2 v2 HSteps1 HSteps2.
  - inversion HSteps1; subst.
    inversion HSteps2; subst.
    + repeat split; reflexivity.
    + exfalso. eapply done_no_step; eauto.
  - inversion HSteps1; subst.
    inversion HSteps2; subst.
    + exfalso. eapply done_no_step; eauto.
    + match goal with
      | HStep1 : Step ?state ?label1 ?state1,
        HStep2 : Step ?state ?label2 ?state2 |- _ =>
          destruct (step_deterministic _ _ _ _ _ HStep1 HStep2)
            as [HLabel HState]
      end.
      subst.
      match goal with
      | HTail1 : StepsPhiN n1 ?tail_state ?phi_tail1 (StDone heap1 v1),
        HTail2 : StepsPhiN ?n2_tail ?tail_state ?phi_tail2
          (StDone heap2 v2) |- _ =>
          destruct
            (IH tail_state phi_tail1 heap1 v1
              n2_tail phi_tail2 heap2 v2 HTail1 HTail2)
            as [HCount [HTrace [HHeap HVal]]]
      end.
      subst.
      repeat split; try reflexivity.
      simpl.
      now rewrite HTrace.
Qed.

Lemma StepsPhiN_of_terminal_StepsPhi :
  forall n state phi_indexed heap_indexed v_indexed
         phi heap v,
    StepsPhiN n state phi_indexed (StDone heap_indexed v_indexed) ->
    StepsPhi state phi (StDone heap v) ->
    StepsPhiN n state phi (StDone heap v) /\
    phi_as_list phi_indexed = phi_as_list phi /\
    heap_indexed = heap /\
    v_indexed = v.
Proof.
  intros n state phi_indexed heap_indexed v_indexed
    phi heap v HIndexed HSteps.
  destruct (StepsPhi_to_StepsPhiN _ _ _ HSteps) as (n_phi & HIndexedPhi).
  destruct
    (StepsPhiN_terminal_deterministic
      n state phi_indexed heap_indexed v_indexed
      n_phi phi heap v HIndexed HIndexedPhi)
    as [HCount [HTrace [HHeap HVal]]].
  subst.
  repeat split; assumption.
Qed.

Lemma StepsPhiN_terminal_tail_from_step :
  forall n state label state' phi heap_done v_done phi_tail,
    Step state label state' ->
    StepsPhiN n state phi (StDone heap_done v_done) ->
    StepsPhi state' phi_tail (StDone heap_done v_done) ->
    exists n_tail,
      n_tail < n /\
      StepsPhiN n_tail state' phi_tail (StDone heap_done v_done).
Proof.
  intros n state label state' phi heap_done v_done phi_tail
    HStep HIndexed HTail.
  destruct
    (StepsPhiN_terminal_inv_step
      n state label state' phi heap_done v_done HStep HIndexed)
    as (n_tail & phi_indexed_tail & HN & HIndexedTail & _).
  subst.
  destruct
    (StepsPhiN_of_terminal_StepsPhi
      n_tail state' phi_indexed_tail heap_done v_done
      phi_tail heap_done v_done HIndexedTail HTail)
    as [HIndexedPhiTail _].
  exists n_tail.
  split; [lia | exact HIndexedPhiTail].
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

Theorem StepsPhiN_append_kont_terminal_continue :
  forall n state phi heap' v tail state_next,
    StepsPhiN n state phi (StDone heap' v) ->
    Step (StReturn heap' v tail) Silent state_next ->
    ~ Terminal state ->
    StepsPhiN n (state_append_kont state tail) phi state_next.
Proof.
  intros n state phi heap' v tail state_next HSteps HFinal HNotTerminal.
  remember (StDone heap' v) as final_state eqn:HFinalState.
  revert heap' v HFinalState tail state_next HFinal HNotTerminal.
  induction HSteps as
    [state | n state label state' phi state'' HStep HSteps IH];
    intros heap' v HFinalState tail state_next HFinal HNotTerminal.
  - exfalso.
    subst.
    apply HNotTerminal.
    constructor.
  - destruct (Step_append_kont_or_done state label state' tail HStep)
      as [(heap_done & v_done & HState & HLabel & HState') | HStepAppend].
    + subst.
      destruct (StepsPhiN_from_done_inv _ _ _ _ _ HSteps)
        as [HN [HPhi HDone]].
      subst.
      inversion HDone; subst.
      simpl.
      change (Phi_Seq Phi_Nil Phi_Nil)
        with (Phi_Seq (label_phi Silent) Phi_Nil).
      eapply StepsPhiN_Step.
      * exact HFinal.
      * constructor.
    + eapply StepsPhiN_Step.
      * exact HStepAppend.
      * eapply IH.
        -- exact HFinalState.
        -- exact HFinal.
        -- intros HTerminal.
           inversion HTerminal; subst.
           destruct (Step_to_done_inv state label heap v0 HStep)
             as (HState & HLabel).
           subst.
           simpl in HStepAppend.
           eapply Step_return_self_absurd; eauto.
Qed.

Theorem StepsPhiN_initial_terminal_continue :
  forall n heap env rho e phi heap' v tail state_next,
    StepsPhiN n (initial_state heap env rho e) phi (StDone heap' v) ->
    Step (StReturn heap' v tail) Silent state_next ->
    StepsPhiN n (StEval heap env rho e tail) phi state_next.
Proof.
  intros n heap env rho e phi heap' v tail state_next HSteps HFinal.
  unfold initial_state in HSteps.
  change (StEval heap env rho e tail)
    with (state_append_kont (StEval heap env rho e KDone) tail).
  eapply StepsPhiN_append_kont_terminal_continue; eauto.
  intros HTerminal.
  inversion HTerminal.
Qed.

Lemma StepsPhiN_append_kont_terminal_continue_label :
  forall n state phi heap' v tail label state_next,
    StepsPhiN n state phi (StDone heap' v) ->
    Step (StReturn heap' v tail) label state_next ->
    ~ Terminal state ->
    exists phi_next,
      StepsPhiN n (state_append_kont state tail) phi_next state_next /\
      phi_as_list phi_next = phi_as_list phi ++ label_trace label.
Proof.
  intros n state phi heap' v tail label_final state_next
    HStepsN HFinal HNotTerminal.
  remember (StDone heap' v) as final_state eqn:HFinalState.
  revert heap' v HFinalState tail label_final state_next HFinal HNotTerminal.
  induction HStepsN as
    [state | n state label_step state' phi state'' HStep HStepsN IH];
    intros heap' v HFinalState tail label_final state_next HFinal HNotTerminal.
  - exfalso.
    subst.
    apply HNotTerminal.
    constructor.
  - destruct (Step_append_kont_or_done state label_step state' tail HStep)
      as [(heap_done & v_done & HState & HLabel & HState') | HStepAppend].
    + subst.
      destruct (StepsPhiN_from_done_inv _ _ _ _ _ HStepsN)
        as [HN [HPhi HDone]].
      subst.
      inversion HDone; subst.
      exists (Phi_Seq (label_phi label_final) Phi_Nil).
      split.
      * eapply StepsPhiN_Step.
        -- exact HFinal.
        -- constructor.
      * simpl.
        rewrite phi_as_list_label_phi.
        now rewrite app_nil_r.
    + destruct (IH heap' v HFinalState tail label_final state_next HFinal)
        as (phi_next_tail & HStepsNextTail & HTraceTail).
      {
        intros HTerminal.
        inversion HTerminal; subst.
        destruct (Step_to_done_inv state label_step heap v0 HStep)
          as (HStateDone & HLabelDone).
        subst.
        simpl in HStepAppend.
        eapply Step_return_self_absurd; eauto.
      }
      exists (Phi_Seq (label_phi label_step) phi_next_tail).
      split.
      * eapply StepsPhiN_Step; eauto.
      * simpl.
        rewrite phi_as_list_label_phi.
        rewrite HTraceTail.
        now rewrite app_assoc.
Qed.

Lemma StepsPhiN_initial_terminal_continue_label :
  forall n heap env rho e phi heap' v tail label state_next,
    StepsPhiN n (initial_state heap env rho e) phi (StDone heap' v) ->
    Step (StReturn heap' v tail) label state_next ->
    exists phi_next,
      StepsPhiN n (StEval heap env rho e tail) phi_next state_next /\
      phi_as_list phi_next = phi_as_list phi ++ label_trace label.
Proof.
  intros n heap env rho e phi heap' v tail label state_next HStepsN HFinal.
  unfold initial_state in HStepsN.
  change (StEval heap env rho e tail)
    with (state_append_kont (StEval heap env rho e KDone) tail).
  eapply StepsPhiN_append_kont_terminal_continue_label; eauto.
  intros HTerminal.
  inversion HTerminal.
Qed.

Lemma Steps_append_kont_terminal_continue_label :
  forall state trace heap' v tail label state_next,
    Steps state trace (StDone heap' v) ->
    Step (StReturn heap' v tail) label state_next ->
    ~ Terminal state ->
    Steps (state_append_kont state tail)
      (trace ++ label_trace label)
      state_next.
Proof.
  intros state trace heap' v tail label_final state_next
    HSteps HFinal HNotTerminal.
  dependent induction HSteps.
  - exfalso. apply HNotTerminal. constructor.
  - destruct (Step_append_kont_or_done state label state' tail H)
      as [(heap_done & v_done & HState & HLabel & HState') | HStepAppend].
    + subst.
      destruct
        (terminal_steps_refl
          (StDone heap_done v_done) trace (StDone heap' v)
          (Terminal_Done heap_done v_done) HSteps)
        as [-> HDone].
      inversion HDone; subst.
      simpl.
      replace (label_trace label_final)
        with (label_trace label_final ++ @nil DynamicAction)
        by now rewrite app_nil_r.
      econstructor; eauto.
      constructor.
    + simpl.
      rewrite <- app_assoc.
      econstructor; eauto.
      eapply IHHSteps; eauto.
      intros HTerminal.
      inversion HTerminal; subst.
      destruct (Step_to_done_inv state label heap v0 H)
        as (HStateDone & HLabelDone).
      subst.
      simpl in HStepAppend.
      eapply Step_return_self_absurd; eauto.
Qed.

Lemma StepsPhi_initial_terminal_continue_label :
  forall heap env rho e phi heap' v tail label state_next,
    StepsPhi (initial_state heap env rho e) phi (StDone heap' v) ->
    Step (StReturn heap' v tail) label state_next ->
    exists phi_next,
      StepsPhi (StEval heap env rho e tail) phi_next state_next /\
      phi_as_list phi_next = phi_as_list phi ++ label_trace label.
Proof.
  intros heap env rho e phi heap' v tail label state_next HStepsPhi HFinal.
  pose proof (StepsPhi_as_steps _ _ _ HStepsPhi) as HSteps.
  unfold initial_state in HSteps.
  destruct
    (steps_as_StepsPhi
      (StEval heap env rho e tail)
      (phi_as_list phi ++ label_trace label)
      state_next)
    as (phi_next & HStepsNext & HTraceNext).
  {
    change (StEval heap env rho e tail)
      with (state_append_kont (StEval heap env rho e KDone) tail).
    eapply Steps_append_kont_terminal_continue_label; eauto.
    intros HTerminal. inversion HTerminal.
  }
  exists phi_next. split; assumption.
Qed.

Lemma Step_append_kont_inv :
  forall state tail label state',
    ~ Terminal state ->
    Step (state_append_kont state tail) label state' ->
    (exists state0,
      Step state label state0 /\
      state' = state_append_kont state0 tail /\
      ~ Terminal state0) \/
    (exists heap v,
      state = StReturn heap v KDone /\
      Step (StReturn heap v tail) label state').
Proof.
  intros state tail label state' HNotTerminal HStep.
  destruct state as [heap env rho e k | heap v k | heap v].
  - simpl in HStep.
    inversion HStep; subst;
      (left; eexists; split; [eauto using Step |];
       split; [reflexivity | intros HTerminal; inversion HTerminal]).
  - destruct k; simpl in HStep;
      try solve
        [ inversion HStep; subst;
          left; eexists; split; [eauto using Step |];
          split; [reflexivity | intros HTerminal; inversion HTerminal] ].
    + right. exists heap, v. split; [reflexivity | exact HStep].
    + inversion HStep; subst.
      * left; eexists; split;
          [eapply Step_PairPar_EvalMu1; eauto |].
        split; [reflexivity | intros HTerminal; inversion HTerminal].
      * left; eexists; split;
          [eapply Step_PairPar_FallbackMu1; eauto |].
        split; [reflexivity | intros HTerminal; inversion HTerminal].
    + inversion HStep; subst;
        (left; eexists; split; [eauto using Step |];
         split; [reflexivity | intros HTerminal; inversion HTerminal]).
  - simpl in HStep.
    exfalso. apply HNotTerminal. constructor.
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

Lemma StepsPhiN_child_from_initial_step_terminal_decompose :
  forall n state label heap env rho e tail phi heap_final v_final,
    Step state label (StEval heap env rho e tail) ->
    StepsPhiN n state phi (StDone heap_final v_final) ->
    exists n_expr heap_mid v_mid phi_expr phi_tail,
      n_expr < n /\
      StepsPhiN n_expr (initial_state heap env rho e) phi_expr
        (StDone heap_mid v_mid) /\
      StepsPhi (StReturn heap_mid v_mid tail) phi_tail
        (StDone heap_final v_final).
Proof.
  intros n state label heap env rho e tail phi heap_final v_final
    HStep HSteps.
  destruct
    (StepsPhiN_terminal_inv_step
      n state label (StEval heap env rho e tail)
      phi heap_final v_final HStep HSteps)
    as (n_tail & phi_tail_indexed & HLTail & HTail & _).
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_tail heap env rho e tail phi_tail_indexed heap_final v_final HTail)
    as (n_expr & n_tail_done & heap_mid & v_mid & phi_expr & phi_tail &
        HLeExpr & _ & HExpr & HTailDone & _).
  exists n_expr, heap_mid, v_mid, phi_expr, phi_tail.
  split; [lia |].
  split; [exact HExpr |].
  exact (StepsPhiN_to_StepsPhi _ _ _ _ HTailDone).
Qed.

Lemma StepsPhi_append_kont_terminal_decompose :
  forall app phi heap_final v_final,
    StepsPhi app phi (StDone heap_final v_final) ->
    forall state tail,
      app = state_append_kont state tail ->
      ~ Terminal state ->
      exists heap_mid v_mid phi_state phi_tail,
        StepsPhi state phi_state (StDone heap_mid v_mid) /\
        StepsPhi (StReturn heap_mid v_mid tail) phi_tail
          (StDone heap_final v_final) /\
        phi_as_list phi =
          phi_as_list phi_state ++ phi_as_list phi_tail.
Proof.
  intros app phi heap_final v_final HSteps.
  remember (StDone heap_final v_final) as final_state eqn:HFinal.
  revert heap_final v_final HFinal.
  induction HSteps as
    [app | app label app' phi_tail app'' HStep HStepsTail IH];
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
        as (heap_mid & v_mid & phi_state_tail & phi_tail_final &
            HStateTail & HTailFinal & HTraceTail).
      exists heap_mid, v_mid, (Phi_Seq (label_phi label) phi_state_tail),
        phi_tail_final.
      split.
      * eapply StepsPhi_Step; eauto.
      * split; [exact HTailFinal |].
        simpl. rewrite HTraceTail.
        rewrite app_assoc. reflexivity.
    + subst state.
      exists heap_mid, v_mid, (Phi_Seq (label_phi Silent) Phi_Nil),
        (Phi_Seq (label_phi label) phi_tail).
      split.
      * eapply StepsPhi_Step.
        -- constructor.
        -- constructor.
      * split.
        -- eapply StepsPhi_Step; eauto.
        -- simpl. reflexivity.
Qed.

Lemma StepsPhi_initial_with_kont_terminal_decompose :
  forall heap env rho e tail phi heap_final v_final,
    StepsPhi (StEval heap env rho e tail) phi
      (StDone heap_final v_final) ->
    exists heap_mid v_mid phi_expr phi_tail,
      StepsPhi (initial_state heap env rho e) phi_expr
        (StDone heap_mid v_mid) /\
      StepsPhi (StReturn heap_mid v_mid tail) phi_tail
        (StDone heap_final v_final) /\
      phi_as_list phi =
        phi_as_list phi_expr ++ phi_as_list phi_tail.
Proof.
  intros heap env rho e tail phi heap_final v_final HSteps.
  eapply (StepsPhi_append_kont_terminal_decompose
    (StEval heap env rho e tail) phi heap_final v_final HSteps
    (StEval heap env rho e KDone) tail).
  - reflexivity.
  - intros HTerminal. inversion HTerminal.
Qed.

Lemma ReadOnlyPhi_of_phi_as_list_included :
  forall phi phi_ro,
    ReadOnlyPhi phi_ro ->
    (forall da,
      List.In da (phi_as_list phi) ->
      List.In da (phi_as_list phi_ro)) ->
    ReadOnlyPhi phi.
Proof.
  intros phi phi_ro HReadOnly HIncluded.
  apply ReadOnlyPhi_of_da_in_read.
  intros da HIn.
  eapply ReadOnlyPhi_da_in_read; eauto.
  apply In_phi_as_list_DA_in.
  apply HIncluded.
  now apply DA_in_Phi_in_phi_as_list.
Qed.

Lemma ReadOnlyPhi_of_phi_as_list_nil :
  forall phi,
    phi_as_list phi = nil ->
    ReadOnlyPhi phi.
Proof.
  intros phi HList.
  apply ReadOnlyPhi_of_da_in_read.
  intros da HIn.
  pose proof (DA_in_Phi_in_phi_as_list da phi HIn) as HInList.
  rewrite HList in HInList.
  contradiction.
Qed.

Definition HeapFootprint := Ensemble HeapKey.

Definition HeterogeneousHeapOn
    (footprint : HeapFootprint) (heap_actual heap_summary : Heap) : Prop :=
  forall k,
    Ensembles.In HeapKey footprint k ->
    find_H k heap_actual = find_H k heap_summary.

Definition PhiReadFootprint (phi : Phi) : HeapFootprint :=
  fun k =>
    exists r l v,
      k = (r, l) /\ DA_in_Phi (DA_Read r l v) phi.

Definition HeterogeneousHeapForPhi
    (phi : Phi) (heap_actual heap_summary : Heap) : Prop :=
  HeterogeneousHeapOn (PhiReadFootprint phi) heap_actual heap_summary.

Definition HeapEquivalentOn
    (footprint : HeapFootprint) (heap_actual heap_summary : Heap) : Prop :=
  HeterogeneousHeapOn footprint heap_actual heap_summary.

Definition HeapEquivalentOnPhi
    (phi : Phi) (heap_actual heap_summary : Heap) : Prop :=
  HeapEquivalentOn (PhiReadFootprint phi) heap_actual heap_summary.

Lemma HeterogeneousHeapOn_refl :
  forall footprint heap,
    HeterogeneousHeapOn footprint heap heap.
Proof.
  intros footprint heap k _.
  reflexivity.
Qed.

Lemma HeterogeneousHeapForPhi_refl :
  forall phi heap,
    HeterogeneousHeapForPhi phi heap heap.
Proof.
  intros phi heap.
  apply HeterogeneousHeapOn_refl.
Qed.

Lemma HeapEquivalentOn_refl :
  forall footprint heap,
    HeapEquivalentOn footprint heap heap.
Proof.
  intros footprint heap.
  apply HeterogeneousHeapOn_refl.
Qed.

Lemma HeapEquivalentOnPhi_refl :
  forall phi heap,
    HeapEquivalentOnPhi phi heap heap.
Proof.
  intros phi heap.
  apply HeapEquivalentOn_refl.
Qed.

Lemma HeterogeneousHeapForPhi_read :
  forall phi heap_actual heap_summary r l v,
    HeterogeneousHeapForPhi phi heap_actual heap_summary ->
    DA_in_Phi (DA_Read r l v) phi ->
    find_H (r, l) heap_actual = find_H (r, l) heap_summary.
Proof.
  intros phi heap_actual heap_summary r l v HAgree HIn.
  unfold HeterogeneousHeapForPhi, HeterogeneousHeapOn in HAgree.
  apply HAgree.
  unfold PhiReadFootprint.
  exists r, l, v.
  split; [reflexivity | exact HIn].
Qed.

Lemma HeapEquivalentOnPhi_read :
  forall phi heap_actual heap_summary r l v,
    HeapEquivalentOnPhi phi heap_actual heap_summary ->
    DA_in_Phi (DA_Read r l v) phi ->
    find_H (r, l) heap_actual = find_H (r, l) heap_summary.
Proof.
  intros phi heap_actual heap_summary r l v HAgree HIn.
  unfold HeapEquivalentOnPhi, HeapEquivalentOn in HAgree.
  eapply HeterogeneousHeapForPhi_read; eauto.
Qed.

Lemma HeapLookupEquivalent_implies_HeapEquivalentOn :
  forall footprint heap_actual heap_summary,
    HeapLookupEquivalent heap_actual heap_summary ->
    HeapEquivalentOn footprint heap_actual heap_summary.
Proof.
  intros footprint heap_actual heap_summary HLookup k _.
  exact (HLookup k).
Qed.

Lemma HeapLookupEquivalent_implies_HeapEquivalentOnPhi :
  forall phi heap_actual heap_summary,
    HeapLookupEquivalent heap_actual heap_summary ->
    HeapEquivalentOnPhi phi heap_actual heap_summary.
Proof.
  intros phi heap_actual heap_summary HLookup.
  apply HeapLookupEquivalent_implies_HeapEquivalentOn.
  exact HLookup.
Qed.

Lemma HeterogeneousHeapForPhi_of_phi_as_list_eq :
  forall phi1 phi2 heap_actual heap_summary,
    phi_as_list phi1 = phi_as_list phi2 ->
    HeterogeneousHeapForPhi phi2 heap_actual heap_summary ->
    HeterogeneousHeapForPhi phi1 heap_actual heap_summary.
Proof.
  intros phi1 phi2 heap_actual heap_summary HList HAgree.
  unfold HeterogeneousHeapForPhi, HeterogeneousHeapOn.
  intros k HFootprint.
  unfold PhiReadFootprint in HFootprint.
  destruct HFootprint as (r & l & v & HKey & HIn1).
  subst k.
  apply HeterogeneousHeapForPhi_read with (v := v) (phi := phi2);
    [exact HAgree |].
  apply In_phi_as_list_DA_in.
  rewrite <- HList.
  now apply DA_in_Phi_in_phi_as_list.
Qed.

Lemma HeterogeneousHeapForPhi_sym :
  forall phi heap1 heap2,
    HeterogeneousHeapForPhi phi heap1 heap2 ->
    HeterogeneousHeapForPhi phi heap2 heap1.
Proof.
  intros phi heap1 heap2 HAgree.
  unfold HeterogeneousHeapForPhi, HeterogeneousHeapOn in *.
  intros k HFootprint.
  symmetry.
  now apply HAgree.
Qed.

Lemma HeterogeneousHeapForPhi_seq_left :
  forall phi1 phi2 heap_actual heap_summary,
    HeterogeneousHeapForPhi (Phi_Seq phi1 phi2) heap_actual heap_summary ->
    HeterogeneousHeapForPhi phi1 heap_actual heap_summary.
Proof.
  intros phi1 phi2 heap_actual heap_summary HAgree.
  unfold HeterogeneousHeapForPhi, HeterogeneousHeapOn.
  intros k HFootprint.
  unfold PhiReadFootprint in *.
  destruct HFootprint as (r & l & v & HKey & HIn).
  subst k.
  apply HAgree.
  exists r, l, v.
  split; [reflexivity |].
  apply DAP_Seq.
  now left.
Qed.

Lemma HeterogeneousHeapForPhi_seq_right :
  forall phi1 phi2 heap_actual heap_summary,
    HeterogeneousHeapForPhi (Phi_Seq phi1 phi2) heap_actual heap_summary ->
    HeterogeneousHeapForPhi phi2 heap_actual heap_summary.
Proof.
  intros phi1 phi2 heap_actual heap_summary HAgree.
  unfold HeterogeneousHeapForPhi, HeterogeneousHeapOn.
  intros k HFootprint.
  unfold PhiReadFootprint in *.
  destruct HFootprint as (r & l & v & HKey & HIn).
  subst k.
  apply HAgree.
  exists r, l, v.
  split; [reflexivity |].
  apply DAP_Seq.
  now right.
Qed.

Lemma HeterogeneousHeapForPhi_par_left :
  forall phi1 phi2 heap_actual heap_summary,
    HeterogeneousHeapForPhi (Phi_Par phi1 phi2) heap_actual heap_summary ->
    HeterogeneousHeapForPhi phi1 heap_actual heap_summary.
Proof.
  intros phi1 phi2 heap_actual heap_summary HAgree.
  unfold HeterogeneousHeapForPhi, HeterogeneousHeapOn.
  intros k HFootprint.
  unfold PhiReadFootprint in *.
  destruct HFootprint as (r & l & v & HKey & HIn).
  subst k.
  apply HAgree.
  exists r, l, v.
  split; [reflexivity |].
  apply DAP_Par.
  now left.
Qed.

Lemma HeterogeneousHeapForPhi_par_right :
  forall phi1 phi2 heap_actual heap_summary,
    HeterogeneousHeapForPhi (Phi_Par phi1 phi2) heap_actual heap_summary ->
    HeterogeneousHeapForPhi phi2 heap_actual heap_summary.
Proof.
  intros phi1 phi2 heap_actual heap_summary HAgree.
  unfold HeterogeneousHeapForPhi, HeterogeneousHeapOn.
  intros k HFootprint.
  unfold PhiReadFootprint in *.
  destruct HFootprint as (r & l & v & HKey & HIn).
  subst k.
  apply HAgree.
  exists r, l, v.
  split; [reflexivity |].
  apply DAP_Par.
  now right.
Qed.

Lemma Phi_Heap_Step_preserves_disjoint_read_lookup :
  forall phi phi' heap heap' r l v,
    Phi_Heap_Step (phi, heap) (phi', heap') ->
    (forall da,
      List.In da (phi_as_list phi) ->
      Disjoint_Dynamic da (DA_Read r l v)) ->
    find_H (r, l) heap' = find_H (r, l) heap.
Proof.
  intros phi phi' heap heap' r l v HStep.
  dependent induction HStep; intros HDisjoint; simpl in *.
  - specialize (HDisjoint (DA_Alloc r0 l0 v0) (or_introl eq_refl)).
    inversion HDisjoint; subst.
    unfold find_H, update_H.
    simpl.
    apply lookup_insert_ne.
    intro HContra.
    match goal with
    | Hneq : (?r1, ?l1) <> (?r2, ?l2) |- _ =>
        apply Hneq; inversion HContra; reflexivity
    end.
  - reflexivity.
  - specialize (HDisjoint (DA_Write r0 l0 v0) (or_introl eq_refl)).
    inversion HDisjoint; subst.
    unfold find_H, update_H.
    simpl.
    apply lookup_insert_ne.
    intro HContra.
    match goal with
    | Hneq : (?r1, ?l1) <> (?r2, ?l2) |- _ =>
        apply Hneq; inversion HContra; reflexivity
    end.
  - eapply IHHStep; eauto.
    intros da HIn.
    apply HDisjoint.
    apply in_or_app.
    now left.
  - eapply IHHStep; eauto.
  - reflexivity.
  - eapply IHHStep; eauto.
    intros da HIn.
    apply HDisjoint.
    apply in_or_app.
    now left.
  - eapply IHHStep; eauto.
    intros da HIn.
    apply HDisjoint.
    apply in_or_app.
    now right.
  - reflexivity.
Qed.

Lemma Phi_Heap_StepsAux_preserves_DAs :
  forall phi heap phi' heap' n,
    Phi_Heap_StepsAux (phi, heap) (phi', heap', n) ->
    forall da,
      List.In da (phi_as_list phi') ->
      List.In da (phi_as_list phi).
Proof.
  intros phi heap phi' heap' n HSteps.
  dependent induction HSteps; intros da HIn.
  - exact HIn.
  - eapply Phi_Heap_Step__Preserves_DAs; eauto.
  - pose proof
      (IHHSteps2 phi'0 heap'0 phi' heap' n''
        eq_refl eq_refl da HIn) as HMid.
    exact
      (IHHSteps1 phi heap phi'0 heap'0 n'
        eq_refl eq_refl da HMid).
Qed.

Lemma Phi_Heap_StepsAux_preserves_disjoint_read_lookup :
  forall phi heap phi' heap' n r l v,
    Phi_Heap_StepsAux (phi, heap) (phi', heap', n) ->
    (forall da,
      List.In da (phi_as_list phi) ->
      Disjoint_Dynamic da (DA_Read r l v)) ->
    find_H (r, l) heap' = find_H (r, l) heap.
Proof.
  intros phi heap phi' heap' n r l v HSteps.
  dependent induction HSteps; intros HDisjoint.
  - reflexivity.
  - eapply Phi_Heap_Step_preserves_disjoint_read_lookup; eauto.
  - assert (HDisjointMid :
      forall da,
        List.In da (phi_as_list phi'0) ->
        Disjoint_Dynamic da (DA_Read r l v)).
    {
      intros da HIn.
      apply HDisjoint.
      eapply Phi_Heap_StepsAux_preserves_DAs; eauto.
    }
    pose proof
      (IHHSteps2 phi'0 heap'0 phi' heap' n''
        eq_refl eq_refl HDisjointMid) as HRight.
    pose proof
      (IHHSteps1 phi heap phi'0 heap'0 n'
        eq_refl eq_refl HDisjoint) as HLeft.
    now rewrite HRight, HLeft.
Qed.

Lemma Phi_Heap_Steps_preserves_disjoint_read_lookup :
  forall phi heap heap' r l v,
    Phi_Heap_Steps (phi, heap) (Phi_Nil, heap') ->
    (forall da,
      List.In da (phi_as_list phi) ->
      Disjoint_Dynamic da (DA_Read r l v)) ->
    find_H (r, l) heap' = find_H (r, l) heap.
Proof.
  intros phi heap heap' r l v HSteps HDisjoint.
  unfold Phi_Heap_Steps in HSteps.
  destruct HSteps as (n & HSteps).
  eapply Phi_Heap_StepsAux_preserves_disjoint_read_lookup; eauto.
Qed.

Lemma HeterogeneousHeapForPhi_preserved_by_disjoint_replay :
  forall phi_writer heap heap' phi_reader heap_summary,
    Phi_Heap_Steps (phi_writer, heap) (Phi_Nil, heap') ->
    Disjoint_Traces (phi_as_list phi_writer) (phi_as_list phi_reader) ->
    HeterogeneousHeapForPhi phi_reader heap heap_summary ->
    HeterogeneousHeapForPhi phi_reader heap' heap_summary.
Proof.
  intros phi_writer heap heap' phi_reader heap_summary
    HReplay HDisjoint HAgree.
  unfold HeterogeneousHeapForPhi, HeterogeneousHeapOn.
  intros k HFootprint.
  unfold PhiReadFootprint in HFootprint.
  destruct HFootprint as (r & l & v & HKey & HInRead).
  subst k.
  pose proof
    (Phi_Heap_Steps_preserves_disjoint_read_lookup
      phi_writer heap heap' r l v HReplay) as HPres.
  assert (HDisjointRead :
    forall da,
      List.In da (phi_as_list phi_writer) ->
      Disjoint_Dynamic da (DA_Read r l v)).
  {
    intros da HInWriter.
    inversion HDisjoint as [writer reader HAll]; subst.
    apply HAll; auto.
    now apply DA_in_Phi_in_phi_as_list.
  }
  specialize (HPres HDisjointRead).
  transitivity (find_H (r, l) heap).
  - exact HPres.
  - apply HeterogeneousHeapForPhi_read with (v := v) (phi := phi_reader);
      assumption.
Qed.

Lemma HeterogeneousHeapForPhi_preserved_by_disjoint_steps_phi :
  forall state phi_writer state' phi_reader heap_summary,
    StepsPhi state phi_writer state' ->
    Disjoint_Traces (phi_as_list phi_writer) (phi_as_list phi_reader) ->
    HeterogeneousHeapForPhi phi_reader (state_heap state) heap_summary ->
    HeterogeneousHeapForPhi phi_reader (state_heap state') heap_summary.
Proof.
  intros state phi_writer state' phi_reader heap_summary
    HSteps HDisjoint HAgree.
  eapply HeterogeneousHeapForPhi_preserved_by_disjoint_replay; eauto.
  eapply StepsPhi_replays_heap; eauto.
Qed.

Lemma HeterogeneousHeapForPhi_preserved_by_disjoint_summaries :
  forall state_writer phi_writer state_writer'
    phi_reader heap_summary theta_writer theta_reader,
    StepsPhi state_writer phi_writer state_writer' ->
    phi_writer ⋞ theta_writer ->
    phi_reader ⋞ theta_reader ->
    Disjointness theta_writer theta_reader ->
    HeterogeneousHeapForPhi phi_reader (state_heap state_writer) heap_summary ->
    HeterogeneousHeapForPhi phi_reader (state_heap state_writer') heap_summary.
Proof.
  intros state_writer phi_writer state_writer'
    phi_reader heap_summary theta_writer theta_reader
    HSteps HWriterSound HReaderSound HDisjoint HAgree.
  eapply HeterogeneousHeapForPhi_preserved_by_disjoint_steps_phi; eauto.
  eapply Phi_Theta_Disjointness_disjoint_traces; eauto.
Qed.

Lemma Step_readonly_replay_on_heap_agreement :
  forall state label state' heap_summary,
    Step state label state' ->
    ReadOnlyPhi (label_phi label) ->
    HeterogeneousHeapForPhi (label_phi label)
      (state_heap state) heap_summary ->
    Step (with_state_heap heap_summary state) label
      (with_state_heap heap_summary state').
Proof.
  intros state label state' heap_summary HStep HReadOnly HAgree.
  inversion HStep; subst; simpl in *;
    try solve [constructor; eauto | inversion HReadOnly].
  - constructor; eauto.
    pose proof
      (HeterogeneousHeapForPhi_read
        (Phi_Elem (DA_Read r l v)) heap heap_summary
        r l v HAgree (DAP_Trace (DA_Read r l v))) as HFind.
    now rewrite <- HFind.
Qed.

Lemma StepsPhi_readonly_replay_on_heap_agreement :
  forall state phi state' heap_summary,
    StepsPhi state phi state' ->
    ReadOnlyPhi phi ->
    HeterogeneousHeapForPhi phi (state_heap state) heap_summary ->
    StepsPhi (with_state_heap heap_summary state) phi
      (with_state_heap heap_summary state').
Proof.
  intros state phi state' heap_summary HSteps.
  revert heap_summary.
  induction HSteps as [state | state label state1 phi state2 HStep HSteps IH];
    intros heap_summary HReadOnly HAgree.
  - constructor.
  - apply ReadOnlyPhi_Seq_inv in HReadOnly.
    destruct HReadOnly as [HReadOnlyLabel HReadOnlyTail].
    pose proof
      (Step_readonly_replay_on_heap_agreement
        state label state1 heap_summary HStep HReadOnlyLabel) as HStepReplay.
    assert (HAgreeLabel :
      HeterogeneousHeapForPhi (label_phi label)
        (state_heap state) heap_summary).
    {
      eapply HeterogeneousHeapForPhi_seq_left; eauto.
    }
    specialize (HStepReplay HAgreeLabel).
    assert (HHeapStep : state_heap state = state_heap state1).
    {
      eapply StepsPhi_readonly_preserves_heap.
      - exact
          (StepsPhi_Step state label state1 Phi_Nil state1
            HStep (StepsPhi_Refl state1)).
      - apply Phi_RO_Seq; [exact HReadOnlyLabel | constructor].
    }
    econstructor.
    + exact HStepReplay.
    + apply IH.
      * exact HReadOnlyTail.
      * rewrite <- HHeapStep.
        eapply HeterogeneousHeapForPhi_seq_right; eauto.
Qed.

Lemma StepsPhi_readonly_replay_on_lookup_equivalent_heap :
  forall state phi state' heap_summary,
    StepsPhi state phi state' ->
    ReadOnlyPhi phi ->
    HeapLookupEquivalent (state_heap state) heap_summary ->
    StepsPhi (with_state_heap heap_summary state) phi
      (with_state_heap heap_summary state').
Proof.
  intros state phi state' heap_summary HSteps HReadOnly HLookup.
  eapply StepsPhi_readonly_replay_on_heap_agreement; eauto.
  unfold HeterogeneousHeapForPhi, HeterogeneousHeapOn.
  intros k _.
  exact (HLookup k).
Qed.

Lemma StepsPhi_readonly_replay_terminal_on_lookup_equivalent_heap :
  forall heap heap_summary_start env rho e phi heap_summary v,
    HeapLookupEquivalent heap heap_summary_start ->
    StepsPhi (initial_state heap_summary_start env rho e) phi
      (StDone heap_summary v) ->
    ReadOnlyPhi phi ->
    StepsPhi (initial_state heap env rho e) phi (StDone heap v).
Proof.
  intros heap heap_summary_start env rho e phi heap_summary v
    HLookup HSteps HReadOnly.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap_summary_start env rho e) phi
      (StDone heap_summary v) HSteps HReadOnly) as HHeapSummary.
  simpl in HHeapSummary.
  subst heap_summary.
  pose proof
    (StepsPhi_readonly_replay_on_lookup_equivalent_heap
      (initial_state heap_summary_start env rho e) phi
      (StDone heap_summary_start v) heap
      HSteps HReadOnly) as HReplay.
  assert (HLookupSym :
    HeapLookupEquivalent (state_heap (initial_state heap_summary_start env rho e))
      heap).
  {
    simpl.
    intros k.
    symmetry.
    apply HLookup.
  }
  specialize (HReplay HLookupSym).
  simpl in HReplay.
  exact HReplay.
Qed.

Lemma ReadOnlyPhi_app_list_left :
  forall phi phi_left phi_right,
    ReadOnlyPhi phi ->
    phi_as_list phi = phi_as_list phi_left ++ phi_as_list phi_right ->
    ReadOnlyPhi phi_left.
Proof.
  intros phi phi_left phi_right HReadOnly HList.
  eapply ReadOnlyPhi_of_phi_as_list_included; eauto.
  intros da HIn.
  rewrite HList.
  apply in_or_app.
  now left.
Qed.

Lemma ReadOnlyPhi_app_list_right :
  forall phi phi_left phi_right,
    ReadOnlyPhi phi ->
    phi_as_list phi = phi_as_list phi_left ++ phi_as_list phi_right ->
    ReadOnlyPhi phi_right.
Proof.
  intros phi phi_left phi_right HReadOnly HList.
  eapply ReadOnlyPhi_of_phi_as_list_included; eauto.
  intros da HIn.
  rewrite HList.
  apply in_or_app.
  now right.
Qed.

Lemma ReadOnlyPhi_app_list3_left :
  forall phi phi1 phi2 phi3,
    ReadOnlyPhi phi ->
    phi_as_list phi =
      phi_as_list phi1 ++ phi_as_list phi2 ++ phi_as_list phi3 ->
    ReadOnlyPhi phi1.
Proof.
  intros phi phi1 phi2 phi3 HReadOnly HList.
  eapply ReadOnlyPhi_of_phi_as_list_included; eauto.
  intros da HIn.
  rewrite HList.
  apply in_or_app.
  now left.
Qed.

Lemma ReadOnlyPhi_app_list3_middle :
  forall phi phi1 phi2 phi3,
    ReadOnlyPhi phi ->
    phi_as_list phi =
      phi_as_list phi1 ++ phi_as_list phi2 ++ phi_as_list phi3 ->
    ReadOnlyPhi phi2.
Proof.
  intros phi phi1 phi2 phi3 HReadOnly HList.
  eapply ReadOnlyPhi_of_phi_as_list_included; eauto.
  intros da HIn.
  rewrite HList.
  apply in_or_app.
  right.
  apply in_or_app.
  now left.
Qed.

Lemma ReadOnlyPhi_app_list3_right :
  forall phi phi1 phi2 phi3,
    ReadOnlyPhi phi ->
    phi_as_list phi =
      phi_as_list phi1 ++ phi_as_list phi2 ++ phi_as_list phi3 ->
    ReadOnlyPhi phi3.
Proof.
  intros phi phi1 phi2 phi3 HReadOnly HList.
  eapply ReadOnlyPhi_of_phi_as_list_included; eauto.
  intros da HIn.
  rewrite HList.
  apply in_or_app.
  right.
  apply in_or_app.
  now right.
Qed.

Theorem StepsPhi_initial_terminal_value_typed :
  forall heap env rho e stty ctxt rgns ty static phi heap' v,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty, static) ->
    StepsPhi (initial_state heap env rho e) phi (StDone heap' v) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, subst_rho rho ty) /\
      RuntimeValShape stty' (subst_rho rho ty) v.
Proof.
  intros heap env rho e stty ctxt rgns ty static phi heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps.
  destruct
    (WTStateEffectAt_initial_terminal_trace_budget
      heap env rho e stty ctxt rgns ty static
      (phi_as_list phi) heap' v
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp
      (StepsPhi_as_steps _ _ _ HSteps))
    as (stty' & HExt & HTcHeap' & HHeapShape' & HTcVal' &
        HValShape' & _).
  exists stty'.
  split; [exact HExt |].
  split; [exact HTcHeap' |].
  split; [exact HHeapShape' |].
  split; [exact HTcVal' | exact HValShape'].
Qed.

Lemma TcHeap_same_heap_store_extends_back :
  forall heap stty stty',
    TcHeap (heap, stty) ->
    TcHeap (heap, stty') ->
    StoreExtends stty stty' ->
    StoreExtends stty' stty.
Proof.
  intros heap stty stty' HTcHeap HTcHeap' HExt k t HFind'.
  inversion HTcHeap as [? ? HHeapStore _ _]; subst.
  inversion HTcHeap' as [? ? _ HStoreHeap' _]; subst.
  destruct (HStoreHeap' k t HFind') as (v & HFindHeap).
  destruct (HHeapStore k v HFindHeap) as (t0 & HFindBase).
  pose proof (HExt k t0 HFindBase) as HFindExt.
  assert (t = t0) by (eapply PairType_unique_type; eauto).
  subst. exact HFindBase.
Qed.

Theorem StepsPhi_typed_readonly_static_preserves_heap :
  forall heap env rho e stty ctxt rgns ty static phi heap' v,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty, static) ->
    StepsPhi (initial_state heap env rho e) phi (StDone heap' v) ->
    ReadOnlyStatic (fold_subst_eps rho static) ->
    heap' = heap.
Proof.
  intros heap env rho e stty ctxt rgns ty static phi heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps
    HReadOnlyStatic.
  pose proof
    (small_step_eff_sound
      heap env rho e stty ctxt rgns ty static
      (phi_as_list phi) heap' v
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp
      (StepsPhi_as_steps _ _ _ HSteps)) as HSoundTrace.
  pose proof
    (Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list
      (fold_subst_eps rho static) phi HSoundTrace) as HSoundPhi.
  pose proof
    (ReadOnlyStaticImpliesReadOnlyPhi
      (fold_subst_eps rho static) phi HReadOnlyStatic HSoundPhi)
    as HReadOnlyPhi.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho e) phi (StDone heap' v)
      HSteps HReadOnlyPhi) as HHeap.
  simpl in HHeap.
  now symmetry.
Qed.

Theorem StepsPhi_typed_readonly_static_readonly_phi :
  forall heap env rho e stty ctxt rgns ty static phi heap' v,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty, static) ->
    StepsPhi (initial_state heap env rho e) phi (StDone heap' v) ->
    ReadOnlyStatic (fold_subst_eps rho static) ->
    ReadOnlyPhi phi.
Proof.
  intros heap env rho e stty ctxt rgns ty static phi heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps
    HReadOnlyStatic.
  pose proof
    (small_step_eff_sound
      heap env rho e stty ctxt rgns ty static
      (phi_as_list phi) heap' v
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp
      (StepsPhi_as_steps _ _ _ HSteps)) as HSoundTrace.
  pose proof
    (Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list
      (fold_subst_eps rho static) phi HSoundTrace) as HSoundPhi.
  eapply ReadOnlyStaticImpliesReadOnlyPhi; eauto.
Qed.

Theorem StepsPhi_typed_readonly_terminal_value_typed_base :
  forall heap env rho e stty ctxt rgns ty static phi heap' v,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty, static) ->
    StepsPhi (initial_state heap env rho e) phi (StDone heap' v) ->
    ReadOnlyStatic (fold_subst_eps rho static) ->
    heap' = heap /\
    TcVal (stty, v, subst_rho rho ty) /\
    RuntimeValShape stty (subst_rho rho ty) v.
Proof.
  intros heap env rho e stty ctxt rgns ty static phi heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps
    HReadOnlyStatic.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho e stty ctxt rgns ty static phi heap' v
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps
      HReadOnlyStatic) as HHeapEq.
  destruct
    (StepsPhi_initial_terminal_value_typed
      heap env rho e stty ctxt rgns ty static phi heap' v
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps)
    as (stty' & HExt & HTcHeap' & _ & HTcVal' & HValShape').
  subst heap'.
  pose proof
    (TcHeap_same_heap_store_extends_back heap stty stty'
      HTcHeap HTcHeap' HExt) as HExtBack.
  split; [reflexivity |].
  split.
  - eapply ext_stores__val; eauto.
  - eapply RuntimeValShape_store_ext; eauto.
Qed.

Theorem StepsPhi_mixed_readonly_terminal_value_typed_base :
  forall heap env rho e stty ctxt rgns
         ty_shape static_shape ty_readonly static_readonly phi heap' v,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty_shape, static_shape) ->
    TcExp (ctxt, rgns, e, ty_readonly, static_readonly) ->
    StepsPhi (initial_state heap env rho e) phi (StDone heap' v) ->
    ReadOnlyStatic (fold_subst_eps rho static_readonly) ->
    heap' = heap /\
    TcVal (stty, v, subst_rho rho ty_shape) /\
    RuntimeValShape stty (subst_rho rho ty_shape) v.
Proof.
  intros heap env rho e stty ctxt rgns
    ty_shape static_shape ty_readonly static_readonly phi heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcShape HTcReadonly HSteps HReadOnlyStatic.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho e stty ctxt rgns ty_readonly static_readonly
      phi heap' v
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcReadonly
      HSteps HReadOnlyStatic) as HHeapEq.
  destruct
    (StepsPhi_initial_terminal_value_typed
      heap env rho e stty ctxt rgns ty_shape static_shape
      phi heap' v
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcShape HSteps)
    as (stty' & HExt & HTcHeap' & _ & HTcVal' & HValShape').
  subst heap'.
  pose proof
    (TcHeap_same_heap_store_extends_back heap stty stty'
      HTcHeap HTcHeap' HExt) as HExtBack.
  split; [reflexivity |].
  split.
  - eapply ext_stores__val; eauto.
  - eapply RuntimeValShape_store_ext; eauto.
Qed.

Lemma initial_const_steps_done :
  forall heap env rho n,
    Steps (initial_state heap env rho (Const n)) nil
      (StDone heap (Num n)).
Proof.
  intros heap env rho n.
  apply initial_silent_return_steps_done.
  constructor.
Qed.

Lemma initial_bool_steps_done :
  forall heap env rho b,
    Steps (initial_state heap env rho (Bool b)) nil
      (StDone heap (Bit b)).
Proof.
  intros heap env rho b.
  apply initial_silent_return_steps_done.
  constructor.
Qed.

Lemma initial_var_steps_done :
  forall heap env rho x v,
    find_E x env = Some v ->
    Steps (initial_state heap env rho (Var x)) nil
      (StDone heap v).
Proof.
  intros heap env rho x v HFind.
  apply initial_silent_return_steps_done.
  now constructor.
Qed.

Lemma initial_mu_steps_done :
  forall heap env rho f x ec ee,
    Steps (initial_state heap env rho (Mu f x ec ee)) nil
      (StDone heap (Cls (env, rho, Mu f x ec ee))).
Proof.
  intros heap env rho f x ec ee.
  apply initial_silent_return_steps_done.
  constructor.
Qed.

Lemma initial_lambda_steps_done :
  forall heap env rho x e,
    Steps (initial_state heap env rho (Lambda x e)) nil
      (StDone heap (Cls (env, rho, Lambda x e))).
Proof.
  intros heap env rho x e.
  apply initial_silent_return_steps_done.
  constructor.
Qed.

Lemma initial_empty_steps_done :
  forall heap env rho,
    Steps (initial_state heap env rho Empty) nil
      (StDone heap (Eff Theta_Empty)).
Proof.
  intros heap env rho.
  unfold Theta_Empty.
  apply initial_silent_return_steps_done.
  constructor.
Qed.

Lemma initial_empty_steps_phi_done :
  forall heap env rho,
    StepsPhi (initial_state heap env rho Empty)
      (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))
      (StDone heap (Eff Theta_Empty)).
Proof.
  intros heap env rho.
  unfold initial_state, Theta_Empty.
  eapply StepsPhi_Step.
  - constructor.
  - eapply StepsPhi_Step.
    + constructor.
    + constructor.
Qed.

Lemma initial_top_steps_done :
  forall heap env rho,
    Steps (initial_state heap env rho Top) nil
      (StDone heap (Eff Theta_Top)).
Proof.
  intros heap env rho.
  unfold Theta_Top.
  apply initial_silent_return_steps_done.
  constructor.
Qed.

Lemma initial_allocabs_steps_done :
  forall heap env rho w r,
    find_R w rho = Some r ->
    Steps (initial_state heap env rho (AllocAbs w)) nil
      (StDone heap (Eff (Some (singleton_set (CA_AllocAbs r))))).
Proof.
  intros heap env rho w r HFind.
  apply initial_silent_return_steps_done.
  now constructor.
Qed.

Lemma initial_readabs_steps_done :
  forall heap env rho w r,
    find_R w rho = Some r ->
    Steps (initial_state heap env rho (ReadAbs w)) nil
      (StDone heap (Eff (Some (singleton_set (CA_ReadAbs r))))).
Proof.
  intros heap env rho w r HFind.
  apply initial_silent_return_steps_done.
  now constructor.
Qed.

Lemma initial_writeabs_steps_done :
  forall heap env rho w r,
    find_R w rho = Some r ->
    Steps (initial_state heap env rho (WriteAbs w)) nil
      (StDone heap (Eff (Some (singleton_set (CA_WriteAbs r))))).
Proof.
  intros heap env rho w r HFind.
  apply initial_silent_return_steps_done.
  now constructor.
Qed.

Lemma StepsPhi_initial_const_terminal_trace_nil :
  forall heap env rho n phi heap' v,
    StepsPhi (initial_state heap env rho (Const n)) phi (StDone heap' v) ->
    phi_as_list phi = nil.
Proof.
  intros heap env rho n phi heap' v HStepsPhi.
  eapply StepsPhi_terminal_trace_nil_from_nil_steps; eauto.
  apply initial_const_steps_done.
Qed.

Lemma StepsPhi_initial_bool_terminal_trace_nil :
  forall heap env rho b phi heap' v,
    StepsPhi (initial_state heap env rho (Bool b)) phi (StDone heap' v) ->
    phi_as_list phi = nil.
Proof.
  intros heap env rho b phi heap' v HStepsPhi.
  eapply StepsPhi_terminal_trace_nil_from_nil_steps; eauto.
  apply initial_bool_steps_done.
Qed.

Lemma StepsPhi_initial_var_terminal_trace_nil :
  forall heap env rho x v_lookup phi heap' v,
    find_E x env = Some v_lookup ->
    StepsPhi (initial_state heap env rho (Var x)) phi (StDone heap' v) ->
    phi_as_list phi = nil.
Proof.
  intros heap env rho x v_lookup phi heap' v HFind HStepsPhi.
  eapply StepsPhi_terminal_trace_nil_from_nil_steps; eauto.
  eapply initial_var_steps_done.
  exact HFind.
Qed.

Lemma StepsPhi_initial_mu_terminal_trace_nil :
  forall heap env rho f x ec ee phi heap' v,
    StepsPhi (initial_state heap env rho (Mu f x ec ee)) phi
      (StDone heap' v) ->
    phi_as_list phi = nil.
Proof.
  intros heap env rho f x ec ee phi heap' v HStepsPhi.
  eapply StepsPhi_terminal_trace_nil_from_nil_steps; eauto.
  apply initial_mu_steps_done.
Qed.

Lemma StepsPhi_initial_lambda_terminal_trace_nil :
  forall heap env rho x e phi heap' v,
    StepsPhi (initial_state heap env rho (Lambda x e)) phi
      (StDone heap' v) ->
    phi_as_list phi = nil.
Proof.
  intros heap env rho x e phi heap' v HStepsPhi.
  eapply StepsPhi_terminal_trace_nil_from_nil_steps; eauto.
  apply initial_lambda_steps_done.
Qed.

Lemma StepsPhi_initial_empty_terminal :
  forall heap env rho phi heap' theta,
    StepsPhi (initial_state heap env rho Empty) phi
      (StDone heap' (Eff theta)) ->
    phi_as_list phi = nil /\ heap' = heap /\ theta = Theta_Empty.
Proof.
  intros heap env rho phi heap' theta HStepsPhi.
  pose proof (initial_empty_steps_done heap env rho) as HEmptySteps.
  pose proof (StepsPhi_as_steps _ _ _ HStepsPhi) as HSteps.
  destruct
    (Steps_terminal_deterministic
      (initial_state heap env rho Empty)
      nil heap (Eff Theta_Empty)
      (phi_as_list phi) heap' (Eff theta)
      HEmptySteps HSteps)
    as [HTrace [HHeap HVal]].
  inversion HVal; subst.
  split.
  - now symmetry.
  - split.
    + now symmetry.
    + reflexivity.
Qed.

Lemma StepsPhi_initial_top_terminal :
  forall heap env rho phi heap' theta,
    StepsPhi (initial_state heap env rho Top) phi
      (StDone heap' (Eff theta)) ->
    phi_as_list phi = nil /\ heap' = heap /\ theta = Theta_Top.
Proof.
  intros heap env rho phi heap' theta HStepsPhi.
  pose proof (initial_top_steps_done heap env rho) as HTopSteps.
  pose proof (StepsPhi_as_steps _ _ _ HStepsPhi) as HSteps.
  destruct
    (Steps_terminal_deterministic
      (initial_state heap env rho Top)
      nil heap (Eff Theta_Top)
      (phi_as_list phi) heap' (Eff theta)
      HTopSteps HSteps)
    as [HTrace [HHeap HVal]].
  inversion HVal; subst.
  split.
  - now symmetry.
  - split.
    + now symmetry.
    + reflexivity.
Qed.

Lemma StepsPhi_initial_allocabs_terminal :
  forall heap env rho w r phi heap' theta,
    find_R w rho = Some r ->
    StepsPhi (initial_state heap env rho (AllocAbs w)) phi
      (StDone heap' (Eff theta)) ->
    phi_as_list phi = nil /\
    heap' = heap /\
    theta = Some (singleton_set (CA_AllocAbs r)).
Proof.
  intros heap env rho w r phi heap' theta HFind HStepsPhi.
  pose proof (initial_allocabs_steps_done heap env rho w r HFind) as HAbsSteps.
  pose proof (StepsPhi_as_steps _ _ _ HStepsPhi) as HSteps.
  destruct
    (Steps_terminal_deterministic
      (initial_state heap env rho (AllocAbs w))
      nil heap (Eff (Some (singleton_set (CA_AllocAbs r))))
      (phi_as_list phi) heap' (Eff theta)
      HAbsSteps HSteps)
    as [HTrace [HHeap HVal]].
  inversion HVal; subst.
  split.
  - now symmetry.
  - split.
    + now symmetry.
    + reflexivity.
Qed.

Lemma StepsPhi_initial_readabs_terminal :
  forall heap env rho w r phi heap' theta,
    find_R w rho = Some r ->
    StepsPhi (initial_state heap env rho (ReadAbs w)) phi
      (StDone heap' (Eff theta)) ->
    phi_as_list phi = nil /\
    heap' = heap /\
    theta = Some (singleton_set (CA_ReadAbs r)).
Proof.
  intros heap env rho w r phi heap' theta HFind HStepsPhi.
  pose proof (initial_readabs_steps_done heap env rho w r HFind) as HAbsSteps.
  pose proof (StepsPhi_as_steps _ _ _ HStepsPhi) as HSteps.
  destruct
    (Steps_terminal_deterministic
      (initial_state heap env rho (ReadAbs w))
      nil heap (Eff (Some (singleton_set (CA_ReadAbs r))))
      (phi_as_list phi) heap' (Eff theta)
      HAbsSteps HSteps)
    as [HTrace [HHeap HVal]].
  inversion HVal; subst.
  split.
  - now symmetry.
  - split.
    + now symmetry.
    + reflexivity.
Qed.

Lemma StepsPhi_initial_writeabs_terminal :
  forall heap env rho w r phi heap' theta,
    find_R w rho = Some r ->
    StepsPhi (initial_state heap env rho (WriteAbs w)) phi
      (StDone heap' (Eff theta)) ->
    phi_as_list phi = nil /\
    heap' = heap /\
    theta = Some (singleton_set (CA_WriteAbs r)).
Proof.
  intros heap env rho w r phi heap' theta HFind HStepsPhi.
  pose proof (initial_writeabs_steps_done heap env rho w r HFind) as HAbsSteps.
  pose proof (StepsPhi_as_steps _ _ _ HStepsPhi) as HSteps.
  destruct
    (Steps_terminal_deterministic
      (initial_state heap env rho (WriteAbs w))
      nil heap (Eff (Some (singleton_set (CA_WriteAbs r))))
      (phi_as_list phi) heap' (Eff theta)
      HAbsSteps HSteps)
    as [HTrace [HHeap HVal]].
  inversion HVal; subst.
  split.
  - now symmetry.
  - split.
    + now symmetry.
    + reflexivity.
Qed.

Lemma StepsPhi_cond_true_from_guard_branch :
  forall heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch v,
    StepsPhi (initial_state heap env rho e) phi_guard
      (StDone heap_guard (Bit true)) ->
    StepsPhi (initial_state heap_guard env rho et) phi_branch
      (StDone heap_branch v) ->
    exists phi_cond,
      StepsPhi (initial_state heap env rho (Cond e et ef)) phi_cond
        (StDone heap_branch v) /\
      phi_as_list phi_cond =
        phi_as_list phi_guard ++ phi_as_list phi_branch.
Proof.
  intros heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch v HGuard HBranch.
  assert
    (HGuardContinue :
      StepsPhi
        (StEval heap env rho e (KCond et ef env rho KDone))
        phi_guard
        (initial_state heap_guard env rho et)).
  {
    unfold initial_state.
    eapply StepsPhi_initial_terminal_continue; eauto.
    apply Step_Cond_True.
  }
  destruct
    (StepsPhi_trans_exists
      (StEval heap env rho e (KCond et ef env rho KDone))
      phi_guard
      (initial_state heap_guard env rho et)
      phi_branch
      (StDone heap_branch v)
      HGuardContinue HBranch)
    as (phi_rest & HRest & HTrace).
  exists (Phi_Seq (label_phi Silent) phi_rest).
  split.
  - unfold initial_state.
    eapply StepsPhi_Step.
    + constructor.
    + exact HRest.
  - simpl. exact HTrace.
Qed.

Lemma StepsPhi_cond_false_from_guard_branch :
  forall heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch v,
    StepsPhi (initial_state heap env rho e) phi_guard
      (StDone heap_guard (Bit false)) ->
    StepsPhi (initial_state heap_guard env rho ef) phi_branch
      (StDone heap_branch v) ->
    exists phi_cond,
      StepsPhi (initial_state heap env rho (Cond e et ef)) phi_cond
        (StDone heap_branch v) /\
      phi_as_list phi_cond =
        phi_as_list phi_guard ++ phi_as_list phi_branch.
Proof.
  intros heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch v HGuard HBranch.
  assert
    (HGuardContinue :
      StepsPhi
        (StEval heap env rho e (KCond et ef env rho KDone))
        phi_guard
        (initial_state heap_guard env rho ef)).
  {
    unfold initial_state.
    eapply StepsPhi_initial_terminal_continue; eauto.
    apply Step_Cond_False.
  }
  destruct
    (StepsPhi_trans_exists
      (StEval heap env rho e (KCond et ef env rho KDone))
      phi_guard
      (initial_state heap_guard env rho ef)
      phi_branch
      (StDone heap_branch v)
      HGuardContinue HBranch)
    as (phi_rest & HRest & HTrace).
  exists (Phi_Seq (label_phi Silent) phi_rest).
  split.
  - unfold initial_state.
    eapply StepsPhi_Step.
    + constructor.
    + exact HRest.
  - simpl. exact HTrace.
Qed.

Lemma StepsPhi_cond_terminal_decompose :
  forall heap env rho e et ef phi heap_final v_final,
    StepsPhi (initial_state heap env rho (Cond e et ef)) phi
      (StDone heap_final v_final) ->
    (exists phi_guard heap_guard phi_branch heap_branch,
      StepsPhi (initial_state heap env rho e) phi_guard
        (StDone heap_guard (Bit true)) /\
      StepsPhi (initial_state heap_guard env rho et) phi_branch
        (StDone heap_branch v_final) /\
      heap_final = heap_branch /\
      phi_as_list phi =
        phi_as_list phi_guard ++ phi_as_list phi_branch) \/
    (exists phi_guard heap_guard phi_branch heap_branch,
      StepsPhi (initial_state heap env rho e) phi_guard
        (StDone heap_guard (Bit false)) /\
      StepsPhi (initial_state heap_guard env rho ef) phi_branch
        (StDone heap_branch v_final) /\
      heap_final = heap_branch /\
      phi_as_list phi =
        phi_as_list phi_guard ++ phi_as_list phi_branch).
Proof.
  intros heap env rho e et ef phi heap_final v_final HCond.
  assert
    (HFirst :
      Step (initial_state heap env rho (Cond e et ef)) Silent
        (StEval heap env rho e (KCond et ef env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Cond e et ef))
      Silent
      (StEval heap env rho e (KCond et ef env rho KDone))
      phi heap_final v_final HFirst HCond)
    as (phi_after_guard & HAfterGuard & HTraceStart).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho e (KCond et ef env rho KDone)
      phi_after_guard heap_final v_final HAfterGuard)
    as (heap_guard & v_guard & phi_guard & phi_after_branch &
        HGuard & HAfterBranch & HTraceGuard).
  inversion HAfterBranch as
    [| ? ? ? phi_branch ? HStepBranch HBranch];
    subst; try discriminate.
  destruct v_guard as [w l | n | b | cls | theta | | pair];
    inversion HStepBranch; subst.
  - left.
    exists phi_guard, heap_guard, phi_branch, heap_final.
    split; [exact HGuard |].
    split; [exact HBranch |].
    split; [reflexivity |].
    rewrite HTraceStart.
    simpl.
    rewrite HTraceGuard.
    simpl.
    reflexivity.
  - right.
    exists phi_guard, heap_guard, phi_branch, heap_final.
    split; [exact HGuard |].
    split; [exact HBranch |].
    split; [reflexivity |].
    rewrite HTraceStart.
    simpl.
    rewrite HTraceGuard.
	    simpl.
	    reflexivity.
Qed.

Lemma StepsPhiN_cond_terminal_decompose_counts :
  forall n heap env rho e et ef phi heap_final v_final,
    StepsPhiN n (initial_state heap env rho (Cond e et ef)) phi
      (StDone heap_final v_final) ->
    (exists n_guard phi_guard heap_guard
            n_branch phi_branch heap_branch,
      n_guard < n /\
      n_branch < n /\
      StepsPhiN n_guard (initial_state heap env rho e) phi_guard
        (StDone heap_guard (Bit true)) /\
      StepsPhiN n_branch (initial_state heap_guard env rho et) phi_branch
        (StDone heap_branch v_final) /\
      heap_final = heap_branch /\
      phi_as_list phi =
        phi_as_list phi_guard ++ phi_as_list phi_branch) \/
    (exists n_guard phi_guard heap_guard
            n_branch phi_branch heap_branch,
      n_guard < n /\
      n_branch < n /\
      StepsPhiN n_guard (initial_state heap env rho e) phi_guard
        (StDone heap_guard (Bit false)) /\
      StepsPhiN n_branch (initial_state heap_guard env rho ef) phi_branch
        (StDone heap_branch v_final) /\
      heap_final = heap_branch /\
      phi_as_list phi =
        phi_as_list phi_guard ++ phi_as_list phi_branch).
Proof.
  intros n heap env rho e et ef phi heap_final v_final HCond.
  assert
    (HFirst :
      Step (initial_state heap env rho (Cond e et ef)) Silent
        (StEval heap env rho e (KCond et ef env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhiN_terminal_inv_step
      n
      (initial_state heap env rho (Cond e et ef))
      Silent
      (StEval heap env rho e (KCond et ef env rho KDone))
      phi heap_final v_final HFirst HCond)
    as (n_after_guard & phi_after_guard & HNAfterGuard &
        HAfterGuard & HTraceStart).
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_guard heap env rho e (KCond et ef env rho KDone)
      phi_after_guard heap_final v_final HAfterGuard)
    as (n_guard & n_after_branch & heap_guard & v_guard &
        phi_guard & phi_after_branch &
        HLeGuard & HLeAfterBranch & HGuard & HAfterBranch & HTraceGuard).
  inversion HAfterBranch as
    [| n_branch state_branch label_branch state_after_branch
       phi_branch final_branch HStepBranch HBranch];
    subst; try discriminate.
  destruct v_guard as [w l | n_guard_value | b | cls | theta | | pair];
    inversion HStepBranch; subst.
  - left.
    exists n_guard, phi_guard, heap_guard,
      n_branch, phi_branch, heap_final.
    split; [lia |].
    split; [lia |].
    split; [exact HGuard |].
    split; [exact HBranch |].
    split; [reflexivity |].
    rewrite HTraceStart.
    simpl.
    rewrite HTraceGuard.
    simpl.
    reflexivity.
  - right.
    exists n_guard, phi_guard, heap_guard,
      n_branch, phi_branch, heap_final.
    split; [lia |].
    split; [lia |].
    split; [exact HGuard |].
    split; [exact HBranch |].
    split; [reflexivity |].
    rewrite HTraceStart.
    simpl.
    rewrite HTraceGuard.
    simpl.
    reflexivity.
Qed.

Lemma StepsPhi_binary_from_left_right :
  forall heap env rho ebin e1 e2 k_left k_right
    v_left v_right v_result
    phi_left heap_left phi_right heap_right,
    Step (StEval heap env rho ebin KDone) Silent
      (StEval heap env rho e1 k_left) ->
    Step (StReturn heap_left v_left k_left) Silent
      (StEval heap_left env rho e2 k_right) ->
    Step (StReturn heap_right v_right k_right) Silent
      (StReturn heap_right v_result KDone) ->
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left v_left) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right v_right) ->
    exists phi_bin,
      StepsPhi (initial_state heap env rho ebin) phi_bin
        (StDone heap_right v_result) /\
      phi_as_list phi_bin =
        phi_as_list phi_left ++ phi_as_list phi_right.
Proof.
  intros heap env rho ebin e1 e2 k_left k_right
    v_left v_right v_result
    phi_left heap_left phi_right heap_right
    HStepStart HStepLeft HStepRight HLeft HRight.
  assert
    (HLeftContinue :
      StepsPhi
        (StEval heap env rho e1 k_left)
        phi_left
        (StEval heap_left env rho e2 k_right)).
  {
    eapply StepsPhi_initial_terminal_continue; eauto.
  }
  assert
    (HRightContinue :
      StepsPhi
        (StEval heap_left env rho e2 k_right)
        phi_right
        (StReturn heap_right v_result KDone)).
  {
    eapply StepsPhi_initial_terminal_continue; eauto.
  }
  assert
    (HDone :
      StepsPhi
        (StReturn heap_right v_result KDone)
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (StDone heap_right v_result)).
  {
    eapply StepsPhi_Step.
    - constructor.
    - constructor.
  }
  destruct
    (StepsPhi_trans_exists
      (StEval heap_left env rho e2 k_right)
      phi_right
      (StReturn heap_right v_result KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      (StDone heap_right v_result)
      HRightContinue HDone)
    as (phi_right_done & HRightDone & HRightTrace).
  destruct
    (StepsPhi_trans_exists
      (StEval heap env rho e1 k_left)
      phi_left
      (StEval heap_left env rho e2 k_right)
      phi_right_done
      (StDone heap_right v_result)
      HLeftContinue HRightDone)
    as (phi_rest & HRest & HRestTrace).
  exists (Phi_Seq (label_phi Silent) phi_rest).
  split.
  - unfold initial_state.
    eapply StepsPhi_Step.
    + exact HStepStart.
    + exact HRest.
  - simpl.
    rewrite HRestTrace.
    rewrite HRightTrace.
    simpl.
    now rewrite app_nil_r.
Qed.

Lemma StepsPhi_plus_from_left_right :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    exists phi_plus,
      StepsPhi (initial_state heap env rho (Plus e1 e2)) phi_plus
        (StDone heap_right (Num (n1 + n2))) /\
      phi_as_list phi_plus =
        phi_as_list phi_left ++ phi_as_list phi_right.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 HLeft HRight.
  eapply StepsPhi_binary_from_left_right; eauto; constructor.
Qed.

Lemma StepsPhi_plus_terminal_decompose :
  forall heap env rho e1 e2 phi heap_final v_final,
    StepsPhi (initial_state heap env rho (Plus e1 e2)) phi
      (StDone heap_final v_final) ->
    exists phi_left heap_left n1 phi_right heap_right n2,
      StepsPhi (initial_state heap env rho e1) phi_left
        (StDone heap_left (Num n1)) /\
      StepsPhi (initial_state heap_left env rho e2) phi_right
        (StDone heap_right (Num n2)) /\
      heap_final = heap_right /\
      v_final = Num (n1 + n2).
Proof.
  intros heap env rho e1 e2 phi heap_final v_final HPlus.
  assert
    (HFirst :
      Step (initial_state heap env rho (Plus e1 e2)) Silent
        (StEval heap env rho e1 (KPlusL e2 env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Plus e1 e2))
      Silent
      (StEval heap env rho e1 (KPlusL e2 env rho KDone))
      phi heap_final v_final HFirst HPlus)
    as (phi_after_left & HAfterLeft & _).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho e1 (KPlusL e2 env rho KDone)
      phi_after_left heap_final v_final HAfterLeft)
    as (heap_left & v_left & phi_left & phi_after_right &
        HLeft & HAfterRight & _).
  inversion HAfterRight as
    [| ? ? ? phi_after_right_tail ? HStepRight HStepsRight];
    subst; try discriminate.
  destruct v_left as [w l | n1 | b | cls | theta | | pair];
    inversion HStepRight; subst.
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap_left env rho e2 (KPlusR n1 KDone)
      phi_after_right_tail heap_final v_final HStepsRight)
    as (heap_right & v_right & phi_right & phi_after_done &
        HRight & HAfterDone & _).
  inversion HAfterDone as
    [| ? ? ? phi_after_done_tail ? HStepDone HStepsDone];
    subst; try discriminate.
  destruct v_right as [w l | n2 | b | cls | theta | | pair];
    inversion HStepDone; subst.
  assert
    (HDone :
      StepsPhi
        (StReturn heap_right (Num (n1 + n2)) KDone)
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (StDone heap_right (Num (n1 + n2)))).
  {
    eapply StepsPhi_Step.
    - constructor.
    - constructor.
  }
  destruct
    (StepsPhi_terminal_deterministic
      (StReturn heap_right (Num (n1 + n2)) KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      heap_right (Num (n1 + n2))
      phi_after_done_tail heap_final v_final
      HDone HStepsDone)
    as [_ [HHeap HVal]].
  exists phi_left, heap_left, n1, phi_right, heap_right, n2.
  repeat split; try assumption; symmetry; assumption.
Qed.

Lemma StepsPhiN_plus_terminal_decompose_counts :
  forall n heap env rho e1 e2 phi heap_final v_final,
    StepsPhiN n (initial_state heap env rho (Plus e1 e2)) phi
      (StDone heap_final v_final) ->
    exists n_left phi_left heap_left n1
      n_right phi_right heap_right n2,
      n_left < n /\
      n_right < n /\
      StepsPhiN n_left (initial_state heap env rho e1) phi_left
        (StDone heap_left (Num n1)) /\
      StepsPhiN n_right (initial_state heap_left env rho e2) phi_right
        (StDone heap_right (Num n2)) /\
      heap_final = heap_right /\
      v_final = Num (n1 + n2) /\
      phi_as_list phi =
        phi_as_list phi_left ++ phi_as_list phi_right.
Proof.
  intros n heap env rho e1 e2 phi heap_final v_final HPlus.
  assert
    (HFirst :
      Step (initial_state heap env rho (Plus e1 e2)) Silent
        (StEval heap env rho e1 (KPlusL e2 env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhiN_terminal_inv_step
      n
      (initial_state heap env rho (Plus e1 e2))
      Silent
      (StEval heap env rho e1 (KPlusL e2 env rho KDone))
      phi heap_final v_final HFirst HPlus)
    as (n_after_left & phi_after_left & HNAfterLeft &
        HAfterLeft & HTraceStart).
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_left heap env rho e1 (KPlusL e2 env rho KDone)
      phi_after_left heap_final v_final HAfterLeft)
    as (n_left & n_after_right & heap_left & v_left &
        phi_left & phi_after_right &
        HLeLeft & HLeAfterRight & HLeft & HAfterRight & HTraceLeft).
  inversion HAfterRight as
    [| n_after_right_tail state_right label_right state_after_right
       phi_after_right_tail final_right HStepRight HStepsRight];
    subst; try discriminate.
  destruct v_left as [w l | n1 | b | cls | theta | | pair];
    inversion HStepRight; subst.
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_right_tail heap_left env rho e2 (KPlusR n1 KDone)
      phi_after_right_tail heap_final v_final HStepsRight)
    as (n_right & n_after_done & heap_right & v_right &
        phi_right & phi_after_done &
        HLeRight & HLeAfterDone & HRight & HAfterDone & HTraceRight).
  inversion HAfterDone as
    [| n_after_done_tail state_done label_done state_after_done
       phi_after_done_tail final_done HStepDone HStepsDone];
    subst; try discriminate.
  destruct v_right as [w l | n2 | b | cls | theta | | pair];
    inversion HStepDone; subst.
  assert
    (HDone :
      StepsPhiN 1
        (StReturn heap_right (Num (n1 + n2)) KDone)
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (StDone heap_right (Num (n1 + n2)))).
  {
    eapply StepsPhiN_Step.
    - constructor.
    - constructor.
  }
  destruct
    (StepsPhiN_terminal_deterministic
      1
      (StReturn heap_right (Num (n1 + n2)) KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      heap_right (Num (n1 + n2))
      n_after_done_tail phi_after_done_tail heap_final v_final
      HDone HStepsDone)
    as [_ [HTraceDone [HHeap HVal]]].
  exists n_left, phi_left, heap_left, n1,
    n_right, phi_right, heap_right, n2.
  split; [lia |].
  split; [lia |].
  split; [exact HLeft |].
  split; [exact HRight |].
  split; [symmetry; exact HHeap |].
  split; [symmetry; exact HVal |].
  rewrite HTraceStart.
  simpl.
  rewrite HTraceLeft.
  simpl.
  rewrite HTraceRight.
  simpl.
  rewrite <- HTraceDone.
  repeat rewrite app_assoc.
  now rewrite app_nil_r.
Qed.

Lemma StepsPhi_minus_from_left_right :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    exists phi_minus,
      StepsPhi (initial_state heap env rho (Minus e1 e2)) phi_minus
        (StDone heap_right (Num (n1 - n2))) /\
      phi_as_list phi_minus =
        phi_as_list phi_left ++ phi_as_list phi_right.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 HLeft HRight.
  eapply StepsPhi_binary_from_left_right; eauto; constructor.
Qed.

Lemma StepsPhi_minus_terminal_decompose :
  forall heap env rho e1 e2 phi heap_final v_final,
    StepsPhi (initial_state heap env rho (Minus e1 e2)) phi
      (StDone heap_final v_final) ->
    exists phi_left heap_left n1 phi_right heap_right n2,
      StepsPhi (initial_state heap env rho e1) phi_left
        (StDone heap_left (Num n1)) /\
      StepsPhi (initial_state heap_left env rho e2) phi_right
        (StDone heap_right (Num n2)) /\
      heap_final = heap_right /\
      v_final = Num (n1 - n2).
Proof.
  intros heap env rho e1 e2 phi heap_final v_final HMinus.
  assert
    (HFirst :
      Step (initial_state heap env rho (Minus e1 e2)) Silent
        (StEval heap env rho e1 (KMinusL e2 env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Minus e1 e2))
      Silent
      (StEval heap env rho e1 (KMinusL e2 env rho KDone))
      phi heap_final v_final HFirst HMinus)
    as (phi_after_left & HAfterLeft & _).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho e1 (KMinusL e2 env rho KDone)
      phi_after_left heap_final v_final HAfterLeft)
    as (heap_left & v_left & phi_left & phi_after_right &
        HLeft & HAfterRight & _).
  inversion HAfterRight as
    [| ? ? ? phi_after_right_tail ? HStepRight HStepsRight];
    subst; try discriminate.
  destruct v_left as [w l | n1 | b | cls | theta | | pair];
    inversion HStepRight; subst.
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap_left env rho e2 (KMinusR n1 KDone)
      phi_after_right_tail heap_final v_final HStepsRight)
    as (heap_right & v_right & phi_right & phi_after_done &
        HRight & HAfterDone & _).
  inversion HAfterDone as
    [| ? ? ? phi_after_done_tail ? HStepDone HStepsDone];
    subst; try discriminate.
  destruct v_right as [w l | n2 | b | cls | theta | | pair];
    inversion HStepDone; subst.
  assert
    (HDone :
      StepsPhi
        (StReturn heap_right (Num (n1 - n2)) KDone)
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (StDone heap_right (Num (n1 - n2)))).
  {
    eapply StepsPhi_Step.
    - constructor.
    - constructor.
  }
  destruct
    (StepsPhi_terminal_deterministic
      (StReturn heap_right (Num (n1 - n2)) KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      heap_right (Num (n1 - n2))
      phi_after_done_tail heap_final v_final
      HDone HStepsDone)
    as [_ [HHeap HVal]].
  exists phi_left, heap_left, n1, phi_right, heap_right, n2.
  repeat split; try assumption; symmetry; assumption.
Qed.

Lemma StepsPhiN_minus_terminal_decompose_counts :
  forall n heap env rho e1 e2 phi heap_final v_final,
    StepsPhiN n (initial_state heap env rho (Minus e1 e2)) phi
      (StDone heap_final v_final) ->
    exists n_left phi_left heap_left n1
      n_right phi_right heap_right n2,
      n_left < n /\
      n_right < n /\
      StepsPhiN n_left (initial_state heap env rho e1) phi_left
        (StDone heap_left (Num n1)) /\
      StepsPhiN n_right (initial_state heap_left env rho e2) phi_right
        (StDone heap_right (Num n2)) /\
      heap_final = heap_right /\
      v_final = Num (n1 - n2) /\
      phi_as_list phi =
        phi_as_list phi_left ++ phi_as_list phi_right.
Proof.
  intros n heap env rho e1 e2 phi heap_final v_final HMinus.
  assert
    (HFirst :
      Step (initial_state heap env rho (Minus e1 e2)) Silent
        (StEval heap env rho e1 (KMinusL e2 env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhiN_terminal_inv_step
      n
      (initial_state heap env rho (Minus e1 e2))
      Silent
      (StEval heap env rho e1 (KMinusL e2 env rho KDone))
      phi heap_final v_final HFirst HMinus)
    as (n_after_left & phi_after_left & HNAfterLeft &
        HAfterLeft & HTraceStart).
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_left heap env rho e1 (KMinusL e2 env rho KDone)
      phi_after_left heap_final v_final HAfterLeft)
    as (n_left & n_after_right & heap_left & v_left &
        phi_left & phi_after_right &
        HLeLeft & HLeAfterRight & HLeft & HAfterRight & HTraceLeft).
  inversion HAfterRight as
    [| n_after_right_tail state_right label_right state_after_right
       phi_after_right_tail final_right HStepRight HStepsRight];
    subst; try discriminate.
  destruct v_left as [w l | n1 | b | cls | theta | | pair];
    inversion HStepRight; subst.
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_right_tail heap_left env rho e2 (KMinusR n1 KDone)
      phi_after_right_tail heap_final v_final HStepsRight)
    as (n_right & n_after_done & heap_right & v_right &
        phi_right & phi_after_done &
        HLeRight & HLeAfterDone & HRight & HAfterDone & HTraceRight).
  inversion HAfterDone as
    [| n_after_done_tail state_done label_done state_after_done
       phi_after_done_tail final_done HStepDone HStepsDone];
    subst; try discriminate.
  destruct v_right as [w l | n2 | b | cls | theta | | pair];
    inversion HStepDone; subst.
  assert
    (HDone :
      StepsPhiN 1
        (StReturn heap_right (Num (n1 - n2)) KDone)
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (StDone heap_right (Num (n1 - n2)))).
  {
    eapply StepsPhiN_Step.
    - constructor.
    - constructor.
  }
  destruct
    (StepsPhiN_terminal_deterministic
      1
      (StReturn heap_right (Num (n1 - n2)) KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      heap_right (Num (n1 - n2))
      n_after_done_tail phi_after_done_tail heap_final v_final
      HDone HStepsDone)
    as [_ [HTraceDone [HHeap HVal]]].
  exists n_left, phi_left, heap_left, n1,
    n_right, phi_right, heap_right, n2.
  split; [lia |].
  split; [lia |].
  split; [exact HLeft |].
  split; [exact HRight |].
  split; [symmetry; exact HHeap |].
  split; [symmetry; exact HVal |].
  rewrite HTraceStart.
  simpl.
  rewrite HTraceLeft.
  simpl.
  rewrite HTraceRight.
  simpl.
  rewrite <- HTraceDone.
  repeat rewrite app_assoc.
  now rewrite app_nil_r.
Qed.

Lemma StepsPhi_times_from_left_right :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    exists phi_times,
      StepsPhi (initial_state heap env rho (Times e1 e2)) phi_times
        (StDone heap_right (Num (n1 * n2))) /\
      phi_as_list phi_times =
        phi_as_list phi_left ++ phi_as_list phi_right.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 HLeft HRight.
  eapply StepsPhi_binary_from_left_right; eauto; constructor.
Qed.

Lemma StepsPhi_times_terminal_decompose :
  forall heap env rho e1 e2 phi heap_final v_final,
    StepsPhi (initial_state heap env rho (Times e1 e2)) phi
      (StDone heap_final v_final) ->
    exists phi_left heap_left n1 phi_right heap_right n2,
      StepsPhi (initial_state heap env rho e1) phi_left
        (StDone heap_left (Num n1)) /\
      StepsPhi (initial_state heap_left env rho e2) phi_right
        (StDone heap_right (Num n2)) /\
      heap_final = heap_right /\
      v_final = Num (n1 * n2).
Proof.
  intros heap env rho e1 e2 phi heap_final v_final HTimes.
  assert
    (HFirst :
      Step (initial_state heap env rho (Times e1 e2)) Silent
        (StEval heap env rho e1 (KTimesL e2 env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Times e1 e2))
      Silent
      (StEval heap env rho e1 (KTimesL e2 env rho KDone))
      phi heap_final v_final HFirst HTimes)
    as (phi_after_left & HAfterLeft & _).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho e1 (KTimesL e2 env rho KDone)
      phi_after_left heap_final v_final HAfterLeft)
    as (heap_left & v_left & phi_left & phi_after_right &
        HLeft & HAfterRight & _).
  inversion HAfterRight as
    [| ? ? ? phi_after_right_tail ? HStepRight HStepsRight];
    subst; try discriminate.
  destruct v_left as [w l | n1 | b | cls | theta | | pair];
    inversion HStepRight; subst.
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap_left env rho e2 (KTimesR n1 KDone)
      phi_after_right_tail heap_final v_final HStepsRight)
    as (heap_right & v_right & phi_right & phi_after_done &
        HRight & HAfterDone & _).
  inversion HAfterDone as
    [| ? ? ? phi_after_done_tail ? HStepDone HStepsDone];
    subst; try discriminate.
  destruct v_right as [w l | n2 | b | cls | theta | | pair];
    inversion HStepDone; subst.
  assert
    (HDone :
      StepsPhi
        (StReturn heap_right (Num (n1 * n2)) KDone)
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (StDone heap_right (Num (n1 * n2)))).
  {
    eapply StepsPhi_Step.
    - constructor.
    - constructor.
  }
  destruct
    (StepsPhi_terminal_deterministic
      (StReturn heap_right (Num (n1 * n2)) KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      heap_right (Num (n1 * n2))
      phi_after_done_tail heap_final v_final
      HDone HStepsDone)
    as [_ [HHeap HVal]].
  exists phi_left, heap_left, n1, phi_right, heap_right, n2.
  repeat split; try assumption; symmetry; assumption.
Qed.

Lemma StepsPhiN_times_terminal_decompose_counts :
  forall n heap env rho e1 e2 phi heap_final v_final,
    StepsPhiN n (initial_state heap env rho (Times e1 e2)) phi
      (StDone heap_final v_final) ->
    exists n_left phi_left heap_left n1
      n_right phi_right heap_right n2,
      n_left < n /\
      n_right < n /\
      StepsPhiN n_left (initial_state heap env rho e1) phi_left
        (StDone heap_left (Num n1)) /\
      StepsPhiN n_right (initial_state heap_left env rho e2) phi_right
        (StDone heap_right (Num n2)) /\
      heap_final = heap_right /\
      v_final = Num (n1 * n2) /\
      phi_as_list phi =
        phi_as_list phi_left ++ phi_as_list phi_right.
Proof.
  intros n heap env rho e1 e2 phi heap_final v_final HTimes.
  assert
    (HFirst :
      Step (initial_state heap env rho (Times e1 e2)) Silent
        (StEval heap env rho e1 (KTimesL e2 env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhiN_terminal_inv_step
      n
      (initial_state heap env rho (Times e1 e2))
      Silent
      (StEval heap env rho e1 (KTimesL e2 env rho KDone))
      phi heap_final v_final HFirst HTimes)
    as (n_after_left & phi_after_left & HNAfterLeft &
        HAfterLeft & HTraceStart).
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_left heap env rho e1 (KTimesL e2 env rho KDone)
      phi_after_left heap_final v_final HAfterLeft)
    as (n_left & n_after_right & heap_left & v_left &
        phi_left & phi_after_right &
        HLeLeft & HLeAfterRight & HLeft & HAfterRight & HTraceLeft).
  inversion HAfterRight as
    [| n_after_right_tail state_right label_right state_after_right
       phi_after_right_tail final_right HStepRight HStepsRight];
    subst; try discriminate.
  destruct v_left as [w l | n1 | b | cls | theta | | pair];
    inversion HStepRight; subst.
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_right_tail heap_left env rho e2 (KTimesR n1 KDone)
      phi_after_right_tail heap_final v_final HStepsRight)
    as (n_right & n_after_done & heap_right & v_right &
        phi_right & phi_after_done &
        HLeRight & HLeAfterDone & HRight & HAfterDone & HTraceRight).
  inversion HAfterDone as
    [| n_after_done_tail state_done label_done state_after_done
       phi_after_done_tail final_done HStepDone HStepsDone];
    subst; try discriminate.
  destruct v_right as [w l | n2 | b | cls | theta | | pair];
    inversion HStepDone; subst.
  assert
    (HDone :
      StepsPhiN 1
        (StReturn heap_right (Num (n1 * n2)) KDone)
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (StDone heap_right (Num (n1 * n2)))).
  {
    eapply StepsPhiN_Step.
    - constructor.
    - constructor.
  }
  destruct
    (StepsPhiN_terminal_deterministic
      1
      (StReturn heap_right (Num (n1 * n2)) KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      heap_right (Num (n1 * n2))
      n_after_done_tail phi_after_done_tail heap_final v_final
      HDone HStepsDone)
    as [_ [HTraceDone [HHeap HVal]]].
  exists n_left, phi_left, heap_left, n1,
    n_right, phi_right, heap_right, n2.
  split; [lia |].
  split; [lia |].
  split; [exact HLeft |].
  split; [exact HRight |].
  split; [symmetry; exact HHeap |].
  split; [symmetry; exact HVal |].
  rewrite HTraceStart.
  simpl.
  rewrite HTraceLeft.
  simpl.
  rewrite HTraceRight.
  simpl.
  rewrite <- HTraceDone.
  repeat rewrite app_assoc.
  now rewrite app_nil_r.
Qed.

Lemma StepsPhi_eq_from_left_right :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    exists phi_eq,
      StepsPhi (initial_state heap env rho (Eq e1 e2)) phi_eq
        (StDone heap_right (Bit (Nat.eqb n1 n2))) /\
      phi_as_list phi_eq =
        phi_as_list phi_left ++ phi_as_list phi_right.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 HLeft HRight.
  eapply StepsPhi_binary_from_left_right; eauto; constructor.
Qed.

Lemma StepsPhi_eq_terminal_decompose :
  forall heap env rho e1 e2 phi heap_final v_final,
    StepsPhi (initial_state heap env rho (Eq e1 e2)) phi
      (StDone heap_final v_final) ->
    exists phi_left heap_left n1 phi_right heap_right n2,
      StepsPhi (initial_state heap env rho e1) phi_left
        (StDone heap_left (Num n1)) /\
      StepsPhi (initial_state heap_left env rho e2) phi_right
        (StDone heap_right (Num n2)) /\
      heap_final = heap_right /\
      v_final = Bit (Nat.eqb n1 n2).
Proof.
  intros heap env rho e1 e2 phi heap_final v_final HEq.
  assert
    (HFirst :
      Step (initial_state heap env rho (Eq e1 e2)) Silent
        (StEval heap env rho e1 (KEqL e2 env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Eq e1 e2))
      Silent
      (StEval heap env rho e1 (KEqL e2 env rho KDone))
      phi heap_final v_final HFirst HEq)
    as (phi_after_left & HAfterLeft & _).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho e1 (KEqL e2 env rho KDone)
      phi_after_left heap_final v_final HAfterLeft)
    as (heap_left & v_left & phi_left & phi_after_right &
        HLeft & HAfterRight & _).
  inversion HAfterRight as
    [| ? ? ? phi_after_right_tail ? HStepRight HStepsRight];
    subst; try discriminate.
  destruct v_left as [w l | n1 | b | cls | theta | | pair];
    inversion HStepRight; subst.
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap_left env rho e2 (KEqR n1 KDone)
      phi_after_right_tail heap_final v_final HStepsRight)
    as (heap_right & v_right & phi_right & phi_after_done &
        HRight & HAfterDone & _).
  inversion HAfterDone as
    [| ? ? ? phi_after_done_tail ? HStepDone HStepsDone];
    subst; try discriminate.
  destruct v_right as [w l | n2 | b | cls | theta | | pair];
    inversion HStepDone; subst.
  assert
    (HDone :
      StepsPhi
        (StReturn heap_right (Bit (Nat.eqb n1 n2)) KDone)
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (StDone heap_right (Bit (Nat.eqb n1 n2)))).
  {
    eapply StepsPhi_Step.
    - constructor.
    - constructor.
  }
  destruct
    (StepsPhi_terminal_deterministic
      (StReturn heap_right (Bit (Nat.eqb n1 n2)) KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      heap_right (Bit (Nat.eqb n1 n2))
      phi_after_done_tail heap_final v_final
      HDone HStepsDone)
    as [_ [HHeap HVal]].
  exists phi_left, heap_left, n1, phi_right, heap_right, n2.
  repeat split; try assumption; symmetry; assumption.
Qed.

Lemma StepsPhiN_eq_terminal_decompose_counts :
  forall n heap env rho e1 e2 phi heap_final v_final,
    StepsPhiN n (initial_state heap env rho (Eq e1 e2)) phi
      (StDone heap_final v_final) ->
    exists n_left phi_left heap_left n1
      n_right phi_right heap_right n2,
      n_left < n /\
      n_right < n /\
      StepsPhiN n_left (initial_state heap env rho e1) phi_left
        (StDone heap_left (Num n1)) /\
      StepsPhiN n_right (initial_state heap_left env rho e2) phi_right
        (StDone heap_right (Num n2)) /\
      heap_final = heap_right /\
      v_final = Bit (Nat.eqb n1 n2) /\
      phi_as_list phi =
        phi_as_list phi_left ++ phi_as_list phi_right.
Proof.
  intros n heap env rho e1 e2 phi heap_final v_final HEq.
  assert
    (HFirst :
      Step (initial_state heap env rho (Eq e1 e2)) Silent
        (StEval heap env rho e1 (KEqL e2 env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhiN_terminal_inv_step
      n
      (initial_state heap env rho (Eq e1 e2))
      Silent
      (StEval heap env rho e1 (KEqL e2 env rho KDone))
      phi heap_final v_final HFirst HEq)
    as (n_after_left & phi_after_left & HNAfterLeft &
        HAfterLeft & HTraceStart).
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_left heap env rho e1 (KEqL e2 env rho KDone)
      phi_after_left heap_final v_final HAfterLeft)
    as (n_left & n_after_right & heap_left & v_left &
        phi_left & phi_after_right &
        HLeLeft & HLeAfterRight & HLeft & HAfterRight & HTraceLeft).
  inversion HAfterRight as
    [| n_after_right_tail state_right label_right state_after_right
       phi_after_right_tail final_right HStepRight HStepsRight];
    subst; try discriminate.
  destruct v_left as [w l | n1 | b | cls | theta | | pair];
    inversion HStepRight; subst.
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_right_tail heap_left env rho e2 (KEqR n1 KDone)
      phi_after_right_tail heap_final v_final HStepsRight)
    as (n_right & n_after_done & heap_right & v_right &
        phi_right & phi_after_done &
        HLeRight & HLeAfterDone & HRight & HAfterDone & HTraceRight).
  inversion HAfterDone as
    [| n_after_done_tail state_done label_done state_after_done
       phi_after_done_tail final_done HStepDone HStepsDone];
    subst; try discriminate.
  destruct v_right as [w l | n2 | b | cls | theta | | pair];
    inversion HStepDone; subst.
  assert
    (HDone :
      StepsPhiN 1
        (StReturn heap_right (Bit (Nat.eqb n1 n2)) KDone)
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (StDone heap_right (Bit (Nat.eqb n1 n2)))).
  {
    eapply StepsPhiN_Step.
    - constructor.
    - constructor.
  }
  destruct
    (StepsPhiN_terminal_deterministic
      1
      (StReturn heap_right (Bit (Nat.eqb n1 n2)) KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      heap_right (Bit (Nat.eqb n1 n2))
      n_after_done_tail phi_after_done_tail heap_final v_final
      HDone HStepsDone)
    as [_ [HTraceDone [HHeap HVal]]].
  exists n_left, phi_left, heap_left, n1,
    n_right, phi_right, heap_right, n2.
  split; [lia |].
  split; [lia |].
  split; [exact HLeft |].
  split; [exact HRight |].
  split; [symmetry; exact HHeap |].
  split; [symmetry; exact HVal |].
  rewrite HTraceStart.
  simpl.
  rewrite HTraceLeft.
  simpl.
  rewrite HTraceRight.
  simpl.
  rewrite <- HTraceDone.
  repeat rewrite app_assoc.
  now rewrite app_nil_r.
Qed.

Lemma StepsPhi_mu_app_from_fun_arg_body :
  forall heap env rho ef ea env_fun rho_fun f x ec ee
    phi_fun heap_fun phi_arg heap_arg v_arg phi_body heap_body v_body,
    StepsPhi (initial_state heap env rho ef) phi_fun
      (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) ->
    StepsPhi (initial_state heap_fun env rho ea) phi_arg
      (StDone heap_arg v_arg) ->
    StepsPhi
      (initial_state heap_arg
        (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
          (x, v_arg) env_fun)
        rho_fun ec) phi_body
      (StDone heap_body v_body) ->
    exists phi_app,
      StepsPhi (initial_state heap env rho (Mu_App ef ea)) phi_app
        (StDone heap_body v_body) /\
      phi_as_list phi_app =
        phi_as_list phi_fun ++ phi_as_list phi_arg ++ phi_as_list phi_body.
Proof.
  intros heap env rho ef ea env_fun rho_fun f x ec ee
    phi_fun heap_fun phi_arg heap_arg v_arg phi_body heap_body v_body
    HFun HArg HBody.
  assert
    (HFunContinue :
      StepsPhi
        (StEval heap env rho ef (KMuAppFun ea env rho KDone))
        phi_fun
        (StEval heap_fun env rho ea
          (KMuAppArg env_fun rho_fun f x ec ee KDone))).
  {
    eapply StepsPhi_initial_terminal_continue; eauto.
    constructor.
  }
  assert
    (HArgContinue :
      StepsPhi
        (StEval heap_fun env rho ea
          (KMuAppArg env_fun rho_fun f x ec ee KDone))
        phi_arg
        (initial_state heap_arg
          (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
            (x, v_arg) env_fun)
          rho_fun ec)).
  {
    unfold initial_state.
    eapply StepsPhi_initial_terminal_continue; eauto.
    constructor.
  }
  destruct
    (StepsPhi_trans_exists
      (StEval heap_fun env rho ea
        (KMuAppArg env_fun rho_fun f x ec ee KDone))
      phi_arg
      (initial_state heap_arg
        (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
          (x, v_arg) env_fun)
        rho_fun ec)
      phi_body
      (StDone heap_body v_body)
      HArgContinue HBody)
    as (phi_arg_body & HArgBody & HArgBodyTrace).
  destruct
    (StepsPhi_trans_exists
      (StEval heap env rho ef (KMuAppFun ea env rho KDone))
      phi_fun
      (StEval heap_fun env rho ea
        (KMuAppArg env_fun rho_fun f x ec ee KDone))
      phi_arg_body
      (StDone heap_body v_body)
      HFunContinue HArgBody)
    as (phi_rest & HRest & HRestTrace).
  exists (Phi_Seq (label_phi Silent) phi_rest).
  split.
  - unfold initial_state.
    eapply StepsPhi_Step.
    + constructor.
    + exact HRest.
  - simpl.
    rewrite HRestTrace.
    rewrite HArgBodyTrace.
    now rewrite app_assoc.
Qed.

Lemma StepsPhi_eff_app_from_fun_arg_body :
  forall heap env rho ef ea env_fun rho_fun f x ec ee
    phi_fun heap_fun phi_arg heap_arg v_arg phi_body heap_body v_body,
    StepsPhi (initial_state heap env rho ef) phi_fun
      (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) ->
    StepsPhi (initial_state heap_fun env rho ea) phi_arg
      (StDone heap_arg v_arg) ->
    StepsPhi
      (initial_state heap_arg
        (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
          (x, v_arg) env_fun)
        rho_fun ee) phi_body
      (StDone heap_body v_body) ->
    exists phi_app,
      StepsPhi (initial_state heap env rho (Eff_App ef ea)) phi_app
        (StDone heap_body v_body) /\
      phi_as_list phi_app =
        phi_as_list phi_fun ++ phi_as_list phi_arg ++ phi_as_list phi_body.
Proof.
  intros heap env rho ef ea env_fun rho_fun f x ec ee
    phi_fun heap_fun phi_arg heap_arg v_arg phi_body heap_body v_body
    HFun HArg HBody.
  assert
    (HFunContinue :
      StepsPhi
        (StEval heap env rho ef (KEffAppFun ea env rho KDone))
        phi_fun
        (StEval heap_fun env rho ea
          (KEffAppArg env_fun rho_fun f x ec ee KDone))).
  {
    eapply StepsPhi_initial_terminal_continue; eauto.
    constructor.
  }
  assert
    (HArgContinue :
      StepsPhi
        (StEval heap_fun env rho ea
          (KEffAppArg env_fun rho_fun f x ec ee KDone))
        phi_arg
        (initial_state heap_arg
          (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
            (x, v_arg) env_fun)
          rho_fun ee)).
  {
    unfold initial_state.
    eapply StepsPhi_initial_terminal_continue; eauto.
    constructor.
  }
  destruct
    (StepsPhi_trans_exists
      (StEval heap_fun env rho ea
        (KEffAppArg env_fun rho_fun f x ec ee KDone))
      phi_arg
      (initial_state heap_arg
        (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
          (x, v_arg) env_fun)
        rho_fun ee)
      phi_body
      (StDone heap_body v_body)
      HArgContinue HBody)
    as (phi_arg_body & HArgBody & HArgBodyTrace).
  destruct
    (StepsPhi_trans_exists
      (StEval heap env rho ef (KEffAppFun ea env rho KDone))
      phi_fun
      (StEval heap_fun env rho ea
        (KEffAppArg env_fun rho_fun f x ec ee KDone))
      phi_arg_body
      (StDone heap_body v_body)
      HFunContinue HArgBody)
    as (phi_rest & HRest & HRestTrace).
  exists (Phi_Seq (label_phi Silent) phi_rest).
  split.
  - unfold initial_state.
    eapply StepsPhi_Step.
    + constructor.
    + exact HRest.
  - simpl.
    rewrite HRestTrace.
    rewrite HArgBodyTrace.
    now rewrite app_assoc.
Qed.

Lemma StepsPhi_rgn_app_from_fun_body :
  forall heap env rho er w env_fun rho_fun x eb r
    phi_fun heap_fun phi_body heap_body v_body,
    StepsPhi (initial_state heap env rho er) phi_fun
      (StDone heap_fun (Cls (env_fun, rho_fun, Lambda x eb))) ->
    find_R w rho = Some r ->
    StepsPhi
      (initial_state heap_fun env_fun (update_R (x, r) rho_fun) eb)
      phi_body
      (StDone heap_body v_body) ->
    exists phi_app,
      StepsPhi (initial_state heap env rho (Rgn_App er w)) phi_app
        (StDone heap_body v_body) /\
      phi_as_list phi_app = phi_as_list phi_fun ++ phi_as_list phi_body.
Proof.
  intros heap env rho er w env_fun rho_fun x eb r
    phi_fun heap_fun phi_body heap_body v_body HFun HFind HBody.
  assert
    (HFunContinue :
      StepsPhi
        (StEval heap env rho er (KRgnApp w rho KDone))
        phi_fun
        (initial_state heap_fun env_fun (update_R (x, r) rho_fun) eb)).
  {
    unfold initial_state.
    eapply StepsPhi_initial_terminal_continue; eauto.
    now constructor.
  }
  destruct
    (StepsPhi_trans_exists
      (StEval heap env rho er (KRgnApp w rho KDone))
      phi_fun
      (initial_state heap_fun env_fun (update_R (x, r) rho_fun) eb)
      phi_body
      (StDone heap_body v_body)
      HFunContinue HBody)
    as (phi_rest & HRest & HTrace).
  exists (Phi_Seq (label_phi Silent) phi_rest).
  split.
  - unfold initial_state.
    eapply StepsPhi_Step.
    + constructor.
    + exact HRest.
  - simpl. exact HTrace.
Qed.

Lemma StepsPhi_pair_par_from_components :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap_eff1 (Eff theta1)) ->
    StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap_eff2 (Eff theta2)) ->
    Step
      (StReturn heap_eff2 (Eff theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone))
      Silent
      (StEval heap_eff2 env rho (Mu_App ef1 ea1)
        (KPairParMu1 ef2 ea2 env rho KDone)) ->
    StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    exists phi_pair,
      StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
        phi_pair (StDone heap_mu2 (Pair (v1, v2))) /\
      phi_as_list phi_pair =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2 ++
        phi_as_list phi_mu1 ++ phi_as_list phi_mu2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2 HEff1 HEff2 HCheck HMu1 HMu2.
  assert
    (HEff1Continue :
      StepsPhi
        (StEval heap env rho (Eff_App ef1 ea1)
          (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))
        phi_eff1
        (StEval heap_eff1 env rho (Eff_App ef2 ea2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone))).
  {
    eapply StepsPhi_initial_terminal_continue; eauto.
    constructor.
  }
  assert
    (HEff2Continue :
      StepsPhi
        (StEval heap_eff1 env rho (Eff_App ef2 ea2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone))
        phi_eff2
        (StEval heap_eff2 env rho (Mu_App ef1 ea1)
          (KPairParMu1 ef2 ea2 env rho KDone))).
  {
    eapply StepsPhi_initial_terminal_continue; eauto.
  }
  assert
    (HMu1Continue :
      StepsPhi
        (StEval heap_eff2 env rho (Mu_App ef1 ea1)
          (KPairParMu1 ef2 ea2 env rho KDone))
        phi_mu1
        (StEval heap_mu1 env rho (Mu_App ef2 ea2)
          (KPairParMu2 v1 KDone))).
  {
    eapply StepsPhi_initial_terminal_continue; eauto.
    constructor.
  }
  assert
    (HMu2Continue :
      StepsPhi
        (StEval heap_mu1 env rho (Mu_App ef2 ea2) (KPairParMu2 v1 KDone))
        phi_mu2
        (StReturn heap_mu2 (Pair (v1, v2)) KDone)).
  {
    eapply StepsPhi_initial_terminal_continue; eauto.
    constructor.
  }
  assert
    (HDone :
      StepsPhi
        (StReturn heap_mu2 (Pair (v1, v2)) KDone)
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (StDone heap_mu2 (Pair (v1, v2)))).
  {
    eapply StepsPhi_Step.
    - constructor.
    - constructor.
  }
  destruct
    (StepsPhi_trans_exists
      (StEval heap_mu1 env rho (Mu_App ef2 ea2) (KPairParMu2 v1 KDone))
      phi_mu2
      (StReturn heap_mu2 (Pair (v1, v2)) KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      (StDone heap_mu2 (Pair (v1, v2)))
      HMu2Continue HDone)
    as (phi_mu2_done & HMu2Done & HMu2DoneTrace).
  destruct
    (StepsPhi_trans_exists
      (StEval heap_eff2 env rho (Mu_App ef1 ea1)
        (KPairParMu1 ef2 ea2 env rho KDone))
      phi_mu1
      (StEval heap_mu1 env rho (Mu_App ef2 ea2)
        (KPairParMu2 v1 KDone))
      phi_mu2_done
      (StDone heap_mu2 (Pair (v1, v2)))
      HMu1Continue HMu2Done)
    as (phi_mu1_mu2 & HMu1Mu2 & HMu1Mu2Trace).
  destruct
    (StepsPhi_trans_exists
      (StEval heap_eff1 env rho (Eff_App ef2 ea2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone))
      phi_eff2
      (StEval heap_eff2 env rho (Mu_App ef1 ea1)
        (KPairParMu1 ef2 ea2 env rho KDone))
      phi_mu1_mu2
      (StDone heap_mu2 (Pair (v1, v2)))
      HEff2Continue HMu1Mu2)
    as (phi_eff2_mu & HEff2Mu & HEff2MuTrace).
  destruct
    (StepsPhi_trans_exists
      (StEval heap env rho (Eff_App ef1 ea1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))
      phi_eff1
      (StEval heap_eff1 env rho (Eff_App ef2 ea2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone))
      phi_eff2_mu
      (StDone heap_mu2 (Pair (v1, v2)))
      HEff1Continue HEff2Mu)
    as (phi_rest & HRest & HRestTrace).
  exists (Phi_Seq (label_phi Silent) phi_rest).
  split.
  - unfold initial_state.
    eapply StepsPhi_Step.
    + constructor.
    + exact HRest.
  - simpl.
    rewrite HRestTrace.
    rewrite HEff2MuTrace.
    rewrite HMu1Mu2Trace.
    rewrite HMu2DoneTrace.
    simpl.
    repeat rewrite app_nil_r.
    reflexivity.
Qed.

Lemma StepsPhi_pair_par_pass_from_components :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap_eff1 (Eff theta1)) ->
    StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap_eff2 (Eff theta2)) ->
    Disjointness theta1 theta2 ->
    ~ Conflictness theta1 theta2 ->
    StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    exists phi_pair,
      StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
        phi_pair (StDone heap_mu2 (Pair (v1, v2))) /\
      phi_as_list phi_pair =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2 ++
        phi_as_list phi_mu1 ++ phi_as_list phi_mu2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2 HEff1 HEff2 HDisjoint HNoConflict HMu1 HMu2.
  eapply StepsPhi_pair_par_from_components; eauto.
  now apply Step_PairPar_EvalMu1.
Qed.

Lemma StepsPhi_pair_par_fallback_from_components :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap_eff1 (Eff theta1)) ->
    StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap_eff2 (Eff theta2)) ->
    ~ (Disjointness theta1 theta2 /\ ~ Conflictness theta1 theta2) ->
    StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    exists phi_pair,
      StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
        phi_pair (StDone heap_mu2 (Pair (v1, v2))) /\
      phi_as_list phi_pair =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2 ++
        phi_as_list phi_mu1 ++ phi_as_list phi_mu2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2 HEff1 HEff2 HFail HMu1 HMu2.
  eapply StepsPhi_pair_par_from_components; eauto.
  now apply Step_PairPar_FallbackMu1.
Qed.

Lemma StepsPhi_pair_par_after_check_terminal_decompose :
  forall heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final,
    StepsPhi
      (StEval heap env rho (Mu_App ef1 ea1)
        (KPairParMu1 ef2 ea2 env rho KDone))
      phi
      (StDone heap_final v_final) ->
    exists phi_mu1 heap_mu1 v1 phi_mu2 heap_mu2 v2,
      StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) /\
      StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
        (StDone heap_mu2 v2) /\
      heap_final = heap_mu2 /\
      v_final = Pair (v1, v2) /\
      phi_as_list phi = phi_as_list phi_mu1 ++ phi_as_list phi_mu2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps.
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho (Mu_App ef1 ea1)
      (KPairParMu1 ef2 ea2 env rho KDone)
      phi heap_final v_final HSteps)
    as (heap_mu1 & v1 & phi_mu1 & phi_after_mu2 &
        HMu1 & HAfterMu2 & HTraceMu1).
  inversion HAfterMu2 as
    [| ? ? ? phi_after_mu2_tail ? HStepMu2 HStepsMu2];
    subst; try discriminate.
  inversion HStepMu2; subst.
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap_mu1 env rho (Mu_App ef2 ea2)
      (KPairParMu2 v1 KDone)
      phi_after_mu2_tail heap_final v_final HStepsMu2)
    as (heap_mu2 & v2 & phi_mu2 & phi_after_done &
        HMu2 & HAfterDone & HTraceMu2).
  inversion HAfterDone as
    [| ? ? ? phi_after_done_tail ? HStepDone HStepsDone];
    subst; try discriminate.
  inversion HStepDone; subst.
  assert
    (HDone :
      StepsPhi
        (StReturn heap_mu2 (Pair (v1, v2)) KDone)
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (StDone heap_mu2 (Pair (v1, v2)))).
  {
    eapply StepsPhi_Step.
    - constructor.
    - constructor.
  }
  destruct
    (StepsPhi_terminal_deterministic
      (StReturn heap_mu2 (Pair (v1, v2)) KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      heap_mu2 (Pair (v1, v2))
      phi_after_done_tail heap_final v_final
      HDone HStepsDone)
    as [HTraceDone [HHeapFinal HValueFinal]].
  exists phi_mu1, heap_mu1, v1, phi_mu2, heap_mu2, v2.
  split; [exact HMu1 |].
  split; [exact HMu2 |].
  split; [now symmetry |].
  split; [now symmetry |].
  rewrite HTraceMu1.
  simpl.
  rewrite HTraceMu2.
  simpl.
	  simpl in HTraceDone.
	  rewrite <- HTraceDone.
	  now rewrite app_nil_r.
Qed.

Lemma StepsPhiN_pair_par_after_check_terminal_decompose_counts :
  forall n heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final,
    StepsPhiN n
      (StEval heap env rho (Mu_App ef1 ea1)
        (KPairParMu1 ef2 ea2 env rho KDone))
      phi
      (StDone heap_final v_final) ->
    exists n_mu1 phi_mu1 heap_mu1 v1
      n_mu2 phi_mu2 heap_mu2 v2,
      n_mu1 <= n /\
      n_mu2 <= n /\
      StepsPhiN n_mu1 (initial_state heap env rho (Mu_App ef1 ea1))
        phi_mu1 (StDone heap_mu1 v1) /\
      StepsPhiN n_mu2 (initial_state heap_mu1 env rho (Mu_App ef2 ea2))
        phi_mu2 (StDone heap_mu2 v2) /\
      heap_final = heap_mu2 /\
      v_final = Pair (v1, v2) /\
      phi_as_list phi = phi_as_list phi_mu1 ++ phi_as_list phi_mu2.
Proof.
  intros n heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HSteps.
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n heap env rho (Mu_App ef1 ea1)
      (KPairParMu1 ef2 ea2 env rho KDone)
      phi heap_final v_final HSteps)
    as (n_mu1 & n_after_mu2 & heap_mu1 & v1 &
        phi_mu1 & phi_after_mu2 &
        HLeMu1 & HLeAfterMu2 & HMu1 & HAfterMu2 & HTraceMu1).
  inversion HAfterMu2 as
    [| n_after_mu2_tail state_mu2 label_mu2 state_after_mu2
       phi_after_mu2_tail final_mu2 HStepMu2 HStepsMu2];
    subst; try discriminate.
  inversion HStepMu2; subst.
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_mu2_tail heap_mu1 env rho (Mu_App ef2 ea2)
      (KPairParMu2 v1 KDone)
      phi_after_mu2_tail heap_final v_final HStepsMu2)
    as (n_mu2 & n_after_done & heap_mu2 & v2 &
        phi_mu2 & phi_after_done &
        HLeMu2 & HLeAfterDone & HMu2 & HAfterDone & HTraceMu2).
  inversion HAfterDone as
    [| n_done state_done label_done state_after_done
       phi_after_done_tail final_done HStepDone HStepsDone];
    subst; try discriminate.
  inversion HStepDone; subst.
  assert
    (HDone :
      StepsPhiN 1
        (StReturn heap_mu2 (Pair (v1, v2)) KDone)
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (StDone heap_mu2 (Pair (v1, v2)))).
  {
    eapply StepsPhiN_Step.
    - constructor.
    - constructor.
  }
  destruct
    (StepsPhiN_terminal_deterministic
      1
      (StReturn heap_mu2 (Pair (v1, v2)) KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      heap_mu2 (Pair (v1, v2))
      n_done phi_after_done_tail heap_final v_final
      HDone HStepsDone)
    as [_ [HTraceDone [HHeapFinal HValueFinal]]].
  exists n_mu1, phi_mu1, heap_mu1, v1,
    n_mu2, phi_mu2, heap_mu2, v2.
  repeat split; try lia; try assumption.
  - now symmetry.
  - now symmetry.
  - rewrite HTraceMu1.
    simpl.
    rewrite HTraceMu2.
    simpl.
    simpl in HTraceDone.
    rewrite <- HTraceDone.
    now rewrite app_nil_r.
Qed.

Lemma StepsPhi_pair_par_terminal_decompose :
  forall heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final,
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi (StDone heap_final v_final) ->
    exists phi_eff1 heap_eff1 theta1
      phi_eff2 heap_eff2 theta2
      phi_mu1 heap_mu1 v1
      phi_mu2 heap_mu2 v2,
      StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
        (StDone heap_eff1 (Eff theta1)) /\
      StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
        (StDone heap_eff2 (Eff theta2)) /\
      StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) /\
      StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
        (StDone heap_mu2 v2) /\
      heap_final = heap_mu2 /\
      v_final = Pair (v1, v2) /\
      phi_as_list phi =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2 ++
        phi_as_list phi_mu1 ++ phi_as_list phi_mu2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HPair.
  assert
    (HFirst :
      Step (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2)) Silent
        (StEval heap env rho (Eff_App ef1 ea1)
          (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      Silent
      (StEval heap env rho (Eff_App ef1 ea1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))
      phi heap_final v_final HFirst HPair)
    as (phi_after_eff1 & HAfterEff1 & HTraceStart).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho (Eff_App ef1 ea1)
      (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone)
      phi_after_eff1 heap_final v_final HAfterEff1)
    as (heap_eff1 & v_eff1 & phi_eff1 & phi_after_eff2 &
        HEff1 & HAfterEff2 & HTraceEff1).
  inversion HAfterEff2 as
    [| ? ? ? phi_after_eff2_tail ? HStepEff2 HStepsEff2];
    subst; try discriminate.
  destruct v_eff1 as [w1 l1 | n1 | b1 | cls1 | theta1 | | pair1];
    inversion HStepEff2; subst.
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap_eff1 env rho (Eff_App ef2 ea2)
      (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone)
      phi_after_eff2_tail heap_final v_final HStepsEff2)
    as (heap_eff2 & v_eff2 & phi_eff2 & phi_after_mu1 &
        HEff2 & HAfterMu1 & HTraceEff2).
  inversion HAfterMu1 as
    [| ? ? ? phi_after_mu1_tail ? HStepCheck HStepsCheck];
    subst; try discriminate.
  destruct v_eff2 as [w2 l2 | n2 | b2 | cls2 | theta2 | | pair2];
    inversion HStepCheck; subst;
    destruct
      (StepsPhi_pair_par_after_check_terminal_decompose
        heap_eff2 env rho ef1 ea1 ef2 ea2
        phi_after_mu1_tail heap_final v_final HStepsCheck)
      as (phi_mu1 & heap_mu1 & v1 & phi_mu2 & heap_mu2 & v2 &
          HMu1 & HMu2 & HHeapFinal & HValueFinal & HTraceMu);
    exists phi_eff1, heap_eff1, theta1,
      phi_eff2, heap_eff2, theta2,
      phi_mu1, heap_mu1, v1,
      phi_mu2, heap_mu2, v2;
    repeat split; try assumption;
    rewrite HTraceStart;
    simpl;
    rewrite HTraceEff1;
    simpl;
    rewrite HTraceEff2;
    simpl;
    rewrite HTraceMu;
	    repeat rewrite app_assoc;
	    reflexivity.
Qed.

Lemma StepsPhiN_pair_par_terminal_decompose_counts :
  forall n heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final,
    StepsPhiN n (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi (StDone heap_final v_final) ->
    exists n_eff1 phi_eff1 heap_eff1 theta1
      n_eff2 phi_eff2 heap_eff2 theta2
      n_mu1 phi_mu1 heap_mu1 v1
      n_mu2 phi_mu2 heap_mu2 v2,
      n_eff1 < n /\
      n_eff2 < n /\
      n_mu1 < n /\
      n_mu2 < n /\
      StepsPhiN n_eff1 (initial_state heap env rho (Eff_App ef1 ea1))
        phi_eff1 (StDone heap_eff1 (Eff theta1)) /\
      StepsPhiN n_eff2 (initial_state heap_eff1 env rho (Eff_App ef2 ea2))
        phi_eff2 (StDone heap_eff2 (Eff theta2)) /\
      StepsPhiN n_mu1 (initial_state heap_eff2 env rho (Mu_App ef1 ea1))
        phi_mu1 (StDone heap_mu1 v1) /\
      StepsPhiN n_mu2 (initial_state heap_mu1 env rho (Mu_App ef2 ea2))
        phi_mu2 (StDone heap_mu2 v2) /\
      heap_final = heap_mu2 /\
      v_final = Pair (v1, v2) /\
      phi_as_list phi =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2 ++
        phi_as_list phi_mu1 ++ phi_as_list phi_mu2.
Proof.
  intros n heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HPair.
  assert
    (HFirst :
      Step (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2)) Silent
        (StEval heap env rho (Eff_App ef1 ea1)
          (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhiN_terminal_inv_step
      n
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      Silent
      (StEval heap env rho (Eff_App ef1 ea1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))
      phi heap_final v_final HFirst HPair)
    as (n_after_eff1 & phi_after_eff1 & HNAfterEff1 &
        HAfterEff1 & HTraceStart).
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_eff1 heap env rho (Eff_App ef1 ea1)
      (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone)
      phi_after_eff1 heap_final v_final HAfterEff1)
    as (n_eff1 & n_after_eff2 & heap_eff1 & v_eff1 &
        phi_eff1 & phi_after_eff2 &
        HLeEff1 & HLeAfterEff2 & HEff1 & HAfterEff2 & HTraceEff1).
  inversion HAfterEff2 as
    [| n_after_eff2_tail state_eff2 label_eff2 state_after_eff2
       phi_after_eff2_tail final_eff2 HStepEff2 HStepsEff2];
    subst; try discriminate.
  destruct v_eff1 as [w1 l1 | n1 | b1 | cls1 | theta1 | | pair1];
    inversion HStepEff2; subst.
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_eff2_tail heap_eff1 env rho (Eff_App ef2 ea2)
      (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone)
      phi_after_eff2_tail heap_final v_final HStepsEff2)
    as (n_eff2 & n_after_mu1 & heap_eff2 & v_eff2 &
        phi_eff2 & phi_after_mu1 &
        HLeEff2 & HLeAfterMu1 & HEff2 & HAfterMu1 & HTraceEff2).
  inversion HAfterMu1 as
    [| n_after_mu1_tail state_mu1 label_mu1 state_after_mu1
       phi_after_mu1_tail final_mu1 HStepCheck HStepsCheck];
    subst; try discriminate.
  destruct v_eff2 as [w2 l2 | n2 | b2 | cls2 | theta2 | | pair2];
    inversion HStepCheck; subst;
    destruct
      (StepsPhiN_pair_par_after_check_terminal_decompose_counts
        n_after_mu1_tail heap_eff2 env rho ef1 ea1 ef2 ea2
        phi_after_mu1_tail heap_final v_final HStepsCheck)
      as (n_mu1 & phi_mu1 & heap_mu1 & v1 &
          n_mu2 & phi_mu2 & heap_mu2 & v2 &
          HLeMu1 & HLeMu2 & HMu1 & HMu2 &
          HHeapFinal & HValueFinal & HTraceMu);
    exists n_eff1, phi_eff1, heap_eff1, theta1,
      n_eff2, phi_eff2, heap_eff2, theta2,
      n_mu1, phi_mu1, heap_mu1, v1,
      n_mu2, phi_mu2, heap_mu2, v2;
    repeat split; try lia; try assumption;
    rewrite HTraceStart;
    simpl;
    rewrite HTraceEff1;
    simpl;
    rewrite HTraceEff2;
    simpl;
    rewrite HTraceMu;
    repeat rewrite app_assoc;
    reflexivity.
Qed.

Lemma StepsPhi_pair_par_terminal_decompose_checked :
  forall heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final,
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi (StDone heap_final v_final) ->
    exists phi_eff1 heap_eff1 theta1
      phi_eff2 heap_eff2 theta2
      phi_mu1 heap_mu1 v1
      phi_mu2 heap_mu2 v2,
      StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
        (StDone heap_eff1 (Eff theta1)) /\
      StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
        (StDone heap_eff2 (Eff theta2)) /\
      StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) /\
      StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
        (StDone heap_mu2 v2) /\
      (PairParCheckPass theta1 theta2 \/ PairParCheckFail theta1 theta2) /\
      heap_final = heap_mu2 /\
      v_final = Pair (v1, v2) /\
      phi_as_list phi =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2 ++
        phi_as_list phi_mu1 ++ phi_as_list phi_mu2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HPair.
  assert
    (HFirst :
      Step (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2)) Silent
        (StEval heap env rho (Eff_App ef1 ea1)
          (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      Silent
      (StEval heap env rho (Eff_App ef1 ea1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))
      phi heap_final v_final HFirst HPair)
    as (phi_after_eff1 & HAfterEff1 & HTraceStart).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho (Eff_App ef1 ea1)
      (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone)
      phi_after_eff1 heap_final v_final HAfterEff1)
    as (heap_eff1 & v_eff1 & phi_eff1 & phi_after_eff2 &
        HEff1 & HAfterEff2 & HTraceEff1).
  inversion HAfterEff2 as
    [| ? ? ? phi_after_eff2_tail ? HStepEff2 HStepsEff2];
    subst; try discriminate.
  destruct v_eff1 as [w1 l1 | n1 | b1 | cls1 | theta1 | | pair1];
    inversion HStepEff2; subst.
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap_eff1 env rho (Eff_App ef2 ea2)
      (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone)
      phi_after_eff2_tail heap_final v_final HStepsEff2)
    as (heap_eff2 & v_eff2 & phi_eff2 & phi_after_mu1 &
        HEff2 & HAfterMu1 & HTraceEff2).
  inversion HAfterMu1 as
    [| ? ? ? phi_after_mu1_tail ? HStepCheck HStepsCheck];
    subst; try discriminate.
  destruct v_eff2 as [w2 l2 | n2 | b2 | cls2 | theta2 | | pair2];
    inversion HStepCheck; subst;
    destruct
      (StepsPhi_pair_par_after_check_terminal_decompose
        heap_eff2 env rho ef1 ea1 ef2 ea2
        phi_after_mu1_tail heap_final v_final HStepsCheck)
      as (phi_mu1 & heap_mu1 & v1 & phi_mu2 & heap_mu2 & v2 &
          HMu1 & HMu2 & HHeapFinal & HValueFinal & HTraceMu);
    exists phi_eff1, heap_eff1, theta1,
      phi_eff2, heap_eff2, theta2,
      phi_mu1, heap_mu1, v1,
      phi_mu2, heap_mu2, v2;
    repeat split; try assumption;
    try (left; split; assumption);
    try (right; assumption);
    rewrite HTraceStart;
    simpl;
    rewrite HTraceEff1;
    simpl;
    rewrite HTraceEff2;
    simpl;
    rewrite HTraceMu;
	    repeat rewrite app_assoc;
	    reflexivity.
Qed.

Lemma StepsPhiN_pair_par_terminal_decompose_checked_counts :
  forall n heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final,
    StepsPhiN n (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi (StDone heap_final v_final) ->
    exists n_eff1 phi_eff1 heap_eff1 theta1
      n_eff2 phi_eff2 heap_eff2 theta2
      n_mu1 phi_mu1 heap_mu1 v1
      n_mu2 phi_mu2 heap_mu2 v2,
      n_eff1 < n /\
      n_eff2 < n /\
      n_mu1 < n /\
      n_mu2 < n /\
      StepsPhiN n_eff1 (initial_state heap env rho (Eff_App ef1 ea1))
        phi_eff1 (StDone heap_eff1 (Eff theta1)) /\
      StepsPhiN n_eff2 (initial_state heap_eff1 env rho (Eff_App ef2 ea2))
        phi_eff2 (StDone heap_eff2 (Eff theta2)) /\
      StepsPhiN n_mu1 (initial_state heap_eff2 env rho (Mu_App ef1 ea1))
        phi_mu1 (StDone heap_mu1 v1) /\
      StepsPhiN n_mu2 (initial_state heap_mu1 env rho (Mu_App ef2 ea2))
        phi_mu2 (StDone heap_mu2 v2) /\
      (PairParCheckPass theta1 theta2 \/ PairParCheckFail theta1 theta2) /\
      heap_final = heap_mu2 /\
      v_final = Pair (v1, v2) /\
      phi_as_list phi =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2 ++
        phi_as_list phi_mu1 ++ phi_as_list phi_mu2.
Proof.
  intros n heap env rho ef1 ea1 ef2 ea2 phi heap_final v_final HPair.
  assert
    (HFirst :
      Step (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2)) Silent
        (StEval heap env rho (Eff_App ef1 ea1)
          (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhiN_terminal_inv_step
      n
      (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      Silent
      (StEval heap env rho (Eff_App ef1 ea1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone))
      phi heap_final v_final HFirst HPair)
    as (n_after_eff1 & phi_after_eff1 & HNAfterEff1 &
        HAfterEff1 & HTraceStart).
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_eff1 heap env rho (Eff_App ef1 ea1)
      (KPairParEff1 ef1 ea1 ef2 ea2 env rho KDone)
      phi_after_eff1 heap_final v_final HAfterEff1)
    as (n_eff1 & n_after_eff2 & heap_eff1 & v_eff1 &
        phi_eff1 & phi_after_eff2 &
        HLeEff1 & HLeAfterEff2 & HEff1 & HAfterEff2 & HTraceEff1).
  inversion HAfterEff2 as
    [| n_after_eff2_tail state_eff2 label_eff2 state_after_eff2
       phi_after_eff2_tail final_eff2 HStepEff2 HStepsEff2];
    subst; try discriminate.
  destruct v_eff1 as [w1 l1 | n1 | b1 | cls1 | theta1 | | pair1];
    inversion HStepEff2; subst.
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_eff2_tail heap_eff1 env rho (Eff_App ef2 ea2)
      (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone)
      phi_after_eff2_tail heap_final v_final HStepsEff2)
    as (n_eff2 & n_after_mu1 & heap_eff2 & v_eff2 &
        phi_eff2 & phi_after_mu1 &
        HLeEff2 & HLeAfterMu1 & HEff2 & HAfterMu1 & HTraceEff2).
  inversion HAfterMu1 as
    [| n_after_mu1_tail state_mu1 label_mu1 state_after_mu1
       phi_after_mu1_tail final_mu1 HStepCheck HStepsCheck];
    subst; try discriminate.
  destruct v_eff2 as [w2 l2 | n2 | b2 | cls2 | theta2 | | pair2];
    inversion HStepCheck; subst;
    destruct
      (StepsPhiN_pair_par_after_check_terminal_decompose_counts
        n_after_mu1_tail heap_eff2 env rho ef1 ea1 ef2 ea2
        phi_after_mu1_tail heap_final v_final HStepsCheck)
      as (n_mu1 & phi_mu1 & heap_mu1 & v1 &
          n_mu2 & phi_mu2 & heap_mu2 & v2 &
          HLeMu1 & HLeMu2 & HMu1 & HMu2 &
          HHeapFinal & HValueFinal & HTraceMu);
    exists n_eff1, phi_eff1, heap_eff1, theta1,
      n_eff2, phi_eff2, heap_eff2, theta2,
      n_mu1, phi_mu1, heap_mu1, v1,
      n_mu2, phi_mu2, heap_mu2, v2;
    repeat split; try lia; try assumption;
    try (left; split; assumption);
    try (right; assumption);
    rewrite HTraceStart;
    simpl;
    rewrite HTraceEff1;
    simpl;
    rewrite HTraceEff2;
    simpl;
    rewrite HTraceMu;
    repeat rewrite app_assoc;
    reflexivity.
Qed.

Lemma StepsPhi_readconc_from_arg :
  forall heap env rho e phi_arg heap_arg r l,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg (Loc (Rgn_Const true false r) l)) ->
    exists phi_read,
      StepsPhi (initial_state heap env rho (ReadConc e)) phi_read
        (StDone heap_arg (Eff (Some (singleton_set (CA_ReadConc r l))))) /\
      phi_as_list phi_read = phi_as_list phi_arg.
Proof.
  intros heap env rho e phi_arg heap_arg r l HArg.
  assert
    (HArgContinue :
      StepsPhi
        (StEval heap env rho e (KReadConc KDone))
        phi_arg
        (StReturn heap_arg
          (Eff (Some (singleton_set (CA_ReadConc r l)))) KDone)).
  {
    eapply StepsPhi_initial_terminal_continue; eauto.
    constructor.
  }
  assert
    (HDone :
      StepsPhi
        (StReturn heap_arg
          (Eff (Some (singleton_set (CA_ReadConc r l)))) KDone)
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (StDone heap_arg (Eff (Some (singleton_set (CA_ReadConc r l)))))).
  {
    eapply StepsPhi_Step.
    - constructor.
    - constructor.
  }
  destruct
    (StepsPhi_trans_exists
      (StEval heap env rho e (KReadConc KDone))
      phi_arg
      (StReturn heap_arg
        (Eff (Some (singleton_set (CA_ReadConc r l)))) KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      (StDone heap_arg (Eff (Some (singleton_set (CA_ReadConc r l)))))
      HArgContinue HDone)
    as (phi_rest & HRest & HTrace).
  exists (Phi_Seq (label_phi Silent) phi_rest).
  split.
  - unfold initial_state.
    eapply StepsPhi_Step.
    + constructor.
    + exact HRest.
  - simpl.
    rewrite HTrace.
    simpl.
    now rewrite app_nil_r.
Qed.

Lemma StepsPhi_readconc_terminal_from_arg :
  forall heap env rho e phi_arg heap_arg r l
    phi_read heap_read theta,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg (Loc (Rgn_Const true false r) l)) ->
    StepsPhi (initial_state heap env rho (ReadConc e)) phi_read
      (StDone heap_read (Eff theta)) ->
    phi_as_list phi_read = phi_as_list phi_arg /\
    heap_read = heap_arg /\
    theta = Some (singleton_set (CA_ReadConc r l)).
Proof.
  intros heap env rho e phi_arg heap_arg r l
    phi_read heap_read theta HArg HRead.
  destruct
    (StepsPhi_readconc_from_arg
      heap env rho e phi_arg heap_arg r l HArg)
    as (phi_read_sound & HReadSound & HList).
  destruct
    (StepsPhi_effect_terminal_deterministic
      (initial_state heap env rho (ReadConc e))
      phi_read_sound heap_arg (Some (singleton_set (CA_ReadConc r l)))
      phi_read heap_read theta HReadSound HRead)
    as [HTrace [HHeap HTheta]].
  split.
  - rewrite <- HTrace. exact HList.
  - split.
    + now symmetry.
    + now symmetry.
Qed.

Lemma StepsPhi_writeconc_from_arg :
  forall heap env rho e phi_arg heap_arg r l,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg (Loc (Rgn_Const true false r) l)) ->
    exists phi_write,
      StepsPhi (initial_state heap env rho (WriteConc e)) phi_write
        (StDone heap_arg (Eff (Some (singleton_set (CA_WriteConc r l))))) /\
      phi_as_list phi_write = phi_as_list phi_arg.
Proof.
  intros heap env rho e phi_arg heap_arg r l HArg.
  assert
    (HArgContinue :
      StepsPhi
        (StEval heap env rho e (KWriteConc KDone))
        phi_arg
        (StReturn heap_arg
          (Eff (Some (singleton_set (CA_WriteConc r l)))) KDone)).
  {
    eapply StepsPhi_initial_terminal_continue; eauto.
    constructor.
  }
  assert
    (HDone :
      StepsPhi
        (StReturn heap_arg
          (Eff (Some (singleton_set (CA_WriteConc r l)))) KDone)
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (StDone heap_arg (Eff (Some (singleton_set (CA_WriteConc r l)))))).
  {
    eapply StepsPhi_Step.
    - constructor.
    - constructor.
  }
  destruct
    (StepsPhi_trans_exists
      (StEval heap env rho e (KWriteConc KDone))
      phi_arg
      (StReturn heap_arg
        (Eff (Some (singleton_set (CA_WriteConc r l)))) KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      (StDone heap_arg (Eff (Some (singleton_set (CA_WriteConc r l)))))
      HArgContinue HDone)
    as (phi_rest & HRest & HTrace).
  exists (Phi_Seq (label_phi Silent) phi_rest).
  split.
  - unfold initial_state.
    eapply StepsPhi_Step.
    + constructor.
    + exact HRest.
  - simpl.
    rewrite HTrace.
    simpl.
    now rewrite app_nil_r.
Qed.

Lemma StepsPhi_writeconc_terminal_from_arg :
  forall heap env rho e phi_arg heap_arg r l
    phi_write heap_write theta,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg (Loc (Rgn_Const true false r) l)) ->
    StepsPhi (initial_state heap env rho (WriteConc e)) phi_write
      (StDone heap_write (Eff theta)) ->
    phi_as_list phi_write = phi_as_list phi_arg /\
    heap_write = heap_arg /\
    theta = Some (singleton_set (CA_WriteConc r l)).
Proof.
  intros heap env rho e phi_arg heap_arg r l
    phi_write heap_write theta HArg HWrite.
  destruct
    (StepsPhi_writeconc_from_arg
      heap env rho e phi_arg heap_arg r l HArg)
    as (phi_write_sound & HWriteSound & HList).
  destruct
    (StepsPhi_effect_terminal_deterministic
      (initial_state heap env rho (WriteConc e))
      phi_write_sound heap_arg (Some (singleton_set (CA_WriteConc r l)))
      phi_write heap_write theta HWriteSound HWrite)
    as [HTrace [HHeap HTheta]].
  split.
  - rewrite <- HTrace. exact HList.
  - split.
    + now symmetry.
    + now symmetry.
Qed.

Lemma StepsPhi_concat_from_left_right :
  forall heap env rho e1 e2
    phi_left heap_left theta1 phi_right heap_right theta2,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Eff theta1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Eff theta2)) ->
    exists phi_concat,
      StepsPhi (initial_state heap env rho (Concat e1 e2)) phi_concat
        (StDone heap_right (Eff (Union_Theta theta1 theta2))) /\
      phi_as_list phi_concat =
        phi_as_list phi_left ++ phi_as_list phi_right.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left theta1 phi_right heap_right theta2 HLeft HRight.
  eapply StepsPhi_binary_from_left_right; eauto; constructor.
Qed.

Lemma StepsPhi_concat_terminal_decompose :
  forall heap env rho e1 e2 phi heap_final v_final,
    StepsPhi (initial_state heap env rho (Concat e1 e2)) phi
      (StDone heap_final v_final) ->
    exists phi_left heap_left theta1 phi_right heap_right theta2,
      StepsPhi (initial_state heap env rho e1) phi_left
        (StDone heap_left (Eff theta1)) /\
      StepsPhi (initial_state heap_left env rho e2) phi_right
        (StDone heap_right (Eff theta2)) /\
      heap_final = heap_right /\
      v_final = Eff (Union_Theta theta1 theta2) /\
      phi_as_list phi =
        phi_as_list phi_left ++ phi_as_list phi_right.
Proof.
  intros heap env rho e1 e2 phi heap_final v_final HConcat.
  assert
    (HFirst :
      Step (initial_state heap env rho (Concat e1 e2)) Silent
        (StEval heap env rho e1 (KConcatL e2 env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Concat e1 e2))
      Silent
      (StEval heap env rho e1 (KConcatL e2 env rho KDone))
      phi heap_final v_final HFirst HConcat)
    as (phi_after_left & HAfterLeft & HTraceStart).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho e1 (KConcatL e2 env rho KDone)
      phi_after_left heap_final v_final HAfterLeft)
    as (heap_left & v_left & phi_left & phi_after_right &
        HLeft & HAfterRight & HTraceLeft).
  inversion HAfterRight as
    [| ? ? ? phi_after_right_tail ? HStepRight HStepsRight];
    subst; try discriminate.
  inversion HStepRight; subst.
    destruct
      (StepsPhi_initial_with_kont_terminal_decompose
        heap_left env rho e2 (KConcatR theta KDone)
        phi_after_right_tail heap_final v_final HStepsRight)
      as (heap_right & v_right & phi_right & phi_after_done &
          HRight & HAfterDone & HTraceRight).
    inversion HAfterDone as
      [| ? ? ? phi_after_done_tail ? HStepDone HStepsDone];
      subst; try discriminate.
    destruct v_right as [w l | n | b | cls | theta_right | | pair];
      inversion HStepDone; subst.
      assert
        (HDone :
          StepsPhi
            (StReturn heap_right (Eff (Union_Theta theta theta_right)) KDone)
            (Phi_Seq (label_phi Silent) Phi_Nil)
            (StDone heap_right (Eff (Union_Theta theta theta_right)))).
      {
        eapply StepsPhi_Step.
        - constructor.
        - constructor.
      }
      destruct
        (StepsPhi_terminal_deterministic
          (StReturn heap_right (Eff (Union_Theta theta theta_right)) KDone)
          (Phi_Seq (label_phi Silent) Phi_Nil)
          heap_right (Eff (Union_Theta theta theta_right))
          phi_after_done_tail heap_final v_final
          HDone HStepsDone)
        as [HTraceDone [HHeap HVal]].
      exists phi_left, heap_left, theta, phi_right, heap_right, theta_right.
      repeat split; try assumption.
      - symmetry. assumption.
      - symmetry. assumption.
      - rewrite HTraceStart.
        simpl.
        rewrite HTraceLeft.
        simpl.
        rewrite HTraceRight.
        simpl.
        rewrite <- HTraceDone.
        now rewrite app_nil_r.
Qed.

Lemma StepsPhi_concat_effect_terminal_decompose :
  forall heap env rho e1 e2 phi heap_final theta_summary,
    StepsPhi (initial_state heap env rho (Concat e1 e2)) phi
      (StDone heap_final (Eff theta_summary)) ->
    exists phi_left heap_left theta1 phi_right heap_right theta2,
      StepsPhi (initial_state heap env rho e1) phi_left
        (StDone heap_left (Eff theta1)) /\
      StepsPhi (initial_state heap_left env rho e2) phi_right
        (StDone heap_right (Eff theta2)) /\
      heap_final = heap_right /\
      theta_summary = Union_Theta theta1 theta2 /\
      phi_as_list phi =
        phi_as_list phi_left ++ phi_as_list phi_right.
Proof.
  intros heap env rho e1 e2 phi heap_final theta_summary HConcat.
  destruct
    (StepsPhi_concat_terminal_decompose
      heap env rho e1 e2 phi heap_final (Eff theta_summary) HConcat)
    as (phi_left & heap_left & theta1 & phi_right & heap_right & theta2 &
        HLeft & HRight & HHeap & HValue & HTrace).
  inversion HValue; subst.
  exists phi_left, heap_left, theta1, phi_right, heap_right, theta2.
  repeat split; assumption.
Qed.

Lemma StepsPhi_ref_terminal_decompose :
  forall heap env rho w e phi heap_final v_final,
    StepsPhi (initial_state heap env rho (Ref w e)) phi
      (StDone heap_final v_final) ->
    exists phi_arg heap_arg v_arg r l,
      StepsPhi (initial_state heap env rho e) phi_arg
        (StDone heap_arg v_arg) /\
      find_R w rho = Some r /\
      allocate_H heap_arg r = l /\
      heap_final = update_H ((r, l), v_arg) heap_arg /\
      v_final = Loc (Rgn_Const true false r) l /\
      phi_as_list phi =
        phi_as_list phi_arg ++ DA_Alloc r l v_arg :: nil.
Proof.
  intros heap env rho w e phi heap_final v_final HRef.
  assert
    (HFirst :
      Step (initial_state heap env rho (Ref w e)) Silent
        (StEval heap env rho e (KRef w rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Ref w e))
      Silent
      (StEval heap env rho e (KRef w rho KDone))
      phi heap_final v_final HFirst HRef)
    as (phi_after_arg & HAfterArg & HTraceStart).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho e (KRef w rho KDone)
      phi_after_arg heap_final v_final HAfterArg)
    as (heap_arg & v_arg & phi_arg & phi_after_action &
        HArg & HAfterAction & HTraceArg).
  inversion HAfterAction as
    [| ? ? ? phi_after_done ? HStepAction HStepsDone];
    subst; try discriminate.
  inversion HStepAction; subst.
  match type of HStepsDone with
  | StepsPhi
      (StReturn (update_H ((?r_alloc, ?l_alloc), v_arg) heap_arg)
        (Loc (Rgn_Const true false ?r_alloc) ?l_alloc) KDone)
      phi_after_done (StDone heap_final v_final) =>
      assert
        (HDone :
          StepsPhi
            (StReturn (update_H ((r_alloc, l_alloc), v_arg) heap_arg)
              (Loc (Rgn_Const true false r_alloc) l_alloc) KDone)
            (Phi_Seq (label_phi Silent) Phi_Nil)
            (StDone (update_H ((r_alloc, l_alloc), v_arg) heap_arg)
              (Loc (Rgn_Const true false r_alloc) l_alloc)))
      by
        (eapply (StepsPhi_Step _ Silent _ Phi_Nil _);
         [apply Step_Done | apply StepsPhi_Refl]);
      destruct
        (StepsPhi_terminal_deterministic
          (StReturn (update_H ((r_alloc, l_alloc), v_arg) heap_arg)
            (Loc (Rgn_Const true false r_alloc) l_alloc) KDone)
          (Phi_Seq (label_phi Silent) Phi_Nil)
          (update_H ((r_alloc, l_alloc), v_arg) heap_arg)
          (Loc (Rgn_Const true false r_alloc) l_alloc)
          phi_after_done heap_final v_final
          HDone HStepsDone)
        as [HTraceDone [HHeap HVal]];
      exists phi_arg, heap_arg, v_arg, r_alloc, l_alloc;
      split; [exact HArg |];
      split; [eassumption |];
      split; [reflexivity |];
      split; [symmetry; exact HHeap |];
      split; [symmetry; exact HVal |];
      rewrite HTraceStart;
      simpl;
      rewrite HTraceArg;
      simpl;
      rewrite <- HTraceDone;
      reflexivity
	  end.
Qed.

Lemma StepsPhiN_ref_terminal_decompose_counts :
  forall n heap env rho w e phi heap_final v_final,
    StepsPhiN n (initial_state heap env rho (Ref w e)) phi
      (StDone heap_final v_final) ->
    exists n_arg phi_arg heap_arg v_arg r l,
      n_arg < n /\
      StepsPhiN n_arg (initial_state heap env rho e) phi_arg
        (StDone heap_arg v_arg) /\
      find_R w rho = Some r /\
      allocate_H heap_arg r = l /\
      heap_final = update_H ((r, l), v_arg) heap_arg /\
      v_final = Loc (Rgn_Const true false r) l /\
      phi_as_list phi =
        phi_as_list phi_arg ++ DA_Alloc r l v_arg :: nil.
Proof.
  intros n heap env rho w e phi heap_final v_final HRef.
  assert
    (HFirst :
      Step (initial_state heap env rho (Ref w e)) Silent
        (StEval heap env rho e (KRef w rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhiN_terminal_inv_step
      n
      (initial_state heap env rho (Ref w e))
      Silent
      (StEval heap env rho e (KRef w rho KDone))
      phi heap_final v_final HFirst HRef)
    as (n_after_arg & phi_after_arg & HNAfterArg &
        HAfterArg & HTraceStart).
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_arg heap env rho e (KRef w rho KDone)
      phi_after_arg heap_final v_final HAfterArg)
    as (n_arg & n_after_action & heap_arg & v_arg &
        phi_arg & phi_after_action &
        HLeArg & HLeAfterAction & HArg & HAfterAction & HTraceArg).
  inversion HAfterAction as
    [| n_after_done state_action label_action state_after_action
       phi_after_done final_action HStepAction HStepsDone];
    subst; try discriminate.
  inversion HStepAction; subst.
  match type of HStepsDone with
  | StepsPhiN ?n_done
      (StReturn (update_H ((?r_alloc, ?l_alloc), v_arg) heap_arg)
        (Loc (Rgn_Const true false ?r_alloc) ?l_alloc) KDone)
      ?phi_done (StDone heap_final v_final) =>
      assert
        (HDone :
          StepsPhiN 1
            (StReturn (update_H ((r_alloc, l_alloc), v_arg) heap_arg)
              (Loc (Rgn_Const true false r_alloc) l_alloc) KDone)
            (Phi_Seq (label_phi Silent) Phi_Nil)
            (StDone (update_H ((r_alloc, l_alloc), v_arg) heap_arg)
              (Loc (Rgn_Const true false r_alloc) l_alloc)))
      by
        (eapply StepsPhiN_Step;
         [apply Step_Done | apply StepsPhiN_Refl]);
      destruct
        (StepsPhiN_terminal_deterministic
          1
          (StReturn (update_H ((r_alloc, l_alloc), v_arg) heap_arg)
            (Loc (Rgn_Const true false r_alloc) l_alloc) KDone)
          (Phi_Seq (label_phi Silent) Phi_Nil)
          (update_H ((r_alloc, l_alloc), v_arg) heap_arg)
          (Loc (Rgn_Const true false r_alloc) l_alloc)
          n_done phi_done heap_final v_final
          HDone HStepsDone)
        as [_ [HTraceDone [HHeap HVal]]];
      exists n_arg, phi_arg, heap_arg, v_arg, r_alloc, l_alloc;
      split; [lia |];
      split; [exact HArg |];
      split; [eassumption |];
      split; [reflexivity |];
      split; [symmetry; exact HHeap |];
      split; [symmetry; exact HVal |];
      rewrite HTraceStart;
      simpl;
      rewrite HTraceArg;
      simpl;
      rewrite <- HTraceDone;
      reflexivity
  end.
Qed.

Lemma StepsPhi_ref_from_arg :
  forall heap env rho w e phi_arg heap_arg v r l,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg v) ->
    find_R w rho = Some r ->
    allocate_H heap_arg r = l ->
    exists phi_ref,
      StepsPhi (initial_state heap env rho (Ref w e)) phi_ref
        (StDone (update_H ((r, l), v) heap_arg)
          (Loc (Rgn_Const true false r) l)) /\
      phi_as_list phi_ref =
        phi_as_list phi_arg ++ DA_Alloc r l v :: nil.
Proof.
  intros heap env rho w e phi_arg heap_arg v r l HArg HFind HAlloc.
  destruct
    (StepsPhi_initial_terminal_continue_label
      heap env rho e phi_arg heap_arg v
      (KRef w rho KDone)
      (Act (DA_Alloc r l v))
      (StReturn (update_H ((r, l), v) heap_arg)
        (Loc (Rgn_Const true false r) l) KDone)
      HArg)
    as (phi_action & HAction & HActionTrace).
  {
    econstructor; eauto.
  }
  assert
    (HDone :
      StepsPhi
        (StReturn (update_H ((r, l), v) heap_arg)
          (Loc (Rgn_Const true false r) l) KDone)
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (StDone (update_H ((r, l), v) heap_arg)
          (Loc (Rgn_Const true false r) l))).
  {
    eapply StepsPhi_Step.
    - constructor.
    - constructor.
  }
  destruct
    (StepsPhi_trans_exists
      (StEval heap env rho e (KRef w rho KDone))
      phi_action
      (StReturn (update_H ((r, l), v) heap_arg)
        (Loc (Rgn_Const true false r) l) KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      (StDone (update_H ((r, l), v) heap_arg)
        (Loc (Rgn_Const true false r) l))
      HAction HDone)
    as (phi_rest & HRest & HRestTrace).
  exists (Phi_Seq (label_phi Silent) phi_rest).
  split.
  - unfold initial_state.
    eapply StepsPhi_Step.
    + constructor.
    + exact HRest.
  - simpl.
    rewrite HRestTrace.
    rewrite HActionTrace.
    simpl.
    now rewrite app_nil_r.
Qed.

Lemma StepsPhi_deref_terminal_decompose :
  forall heap env rho w e phi heap_final v_final,
    StepsPhi (initial_state heap env rho (DeRef w e)) phi
      (StDone heap_final v_final) ->
    exists phi_arg heap_arg r l v,
      StepsPhi (initial_state heap env rho e) phi_arg
        (StDone heap_arg (Loc w l)) /\
      find_R w rho = Some r /\
      find_H (r, l) heap_arg = Some v /\
      heap_final = heap_arg /\
      v_final = v /\
      phi_as_list phi =
        phi_as_list phi_arg ++ DA_Read r l v :: nil.
Proof.
  intros heap env rho w e phi heap_final v_final HDeref.
  assert
    (HFirst :
      Step (initial_state heap env rho (DeRef w e)) Silent
        (StEval heap env rho e (KDeRef w rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (DeRef w e))
      Silent
      (StEval heap env rho e (KDeRef w rho KDone))
      phi heap_final v_final HFirst HDeref)
    as (phi_after_arg & HAfterArg & HTraceStart).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho e (KDeRef w rho KDone)
      phi_after_arg heap_final v_final HAfterArg)
    as (heap_arg & v_arg & phi_arg & phi_after_action &
        HArg & HAfterAction & HTraceArg).
  inversion HAfterAction as
    [| ? ? ? phi_after_done ? HStepAction HStepsDone];
    subst; try discriminate.
  inversion HStepAction; subst.
  match type of HAfterAction with
  | StepsPhi
      (StReturn heap_arg (Loc w ?l_read) (KDeRef w rho KDone))
      (Phi_Seq (label_phi (Act (DA_Read ?r_read ?l_read ?v_read)))
        phi_after_done)
      (StDone heap_final v_final) =>
      assert
        (HDone :
          StepsPhi
            (StReturn heap_arg v_read KDone)
            (Phi_Seq (label_phi Silent) Phi_Nil)
            (StDone heap_arg v_read))
      by
        (eapply (StepsPhi_Step _ Silent _ Phi_Nil _);
         [apply Step_Done | apply StepsPhi_Refl]);
      destruct
        (StepsPhi_terminal_deterministic
          (StReturn heap_arg v_read KDone)
          (Phi_Seq (label_phi Silent) Phi_Nil)
          heap_arg v_read
          phi_after_done heap_final v_final
          HDone HStepsDone)
        as [HTraceDone [HHeap HVal]];
      exists phi_arg, heap_arg, r_read, l_read, v_read;
      split; [exact HArg |];
      split; [eassumption |];
      split; [eassumption |];
      split; [symmetry; exact HHeap |];
      split; [symmetry; exact HVal |];
      rewrite HTraceStart;
      simpl;
      rewrite HTraceArg;
      simpl;
      rewrite <- HTraceDone;
      reflexivity
	  end.
Qed.

Lemma StepsPhiN_deref_terminal_decompose_counts :
  forall n heap env rho w e phi heap_final v_final,
    StepsPhiN n (initial_state heap env rho (DeRef w e)) phi
      (StDone heap_final v_final) ->
    exists n_arg phi_arg heap_arg r l v,
      n_arg < n /\
      StepsPhiN n_arg (initial_state heap env rho e) phi_arg
        (StDone heap_arg (Loc w l)) /\
      find_R w rho = Some r /\
      find_H (r, l) heap_arg = Some v /\
      heap_final = heap_arg /\
      v_final = v /\
      phi_as_list phi =
        phi_as_list phi_arg ++ DA_Read r l v :: nil.
Proof.
  intros n heap env rho w e phi heap_final v_final HDeref.
  assert
    (HFirst :
      Step (initial_state heap env rho (DeRef w e)) Silent
        (StEval heap env rho e (KDeRef w rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhiN_terminal_inv_step
      n
      (initial_state heap env rho (DeRef w e))
      Silent
      (StEval heap env rho e (KDeRef w rho KDone))
      phi heap_final v_final HFirst HDeref)
    as (n_after_arg & phi_after_arg & HNAfterArg &
        HAfterArg & HTraceStart).
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_arg heap env rho e (KDeRef w rho KDone)
      phi_after_arg heap_final v_final HAfterArg)
    as (n_arg & n_after_action & heap_arg & v_arg &
        phi_arg & phi_after_action &
        HLeArg & HLeAfterAction & HArg & HAfterAction & HTraceArg).
  inversion HAfterAction as
    [| n_after_done state_action label_action state_after_action
       phi_after_done final_action HStepAction HStepsDone];
    subst; try discriminate.
  inversion HStepAction; subst.
  match type of HAfterAction with
  | StepsPhiN _
      (StReturn heap_arg (Loc w ?l_read) (KDeRef w rho KDone))
      (Phi_Seq (label_phi (Act (DA_Read ?r_read ?l_read ?v_read)))
        phi_after_done)
      (StDone heap_final v_final) =>
      assert
        (HDone :
          StepsPhiN 1
            (StReturn heap_arg v_read KDone)
            (Phi_Seq (label_phi Silent) Phi_Nil)
            (StDone heap_arg v_read))
      by
        (eapply StepsPhiN_Step;
         [apply Step_Done | apply StepsPhiN_Refl]);
      destruct
        (StepsPhiN_terminal_deterministic
          1
          (StReturn heap_arg v_read KDone)
          (Phi_Seq (label_phi Silent) Phi_Nil)
          heap_arg v_read
          n_after_done phi_after_done heap_final v_final
          HDone HStepsDone)
        as [_ [HTraceDone [HHeap HVal]]];
      exists n_arg, phi_arg, heap_arg, r_read, l_read, v_read;
      split; [lia |];
      split; [exact HArg |];
      split; [eassumption |];
      split; [eassumption |];
      split; [symmetry; exact HHeap |];
      split; [symmetry; exact HVal |];
      rewrite HTraceStart;
      simpl;
      rewrite HTraceArg;
      simpl;
      rewrite <- HTraceDone;
      reflexivity
  end.
Qed.

Lemma StepsPhi_deref_from_arg :
  forall heap env rho w e phi_arg heap_arg r l v,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg (Loc w l)) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_arg = Some v ->
    exists phi_deref,
      StepsPhi (initial_state heap env rho (DeRef w e)) phi_deref
        (StDone heap_arg v) /\
      phi_as_list phi_deref =
      phi_as_list phi_arg ++ DA_Read r l v :: nil.
Proof.
  intros heap env rho w e phi_arg heap_arg r l v HArg HFindR HFindH.
  destruct
    (StepsPhi_initial_terminal_continue_label
      heap env rho e phi_arg heap_arg (Loc w l)
      (KDeRef w rho KDone)
      (Act (DA_Read r l v))
      (StReturn heap_arg v KDone)
      HArg)
    as (phi_action & HAction & HActionTrace).
  {
    econstructor; eauto.
  }
  assert
    (HDone :
      StepsPhi
        (StReturn heap_arg v KDone)
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (StDone heap_arg v)).
  {
    eapply StepsPhi_Step.
    - constructor.
    - constructor.
  }
  destruct
    (StepsPhi_trans_exists
      (StEval heap env rho e (KDeRef w rho KDone))
      phi_action
      (StReturn heap_arg v KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      (StDone heap_arg v)
      HAction HDone)
    as (phi_rest & HRest & HRestTrace).
  exists (Phi_Seq (label_phi Silent) phi_rest).
  split.
  - unfold initial_state.
    eapply StepsPhi_Step.
    + constructor.
    + exact HRest.
  - simpl.
    rewrite HRestTrace.
    rewrite HActionTrace.
    simpl.
    now rewrite app_nil_r.
Qed.

Lemma StepsPhi_assign_terminal_decompose :
  forall heap env rho w ea ev phi heap_final v_final,
    StepsPhi (initial_state heap env rho (Assign w ea ev)) phi
      (StDone heap_final v_final) ->
    exists phi_loc heap_loc l phi_val heap_val v r,
      StepsPhi (initial_state heap env rho ea) phi_loc
        (StDone heap_loc (Loc w l)) /\
      StepsPhi (initial_state heap_loc env rho ev) phi_val
        (StDone heap_val v) /\
      find_R w rho = Some r /\
      find_H (r, l) heap_val <> None /\
      heap_final = update_H ((r, l), v) heap_val /\
      v_final = Unit /\
      phi_as_list phi =
        phi_as_list phi_loc ++ phi_as_list phi_val ++
        DA_Write r l v :: nil.
Proof.
  intros heap env rho w ea ev phi heap_final v_final HAssign.
  assert
    (HFirst :
      Step (initial_state heap env rho (Assign w ea ev)) Silent
        (StEval heap env rho ea (KAssignLoc w ev env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Assign w ea ev))
      Silent
      (StEval heap env rho ea (KAssignLoc w ev env rho KDone))
      phi heap_final v_final HFirst HAssign)
    as (phi_after_loc & HAfterLoc & HTraceStart).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho ea (KAssignLoc w ev env rho KDone)
      phi_after_loc heap_final v_final HAfterLoc)
    as (heap_loc & v_loc & phi_loc & phi_after_val &
        HLoc & HAfterVal & HTraceLoc).
  inversion HAfterVal as
    [| ? ? ? phi_after_val_tail ? HStepVal HStepsVal];
    subst; try discriminate.
  inversion HStepVal; subst.
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap_loc env rho ev (KAssignVal w l rho KDone)
      phi_after_val_tail heap_final v_final HStepsVal)
    as (heap_val & v & phi_val & phi_after_write &
        HVal & HAfterWrite & HTraceVal).
  inversion HAfterWrite as
    [| ? ? ? phi_after_done ? HStepWrite HStepsDone];
    subst; try discriminate.
  inversion HStepWrite; subst.
  match type of HStepsDone with
  | StepsPhi
      (StReturn (update_H ((?r_write, ?l_write), ?v_write) heap_val)
        Unit KDone)
      phi_after_done (StDone heap_final v_final) =>
      assert
        (HDone :
          StepsPhi
            (StReturn (update_H ((r_write, l_write), v_write) heap_val)
              Unit KDone)
            (Phi_Seq (label_phi Silent) Phi_Nil)
            (StDone (update_H ((r_write, l_write), v_write) heap_val)
              Unit))
      by
        (eapply (StepsPhi_Step _ Silent _ Phi_Nil _);
         [apply Step_Done | apply StepsPhi_Refl]);
      destruct
        (StepsPhi_terminal_deterministic
          (StReturn (update_H ((r_write, l_write), v_write) heap_val)
            Unit KDone)
          (Phi_Seq (label_phi Silent) Phi_Nil)
          (update_H ((r_write, l_write), v_write) heap_val)
          Unit
          phi_after_done heap_final v_final
          HDone HStepsDone)
        as [HTraceDone [HHeap HUnit]];
      exists phi_loc, heap_loc, l_write, phi_val, heap_val, v_write,
        r_write;
      split; [exact HLoc |];
      split; [exact HVal |];
      split; [eassumption |];
      split; [eassumption |];
      split; [symmetry; exact HHeap |];
      split; [symmetry; exact HUnit |];
      rewrite HTraceStart;
      simpl;
      rewrite HTraceLoc;
      simpl;
      rewrite HTraceVal;
      simpl;
      rewrite <- HTraceDone;
      repeat rewrite app_assoc;
      reflexivity
	  end.
Qed.

Lemma StepsPhiN_assign_terminal_decompose_counts :
  forall n heap env rho w ea ev phi heap_final v_final,
    StepsPhiN n (initial_state heap env rho (Assign w ea ev)) phi
      (StDone heap_final v_final) ->
    exists n_loc phi_loc heap_loc l
      n_val phi_val heap_val v r,
      n_loc < n /\
      n_val < n /\
      StepsPhiN n_loc (initial_state heap env rho ea) phi_loc
        (StDone heap_loc (Loc w l)) /\
      StepsPhiN n_val (initial_state heap_loc env rho ev) phi_val
        (StDone heap_val v) /\
      find_R w rho = Some r /\
      find_H (r, l) heap_val <> None /\
      heap_final = update_H ((r, l), v) heap_val /\
      v_final = Unit /\
      phi_as_list phi =
        phi_as_list phi_loc ++ phi_as_list phi_val ++
        DA_Write r l v :: nil.
Proof.
  intros n heap env rho w ea ev phi heap_final v_final HAssign.
  assert
    (HFirst :
      Step (initial_state heap env rho (Assign w ea ev)) Silent
        (StEval heap env rho ea (KAssignLoc w ev env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhiN_terminal_inv_step
      n
      (initial_state heap env rho (Assign w ea ev))
      Silent
      (StEval heap env rho ea (KAssignLoc w ev env rho KDone))
      phi heap_final v_final HFirst HAssign)
    as (n_after_loc & phi_after_loc & HNAfterLoc &
        HAfterLoc & HTraceStart).
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_loc heap env rho ea (KAssignLoc w ev env rho KDone)
      phi_after_loc heap_final v_final HAfterLoc)
    as (n_loc & n_after_val & heap_loc & v_loc &
        phi_loc & phi_after_val &
        HLeLoc & HLeAfterVal & HLoc & HAfterVal & HTraceLoc).
  inversion HAfterVal as
    [| n_after_val_tail state_val label_val state_after_val
       phi_after_val_tail final_val HStepVal HStepsVal];
    subst; try discriminate.
  inversion HStepVal; subst.
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_val_tail heap_loc env rho ev (KAssignVal w l rho KDone)
      phi_after_val_tail heap_final v_final HStepsVal)
    as (n_val & n_after_write & heap_val & v &
        phi_val & phi_after_write &
        HLeVal & HLeAfterWrite & HVal & HAfterWrite & HTraceVal).
  inversion HAfterWrite as
    [| n_after_done state_write label_write state_after_write
       phi_after_done final_write HStepWrite HStepsDone];
    subst; try discriminate.
  inversion HStepWrite; subst.
  match type of HStepsDone with
  | StepsPhiN ?n_done
      (StReturn (update_H ((?r_write, ?l_write), ?v_write) heap_val)
        Unit KDone)
      ?phi_done (StDone heap_final v_final) =>
      assert
        (HDone :
          StepsPhiN 1
            (StReturn (update_H ((r_write, l_write), v_write) heap_val)
              Unit KDone)
            (Phi_Seq (label_phi Silent) Phi_Nil)
            (StDone (update_H ((r_write, l_write), v_write) heap_val)
              Unit))
      by
        (eapply StepsPhiN_Step;
         [apply Step_Done | apply StepsPhiN_Refl]);
      destruct
        (StepsPhiN_terminal_deterministic
          1
          (StReturn (update_H ((r_write, l_write), v_write) heap_val)
            Unit KDone)
          (Phi_Seq (label_phi Silent) Phi_Nil)
          (update_H ((r_write, l_write), v_write) heap_val)
          Unit
          n_done phi_done heap_final v_final
          HDone HStepsDone)
        as [_ [HTraceDone [HHeap HUnit]]];
      exists n_loc, phi_loc, heap_loc, l_write,
        n_val, phi_val, heap_val, v_write, r_write;
      split; [lia |];
      split; [lia |];
      split; [exact HLoc |];
      split; [exact HVal |];
      split; [eassumption |];
      split; [eassumption |];
      split; [symmetry; exact HHeap |];
      split; [symmetry; exact HUnit |];
      rewrite HTraceStart;
      simpl;
      rewrite HTraceLoc;
      simpl;
      rewrite HTraceVal;
      simpl;
      rewrite <- HTraceDone;
      repeat rewrite app_assoc;
      reflexivity
  end.
Qed.

Lemma StepsPhi_assign_from_loc_value :
  forall heap env rho w ea ev
    phi_loc heap_loc l phi_val heap_val v r,
    StepsPhi (initial_state heap env rho ea) phi_loc
      (StDone heap_loc (Loc w l)) ->
    StepsPhi (initial_state heap_loc env rho ev) phi_val
      (StDone heap_val v) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_val <> None ->
    exists phi_assign,
      StepsPhi (initial_state heap env rho (Assign w ea ev)) phi_assign
        (StDone (update_H ((r, l), v) heap_val) Unit) /\
      phi_as_list phi_assign =
        phi_as_list phi_loc ++ phi_as_list phi_val ++
        DA_Write r l v :: nil.
Proof.
  intros heap env rho w ea ev
    phi_loc heap_loc l phi_val heap_val v r
    HLoc HVal HFindR HFindH.
  assert
    (HLocContinue :
      StepsPhi
        (StEval heap env rho ea (KAssignLoc w ev env rho KDone))
        phi_loc
        (StEval heap_loc env rho ev (KAssignVal w l rho KDone))).
  {
    eapply StepsPhi_initial_terminal_continue; eauto.
    apply Step_Assign_EvalVal.
  }
  destruct
    (StepsPhi_initial_terminal_continue_label
      heap_loc env rho ev phi_val heap_val v
      (KAssignVal w l rho KDone)
      (Act (DA_Write r l v))
      (StReturn (update_H ((r, l), v) heap_val) Unit KDone)
      HVal)
    as (phi_write & HWrite & HWriteTrace).
  {
    econstructor; eauto.
  }
  assert
    (HDone :
      StepsPhi
        (StReturn (update_H ((r, l), v) heap_val) Unit KDone)
        (Phi_Seq (label_phi Silent) Phi_Nil)
        (StDone (update_H ((r, l), v) heap_val) Unit)).
  {
    eapply StepsPhi_Step.
    - constructor.
    - constructor.
  }
  destruct
    (StepsPhi_trans_exists
      (StEval heap_loc env rho ev (KAssignVal w l rho KDone))
      phi_write
      (StReturn (update_H ((r, l), v) heap_val) Unit KDone)
      (Phi_Seq (label_phi Silent) Phi_Nil)
      (StDone (update_H ((r, l), v) heap_val) Unit)
      HWrite HDone)
    as (phi_val_done & HValDone & HValDoneTrace).
  destruct
    (StepsPhi_trans_exists
      (StEval heap env rho ea (KAssignLoc w ev env rho KDone))
      phi_loc
      (StEval heap_loc env rho ev (KAssignVal w l rho KDone))
      phi_val_done
      (StDone (update_H ((r, l), v) heap_val) Unit)
      HLocContinue HValDone)
    as (phi_rest & HRest & HRestTrace).
  exists (Phi_Seq (label_phi Silent) phi_rest).
  split.
  - unfold initial_state.
    eapply StepsPhi_Step.
    + constructor.
    + exact HRest.
  - simpl.
    rewrite HRestTrace.
    rewrite HValDoneTrace.
    rewrite HWriteTrace.
    simpl.
    repeat rewrite app_assoc.
    now rewrite app_nil_r.
Qed.

Lemma TcEnv_TcExp_var_find_E :
  forall stty rho env ctxt rgns x ty static,
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns, Var x, ty, static) ->
    exists v, find_E x env = Some v.
Proof.
  intros stty rho env ctxt rgns x ty static HTcEnv HTcExp.
  inversion HTcExp; subst.
  inversion HTcEnv; subst.
  eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_empty_trace :
  forall phi theta,
    phi_as_list phi = nil ->
    phi ⋞ theta.
Proof.
  exact Phi_Theta_Soundness_of_phi_as_list_nil.
Qed.

Theorem Correctness_soundness_ext_small_step_terminal_transfer :
  forall state phi_sound heap_sound v_sound phi heap v theta,
    StepsPhi state phi_sound (StDone heap_sound v_sound) ->
    StepsPhi state phi (StDone heap v) ->
    phi_sound ⋞ theta ->
    phi ⋞ theta.
Proof.
  intros state phi_sound heap_sound v_sound phi heap v theta
    HSoundSteps HSteps HSound.
  destruct
    (StepsPhi_terminal_deterministic
      state phi_sound heap_sound v_sound phi heap v HSoundSteps HSteps)
    as [HTrace _].
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with (phi2 := phi_sound).
  - symmetry. exact HTrace.
  - exact HSound.
Qed.

Lemma Phi_Theta_Soundness_alloc_abs_singleton :
  forall r l v,
    Phi_Elem (DA_Alloc r l v) ⋞ Some (singleton_set (CA_AllocAbs r)).
Proof.
  intros r l v.
  apply PTS_Elem.
  apply DAT_Alloc_Abs.
  constructor.
Qed.

Lemma Phi_Theta_Soundness_read_abs_singleton :
  forall r l v,
    Phi_Elem (DA_Read r l v) ⋞ Some (singleton_set (CA_ReadAbs r)).
Proof.
  intros r l v.
  apply PTS_Elem.
  apply DAT_Read_Abs.
  constructor.
Qed.

Lemma Phi_Theta_Soundness_read_conc_singleton :
  forall r l v,
    Phi_Elem (DA_Read r l v) ⋞ Some (singleton_set (CA_ReadConc r l)).
Proof.
  intros r l v.
  apply PTS_Elem.
  apply DAT_Read_Conc.
  constructor.
Qed.

Lemma Phi_Theta_Soundness_write_abs_singleton :
  forall r l v,
    Phi_Elem (DA_Write r l v) ⋞ Some (singleton_set (CA_WriteAbs r)).
Proof.
  intros r l v.
  apply PTS_Elem.
  apply DAT_Write_Abs.
  constructor.
Qed.

Lemma Phi_Theta_Soundness_write_conc_singleton :
  forall r l v,
    Phi_Elem (DA_Write r l v) ⋞ Some (singleton_set (CA_WriteConc r l)).
Proof.
  intros r l v.
  apply PTS_Elem.
  apply DAT_Write_Conc.
  constructor.
Qed.

Theorem Correctness_soundness_ext_small_step_unary_action_join_case :
  forall phi phi_prefix da theta_prefix theta_action,
    phi_as_list phi = phi_as_list phi_prefix ++ da :: nil ->
    phi_prefix ⋞ theta_prefix ->
    Phi_Elem da ⋞ theta_action ->
    phi ⋞ Union_Theta theta_prefix theta_action.
Proof.
  intros phi phi_prefix da theta_prefix theta_action
    HList HPrefixSound HActionSound.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with (phi2 := Phi_Seq phi_prefix (Phi_Elem da)).
  - simpl. exact HList.
  - apply EnsembleUnionComp; assumption.
Qed.

Theorem Correctness_soundness_ext_small_step_unary_action_empty_prefix_case :
  forall phi phi_prefix da theta_action,
    phi_as_list phi = phi_as_list phi_prefix ++ da :: nil ->
    phi_prefix ⋞ Theta_Empty ->
    Phi_Elem da ⋞ theta_action ->
    phi ⋞ theta_action.
Proof.
  intros phi phi_prefix da theta_action HList HPrefixSound HActionSound.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with (phi2 := Phi_Seq phi_prefix (Phi_Elem da)).
  - simpl. exact HList.
  - apply PTS_Seq.
    + eapply EmptyInAnyTheta; eauto.
    + exact HActionSound.
Qed.

Theorem Correctness_soundness_ext_small_step_binary_action_join_case :
  forall phi phi1 phi2 da theta1 theta2 theta_action,
    phi_as_list phi =
      phi_as_list phi1 ++ phi_as_list phi2 ++ da :: nil ->
    phi1 ⋞ theta1 ->
    phi2 ⋞ theta2 ->
    Phi_Elem da ⋞ theta_action ->
    phi ⋞ Union_Theta theta1 (Union_Theta theta2 theta_action).
Proof.
  intros phi phi1 phi2 da theta1 theta2 theta_action
    HList HSound1 HSound2 HActionSound.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with (phi2 := Phi_Seq phi1 (Phi_Seq phi2 (Phi_Elem da))).
  - simpl. exact HList.
  - apply EnsembleUnionComp.
    + exact HSound1.
    + apply EnsembleUnionComp; assumption.
Qed.

Theorem Correctness_soundness_ext_small_step_ref_abs_composed_case :
  forall heap env rho w e phi_arg heap_arg v r l theta_arg,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg v) ->
    find_R w rho = Some r ->
    allocate_H heap_arg r = l ->
    phi_arg ⋞ theta_arg ->
    exists phi_ref,
      StepsPhi (initial_state heap env rho (Ref w e)) phi_ref
        (StDone (update_H ((r, l), v) heap_arg)
          (Loc (Rgn_Const true false r) l)) /\
      phi_ref ⋞
        Union_Theta theta_arg (Some (singleton_set (CA_AllocAbs r))).
Proof.
  intros heap env rho w e phi_arg heap_arg v r l theta_arg
    HArg HFind HAlloc HArgSound.
  destruct
    (StepsPhi_ref_from_arg
      heap env rho w e phi_arg heap_arg v r l HArg HFind HAlloc)
    as (phi_ref & HRef & HList).
  exists phi_ref.
  split; [exact HRef |].
  eapply Correctness_soundness_ext_small_step_unary_action_join_case; eauto.
  apply Phi_Theta_Soundness_alloc_abs_singleton.
Qed.

Theorem Correctness_soundness_ext_small_step_ref_abs_terminal_case :
  forall heap env rho w e phi_arg heap_arg v r l theta_arg
    phi_ref heap_ref v_ref,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg v) ->
    find_R w rho = Some r ->
    allocate_H heap_arg r = l ->
    StepsPhi (initial_state heap env rho (Ref w e)) phi_ref
      (StDone heap_ref v_ref) ->
    phi_arg ⋞ theta_arg ->
    phi_ref ⋞
      Union_Theta theta_arg (Some (singleton_set (CA_AllocAbs r))).
Proof.
  intros heap env rho w e phi_arg heap_arg v r l theta_arg
    phi_ref heap_ref v_ref HArg HFind HAlloc HRef HArgSound.
  destruct
    (Correctness_soundness_ext_small_step_ref_abs_composed_case
      heap env rho w e phi_arg heap_arg v r l theta_arg
      HArg HFind HAlloc HArgSound)
    as (phi_ref_sound & HRefSoundSteps & HRefSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_ref_abs_summary_terminal_case :
  forall heap env rho w e phi_arg heap_arg v r l theta_arg
    heap_action phi_summary heap_summary theta_action
    phi_ref heap_ref v_ref,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg v) ->
    find_R w rho = Some r ->
    allocate_H heap_arg r = l ->
    StepsPhi (initial_state heap_action env rho (AllocAbs w)) phi_summary
      (StDone heap_summary (Eff theta_action)) ->
    StepsPhi (initial_state heap env rho (Ref w e)) phi_ref
      (StDone heap_ref v_ref) ->
    phi_arg ⋞ theta_arg ->
    phi_ref ⋞ Union_Theta theta_arg theta_action.
Proof.
  intros heap env rho w e phi_arg heap_arg v r l theta_arg
    heap_action phi_summary heap_summary theta_action
    phi_ref heap_ref v_ref HArg HFind HAlloc HSummary HRef HArgSound.
  destruct
    (StepsPhi_initial_allocabs_terminal
      heap_action env rho w r phi_summary heap_summary theta_action
      HFind HSummary)
    as [_ [_ HTheta]].
  subst theta_action.
  eapply (Correctness_soundness_ext_small_step_ref_abs_terminal_case
    heap env rho w e phi_arg heap_arg v r l theta_arg
    phi_ref heap_ref v_ref); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_deref_abs_composed_case :
  forall heap env rho w e phi_arg heap_arg r l v theta_arg,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg (Loc w l)) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_arg = Some v ->
    phi_arg ⋞ theta_arg ->
    exists phi_deref,
      StepsPhi (initial_state heap env rho (DeRef w e)) phi_deref
        (StDone heap_arg v) /\
      phi_deref ⋞
        Union_Theta theta_arg (Some (singleton_set (CA_ReadAbs r))).
Proof.
  intros heap env rho w e phi_arg heap_arg r l v theta_arg
    HArg HFindR HFindH HArgSound.
  destruct
    (StepsPhi_deref_from_arg
      heap env rho w e phi_arg heap_arg r l v HArg HFindR HFindH)
    as (phi_deref & HDeref & HList).
  exists phi_deref.
  split; [exact HDeref |].
  eapply Correctness_soundness_ext_small_step_unary_action_join_case; eauto.
  apply Phi_Theta_Soundness_read_abs_singleton.
Qed.

Theorem Correctness_soundness_ext_small_step_deref_abs_terminal_case :
  forall heap env rho w e phi_arg heap_arg r l v theta_arg
    phi_deref heap_deref v_deref,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg (Loc w l)) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_arg = Some v ->
    StepsPhi (initial_state heap env rho (DeRef w e)) phi_deref
      (StDone heap_deref v_deref) ->
    phi_arg ⋞ theta_arg ->
    phi_deref ⋞
      Union_Theta theta_arg (Some (singleton_set (CA_ReadAbs r))).
Proof.
  intros heap env rho w e phi_arg heap_arg r l v theta_arg
    phi_deref heap_deref v_deref HArg HFindR HFindH HDeref HArgSound.
  destruct
    (Correctness_soundness_ext_small_step_deref_abs_composed_case
      heap env rho w e phi_arg heap_arg r l v theta_arg
      HArg HFindR HFindH HArgSound)
    as (phi_deref_sound & HDerefSoundSteps & HDerefSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_deref_abs_summary_terminal_case :
  forall heap env rho w e phi_arg heap_arg r l v theta_arg
    heap_action phi_summary heap_summary theta_action
    phi_deref heap_deref v_deref,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg (Loc w l)) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_arg = Some v ->
    StepsPhi (initial_state heap_action env rho (ReadAbs w)) phi_summary
      (StDone heap_summary (Eff theta_action)) ->
    StepsPhi (initial_state heap env rho (DeRef w e)) phi_deref
      (StDone heap_deref v_deref) ->
    phi_arg ⋞ theta_arg ->
    phi_deref ⋞ Union_Theta theta_arg theta_action.
Proof.
  intros heap env rho w e phi_arg heap_arg r l v theta_arg
    heap_action phi_summary heap_summary theta_action
    phi_deref heap_deref v_deref
    HArg HFindR HFindH HSummary HDeref HArgSound.
  destruct
    (StepsPhi_initial_readabs_terminal
      heap_action env rho w r phi_summary heap_summary theta_action
      HFindR HSummary)
    as [_ [_ HTheta]].
  subst theta_action.
  eapply (Correctness_soundness_ext_small_step_deref_abs_terminal_case
    heap env rho w e phi_arg heap_arg r l v theta_arg
    phi_deref heap_deref v_deref); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_deref_conc_composed_case :
  forall heap env rho w e phi_arg heap_arg r l v,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg (Loc w l)) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_arg = Some v ->
    phi_arg ⋞ Theta_Empty ->
    exists phi_deref,
      StepsPhi (initial_state heap env rho (DeRef w e)) phi_deref
        (StDone heap_arg v) /\
      phi_deref ⋞ Some (singleton_set (CA_ReadConc r l)).
Proof.
  intros heap env rho w e phi_arg heap_arg r l v
    HArg HFindR HFindH HArgSound.
  destruct
    (StepsPhi_deref_from_arg
      heap env rho w e phi_arg heap_arg r l v HArg HFindR HFindH)
    as (phi_deref & HDeref & HList).
  exists phi_deref.
  split; [exact HDeref |].
  eapply Correctness_soundness_ext_small_step_unary_action_empty_prefix_case;
    eauto.
  apply Phi_Theta_Soundness_read_conc_singleton.
Qed.

Theorem Correctness_soundness_ext_small_step_deref_conc_terminal_case :
  forall heap env rho w e phi_arg heap_arg r l v
    phi_deref heap_deref v_deref,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg (Loc w l)) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_arg = Some v ->
    StepsPhi (initial_state heap env rho (DeRef w e)) phi_deref
      (StDone heap_deref v_deref) ->
    phi_arg ⋞ Theta_Empty ->
    phi_deref ⋞ Some (singleton_set (CA_ReadConc r l)).
Proof.
  intros heap env rho w e phi_arg heap_arg r l v
    phi_deref heap_deref v_deref HArg HFindR HFindH HDeref HArgSound.
  destruct
    (Correctness_soundness_ext_small_step_deref_conc_composed_case
      heap env rho w e phi_arg heap_arg r l v
      HArg HFindR HFindH HArgSound)
    as (phi_deref_sound & HDerefSoundSteps & HDerefSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_deref_conc_summary_terminal_case :
  forall heap env rho e phi_arg heap_arg r l v
    phi_summary heap_summary theta
    phi_deref heap_deref v_deref,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg (Loc (Rgn_Const true false r) l)) ->
    find_H (r, l) heap_arg = Some v ->
    StepsPhi (initial_state heap env rho (ReadConc e)) phi_summary
      (StDone heap_summary (Eff theta)) ->
    StepsPhi
      (initial_state heap env rho (DeRef (Rgn_Const true false r) e))
      phi_deref (StDone heap_deref v_deref) ->
    phi_arg ⋞ Theta_Empty ->
    phi_deref ⋞ theta.
Proof.
  intros heap env rho e phi_arg heap_arg r l v
    phi_summary heap_summary theta
    phi_deref heap_deref v_deref HArg HFindH HSummary HDeref HArgSound.
  destruct
    (StepsPhi_readconc_terminal_from_arg
      heap env rho e phi_arg heap_arg r l
      phi_summary heap_summary theta HArg HSummary)
    as [_ [_ HTheta]].
  subst.
  eapply Correctness_soundness_ext_small_step_deref_conc_terminal_case;
    eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_deref_conc_summary_terminal_direct_case :
  forall heap env rho e r
    phi_summary heap_summary theta
    phi_deref heap_deref v_deref,
    StepsPhi (initial_state heap env rho (ReadConc e)) phi_summary
      (StDone heap_summary (Eff theta)) ->
    StepsPhi
      (initial_state heap env rho (DeRef (Rgn_Const true false r) e))
      phi_deref (StDone heap_deref v_deref) ->
    (forall phi_arg heap_arg l,
      StepsPhi (initial_state heap env rho e) phi_arg
        (StDone heap_arg (Loc (Rgn_Const true false r) l)) ->
      phi_arg ⋞ Theta_Empty) ->
    phi_deref ⋞ theta.
Proof.
  intros heap env rho e r
    phi_summary heap_summary theta
    phi_deref heap_deref v_deref HSummary HDeref HArgIH.
  destruct
    (StepsPhi_deref_terminal_decompose
      heap env rho (Rgn_Const true false r) e
      phi_deref heap_deref v_deref HDeref)
    as (phi_arg & heap_arg & r_read & l & v &
        HArg & HFindR & HFindH & _ & _ & _).
  simpl in HFindR.
  inversion HFindR; subst r_read.
  pose proof (HArgIH phi_arg heap_arg l HArg) as HArgSound.
  eapply Correctness_soundness_ext_small_step_deref_conc_summary_terminal_case;
    eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_abs_composed_case :
  forall heap env rho w ea ev
    phi_loc heap_loc l phi_val heap_val v r theta_loc theta_val,
    StepsPhi (initial_state heap env rho ea) phi_loc
      (StDone heap_loc (Loc w l)) ->
    StepsPhi (initial_state heap_loc env rho ev) phi_val
      (StDone heap_val v) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_val <> None ->
    phi_loc ⋞ theta_loc ->
    phi_val ⋞ theta_val ->
    exists phi_assign,
      StepsPhi (initial_state heap env rho (Assign w ea ev)) phi_assign
        (StDone (update_H ((r, l), v) heap_val) Unit) /\
      phi_assign ⋞
        Union_Theta theta_loc
          (Union_Theta theta_val (Some (singleton_set (CA_WriteAbs r)))).
Proof.
  intros heap env rho w ea ev
    phi_loc heap_loc l phi_val heap_val v r theta_loc theta_val
    HLoc HVal HFindR HFindH HLocSound HValSound.
  destruct
    (StepsPhi_assign_from_loc_value
      heap env rho w ea ev
      phi_loc heap_loc l phi_val heap_val v r
      HLoc HVal HFindR HFindH)
    as (phi_assign & HAssign & HList).
  exists phi_assign.
  split; [exact HAssign |].
  eapply Correctness_soundness_ext_small_step_binary_action_join_case; eauto.
  apply Phi_Theta_Soundness_write_abs_singleton.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_abs_terminal_case :
  forall heap env rho w ea ev
    phi_loc heap_loc l phi_val heap_val v r theta_loc theta_val
    phi_assign heap_assign v_assign,
    StepsPhi (initial_state heap env rho ea) phi_loc
      (StDone heap_loc (Loc w l)) ->
    StepsPhi (initial_state heap_loc env rho ev) phi_val
      (StDone heap_val v) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_val <> None ->
    StepsPhi (initial_state heap env rho (Assign w ea ev)) phi_assign
      (StDone heap_assign v_assign) ->
    phi_loc ⋞ theta_loc ->
    phi_val ⋞ theta_val ->
    phi_assign ⋞
      Union_Theta theta_loc
        (Union_Theta theta_val (Some (singleton_set (CA_WriteAbs r)))).
Proof.
  intros heap env rho w ea ev
    phi_loc heap_loc l phi_val heap_val v r theta_loc theta_val
    phi_assign heap_assign v_assign
    HLoc HVal HFindR HFindH HAssign HLocSound HValSound.
  destruct
    (Correctness_soundness_ext_small_step_assign_abs_composed_case
      heap env rho w ea ev
      phi_loc heap_loc l phi_val heap_val v r theta_loc theta_val
      HLoc HVal HFindR HFindH HLocSound HValSound)
    as (phi_assign_sound & HAssignSoundSteps & HAssignSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_abs_summary_terminal_case :
  forall heap env rho w ea ev
    phi_loc heap_loc l phi_val heap_val v r theta_loc theta_val
    heap_action phi_summary heap_summary theta_action
    phi_assign heap_assign v_assign,
    StepsPhi (initial_state heap env rho ea) phi_loc
      (StDone heap_loc (Loc w l)) ->
    StepsPhi (initial_state heap_loc env rho ev) phi_val
      (StDone heap_val v) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_val <> None ->
    StepsPhi (initial_state heap_action env rho (WriteAbs w)) phi_summary
      (StDone heap_summary (Eff theta_action)) ->
    StepsPhi (initial_state heap env rho (Assign w ea ev)) phi_assign
      (StDone heap_assign v_assign) ->
    phi_loc ⋞ theta_loc ->
    phi_val ⋞ theta_val ->
    phi_assign ⋞ Union_Theta theta_loc
      (Union_Theta theta_val theta_action).
Proof.
  intros heap env rho w ea ev
    phi_loc heap_loc l phi_val heap_val v r theta_loc theta_val
    heap_action phi_summary heap_summary theta_action
    phi_assign heap_assign v_assign
    HLoc HVal HFindR HFindH HSummary HAssign HLocSound HValSound.
  destruct
    (StepsPhi_initial_writeabs_terminal
      heap_action env rho w r phi_summary heap_summary theta_action
      HFindR HSummary)
    as [_ [_ HTheta]].
  subst theta_action.
  eapply (Correctness_soundness_ext_small_step_assign_abs_terminal_case
    heap env rho w ea ev
    phi_loc heap_loc l phi_val heap_val v r theta_loc theta_val
    phi_assign heap_assign v_assign); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_conc_composed_case :
  forall heap env rho w ea ev
    phi_loc heap_loc l phi_val heap_val v r theta_loc theta_val,
    StepsPhi (initial_state heap env rho ea) phi_loc
      (StDone heap_loc (Loc w l)) ->
    StepsPhi (initial_state heap_loc env rho ev) phi_val
      (StDone heap_val v) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_val <> None ->
    phi_loc ⋞ theta_loc ->
    phi_val ⋞ theta_val ->
    exists phi_assign,
      StepsPhi (initial_state heap env rho (Assign w ea ev)) phi_assign
        (StDone (update_H ((r, l), v) heap_val) Unit) /\
      phi_assign ⋞
        Union_Theta theta_loc
          (Union_Theta theta_val (Some (singleton_set (CA_WriteConc r l)))).
Proof.
  intros heap env rho w ea ev
    phi_loc heap_loc l phi_val heap_val v r theta_loc theta_val
    HLoc HVal HFindR HFindH HLocSound HValSound.
  destruct
    (StepsPhi_assign_from_loc_value
      heap env rho w ea ev
      phi_loc heap_loc l phi_val heap_val v r
      HLoc HVal HFindR HFindH)
    as (phi_assign & HAssign & HList).
  exists phi_assign.
  split; [exact HAssign |].
  eapply Correctness_soundness_ext_small_step_binary_action_join_case; eauto.
  apply Phi_Theta_Soundness_write_conc_singleton.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_conc_terminal_case :
  forall heap env rho w ea ev
    phi_loc heap_loc l phi_val heap_val v r theta_loc theta_val
    phi_assign heap_assign v_assign,
    StepsPhi (initial_state heap env rho ea) phi_loc
      (StDone heap_loc (Loc w l)) ->
    StepsPhi (initial_state heap_loc env rho ev) phi_val
      (StDone heap_val v) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_val <> None ->
    StepsPhi (initial_state heap env rho (Assign w ea ev)) phi_assign
      (StDone heap_assign v_assign) ->
    phi_loc ⋞ theta_loc ->
    phi_val ⋞ theta_val ->
    phi_assign ⋞
      Union_Theta theta_loc
        (Union_Theta theta_val (Some (singleton_set (CA_WriteConc r l)))).
Proof.
  intros heap env rho w ea ev
    phi_loc heap_loc l phi_val heap_val v r theta_loc theta_val
    phi_assign heap_assign v_assign
    HLoc HVal HFindR HFindH HAssign HLocSound HValSound.
  destruct
    (Correctness_soundness_ext_small_step_assign_conc_composed_case
      heap env rho w ea ev
      phi_loc heap_loc l phi_val heap_val v r theta_loc theta_val
      HLoc HVal HFindR HFindH HLocSound HValSound)
    as (phi_assign_sound & HAssignSoundSteps & HAssignSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_conc_summary_terminal_case :
  forall heap env rho ea ev
    phi_loc heap_loc r l phi_val heap_val v theta_loc theta_val
    phi_summary heap_summary theta_action
    phi_assign heap_assign v_assign,
    StepsPhi (initial_state heap env rho ea) phi_loc
      (StDone heap_loc (Loc (Rgn_Const true false r) l)) ->
    StepsPhi (initial_state heap_loc env rho ev) phi_val
      (StDone heap_val v) ->
    find_H (r, l) heap_val <> None ->
    StepsPhi (initial_state heap env rho (WriteConc ea)) phi_summary
      (StDone heap_summary (Eff theta_action)) ->
    StepsPhi
      (initial_state heap env rho (Assign (Rgn_Const true false r) ea ev))
      phi_assign (StDone heap_assign v_assign) ->
    phi_loc ⋞ theta_loc ->
    phi_val ⋞ theta_val ->
    phi_assign ⋞ Union_Theta theta_loc
      (Union_Theta theta_val theta_action).
Proof.
  intros heap env rho ea ev
    phi_loc heap_loc r l phi_val heap_val v theta_loc theta_val
    phi_summary heap_summary theta_action
    phi_assign heap_assign v_assign
    HLoc HVal HFindH HSummary HAssign HLocSound HValSound.
  destruct
    (StepsPhi_writeconc_terminal_from_arg
      heap env rho ea phi_loc heap_loc r l
      phi_summary heap_summary theta_action HLoc HSummary)
    as [_ [_ HTheta]].
  subst.
  eapply Correctness_soundness_ext_small_step_assign_conc_terminal_case;
    eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_num_case :
  forall heap env rho n phi heap' v theta,
    StepsPhi (initial_state heap env rho (Const n)) phi (StDone heap' v) ->
    phi ⋞ theta.
Proof.
  intros heap env rho n phi heap' v theta HSteps.
  apply Phi_Theta_Soundness_of_phi_as_list_nil.
  eapply StepsPhi_initial_const_terminal_trace_nil; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_bool_case :
  forall heap env rho b phi heap' v theta,
    StepsPhi (initial_state heap env rho (Bool b)) phi (StDone heap' v) ->
    phi ⋞ theta.
Proof.
  intros heap env rho b phi heap' v theta HSteps.
  apply Phi_Theta_Soundness_of_phi_as_list_nil.
  eapply StepsPhi_initial_bool_terminal_trace_nil; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_var_case :
  forall heap env rho x v_lookup phi heap' v theta,
    find_E x env = Some v_lookup ->
    StepsPhi (initial_state heap env rho (Var x)) phi (StDone heap' v) ->
    phi ⋞ theta.
Proof.
  intros heap env rho x v_lookup phi heap' v theta HFind HSteps.
  apply Phi_Theta_Soundness_of_phi_as_list_nil.
  eapply StepsPhi_initial_var_terminal_trace_nil; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_var_typed_case :
  forall heap env rho x phi heap' v theta stty ctxt rgns ty static,
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns, Var x, ty, static) ->
    StepsPhi (initial_state heap env rho (Var x)) phi (StDone heap' v) ->
    phi ⋞ theta.
Proof.
  intros heap env rho x phi heap' v theta stty ctxt rgns ty static
    HTcEnv HTcExp HSteps.
  destruct
    (TcEnv_TcExp_var_find_E
      stty rho env ctxt rgns x ty static HTcEnv HTcExp)
    as [v_lookup HFind].
  eapply Correctness_soundness_ext_small_step_var_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_top_summary_case :
  forall phi_body heap env rho phi_summary heap_summary theta,
    StepsPhi (initial_state heap env rho Top) phi_summary
      (StDone heap_summary (Eff theta)) ->
    phi_body ⋞ theta.
Proof.
  intros phi_body heap env rho phi_summary heap_summary theta HSummary.
  destruct
    (StepsPhi_initial_top_terminal
      heap env rho phi_summary heap_summary theta HSummary)
    as [_ [_ HTheta]].
  subst.
  apply PhiInThetaTop.
Qed.

Theorem Correctness_soundness_ext_small_step_ternary_join_case :
  forall phi_app phi_fun phi_arg phi_body theta,
    phi_as_list phi_app =
      phi_as_list phi_fun ++ phi_as_list phi_arg ++ phi_as_list phi_body ->
    phi_fun ⋞ theta ->
    phi_arg ⋞ theta ->
    phi_body ⋞ theta ->
    phi_app ⋞ theta.
Proof.
  intros phi_app phi_fun phi_arg phi_body theta
    HList HFunSound HArgSound HBodySound.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with (phi2 := Phi_Seq phi_fun (Phi_Seq phi_arg phi_body)).
  - simpl. exact HList.
  - apply PTS_Seq.
    + exact HFunSound.
    + now apply PTS_Seq.
Qed.

Lemma StepsPhi_mu_app_terminal_decompose :
  forall heap env rho ef ea phi heap_final v_final,
    StepsPhi (initial_state heap env rho (Mu_App ef ea)) phi
      (StDone heap_final v_final) ->
    exists env_fun rho_fun f x ec ee
      phi_fun heap_fun
      phi_arg heap_arg v_arg
      phi_body,
      StepsPhi (initial_state heap env rho ef) phi_fun
        (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) /\
      StepsPhi (initial_state heap_fun env rho ea) phi_arg
        (StDone heap_arg v_arg) /\
      StepsPhi
        (initial_state heap_arg
          (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
            (x, v_arg) env_fun)
          rho_fun ec) phi_body
        (StDone heap_final v_final) /\
      phi_as_list phi =
        phi_as_list phi_fun ++ phi_as_list phi_arg ++ phi_as_list phi_body.
Proof.
  intros heap env rho ef ea phi heap_final v_final HApp.
  assert
    (HFirst :
      Step (initial_state heap env rho (Mu_App ef ea)) Silent
        (StEval heap env rho ef (KMuAppFun ea env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Mu_App ef ea))
      Silent
      (StEval heap env rho ef (KMuAppFun ea env rho KDone))
      phi heap_final v_final HFirst HApp)
    as (phi_after_fun & HAfterFun & HTraceStart).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho ef (KMuAppFun ea env rho KDone)
      phi_after_fun heap_final v_final HAfterFun)
    as (heap_fun & v_fun & phi_fun & phi_after_arg &
        HFun & HAfterArg & HTraceFun).
  inversion HAfterArg as
    [| ? ? ? phi_after_arg_tail ? HStepArg HStepsArg];
    subst; try discriminate.
  inversion HStepArg; subst.
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap_fun env rho ea
      (KMuAppArg env' rho' f x ec ee KDone)
      phi_after_arg_tail heap_final v_final HStepsArg)
    as (heap_arg & v_arg & phi_arg & phi_after_body &
        HArg & HAfterBody & HTraceArg).
  inversion HAfterBody as
    [| ? ? ? phi_body ? HStepBody HBody];
    subst; try discriminate.
  inversion HStepBody; subst.
  exists env', rho', f, x, ec, ee,
    phi_fun, heap_fun, phi_arg, heap_arg, v_arg, phi_body.
  split; [exact HFun |].
  split; [exact HArg |].
  split; [exact HBody |].
  rewrite HTraceStart.
  simpl.
  rewrite HTraceFun.
  simpl.
  rewrite HTraceArg.
  simpl.
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

Lemma StepsPhi_eff_app_terminal_decompose :
  forall heap env rho ef ea phi heap_final v_final,
    StepsPhi (initial_state heap env rho (Eff_App ef ea)) phi
      (StDone heap_final v_final) ->
    exists env_fun rho_fun f x ec ee
      phi_fun heap_fun
      phi_arg heap_arg v_arg
      phi_body,
      StepsPhi (initial_state heap env rho ef) phi_fun
        (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) /\
      StepsPhi (initial_state heap_fun env rho ea) phi_arg
        (StDone heap_arg v_arg) /\
      StepsPhi
        (initial_state heap_arg
          (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
            (x, v_arg) env_fun)
          rho_fun ee) phi_body
        (StDone heap_final v_final) /\
      phi_as_list phi =
        phi_as_list phi_fun ++ phi_as_list phi_arg ++ phi_as_list phi_body.
Proof.
  intros heap env rho ef ea phi heap_final v_final HApp.
  assert
    (HFirst :
      Step (initial_state heap env rho (Eff_App ef ea)) Silent
        (StEval heap env rho ef (KEffAppFun ea env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Eff_App ef ea))
      Silent
      (StEval heap env rho ef (KEffAppFun ea env rho KDone))
      phi heap_final v_final HFirst HApp)
    as (phi_after_fun & HAfterFun & HTraceStart).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho ef (KEffAppFun ea env rho KDone)
      phi_after_fun heap_final v_final HAfterFun)
    as (heap_fun & v_fun & phi_fun & phi_after_arg &
        HFun & HAfterArg & HTraceFun).
  inversion HAfterArg as
    [| ? ? ? phi_after_arg_tail ? HStepArg HStepsArg];
    subst; try discriminate.
  inversion HStepArg; subst.
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap_fun env rho ea
      (KEffAppArg env' rho' f x ec ee KDone)
      phi_after_arg_tail heap_final v_final HStepsArg)
    as (heap_arg & v_arg & phi_arg & phi_after_body &
        HArg & HAfterBody & HTraceArg).
  inversion HAfterBody as
    [| ? ? ? phi_body ? HStepBody HBody];
    subst; try discriminate.
  inversion HStepBody; subst.
  exists env', rho', f, x, ec, ee,
    phi_fun, heap_fun, phi_arg, heap_arg, v_arg, phi_body.
  split; [exact HFun |].
  split; [exact HArg |].
  split; [exact HBody |].
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

Lemma StepsPhi_rgn_app_terminal_decompose :
  forall heap env rho er w phi heap_final v_final,
    StepsPhi (initial_state heap env rho (Rgn_App er w)) phi
      (StDone heap_final v_final) ->
    exists env_fun rho_fun x eb r
      phi_fun heap_fun
      phi_body,
      StepsPhi (initial_state heap env rho er) phi_fun
        (StDone heap_fun (Cls (env_fun, rho_fun, Lambda x eb))) /\
      find_R w rho = Some r /\
      StepsPhi
        (initial_state heap_fun env_fun (update_R (x, r) rho_fun) eb)
        phi_body
        (StDone heap_final v_final) /\
      phi_as_list phi = phi_as_list phi_fun ++ phi_as_list phi_body.
Proof.
  intros heap env rho er w phi heap_final v_final HApp.
  assert
    (HFirst :
      Step (initial_state heap env rho (Rgn_App er w)) Silent
        (StEval heap env rho er (KRgnApp w rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Rgn_App er w))
      Silent
      (StEval heap env rho er (KRgnApp w rho KDone))
      phi heap_final v_final HFirst HApp)
    as (phi_after_fun & HAfterFun & HTraceStart).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho er (KRgnApp w rho KDone)
      phi_after_fun heap_final v_final HAfterFun)
    as (heap_fun & v_fun & phi_fun & phi_after_body &
        HFun & HAfterBody & HTraceFun).
  inversion HAfterBody as
    [| ? ? ? phi_body ? HStepBody HBody];
    subst; try discriminate.
  inversion HStepBody; subst.
  exists env', rho', x, eb, r, phi_fun, heap_fun, phi_body.
  split; [exact HFun |].
  split; [assumption |].
  split; [exact HBody |].
  rewrite HTraceStart.
  simpl.
  rewrite HTraceFun.
	  simpl.
	  reflexivity.
Qed.

Lemma StepsPhiN_rgn_app_terminal_decompose_counts :
  forall n heap env rho er w phi heap_final v_final,
    StepsPhiN n (initial_state heap env rho (Rgn_App er w)) phi
      (StDone heap_final v_final) ->
    exists env_fun rho_fun x eb r
      n_fun phi_fun heap_fun
      n_body phi_body,
      n_fun < n /\
      n_body < n /\
      StepsPhiN n_fun (initial_state heap env rho er) phi_fun
        (StDone heap_fun (Cls (env_fun, rho_fun, Lambda x eb))) /\
      find_R w rho = Some r /\
      StepsPhiN n_body
        (initial_state heap_fun env_fun (update_R (x, r) rho_fun) eb)
        phi_body
        (StDone heap_final v_final) /\
      phi_as_list phi = phi_as_list phi_fun ++ phi_as_list phi_body.
Proof.
  intros n heap env rho er w phi heap_final v_final HApp.
  assert
    (HFirst :
      Step (initial_state heap env rho (Rgn_App er w)) Silent
        (StEval heap env rho er (KRgnApp w rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhiN_terminal_inv_step
      n
      (initial_state heap env rho (Rgn_App er w))
      Silent
      (StEval heap env rho er (KRgnApp w rho KDone))
      phi heap_final v_final HFirst HApp)
    as (n_after_fun & phi_after_fun & HNAfterFun &
        HAfterFun & HTraceStart).
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_fun heap env rho er (KRgnApp w rho KDone)
      phi_after_fun heap_final v_final HAfterFun)
    as (n_fun & n_after_body & heap_fun & v_fun &
        phi_fun & phi_after_body &
        HLeFun & HLeAfterBody & HFun & HAfterBody & HTraceFun).
  inversion HAfterBody as
    [| n_body state_body label_body state_after_body
       phi_body final_body HStepBody HBody];
    subst; try discriminate.
  inversion HStepBody; subst.
  exists env', rho', x, eb, r,
    n_fun, phi_fun, heap_fun,
    n_body, phi_body.
  split; [lia |].
  split; [lia |].
  split; [exact HFun |].
  split; [assumption |].
  split; [exact HBody |].
  rewrite HTraceStart.
  simpl.
  rewrite HTraceFun.
  simpl.
  reflexivity.
Qed.

Theorem Correctness_soundness_ext_small_step_mu_app_composed_case :
  forall heap env rho ef ea env_fun rho_fun f x ec ee
    phi_fun heap_fun phi_arg heap_arg v_arg phi_body heap_body v_body theta,
    StepsPhi (initial_state heap env rho ef) phi_fun
      (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) ->
    StepsPhi (initial_state heap_fun env rho ea) phi_arg
      (StDone heap_arg v_arg) ->
    StepsPhi
      (initial_state heap_arg
        (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
          (x, v_arg) env_fun)
        rho_fun ec) phi_body
      (StDone heap_body v_body) ->
    phi_fun ⋞ theta ->
    phi_arg ⋞ theta ->
    phi_body ⋞ theta ->
    exists phi_app,
      StepsPhi (initial_state heap env rho (Mu_App ef ea)) phi_app
        (StDone heap_body v_body) /\
      phi_app ⋞ theta.
Proof.
  intros heap env rho ef ea env_fun rho_fun f x ec ee
    phi_fun heap_fun phi_arg heap_arg v_arg phi_body heap_body v_body theta
    HFun HArg HBody HFunSound HArgSound HBodySound.
  destruct
    (StepsPhi_mu_app_from_fun_arg_body
      heap env rho ef ea env_fun rho_fun f x ec ee
      phi_fun heap_fun phi_arg heap_arg v_arg phi_body heap_body v_body
      HFun HArg HBody)
    as (phi_app & HApp & HList).
  exists phi_app.
  split; [exact HApp |].
  eapply Correctness_soundness_ext_small_step_ternary_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_mu_app_terminal_case :
  forall heap env rho ef ea env_fun rho_fun f x ec ee
    phi_fun heap_fun phi_arg heap_arg v_arg phi_body heap_body v_body theta
    phi_app heap_app v_app,
    StepsPhi (initial_state heap env rho ef) phi_fun
      (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) ->
    StepsPhi (initial_state heap_fun env rho ea) phi_arg
      (StDone heap_arg v_arg) ->
    StepsPhi
      (initial_state heap_arg
        (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
          (x, v_arg) env_fun)
        rho_fun ec) phi_body
      (StDone heap_body v_body) ->
    StepsPhi (initial_state heap env rho (Mu_App ef ea)) phi_app
      (StDone heap_app v_app) ->
    phi_fun ⋞ theta ->
    phi_arg ⋞ theta ->
    phi_body ⋞ theta ->
    phi_app ⋞ theta.
Proof.
  intros heap env rho ef ea env_fun rho_fun f x ec ee
    phi_fun heap_fun phi_arg heap_arg v_arg phi_body heap_body v_body theta
    phi_app heap_app v_app HFun HArg HBody HApp
    HFunSound HArgSound HBodySound.
  destruct
    (Correctness_soundness_ext_small_step_mu_app_composed_case
      heap env rho ef ea env_fun rho_fun f x ec ee
      phi_fun heap_fun phi_arg heap_arg v_arg phi_body heap_body v_body theta
      HFun HArg HBody HFunSound HArgSound HBodySound)
    as (phi_app_sound & HAppSoundSteps & HAppSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_eff_app_composed_case :
  forall heap env rho ef ea env_fun rho_fun f x ec ee
    phi_fun heap_fun phi_arg heap_arg v_arg phi_body heap_body v_body theta,
    StepsPhi (initial_state heap env rho ef) phi_fun
      (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) ->
    StepsPhi (initial_state heap_fun env rho ea) phi_arg
      (StDone heap_arg v_arg) ->
    StepsPhi
      (initial_state heap_arg
        (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
          (x, v_arg) env_fun)
        rho_fun ee) phi_body
      (StDone heap_body v_body) ->
    phi_fun ⋞ theta ->
    phi_arg ⋞ theta ->
    phi_body ⋞ theta ->
    exists phi_app,
      StepsPhi (initial_state heap env rho (Eff_App ef ea)) phi_app
        (StDone heap_body v_body) /\
      phi_app ⋞ theta.
Proof.
  intros heap env rho ef ea env_fun rho_fun f x ec ee
    phi_fun heap_fun phi_arg heap_arg v_arg phi_body heap_body v_body theta
    HFun HArg HBody HFunSound HArgSound HBodySound.
  destruct
    (StepsPhi_eff_app_from_fun_arg_body
      heap env rho ef ea env_fun rho_fun f x ec ee
      phi_fun heap_fun phi_arg heap_arg v_arg phi_body heap_body v_body
      HFun HArg HBody)
    as (phi_app & HApp & HList).
  exists phi_app.
  split; [exact HApp |].
  eapply Correctness_soundness_ext_small_step_ternary_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_eff_app_terminal_case :
  forall heap env rho ef ea env_fun rho_fun f x ec ee
    phi_fun heap_fun phi_arg heap_arg v_arg phi_body heap_body v_body theta
    phi_app heap_app v_app,
    StepsPhi (initial_state heap env rho ef) phi_fun
      (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) ->
    StepsPhi (initial_state heap_fun env rho ea) phi_arg
      (StDone heap_arg v_arg) ->
    StepsPhi
      (initial_state heap_arg
        (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
          (x, v_arg) env_fun)
        rho_fun ee) phi_body
      (StDone heap_body v_body) ->
    StepsPhi (initial_state heap env rho (Eff_App ef ea)) phi_app
      (StDone heap_app v_app) ->
    phi_fun ⋞ theta ->
    phi_arg ⋞ theta ->
    phi_body ⋞ theta ->
    phi_app ⋞ theta.
Proof.
  intros heap env rho ef ea env_fun rho_fun f x ec ee
    phi_fun heap_fun phi_arg heap_arg v_arg phi_body heap_body v_body theta
    phi_app heap_app v_app HFun HArg HBody HApp
    HFunSound HArgSound HBodySound.
  destruct
    (Correctness_soundness_ext_small_step_eff_app_composed_case
      heap env rho ef ea env_fun rho_fun f x ec ee
      phi_fun heap_fun phi_arg heap_arg v_arg phi_body heap_body v_body theta
      HFun HArg HBody HFunSound HArgSound HBodySound)
    as (phi_app_sound & HAppSoundSteps & HAppSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Lemma StepsPhi_eff_app_summary_terminal_theta :
  forall heap env rho ef ea env_fun rho_fun f x ec ee
    phi_fun heap_fun phi_arg heap_arg v_arg
    phi_body heap_body theta_body
    phi_summary heap_summary theta_summary,
    StepsPhi (initial_state heap env rho ef) phi_fun
      (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) ->
    StepsPhi (initial_state heap_fun env rho ea) phi_arg
      (StDone heap_arg v_arg) ->
    StepsPhi
      (initial_state heap_arg
        (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
          (x, v_arg) env_fun)
        rho_fun ee) phi_body
      (StDone heap_body (Eff theta_body)) ->
    StepsPhi (initial_state heap env rho (Eff_App ef ea)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    theta_summary = theta_body.
Proof.
  intros heap env rho ef ea env_fun rho_fun f x ec ee
    phi_fun heap_fun phi_arg heap_arg v_arg
    phi_body heap_body theta_body
    phi_summary heap_summary theta_summary HFun HArg HBody HSummary.
  destruct
    (StepsPhi_eff_app_from_fun_arg_body
      heap env rho ef ea env_fun rho_fun f x ec ee
      phi_fun heap_fun phi_arg heap_arg v_arg
      phi_body heap_body (Eff theta_body)
      HFun HArg HBody)
    as (phi_summary_sound & HSummarySound & _).
  destruct
    (StepsPhi_effect_terminal_deterministic
      (initial_state heap env rho (Eff_App ef ea))
      phi_summary_sound heap_body theta_body
      phi_summary heap_summary theta_summary
      HSummarySound HSummary)
    as [_ [_ HTheta]].
  now symmetry.
Qed.

Theorem Correctness_soundness_ext_small_step_mu_app_summary_terminal_case :
  forall heap env rho ef ea env_fun rho_fun f x ec ee
    phi_fun heap_fun phi_arg heap_arg v_arg
    phi_body heap_body v_body
    phi_summary_body heap_summary_body theta_body
    phi_summary heap_summary theta_summary
    phi_app heap_app v_app,
    StepsPhi (initial_state heap env rho ef) phi_fun
      (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) ->
    StepsPhi (initial_state heap_fun env rho ea) phi_arg
      (StDone heap_arg v_arg) ->
    StepsPhi
      (initial_state heap_arg
        (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
          (x, v_arg) env_fun)
        rho_fun ec) phi_body
      (StDone heap_body v_body) ->
    StepsPhi
      (initial_state heap_arg
        (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
          (x, v_arg) env_fun)
        rho_fun ee) phi_summary_body
      (StDone heap_summary_body (Eff theta_body)) ->
    StepsPhi (initial_state heap env rho (Eff_App ef ea)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Mu_App ef ea)) phi_app
      (StDone heap_app v_app) ->
    phi_fun ⋞ theta_summary ->
    phi_arg ⋞ theta_summary ->
    phi_body ⋞ theta_body ->
    phi_app ⋞ theta_summary.
Proof.
  intros heap env rho ef ea env_fun rho_fun f x ec ee
    phi_fun heap_fun phi_arg heap_arg v_arg
    phi_body heap_body v_body
    phi_summary_body heap_summary_body theta_body
    phi_summary heap_summary theta_summary
    phi_app heap_app v_app
    HFun HArg HBody HSummaryBody HSummary HApp
    HFunSound HArgSound HBodySound.
  pose proof
    (StepsPhi_eff_app_summary_terminal_theta
      heap env rho ef ea env_fun rho_fun f x ec ee
      phi_fun heap_fun phi_arg heap_arg v_arg
      phi_summary_body heap_summary_body theta_body
      phi_summary heap_summary theta_summary
      HFun HArg HSummaryBody HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_mu_app_terminal_case
    heap env rho ef ea env_fun rho_fun f x ec ee
    phi_fun heap_fun phi_arg heap_arg v_arg
    phi_body heap_body v_body theta_body
    phi_app heap_app v_app); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_mu_app_summary_terminal_direct_case :
  forall heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_ef static_ef ty_ea static_ea,
    StepsPhi (initial_state heap env rho (Mu_App ef ea)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho (Eff_App ef ea)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ef, ty_ef, static_ef) ->
    TcExp (ctxt, rgns, ea, ty_ea, static_ea) ->
    ReadOnlyStatic (fold_subst_eps rho static_ef) ->
    ReadOnlyStatic (fold_subst_eps rho static_ea) ->
    ReadOnlyPhi phi_summary ->
    (forall phi_fun heap_fun env_fun rho_fun f x ec ee,
      StepsPhi (initial_state heap env rho ef) phi_fun
        (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) ->
      phi_fun ⋞ theta_summary) ->
    (forall phi_arg heap_arg v_arg,
      StepsPhi (initial_state heap env rho ea) phi_arg
        (StDone heap_arg v_arg) ->
      phi_arg ⋞ theta_summary) ->
    (forall env_fun rho_fun f x ec ee v_arg
            phi_body heap_body v_body
            phi_summary_body heap_summary_body theta_body,
      StepsPhi
        (initial_state heap
          (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
            (x, v_arg) env_fun)
          rho_fun ec) phi_body
        (StDone heap_body v_body) ->
      StepsPhi
        (initial_state heap
          (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
            (x, v_arg) env_fun)
          rho_fun ee) phi_summary_body
        (StDone heap_summary_body (Eff theta_body)) ->
      ReadOnlyPhi phi_summary_body ->
      phi_body ⋞ theta_body) ->
    phi_app ⋞ theta_summary.
Proof.
  intros heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_ef static_ef ty_ea static_ea
    HApp HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEf HTcEa HReadOnlyStaticEf HReadOnlyStaticEa HReadOnlySummary
    HFunIH HArgIH HBodyIH.
  destruct
    (StepsPhi_mu_app_terminal_decompose
      heap env rho ef ea phi_app heap_app v_app HApp)
    as (env_fun & rho_fun & f & x & ec & ee &
        phi_fun & heap_fun & phi_arg & heap_arg & v_arg &
        phi_body & HFun & HArg & HBody & _).
  destruct
    (StepsPhi_eff_app_terminal_decompose
      heap env rho ef ea phi_summary heap_summary (Eff theta_summary)
      HSummary)
    as (env_fun_summary & rho_fun_summary & f_summary & x_summary &
        ec_summary & ee_summary &
        phi_fun_summary & heap_fun_summary &
        phi_arg_summary & heap_arg_summary & v_arg_summary &
        phi_body_summary &
        HFunSummary & HArgSummary & HBodySummary & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list3_right
      phi_summary phi_fun_summary phi_arg_summary phi_body_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyBodySummary.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ef stty ctxt rgns ty_ef static_ef
      phi_fun heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEf HFun
      HReadOnlyStaticEf) as HHeapFun.
  subst heap_fun.
  destruct
    (StepsPhi_terminal_deterministic
      (initial_state heap env rho ef)
      phi_fun heap (Cls (env_fun, rho_fun, Mu f x ec ee))
      phi_fun_summary heap_fun_summary
        (Cls (env_fun_summary, rho_fun_summary,
          Mu f_summary x_summary ec_summary ee_summary))
      HFun HFunSummary)
    as [_ [HHeapFunSummary HClosureEq]].
  symmetry in HHeapFunSummary.
  subst heap_fun_summary.
  inversion HClosureEq; subst.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ea stty ctxt rgns ty_ea static_ea
      phi_arg heap_arg v_arg
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEa HArg
      HReadOnlyStaticEa) as HHeapArg.
  subst heap_arg.
  destruct
    (StepsPhi_terminal_deterministic
      (initial_state heap env rho ea)
      phi_arg heap v_arg
      phi_arg_summary heap_arg_summary v_arg_summary
      HArg HArgSummary)
    as [_ [HHeapArgSummary HArgEq]].
  symmetry in HHeapArgSummary.
  subst heap_arg_summary.
  subst v_arg_summary.
  pose proof
    (HFunIH
      phi_fun heap env_fun_summary rho_fun_summary
      f_summary x_summary ec_summary ee_summary HFun) as HFunSound.
  pose proof
    (HArgIH phi_arg heap v_arg HArg) as HArgSound.
  pose proof
    (HBodyIH env_fun_summary rho_fun_summary
      f_summary x_summary ec_summary ee_summary v_arg
      phi_body heap_app v_app
      phi_body_summary heap_summary theta_summary
      HBody HBodySummary HReadOnlyBodySummary) as HBodySound.
  eapply (Correctness_soundness_ext_small_step_mu_app_summary_terminal_case
    heap env rho ef ea env_fun_summary rho_fun_summary
    f_summary x_summary ec_summary ee_summary
    phi_fun heap phi_arg heap v_arg
    phi_body heap_app v_app
    phi_body_summary heap_summary theta_summary
    phi_summary heap_summary theta_summary
    phi_app heap_app v_app); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_rgn_app_composed_case :
  forall heap env rho er w env_fun rho_fun x eb r
    phi_fun heap_fun phi_body heap_body v_body theta,
    StepsPhi (initial_state heap env rho er) phi_fun
      (StDone heap_fun (Cls (env_fun, rho_fun, Lambda x eb))) ->
    find_R w rho = Some r ->
    StepsPhi
      (initial_state heap_fun env_fun (update_R (x, r) rho_fun) eb)
      phi_body
      (StDone heap_body v_body) ->
    phi_fun ⋞ theta ->
    phi_body ⋞ theta ->
    exists phi_app,
      StepsPhi (initial_state heap env rho (Rgn_App er w)) phi_app
        (StDone heap_body v_body) /\
      phi_app ⋞ theta.
Proof.
  intros heap env rho er w env_fun rho_fun x eb r
    phi_fun heap_fun phi_body heap_body v_body theta
    HFun HFind HBody HFunSound HBodySound.
  destruct
    (StepsPhi_rgn_app_from_fun_body
      heap env rho er w env_fun rho_fun x eb r
      phi_fun heap_fun phi_body heap_body v_body HFun HFind HBody)
    as (phi_app & HApp & HList).
  exists phi_app.
  split; [exact HApp |].
  eapply Phi_Theta_Soundness_of_phi_as_list_app; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_rgn_app_terminal_case :
  forall heap env rho er w env_fun rho_fun x eb r
    phi_fun heap_fun phi_body heap_body v_body theta
    phi_app heap_app v_app,
    StepsPhi (initial_state heap env rho er) phi_fun
      (StDone heap_fun (Cls (env_fun, rho_fun, Lambda x eb))) ->
    find_R w rho = Some r ->
    StepsPhi
      (initial_state heap_fun env_fun (update_R (x, r) rho_fun) eb)
      phi_body
      (StDone heap_body v_body) ->
    StepsPhi (initial_state heap env rho (Rgn_App er w)) phi_app
      (StDone heap_app v_app) ->
    phi_fun ⋞ theta ->
    phi_body ⋞ theta ->
    phi_app ⋞ theta.
Proof.
  intros heap env rho er w env_fun rho_fun x eb r
    phi_fun heap_fun phi_body heap_body v_body theta
    phi_app heap_app v_app HFun HFind HBody HApp HFunSound HBodySound.
  destruct
    (Correctness_soundness_ext_small_step_rgn_app_composed_case
      heap env rho er w env_fun rho_fun x eb r
      phi_fun heap_fun phi_body heap_body v_body theta
      HFun HFind HBody HFunSound HBodySound)
    as (phi_app_sound & HAppSoundSteps & HAppSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_case :
  forall heap env rho er w env_fun rho_fun x eb r
    phi_fun heap_fun phi_body heap_body v_body
    phi_summary heap_summary theta_summary
    phi_app heap_app v_app,
    StepsPhi (initial_state heap env rho er) phi_fun
      (StDone heap_fun (Cls (env_fun, rho_fun, Lambda x eb))) ->
    find_R w rho = Some r ->
    StepsPhi
      (initial_state heap_fun env_fun (update_R (x, r) rho_fun) eb)
      phi_body
      (StDone heap_body v_body) ->
    StepsPhi (initial_state heap env rho Empty) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Rgn_App er w)) phi_app
      (StDone heap_app v_app) ->
    phi_fun ⋞ Theta_Empty ->
    phi_body ⋞ Theta_Empty ->
    phi_app ⋞ theta_summary.
Proof.
  intros heap env rho er w env_fun rho_fun x eb r
    phi_fun heap_fun phi_body heap_body v_body
    phi_summary heap_summary theta_summary
    phi_app heap_app v_app HFun HFind HBody HSummary HApp
    HFunSound HBodySound.
  destruct
    (StepsPhi_initial_empty_terminal
      heap env rho phi_summary heap_summary theta_summary HSummary)
    as [_ [_ HTheta]].
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_rgn_app_terminal_case
    heap env rho er w env_fun rho_fun x eb r
    phi_fun heap_fun phi_body heap_body v_body Theta_Empty
    phi_app heap_app v_app); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_direct_case :
  forall heap env rho er w
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary,
    StepsPhi (initial_state heap env rho (Rgn_App er w)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho Empty) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    (forall phi_fun heap_fun env_fun rho_fun x eb,
      StepsPhi (initial_state heap env rho er) phi_fun
        (StDone heap_fun (Cls (env_fun, rho_fun, Lambda x eb))) ->
      phi_fun ⋞ Theta_Empty) ->
    (forall env_fun rho_fun x eb r phi_body heap_start heap_body v_body,
      find_R w rho = Some r ->
      StepsPhi
        (initial_state heap_start env_fun (update_R (x, r) rho_fun) eb)
        phi_body
        (StDone heap_body v_body) ->
      phi_body ⋞ Theta_Empty) ->
    phi_app ⋞ theta_summary.
Proof.
  intros heap env rho er w
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    HApp HSummary HFunIH HBodyIH.
  destruct
    (StepsPhi_rgn_app_terminal_decompose
      heap env rho er w phi_app heap_app v_app HApp)
    as (env_fun & rho_fun & x & eb & r &
        phi_fun & heap_fun & phi_body &
        HFun & HFind & HBody & _).
  pose proof
    (HFunIH phi_fun heap_fun env_fun rho_fun x eb HFun) as HFunSound.
  pose proof
    (HBodyIH env_fun rho_fun x eb r phi_body heap_fun heap_app v_app
      HFind HBody) as HBodySound.
  eapply (Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_case
    heap env rho er w env_fun rho_fun x eb r
    phi_fun heap_fun phi_body heap_app v_app
    phi_summary heap_summary theta_summary
    phi_app heap_app v_app); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_quad_join_case :
  forall phi_pair phi1 phi2 phi3 phi4 theta1 theta2 theta3 theta4,
    phi_as_list phi_pair =
      phi_as_list phi1 ++ phi_as_list phi2 ++
      phi_as_list phi3 ++ phi_as_list phi4 ->
    phi1 ⋞ theta1 ->
    phi2 ⋞ theta2 ->
    phi3 ⋞ theta3 ->
    phi4 ⋞ theta4 ->
    phi_pair ⋞ Union_Theta (Union_Theta theta1 theta2)
      (Union_Theta theta3 theta4).
Proof.
  intros phi_pair phi1 phi2 phi3 phi4 theta1 theta2 theta3 theta4
    HList HSound1 HSound2 HSound3 HSound4.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with (phi2 := Phi_Seq (Phi_Seq phi1 phi2) (Phi_Seq phi3 phi4)).
  - simpl. rewrite HList. repeat rewrite app_assoc. reflexivity.
  - apply EnsembleUnionComp; now apply EnsembleUnionComp.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_composed_case :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1 theta_mu1
    phi_mu2 heap_mu2 v2 theta_mu2,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap_eff1 (Eff theta1)) ->
    StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap_eff2 (Eff theta2)) ->
    Step
      (StReturn heap_eff2 (Eff theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone))
      Silent
      (StEval heap_eff2 env rho (Mu_App ef1 ea1)
        (KPairParMu1 ef2 ea2 env rho KDone)) ->
    StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta_mu1 ->
    phi_mu2 ⋞ theta_mu2 ->
    exists phi_pair,
      StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
        phi_pair (StDone heap_mu2 (Pair (v1, v2))) /\
      phi_pair ⋞ Union_Theta (Union_Theta theta1 theta2)
        (Union_Theta theta_mu1 theta_mu2).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1 theta_mu1
    phi_mu2 heap_mu2 v2 theta_mu2
    HEff1 HEff2 HCheck HMu1 HMu2
    HEff1Sound HEff2Sound HMu1Sound HMu2Sound.
  destruct
    (StepsPhi_pair_par_from_components
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 heap_eff1 theta1
      phi_eff2 heap_eff2 theta2
      phi_mu1 heap_mu1 v1
      phi_mu2 heap_mu2 v2
      HEff1 HEff2 HCheck HMu1 HMu2)
    as (phi_pair & HPair & HList).
  exists phi_pair.
  split; [exact HPair |].
  eapply Correctness_soundness_ext_small_step_quad_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_pass_composed_case :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1 theta_mu1
    phi_mu2 heap_mu2 v2 theta_mu2,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap_eff1 (Eff theta1)) ->
    StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap_eff2 (Eff theta2)) ->
    Disjointness theta1 theta2 ->
    ~ Conflictness theta1 theta2 ->
    StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta_mu1 ->
    phi_mu2 ⋞ theta_mu2 ->
    exists phi_pair,
      StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
        phi_pair (StDone heap_mu2 (Pair (v1, v2))) /\
      phi_pair ⋞ Union_Theta (Union_Theta theta1 theta2)
        (Union_Theta theta_mu1 theta_mu2).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1 theta_mu1
    phi_mu2 heap_mu2 v2 theta_mu2
    HEff1 HEff2 HDisjoint HNoConflict HMu1 HMu2
    HEff1Sound HEff2Sound HMu1Sound HMu2Sound.
  eapply Correctness_soundness_ext_small_step_pair_par_composed_case; eauto.
  now apply Step_PairPar_EvalMu1.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_fallback_composed_case :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1 theta_mu1
    phi_mu2 heap_mu2 v2 theta_mu2,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap_eff1 (Eff theta1)) ->
    StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap_eff2 (Eff theta2)) ->
    ~ (Disjointness theta1 theta2 /\ ~ Conflictness theta1 theta2) ->
    StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta_mu1 ->
    phi_mu2 ⋞ theta_mu2 ->
    exists phi_pair,
      StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
        phi_pair (StDone heap_mu2 (Pair (v1, v2))) /\
      phi_pair ⋞ Union_Theta (Union_Theta theta1 theta2)
        (Union_Theta theta_mu1 theta_mu2).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1 theta_mu1
    phi_mu2 heap_mu2 v2 theta_mu2
    HEff1 HEff2 HFail HMu1 HMu2
    HEff1Sound HEff2Sound HMu1Sound HMu2Sound.
  eapply Correctness_soundness_ext_small_step_pair_par_composed_case; eauto.
  now apply Step_PairPar_FallbackMu1.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_checked_composed_case :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1 theta_mu1
    phi_mu2 heap_mu2 v2 theta_mu2,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap_eff1 (Eff theta1)) ->
    StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap_eff2 (Eff theta2)) ->
    StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta_mu1 ->
    phi_mu2 ⋞ theta_mu2 ->
    exists phi_pair,
      StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
        phi_pair (StDone heap_mu2 (Pair (v1, v2))) /\
      phi_pair ⋞ Union_Theta (Union_Theta theta1 theta2)
        (Union_Theta theta_mu1 theta_mu2).
Proof.
  intros HCheck heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1 theta_mu1
    phi_mu2 heap_mu2 v2 theta_mu2
    HEff1 HEff2 HMu1 HMu2
    HEff1Sound HEff2Sound HMu1Sound HMu2Sound.
  destruct (HCheck theta1 theta2) as [[HDisjoint HNoConflict] | HFail].
  - eapply Correctness_soundness_ext_small_step_pair_par_pass_composed_case;
      eauto.
  - eapply Correctness_soundness_ext_small_step_pair_par_fallback_composed_case;
      eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_pass_terminal_case :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1 theta_mu1
    phi_mu2 heap_mu2 v2 theta_mu2
    phi_pair heap_pair v_pair,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap_eff1 (Eff theta1)) ->
    StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap_eff2 (Eff theta2)) ->
    Disjointness theta1 theta2 ->
    ~ Conflictness theta1 theta2 ->
    StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta_mu1 ->
    phi_mu2 ⋞ theta_mu2 ->
    phi_pair ⋞ Union_Theta (Union_Theta theta1 theta2)
      (Union_Theta theta_mu1 theta_mu2).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1 theta_mu1
    phi_mu2 heap_mu2 v2 theta_mu2
    phi_pair heap_pair v_pair
    HEff1 HEff2 HDisjoint HNoConflict HMu1 HMu2 HPair
    HEff1Sound HEff2Sound HMu1Sound HMu2Sound.
  destruct
    (Correctness_soundness_ext_small_step_pair_par_pass_composed_case
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 heap_eff1 theta1
      phi_eff2 heap_eff2 theta2
      phi_mu1 heap_mu1 v1 theta_mu1
      phi_mu2 heap_mu2 v2 theta_mu2
      HEff1 HEff2 HDisjoint HNoConflict HMu1 HMu2
      HEff1Sound HEff2Sound HMu1Sound HMu2Sound)
    as (phi_pair_sound & HPairSoundSteps & HPairSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_fallback_terminal_case :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1 theta_mu1
    phi_mu2 heap_mu2 v2 theta_mu2
    phi_pair heap_pair v_pair,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap_eff1 (Eff theta1)) ->
    StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap_eff2 (Eff theta2)) ->
    ~ (Disjointness theta1 theta2 /\ ~ Conflictness theta1 theta2) ->
    StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta_mu1 ->
    phi_mu2 ⋞ theta_mu2 ->
    phi_pair ⋞ Union_Theta (Union_Theta theta1 theta2)
      (Union_Theta theta_mu1 theta_mu2).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1 theta_mu1
    phi_mu2 heap_mu2 v2 theta_mu2
    phi_pair heap_pair v_pair
    HEff1 HEff2 HFail HMu1 HMu2 HPair
    HEff1Sound HEff2Sound HMu1Sound HMu2Sound.
  destruct
    (Correctness_soundness_ext_small_step_pair_par_fallback_composed_case
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 heap_eff1 theta1
      phi_eff2 heap_eff2 theta2
      phi_mu1 heap_mu1 v1 theta_mu1
      phi_mu2 heap_mu2 v2 theta_mu2
      HEff1 HEff2 HFail HMu1 HMu2
      HEff1Sound HEff2Sound HMu1Sound HMu2Sound)
    as (phi_pair_sound & HPairSoundSteps & HPairSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_checked_terminal_case :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1 theta_mu1
    phi_mu2 heap_mu2 v2 theta_mu2
    phi_pair heap_pair v_pair,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap_eff1 (Eff theta1)) ->
    StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap_eff2 (Eff theta2)) ->
    StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta_mu1 ->
    phi_mu2 ⋞ theta_mu2 ->
    phi_pair ⋞ Union_Theta (Union_Theta theta1 theta2)
      (Union_Theta theta_mu1 theta_mu2).
Proof.
  intros HCheck heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1 theta_mu1
    phi_mu2 heap_mu2 v2 theta_mu2
    phi_pair heap_pair v_pair
    HEff1 HEff2 HMu1 HMu2 HPair
    HEff1Sound HEff2Sound HMu1Sound HMu2Sound.
  destruct (HCheck theta1 theta2) as [[HDisjoint HNoConflict] | HFail].
  - eapply Correctness_soundness_ext_small_step_pair_par_pass_terminal_case;
      eauto.
  - eapply Correctness_soundness_ext_small_step_pair_par_fallback_terminal_case;
      eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_same_summary_join_case :
  forall phi_pair phi_eff1 phi_eff2 phi_mu1 phi_mu2 theta1 theta2,
    phi_as_list phi_pair =
      phi_as_list phi_eff1 ++ phi_as_list phi_eff2 ++
      phi_as_list phi_mu1 ++ phi_as_list phi_mu2 ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta1 ->
    phi_mu2 ⋞ theta2 ->
    phi_pair ⋞ Union_Theta theta1 theta2.
Proof.
  intros phi_pair phi_eff1 phi_eff2 phi_mu1 phi_mu2 theta1 theta2
    HList HEff1Sound HEff2Sound HMu1Sound HMu2Sound.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with (phi2 := Phi_Seq (Phi_Seq phi_eff1 phi_eff2)
      (Phi_Seq phi_mu1 phi_mu2)).
  - simpl. rewrite HList. repeat rewrite app_assoc. reflexivity.
  - apply PTS_Seq; now apply EnsembleUnionComp.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_same_summary_composed_case :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap_eff1 (Eff theta1)) ->
    StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap_eff2 (Eff theta2)) ->
    Step
      (StReturn heap_eff2 (Eff theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 KDone))
      Silent
      (StEval heap_eff2 env rho (Mu_App ef1 ea1)
        (KPairParMu1 ef2 ea2 env rho KDone)) ->
    StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta1 ->
    phi_mu2 ⋞ theta2 ->
    exists phi_pair,
      StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
        phi_pair (StDone heap_mu2 (Pair (v1, v2))) /\
      phi_pair ⋞ Union_Theta theta1 theta2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2
    HEff1 HEff2 HCheck HMu1 HMu2
    HEff1Sound HEff2Sound HMu1Sound HMu2Sound.
  destruct
    (StepsPhi_pair_par_from_components
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 heap_eff1 theta1
      phi_eff2 heap_eff2 theta2
      phi_mu1 heap_mu1 v1
      phi_mu2 heap_mu2 v2
      HEff1 HEff2 HCheck HMu1 HMu2)
    as (phi_pair & HPair & HList).
  exists phi_pair.
  split; [exact HPair |].
  eapply Correctness_soundness_ext_small_step_pair_par_same_summary_join_case;
    eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_same_summary_pass_terminal_case :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2
    phi_pair heap_pair v_pair,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap_eff1 (Eff theta1)) ->
    StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap_eff2 (Eff theta2)) ->
    Disjointness theta1 theta2 ->
    ~ Conflictness theta1 theta2 ->
    StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta1 ->
    phi_mu2 ⋞ theta2 ->
    phi_pair ⋞ Union_Theta theta1 theta2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2
    phi_pair heap_pair v_pair
    HEff1 HEff2 HDisjoint HNoConflict HMu1 HMu2 HPair
    HEff1Sound HEff2Sound HMu1Sound HMu2Sound.
  destruct
    (Correctness_soundness_ext_small_step_pair_par_same_summary_composed_case
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 heap_eff1 theta1
      phi_eff2 heap_eff2 theta2
      phi_mu1 heap_mu1 v1
      phi_mu2 heap_mu2 v2
      HEff1 HEff2
      (Step_PairPar_EvalMu1
        heap_eff2 env rho KDone ef1 ea1 ef2 ea2 theta1 theta2
        HDisjoint HNoConflict)
      HMu1 HMu2 HEff1Sound HEff2Sound HMu1Sound HMu2Sound)
    as (phi_pair_sound & HPairSoundSteps & HPairSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_same_summary_fallback_terminal_case :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2
    phi_pair heap_pair v_pair,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap_eff1 (Eff theta1)) ->
    StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap_eff2 (Eff theta2)) ->
    ~ (Disjointness theta1 theta2 /\ ~ Conflictness theta1 theta2) ->
    StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta1 ->
    phi_mu2 ⋞ theta2 ->
    phi_pair ⋞ Union_Theta theta1 theta2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2
    phi_pair heap_pair v_pair
    HEff1 HEff2 HFail HMu1 HMu2 HPair
    HEff1Sound HEff2Sound HMu1Sound HMu2Sound.
  destruct
    (Correctness_soundness_ext_small_step_pair_par_same_summary_composed_case
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 heap_eff1 theta1
      phi_eff2 heap_eff2 theta2
      phi_mu1 heap_mu1 v1
      phi_mu2 heap_mu2 v2
      HEff1 HEff2
      (Step_PairPar_FallbackMu1
        heap_eff2 env rho KDone ef1 ea1 ef2 ea2 theta1 theta2
        HFail)
      HMu1 HMu2 HEff1Sound HEff2Sound HMu1Sound HMu2Sound)
    as (phi_pair_sound & HPairSoundSteps & HPairSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_same_summary_checked_terminal_case :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2
    phi_pair heap_pair v_pair,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap_eff1 (Eff theta1)) ->
    StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap_eff2 (Eff theta2)) ->
    StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta1 ->
    phi_mu2 ⋞ theta2 ->
    phi_pair ⋞ Union_Theta theta1 theta2.
Proof.
  intros HCheck heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2
    phi_pair heap_pair v_pair
    HEff1 HEff2 HMu1 HMu2 HPair
    HEff1Sound HEff2Sound HMu1Sound HMu2Sound.
  destruct (HCheck theta1 theta2) as [[HDisjoint HNoConflict] | HFail].
  - eapply
      Correctness_soundness_ext_small_step_pair_par_same_summary_pass_terminal_case;
      eauto.
  - eapply
      Correctness_soundness_ext_small_step_pair_par_same_summary_fallback_terminal_case;
      eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_same_summary_readonly_terminal_case :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2
    phi_pair heap_pair v_pair,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap_eff1 (Eff theta1)) ->
    StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap_eff2 (Eff theta2)) ->
    ReadOnlyPhi phi_eff1 ->
    ReadOnlyPhi phi_eff2 ->
    StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta1 ->
    phi_mu2 ⋞ theta2 ->
    phi_pair ⋞ Union_Theta theta1 theta2.
Proof.
  intros HCheck heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2
    phi_pair heap_pair v_pair
    HEff1 HEff2 HReadOnly1 HReadOnly2 HMu1 HMu2 HPair
    HEff1Sound HEff2Sound HMu1Sound HMu2Sound.
  pose proof
    (pairpar_effect_summary_steps_phi_heap_neutral
      heap env rho ef1 ea1 phi_eff1 heap_eff1 theta1
      HEff1 HReadOnly1) as HHeap1.
  pose proof
    (pairpar_effect_summary_steps_phi_heap_neutral
      heap_eff1 env rho ef2 ea2 phi_eff2 heap_eff2 theta2
      HEff2 HReadOnly2) as HHeap2.
  subst heap_eff2.
  subst heap_eff1.
  eapply Correctness_soundness_ext_small_step_pair_par_same_summary_checked_terminal_case;
    eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_same_summary_sequential_readonly_terminal_case :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2
    phi_pair heap_pair v_pair,
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyPhi phi_eff1 ->
    ReadOnlyPhi phi_eff2 ->
    StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta1 ->
    phi_mu2 ⋞ theta2 ->
    phi_pair ⋞ Union_Theta theta1 theta2.
Proof.
  intros HCheck heap env rho ef1 ea1 ef2 ea2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2
    phi_pair heap_pair v_pair
    HSummary HReadOnly1 HReadOnly2 HMu1 HMu2 HPair
    HEff1Sound HEff2Sound HMu1Sound HMu2Sound.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HEff1 HEff2]; subst.
  eapply
    Correctness_soundness_ext_small_step_pair_par_same_summary_readonly_terminal_case;
    eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_same_summary_static_readonly_terminal_case :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 static_eff1 static_eff2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2
    phi_pair heap_pair v_pair,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap_eff1 (Eff theta1)) ->
    StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap_eff2 (Eff theta2)) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    Epsilon_Phi_Soundness (fold_subst_eps rho static_eff1, phi_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    Epsilon_Phi_Soundness (fold_subst_eps rho static_eff2, phi_eff2) ->
    StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta1 ->
    phi_mu2 ⋞ theta2 ->
    phi_pair ⋞ Union_Theta theta1 theta2.
Proof.
  intros HCheck heap env rho ef1 ea1 ef2 ea2 static_eff1 static_eff2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2
    phi_pair heap_pair v_pair
    HEff1 HEff2 HReadOnlyStatic1 HEpsilon1 HReadOnlyStatic2 HEpsilon2
    HMu1 HMu2 HPair HEff1Sound HEff2Sound HMu1Sound HMu2Sound.
  pose proof
    (effect_summary_trace_readonly_from_static_soundness
      rho static_eff1 phi_eff1 HReadOnlyStatic1 HEpsilon1)
    as HReadOnly1.
  pose proof
    (effect_summary_trace_readonly_from_static_soundness
      rho static_eff2 phi_eff2 HReadOnlyStatic2 HEpsilon2)
    as HReadOnly2.
  eapply
    Correctness_soundness_ext_small_step_pair_par_same_summary_readonly_terminal_case;
    eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_same_summary_typed_readonly_terminal_case :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    static_eff1 static_eff2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2
    phi_pair heap_pair v_pair,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, Ty_Effect, static_eff2) ->
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta1 ->
    phi_mu2 ⋞ theta2 ->
    phi_pair ⋞ Union_Theta theta1 theta2.
Proof.
  intros HCheck heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    static_eff1 static_eff2
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1
    phi_mu2 heap_mu2 v2
    phi_pair heap_pair v_pair
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEff1 HTcEff2 HSummary HReadOnlyStatic1 HReadOnlyStatic2
    HMu1 HMu2 HPair HEff1Sound HEff2Sound HMu1Sound HMu2Sound.
  destruct
    (PairParSequentialEffectSummaryStepsPhi_readonly_from_small_step_sound
      heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
      static_eff1 static_eff2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEff1 HTcEff2 HSummary HReadOnlyStatic1 HReadOnlyStatic2)
    as [HReadOnly1 HReadOnly2].
  eapply
    Correctness_soundness_ext_small_step_pair_par_same_summary_sequential_readonly_terminal_case;
    eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_cond_join_case :
  forall phi_cond phi_guard phi_branch theta,
    phi_as_list phi_cond =
      phi_as_list phi_guard ++ phi_as_list phi_branch ->
    phi_guard ⋞ Theta_Empty ->
    phi_branch ⋞ theta ->
    phi_cond ⋞ theta.
Proof.
  intros phi_cond phi_guard phi_branch theta HList HGuardSound HBranchSound.
  eapply Phi_Theta_Soundness_of_phi_as_list_app; eauto.
  eapply EmptyInAnyTheta; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_cond_true_composed_case :
  forall heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch v theta,
    StepsPhi (initial_state heap env rho e) phi_guard
      (StDone heap_guard (Bit true)) ->
    StepsPhi (initial_state heap_guard env rho et) phi_branch
      (StDone heap_branch v) ->
    phi_guard ⋞ Theta_Empty ->
    phi_branch ⋞ theta ->
    exists phi_cond,
      StepsPhi (initial_state heap env rho (Cond e et ef)) phi_cond
        (StDone heap_branch v) /\
      phi_cond ⋞ theta.
Proof.
  intros heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch v theta
    HGuard HBranch HGuardSound HBranchSound.
  destruct
    (StepsPhi_cond_true_from_guard_branch
      heap env rho e et ef
      phi_guard heap_guard phi_branch heap_branch v HGuard HBranch)
    as (phi_cond & HCond & HList).
  exists phi_cond.
  split; [exact HCond |].
  eapply Correctness_soundness_ext_small_step_cond_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_cond_true_terminal_case :
  forall heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch v theta
    phi_cond heap_cond v_cond,
    StepsPhi (initial_state heap env rho e) phi_guard
      (StDone heap_guard (Bit true)) ->
    StepsPhi (initial_state heap_guard env rho et) phi_branch
      (StDone heap_branch v) ->
    StepsPhi (initial_state heap env rho (Cond e et ef)) phi_cond
      (StDone heap_cond v_cond) ->
    phi_guard ⋞ Theta_Empty ->
    phi_branch ⋞ theta ->
    phi_cond ⋞ theta.
Proof.
  intros heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch v theta
    phi_cond heap_cond v_cond
    HGuard HBranch HCond HGuardSound HBranchSound.
  destruct
    (Correctness_soundness_ext_small_step_cond_true_composed_case
      heap env rho e et ef
      phi_guard heap_guard phi_branch heap_branch v theta
      HGuard HBranch HGuardSound HBranchSound)
    as (phi_cond_sound & HCondSoundSteps & HCondSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_cond_false_composed_case :
  forall heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch v theta,
    StepsPhi (initial_state heap env rho e) phi_guard
      (StDone heap_guard (Bit false)) ->
    StepsPhi (initial_state heap_guard env rho ef) phi_branch
      (StDone heap_branch v) ->
    phi_guard ⋞ Theta_Empty ->
    phi_branch ⋞ theta ->
    exists phi_cond,
      StepsPhi (initial_state heap env rho (Cond e et ef)) phi_cond
        (StDone heap_branch v) /\
      phi_cond ⋞ theta.
Proof.
  intros heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch v theta
    HGuard HBranch HGuardSound HBranchSound.
  destruct
    (StepsPhi_cond_false_from_guard_branch
      heap env rho e et ef
      phi_guard heap_guard phi_branch heap_branch v HGuard HBranch)
    as (phi_cond & HCond & HList).
  exists phi_cond.
  split; [exact HCond |].
  eapply Correctness_soundness_ext_small_step_cond_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_cond_false_terminal_case :
  forall heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch v theta
    phi_cond heap_cond v_cond,
    StepsPhi (initial_state heap env rho e) phi_guard
      (StDone heap_guard (Bit false)) ->
    StepsPhi (initial_state heap_guard env rho ef) phi_branch
      (StDone heap_branch v) ->
    StepsPhi (initial_state heap env rho (Cond e et ef)) phi_cond
      (StDone heap_cond v_cond) ->
    phi_guard ⋞ Theta_Empty ->
    phi_branch ⋞ theta ->
    phi_cond ⋞ theta.
Proof.
  intros heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch v theta
    phi_cond heap_cond v_cond
    HGuard HBranch HCond HGuardSound HBranchSound.
  destruct
    (Correctness_soundness_ext_small_step_cond_false_composed_case
      heap env rho e et ef
      phi_guard heap_guard phi_branch heap_branch v theta
      HGuard HBranch HGuardSound HBranchSound)
    as (phi_cond_sound & HCondSoundSteps & HCondSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Lemma StepsPhi_cond_true_summary_terminal_theta :
  forall heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch theta_branch
    phi_summary heap_summary theta_summary,
    StepsPhi (initial_state heap env rho e) phi_guard
      (StDone heap_guard (Bit true)) ->
    StepsPhi (initial_state heap_guard env rho et) phi_branch
      (StDone heap_branch (Eff theta_branch)) ->
    StepsPhi (initial_state heap env rho (Cond e et ef)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    theta_summary = theta_branch.
Proof.
  intros heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch theta_branch
    phi_summary heap_summary theta_summary HGuard HBranch HSummary.
  destruct
    (StepsPhi_cond_true_from_guard_branch
      heap env rho e et ef
      phi_guard heap_guard phi_branch heap_branch (Eff theta_branch)
      HGuard HBranch)
    as (phi_summary_sound & HSummarySound & _).
  destruct
    (StepsPhi_effect_terminal_deterministic
      (initial_state heap env rho (Cond e et ef))
      phi_summary_sound heap_branch theta_branch
      phi_summary heap_summary theta_summary
      HSummarySound HSummary)
    as [_ [_ HTheta]].
  now symmetry.
Qed.

Lemma StepsPhi_cond_false_summary_terminal_theta :
  forall heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch theta_branch
    phi_summary heap_summary theta_summary,
    StepsPhi (initial_state heap env rho e) phi_guard
      (StDone heap_guard (Bit false)) ->
    StepsPhi (initial_state heap_guard env rho ef) phi_branch
      (StDone heap_branch (Eff theta_branch)) ->
    StepsPhi (initial_state heap env rho (Cond e et ef)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    theta_summary = theta_branch.
Proof.
  intros heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch theta_branch
    phi_summary heap_summary theta_summary HGuard HBranch HSummary.
  destruct
    (StepsPhi_cond_false_from_guard_branch
      heap env rho e et ef
      phi_guard heap_guard phi_branch heap_branch (Eff theta_branch)
      HGuard HBranch)
    as (phi_summary_sound & HSummarySound & _).
  destruct
    (StepsPhi_effect_terminal_deterministic
      (initial_state heap env rho (Cond e et ef))
      phi_summary_sound heap_branch theta_branch
      phi_summary heap_summary theta_summary
      HSummarySound HSummary)
    as [_ [_ HTheta]].
  now symmetry.
Qed.

Theorem Correctness_soundness_ext_small_step_cond_true_summary_terminal_case :
  forall heap env rho e et ef efft efff
    phi_guard heap_guard phi_branch heap_branch v
    phi_branch_summary heap_branch_summary theta_branch
    phi_summary heap_summary theta_summary
    phi_cond heap_cond v_cond,
    StepsPhi (initial_state heap env rho e) phi_guard
      (StDone heap_guard (Bit true)) ->
    StepsPhi (initial_state heap_guard env rho et) phi_branch
      (StDone heap_branch v) ->
    StepsPhi (initial_state heap_guard env rho efft) phi_branch_summary
      (StDone heap_branch_summary (Eff theta_branch)) ->
    StepsPhi (initial_state heap env rho (Cond e efft efff)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Cond e et ef)) phi_cond
      (StDone heap_cond v_cond) ->
    phi_guard ⋞ Theta_Empty ->
    phi_branch ⋞ theta_branch ->
    phi_cond ⋞ theta_summary.
Proof.
  intros heap env rho e et ef efft efff
    phi_guard heap_guard phi_branch heap_branch v
    phi_branch_summary heap_branch_summary theta_branch
    phi_summary heap_summary theta_summary
    phi_cond heap_cond v_cond
    HGuard HBranch HBranchSummary HSummary HCond
    HGuardSound HBranchSound.
  pose proof
    (StepsPhi_cond_true_summary_terminal_theta
      heap env rho e efft efff
      phi_guard heap_guard
      phi_branch_summary heap_branch_summary theta_branch
      phi_summary heap_summary theta_summary
      HGuard HBranchSummary HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_cond_true_terminal_case
    heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch v theta_branch
    phi_cond heap_cond v_cond); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_cond_false_summary_terminal_case :
  forall heap env rho e et ef efft efff
    phi_guard heap_guard phi_branch heap_branch v
    phi_branch_summary heap_branch_summary theta_branch
    phi_summary heap_summary theta_summary
    phi_cond heap_cond v_cond,
    StepsPhi (initial_state heap env rho e) phi_guard
      (StDone heap_guard (Bit false)) ->
    StepsPhi (initial_state heap_guard env rho ef) phi_branch
      (StDone heap_branch v) ->
    StepsPhi (initial_state heap_guard env rho efff) phi_branch_summary
      (StDone heap_branch_summary (Eff theta_branch)) ->
    StepsPhi (initial_state heap env rho (Cond e efft efff)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Cond e et ef)) phi_cond
      (StDone heap_cond v_cond) ->
    phi_guard ⋞ Theta_Empty ->
    phi_branch ⋞ theta_branch ->
    phi_cond ⋞ theta_summary.
Proof.
  intros heap env rho e et ef efft efff
    phi_guard heap_guard phi_branch heap_branch v
    phi_branch_summary heap_branch_summary theta_branch
    phi_summary heap_summary theta_summary
    phi_cond heap_cond v_cond
    HGuard HBranch HBranchSummary HSummary HCond
    HGuardSound HBranchSound.
  pose proof
    (StepsPhi_cond_false_summary_terminal_theta
      heap env rho e efft efff
      phi_guard heap_guard
      phi_branch_summary heap_branch_summary theta_branch
      phi_summary heap_summary theta_summary
      HGuard HBranchSummary HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_cond_false_terminal_case
    heap env rho e et ef
    phi_guard heap_guard phi_branch heap_branch v theta_branch
    phi_cond heap_cond v_cond); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_cond_summary_terminal_direct_case :
  forall heap env rho e et ef efft efff
    phi_cond heap_cond v_cond
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e static_e,
    StepsPhi (initial_state heap env rho (Cond e et ef)) phi_cond
      (StDone heap_cond v_cond) ->
    StepsPhi (initial_state heap env rho (Cond e efft efff)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    ReadOnlyStatic (fold_subst_eps rho static_e) ->
    ReadOnlyPhi phi_summary ->
    (forall phi_guard heap_guard b,
      StepsPhi (initial_state heap env rho e) phi_guard
        (StDone heap_guard (Bit b)) ->
      phi_guard ⋞ Theta_Empty) ->
    (forall phi_branch heap_branch v
            phi_branch_summary heap_branch_summary theta_branch,
      StepsPhi (initial_state heap env rho et) phi_branch
        (StDone heap_branch v) ->
      StepsPhi (initial_state heap env rho efft) phi_branch_summary
        (StDone heap_branch_summary (Eff theta_branch)) ->
      ReadOnlyPhi phi_branch_summary ->
      phi_branch ⋞ theta_branch) ->
    (forall phi_branch heap_branch v
            phi_branch_summary heap_branch_summary theta_branch,
      StepsPhi (initial_state heap env rho ef) phi_branch
        (StDone heap_branch v) ->
      StepsPhi (initial_state heap env rho efff) phi_branch_summary
        (StDone heap_branch_summary (Eff theta_branch)) ->
      ReadOnlyPhi phi_branch_summary ->
      phi_branch ⋞ theta_branch) ->
    phi_cond ⋞ theta_summary.
Proof.
  intros heap env rho e et ef efft efff
    phi_cond heap_cond v_cond
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e static_e
    HCond HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcGuard HReadOnlyStaticGuard HReadOnlySummary
    HGuardIH HTrueIH HFalseIH.
  destruct
    (StepsPhi_cond_terminal_decompose
      heap env rho e et ef phi_cond heap_cond v_cond HCond)
    as
      [(phi_guard & heap_guard & phi_branch & heap_branch &
        HGuard & HBranch & _ & _) |
       (phi_guard & heap_guard & phi_branch & heap_branch &
        HGuard & HBranch & _ & _)].
  - destruct
      (StepsPhi_cond_terminal_decompose
        heap env rho e efft efff phi_summary heap_summary
        (Eff theta_summary) HSummary)
      as
        [(phi_guard_summary & heap_guard_summary &
          phi_branch_summary & heap_branch_summary &
          HGuardSummary & HBranchSummary & _ & HTraceSummary) |
         (phi_guard_summary & heap_guard_summary &
          phi_branch_summary & heap_branch_summary &
          HGuardSummary & HBranchSummary & _ & HTraceSummary)].
    + pose proof
        (ReadOnlyPhi_app_list_left
          phi_summary phi_guard_summary phi_branch_summary
          HReadOnlySummary HTraceSummary) as HReadOnlyGuardSummary.
      pose proof
        (ReadOnlyPhi_app_list_right
          phi_summary phi_guard_summary phi_branch_summary
          HReadOnlySummary HTraceSummary) as HReadOnlyBranchSummary.
      pose proof
        (StepsPhi_typed_readonly_static_preserves_heap
          heap env rho e stty ctxt rgns ty_e static_e
          phi_guard heap_guard (Bit true)
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcGuard
          HGuard HReadOnlyStaticGuard) as HHeapGuard.
      pose proof
        (StepsPhi_readonly_preserves_heap
          (initial_state heap env rho e) phi_guard_summary
          (StDone heap_guard_summary (Bit true))
          HGuardSummary HReadOnlyGuardSummary) as HHeapGuardSummary.
      simpl in HHeapGuardSummary.
      subst heap_guard.
      symmetry in HHeapGuardSummary.
      subst heap_guard_summary.
      pose proof (HGuardIH phi_guard heap true HGuard) as HGuardSound.
      pose proof
        (HTrueIH
          phi_branch heap_branch v_cond
          phi_branch_summary heap_branch_summary theta_summary
          HBranch HBranchSummary HReadOnlyBranchSummary) as HBranchSound.
      eapply (Correctness_soundness_ext_small_step_cond_true_terminal_case
        heap env rho e et ef
        phi_guard heap phi_branch heap_branch v_cond theta_summary
        phi_cond heap_cond v_cond); eauto.
    + destruct
        (StepsPhi_terminal_deterministic
          (initial_state heap env rho e)
          phi_guard heap_guard (Bit true)
          phi_guard_summary heap_guard_summary (Bit false)
          HGuard HGuardSummary)
        as [_ [_ HValue]].
      inversion HValue.
  - destruct
      (StepsPhi_cond_terminal_decompose
        heap env rho e efft efff phi_summary heap_summary
        (Eff theta_summary) HSummary)
      as
        [(phi_guard_summary & heap_guard_summary &
          phi_branch_summary & heap_branch_summary &
          HGuardSummary & HBranchSummary & _ & HTraceSummary) |
         (phi_guard_summary & heap_guard_summary &
          phi_branch_summary & heap_branch_summary &
          HGuardSummary & HBranchSummary & _ & HTraceSummary)].
    + destruct
        (StepsPhi_terminal_deterministic
          (initial_state heap env rho e)
          phi_guard heap_guard (Bit false)
          phi_guard_summary heap_guard_summary (Bit true)
          HGuard HGuardSummary)
        as [_ [_ HValue]].
      inversion HValue.
    + pose proof
        (ReadOnlyPhi_app_list_left
          phi_summary phi_guard_summary phi_branch_summary
          HReadOnlySummary HTraceSummary) as HReadOnlyGuardSummary.
      pose proof
        (ReadOnlyPhi_app_list_right
          phi_summary phi_guard_summary phi_branch_summary
          HReadOnlySummary HTraceSummary) as HReadOnlyBranchSummary.
      pose proof
        (StepsPhi_typed_readonly_static_preserves_heap
          heap env rho e stty ctxt rgns ty_e static_e
          phi_guard heap_guard (Bit false)
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcGuard
          HGuard HReadOnlyStaticGuard) as HHeapGuard.
      pose proof
        (StepsPhi_readonly_preserves_heap
          (initial_state heap env rho e) phi_guard_summary
          (StDone heap_guard_summary (Bit false))
          HGuardSummary HReadOnlyGuardSummary) as HHeapGuardSummary.
      simpl in HHeapGuardSummary.
      subst heap_guard.
      symmetry in HHeapGuardSummary.
      subst heap_guard_summary.
      pose proof (HGuardIH phi_guard heap false HGuard) as HGuardSound.
      pose proof
        (HFalseIH
          phi_branch heap_branch v_cond
          phi_branch_summary heap_branch_summary theta_summary
          HBranch HBranchSummary HReadOnlyBranchSummary) as HBranchSound.
      eapply (Correctness_soundness_ext_small_step_cond_false_terminal_case
        heap env rho e et ef
        phi_guard heap phi_branch heap_branch v_cond theta_summary
        phi_cond heap_cond v_cond); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_binary_join_case :
  forall phi_bin phi_left phi_right theta,
    phi_as_list phi_bin =
      phi_as_list phi_left ++ phi_as_list phi_right ->
    phi_left ⋞ theta ->
    phi_right ⋞ theta ->
    phi_bin ⋞ theta.
Proof.
  intros phi_bin phi_left phi_right theta HList HLeftSound HRightSound.
  eapply Phi_Theta_Soundness_of_phi_as_list_app; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_binary_union_join_case :
  forall phi_bin phi_left phi_right theta1 theta2,
    phi_as_list phi_bin =
      phi_as_list phi_left ++ phi_as_list phi_right ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    phi_bin ⋞ Union_Theta theta1 theta2.
Proof.
  intros phi_bin phi_left phi_right theta1 theta2
    HList HLeftSound HRightSound.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with (phi2 := Phi_Seq phi_left phi_right).
  - simpl. exact HList.
  - now apply EnsembleUnionComp.
Qed.

Theorem Correctness_soundness_ext_small_step_concat_join_case :
  forall phi_concat phi_left phi_right theta1 theta2,
    phi_as_list phi_concat =
      phi_as_list phi_left ++ phi_as_list phi_right ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    phi_concat ⋞ Union_Theta theta1 theta2.
Proof.
  intros phi_concat phi_left phi_right theta1 theta2
    HList HLeftSound HRightSound.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with (phi2 := Phi_Seq phi_left phi_right).
  - simpl. exact HList.
  - now apply EnsembleUnionComp.
Qed.

Theorem Correctness_soundness_ext_small_step_concat_composed_case :
  forall heap env rho e1 e2
    phi_left heap_left theta1 phi_right heap_right theta2,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Eff theta1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Eff theta2)) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    exists phi_concat,
      StepsPhi (initial_state heap env rho (Concat e1 e2)) phi_concat
        (StDone heap_right (Eff (Union_Theta theta1 theta2))) /\
      phi_concat ⋞ Union_Theta theta1 theta2.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left theta1 phi_right heap_right theta2
    HLeft HRight HLeftSound HRightSound.
  destruct
    (StepsPhi_concat_from_left_right
      heap env rho e1 e2
      phi_left heap_left theta1 phi_right heap_right theta2 HLeft HRight)
    as (phi_concat & HConcat & HList).
  exists phi_concat.
  split; [exact HConcat |].
  eapply Correctness_soundness_ext_small_step_concat_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_concat_terminal_case :
  forall heap env rho e1 e2
    phi_left heap_left theta1 phi_right heap_right theta2
    phi_concat heap_concat v_concat,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Eff theta1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Eff theta2)) ->
    StepsPhi (initial_state heap env rho (Concat e1 e2)) phi_concat
      (StDone heap_concat v_concat) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    phi_concat ⋞ Union_Theta theta1 theta2.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left theta1 phi_right heap_right theta2
    phi_concat heap_concat v_concat HLeft HRight HConcat HLeftSound HRightSound.
  destruct
    (Correctness_soundness_ext_small_step_concat_composed_case
      heap env rho e1 e2
      phi_left heap_left theta1 phi_right heap_right theta2
      HLeft HRight HLeftSound HRightSound)
    as (phi_concat_sound & HConcatSoundSteps & HConcatSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Lemma StepsPhi_concat_summary_terminal_theta :
  forall heap env rho e1 e2
    phi_left heap_left theta1 phi_right heap_right theta2
    phi_summary heap_summary theta_summary,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Eff theta1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Eff theta2)) ->
    StepsPhi (initial_state heap env rho (Concat e1 e2)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    theta_summary = Union_Theta theta1 theta2.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left theta1 phi_right heap_right theta2
    phi_summary heap_summary theta_summary HLeft HRight HSummary.
  destruct
    (StepsPhi_concat_from_left_right
      heap env rho e1 e2
      phi_left heap_left theta1 phi_right heap_right theta2 HLeft HRight)
    as (phi_summary_sound & HSummarySound & _).
  destruct
    (StepsPhi_effect_terminal_deterministic
      (initial_state heap env rho (Concat e1 e2))
      phi_summary_sound heap_right (Union_Theta theta1 theta2)
      phi_summary heap_summary theta_summary
      HSummarySound HSummary)
    as [_ [_ HTheta]].
  now symmetry.
Qed.

Lemma StepsPhi_nested_concat_summary_terminal_theta :
  forall heap env rho e1 e2 e3 e4
    phi1 heap1 theta1 phi2 heap2 theta2
    phi3 heap3 theta3 phi4 heap4 theta4
    phi_summary heap_summary theta_summary,
    StepsPhi (initial_state heap env rho e1) phi1
      (StDone heap1 (Eff theta1)) ->
    StepsPhi (initial_state heap1 env rho e2) phi2
      (StDone heap2 (Eff theta2)) ->
    StepsPhi (initial_state heap2 env rho e3) phi3
      (StDone heap3 (Eff theta3)) ->
    StepsPhi (initial_state heap3 env rho e4) phi4
      (StDone heap4 (Eff theta4)) ->
    StepsPhi
      (initial_state heap env rho (Concat (Concat e1 e2) (Concat e3 e4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    theta_summary =
      Union_Theta (Union_Theta theta1 theta2)
        (Union_Theta theta3 theta4).
Proof.
  intros heap env rho e1 e2 e3 e4
    phi1 heap1 theta1 phi2 heap2 theta2
    phi3 heap3 theta3 phi4 heap4 theta4
    phi_summary heap_summary theta_summary
    H1 H2 H3 H4 HSummary.
  destruct
    (StepsPhi_concat_from_left_right
      heap env rho e1 e2
      phi1 heap1 theta1 phi2 heap2 theta2 H1 H2)
    as (phi12 & H12 & _).
  destruct
    (StepsPhi_concat_from_left_right
      heap2 env rho e3 e4
      phi3 heap3 theta3 phi4 heap4 theta4 H3 H4)
    as (phi34 & H34 & _).
  destruct
    (StepsPhi_concat_from_left_right
      heap env rho (Concat e1 e2) (Concat e3 e4)
      phi12 heap2 (Union_Theta theta1 theta2)
      phi34 heap4 (Union_Theta theta3 theta4)
      H12 H34)
    as (phi_summary_sound & HSummarySound & _).
  destruct
    (StepsPhi_effect_terminal_deterministic
      (initial_state heap env rho
        (Concat (Concat e1 e2) (Concat e3 e4)))
      phi_summary_sound heap4
      (Union_Theta (Union_Theta theta1 theta2)
        (Union_Theta theta3 theta4))
      phi_summary heap_summary theta_summary
      HSummarySound HSummary)
    as [_ [_ HTheta]].
  now symmetry.
Qed.

Lemma StepsPhi_right_nested_concat_summary_terminal_theta :
  forall heap env rho e1 e2 e3
    phi1 heap1 theta1 phi2 heap2 theta2 phi3 heap3 theta3
    phi_summary heap_summary theta_summary,
    StepsPhi (initial_state heap env rho e1) phi1
      (StDone heap1 (Eff theta1)) ->
    StepsPhi (initial_state heap1 env rho e2) phi2
      (StDone heap2 (Eff theta2)) ->
    StepsPhi (initial_state heap2 env rho e3) phi3
      (StDone heap3 (Eff theta3)) ->
    StepsPhi (initial_state heap env rho (Concat e1 (Concat e2 e3)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    theta_summary = Union_Theta theta1 (Union_Theta theta2 theta3).
Proof.
  intros heap env rho e1 e2 e3
    phi1 heap1 theta1 phi2 heap2 theta2 phi3 heap3 theta3
    phi_summary heap_summary theta_summary H1 H2 H3 HSummary.
  destruct
    (StepsPhi_concat_from_left_right
      heap1 env rho e2 e3
      phi2 heap2 theta2 phi3 heap3 theta3 H2 H3)
    as (phi23 & H23 & _).
  destruct
    (StepsPhi_concat_from_left_right
      heap env rho e1 (Concat e2 e3)
      phi1 heap1 theta1 phi23 heap3 (Union_Theta theta2 theta3)
      H1 H23)
    as (phi_summary_sound & HSummarySound & _).
  destruct
    (StepsPhi_effect_terminal_deterministic
      (initial_state heap env rho (Concat e1 (Concat e2 e3)))
      phi_summary_sound heap3 (Union_Theta theta1 (Union_Theta theta2 theta3))
      phi_summary heap_summary theta_summary
      HSummarySound HSummary)
    as [_ [_ HTheta]].
  now symmetry.
Qed.

Theorem Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_case :
  forall heap env rho w e eff
    phi_arg heap_arg v r l
    phi_eff heap_eff theta_eff
    phi_summary heap_summary theta_summary
    phi_ref heap_ref v_ref,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg v) ->
    StepsPhi (initial_state heap env rho eff) phi_eff
      (StDone heap_eff (Eff theta_eff)) ->
    find_R w rho = Some r ->
    allocate_H heap_arg r = l ->
    StepsPhi (initial_state heap env rho (Concat eff (AllocAbs w)))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Ref w e)) phi_ref
      (StDone heap_ref v_ref) ->
    phi_arg ⋞ theta_eff ->
    phi_ref ⋞ theta_summary.
Proof.
  intros heap env rho w e eff
    phi_arg heap_arg v r l
    phi_eff heap_eff theta_eff
    phi_summary heap_summary theta_summary
    phi_ref heap_ref v_ref HArg HEff HFind HAlloc HSummary HRef
    HArgSound.
  destruct
    (steps_as_StepsPhi
      (initial_state heap_eff env rho (AllocAbs w))
      nil
      (StDone heap_eff (Eff (Some (singleton_set (CA_AllocAbs r)))))
      (initial_allocabs_steps_done heap_eff env rho w r HFind))
    as (phi_action & HAction & _).
  pose proof
    (StepsPhi_concat_summary_terminal_theta
      heap env rho eff (AllocAbs w)
      phi_eff heap_eff theta_eff
      phi_action heap_eff (Some (singleton_set (CA_AllocAbs r)))
      phi_summary heap_summary theta_summary
      HEff HAction HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_ref_abs_terminal_case
    heap env rho w e phi_arg heap_arg v r l theta_eff
    phi_ref heap_ref v_ref); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_direct_case :
  forall heap env rho w e eff
    phi_summary heap_summary theta_summary
    phi_ref heap_ref v_ref,
    StepsPhi (initial_state heap env rho (Concat eff (AllocAbs w)))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Ref w e)) phi_ref
      (StDone heap_ref v_ref) ->
    ReadOnlyPhi phi_summary ->
    (forall phi_arg heap_arg v phi_eff heap_eff theta_eff,
      StepsPhi (initial_state heap env rho e) phi_arg
        (StDone heap_arg v) ->
      StepsPhi (initial_state heap env rho eff) phi_eff
        (StDone heap_eff (Eff theta_eff)) ->
      ReadOnlyPhi phi_eff ->
      phi_arg ⋞ theta_eff) ->
    phi_ref ⋞ theta_summary.
Proof.
  intros heap env rho w e eff
    phi_summary heap_summary theta_summary
    phi_ref heap_ref v_ref HSummary HRef HReadOnlySummary HArgIH.
  destruct
    (StepsPhi_ref_terminal_decompose
      heap env rho w e phi_ref heap_ref v_ref HRef)
    as (phi_arg & heap_arg & v & r & l &
        HArg & HFind & HAlloc & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff (AllocAbs w)
      phi_summary heap_summary theta_summary HSummary)
    as (phi_eff & heap_eff & theta_eff &
        phi_alloc & heap_alloc & theta_alloc &
        HEff & HAllocSummary & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_eff phi_alloc HReadOnlySummary HTraceSummary)
    as HReadOnlyEff.
  pose proof
    (HArgIH phi_arg heap_arg v phi_eff heap_eff theta_eff
      HArg HEff HReadOnlyEff) as HArgSound.
  eapply (Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_case
    heap env rho w e eff
    phi_arg heap_arg v r l
    phi_eff heap_eff theta_eff
    phi_summary heap_summary theta_summary
    phi_ref heap_ref v_ref); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_case :
  forall heap env rho w e eff
    phi_arg heap_arg r l v
    phi_eff heap_eff theta_eff
    phi_summary heap_summary theta_summary
    phi_deref heap_deref v_deref,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg (Loc w l)) ->
    StepsPhi (initial_state heap env rho eff) phi_eff
      (StDone heap_eff (Eff theta_eff)) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_arg = Some v ->
    StepsPhi (initial_state heap env rho (Concat eff (ReadAbs w)))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (DeRef w e)) phi_deref
      (StDone heap_deref v_deref) ->
    phi_arg ⋞ theta_eff ->
    phi_deref ⋞ theta_summary.
Proof.
  intros heap env rho w e eff
    phi_arg heap_arg r l v
    phi_eff heap_eff theta_eff
    phi_summary heap_summary theta_summary
    phi_deref heap_deref v_deref
    HArg HEff HFindR HFindH HSummary HDeref HArgSound.
  destruct
    (steps_as_StepsPhi
      (initial_state heap_eff env rho (ReadAbs w))
      nil
      (StDone heap_eff (Eff (Some (singleton_set (CA_ReadAbs r)))))
      (initial_readabs_steps_done heap_eff env rho w r HFindR))
    as (phi_action & HAction & _).
  pose proof
    (StepsPhi_concat_summary_terminal_theta
      heap env rho eff (ReadAbs w)
      phi_eff heap_eff theta_eff
      phi_action heap_eff (Some (singleton_set (CA_ReadAbs r)))
      phi_summary heap_summary theta_summary
      HEff HAction HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_deref_abs_terminal_case
    heap env rho w e phi_arg heap_arg r l v theta_eff
    phi_deref heap_deref v_deref); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_direct_case :
  forall heap env rho w e eff
    phi_summary heap_summary theta_summary
    phi_deref heap_deref v_deref,
    StepsPhi (initial_state heap env rho (Concat eff (ReadAbs w)))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (DeRef w e)) phi_deref
      (StDone heap_deref v_deref) ->
    ReadOnlyPhi phi_summary ->
    (forall phi_arg heap_arg l phi_eff heap_eff theta_eff,
      StepsPhi (initial_state heap env rho e) phi_arg
        (StDone heap_arg (Loc w l)) ->
      StepsPhi (initial_state heap env rho eff) phi_eff
        (StDone heap_eff (Eff theta_eff)) ->
      ReadOnlyPhi phi_eff ->
      phi_arg ⋞ theta_eff) ->
    phi_deref ⋞ theta_summary.
Proof.
  intros heap env rho w e eff
    phi_summary heap_summary theta_summary
    phi_deref heap_deref v_deref HSummary HDeref HReadOnlySummary HArgIH.
  destruct
    (StepsPhi_deref_terminal_decompose
      heap env rho w e phi_deref heap_deref v_deref HDeref)
    as (phi_arg & heap_arg & r & l & v &
        HArg & HFindR & HFindH & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff (ReadAbs w)
      phi_summary heap_summary theta_summary HSummary)
    as (phi_eff & heap_eff & theta_eff &
        phi_read & heap_read & theta_read &
        HEff & HReadSummary & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_eff phi_read HReadOnlySummary HTraceSummary)
    as HReadOnlyEff.
  pose proof
    (HArgIH phi_arg heap_arg l phi_eff heap_eff theta_eff
      HArg HEff HReadOnlyEff) as HArgSound.
  eapply (Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_case
    heap env rho w e eff
    phi_arg heap_arg r l v
    phi_eff heap_eff theta_eff
    phi_summary heap_summary theta_summary
    phi_deref heap_deref v_deref); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_abs_bt_summary_terminal_case :
  forall heap env rho w ea ev eff1 eff2
    phi_loc heap_loc l phi_val heap_val v r
    phi_eff1 heap_eff1 theta_loc
    phi_eff2 heap_eff2 theta_val
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign,
    StepsPhi (initial_state heap env rho ea) phi_loc
      (StDone heap_loc (Loc w l)) ->
    StepsPhi (initial_state heap_loc env rho ev) phi_val
      (StDone heap_val v) ->
    StepsPhi (initial_state heap env rho eff1) phi_eff1
      (StDone heap_eff1 (Eff theta_loc)) ->
    StepsPhi (initial_state heap_eff1 env rho eff2) phi_eff2
      (StDone heap_eff2 (Eff theta_val)) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_val <> None ->
    StepsPhi
      (initial_state heap env rho (Concat eff1 (Concat eff2 (WriteAbs w))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Assign w ea ev)) phi_assign
      (StDone heap_assign v_assign) ->
    phi_loc ⋞ theta_loc ->
    phi_val ⋞ theta_val ->
    phi_assign ⋞ theta_summary.
Proof.
  intros heap env rho w ea ev eff1 eff2
    phi_loc heap_loc l phi_val heap_val v r
    phi_eff1 heap_eff1 theta_loc
    phi_eff2 heap_eff2 theta_val
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    HLoc HVal HEff1 HEff2 HFindR HFindH HSummary HAssign
    HLocSound HValSound.
  destruct
    (steps_as_StepsPhi
      (initial_state heap_eff2 env rho (WriteAbs w))
      nil
      (StDone heap_eff2 (Eff (Some (singleton_set (CA_WriteAbs r)))))
      (initial_writeabs_steps_done heap_eff2 env rho w r HFindR))
    as (phi_action & HAction & _).
  pose proof
    (StepsPhi_right_nested_concat_summary_terminal_theta
      heap env rho eff1 eff2 (WriteAbs w)
      phi_eff1 heap_eff1 theta_loc
      phi_eff2 heap_eff2 theta_val
      phi_action heap_eff2 (Some (singleton_set (CA_WriteAbs r)))
      phi_summary heap_summary theta_summary
      HEff1 HEff2 HAction HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_assign_abs_terminal_case
    heap env rho w ea ev
    phi_loc heap_loc l phi_val heap_val v r theta_loc theta_val
    phi_assign heap_assign v_assign); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_abs_bt_summary_terminal_direct_case :
  forall heap env rho w ea ev eff1 eff2
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc,
    StepsPhi
      (initial_state heap env rho (Concat eff1 (Concat eff2 (WriteAbs w))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Assign w ea ev)) phi_assign
      (StDone heap_assign v_assign) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty_loc, static_loc) ->
    ReadOnlyStatic (fold_subst_eps rho static_loc) ->
    ReadOnlyPhi phi_summary ->
    (forall phi_loc heap_loc l phi_eff1 heap_eff1 theta_loc,
      StepsPhi (initial_state heap env rho ea) phi_loc
        (StDone heap_loc (Loc w l)) ->
      StepsPhi (initial_state heap env rho eff1) phi_eff1
        (StDone heap_eff1 (Eff theta_loc)) ->
      ReadOnlyPhi phi_eff1 ->
      phi_loc ⋞ theta_loc) ->
    (forall phi_val heap_val v phi_eff2 heap_eff2 theta_val,
      StepsPhi (initial_state heap env rho ev) phi_val
        (StDone heap_val v) ->
      StepsPhi (initial_state heap env rho eff2) phi_eff2
        (StDone heap_eff2 (Eff theta_val)) ->
      ReadOnlyPhi phi_eff2 ->
      phi_val ⋞ theta_val) ->
    phi_assign ⋞ theta_summary.
Proof.
  intros heap env rho w ea ev eff1 eff2
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc
    HSummary HAssign HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcLoc HReadOnlyStaticLoc HReadOnlySummary HLocIH HValIH.
  destruct
    (StepsPhi_assign_terminal_decompose
      heap env rho w ea ev phi_assign heap_assign v_assign HAssign)
    as (phi_loc & heap_loc & l & phi_val & heap_val & v & r &
        HLoc & HVal & HFindR & HFindH & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 (Concat eff2 (WriteAbs w))
      phi_summary heap_summary theta_summary HSummary)
    as (phi_eff1 & heap_eff1 & theta_loc &
        phi_summary_tail & heap_summary_tail & theta_tail &
        HEff1 & HSummaryTail & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyEff1.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyTail.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_eff1 env rho eff2 (WriteAbs w)
      phi_summary_tail heap_summary_tail theta_tail HSummaryTail)
    as (phi_eff2 & heap_eff2 & theta_val &
        phi_write & heap_write & theta_write &
        HEff2 & HWriteSummary & _ & _ & HTraceTail).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary_tail phi_eff2 phi_write
      HReadOnlyTail HTraceTail) as HReadOnlyEff2.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ea stty ctxt rgns ty_loc static_loc
      phi_loc heap_loc (Loc w l)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcLoc
      HLoc HReadOnlyStaticLoc) as HHeapLoc.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff1) phi_eff1
      (StDone heap_eff1 (Eff theta_loc))
      HEff1 HReadOnlyEff1) as HHeapEff1.
  simpl in HHeapEff1.
  subst heap_loc.
  symmetry in HHeapEff1.
  subst heap_eff1.
  pose proof
    (HLocIH phi_loc heap l phi_eff1 heap theta_loc
      HLoc HEff1 HReadOnlyEff1) as HLocSound.
  pose proof
    (HValIH phi_val heap_val v phi_eff2 heap_eff2 theta_val
      HVal HEff2 HReadOnlyEff2) as HValSound.
  eapply (Correctness_soundness_ext_small_step_assign_abs_bt_summary_terminal_case
    heap env rho w ea ev eff1 eff2
    phi_loc heap l phi_val heap_val v r
    phi_eff1 heap theta_loc
    phi_eff2 heap_eff2 theta_val
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_conc_bt_summary_readonly_terminal_case :
  forall heap env rho ea ev eff1 eff2
    phi_loc heap_loc r l phi_val heap_val v
    phi_eff1 heap_eff1 theta_loc
    phi_eff2 heap_eff2 theta_val
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign,
    StepsPhi (initial_state heap env rho ea) phi_loc
      (StDone heap_loc (Loc (Rgn_Const true false r) l)) ->
    StepsPhi (initial_state heap_loc env rho ev) phi_val
      (StDone heap_val v) ->
    StepsPhi (initial_state heap env rho eff1) phi_eff1
      (StDone heap_eff1 (Eff theta_loc)) ->
    StepsPhi (initial_state heap_eff1 env rho eff2) phi_eff2
      (StDone heap_eff2 (Eff theta_val)) ->
    ReadOnlyPhi phi_eff1 ->
    ReadOnlyPhi phi_eff2 ->
    find_H (r, l) heap_val <> None ->
    StepsPhi
      (initial_state heap env rho (Concat eff1 (Concat eff2 (WriteConc ea))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi
      (initial_state heap env rho (Assign (Rgn_Const true false r) ea ev))
      phi_assign (StDone heap_assign v_assign) ->
    phi_loc ⋞ theta_loc ->
    phi_val ⋞ theta_val ->
    phi_assign ⋞ theta_summary.
Proof.
  intros heap env rho ea ev eff1 eff2
    phi_loc heap_loc r l phi_val heap_val v
    phi_eff1 heap_eff1 theta_loc
    phi_eff2 heap_eff2 theta_val
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    HLoc HVal HEff1 HEff2 HReadOnly1 HReadOnly2 HFindH HSummary
    HAssign HLocSound HValSound.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff1) phi_eff1
      (StDone heap_eff1 (Eff theta_loc)) HEff1 HReadOnly1)
    as HHeap1.
  simpl in HHeap1.
  subst heap_eff1.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff2) phi_eff2
      (StDone heap_eff2 (Eff theta_val)) HEff2 HReadOnly2)
    as HHeap2.
  simpl in HHeap2.
  subst heap_eff2.
  destruct
    (StepsPhi_writeconc_from_arg
      heap env rho ea phi_loc heap_loc r l HLoc)
    as (phi_action & HAction & _).
  pose proof
    (StepsPhi_right_nested_concat_summary_terminal_theta
      heap env rho eff1 eff2 (WriteConc ea)
      phi_eff1 heap theta_loc
      phi_eff2 heap theta_val
      phi_action heap_loc (Some (singleton_set (CA_WriteConc r l)))
      phi_summary heap_summary theta_summary
      HEff1 HEff2 HAction HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_assign_conc_terminal_case
    heap env rho (Rgn_Const true false r) ea ev
    phi_loc heap_loc l phi_val heap_val v r theta_loc theta_val
    phi_assign heap_assign v_assign); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_direct_case :
  forall heap env rho ea ev eff1 eff2 r
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc,
    StepsPhi
      (initial_state heap env rho (Concat eff1 (Concat eff2 (WriteConc ea))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi
      (initial_state heap env rho (Assign (Rgn_Const true false r) ea ev))
      phi_assign (StDone heap_assign v_assign) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty_loc, static_loc) ->
    ReadOnlyStatic (fold_subst_eps rho static_loc) ->
    ReadOnlyPhi phi_summary ->
    (forall phi_loc heap_loc l phi_eff1 heap_eff1 theta_loc,
      StepsPhi (initial_state heap env rho ea) phi_loc
        (StDone heap_loc (Loc (Rgn_Const true false r) l)) ->
      StepsPhi (initial_state heap env rho eff1) phi_eff1
        (StDone heap_eff1 (Eff theta_loc)) ->
      ReadOnlyPhi phi_eff1 ->
      phi_loc ⋞ theta_loc) ->
    (forall phi_val heap_val v phi_eff2 heap_eff2 theta_val,
      StepsPhi (initial_state heap env rho ev) phi_val
        (StDone heap_val v) ->
      StepsPhi (initial_state heap env rho eff2) phi_eff2
        (StDone heap_eff2 (Eff theta_val)) ->
      ReadOnlyPhi phi_eff2 ->
      phi_val ⋞ theta_val) ->
    phi_assign ⋞ theta_summary.
Proof.
  intros heap env rho ea ev eff1 eff2 r
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc
    HSummary HAssign HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcLoc HReadOnlyStaticLoc HReadOnlySummary HLocIH HValIH.
  destruct
    (StepsPhi_assign_terminal_decompose
      heap env rho (Rgn_Const true false r) ea ev
      phi_assign heap_assign v_assign HAssign)
    as (phi_loc & heap_loc & l & phi_val & heap_val & v & r_write &
        HLoc & HVal & HFindR & HFindH & _ & _ & _).
  simpl in HFindR.
  inversion HFindR; subst r_write.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 (Concat eff2 (WriteConc ea))
      phi_summary heap_summary theta_summary HSummary)
    as (phi_eff1 & heap_eff1 & theta_loc &
        phi_summary_tail & heap_summary_tail & theta_tail &
        HEff1 & HSummaryTail & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyEff1.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyTail.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_eff1 env rho eff2 (WriteConc ea)
      phi_summary_tail heap_summary_tail theta_tail HSummaryTail)
    as (phi_eff2 & heap_eff2 & theta_val &
        phi_write & heap_write & theta_write &
        HEff2 & HWriteSummary & _ & _ & HTraceTail).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary_tail phi_eff2 phi_write
      HReadOnlyTail HTraceTail) as HReadOnlyEff2.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ea stty ctxt rgns ty_loc static_loc
      phi_loc heap_loc (Loc (Rgn_Const true false r) l)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcLoc
      HLoc HReadOnlyStaticLoc) as HHeapLoc.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff1) phi_eff1
      (StDone heap_eff1 (Eff theta_loc))
      HEff1 HReadOnlyEff1) as HHeapEff1.
  simpl in HHeapEff1.
  subst heap_loc.
  symmetry in HHeapEff1.
  subst heap_eff1.
  pose proof
    (HLocIH phi_loc heap l phi_eff1 heap theta_loc
      HLoc HEff1 HReadOnlyEff1) as HLocSound.
  pose proof
    (HValIH phi_val heap_val v phi_eff2 heap_eff2 theta_val
      HVal HEff2 HReadOnlyEff2) as HValSound.
  eapply (Correctness_soundness_ext_small_step_assign_conc_bt_summary_readonly_terminal_case
    heap env rho ea ev eff1 eff2
    phi_loc heap r l phi_val heap_val v
    phi_eff1 heap theta_loc
    phi_eff2 heap_eff2 theta_val
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_case :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1 theta3
    phi_mu2 heap_mu2 v2 theta4
    phi_sum1 heap_sum1
    phi_sum2 heap_sum2
    phi_sum3 heap_sum3
    phi_sum4 heap_sum4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair,
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    StepsPhi (initial_state heap env rho eff1) phi_sum1
      (StDone heap_sum1 (Eff theta1)) ->
    StepsPhi (initial_state heap_sum1 env rho eff2) phi_sum2
      (StDone heap_sum2 (Eff theta2)) ->
    StepsPhi (initial_state heap_sum2 env rho eff3) phi_sum3
      (StDone heap_sum3 (Eff theta3)) ->
    StepsPhi (initial_state heap_sum3 env rho eff4) phi_sum4
      (StDone heap_sum4 (Eff theta4)) ->
    StepsPhi
      (initial_state heap env rho
        (Concat (Concat eff1 eff2) (Concat eff3 eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta3 ->
    phi_mu2 ⋞ theta4 ->
    phi_pair ⋞ theta_summary.
Proof.
  intros HCheck heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1 theta3
    phi_mu2 heap_mu2 v2 theta4
    phi_sum1 heap_sum1
    phi_sum2 heap_sum2
    phi_sum3 heap_sum3
    phi_sum4 heap_sum4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    HSummaryPair HSum1 HSum2 HSum3 HSum4 HSummary
    HMu1 HMu2 HPair
    HEff1Sound HEff2Sound HMu1Sound HMu2Sound.
  pose proof
    (StepsPhi_nested_concat_summary_terminal_theta
      heap env rho eff1 eff2 eff3 eff4
      phi_sum1 heap_sum1 theta1
      phi_sum2 heap_sum2 theta2
      phi_sum3 heap_sum3 theta3
      phi_sum4 heap_sum4 theta4
      phi_summary heap_summary theta_summary
      HSum1 HSum2 HSum3 HSum4 HSummary) as HTheta.
  subst theta_summary.
  inversion HSummaryPair as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HEff1 HEff2]; subst.
  eapply Correctness_soundness_ext_small_step_pair_par_checked_terminal_case;
    eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_direct_case :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair,
    StepsPhi
      (initial_state heap env rho
        (Concat (Concat eff1 eff2) (Concat eff3 eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    (forall phi_eff1 heap_eff1 theta_eff1
            phi_sum1 heap_sum1 theta1,
      StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
        (StDone heap_eff1 (Eff theta_eff1)) ->
      StepsPhi (initial_state heap env rho eff1) phi_sum1
        (StDone heap_sum1 (Eff theta1)) ->
      phi_eff1 ⋞ theta1) ->
    (forall heap_eff1 phi_eff2 heap_eff2 theta_eff2
            heap_sum1 phi_sum2 heap_sum2 theta2,
      StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2))
        phi_eff2
        (StDone heap_eff2 (Eff theta_eff2)) ->
      StepsPhi (initial_state heap_sum1 env rho eff2) phi_sum2
        (StDone heap_sum2 (Eff theta2)) ->
      phi_eff2 ⋞ theta2) ->
    (forall heap_eff2 phi_mu1 heap_mu1 v1
            heap_sum2 phi_sum3 heap_sum3 theta3,
      StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) ->
      StepsPhi (initial_state heap_sum2 env rho eff3) phi_sum3
        (StDone heap_sum3 (Eff theta3)) ->
      phi_mu1 ⋞ theta3) ->
    (forall heap_mu1 phi_mu2 heap_mu2 v2
            heap_sum3 phi_sum4 heap_sum4 theta4,
      StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
        (StDone heap_mu2 v2) ->
      StepsPhi (initial_state heap_sum3 env rho eff4) phi_sum4
        (StDone heap_sum4 (Eff theta4)) ->
      phi_mu2 ⋞ theta4) ->
    phi_pair ⋞ theta_summary.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair HSummary HPair
    HEff1IH HEff2IH HMu1IH HMu2IH.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho (Concat eff1 eff2) (Concat eff3 eff4)
      phi_summary heap_summary theta_summary HSummary)
    as (phi_sum12 & heap_sum12 & theta12 &
        phi_sum34 & heap_sum34 & theta34 &
        HSum12 & HSum34 & HHeapSummary & HThetaSummary & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 eff2
      phi_sum12 heap_sum12 theta12 HSum12)
    as (phi_sum1 & heap_sum1 & theta1 &
        phi_sum2 & heap_sum2 & theta2 &
        HSum1 & HSum2 & HHeap12 & HTheta12 & _).
  subst heap_sum12.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_sum2 env rho eff3 eff4
      phi_sum34 heap_sum34 theta34 HSum34)
    as (phi_sum3 & heap_sum3 & theta3 &
        phi_sum4 & heap_sum4 & theta4 &
        HSum3 & HSum4 & HHeap34 & HTheta34 & _).
  subst heap_sum34.
  destruct
    (StepsPhi_pair_par_terminal_decompose
      heap env rho ef1 ea1 ef2 ea2 phi_pair heap_pair v_pair HPair)
    as (phi_eff1 & heap_eff1 & theta_eff1 &
        phi_eff2 & heap_eff2 & theta_eff2 &
        phi_mu1 & heap_mu1 & v1 &
        phi_mu2 & heap_mu2 & v2 &
        HEff1 & HEff2 & HMu1 & HMu2 &
        _ & _ & HTracePair).
  pose proof
    (HEff1IH phi_eff1 heap_eff1 theta_eff1
      phi_sum1 heap_sum1 theta1 HEff1 HSum1) as HEff1Sound.
  pose proof
    (HEff2IH heap_eff1 phi_eff2 heap_eff2 theta_eff2
      heap_sum1 phi_sum2 heap_sum2 theta2 HEff2 HSum2) as HEff2Sound.
  pose proof
    (HMu1IH heap_eff2 phi_mu1 heap_mu1 v1
      heap_sum2 phi_sum3 heap_sum3 theta3 HMu1 HSum3) as HMu1Sound.
  pose proof
    (HMu2IH heap_mu1 phi_mu2 heap_mu2 v2
      heap_sum3 phi_sum4 heap_sum4 theta4 HMu2 HSum4) as HMu2Sound.
  subst theta12.
  subst theta34.
  subst theta_summary.
  eapply Correctness_soundness_ext_small_step_quad_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_plus_composed_case :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    phi_left ⋞ theta ->
    phi_right ⋞ theta ->
    exists phi_plus,
      StepsPhi (initial_state heap env rho (Plus e1 e2)) phi_plus
        (StDone heap_right (Num (n1 + n2))) /\
      phi_plus ⋞ theta.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta
    HLeft HRight HLeftSound HRightSound.
  destruct
    (StepsPhi_plus_from_left_right
      heap env rho e1 e2
      phi_left heap_left n1 phi_right heap_right n2 HLeft HRight)
    as (phi_plus & HPlus & HList).
  exists phi_plus.
  split; [exact HPlus |].
  eapply Correctness_soundness_ext_small_step_binary_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_plus_terminal_case :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta
    phi_plus heap_plus v_plus,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    StepsPhi (initial_state heap env rho (Plus e1 e2)) phi_plus
      (StDone heap_plus v_plus) ->
    phi_left ⋞ theta ->
    phi_right ⋞ theta ->
    phi_plus ⋞ theta.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta
    phi_plus heap_plus v_plus HLeft HRight HPlus HLeftSound HRightSound.
  destruct
    (Correctness_soundness_ext_small_step_plus_composed_case
      heap env rho e1 e2
      phi_left heap_left n1 phi_right heap_right n2 theta
      HLeft HRight HLeftSound HRightSound)
    as (phi_plus_sound & HPlusSoundSteps & HPlusSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_plus_union_composed_case :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    exists phi_plus,
      StepsPhi (initial_state heap env rho (Plus e1 e2)) phi_plus
        (StDone heap_right (Num (n1 + n2))) /\
      phi_plus ⋞ Union_Theta theta1 theta2.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
    HLeft HRight HLeftSound HRightSound.
  destruct
    (StepsPhi_plus_from_left_right
      heap env rho e1 e2
      phi_left heap_left n1 phi_right heap_right n2 HLeft HRight)
    as (phi_plus & HPlus & HList).
  exists phi_plus.
  split; [exact HPlus |].
  eapply Correctness_soundness_ext_small_step_binary_union_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_plus_union_terminal_case :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
    phi_plus heap_plus v_plus,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    StepsPhi (initial_state heap env rho (Plus e1 e2)) phi_plus
      (StDone heap_plus v_plus) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    phi_plus ⋞ Union_Theta theta1 theta2.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
    phi_plus heap_plus v_plus HLeft HRight HPlus HLeftSound HRightSound.
  destruct
    (Correctness_soundness_ext_small_step_plus_union_composed_case
      heap env rho e1 e2
      phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
      HLeft HRight HLeftSound HRightSound)
    as (phi_plus_sound & HPlusSoundSteps & HPlusSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_plus_summary_terminal_case :
  forall heap env rho e1 e2 eff1 eff2
    phi_left heap_left n1 phi_right heap_right n2
    phi_left_summary heap_left_summary theta1
    phi_right_summary heap_right_summary theta2
    phi_summary heap_summary theta_summary
    phi_plus heap_plus v_plus,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    StepsPhi (initial_state heap env rho eff1) phi_left_summary
      (StDone heap_left_summary (Eff theta1)) ->
    StepsPhi (initial_state heap_left_summary env rho eff2) phi_right_summary
      (StDone heap_right_summary (Eff theta2)) ->
    StepsPhi (initial_state heap env rho (Concat eff1 eff2)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Plus e1 e2)) phi_plus
      (StDone heap_plus v_plus) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    phi_plus ⋞ theta_summary.
Proof.
  intros heap env rho e1 e2 eff1 eff2
    phi_left heap_left n1 phi_right heap_right n2
    phi_left_summary heap_left_summary theta1
    phi_right_summary heap_right_summary theta2
    phi_summary heap_summary theta_summary
    phi_plus heap_plus v_plus
    HLeft HRight HLeftSummary HRightSummary HSummary HPlus
    HLeftSound HRightSound.
  pose proof
    (StepsPhi_concat_summary_terminal_theta
      heap env rho eff1 eff2
      phi_left_summary heap_left_summary theta1
      phi_right_summary heap_right_summary theta2
      phi_summary heap_summary theta_summary
      HLeftSummary HRightSummary HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_plus_union_terminal_case
    heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
	    phi_plus heap_plus v_plus); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_plus_summary_terminal_heterogeneous_case :
  forall heap heap_summary_start env rho e1 e2 eff1 eff2
    phi_left heap_left n1 phi_right heap_right n2
    phi_left_summary heap_left_summary theta1
    phi_right_summary heap_right_summary theta2
    phi_summary heap_summary theta_summary
    phi_plus heap_plus v_plus,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    StepsPhi (initial_state heap_summary_start env rho eff1) phi_left_summary
      (StDone heap_left_summary (Eff theta1)) ->
    StepsPhi (initial_state heap_left_summary env rho eff2) phi_right_summary
      (StDone heap_right_summary (Eff theta2)) ->
    StepsPhi (initial_state heap_summary_start env rho (Concat eff1 eff2))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Plus e1 e2)) phi_plus
      (StDone heap_plus v_plus) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    phi_plus ⋞ theta_summary.
Proof.
  intros heap heap_summary_start env rho e1 e2 eff1 eff2
    phi_left heap_left n1 phi_right heap_right n2
    phi_left_summary heap_left_summary theta1
    phi_right_summary heap_right_summary theta2
    phi_summary heap_summary theta_summary
    phi_plus heap_plus v_plus
    HLeft HRight HLeftSummary HRightSummary HSummary HPlus
    HLeftSound HRightSound.
  pose proof
    (StepsPhi_concat_summary_terminal_theta
      heap_summary_start env rho eff1 eff2
      phi_left_summary heap_left_summary theta1
      phi_right_summary heap_right_summary theta2
      phi_summary heap_summary theta_summary
      HLeftSummary HRightSummary HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_plus_union_terminal_case
    heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
    phi_plus heap_plus v_plus); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_plus_summary_terminal_direct_case :
  forall heap env rho e1 e2 eff1 eff2
    phi_plus heap_plus v_plus
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2,
    StepsPhi (initial_state heap env rho (Plus e1 e2)) phi_plus
      (StDone heap_plus v_plus) ->
    StepsPhi (initial_state heap env rho (Concat eff1 eff2)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    ReadOnlyPhi phi_summary ->
    (forall phi_left heap_left n1 phi_left_summary heap_left_summary theta1,
      StepsPhi (initial_state heap env rho e1) phi_left
        (StDone heap_left (Num n1)) ->
      StepsPhi (initial_state heap env rho eff1) phi_left_summary
        (StDone heap_left_summary (Eff theta1)) ->
      ReadOnlyPhi phi_left_summary ->
      phi_left ⋞ theta1) ->
    (forall phi_right heap_right n2 phi_right_summary heap_right_summary theta2,
      StepsPhi (initial_state heap env rho e2) phi_right
        (StDone heap_right (Num n2)) ->
      StepsPhi (initial_state heap env rho eff2) phi_right_summary
        (StDone heap_right_summary (Eff theta2)) ->
      ReadOnlyPhi phi_right_summary ->
      phi_right ⋞ theta2) ->
    phi_plus ⋞ theta_summary.
Proof.
  intros heap env rho e1 e2 eff1 eff2
    phi_plus heap_plus v_plus
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2
    HPlus HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE1 HTcE2 HReadOnlyStatic1 HReadOnlySummary HLeftIH HRightIH.
  destruct
    (StepsPhi_plus_terminal_decompose
      heap env rho e1 e2 phi_plus heap_plus v_plus HPlus)
    as (phi_left & heap_left & n1 & phi_right & heap_right & n2 &
        HLeft & HRight & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 eff2 phi_summary heap_summary theta_summary
      HSummary)
    as (phi_left_summary & heap_left_summary & theta1 &
        phi_right_summary & heap_right_summary & theta2 &
        HLeftSummary & HRightSummary & _ & HTheta & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyLeftSummary.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyRightSummary.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho e1 stty ctxt rgns ty_e1 static_e1
      phi_left heap_left (Num n1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcE1
      HLeft HReadOnlyStatic1) as HHeapLeft.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff1) phi_left_summary
      (StDone heap_left_summary (Eff theta1))
      HLeftSummary HReadOnlyLeftSummary) as HHeapLeftSummary.
  simpl in HHeapLeftSummary.
  subst heap_left.
  symmetry in HHeapLeftSummary.
  subst heap_left_summary.
  pose proof
    (HLeftIH
      phi_left heap n1 phi_left_summary heap theta1
      HLeft HLeftSummary HReadOnlyLeftSummary) as HLeftSound.
  pose proof
    (HRightIH
      phi_right heap_right n2 phi_right_summary heap_right_summary theta2
      HRight HRightSummary HReadOnlyRightSummary) as HRightSound.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_plus_union_terminal_case
    heap env rho e1 e2
    phi_left heap n1 phi_right heap_right n2 theta1 theta2
    phi_plus heap_plus v_plus); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_minus_composed_case :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    phi_left ⋞ theta ->
    phi_right ⋞ theta ->
    exists phi_minus,
      StepsPhi (initial_state heap env rho (Minus e1 e2)) phi_minus
        (StDone heap_right (Num (n1 - n2))) /\
      phi_minus ⋞ theta.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta
    HLeft HRight HLeftSound HRightSound.
  destruct
    (StepsPhi_minus_from_left_right
      heap env rho e1 e2
      phi_left heap_left n1 phi_right heap_right n2 HLeft HRight)
    as (phi_minus & HMinus & HList).
  exists phi_minus.
  split; [exact HMinus |].
  eapply Correctness_soundness_ext_small_step_binary_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_minus_terminal_case :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta
    phi_minus heap_minus v_minus,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    StepsPhi (initial_state heap env rho (Minus e1 e2)) phi_minus
      (StDone heap_minus v_minus) ->
    phi_left ⋞ theta ->
    phi_right ⋞ theta ->
    phi_minus ⋞ theta.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta
    phi_minus heap_minus v_minus HLeft HRight HMinus HLeftSound HRightSound.
  destruct
    (Correctness_soundness_ext_small_step_minus_composed_case
      heap env rho e1 e2
      phi_left heap_left n1 phi_right heap_right n2 theta
      HLeft HRight HLeftSound HRightSound)
    as (phi_minus_sound & HMinusSoundSteps & HMinusSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_minus_union_composed_case :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    exists phi_minus,
      StepsPhi (initial_state heap env rho (Minus e1 e2)) phi_minus
        (StDone heap_right (Num (n1 - n2))) /\
      phi_minus ⋞ Union_Theta theta1 theta2.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
    HLeft HRight HLeftSound HRightSound.
  destruct
    (StepsPhi_minus_from_left_right
      heap env rho e1 e2
      phi_left heap_left n1 phi_right heap_right n2 HLeft HRight)
    as (phi_minus & HMinus & HList).
  exists phi_minus.
  split; [exact HMinus |].
  eapply Correctness_soundness_ext_small_step_binary_union_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_minus_union_terminal_case :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
    phi_minus heap_minus v_minus,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    StepsPhi (initial_state heap env rho (Minus e1 e2)) phi_minus
      (StDone heap_minus v_minus) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    phi_minus ⋞ Union_Theta theta1 theta2.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
    phi_minus heap_minus v_minus HLeft HRight HMinus HLeftSound HRightSound.
  destruct
    (Correctness_soundness_ext_small_step_minus_union_composed_case
      heap env rho e1 e2
      phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
      HLeft HRight HLeftSound HRightSound)
    as (phi_minus_sound & HMinusSoundSteps & HMinusSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_minus_summary_terminal_case :
  forall heap env rho e1 e2 eff1 eff2
    phi_left heap_left n1 phi_right heap_right n2
    phi_left_summary heap_left_summary theta1
    phi_right_summary heap_right_summary theta2
    phi_summary heap_summary theta_summary
    phi_minus heap_minus v_minus,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    StepsPhi (initial_state heap env rho eff1) phi_left_summary
      (StDone heap_left_summary (Eff theta1)) ->
    StepsPhi (initial_state heap_left_summary env rho eff2) phi_right_summary
      (StDone heap_right_summary (Eff theta2)) ->
    StepsPhi (initial_state heap env rho (Concat eff1 eff2)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Minus e1 e2)) phi_minus
      (StDone heap_minus v_minus) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    phi_minus ⋞ theta_summary.
Proof.
  intros heap env rho e1 e2 eff1 eff2
    phi_left heap_left n1 phi_right heap_right n2
    phi_left_summary heap_left_summary theta1
    phi_right_summary heap_right_summary theta2
    phi_summary heap_summary theta_summary
    phi_minus heap_minus v_minus
    HLeft HRight HLeftSummary HRightSummary HSummary HMinus
    HLeftSound HRightSound.
  pose proof
    (StepsPhi_concat_summary_terminal_theta
      heap env rho eff1 eff2
      phi_left_summary heap_left_summary theta1
      phi_right_summary heap_right_summary theta2
      phi_summary heap_summary theta_summary
      HLeftSummary HRightSummary HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_minus_union_terminal_case
    heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
	    phi_minus heap_minus v_minus); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_minus_summary_terminal_heterogeneous_case :
  forall heap heap_summary_start env rho e1 e2 eff1 eff2
    phi_left heap_left n1 phi_right heap_right n2
    phi_left_summary heap_left_summary theta1
    phi_right_summary heap_right_summary theta2
    phi_summary heap_summary theta_summary
    phi_minus heap_minus v_minus,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    StepsPhi (initial_state heap_summary_start env rho eff1) phi_left_summary
      (StDone heap_left_summary (Eff theta1)) ->
    StepsPhi (initial_state heap_left_summary env rho eff2) phi_right_summary
      (StDone heap_right_summary (Eff theta2)) ->
    StepsPhi (initial_state heap_summary_start env rho (Concat eff1 eff2))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Minus e1 e2)) phi_minus
      (StDone heap_minus v_minus) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    phi_minus ⋞ theta_summary.
Proof.
  intros heap heap_summary_start env rho e1 e2 eff1 eff2
    phi_left heap_left n1 phi_right heap_right n2
    phi_left_summary heap_left_summary theta1
    phi_right_summary heap_right_summary theta2
    phi_summary heap_summary theta_summary
    phi_minus heap_minus v_minus
    HLeft HRight HLeftSummary HRightSummary HSummary HMinus
    HLeftSound HRightSound.
  pose proof
    (StepsPhi_concat_summary_terminal_theta
      heap_summary_start env rho eff1 eff2
      phi_left_summary heap_left_summary theta1
      phi_right_summary heap_right_summary theta2
      phi_summary heap_summary theta_summary
      HLeftSummary HRightSummary HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_minus_union_terminal_case
    heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
    phi_minus heap_minus v_minus); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_minus_summary_terminal_direct_case :
  forall heap env rho e1 e2 eff1 eff2
    phi_minus heap_minus v_minus
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2,
    StepsPhi (initial_state heap env rho (Minus e1 e2)) phi_minus
      (StDone heap_minus v_minus) ->
    StepsPhi (initial_state heap env rho (Concat eff1 eff2)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    ReadOnlyPhi phi_summary ->
    (forall phi_left heap_left n1 phi_left_summary heap_left_summary theta1,
      StepsPhi (initial_state heap env rho e1) phi_left
        (StDone heap_left (Num n1)) ->
      StepsPhi (initial_state heap env rho eff1) phi_left_summary
        (StDone heap_left_summary (Eff theta1)) ->
      ReadOnlyPhi phi_left_summary ->
      phi_left ⋞ theta1) ->
    (forall phi_right heap_right n2 phi_right_summary heap_right_summary theta2,
      StepsPhi (initial_state heap env rho e2) phi_right
        (StDone heap_right (Num n2)) ->
      StepsPhi (initial_state heap env rho eff2) phi_right_summary
        (StDone heap_right_summary (Eff theta2)) ->
      ReadOnlyPhi phi_right_summary ->
      phi_right ⋞ theta2) ->
    phi_minus ⋞ theta_summary.
Proof.
  intros heap env rho e1 e2 eff1 eff2
    phi_minus heap_minus v_minus
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2
    HMinus HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE1 HTcE2 HReadOnlyStatic1 HReadOnlySummary HLeftIH HRightIH.
  destruct
    (StepsPhi_minus_terminal_decompose
      heap env rho e1 e2 phi_minus heap_minus v_minus HMinus)
    as (phi_left & heap_left & n1 & phi_right & heap_right & n2 &
        HLeft & HRight & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 eff2 phi_summary heap_summary theta_summary
      HSummary)
    as (phi_left_summary & heap_left_summary & theta1 &
        phi_right_summary & heap_right_summary & theta2 &
        HLeftSummary & HRightSummary & _ & HTheta & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyLeftSummary.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyRightSummary.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho e1 stty ctxt rgns ty_e1 static_e1
      phi_left heap_left (Num n1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcE1
      HLeft HReadOnlyStatic1) as HHeapLeft.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff1) phi_left_summary
      (StDone heap_left_summary (Eff theta1))
      HLeftSummary HReadOnlyLeftSummary) as HHeapLeftSummary.
  simpl in HHeapLeftSummary.
  subst heap_left.
  symmetry in HHeapLeftSummary.
  subst heap_left_summary.
  pose proof
    (HLeftIH
      phi_left heap n1 phi_left_summary heap theta1
      HLeft HLeftSummary HReadOnlyLeftSummary) as HLeftSound.
  pose proof
    (HRightIH
      phi_right heap_right n2 phi_right_summary heap_right_summary theta2
      HRight HRightSummary HReadOnlyRightSummary) as HRightSound.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_minus_union_terminal_case
    heap env rho e1 e2
    phi_left heap n1 phi_right heap_right n2 theta1 theta2
    phi_minus heap_minus v_minus); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_times_composed_case :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    phi_left ⋞ theta ->
    phi_right ⋞ theta ->
    exists phi_times,
      StepsPhi (initial_state heap env rho (Times e1 e2)) phi_times
        (StDone heap_right (Num (n1 * n2))) /\
      phi_times ⋞ theta.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta
    HLeft HRight HLeftSound HRightSound.
  destruct
    (StepsPhi_times_from_left_right
      heap env rho e1 e2
      phi_left heap_left n1 phi_right heap_right n2 HLeft HRight)
    as (phi_times & HTimes & HList).
  exists phi_times.
  split; [exact HTimes |].
  eapply Correctness_soundness_ext_small_step_binary_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_times_terminal_case :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta
    phi_times heap_times v_times,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    StepsPhi (initial_state heap env rho (Times e1 e2)) phi_times
      (StDone heap_times v_times) ->
    phi_left ⋞ theta ->
    phi_right ⋞ theta ->
    phi_times ⋞ theta.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta
    phi_times heap_times v_times HTLeft HTRight HTimes HLeftSound HRightSound.
  destruct
    (Correctness_soundness_ext_small_step_times_composed_case
      heap env rho e1 e2
      phi_left heap_left n1 phi_right heap_right n2 theta
      HTLeft HTRight HLeftSound HRightSound)
    as (phi_times_sound & HTimesSoundSteps & HTimesSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_times_union_composed_case :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    exists phi_times,
      StepsPhi (initial_state heap env rho (Times e1 e2)) phi_times
        (StDone heap_right (Num (n1 * n2))) /\
      phi_times ⋞ Union_Theta theta1 theta2.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
    HLeft HRight HLeftSound HRightSound.
  destruct
    (StepsPhi_times_from_left_right
      heap env rho e1 e2
      phi_left heap_left n1 phi_right heap_right n2 HLeft HRight)
    as (phi_times & HTimes & HList).
  exists phi_times.
  split; [exact HTimes |].
  eapply Correctness_soundness_ext_small_step_binary_union_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_times_union_terminal_case :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
    phi_times heap_times v_times,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    StepsPhi (initial_state heap env rho (Times e1 e2)) phi_times
      (StDone heap_times v_times) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    phi_times ⋞ Union_Theta theta1 theta2.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
    phi_times heap_times v_times HLeft HRight HTimes HLeftSound HRightSound.
  destruct
    (Correctness_soundness_ext_small_step_times_union_composed_case
      heap env rho e1 e2
      phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
      HLeft HRight HLeftSound HRightSound)
    as (phi_times_sound & HTimesSoundSteps & HTimesSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_times_summary_terminal_case :
  forall heap env rho e1 e2 eff1 eff2
    phi_left heap_left n1 phi_right heap_right n2
    phi_left_summary heap_left_summary theta1
    phi_right_summary heap_right_summary theta2
    phi_summary heap_summary theta_summary
    phi_times heap_times v_times,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    StepsPhi (initial_state heap env rho eff1) phi_left_summary
      (StDone heap_left_summary (Eff theta1)) ->
    StepsPhi (initial_state heap_left_summary env rho eff2) phi_right_summary
      (StDone heap_right_summary (Eff theta2)) ->
    StepsPhi (initial_state heap env rho (Concat eff1 eff2)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Times e1 e2)) phi_times
      (StDone heap_times v_times) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    phi_times ⋞ theta_summary.
Proof.
  intros heap env rho e1 e2 eff1 eff2
    phi_left heap_left n1 phi_right heap_right n2
    phi_left_summary heap_left_summary theta1
    phi_right_summary heap_right_summary theta2
    phi_summary heap_summary theta_summary
    phi_times heap_times v_times
    HLeft HRight HLeftSummary HRightSummary HSummary HTimes
    HLeftSound HRightSound.
  pose proof
    (StepsPhi_concat_summary_terminal_theta
      heap env rho eff1 eff2
      phi_left_summary heap_left_summary theta1
      phi_right_summary heap_right_summary theta2
      phi_summary heap_summary theta_summary
      HLeftSummary HRightSummary HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_times_union_terminal_case
    heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
	    phi_times heap_times v_times); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_times_summary_terminal_heterogeneous_case :
  forall heap heap_summary_start env rho e1 e2 eff1 eff2
    phi_left heap_left n1 phi_right heap_right n2
    phi_left_summary heap_left_summary theta1
    phi_right_summary heap_right_summary theta2
    phi_summary heap_summary theta_summary
    phi_times heap_times v_times,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    StepsPhi (initial_state heap_summary_start env rho eff1) phi_left_summary
      (StDone heap_left_summary (Eff theta1)) ->
    StepsPhi (initial_state heap_left_summary env rho eff2) phi_right_summary
      (StDone heap_right_summary (Eff theta2)) ->
    StepsPhi (initial_state heap_summary_start env rho (Concat eff1 eff2))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Times e1 e2)) phi_times
      (StDone heap_times v_times) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    phi_times ⋞ theta_summary.
Proof.
  intros heap heap_summary_start env rho e1 e2 eff1 eff2
    phi_left heap_left n1 phi_right heap_right n2
    phi_left_summary heap_left_summary theta1
    phi_right_summary heap_right_summary theta2
    phi_summary heap_summary theta_summary
    phi_times heap_times v_times
    HLeft HRight HLeftSummary HRightSummary HSummary HTimes
    HLeftSound HRightSound.
  pose proof
    (StepsPhi_concat_summary_terminal_theta
      heap_summary_start env rho eff1 eff2
      phi_left_summary heap_left_summary theta1
      phi_right_summary heap_right_summary theta2
      phi_summary heap_summary theta_summary
      HLeftSummary HRightSummary HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_times_union_terminal_case
    heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
    phi_times heap_times v_times); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_times_summary_terminal_direct_case :
  forall heap env rho e1 e2 eff1 eff2
    phi_times heap_times v_times
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2,
    StepsPhi (initial_state heap env rho (Times e1 e2)) phi_times
      (StDone heap_times v_times) ->
    StepsPhi (initial_state heap env rho (Concat eff1 eff2)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    ReadOnlyPhi phi_summary ->
    (forall phi_left heap_left n1 phi_left_summary heap_left_summary theta1,
      StepsPhi (initial_state heap env rho e1) phi_left
        (StDone heap_left (Num n1)) ->
      StepsPhi (initial_state heap env rho eff1) phi_left_summary
        (StDone heap_left_summary (Eff theta1)) ->
      ReadOnlyPhi phi_left_summary ->
      phi_left ⋞ theta1) ->
    (forall phi_right heap_right n2 phi_right_summary heap_right_summary theta2,
      StepsPhi (initial_state heap env rho e2) phi_right
        (StDone heap_right (Num n2)) ->
      StepsPhi (initial_state heap env rho eff2) phi_right_summary
        (StDone heap_right_summary (Eff theta2)) ->
      ReadOnlyPhi phi_right_summary ->
      phi_right ⋞ theta2) ->
    phi_times ⋞ theta_summary.
Proof.
  intros heap env rho e1 e2 eff1 eff2
    phi_times heap_times v_times
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2
    HTimes HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE1 HTcE2 HReadOnlyStatic1 HReadOnlySummary HLeftIH HRightIH.
  destruct
    (StepsPhi_times_terminal_decompose
      heap env rho e1 e2 phi_times heap_times v_times HTimes)
    as (phi_left & heap_left & n1 & phi_right & heap_right & n2 &
        HLeft & HRight & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 eff2 phi_summary heap_summary theta_summary
      HSummary)
    as (phi_left_summary & heap_left_summary & theta1 &
        phi_right_summary & heap_right_summary & theta2 &
        HLeftSummary & HRightSummary & _ & HTheta & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyLeftSummary.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyRightSummary.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho e1 stty ctxt rgns ty_e1 static_e1
      phi_left heap_left (Num n1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcE1
      HLeft HReadOnlyStatic1) as HHeapLeft.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff1) phi_left_summary
      (StDone heap_left_summary (Eff theta1))
      HLeftSummary HReadOnlyLeftSummary) as HHeapLeftSummary.
  simpl in HHeapLeftSummary.
  subst heap_left.
  symmetry in HHeapLeftSummary.
  subst heap_left_summary.
  pose proof
    (HLeftIH
      phi_left heap n1 phi_left_summary heap theta1
      HLeft HLeftSummary HReadOnlyLeftSummary) as HLeftSound.
  pose proof
    (HRightIH
      phi_right heap_right n2 phi_right_summary heap_right_summary theta2
      HRight HRightSummary HReadOnlyRightSummary) as HRightSound.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_times_union_terminal_case
    heap env rho e1 e2
    phi_left heap n1 phi_right heap_right n2 theta1 theta2
    phi_times heap_times v_times); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_eq_composed_case :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    phi_left ⋞ theta ->
    phi_right ⋞ theta ->
    exists phi_eq,
      StepsPhi (initial_state heap env rho (Eq e1 e2)) phi_eq
        (StDone heap_right (Bit (Nat.eqb n1 n2))) /\
      phi_eq ⋞ theta.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta
    HLeft HRight HLeftSound HRightSound.
  destruct
    (StepsPhi_eq_from_left_right
      heap env rho e1 e2
      phi_left heap_left n1 phi_right heap_right n2 HLeft HRight)
    as (phi_eq & HEq & HList).
  exists phi_eq.
  split; [exact HEq |].
  eapply Correctness_soundness_ext_small_step_binary_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_eq_terminal_case :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta
    phi_eq heap_eq v_eq,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    StepsPhi (initial_state heap env rho (Eq e1 e2)) phi_eq
      (StDone heap_eq v_eq) ->
    phi_left ⋞ theta ->
    phi_right ⋞ theta ->
    phi_eq ⋞ theta.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta
    phi_eq heap_eq v_eq HLeft HRight HEq HLeftSound HRightSound.
  destruct
    (Correctness_soundness_ext_small_step_eq_composed_case
      heap env rho e1 e2
      phi_left heap_left n1 phi_right heap_right n2 theta
      HLeft HRight HLeftSound HRightSound)
    as (phi_eq_sound & HEqSoundSteps & HEqSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_eq_union_composed_case :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    exists phi_eq,
      StepsPhi (initial_state heap env rho (Eq e1 e2)) phi_eq
        (StDone heap_right (Bit (Nat.eqb n1 n2))) /\
      phi_eq ⋞ Union_Theta theta1 theta2.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
    HLeft HRight HLeftSound HRightSound.
  destruct
    (StepsPhi_eq_from_left_right
      heap env rho e1 e2
      phi_left heap_left n1 phi_right heap_right n2 HLeft HRight)
    as (phi_eq & HEq & HList).
  exists phi_eq.
  split; [exact HEq |].
  eapply Correctness_soundness_ext_small_step_binary_union_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_eq_union_terminal_case :
  forall heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
    phi_eq heap_eq v_eq,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    StepsPhi (initial_state heap env rho (Eq e1 e2)) phi_eq
      (StDone heap_eq v_eq) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    phi_eq ⋞ Union_Theta theta1 theta2.
Proof.
  intros heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
    phi_eq heap_eq v_eq HLeft HRight HEq HLeftSound HRightSound.
  destruct
    (Correctness_soundness_ext_small_step_eq_union_composed_case
      heap env rho e1 e2
      phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
      HLeft HRight HLeftSound HRightSound)
    as (phi_eq_sound & HEqSoundSteps & HEqSound).
  eapply Correctness_soundness_ext_small_step_terminal_transfer; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_eq_summary_terminal_case :
  forall heap env rho e1 e2 eff1 eff2
    phi_left heap_left n1 phi_right heap_right n2
    phi_left_summary heap_left_summary theta1
    phi_right_summary heap_right_summary theta2
    phi_summary heap_summary theta_summary
    phi_eq heap_eq v_eq,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    StepsPhi (initial_state heap env rho eff1) phi_left_summary
      (StDone heap_left_summary (Eff theta1)) ->
    StepsPhi (initial_state heap_left_summary env rho eff2) phi_right_summary
      (StDone heap_right_summary (Eff theta2)) ->
    StepsPhi (initial_state heap env rho (Concat eff1 eff2)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Eq e1 e2)) phi_eq
      (StDone heap_eq v_eq) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    phi_eq ⋞ theta_summary.
Proof.
  intros heap env rho e1 e2 eff1 eff2
    phi_left heap_left n1 phi_right heap_right n2
    phi_left_summary heap_left_summary theta1
    phi_right_summary heap_right_summary theta2
    phi_summary heap_summary theta_summary
    phi_eq heap_eq v_eq
    HLeft HRight HLeftSummary HRightSummary HSummary HEq
    HLeftSound HRightSound.
  pose proof
    (StepsPhi_concat_summary_terminal_theta
      heap env rho eff1 eff2
      phi_left_summary heap_left_summary theta1
      phi_right_summary heap_right_summary theta2
      phi_summary heap_summary theta_summary
      HLeftSummary HRightSummary HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_eq_union_terminal_case
    heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
	    phi_eq heap_eq v_eq); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_eq_summary_terminal_heterogeneous_case :
  forall heap heap_summary_start env rho e1 e2 eff1 eff2
    phi_left heap_left n1 phi_right heap_right n2
    phi_left_summary heap_left_summary theta1
    phi_right_summary heap_right_summary theta2
    phi_summary heap_summary theta_summary
    phi_eq heap_eq v_eq,
    StepsPhi (initial_state heap env rho e1) phi_left
      (StDone heap_left (Num n1)) ->
    StepsPhi (initial_state heap_left env rho e2) phi_right
      (StDone heap_right (Num n2)) ->
    StepsPhi (initial_state heap_summary_start env rho eff1) phi_left_summary
      (StDone heap_left_summary (Eff theta1)) ->
    StepsPhi (initial_state heap_left_summary env rho eff2) phi_right_summary
      (StDone heap_right_summary (Eff theta2)) ->
    StepsPhi (initial_state heap_summary_start env rho (Concat eff1 eff2))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Eq e1 e2)) phi_eq
      (StDone heap_eq v_eq) ->
    phi_left ⋞ theta1 ->
    phi_right ⋞ theta2 ->
    phi_eq ⋞ theta_summary.
Proof.
  intros heap heap_summary_start env rho e1 e2 eff1 eff2
    phi_left heap_left n1 phi_right heap_right n2
    phi_left_summary heap_left_summary theta1
    phi_right_summary heap_right_summary theta2
    phi_summary heap_summary theta_summary
    phi_eq heap_eq v_eq
    HLeft HRight HLeftSummary HRightSummary HSummary HEq
    HLeftSound HRightSound.
  pose proof
    (StepsPhi_concat_summary_terminal_theta
      heap_summary_start env rho eff1 eff2
      phi_left_summary heap_left_summary theta1
      phi_right_summary heap_right_summary theta2
      phi_summary heap_summary theta_summary
      HLeftSummary HRightSummary HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_eq_union_terminal_case
    heap env rho e1 e2
    phi_left heap_left n1 phi_right heap_right n2 theta1 theta2
    phi_eq heap_eq v_eq); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_eq_summary_terminal_direct_case :
  forall heap env rho e1 e2 eff1 eff2
    phi_eq heap_eq v_eq
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2,
    StepsPhi (initial_state heap env rho (Eq e1 e2)) phi_eq
      (StDone heap_eq v_eq) ->
    StepsPhi (initial_state heap env rho (Concat eff1 eff2)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    ReadOnlyPhi phi_summary ->
    (forall phi_left heap_left n1 phi_left_summary heap_left_summary theta1,
      StepsPhi (initial_state heap env rho e1) phi_left
        (StDone heap_left (Num n1)) ->
      StepsPhi (initial_state heap env rho eff1) phi_left_summary
        (StDone heap_left_summary (Eff theta1)) ->
      ReadOnlyPhi phi_left_summary ->
      phi_left ⋞ theta1) ->
    (forall phi_right heap_right n2 phi_right_summary heap_right_summary theta2,
      StepsPhi (initial_state heap env rho e2) phi_right
        (StDone heap_right (Num n2)) ->
      StepsPhi (initial_state heap env rho eff2) phi_right_summary
        (StDone heap_right_summary (Eff theta2)) ->
      ReadOnlyPhi phi_right_summary ->
      phi_right ⋞ theta2) ->
    phi_eq ⋞ theta_summary.
Proof.
  intros heap env rho e1 e2 eff1 eff2
    phi_eq heap_eq v_eq
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2
    HEq HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE1 HTcE2 HReadOnlyStatic1 HReadOnlySummary HLeftIH HRightIH.
  destruct
    (StepsPhi_eq_terminal_decompose
      heap env rho e1 e2 phi_eq heap_eq v_eq HEq)
    as (phi_left & heap_left & n1 & phi_right & heap_right & n2 &
        HLeft & HRight & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 eff2 phi_summary heap_summary theta_summary
      HSummary)
    as (phi_left_summary & heap_left_summary & theta1 &
        phi_right_summary & heap_right_summary & theta2 &
        HLeftSummary & HRightSummary & _ & HTheta & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyLeftSummary.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyRightSummary.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho e1 stty ctxt rgns ty_e1 static_e1
      phi_left heap_left (Num n1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcE1
      HLeft HReadOnlyStatic1) as HHeapLeft.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff1) phi_left_summary
      (StDone heap_left_summary (Eff theta1))
      HLeftSummary HReadOnlyLeftSummary) as HHeapLeftSummary.
  simpl in HHeapLeftSummary.
  subst heap_left.
  symmetry in HHeapLeftSummary.
  subst heap_left_summary.
  pose proof
    (HLeftIH
      phi_left heap n1 phi_left_summary heap theta1
      HLeft HLeftSummary HReadOnlyLeftSummary) as HLeftSound.
  pose proof
    (HRightIH
      phi_right heap_right n2 phi_right_summary heap_right_summary theta2
      HRight HRightSummary HReadOnlyRightSummary) as HRightSound.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_eq_union_terminal_case
    heap env rho e1 e2
    phi_left heap n1 phi_right heap_right n2 theta1 theta2
    phi_eq heap_eq v_eq); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_mu_abs_case :
  forall heap env rho f x ec ee phi heap' v theta,
    StepsPhi (initial_state heap env rho (Mu f x ec ee)) phi
      (StDone heap' v) ->
    phi ⋞ theta.
Proof.
  intros heap env rho f x ec ee phi heap' v theta HSteps.
  apply Phi_Theta_Soundness_of_phi_as_list_nil.
  eapply StepsPhi_initial_mu_terminal_trace_nil; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_rgn_abs_case :
  forall heap env rho x e phi heap' v theta,
    StepsPhi (initial_state heap env rho (Lambda x e)) phi
      (StDone heap' v) ->
    phi ⋞ theta.
Proof.
  intros heap env rho x e phi heap' v theta HSteps.
  apply Phi_Theta_Soundness_of_phi_as_list_nil.
  eapply StepsPhi_initial_lambda_terminal_trace_nil; eauto.
Qed.

Lemma TcExp_mu_abs_body_data :
  forall ctxt rgns f x ec ee tyx effc tyc effe rho_body,
    TcExp
      (ctxt, rgns, Mu f x ec ee,
        Ty_Arrow tyx effc tyc effe Ty_Effect, Empty_Static_Action) ->
    BackTriangle
      (update_rec_T
        (f, Ty_Arrow tyx effc tyc effe Ty_Effect) (x, tyx) ctxt,
        rgns, rho_body, ec, ee) /\
    TcExp
      (update_rec_T
        (f, Ty_Arrow tyx effc tyc effe Ty_Effect) (x, tyx) ctxt,
        rgns, ec, tyc, effc) /\
    TcExp
      (update_rec_T
        (f, Ty_Arrow tyx effc tyc effe Ty_Effect) (x, tyx) ctxt,
        rgns, ee, Ty_Effect, effe).
Proof.
  intros ctxt rgns f x ec ee tyx effc tyc effe rho_body HTcMu.
  inversion HTcMu; subst.
  repeat split; eauto.
Qed.

Lemma RuntimeValShape_mu_closure_body_data :
  forall stty ty env rho f x ec ee rho_body,
    RuntimeValShape stty ty (Cls (env, rho, Mu f x ec ee)) ->
    exists rgns ctxt tyx effc tyc effe,
      ty = subst_rho rho (Ty_Arrow tyx effc tyc effe Ty_Effect) /\
      TcRho (rho, rgns) /\
      TcInc (ctxt, rgns) /\
      TcEnv (stty, rho, env, ctxt) /\
      RuntimeEnvShape stty rho env ctxt /\
      TcExp
        (ctxt, rgns, Mu f x ec ee,
          Ty_Arrow tyx effc tyc effe Ty_Effect, Empty_Static_Action) /\
      BackTriangle
        (update_rec_T
          (f, Ty_Arrow tyx effc tyc effe Ty_Effect) (x, tyx) ctxt,
          rgns, rho_body, ec, ee) /\
      TcExp
        (update_rec_T
          (f, Ty_Arrow tyx effc tyc effe Ty_Effect) (x, tyx) ctxt,
          rgns, ec, tyc, effc) /\
      TcExp
        (update_rec_T
          (f, Ty_Arrow tyx effc tyc effe Ty_Effect) (x, tyx) ctxt,
          rgns, ee, Ty_Effect, effe).
Proof.
  intros stty ty env rho f x ec ee rho_body HShape.
  destruct
    (RuntimeValShape_mu_closure_inv
      stty ty env rho f x ec ee HShape)
    as (rgns & ctxt & tyx & effc & tyc & effe &
        HTy & HTcRho & HTcInc & HTcEnv & HEnvShape & HTcMu).
  destruct
    (TcExp_mu_abs_body_data
      ctxt rgns f x ec ee tyx effc tyc effe rho_body HTcMu)
    as (HBT & HTcBody & HTcSummary).
  exists rgns, ctxt, tyx, effc, tyc, effe.
  split; [exact HTy |].
  split; [exact HTcRho |].
  split; [exact HTcInc |].
  split; [exact HTcEnv |].
  split; [exact HEnvShape |].
  split; [exact HTcMu |].
  split; [exact HBT |].
  split; [exact HTcBody | exact HTcSummary].
Qed.

Lemma MuApp_body_context_from_readonly_terminals :
  forall heap env rho ef ea heap_fun heap_arg env_fun rho_fun f x ec ee v_arg
         phi_fun phi_arg stty ctxt rgns tya effc tyc effe static_ef static_ea,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp
      (ctxt, rgns, ef,
        Ty_Arrow tya effc tyc effe Ty_Effect, static_ef) ->
    TcExp (ctxt, rgns, ea, tya, static_ea) ->
    StepsPhi (initial_state heap env rho ef) phi_fun
      (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) ->
    StepsPhi (initial_state heap env rho ea) phi_arg
      (StDone heap_arg v_arg) ->
    ReadOnlyStatic (fold_subst_eps rho static_ef) ->
    ReadOnlyStatic (fold_subst_eps rho static_ea) ->
    exists rgns_body ctxt_body tyx_body effc_body tyc_body effe_body,
      heap_fun = heap /\
      heap_arg = heap /\
      TcRho (rho_fun, rgns_body) /\
      TcInc (ctxt_body, rgns_body) /\
      TcInc
        (update_rec_T
          (f, Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
          (x, tyx_body) ctxt_body,
          rgns_body) /\
      TcEnv
        (stty, rho_fun,
          update_rec_E
            (f, Cls (env_fun, rho_fun, Mu f x ec ee)) (x, v_arg) env_fun,
          update_rec_T
            (f, Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
            (x, tyx_body) ctxt_body) /\
      RuntimeEnvShape stty rho_fun
        (update_rec_E
          (f, Cls (env_fun, rho_fun, Mu f x ec ee)) (x, v_arg) env_fun)
        (update_rec_T
          (f, Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
          (x, tyx_body) ctxt_body) /\
      BackTriangle
        (update_rec_T
          (f, Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
          (x, tyx_body) ctxt_body,
          rgns_body, rho_fun, ec, ee) /\
      TcExp
        (update_rec_T
          (f, Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
          (x, tyx_body) ctxt_body,
          rgns_body, ec, tyc_body, effc_body) /\
      TcExp
        (update_rec_T
          (f, Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
          (x, tyx_body) ctxt_body,
          rgns_body, ee, Ty_Effect, effe_body).
Proof.
  intros heap env rho ef ea heap_fun heap_arg env_fun rho_fun f x ec ee v_arg
    phi_fun phi_arg stty ctxt rgns tya effc tyc effe static_ef static_ea
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEf HTcEa HFun HArg HReadOnlyEf HReadOnlyEa.
  destruct
    (StepsPhi_typed_readonly_terminal_value_typed_base
      heap env rho ef stty ctxt rgns
      (Ty_Arrow tya effc tyc effe Ty_Effect) static_ef
      phi_fun heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEf HFun
      HReadOnlyEf)
    as (HHeapFun & _ & HClosureShape).
  destruct
    (StepsPhi_typed_readonly_terminal_value_typed_base
      heap env rho ea stty ctxt rgns tya static_ea
      phi_arg heap_arg v_arg
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEa HArg
      HReadOnlyEa)
    as (HHeapArg & HArgVal & HArgShape).
  destruct
    (RuntimeValShape_mu_closure_body_data
      stty (subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))
      env_fun rho_fun f x ec ee rho_fun HClosureShape)
    as (rgns_body & ctxt_body & tyx_body & effc_body &
        tyc_body & effe_body & HClosureTy & HTcRhoBody & HTcIncBody &
        HTcEnvBodyBase & HEnvShapeBodyBase & HTcMuBody & HBTBody &
        HTcBody & HTcSummary).
  pose proof
    (subst_rho_arrow_arg_eq
      rho rho_fun tya effc tyc effe
      tyx_body effc_body tyc_body effe_body HClosureTy) as HArgTyEq.
  assert (HArgValBody :
    TcVal (stty, v_arg, subst_rho rho_fun tyx_body)).
  { rewrite <- HArgTyEq. exact HArgVal. }
  assert (HArgShapeBody :
    RuntimeValShape stty (subst_rho rho_fun tyx_body) v_arg).
  { rewrite <- HArgTyEq. exact HArgShape. }
  assert (HTcIncBodyUpdated :
    TcInc
      (update_rec_T
        (f, Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
        (x, tyx_body) ctxt_body,
        rgns_body)).
  {
    inversion HTcMuBody; subst.
    inversion HTcIncBody as [? ? HFrvBody]; subst.
    eapply ExtendedTcInv_2; eauto.
  }
  assert (HSelfVal :
    TcVal
      (stty, Cls (env_fun, rho_fun, Mu f x ec ee),
        subst_rho rho_fun
          (Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect))).
  {
    eapply TC_Cls with (rgns := rgns_body) (ctxt := ctxt_body); eauto.
  }
  assert (HSelfShape :
    RuntimeValShape stty
      (subst_rho rho_fun
        (Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect))
      (Cls (env_fun, rho_fun, Mu f x ec ee))).
  {
    eapply RVS_Arrow with (rgns := rgns_body) (ctxt := ctxt_body);
      eauto.
  }
  exists rgns_body, ctxt_body, tyx_body, effc_body, tyc_body, effe_body.
  split; [exact HHeapFun |].
  split; [exact HHeapArg |].
  split; [exact HTcRhoBody |].
  split; [exact HTcIncBody |].
  split; [exact HTcIncBodyUpdated |].
  split.
  { eapply TcEnv_update_rec; eauto. }
  split.
  { eapply RuntimeEnvShape_update_rec; eauto. }
  split; [exact HBTBody |].
  split; [exact HTcBody | exact HTcSummary].
Qed.

Lemma MuApp_body_context_from_mixed_readonly_terminals :
  forall heap env rho ef ea heap_fun heap_arg env_fun rho_fun f x ec ee v_arg
         phi_fun phi_arg stty ctxt rgns tya effc tyc effe
         static_ef_shape static_ea_shape
         ty_ef_readonly static_ef_readonly
         ty_ea_readonly static_ea_readonly,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp
      (ctxt, rgns, ef,
        Ty_Arrow tya effc tyc effe Ty_Effect, static_ef_shape) ->
    TcExp (ctxt, rgns, ea, tya, static_ea_shape) ->
    TcExp (ctxt, rgns, ef, ty_ef_readonly, static_ef_readonly) ->
    TcExp (ctxt, rgns, ea, ty_ea_readonly, static_ea_readonly) ->
    StepsPhi (initial_state heap env rho ef) phi_fun
      (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) ->
    StepsPhi (initial_state heap env rho ea) phi_arg
      (StDone heap_arg v_arg) ->
    ReadOnlyStatic (fold_subst_eps rho static_ef_readonly) ->
    ReadOnlyStatic (fold_subst_eps rho static_ea_readonly) ->
    exists rgns_body ctxt_body tyx_body effc_body tyc_body effe_body,
      heap_fun = heap /\
      heap_arg = heap /\
      TcRho (rho_fun, rgns_body) /\
      TcInc (ctxt_body, rgns_body) /\
      TcInc
        (update_rec_T
          (f, Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
          (x, tyx_body) ctxt_body,
          rgns_body) /\
      TcEnv
        (stty, rho_fun,
          update_rec_E
            (f, Cls (env_fun, rho_fun, Mu f x ec ee)) (x, v_arg) env_fun,
          update_rec_T
            (f, Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
            (x, tyx_body) ctxt_body) /\
      RuntimeEnvShape stty rho_fun
        (update_rec_E
          (f, Cls (env_fun, rho_fun, Mu f x ec ee)) (x, v_arg) env_fun)
        (update_rec_T
          (f, Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
          (x, tyx_body) ctxt_body) /\
      BackTriangle
        (update_rec_T
          (f, Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
          (x, tyx_body) ctxt_body,
          rgns_body, rho_fun, ec, ee) /\
      TcExp
        (update_rec_T
          (f, Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
          (x, tyx_body) ctxt_body,
          rgns_body, ec, tyc_body, effc_body) /\
      TcExp
        (update_rec_T
          (f, Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
          (x, tyx_body) ctxt_body,
          rgns_body, ee, Ty_Effect, effe_body).
Proof.
  intros heap env rho ef ea heap_fun heap_arg env_fun rho_fun f x ec ee v_arg
    phi_fun phi_arg stty ctxt rgns tya effc tyc effe
    static_ef_shape static_ea_shape
    ty_ef_readonly static_ef_readonly
    ty_ea_readonly static_ea_readonly
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEfShape HTcEaShape HTcEfReadonly HTcEaReadonly
    HFun HArg HReadOnlyEf HReadOnlyEa.
  destruct
    (StepsPhi_mixed_readonly_terminal_value_typed_base
      heap env rho ef stty ctxt rgns
      (Ty_Arrow tya effc tyc effe Ty_Effect) static_ef_shape
      ty_ef_readonly static_ef_readonly
      phi_fun heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEfShape HTcEfReadonly HFun HReadOnlyEf)
    as (HHeapFun & _ & HClosureShape).
  destruct
    (StepsPhi_mixed_readonly_terminal_value_typed_base
      heap env rho ea stty ctxt rgns tya static_ea_shape
      ty_ea_readonly static_ea_readonly
      phi_arg heap_arg v_arg
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEaShape HTcEaReadonly HArg HReadOnlyEa)
    as (HHeapArg & HArgVal & HArgShape).
  destruct
    (RuntimeValShape_mu_closure_body_data
      stty (subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))
      env_fun rho_fun f x ec ee rho_fun HClosureShape)
    as (rgns_body & ctxt_body & tyx_body & effc_body &
        tyc_body & effe_body & HClosureTy & HTcRhoBody & HTcIncBody &
        HTcEnvBodyBase & HEnvShapeBodyBase & HTcMuBody & HBTBody &
        HTcBody & HTcSummary).
  pose proof
    (subst_rho_arrow_arg_eq
      rho rho_fun tya effc tyc effe
      tyx_body effc_body tyc_body effe_body HClosureTy) as HArgTyEq.
  assert (HArgValBody :
    TcVal (stty, v_arg, subst_rho rho_fun tyx_body)).
  { rewrite <- HArgTyEq. exact HArgVal. }
  assert (HArgShapeBody :
    RuntimeValShape stty (subst_rho rho_fun tyx_body) v_arg).
  { rewrite <- HArgTyEq. exact HArgShape. }
  assert (HTcIncBodyUpdated :
    TcInc
      (update_rec_T
        (f, Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
        (x, tyx_body) ctxt_body,
        rgns_body)).
  {
    inversion HTcMuBody; subst.
    inversion HTcIncBody as [? ? HFrvBody]; subst.
    eapply ExtendedTcInv_2; eauto.
  }
  assert (HSelfVal :
    TcVal
      (stty, Cls (env_fun, rho_fun, Mu f x ec ee),
        subst_rho rho_fun
          (Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect))).
  {
    eapply TC_Cls with (rgns := rgns_body) (ctxt := ctxt_body); eauto.
  }
  assert (HSelfShape :
    RuntimeValShape stty
      (subst_rho rho_fun
        (Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect))
      (Cls (env_fun, rho_fun, Mu f x ec ee))).
  {
    eapply RVS_Arrow with (rgns := rgns_body) (ctxt := ctxt_body);
      eauto.
  }
  exists rgns_body, ctxt_body, tyx_body, effc_body, tyc_body, effe_body.
  split; [exact HHeapFun |].
  split; [exact HHeapArg |].
  split; [exact HTcRhoBody |].
  split; [exact HTcIncBody |].
  split; [exact HTcIncBodyUpdated |].
  split.
  { eapply TcEnv_update_rec; eauto. }
  split.
  { eapply RuntimeEnvShape_update_rec; eauto. }
  split; [exact HBTBody |].
  split; [exact HTcBody | exact HTcSummary].
Qed.

Theorem Correctness_soundness_ext_small_step_mu_app_summary_terminal_recursive_case :
  forall heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns tya effc tyc effe static_ef static_ea,
    StepsPhi (initial_state heap env rho (Mu_App ef ea)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho (Eff_App ef ea)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp
      (ctxt, rgns, ef,
        Ty_Arrow tya effc tyc effe Ty_Effect, static_ef) ->
    TcExp (ctxt, rgns, ea, tya, static_ea) ->
    ReadOnlyStatic (fold_subst_eps rho static_ef) ->
    ReadOnlyStatic (fold_subst_eps rho static_ea) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ef, Eff_App ef ea) ->
    BackTriangle (ctxt, rgns, rho, ea, Eff_App ef ea) ->
    (forall heap env rho ea ee phi heap' v
            phi_summary heap_summary theta_summary
            stty ctxt rgns ty static,
      BackTriangle (ctxt, rgns, rho, ea, ee) ->
      StepsPhi (initial_state heap env rho ea) phi
        (StDone heap' v) ->
      StepsPhi (initial_state heap env rho ee) phi_summary
        (StDone heap_summary (Eff theta_summary)) ->
      ReadOnlyPhi phi_summary ->
      TcHeap (heap, stty) ->
      RuntimeHeapShape heap stty ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, ea, ty, static) ->
      phi ⋞ theta_summary) ->
    phi_app ⋞ theta_summary.
Proof.
  intros heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns tya effc tyc effe static_ef static_ea
    HApp HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEf HTcEa HReadOnlyStaticEf HReadOnlyStaticEa HReadOnlySummary
    HBTFun HBTArg HRecursive.
  destruct
    (StepsPhi_mu_app_terminal_decompose
      heap env rho ef ea phi_app heap_app v_app HApp)
    as (env_fun & rho_fun & f & x & ec & ee &
        phi_fun & heap_fun & phi_arg & heap_arg & v_arg &
        phi_body & HFun & HArg & HBody & _).
  destruct
    (StepsPhi_eff_app_terminal_decompose
      heap env rho ef ea phi_summary heap_summary (Eff theta_summary)
      HSummary)
    as (env_fun_summary & rho_fun_summary & f_summary & x_summary &
        ec_summary & ee_summary &
        phi_fun_summary & heap_fun_summary &
        phi_arg_summary & heap_arg_summary & v_arg_summary &
        phi_body_summary &
        HFunSummary & HArgSummary & HBodySummary & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list3_right
      phi_summary phi_fun_summary phi_arg_summary phi_body_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyBodySummary.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ef stty ctxt rgns
      (Ty_Arrow tya effc tyc effe Ty_Effect) static_ef
      phi_fun heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEf HFun
      HReadOnlyStaticEf) as HHeapFun.
  subst heap_fun.
  destruct
    (StepsPhi_terminal_deterministic
      (initial_state heap env rho ef)
      phi_fun heap (Cls (env_fun, rho_fun, Mu f x ec ee))
      phi_fun_summary heap_fun_summary
        (Cls (env_fun_summary, rho_fun_summary,
          Mu f_summary x_summary ec_summary ee_summary))
      HFun HFunSummary)
    as [_ [HHeapFunSummary HClosureEq]].
  symmetry in HHeapFunSummary.
  subst heap_fun_summary.
  inversion HClosureEq; subst.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ea stty ctxt rgns tya static_ea
      phi_arg heap_arg v_arg
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEa HArg
      HReadOnlyStaticEa) as HHeapArg.
  subst heap_arg.
  destruct
    (StepsPhi_terminal_deterministic
      (initial_state heap env rho ea)
      phi_arg heap v_arg
      phi_arg_summary heap_arg_summary v_arg_summary
      HArg HArgSummary)
    as [_ [HHeapArgSummary HArgEq]].
  symmetry in HHeapArgSummary.
  subst heap_arg_summary.
  subst v_arg_summary.
  destruct
    (MuApp_body_context_from_readonly_terminals
      heap env rho ef ea heap heap env_fun_summary rho_fun_summary
      f_summary x_summary ec_summary ee_summary v_arg
      phi_fun phi_arg stty ctxt rgns tya effc tyc effe static_ef static_ea
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEf HTcEa
      HFun HArg HReadOnlyStaticEf HReadOnlyStaticEa)
    as (rgns_body & ctxt_body & tyx_body & effc_body & tyc_body &
        effe_body & _ & _ & HTcRhoBody & _ & HTcIncBodyUpdated &
        HTcEnvBody & HEnvShapeBody & HBTBody & HTcBody & _).
  pose proof
    (HRecursive
      heap env rho ef (Eff_App ef ea)
      phi_fun heap (Cls (env_fun_summary, rho_fun_summary,
        Mu f_summary x_summary ec_summary ee_summary))
      phi_summary heap_summary theta_summary
      stty ctxt rgns
      (Ty_Arrow tya effc tyc effe Ty_Effect) static_ef
      HBTFun HFun HSummary HReadOnlySummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEf)
    as HFunSound.
  pose proof
    (HRecursive
      heap env rho ea (Eff_App ef ea)
      phi_arg heap v_arg
      phi_summary heap_summary theta_summary
      stty ctxt rgns tya static_ea
      HBTArg HArg HSummary HReadOnlySummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEa)
    as HArgSound.
  pose proof
    (HRecursive
      heap
      (update_rec_E
        (f_summary,
          Cls (env_fun_summary, rho_fun_summary,
            Mu f_summary x_summary ec_summary ee_summary))
      (x_summary, v_arg) env_fun_summary)
      rho_fun_summary ec_summary ee_summary
      phi_body heap_app v_app
      phi_body_summary heap_summary theta_summary
      stty
      (update_rec_T
        (f_summary,
          Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
        (x_summary, tyx_body) ctxt_body)
      rgns_body tyc_body effc_body
      HBTBody HBody HBodySummary HReadOnlyBodySummary
      HTcHeap HHeapShape HTcRhoBody HTcIncBodyUpdated HTcEnvBody HEnvShapeBody
      HTcBody)
    as HBodySound.
  eapply (Correctness_soundness_ext_small_step_mu_app_summary_terminal_case
    heap env rho ef ea env_fun_summary rho_fun_summary
    f_summary x_summary ec_summary ee_summary
    phi_fun heap phi_arg heap v_arg
    phi_body heap_app v_app
    phi_body_summary heap_summary theta_summary
    phi_summary heap_summary theta_summary
    phi_app heap_app v_app); eauto.
Qed.

Lemma TcExp_lambda_body_data :
  forall ctxt rgns x eb effr_closed tyr_closed rho_body,
    TcExp
      (ctxt, rgns, Lambda x eb,
        Ty_ForallRgn effr_closed tyr_closed, Empty_Static_Action) ->
    exists effr_body tyr_body,
      not_set_elem rgns x /\
      BackTriangle
        (ctxt, set_union rgns (singleton_set x), rho_body, eb, Empty) /\
      TcExp
        (ctxt, set_union rgns (singleton_set x),
          eb, tyr_body, effr_body).
Proof.
  intros ctxt rgns x eb effr_closed tyr_closed rho_body HTcLambda.
  inversion HTcLambda; subst.
  exists effr, tyr.
  repeat split; eauto.
Qed.

Lemma RuntimeValShape_lambda_closure_body_data :
  forall stty ty env rho x eb rho_body,
    RuntimeValShape stty ty (Cls (env, rho, Lambda x eb)) ->
    exists rgns ctxt effr_closed tyr_closed effr_body tyr_body,
      ty = subst_rho rho (Ty_ForallRgn effr_closed tyr_closed) /\
      TcRho (rho, rgns) /\
      TcInc (ctxt, rgns) /\
      TcEnv (stty, rho, env, ctxt) /\
      RuntimeEnvShape stty rho env ctxt /\
      not_set_elem rgns x /\
      TcExp
        (ctxt, rgns, Lambda x eb,
          Ty_ForallRgn effr_closed tyr_closed, Empty_Static_Action) /\
      BackTriangle
        (ctxt, set_union rgns (singleton_set x), rho_body, eb, Empty) /\
      TcExp
        (ctxt, set_union rgns (singleton_set x),
          eb, tyr_body, effr_body).
Proof.
  intros stty ty env rho x eb rho_body HShape.
  destruct
    (RuntimeValShape_lambda_closure_inv
      stty ty env rho x eb HShape)
    as (rgns & ctxt & effr_closed & tyr_closed &
        HTy & HTcRho & HTcInc & HTcEnv & HEnvShape & HTcLambda).
  destruct
    (TcExp_lambda_body_data
      ctxt rgns x eb effr_closed tyr_closed rho_body HTcLambda)
    as (effr_body & tyr_body & HFresh & HBTBody & HTcBody).
  exists rgns, ctxt, effr_closed, tyr_closed, effr_body, tyr_body.
  split; [exact HTy |].
  split; [exact HTcRho |].
  split; [exact HTcInc |].
  split; [exact HTcEnv |].
  split; [exact HEnvShape |].
  split; [exact HFresh |].
  split; [exact HTcLambda |].
  split; [exact HBTBody | exact HTcBody].
Qed.

Lemma RgnApp_body_context_from_terminal :
  forall heap env rho er heap_fun env_fun rho_fun x eb w r
         phi_fun stty ctxt rgns effr tyr static_er,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp
      (ctxt, rgns, er, Ty_ForallRgn effr tyr, static_er) ->
    StepsPhi (initial_state heap env rho er) phi_fun
      (StDone heap_fun (Cls (env_fun, rho_fun, Lambda x eb))) ->
    find_R w rho = Some r ->
    exists stty_fun rgns_body ctxt_body effr_body tyr_body,
      StoreExtends stty stty_fun /\
      TcHeap (heap_fun, stty_fun) /\
      RuntimeHeapShape heap_fun stty_fun /\
      TcRho
        (update_R (x, r) rho_fun,
          set_union rgns_body (singleton_set x)) /\
      TcInc (ctxt_body, set_union rgns_body (singleton_set x)) /\
      TcEnv (stty_fun, update_R (x, r) rho_fun, env_fun, ctxt_body) /\
      RuntimeEnvShape stty_fun (update_R (x, r) rho_fun) env_fun ctxt_body /\
      BackTriangle
        (ctxt_body, set_union rgns_body (singleton_set x),
          update_R (x, r) rho_fun, eb, Empty) /\
      TcExp
        (ctxt_body, set_union rgns_body (singleton_set x),
          eb, tyr_body, effr_body).
Proof.
  intros heap env rho er heap_fun env_fun rho_fun x eb w r
    phi_fun stty ctxt rgns effr tyr static_er
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEr HFun HFind.
  destruct
    (StepsPhi_initial_terminal_value_typed
      heap env rho er stty ctxt rgns
      (Ty_ForallRgn effr tyr) static_er
      phi_fun heap_fun (Cls (env_fun, rho_fun, Lambda x eb))
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEr HFun)
    as (stty_fun & HExt & HTcHeapFun & HHeapShapeFun & _ &
        HClosureShape).
  destruct
    (RuntimeValShape_lambda_closure_body_data
      stty_fun (subst_rho rho (Ty_ForallRgn effr tyr))
      env_fun rho_fun x eb (update_R (x, r) rho_fun) HClosureShape)
    as (rgns_body & ctxt_body & effr_closed & tyr_closed &
        effr_body & tyr_body & _ & HTcRhoBody & HTcIncBody &
        HTcEnvBodyBase & HEnvShapeBodyBase & HFreshBody & _ &
        HBTBody & HTcBody).
  exists stty_fun, rgns_body, ctxt_body, effr_body, tyr_body.
  split; [exact HExt |].
  split; [exact HTcHeapFun |].
  split; [exact HHeapShapeFun |].
  split.
  { eapply update_rho; eauto. }
  split.
  { eapply TcInc_extend_rgn_singleton; eauto. }
  split.
  { eapply extended_rho; eauto. }
  split.
  { eapply RuntimeEnvShape_extended_rho; eauto. }
  split; [exact HBTBody | exact HTcBody].
Qed.

Theorem Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_recursive_case :
  forall heap env rho er w
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns effr tyr static_er,
    StepsPhi (initial_state heap env rho (Rgn_App er w)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho Empty) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, er, Ty_ForallRgn effr tyr, static_er) ->
    BackTriangle (ctxt, rgns, rho, er, Empty) ->
    (forall heap env rho ea ee phi heap' v
            phi_summary heap_summary theta_summary
            stty ctxt rgns ty static,
      BackTriangle (ctxt, rgns, rho, ea, ee) ->
      StepsPhi (initial_state heap env rho ea) phi
        (StDone heap' v) ->
      StepsPhi (initial_state heap env rho ee) phi_summary
        (StDone heap_summary (Eff theta_summary)) ->
      ReadOnlyPhi phi_summary ->
      TcHeap (heap, stty) ->
      RuntimeHeapShape heap stty ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, ea, ty, static) ->
      phi ⋞ theta_summary) ->
    phi_app ⋞ theta_summary.
Proof.
  intros heap env rho er w
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns effr tyr static_er
    HApp HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEr HBTFun HRecursive.
  destruct
    (StepsPhi_rgn_app_terminal_decompose
      heap env rho er w phi_app heap_app v_app HApp)
    as (env_fun & rho_fun & x & eb & r &
        phi_fun & heap_fun & phi_body &
        HFun & HFind & HBody & _).
  destruct
    (StepsPhi_initial_empty_terminal
      heap env rho phi_summary heap_summary theta_summary HSummary)
    as (HSummaryNil & _ & HTheta).
  pose proof
    (ReadOnlyPhi_of_phi_as_list_nil phi_summary HSummaryNil)
    as HReadOnlySummary.
  subst theta_summary.
  destruct
    (RgnApp_body_context_from_terminal
      heap env rho er heap_fun env_fun rho_fun x eb w r
      phi_fun stty ctxt rgns effr tyr static_er
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEr
      HFun HFind)
    as (stty_fun & rgns_body & ctxt_body & effr_body & tyr_body &
        HExtFun & HTcHeapFun & HHeapShapeFun & HTcRhoBody &
        HTcIncBody & HTcEnvBody & HEnvShapeBody & HBTBody & HTcBody).
  pose proof
    (HRecursive
      heap env rho er Empty
      phi_fun heap_fun (Cls (env_fun, rho_fun, Lambda x eb))
      phi_summary heap_summary Theta_Empty
      stty ctxt rgns (Ty_ForallRgn effr tyr) static_er
      HBTFun HFun HSummary HReadOnlySummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEr)
    as HFunSound.
  pose proof
    (initial_empty_steps_phi_done
      heap_fun env_fun (update_R (x, r) rho_fun))
    as HBodySummary.
  assert (HReadOnlyBodySummary :
    ReadOnlyPhi
      (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))).
  {
    apply ReadOnlyPhi_of_phi_as_list_nil.
    reflexivity.
  }
  pose proof
    (HRecursive
      heap_fun env_fun (update_R (x, r) rho_fun) eb Empty
      phi_body heap_app v_app
      (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))
      heap_fun Theta_Empty
      stty_fun ctxt_body (set_union rgns_body (singleton_set x))
      tyr_body effr_body
      HBTBody HBody HBodySummary HReadOnlyBodySummary
      HTcHeapFun HHeapShapeFun HTcRhoBody HTcIncBody HTcEnvBody
      HEnvShapeBody HTcBody)
    as HBodySound.
  eapply (Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_case
    heap env rho er w env_fun rho_fun x eb r
    phi_fun heap_fun phi_body heap_app v_app
    phi_summary heap_summary Theta_Empty
    phi_app heap_app v_app); eauto.
Qed.

Definition SmallStepCorrectnessRecursivePremise : Prop :=
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    phi ⋞ theta_summary.

Definition SmallStepCorrectnessHeterogeneousRecursivePremise : Prop :=
  forall heap heap_summary_start env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap_summary_start env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    phi ⋞ theta_summary.

Definition SmallStepCorrectnessHeterogeneousRecursivePremiseBelow
    (n_parent : nat) : Prop :=
  forall n heap heap_summary_start env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    n < n_parent ->
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhiN n (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap_summary_start env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    phi ⋞ theta_summary.

Inductive RuntimeBackTriangleSummary :
    Gamma -> Omega -> Rho -> Expr -> Expr -> Prop :=
| RBTS_Sequential :
    forall ctxt rgns rho e eff,
      SequentialHead e ->
      BackTriangle (ctxt, rgns, rho, e, eff) ->
      RuntimeBackTriangleSummary ctxt rgns rho e eff
| RBTS_PairParCanonical :
    forall ctxt rgns rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4,
      BackTriangle
        (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
         (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
      RuntimeBackTriangleSummary ctxt rgns rho
        (Pair_Par ef1 ea1 ef2 ea2)
        ((eff1 ⊕ eff2) ⊕ (Eff_App ef1 ea1 ⊕ Eff_App ef2 ea2))
| RBTS_Top :
    forall ctxt rgns rho e,
      RuntimeBackTriangleSummary ctxt rgns rho e Top.

Definition RuntimeBackTriangleCorrectnessPremiseBelow
    (n_parent : nat) : Prop :=
  forall n heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    n < n_parent ->
    RuntimeBackTriangleSummary ctxt rgns rho ea ee ->
    StepsPhiN n (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    phi ⋞ theta_summary.

Definition PairParCanonicalFallback
    (heap : Heap) (env : Env) (rho : Rho) (e : Expr) : Prop :=
  exists ef1 ea1 ef2 ea2 phi_eff1 theta1 phi_eff2 theta2,
    e = Pair_Par ef1 ea1 ef2 ea2 /\
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap (Eff theta1)) /\
    StepsPhi (initial_state heap env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap (Eff theta2)) /\
    PairParCheckFail theta1 theta2.

Definition HeterogeneousHeapForExpr
    (env : Env) (rho : Rho) (e : Expr)
    (heap_actual heap_summary : Heap) : Prop :=
  forall phi_actual heap_actual' v,
    StepsPhi (initial_state heap_actual env rho e) phi_actual
      (StDone heap_actual' v) ->
    ReadOnlyPhi phi_actual ->
    HeterogeneousHeapForPhi phi_actual heap_actual heap_summary /\
    exists phi_summary heap_summary',
      StepsPhi (initial_state heap_summary env rho e) phi_summary
        (StDone heap_summary' v) /\
      phi_as_list phi_summary = phi_as_list phi_actual.

Definition HeapEquivalentForExpr
    (env : Env) (rho : Rho) (e : Expr)
    (heap_actual heap_summary : Heap) : Prop :=
  HeterogeneousHeapForExpr env rho e heap_actual heap_summary.

Definition SummaryReplayCompatibleForExpr
    (env : Env) (rho : Rho) (e : Expr)
    (heap_actual heap_summary : Heap) : Prop :=
  forall phi_summary heap_summary' v,
    StepsPhi (initial_state heap_summary env rho e) phi_summary
      (StDone heap_summary' v) ->
    ReadOnlyPhi phi_summary ->
    HeterogeneousHeapForPhi phi_summary heap_summary heap_actual /\
    StepsPhi (initial_state heap_actual env rho e) phi_summary
      (StDone heap_actual v).

Definition PairParBranchHeapCompatible
    (heap : Heap) (env : Env) (rho : Rho)
    (ef1 ea1 ef2 ea2 : Expr) : Prop :=
  forall phi_mu1 heap_mu1 v1,
    StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    HeterogeneousHeapForExpr env rho (Mu_App ef2 ea2) heap_mu1 heap.

Definition PairParBranchHeapEquivalent
    (heap : Heap) (env : Env) (rho : Rho)
    (ef1 ea1 ef2 ea2 : Expr) : Prop :=
  forall phi_mu1 heap_mu1 v1,
    StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    HeapEquivalentForExpr env rho (Mu_App ef2 ea2) heap_mu1 heap.

Definition PairParBranchHeapCompatibleRecursivePremise : Prop :=
  forall heap env rho ef1 ea1 ef2 ea2,
    PairParBranchHeapCompatible heap env rho ef1 ea1 ef2 ea2.

Definition PairParBranchHeapEquivalentRecursivePremise : Prop :=
  forall heap env rho ef1 ea1 ef2 ea2,
    PairParBranchHeapEquivalent heap env rho ef1 ea1 ef2 ea2.

Definition PairParBranchTraceDisjoint
    (heap : Heap) (env : Env) (rho : Rho)
    (ef1 ea1 ef2 ea2 : Expr) : Prop :=
  forall phi_mu1 heap_mu1 v1 phi_mu2 heap_mu2 v2,
    StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    ReadOnlyPhi phi_mu2 ->
    Disjoint_Traces (phi_as_list phi_mu1) (phi_as_list phi_mu2).

Definition PairParBranchTraceDisjointRecursivePremise : Prop :=
  forall heap env rho ef1 ea1 ef2 ea2,
    PairParBranchTraceDisjoint heap env rho ef1 ea1 ef2 ea2.

Definition PairParBranchSummaryReplayCompatible
    (heap : Heap) (env : Env) (rho : Rho)
    (ef1 ea1 summary2 : Expr) : Prop :=
  forall phi_mu1 heap_mu1 v1,
    StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    SummaryReplayCompatibleForExpr env rho summary2 heap_mu1 heap.

Definition PairParBranchSummaryReplayCompatibleRecursivePremise : Prop :=
  forall heap env rho ef1 ea1 summary2,
    PairParBranchSummaryReplayCompatible heap env rho ef1 ea1 summary2.

Definition PairParBranchSummaryTraceDisjoint
    (heap : Heap) (env : Env) (rho : Rho)
    (ef1 ea1 summary2 : Expr) : Prop :=
  forall phi_mu1 heap_mu1 v1 phi_summary heap_summary v_summary,
    StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap env rho summary2) phi_summary
      (StDone heap_summary v_summary) ->
    ReadOnlyPhi phi_summary ->
    Disjoint_Traces (phi_as_list phi_mu1) (phi_as_list phi_summary).

Definition SmallStepCorrectnessHeapCompatibleRecursivePremise : Prop :=
  forall heap heap_summary_start env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    HeterogeneousHeapForExpr env rho ea heap heap_summary_start ->
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap_summary_start env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    phi ⋞ theta_summary.

Definition SmallStepCorrectnessSummaryReplayRecursivePremise : Prop :=
  forall heap heap_summary_start env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    SummaryReplayCompatibleForExpr env rho ee heap heap_summary_start ->
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap_summary_start env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    phi ⋞ theta_summary.

Definition SmallStepCorrectnessSummaryReplayRecursivePremiseBelow
    (n_parent : nat) : Prop :=
  forall n heap heap_summary_start env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    n < n_parent ->
    SummaryReplayCompatibleForExpr env rho ee heap heap_summary_start ->
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhiN n (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap_summary_start env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    phi ⋞ theta_summary.

Definition SmallStepCorrectnessHeapEquivalentRecursivePremise : Prop :=
  forall heap heap_summary_start env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    HeapEquivalentForExpr env rho ea heap heap_summary_start ->
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap_summary_start env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    phi ⋞ theta_summary.

Definition SmallStepCorrectnessLookupEquivalentRecursivePremise : Prop :=
  forall heap heap_summary_start env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    HeapLookupEquivalent heap heap_summary_start ->
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap_summary_start env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    phi ⋞ theta_summary.

Definition SmallStepCorrectnessLookupEquivalentRecursivePremiseBelow
    (n_parent : nat) : Prop :=
  forall n heap heap_summary_start env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    n < n_parent ->
    HeapLookupEquivalent heap heap_summary_start ->
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhiN n (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap_summary_start env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    phi ⋞ theta_summary.

Lemma HeterogeneousHeapForExpr_from_readonly_replay :
  forall env rho e heap_actual heap_summary,
    (forall phi_actual heap_actual' v,
      StepsPhi (initial_state heap_actual env rho e) phi_actual
        (StDone heap_actual' v) ->
      ReadOnlyPhi phi_actual ->
      HeterogeneousHeapForPhi phi_actual heap_actual heap_summary) ->
    HeterogeneousHeapForExpr env rho e heap_actual heap_summary.
Proof.
  intros env rho e heap_actual heap_summary HAgree
    phi_actual heap_actual' v HSteps HReadOnly.
  pose proof
    (HAgree phi_actual heap_actual' v HSteps HReadOnly) as HFootprint.
  split; [exact HFootprint |].
  exists phi_actual, heap_summary.
  split; [| reflexivity].
  exact
    (StepsPhi_readonly_replay_on_heap_agreement
      (initial_state heap_actual env rho e)
      phi_actual
      (StDone heap_actual' v)
      heap_summary
	      HSteps HReadOnly HFootprint).
Qed.

Lemma HeapEquivalentForExpr_from_readonly_replay :
  forall env rho e heap_actual heap_summary,
    (forall phi_actual heap_actual' v,
      StepsPhi (initial_state heap_actual env rho e) phi_actual
        (StDone heap_actual' v) ->
      ReadOnlyPhi phi_actual ->
      HeapEquivalentOnPhi phi_actual heap_actual heap_summary) ->
    HeapEquivalentForExpr env rho e heap_actual heap_summary.
Proof.
  intros env rho e heap_actual heap_summary HAgree.
  unfold HeapEquivalentForExpr.
  apply HeterogeneousHeapForExpr_from_readonly_replay.
  intros phi_actual heap_actual' v HSteps HReadOnly.
  unfold HeapEquivalentOnPhi, HeapEquivalentOn.
  eapply HAgree; eauto.
Qed.

Lemma HeapLookupEquivalent_implies_HeapEquivalentForExpr :
  forall env rho e heap_actual heap_summary,
    HeapLookupEquivalent heap_actual heap_summary ->
    HeapEquivalentForExpr env rho e heap_actual heap_summary.
Proof.
  intros env rho e heap_actual heap_summary HLookup.
  apply HeapEquivalentForExpr_from_readonly_replay.
  intros phi_actual heap_actual' v _ _.
  apply HeapLookupEquivalent_implies_HeapEquivalentOnPhi.
  exact HLookup.
Qed.

Lemma SummaryReplayCompatibleForExpr_from_readonly_replay :
  forall env rho e heap_actual heap_summary,
    (forall phi_summary heap_summary' v,
      StepsPhi (initial_state heap_summary env rho e) phi_summary
        (StDone heap_summary' v) ->
      ReadOnlyPhi phi_summary ->
      HeterogeneousHeapForPhi phi_summary heap_summary heap_actual) ->
    SummaryReplayCompatibleForExpr env rho e heap_actual heap_summary.
Proof.
  intros env rho e heap_actual heap_summary HAgree
    phi_summary heap_summary' v HSteps HReadOnly.
  pose proof
    (HAgree phi_summary heap_summary' v HSteps HReadOnly) as HFootprint.
  split; [exact HFootprint |].
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap_summary env rho e) phi_summary
      (StDone heap_summary' v) HSteps HReadOnly) as HHeapSummary.
  simpl in HHeapSummary.
  subst heap_summary'.
  pose proof
    (StepsPhi_readonly_replay_on_heap_agreement
      (initial_state heap_summary env rho e)
      phi_summary
      (StDone heap_summary v)
      heap_actual
      HSteps HReadOnly HFootprint) as HReplay.
  simpl in HReplay.
  exact HReplay.
Qed.

Lemma SummaryReplayCompatibleForExpr_refl :
  forall env rho e heap,
    SummaryReplayCompatibleForExpr env rho e heap heap.
Proof.
  intros env rho e heap.
  apply SummaryReplayCompatibleForExpr_from_readonly_replay.
  intros phi_summary heap_summary' v _ _.
  apply HeterogeneousHeapForPhi_refl.
Qed.

Lemma HeapLookupEquivalent_implies_SummaryReplayCompatibleForExpr :
  forall env rho e heap_actual heap_summary,
    HeapLookupEquivalent heap_actual heap_summary ->
    SummaryReplayCompatibleForExpr env rho e heap_actual heap_summary.
Proof.
  intros env rho e heap_actual heap_summary HLookup.
  apply SummaryReplayCompatibleForExpr_from_readonly_replay.
  intros phi_summary heap_summary' v _ _.
  apply HeterogeneousHeapForPhi_sym.
  apply HeapLookupEquivalent_implies_HeapEquivalentOnPhi.
  exact HLookup.
Qed.

Lemma SummaryReplayCompatibleForExpr_from_disjoint_writer :
  forall heap env rho writer summary phi_writer heap_writer' v_writer,
    StepsPhi (initial_state heap env rho writer) phi_writer
      (StDone heap_writer' v_writer) ->
    (forall phi_summary heap_summary' v_summary,
      StepsPhi (initial_state heap env rho summary) phi_summary
        (StDone heap_summary' v_summary) ->
      ReadOnlyPhi phi_summary ->
      Disjoint_Traces (phi_as_list phi_writer) (phi_as_list phi_summary)) ->
    SummaryReplayCompatibleForExpr env rho summary heap_writer' heap.
Proof.
  intros heap env rho writer summary phi_writer heap_writer' v_writer
    HWriter HDisjoint.
  apply SummaryReplayCompatibleForExpr_from_readonly_replay.
  intros phi_summary heap_summary' v_summary HSummary HReadOnly.
  assert (HPostAgree :
    HeterogeneousHeapForPhi phi_summary heap_writer' heap).
  {
    eapply
      (HeterogeneousHeapForPhi_preserved_by_disjoint_steps_phi
        (initial_state heap env rho writer)
        phi_writer
        (StDone heap_writer' v_writer)
        phi_summary
        heap).
    - exact HWriter.
    - eapply HDisjoint; eauto.
    - apply HeterogeneousHeapForPhi_refl.
  }
  now apply HeterogeneousHeapForPhi_sym.
Qed.

Lemma PairParBranchSummaryReplayCompatible_from_trace_disjoint :
  forall heap env rho ef1 ea1 summary2,
    PairParBranchSummaryTraceDisjoint heap env rho ef1 ea1 summary2 ->
    PairParBranchSummaryReplayCompatible heap env rho ef1 ea1 summary2.
Proof.
  intros heap env rho ef1 ea1 summary2 HDisjoint.
  unfold PairParBranchSummaryReplayCompatible.
  intros phi_mu1 heap_mu1 v1 HMu1.
  eapply SummaryReplayCompatibleForExpr_from_disjoint_writer.
  - exact HMu1.
  - intros phi_summary heap_summary v_summary HSummary HReadOnly.
    unfold PairParBranchSummaryTraceDisjoint in HDisjoint.
    eapply HDisjoint; eauto.
Qed.

Lemma PairParBranchHeapCompatible_from_trace_disjoint :
  forall heap env rho ef1 ea1 ef2 ea2,
    PairParBranchTraceDisjoint heap env rho ef1 ea1 ef2 ea2 ->
    PairParBranchHeapCompatible heap env rho ef1 ea1 ef2 ea2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 HDisjoint.
  unfold PairParBranchHeapCompatible.
  intros phi_mu1 heap_mu1 v1 HMu1.
  apply HeterogeneousHeapForExpr_from_readonly_replay.
  intros phi_mu2 heap_mu2 v2 HMu2 HReadOnlyMu2.
  eapply
    (HeterogeneousHeapForPhi_preserved_by_disjoint_steps_phi
      (initial_state heap env rho (Mu_App ef1 ea1))
      phi_mu1
      (StDone heap_mu1 v1)
      phi_mu2
      heap).
  - exact HMu1.
  - eapply HDisjoint; eauto.
  - apply HeterogeneousHeapForPhi_refl.
Qed.

Lemma PairParBranchTraceDisjoint_from_check_dependent_soundness :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2,
    PairParCheckPass theta1 theta2 ->
    (forall phi_mu1 heap_mu1 v1,
      StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) ->
      phi_mu1 ⋞ theta1) ->
    (forall phi_mu1 heap_mu1 v1 phi_mu2 heap_mu2 v2,
      StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) ->
      StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
        (StDone heap_mu2 v2) ->
      ReadOnlyPhi phi_mu2 ->
      phi_mu2 ⋞ theta2) ->
    PairParBranchTraceDisjoint heap env rho ef1 ea1 ef2 ea2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2
    [HDisjoint _] HLeftSound HRightSound.
  unfold PairParBranchTraceDisjoint.
  intros phi_mu1 heap_mu1 v1 phi_mu2 heap_mu2 v2
    HMu1 HMu2 HReadOnlyMu2.
  eapply Phi_Theta_Disjointness_disjoint_traces; eauto.
Qed.

Lemma PairParBranchTraceDisjoint_from_check_soundness :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2,
    PairParCheckPass theta1 theta2 ->
    (forall phi_mu1 heap_mu1 v1,
      StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) ->
      phi_mu1 ⋞ theta1) ->
    (forall heap_mu1 phi_mu2 heap_mu2 v2,
      StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
        (StDone heap_mu2 v2) ->
      ReadOnlyPhi phi_mu2 ->
      phi_mu2 ⋞ theta2) ->
    PairParBranchTraceDisjoint heap env rho ef1 ea1 ef2 ea2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2
    [HDisjoint _] HLeftSound HRightSound.
  unfold PairParBranchTraceDisjoint.
  intros phi_mu1 heap_mu1 v1 phi_mu2 heap_mu2 v2
    HMu1 HMu2 HReadOnlyMu2.
  eapply Phi_Theta_Disjointness_disjoint_traces; eauto.
Qed.

Lemma PairParBranchSummaryTraceDisjoint_from_check_soundness :
  forall heap env rho ef1 ea1 summary2 theta1 theta2,
    PairParCheckPass theta1 theta2 ->
    (forall phi_mu1 heap_mu1 v1,
      StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) ->
      phi_mu1 ⋞ theta1) ->
    (forall phi_summary heap_summary v_summary,
      StepsPhi (initial_state heap env rho summary2) phi_summary
        (StDone heap_summary v_summary) ->
      ReadOnlyPhi phi_summary ->
      phi_summary ⋞ theta2) ->
    PairParBranchSummaryTraceDisjoint heap env rho ef1 ea1 summary2.
Proof.
  intros heap env rho ef1 ea1 summary2 theta1 theta2
    [HDisjoint _] HLeftSound HSummarySound.
  unfold PairParBranchSummaryTraceDisjoint.
  intros phi_mu1 heap_mu1 v1 phi_summary heap_summary v_summary
    HMu1 HSummary HReadOnlySummary.
  eapply Phi_Theta_Disjointness_disjoint_traces; eauto.
Qed.

Lemma PairParBranchSummaryReplayCompatible_from_check_soundness :
  forall heap env rho ef1 ea1 summary2 theta1 theta2,
    PairParCheckPass theta1 theta2 ->
    (forall phi_mu1 heap_mu1 v1,
      StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) ->
      phi_mu1 ⋞ theta1) ->
    (forall phi_summary heap_summary v_summary,
      StepsPhi (initial_state heap env rho summary2) phi_summary
        (StDone heap_summary v_summary) ->
      ReadOnlyPhi phi_summary ->
      phi_summary ⋞ theta2) ->
    PairParBranchSummaryReplayCompatible heap env rho ef1 ea1 summary2.
Proof.
  intros heap env rho ef1 ea1 summary2 theta1 theta2
    HPass HLeftSound HSummarySound.
  apply PairParBranchSummaryReplayCompatible_from_trace_disjoint.
  eapply PairParBranchSummaryTraceDisjoint_from_check_soundness; eauto.
Qed.

Lemma PairParBranchSummaryReplayCompatible_from_check_summary_witness :
  forall heap env rho ef1 ea1 summary2 theta1 theta2
    phi_summary2 heap_summary2 v_summary2,
    PairParCheckPass theta1 theta2 ->
    StepsPhi (initial_state heap env rho summary2) phi_summary2
      (StDone heap_summary2 v_summary2) ->
    phi_summary2 ⋞ theta2 ->
    (forall phi_mu1 heap_mu1 v1,
      StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) ->
      phi_mu1 ⋞ theta1) ->
    PairParBranchSummaryReplayCompatible heap env rho ef1 ea1 summary2.
Proof.
  intros heap env rho ef1 ea1 summary2 theta1 theta2
    phi_summary2 heap_summary2 v_summary2
    HPass HSummary2 HSummary2Sound HLeftSound.
  eapply
    (PairParBranchSummaryReplayCompatible_from_check_soundness
      heap env rho ef1 ea1 summary2 theta1 theta2).
  - exact HPass.
  - exact HLeftSound.
  - intros phi_summary heap_summary v_summary HSummary _.
    eapply
      (Correctness_soundness_ext_small_step_terminal_transfer
        (initial_state heap env rho summary2)
        phi_summary2 heap_summary2 v_summary2
        phi_summary heap_summary v_summary theta2);
      eauto.
Qed.

Lemma PairParBranchTraceDisjoint_from_check_heterogeneous_recursive :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2
    phi_eff1 phi_eff2
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2,
    PairParCheckPass theta1 theta2 ->
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap (Eff theta1)) ->
    StepsPhi (initial_state heap env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap (Eff theta2)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, static_mu1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, static_mu2) ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_eff1, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_eff2, static_eff2) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    PairParBranchTraceDisjoint heap env rho ef1 ea1 ef2 ea2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2
    phi_eff1 phi_eff2
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2
    HPass HEff1 HEff2 HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcMu1 HTcMu2 HTcEff1 HTcEff2 HReadOnlyStatic1 HReadOnlyStatic2
    HBTMu1Eff HBTMu2Eff HRecursive.
  pose proof
    (StepsPhi_typed_readonly_static_readonly_phi
      heap env rho (Eff_App ef1 ea1) stty ctxt rgns
      ty_eff1 static_eff1 phi_eff1 heap (Eff theta1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff1
      HEff1 HReadOnlyStatic1) as HReadOnlyEff1.
  pose proof
    (StepsPhi_typed_readonly_static_readonly_phi
      heap env rho (Eff_App ef2 ea2) stty ctxt rgns
      ty_eff2 static_eff2 phi_eff2 heap (Eff theta2)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff2
      HEff2 HReadOnlyStatic2) as HReadOnlyEff2.
  eapply
    (PairParBranchTraceDisjoint_from_check_dependent_soundness
      heap env rho ef1 ea1 ef2 ea2 theta1 theta2).
  - exact HPass.
  - intros phi_mu1 heap_mu1 v1 HMu1.
    eapply (HRecursive
      heap heap env rho (Mu_App ef1 ea1) (Eff_App ef1 ea1)
      phi_mu1 heap_mu1 v1
      phi_eff1 heap theta1
      stty ctxt rgns ty1 static_mu1); eauto.
  - intros phi_mu1 heap_mu1 v1 phi_mu2 heap_mu2 v2
      HMu1 HMu2 HReadOnlyMu2.
    destruct
      (StepsPhi_initial_terminal_value_typed
        heap env rho (Mu_App ef1 ea1) stty ctxt rgns
        ty1 static_mu1 phi_mu1 heap_mu1 v1
        HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
        HTcMu1 HMu1)
      as (stty_mu1 & HExtMu1 & HTcHeapMu1 & HHeapShapeMu1 &
          _ & _).
    assert (HTcEnvMu1 : TcEnv (stty_mu1, rho, env, ctxt)).
    {
      eapply ext_stores__env; eauto.
    }
    assert (HEnvShapeMu1 : RuntimeEnvShape stty_mu1 rho env ctxt).
    {
      eapply RuntimeEnvShape_store_ext; eauto.
    }
    eapply (HRecursive
      heap_mu1 heap env rho (Mu_App ef2 ea2) (Eff_App ef2 ea2)
      phi_mu2 heap_mu2 v2
      phi_eff2 heap theta2
      stty_mu1 ctxt rgns ty2 static_mu2); eauto.
Qed.

Lemma PairParBranchHeapCompatible_from_check_heterogeneous_recursive :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2
    phi_eff1 phi_eff2
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2,
    PairParCheckPass theta1 theta2 ->
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap (Eff theta1)) ->
    StepsPhi (initial_state heap env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap (Eff theta2)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, static_mu1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, static_mu2) ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_eff1, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_eff2, static_eff2) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    PairParBranchHeapCompatible heap env rho ef1 ea1 ef2 ea2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2
    phi_eff1 phi_eff2
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2
    HPass HEff1 HEff2 HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcMu1 HTcMu2 HTcEff1 HTcEff2 HReadOnlyStatic1 HReadOnlyStatic2
    HBTMu1Eff HBTMu2Eff HRecursive.
  apply PairParBranchHeapCompatible_from_trace_disjoint.
  eapply PairParBranchTraceDisjoint_from_check_heterogeneous_recursive;
    eauto.
Qed.

Lemma StepsPhi_pair_par_terminal_decompose_checked_heap_compatible_or_fallback :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2,
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, static_mu1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, static_mu2) ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_eff1, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_eff2, static_eff2) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    exists phi_eff1 theta1
      phi_eff2 theta2
      phi_mu1 heap_mu1 v1
      phi_mu2 heap_mu2 v2,
      StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
        (StDone heap (Eff theta1)) /\
      StepsPhi (initial_state heap env rho (Eff_App ef2 ea2)) phi_eff2
        (StDone heap (Eff theta2)) /\
      StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) /\
      StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
        (StDone heap_mu2 v2) /\
      (PairParCheckFail theta1 theta2 \/
        PairParBranchHeapCompatible heap env rho ef1 ea1 ef2 ea2) /\
      heap_pair = heap_mu2 /\
      v_pair = Pair (v1, v2) /\
      phi_as_list phi_pair =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2 ++
        phi_as_list phi_mu1 ++ phi_as_list phi_mu2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2
    HPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcMu1 HTcMu2 HTcEff1 HTcEff2 HReadOnlyStatic1 HReadOnlyStatic2
    HBTMu1Eff HBTMu2Eff HRecursive.
  destruct
    (StepsPhi_pair_par_terminal_decompose_checked
      heap env rho ef1 ea1 ef2 ea2
      phi_pair heap_pair v_pair HPair)
    as (phi_eff1 & heap_eff1 & theta1 &
        phi_eff2 & heap_eff2 & theta2 &
        phi_mu1 & heap_mu1 & v1 &
        phi_mu2 & heap_mu2 & v2 &
        HEff1 & HEff2 & HMu1 & HMu2 &
        HCheck & HHeapPair & HValuePair & HTracePair).
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho (Eff_App ef1 ea1) stty ctxt rgns
      ty_eff1 static_eff1
      phi_eff1 heap_eff1 (Eff theta1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff1
      HEff1 HReadOnlyStatic1) as HHeapEff1.
  subst heap_eff1.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho (Eff_App ef2 ea2) stty ctxt rgns
      ty_eff2 static_eff2
      phi_eff2 heap_eff2 (Eff theta2)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff2
      HEff2 HReadOnlyStatic2) as HHeapEff2.
  subst heap_eff2.
  exists phi_eff1, theta1,
    phi_eff2, theta2,
    phi_mu1, heap_mu1, v1,
    phi_mu2, heap_mu2, v2.
  repeat split; try assumption.
  destruct HCheck as [HPass | HFail].
  - right.
    eapply PairParBranchHeapCompatible_from_check_heterogeneous_recursive;
      eauto.
  - now left.
Qed.

Lemma PairParBranchTraceDisjoint_implies_heap_compatible :
  PairParBranchTraceDisjointRecursivePremise ->
  PairParBranchHeapCompatibleRecursivePremise.
Proof.
  intros HTraceDisjoint.
  unfold PairParBranchHeapCompatibleRecursivePremise.
  intros heap env rho ef1 ea1 ef2 ea2.
  apply PairParBranchHeapCompatible_from_trace_disjoint.
  unfold PairParBranchTraceDisjointRecursivePremise in HTraceDisjoint.
  eapply HTraceDisjoint.
Qed.

Lemma HeterogeneousHeapForExpr_refl :
  forall env rho e heap,
    HeterogeneousHeapForExpr env rho e heap heap.
Proof.
  intros env rho e heap phi_actual heap_actual' v HSteps _.
  split.
  - apply HeterogeneousHeapForPhi_refl.
  - exists phi_actual, heap_actual'.
    split; [exact HSteps | reflexivity].
Qed.

Lemma HeapEquivalentForExpr_refl :
  forall env rho e heap,
    HeapEquivalentForExpr env rho e heap heap.
Proof.
  intros env rho e heap.
  unfold HeapEquivalentForExpr.
  apply HeterogeneousHeapForExpr_refl.
Qed.

Lemma SmallStepCorrectnessHeterogeneous_implies_heap_compatible :
  SmallStepCorrectnessHeterogeneousRecursivePremise ->
  SmallStepCorrectnessHeapCompatibleRecursivePremise.
Proof.
  intros HRecursive.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremise in HRecursive.
  unfold SmallStepCorrectnessHeapCompatibleRecursivePremise.
  intros heap heap_summary_start env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    _ HBT HSteps HSummary HReadOnlySummary HTcHeap HHeapShape HTcRho
    HTcInc HTcEnv HEnvShape HTcExp.
  eapply HRecursive; eauto.
Qed.

Lemma SmallStepCorrectnessHeapCompatible_same_heap_recursive :
  SmallStepCorrectnessHeapCompatibleRecursivePremise ->
  SmallStepCorrectnessRecursivePremise.
Proof.
  intros HRecursive.
  unfold SmallStepCorrectnessHeapCompatibleRecursivePremise in HRecursive.
  unfold SmallStepCorrectnessRecursivePremise.
  intros heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HBT HSteps HSummary HReadOnlySummary HTcHeap HHeapShape HTcRho HTcInc
    HTcEnv HEnvShape HTcExp.
	  eapply HRecursive; eauto.
	  apply HeterogeneousHeapForExpr_refl.
Qed.

Lemma SmallStepCorrectnessRecursive_implies_lookup_equivalent_recursive :
  SmallStepCorrectnessRecursivePremise ->
  SmallStepCorrectnessLookupEquivalentRecursivePremise.
Proof.
  intros HRecursive.
  unfold SmallStepCorrectnessRecursivePremise in HRecursive.
  unfold SmallStepCorrectnessLookupEquivalentRecursivePremise.
  intros heap heap_summary_start env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HLookup HBT HSteps HSummary HReadOnlySummary HTcHeap HHeapShape
    HTcRho HTcInc HTcEnv HEnvShape HTcExp.
  pose proof
    (StepsPhi_readonly_replay_terminal_on_lookup_equivalent_heap
      heap heap_summary_start env rho ee phi_summary heap_summary
      (Eff theta_summary) HLookup HSummary HReadOnlySummary)
    as HSummarySame.
  eapply HRecursive; eauto.
Qed.

Lemma SmallStepCorrectnessRecursive_implies_summary_replay_recursive :
  SmallStepCorrectnessRecursivePremise ->
  SmallStepCorrectnessSummaryReplayRecursivePremise.
Proof.
  intros HRecursive.
  unfold SmallStepCorrectnessRecursivePremise in HRecursive.
  unfold SmallStepCorrectnessSummaryReplayRecursivePremise.
  intros heap heap_summary_start env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HSummaryCompat HBT HSteps HSummary HReadOnlySummary HTcHeap HHeapShape
    HTcRho HTcInc HTcEnv HEnvShape HTcExp.
  destruct
    (HSummaryCompat phi_summary heap_summary (Eff theta_summary)
      HSummary HReadOnlySummary) as (_ & HSummarySame).
  eapply HRecursive; eauto.
Qed.

Lemma SmallStepCorrectnessSummaryReplay_same_heap_recursive :
  SmallStepCorrectnessSummaryReplayRecursivePremise ->
  SmallStepCorrectnessRecursivePremise.
Proof.
  intros HRecursive.
  unfold SmallStepCorrectnessSummaryReplayRecursivePremise in HRecursive.
  unfold SmallStepCorrectnessRecursivePremise.
  intros heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HBT HSteps HSummary HReadOnlySummary HTcHeap HHeapShape HTcRho HTcInc
    HTcEnv HEnvShape HTcExp.
  eapply HRecursive; eauto.
  apply SummaryReplayCompatibleForExpr_refl.
Qed.

Lemma SmallStepCorrectnessHeterogeneous_implies_lookup_equivalent_recursive :
  SmallStepCorrectnessHeterogeneousRecursivePremise ->
  SmallStepCorrectnessLookupEquivalentRecursivePremise.
Proof.
  intros HRecursive.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremise in HRecursive.
  unfold SmallStepCorrectnessLookupEquivalentRecursivePremise.
  intros heap heap_summary_start env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    _ HBT HSteps HSummary HReadOnlySummary HTcHeap HHeapShape
    HTcRho HTcInc HTcEnv HEnvShape HTcExp.
  eapply HRecursive; eauto.
Qed.

Lemma SmallStepCorrectnessHeapEquivalent_implies_lookup_equivalent_recursive :
  SmallStepCorrectnessHeapEquivalentRecursivePremise ->
  SmallStepCorrectnessLookupEquivalentRecursivePremise.
Proof.
  intros HRecursive.
  unfold SmallStepCorrectnessHeapEquivalentRecursivePremise in HRecursive.
  unfold SmallStepCorrectnessLookupEquivalentRecursivePremise.
  intros heap heap_summary_start env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HLookup HBT HSteps HSummary HReadOnlySummary HTcHeap HHeapShape
    HTcRho HTcInc HTcEnv HEnvShape HTcExp.
  eapply HRecursive; eauto.
  eapply HeapLookupEquivalent_implies_HeapEquivalentForExpr.
  exact HLookup.
Qed.

Lemma SmallStepCorrectnessLookupEquivalent_same_heap_recursive :
  SmallStepCorrectnessLookupEquivalentRecursivePremise ->
  SmallStepCorrectnessRecursivePremise.
Proof.
  intros HRecursive.
  unfold SmallStepCorrectnessLookupEquivalentRecursivePremise in HRecursive.
  unfold SmallStepCorrectnessRecursivePremise.
  intros heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HBT HSteps HSummary HReadOnlySummary HTcHeap HHeapShape HTcRho HTcInc
    HTcEnv HEnvShape HTcExp.
  eapply HRecursive; eauto.
  intros k.
  reflexivity.
Qed.

Theorem Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_below_case :
  forall n heap env rho er w
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns effr tyr static_er,
    StepsPhiN n (initial_state heap env rho (Rgn_App er w)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho Empty) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, er, Ty_ForallRgn effr tyr, static_er) ->
    BackTriangle (ctxt, rgns, rho, er, Empty) ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi_app ⋞ theta_summary.
Proof.
  intros n heap env rho er w
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns effr tyr static_er
    HApp HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEr HBTFun HBelow.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_rgn_app_terminal_decompose_counts
      n heap env rho er w phi_app heap_app v_app HApp)
    as (env_fun & rho_fun & x & eb & r &
        n_fun & phi_fun & heap_fun &
        n_body & phi_body &
        HLtFun & HLtBody & HFun & HFind & HBody & _).
  destruct
    (StepsPhi_initial_empty_terminal
      heap env rho phi_summary heap_summary theta_summary HSummary)
    as (HSummaryNil & _ & HTheta).
  pose proof
    (ReadOnlyPhi_of_phi_as_list_nil phi_summary HSummaryNil)
    as HReadOnlySummary.
  subst theta_summary.
  destruct
    (RgnApp_body_context_from_terminal
      heap env rho er heap_fun env_fun rho_fun x eb w r
      phi_fun stty ctxt rgns effr tyr static_er
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEr
      (StepsPhiN_to_StepsPhi _ _ _ _ HFun) HFind)
    as (stty_fun & rgns_body & ctxt_body & effr_body & tyr_body &
        HExtFun & HTcHeapFun & HHeapShapeFun & HTcRhoBody &
        HTcIncBody & HTcEnvBody & HEnvShapeBody & HBTBody & HTcBody).
  pose proof
    (HBelow
      n_fun heap heap env rho er Empty
      phi_fun heap_fun (Cls (env_fun, rho_fun, Lambda x eb))
      phi_summary heap_summary Theta_Empty
      stty ctxt rgns (Ty_ForallRgn effr tyr) static_er
      HLtFun HBTFun HFun HSummary HReadOnlySummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEr)
    as HFunSound.
  pose proof
    (initial_empty_steps_phi_done
      heap_fun env_fun (update_R (x, r) rho_fun))
    as HBodySummary.
  assert (HReadOnlyBodySummary :
    ReadOnlyPhi
      (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))).
  {
    apply ReadOnlyPhi_of_phi_as_list_nil.
    reflexivity.
  }
  pose proof
    (HBelow
      n_body heap_fun heap_fun env_fun (update_R (x, r) rho_fun) eb Empty
      phi_body heap_app v_app
      (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))
      heap_fun Theta_Empty
      stty_fun ctxt_body (set_union rgns_body (singleton_set x))
      tyr_body effr_body
      HLtBody HBTBody HBody HBodySummary HReadOnlyBodySummary
      HTcHeapFun HHeapShapeFun HTcRhoBody HTcIncBody HTcEnvBody
      HEnvShapeBody HTcBody)
    as HBodySound.
  eapply
    (Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_case
      heap env rho er w env_fun rho_fun x eb r
      phi_fun heap_fun phi_body heap_app v_app
      phi_summary heap_summary Theta_Empty
      phi_app heap_app v_app); eauto.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HFun).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HBody).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HApp).
Qed.

Theorem Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_summary_replay_below_case :
  forall n heap env rho er w
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns effr tyr static_er,
    StepsPhiN n (initial_state heap env rho (Rgn_App er w)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho Empty) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, er, Ty_ForallRgn effr tyr, static_er) ->
    BackTriangle (ctxt, rgns, rho, er, Empty) ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi_app ⋞ theta_summary.
Proof.
  intros n heap env rho er w
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns effr tyr static_er
    HApp HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEr HBTFun HBelow.
  unfold SmallStepCorrectnessSummaryReplayRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_rgn_app_terminal_decompose_counts
      n heap env rho er w phi_app heap_app v_app HApp)
    as (env_fun & rho_fun & x & eb & r &
        n_fun & phi_fun & heap_fun &
        n_body & phi_body &
        HLtFun & HLtBody & HFun & HFind & HBody & _).
  destruct
    (StepsPhi_initial_empty_terminal
      heap env rho phi_summary heap_summary theta_summary HSummary)
    as (HSummaryNil & _ & HTheta).
  pose proof
    (ReadOnlyPhi_of_phi_as_list_nil phi_summary HSummaryNil)
    as HReadOnlySummary.
  subst theta_summary.
  destruct
    (RgnApp_body_context_from_terminal
      heap env rho er heap_fun env_fun rho_fun x eb w r
      phi_fun stty ctxt rgns effr tyr static_er
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEr
      (StepsPhiN_to_StepsPhi _ _ _ _ HFun) HFind)
    as (stty_fun & rgns_body & ctxt_body & effr_body & tyr_body &
        HExtFun & HTcHeapFun & HHeapShapeFun & HTcRhoBody &
        HTcIncBody & HTcEnvBody & HEnvShapeBody & HBTBody & HTcBody).
  pose proof
    (HBelow
      n_fun heap heap env rho er Empty
      phi_fun heap_fun (Cls (env_fun, rho_fun, Lambda x eb))
      phi_summary heap_summary Theta_Empty
      stty ctxt rgns (Ty_ForallRgn effr tyr) static_er
      HLtFun (SummaryReplayCompatibleForExpr_refl env rho Empty heap)
      HBTFun HFun HSummary HReadOnlySummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEr)
    as HFunSound.
  pose proof
    (initial_empty_steps_phi_done
      heap_fun env_fun (update_R (x, r) rho_fun))
    as HBodySummary.
  assert (HReadOnlyBodySummary :
    ReadOnlyPhi
      (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))).
  {
    apply ReadOnlyPhi_of_phi_as_list_nil.
    reflexivity.
  }
  pose proof
    (HBelow
      n_body heap_fun heap_fun env_fun (update_R (x, r) rho_fun) eb Empty
      phi_body heap_app v_app
      (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))
      heap_fun Theta_Empty
      stty_fun ctxt_body (set_union rgns_body (singleton_set x))
      tyr_body effr_body
      HLtBody
      (SummaryReplayCompatibleForExpr_refl
        env_fun (update_R (x, r) rho_fun) Empty heap_fun)
      HBTBody HBody HBodySummary HReadOnlyBodySummary
      HTcHeapFun HHeapShapeFun HTcRhoBody HTcIncBody HTcEnvBody
      HEnvShapeBody HTcBody)
    as HBodySound.
  eapply
    (Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_case
      heap env rho er w env_fun rho_fun x eb r
      phi_fun heap_fun phi_body heap_app v_app
      phi_summary heap_summary Theta_Empty
      phi_app heap_app v_app); eauto.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HFun).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HBody).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HApp).
Qed.

Theorem Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_recursive_case :
  forall heap env rho w e eff
    phi_summary heap_summary theta_summary
    phi_ref heap_ref v_ref
    stty ctxt rgns ty_e static_e,
    StepsPhi (initial_state heap env rho (Concat eff (AllocAbs w)))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Ref w e)) phi_ref
      (StDone heap_ref v_ref) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e, eff) ->
    SmallStepCorrectnessRecursivePremise ->
    phi_ref ⋞ theta_summary.
Proof.
  intros heap env rho w e eff
    phi_summary heap_summary theta_summary
    phi_ref heap_ref v_ref stty ctxt rgns ty_e static_e
    HSummary HRef HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE HReadOnlySummary HBT HRecursive.
  unfold SmallStepCorrectnessRecursivePremise in HRecursive.
  eapply Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_direct_case;
    try eassumption.
  intros phi_arg heap_arg v phi_eff heap_eff theta_eff
    HArg HEff HReadOnlyEff.
  eapply (HRecursive
    heap env rho e eff
    phi_arg heap_arg v
    phi_eff heap_eff theta_eff
    stty ctxt rgns ty_e static_e); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_heterogeneous_case :
  forall heap heap_summary_start env rho w e eff
    phi_arg heap_arg v r l
    phi_eff heap_eff theta_eff
    phi_summary heap_summary theta_summary
    phi_ref heap_ref v_ref,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg v) ->
    StepsPhi (initial_state heap_summary_start env rho eff) phi_eff
      (StDone heap_eff (Eff theta_eff)) ->
    find_R w rho = Some r ->
    allocate_H heap_arg r = l ->
    StepsPhi
      (initial_state heap_summary_start env rho (Concat eff (AllocAbs w)))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Ref w e)) phi_ref
      (StDone heap_ref v_ref) ->
    phi_arg ⋞ theta_eff ->
    phi_ref ⋞ theta_summary.
Proof.
  intros heap heap_summary_start env rho w e eff
    phi_arg heap_arg v r l
    phi_eff heap_eff theta_eff
    phi_summary heap_summary theta_summary
    phi_ref heap_ref v_ref HArg HEff HFind HAlloc HSummary HRef
    HArgSound.
  destruct
    (steps_as_StepsPhi
      (initial_state heap_eff env rho (AllocAbs w))
      nil
      (StDone heap_eff (Eff (Some (singleton_set (CA_AllocAbs r)))))
      (initial_allocabs_steps_done heap_eff env rho w r HFind))
    as (phi_action & HAction & _).
  pose proof
    (StepsPhi_concat_summary_terminal_theta
      heap_summary_start env rho eff (AllocAbs w)
      phi_eff heap_eff theta_eff
      phi_action heap_eff (Some (singleton_set (CA_AllocAbs r)))
      phi_summary heap_summary theta_summary
      HEff HAction HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_ref_abs_terminal_case
    heap env rho w e phi_arg heap_arg v r l theta_eff
    phi_ref heap_ref v_ref); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_heterogeneous_recursive_case :
  forall heap heap_summary_start env rho w e eff
    phi_summary heap_summary theta_summary
    phi_ref heap_ref v_ref
    stty ctxt rgns ty_e static_e,
    StepsPhi
      (initial_state heap_summary_start env rho (Concat eff (AllocAbs w)))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Ref w e)) phi_ref
      (StDone heap_ref v_ref) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e, eff) ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi_ref ⋞ theta_summary.
Proof.
  intros heap heap_summary_start env rho w e eff
    phi_summary heap_summary theta_summary
    phi_ref heap_ref v_ref stty ctxt rgns ty_e static_e
    HSummary HRef HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE HReadOnlySummary HBT HRecursive.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremise in HRecursive.
  destruct
    (StepsPhi_ref_terminal_decompose
      heap env rho w e phi_ref heap_ref v_ref HRef)
    as (phi_arg & heap_arg & v & r & l &
        HArg & HFind & HAlloc & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_summary_start env rho eff (AllocAbs w)
      phi_summary heap_summary theta_summary HSummary)
    as (phi_eff & heap_eff & theta_eff &
        phi_alloc & heap_alloc & theta_alloc &
        HEff & HAllocSummary & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_eff phi_alloc HReadOnlySummary HTraceSummary)
    as HReadOnlyEff.
  pose proof
    (HRecursive
      heap heap_summary_start env rho e eff
      phi_arg heap_arg v
      phi_eff heap_eff theta_eff
      stty ctxt rgns ty_e static_e
      HBT HArg HEff HReadOnlyEff
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE) as HArgSound.
  eapply
    (Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_heterogeneous_case
      heap heap_summary_start env rho w e eff
      phi_arg heap_arg v r l
      phi_eff heap_eff theta_eff
      phi_summary heap_summary theta_summary
	      phi_ref heap_ref v_ref); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_heterogeneous_below_case :
  forall n heap heap_summary_start env rho w e eff
    phi_summary heap_summary theta_summary
    phi_ref heap_ref v_ref
    stty ctxt rgns ty_e static_e,
    StepsPhi
      (initial_state heap_summary_start env rho (Concat eff (AllocAbs w)))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhiN n (initial_state heap env rho (Ref w e)) phi_ref
      (StDone heap_ref v_ref) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e, eff) ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi_ref ⋞ theta_summary.
Proof.
  intros n heap heap_summary_start env rho w e eff
    phi_summary heap_summary theta_summary
    phi_ref heap_ref v_ref stty ctxt rgns ty_e static_e
    HSummary HRef HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE HReadOnlySummary HBT HBelow.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_ref_terminal_decompose_counts
      n heap env rho w e phi_ref heap_ref v_ref HRef)
    as (n_arg & phi_arg & heap_arg & v & r & l &
        HLtArg & HArg & HFind & HAlloc & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_summary_start env rho eff (AllocAbs w)
      phi_summary heap_summary theta_summary HSummary)
    as (phi_eff & heap_eff & theta_eff &
        phi_alloc & heap_alloc & theta_alloc &
        HEff & HAllocSummary & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_eff phi_alloc HReadOnlySummary HTraceSummary)
    as HReadOnlyEff.
  pose proof
    (HBelow
      n_arg heap heap_summary_start env rho e eff
      phi_arg heap_arg v
      phi_eff heap_eff theta_eff
      stty ctxt rgns ty_e static_e
      HLtArg HBT HArg HEff HReadOnlyEff
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE) as HArgSound.
  eapply
    (Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_heterogeneous_case
      heap heap_summary_start env rho w e eff
      phi_arg heap_arg v r l
      phi_eff heap_eff theta_eff
      phi_summary heap_summary theta_summary
      phi_ref heap_ref v_ref); eauto.
  exact (StepsPhiN_to_StepsPhi _ _ _ _ HArg).
  exact (StepsPhiN_to_StepsPhi _ _ _ _ HRef).
Qed.

Theorem Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_summary_replay_below_case :
  forall n heap env rho w e eff
    phi_summary heap_summary theta_summary
    phi_ref heap_ref v_ref
    stty ctxt rgns ty_e static_e,
    StepsPhi (initial_state heap env rho (Concat eff (AllocAbs w)))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhiN n (initial_state heap env rho (Ref w e)) phi_ref
      (StDone heap_ref v_ref) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e, eff) ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi_ref ⋞ theta_summary.
Proof.
  intros n heap env rho w e eff
    phi_summary heap_summary theta_summary
    phi_ref heap_ref v_ref stty ctxt rgns ty_e static_e
    HSummary HRef HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE HReadOnlySummary HBT HBelow.
  unfold SmallStepCorrectnessSummaryReplayRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_ref_terminal_decompose_counts
      n heap env rho w e phi_ref heap_ref v_ref HRef)
    as (n_arg & phi_arg & heap_arg & v & r & l &
        HLtArg & HArg & HFind & HAlloc & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff (AllocAbs w)
      phi_summary heap_summary theta_summary HSummary)
    as (phi_eff & heap_eff & theta_eff &
        phi_alloc & heap_alloc & theta_alloc &
        HEff & HAllocSummary & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_eff phi_alloc HReadOnlySummary HTraceSummary)
    as HReadOnlyEff.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff) phi_eff
      (StDone heap_eff (Eff theta_eff))
      HEff HReadOnlyEff) as HHeapEff.
  simpl in HHeapEff.
  subst heap_eff.
  pose proof
    (HBelow
      n_arg heap heap env rho e eff
      phi_arg heap_arg v
      phi_eff heap theta_eff
      stty ctxt rgns ty_e static_e
      HLtArg (SummaryReplayCompatibleForExpr_refl env rho eff heap)
      HBT HArg HEff HReadOnlyEff
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE) as HArgSound.
  eapply
    (Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_heterogeneous_case
      heap heap env rho w e eff
      phi_arg heap_arg v r l
      phi_eff heap theta_eff
      phi_summary heap_summary theta_summary
      phi_ref heap_ref v_ref); eauto.
  exact (StepsPhiN_to_StepsPhi _ _ _ _ HArg).
  exact (StepsPhiN_to_StepsPhi _ _ _ _ HRef).
Qed.

Theorem Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_recursive_case :
  forall heap env rho w e eff
    phi_summary heap_summary theta_summary
    phi_deref heap_deref v_deref
    stty ctxt rgns ty_e static_e,
    StepsPhi (initial_state heap env rho (Concat eff (ReadAbs w)))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (DeRef w e)) phi_deref
      (StDone heap_deref v_deref) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e, eff) ->
    SmallStepCorrectnessRecursivePremise ->
    phi_deref ⋞ theta_summary.
Proof.
  intros heap env rho w e eff
    phi_summary heap_summary theta_summary
    phi_deref heap_deref v_deref stty ctxt rgns ty_e static_e
    HSummary HDeref HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE HReadOnlySummary HBT HRecursive.
  unfold SmallStepCorrectnessRecursivePremise in HRecursive.
  eapply Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_direct_case;
    try eassumption.
  intros phi_arg heap_arg l phi_eff heap_eff theta_eff
    HArg HEff HReadOnlyEff.
  eapply (HRecursive
    heap env rho e eff
    phi_arg heap_arg (Loc w l)
    phi_eff heap_eff theta_eff
    stty ctxt rgns ty_e static_e); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_heterogeneous_case :
  forall heap heap_summary_start env rho w e eff
    phi_arg heap_arg r l v
    phi_eff heap_eff theta_eff
    phi_summary heap_summary theta_summary
    phi_deref heap_deref v_deref,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg (Loc w l)) ->
    StepsPhi (initial_state heap_summary_start env rho eff) phi_eff
      (StDone heap_eff (Eff theta_eff)) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_arg = Some v ->
    StepsPhi
      (initial_state heap_summary_start env rho (Concat eff (ReadAbs w)))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (DeRef w e)) phi_deref
      (StDone heap_deref v_deref) ->
    phi_arg ⋞ theta_eff ->
    phi_deref ⋞ theta_summary.
Proof.
  intros heap heap_summary_start env rho w e eff
    phi_arg heap_arg r l v
    phi_eff heap_eff theta_eff
    phi_summary heap_summary theta_summary
    phi_deref heap_deref v_deref
    HArg HEff HFindR HFindH HSummary HDeref HArgSound.
  destruct
    (steps_as_StepsPhi
      (initial_state heap_eff env rho (ReadAbs w))
      nil
      (StDone heap_eff (Eff (Some (singleton_set (CA_ReadAbs r)))))
      (initial_readabs_steps_done heap_eff env rho w r HFindR))
    as (phi_action & HAction & _).
  pose proof
    (StepsPhi_concat_summary_terminal_theta
      heap_summary_start env rho eff (ReadAbs w)
      phi_eff heap_eff theta_eff
      phi_action heap_eff (Some (singleton_set (CA_ReadAbs r)))
      phi_summary heap_summary theta_summary
      HEff HAction HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_deref_abs_terminal_case
    heap env rho w e phi_arg heap_arg r l v theta_eff
    phi_deref heap_deref v_deref); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_heterogeneous_recursive_case :
  forall heap heap_summary_start env rho w e eff
    phi_summary heap_summary theta_summary
    phi_deref heap_deref v_deref
    stty ctxt rgns ty_e static_e,
    StepsPhi
      (initial_state heap_summary_start env rho (Concat eff (ReadAbs w)))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (DeRef w e)) phi_deref
      (StDone heap_deref v_deref) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e, eff) ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi_deref ⋞ theta_summary.
Proof.
  intros heap heap_summary_start env rho w e eff
    phi_summary heap_summary theta_summary
    phi_deref heap_deref v_deref stty ctxt rgns ty_e static_e
    HSummary HDeref HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE HReadOnlySummary HBT HRecursive.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremise in HRecursive.
  destruct
    (StepsPhi_deref_terminal_decompose
      heap env rho w e phi_deref heap_deref v_deref HDeref)
    as (phi_arg & heap_arg & r & l & v &
        HArg & HFindR & HFindH & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_summary_start env rho eff (ReadAbs w)
      phi_summary heap_summary theta_summary HSummary)
    as (phi_eff & heap_eff & theta_eff &
        phi_read & heap_read & theta_read &
        HEff & HReadSummary & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_eff phi_read HReadOnlySummary HTraceSummary)
    as HReadOnlyEff.
  pose proof
    (HRecursive
      heap heap_summary_start env rho e eff
      phi_arg heap_arg (Loc w l)
      phi_eff heap_eff theta_eff
      stty ctxt rgns ty_e static_e
      HBT HArg HEff HReadOnlyEff
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE) as HArgSound.
  eapply
    (Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_heterogeneous_case
      heap heap_summary_start env rho w e eff
      phi_arg heap_arg r l v
      phi_eff heap_eff theta_eff
	      phi_summary heap_summary theta_summary
	      phi_deref heap_deref v_deref); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_heterogeneous_below_case :
  forall n heap heap_summary_start env rho w e eff
    phi_summary heap_summary theta_summary
    phi_deref heap_deref v_deref
    stty ctxt rgns ty_e static_e,
    StepsPhi
      (initial_state heap_summary_start env rho (Concat eff (ReadAbs w)))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhiN n (initial_state heap env rho (DeRef w e)) phi_deref
      (StDone heap_deref v_deref) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e, eff) ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi_deref ⋞ theta_summary.
Proof.
  intros n heap heap_summary_start env rho w e eff
    phi_summary heap_summary theta_summary
    phi_deref heap_deref v_deref stty ctxt rgns ty_e static_e
    HSummary HDeref HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE HReadOnlySummary HBT HBelow.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_deref_terminal_decompose_counts
      n heap env rho w e phi_deref heap_deref v_deref HDeref)
    as (n_arg & phi_arg & heap_arg & r & l & v &
        HLtArg & HArg & HFindR & HFindH & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_summary_start env rho eff (ReadAbs w)
      phi_summary heap_summary theta_summary HSummary)
    as (phi_eff & heap_eff & theta_eff &
        phi_read & heap_read & theta_read &
        HEff & HReadSummary & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_eff phi_read HReadOnlySummary HTraceSummary)
    as HReadOnlyEff.
  pose proof
    (HBelow
      n_arg heap heap_summary_start env rho e eff
      phi_arg heap_arg (Loc w l)
      phi_eff heap_eff theta_eff
      stty ctxt rgns ty_e static_e
      HLtArg HBT HArg HEff HReadOnlyEff
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE) as HArgSound.
  eapply
    (Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_heterogeneous_case
      heap heap_summary_start env rho w e eff
      phi_arg heap_arg r l v
      phi_eff heap_eff theta_eff
      phi_summary heap_summary theta_summary
      phi_deref heap_deref v_deref); eauto.
  exact (StepsPhiN_to_StepsPhi _ _ _ _ HArg).
  exact (StepsPhiN_to_StepsPhi _ _ _ _ HDeref).
Qed.

Theorem Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_summary_replay_below_case :
  forall n heap env rho w e eff
    phi_summary heap_summary theta_summary
    phi_deref heap_deref v_deref
    stty ctxt rgns ty_e static_e,
    StepsPhi (initial_state heap env rho (Concat eff (ReadAbs w)))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhiN n (initial_state heap env rho (DeRef w e)) phi_deref
      (StDone heap_deref v_deref) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e, eff) ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi_deref ⋞ theta_summary.
Proof.
  intros n heap env rho w e eff
    phi_summary heap_summary theta_summary
    phi_deref heap_deref v_deref stty ctxt rgns ty_e static_e
    HSummary HDeref HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE HReadOnlySummary HBT HBelow.
  unfold SmallStepCorrectnessSummaryReplayRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_deref_terminal_decompose_counts
      n heap env rho w e phi_deref heap_deref v_deref HDeref)
    as (n_arg & phi_arg & heap_arg & r & l & v &
        HLtArg & HArg & HFindR & HFindH & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff (ReadAbs w)
      phi_summary heap_summary theta_summary HSummary)
    as (phi_eff & heap_eff & theta_eff &
        phi_read & heap_read & theta_read &
        HEff & HReadSummary & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_eff phi_read HReadOnlySummary HTraceSummary)
    as HReadOnlyEff.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff) phi_eff
      (StDone heap_eff (Eff theta_eff))
      HEff HReadOnlyEff) as HHeapEff.
  simpl in HHeapEff.
  subst heap_eff.
  pose proof
    (HBelow
      n_arg heap heap env rho e eff
      phi_arg heap_arg (Loc w l)
      phi_eff heap theta_eff
      stty ctxt rgns ty_e static_e
      HLtArg (SummaryReplayCompatibleForExpr_refl env rho eff heap)
      HBT HArg HEff HReadOnlyEff
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE) as HArgSound.
  eapply
    (Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_heterogeneous_case
      heap heap env rho w e eff
      phi_arg heap_arg r l v
      phi_eff heap theta_eff
      phi_summary heap_summary theta_summary
      phi_deref heap_deref v_deref); eauto.
  exact (StepsPhiN_to_StepsPhi _ _ _ _ HArg).
  exact (StepsPhiN_to_StepsPhi _ _ _ _ HDeref).
Qed.

Theorem Correctness_soundness_ext_small_step_assign_abs_bt_summary_terminal_recursive_case :
  forall heap env rho w ea ev eff1 eff2
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val,
    StepsPhi
      (initial_state heap env rho (Concat eff1 (Concat eff2 (WriteAbs w))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Assign w ea ev)) phi_assign
      (StDone heap_assign v_assign) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty_loc, static_loc) ->
    TcExp (ctxt, rgns, ev, ty_val, static_val) ->
    ReadOnlyStatic (fold_subst_eps rho static_loc) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ea, eff1) ->
    BackTriangle (ctxt, rgns, rho, ev, eff2) ->
    SmallStepCorrectnessRecursivePremise ->
    phi_assign ⋞ theta_summary.
Proof.
  intros heap env rho w ea ev eff1 eff2
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val
    HSummary HAssign HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcLoc HTcVal HReadOnlyStaticLoc HReadOnlySummary
    HBTLoc HBTVal HRecursive.
  unfold SmallStepCorrectnessRecursivePremise in HRecursive.
  eapply Correctness_soundness_ext_small_step_assign_abs_bt_summary_terminal_direct_case;
    try eassumption.
  - intros phi_loc heap_loc l phi_eff1 heap_eff1 theta_loc
      HLoc HEff1 HReadOnlyEff1.
    eapply (HRecursive
      heap env rho ea eff1
      phi_loc heap_loc (Loc w l)
      phi_eff1 heap_eff1 theta_loc
      stty ctxt rgns ty_loc static_loc); eauto.
  - intros phi_val heap_val v phi_eff2 heap_eff2 theta_val
      HVal HEff2 HReadOnlyEff2.
    eapply (HRecursive
      heap env rho ev eff2
      phi_val heap_val v
      phi_eff2 heap_eff2 theta_val
      stty ctxt rgns ty_val static_val); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_abs_bt_summary_terminal_heterogeneous_case :
  forall heap heap_summary_start env rho w ea ev eff1 eff2
    phi_loc heap_loc l phi_val heap_val v r
    phi_eff1 heap_eff1 theta_loc
    phi_eff2 heap_eff2 theta_val
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign,
    StepsPhi (initial_state heap env rho ea) phi_loc
      (StDone heap_loc (Loc w l)) ->
    StepsPhi (initial_state heap_loc env rho ev) phi_val
      (StDone heap_val v) ->
    StepsPhi (initial_state heap_summary_start env rho eff1) phi_eff1
      (StDone heap_eff1 (Eff theta_loc)) ->
    StepsPhi (initial_state heap_eff1 env rho eff2) phi_eff2
      (StDone heap_eff2 (Eff theta_val)) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_val <> None ->
    StepsPhi
      (initial_state heap_summary_start env rho
        (Concat eff1 (Concat eff2 (WriteAbs w))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Assign w ea ev)) phi_assign
      (StDone heap_assign v_assign) ->
    phi_loc ⋞ theta_loc ->
    phi_val ⋞ theta_val ->
    phi_assign ⋞ theta_summary.
Proof.
  intros heap heap_summary_start env rho w ea ev eff1 eff2
    phi_loc heap_loc l phi_val heap_val v r
    phi_eff1 heap_eff1 theta_loc
    phi_eff2 heap_eff2 theta_val
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    HLoc HVal HEff1 HEff2 HFindR HFindH HSummary HAssign
    HLocSound HValSound.
  destruct
    (steps_as_StepsPhi
      (initial_state heap_eff2 env rho (WriteAbs w))
      nil
      (StDone heap_eff2 (Eff (Some (singleton_set (CA_WriteAbs r)))))
      (initial_writeabs_steps_done heap_eff2 env rho w r HFindR))
    as (phi_action & HAction & _).
  pose proof
    (StepsPhi_right_nested_concat_summary_terminal_theta
      heap_summary_start env rho eff1 eff2 (WriteAbs w)
      phi_eff1 heap_eff1 theta_loc
      phi_eff2 heap_eff2 theta_val
      phi_action heap_eff2 (Some (singleton_set (CA_WriteAbs r)))
      phi_summary heap_summary theta_summary
      HEff1 HEff2 HAction HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_assign_abs_terminal_case
    heap env rho w ea ev
    phi_loc heap_loc l phi_val heap_val v r theta_loc theta_val
    phi_assign heap_assign v_assign); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_abs_bt_summary_terminal_heterogeneous_recursive_case :
  forall heap heap_summary_start env rho w ea ev eff1 eff2
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val,
    StepsPhi
      (initial_state heap_summary_start env rho
        (Concat eff1 (Concat eff2 (WriteAbs w))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Assign w ea ev)) phi_assign
      (StDone heap_assign v_assign) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty_loc, static_loc) ->
    TcExp (ctxt, rgns, ev, ty_val, static_val) ->
    ReadOnlyStatic (fold_subst_eps rho static_loc) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ea, eff1) ->
    BackTriangle (ctxt, rgns, rho, ev, eff2) ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi_assign ⋞ theta_summary.
Proof.
  intros heap heap_summary_start env rho w ea ev eff1 eff2
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val
    HSummary HAssign HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcLoc HTcVal HReadOnlyStaticLoc HReadOnlySummary
    HBTLoc HBTVal HRecursive.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremise in HRecursive.
  destruct
    (StepsPhi_assign_terminal_decompose
      heap env rho w ea ev phi_assign heap_assign v_assign HAssign)
    as (phi_loc & heap_loc & l & phi_val & heap_val & v & r &
        HLoc & HVal & HFindR & HFindH & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_summary_start env rho eff1 (Concat eff2 (WriteAbs w))
      phi_summary heap_summary theta_summary HSummary)
    as (phi_eff1 & heap_eff1 & theta_loc &
        phi_summary_tail & heap_summary_tail & theta_tail &
        HEff1 & HSummaryTail & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyEff1.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyTail.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_eff1 env rho eff2 (WriteAbs w)
      phi_summary_tail heap_summary_tail theta_tail HSummaryTail)
    as (phi_eff2 & heap_eff2 & theta_val &
        phi_write & heap_write & theta_write &
        HEff2 & HWriteSummary & _ & _ & HTraceTail).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary_tail phi_eff2 phi_write
      HReadOnlyTail HTraceTail) as HReadOnlyEff2.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ea stty ctxt rgns ty_loc static_loc
      phi_loc heap_loc (Loc w l)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcLoc
      HLoc HReadOnlyStaticLoc) as HHeapLoc.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap_summary_start env rho eff1) phi_eff1
      (StDone heap_eff1 (Eff theta_loc))
      HEff1 HReadOnlyEff1) as HHeapEff1.
  simpl in HHeapEff1.
  subst heap_loc.
  symmetry in HHeapEff1.
  subst heap_eff1.
  pose proof
    (HRecursive
      heap heap_summary_start env rho ea eff1
      phi_loc heap (Loc w l)
      phi_eff1 heap_summary_start theta_loc
      stty ctxt rgns ty_loc static_loc
      HBTLoc HLoc HEff1 HReadOnlyEff1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcLoc) as HLocSound.
  pose proof
    (HRecursive
      heap heap_summary_start env rho ev eff2
      phi_val heap_val v
      phi_eff2 heap_eff2 theta_val
      stty ctxt rgns ty_val static_val
      HBTVal HVal HEff2 HReadOnlyEff2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcVal) as HValSound.
  eapply
    (Correctness_soundness_ext_small_step_assign_abs_bt_summary_terminal_heterogeneous_case
      heap heap_summary_start env rho w ea ev eff1 eff2
      phi_loc heap l phi_val heap_val v r
      phi_eff1 heap_summary_start theta_loc
      phi_eff2 heap_eff2 theta_val
	      phi_summary heap_summary theta_summary
	      phi_assign heap_assign v_assign); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_abs_bt_summary_terminal_heterogeneous_below_case :
  forall n heap heap_summary_start env rho w ea ev eff1 eff2
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val,
    StepsPhi
      (initial_state heap_summary_start env rho
        (Concat eff1 (Concat eff2 (WriteAbs w))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhiN n (initial_state heap env rho (Assign w ea ev))
      phi_assign (StDone heap_assign v_assign) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty_loc, static_loc) ->
    TcExp (ctxt, rgns, ev, ty_val, static_val) ->
    ReadOnlyStatic (fold_subst_eps rho static_loc) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ea, eff1) ->
    BackTriangle (ctxt, rgns, rho, ev, eff2) ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi_assign ⋞ theta_summary.
Proof.
  intros n heap heap_summary_start env rho w ea ev eff1 eff2
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val
    HSummary HAssign HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcLoc HTcVal HReadOnlyStaticLoc HReadOnlySummary
    HBTLoc HBTVal HBelow.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_assign_terminal_decompose_counts
      n heap env rho w ea ev phi_assign heap_assign v_assign HAssign)
    as (n_loc & phi_loc & heap_loc & l &
        n_val & phi_val & heap_val & v & r &
        HLtLoc & HLtVal & HLoc & HVal &
        HFindR & HFindH & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_summary_start env rho eff1 (Concat eff2 (WriteAbs w))
      phi_summary heap_summary theta_summary HSummary)
    as (phi_eff1 & heap_eff1 & theta_loc &
        phi_summary_tail & heap_summary_tail & theta_tail &
        HEff1 & HSummaryTail & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyEff1.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyTail.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_eff1 env rho eff2 (WriteAbs w)
      phi_summary_tail heap_summary_tail theta_tail HSummaryTail)
    as (phi_eff2 & heap_eff2 & theta_val &
        phi_write & heap_write & theta_write &
        HEff2 & HWriteSummary & _ & _ & HTraceTail).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary_tail phi_eff2 phi_write
      HReadOnlyTail HTraceTail) as HReadOnlyEff2.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ea stty ctxt rgns ty_loc static_loc
      phi_loc heap_loc (Loc w l)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcLoc
      (StepsPhiN_to_StepsPhi _ _ _ _ HLoc) HReadOnlyStaticLoc) as HHeapLoc.
  subst heap_loc.
  pose proof
    (HBelow
      n_loc heap heap_summary_start env rho ea eff1
      phi_loc heap (Loc w l)
      phi_eff1 heap_eff1 theta_loc
      stty ctxt rgns ty_loc static_loc
      HLtLoc HBTLoc HLoc HEff1 HReadOnlyEff1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcLoc) as HLocSound.
  pose proof
    (HBelow
      n_val heap heap_eff1 env rho ev eff2
      phi_val heap_val v
      phi_eff2 heap_eff2 theta_val
      stty ctxt rgns ty_val static_val
      HLtVal HBTVal HVal HEff2 HReadOnlyEff2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcVal) as HValSound.
  eapply
    (Correctness_soundness_ext_small_step_assign_abs_bt_summary_terminal_heterogeneous_case
      heap heap_summary_start env rho w ea ev eff1 eff2
      phi_loc heap l phi_val heap_val v r
      phi_eff1 heap_eff1 theta_loc
      phi_eff2 heap_eff2 theta_val
      phi_summary heap_summary theta_summary
      phi_assign heap_assign v_assign); eauto.
  exact (StepsPhiN_to_StepsPhi _ _ _ _ HLoc).
  exact (StepsPhiN_to_StepsPhi _ _ _ _ HVal).
  exact (StepsPhiN_to_StepsPhi _ _ _ _ HAssign).
Qed.

Theorem Correctness_soundness_ext_small_step_assign_abs_bt_summary_terminal_summary_replay_below_case :
  forall n heap env rho w ea ev eff1 eff2
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val,
    StepsPhi
      (initial_state heap env rho
        (Concat eff1 (Concat eff2 (WriteAbs w))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhiN n (initial_state heap env rho (Assign w ea ev))
      phi_assign (StDone heap_assign v_assign) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty_loc, static_loc) ->
    TcExp (ctxt, rgns, ev, ty_val, static_val) ->
    ReadOnlyStatic (fold_subst_eps rho static_loc) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ea, eff1) ->
    BackTriangle (ctxt, rgns, rho, ev, eff2) ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi_assign ⋞ theta_summary.
Proof.
  intros n heap env rho w ea ev eff1 eff2
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val
    HSummary HAssign HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcLoc HTcVal HReadOnlyStaticLoc HReadOnlySummary
    HBTLoc HBTVal HBelow.
  unfold SmallStepCorrectnessSummaryReplayRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_assign_terminal_decompose_counts
      n heap env rho w ea ev phi_assign heap_assign v_assign HAssign)
    as (n_loc & phi_loc & heap_loc & l &
        n_val & phi_val & heap_val & v & r &
        HLtLoc & HLtVal & HLoc & HVal &
        HFindR & HFindH & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 (Concat eff2 (WriteAbs w))
      phi_summary heap_summary theta_summary HSummary)
    as (phi_eff1 & heap_eff1 & theta_loc &
        phi_summary_tail & heap_summary_tail & theta_tail &
        HEff1 & HSummaryTail & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyEff1.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyTail.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_eff1 env rho eff2 (WriteAbs w)
      phi_summary_tail heap_summary_tail theta_tail HSummaryTail)
    as (phi_eff2 & heap_eff2 & theta_val &
        phi_write & heap_write & theta_write &
        HEff2 & HWriteSummary & _ & _ & HTraceTail).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary_tail phi_eff2 phi_write
      HReadOnlyTail HTraceTail) as HReadOnlyEff2.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ea stty ctxt rgns ty_loc static_loc
      phi_loc heap_loc (Loc w l)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcLoc
      (StepsPhiN_to_StepsPhi _ _ _ _ HLoc) HReadOnlyStaticLoc)
    as HHeapLoc.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff1) phi_eff1
      (StDone heap_eff1 (Eff theta_loc))
      HEff1 HReadOnlyEff1) as HHeapEff1.
  simpl in HHeapEff1.
  subst heap_loc.
  subst heap_eff1.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff2) phi_eff2
      (StDone heap_eff2 (Eff theta_val))
      HEff2 HReadOnlyEff2) as HHeapEff2.
  simpl in HHeapEff2.
  subst heap_eff2.
  pose proof
    (HBelow
      n_loc heap heap env rho ea eff1
      phi_loc heap (Loc w l)
      phi_eff1 heap theta_loc
      stty ctxt rgns ty_loc static_loc
      HLtLoc (SummaryReplayCompatibleForExpr_refl env rho eff1 heap)
      HBTLoc HLoc HEff1 HReadOnlyEff1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcLoc) as HLocSound.
  pose proof
    (HBelow
      n_val heap heap env rho ev eff2
      phi_val heap_val v
      phi_eff2 heap theta_val
      stty ctxt rgns ty_val static_val
      HLtVal (SummaryReplayCompatibleForExpr_refl env rho eff2 heap)
      HBTVal HVal HEff2 HReadOnlyEff2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcVal) as HValSound.
  eapply
    (Correctness_soundness_ext_small_step_assign_abs_bt_summary_terminal_heterogeneous_case
      heap heap env rho w ea ev eff1 eff2
      phi_loc heap l phi_val heap_val v r
      phi_eff1 heap theta_loc
      phi_eff2 heap theta_val
      phi_summary heap_summary theta_summary
      phi_assign heap_assign v_assign); eauto.
  exact (StepsPhiN_to_StepsPhi _ _ _ _ HLoc).
  exact (StepsPhiN_to_StepsPhi _ _ _ _ HVal).
  exact (StepsPhiN_to_StepsPhi _ _ _ _ HAssign).
Qed.

Theorem Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_recursive_case :
  forall heap env rho ea ev eff1 eff2 r
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val,
    StepsPhi
      (initial_state heap env rho (Concat eff1 (Concat eff2 (WriteConc ea))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi
      (initial_state heap env rho (Assign (Rgn_Const true false r) ea ev))
      phi_assign (StDone heap_assign v_assign) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty_loc, static_loc) ->
    TcExp (ctxt, rgns, ev, ty_val, static_val) ->
    ReadOnlyStatic (fold_subst_eps rho static_loc) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ea, eff1) ->
    BackTriangle (ctxt, rgns, rho, ev, eff2) ->
    SmallStepCorrectnessRecursivePremise ->
    phi_assign ⋞ theta_summary.
Proof.
  intros heap env rho ea ev eff1 eff2 r
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val
    HSummary HAssign HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcLoc HTcVal HReadOnlyStaticLoc HReadOnlySummary
    HBTLoc HBTVal HRecursive.
  unfold SmallStepCorrectnessRecursivePremise in HRecursive.
  eapply Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_direct_case;
    try eassumption.
  - intros phi_loc heap_loc l phi_eff1 heap_eff1 theta_loc
      HLoc HEff1 HReadOnlyEff1.
    eapply (HRecursive
      heap env rho ea eff1
      phi_loc heap_loc (Loc (Rgn_Const true false r) l)
      phi_eff1 heap_eff1 theta_loc
      stty ctxt rgns ty_loc static_loc); eauto.
  - intros phi_val heap_val v phi_eff2 heap_eff2 theta_val
      HVal HEff2 HReadOnlyEff2.
    eapply (HRecursive
      heap env rho ev eff2
      phi_val heap_val v
      phi_eff2 heap_eff2 theta_val
      stty ctxt rgns ty_val static_val); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_address_agreement_case :
  forall heap heap_summary_start env rho ea ev eff1 eff2
    phi_loc heap_loc r l phi_val heap_val v
    phi_eff1 heap_eff1 theta_loc
    phi_eff2 heap_eff2 theta_val
    phi_loc_summary heap_loc_summary
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign,
    StepsPhi (initial_state heap env rho ea) phi_loc
      (StDone heap_loc (Loc (Rgn_Const true false r) l)) ->
    StepsPhi (initial_state heap_loc env rho ev) phi_val
      (StDone heap_val v) ->
    StepsPhi (initial_state heap_summary_start env rho eff1) phi_eff1
      (StDone heap_eff1 (Eff theta_loc)) ->
    StepsPhi (initial_state heap_eff1 env rho eff2) phi_eff2
      (StDone heap_eff2 (Eff theta_val)) ->
    StepsPhi (initial_state heap_eff2 env rho ea) phi_loc_summary
      (StDone heap_loc_summary (Loc (Rgn_Const true false r) l)) ->
    find_H (r, l) heap_val <> None ->
    StepsPhi
      (initial_state heap_summary_start env rho
        (Concat eff1 (Concat eff2 (WriteConc ea))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi
      (initial_state heap env rho (Assign (Rgn_Const true false r) ea ev))
      phi_assign (StDone heap_assign v_assign) ->
    phi_loc ⋞ theta_loc ->
    phi_val ⋞ theta_val ->
    phi_assign ⋞ theta_summary.
Proof.
  intros heap heap_summary_start env rho ea ev eff1 eff2
    phi_loc heap_loc r l phi_val heap_val v
    phi_eff1 heap_eff1 theta_loc
    phi_eff2 heap_eff2 theta_val
    phi_loc_summary heap_loc_summary
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    HLoc HVal HEff1 HEff2 HLocSummary HFindH HSummary HAssign
    HLocSound HValSound.
  destruct
    (StepsPhi_writeconc_from_arg
      heap_eff2 env rho ea phi_loc_summary heap_loc_summary r l
      HLocSummary)
    as (phi_action & HAction & _).
  pose proof
    (StepsPhi_right_nested_concat_summary_terminal_theta
      heap_summary_start env rho eff1 eff2 (WriteConc ea)
      phi_eff1 heap_eff1 theta_loc
      phi_eff2 heap_eff2 theta_val
      phi_action heap_loc_summary (Some (singleton_set (CA_WriteConc r l)))
      phi_summary heap_summary theta_summary
      HEff1 HEff2 HAction HSummary) as HTheta.
  subst theta_summary.
  eapply (Correctness_soundness_ext_small_step_assign_conc_terminal_case
    heap env rho (Rgn_Const true false r) ea ev
    phi_loc heap_loc l phi_val heap_val v r theta_loc theta_val
    phi_assign heap_assign v_assign); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_heterogeneous_heap_case :
  forall heap heap_summary_start env rho ea ev eff1 eff2
    phi_loc heap_loc r l phi_val heap_val v
    phi_eff1 heap_eff1 theta_loc
    phi_eff2 heap_eff2 theta_val
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign,
    StepsPhi (initial_state heap env rho ea) phi_loc
      (StDone heap_loc (Loc (Rgn_Const true false r) l)) ->
    StepsPhi (initial_state heap_loc env rho ev) phi_val
      (StDone heap_val v) ->
    StepsPhi (initial_state heap_summary_start env rho eff1) phi_eff1
      (StDone heap_eff1 (Eff theta_loc)) ->
    StepsPhi (initial_state heap_eff1 env rho eff2) phi_eff2
      (StDone heap_eff2 (Eff theta_val)) ->
    HeterogeneousHeapForExpr env rho ea heap heap_eff2 ->
    ReadOnlyPhi phi_loc ->
    find_H (r, l) heap_val <> None ->
    StepsPhi
      (initial_state heap_summary_start env rho
        (Concat eff1 (Concat eff2 (WriteConc ea))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi
      (initial_state heap env rho (Assign (Rgn_Const true false r) ea ev))
      phi_assign (StDone heap_assign v_assign) ->
    phi_loc ⋞ theta_loc ->
    phi_val ⋞ theta_val ->
    phi_assign ⋞ theta_summary.
Proof.
  intros heap heap_summary_start env rho ea ev eff1 eff2
    phi_loc heap_loc r l phi_val heap_val v
    phi_eff1 heap_eff1 theta_loc
    phi_eff2 heap_eff2 theta_val
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    HLoc HVal HEff1 HEff2 HHeapCompat HReadOnlyLoc HFindH
    HSummary HAssign HLocSound HValSound.
  destruct
    (HHeapCompat phi_loc heap_loc (Loc (Rgn_Const true false r) l)
      HLoc HReadOnlyLoc)
    as (_ & phi_loc_summary & heap_loc_summary & HLocSummary & _).
  eapply
    (Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_address_agreement_case
      heap heap_summary_start env rho ea ev eff1 eff2
      phi_loc heap_loc r l phi_val heap_val v
      phi_eff1 heap_eff1 theta_loc
      phi_eff2 heap_eff2 theta_val
      phi_loc_summary heap_loc_summary
      phi_summary heap_summary theta_summary
      phi_assign heap_assign v_assign); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_heterogeneous_recursive_case :
  forall heap heap_summary_start env rho ea ev eff1 eff2 r
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val,
    StepsPhi
      (initial_state heap_summary_start env rho
        (Concat eff1 (Concat eff2 (WriteConc ea))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi
      (initial_state heap env rho (Assign (Rgn_Const true false r) ea ev))
      phi_assign (StDone heap_assign v_assign) ->
    HeterogeneousHeapForExpr env rho ea heap heap_summary_start ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty_loc, static_loc) ->
    TcExp (ctxt, rgns, ev, ty_val, static_val) ->
    ReadOnlyStatic (fold_subst_eps rho static_loc) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ea, eff1) ->
    BackTriangle (ctxt, rgns, rho, ev, eff2) ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi_assign ⋞ theta_summary.
Proof.
  intros heap heap_summary_start env rho ea ev eff1 eff2 r
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val
    HSummary HAssign HHeapCompat HTcHeap HHeapShape HTcRho HTcInc
    HTcEnv HEnvShape HTcLoc HTcVal HReadOnlyStaticLoc HReadOnlySummary
    HBTLoc HBTVal HRecursive.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremise in HRecursive.
  destruct
    (StepsPhi_assign_terminal_decompose
      heap env rho (Rgn_Const true false r) ea ev
      phi_assign heap_assign v_assign HAssign)
    as (phi_loc & heap_loc & l & phi_val & heap_val & v & r_write &
        HLoc & HVal & HFindR & HFindH & _ & _ & _).
  simpl in HFindR.
  inversion HFindR; subst r_write.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_summary_start env rho eff1 (Concat eff2 (WriteConc ea))
      phi_summary heap_summary theta_summary HSummary)
    as (phi_eff1 & heap_eff1 & theta_loc &
        phi_summary_tail & heap_summary_tail & theta_tail &
        HEff1 & HSummaryTail & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyEff1.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyTail.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_eff1 env rho eff2 (WriteConc ea)
      phi_summary_tail heap_summary_tail theta_tail HSummaryTail)
    as (phi_eff2 & heap_eff2 & theta_val &
        phi_write & heap_write & theta_write &
        HEff2 & HWriteSummary & _ & _ & HTraceTail).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary_tail phi_eff2 phi_write
      HReadOnlyTail HTraceTail) as HReadOnlyEff2.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ea stty ctxt rgns ty_loc static_loc
      phi_loc heap_loc (Loc (Rgn_Const true false r) l)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcLoc
      HLoc HReadOnlyStaticLoc) as HHeapLoc.
  pose proof
    (StepsPhi_typed_readonly_static_readonly_phi
      heap env rho ea stty ctxt rgns ty_loc static_loc
      phi_loc heap_loc (Loc (Rgn_Const true false r) l)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcLoc
      HLoc HReadOnlyStaticLoc) as HReadOnlyLoc.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap_summary_start env rho eff1) phi_eff1
      (StDone heap_eff1 (Eff theta_loc))
      HEff1 HReadOnlyEff1) as HHeapEff1.
  simpl in HHeapEff1.
  subst heap_loc.
  symmetry in HHeapEff1.
  subst heap_eff1.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap_summary_start env rho eff2) phi_eff2
      (StDone heap_eff2 (Eff theta_val))
      HEff2 HReadOnlyEff2) as HHeapEff2.
  simpl in HHeapEff2.
  symmetry in HHeapEff2.
  subst heap_eff2.
  pose proof
    (HRecursive
      heap heap_summary_start env rho ea eff1
      phi_loc heap (Loc (Rgn_Const true false r) l)
      phi_eff1 heap_summary_start theta_loc
      stty ctxt rgns ty_loc static_loc
      HBTLoc HLoc HEff1 HReadOnlyEff1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcLoc) as HLocSound.
  pose proof
    (HRecursive
      heap heap_summary_start env rho ev eff2
      phi_val heap_val v
      phi_eff2 heap_summary_start theta_val
      stty ctxt rgns ty_val static_val
      HBTVal HVal HEff2 HReadOnlyEff2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcVal) as HValSound.
  eapply
    (Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_heterogeneous_heap_case
      heap heap_summary_start env rho ea ev eff1 eff2
      phi_loc heap r l phi_val heap_val v
      phi_eff1 heap_summary_start theta_loc
      phi_eff2 heap_summary_start theta_val
      phi_summary heap_summary theta_summary
      phi_assign heap_assign v_assign); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_heap_compatible_recursive_case :
  forall heap heap_summary_start env rho ea ev eff1 eff2 r
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val,
    StepsPhi
      (initial_state heap_summary_start env rho
        (Concat eff1 (Concat eff2 (WriteConc ea))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi
      (initial_state heap env rho (Assign (Rgn_Const true false r) ea ev))
      phi_assign (StDone heap_assign v_assign) ->
    HeterogeneousHeapForExpr env rho ea heap heap_summary_start ->
    HeterogeneousHeapForExpr env rho ev heap heap_summary_start ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty_loc, static_loc) ->
    TcExp (ctxt, rgns, ev, ty_val, static_val) ->
    ReadOnlyStatic (fold_subst_eps rho static_loc) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ea, eff1) ->
    BackTriangle (ctxt, rgns, rho, ev, eff2) ->
    SmallStepCorrectnessHeapCompatibleRecursivePremise ->
    phi_assign ⋞ theta_summary.
Proof.
  intros heap heap_summary_start env rho ea ev eff1 eff2 r
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val
    HSummary HAssign HHeapCompatLoc HHeapCompatVal HTcHeap HHeapShape
    HTcRho HTcInc HTcEnv HEnvShape HTcLoc HTcVal HReadOnlyStaticLoc
    HReadOnlySummary HBTLoc HBTVal HRecursive.
  unfold SmallStepCorrectnessHeapCompatibleRecursivePremise in HRecursive.
  destruct
    (StepsPhi_assign_terminal_decompose
      heap env rho (Rgn_Const true false r) ea ev
      phi_assign heap_assign v_assign HAssign)
    as (phi_loc & heap_loc & l & phi_val & heap_val & v & r_write &
        HLoc & HVal & HFindR & HFindH & _ & _ & _).
  simpl in HFindR.
  inversion HFindR; subst r_write.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_summary_start env rho eff1 (Concat eff2 (WriteConc ea))
      phi_summary heap_summary theta_summary HSummary)
    as (phi_eff1 & heap_eff1 & theta_loc &
        phi_summary_tail & heap_summary_tail & theta_tail &
        HEff1 & HSummaryTail & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyEff1.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyTail.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_eff1 env rho eff2 (WriteConc ea)
      phi_summary_tail heap_summary_tail theta_tail HSummaryTail)
    as (phi_eff2 & heap_eff2 & theta_val &
        phi_write & heap_write & theta_write &
        HEff2 & HWriteSummary & _ & _ & HTraceTail).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary_tail phi_eff2 phi_write
      HReadOnlyTail HTraceTail) as HReadOnlyEff2.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ea stty ctxt rgns ty_loc static_loc
      phi_loc heap_loc (Loc (Rgn_Const true false r) l)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcLoc
      HLoc HReadOnlyStaticLoc) as HHeapLoc.
  pose proof
    (StepsPhi_typed_readonly_static_readonly_phi
      heap env rho ea stty ctxt rgns ty_loc static_loc
      phi_loc heap_loc (Loc (Rgn_Const true false r) l)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcLoc
      HLoc HReadOnlyStaticLoc) as HReadOnlyLoc.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap_summary_start env rho eff1) phi_eff1
      (StDone heap_eff1 (Eff theta_loc))
      HEff1 HReadOnlyEff1) as HHeapEff1.
  simpl in HHeapEff1.
  subst heap_loc.
  symmetry in HHeapEff1.
  subst heap_eff1.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap_summary_start env rho eff2) phi_eff2
      (StDone heap_eff2 (Eff theta_val))
      HEff2 HReadOnlyEff2) as HHeapEff2.
  simpl in HHeapEff2.
  symmetry in HHeapEff2.
  subst heap_eff2.
  pose proof
    (HRecursive
      heap heap_summary_start env rho ea eff1
      phi_loc heap (Loc (Rgn_Const true false r) l)
      phi_eff1 heap_summary_start theta_loc
      stty ctxt rgns ty_loc static_loc
      HHeapCompatLoc HBTLoc HLoc HEff1 HReadOnlyEff1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcLoc) as HLocSound.
  pose proof
    (HRecursive
      heap heap_summary_start env rho ev eff2
      phi_val heap_val v
      phi_eff2 heap_summary_start theta_val
      stty ctxt rgns ty_val static_val
      HHeapCompatVal HBTVal HVal HEff2 HReadOnlyEff2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcVal) as HValSound.
  eapply
    (Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_heterogeneous_heap_case
      heap heap_summary_start env rho ea ev eff1 eff2
      phi_loc heap r l phi_val heap_val v
      phi_eff1 heap_summary_start theta_loc
      phi_eff2 heap_summary_start theta_val
      phi_summary heap_summary theta_summary
	      phi_assign heap_assign v_assign); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_heterogeneous_below_case :
  forall n heap heap_summary_start env rho ea ev eff1 eff2 r
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val,
    StepsPhi
      (initial_state heap_summary_start env rho
        (Concat eff1 (Concat eff2 (WriteConc ea))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhiN n
      (initial_state heap env rho (Assign (Rgn_Const true false r) ea ev))
      phi_assign (StDone heap_assign v_assign) ->
    HeterogeneousHeapForExpr env rho ea heap heap_summary_start ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty_loc, static_loc) ->
    TcExp (ctxt, rgns, ev, ty_val, static_val) ->
    ReadOnlyStatic (fold_subst_eps rho static_loc) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ea, eff1) ->
    BackTriangle (ctxt, rgns, rho, ev, eff2) ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi_assign ⋞ theta_summary.
Proof.
  intros n heap heap_summary_start env rho ea ev eff1 eff2 r
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val
    HSummary HAssign HHeapCompatLoc HTcHeap HHeapShape HTcRho HTcInc
    HTcEnv HEnvShape HTcLoc HTcVal HReadOnlyStaticLoc HReadOnlySummary
    HBTLoc HBTVal HBelow.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_assign_terminal_decompose_counts
      n heap env rho (Rgn_Const true false r) ea ev
      phi_assign heap_assign v_assign HAssign)
    as (n_loc & phi_loc & heap_loc & l &
        n_val & phi_val & heap_val & v & r_write &
        HLtLoc & HLtVal & HLoc & HVal &
        HFindR & HFindH & _ & _ & _).
  simpl in HFindR.
  inversion HFindR; subst r_write.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_summary_start env rho eff1 (Concat eff2 (WriteConc ea))
      phi_summary heap_summary theta_summary HSummary)
    as (phi_eff1 & heap_eff1 & theta_loc &
        phi_summary_tail & heap_summary_tail & theta_tail &
        HEff1 & HSummaryTail & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyEff1.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyTail.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_eff1 env rho eff2 (WriteConc ea)
      phi_summary_tail heap_summary_tail theta_tail HSummaryTail)
    as (phi_eff2 & heap_eff2 & theta_val &
        phi_write & heap_write & theta_write &
        HEff2 & HWriteSummary & _ & _ & HTraceTail).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary_tail phi_eff2 phi_write
      HReadOnlyTail HTraceTail) as HReadOnlyEff2.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ea stty ctxt rgns ty_loc static_loc
      phi_loc heap_loc (Loc (Rgn_Const true false r) l)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcLoc
      (StepsPhiN_to_StepsPhi _ _ _ _ HLoc) HReadOnlyStaticLoc) as HHeapLoc.
  pose proof
    (StepsPhi_typed_readonly_static_readonly_phi
      heap env rho ea stty ctxt rgns ty_loc static_loc
      phi_loc heap_loc (Loc (Rgn_Const true false r) l)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcLoc
      (StepsPhiN_to_StepsPhi _ _ _ _ HLoc) HReadOnlyStaticLoc) as HReadOnlyLoc.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap_summary_start env rho eff1) phi_eff1
      (StDone heap_eff1 (Eff theta_loc))
      HEff1 HReadOnlyEff1) as HHeapEff1.
  simpl in HHeapEff1.
  subst heap_loc.
  symmetry in HHeapEff1.
  subst heap_eff1.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap_summary_start env rho eff2) phi_eff2
      (StDone heap_eff2 (Eff theta_val))
      HEff2 HReadOnlyEff2) as HHeapEff2.
  simpl in HHeapEff2.
  symmetry in HHeapEff2.
  subst heap_eff2.
  pose proof
    (HBelow
      n_loc heap heap_summary_start env rho ea eff1
      phi_loc heap (Loc (Rgn_Const true false r) l)
      phi_eff1 heap_summary_start theta_loc
      stty ctxt rgns ty_loc static_loc
      HLtLoc HBTLoc HLoc HEff1 HReadOnlyEff1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcLoc) as HLocSound.
  pose proof
    (HBelow
      n_val heap heap_summary_start env rho ev eff2
      phi_val heap_val v
      phi_eff2 heap_summary_start theta_val
      stty ctxt rgns ty_val static_val
      HLtVal HBTVal HVal HEff2 HReadOnlyEff2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcVal) as HValSound.
  eapply
    (Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_heterogeneous_heap_case
      heap heap_summary_start env rho ea ev eff1 eff2
      phi_loc heap r l phi_val heap_val v
      phi_eff1 heap_summary_start theta_loc
      phi_eff2 heap_summary_start theta_val
      phi_summary heap_summary theta_summary
      phi_assign heap_assign v_assign); eauto.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HLoc).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HVal).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HAssign).
Qed.

Theorem Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_summary_replay_below_case :
  forall n heap env rho ea ev eff1 eff2 r
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val,
    StepsPhi
      (initial_state heap env rho
        (Concat eff1 (Concat eff2 (WriteConc ea))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhiN n
      (initial_state heap env rho (Assign (Rgn_Const true false r) ea ev))
      phi_assign (StDone heap_assign v_assign) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty_loc, static_loc) ->
    TcExp (ctxt, rgns, ev, ty_val, static_val) ->
    ReadOnlyStatic (fold_subst_eps rho static_loc) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ea, eff1) ->
    BackTriangle (ctxt, rgns, rho, ev, eff2) ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi_assign ⋞ theta_summary.
Proof.
  intros n heap env rho ea ev eff1 eff2 r
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val
    HSummary HAssign HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcLoc HTcVal HReadOnlyStaticLoc HReadOnlySummary
    HBTLoc HBTVal HBelow.
  unfold SmallStepCorrectnessSummaryReplayRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_assign_terminal_decompose_counts
      n heap env rho (Rgn_Const true false r) ea ev
      phi_assign heap_assign v_assign HAssign)
    as (n_loc & phi_loc & heap_loc & l &
        n_val & phi_val & heap_val & v & r_write &
        HLtLoc & HLtVal & HLoc & HVal &
        HFindR & HFindH & _ & _ & _).
  simpl in HFindR.
  inversion HFindR; subst r_write.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 (Concat eff2 (WriteConc ea))
      phi_summary heap_summary theta_summary HSummary)
    as (phi_eff1 & heap_eff1 & theta_loc &
        phi_summary_tail & heap_summary_tail & theta_tail &
        HEff1 & HSummaryTail & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyEff1.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_eff1 phi_summary_tail
      HReadOnlySummary HTraceSummary) as HReadOnlyTail.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_eff1 env rho eff2 (WriteConc ea)
      phi_summary_tail heap_summary_tail theta_tail HSummaryTail)
    as (phi_eff2 & heap_eff2 & theta_val &
        phi_write & heap_write & theta_write &
        HEff2 & HWriteSummary & _ & _ & HTraceTail).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary_tail phi_eff2 phi_write
      HReadOnlyTail HTraceTail) as HReadOnlyEff2.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ea stty ctxt rgns ty_loc static_loc
      phi_loc heap_loc (Loc (Rgn_Const true false r) l)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcLoc
      (StepsPhiN_to_StepsPhi _ _ _ _ HLoc) HReadOnlyStaticLoc)
    as HHeapLoc.
  pose proof
    (StepsPhi_typed_readonly_static_readonly_phi
      heap env rho ea stty ctxt rgns ty_loc static_loc
      phi_loc heap_loc (Loc (Rgn_Const true false r) l)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcLoc
      (StepsPhiN_to_StepsPhi _ _ _ _ HLoc) HReadOnlyStaticLoc)
    as HReadOnlyLoc.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff1) phi_eff1
      (StDone heap_eff1 (Eff theta_loc))
      HEff1 HReadOnlyEff1) as HHeapEff1.
  simpl in HHeapEff1.
  subst heap_loc.
  subst heap_eff1.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff2) phi_eff2
      (StDone heap_eff2 (Eff theta_val))
      HEff2 HReadOnlyEff2) as HHeapEff2.
  simpl in HHeapEff2.
  subst heap_eff2.
  pose proof
    (HBelow
      n_loc heap heap env rho ea eff1
      phi_loc heap (Loc (Rgn_Const true false r) l)
      phi_eff1 heap theta_loc
      stty ctxt rgns ty_loc static_loc
      HLtLoc (SummaryReplayCompatibleForExpr_refl env rho eff1 heap)
      HBTLoc HLoc HEff1 HReadOnlyEff1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcLoc) as HLocSound.
  pose proof
    (HBelow
      n_val heap heap env rho ev eff2
      phi_val heap_val v
      phi_eff2 heap theta_val
      stty ctxt rgns ty_val static_val
      HLtVal (SummaryReplayCompatibleForExpr_refl env rho eff2 heap)
      HBTVal HVal HEff2 HReadOnlyEff2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcVal) as HValSound.
  eapply
    (Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_heterogeneous_heap_case
      heap heap env rho ea ev eff1 eff2
      phi_loc heap r l phi_val heap_val v
      phi_eff1 heap theta_loc
      phi_eff2 heap theta_val
      phi_summary heap_summary theta_summary
      phi_assign heap_assign v_assign).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HLoc).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HVal).
  - exact HEff1.
  - exact HEff2.
  - apply HeterogeneousHeapForExpr_refl.
  - exact HReadOnlyLoc.
  - exact HFindH.
  - exact HSummary.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HAssign).
  - exact HLocSound.
  - exact HValSound.
Qed.

Theorem Correctness_soundness_ext_small_step_cond_summary_terminal_recursive_case :
  forall heap env rho e et ef efft efff
    phi_cond heap_cond v_cond
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e static_e ty_t static_t ty_f static_f,
    StepsPhi (initial_state heap env rho (Cond e et ef)) phi_cond
      (StDone heap_cond v_cond) ->
    StepsPhi (initial_state heap env rho (Cond e efft efff)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    TcExp (ctxt, rgns, et, ty_t, static_t) ->
    TcExp (ctxt, rgns, ef, ty_f, static_f) ->
    ReadOnlyStatic (fold_subst_eps rho static_e) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e, Empty) ->
    BackTriangle (ctxt, rgns, rho, et, efft) ->
    BackTriangle (ctxt, rgns, rho, ef, efff) ->
    SmallStepCorrectnessRecursivePremise ->
    phi_cond ⋞ theta_summary.
Proof.
  intros heap env rho e et ef efft efff
    phi_cond heap_cond v_cond
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e static_e ty_t static_t ty_f static_f
    HCond HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcGuard HTcTrue HTcFalse HReadOnlyStaticGuard HReadOnlySummary
    HBTGuard HBTTrue HBTFalse HRecursive.
  unfold SmallStepCorrectnessRecursivePremise in HRecursive.
  eapply Correctness_soundness_ext_small_step_cond_summary_terminal_direct_case;
    try eassumption.
  - intros phi_guard heap_guard b HGuard.
    pose proof (initial_empty_steps_phi_done heap env rho) as HEmpty.
    assert (HReadOnlyEmpty :
      ReadOnlyPhi
        (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))).
    {
      apply ReadOnlyPhi_of_phi_as_list_nil.
      reflexivity.
    }
    eapply (HRecursive
      heap env rho e Empty
      phi_guard heap_guard (Bit b)
      (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))
      heap Theta_Empty
      stty ctxt rgns ty_e static_e); eauto.
  - intros phi_branch heap_branch v
      phi_branch_summary heap_branch_summary theta_branch
      HBranch HBranchSummary HReadOnlyBranchSummary.
    eapply (HRecursive
      heap env rho et efft
      phi_branch heap_branch v
      phi_branch_summary heap_branch_summary theta_branch
      stty ctxt rgns ty_t static_t); eauto.
  - intros phi_branch heap_branch v
      phi_branch_summary heap_branch_summary theta_branch
      HBranch HBranchSummary HReadOnlyBranchSummary.
    eapply (HRecursive
      heap env rho ef efff
      phi_branch heap_branch v
      phi_branch_summary heap_branch_summary theta_branch
	      stty ctxt rgns ty_f static_f); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_cond_summary_terminal_below_case :
  forall n heap env rho e et ef efft efff
    phi_cond heap_cond v_cond
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e static_e ty_t static_t ty_f static_f,
    StepsPhiN n (initial_state heap env rho (Cond e et ef)) phi_cond
      (StDone heap_cond v_cond) ->
    StepsPhi (initial_state heap env rho (Cond e efft efff)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    TcExp (ctxt, rgns, et, ty_t, static_t) ->
    TcExp (ctxt, rgns, ef, ty_f, static_f) ->
    ReadOnlyStatic (fold_subst_eps rho static_e) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e, Empty) ->
    BackTriangle (ctxt, rgns, rho, et, efft) ->
    BackTriangle (ctxt, rgns, rho, ef, efff) ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi_cond ⋞ theta_summary.
Proof.
  intros n heap env rho e et ef efft efff
    phi_cond heap_cond v_cond
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e static_e ty_t static_t ty_f static_f
    HCond HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcGuard HTcTrue HTcFalse HReadOnlyStaticGuard HReadOnlySummary
    HBTGuard HBTTrue HBTFalse HBelow.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremiseBelow in HBelow.
  assert (HEmpty : StepsPhi
    (initial_state heap env rho Empty)
    (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))
    (StDone heap (Eff Theta_Empty))).
  {
    apply initial_empty_steps_phi_done.
  }
  assert (HReadOnlyEmpty :
    ReadOnlyPhi
      (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))).
  {
    apply ReadOnlyPhi_of_phi_as_list_nil.
    reflexivity.
  }
  destruct
    (StepsPhiN_cond_terminal_decompose_counts
      n heap env rho e et ef phi_cond heap_cond v_cond HCond)
    as
      [(n_guard & phi_guard & heap_guard &
        n_branch & phi_branch & heap_branch &
        HLtGuard & HLtBranch & HGuard & HBranch & _ & _) |
       (n_guard & phi_guard & heap_guard &
        n_branch & phi_branch & heap_branch &
        HLtGuard & HLtBranch & HGuard & HBranch & _ & _)].
  - destruct
      (StepsPhi_cond_terminal_decompose
        heap env rho e efft efff phi_summary heap_summary
        (Eff theta_summary) HSummary)
      as
        [(phi_guard_summary & heap_guard_summary &
          phi_branch_summary & heap_branch_summary &
          HGuardSummary & HBranchSummary & _ & HTraceSummary) |
         (phi_guard_summary & heap_guard_summary &
          phi_branch_summary & heap_branch_summary &
          HGuardSummary & HBranchSummary & _ & HTraceSummary)].
    + pose proof
        (ReadOnlyPhi_app_list_left
          phi_summary phi_guard_summary phi_branch_summary
          HReadOnlySummary HTraceSummary) as HReadOnlyGuardSummary.
      pose proof
        (ReadOnlyPhi_app_list_right
          phi_summary phi_guard_summary phi_branch_summary
          HReadOnlySummary HTraceSummary) as HReadOnlyBranchSummary.
      pose proof
        (StepsPhi_typed_readonly_static_preserves_heap
          heap env rho e stty ctxt rgns ty_e static_e
          phi_guard heap_guard (Bit true)
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcGuard
          (StepsPhiN_to_StepsPhi _ _ _ _ HGuard)
          HReadOnlyStaticGuard) as HHeapGuard.
      pose proof
        (StepsPhi_readonly_preserves_heap
          (initial_state heap env rho e) phi_guard_summary
          (StDone heap_guard_summary (Bit true))
          HGuardSummary HReadOnlyGuardSummary) as HHeapGuardSummary.
      simpl in HHeapGuardSummary.
      subst heap_guard.
      symmetry in HHeapGuardSummary.
      subst heap_guard_summary.
      pose proof
        (HBelow
          n_guard heap heap env rho e Empty
          phi_guard heap (Bit true)
          (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))
          heap Theta_Empty
          stty ctxt rgns ty_e static_e
          HLtGuard HBTGuard HGuard HEmpty HReadOnlyEmpty
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcGuard) as HGuardSound.
      pose proof
        (HBelow
          n_branch heap heap env rho et efft
          phi_branch heap_branch v_cond
          phi_branch_summary heap_branch_summary theta_summary
          stty ctxt rgns ty_t static_t
          HLtBranch HBTTrue HBranch HBranchSummary HReadOnlyBranchSummary
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcTrue) as HBranchSound.
      eapply (Correctness_soundness_ext_small_step_cond_true_terminal_case
        heap env rho e et ef
        phi_guard heap phi_branch heap_branch v_cond theta_summary
        phi_cond heap_cond v_cond); eauto.
      exact (StepsPhiN_to_StepsPhi _ _ _ _ HGuard).
      exact (StepsPhiN_to_StepsPhi _ _ _ _ HBranch).
      exact (StepsPhiN_to_StepsPhi _ _ _ _ HCond).
    + destruct
        (StepsPhi_terminal_deterministic
          (initial_state heap env rho e)
          (phi_guard) heap_guard (Bit true)
          phi_guard_summary heap_guard_summary (Bit false)
          (StepsPhiN_to_StepsPhi _ _ _ _ HGuard) HGuardSummary)
        as [_ [_ HValue]].
      inversion HValue.
  - destruct
      (StepsPhi_cond_terminal_decompose
        heap env rho e efft efff phi_summary heap_summary
        (Eff theta_summary) HSummary)
      as
        [(phi_guard_summary & heap_guard_summary &
          phi_branch_summary & heap_branch_summary &
          HGuardSummary & HBranchSummary & _ & HTraceSummary) |
         (phi_guard_summary & heap_guard_summary &
          phi_branch_summary & heap_branch_summary &
          HGuardSummary & HBranchSummary & _ & HTraceSummary)].
    + destruct
        (StepsPhi_terminal_deterministic
          (initial_state heap env rho e)
          phi_guard heap_guard (Bit false)
          phi_guard_summary heap_guard_summary (Bit true)
          (StepsPhiN_to_StepsPhi _ _ _ _ HGuard) HGuardSummary)
        as [_ [_ HValue]].
      inversion HValue.
    + pose proof
        (ReadOnlyPhi_app_list_left
          phi_summary phi_guard_summary phi_branch_summary
          HReadOnlySummary HTraceSummary) as HReadOnlyGuardSummary.
      pose proof
        (ReadOnlyPhi_app_list_right
          phi_summary phi_guard_summary phi_branch_summary
          HReadOnlySummary HTraceSummary) as HReadOnlyBranchSummary.
      pose proof
        (StepsPhi_typed_readonly_static_preserves_heap
          heap env rho e stty ctxt rgns ty_e static_e
          phi_guard heap_guard (Bit false)
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcGuard
          (StepsPhiN_to_StepsPhi _ _ _ _ HGuard)
          HReadOnlyStaticGuard) as HHeapGuard.
      pose proof
        (StepsPhi_readonly_preserves_heap
          (initial_state heap env rho e) phi_guard_summary
          (StDone heap_guard_summary (Bit false))
          HGuardSummary HReadOnlyGuardSummary) as HHeapGuardSummary.
      simpl in HHeapGuardSummary.
      subst heap_guard.
      symmetry in HHeapGuardSummary.
      subst heap_guard_summary.
      pose proof
        (HBelow
          n_guard heap heap env rho e Empty
          phi_guard heap (Bit false)
          (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))
          heap Theta_Empty
          stty ctxt rgns ty_e static_e
          HLtGuard HBTGuard HGuard HEmpty HReadOnlyEmpty
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcGuard) as HGuardSound.
      pose proof
        (HBelow
          n_branch heap heap env rho ef efff
          phi_branch heap_branch v_cond
          phi_branch_summary heap_branch_summary theta_summary
          stty ctxt rgns ty_f static_f
          HLtBranch HBTFalse HBranch HBranchSummary HReadOnlyBranchSummary
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcFalse) as HBranchSound.
      eapply (Correctness_soundness_ext_small_step_cond_false_terminal_case
        heap env rho e et ef
        phi_guard heap phi_branch heap_branch v_cond theta_summary
        phi_cond heap_cond v_cond); eauto.
      exact (StepsPhiN_to_StepsPhi _ _ _ _ HGuard).
      exact (StepsPhiN_to_StepsPhi _ _ _ _ HBranch).
      exact (StepsPhiN_to_StepsPhi _ _ _ _ HCond).
Qed.

Theorem Correctness_soundness_ext_small_step_cond_summary_terminal_summary_replay_below_case :
  forall n heap env rho e et ef efft efff
    phi_cond heap_cond v_cond
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e static_e ty_t static_t ty_f static_f,
    StepsPhiN n (initial_state heap env rho (Cond e et ef)) phi_cond
      (StDone heap_cond v_cond) ->
    StepsPhi (initial_state heap env rho (Cond e efft efff)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    TcExp (ctxt, rgns, et, ty_t, static_t) ->
    TcExp (ctxt, rgns, ef, ty_f, static_f) ->
    ReadOnlyStatic (fold_subst_eps rho static_e) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e, Empty) ->
    BackTriangle (ctxt, rgns, rho, et, efft) ->
    BackTriangle (ctxt, rgns, rho, ef, efff) ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi_cond ⋞ theta_summary.
Proof.
  intros n heap env rho e et ef efft efff
    phi_cond heap_cond v_cond
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e static_e ty_t static_t ty_f static_f
    HCond HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcGuard HTcTrue HTcFalse HReadOnlyStaticGuard HReadOnlySummary
    HBTGuard HBTTrue HBTFalse HBelow.
  unfold SmallStepCorrectnessSummaryReplayRecursivePremiseBelow in HBelow.
  assert (HEmpty : StepsPhi
    (initial_state heap env rho Empty)
    (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))
    (StDone heap (Eff Theta_Empty))).
  {
    apply initial_empty_steps_phi_done.
  }
  assert (HReadOnlyEmpty :
    ReadOnlyPhi
      (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))).
  {
    apply ReadOnlyPhi_of_phi_as_list_nil.
    reflexivity.
  }
  destruct
    (StepsPhiN_cond_terminal_decompose_counts
      n heap env rho e et ef phi_cond heap_cond v_cond HCond)
    as
      [(n_guard & phi_guard & heap_guard &
        n_branch & phi_branch & heap_branch &
        HLtGuard & HLtBranch & HGuard & HBranch & _ & _) |
       (n_guard & phi_guard & heap_guard &
        n_branch & phi_branch & heap_branch &
        HLtGuard & HLtBranch & HGuard & HBranch & _ & _)].
  - destruct
      (StepsPhi_cond_terminal_decompose
        heap env rho e efft efff phi_summary heap_summary
        (Eff theta_summary) HSummary)
      as
        [(phi_guard_summary & heap_guard_summary &
          phi_branch_summary & heap_branch_summary &
          HGuardSummary & HBranchSummary & _ & HTraceSummary) |
         (phi_guard_summary & heap_guard_summary &
          phi_branch_summary & heap_branch_summary &
          HGuardSummary & HBranchSummary & _ & HTraceSummary)].
    + pose proof
        (ReadOnlyPhi_app_list_left
          phi_summary phi_guard_summary phi_branch_summary
          HReadOnlySummary HTraceSummary) as HReadOnlyGuardSummary.
      pose proof
        (ReadOnlyPhi_app_list_right
          phi_summary phi_guard_summary phi_branch_summary
          HReadOnlySummary HTraceSummary) as HReadOnlyBranchSummary.
      pose proof
        (StepsPhi_typed_readonly_static_preserves_heap
          heap env rho e stty ctxt rgns ty_e static_e
          phi_guard heap_guard (Bit true)
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcGuard
          (StepsPhiN_to_StepsPhi _ _ _ _ HGuard)
          HReadOnlyStaticGuard) as HHeapGuard.
      pose proof
        (StepsPhi_readonly_preserves_heap
          (initial_state heap env rho e) phi_guard_summary
          (StDone heap_guard_summary (Bit true))
          HGuardSummary HReadOnlyGuardSummary) as HHeapGuardSummary.
      simpl in HHeapGuardSummary.
      subst heap_guard.
      symmetry in HHeapGuardSummary.
      subst heap_guard_summary.
      pose proof
        (HBelow
          n_guard heap heap env rho e Empty
          phi_guard heap (Bit true)
          (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))
          heap Theta_Empty
          stty ctxt rgns ty_e static_e
          HLtGuard (SummaryReplayCompatibleForExpr_refl env rho Empty heap)
          HBTGuard HGuard HEmpty HReadOnlyEmpty
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcGuard) as HGuardSound.
      pose proof
        (HBelow
          n_branch heap heap env rho et efft
          phi_branch heap_branch v_cond
          phi_branch_summary heap_branch_summary theta_summary
          stty ctxt rgns ty_t static_t
          HLtBranch (SummaryReplayCompatibleForExpr_refl env rho efft heap)
          HBTTrue HBranch HBranchSummary HReadOnlyBranchSummary
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcTrue) as HBranchSound.
      eapply (Correctness_soundness_ext_small_step_cond_true_terminal_case
        heap env rho e et ef
        phi_guard heap phi_branch heap_branch v_cond theta_summary
        phi_cond heap_cond v_cond); eauto.
      exact (StepsPhiN_to_StepsPhi _ _ _ _ HGuard).
      exact (StepsPhiN_to_StepsPhi _ _ _ _ HBranch).
      exact (StepsPhiN_to_StepsPhi _ _ _ _ HCond).
    + destruct
        (StepsPhi_terminal_deterministic
          (initial_state heap env rho e)
          (phi_guard) heap_guard (Bit true)
          phi_guard_summary heap_guard_summary (Bit false)
          (StepsPhiN_to_StepsPhi _ _ _ _ HGuard) HGuardSummary)
        as [_ [_ HValue]].
      inversion HValue.
  - destruct
      (StepsPhi_cond_terminal_decompose
        heap env rho e efft efff phi_summary heap_summary
        (Eff theta_summary) HSummary)
      as
        [(phi_guard_summary & heap_guard_summary &
          phi_branch_summary & heap_branch_summary &
          HGuardSummary & HBranchSummary & _ & HTraceSummary) |
         (phi_guard_summary & heap_guard_summary &
          phi_branch_summary & heap_branch_summary &
          HGuardSummary & HBranchSummary & _ & HTraceSummary)].
    + destruct
        (StepsPhi_terminal_deterministic
          (initial_state heap env rho e)
          phi_guard heap_guard (Bit false)
          phi_guard_summary heap_guard_summary (Bit true)
          (StepsPhiN_to_StepsPhi _ _ _ _ HGuard) HGuardSummary)
        as [_ [_ HValue]].
      inversion HValue.
    + pose proof
        (ReadOnlyPhi_app_list_left
          phi_summary phi_guard_summary phi_branch_summary
          HReadOnlySummary HTraceSummary) as HReadOnlyGuardSummary.
      pose proof
        (ReadOnlyPhi_app_list_right
          phi_summary phi_guard_summary phi_branch_summary
          HReadOnlySummary HTraceSummary) as HReadOnlyBranchSummary.
      pose proof
        (StepsPhi_typed_readonly_static_preserves_heap
          heap env rho e stty ctxt rgns ty_e static_e
          phi_guard heap_guard (Bit false)
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcGuard
          (StepsPhiN_to_StepsPhi _ _ _ _ HGuard)
          HReadOnlyStaticGuard) as HHeapGuard.
      pose proof
        (StepsPhi_readonly_preserves_heap
          (initial_state heap env rho e) phi_guard_summary
          (StDone heap_guard_summary (Bit false))
          HGuardSummary HReadOnlyGuardSummary) as HHeapGuardSummary.
      simpl in HHeapGuardSummary.
      subst heap_guard.
      symmetry in HHeapGuardSummary.
      subst heap_guard_summary.
      pose proof
        (HBelow
          n_guard heap heap env rho e Empty
          phi_guard heap (Bit false)
          (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))
          heap Theta_Empty
          stty ctxt rgns ty_e static_e
          HLtGuard (SummaryReplayCompatibleForExpr_refl env rho Empty heap)
          HBTGuard HGuard HEmpty HReadOnlyEmpty
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcGuard) as HGuardSound.
      pose proof
        (HBelow
          n_branch heap heap env rho ef efff
          phi_branch heap_branch v_cond
          phi_branch_summary heap_branch_summary theta_summary
          stty ctxt rgns ty_f static_f
          HLtBranch (SummaryReplayCompatibleForExpr_refl env rho efff heap)
          HBTFalse HBranch HBranchSummary HReadOnlyBranchSummary
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcFalse) as HBranchSound.
      eapply (Correctness_soundness_ext_small_step_cond_false_terminal_case
        heap env rho e et ef
        phi_guard heap phi_branch heap_branch v_cond theta_summary
        phi_cond heap_cond v_cond); eauto.
      exact (StepsPhiN_to_StepsPhi _ _ _ _ HGuard).
      exact (StepsPhiN_to_StepsPhi _ _ _ _ HBranch).
      exact (StepsPhiN_to_StepsPhi _ _ _ _ HCond).
Qed.

Theorem Correctness_soundness_ext_small_step_plus_summary_terminal_recursive_case :
  forall heap env rho e1 e2 eff1 eff2
    phi_plus heap_plus v_plus
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2,
    StepsPhi (initial_state heap env rho (Plus e1 e2)) phi_plus
      (StDone heap_plus v_plus) ->
    StepsPhi (initial_state heap env rho (Concat eff1 eff2)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    SmallStepCorrectnessRecursivePremise ->
    phi_plus ⋞ theta_summary.
Proof.
  intros heap env rho e1 e2 eff1 eff2
    phi_plus heap_plus v_plus
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2
    HPlus HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE1 HTcE2 HReadOnlyStatic1 HReadOnlySummary
    HBT1 HBT2 HRecursive.
  unfold SmallStepCorrectnessRecursivePremise in HRecursive.
  eapply Correctness_soundness_ext_small_step_plus_summary_terminal_direct_case;
    try eassumption.
  - intros phi_left heap_left n1 phi_left_summary heap_left_summary theta1
      HLeft HLeftSummary HReadOnlyLeft.
    eapply (HRecursive
      heap env rho e1 eff1
      phi_left heap_left (Num n1)
      phi_left_summary heap_left_summary theta1
      stty ctxt rgns ty_e1 static_e1); eauto.
  - intros phi_right heap_right n2 phi_right_summary heap_right_summary theta2
      HRight HRightSummary HReadOnlyRight.
    eapply (HRecursive
      heap env rho e2 eff2
      phi_right heap_right (Num n2)
      phi_right_summary heap_right_summary theta2
	      stty ctxt rgns ty_e2 static_e2); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_plus_summary_terminal_heterogeneous_below_case :
  forall n heap heap_summary_start env rho e1 e2 eff1 eff2
    phi_plus heap_plus v_plus
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2,
    StepsPhiN n (initial_state heap env rho (Plus e1 e2)) phi_plus
      (StDone heap_plus v_plus) ->
    StepsPhi (initial_state heap_summary_start env rho (Concat eff1 eff2))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi_plus ⋞ theta_summary.
Proof.
  intros n heap heap_summary_start env rho e1 e2 eff1 eff2
    phi_plus heap_plus v_plus
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2
    HPlus HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE1 HTcE2 HReadOnlyStatic1 HReadOnlySummary
    HBT1 HBT2 HBelow.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_plus_terminal_decompose_counts
      n heap env rho e1 e2 phi_plus heap_plus v_plus HPlus)
    as (n_left & phi_left & heap_left & n1 &
        n_right & phi_right & heap_right & n2 &
        HLtLeft & HLtRight & HLeft & HRight & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_summary_start env rho eff1 eff2
      phi_summary heap_summary theta_summary HSummary)
    as (phi_left_summary & heap_left_summary & theta1 &
        phi_right_summary & heap_right_summary & theta2 &
        HLeftSummary & HRightSummary & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyLeftSummary.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyRightSummary.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho e1 stty ctxt rgns ty_e1 static_e1
      phi_left heap_left (Num n1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcE1
      (StepsPhiN_to_StepsPhi _ _ _ _ HLeft) HReadOnlyStatic1)
    as HHeapLeft.
  subst heap_left.
  pose proof
    (HBelow
      n_left heap heap_summary_start env rho e1 eff1
      phi_left heap (Num n1)
      phi_left_summary heap_left_summary theta1
      stty ctxt rgns ty_e1 static_e1
      HLtLeft HBT1 HLeft HLeftSummary HReadOnlyLeftSummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE1) as HLeftSound.
  pose proof
    (HBelow
      n_right heap heap_left_summary env rho e2 eff2
      phi_right heap_right (Num n2)
      phi_right_summary heap_right_summary theta2
      stty ctxt rgns ty_e2 static_e2
      HLtRight HBT2 HRight HRightSummary HReadOnlyRightSummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE2) as HRightSound.
  eapply
    (Correctness_soundness_ext_small_step_plus_summary_terminal_heterogeneous_case
      heap heap_summary_start env rho e1 e2 eff1 eff2
      phi_left heap n1 phi_right heap_right n2
      phi_left_summary heap_left_summary theta1
      phi_right_summary heap_right_summary theta2
      phi_summary heap_summary theta_summary
      phi_plus heap_plus v_plus); eauto.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HLeft).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HRight).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HPlus).
Qed.

Theorem Correctness_soundness_ext_small_step_plus_summary_terminal_summary_replay_below_case :
  forall n heap env rho e1 e2 eff1 eff2
    phi_plus heap_plus v_plus
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2,
    StepsPhiN n (initial_state heap env rho (Plus e1 e2)) phi_plus
      (StDone heap_plus v_plus) ->
    StepsPhi (initial_state heap env rho (Concat eff1 eff2))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi_plus ⋞ theta_summary.
Proof.
  intros n heap env rho e1 e2 eff1 eff2
    phi_plus heap_plus v_plus
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2
    HPlus HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE1 HTcE2 HReadOnlyStatic1 HReadOnlySummary
    HBT1 HBT2 HBelow.
  unfold SmallStepCorrectnessSummaryReplayRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_plus_terminal_decompose_counts
      n heap env rho e1 e2 phi_plus heap_plus v_plus HPlus)
    as (n_left & phi_left & heap_left & n1 &
        n_right & phi_right & heap_right & n2 &
        HLtLeft & HLtRight & HLeft & HRight & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 eff2
      phi_summary heap_summary theta_summary HSummary)
    as (phi_left_summary & heap_left_summary & theta1 &
        phi_right_summary & heap_right_summary & theta2 &
        HLeftSummary & HRightSummary & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyLeftSummary.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyRightSummary.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho e1 stty ctxt rgns ty_e1 static_e1
      phi_left heap_left (Num n1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcE1
      (StepsPhiN_to_StepsPhi _ _ _ _ HLeft) HReadOnlyStatic1)
    as HHeapLeft.
  subst heap_left.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff1) phi_left_summary
      (StDone heap_left_summary (Eff theta1))
      HLeftSummary HReadOnlyLeftSummary) as HHeapLeftSummary.
  simpl in HHeapLeftSummary.
  subst heap_left_summary.
  pose proof
    (HBelow
      n_left heap heap env rho e1 eff1
      phi_left heap (Num n1)
      phi_left_summary heap theta1
      stty ctxt rgns ty_e1 static_e1
      HLtLeft (SummaryReplayCompatibleForExpr_refl env rho eff1 heap)
      HBT1 HLeft HLeftSummary HReadOnlyLeftSummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE1) as HLeftSound.
  pose proof
    (HBelow
      n_right heap heap env rho e2 eff2
      phi_right heap_right (Num n2)
      phi_right_summary heap_right_summary theta2
      stty ctxt rgns ty_e2 static_e2
      HLtRight (SummaryReplayCompatibleForExpr_refl env rho eff2 heap)
      HBT2 HRight HRightSummary HReadOnlyRightSummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE2) as HRightSound.
  eapply
    (Correctness_soundness_ext_small_step_plus_summary_terminal_heterogeneous_case
      heap heap env rho e1 e2 eff1 eff2
      phi_left heap n1 phi_right heap_right n2
      phi_left_summary heap theta1
      phi_right_summary heap_right_summary theta2
      phi_summary heap_summary theta_summary
      phi_plus heap_plus v_plus); eauto.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HLeft).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HRight).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HPlus).
Qed.

Theorem Correctness_soundness_ext_small_step_minus_summary_terminal_recursive_case :
  forall heap env rho e1 e2 eff1 eff2
    phi_minus heap_minus v_minus
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2,
    StepsPhi (initial_state heap env rho (Minus e1 e2)) phi_minus
      (StDone heap_minus v_minus) ->
    StepsPhi (initial_state heap env rho (Concat eff1 eff2)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    SmallStepCorrectnessRecursivePremise ->
    phi_minus ⋞ theta_summary.
Proof.
  intros heap env rho e1 e2 eff1 eff2
    phi_minus heap_minus v_minus
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2
    HMinus HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE1 HTcE2 HReadOnlyStatic1 HReadOnlySummary
    HBT1 HBT2 HRecursive.
  unfold SmallStepCorrectnessRecursivePremise in HRecursive.
  eapply Correctness_soundness_ext_small_step_minus_summary_terminal_direct_case;
    try eassumption.
  - intros phi_left heap_left n1 phi_left_summary heap_left_summary theta1
      HLeft HLeftSummary HReadOnlyLeft.
    eapply (HRecursive
      heap env rho e1 eff1
      phi_left heap_left (Num n1)
      phi_left_summary heap_left_summary theta1
      stty ctxt rgns ty_e1 static_e1); eauto.
  - intros phi_right heap_right n2 phi_right_summary heap_right_summary theta2
      HRight HRightSummary HReadOnlyRight.
    eapply (HRecursive
      heap env rho e2 eff2
      phi_right heap_right (Num n2)
      phi_right_summary heap_right_summary theta2
	      stty ctxt rgns ty_e2 static_e2); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_minus_summary_terminal_heterogeneous_below_case :
  forall n heap heap_summary_start env rho e1 e2 eff1 eff2
    phi_minus heap_minus v_minus
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2,
    StepsPhiN n (initial_state heap env rho (Minus e1 e2)) phi_minus
      (StDone heap_minus v_minus) ->
    StepsPhi (initial_state heap_summary_start env rho (Concat eff1 eff2))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi_minus ⋞ theta_summary.
Proof.
  intros n heap heap_summary_start env rho e1 e2 eff1 eff2
    phi_minus heap_minus v_minus
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2
    HMinus HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE1 HTcE2 HReadOnlyStatic1 HReadOnlySummary
    HBT1 HBT2 HBelow.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_minus_terminal_decompose_counts
      n heap env rho e1 e2 phi_minus heap_minus v_minus HMinus)
    as (n_left & phi_left & heap_left & n1 &
        n_right & phi_right & heap_right & n2 &
        HLtLeft & HLtRight & HLeft & HRight & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_summary_start env rho eff1 eff2
      phi_summary heap_summary theta_summary HSummary)
    as (phi_left_summary & heap_left_summary & theta1 &
        phi_right_summary & heap_right_summary & theta2 &
        HLeftSummary & HRightSummary & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyLeftSummary.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyRightSummary.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho e1 stty ctxt rgns ty_e1 static_e1
      phi_left heap_left (Num n1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcE1
      (StepsPhiN_to_StepsPhi _ _ _ _ HLeft) HReadOnlyStatic1)
    as HHeapLeft.
  subst heap_left.
  pose proof
    (HBelow
      n_left heap heap_summary_start env rho e1 eff1
      phi_left heap (Num n1)
      phi_left_summary heap_left_summary theta1
      stty ctxt rgns ty_e1 static_e1
      HLtLeft HBT1 HLeft HLeftSummary HReadOnlyLeftSummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE1) as HLeftSound.
  pose proof
    (HBelow
      n_right heap heap_left_summary env rho e2 eff2
      phi_right heap_right (Num n2)
      phi_right_summary heap_right_summary theta2
      stty ctxt rgns ty_e2 static_e2
      HLtRight HBT2 HRight HRightSummary HReadOnlyRightSummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE2) as HRightSound.
  eapply
    (Correctness_soundness_ext_small_step_minus_summary_terminal_heterogeneous_case
      heap heap_summary_start env rho e1 e2 eff1 eff2
      phi_left heap n1 phi_right heap_right n2
      phi_left_summary heap_left_summary theta1
      phi_right_summary heap_right_summary theta2
      phi_summary heap_summary theta_summary
      phi_minus heap_minus v_minus); eauto.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HLeft).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HRight).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HMinus).
Qed.

Theorem Correctness_soundness_ext_small_step_minus_summary_terminal_summary_replay_below_case :
  forall n heap env rho e1 e2 eff1 eff2
    phi_minus heap_minus v_minus
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2,
    StepsPhiN n (initial_state heap env rho (Minus e1 e2)) phi_minus
      (StDone heap_minus v_minus) ->
    StepsPhi (initial_state heap env rho (Concat eff1 eff2))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi_minus ⋞ theta_summary.
Proof.
  intros n heap env rho e1 e2 eff1 eff2
    phi_minus heap_minus v_minus
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2
    HMinus HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE1 HTcE2 HReadOnlyStatic1 HReadOnlySummary
    HBT1 HBT2 HBelow.
  unfold SmallStepCorrectnessSummaryReplayRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_minus_terminal_decompose_counts
      n heap env rho e1 e2 phi_minus heap_minus v_minus HMinus)
    as (n_left & phi_left & heap_left & n1 &
        n_right & phi_right & heap_right & n2 &
        HLtLeft & HLtRight & HLeft & HRight & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 eff2
      phi_summary heap_summary theta_summary HSummary)
    as (phi_left_summary & heap_left_summary & theta1 &
        phi_right_summary & heap_right_summary & theta2 &
        HLeftSummary & HRightSummary & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyLeftSummary.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyRightSummary.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho e1 stty ctxt rgns ty_e1 static_e1
      phi_left heap_left (Num n1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcE1
      (StepsPhiN_to_StepsPhi _ _ _ _ HLeft) HReadOnlyStatic1)
    as HHeapLeft.
  subst heap_left.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff1) phi_left_summary
      (StDone heap_left_summary (Eff theta1))
      HLeftSummary HReadOnlyLeftSummary) as HHeapLeftSummary.
  simpl in HHeapLeftSummary.
  subst heap_left_summary.
  pose proof
    (HBelow
      n_left heap heap env rho e1 eff1
      phi_left heap (Num n1)
      phi_left_summary heap theta1
      stty ctxt rgns ty_e1 static_e1
      HLtLeft (SummaryReplayCompatibleForExpr_refl env rho eff1 heap)
      HBT1 HLeft HLeftSummary HReadOnlyLeftSummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE1) as HLeftSound.
  pose proof
    (HBelow
      n_right heap heap env rho e2 eff2
      phi_right heap_right (Num n2)
      phi_right_summary heap_right_summary theta2
      stty ctxt rgns ty_e2 static_e2
      HLtRight (SummaryReplayCompatibleForExpr_refl env rho eff2 heap)
      HBT2 HRight HRightSummary HReadOnlyRightSummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE2) as HRightSound.
  eapply
    (Correctness_soundness_ext_small_step_minus_summary_terminal_heterogeneous_case
      heap heap env rho e1 e2 eff1 eff2
      phi_left heap n1 phi_right heap_right n2
      phi_left_summary heap theta1
      phi_right_summary heap_right_summary theta2
      phi_summary heap_summary theta_summary
      phi_minus heap_minus v_minus); eauto.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HLeft).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HRight).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HMinus).
Qed.

Theorem Correctness_soundness_ext_small_step_times_summary_terminal_recursive_case :
  forall heap env rho e1 e2 eff1 eff2
    phi_times heap_times v_times
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2,
    StepsPhi (initial_state heap env rho (Times e1 e2)) phi_times
      (StDone heap_times v_times) ->
    StepsPhi (initial_state heap env rho (Concat eff1 eff2)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    SmallStepCorrectnessRecursivePremise ->
    phi_times ⋞ theta_summary.
Proof.
  intros heap env rho e1 e2 eff1 eff2
    phi_times heap_times v_times
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2
    HTimes HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE1 HTcE2 HReadOnlyStatic1 HReadOnlySummary
    HBT1 HBT2 HRecursive.
  unfold SmallStepCorrectnessRecursivePremise in HRecursive.
  eapply Correctness_soundness_ext_small_step_times_summary_terminal_direct_case;
    try eassumption.
  - intros phi_left heap_left n1 phi_left_summary heap_left_summary theta1
      HLeft HLeftSummary HReadOnlyLeft.
    eapply (HRecursive
      heap env rho e1 eff1
      phi_left heap_left (Num n1)
      phi_left_summary heap_left_summary theta1
      stty ctxt rgns ty_e1 static_e1); eauto.
  - intros phi_right heap_right n2 phi_right_summary heap_right_summary theta2
      HRight HRightSummary HReadOnlyRight.
    eapply (HRecursive
      heap env rho e2 eff2
      phi_right heap_right (Num n2)
      phi_right_summary heap_right_summary theta2
	      stty ctxt rgns ty_e2 static_e2); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_times_summary_terminal_heterogeneous_below_case :
  forall n heap heap_summary_start env rho e1 e2 eff1 eff2
    phi_times heap_times v_times
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2,
    StepsPhiN n (initial_state heap env rho (Times e1 e2)) phi_times
      (StDone heap_times v_times) ->
    StepsPhi (initial_state heap_summary_start env rho (Concat eff1 eff2))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi_times ⋞ theta_summary.
Proof.
  intros n heap heap_summary_start env rho e1 e2 eff1 eff2
    phi_times heap_times v_times
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2
    HTimes HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE1 HTcE2 HReadOnlyStatic1 HReadOnlySummary
    HBT1 HBT2 HBelow.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_times_terminal_decompose_counts
      n heap env rho e1 e2 phi_times heap_times v_times HTimes)
    as (n_left & phi_left & heap_left & n1 &
        n_right & phi_right & heap_right & n2 &
        HLtLeft & HLtRight & HLeft & HRight & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_summary_start env rho eff1 eff2
      phi_summary heap_summary theta_summary HSummary)
    as (phi_left_summary & heap_left_summary & theta1 &
        phi_right_summary & heap_right_summary & theta2 &
        HLeftSummary & HRightSummary & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyLeftSummary.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyRightSummary.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho e1 stty ctxt rgns ty_e1 static_e1
      phi_left heap_left (Num n1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcE1
      (StepsPhiN_to_StepsPhi _ _ _ _ HLeft) HReadOnlyStatic1)
    as HHeapLeft.
  subst heap_left.
  pose proof
    (HBelow
      n_left heap heap_summary_start env rho e1 eff1
      phi_left heap (Num n1)
      phi_left_summary heap_left_summary theta1
      stty ctxt rgns ty_e1 static_e1
      HLtLeft HBT1 HLeft HLeftSummary HReadOnlyLeftSummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE1) as HLeftSound.
  pose proof
    (HBelow
      n_right heap heap_left_summary env rho e2 eff2
      phi_right heap_right (Num n2)
      phi_right_summary heap_right_summary theta2
      stty ctxt rgns ty_e2 static_e2
      HLtRight HBT2 HRight HRightSummary HReadOnlyRightSummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE2) as HRightSound.
  eapply
    (Correctness_soundness_ext_small_step_times_summary_terminal_heterogeneous_case
      heap heap_summary_start env rho e1 e2 eff1 eff2
      phi_left heap n1 phi_right heap_right n2
      phi_left_summary heap_left_summary theta1
      phi_right_summary heap_right_summary theta2
      phi_summary heap_summary theta_summary
      phi_times heap_times v_times); eauto.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HLeft).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HRight).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HTimes).
Qed.

Theorem Correctness_soundness_ext_small_step_times_summary_terminal_summary_replay_below_case :
  forall n heap env rho e1 e2 eff1 eff2
    phi_times heap_times v_times
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2,
    StepsPhiN n (initial_state heap env rho (Times e1 e2)) phi_times
      (StDone heap_times v_times) ->
    StepsPhi (initial_state heap env rho (Concat eff1 eff2))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi_times ⋞ theta_summary.
Proof.
  intros n heap env rho e1 e2 eff1 eff2
    phi_times heap_times v_times
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2
    HTimes HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE1 HTcE2 HReadOnlyStatic1 HReadOnlySummary
    HBT1 HBT2 HBelow.
  unfold SmallStepCorrectnessSummaryReplayRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_times_terminal_decompose_counts
      n heap env rho e1 e2 phi_times heap_times v_times HTimes)
    as (n_left & phi_left & heap_left & n1 &
        n_right & phi_right & heap_right & n2 &
        HLtLeft & HLtRight & HLeft & HRight & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 eff2
      phi_summary heap_summary theta_summary HSummary)
    as (phi_left_summary & heap_left_summary & theta1 &
        phi_right_summary & heap_right_summary & theta2 &
        HLeftSummary & HRightSummary & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyLeftSummary.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyRightSummary.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho e1 stty ctxt rgns ty_e1 static_e1
      phi_left heap_left (Num n1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcE1
      (StepsPhiN_to_StepsPhi _ _ _ _ HLeft) HReadOnlyStatic1)
    as HHeapLeft.
  subst heap_left.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff1) phi_left_summary
      (StDone heap_left_summary (Eff theta1))
      HLeftSummary HReadOnlyLeftSummary) as HHeapLeftSummary.
  simpl in HHeapLeftSummary.
  subst heap_left_summary.
  pose proof
    (HBelow
      n_left heap heap env rho e1 eff1
      phi_left heap (Num n1)
      phi_left_summary heap theta1
      stty ctxt rgns ty_e1 static_e1
      HLtLeft (SummaryReplayCompatibleForExpr_refl env rho eff1 heap)
      HBT1 HLeft HLeftSummary HReadOnlyLeftSummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE1) as HLeftSound.
  pose proof
    (HBelow
      n_right heap heap env rho e2 eff2
      phi_right heap_right (Num n2)
      phi_right_summary heap_right_summary theta2
      stty ctxt rgns ty_e2 static_e2
      HLtRight (SummaryReplayCompatibleForExpr_refl env rho eff2 heap)
      HBT2 HRight HRightSummary HReadOnlyRightSummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE2) as HRightSound.
  eapply
    (Correctness_soundness_ext_small_step_times_summary_terminal_heterogeneous_case
      heap heap env rho e1 e2 eff1 eff2
      phi_left heap n1 phi_right heap_right n2
      phi_left_summary heap theta1
      phi_right_summary heap_right_summary theta2
      phi_summary heap_summary theta_summary
      phi_times heap_times v_times); eauto.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HLeft).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HRight).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HTimes).
Qed.

Theorem Correctness_soundness_ext_small_step_eq_summary_terminal_recursive_case :
  forall heap env rho e1 e2 eff1 eff2
    phi_eq heap_eq v_eq
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2,
    StepsPhi (initial_state heap env rho (Eq e1 e2)) phi_eq
      (StDone heap_eq v_eq) ->
    StepsPhi (initial_state heap env rho (Concat eff1 eff2)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    SmallStepCorrectnessRecursivePremise ->
    phi_eq ⋞ theta_summary.
Proof.
  intros heap env rho e1 e2 eff1 eff2
    phi_eq heap_eq v_eq
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2
    HEq HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE1 HTcE2 HReadOnlyStatic1 HReadOnlySummary
    HBT1 HBT2 HRecursive.
  unfold SmallStepCorrectnessRecursivePremise in HRecursive.
  eapply Correctness_soundness_ext_small_step_eq_summary_terminal_direct_case;
    try eassumption.
  - intros phi_left heap_left n1 phi_left_summary heap_left_summary theta1
      HLeft HLeftSummary HReadOnlyLeft.
    eapply (HRecursive
      heap env rho e1 eff1
      phi_left heap_left (Num n1)
      phi_left_summary heap_left_summary theta1
      stty ctxt rgns ty_e1 static_e1); eauto.
  - intros phi_right heap_right n2 phi_right_summary heap_right_summary theta2
      HRight HRightSummary HReadOnlyRight.
    eapply (HRecursive
      heap env rho e2 eff2
      phi_right heap_right (Num n2)
      phi_right_summary heap_right_summary theta2
	      stty ctxt rgns ty_e2 static_e2); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_eq_summary_terminal_heterogeneous_below_case :
  forall n heap heap_summary_start env rho e1 e2 eff1 eff2
    phi_eq heap_eq v_eq
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2,
    StepsPhiN n (initial_state heap env rho (Eq e1 e2)) phi_eq
      (StDone heap_eq v_eq) ->
    StepsPhi (initial_state heap_summary_start env rho (Concat eff1 eff2))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi_eq ⋞ theta_summary.
Proof.
  intros n heap heap_summary_start env rho e1 e2 eff1 eff2
    phi_eq heap_eq v_eq
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2
    HEq HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE1 HTcE2 HReadOnlyStatic1 HReadOnlySummary
    HBT1 HBT2 HBelow.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_eq_terminal_decompose_counts
      n heap env rho e1 e2 phi_eq heap_eq v_eq HEq)
    as (n_left & phi_left & heap_left & n1 &
        n_right & phi_right & heap_right & n2 &
        HLtLeft & HLtRight & HLeft & HRight & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_summary_start env rho eff1 eff2
      phi_summary heap_summary theta_summary HSummary)
    as (phi_left_summary & heap_left_summary & theta1 &
        phi_right_summary & heap_right_summary & theta2 &
        HLeftSummary & HRightSummary & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyLeftSummary.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyRightSummary.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho e1 stty ctxt rgns ty_e1 static_e1
      phi_left heap_left (Num n1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcE1
      (StepsPhiN_to_StepsPhi _ _ _ _ HLeft) HReadOnlyStatic1)
    as HHeapLeft.
  subst heap_left.
  pose proof
    (HBelow
      n_left heap heap_summary_start env rho e1 eff1
      phi_left heap (Num n1)
      phi_left_summary heap_left_summary theta1
      stty ctxt rgns ty_e1 static_e1
      HLtLeft HBT1 HLeft HLeftSummary HReadOnlyLeftSummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE1) as HLeftSound.
  pose proof
    (HBelow
      n_right heap heap_left_summary env rho e2 eff2
      phi_right heap_right (Num n2)
      phi_right_summary heap_right_summary theta2
      stty ctxt rgns ty_e2 static_e2
      HLtRight HBT2 HRight HRightSummary HReadOnlyRightSummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE2) as HRightSound.
  eapply
    (Correctness_soundness_ext_small_step_eq_summary_terminal_heterogeneous_case
      heap heap_summary_start env rho e1 e2 eff1 eff2
      phi_left heap n1 phi_right heap_right n2
      phi_left_summary heap_left_summary theta1
      phi_right_summary heap_right_summary theta2
      phi_summary heap_summary theta_summary
      phi_eq heap_eq v_eq); eauto.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HLeft).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HRight).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HEq).
Qed.

Theorem Correctness_soundness_ext_small_step_eq_summary_terminal_summary_replay_below_case :
  forall n heap env rho e1 e2 eff1 eff2
    phi_eq heap_eq v_eq
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2,
    StepsPhiN n (initial_state heap env rho (Eq e1 e2)) phi_eq
      (StDone heap_eq v_eq) ->
    StepsPhi (initial_state heap env rho (Concat eff1 eff2))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi_eq ⋞ theta_summary.
Proof.
  intros n heap env rho e1 e2 eff1 eff2
    phi_eq heap_eq v_eq
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_e1 ty_e2 static_e1 static_e2
    HEq HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE1 HTcE2 HReadOnlyStatic1 HReadOnlySummary
    HBT1 HBT2 HBelow.
  unfold SmallStepCorrectnessSummaryReplayRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_eq_terminal_decompose_counts
      n heap env rho e1 e2 phi_eq heap_eq v_eq HEq)
    as (n_left & phi_left & heap_left & n1 &
        n_right & phi_right & heap_right & n2 &
        HLtLeft & HLtRight & HLeft & HRight & _ & _ & _).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 eff2
      phi_summary heap_summary theta_summary HSummary)
    as (phi_left_summary & heap_left_summary & theta1 &
        phi_right_summary & heap_right_summary & theta2 &
        HLeftSummary & HRightSummary & _ & _ & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyLeftSummary.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_left_summary phi_right_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyRightSummary.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho e1 stty ctxt rgns ty_e1 static_e1
      phi_left heap_left (Num n1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcE1
      (StepsPhiN_to_StepsPhi _ _ _ _ HLeft) HReadOnlyStatic1)
    as HHeapLeft.
  subst heap_left.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff1) phi_left_summary
      (StDone heap_left_summary (Eff theta1))
      HLeftSummary HReadOnlyLeftSummary) as HHeapLeftSummary.
  simpl in HHeapLeftSummary.
  subst heap_left_summary.
  pose proof
    (HBelow
      n_left heap heap env rho e1 eff1
      phi_left heap (Num n1)
      phi_left_summary heap theta1
      stty ctxt rgns ty_e1 static_e1
      HLtLeft (SummaryReplayCompatibleForExpr_refl env rho eff1 heap)
      HBT1 HLeft HLeftSummary HReadOnlyLeftSummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE1) as HLeftSound.
  pose proof
    (HBelow
      n_right heap heap env rho e2 eff2
      phi_right heap_right (Num n2)
      phi_right_summary heap_right_summary theta2
      stty ctxt rgns ty_e2 static_e2
      HLtRight (SummaryReplayCompatibleForExpr_refl env rho eff2 heap)
      HBT2 HRight HRightSummary HReadOnlyRightSummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcE2) as HRightSound.
  eapply
    (Correctness_soundness_ext_small_step_eq_summary_terminal_heterogeneous_case
      heap heap env rho e1 e2 eff1 eff2
      phi_left heap n1 phi_right heap_right n2
      phi_left_summary heap theta1
      phi_right_summary heap_right_summary theta2
      phi_summary heap_summary theta_summary
      phi_eq heap_eq v_eq); eauto.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HLeft).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HRight).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HEq).
Qed.

Theorem Correctness_soundness_ext_small_step_mu_app_summary_terminal_named_recursive_case :
  forall heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns tya effc tyc effe static_ef static_ea,
    StepsPhi (initial_state heap env rho (Mu_App ef ea)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho (Eff_App ef ea)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp
      (ctxt, rgns, ef,
        Ty_Arrow tya effc tyc effe Ty_Effect, static_ef) ->
    TcExp (ctxt, rgns, ea, tya, static_ea) ->
    ReadOnlyStatic (fold_subst_eps rho static_ef) ->
    ReadOnlyStatic (fold_subst_eps rho static_ea) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ef, Eff_App ef ea) ->
    BackTriangle (ctxt, rgns, rho, ea, Eff_App ef ea) ->
    SmallStepCorrectnessRecursivePremise ->
    phi_app ⋞ theta_summary.
Proof.
  intros heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns tya effc tyc effe static_ef static_ea
    HApp HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEf HTcEa HReadOnlyEf HReadOnlyEa HReadOnlySummary
    HBTFun HBTArg HRecursive.
  unfold SmallStepCorrectnessRecursivePremise in HRecursive.
  eapply Correctness_soundness_ext_small_step_mu_app_summary_terminal_recursive_case;
    eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_named_recursive_case :
  forall heap env rho er w
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns effr tyr static_er,
    StepsPhi (initial_state heap env rho (Rgn_App er w)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho Empty) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, er, Ty_ForallRgn effr tyr, static_er) ->
    BackTriangle (ctxt, rgns, rho, er, Empty) ->
    SmallStepCorrectnessRecursivePremise ->
    phi_app ⋞ theta_summary.
Proof.
  intros heap env rho er w
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns effr tyr static_er
    HApp HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEr HBTEr HRecursive.
  unfold SmallStepCorrectnessRecursivePremise in HRecursive.
  eapply Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_recursive_case;
    eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_mu_app_summary_terminal_mixed_recursive_case :
  forall heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns tya effc tyc effe
    static_ef_shape static_ea_shape
    ty_ef_readonly static_ef_readonly
    ty_ea_readonly static_ea_readonly,
    StepsPhi (initial_state heap env rho (Mu_App ef ea)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho (Eff_App ef ea)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp
      (ctxt, rgns, ef,
        Ty_Arrow tya effc tyc effe Ty_Effect, static_ef_shape) ->
    TcExp (ctxt, rgns, ea, tya, static_ea_shape) ->
    TcExp (ctxt, rgns, ef, ty_ef_readonly, static_ef_readonly) ->
    TcExp (ctxt, rgns, ea, ty_ea_readonly, static_ea_readonly) ->
    ReadOnlyStatic (fold_subst_eps rho static_ef_readonly) ->
    ReadOnlyStatic (fold_subst_eps rho static_ea_readonly) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ef, Eff_App ef ea) ->
    BackTriangle (ctxt, rgns, rho, ea, Eff_App ef ea) ->
    SmallStepCorrectnessRecursivePremise ->
    phi_app ⋞ theta_summary.
Proof.
  intros heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns tya effc tyc effe
    static_ef_shape static_ea_shape
    ty_ef_readonly static_ef_readonly
    ty_ea_readonly static_ea_readonly
    HApp HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEfShape HTcEaShape HTcEfReadonly HTcEaReadonly
    HReadOnlyEf HReadOnlyEa HReadOnlySummary HBTFun HBTArg HRecursive.
  unfold SmallStepCorrectnessRecursivePremise in HRecursive.
  destruct
    (StepsPhi_mu_app_terminal_decompose
      heap env rho ef ea phi_app heap_app v_app HApp)
    as (env_fun & rho_fun & f & x & ec & ee &
        phi_fun & heap_fun & phi_arg & heap_arg & v_arg &
        phi_body & HFun & HArg & HBody & _).
  destruct
    (StepsPhi_eff_app_terminal_decompose
      heap env rho ef ea phi_summary heap_summary (Eff theta_summary)
      HSummary)
    as (env_fun_summary & rho_fun_summary & f_summary & x_summary &
        ec_summary & ee_summary &
        phi_fun_summary & heap_fun_summary &
        phi_arg_summary & heap_arg_summary & v_arg_summary &
        phi_body_summary &
        HFunSummary & HArgSummary & HBodySummary & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list3_right
      phi_summary phi_fun_summary phi_arg_summary phi_body_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyBodySummary.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ef stty ctxt rgns
      ty_ef_readonly static_ef_readonly
      phi_fun heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEfReadonly HFun
      HReadOnlyEf) as HHeapFun.
  subst heap_fun.
  destruct
    (StepsPhi_terminal_deterministic
      (initial_state heap env rho ef)
      phi_fun heap (Cls (env_fun, rho_fun, Mu f x ec ee))
      phi_fun_summary heap_fun_summary
        (Cls (env_fun_summary, rho_fun_summary,
          Mu f_summary x_summary ec_summary ee_summary))
      HFun HFunSummary)
    as [_ [HHeapFunSummary HClosureEq]].
  symmetry in HHeapFunSummary.
  subst heap_fun_summary.
  inversion HClosureEq; subst.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ea stty ctxt rgns
      ty_ea_readonly static_ea_readonly
      phi_arg heap_arg v_arg
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEaReadonly HArg
      HReadOnlyEa) as HHeapArg.
  subst heap_arg.
  destruct
    (StepsPhi_terminal_deterministic
      (initial_state heap env rho ea)
      phi_arg heap v_arg
      phi_arg_summary heap_arg_summary v_arg_summary
      HArg HArgSummary)
    as [_ [HHeapArgSummary HArgEq]].
  symmetry in HHeapArgSummary.
  subst heap_arg_summary.
  subst v_arg_summary.
  destruct
    (MuApp_body_context_from_mixed_readonly_terminals
      heap env rho ef ea heap heap env_fun_summary rho_fun_summary
      f_summary x_summary ec_summary ee_summary v_arg
      phi_fun phi_arg stty ctxt rgns tya effc tyc effe
      static_ef_shape static_ea_shape
      ty_ef_readonly static_ef_readonly
      ty_ea_readonly static_ea_readonly
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEfShape HTcEaShape HTcEfReadonly HTcEaReadonly
      HFun HArg HReadOnlyEf HReadOnlyEa)
    as (rgns_body & ctxt_body & tyx_body & effc_body & tyc_body &
        effe_body & _ & _ & HTcRhoBody & _ & HTcIncBodyUpdated &
        HTcEnvBody & HEnvShapeBody & HBTBody & HTcBody & _).
  pose proof
    (HRecursive
      heap env rho ef (Eff_App ef ea)
      phi_fun heap (Cls (env_fun_summary, rho_fun_summary,
        Mu f_summary x_summary ec_summary ee_summary))
      phi_summary heap_summary theta_summary
      stty ctxt rgns ty_ef_readonly static_ef_readonly
      HBTFun HFun HSummary HReadOnlySummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEfReadonly)
    as HFunSound.
  pose proof
    (HRecursive
      heap env rho ea (Eff_App ef ea)
      phi_arg heap v_arg
      phi_summary heap_summary theta_summary
      stty ctxt rgns ty_ea_readonly static_ea_readonly
      HBTArg HArg HSummary HReadOnlySummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEaReadonly)
    as HArgSound.
  pose proof
    (HRecursive
      heap
      (update_rec_E
        (f_summary,
          Cls (env_fun_summary, rho_fun_summary,
            Mu f_summary x_summary ec_summary ee_summary))
      (x_summary, v_arg) env_fun_summary)
      rho_fun_summary ec_summary ee_summary
      phi_body heap_app v_app
      phi_body_summary heap_summary theta_summary
      stty
      (update_rec_T
        (f_summary,
          Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
        (x_summary, tyx_body) ctxt_body)
      rgns_body tyc_body effc_body
      HBTBody HBody HBodySummary HReadOnlyBodySummary
      HTcHeap HHeapShape HTcRhoBody HTcIncBodyUpdated HTcEnvBody HEnvShapeBody
      HTcBody)
    as HBodySound.
  eapply (Correctness_soundness_ext_small_step_mu_app_summary_terminal_case
    heap env rho ef ea env_fun_summary rho_fun_summary
    f_summary x_summary ec_summary ee_summary
    phi_fun heap phi_arg heap v_arg
    phi_body heap_app v_app
    phi_body_summary heap_summary theta_summary
	    phi_summary heap_summary theta_summary
	    phi_app heap_app v_app); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_mu_app_summary_terminal_mixed_below_case :
  forall n heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns tya effc tyc effe
    static_ef_shape static_ea_shape
    ty_ef_readonly static_ef_readonly
    ty_ea_readonly static_ea_readonly,
    StepsPhiN n (initial_state heap env rho (Mu_App ef ea)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho (Eff_App ef ea)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp
      (ctxt, rgns, ef,
        Ty_Arrow tya effc tyc effe Ty_Effect, static_ef_shape) ->
    TcExp (ctxt, rgns, ea, tya, static_ea_shape) ->
    TcExp (ctxt, rgns, ef, ty_ef_readonly, static_ef_readonly) ->
    TcExp (ctxt, rgns, ea, ty_ea_readonly, static_ea_readonly) ->
    ReadOnlyStatic (fold_subst_eps rho static_ef_readonly) ->
    ReadOnlyStatic (fold_subst_eps rho static_ea_readonly) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ef, Eff_App ef ea) ->
    BackTriangle (ctxt, rgns, rho, ea, Eff_App ef ea) ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi_app ⋞ theta_summary.
Proof.
  intros n heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns tya effc tyc effe
    static_ef_shape static_ea_shape
    ty_ef_readonly static_ef_readonly
    ty_ea_readonly static_ea_readonly
    HApp HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEfShape HTcEaShape HTcEfReadonly HTcEaReadonly
    HReadOnlyEf HReadOnlyEa HReadOnlySummary HBTFun HBTArg HBelow.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_mu_app_terminal_decompose_counts
      n heap env rho ef ea phi_app heap_app v_app HApp)
    as (env_fun & rho_fun & f & x & ec & ee &
        n_fun & phi_fun & heap_fun &
        n_arg & phi_arg & heap_arg & v_arg &
        n_body & phi_body &
        HLtFun & HLtArg & HLtBody & HFun & HArg & HBody & _).
  destruct
    (StepsPhi_eff_app_terminal_decompose
      heap env rho ef ea phi_summary heap_summary (Eff theta_summary)
      HSummary)
    as (env_fun_summary & rho_fun_summary & f_summary & x_summary &
        ec_summary & ee_summary &
        phi_fun_summary & heap_fun_summary &
        phi_arg_summary & heap_arg_summary & v_arg_summary &
        phi_body_summary &
        HFunSummary & HArgSummary & HBodySummary & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list3_right
      phi_summary phi_fun_summary phi_arg_summary phi_body_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyBodySummary.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ef stty ctxt rgns
      ty_ef_readonly static_ef_readonly
      phi_fun heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEfReadonly
      (StepsPhiN_to_StepsPhi _ _ _ _ HFun)
      HReadOnlyEf) as HHeapFun.
  subst heap_fun.
  destruct
    (StepsPhi_terminal_deterministic
      (initial_state heap env rho ef)
      phi_fun heap (Cls (env_fun, rho_fun, Mu f x ec ee))
      phi_fun_summary heap_fun_summary
        (Cls (env_fun_summary, rho_fun_summary,
          Mu f_summary x_summary ec_summary ee_summary))
      (StepsPhiN_to_StepsPhi _ _ _ _ HFun) HFunSummary)
    as [_ [HHeapFunSummary HClosureEq]].
  symmetry in HHeapFunSummary.
  subst heap_fun_summary.
  inversion HClosureEq; subst.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ea stty ctxt rgns
      ty_ea_readonly static_ea_readonly
      phi_arg heap_arg v_arg
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEaReadonly
      (StepsPhiN_to_StepsPhi _ _ _ _ HArg)
      HReadOnlyEa) as HHeapArg.
  subst heap_arg.
  destruct
    (StepsPhi_terminal_deterministic
      (initial_state heap env rho ea)
      phi_arg heap v_arg
      phi_arg_summary heap_arg_summary v_arg_summary
      (StepsPhiN_to_StepsPhi _ _ _ _ HArg) HArgSummary)
    as [_ [HHeapArgSummary HArgEq]].
  symmetry in HHeapArgSummary.
  subst heap_arg_summary.
  subst v_arg_summary.
  destruct
    (MuApp_body_context_from_mixed_readonly_terminals
      heap env rho ef ea heap heap env_fun_summary rho_fun_summary
      f_summary x_summary ec_summary ee_summary v_arg
      phi_fun phi_arg stty ctxt rgns tya effc tyc effe
      static_ef_shape static_ea_shape
      ty_ef_readonly static_ef_readonly
      ty_ea_readonly static_ea_readonly
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEfShape HTcEaShape HTcEfReadonly HTcEaReadonly
      (StepsPhiN_to_StepsPhi _ _ _ _ HFun)
      (StepsPhiN_to_StepsPhi _ _ _ _ HArg)
      HReadOnlyEf HReadOnlyEa)
    as (rgns_body & ctxt_body & tyx_body & effc_body & tyc_body &
        effe_body & _ & _ & HTcRhoBody & _ & HTcIncBodyUpdated &
        HTcEnvBody & HEnvShapeBody & HBTBody & HTcBody & _).
  pose proof
    (HBelow
      n_fun heap heap env rho ef (Eff_App ef ea)
      phi_fun heap (Cls (env_fun_summary, rho_fun_summary,
        Mu f_summary x_summary ec_summary ee_summary))
      phi_summary heap_summary theta_summary
      stty ctxt rgns ty_ef_readonly static_ef_readonly
      HLtFun HBTFun HFun HSummary HReadOnlySummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEfReadonly)
    as HFunSound.
  pose proof
    (HBelow
      n_arg heap heap env rho ea (Eff_App ef ea)
      phi_arg heap v_arg
      phi_summary heap_summary theta_summary
      stty ctxt rgns ty_ea_readonly static_ea_readonly
      HLtArg HBTArg HArg HSummary HReadOnlySummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEaReadonly)
    as HArgSound.
  pose proof
    (HBelow
      n_body heap heap
      (update_rec_E
        (f_summary,
          Cls (env_fun_summary, rho_fun_summary,
            Mu f_summary x_summary ec_summary ee_summary))
      (x_summary, v_arg) env_fun_summary)
      rho_fun_summary ec_summary ee_summary
      phi_body heap_app v_app
      phi_body_summary heap_summary theta_summary
      stty
      (update_rec_T
        (f_summary,
          Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
        (x_summary, tyx_body) ctxt_body)
      rgns_body tyc_body effc_body
      HLtBody HBTBody HBody HBodySummary HReadOnlyBodySummary
      HTcHeap HHeapShape HTcRhoBody HTcIncBodyUpdated HTcEnvBody HEnvShapeBody
      HTcBody)
    as HBodySound.
  eapply (Correctness_soundness_ext_small_step_mu_app_summary_terminal_case
    heap env rho ef ea env_fun_summary rho_fun_summary
    f_summary x_summary ec_summary ee_summary
    phi_fun heap phi_arg heap v_arg
    phi_body heap_app v_app
    phi_body_summary heap_summary theta_summary
    phi_summary heap_summary theta_summary
    phi_app heap_app v_app); eauto.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HFun).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HArg).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HBody).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HApp).
Qed.

Theorem Correctness_soundness_ext_small_step_mu_app_summary_terminal_mixed_summary_replay_below_case :
  forall n heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns tya effc tyc effe
    static_ef_shape static_ea_shape
    ty_ef_readonly static_ef_readonly
    ty_ea_readonly static_ea_readonly,
    StepsPhiN n (initial_state heap env rho (Mu_App ef ea)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho (Eff_App ef ea)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp
      (ctxt, rgns, ef,
        Ty_Arrow tya effc tyc effe Ty_Effect, static_ef_shape) ->
    TcExp (ctxt, rgns, ea, tya, static_ea_shape) ->
    TcExp (ctxt, rgns, ef, ty_ef_readonly, static_ef_readonly) ->
    TcExp (ctxt, rgns, ea, ty_ea_readonly, static_ea_readonly) ->
    ReadOnlyStatic (fold_subst_eps rho static_ef_readonly) ->
    ReadOnlyStatic (fold_subst_eps rho static_ea_readonly) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ef, Eff_App ef ea) ->
    BackTriangle (ctxt, rgns, rho, ea, Eff_App ef ea) ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi_app ⋞ theta_summary.
Proof.
  intros n heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns tya effc tyc effe
    static_ef_shape static_ea_shape
    ty_ef_readonly static_ef_readonly
    ty_ea_readonly static_ea_readonly
    HApp HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEfShape HTcEaShape HTcEfReadonly HTcEaReadonly
    HReadOnlyEf HReadOnlyEa HReadOnlySummary HBTFun HBTArg HBelow.
  unfold SmallStepCorrectnessSummaryReplayRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_mu_app_terminal_decompose_counts
      n heap env rho ef ea phi_app heap_app v_app HApp)
    as (env_fun & rho_fun & f & x & ec & ee &
        n_fun & phi_fun & heap_fun &
        n_arg & phi_arg & heap_arg & v_arg &
        n_body & phi_body &
        HLtFun & HLtArg & HLtBody & HFun & HArg & HBody & _).
  destruct
    (StepsPhi_eff_app_terminal_decompose
      heap env rho ef ea phi_summary heap_summary (Eff theta_summary)
      HSummary)
    as (env_fun_summary & rho_fun_summary & f_summary & x_summary &
        ec_summary & ee_summary &
        phi_fun_summary & heap_fun_summary &
        phi_arg_summary & heap_arg_summary & v_arg_summary &
        phi_body_summary &
        HFunSummary & HArgSummary & HBodySummary & HTraceSummary).
  pose proof
    (ReadOnlyPhi_app_list3_right
      phi_summary phi_fun_summary phi_arg_summary phi_body_summary
      HReadOnlySummary HTraceSummary) as HReadOnlyBodySummary.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ef stty ctxt rgns
      ty_ef_readonly static_ef_readonly
      phi_fun heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEfReadonly
      (StepsPhiN_to_StepsPhi _ _ _ _ HFun)
      HReadOnlyEf) as HHeapFun.
  subst heap_fun.
  destruct
    (StepsPhi_terminal_deterministic
      (initial_state heap env rho ef)
      phi_fun heap (Cls (env_fun, rho_fun, Mu f x ec ee))
      phi_fun_summary heap_fun_summary
        (Cls (env_fun_summary, rho_fun_summary,
          Mu f_summary x_summary ec_summary ee_summary))
      (StepsPhiN_to_StepsPhi _ _ _ _ HFun) HFunSummary)
    as [_ [HHeapFunSummary HClosureEq]].
  symmetry in HHeapFunSummary.
  subst heap_fun_summary.
  inversion HClosureEq; subst.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho ea stty ctxt rgns
      ty_ea_readonly static_ea_readonly
      phi_arg heap_arg v_arg
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEaReadonly
      (StepsPhiN_to_StepsPhi _ _ _ _ HArg)
      HReadOnlyEa) as HHeapArg.
  subst heap_arg.
  destruct
    (StepsPhi_terminal_deterministic
      (initial_state heap env rho ea)
      phi_arg heap v_arg
      phi_arg_summary heap_arg_summary v_arg_summary
      (StepsPhiN_to_StepsPhi _ _ _ _ HArg) HArgSummary)
    as [_ [HHeapArgSummary HArgEq]].
  symmetry in HHeapArgSummary.
  subst heap_arg_summary.
  subst v_arg_summary.
  destruct
    (MuApp_body_context_from_mixed_readonly_terminals
      heap env rho ef ea heap heap env_fun_summary rho_fun_summary
      f_summary x_summary ec_summary ee_summary v_arg
      phi_fun phi_arg stty ctxt rgns tya effc tyc effe
      static_ef_shape static_ea_shape
      ty_ef_readonly static_ef_readonly
      ty_ea_readonly static_ea_readonly
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEfShape HTcEaShape HTcEfReadonly HTcEaReadonly
      (StepsPhiN_to_StepsPhi _ _ _ _ HFun)
      (StepsPhiN_to_StepsPhi _ _ _ _ HArg)
      HReadOnlyEf HReadOnlyEa)
    as (rgns_body & ctxt_body & tyx_body & effc_body & tyc_body &
        effe_body & _ & _ & HTcRhoBody & _ & HTcIncBodyUpdated &
        HTcEnvBody & HEnvShapeBody & HBTBody & HTcBody & _).
  pose proof
    (HBelow
      n_fun heap heap env rho ef (Eff_App ef ea)
      phi_fun heap (Cls (env_fun_summary, rho_fun_summary,
        Mu f_summary x_summary ec_summary ee_summary))
      phi_summary heap_summary theta_summary
      stty ctxt rgns ty_ef_readonly static_ef_readonly
      HLtFun
      (SummaryReplayCompatibleForExpr_refl
        env rho (Eff_App ef ea) heap)
      HBTFun HFun HSummary HReadOnlySummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEfReadonly)
    as HFunSound.
  pose proof
    (HBelow
      n_arg heap heap env rho ea (Eff_App ef ea)
      phi_arg heap v_arg
      phi_summary heap_summary theta_summary
      stty ctxt rgns ty_ea_readonly static_ea_readonly
      HLtArg
      (SummaryReplayCompatibleForExpr_refl
        env rho (Eff_App ef ea) heap)
      HBTArg HArg HSummary HReadOnlySummary
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEaReadonly)
    as HArgSound.
  pose proof
    (HBelow
      n_body heap heap
      (update_rec_E
        (f_summary,
          Cls (env_fun_summary, rho_fun_summary,
            Mu f_summary x_summary ec_summary ee_summary))
      (x_summary, v_arg) env_fun_summary)
      rho_fun_summary ec_summary ee_summary
      phi_body heap_app v_app
      phi_body_summary heap_summary theta_summary
      stty
      (update_rec_T
        (f_summary,
          Ty_Arrow tyx_body effc_body tyc_body effe_body Ty_Effect)
        (x_summary, tyx_body) ctxt_body)
      rgns_body tyc_body effc_body
      HLtBody
      (SummaryReplayCompatibleForExpr_refl
        (update_rec_E
          (f_summary,
            Cls (env_fun_summary, rho_fun_summary,
              Mu f_summary x_summary ec_summary ee_summary))
        (x_summary, v_arg) env_fun_summary)
        rho_fun_summary ee_summary heap)
      HBTBody HBody HBodySummary HReadOnlyBodySummary
      HTcHeap HHeapShape HTcRhoBody HTcIncBodyUpdated HTcEnvBody HEnvShapeBody
      HTcBody)
    as HBodySound.
  eapply (Correctness_soundness_ext_small_step_mu_app_summary_terminal_case
    heap env rho ef ea env_fun_summary rho_fun_summary
    f_summary x_summary ec_summary ee_summary
    phi_fun heap phi_arg heap v_arg
    phi_body heap_app v_app
    phi_body_summary heap_summary theta_summary
    phi_summary heap_summary theta_summary
    phi_app heap_app v_app); eauto.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HFun).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HArg).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HBody).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HApp).
Qed.

Theorem Correctness_soundness_ext_small_step_mu_app_summary_terminal_bt_app_conc_recursive_case :
  forall heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_mu static_mu ty_eff static_ee
    ty_ef static_ef ty_ea static_ea,
    StepsPhi (initial_state heap env rho (Mu_App ef ea)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho (Eff_App ef ea)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef ea, ty_mu, static_mu) ->
    TcExp (ctxt, rgns, Eff_App ef ea, ty_eff, static_ee) ->
    ReadOnlyStatic (fold_subst_eps rho static_ee) ->
    TcExp (ctxt, rgns, ef, ty_ef, static_ef) ->
    TcExp (ctxt, rgns, ea, ty_ea, static_ea) ->
    ReadOnlyStatic (fold_subst_eps rho static_ef) ->
    ReadOnlyStatic (fold_subst_eps rho static_ea) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ef, Eff_App ef ea) ->
    BackTriangle (ctxt, rgns, rho, ea, Eff_App ef ea) ->
    SmallStepCorrectnessRecursivePremise ->
    phi_app ⋞ theta_summary.
Proof.
  intros heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_mu static_mu ty_eff static_ee
    ty_ef static_ef ty_ea static_ea
    HApp HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcMuApp HTcEffApp HReadOnlyEffApp HTcEfReadonly HTcEaReadonly
    HReadOnlyEf HReadOnlyEa HReadOnlySummary HBTFun HBTArg HRecursive.
  inversion HTcMuApp; subst.
  match goal with
  | HTcEfShape : TcExp
      (ctxt, rgns, ef,
        Ty_Arrow ?tya0 ?effc0 ?tyc0 ?effe0 Ty_Effect,
        ?static_ef_shape),
    HTcEaShape : TcExp (ctxt, rgns, ea, ?tya0, ?static_ea_shape) |- _ =>
      eapply
        (Correctness_soundness_ext_small_step_mu_app_summary_terminal_mixed_recursive_case
          heap env rho ef ea
          phi_app heap_app v_app
          phi_summary heap_summary theta_summary
          stty ctxt rgns tya0 effc0 tyc0 effe0
          static_ef_shape static_ea_shape
          ty_ef static_ef ty_ea static_ea);
	      eauto
	  end.
Qed.

Theorem Correctness_soundness_ext_small_step_mu_app_summary_terminal_bt_app_conc_below_case :
  forall n heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_mu static_mu ty_eff static_ee
    ty_ef static_ef ty_ea static_ea,
    StepsPhiN n (initial_state heap env rho (Mu_App ef ea)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho (Eff_App ef ea)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef ea, ty_mu, static_mu) ->
    TcExp (ctxt, rgns, Eff_App ef ea, ty_eff, static_ee) ->
    ReadOnlyStatic (fold_subst_eps rho static_ee) ->
    TcExp (ctxt, rgns, ef, ty_ef, static_ef) ->
    TcExp (ctxt, rgns, ea, ty_ea, static_ea) ->
    ReadOnlyStatic (fold_subst_eps rho static_ef) ->
    ReadOnlyStatic (fold_subst_eps rho static_ea) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ef, Eff_App ef ea) ->
    BackTriangle (ctxt, rgns, rho, ea, Eff_App ef ea) ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi_app ⋞ theta_summary.
Proof.
  intros n heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_mu static_mu ty_eff static_ee
    ty_ef static_ef ty_ea static_ea
    HApp HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcMuApp HTcEffApp HReadOnlyEffApp HTcEfReadonly HTcEaReadonly
    HReadOnlyEf HReadOnlyEa HReadOnlySummary HBTFun HBTArg HBelow.
  inversion HTcMuApp; subst.
  match goal with
  | HTcEfShape : TcExp
      (ctxt, rgns, ef,
        Ty_Arrow ?tya0 ?effc0 ?tyc0 ?effe0 Ty_Effect,
        ?static_ef_shape),
    HTcEaShape : TcExp (ctxt, rgns, ea, ?tya0, ?static_ea_shape) |- _ =>
      eapply
        (Correctness_soundness_ext_small_step_mu_app_summary_terminal_mixed_below_case
          n heap env rho ef ea
          phi_app heap_app v_app
          phi_summary heap_summary theta_summary
          stty ctxt rgns tya0 effc0 tyc0 effe0
          static_ef_shape static_ea_shape
          ty_ef static_ef ty_ea static_ea);
      eauto
  end.
Qed.

Theorem Correctness_soundness_ext_small_step_mu_app_summary_terminal_bt_app_conc_summary_replay_below_case :
  forall n heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_mu static_mu ty_eff static_ee
    ty_ef static_ef ty_ea static_ea,
    StepsPhiN n (initial_state heap env rho (Mu_App ef ea)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho (Eff_App ef ea)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef ea, ty_mu, static_mu) ->
    TcExp (ctxt, rgns, Eff_App ef ea, ty_eff, static_ee) ->
    ReadOnlyStatic (fold_subst_eps rho static_ee) ->
    TcExp (ctxt, rgns, ef, ty_ef, static_ef) ->
    TcExp (ctxt, rgns, ea, ty_ea, static_ea) ->
    ReadOnlyStatic (fold_subst_eps rho static_ef) ->
    ReadOnlyStatic (fold_subst_eps rho static_ea) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ef, Eff_App ef ea) ->
    BackTriangle (ctxt, rgns, rho, ea, Eff_App ef ea) ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi_app ⋞ theta_summary.
Proof.
  intros n heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_mu static_mu ty_eff static_ee
    ty_ef static_ef ty_ea static_ea
    HApp HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcMuApp HTcEffApp HReadOnlyEffApp HTcEfReadonly HTcEaReadonly
    HReadOnlyEf HReadOnlyEa HReadOnlySummary HBTFun HBTArg HBelow.
  inversion HTcMuApp; subst.
  match goal with
  | HTcEfShape : TcExp
      (ctxt, rgns, ef,
        Ty_Arrow ?tya0 ?effc0 ?tyc0 ?effe0 Ty_Effect,
        ?static_ef_shape),
    HTcEaShape : TcExp (ctxt, rgns, ea, ?tya0, ?static_ea_shape) |- _ =>
      eapply
        (Correctness_soundness_ext_small_step_mu_app_summary_terminal_mixed_summary_replay_below_case
          n heap env rho ef ea
          phi_app heap_app v_app
          phi_summary heap_summary theta_summary
          stty ctxt rgns tya0 effc0 tyc0 effe0
          static_ef_shape static_ea_shape
          ty_ef static_ef ty_ea static_ea);
      eauto
  end.
Qed.

Theorem Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_bt_recursive_case :
  forall heap env rho er w
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_app static_app ty_er static_er,
    StepsPhi (initial_state heap env rho (Rgn_App er w)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho Empty) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Rgn_App er w, ty_app, static_app) ->
    TcExp (ctxt, rgns, er, ty_er, static_er) ->
    BackTriangle (ctxt, rgns, rho, er, Empty) ->
    SmallStepCorrectnessRecursivePremise ->
    phi_app ⋞ theta_summary.
Proof.
  intros heap env rho er w
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_app static_app ty_er static_er
    HApp HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcRgnApp HTcErBT HBTEr HRecursive.
  inversion HTcRgnApp; subst.
  match goal with
  | HTcEr : TcExp
      (ctxt, rgns, er, Ty_ForallRgn ?effr0 ?tyr0, ?static_er0) |- _ =>
      eapply
        (Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_named_recursive_case
          heap env rho er w
          phi_app heap_app v_app
          phi_summary heap_summary theta_summary
          stty ctxt rgns effr0 tyr0 static_er0);
	      eauto
	  end.
Qed.

Theorem Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_bt_below_case :
  forall n heap env rho er w
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_app static_app ty_er static_er,
    StepsPhiN n (initial_state heap env rho (Rgn_App er w)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho Empty) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Rgn_App er w, ty_app, static_app) ->
    TcExp (ctxt, rgns, er, ty_er, static_er) ->
    BackTriangle (ctxt, rgns, rho, er, Empty) ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi_app ⋞ theta_summary.
Proof.
  intros n heap env rho er w
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_app static_app ty_er static_er
    HApp HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcRgnApp HTcErBT HBTEr HBelow.
  inversion HTcRgnApp; subst.
  match goal with
  | HTcEr : TcExp
      (ctxt, rgns, er, Ty_ForallRgn ?effr0 ?tyr0, ?static_er0) |- _ =>
      eapply
        (Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_below_case
          n heap env rho er w
          phi_app heap_app v_app
          phi_summary heap_summary theta_summary
          stty ctxt rgns effr0 tyr0 static_er0);
      eauto
  end.
Qed.

Theorem Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_bt_summary_replay_below_case :
  forall n heap env rho er w
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_app static_app ty_er static_er,
    StepsPhiN n (initial_state heap env rho (Rgn_App er w)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho Empty) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Rgn_App er w, ty_app, static_app) ->
    TcExp (ctxt, rgns, er, ty_er, static_er) ->
    BackTriangle (ctxt, rgns, rho, er, Empty) ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi_app ⋞ theta_summary.
Proof.
  intros n heap env rho er w
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_app static_app ty_er static_er
    HApp HSummary HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcRgnApp HTcErBT HBTEr HBelow.
  inversion HTcRgnApp; subst.
  match goal with
  | HTcEr : TcExp
      (ctxt, rgns, er, Ty_ForallRgn ?effr0 ?tyr0, ?static_er0) |- _ =>
      eapply
        (Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_summary_replay_below_case
          n heap env rho er w
          phi_app heap_app v_app
          phi_summary heap_summary theta_summary
          stty ctxt rgns effr0 tyr0 static_er0);
      eauto
  end.
Qed.

Theorem Correctness_soundness_ext_small_step_deref_conc_summary_terminal_recursive_case :
  forall heap env rho e r
    phi_summary heap_summary theta
    phi_deref heap_deref v_deref
    stty ctxt rgns ty_e static_e,
    StepsPhi (initial_state heap env rho (ReadConc e)) phi_summary
      (StDone heap_summary (Eff theta)) ->
    StepsPhi
      (initial_state heap env rho (DeRef (Rgn_Const true false r) e))
      phi_deref (StDone heap_deref v_deref) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    BackTriangle (ctxt, rgns, rho, e, Empty) ->
    SmallStepCorrectnessRecursivePremise ->
    phi_deref ⋞ theta.
Proof.
  intros heap env rho e r
    phi_summary heap_summary theta
    phi_deref heap_deref v_deref
    stty ctxt rgns ty_e static_e
    HSummary HDeref HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE HBTE HRecursive.
  unfold SmallStepCorrectnessRecursivePremise in HRecursive.
  eapply Correctness_soundness_ext_small_step_deref_conc_summary_terminal_direct_case;
    eauto.
  intros phi_arg heap_arg l HArg.
  pose proof (initial_empty_steps_phi_done heap env rho) as HEmpty.
  assert (HReadOnlyEmpty :
    ReadOnlyPhi
      (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))).
  {
    apply ReadOnlyPhi_of_phi_as_list_nil.
    reflexivity.
  }
  eapply (HRecursive
    heap env rho e Empty
    phi_arg heap_arg (Loc (Rgn_Const true false r) l)
    (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))
    heap Theta_Empty
	    stty ctxt rgns ty_e static_e); eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_deref_conc_summary_terminal_below_case :
  forall n heap env rho e r
    phi_summary heap_summary theta
    phi_deref heap_deref v_deref
    stty ctxt rgns ty_e static_e,
    StepsPhi (initial_state heap env rho (ReadConc e)) phi_summary
      (StDone heap_summary (Eff theta)) ->
    StepsPhiN n
      (initial_state heap env rho (DeRef (Rgn_Const true false r) e))
      phi_deref (StDone heap_deref v_deref) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    BackTriangle (ctxt, rgns, rho, e, Empty) ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi_deref ⋞ theta.
Proof.
  intros n heap env rho e r
    phi_summary heap_summary theta
    phi_deref heap_deref v_deref
    stty ctxt rgns ty_e static_e
    HSummary HDeref HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE HBTE HBelow.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_deref_terminal_decompose_counts
      n heap env rho (Rgn_Const true false r) e
      phi_deref heap_deref v_deref HDeref)
    as (n_arg & phi_arg & heap_arg & r_read & l & v &
        HLtArg & HArg & HFindR & HFindH & _ & _ & _).
  simpl in HFindR.
  inversion HFindR; subst r_read.
  pose proof (initial_empty_steps_phi_done heap env rho) as HEmpty.
  assert (HReadOnlyEmpty :
    ReadOnlyPhi
      (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))).
  {
    apply ReadOnlyPhi_of_phi_as_list_nil.
    reflexivity.
  }
  pose proof
    (HBelow
      n_arg heap heap env rho e Empty
      phi_arg heap_arg (Loc (Rgn_Const true false r) l)
      (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))
      heap Theta_Empty
      stty ctxt rgns ty_e static_e
      HLtArg HBTE HArg HEmpty HReadOnlyEmpty
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcE)
    as HArgSound.
  eapply
    (Correctness_soundness_ext_small_step_deref_conc_summary_terminal_case
      heap env rho e phi_arg heap_arg r l v
      phi_summary heap_summary theta
      phi_deref heap_deref v_deref); eauto.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HArg).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HDeref).
Qed.

Theorem Correctness_soundness_ext_small_step_deref_conc_summary_terminal_summary_replay_below_case :
  forall n heap env rho e r
    phi_summary heap_summary theta
    phi_deref heap_deref v_deref
    stty ctxt rgns ty_e static_e,
    StepsPhi (initial_state heap env rho (ReadConc e)) phi_summary
      (StDone heap_summary (Eff theta)) ->
    StepsPhiN n
      (initial_state heap env rho (DeRef (Rgn_Const true false r) e))
      phi_deref (StDone heap_deref v_deref) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    BackTriangle (ctxt, rgns, rho, e, Empty) ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi_deref ⋞ theta.
Proof.
  intros n heap env rho e r
    phi_summary heap_summary theta
    phi_deref heap_deref v_deref
    stty ctxt rgns ty_e static_e
    HSummary HDeref HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcE HBTE HBelow.
  unfold SmallStepCorrectnessSummaryReplayRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhiN_deref_terminal_decompose_counts
      n heap env rho (Rgn_Const true false r) e
      phi_deref heap_deref v_deref HDeref)
    as (n_arg & phi_arg & heap_arg & r_read & l & v &
        HLtArg & HArg & HFindR & HFindH & _ & _ & _).
  simpl in HFindR.
  inversion HFindR; subst r_read.
  pose proof (initial_empty_steps_phi_done heap env rho) as HEmpty.
  assert (HReadOnlyEmpty :
    ReadOnlyPhi
      (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))).
  {
    apply ReadOnlyPhi_of_phi_as_list_nil.
    reflexivity.
  }
  pose proof
    (HBelow
      n_arg heap heap env rho e Empty
      phi_arg heap_arg (Loc (Rgn_Const true false r) l)
      (Phi_Seq (label_phi Silent) (Phi_Seq (label_phi Silent) Phi_Nil))
      heap Theta_Empty
      stty ctxt rgns ty_e static_e
      HLtArg (SummaryReplayCompatibleForExpr_refl env rho Empty heap)
      HBTE HArg HEmpty HReadOnlyEmpty
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcE)
    as HArgSound.
  eapply
    (Correctness_soundness_ext_small_step_deref_conc_summary_terminal_case
      heap env rho e phi_arg heap_arg r l v
      phi_summary heap_summary theta
      phi_deref heap_deref v_deref); eauto.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HArg).
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HDeref).
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_heterogeneous_recursive_case :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2,
    StepsPhi
      (initial_state heap env rho
        (Concat (Concat eff1 eff2) (Concat eff3 eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, static_mu1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, static_mu2) ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_eff1, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_eff2, static_eff2) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, eff3) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, eff4) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2
    HSummary HPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcMu1 HTcMu2 HTcEff1 HTcEff2 HReadOnlyStatic1 HReadOnlyStatic2
    HBTEff1 HBTEff2 HBTMu1 HBTMu2 HReadOnlySummary HRecursive.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremise in HRecursive.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho (Concat eff1 eff2) (Concat eff3 eff4)
      phi_summary heap_summary theta_summary HSummary)
    as (phi_sum12 & heap_sum12 & theta12 &
        phi_sum34 & heap_sum34 & theta34 &
        HSum12 & HSum34 & HHeapSummary & HThetaSummary & HTraceSummary).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 eff2
      phi_sum12 heap_sum12 theta12 HSum12)
    as (phi_sum1 & heap_sum1 & theta1 &
        phi_sum2 & heap_sum2 & theta2 &
        HSum1 & HSum2 & HHeap12 & HTheta12 & HTrace12).
  subst heap_sum12.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_sum2 env rho eff3 eff4
      phi_sum34 heap_sum34 theta34 HSum34)
    as (phi_sum3 & heap_sum3 & theta3 &
        phi_sum4 & heap_sum4 & theta4 &
        HSum3 & HSum4 & HHeap34 & HTheta34 & HTrace34).
  subst heap_sum34.
  destruct
    (StepsPhi_pair_par_terminal_decompose
      heap env rho ef1 ea1 ef2 ea2 phi_pair heap_pair v_pair HPair)
    as (phi_eff1 & heap_eff1 & theta_eff1 &
        phi_eff2 & heap_eff2 & theta_eff2 &
        phi_mu1 & heap_mu1 & v1 &
        phi_mu2 & heap_mu2 & v2 &
        HEff1 & HEff2 & HMu1 & HMu2 &
        _ & _ & HTracePair).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_sum12 phi_sum34
      HReadOnlySummary HTraceSummary) as HReadOnly12.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_sum12 phi_sum34
      HReadOnlySummary HTraceSummary) as HReadOnly34.
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_sum12 phi_sum1 phi_sum2
      HReadOnly12 HTrace12) as HReadOnly1.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_sum12 phi_sum1 phi_sum2
      HReadOnly12 HTrace12) as HReadOnly2.
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_sum34 phi_sum3 phi_sum4
      HReadOnly34 HTrace34) as HReadOnly3.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_sum34 phi_sum3 phi_sum4
      HReadOnly34 HTrace34) as HReadOnly4.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho (Eff_App ef1 ea1) stty ctxt rgns
      ty_eff1 static_eff1
      phi_eff1 heap_eff1 (Eff theta_eff1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff1
      HEff1 HReadOnlyStatic1) as HHeapEff1.
  subst heap_eff1.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho (Eff_App ef2 ea2) stty ctxt rgns
      ty_eff2 static_eff2
      phi_eff2 heap_eff2 (Eff theta_eff2)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff2
      HEff2 HReadOnlyStatic2) as HHeapEff2.
  subst heap_eff2.
  destruct
    (StepsPhi_initial_terminal_value_typed
      heap env rho (Mu_App ef1 ea1) stty ctxt rgns
      ty1 static_mu1 phi_mu1 heap_mu1 v1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcMu1 HMu1)
    as (stty_mu1 & HExtMu1 & HTcHeapMu1 & HHeapShapeMu1 &
        _ & _).
  assert (HTcEnvMu1 : TcEnv (stty_mu1, rho, env, ctxt)).
  {
    eapply ext_stores__env; eauto.
  }
  assert (HEnvShapeMu1 : RuntimeEnvShape stty_mu1 rho env ctxt).
  {
    eapply RuntimeEnvShape_store_ext; eauto.
  }
  pose proof
    (HRecursive
      heap heap env rho (Eff_App ef1 ea1) eff1
      phi_eff1 heap (Eff theta_eff1)
      phi_sum1 heap_sum1 theta1
      stty ctxt rgns ty_eff1 static_eff1
      HBTEff1 HEff1 HSum1 HReadOnly1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEff1) as HEff1Sound.
  pose proof
    (HRecursive
      heap heap_sum1 env rho (Eff_App ef2 ea2) eff2
      phi_eff2 heap (Eff theta_eff2)
      phi_sum2 heap_sum2 theta2
      stty ctxt rgns ty_eff2 static_eff2
      HBTEff2 HEff2 HSum2 HReadOnly2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEff2) as HEff2Sound.
  pose proof
    (HRecursive
      heap heap_sum2 env rho (Mu_App ef1 ea1) eff3
      phi_mu1 heap_mu1 v1
      phi_sum3 heap_sum3 theta3
      stty ctxt rgns ty1 static_mu1
      HBTMu1 HMu1 HSum3 HReadOnly3
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcMu1) as HMu1Sound.
  pose proof
    (HRecursive
      heap_mu1 heap_sum3 env rho (Mu_App ef2 ea2) eff4
      phi_mu2 heap_mu2 v2
      phi_sum4 heap_sum4 theta4
      stty_mu1 ctxt rgns ty2 static_mu2
      HBTMu2 HMu2 HSum4 HReadOnly4
      HTcHeapMu1 HHeapShapeMu1 HTcRho HTcInc HTcEnvMu1 HEnvShapeMu1
      HTcMu2) as HMu2Sound.
  subst theta12.
  subst theta34.
  subst theta_summary.
	  eapply Correctness_soundness_ext_small_step_quad_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_heterogeneous_below_case :
  forall n heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2,
    StepsPhi
      (initial_state heap env rho
        (Concat (Concat eff1 eff2) (Concat eff3 eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhiN n (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, static_mu1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, static_mu2) ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_eff1, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_eff2, static_eff2) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, eff3) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, eff4) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi_pair ⋞ theta_summary.
Proof.
  intros n heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2
    HSummary HPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcMu1 HTcMu2 HTcEff1 HTcEff2 HReadOnlyStatic1 HReadOnlyStatic2
    HBTEff1 HBTEff2 HBTMu1 HBTMu2 HReadOnlySummary HBelow.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho (Concat eff1 eff2) (Concat eff3 eff4)
      phi_summary heap_summary theta_summary HSummary)
    as (phi_sum12 & heap_sum12 & theta12 &
        phi_sum34 & heap_sum34 & theta34 &
        HSum12 & HSum34 & HHeapSummary & HThetaSummary & HTraceSummary).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 eff2
      phi_sum12 heap_sum12 theta12 HSum12)
    as (phi_sum1 & heap_sum1 & theta1 &
        phi_sum2 & heap_sum2 & theta2 &
        HSum1 & HSum2 & HHeap12 & HTheta12 & HTrace12).
  subst heap_sum12.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_sum2 env rho eff3 eff4
      phi_sum34 heap_sum34 theta34 HSum34)
    as (phi_sum3 & heap_sum3 & theta3 &
        phi_sum4 & heap_sum4 & theta4 &
        HSum3 & HSum4 & HHeap34 & HTheta34 & HTrace34).
  subst heap_sum34.
  destruct
    (StepsPhiN_pair_par_terminal_decompose_counts
      n heap env rho ef1 ea1 ef2 ea2 phi_pair heap_pair v_pair HPair)
    as (n_eff1 & phi_eff1 & heap_eff1 & theta_eff1 &
        n_eff2 & phi_eff2 & heap_eff2 & theta_eff2 &
        n_mu1 & phi_mu1 & heap_mu1 & v1 &
        n_mu2 & phi_mu2 & heap_mu2 & v2 &
        HLtEff1 & HLtEff2 & HLtMu1 & HLtMu2 &
        HEff1 & HEff2 & HMu1 & HMu2 &
        _ & _ & HTracePair).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_sum12 phi_sum34
      HReadOnlySummary HTraceSummary) as HReadOnly12.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_sum12 phi_sum34
      HReadOnlySummary HTraceSummary) as HReadOnly34.
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_sum12 phi_sum1 phi_sum2
      HReadOnly12 HTrace12) as HReadOnly1.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_sum12 phi_sum1 phi_sum2
      HReadOnly12 HTrace12) as HReadOnly2.
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_sum34 phi_sum3 phi_sum4
      HReadOnly34 HTrace34) as HReadOnly3.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_sum34 phi_sum3 phi_sum4
      HReadOnly34 HTrace34) as HReadOnly4.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho (Eff_App ef1 ea1) stty ctxt rgns
      ty_eff1 static_eff1
      phi_eff1 heap_eff1 (Eff theta_eff1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff1
      (StepsPhiN_to_StepsPhi _ _ _ _ HEff1) HReadOnlyStatic1) as HHeapEff1.
  subst heap_eff1.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho (Eff_App ef2 ea2) stty ctxt rgns
      ty_eff2 static_eff2
      phi_eff2 heap_eff2 (Eff theta_eff2)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff2
      (StepsPhiN_to_StepsPhi _ _ _ _ HEff2) HReadOnlyStatic2) as HHeapEff2.
  subst heap_eff2.
  destruct
    (StepsPhi_initial_terminal_value_typed
      heap env rho (Mu_App ef1 ea1) stty ctxt rgns
      ty1 static_mu1 phi_mu1 heap_mu1 v1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcMu1 (StepsPhiN_to_StepsPhi _ _ _ _ HMu1))
    as (stty_mu1 & HExtMu1 & HTcHeapMu1 & HHeapShapeMu1 &
        _ & _).
  assert (HTcEnvMu1 : TcEnv (stty_mu1, rho, env, ctxt)).
  {
    eapply ext_stores__env; eauto.
  }
  assert (HEnvShapeMu1 : RuntimeEnvShape stty_mu1 rho env ctxt).
  {
    eapply RuntimeEnvShape_store_ext; eauto.
  }
  pose proof
    (HBelow
      n_eff1 heap heap env rho (Eff_App ef1 ea1) eff1
      phi_eff1 heap (Eff theta_eff1)
      phi_sum1 heap_sum1 theta1
      stty ctxt rgns ty_eff1 static_eff1
      HLtEff1 HBTEff1 HEff1 HSum1 HReadOnly1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEff1) as HEff1Sound.
  pose proof
    (HBelow
      n_eff2 heap heap_sum1 env rho (Eff_App ef2 ea2) eff2
      phi_eff2 heap (Eff theta_eff2)
      phi_sum2 heap_sum2 theta2
      stty ctxt rgns ty_eff2 static_eff2
      HLtEff2 HBTEff2 HEff2 HSum2 HReadOnly2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEff2) as HEff2Sound.
  pose proof
    (HBelow
      n_mu1 heap heap_sum2 env rho (Mu_App ef1 ea1) eff3
      phi_mu1 heap_mu1 v1
      phi_sum3 heap_sum3 theta3
      stty ctxt rgns ty1 static_mu1
      HLtMu1 HBTMu1 HMu1 HSum3 HReadOnly3
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcMu1) as HMu1Sound.
  pose proof
    (HBelow
      n_mu2 heap_mu1 heap_sum3 env rho (Mu_App ef2 ea2) eff4
      phi_mu2 heap_mu2 v2
      phi_sum4 heap_sum4 theta4
      stty_mu1 ctxt rgns ty2 static_mu2
      HLtMu2 HBTMu2 HMu2 HSum4 HReadOnly4
      HTcHeapMu1 HHeapShapeMu1 HTcRho HTcInc HTcEnvMu1 HEnvShapeMu1
      HTcMu2) as HMu2Sound.
  subst theta12.
  subst theta34.
  subst theta_summary.
  eapply Correctness_soundness_ext_small_step_quad_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_canonical_eff_app_backtriangle_heterogeneous_below_case :
  forall n heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (Eff_App ef1 ea1 ⊕ Eff_App ef2 ea2)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhiN n (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi_pair ⋞ theta_summary.
Proof.
  intros n heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair
    HBack HSummary HPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcPair HReadOnlySummary HBelow.
  assert (HBackCanonical :
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (Eff_App ef1 ea1 ⊕ Eff_App ef2 ea2))).
  {
    inversion HBack; subst; try discriminate.
    inversion HTcPair; subst.
    match goal with
    | HTcMu1 : TcExp (ctxt, rgns, Mu_App ef1 ea1, _, _),
      HTcMu2 : TcExp (ctxt, rgns, Mu_App ef2 ea2, _, _),
      HTcEff1 : TcExp
        (ctxt, rgns, Eff_App ef1 ea1, ?ty_e, ?static_ee_1),
      HReadOnly1 : ReadOnlyStatic (fold_subst_eps rho ?static_ee_1),
      HTcEff2 : TcExp
        (ctxt, rgns, Eff_App ef2 ea2, ?ty_e, ?static_ee_2),
      HReadOnly2 : ReadOnlyStatic (fold_subst_eps rho ?static_ee_2),
      HBTEff1 : BackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1),
      HBTEff2 : BackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2)
        |- _ =>
        assert (HBTMu1Eff :
          BackTriangle
            (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1))
          by (inversion HTcMu1; subst; eauto);
        assert (HBTMu2Eff :
          BackTriangle
            (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2))
          by (inversion HTcMu2; subst; eauto);
        eapply
          (BT_Pair_Par ctxt rgns rho ef1 ea1 ef2 ea2
            eff1 eff2 (Eff_App ef1 ea1) (Eff_App ef2 ea2)
            ty_e static_ee_1 static_ee_2);
        eauto
    end.
  }
  inversion HBackCanonical; subst; try discriminate.
  inversion HTcPair; subst.
  match goal with
  | HTcMu1 : TcExp
      (ctxt, rgns, Mu_App ef1 ea1, ?ty_mu1, ?static_mu1),
    HTcMu2 : TcExp
      (ctxt, rgns, Mu_App ef2 ea2, ?ty_mu2, ?static_mu2),
    HTcEff1 : TcExp
      (ctxt, rgns, Eff_App ef1 ea1, ?ty_eff1, ?static_eff1),
    HTcEff2 : TcExp
      (ctxt, rgns, Eff_App ef2 ea2, ?ty_eff2, ?static_eff2),
    HReadOnly1 : ReadOnlyStatic (fold_subst_eps rho ?static_eff1),
    HReadOnly2 : ReadOnlyStatic (fold_subst_eps rho ?static_eff2),
    HBTEff1 : BackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1),
    HBTEff2 : BackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2),
    HBTMu1Eff : BackTriangle
      (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1),
    HBTMu2Eff : BackTriangle
      (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) |- _ =>
      eapply
        (Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_heterogeneous_below_case
          n heap env rho ef1 ea1 ef2 ea2
          eff1 eff2 (Eff_App ef1 ea1) (Eff_App ef2 ea2)
          phi_summary heap_summary theta_summary
          phi_pair heap_pair v_pair
          stty ctxt rgns ty_mu1 ty_mu2 static_mu1 static_mu2
          ty_eff1 ty_eff2 static_eff1 static_eff2);
	      eauto
	  end.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_backtriangle_heterogeneous_below_case :
  forall n heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhiN n (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi_pair ⋞ theta_summary.
Proof.
  intros n heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair
    HBack HSummary HPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcPair HReadOnlySummary HBelow.
  inversion HBack; subst; try discriminate.
  inversion HTcPair; subst.
  match goal with
  | HTcMu1 : TcExp
      (ctxt, rgns, Mu_App ef1 ea1, ?ty_mu1, ?static_mu1),
    HTcMu2 : TcExp
      (ctxt, rgns, Mu_App ef2 ea2, ?ty_mu2, ?static_mu2),
    HTcEff1 : TcExp
      (ctxt, rgns, Eff_App ef1 ea1, ?ty_eff1, ?static_eff1),
    HTcEff2 : TcExp
      (ctxt, rgns, Eff_App ef2 ea2, ?ty_eff2, ?static_eff2),
    HReadOnly1 : ReadOnlyStatic (fold_subst_eps rho ?static_eff1),
    HReadOnly2 : ReadOnlyStatic (fold_subst_eps rho ?static_eff2) |- _ =>
      eapply
        (Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_heterogeneous_below_case
          n heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
          phi_summary heap_summary theta_summary
          phi_pair heap_pair v_pair
          stty ctxt rgns ty_mu1 ty_mu2 static_mu1 static_mu2
          ty_eff1 ty_eff2 static_eff1 static_eff2);
      eauto
  end.
Qed.

Theorem Correctness_soundness_ext_small_step_backtriangle_terminal_below_case :
  forall n heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhiN n (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    SmallStepCorrectnessHeterogeneousRecursivePremiseBelow n ->
    phi ⋞ theta_summary.
Proof.
  intros n heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HBack HStepsN HSummary HReadOnlySummary
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HBelow.
  pose proof (StepsPhiN_to_StepsPhi _ _ _ _ HStepsN) as HSteps.
  inversion HBack; subst;
    try solve [eauto using
      Correctness_soundness_ext_small_step_num_case,
      Correctness_soundness_ext_small_step_bool_case,
      Correctness_soundness_ext_small_step_var_typed_case,
      Correctness_soundness_ext_small_step_mu_abs_case,
	      Correctness_soundness_ext_small_step_rgn_abs_case,
	      Correctness_soundness_ext_small_step_top_summary_case,
	      Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_heterogeneous_below_case,
	      Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_heterogeneous_below_case,
	      Correctness_soundness_ext_small_step_deref_conc_summary_terminal_below_case,
	      Correctness_soundness_ext_small_step_cond_summary_terminal_below_case,
	      Correctness_soundness_ext_small_step_plus_summary_terminal_heterogeneous_below_case,
	      Correctness_soundness_ext_small_step_minus_summary_terminal_heterogeneous_below_case,
      Correctness_soundness_ext_small_step_times_summary_terminal_heterogeneous_below_case,
      Correctness_soundness_ext_small_step_eq_summary_terminal_heterogeneous_below_case,
	      Correctness_soundness_ext_small_step_mu_app_summary_terminal_bt_app_conc_below_case,
	      Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_bt_below_case,
	      Correctness_soundness_ext_small_step_pair_par_backtriangle_heterogeneous_below_case].
  all:
    lazymatch goal with
    | HStepsMu : StepsPhiN ?n0
        (initial_state ?heap0 ?env0 ?rho0 (Mu_App ?ef ?ea))
        ?phi0 (StDone ?heap_done ?v_done),
      HSummaryMu : StepsPhi
        (initial_state ?heap0 ?env0 ?rho0 (Eff_App ?ef ?ea))
        ?phi_summary0 (StDone ?heap_summary0 (Eff ?theta_summary0)) |- _ =>
        eapply
          Correctness_soundness_ext_small_step_mu_app_summary_terminal_bt_app_conc_below_case;
        eauto
    | HStepsAssign : StepsPhiN ?n0
        (initial_state ?heap0 ?env0 ?rho0
          (Assign (Rgn_Const true false ?r) ?e1 ?e2))
        ?phi0 (StDone ?heap_done ?v_done) |- _ =>
        inversion HTcExp; subst;
        eapply
          (Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_heterogeneous_below_case
            n heap heap env rho e1 e2 eff1 eff2 r
            phi_summary heap_summary theta_summary
            phi heap' v
            stty ctxt rgns ty_e1 static_e1 _ _);
        eauto using HeterogeneousHeapForExpr_refl
    | HStepsAssign : StepsPhiN ?n0
        (initial_state ?heap0 ?env0 ?rho0 (Assign ?w ?e1 ?e2))
        ?phi0 (StDone ?heap_done ?v_done),
      HSummaryAssign : StepsPhi
        (initial_state ?heap0 ?env0 ?rho0 (Concat ?eff1 (Concat ?eff2 (WriteAbs ?w))))
        ?phi_summary0 (StDone ?heap_summary0 (Eff ?theta_summary0)) |- _ =>
        inversion HTcExp; subst;
        eapply
          (Correctness_soundness_ext_small_step_assign_abs_bt_summary_terminal_heterogeneous_below_case
            n heap heap env rho _ _ _ _ _
            phi_summary heap_summary theta_summary
            phi heap' v
            stty ctxt rgns ty_e1 static_e1 _ _);
        eauto
    end.
Qed.

Theorem Correctness_soundness_ext_small_step_backtriangle_terminal_counted_recursive_case :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
  intros heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HBack HSteps HSummary HReadOnlySummary
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp
    HRecursive.
  destruct (StepsPhi_to_StepsPhiN _ _ _ HSteps) as (n & HStepsN).
  eapply
    (Correctness_soundness_ext_small_step_backtriangle_terminal_below_case
      n heap env rho ea ee phi heap' v
      phi_summary heap_summary theta_summary
      stty ctxt rgns ty static); eauto.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremiseBelow.
  intros n_child heap_child heap_summary_start env_child rho_child
    ea_child ee_child phi_child heap_child' v_child
    phi_summary_child heap_summary_child theta_summary_child
    stty_child ctxt_child rgns_child ty_child static_child
    _ HBackChild HStepsChild HSummaryChild HReadOnlySummaryChild
    HTcHeapChild HHeapShapeChild HTcRhoChild HTcIncChild HTcEnvChild
    HEnvShapeChild HTcExpChild.
  unfold SmallStepCorrectnessHeterogeneousRecursivePremise in HRecursive.
  eapply
    (HRecursive
      heap_child heap_summary_start env_child rho_child ea_child ee_child
      phi_child heap_child' v_child
      phi_summary_child heap_summary_child theta_summary_child
      stty_child ctxt_child rgns_child ty_child static_child); eauto.
  exact (StepsPhiN_to_StepsPhi _ _ _ _ HStepsChild).
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_heap_compatible_recursive_case :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2,
    StepsPhi
      (initial_state heap env rho
        (Concat (Concat eff1 eff2) (Concat eff3 eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    PairParBranchHeapCompatible heap env rho ef1 ea1 ef2 ea2 ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, static_mu1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, static_mu2) ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_eff1, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_eff2, static_eff2) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, eff3) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, eff4) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeapCompatibleRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2
    HSummary HPair HBranchCompat HTcHeap HHeapShape HTcRho HTcInc
    HTcEnv HEnvShape HTcMu1 HTcMu2 HTcEff1 HTcEff2
    HReadOnlyStatic1 HReadOnlyStatic2 HBTEff1 HBTEff2 HBTMu1 HBTMu2
    HReadOnlySummary HRecursive.
  unfold SmallStepCorrectnessHeapCompatibleRecursivePremise in HRecursive.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho (Concat eff1 eff2) (Concat eff3 eff4)
      phi_summary heap_summary theta_summary HSummary)
    as (phi_sum12 & heap_sum12 & theta12 &
        phi_sum34 & heap_sum34 & theta34 &
        HSum12 & HSum34 & HHeapSummary & HThetaSummary & HTraceSummary).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 eff2
      phi_sum12 heap_sum12 theta12 HSum12)
    as (phi_sum1 & heap_sum1 & theta1 &
        phi_sum2 & heap_sum2 & theta2 &
        HSum1 & HSum2 & HHeap12 & HTheta12 & HTrace12).
  subst heap_sum12.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_sum2 env rho eff3 eff4
      phi_sum34 heap_sum34 theta34 HSum34)
    as (phi_sum3 & heap_sum3 & theta3 &
        phi_sum4 & heap_sum4 & theta4 &
        HSum3 & HSum4 & HHeap34 & HTheta34 & HTrace34).
  subst heap_sum34.
  destruct
    (StepsPhi_pair_par_terminal_decompose
      heap env rho ef1 ea1 ef2 ea2 phi_pair heap_pair v_pair HPair)
    as (phi_eff1 & heap_eff1 & theta_eff1 &
        phi_eff2 & heap_eff2 & theta_eff2 &
        phi_mu1 & heap_mu1 & v1 &
        phi_mu2 & heap_mu2 & v2 &
        HEff1 & HEff2 & HMu1 & HMu2 &
        _ & _ & HTracePair).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_sum12 phi_sum34
      HReadOnlySummary HTraceSummary) as HReadOnly12.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_sum12 phi_sum34
      HReadOnlySummary HTraceSummary) as HReadOnly34.
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_sum12 phi_sum1 phi_sum2
      HReadOnly12 HTrace12) as HReadOnly1.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_sum12 phi_sum1 phi_sum2
      HReadOnly12 HTrace12) as HReadOnly2.
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_sum34 phi_sum3 phi_sum4
      HReadOnly34 HTrace34) as HReadOnly3.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_sum34 phi_sum3 phi_sum4
      HReadOnly34 HTrace34) as HReadOnly4.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho (Eff_App ef1 ea1) stty ctxt rgns
      ty_eff1 static_eff1
      phi_eff1 heap_eff1 (Eff theta_eff1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff1
      HEff1 HReadOnlyStatic1) as HHeapEff1.
  subst heap_eff1.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho (Eff_App ef2 ea2) stty ctxt rgns
      ty_eff2 static_eff2
      phi_eff2 heap_eff2 (Eff theta_eff2)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff2
      HEff2 HReadOnlyStatic2) as HHeapEff2.
  subst heap_eff2.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff1) phi_sum1
      (StDone heap_sum1 (Eff theta1))
      HSum1 HReadOnly1) as HHeapSum1.
  simpl in HHeapSum1.
  subst heap_sum1.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff2) phi_sum2
      (StDone heap_sum2 (Eff theta2))
      HSum2 HReadOnly2) as HHeapSum2.
  simpl in HHeapSum2.
  subst heap_sum2.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff3) phi_sum3
      (StDone heap_sum3 (Eff theta3))
      HSum3 HReadOnly3) as HHeapSum3.
  simpl in HHeapSum3.
  subst heap_sum3.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff4) phi_sum4
      (StDone heap_sum4 (Eff theta4))
      HSum4 HReadOnly4) as HHeapSum4.
  simpl in HHeapSum4.
  symmetry in HHeapSum4.
  rewrite HHeapSum4 in *.
  clear HHeapSum4.
  destruct
    (StepsPhi_initial_terminal_value_typed
      heap env rho (Mu_App ef1 ea1) stty ctxt rgns
      ty1 static_mu1 phi_mu1 heap_mu1 v1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcMu1 HMu1)
    as (stty_mu1 & HExtMu1 & HTcHeapMu1 & HHeapShapeMu1 &
        _ & _).
  assert (HTcEnvMu1 : TcEnv (stty_mu1, rho, env, ctxt)).
  {
    eapply ext_stores__env; eauto.
  }
  assert (HEnvShapeMu1 : RuntimeEnvShape stty_mu1 rho env ctxt).
  {
    eapply RuntimeEnvShape_store_ext; eauto.
  }
  assert (HCompatEff1 :
    HeterogeneousHeapForExpr env rho (Eff_App ef1 ea1) heap heap).
  {
    apply HeterogeneousHeapForExpr_refl.
  }
  assert (HCompatEff2 :
    HeterogeneousHeapForExpr env rho (Eff_App ef2 ea2) heap heap).
  {
    apply HeterogeneousHeapForExpr_refl.
  }
  assert (HCompatMu1 :
    HeterogeneousHeapForExpr env rho (Mu_App ef1 ea1) heap heap).
  {
    apply HeterogeneousHeapForExpr_refl.
  }
  pose proof
    (HBranchCompat phi_mu1 heap_mu1 v1 HMu1) as HCompatMu2.
  pose proof
    (HRecursive
      heap heap env rho (Eff_App ef1 ea1) eff1
      phi_eff1 heap (Eff theta_eff1)
      phi_sum1 heap theta1
      stty ctxt rgns ty_eff1 static_eff1
      HCompatEff1 HBTEff1 HEff1 HSum1 HReadOnly1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEff1) as HEff1Sound.
  pose proof
    (HRecursive
      heap heap env rho (Eff_App ef2 ea2) eff2
      phi_eff2 heap (Eff theta_eff2)
      phi_sum2 heap theta2
      stty ctxt rgns ty_eff2 static_eff2
      HCompatEff2 HBTEff2 HEff2 HSum2 HReadOnly2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEff2) as HEff2Sound.
  pose proof
    (HRecursive
      heap heap env rho (Mu_App ef1 ea1) eff3
      phi_mu1 heap_mu1 v1
      phi_sum3 heap theta3
      stty ctxt rgns ty1 static_mu1
      HCompatMu1 HBTMu1 HMu1 HSum3 HReadOnly3
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcMu1) as HMu1Sound.
  pose proof
    (HRecursive
      heap_mu1 heap env rho (Mu_App ef2 ea2) eff4
      phi_mu2 heap_mu2 v2
      phi_sum4 heap theta4
      stty_mu1 ctxt rgns ty2 static_mu2
      HCompatMu2 HBTMu2 HMu2 HSum4 HReadOnly4
      HTcHeapMu1 HHeapShapeMu1 HTcRho HTcInc HTcEnvMu1 HEnvShapeMu1
      HTcMu2) as HMu2Sound.
  subst theta12.
  subst theta34.
  subst theta_summary.
  eapply Correctness_soundness_ext_small_step_quad_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_summary_replay_recursive_case :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2,
    StepsPhi
      (initial_state heap env rho
        (Concat (Concat eff1 eff2) (Concat eff3 eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    PairParBranchSummaryReplayCompatible heap env rho ef1 ea1 eff4 ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, static_mu1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, static_mu2) ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_eff1, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_eff2, static_eff2) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, eff3) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, eff4) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessSummaryReplayRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2
    HSummary HPair HBranchSummary HTcHeap HHeapShape HTcRho HTcInc
    HTcEnv HEnvShape HTcMu1 HTcMu2 HTcEff1 HTcEff2
    HReadOnlyStatic1 HReadOnlyStatic2 HBTEff1 HBTEff2 HBTMu1 HBTMu2
    HReadOnlySummary HRecursive.
  unfold SmallStepCorrectnessSummaryReplayRecursivePremise in HRecursive.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho (Concat eff1 eff2) (Concat eff3 eff4)
      phi_summary heap_summary theta_summary HSummary)
    as (phi_sum12 & heap_sum12 & theta12 &
        phi_sum34 & heap_sum34 & theta34 &
        HSum12 & HSum34 & HHeapSummary & HThetaSummary & HTraceSummary).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 eff2
      phi_sum12 heap_sum12 theta12 HSum12)
    as (phi_sum1 & heap_sum1 & theta1 &
        phi_sum2 & heap_sum2 & theta2 &
        HSum1 & HSum2 & HHeap12 & HTheta12 & HTrace12).
  subst heap_sum12.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_sum2 env rho eff3 eff4
      phi_sum34 heap_sum34 theta34 HSum34)
    as (phi_sum3 & heap_sum3 & theta3 &
        phi_sum4 & heap_sum4 & theta4 &
        HSum3 & HSum4 & HHeap34 & HTheta34 & HTrace34).
  subst heap_sum34.
  destruct
    (StepsPhi_pair_par_terminal_decompose
      heap env rho ef1 ea1 ef2 ea2 phi_pair heap_pair v_pair HPair)
    as (phi_eff1 & heap_eff1 & theta_eff1 &
        phi_eff2 & heap_eff2 & theta_eff2 &
        phi_mu1 & heap_mu1 & v1 &
        phi_mu2 & heap_mu2 & v2 &
        HEff1 & HEff2 & HMu1 & HMu2 &
        _ & _ & HTracePair).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_sum12 phi_sum34
      HReadOnlySummary HTraceSummary) as HReadOnly12.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_sum12 phi_sum34
      HReadOnlySummary HTraceSummary) as HReadOnly34.
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_sum12 phi_sum1 phi_sum2
      HReadOnly12 HTrace12) as HReadOnly1.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_sum12 phi_sum1 phi_sum2
      HReadOnly12 HTrace12) as HReadOnly2.
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_sum34 phi_sum3 phi_sum4
      HReadOnly34 HTrace34) as HReadOnly3.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_sum34 phi_sum3 phi_sum4
      HReadOnly34 HTrace34) as HReadOnly4.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho (Eff_App ef1 ea1) stty ctxt rgns
      ty_eff1 static_eff1
      phi_eff1 heap_eff1 (Eff theta_eff1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff1
      HEff1 HReadOnlyStatic1) as HHeapEff1.
  subst heap_eff1.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho (Eff_App ef2 ea2) stty ctxt rgns
      ty_eff2 static_eff2
      phi_eff2 heap_eff2 (Eff theta_eff2)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff2
      HEff2 HReadOnlyStatic2) as HHeapEff2.
  subst heap_eff2.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff1) phi_sum1
      (StDone heap_sum1 (Eff theta1))
      HSum1 HReadOnly1) as HHeapSum1.
  simpl in HHeapSum1.
  subst heap_sum1.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff2) phi_sum2
      (StDone heap_sum2 (Eff theta2))
      HSum2 HReadOnly2) as HHeapSum2.
  simpl in HHeapSum2.
  subst heap_sum2.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff3) phi_sum3
      (StDone heap_sum3 (Eff theta3))
      HSum3 HReadOnly3) as HHeapSum3.
  simpl in HHeapSum3.
  subst heap_sum3.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff4) phi_sum4
      (StDone heap_sum4 (Eff theta4))
      HSum4 HReadOnly4) as HHeapSum4.
  simpl in HHeapSum4.
  symmetry in HHeapSum4.
  rewrite HHeapSum4 in *.
  clear HHeapSum4.
  destruct
    (StepsPhi_initial_terminal_value_typed
      heap env rho (Mu_App ef1 ea1) stty ctxt rgns
      ty1 static_mu1 phi_mu1 heap_mu1 v1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcMu1 HMu1)
    as (stty_mu1 & HExtMu1 & HTcHeapMu1 & HHeapShapeMu1 &
        _ & _).
  assert (HTcEnvMu1 : TcEnv (stty_mu1, rho, env, ctxt)).
  {
    eapply ext_stores__env; eauto.
  }
  assert (HEnvShapeMu1 : RuntimeEnvShape stty_mu1 rho env ctxt).
  {
    eapply RuntimeEnvShape_store_ext; eauto.
  }
  pose proof
    (HBranchSummary phi_mu1 heap_mu1 v1 HMu1) as HSummaryMu2.
  pose proof
    (HRecursive
      heap heap env rho (Eff_App ef1 ea1) eff1
      phi_eff1 heap (Eff theta_eff1)
      phi_sum1 heap theta1
      stty ctxt rgns ty_eff1 static_eff1
      (SummaryReplayCompatibleForExpr_refl env rho eff1 heap)
      HBTEff1 HEff1 HSum1 HReadOnly1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEff1) as HEff1Sound.
  pose proof
    (HRecursive
      heap heap env rho (Eff_App ef2 ea2) eff2
      phi_eff2 heap (Eff theta_eff2)
      phi_sum2 heap theta2
      stty ctxt rgns ty_eff2 static_eff2
      (SummaryReplayCompatibleForExpr_refl env rho eff2 heap)
      HBTEff2 HEff2 HSum2 HReadOnly2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEff2) as HEff2Sound.
  pose proof
    (HRecursive
      heap heap env rho (Mu_App ef1 ea1) eff3
      phi_mu1 heap_mu1 v1
      phi_sum3 heap theta3
      stty ctxt rgns ty1 static_mu1
      (SummaryReplayCompatibleForExpr_refl env rho eff3 heap)
      HBTMu1 HMu1 HSum3 HReadOnly3
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcMu1) as HMu1Sound.
  pose proof
    (HRecursive
      heap_mu1 heap env rho (Mu_App ef2 ea2) eff4
      phi_mu2 heap_mu2 v2
      phi_sum4 heap theta4
      stty_mu1 ctxt rgns ty2 static_mu2
      HSummaryMu2 HBTMu2 HMu2 HSum4 HReadOnly4
      HTcHeapMu1 HHeapShapeMu1 HTcRho HTcInc HTcEnvMu1 HEnvShapeMu1
      HTcMu2) as HMu2Sound.
  subst theta12.
  subst theta34.
  subst theta_summary.
  eapply Correctness_soundness_ext_small_step_quad_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_summary_replay_below_case :
  forall n heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2,
    StepsPhi
      (initial_state heap env rho
        (Concat (Concat eff1 eff2) (Concat eff3 eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhiN n (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    PairParBranchSummaryReplayCompatible heap env rho ef1 ea1 eff4 ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, static_mu1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, static_mu2) ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_eff1, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_eff2, static_eff2) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, eff3) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, eff4) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi_pair ⋞ theta_summary.
Proof.
  intros n heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2
    HSummary HPair HBranchSummary HTcHeap HHeapShape HTcRho HTcInc
    HTcEnv HEnvShape HTcMu1 HTcMu2 HTcEff1 HTcEff2
    HReadOnlyStatic1 HReadOnlyStatic2 HBTEff1 HBTEff2 HBTMu1 HBTMu2
    HReadOnlySummary HBelow.
  unfold SmallStepCorrectnessSummaryReplayRecursivePremiseBelow in HBelow.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho (Concat eff1 eff2) (Concat eff3 eff4)
      phi_summary heap_summary theta_summary HSummary)
    as (phi_sum12 & heap_sum12 & theta12 &
        phi_sum34 & heap_sum34 & theta34 &
        HSum12 & HSum34 & HHeapSummary & HThetaSummary & HTraceSummary).
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap env rho eff1 eff2
      phi_sum12 heap_sum12 theta12 HSum12)
    as (phi_sum1 & heap_sum1 & theta1 &
        phi_sum2 & heap_sum2 & theta2 &
        HSum1 & HSum2 & HHeap12 & HTheta12 & HTrace12).
  subst heap_sum12.
  destruct
    (StepsPhi_concat_effect_terminal_decompose
      heap_sum2 env rho eff3 eff4
      phi_sum34 heap_sum34 theta34 HSum34)
    as (phi_sum3 & heap_sum3 & theta3 &
        phi_sum4 & heap_sum4 & theta4 &
        HSum3 & HSum4 & HHeap34 & HTheta34 & HTrace34).
  subst heap_sum34.
  destruct
    (StepsPhiN_pair_par_terminal_decompose_counts
      n heap env rho ef1 ea1 ef2 ea2 phi_pair heap_pair v_pair HPair)
    as (n_eff1 & phi_eff1 & heap_eff1 & theta_eff1 &
        n_eff2 & phi_eff2 & heap_eff2 & theta_eff2 &
        n_mu1 & phi_mu1 & heap_mu1 & v1 &
        n_mu2 & phi_mu2 & heap_mu2 & v2 &
        HLtEff1 & HLtEff2 & HLtMu1 & HLtMu2 &
        HEff1 & HEff2 & HMu1 & HMu2 &
        _ & _ & HTracePair).
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_summary phi_sum12 phi_sum34
      HReadOnlySummary HTraceSummary) as HReadOnly12.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_summary phi_sum12 phi_sum34
      HReadOnlySummary HTraceSummary) as HReadOnly34.
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_sum12 phi_sum1 phi_sum2
      HReadOnly12 HTrace12) as HReadOnly1.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_sum12 phi_sum1 phi_sum2
      HReadOnly12 HTrace12) as HReadOnly2.
  pose proof
    (ReadOnlyPhi_app_list_left
      phi_sum34 phi_sum3 phi_sum4
      HReadOnly34 HTrace34) as HReadOnly3.
  pose proof
    (ReadOnlyPhi_app_list_right
      phi_sum34 phi_sum3 phi_sum4
      HReadOnly34 HTrace34) as HReadOnly4.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho (Eff_App ef1 ea1) stty ctxt rgns
      ty_eff1 static_eff1
      phi_eff1 heap_eff1 (Eff theta_eff1)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff1
      (StepsPhiN_to_StepsPhi _ _ _ _ HEff1) HReadOnlyStatic1) as HHeapEff1.
  subst heap_eff1.
  pose proof
    (StepsPhi_typed_readonly_static_preserves_heap
      heap env rho (Eff_App ef2 ea2) stty ctxt rgns
      ty_eff2 static_eff2
      phi_eff2 heap_eff2 (Eff theta_eff2)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff2
      (StepsPhiN_to_StepsPhi _ _ _ _ HEff2) HReadOnlyStatic2) as HHeapEff2.
  subst heap_eff2.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff1) phi_sum1
      (StDone heap_sum1 (Eff theta1))
      HSum1 HReadOnly1) as HHeapSum1.
  simpl in HHeapSum1.
  subst heap_sum1.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff2) phi_sum2
      (StDone heap_sum2 (Eff theta2))
      HSum2 HReadOnly2) as HHeapSum2.
  simpl in HHeapSum2.
  subst heap_sum2.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff3) phi_sum3
      (StDone heap_sum3 (Eff theta3))
      HSum3 HReadOnly3) as HHeapSum3.
  simpl in HHeapSum3.
  subst heap_sum3.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho eff4) phi_sum4
      (StDone heap_sum4 (Eff theta4))
      HSum4 HReadOnly4) as HHeapSum4.
  simpl in HHeapSum4.
  symmetry in HHeapSum4.
  rewrite HHeapSum4 in *.
  clear HHeapSum4.
  destruct
    (StepsPhi_initial_terminal_value_typed
      heap env rho (Mu_App ef1 ea1) stty ctxt rgns
      ty1 static_mu1 phi_mu1 heap_mu1 v1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcMu1 (StepsPhiN_to_StepsPhi _ _ _ _ HMu1))
    as (stty_mu1 & HExtMu1 & HTcHeapMu1 & HHeapShapeMu1 &
        _ & _).
  assert (HTcEnvMu1 : TcEnv (stty_mu1, rho, env, ctxt)).
  {
    eapply ext_stores__env; eauto.
  }
  assert (HEnvShapeMu1 : RuntimeEnvShape stty_mu1 rho env ctxt).
  {
    eapply RuntimeEnvShape_store_ext; eauto.
  }
  pose proof
    (HBranchSummary phi_mu1 heap_mu1 v1
      (StepsPhiN_to_StepsPhi _ _ _ _ HMu1)) as HSummaryMu2.
  pose proof
    (HBelow
      n_eff1 heap heap env rho (Eff_App ef1 ea1) eff1
      phi_eff1 heap (Eff theta_eff1)
      phi_sum1 heap theta1
      stty ctxt rgns ty_eff1 static_eff1
      HLtEff1
      (SummaryReplayCompatibleForExpr_refl env rho eff1 heap)
      HBTEff1 HEff1 HSum1 HReadOnly1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEff1) as HEff1Sound.
  pose proof
    (HBelow
      n_eff2 heap heap env rho (Eff_App ef2 ea2) eff2
      phi_eff2 heap (Eff theta_eff2)
      phi_sum2 heap theta2
      stty ctxt rgns ty_eff2 static_eff2
      HLtEff2
      (SummaryReplayCompatibleForExpr_refl env rho eff2 heap)
      HBTEff2 HEff2 HSum2 HReadOnly2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEff2) as HEff2Sound.
  pose proof
    (HBelow
      n_mu1 heap heap env rho (Mu_App ef1 ea1) eff3
      phi_mu1 heap_mu1 v1
      phi_sum3 heap theta3
      stty ctxt rgns ty1 static_mu1
      HLtMu1
      (SummaryReplayCompatibleForExpr_refl env rho eff3 heap)
      HBTMu1 HMu1 HSum3 HReadOnly3
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcMu1) as HMu1Sound.
  pose proof
    (HBelow
      n_mu2 heap_mu1 heap env rho (Mu_App ef2 ea2) eff4
      phi_mu2 heap_mu2 v2
      phi_sum4 heap theta4
      stty_mu1 ctxt rgns ty2 static_mu2
      HLtMu2 HSummaryMu2 HBTMu2 HMu2 HSum4 HReadOnly4
      HTcHeapMu1 HHeapShapeMu1 HTcRho HTcInc HTcEnvMu1 HEnvShapeMu1
      HTcMu2) as HMu2Sound.
  subst theta12.
  subst theta34.
  subst theta_summary.
  eapply Correctness_soundness_ext_small_step_quad_join_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_trace_disjoint_recursive_case :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2,
    StepsPhi
      (initial_state heap env rho
        (Concat (Concat eff1 eff2) (Concat eff3 eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    PairParBranchTraceDisjoint heap env rho ef1 ea1 ef2 ea2 ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, static_mu1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, static_mu2) ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_eff1, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_eff2, static_eff2) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, eff3) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, eff4) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeapCompatibleRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2
    HSummary HPair HTraceDisjoint HTcHeap HHeapShape HTcRho HTcInc
    HTcEnv HEnvShape HTcMu1 HTcMu2 HTcEff1 HTcEff2
    HReadOnlyStatic1 HReadOnlyStatic2 HBTEff1 HBTEff2 HBTMu1 HBTMu2
    HReadOnlySummary HRecursive.
  eapply
    Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_heap_compatible_recursive_case;
    eauto.
  now apply PairParBranchHeapCompatible_from_trace_disjoint.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_eff_app_bt_summary_terminal_pass_heterogeneous_recursive_case :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2
    phi_eff1 phi_eff2 theta1 theta2
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap (Eff theta1)) ->
    StepsPhi (initial_state heap env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap (Eff theta2)) ->
    PairParCheckPass theta1 theta2 ->
    StepsPhi
      (initial_state heap env rho
        (Concat (Concat eff1 eff2)
          (Concat (Eff_App ef1 ea1) (Eff_App ef2 ea2))))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, static_mu1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, static_mu2) ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_eff1, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_eff2, static_eff2) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2
    phi_eff1 phi_eff2 theta1 theta2
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2
    HEff1 HEff2 HPass HSummary HPair
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcMu1 HTcMu2 HTcEff1 HTcEff2 HReadOnlyStatic1 HReadOnlyStatic2
    HBTEff1 HBTEff2 HBTMu1Eff HBTMu2Eff HReadOnlySummary HRecursive.
  pose proof
    (PairParBranchHeapCompatible_from_check_heterogeneous_recursive
      heap env rho ef1 ea1 ef2 ea2 theta1 theta2
      phi_eff1 phi_eff2
      stty ctxt rgns ty1 ty2 static_mu1 static_mu2
      ty_eff1 ty_eff2 static_eff1 static_eff2
      HPass HEff1 HEff2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcMu1 HTcMu2 HTcEff1 HTcEff2
      HReadOnlyStatic1 HReadOnlyStatic2
      HBTMu1Eff HBTMu2Eff HRecursive) as HBranchCompat.
  pose proof
    (SmallStepCorrectnessHeterogeneous_implies_heap_compatible HRecursive)
    as HHeapRecursive.
  eapply
    (Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_heap_compatible_recursive_case
      heap env rho ef1 ea1 ef2 ea2
      eff1 eff2 (Eff_App ef1 ea1) (Eff_App ef2 ea2)
      phi_summary heap_summary theta_summary
      phi_pair heap_pair v_pair
      stty ctxt rgns ty1 ty2 static_mu1 static_mu2
      ty_eff1 ty_eff2 static_eff1 static_eff2);
    eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_eff_app_bt_summary_terminal_checked_or_fallback_heterogeneous_recursive_case :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2,
    StepsPhi
      (initial_state heap env rho
        (Concat (Concat eff1 eff2)
          (Concat (Eff_App ef1 ea1) (Eff_App ef2 ea2))))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, static_mu1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, static_mu2) ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_eff1, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_eff2, static_eff2) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    (exists phi_eff1 theta1 phi_eff2 theta2,
      StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
        (StDone heap (Eff theta1)) /\
      StepsPhi (initial_state heap env rho (Eff_App ef2 ea2)) phi_eff2
        (StDone heap (Eff theta2)) /\
      PairParCheckFail theta1 theta2) \/
    phi_pair ⋞ theta_summary.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2
    HSummary HPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcMu1 HTcMu2 HTcEff1 HTcEff2 HReadOnlyStatic1 HReadOnlyStatic2
    HBTEff1 HBTEff2 HBTMu1Eff HBTMu2Eff HReadOnlySummary HRecursive.
  destruct
    (StepsPhi_pair_par_terminal_decompose_checked_heap_compatible_or_fallback
      heap env rho ef1 ea1 ef2 ea2
      phi_pair heap_pair v_pair
      stty ctxt rgns ty1 ty2 static_mu1 static_mu2
      ty_eff1 ty_eff2 static_eff1 static_eff2
      HPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcMu1 HTcMu2 HTcEff1 HTcEff2
      HReadOnlyStatic1 HReadOnlyStatic2
      HBTMu1Eff HBTMu2Eff HRecursive)
    as (phi_eff1 & theta1 &
        phi_eff2 & theta2 &
        phi_mu1 & heap_mu1 & v1 &
        phi_mu2 & heap_mu2 & v2 &
        HEff1 & HEff2 & HMu1 & HMu2 &
        HCheckOrCompat & _ & _ & _).
  destruct HCheckOrCompat as [HFail | HBranchCompat].
  - left.
    exists phi_eff1, theta1, phi_eff2, theta2.
    repeat split; assumption.
  - right.
    pose proof
      (SmallStepCorrectnessHeterogeneous_implies_heap_compatible HRecursive)
      as HHeapRecursive.
    eapply
      (Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_heap_compatible_recursive_case
        heap env rho ef1 ea1 ef2 ea2
        eff1 eff2 (Eff_App ef1 ea1) (Eff_App ef2 ea2)
        phi_summary heap_summary theta_summary
        phi_pair heap_pair v_pair
        stty ctxt rgns ty1 ty2 static_mu1 static_mu2
        ty_eff1 ty_eff2 static_eff1 static_eff2);
      eauto.
Qed.

Lemma PairParBackTriangle_canonical_eff_app_summary :
  forall ctxt rgns rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (Eff_App ef1 ea1 ⊕ Eff_App ef2 ea2)).
Proof.
  intros ctxt rgns rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    ty_pair static_pair HBack HTcPair.
  inversion HBack; subst; try discriminate.
  inversion HTcPair; subst.
  match goal with
  | HTcMu1 : TcExp (ctxt, rgns, Mu_App ef1 ea1, _, _),
    HTcMu2 : TcExp (ctxt, rgns, Mu_App ef2 ea2, _, _),
    HTcEff1 : TcExp
      (ctxt, rgns, Eff_App ef1 ea1, ?ty_e, ?static_ee_1),
    HReadOnly1 : ReadOnlyStatic (fold_subst_eps rho ?static_ee_1),
    HTcEff2 : TcExp
      (ctxt, rgns, Eff_App ef2 ea2, ?ty_e, ?static_ee_2),
    HReadOnly2 : ReadOnlyStatic (fold_subst_eps rho ?static_ee_2),
    HBTEff1 : BackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1),
    HBTEff2 : BackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2)
      |- _ =>
      assert (HBTMu1Eff :
        BackTriangle
          (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1))
        by (inversion HTcMu1; subst; eauto);
      assert (HBTMu2Eff :
        BackTriangle
          (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2))
        by (inversion HTcMu2; subst; eauto);
      eapply
        (BT_Pair_Par ctxt rgns rho ef1 ea1 ef2 ea2
          eff1 eff2 (Eff_App ef1 ea1) (Eff_App ef2 ea2)
          ty_e static_ee_1 static_ee_2);
      eauto
  end.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_eff_app_backtriangle_checked_or_fallback_heterogeneous_recursive_case :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (Eff_App ef1 ea1 ⊕ Eff_App ef2 ea2)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (Eff_App ef1 ea1 ⊕ Eff_App ef2 ea2)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    (exists phi_eff1 theta1 phi_eff2 theta2,
      StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
        (StDone heap (Eff theta1)) /\
      StepsPhi (initial_state heap env rho (Eff_App ef2 ea2)) phi_eff2
        (StDone heap (Eff theta2)) /\
      PairParCheckFail theta1 theta2) \/
    phi_pair ⋞ theta_summary.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair
    HBack HSummary HPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcPair HReadOnlySummary HRecursive.
  inversion HBack; subst; try discriminate.
  inversion HTcPair; subst.
  match goal with
  | HTcMu1 : TcExp
      (ctxt, rgns, Mu_App ef1 ea1, ?ty_mu1, ?static_mu1),
    HTcMu2 : TcExp
      (ctxt, rgns, Mu_App ef2 ea2, ?ty_mu2, ?static_mu2),
    HTcEff1 : TcExp
      (ctxt, rgns, Eff_App ef1 ea1, ?ty_eff1, ?static_eff1),
    HTcEff2 : TcExp
      (ctxt, rgns, Eff_App ef2 ea2, ?ty_eff2, ?static_eff2),
    HReadOnly1 : ReadOnlyStatic (fold_subst_eps rho ?static_eff1),
    HReadOnly2 : ReadOnlyStatic (fold_subst_eps rho ?static_eff2),
    HBTEff1 : BackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1),
    HBTEff2 : BackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2),
    HBTMu1Eff : BackTriangle
      (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1),
    HBTMu2Eff : BackTriangle
      (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) |- _ =>
      eapply
        (Correctness_soundness_ext_small_step_pair_par_eff_app_bt_summary_terminal_checked_or_fallback_heterogeneous_recursive_case
          heap env rho ef1 ea1 ef2 ea2 eff1 eff2
          phi_summary heap_summary theta_summary
          phi_pair heap_pair v_pair
          stty ctxt rgns ty_mu1 ty_mu2 static_mu1 static_mu2
          ty_eff1 ty_eff2 static_eff1 static_eff2);
      eauto
  end.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_canonical_eff_app_backtriangle_checked_or_fallback_heterogeneous_recursive_case :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (Eff_App ef1 ea1 ⊕ Eff_App ef2 ea2)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    (exists phi_eff1 theta1 phi_eff2 theta2,
      StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
        (StDone heap (Eff theta1)) /\
      StepsPhi (initial_state heap env rho (Eff_App ef2 ea2)) phi_eff2
        (StDone heap (Eff theta2)) /\
      PairParCheckFail theta1 theta2) \/
    phi_pair ⋞ theta_summary.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair
    HBack HSummary HPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcPair HReadOnlySummary HRecursive.
  pose proof
    (PairParBackTriangle_canonical_eff_app_summary
      ctxt rgns rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
      ty_pair static_pair HBack HTcPair) as HBackCanonical.
  eapply
    (Correctness_soundness_ext_small_step_pair_par_eff_app_backtriangle_checked_or_fallback_heterogeneous_recursive_case
      heap env rho ef1 ea1 ef2 ea2 eff1 eff2
      phi_summary heap_summary theta_summary
      phi_pair heap_pair v_pair
      stty ctxt rgns ty_pair static_pair);
    eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_backtriangle_heterogeneous_recursive_case :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair
    HBack HSummary HPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcPair HReadOnlySummary HRecursive.
  inversion HBack; subst; try discriminate.
  inversion HTcPair; subst.
  match goal with
  | HTcMu1 : TcExp
      (ctxt, rgns, Mu_App ef1 ea1, ?ty_mu1, ?static_mu1),
    HTcMu2 : TcExp
      (ctxt, rgns, Mu_App ef2 ea2, ?ty_mu2, ?static_mu2),
    HTcEff1 : TcExp
      (ctxt, rgns, Eff_App ef1 ea1, ?ty_eff1, ?static_eff1),
    HTcEff2 : TcExp
      (ctxt, rgns, Eff_App ef2 ea2, ?ty_eff2, ?static_eff2),
    HReadOnly1 : ReadOnlyStatic (fold_subst_eps rho ?static_eff1),
    HReadOnly2 : ReadOnlyStatic (fold_subst_eps rho ?static_eff2) |- _ =>
      eapply
        (Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_heterogeneous_recursive_case
          heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
          phi_summary heap_summary theta_summary
          phi_pair heap_pair v_pair
          stty ctxt rgns ty_mu1 ty_mu2 static_mu1 static_mu2
          ty_eff1 ty_eff2 static_eff1 static_eff2);
      eauto
  end.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_canonical_eff_app_backtriangle_heterogeneous_recursive_case :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (Eff_App ef1 ea1 ⊕ Eff_App ef2 ea2)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair
    HBack HSummary HPair HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcPair HReadOnlySummary HRecursive.
  pose proof
    (PairParBackTriangle_canonical_eff_app_summary
      ctxt rgns rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
      ty_pair static_pair HBack HTcPair) as HBackCanonical.
  eapply
    (Correctness_soundness_ext_small_step_pair_par_backtriangle_heterogeneous_recursive_case
      heap env rho ef1 ea1 ef2 ea2
      eff1 eff2 (Eff_App ef1 ea1) (Eff_App ef2 ea2)
      phi_summary heap_summary theta_summary
      phi_pair heap_pair v_pair
      stty ctxt rgns ty_pair static_pair);
    eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_backtriangle_heap_compatible_recursive_case :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    PairParBranchHeapCompatible heap env rho ef1 ea1 ef2 ea2 ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeapCompatibleRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair
    HBack HSummary HPair HBranchCompat HTcHeap HHeapShape HTcRho HTcInc
    HTcEnv HEnvShape HTcPair HReadOnlySummary HRecursive.
  inversion HBack; subst; try discriminate.
  inversion HTcPair; subst.
  match goal with
  | HTcMu1 : TcExp
      (ctxt, rgns, Mu_App ef1 ea1, ?ty_mu1, ?static_mu1),
    HTcMu2 : TcExp
      (ctxt, rgns, Mu_App ef2 ea2, ?ty_mu2, ?static_mu2),
    HTcEff1 : TcExp
      (ctxt, rgns, Eff_App ef1 ea1, ?ty_eff1, ?static_eff1),
    HTcEff2 : TcExp
      (ctxt, rgns, Eff_App ef2 ea2, ?ty_eff2, ?static_eff2),
    HReadOnly1 : ReadOnlyStatic (fold_subst_eps rho ?static_eff1),
    HReadOnly2 : ReadOnlyStatic (fold_subst_eps rho ?static_eff2) |- _ =>
      eapply
        (Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_heap_compatible_recursive_case
          heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
          phi_summary heap_summary theta_summary
          phi_pair heap_pair v_pair
          stty ctxt rgns ty_mu1 ty_mu2 static_mu1 static_mu2
          ty_eff1 ty_eff2 static_eff1 static_eff2);
      eauto
  end.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_backtriangle_summary_replay_recursive_case :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    PairParBranchSummaryReplayCompatible heap env rho ef1 ea1 eff4 ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessSummaryReplayRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair
    HBack HSummary HPair HBranchSummary HTcHeap HHeapShape HTcRho HTcInc
    HTcEnv HEnvShape HTcPair HReadOnlySummary HRecursive.
  inversion HBack; subst; try discriminate.
  inversion HTcPair; subst.
  match goal with
  | HTcMu1 : TcExp
      (ctxt, rgns, Mu_App ef1 ea1, ?ty_mu1, ?static_mu1),
    HTcMu2 : TcExp
      (ctxt, rgns, Mu_App ef2 ea2, ?ty_mu2, ?static_mu2),
    HTcEff1 : TcExp
      (ctxt, rgns, Eff_App ef1 ea1, ?ty_eff1, ?static_eff1),
    HTcEff2 : TcExp
      (ctxt, rgns, Eff_App ef2 ea2, ?ty_eff2, ?static_eff2),
    HReadOnly1 : ReadOnlyStatic (fold_subst_eps rho ?static_eff1),
    HReadOnly2 : ReadOnlyStatic (fold_subst_eps rho ?static_eff2) |- _ =>
      eapply
        (Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_summary_replay_recursive_case
          heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
          phi_summary heap_summary theta_summary
          phi_pair heap_pair v_pair
          stty ctxt rgns ty_mu1 ty_mu2 static_mu1 static_mu2
          ty_eff1 ty_eff2 static_eff1 static_eff2);
      eauto
  end.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_backtriangle_summary_replay_below_case :
  forall n heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhiN n (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    PairParBranchSummaryReplayCompatible heap env rho ef1 ea1 eff4 ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi_pair ⋞ theta_summary.
Proof.
  intros n heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair
    HBack HSummary HPair HBranchSummary HTcHeap HHeapShape HTcRho HTcInc
    HTcEnv HEnvShape HTcPair HReadOnlySummary HBelow.
  inversion HBack; subst; try discriminate.
  inversion HTcPair; subst.
  match goal with
  | HTcMu1 : TcExp
      (ctxt, rgns, Mu_App ef1 ea1, ?ty_mu1, ?static_mu1),
    HTcMu2 : TcExp
      (ctxt, rgns, Mu_App ef2 ea2, ?ty_mu2, ?static_mu2),
    HTcEff1 : TcExp
      (ctxt, rgns, Eff_App ef1 ea1, ?ty_eff1, ?static_eff1),
    HTcEff2 : TcExp
      (ctxt, rgns, Eff_App ef2 ea2, ?ty_eff2, ?static_eff2),
    HReadOnly1 : ReadOnlyStatic (fold_subst_eps rho ?static_eff1),
    HReadOnly2 : ReadOnlyStatic (fold_subst_eps rho ?static_eff2) |- _ =>
      eapply
        (Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_summary_replay_below_case
          n heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
          phi_summary heap_summary theta_summary
          phi_pair heap_pair v_pair
          stty ctxt rgns ty_mu1 ty_mu2 static_mu1 static_mu2
          ty_eff1 ty_eff2 static_eff1 static_eff2);
      eauto
  end.
Qed.

Theorem Correctness_soundness_ext_small_step_pair_par_backtriangle_trace_disjoint_recursive_case :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    PairParBranchTraceDisjoint heap env rho ef1 ea1 ef2 ea2 ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeapCompatibleRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair
    HBack HSummary HPair HTraceDisjoint HTcHeap HHeapShape HTcRho HTcInc
    HTcEnv HEnvShape HTcPair HReadOnlySummary HRecursive.
  inversion HBack; subst; try discriminate.
  inversion HTcPair; subst.
  match goal with
  | HTcMu1 : TcExp
      (ctxt, rgns, Mu_App ef1 ea1, ?ty_mu1, ?static_mu1),
    HTcMu2 : TcExp
      (ctxt, rgns, Mu_App ef2 ea2, ?ty_mu2, ?static_mu2),
    HTcEff1 : TcExp
      (ctxt, rgns, Eff_App ef1 ea1, ?ty_eff1, ?static_eff1),
    HTcEff2 : TcExp
      (ctxt, rgns, Eff_App ef2 ea2, ?ty_eff2, ?static_eff2),
    HReadOnly1 : ReadOnlyStatic (fold_subst_eps rho ?static_eff1),
    HReadOnly2 : ReadOnlyStatic (fold_subst_eps rho ?static_eff2) |- _ =>
      eapply
        (Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_trace_disjoint_recursive_case
          heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
          phi_summary heap_summary theta_summary
          phi_pair heap_pair v_pair
          stty ctxt rgns ty_mu1 ty_mu2 static_mu1 static_mu2
          ty_eff1 ty_eff2 static_eff1 static_eff2);
      eauto
  end.
Qed.

Theorem Correctness_soundness_ext_small_step_backtriangle_terminal_summary_replay_below_case :
  forall n heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhiN n (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    PairParBranchSummaryReplayCompatibleRecursivePremise ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi ⋞ theta_summary.
Proof.
  intros n heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HBack HStepsN HSummary HReadOnlySummary
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp
    HPairBranch HBelow.
  pose proof (StepsPhiN_to_StepsPhi _ _ _ _ HStepsN) as HSteps.
  inversion HBack; subst;
    try solve [eauto using
      Correctness_soundness_ext_small_step_num_case,
      Correctness_soundness_ext_small_step_bool_case,
      Correctness_soundness_ext_small_step_var_typed_case,
      Correctness_soundness_ext_small_step_mu_abs_case,
      Correctness_soundness_ext_small_step_rgn_abs_case,
      Correctness_soundness_ext_small_step_top_summary_case,
      Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_summary_replay_below_case,
      Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_summary_replay_below_case,
      Correctness_soundness_ext_small_step_deref_conc_summary_terminal_summary_replay_below_case,
      Correctness_soundness_ext_small_step_cond_summary_terminal_summary_replay_below_case,
      Correctness_soundness_ext_small_step_plus_summary_terminal_summary_replay_below_case,
      Correctness_soundness_ext_small_step_minus_summary_terminal_summary_replay_below_case,
      Correctness_soundness_ext_small_step_times_summary_terminal_summary_replay_below_case,
      Correctness_soundness_ext_small_step_eq_summary_terminal_summary_replay_below_case,
      Correctness_soundness_ext_small_step_mu_app_summary_terminal_bt_app_conc_summary_replay_below_case,
      Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_bt_summary_replay_below_case,
      Correctness_soundness_ext_small_step_pair_par_backtriangle_summary_replay_below_case].
  all:
    lazymatch goal with
    | HStepsMu : StepsPhiN ?n0
        (initial_state ?heap0 ?env0 ?rho0 (Mu_App ?ef ?ea))
        ?phi0 (StDone ?heap_done ?v_done),
      HSummaryMu : StepsPhi
        (initial_state ?heap0 ?env0 ?rho0 (Eff_App ?ef ?ea))
        ?phi_summary0 (StDone ?heap_summary0 (Eff ?theta_summary0)) |- _ =>
        eapply
          Correctness_soundness_ext_small_step_mu_app_summary_terminal_bt_app_conc_summary_replay_below_case;
        eauto
    | HStepsPair : StepsPhiN ?n0
        (initial_state ?heap0 ?env0 ?rho0 (Pair_Par ?ef1 ?ea1 ?ef2 ?ea2))
        ?phi0 (StDone ?heap_done ?v_done) |- _ =>
        unfold PairParBranchSummaryReplayCompatibleRecursivePremise in HPairBranch;
        eapply
          Correctness_soundness_ext_small_step_pair_par_backtriangle_summary_replay_below_case;
        eauto
    | HStepsAssign : StepsPhiN ?n0
        (initial_state ?heap0 ?env0 ?rho0
          (Assign (Rgn_Const true false ?r) ?e1 ?e2))
        ?phi0 (StDone ?heap_done ?v_done) |- _ =>
        inversion HTcExp; subst;
        eapply
          (Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_summary_replay_below_case
            n heap env rho e1 e2 eff1 eff2 r
            phi_summary heap_summary theta_summary
            phi heap' v
            stty ctxt rgns ty_e1 static_e1 _ _);
        eauto
    | HStepsAssign : StepsPhiN ?n0
        (initial_state ?heap0 ?env0 ?rho0 (Assign ?w ?e1 ?e2))
        ?phi0 (StDone ?heap_done ?v_done),
      HSummaryAssign : StepsPhi
        (initial_state ?heap0 ?env0 ?rho0 (Concat ?eff1 (Concat ?eff2 (WriteAbs ?w))))
        ?phi_summary0 (StDone ?heap_summary0 (Eff ?theta_summary0)) |- _ =>
        inversion HTcExp; subst;
        eapply
          (Correctness_soundness_ext_small_step_assign_abs_bt_summary_terminal_summary_replay_below_case
            n heap env rho _ _ _ _ _
            phi_summary heap_summary theta_summary
            phi heap' v
            stty ctxt rgns ty_e1 static_e1 _ _);
        eauto
    end.
Qed.

Theorem Correctness_soundness_ext_small_step_backtriangle_sequential_head_recursive_case :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    SequentialHead ea ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    SmallStepCorrectnessRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
  intros heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HBack HSeq HSteps HSummary HReadOnlySummary
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp
    HRecursive.
  inversion HBack; subst; simpl in HSeq; try contradiction;
    eauto using
      Correctness_soundness_ext_small_step_num_case,
      Correctness_soundness_ext_small_step_bool_case,
      Correctness_soundness_ext_small_step_var_typed_case,
      Correctness_soundness_ext_small_step_mu_abs_case,
      Correctness_soundness_ext_small_step_rgn_abs_case,
      Correctness_soundness_ext_small_step_top_summary_case,
      Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_recursive_case,
      Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_recursive_case,
      Correctness_soundness_ext_small_step_deref_conc_summary_terminal_recursive_case,
      Correctness_soundness_ext_small_step_assign_abs_bt_summary_terminal_recursive_case,
      Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_recursive_case,
      Correctness_soundness_ext_small_step_cond_summary_terminal_recursive_case,
      Correctness_soundness_ext_small_step_plus_summary_terminal_recursive_case,
      Correctness_soundness_ext_small_step_minus_summary_terminal_recursive_case,
      Correctness_soundness_ext_small_step_times_summary_terminal_recursive_case,
      Correctness_soundness_ext_small_step_eq_summary_terminal_recursive_case,
      Correctness_soundness_ext_small_step_mu_app_summary_terminal_bt_app_conc_recursive_case,
      Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_bt_recursive_case.
Qed.

Theorem Correctness_soundness_ext_small_step_backtriangle_sequential_head_lookup_equivalent_recursive_case :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    SequentialHead ea ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    SmallStepCorrectnessLookupEquivalentRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
  intros heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HBack HSeq HSteps HSummary HReadOnlySummary
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp
    HRecursive.
  eapply
    Correctness_soundness_ext_small_step_backtriangle_sequential_head_recursive_case;
    eauto.
  now apply SmallStepCorrectnessLookupEquivalent_same_heap_recursive.
Qed.

Theorem Correctness_soundness_ext_small_step_backtriangle_terminal_heterogeneous_recursive_case :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_backtriangle_terminal_counted_recursive_case.
Qed.

Theorem Correctness_soundness_ext_small_step_runtime_backtriangle_terminal_checked_or_fallback_heterogeneous_recursive_case :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    RuntimeBackTriangleSummary ctxt rgns rho ea ee ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    PairParCanonicalFallback heap env rho ea \/ phi ⋞ theta_summary.
Proof.
  intros heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HRuntime HSteps HSummary HReadOnlySummary
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp
    HRecursive.
  destruct HRuntime as
    [ctxt_rt rgns_rt rho_rt ea_rt ee_rt HSeq HBack
    |ctxt_rt rgns_rt rho_rt ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4 HBack
    |ctxt_rt rgns_rt rho_rt e_top];
    subst.
  - right.
    assert (HRecursiveSame : SmallStepCorrectnessRecursivePremise).
    {
      unfold SmallStepCorrectnessRecursivePremise.
      intros heap_rec env_rec rho_rec ea_rec ee_rec phi_rec heap_rec' v_rec
        phi_summary_rec heap_summary_rec theta_summary_rec
        stty_rec ctxt_rec rgns_rec ty_rec static_rec
        HBackRec HStepsRec HSummaryRec HReadOnlySummaryRec
        HTcHeapRec HHeapShapeRec HTcRhoRec HTcIncRec HTcEnvRec
        HEnvShapeRec HTcExpRec.
      unfold SmallStepCorrectnessHeterogeneousRecursivePremise in HRecursive.
      eapply (HRecursive
        heap_rec heap_rec env_rec rho_rec ea_rec ee_rec
        phi_rec heap_rec' v_rec
        phi_summary_rec heap_summary_rec theta_summary_rec
        stty_rec ctxt_rec rgns_rec ty_rec static_rec); eauto.
    }
    eapply
      Correctness_soundness_ext_small_step_backtriangle_sequential_head_recursive_case;
      eauto.
  - destruct
      (Correctness_soundness_ext_small_step_pair_par_canonical_eff_app_backtriangle_checked_or_fallback_heterogeneous_recursive_case
        heap env rho_rt ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
        phi_summary heap_summary theta_summary
        phi heap' v
        stty ctxt_rt rgns_rt ty static
        HBack HSummary HSteps
        HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
        HTcExp HReadOnlySummary HRecursive)
      as [HFallback | HSound].
    + left.
      destruct HFallback as
        (phi_eff1 & theta1 & phi_eff2 & theta2 &
         HEff1 & HEff2 & HFail).
      unfold PairParCanonicalFallback.
      exists ef1, ea1, ef2, ea2, phi_eff1, theta1, phi_eff2, theta2.
      repeat split; eauto.
    + right.
      exact HSound.
  - right.
    eapply Correctness_soundness_ext_small_step_top_summary_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_runtime_backtriangle_terminal_heterogeneous_recursive_case :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    RuntimeBackTriangleSummary ctxt rgns rho ea ee ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
  intros heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HRuntime HSteps HSummary HReadOnlySummary
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp
    HRecursive.
  destruct HRuntime as
    [ctxt_rt rgns_rt rho_rt ea_rt ee_rt HSeq HBack
    |ctxt_rt rgns_rt rho_rt ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4 HBack
    |ctxt_rt rgns_rt rho_rt e_top];
    subst.
  - assert (HRecursiveSame : SmallStepCorrectnessRecursivePremise).
    {
      unfold SmallStepCorrectnessRecursivePremise.
      intros heap_rec env_rec rho_rec ea_rec ee_rec phi_rec heap_rec' v_rec
        phi_summary_rec heap_summary_rec theta_summary_rec
        stty_rec ctxt_rec rgns_rec ty_rec static_rec
        HBackRec HStepsRec HSummaryRec HReadOnlySummaryRec
        HTcHeapRec HHeapShapeRec HTcRhoRec HTcIncRec HTcEnvRec
        HEnvShapeRec HTcExpRec.
      unfold SmallStepCorrectnessHeterogeneousRecursivePremise in HRecursive.
      eapply (HRecursive
        heap_rec heap_rec env_rec rho_rec ea_rec ee_rec
        phi_rec heap_rec' v_rec
        phi_summary_rec heap_summary_rec theta_summary_rec
        stty_rec ctxt_rec rgns_rec ty_rec static_rec); eauto.
    }
    eapply
      Correctness_soundness_ext_small_step_backtriangle_sequential_head_recursive_case;
      eauto.
  - eapply
      (Correctness_soundness_ext_small_step_pair_par_canonical_eff_app_backtriangle_heterogeneous_recursive_case
        heap env rho_rt ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
        phi_summary heap_summary theta_summary
        phi heap' v
        stty ctxt_rt rgns_rt ty static);
      eauto.
  - eapply Correctness_soundness_ext_small_step_top_summary_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_backtriangle_terminal_heap_compatible_recursive_case :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    PairParBranchHeapCompatibleRecursivePremise ->
    SmallStepCorrectnessHeapCompatibleRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
  intros heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HBack HSteps HSummary HReadOnlySummary
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp
    HPairBranch HRecursive.
  assert (HRecursiveSame : SmallStepCorrectnessRecursivePremise).
  {
    eapply SmallStepCorrectnessHeapCompatible_same_heap_recursive; eauto.
  }
  destruct ea; try solve
    [ eapply
        Correctness_soundness_ext_small_step_backtriangle_sequential_head_recursive_case;
      eauto; simpl; exact I ].
  inversion HBack; subst; try discriminate.
  - unfold PairParBranchHeapCompatibleRecursivePremise in HPairBranch.
    eapply
      Correctness_soundness_ext_small_step_pair_par_backtriangle_heap_compatible_recursive_case;
      eauto.
  - eapply Correctness_soundness_ext_small_step_top_summary_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_backtriangle_terminal_heap_equivalent_recursive_case :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    PairParBranchHeapEquivalentRecursivePremise ->
    SmallStepCorrectnessHeapEquivalentRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_backtriangle_terminal_heap_compatible_recursive_case.
Qed.

Theorem Correctness_soundness_ext_small_step_backtriangle_terminal_summary_replay_recursive_case :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    PairParBranchSummaryReplayCompatibleRecursivePremise ->
    SmallStepCorrectnessSummaryReplayRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
  intros heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HBack HSteps HSummary HReadOnlySummary
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp
    HPairBranch HRecursive.
  assert (HRecursiveSame : SmallStepCorrectnessRecursivePremise).
  {
    eapply SmallStepCorrectnessSummaryReplay_same_heap_recursive; eauto.
  }
  destruct ea; try solve
    [ eapply
        Correctness_soundness_ext_small_step_backtriangle_sequential_head_recursive_case;
      eauto; simpl; exact I ].
  inversion HBack; subst; try discriminate.
  - unfold PairParBranchSummaryReplayCompatibleRecursivePremise in HPairBranch.
    eapply
      Correctness_soundness_ext_small_step_pair_par_backtriangle_summary_replay_recursive_case;
      eauto.
  - eapply Correctness_soundness_ext_small_step_top_summary_case; eauto.
Qed.

Theorem Correctness_soundness_ext_small_step_backtriangle_terminal_summary_replay_case :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    PairParBranchSummaryReplayCompatibleRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
  intros heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HBack HSteps HSummary HReadOnlySummary
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp
    HPairBranch.
  destruct (StepsPhi_to_StepsPhiN _ _ _ HSteps) as (n & HStepsN).
  revert heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HBack HSteps HStepsN HSummary HReadOnlySummary
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp
    HPairBranch.
  induction n using Wf_nat.lt_wf_ind.
  intros heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HBack HSteps HStepsN HSummary HReadOnlySummary
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp
    HPairBranch.
  eapply
    (Correctness_soundness_ext_small_step_backtriangle_terminal_summary_replay_below_case
      n heap env rho ea ee phi heap' v
      phi_summary heap_summary theta_summary
      stty ctxt rgns ty static); eauto.
  unfold SmallStepCorrectnessSummaryReplayRecursivePremiseBelow.
  intros n_child heap_child heap_summary_start env_child rho_child
    ea_child ee_child phi_child heap_child' v_child
    phi_summary_child heap_summary_child theta_summary_child
    stty_child ctxt_child rgns_child ty_child static_child
    HLt HCompat HBackChild HStepsChild HSummaryChild
    HReadOnlySummaryChild HTcHeapChild HHeapShapeChild HTcRhoChild
    HTcIncChild HTcEnvChild HEnvShapeChild HTcExpChild.
  destruct
    (HCompat
      phi_summary_child heap_summary_child (Eff theta_summary_child)
      HSummaryChild HReadOnlySummaryChild)
    as (_ & HSummaryReplay).
  eapply H; eauto.
  exact (StepsPhiN_to_StepsPhi _ _ _ _ HStepsChild).
Qed.

Theorem Correctness_soundness_ext_small_step_backtriangle_terminal_trace_disjoint_recursive_case :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    PairParBranchTraceDisjointRecursivePremise ->
    SmallStepCorrectnessHeapCompatibleRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
  intros heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static
    HBack HSteps HSummary HReadOnlySummary
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp
    HTraceDisjoint HRecursive.
  eapply
    Correctness_soundness_ext_small_step_backtriangle_terminal_heap_compatible_recursive_case;
    eauto.
  now apply PairParBranchTraceDisjoint_implies_heap_compatible.
Qed.
