From Stdlib Require Import Lia.
From Stdlib Require Import List.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Core.Values.
Require Import theories.SmallStep.Determinism.Terminal.
Require Import theories.SmallStep.Runtime.Continuation.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Runtime.Trace.
Require Import theories.SmallStep.Soundness.BackTriangle.
Require Import theories.SmallStep.Soundness.Correctness.
Require Import theories.SmallStep.Typing.Judgments.
Require Import theories.SmallStep.Typing.Regularity.
Require Import theories.SmallStep.Typing.Types.

Import ListNotations.

Definition PairParCheckedRejectSource (state : State) : Prop :=
  exists heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k,
    state =
      StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k) /\
    summary_disjointb theta1 theta2 = false.

Definition PairParRunSource (state : State) : Prop :=
  match state with
  | StPairParRun _ _ _ _ _ => True
  | _ => False
  end.

Inductive CheckedStep : State -> Label -> State -> Prop :=
| CheckedStepRuntime :
    forall state label state',
      Step state label state' ->
      ~ PairParCheckedRejectSource state ->
      ~ PairParRunSource state ->
      CheckedStep state label state'
(* The checked proof relation records the same failed precheck as rejection;
   this is intentionally separate from the raw fallback transition. *)
| CheckedStepPairParReject :
    forall heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k,
      summary_disjointb theta1 theta2 = false ->
      CheckedStep
        (StReturn heap (VSummary theta2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
        LSilent
        (StError heap)
| CheckedStepPairParRunLeft :
    forall left_state right_state phi_left phi_right k label left_state',
      CheckedStep left_state label left_state' ->
      CheckedStep
        (StPairParRun left_state right_state phi_left phi_right k)
        label
        (StPairParRun
          left_state'
          (with_state_heap (state_heap left_state') right_state)
          (phi_left ++ label_trace label)
          phi_right
          k)
| CheckedStepPairParRunRight :
    forall heap v1 right_state phi_left phi_right k label right_state',
      CheckedStep right_state label right_state' ->
      CheckedStep
        (StPairParRun (StDone heap v1) right_state phi_left phi_right k)
        label
        (StPairParRun
          (with_state_heap (state_heap right_state') (StDone heap v1))
          right_state'
          phi_left
          (phi_right ++ label_trace label)
          k)
| CheckedStepPairParRunLeftError :
    forall heap right_state phi_left phi_right k,
      CheckedStep
        (StPairParRun (StError heap) right_state phi_left phi_right k)
        LSilent
        (StError heap)
| CheckedStepPairParRunRightError :
    forall heap_left v1 heap_right phi_left phi_right k,
      CheckedStep
        (StPairParRun
          (StDone heap_left v1)
          (StError heap_right)
          phi_left
          phi_right
          k)
        LSilent
        (StError heap_right)
| CheckedStepPairParRunDonePass :
    forall heap v1 v2 phi_left phi_right k,
      trace_disjointb phi_left phi_right = true ->
      CheckedStep
        (StPairParRun
          (StDone heap v1)
          (StDone heap v2)
          phi_left
          phi_right
          k)
        LSilent
        (StReturn heap (VPair v1 v2) k)
| CheckedStepPairParRunDoneFail :
    forall heap v1 v2 phi_left phi_right k,
      trace_disjointb phi_left phi_right = false ->
      CheckedStep
        (StPairParRun
          (StDone heap v1)
          (StDone heap v2)
          phi_left
          phi_right
          k)
        LSilent
        (StError heap).

Inductive CheckedSteps : State -> Trace -> State -> Prop :=
| CheckedStepsRefl :
    forall state,
      CheckedSteps state [] state
| CheckedStepsStep :
    forall state label state' phi state'',
      CheckedStep state label state' ->
      CheckedSteps state' phi state'' ->
      CheckedSteps state (label_trace label ++ phi) state''.

Inductive CheckedStepsN : nat -> State -> Trace -> State -> Prop :=
| CheckedStepsNRefl :
    forall state,
      CheckedStepsN 0 state [] state
| CheckedStepsNStep :
    forall n state label state' phi state'',
      CheckedStep state label state' ->
      CheckedStepsN n state' phi state'' ->
      CheckedStepsN (S n) state (label_trace label ++ phi) state''.

Inductive StateHasError : State -> Prop :=
| SHE_Error :
    forall heap,
      StateHasError (StError heap)
| SHE_PairParLeft :
    forall left_state right_state phi_left phi_right k,
      StateHasError left_state ->
      StateHasError
        (StPairParRun left_state right_state phi_left phi_right k)
| SHE_PairParRight :
    forall left_state right_state phi_left phi_right k,
      StateHasError right_state ->
      StateHasError
        (StPairParRun left_state right_state phi_left phi_right k).

Definition CheckedComputationEvaluation
    (heap : Heap) (env : Env) (rho : Rho)
    (expr : Expr) (phi : Trace) (heap' : Heap) (v : Val) : Prop :=
  CheckedSteps
    (InitialState heap env rho expr)
    phi
    (StDone heap' v).

Definition CheckedCountedComputationEvaluation
    (n : nat) (heap : Heap) (env : Env) (rho : Rho)
    (expr : Expr) (phi : Trace) (heap' : Heap) (v : Val) : Prop :=
  CheckedStepsN n
    (InitialState heap env rho expr)
    phi
    (StDone heap' v).

Definition CheckedExecutionStoreContextSmallStepCorrectnessBelow
    (n : nat) : Prop :=
  forall n_child gamma omega heap env rho expr summary_expr
    phi heap' v phi_summary heap_summary theta,
    n_child < n ->
    CheckedBackTriangle gamma omega expr summary_expr ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedCountedComputationEvaluation n_child heap env rho
      expr phi heap' v ->
    SummaryEvaluation heap env rho summary_expr
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.

Definition CheckedExecutionStoreSummaryValueSoundnessBelow
    (n : nat) : Prop :=
  forall n_child gamma omega heap env rho expr summary_expr eff
    phi heap_summary theta,
    n_child < n ->
    CheckedBackTriangle gamma omega expr summary_expr ->
    CheckedTcExp gamma omega summary_expr TyEffect eff ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedCountedComputationEvaluation n_child heap env rho
      summary_expr phi heap_summary (VSummary theta) ->
    TraceCoveredBySummary phi theta.

Definition CheckedExecutionStoreContextTerminalCorrectnessGoal : Prop :=
  forall gamma omega heap env rho expr summary_expr phi heap' v
    phi_summary heap_summary theta,
    CheckedBackTriangle gamma omega expr summary_expr ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationEvaluation heap env rho expr phi heap' v ->
    SummaryEvaluation heap env rho summary_expr
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.

Lemma CheckedStep_done_absurd :
  forall heap v label state,
    ~ CheckedStep (StDone heap v) label state.
Proof.
  intros heap v label state HStep.
  inversion HStep; subst; try discriminate; inversion H.
Qed.

Lemma CheckedStep_error_absurd :
  forall heap label state,
    ~ CheckedStep (StError heap) label state.
Proof.
  intros heap label state HStep.
  inversion HStep; subst; try discriminate; inversion H.
Qed.

Lemma CheckedStepsN_error_no_done :
  forall n heap_error phi heap v,
    ~ CheckedStepsN n (StError heap_error) phi (StDone heap v).
Proof.
  induction n as [| n IH]; intros heap_error phi heap v HSteps.
  - inversion HSteps; subst; discriminate.
  - inversion HSteps; subst.
    eapply CheckedStep_error_absurd; eauto.
Qed.

Lemma StateHasError_with_state_heap :
  forall heap state,
    StateHasError state ->
    StateHasError (with_state_heap heap state).
Proof.
  intros heap state HErr.
  induction HErr; simpl.
  - constructor.
  - eapply SHE_PairParLeft. exact IHHErr.
  - eapply SHE_PairParRight. exact IHHErr.
Qed.

Lemma StateHasError_not_done :
  forall state heap v,
    StateHasError state ->
    state <> StDone heap v.
Proof.
  intros state heap v HErr HDone.
  inversion HErr; subst; discriminate.
Qed.

Lemma CheckedStep_state_has_error_preserved :
  forall state label state',
    CheckedStep state label state' ->
    StateHasError state ->
    StateHasError state'.
Proof.
  intros state label state' HStep.
  induction HStep; intros HErr.
  - inversion HErr; subst.
    + match goal with
      | HRaw : Step (StError _) _ _ |- _ => inversion HRaw
      end.
    + exfalso.
      match goal with
      | HNotRun : ~ PairParRunSource (StPairParRun _ _ _ _ _) |- _ =>
          apply HNotRun; simpl; exact I
      end.
    + exfalso.
      match goal with
      | HNotRun : ~ PairParRunSource (StPairParRun _ _ _ _ _) |- _ =>
          apply HNotRun; simpl; exact I
      end.
  - constructor.
  - inversion HErr; subst.
    + eapply SHE_PairParLeft. eapply IHHStep. eassumption.
    + eapply SHE_PairParRight.
      eapply StateHasError_with_state_heap. eassumption.
  - inversion HErr; subst.
    + match goal with
      | HDoneError : StateHasError (StDone _ _) |- _ =>
          inversion HDoneError
      end.
    + eapply SHE_PairParRight. eapply IHHStep. eassumption.
  - constructor.
  - constructor.
  - inversion HErr; subst;
      match goal with
      | HDoneError : StateHasError (StDone _ _) |- _ =>
          inversion HDoneError
      end.
  - constructor.
Qed.

Lemma CheckedStepsN_state_has_error_no_done :
  forall n state phi heap v,
    StateHasError state ->
    ~ CheckedStepsN n state phi (StDone heap v).
Proof.
  induction n as [| n IH]; intros state phi heap v HErr HSteps.
  - inversion HSteps; subst.
    eapply StateHasError_not_done; eauto.
  - inversion HSteps; subst.
    eapply IH.
    + eapply CheckedStep_state_has_error_preserved; eauto.
    + eauto.
Qed.

Theorem CheckedStep_deterministic :
  forall state label1 state1 label2 state2,
    CheckedStep state label1 state1 ->
    CheckedStep state label2 state2 ->
    label1 = label2 /\ state1 = state2.
Proof.
  intros state label1 state1 label2 state2 HStep1.
  revert label2 state2.
  induction HStep1 as
    [state label state' HRaw HNotFail HNotRun
    | heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k HFail
    | left_state right_state phi_left phi_right k label left_state'
        HLeft IHLeft
    | heap v1 right_state phi_left phi_right k label right_state'
        HRight IHRight
    | heap right_state phi_left phi_right k
    | heap_left v1 heap_right phi_left phi_right k
    | heap v1 v2 phi_left phi_right k HTracePass
    | heap v1 v2 phi_left phi_right k HTraceFail];
    intros label2 state2 HStep2;
    inversion HStep2; subst; clear HStep2;
    try solve
      [ eapply Step_deterministic; eauto
      | split; reflexivity
      | exfalso;
        match goal with
        | HNot : ~ PairParRunSource (StPairParRun _ _ _ _ _) |- _ =>
            apply HNot; simpl; exact I
        end
      | exfalso;
        match goal with
        | HDone : CheckedStep (StDone _ _) _ _ |- _ =>
            eapply CheckedStep_done_absurd; exact HDone
        end
      | exfalso;
        match goal with
        | HError : CheckedStep (StError _) _ _ |- _ =>
            eapply CheckedStep_error_absurd; exact HError
        end
      | exfalso;
        match goal with
        | HPass : ?check = true,
          HFail : ?check = false |- _ =>
            rewrite HPass in HFail; discriminate
        end
      | exfalso;
        match goal with
        | HFail : ?check = false,
          HPass : ?check = true |- _ =>
            rewrite HFail in HPass; discriminate
        end
      | exfalso;
        match goal with
        | HNot : ~ PairParCheckedRejectSource
            (StReturn ?heap (VSummary ?theta2)
              (KPairParEff2 ?ef1 ?ea1 ?ef2 ?ea2 ?env ?rho ?theta1 ?k)),
          HFail : summary_disjointb ?theta1 ?theta2 = false |- _ =>
            apply HNot;
            unfold PairParCheckedRejectSource;
            exists heap, theta1, theta2, ef1, ea1, ef2, ea2,
              env, rho, k;
            split; [reflexivity | exact HFail]
        end ].
  all:
    match goal with
    | IH : forall label2 state2,
        CheckedStep ?source label2 state2 ->
        ?label = label2 /\ ?target = state2,
      HBranch : CheckedStep ?source ?label_other ?target_other
        |- ?label = ?label_other /\ _ =>
        destruct (IH label_other target_other HBranch)
          as (HLabel & HState);
        subst label_other target_other;
        split; reflexivity
    end.
Qed.

Lemma CheckedStep_raw_or_error :
  forall state label state',
    CheckedStep state label state' ->
    Step state label state' \/ StateHasError state'.
Proof.
  intros state label state' HStep.
  induction HStep.
  - left.
    match goal with
    | HRaw : Step _ _ _ |- _ => exact HRaw
    end.
  - right. constructor.
  - destruct IHHStep as [HRawBranch | HErrBranch].
    + left. eapply StepPairParRunLeft. exact HRawBranch.
    + right. eapply SHE_PairParLeft. exact HErrBranch.
  - destruct IHHStep as [HRawBranch | HErrBranch].
    + left. eapply StepPairParRunRight. exact HRawBranch.
    + right. eapply SHE_PairParRight. exact HErrBranch.
  - left. apply StepPairParRunLeftError.
  - left. apply StepPairParRunRightError.
  - left. eapply StepPairParRunDonePass. eassumption.
  - left. eapply StepPairParRunDoneFail. eassumption.
Qed.

Lemma CheckedStepsN_known_first_step_terminal_inv :
  forall n state label state' phi heap_final v_final,
    CheckedStep state label state' ->
    CheckedStepsN n state phi (StDone heap_final v_final) ->
    exists n_tail phi_tail,
      n = S n_tail /\
      CheckedStepsN n_tail state' phi_tail
        (StDone heap_final v_final) /\
      phi = label_trace label ++ phi_tail.
Proof.
  intros n state label state' phi heap_final v_final HStep HSteps.
  inversion HSteps; subst.
  - exfalso.
    eapply CheckedStep_done_absurd; eauto.
  - destruct
      (CheckedStep_deterministic
        state label state' label0 state'0 HStep H)
      as (HLabel & HState).
    subst label0 state'0.
    exists n0, phi0.
    repeat split; reflexivity || assumption.
Qed.

Lemma CheckedStepsN_to_StepsN_done :
  forall n state phi heap v,
    CheckedStepsN n state phi (StDone heap v) ->
    StepsN n state phi (StDone heap v).
Proof.
  induction n as [| n IH]; intros state phi heap v HSteps.
  - inversion HSteps; subst.
    constructor.
  - inversion HSteps; subst.
    match goal with
    | HStep : CheckedStep state label state' |- _ =>
        destruct
          (CheckedStep_raw_or_error state label state' HStep)
          as [HRaw | HErr]
    end.
    + eapply StepsNStep.
      * exact HRaw.
      * eapply IH.
        match goal with
        | HTail : CheckedStepsN n state' _ (StDone heap v) |- _ =>
            exact HTail
        end.
    + exfalso.
      eapply CheckedStepsN_state_has_error_no_done; eauto.
Qed.

Lemma CheckedStepsN_to_CheckedSteps :
  forall n state phi state',
    CheckedStepsN n state phi state' ->
    CheckedSteps state phi state'.
Proof.
  intros n state phi state' HSteps.
  induction HSteps.
  - constructor.
  - eapply CheckedStepsStep; eauto.
Qed.

Lemma CheckedSteps_to_CheckedStepsN :
  forall state phi state',
    CheckedSteps state phi state' ->
    exists n,
      CheckedStepsN n state phi state'.
Proof.
  intros state phi state' HSteps.
  induction HSteps as
    [state0
    | state0 label state1 phi0 state2 HStep _HTail
        (n_tail & HTailN)].
  - exists 0. constructor.
  - exists (S n_tail).
    eapply CheckedStepsNStep; eauto.
Qed.

Lemma CheckedComputationEvaluation_to_counted :
  forall heap env rho expr phi heap' v,
    CheckedComputationEvaluation heap env rho expr phi heap' v ->
    exists n,
      CheckedCountedComputationEvaluation n heap env rho
        expr phi heap' v.
Proof.
  intros heap env rho expr phi heap' v HComp.
  unfold CheckedComputationEvaluation,
    CheckedCountedComputationEvaluation in *.
  eapply CheckedSteps_to_CheckedStepsN.
  exact HComp.
Qed.

Lemma PairParCheckedRejectSource_append :
  forall state tail,
    PairParCheckedRejectSource state ->
    PairParCheckedRejectSource (state_append_kont state tail).
Proof.
  intros state tail HFail.
  destruct HFail as
    (heap & theta1 & theta2 & ef1 & ea1 & ef2 & ea2 &
      env & rho & k & HState & HCheck).
  subst state.
  unfold PairParCheckedRejectSource.
  exists heap, theta1, theta2, ef1, ea1, ef2, ea2,
    env, rho, (kont_append k tail).
  split; [reflexivity | exact HCheck].
Qed.

Lemma PairParRunSource_append :
  forall state tail,
    PairParRunSource state ->
    PairParRunSource (state_append_kont state tail).
Proof.
  intros state tail HRun.
  destruct state; simpl in *; try contradiction; exact I.
Qed.

Lemma CheckedStep_append_kont_inv_active :
  forall state tail label appended_state',
    append_active_state state ->
    CheckedStep (state_append_kont state tail) label appended_state' ->
    exists state',
      CheckedStep state label state' /\
      appended_state' = state_append_kont state' tail.
Proof.
  intros state tail label appended_state' HActive HStep.
  inversion HStep; subst; clear HStep.
  - destruct
      (Step_append_kont_inv_active
        state tail label appended_state' HActive H)
      as (state' & HRaw & HState').
    exists state'.
    split; [| exact HState'].
    eapply CheckedStepRuntime.
    + exact HRaw.
    + intros HFail.
      apply H0.
      eapply PairParCheckedRejectSource_append; exact HFail.
    + intros HRun.
      match goal with
      | HNotRun : ~ PairParRunSource (state_append_kont state tail) |- _ =>
          apply HNotRun
      end.
      eapply PairParRunSource_append; exact HRun.
  - destruct state as
      [heap0 env0 rho0 e0 k0
      | heap0 v0 k0
      | heap0 v0
      | left_state right_state phi_left phi_right k0
      | heap0];
      simpl in *; try contradiction; try discriminate.
	    destruct k0; simpl in *; try discriminate.
	    + contradiction.
	    + match goal with
	      | HEq : StReturn _ _ _ = StReturn _ _ _ |- _ =>
	          inversion HEq; subst; clear HEq
	      end.
	      exists (StError heap0).
	      split.
	      * eapply CheckedStepPairParReject.
	        match goal with
	        | HFail : summary_disjointb _ _ = false |- _ =>
	            exact HFail
	        end.
	      * reflexivity.
  - destruct state as
      [heap0 env0 rho0 e0 k0
      | heap0 v0 k0
      | heap0 v0
      | left_state0 right_state0 phi_left0 phi_right0 k0
      | heap0];
      simpl in *; try contradiction; try discriminate.
    match goal with
    | HEq : StPairParRun _ _ _ _ _ = StPairParRun _ _ _ _ _ |- _ =>
        inversion HEq; subst; clear HEq
    end.
    eexists.
    split.
    + eapply CheckedStepPairParRunLeft; eauto.
    + reflexivity.
  - destruct state as
      [heap0 env0 rho0 e0 k0
      | heap0 v0 k0
      | heap0 v0
      | left_state0 right_state0 phi_left0 phi_right0 k0
      | heap0];
      simpl in *; try contradiction; try discriminate.
    match goal with
    | HEq : StPairParRun _ _ _ _ _ = StPairParRun _ _ _ _ _ |- _ =>
        inversion HEq; subst; clear HEq
    end.
    eexists.
    split.
    + eapply CheckedStepPairParRunRight; eauto.
    + reflexivity.
  - destruct state as
      [heap0 env0 rho0 e0 k0
      | heap0 v0 k0
      | heap0 v0
      | left_state0 right_state0 phi_left0 phi_right0 k0
      | heap0];
      simpl in *; try contradiction; try discriminate.
    match goal with
    | HEq : StPairParRun _ _ _ _ _ = StPairParRun _ _ _ _ _ |- _ =>
        inversion HEq; subst; clear HEq
    end.
    exists (StError heap).
    split; [apply CheckedStepPairParRunLeftError | reflexivity].
  - destruct state as
      [heap0 env0 rho0 e0 k0
      | heap0 v0 k0
      | heap0 v0
      | left_state0 right_state0 phi_left0 phi_right0 k0
      | heap0];
      simpl in *; try contradiction; try discriminate.
    match goal with
    | HEq : StPairParRun _ _ _ _ _ = StPairParRun _ _ _ _ _ |- _ =>
        inversion HEq; subst; clear HEq
    end.
    exists (StError heap_right).
    split; [apply CheckedStepPairParRunRightError | reflexivity].
  - destruct state as
      [heap0 env0 rho0 e0 k0
      | heap0 v0 k0
      | heap0 v0
      | left_state0 right_state0 phi_left0 phi_right0 k0
      | heap0];
      simpl in *; try contradiction; try discriminate.
    match goal with
    | HEq : StPairParRun _ _ _ _ _ = StPairParRun _ _ _ _ _ |- _ =>
        inversion HEq; subst; clear HEq
    end.
    eexists.
    split.
    + eapply CheckedStepPairParRunDonePass; eauto.
    + reflexivity.
  - destruct state as
      [heap0 env0 rho0 e0 k0
      | heap0 v0 k0
      | heap0 v0
      | left_state0 right_state0 phi_left0 phi_right0 k0
      | heap0];
      simpl in *; try contradiction; try discriminate.
    match goal with
    | HEq : StPairParRun _ _ _ _ _ = StPairParRun _ _ _ _ _ |- _ =>
        inversion HEq; subst; clear HEq
    end.
    exists (StError heap).
    split.
    + eapply CheckedStepPairParRunDoneFail; eauto.
    + reflexivity.
Qed.

Lemma CheckedStepsN_append_kont_terminal_split_counted :
  forall n appended_start phi heap_final v_final,
    CheckedStepsN n appended_start phi (StDone heap_final v_final) ->
    forall state tail,
      appended_start = state_append_kont state tail ->
      (forall heap v, state <> StDone heap v) ->
      exists n_expr n_tail phi_expr heap_mid v_mid phi_tail,
        CheckedStepsN n_expr state phi_expr (StDone heap_mid v_mid) /\
        CheckedStepsN n_tail
          (StReturn heap_mid v_mid tail)
          phi_tail
          (StDone heap_final v_final) /\
        S n = n_expr + n_tail /\
        phi = phi_expr ++ phi_tail.
Proof.
  intros n appended_start phi heap_final v_final HRun.
  remember (StDone heap_final v_final) as final_state eqn:HFinal.
  revert heap_final v_final HFinal.
  induction HRun as
    [state0
    | n state0 label state1 phi0 state2 HStep HTail IH];
    intros heap_final v_final HFinal state tail HAppend HNotDone.
  - subst state0.
    destruct state as
      [heap env rho e k | heap v k | heap v
      | left_state right_state phi_left phi_right k | heap];
      simpl in HAppend; try discriminate.
  - subst state2.
    specialize (IH heap_final v_final eq_refl).
    destruct state as
      [heap env rho e k | heap v k | heap v
      | left_state right_state phi_left phi_right k | heap];
      simpl in HAppend; subst state0.
    + destruct
        (CheckedStep_append_kont_inv_active
          (StEval heap env rho e k) tail label state1
          I HStep)
        as (state1_unappended & HStepUnappended & HState1).
      assert
        (HNotDone1 :
          forall heap0 v0,
            state1_unappended <> StDone heap0 v0).
      { intros heap0 v0 HDone.
        subst state1_unappended.
        inversion HStepUnappended; subst; try discriminate;
          inversion H. }
      destruct
        (IH state1_unappended tail HState1 HNotDone1)
        as (n_expr & n_tail & phi_expr & heap_mid & v_mid & phi_tail &
          HExpr & HTailRun & HCount & HTrace).
      exists (S n_expr), n_tail, (label_trace label ++ phi_expr),
        heap_mid, v_mid, phi_tail.
      split.
      * eapply CheckedStepsNStep; eauto.
      * split; [assumption |].
        split; [lia |].
        rewrite HTrace.
        apply app_assoc.
    + destruct k eqn:Hk.
      { exists 1, (S n), [], heap, v, (label_trace label ++ phi0).
        split.
        - change ([] : Trace) with (label_trace LSilent ++ ([] : Trace)).
          eapply CheckedStepsNStep.
          + eapply CheckedStepRuntime.
            * apply StepReturnDone.
            * intros HFail. inversion HFail as
                (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & HState & _).
              discriminate.
            * intros HRun. exact HRun.
          + constructor.
        - split.
          + eapply CheckedStepsNStep; eauto.
          + split; [lia | reflexivity]. }
      all:
          assert (HActiveReturn : append_active_state (StReturn heap v k))
            by (rewrite Hk; simpl; exact I);
          subst k;
          match goal with
          | HStepCurrent :
              CheckedStep
                (StReturn ?heap0 ?v0 (kont_append ?k_active ?tail0))
                ?label0 ?state10 |- _ =>
              destruct
                (CheckedStep_append_kont_inv_active
                  (StReturn heap0 v0 k_active) tail0 label0 state10
                  HActiveReturn HStepCurrent)
                as (state1_unappended & HStepUnappended & HState1);
              assert
                (HNotDone1 :
                  forall heap_done v_done,
                    state1_unappended <> StDone heap_done v_done)
                by
                  (intros heap_done v_done HDone;
                   subst state1_unappended;
                   inversion HStepUnappended; subst; try discriminate;
                     inversion H);
              destruct
                (IH state1_unappended tail0 HState1 HNotDone1)
                as (n_expr & n_tail & phi_expr & heap_mid & v_mid &
                  phi_tail & HExpr & HTailRun & HCount & HTrace);
              exists (S n_expr), n_tail,
                (label_trace label0 ++ phi_expr), heap_mid, v_mid,
                phi_tail;
              split;
              [ eapply CheckedStepsNStep; eauto
              | split; [assumption |];
                split; [lia |];
                rewrite HTrace;
                apply app_assoc ]
          end.
    + exfalso. eapply HNotDone. reflexivity.
    + destruct
        (CheckedStep_append_kont_inv_active
          (StPairParRun left_state right_state phi_left phi_right k)
          tail label state1
          I HStep)
        as (state1_unappended & HStepUnappended & HState1).
      assert
        (HNotDone1 :
          forall heap0 v0,
            state1_unappended <> StDone heap0 v0).
      { intros heap0 v0 HDone.
        subst state1_unappended.
        inversion HStepUnappended; subst; try discriminate;
          inversion H. }
      destruct
        (IH state1_unappended tail HState1 HNotDone1)
        as (n_expr & n_tail & phi_expr & heap_mid & v_mid & phi_tail &
          HExpr & HTailRun & HCount & HTrace).
      exists (S n_expr), n_tail, (label_trace label ++ phi_expr),
        heap_mid, v_mid, phi_tail.
      split.
      * eapply CheckedStepsNStep; eauto.
      * split; [assumption |].
        split; [lia |].
        rewrite HTrace.
        apply app_assoc.
    + inversion HStep; subst; try discriminate; inversion H.
Qed.
