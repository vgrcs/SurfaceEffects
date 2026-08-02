From Stdlib Require Import Lia.
From Stdlib Require Import List.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Core.Values.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Runtime.Trace.

Import ListNotations.

Ltac solve_nstep_constructor :=
  match goal with
  | |- Step (StEval _ _ _ (EConst _) _) _ _ => apply StepConst
  | |- Step (StEval _ _ _ (EBool _) _) _ _ => apply StepBool
  | |- Step (StEval _ _ _ (EVar _) _) _ _ => eapply StepVar
  | |- Step (StEval _ _ _ (EMu _ _ _ _) _) _ _ => apply StepMu
  | |- Step (StEval _ _ _ (ELambdaRgn _ _) _) _ _ =>
      apply StepLambdaRgn
  | |- Step (StEval _ _ _ (EMuApp _ _) _) _ _ => apply StepMuApp
  | |- Step (StEval _ _ _ (ERgnApp _ _) _) _ _ => apply StepRgnApp
  | |- Step (StEval _ _ _ (EEffApp _ _) _) _ _ => apply StepEffApp
  | |- Step (StEval _ _ _ (EPairPar _ _) _) _ _ => apply StepPairPar
  | |- Step (StEval _ _ _ (ECond _ _ _) _) _ _ => apply StepCond
  | |- Step (StEval _ _ _ (ERef _ _) _) _ _ => eapply StepRef
  | |- Step (StEval _ _ _ (EDeref _ _) _) _ _ => apply StepDeref
  | |- Step (StEval _ _ _ (EAssign _ _ _) _) _ _ => apply StepAssign
  | |- Step (StEval _ _ _ (EPlus _ _) _) _ _ => apply StepPlus
  | |- Step (StEval _ _ _ (EMinus _ _) _) _ _ => apply StepMinus
  | |- Step (StEval _ _ _ (ETimes _ _) _) _ _ => apply StepTimes
  | |- Step (StEval _ _ _ (EEq _ _) _) _ _ => apply StepEq
  | |- Step (StEval _ _ _ (EAllocAbs _) _) _ _ => eapply StepAllocAbs
  | |- Step (StEval _ _ _ (EReadAbs _) _) _ _ => eapply StepReadAbs
  | |- Step (StEval _ _ _ (EWriteAbs _) _) _ _ => eapply StepWriteAbs
  | |- Step (StEval _ _ _ (EReadConc _) _) _ _ => apply StepReadConc
  | |- Step (StEval _ _ _ (EWriteConc _) _) _ _ => apply StepWriteConc
  | |- Step (StEval _ _ _ (EConcat _ _) _) _ _ => apply StepConcat
  | |- Step (StEval _ _ _ ETop _) _ _ => apply StepTop
  | |- Step (StEval _ _ _ EEmpty _) _ _ => apply StepEmpty
  | |- Step (StReturn _ (VClosure _ _ _ _ _ _)
        (KMuAppFun _ _ _ _)) _ _ =>
      apply StepMuAppFun
  | |- Step (StReturn _ _
        (KMuAppArg _ _ _ _ _ _ _)) _ _ =>
      apply StepMuAppArg
  | |- Step (StReturn _ (VClosure _ _ _ _ _ _)
        (KEffAppFun _ _ _ _)) _ _ =>
      apply StepEffAppFun
  | |- Step (StReturn _ _
        (KEffAppArg _ _ _ _ _ _ _)) _ _ =>
      apply StepEffAppArg
  | |- Step (StReturn _ (VSummary _)
        (KPairParEff1 _ _ _ _ _ _ _)) _ _ =>
      apply StepPairParEff1
  | HCheck : summary_disjointb _ _ = false
      |- Step (StReturn _ (VSummary _)
        (KPairParEff2 _ _ _ _ _ _ _ _)) _ _ =>
      eapply StepPairParCheckFallback; exact HCheck
  | HCheck : summary_disjointb _ _ = true
      |- Step (StReturn _ (VSummary _)
        (KPairParEff2 _ _ _ _ _ _ _ _)) _ _ =>
      eapply StepPairParCheckPass; exact HCheck
  | |- Step (StReturn _ (VSummary _)
        (KPairParEff2 _ _ _ _ _ _ _ _)) _ (StPairParRun _ _ _ _ _) =>
      eapply StepPairParCheckPass
  | |- Step (StReturn _ (VSummary _)
        (KPairParEff2 _ _ _ _ _ _ _ _)) _ (StEval _ _ _ _ _) =>
      eapply StepPairParCheckFallback
  | |- Step (StReturn _ _
        (KPairParFallbackLeft _ _ _ _ _)) _ _ =>
      apply StepPairParFallbackLeftReturn
  | |- Step (StReturn _ _
        (KPairParFallbackRight _ _)) _ _ =>
      apply StepPairParFallbackRightReturn
  | |- Step (StPairParRun (StError _) _ _ _ _) _ _ =>
      apply StepPairParRunLeftError
  | |- Step (StPairParRun (StDone _ _) (StError _) _ _ _) _ _ =>
      apply StepPairParRunRightError
  | |- Step (StPairParRun (StDone _ _) _ _ _ _) _ (StPairParRun _ _ _ _ _) =>
      eapply StepPairParRunRight
  | HCheck : trace_disjointb _ _ = true
      |- Step (StPairParRun (StDone _ _) (StDone _ _) _ _ _) _ _ =>
      eapply StepPairParRunDonePass; exact HCheck
  | HCheck : trace_disjointb _ _ = false
      |- Step (StPairParRun (StDone _ _) (StDone _ _) _ _ _) _ _ =>
      eapply StepPairParRunDoneFail; exact HCheck
  | |- Step (StPairParRun _ _ _ _ _) _ (StPairParRun _ _ _ _ _) =>
      econstructor
  | |- Step (StReturn _ (VRegionClosure _ _ _ _)
        (KRgnApp _ _ _)) _ _ =>
      eapply StepRgnAppReturn
  | |- Step (StReturn _ (VBool true)
        (KCond _ _ _ _ _)) _ _ =>
      apply StepCondTrue
  | |- Step (StReturn _ (VBool false)
        (KCond _ _ _ _ _)) _ _ =>
      apply StepCondFalse
  | |- Step (StReturn _ _ (KRef _ _)) _ _ =>
      eapply StepRefReturn
  | |- Step (StReturn _ (VLoc _ _) (KDeref _ _)) _ _ =>
      eapply StepDerefReturn
  | |- Step (StReturn _ (VLoc _ _) (KAssignLoc _ _ _ _ _)) _ _ =>
      apply StepAssignLoc
  | |- Step (StReturn _ _ (KAssignVal _ (VLoc _ _) _)) _ _ =>
      apply StepAssignVal
  | |- Step (StReturn _ (VNat _) (KPlusL _ _ _ _)) _ _ =>
      apply StepPlusL
  | |- Step (StReturn _ (VNat _) (KPlusR _ _)) _ _ =>
      apply StepPlusR
  | |- Step (StReturn _ (VNat _) (KMinusL _ _ _ _)) _ _ =>
      apply StepMinusL
  | |- Step (StReturn _ (VNat _) (KMinusR _ _)) _ _ =>
      apply StepMinusR
  | |- Step (StReturn _ (VNat _) (KTimesL _ _ _ _)) _ _ =>
      apply StepTimesL
  | |- Step (StReturn _ (VNat _) (KTimesR _ _)) _ _ =>
      apply StepTimesR
  | |- Step (StReturn _ (VNat _) (KEqL _ _ _ _)) _ _ =>
      apply StepEqL
  | |- Step (StReturn _ (VNat _) (KEqR _ _)) _ _ =>
      apply StepEqR
  | |- Step (StReturn _ (VLoc _ _) (KReadConc _)) _ _ =>
      apply StepReadConcReturn
  | |- Step (StReturn _ (VLoc _ _) (KWriteConc _)) _ _ =>
      apply StepWriteConcReturn
  | |- Step (StReturn _ (VSummary _) (KConcatL _ _ _ _)) _ _ =>
      apply StepConcatL
  | |- Step (StReturn _ (VSummary _) (KConcatR _ _)) _ _ =>
      apply StepConcatR
  | |- Step (StReturn _ _ KDone) _ _ => apply StepReturnDone
  | |- Step _ _ _ => econstructor
  end; eauto.

Fixpoint kont_append (k tail : Kont) : Kont :=
  match k with
  | KDone => tail
  | KMuAppFun ea env rho k' =>
      KMuAppFun ea env rho (kont_append k' tail)
  | KMuAppArg closure_env closure_rho f x ec ee k' =>
      KMuAppArg closure_env closure_rho f x ec ee
        (kont_append k' tail)
  | KEffAppFun ea env rho k' =>
      KEffAppFun ea env rho (kont_append k' tail)
  | KEffAppArg closure_env closure_rho f x ec ee k' =>
      KEffAppArg closure_env closure_rho f x ec ee
        (kont_append k' tail)
  | KPairParEff1 ef1 ea1 ef2 ea2 env rho k' =>
      KPairParEff1 ef1 ea1 ef2 ea2 env rho (kont_append k' tail)
  | KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k' =>
      KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1
        (kont_append k' tail)
  | KPairParFallbackLeft ef2 ea2 env rho k' =>
      KPairParFallbackLeft ef2 ea2 env rho (kont_append k' tail)
  | KPairParFallbackRight v_left k' =>
      KPairParFallbackRight v_left (kont_append k' tail)
  | KRgnApp r rho k' =>
      KRgnApp r rho (kont_append k' tail)
  | KCond et ef env rho k' =>
      KCond et ef env rho (kont_append k' tail)
  | KRef r k' =>
      KRef r (kont_append k' tail)
  | KDeref r k' =>
      KDeref r (kont_append k' tail)
  | KAssignLoc r ev env rho k' =>
      KAssignLoc r ev env rho (kont_append k' tail)
  | KAssignVal r loc k' =>
      KAssignVal r loc (kont_append k' tail)
  | KPlusL e2 env rho k' =>
      KPlusL e2 env rho (kont_append k' tail)
  | KPlusR n k' =>
      KPlusR n (kont_append k' tail)
  | KMinusL e2 env rho k' =>
      KMinusL e2 env rho (kont_append k' tail)
  | KMinusR n k' =>
      KMinusR n (kont_append k' tail)
  | KTimesL e2 env rho k' =>
      KTimesL e2 env rho (kont_append k' tail)
  | KTimesR n k' =>
      KTimesR n (kont_append k' tail)
  | KEqL e2 env rho k' =>
      KEqL e2 env rho (kont_append k' tail)
  | KEqR n k' =>
      KEqR n (kont_append k' tail)
  | KReadConc k' =>
      KReadConc (kont_append k' tail)
  | KWriteConc k' =>
      KWriteConc (kont_append k' tail)
  | KConcatL e2 env rho k' =>
      KConcatL e2 env rho (kont_append k' tail)
  | KConcatR theta k' =>
      KConcatR theta (kont_append k' tail)
  end.

Definition state_append_kont (state : State) (tail : Kont) : State :=
  match state with
  | StEval heap env rho e k =>
      StEval heap env rho e (kont_append k tail)
  | StReturn heap v k =>
      StReturn heap v (kont_append k tail)
  | StDone heap v =>
      StReturn heap v tail
  | StPairParRun left_state right_state phi_left phi_right k =>
      StPairParRun left_state right_state phi_left phi_right
        (kont_append k tail)
  | StError heap =>
      StError heap
  end.

Definition append_active_state (state : State) : Prop :=
  match state with
  | StDone _ _ => False
  | StPairParRun _ _ _ _ _ => True
  | StError _ => False
  | StReturn _ _ KDone => False
  | _ => True
  end.

Lemma Step_append_kont_not_done :
  forall state label state' tail,
    Step state label state' ->
    (forall heap v, state <> StReturn heap v KDone) ->
    Step
      (state_append_kont state tail)
      label
      (state_append_kont state' tail).
Proof.
  intros state label state' tail HStep HNotDone.
  inversion HStep; subst; simpl; try solve [econstructor; eauto].
  exfalso. eapply HNotDone. reflexivity.
Qed.

Lemma Steps_append_kont :
  forall state phi state' tail,
    Steps state phi state' ->
    Steps
      (state_append_kont state tail)
      phi
      (state_append_kont state' tail).
Proof.
  intros state phi state' tail HSteps.
  induction HSteps as
    [state | state label state1 phi state2 HStep HTail IH].
  - constructor.
  - inversion HStep; subst;
      try solve
        [ eapply StepsStep;
          [ simpl; econstructor; eauto
          | exact IH ] ].
    destruct
        (Steps_done_inv heap v phi state2 HTail)
        as (HTrace & HState).
    subst phi state2.
    simpl. constructor.
Qed.

Lemma Steps_return_done :
  forall heap v,
    Steps (StReturn heap v KDone) [] (StDone heap v).
Proof.
  intros heap v.
  change ([] : Trace) with (label_trace LSilent ++ ([] : Trace)).
  eapply StepsStep.
  - constructor.
  - constructor.
Qed.

Lemma StepsN_return_done :
  forall heap v,
    StepsN 1 (StReturn heap v KDone) [] (StDone heap v).
Proof.
  intros heap v.
  change ([] : Trace) with (label_trace LSilent ++ ([] : Trace)).
  eapply StepsNStep.
  - constructor.
  - constructor.
Qed.

Lemma Steps_return_done_inv :
  forall heap v phi heap_final v_final,
    Steps
      (StReturn heap v KDone)
      phi
      (StDone heap_final v_final) ->
    heap_final = heap /\ v_final = v /\ phi = [].
Proof.
  intros heap v phi heap_final v_final HSteps.
  remember (StReturn heap v KDone) as start eqn:HStart.
  remember (StDone heap_final v_final) as final eqn:HFinal.
  destruct HSteps as [state | state label state' phi0 state'' HStep HTail].
  - rewrite HStart in HFinal. inversion HFinal.
  - subst state state''.
    inversion HStep; subst.
    destruct
      (Steps_done_inv heap v phi0 (StDone heap_final v_final) HTail)
      as (HTrace & HFinalState).
    inversion HFinalState; subst.
    repeat split; assumption || reflexivity.
Qed.

Lemma Step_append_kont_inv_active :
  forall state tail label appended_state',
    append_active_state state ->
    Step (state_append_kont state tail) label appended_state' ->
    exists state',
      Step state label state' /\
      appended_state' = state_append_kont state' tail.
Proof.
  intros state tail label appended_state' HActive HStep.
  destruct state as
    [heap env rho e k | heap v k | heap v
    | left_state right_state phi_left phi_right k | heap];
    simpl in HActive, HStep.
  - inversion HStep; subst.
    all: eexists; split; [solve_nstep_constructor | reflexivity].
  - destruct k; simpl in HActive; try contradiction;
      inversion HStep; subst.
    all: eexists; split; [solve_nstep_constructor | reflexivity].
  - contradiction.
  - inversion HStep; subst.
    + eexists.
      split.
      * eapply StepPairParRunLeft; eauto.
      * reflexivity.
    + eexists.
      split.
      * eapply StepPairParRunRight; eauto.
      * reflexivity.
    + exists (StError heap).
      split.
      * apply StepPairParRunLeftError.
      * reflexivity.
    + exists (StError heap_right).
      split.
      * apply StepPairParRunRightError.
      * reflexivity.
    + eexists.
      split.
      * eapply StepPairParRunDonePass; eauto.
      * reflexivity.
    + exists (StError heap).
      split.
      * eapply StepPairParRunDoneFail; eauto.
      * reflexivity.
  - contradiction.
Qed.

Lemma StepsN_append_kont_terminal_split :
  forall n appended_start phi heap_final v_final,
    StepsN n appended_start phi (StDone heap_final v_final) ->
    forall state tail,
      appended_start = state_append_kont state tail ->
      exists phi_expr heap_mid v_mid phi_tail,
        Steps state phi_expr (StDone heap_mid v_mid) /\
        Steps
          (StReturn heap_mid v_mid tail)
          phi_tail
          (StDone heap_final v_final) /\
        phi = phi_expr ++ phi_tail.
Proof.
  intros n appended_start phi heap_final v_final HRun.
  remember (StDone heap_final v_final) as final_state eqn:HFinal.
  revert heap_final v_final HFinal.
  induction HRun as
    [state0
    | n state0 label state1 phi0 state2 HStep HTail IH];
    intros heap_final v_final HFinal state tail HAppend.
  - subst state0.
    destruct state as
      [heap env rho e k | heap v k | heap v
      | left_state right_state phi_left phi_right k | heap];
      simpl in HAppend; discriminate.
  - subst state2.
    specialize (IH heap_final v_final eq_refl).
    destruct state as
      [heap env rho e k | heap v k | heap v
      | left_state right_state phi_left phi_right k | heap];
      simpl in HAppend; subst state0.
    + destruct
        (Step_append_kont_inv_active
          (StEval heap env rho e k) tail label state1
          I HStep)
        as (state1_unappended & HStepUnappended & HState1).
      destruct
        (IH state1_unappended tail HState1)
        as (phi_expr & heap_mid & v_mid & phi_tail &
          HExpr & HTailRun & HTrace).
      exists (label_trace label ++ phi_expr), heap_mid, v_mid, phi_tail.
      split.
      * eapply StepsStep; eauto.
      * split; [assumption |].
        rewrite HTrace.
        apply app_assoc.
    + destruct k eqn:Hk.
      { exists [], heap, v, (label_trace label ++ phi0).
        split.
        - apply Steps_return_done.
        - split.
          + eapply StepsStep; eauto.
            eapply StepsN_to_Steps; eauto.
          + reflexivity. }
      all:
          assert (HActive : append_active_state (StReturn heap v k))
            by (rewrite Hk; simpl; exact I);
          subst k;
          match goal with
          | HStep :
              Step (StReturn ?heap0 ?v0 (kont_append ?k_active ?tail0))
                ?label0 ?state10 |- _ =>
              destruct
                (Step_append_kont_inv_active
                  (StReturn heap0 v0 k_active) tail0 label0 state10
                  HActive HStep)
                as (state1_unappended & HStepUnappended & HState1);
              destruct
                (IH state1_unappended tail0 HState1)
                as (phi_expr & heap_mid & v_mid & phi_tail &
                  HExpr & HTailRun & HTrace);
              exists (label_trace label0 ++ phi_expr), heap_mid, v_mid,
                phi_tail;
              split;
              [ eapply StepsStep; eauto
              | split; [assumption |];
                rewrite HTrace;
                apply app_assoc ]
          end.
    + exists [], heap, v, (label_trace label ++ phi0).
      split.
      * constructor.
      * split.
        -- eapply StepsStep; eauto.
           eapply StepsN_to_Steps; eauto.
        -- reflexivity.
    + destruct
        (Step_append_kont_inv_active
          (StPairParRun left_state right_state phi_left phi_right k)
          tail label state1
          I HStep)
        as (state1_unappended & HStepUnappended & HState1).
      destruct
        (IH state1_unappended tail HState1)
        as (phi_expr & heap_mid & v_mid & phi_tail &
          HExpr & HTailRun & HTrace).
      exists (label_trace label ++ phi_expr), heap_mid, v_mid, phi_tail.
      split.
      * eapply StepsStep; eauto.
      * split; [assumption |].
        rewrite HTrace.
        apply app_assoc.
    + inversion HStep.
Qed.

Lemma StepsN_append_kont_terminal_split_counted :
  forall n appended_start phi heap_final v_final,
    StepsN n appended_start phi (StDone heap_final v_final) ->
    forall state tail,
      appended_start = state_append_kont state tail ->
      (forall heap v, state <> StDone heap v) ->
      exists n_expr n_tail phi_expr heap_mid v_mid phi_tail,
        StepsN n_expr state phi_expr (StDone heap_mid v_mid) /\
        StepsN n_tail
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
        (Step_append_kont_inv_active
          (StEval heap env rho e k) tail label state1
          I HStep)
        as (state1_unappended & HStepUnappended & HState1).
      assert
        (HNotDone1 :
          forall heap0 v0,
            state1_unappended <> StDone heap0 v0).
      { intros heap0 v0 HDone.
        subst state1_unappended.
        inversion HStepUnappended. }
      destruct
        (IH state1_unappended tail HState1 HNotDone1)
        as (n_expr & n_tail & phi_expr & heap_mid & v_mid & phi_tail &
          HExpr & HTailRun & HCount & HTrace).
      exists (S n_expr), n_tail, (label_trace label ++ phi_expr),
        heap_mid, v_mid, phi_tail.
      split.
      * eapply StepsNStep; eauto.
      * split; [assumption |].
        split; [lia |].
        rewrite HTrace.
        apply app_assoc.
    + destruct k eqn:Hk.
      { exists 1, (S n), [], heap, v, (label_trace label ++ phi0).
        split.
        - apply StepsN_return_done.
        - split.
          + eapply StepsNStep; eauto.
          + split; [lia | reflexivity]. }
      all:
          assert (HActive : append_active_state (StReturn heap v k))
            by (rewrite Hk; simpl; exact I);
          subst k;
          match goal with
          | HStep :
              Step (StReturn ?heap0 ?v0 (kont_append ?k_active ?tail0))
                ?label0 ?state10 |- _ =>
              destruct
                (Step_append_kont_inv_active
                  (StReturn heap0 v0 k_active) tail0 label0 state10
                  HActive HStep)
                as (state1_unappended & HStepUnappended & HState1);
              assert
                (HNotDone1 :
                  forall heap_done v_done,
                    state1_unappended <> StDone heap_done v_done)
                by
                  (intros heap_done v_done HDone;
                   subst state1_unappended;
                   inversion HStepUnappended);
              destruct
                (IH state1_unappended tail0 HState1 HNotDone1)
                as (n_expr & n_tail & phi_expr & heap_mid & v_mid &
                  phi_tail & HExpr & HTailRun & HCount & HTrace);
              exists (S n_expr), n_tail,
                (label_trace label0 ++ phi_expr), heap_mid, v_mid,
                phi_tail;
              split;
              [ eapply StepsNStep; eauto
              | split; [assumption |];
                split; [lia |];
                rewrite HTrace;
                apply app_assoc ]
          end.
    + exfalso. eapply HNotDone. reflexivity.
    + destruct
        (Step_append_kont_inv_active
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
        inversion HStepUnappended. }
      destruct
        (IH state1_unappended tail HState1 HNotDone1)
        as (n_expr & n_tail & phi_expr & heap_mid & v_mid & phi_tail &
          HExpr & HTailRun & HCount & HTrace).
      exists (S n_expr), n_tail, (label_trace label ++ phi_expr),
        heap_mid, v_mid, phi_tail.
      split.
      * eapply StepsNStep; eauto.
      * split; [assumption |].
        split; [lia |].
        rewrite HTrace.
        apply app_assoc.
    + inversion HStep.
Qed.
