From Stdlib Require Import List.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.Trace.

Import ListNotations.

Ltac solve_nstep_constructor :=
  match goal with
  | |- NStep (StEval _ _ _ (EConst _) _) _ _ => apply StepConst
  | |- NStep (StEval _ _ _ (EBool _) _) _ _ => apply StepBool
  | |- NStep (StEval _ _ _ (EVar _) _) _ _ => eapply StepVar
  | |- NStep (StEval _ _ _ (EMu _ _ _ _) _) _ _ => apply StepMu
  | |- NStep (StEval _ _ _ (ELambdaRgn _ _) _) _ _ =>
      apply StepLambdaRgn
  | |- NStep (StEval _ _ _ (EMuApp _ _) _) _ _ => apply StepMuApp
  | |- NStep (StEval _ _ _ (ERgnApp _ _) _) _ _ => apply StepRgnApp
  | |- NStep (StEval _ _ _ (EEffApp _ _) _) _ _ => apply StepEffApp
  | |- NStep (StEval _ _ _ (ECond _ _ _) _) _ _ => apply StepCond
  | |- NStep (StEval _ _ _ (ERef _ _) _) _ _ => eapply StepRef
  | |- NStep (StEval _ _ _ (EDeref _ _) _) _ _ => apply StepDeref
  | |- NStep (StEval _ _ _ (EAssign _ _ _) _) _ _ => apply StepAssign
  | |- NStep (StEval _ _ _ (EPlus _ _) _) _ _ => apply StepPlus
  | |- NStep (StEval _ _ _ (EMinus _ _) _) _ _ => apply StepMinus
  | |- NStep (StEval _ _ _ (ETimes _ _) _) _ _ => apply StepTimes
  | |- NStep (StEval _ _ _ (EEq _ _) _) _ _ => apply StepEq
  | |- NStep (StEval _ _ _ (EAllocAbs _) _) _ _ => eapply StepAllocAbs
  | |- NStep (StEval _ _ _ (EReadAbs _) _) _ _ => eapply StepReadAbs
  | |- NStep (StEval _ _ _ (EWriteAbs _) _) _ _ => eapply StepWriteAbs
  | |- NStep (StEval _ _ _ (EReadConc _) _) _ _ => apply StepReadConc
  | |- NStep (StEval _ _ _ (EWriteConc _) _) _ _ => apply StepWriteConc
  | |- NStep (StEval _ _ _ (EConcat _ _) _) _ _ => apply StepConcat
  | |- NStep (StEval _ _ _ ETop _) _ _ => apply StepTop
  | |- NStep (StEval _ _ _ EEmpty _) _ _ => apply StepEmpty
  | |- NStep (StReturn _ (VClosure _ _ _ _ _ _)
        (KMuAppFun _ _ _ _)) _ _ =>
      apply StepMuAppFun
  | |- NStep (StReturn _ _
        (KMuAppArg _ _ _ _ _ _ _)) _ _ =>
      apply StepMuAppArg
  | |- NStep (StReturn _ (VClosure _ _ _ _ _ _)
        (KEffAppFun _ _ _ _)) _ _ =>
      apply StepEffAppFun
  | |- NStep (StReturn _ _
        (KEffAppArg _ _ _ _ _ _ _)) _ _ =>
      apply StepEffAppArg
  | |- NStep (StReturn _ (VRegionClosure _ _ _ _)
        (KRgnApp _ _ _)) _ _ =>
      eapply StepRgnAppReturn
  | |- NStep (StReturn _ (VBool true)
        (KCond _ _ _ _ _)) _ _ =>
      apply StepCondTrue
  | |- NStep (StReturn _ (VBool false)
        (KCond _ _ _ _ _)) _ _ =>
      apply StepCondFalse
  | |- NStep (StReturn _ _ (KRef _ _)) _ _ =>
      eapply StepRefReturn
  | |- NStep (StReturn _ (VLoc _ _) (KDeref _ _)) _ _ =>
      eapply StepDerefReturn
  | |- NStep (StReturn _ (VLoc _ _) (KAssignLoc _ _ _ _ _)) _ _ =>
      apply StepAssignLoc
  | |- NStep (StReturn _ _ (KAssignVal _ (VLoc _ _) _)) _ _ =>
      apply StepAssignVal
  | |- NStep (StReturn _ (VNat _) (KPlusL _ _ _ _)) _ _ =>
      apply StepPlusL
  | |- NStep (StReturn _ (VNat _) (KPlusR _ _)) _ _ =>
      apply StepPlusR
  | |- NStep (StReturn _ (VNat _) (KMinusL _ _ _ _)) _ _ =>
      apply StepMinusL
  | |- NStep (StReturn _ (VNat _) (KMinusR _ _)) _ _ =>
      apply StepMinusR
  | |- NStep (StReturn _ (VNat _) (KTimesL _ _ _ _)) _ _ =>
      apply StepTimesL
  | |- NStep (StReturn _ (VNat _) (KTimesR _ _)) _ _ =>
      apply StepTimesR
  | |- NStep (StReturn _ (VNat _) (KEqL _ _ _ _)) _ _ =>
      apply StepEqL
  | |- NStep (StReturn _ (VNat _) (KEqR _ _)) _ _ =>
      apply StepEqR
  | |- NStep (StReturn _ (VLoc _ _) (KReadConc _)) _ _ =>
      apply StepReadConcReturn
  | |- NStep (StReturn _ (VLoc _ _) (KWriteConc _)) _ _ =>
      apply StepWriteConcReturn
  | |- NStep (StReturn _ (VSummary _) (KConcatL _ _ _ _)) _ _ =>
      apply StepConcatL
  | |- NStep (StReturn _ (VSummary _) (KConcatR _ _)) _ _ =>
      apply StepConcatR
  | |- NStep (StReturn _ _ KDone) _ _ => apply StepReturnDone
  end; eauto.

Fixpoint kont_append (k tail : NKont) : NKont :=
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

Definition state_append_kont (state : NState) (tail : NKont) : NState :=
  match state with
  | StEval heap env rho e k =>
      StEval heap env rho e (kont_append k tail)
  | StReturn heap v k =>
      StReturn heap v (kont_append k tail)
  | StDone heap v =>
      StReturn heap v tail
  end.

Definition append_active_state (state : NState) : Prop :=
  match state with
  | StDone _ _ => False
  | StReturn _ _ KDone => False
  | _ => True
  end.

Lemma NStep_append_kont_not_done :
  forall state label state' tail,
    NStep state label state' ->
    (forall heap v, state <> StReturn heap v KDone) ->
    NStep
      (state_append_kont state tail)
      label
      (state_append_kont state' tail).
Proof.
  intros state label state' tail HStep HNotDone.
  inversion HStep; subst; simpl; try solve [econstructor; eauto].
  exfalso. eapply HNotDone. reflexivity.
Qed.

Lemma NSteps_append_kont :
  forall state phi state' tail,
    NSteps state phi state' ->
    NSteps
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
        (NSteps_done_inv heap v phi state2 HTail)
        as (HTrace & HState).
    subst phi state2.
    simpl. constructor.
Qed.

Lemma NSteps_return_done :
  forall heap v,
    NSteps (StReturn heap v KDone) [] (StDone heap v).
Proof.
  intros heap v.
  change ([] : Trace) with (label_trace LSilent ++ ([] : Trace)).
  eapply StepsStep.
  - constructor.
  - constructor.
Qed.

Lemma NSteps_return_done_inv :
  forall heap v phi heap_final v_final,
    NSteps
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
      (NSteps_done_inv heap v phi0 (StDone heap_final v_final) HTail)
      as (HTrace & HFinalState).
    inversion HFinalState; subst.
    repeat split; assumption || reflexivity.
Qed.

Lemma NStep_append_kont_inv_active :
  forall state tail label appended_state',
    append_active_state state ->
    NStep (state_append_kont state tail) label appended_state' ->
    exists state',
      NStep state label state' /\
      appended_state' = state_append_kont state' tail.
Proof.
  intros state tail label appended_state' HActive HStep.
  destruct state as
    [heap env rho e k | heap v k | heap v];
    simpl in HActive, HStep.
  - inversion HStep; subst.
    all: eexists; split; [solve_nstep_constructor | reflexivity].
  - destruct k; simpl in HActive; try contradiction;
      inversion HStep; subst.
    all: eexists; split; [solve_nstep_constructor | reflexivity].
  - contradiction.
Qed.

Lemma NStepsN_append_kont_terminal_split :
  forall n appended_start phi heap_final v_final,
    NStepsN n appended_start phi (StDone heap_final v_final) ->
    forall state tail,
      appended_start = state_append_kont state tail ->
      exists phi_expr heap_mid v_mid phi_tail,
        NSteps state phi_expr (StDone heap_mid v_mid) /\
        NSteps
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
      [heap env rho e k | heap v k | heap v];
      simpl in HAppend; discriminate.
  - subst state2.
    specialize (IH heap_final v_final eq_refl).
    destruct state as
      [heap env rho e k | heap v k | heap v];
      simpl in HAppend; subst state0.
    + destruct
        (NStep_append_kont_inv_active
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
        - apply NSteps_return_done.
        - split.
          + eapply StepsStep; eauto.
            eapply NStepsN_to_NSteps; eauto.
          + reflexivity. }
      all:
          assert (HActive : append_active_state (StReturn heap v k))
            by (rewrite Hk; simpl; exact I);
          subst k;
          match goal with
          | HStep :
              NStep (StReturn ?heap0 ?v0 (kont_append ?k_active ?tail0))
                ?label0 ?state10 |- _ =>
              destruct
                (NStep_append_kont_inv_active
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
           eapply NStepsN_to_NSteps; eauto.
        -- reflexivity.
Qed.
