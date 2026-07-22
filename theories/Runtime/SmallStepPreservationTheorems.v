From stdpp Require Import gmap.
From Stdlib Require Import Sets.Ensembles.

Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepTyping.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepReturnProgress.
Require Import theories.Runtime.SmallStepEvalProgress.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.MapFacts.
Require Import theories.Meta.RegionSubstitutionFacts.
Require Import theories.Meta.HeapFacts.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.TypingWeakeningFacts.
Require Import theories.Meta.TypeFacts.
Require Import theories.Meta.LocallyNameless.

Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepPreservationHeapShapeCases.
Require Import theories.Runtime.SmallStepPreservationKontShapeCases.
Require Import theories.Runtime.SmallStepPreservationHeapSensitiveCases.

Theorem WTStateRuntimeHeapShape_step_preservation :
  forall state tout lbl state',
    WTStateRuntimeHeapShape state tout ->
    NonPairParRunState state ->
    Step state lbl state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros state tout lbl state' HState HNonRun HStep.
  inversion HStep; subst; try solve
    [ eapply WTStateRuntimeHeapShape_const_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_bool_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_var_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_mu_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_lambda_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_mu_app_eval_fun_preservation; eauto
    | eapply WTStateRuntimeHeapShape_mu_app_eval_arg_preservation; eauto
    | eapply WTStateRuntimeHeapShape_mu_app_body_preservation; eauto
    | eapply WTStateRuntimeHeapShape_rgn_app_eval_fun_preservation; eauto
    | eapply WTStateRuntimeHeapShape_rgn_app_body_preservation; eauto
    | eapply WTStateRuntimeHeapShape_eff_app_eval_fun_preservation; eauto
    | eapply WTStateRuntimeHeapShape_eff_app_eval_arg_preservation; eauto
    | eapply WTStateRuntimeHeapShape_eff_app_body_preservation; eauto
    | eapply WTStateRuntimeHeapShape_pairpar_eval_eff1_preservation; eauto
    | eapply WTStateRuntimeHeapShape_pairpar_eval_eff2_preservation; eauto
    | eapply WTStateRuntimeHeapShape_pairpar_eval_mu1_preservation; eauto
    | eapply WTStateRuntimeHeapShape_pairpar_eval_mu2_preservation; eauto
    | eapply WTStateRuntimeHeapShape_pairpar_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_cond_eval_guard_preservation; eauto
    | eapply WTStateRuntimeHeapShape_cond_true_preservation; eauto
    | eapply WTStateRuntimeHeapShape_cond_false_preservation; eauto
    | eapply WTStateRuntimeHeapShape_ref_eval_arg_preservation; eauto
    | eapply WTStateRuntimeHeapShape_ref_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_deref_eval_arg_preservation; eauto
    | eapply WTStateRuntimeHeapShape_deref_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_assign_eval_loc_preservation; eauto
    | eapply WTStateRuntimeHeapShape_assign_eval_val_preservation; eauto
    | eapply WTStateRuntimeHeapShape_assign_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_plus_eval_left_preservation; eauto
    | eapply WTStateRuntimeHeapShape_plus_eval_right_preservation; eauto
    | eapply WTStateRuntimeHeapShape_plus_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_minus_eval_left_preservation; eauto
    | eapply WTStateRuntimeHeapShape_minus_eval_right_preservation; eauto
    | eapply WTStateRuntimeHeapShape_minus_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_times_eval_left_preservation; eauto
    | eapply WTStateRuntimeHeapShape_times_eval_right_preservation; eauto
    | eapply WTStateRuntimeHeapShape_times_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_eq_eval_left_preservation; eauto
    | eapply WTStateRuntimeHeapShape_eq_eval_right_preservation; eauto
    | eapply WTStateRuntimeHeapShape_eq_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_alloc_abs_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_read_abs_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_write_abs_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_read_conc_eval_arg_preservation; eauto
    | eapply WTStateRuntimeHeapShape_read_conc_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_write_conc_eval_arg_preservation; eauto
    | eapply WTStateRuntimeHeapShape_write_conc_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_concat_eval_left_preservation; eauto
    | eapply WTStateRuntimeHeapShape_concat_eval_right_preservation; eauto
    | eapply WTStateRuntimeHeapShape_concat_done_preservation; eauto
    | eapply WTStateRuntimeHeapShape_top_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_empty_step_preservation; eauto
    | eapply WTStateRuntimeHeapShape_done_step_preservation; eauto
    | contradiction
    | inversion HState ].
Qed.

Theorem WTStateRuntimeHeapShape_steps_preservation :
  forall state tout trace state',
    WTStateRuntimeHeapShape state tout ->
    StepsStayNonPairParRun state ->
    Steps state trace state' ->
    WTStateRuntimeHeapShape state' tout.
Proof.
  intros state tout trace state' HState HStay HSteps.
	  induction HSteps.
	  - assumption.
	  - apply IHHSteps.
	    + eapply WTStateRuntimeHeapShape_step_preservation; eauto.
	      eapply HStay.
	      constructor.
	    + eapply steps_stay_non_pairpar_run_tail; eauto.
Qed.

Corollary WTStateRuntimeHeapShape_initial_steps_preservation :
  forall heap env rho e stty ctxt rgns t eff trace state',
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    StepsStayNonPairParRun (initial_state heap env rho e) ->
    Steps (initial_state heap env rho e) trace state' ->
    WTStateRuntimeHeapShape state' (subst_rho rho t).
Proof.
  intros heap env rho e stty ctxt rgns t eff trace state'
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HStay HSteps.
  eapply WTStateRuntimeHeapShape_steps_preservation; eauto.
  eapply WTStateRuntimeHeapShape_initial; eauto.
Qed.

Definition PairParCheckDecidable : Prop :=
  forall theta1 theta2,
    (Disjointness theta1 theta2 /\ ~ Conflictness theta1 theta2) \/
    ~ (Disjointness theta1 theta2 /\ ~ Conflictness theta1 theta2).

Lemma pairpar_check_state_ready :
  forall heap ef1 ea1 ef2 ea2 env rho theta1 theta2 k,
    Disjointness theta1 theta2 ->
    ~ Conflictness theta1 theta2 ->
    CanStep
      (StReturn heap (Eff theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)).
Proof.
	  intros heap ef1 ea1 ef2 ea2 env rho theta1 theta2 k HDisj HNoConf.
	  exists Silent,
	    (StPairParRun
	      (initial_state heap env rho (Mu_App ef1 ea1))
	      (initial_state heap env rho (Mu_App ef2 ea2))
	      k).
	  econstructor; eauto.
Qed.

Lemma pairpar_check_state_decidable_ready :
  PairParCheckDecidable ->
  forall heap ef1 ea1 ef2 ea2 env rho theta1 theta2 k,
    CanStep
      (StReturn heap (Eff theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)) \/
    PairParCheckState
      (StReturn heap (Eff theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)).
Proof.
  intros HDec heap ef1 ea1 ef2 ea2 env rho theta1 theta2 k.
  destruct (HDec theta1 theta2) as [[HDisj HNoConf] | HFail].
  - left. eapply pairpar_check_state_ready; eauto.
  - right. constructor.
Qed.

Lemma WTKontRuntime_return_progress_or_pairpar_check :
  forall heap stty v tin tout k,
    TcHeap (heap, stty) ->
    TcVal (stty, v, tin) ->
    WTKontRuntime stty tin tout k ->
    RuntimeValShape stty tin v ->
    CanStep (StReturn heap v k) \/
      PairParCheckState (StReturn heap v k).
Proof.
  intros heap stty v tin tout k HTcHeap HTcVal HKont HShape.
  revert heap v HTcHeap HTcVal HShape.
  induction HKont; intros heap0 v HTcHeap HTcVal HShape.
  - left. apply return_frame_ready_progress. simpl. exact I.
  - left. apply return_frame_ready_progress. simpl.
    rewrite subst_rho_arrow in HShape.
    rewrite (subst_rho_effect rho) in HShape.
    now eapply RuntimeValShape_arrow_inv; eauto.
  - left. apply return_frame_ready_progress. simpl. exact I.
  - left. apply return_frame_ready_progress. simpl.
    rewrite subst_rho_forallrgn in HShape.
    destruct (RuntimeValShape_forall_inv stty v
      (fold_subst_eps rho effr) (subst_rho rho tyr) HShape)
      as (env' & rho' & x & eb & HValue).
    destruct (TcRho_TcRgn_find_R rho rgns w H H0) as [r HFind].
    repeat eexists; eauto.
  - left. apply return_frame_ready_progress. simpl.
    rewrite subst_rho_arrow in HShape.
    rewrite (subst_rho_effect rho) in HShape.
    now eapply RuntimeValShape_arrow_inv; eauto.
  - left. apply return_frame_ready_progress. simpl. exact I.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_effect_inv; eauto.
  - right.
    destruct (RuntimeValShape_effect_inv stty v HShape) as [theta2 HValue].
    subst. constructor.
  - left. apply return_frame_ready_progress. simpl. exact I.
  - left. apply return_frame_ready_progress. simpl. exact I.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_boolean_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    eapply TcRho_TcRgn_find_R; eauto.
  - subst.
    left. apply return_frame_ready_progress. simpl.
    unfold mk_rgn_type in HShape, HTcVal; simpl in HShape, HTcVal.
    rewrite subst_rho_ref_const in HShape.
    rewrite subst_rho_ref_const in HTcVal.
    destruct (RuntimeValShape_ref_const_inv stty v s (subst_rho rho t) HShape)
      as [l HValue].
    subst.
    pose proof (TcVal_loc_find_ST stty s l (subst_rho rho t) HTcVal)
      as HFindST.
    destruct (TcHeap_find_ST_find_H heap0 stty (s, l) (subst_rho rho t)
      HTcHeap HFindST) as [value HFindH].
    exists l, s, value.
    repeat split; auto.
  - subst.
    left. apply return_frame_ready_progress. simpl.
    unfold mk_rgn_type in HShape; simpl in HShape.
    rewrite subst_rho_ref_const in HShape.
    destruct (RuntimeValShape_ref_const_inv stty v s (subst_rho rho t) HShape)
      as [l HValue].
    exists l. exact HValue.
  - left. apply return_frame_ready_progress. simpl.
    exists r. split; [assumption |].
    eapply TcHeap_find_ST_find_H_not_none; eauto.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_natural_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_natural_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_natural_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_natural_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_natural_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_natural_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_natural_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_natural_inv; eauto.
  - left. apply return_frame_ready_progress. simpl.
    rewrite subst_rho_ref_const in HShape.
    destruct (RuntimeValShape_ref_const_inv stty v r (subst_rho rho t) HShape)
      as [l HValue].
    exists r, l. exact HValue.
  - left. apply return_frame_ready_progress. simpl.
    rewrite subst_rho_ref_const in HShape.
    destruct (RuntimeValShape_ref_const_inv stty v r (subst_rho rho t) HShape)
      as [l HValue].
    exists r, l. exact HValue.
  - left. apply return_frame_ready_progress. simpl.
    now eapply RuntimeValShape_effect_inv; eauto.
	  - left. apply return_frame_ready_progress. simpl.
	    now eapply RuntimeValShape_effect_inv; eauto.
Qed.

Lemma WTKontRuntime_return_progress :
  PairParCheckDecidable ->
  forall heap stty v tin tout k,
    TcHeap (heap, stty) ->
    TcVal (stty, v, tin) ->
    WTKontRuntime stty tin tout k ->
    RuntimeValShape stty tin v ->
    CanStep (StReturn heap v k) \/
    PairParCheckState (StReturn heap v k).
Proof.
  intros HDec heap stty v tin tout k HTcHeap HTcVal HKont HShape.
  destruct (WTKontRuntime_return_progress_or_pairpar_check
    heap stty v tin tout k HTcHeap HTcVal HKont HShape)
    as [HCanStep | HCheck].
  - left. exact HCanStep.
  - inversion HCheck; subst.
    eapply pairpar_check_state_decidable_ready; eauto.
Qed.

Theorem WTStateRuntimeHeapShape_not_stuck_or_pairpar_check :
  forall state tout,
    WTStateRuntimeHeapShape state tout ->
    NonPairParRunState state ->
    (forall heap env rho e k,
        state = StEval heap env rho e k ->
        EvalHeadRegionsResolved rho e) ->
    NotStuck state \/ PairParCheckState state.
Proof.
  intros state tout HState HNonRun HEvalReady.
  inversion HState; subst.
  - left. right. left.
    destruct e; simpl in *; try solve
      [ eapply typed_eval_sequential_head_progress_unindexed; eauto;
        try exact I; try (eapply HEvalReady; reflexivity) ].
    exists Silent,
      (StEval heap env rho (Eff_App e1 e2)
        (KPairParEff1 e1 e2 e3 e4 env rho k)).
    constructor.
  - destruct (WTKontRuntime_return_progress_or_pairpar_check
      heap stty v t tout k H H1 H2 H3) as [HCanStep | HCheck].
    + left. right. left. exact HCanStep.
    + left. right. right. exact HCheck.
  - left. left. constructor.
  - contradiction.
Qed.

Theorem WTStateRuntimeHeapShape_not_stuck :
  PairParCheckDecidable ->
  forall state tout,
    WTStateRuntimeHeapShape state tout ->
    NonPairParRunState state ->
    (forall heap env rho e k,
        state = StEval heap env rho e k ->
        EvalHeadRegionsResolved rho e) ->
    NotStuck state.
Proof.
  intros HDec state tout HState HNonRun HEvalReady.
  inversion HState; subst.
  - right. left.
    destruct e; simpl in *; try solve
      [ eapply typed_eval_sequential_head_progress_unindexed; eauto;
        try exact I; try (eapply HEvalReady; reflexivity) ].
    exists Silent,
      (StEval heap env rho (Eff_App e1 e2)
        (KPairParEff1 e1 e2 e3 e4 env rho k)).
    constructor.
  - destruct
      (WTKontRuntime_return_progress HDec heap stty v t tout k H H1 H2 H3)
      as [HCanStep | HCheck].
    + right. left. exact HCanStep.
    + right. right. exact HCheck.
  - left. constructor.
  - contradiction.
Qed.
