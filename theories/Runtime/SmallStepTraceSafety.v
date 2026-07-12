From stdpp Require Import gmap.
From Stdlib Require Import Program.Equality.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepReturnProgress.
Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepPreservationTheorems.
Require Import theories.Runtime.SmallStepExplicitStoreBase.
Require Import theories.Runtime.SmallStepExplicitStoreTheorems.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.HeapFacts.
Require Import theories.Meta.RegionSubstitutionFacts.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.TraceTypingFacts.
Require Import theories.Meta.TypeFacts.
Require Import theories.Meta.TypingWeakeningFacts.

Definition StateEvalHeadRegionsResolved (state : State) : Prop :=
  forall heap env rho e k,
    state = StEval heap env rho e k ->
    EvalHeadRegionsResolved rho e.

Lemma TcExp_eval_head_regions_resolved :
  forall ctxt rgns e t eff rho,
    TcRho (rho, rgns) ->
    TcExp (ctxt, rgns, e, t, eff) ->
    EvalHeadRegionsResolved rho e.
Proof.
  intros ctxt rgns e t eff rho HTcRho HTcExp.
  destruct e; simpl; try exact I;
    inversion HTcExp; subst; eapply TcRho_TcRgn_find_R; eauto.
Qed.

Lemma WTStateRuntimeHeapShape_eval_heads_resolved :
  forall state tout,
    WTStateRuntimeHeapShape state tout ->
    StateEvalHeadRegionsResolved state.
Proof.
  intros state tout HWT.
  destruct state as [heap0 env0 rho0 e0 k0 | heap0 v k0 | heap0 v];
    intros heap env rho e k HEq; inversion HEq; subst.
  inversion HWT; subst.
  eapply TcExp_eval_head_regions_resolved; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_eval_heads_resolved :
  forall state tout stty,
    WTStateRuntimeHeapShapeAt state tout stty ->
    StateEvalHeadRegionsResolved state.
Proof.
  intros state tout stty HWT.
  destruct state as [heap0 env0 rho0 e0 k0 | heap0 v k0 | heap0 v];
    intros heap env rho e k HEq; inversion HEq; subst.
  inversion HWT; subst.
  eapply TcExp_eval_head_regions_resolved; eauto.
Qed.

Lemma StateEvalHeadRegionsResolved_with_state_heap :
  forall heap state,
    StateEvalHeadRegionsResolved state ->
    StateEvalHeadRegionsResolved (with_state_heap heap state).
Proof.
  intros heap state HReady heap0 env rho e k HEq.
  destruct state; simpl in HEq; inversion HEq; subst.
  eapply HReady. reflexivity.
Qed.

Lemma WTStateRuntimeHeapShapeAt_step_label_typed :
  forall state tin stty label state' tout stty',
    WTStateRuntimeHeapShapeAt state tin stty ->
    Step state label state' ->
    WTStateRuntimeHeapShapeAt state' tout stty' ->
    TcPhi stty' (trace_as_phi (label_trace label)).
Proof.
  intros state tin stty label state' tout stty' HWT HStep HWT'.
  inversion HStep; subst; simpl; try apply TcPhi_nil.
  - apply TcPhi_trace_as_phi_single.
    dependent destruction HWT'.
    eapply TcPhi_elem_alloc_from_heap; eauto.
    unfold find_H, update_H. simpl.
    apply H_same_key_1.
  - apply TcPhi_trace_as_phi_single.
    apply TcPhi_elem_read.
  - apply TcPhi_trace_as_phi_single.
    dependent destruction HWT'.
    eapply TcPhi_elem_write_from_heap; eauto.
    unfold find_H, update_H. simpl.
    apply H_same_key_1.
Qed.

Theorem WTStateRuntimeHeapShapeAt_steps_trace_typed :
  forall state tout stty trace state',
    WTStateRuntimeHeapShapeAt state tout stty ->
    Steps state trace state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      StoreExtends stty stty' /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros state tout stty trace state' HWT HSteps.
  revert tout stty HWT.
  induction HSteps as [state | state label state1 trace state2 HStep HSteps IH];
    intros tout stty HWT.
  - exists stty.
    split; [exact HWT |].
    split; [apply StoreExtends_refl | apply TcPhi_nil].
  - destruct
      (WTStateRuntimeHeapShapeAt_step_preservation
        state tout stty label state1 HWT HStep)
      as (stty1 & HWT1 & _ & _ & HExt1).
    destruct (IH tout stty1 HWT1) as (stty2 & HWT2 & HExt2 & HTcTrace).
    pose proof
      (WTStateRuntimeHeapShapeAt_step_label_typed
        state tout stty label state1 tout stty1 HWT HStep HWT1)
      as HTcLabel1.
    pose proof
      (TcPhi_weaken
        stty1 stty2 (trace_as_phi (label_trace label))
        HExt2 HTcLabel1)
      as HTcLabel2.
    exists stty2.
    split; [exact HWT2 |].
    split; [eapply StoreExtends_trans; eauto |].
    apply TcPhi_trace_as_phi_app; assumption.
Qed.

Lemma WTStateRuntimeHeapShapeAt_initial :
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    WTStateRuntimeHeapShapeAt
      (initial_state heap env rho e) (subst_rho rho t) stty.
Proof.
  intros heap env rho e stty ctxt rgns t eff
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp.
  unfold initial_state.
  eapply WTSRHSA_Eval with (ctxt := ctxt) (rgns := rgns) (t := t)
    (eff := eff); eauto.
  constructor.
Qed.

Theorem initial_state_steps_trace_typed :
  forall heap env rho e stty ctxt rgns t eff trace state',
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    Steps (initial_state heap env rho e) trace state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' (subst_rho rho t) stty' /\
      StoreExtends stty stty' /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros heap env rho e stty ctxt rgns t eff trace state'
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps.
  eapply WTStateRuntimeHeapShapeAt_steps_trace_typed; eauto.
  eapply WTStateRuntimeHeapShapeAt_initial; eauto.
Qed.

Theorem WTStateRuntimeHeapShapeAt_steps_safety_with_trace :
  PairParCheckDecidable ->
  forall state tout stty trace state',
    WTStateRuntimeHeapShapeAt state tout stty ->
    Steps state trace state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      StoreExtends stty stty' /\
      NotStuck state' /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros HDec state tout stty trace state' HWT HSteps.
  destruct
    (WTStateRuntimeHeapShapeAt_steps_trace_typed
      state tout stty trace state' HWT HSteps)
    as (stty' & HWT' & HExt & HTcTrace).
  assert (HReady' : StateEvalHeadRegionsResolved state').
  {
    eapply WTStateRuntimeHeapShapeAt_eval_heads_resolved; eauto.
  }
  assert (HNotStuck' : NotStuck state').
  {
    eapply WTStateRuntimeHeapShape_not_stuck; eauto.
    eapply WTStateRuntimeHeapShapeAt_forget; eauto.
  }
  exists stty'. split; [exact HWT' |].
  split; [exact HExt |].
  split; [exact HNotStuck' | exact HTcTrace].
Qed.

Theorem initial_state_steps_safety_with_trace :
  PairParCheckDecidable ->
  forall heap env rho e stty ctxt rgns t eff trace state',
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    Steps (initial_state heap env rho e) trace state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' (subst_rho rho t) stty' /\
      StoreExtends stty stty' /\
      NotStuck state' /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros HDec heap env rho e stty ctxt rgns t eff trace state'
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps.
  eapply WTStateRuntimeHeapShapeAt_steps_safety_with_trace; eauto.
  eapply WTStateRuntimeHeapShapeAt_initial; eauto.
Qed.

Definition StateTraceSafeAt (state : State) (tout : Tau) (stty : Sigma) : Prop :=
  forall trace state',
    Steps state trace state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      StoreExtends stty stty' /\
      NotStuck state' /\
      TcPhi stty' (trace_as_phi trace).

Theorem WTStateRuntimeHeapShapeAt_trace_safe_typed :
  PairParCheckDecidable ->
  forall state tout stty,
    WTStateRuntimeHeapShapeAt state tout stty ->
    StateTraceSafeAt state tout stty.
Proof.
  intros HDec state tout stty HWT trace state' HSteps.
  eapply WTStateRuntimeHeapShapeAt_steps_safety_with_trace; eauto.
Qed.

Theorem initial_state_trace_safe_typed :
  PairParCheckDecidable ->
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    StateTraceSafeAt (initial_state heap env rho e) (subst_rho rho t) stty.
Proof.
  intros HDec heap env rho e stty ctxt rgns t eff
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp.
  eapply WTStateRuntimeHeapShapeAt_trace_safe_typed; eauto.
  eapply WTStateRuntimeHeapShapeAt_initial; eauto.
Qed.

Definition StateNeverStuck (state : State) : Prop :=
  forall trace state',
    Steps state trace state' ->
    NotStuck state'.

Theorem WTStateRuntimeHeapShapeAt_never_stuck_typed :
  PairParCheckDecidable ->
  forall state tout stty,
    WTStateRuntimeHeapShapeAt state tout stty ->
    StateNeverStuck state.
Proof.
  intros HDec state tout stty HWT trace state' HSteps.
  destruct
    (WTStateRuntimeHeapShapeAt_steps_safety_with_trace
      HDec state tout stty trace state' HWT HSteps)
    as (_ & _ & _ & HNotStuck & _).
  exact HNotStuck.
Qed.

Theorem initial_state_never_stuck_typed :
  PairParCheckDecidable ->
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    StateNeverStuck (initial_state heap env rho e).
Proof.
  intros HDec heap env rho e stty ctxt rgns t eff
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp.
  eapply WTStateRuntimeHeapShapeAt_never_stuck_typed; eauto.
  eapply WTStateRuntimeHeapShapeAt_initial; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_done_value :
  forall heap v tout stty,
    WTStateRuntimeHeapShapeAt (StDone heap v) tout stty ->
    TcHeap (heap, stty) /\
    RuntimeHeapShape heap stty /\
    TcVal (stty, v, tout) /\
    RuntimeValShape stty tout v.
Proof.
  intros heap v tout stty HWT.
  dependent destruction HWT.
  split; [exact H |].
  split; [exact H0 |].
  split; [exact H1 | exact H2].
Qed.

Theorem StateTraceSafeAt_terminal_value :
  forall state tout stty trace heap' v,
    StateTraceSafeAt state tout stty ->
    Steps state trace (StDone heap' v) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, tout) /\
      RuntimeValShape stty' tout v /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros state tout stty trace heap' v HSafe HSteps.
  destruct (HSafe trace (StDone heap' v) HSteps)
    as (stty' & HWT' & HExt & _ & HTcTrace).
  destruct
    (WTStateRuntimeHeapShapeAt_done_value heap' v tout stty' HWT')
    as (HTcHeap' & HHeapShape' & HTcVal' & HValShape').
  exists stty'. split; [exact HExt |].
  split; [exact HTcHeap' |].
  split; [exact HHeapShape' |].
  split; [exact HTcVal' |].
  split; [exact HValShape' | exact HTcTrace].
Qed.

Theorem initial_state_terminal_value_with_trace :
  forall heap env rho e stty ctxt rgns t eff trace heap' v,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    Steps (initial_state heap env rho e) trace (StDone heap' v) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, subst_rho rho t) /\
      RuntimeValShape stty' (subst_rho rho t) v /\
      TcPhi stty' (trace_as_phi trace).
Proof.
  intros heap env rho e stty ctxt rgns t eff trace heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps.
  destruct
    (initial_state_steps_trace_typed
      heap env rho e stty ctxt rgns t eff trace (StDone heap' v)
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcExp HSteps)
    as (stty' & HWT' & HExt & HTcTrace).
  destruct
    (WTStateRuntimeHeapShapeAt_done_value heap' v (subst_rho rho t) stty' HWT')
    as (HTcHeap' & HHeapShape' & HTcVal' & HValShape').
  exists stty'. split; [exact HExt |].
  split; [exact HTcHeap' |].
  split; [exact HHeapShape' |].
  split; [exact HTcVal' |].
  split; [exact HValShape' | exact HTcTrace].
Qed.
