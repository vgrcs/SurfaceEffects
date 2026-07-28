From Stdlib Require Import Lia.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Core.Values.
Require Import theories.SmallStep.Determinism.Terminal.
Require Import theories.SmallStep.Runtime.Continuation.
Require Import theories.SmallStep.Runtime.HeapFacts.
Require Import theories.SmallStep.Runtime.HeapNeutral.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Runtime.Progress.
Require Import theories.SmallStep.Runtime.RegularPreservation.
Require Import theories.SmallStep.Runtime.RegularStateShape.
Require Import theories.SmallStep.Runtime.Trace.
Require Import theories.SmallStep.Runtime.TraceView.
Require Import theories.SmallStep.Runtime.Typing.
Require Import theories.SmallStep.Soundness.BackTriangle.
Require Import theories.SmallStep.Soundness.StaticEffect.
Require Import theories.SmallStep.Typing.Judgments.
Require Import theories.SmallStep.Typing.Regularity.
Require Import theories.SmallStep.Typing.Resolve.
Require Import theories.SmallStep.Typing.Types.

Definition InitialRuntimeTyping
    (gamma : NCtx) (omega : NRgnCtx)
    (heap : Heap) (env : NEnv) (rho : Rho)
    (expr : NExpr) : Prop :=
  exists ty eff,
    NRuntimeHeapShape rho heap /\
    NRuntimeEnvShape rho heap env gamma /\
    NRhoModels omega rho /\
    NTcExp gamma omega expr ty eff.

Definition CheckedRuntimeContext
    (gamma : NCtx) (omega : NRgnCtx)
    (heap : Heap) (env : NEnv) (rho : Rho) : Prop :=
  NRuntimeHeapShape rho heap /\
  NRuntimeEnvShape rho heap env gamma /\
  NRegularResolvedHeapShape heap /\
  NRegularResolvedEnvShape rho heap env gamma /\
  (exists store,
    NStoreResolvedRuntimeShape heap store env rho gamma) /\
  NRhoModels omega rho /\
  NHeapKeysBounded heap.

Definition CheckedStoreRuntimeContext
    (gamma : NCtx) (omega : NRgnCtx)
    (heap : Heap) (env : NEnv) (rho : Rho) : Prop :=
  (exists store,
    NStoreResolvedRuntimeShape heap store env rho gamma) /\
  NRhoModels omega rho.

Definition CheckedBoundedStoreRuntimeContext
    (gamma : NCtx) (omega : NRgnCtx)
    (heap : Heap) (env : NEnv) (rho : Rho) : Prop :=
  CheckedStoreRuntimeContext gamma omega heap env rho /\
  NHeapKeysBounded heap.

Definition CheckedInitialRuntimeTyping
    (gamma : NCtx) (omega : NRgnCtx)
    (heap : Heap) (env : NEnv) (rho : Rho)
    (expr : NExpr) : Prop :=
  exists ty eff,
    CheckedRuntimeContext gamma omega heap env rho /\
    NCheckedTcExp gamma omega expr ty eff.

Lemma InitialRuntimeTyping_to_NWTState :
  forall gamma omega heap env rho expr,
    InitialRuntimeTyping gamma omega heap env rho expr ->
    NWTState gamma omega (NInitialState heap env rho expr).
Proof.
  intros gamma omega heap env rho expr HRuntime.
  destruct HRuntime as (ty & eff & HHeap & HEnv & HRho & HTyped).
  unfold NInitialState.
  eapply NWT_Eval; eauto.
  constructor.
Qed.

Lemma CheckedInitialRuntimeTyping_to_InitialRuntimeTyping :
  forall gamma omega heap env rho expr,
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    InitialRuntimeTyping gamma omega heap env rho expr.
Proof.
  intros gamma omega heap env rho expr HRuntime.
  destruct HRuntime as
    (ty & eff & HContext & HChecked).
  destruct HContext as (HHeap & HEnv & _ & _ & _ & HRho & _).
  exists ty, eff.
  repeat split; eauto using NCheckedTcExp_to_NTcExp.
Qed.

Lemma CheckedInitialRuntimeTyping_to_NWTState :
  forall gamma omega heap env rho expr,
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    NWTState gamma omega (NInitialState heap env rho expr).
Proof.
  intros gamma omega heap env rho expr HRuntime.
  eapply InitialRuntimeTyping_to_NWTState.
  eapply CheckedInitialRuntimeTyping_to_InitialRuntimeTyping; eauto.
Qed.

Lemma CheckedInitialRuntimeTyping_to_regular_state :
  forall gamma omega heap env rho expr,
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    exists ty_res,
      NRegularResolvedStateShape
        (NInitialState heap env rho expr)
        ty_res.
Proof.
  intros gamma omega heap env rho expr HRuntime.
  destruct HRuntime as
    (ty & eff & HContext & HChecked).
  destruct HContext as (_ & _ & HHeap & HEnv & _ & HRho & _).
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ HChecked) as HTyWF.
  destruct (NResolveTy_exists 0 omega rho ty HRho HTyWF)
    as (ty_res & HResolve).
  exists ty_res.
  eapply NRegularResolvedStateShape_initial; eauto.
Qed.

Lemma CheckedRuntimeContext_to_store_runtime_shape :
  forall gamma omega heap env rho,
    CheckedRuntimeContext gamma omega heap env rho ->
    exists store,
      NStoreResolvedRuntimeShape heap store env rho gamma.
Proof.
  intros gamma omega heap env rho HContext.
  destruct HContext as (_ & _ & _ & _ & HStore & _ & _).
  exact HStore.
Qed.

Lemma CheckedRuntimeContext_to_store_context :
  forall gamma omega heap env rho,
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedStoreRuntimeContext gamma omega heap env rho.
Proof.
  intros gamma omega heap env rho HContext.
  destruct HContext as (_ & _ & _ & _ & HStore & HRho & _).
  split; assumption.
Qed.

Lemma CheckedRuntimeContext_to_bounded_store_context :
  forall gamma omega heap env rho,
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedBoundedStoreRuntimeContext gamma omega heap env rho.
Proof.
  intros gamma omega heap env rho HContext.
  destruct HContext as (_ & _ & _ & _ & HStore & HRho & HBounded).
  split.
  - split; assumption.
  - exact HBounded.
Qed.

Lemma CheckedStoreRuntimeContext_to_store_runtime_shape :
  forall gamma omega heap env rho,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    exists store,
      NStoreResolvedRuntimeShape heap store env rho gamma.
Proof.
  intros gamma omega heap env rho HContext.
  destruct HContext as (HStore & _).
  exact HStore.
Qed.

Lemma CheckedStoreRuntimeContext_to_rho_models :
  forall gamma omega heap env rho,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    NRhoModels omega rho.
Proof.
  intros gamma omega heap env rho HContext.
  destruct HContext as (_ & HRho).
  exact HRho.
Qed.

Lemma NStoreResolvedRuntimeShape_heap_lookups_bounded :
  forall heap store env rho gamma,
    NStoreResolvedRuntimeShape heap store env rho gamma ->
    NHeapLookupsBounded heap.
Proof.
  intros heap store env rho gamma HStoreRuntime r l v HLookup.
  unfold NStoreResolvedRuntimeShape in HStoreRuntime.
  destruct HStoreRuntime as (HBounded & HHeap & _).
  destruct HHeap as (HHeapToStore & _).
  destruct (HHeapToStore r l v HLookup)
    as (ty & HStoreLookup & _).
  eapply HBounded.
  eapply store_ty_lookup_in; eauto.
Qed.

Lemma CheckedStoreRuntimeContext_heap_lookups_bounded :
  forall gamma omega heap env rho,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    NHeapLookupsBounded heap.
Proof.
  intros gamma omega heap env rho HContext.
  destruct HContext as ((store & HStoreRuntime) & _).
  eapply NStoreResolvedRuntimeShape_heap_lookups_bounded; eauto.
Qed.

Lemma NStoreResolvedRuntimeShape_heap_keys_bounded :
  forall heap store env rho gamma,
    NStoreResolvedRuntimeShape heap store env rho gamma ->
    NHeapKeysBounded heap.
Proof.
  intros heap store env rho gamma HStoreRuntime r l v HIn.
  destruct (heap_in_lookup_key_exists heap r l v HIn)
    as (v' & HLookup).
  unfold NStoreResolvedRuntimeShape in HStoreRuntime.
  destruct HStoreRuntime as (HBounded & HHeap & _).
  destruct HHeap as (HHeapToStore & _).
  destruct (HHeapToStore r l v' HLookup)
    as (ty & HStoreLookup & _).
  eapply HBounded.
  eapply store_ty_lookup_in; eauto.
Qed.

Lemma CheckedStoreRuntimeContext_heap_keys_bounded :
  forall gamma omega heap env rho,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    NHeapKeysBounded heap.
Proof.
  intros gamma omega heap env rho HContext.
  destruct HContext as ((store & HStoreRuntime) & _).
  eapply NStoreResolvedRuntimeShape_heap_keys_bounded; eauto.
Qed.

Lemma CheckedStoreRuntimeContext_to_bounded_store_context :
  forall gamma omega heap env rho,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedBoundedStoreRuntimeContext gamma omega heap env rho.
Proof.
  intros gamma omega heap env rho HContext.
  split.
  - exact HContext.
  - eapply CheckedStoreRuntimeContext_heap_keys_bounded; eauto.
Qed.

Lemma CheckedInitialRuntimeTyping_to_store_state :
  forall gamma omega heap env rho expr,
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    exists store ty_res,
      NStoreResolvedStateShape store
        (NInitialState heap env rho expr)
        ty_res.
Proof.
  intros gamma omega heap env rho expr HRuntime.
  destruct HRuntime as
    (ty & eff & HContext & HChecked).
  destruct HContext as (_ & _ & _ & _ & HStore & HRho & _).
  destruct HStore as (store & HStore).
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ HChecked) as HTyWF.
  destruct (NResolveTy_exists 0 omega rho ty HRho HTyWF)
    as (ty_res & HResolve).
  exists store, ty_res.
  eapply NStoreResolvedStateShape_initial; eauto.
Qed.

Lemma CheckedRuntimeContext_to_CheckedInitialRuntimeTyping :
  forall gamma omega heap env rho expr ty eff,
    CheckedRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr ty eff ->
    CheckedInitialRuntimeTyping gamma omega heap env rho expr.
Proof.
  intros gamma omega heap env rho expr ty eff HContext HChecked.
  exists ty, eff. split; assumption.
Qed.

Lemma CheckedRuntimeContext_backtriangle_initials :
  forall gamma omega heap env rho expr summary_expr,
    CheckedRuntimeContext gamma omega heap env rho ->
    NCheckedBackTriangle gamma omega expr summary_expr ->
    CheckedInitialRuntimeTyping gamma omega heap env rho expr /\
    CheckedInitialRuntimeTyping gamma omega heap env rho summary_expr.
Proof.
  intros gamma omega heap env rho expr summary_expr HContext HBack.
  destruct (NCheckedBackTriangle_typing _ _ _ _ HBack) as
    (ty & eff & eff_summary & HCheckedExpr & HCheckedSummary).
  split.
  - eapply CheckedRuntimeContext_to_CheckedInitialRuntimeTyping;
      eauto.
  - eapply CheckedRuntimeContext_to_CheckedInitialRuntimeTyping;
      eauto.
Qed.

Lemma CheckedRuntimeContext_heap_neutral_steps :
  forall gamma omega heap env rho expr phi heap_final v,
    CheckedRuntimeContext gamma omega heap env rho ->
    NSteps
      (NInitialState heap env rho expr)
      phi
      (StDone heap_final v) ->
    HeapNeutralTrace phi ->
    CheckedRuntimeContext gamma omega heap_final env rho.
Proof.
  intros gamma omega heap env rho expr phi heap_final v
    HContext HSteps HNeutral.
  pose proof
    (NSteps_heap_neutral_initial_heap
      heap env rho expr phi heap_final v HSteps HNeutral)
    as HHeapEq.
  subst heap_final.
  exact HContext.
Qed.

Theorem checked_initial_progress :
  forall gamma omega heap env rho expr,
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    NProgressState (NInitialState heap env rho expr).
Proof.
  intros gamma omega heap env rho expr HRuntime.
  eapply NStep_progress.
  eapply CheckedInitialRuntimeTyping_to_NWTState; eauto.
Qed.

Theorem checked_initial_step_heap_neutral_preservation :
  forall gamma omega heap env rho expr label state',
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    NStep (NInitialState heap env rho expr) label state' ->
    HeapNeutralTrace (label_trace label) ->
    exists ty_res,
      NRegularResolvedStateShape state' ty_res.
Proof.
  intros gamma omega heap env rho expr label state'
    HRuntime HStep HNeutral.
  destruct
    (CheckedInitialRuntimeTyping_to_regular_state
      gamma omega heap env rho expr HRuntime)
    as (ty_res & HState).
  exists ty_res.
  eapply NStep_heap_neutral_regular_state_preservation; eauto.
Qed.

Theorem checked_initial_steps_heap_neutral_preservation :
  forall gamma omega heap env rho expr phi state',
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    NSteps (NInitialState heap env rho expr) phi state' ->
    HeapNeutralTrace phi ->
    exists ty_res,
      NRegularResolvedStateShape state' ty_res.
Proof.
  intros gamma omega heap env rho expr phi state'
    HRuntime HSteps HNeutral.
  destruct
    (CheckedInitialRuntimeTyping_to_regular_state
      gamma omega heap env rho expr HRuntime)
    as (ty_res & HState).
  exists ty_res.
  eapply NSteps_heap_neutral_regular_state_preservation; eauto.
Qed.

Theorem checked_initial_stepsN_heap_neutral_preservation :
  forall n gamma omega heap env rho expr phi state',
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    NStepsN n (NInitialState heap env rho expr) phi state' ->
    HeapNeutralTrace phi ->
    exists ty_res,
      NRegularResolvedStateShape state' ty_res.
Proof.
  intros n gamma omega heap env rho expr phi state'
    HRuntime HSteps HNeutral.
  destruct
    (CheckedInitialRuntimeTyping_to_regular_state
      gamma omega heap env rho expr HRuntime)
    as (ty_res & HState).
  exists ty_res.
  eapply NStepsN_heap_neutral_regular_state_preservation; eauto.
Qed.

Theorem checked_initial_steps_store_preservation :
  forall gamma omega heap env rho expr phi state',
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    NSteps (NInitialState heap env rho expr) phi state' ->
    exists store ty_res,
      NStoreResolvedStateShape store state' ty_res.
Proof.
  intros gamma omega heap env rho expr phi state'
    HRuntime HSteps.
  destruct
    (CheckedInitialRuntimeTyping_to_store_state
      gamma omega heap env rho expr HRuntime)
    as (store & ty_res & HState).
  destruct
    (NSteps_store_resolved_state_preservation
      (NInitialState heap env rho expr)
      phi state' store ty_res HSteps HState)
    as (store' & HState').
  exists store', ty_res.
  exact HState'.
Qed.

Theorem checked_initial_steps_store_preservation_with_transport :
  forall gamma omega heap env rho expr phi state',
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    NSteps (NInitialState heap env rho expr) phi state' ->
    exists store store' ty_res,
      NStoreResolvedStateShape store
        (NInitialState heap env rho expr)
        ty_res /\
      NStoreResolvedStateShape store' state' ty_res /\
      NStoreStepTransport store store'
        (NInitialState heap env rho expr)
        state'.
Proof.
  intros gamma omega heap env rho expr phi state'
    HRuntime HSteps.
  destruct
    (CheckedInitialRuntimeTyping_to_store_state
      gamma omega heap env rho expr HRuntime)
    as (store & ty_res & HState).
  destruct
    (NSteps_store_resolved_state_preservation_with_transport
      (NInitialState heap env rho expr)
      phi state' store ty_res HSteps HState)
    as (store' & HState' & HTransport).
  exists store, store', ty_res.
  split; [exact HState |].
  split; [exact HState' |].
  exact HTransport.
Qed.

Theorem checked_initial_stepsN_store_preservation :
  forall n gamma omega heap env rho expr phi state',
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    NStepsN n (NInitialState heap env rho expr) phi state' ->
    exists store ty_res,
      NStoreResolvedStateShape store state' ty_res.
Proof.
  intros n gamma omega heap env rho expr phi state'
    HRuntime HSteps.
  eapply checked_initial_steps_store_preservation; eauto.
  eapply NStepsN_to_NSteps; eauto.
Qed.

Theorem checked_initial_stepsN_store_preservation_with_transport :
  forall n gamma omega heap env rho expr phi state',
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    NStepsN n (NInitialState heap env rho expr) phi state' ->
    exists store store' ty_res,
      NStoreResolvedStateShape store
        (NInitialState heap env rho expr)
        ty_res /\
      NStoreResolvedStateShape store' state' ty_res /\
      NStoreStepTransport store store'
        (NInitialState heap env rho expr)
        state'.
Proof.
  intros n gamma omega heap env rho expr phi state'
    HRuntime HSteps.
  eapply checked_initial_steps_store_preservation_with_transport; eauto.
  eapply NStepsN_to_NSteps; eauto.
Qed.

Theorem checked_initial_steps_view_store_preservation :
  forall gamma omega heap env rho expr view state',
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    NStepsView (NInitialState heap env rho expr) view state' ->
    exists store ty_res,
      NStoreResolvedStateShape store state' ty_res.
Proof.
  intros gamma omega heap env rho expr view state'
    HRuntime HSteps.
  eapply checked_initial_steps_store_preservation; eauto.
  eapply NStepsView_to_NSteps; eauto.
Qed.

Theorem checked_initial_steps_view_store_preservation_with_transport :
  forall gamma omega heap env rho expr view state',
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    NStepsView (NInitialState heap env rho expr) view state' ->
    exists store store' ty_res,
      NStoreResolvedStateShape store
        (NInitialState heap env rho expr)
        ty_res /\
      NStoreResolvedStateShape store' state' ty_res /\
      NStoreStepTransport store store'
        (NInitialState heap env rho expr)
        state'.
Proof.
  intros gamma omega heap env rho expr view state'
    HRuntime HSteps.
  eapply checked_initial_steps_store_preservation_with_transport; eauto.
  eapply NStepsView_to_NSteps; eauto.
Qed.

Definition SummaryEvaluation (heap : Heap) (env : NEnv) (rho : Rho)
    (summary_expr : NExpr) (phi_summary : Trace)
    (heap_summary : Heap) (theta : Summary) : Prop :=
  NSteps
    (NInitialState heap env rho summary_expr)
    phi_summary
    (StDone heap_summary (VSummary theta)).

Definition ComputationEvaluation (heap : Heap) (env : NEnv) (rho : Rho)
    (expr : NExpr) (phi : Trace) (heap' : Heap) (v : NVal) : Prop :=
  NSteps
    (NInitialState heap env rho expr)
    phi
    (StDone heap' v).

Theorem checked_computation_store_transport_checked_initial :
  forall gamma omega heap env rho expr ty eff phi heap' v
    next_expr next_ty next_eff,
    CheckedRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr ty eff ->
    NCheckedTcExp gamma omega next_expr next_ty next_eff ->
    ComputationEvaluation heap env rho expr phi heap' v ->
    exists store' next_ty_res,
      NStoreResolvedStateShape store'
        (NInitialState heap' env rho next_expr)
        next_ty_res.
Proof.
  intros gamma omega heap env rho expr ty eff phi heap' v
    next_expr next_ty next_eff HContext HCheckedExpr
    HCheckedNext HComp.
  destruct HContext as
    (_ & _ & _ & _ & HStoreContext & HRho & _).
  destruct HStoreContext as (store & HStoreRuntime).
  pose proof
    (NCheckedTcExp_ty_wf
      gamma omega expr ty eff HCheckedExpr)
    as HTyWF.
  destruct
    (NResolveTy_exists 0 omega rho ty HRho HTyWF)
    as (ty_res & HResolve).
  assert
    (HInitial :
      NStoreResolvedStateShape store
        (NInitialState heap env rho expr)
        ty_res).
  {
    eapply NStoreResolvedStateShape_initial; eauto.
  }
  unfold ComputationEvaluation in HComp.
  destruct
    (NSteps_store_resolved_state_preservation_with_transport
      (NInitialState heap env rho expr)
      phi (StDone heap' v) store ty_res
      HComp HInitial)
    as (store' & _ & HTransport).
  pose proof
    (NCheckedTcExp_ty_wf
      gamma omega next_expr next_ty next_eff HCheckedNext)
    as HNextTyWF.
  destruct
    (NResolveTy_exists 0 omega rho next_ty HRho HNextTyWF)
    as (next_ty_res & HResolveNext).
  assert
    (HNextInitial :
      NStoreResolvedStateShape store
        (NInitialState heap env rho next_expr)
        next_ty_res).
  {
    eapply NStoreResolvedStateShape_initial; eauto.
  }
  destruct HTransport as (HStateTransport & _ & _).
  specialize
    (HStateTransport
      (NInitialState heap env rho next_expr)
      next_ty_res
      eq_refl
      HNextInitial)
    as HNextFinal.
  simpl in HNextFinal.
  exists store', next_ty_res.
  exact HNextFinal.
Qed.

Theorem checked_computation_store_runtime_shape :
  forall gamma omega heap env rho expr ty eff phi heap' v,
    CheckedRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr ty eff ->
    ComputationEvaluation heap env rho expr phi heap' v ->
    exists store',
      NStoreResolvedRuntimeShape heap' store' env rho gamma.
Proof.
  intros gamma omega heap env rho expr ty eff phi heap' v
    HContext HCheckedExpr HComp.
  destruct HContext as
    (_ & _ & _ & _ & HStoreContext & HRho & _).
  destruct HStoreContext as (store & HStoreRuntime).
  pose proof
    (NCheckedTcExp_ty_wf
      gamma omega expr ty eff HCheckedExpr)
    as HTyWF.
  destruct
    (NResolveTy_exists 0 omega rho ty HRho HTyWF)
    as (ty_res & HResolve).
  assert
    (HInitial :
      NStoreResolvedStateShape store
        (NInitialState heap env rho expr)
        ty_res).
  {
    eapply NStoreResolvedStateShape_initial; eauto.
  }
  unfold ComputationEvaluation in HComp.
  destruct
    (NSteps_store_resolved_state_preservation_with_transport
      (NInitialState heap env rho expr)
      phi (StDone heap' v) store ty_res
      HComp HInitial)
    as (store' & _ & HTransport).
  destruct HTransport as (_ & HRuntimeTransport & _).
  exists store'.
  eapply HRuntimeTransport.
  exact HStoreRuntime.
Qed.

Theorem checked_computation_store_runtime_context :
  forall gamma omega heap env rho expr ty eff phi heap' v,
    CheckedRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr ty eff ->
    ComputationEvaluation heap env rho expr phi heap' v ->
    CheckedStoreRuntimeContext gamma omega heap' env rho.
Proof.
  intros gamma omega heap env rho expr ty eff phi heap' v
    HContext HCheckedExpr HComp.
  pose proof HContext as HContextOriginal.
  destruct HContextOriginal as (_ & _ & _ & _ & _ & HRho & _).
  destruct
    (checked_computation_store_runtime_shape
      gamma omega heap env rho expr ty eff phi heap' v
      HContext HCheckedExpr HComp)
    as (store' & HStoreRuntime).
  split.
  - exists store'. exact HStoreRuntime.
  - exact HRho.
Qed.

Theorem checked_store_computation_store_runtime_shape :
  forall gamma omega heap env rho expr ty eff phi heap' v,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr ty eff ->
    ComputationEvaluation heap env rho expr phi heap' v ->
    exists store',
      NStoreResolvedRuntimeShape heap' store' env rho gamma.
Proof.
  intros gamma omega heap env rho expr ty eff phi heap' v
    HContext HCheckedExpr HComp.
  destruct HContext as (HStoreContext & HRho).
  destruct HStoreContext as (store & HStoreRuntime).
  pose proof
    (NCheckedTcExp_ty_wf
      gamma omega expr ty eff HCheckedExpr)
    as HTyWF.
  destruct
    (NResolveTy_exists 0 omega rho ty HRho HTyWF)
    as (ty_res & HResolve).
  assert
    (HInitial :
      NStoreResolvedStateShape store
        (NInitialState heap env rho expr)
        ty_res).
  {
    eapply NStoreResolvedStateShape_initial; eauto.
  }
  unfold ComputationEvaluation in HComp.
  destruct
    (NSteps_store_resolved_state_preservation_with_transport
      (NInitialState heap env rho expr)
      phi (StDone heap' v) store ty_res
      HComp HInitial)
    as (store' & _ & HTransport).
  destruct HTransport as (_ & HRuntimeTransport & _).
  exists store'.
  eapply HRuntimeTransport.
  exact HStoreRuntime.
Qed.

Theorem checked_store_computation_store_runtime_context :
  forall gamma omega heap env rho expr ty eff phi heap' v,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr ty eff ->
    ComputationEvaluation heap env rho expr phi heap' v ->
    CheckedStoreRuntimeContext gamma omega heap' env rho.
Proof.
  intros gamma omega heap env rho expr ty eff phi heap' v
    HContext HCheckedExpr HComp.
  pose proof HContext as HContextOriginal.
  destruct HContextOriginal as (_ & HRho).
  destruct
    (checked_store_computation_store_runtime_shape
      gamma omega heap env rho expr ty eff phi heap' v
      HContext HCheckedExpr HComp)
    as (store' & HStoreRuntime).
  split.
  - exists store'. exact HStoreRuntime.
  - exact HRho.
Qed.

Theorem checked_sequential_computations_store_value_shapes :
  forall gamma omega heap env rho
    expr1 ty1 eff1 phi1 heap1 v1
    expr2 ty2 eff2 phi2 heap2 v2,
    CheckedRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr1 ty1 eff1 ->
    NCheckedTcExp gamma omega expr2 ty2 eff2 ->
    ComputationEvaluation heap env rho expr1 phi1 heap1 v1 ->
    ComputationEvaluation heap1 env rho expr2 phi2 heap2 v2 ->
    exists store2 ty1_res ty2_res,
      NResolveTy rho ty1 ty1_res /\
      NResolveTy rho ty2 ty2_res /\
      NStoreKeysBoundedByHeap heap2 store2 /\
      NStoreResolvedHeapShape heap2 store2 /\
      NStoreResolvedValShape store2 v1 ty1_res /\
      NStoreResolvedValShape store2 v2 ty2_res.
Proof.
  intros gamma omega heap env rho
    expr1 ty1 eff1 phi1 heap1 v1
    expr2 ty2 eff2 phi2 heap2 v2
    HContext HChecked1 HChecked2 HComp1 HComp2.
  destruct HContext as
    (_ & _ & _ & _ & HStoreContext & HRho & _).
  destruct HStoreContext as (store0 & HStoreRuntime0).
  pose proof
    (NCheckedTcExp_ty_wf
      gamma omega expr1 ty1 eff1 HChecked1)
    as HTyWF1.
  destruct
    (NResolveTy_exists 0 omega rho ty1 HRho HTyWF1)
    as (ty1_res & HResolve1).
  assert
    (HInitial1 :
      NStoreResolvedStateShape store0
        (NInitialState heap env rho expr1)
        ty1_res).
  {
    eapply NStoreResolvedStateShape_initial; eauto.
  }
  unfold ComputationEvaluation in HComp1.
  destruct
    (NSteps_store_resolved_state_preservation_with_transport
      (NInitialState heap env rho expr1)
      phi1 (StDone heap1 v1) store0 ty1_res
      HComp1 HInitial1)
    as (store1 & HDone1 & HTransport1).
  destruct HTransport1 as (_ & HRuntimeTransport1 & _).
  pose proof
    (HRuntimeTransport1 env rho gamma HStoreRuntime0)
    as HStoreRuntime1.
  pose proof
    (NCheckedTcExp_ty_wf
      gamma omega expr2 ty2 eff2 HChecked2)
    as HTyWF2.
  destruct
    (NResolveTy_exists 0 omega rho ty2 HRho HTyWF2)
    as (ty2_res & HResolve2).
  assert
    (HInitial2 :
      NStoreResolvedStateShape store1
        (NInitialState heap1 env rho expr2)
        ty2_res).
  {
    eapply NStoreResolvedStateShape_initial; eauto.
  }
  unfold ComputationEvaluation in HComp2.
  destruct
    (NSteps_store_resolved_state_preservation_with_transport
      (NInitialState heap1 env rho expr2)
      phi2 (StDone heap2 v2) store1 ty2_res
      HComp2 HInitial2)
    as (store2 & HDone2 & HTransport2).
  destruct
    (NStoreResolvedStateShape_done_inv
      store2 heap2 v2 ty2_res HDone2)
    as (HBounded2 & HHeap2 & HVal2).
  destruct HTransport2 as (HStateTransport2 & _ & _).
  specialize
    (HStateTransport2
      (StDone heap1 v1)
      ty1_res
      eq_refl
      HDone1)
    as HDone1Final.
  simpl in HDone1Final.
  destruct
    (NStoreResolvedStateShape_done_inv
      store2 heap2 v1 ty1_res HDone1Final)
    as (_ & _ & HVal1).
  exists store2, ty1_res, ty2_res.
  split; [exact HResolve1 |].
  split; [exact HResolve2 |].
  split; [exact HBounded2 |].
  split; [exact HHeap2 |].
  split; assumption.
Qed.

Theorem checked_store_sequential_computations_store_value_shapes :
  forall gamma omega heap env rho
    expr1 ty1 eff1 phi1 heap1 v1
    expr2 ty2 eff2 phi2 heap2 v2,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr1 ty1 eff1 ->
    NCheckedTcExp gamma omega expr2 ty2 eff2 ->
    ComputationEvaluation heap env rho expr1 phi1 heap1 v1 ->
    ComputationEvaluation heap1 env rho expr2 phi2 heap2 v2 ->
    exists store2 ty1_res ty2_res,
      NResolveTy rho ty1 ty1_res /\
      NResolveTy rho ty2 ty2_res /\
      NStoreKeysBoundedByHeap heap2 store2 /\
      NStoreResolvedHeapShape heap2 store2 /\
      NStoreResolvedValShape store2 v1 ty1_res /\
      NStoreResolvedValShape store2 v2 ty2_res.
Proof.
  intros gamma omega heap env rho
    expr1 ty1 eff1 phi1 heap1 v1
    expr2 ty2 eff2 phi2 heap2 v2
    HContext HChecked1 HChecked2 HComp1 HComp2.
  destruct HContext as (HStoreContext & HRho).
  destruct HStoreContext as (store0 & HStoreRuntime0).
  pose proof
    (NCheckedTcExp_ty_wf
      gamma omega expr1 ty1 eff1 HChecked1)
    as HTyWF1.
  destruct
    (NResolveTy_exists 0 omega rho ty1 HRho HTyWF1)
    as (ty1_res & HResolve1).
  assert
    (HInitial1 :
      NStoreResolvedStateShape store0
        (NInitialState heap env rho expr1)
        ty1_res).
  {
    eapply NStoreResolvedStateShape_initial; eauto.
  }
  unfold ComputationEvaluation in HComp1.
  destruct
    (NSteps_store_resolved_state_preservation_with_transport
      (NInitialState heap env rho expr1)
      phi1 (StDone heap1 v1) store0 ty1_res
      HComp1 HInitial1)
    as (store1 & HDone1 & HTransport1).
  destruct HTransport1 as (_ & HRuntimeTransport1 & _).
  pose proof
    (HRuntimeTransport1 env rho gamma HStoreRuntime0)
    as HStoreRuntime1.
  pose proof
    (NCheckedTcExp_ty_wf
      gamma omega expr2 ty2 eff2 HChecked2)
    as HTyWF2.
  destruct
    (NResolveTy_exists 0 omega rho ty2 HRho HTyWF2)
    as (ty2_res & HResolve2).
  assert
    (HInitial2 :
      NStoreResolvedStateShape store1
        (NInitialState heap1 env rho expr2)
        ty2_res).
  {
    eapply NStoreResolvedStateShape_initial; eauto.
  }
  unfold ComputationEvaluation in HComp2.
  destruct
    (NSteps_store_resolved_state_preservation_with_transport
      (NInitialState heap1 env rho expr2)
      phi2 (StDone heap2 v2) store1 ty2_res
      HComp2 HInitial2)
    as (store2 & HDone2 & HTransport2).
  destruct
    (NStoreResolvedStateShape_done_inv
      store2 heap2 v2 ty2_res HDone2)
    as (HBounded2 & HHeap2 & HVal2).
  destruct HTransport2 as (HStateTransport2 & _ & _).
  specialize
    (HStateTransport2
      (StDone heap1 v1)
      ty1_res
      eq_refl
      HDone1)
    as HDone1Final.
  simpl in HDone1Final.
  destruct
    (NStoreResolvedStateShape_done_inv
      store2 heap2 v1 ty1_res HDone1Final)
    as (_ & _ & HVal1).
  exists store2, ty1_res, ty2_res.
  split; [exact HResolve1 |].
  split; [exact HResolve2 |].
  split; [exact HBounded2 |].
  split; [exact HHeap2 |].
  split; assumption.
Qed.

Definition CheckedSummaryTraceSoundnessFor
    (gamma : NCtx) (omega : NRgnCtx)
    (heap : Heap) (env : NEnv) (rho : Rho) : Prop :=
  forall summary_expr eff phi_summary heap_summary theta eff_res,
    NCheckedTcExp gamma omega summary_expr TyEffect eff ->
    SummaryEvaluation heap env rho summary_expr
      phi_summary heap_summary theta ->
    NResolveStaticEffect rho eff eff_res ->
    TraceCoveredByStaticEffect phi_summary eff_res.

Definition CheckedSummaryTraceSoundnessGoal : Prop :=
  forall gamma omega heap env rho,
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho.

Definition CheckedStoreSummaryTraceSoundnessGoal : Prop :=
  forall gamma omega heap env rho,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho.

Lemma CheckedSummaryTraceSoundnessFor_from_goal :
  forall gamma omega heap env rho,
    CheckedSummaryTraceSoundnessGoal ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho.
Proof.
  intros gamma omega heap env rho HGoal HContext.
  unfold CheckedSummaryTraceSoundnessGoal in HGoal.
  eapply HGoal; eauto.
Qed.

Lemma CheckedSummaryTraceSoundnessFor_from_store_goal :
  forall gamma omega heap env rho,
    CheckedStoreSummaryTraceSoundnessGoal ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho.
Proof.
  intros gamma omega heap env rho HGoal HContext.
  unfold CheckedStoreSummaryTraceSoundnessGoal in HGoal.
  eapply HGoal; eauto.
Qed.

Definition CheckedComputationTraceSoundnessFor
    (gamma : NCtx) (omega : NRgnCtx)
    (heap : Heap) (env : NEnv) (rho : Rho) : Prop :=
  forall expr ty eff phi heap' v eff_res,
    NCheckedTcExp gamma omega expr ty eff ->
    ComputationEvaluation heap env rho expr phi heap' v ->
    NResolveStaticEffect rho eff eff_res ->
    TraceCoveredByStaticEffect phi eff_res.

Definition CheckedComputationTraceSoundnessGoal : Prop :=
  forall gamma omega heap env rho,
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho.

Definition CheckedStoreComputationTraceSoundnessGoal : Prop :=
  forall gamma omega heap env rho,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho.

Theorem checked_store_summary_trace_soundness_from_computation :
  CheckedStoreComputationTraceSoundnessGoal ->
  CheckedStoreSummaryTraceSoundnessGoal.
Proof.
  unfold CheckedStoreComputationTraceSoundnessGoal,
    CheckedStoreSummaryTraceSoundnessGoal,
    CheckedComputationTraceSoundnessFor,
    CheckedSummaryTraceSoundnessFor.
  intros HComputationTrace gamma omega heap env rho HContext
    summary_expr eff phi_summary heap_summary theta eff_res
    HChecked HSummary HResolve.
  eapply HComputationTrace.
  - exact HContext.
  - exact HChecked.
  - unfold ComputationEvaluation, SummaryEvaluation in *.
    exact HSummary.
  - exact HResolve.
Qed.

Lemma CheckedComputationTraceSoundnessFor_from_goal :
  forall gamma omega heap env rho,
    CheckedComputationTraceSoundnessGoal ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho.
Proof.
  intros gamma omega heap env rho HGoal HContext.
  unfold CheckedComputationTraceSoundnessGoal in HGoal.
  eapply HGoal; eauto.
Qed.

Lemma CheckedComputationTraceSoundnessFor_from_store_goal :
  forall gamma omega heap env rho,
    CheckedStoreComputationTraceSoundnessGoal ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho.
Proof.
  intros gamma omega heap env rho HGoal HContext.
  unfold CheckedStoreComputationTraceSoundnessGoal in HGoal.
  eapply HGoal; eauto.
Qed.

Theorem summary_static_heap_neutral :
  forall heap env rho summary_expr phi_summary heap_summary theta
    eff eff_res,
    SummaryEvaluation heap env rho summary_expr
      phi_summary heap_summary theta ->
    NResolveStaticEffect rho eff eff_res ->
    TraceCoveredByStaticEffect phi_summary eff_res ->
    static_heap_neutral eff ->
    heap_summary = heap /\ HeapNeutralTrace phi_summary.
Proof.
  intros heap env rho summary_expr phi_summary heap_summary theta
    eff eff_res HSummary HResolve HCovered HStaticNeutral.
  pose proof
    (TraceCoveredByResolvedStaticEffect_heap_neutral
      rho phi_summary eff eff_res
      HResolve HCovered HStaticNeutral)
    as HTraceNeutral.
  split.
  - unfold SummaryEvaluation in HSummary.
    eapply NSteps_heap_neutral_initial_heap; eauto.
  - exact HTraceNeutral.
Qed.

Definition CountedComputationEvaluation (n : nat)
    (heap : Heap) (env : NEnv) (rho : Rho)
    (expr : NExpr) (phi : Trace) (heap' : Heap) (v : NVal) : Prop :=
  NStepsN n
    (NInitialState heap env rho expr)
    phi
    (StDone heap' v).

Lemma counted_silent_initial_return_trace_nil :
  forall n heap env rho expr v0 phi heap_final v_final,
    NStep
      (NInitialState heap env rho expr)
      LSilent
      (StReturn heap v0 KDone) ->
    CountedComputationEvaluation n heap env rho expr
      phi heap_final v_final ->
    phi = nil.
Proof.
  intros n heap env rho expr v0 phi heap_final v_final
    HStep HComp.
  unfold CountedComputationEvaluation in HComp.
  destruct
    (NStepsN_known_first_step_terminal_inv
      n
      (NInitialState heap env rho expr)
      LSilent
      (StReturn heap v0 KDone)
      phi
      heap_final
      v_final
      HStep
      HComp)
    as (n_tail & phi_tail & _ & HReturn & HTrace).
  destruct
    (NSteps_return_done_inv
      heap v0 phi_tail heap_final v_final
      (NStepsN_to_NSteps
        n_tail
        (StReturn heap v0 KDone)
        phi_tail
        (StDone heap_final v_final)
        HReturn))
    as (_ & _ & HPhiTail).
  subst phi_tail.
  simpl in HTrace.
  exact HTrace.
Qed.

Lemma counted_silent_initial_return_covered :
  forall n heap env rho expr v0 phi heap_final v_final theta,
    NStep
      (NInitialState heap env rho expr)
      LSilent
      (StReturn heap v0 KDone) ->
    CountedComputationEvaluation n heap env rho expr
      phi heap_final v_final ->
    TraceCoveredBySummary phi theta.
Proof.
  intros n heap env rho expr v0 phi heap_final v_final theta
    HStep HComp.
  pose proof
    (counted_silent_initial_return_trace_nil
      n heap env rho expr v0 phi heap_final v_final HStep HComp)
    as HPhi.
  subst phi.
  apply trace_covered_nil.
Qed.

Theorem checked_counted_computation_store_runtime_context :
  forall n gamma omega heap env rho expr ty eff phi heap' v,
    CheckedRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr ty eff ->
    CountedComputationEvaluation n heap env rho expr phi heap' v ->
    CheckedStoreRuntimeContext gamma omega heap' env rho.
Proof.
  intros n gamma omega heap env rho expr ty eff phi heap' v
    HContext HCheckedExpr HComp.
  eapply checked_computation_store_runtime_context; eauto.
  unfold ComputationEvaluation, CountedComputationEvaluation in *.
  eapply NStepsN_to_NSteps.
  exact HComp.
Qed.

Theorem checked_store_counted_computation_store_runtime_context :
  forall n gamma omega heap env rho expr ty eff phi heap' v,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr ty eff ->
    CountedComputationEvaluation n heap env rho expr phi heap' v ->
    CheckedStoreRuntimeContext gamma omega heap' env rho.
Proof.
  intros n gamma omega heap env rho expr ty eff phi heap' v
    HContext HCheckedExpr HComp.
  eapply checked_store_computation_store_runtime_context; eauto.
  unfold ComputationEvaluation, CountedComputationEvaluation in *.
  eapply NStepsN_to_NSteps.
  exact HComp.
Qed.

Theorem checked_bounded_store_counted_computation_context :
  forall n gamma omega heap env rho expr ty eff phi heap' v,
    CheckedBoundedStoreRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr ty eff ->
    CountedComputationEvaluation n heap env rho expr phi heap' v ->
    CheckedBoundedStoreRuntimeContext gamma omega heap' env rho.
Proof.
  intros n gamma omega heap env rho expr ty eff phi heap' v
    HContext HCheckedExpr HComp.
  destruct HContext as (HStoreContext & HBounded).
  split.
  - eapply checked_store_counted_computation_store_runtime_context;
      eauto.
  - unfold CountedComputationEvaluation in HComp.
    eapply
      (NStepsN_preserves_heap_bounded_aligned
        n
        (NInitialState heap env rho expr)
        phi
        (StDone heap' v));
      simpl; eauto.
Qed.

Lemma checked_counted_computation_trace_covered_by_static_effect :
  forall n gamma omega heap env rho expr ty eff phi heap' v eff_res,
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr ty eff ->
    CountedComputationEvaluation n heap env rho expr phi heap' v ->
    NResolveStaticEffect rho eff eff_res ->
    TraceCoveredByStaticEffect phi eff_res.
Proof.
  intros n gamma omega heap env rho expr ty eff phi heap' v eff_res
    HSound HChecked HComp HResolve.
  unfold CheckedComputationTraceSoundnessFor in HSound.
  eapply HSound; eauto.
  unfold ComputationEvaluation, CountedComputationEvaluation in *.
  eapply NStepsN_to_NSteps.
  exact HComp.
Qed.

Lemma checked_store_counted_computation_read_only :
  forall n gamma omega heap env rho expr ty eff phi heap' v,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr ty eff ->
    static_readonly eff ->
    CountedComputationEvaluation n heap env rho expr phi heap' v ->
    ReadOnlyTrace phi.
Proof.
  intros n gamma omega heap env rho expr ty eff phi heap' v
    HContext HSound HChecked HReadOnly HComp.
  pose proof
    (NCheckedTcExp_eff_wf
      gamma omega expr ty eff HChecked)
    as HEffWF.
  destruct
    (NResolveStaticEffect_exists
      0 omega rho eff
      (CheckedStoreRuntimeContext_to_rho_models
        gamma omega heap env rho HContext)
      HEffWF)
    as (eff_res & HResolve).
  eapply TraceCoveredByStaticEffect_read_only.
  - eapply checked_counted_computation_trace_covered_by_static_effect;
      eauto.
  - eapply NResolveStaticEffect_static_readonly; eauto.
Qed.

Lemma checked_store_counted_computation_heap_neutral :
  forall n gamma omega heap env rho expr ty eff phi heap' v,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedComputationTraceSoundnessFor gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr ty eff ->
    static_heap_neutral eff ->
    CountedComputationEvaluation n heap env rho expr phi heap' v ->
    heap' = heap /\ HeapNeutralTrace phi.
Proof.
  intros n gamma omega heap env rho expr ty eff phi heap' v
    HContext HSound HChecked HHeapNeutral HComp.
  pose proof
    (NCheckedTcExp_eff_wf
      gamma omega expr ty eff HChecked)
    as HEffWF.
  destruct
    (NResolveStaticEffect_exists
      0 omega rho eff
      (CheckedStoreRuntimeContext_to_rho_models
        gamma omega heap env rho HContext)
      HEffWF)
    as (eff_res & HResolve).
  pose proof
    (checked_counted_computation_trace_covered_by_static_effect
      n gamma omega heap env rho expr ty eff phi heap' v eff_res
      HSound HChecked HComp HResolve)
    as HCovered.
  pose proof
    (TraceCoveredByResolvedStaticEffect_heap_neutral
      rho phi eff eff_res HResolve HCovered HHeapNeutral)
    as HTraceNeutral.
  split.
  - eapply NSteps_heap_neutral_initial_heap.
    + unfold CountedComputationEvaluation in HComp.
      eapply NStepsN_to_NSteps.
      exact HComp.
    + exact HTraceNeutral.
  - exact HTraceNeutral.
Qed.

Definition StructuredSummaryEvaluation
    (heap : Heap) (env : NEnv) (rho : Rho)
    (summary_expr : NExpr) (view_summary : NTraceView)
    (heap_summary : Heap) (theta : Summary) : Prop :=
  NStepsView
    (NInitialState heap env rho summary_expr)
    view_summary
    (StDone heap_summary (VSummary theta)).

Definition StructuredComputationEvaluation
    (heap : Heap) (env : NEnv) (rho : Rho)
    (expr : NExpr) (view : NTraceView)
    (heap' : Heap) (v : NVal) : Prop :=
  NStepsView
    (NInitialState heap env rho expr)
    view
    (StDone heap' v).

Theorem checked_summary_store_preservation :
  forall gamma omega heap env rho summary_expr
    phi_summary heap_summary theta,
    CheckedInitialRuntimeTyping gamma omega heap env rho summary_expr ->
    SummaryEvaluation heap env rho summary_expr
      phi_summary heap_summary theta ->
    exists store ty_res,
      NStoreResolvedStateShape store
        (StDone heap_summary (VSummary theta))
        ty_res.
Proof.
  intros gamma omega heap env rho summary_expr
    phi_summary heap_summary theta HRuntime HSummary.
  unfold SummaryEvaluation in HSummary.
  eapply checked_initial_steps_store_preservation; eauto.
Qed.

Theorem checked_summary_store_value_shape :
  forall gamma omega heap env rho summary_expr
    phi_summary heap_summary theta,
    CheckedInitialRuntimeTyping gamma omega heap env rho summary_expr ->
    SummaryEvaluation heap env rho summary_expr
      phi_summary heap_summary theta ->
    exists store,
      NStoreKeysBoundedByHeap heap_summary store /\
      NStoreResolvedHeapShape heap_summary store /\
      NStoreResolvedValShape store (VSummary theta) TyEffect.
Proof.
  intros gamma omega heap env rho summary_expr
    phi_summary heap_summary theta HRuntime HSummary.
  destruct
    (checked_summary_store_preservation
      gamma omega heap env rho summary_expr
      phi_summary heap_summary theta HRuntime HSummary)
    as (store & ty_res & HState).
  destruct
    (NStoreResolvedStateShape_done_summary_inv
      store heap_summary theta ty_res HState)
    as (_ & HBounded & HHeap).
  exists store.
  split; [exact HBounded |].
  split; [exact HHeap |].
  exact (NSRVS_Summary store theta).
Qed.

Theorem checked_computation_store_preservation :
  forall gamma omega heap env rho expr phi heap' v,
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    ComputationEvaluation heap env rho expr phi heap' v ->
    exists store ty_res,
      NStoreResolvedStateShape store (StDone heap' v) ty_res.
Proof.
  intros gamma omega heap env rho expr phi heap' v
    HRuntime HComp.
  unfold ComputationEvaluation in HComp.
  eapply checked_initial_steps_store_preservation; eauto.
Qed.

Theorem checked_computation_store_value_shape :
  forall gamma omega heap env rho expr phi heap' v,
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    ComputationEvaluation heap env rho expr phi heap' v ->
    exists store ty_res,
      NStoreKeysBoundedByHeap heap' store /\
      NStoreResolvedHeapShape heap' store /\
      NStoreResolvedValShape store v ty_res.
Proof.
  intros gamma omega heap env rho expr phi heap' v
    HRuntime HComp.
  destruct
    (checked_computation_store_preservation
      gamma omega heap env rho expr phi heap' v HRuntime HComp)
    as (store & ty_res & HState).
  destruct
    (NStoreResolvedStateShape_done_inv store heap' v ty_res HState)
    as (HBounded & HHeap & HVal).
  exists store, ty_res.
  split; [exact HBounded |].
  split; [exact HHeap |].
  exact HVal.
Qed.

Theorem checked_pair_computation_store_value_shape :
  forall gamma omega heap env rho expr phi heap' v1 v2,
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    ComputationEvaluation heap env rho expr phi heap' (VPair v1 v2) ->
    exists store ty1 ty2,
      NStoreKeysBoundedByHeap heap' store /\
      NStoreResolvedHeapShape heap' store /\
      NStoreResolvedValShape store v1 ty1 /\
      NStoreResolvedValShape store v2 ty2.
Proof.
  intros gamma omega heap env rho expr phi heap' v1 v2
    HRuntime HComp.
  destruct
    (checked_computation_store_preservation
      gamma omega heap env rho expr phi heap' (VPair v1 v2)
      HRuntime HComp)
    as (store & ty_res & HState).
  destruct
    (NStoreResolvedStateShape_done_pair_inv
      store heap' v1 v2 ty_res HState)
    as (ty1 & ty2 & _ & HBounded & HHeap & HVal1 & HVal2).
  exists store, ty1, ty2.
  split; [exact HBounded |].
  split; [exact HHeap |].
  split; assumption.
Qed.

Theorem checked_counted_computation_store_preservation :
  forall n gamma omega heap env rho expr phi heap' v,
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    CountedComputationEvaluation n heap env rho expr phi heap' v ->
    exists store ty_res,
      NStoreResolvedStateShape store (StDone heap' v) ty_res.
Proof.
  intros n gamma omega heap env rho expr phi heap' v
    HRuntime HComp.
  unfold CountedComputationEvaluation in HComp.
  eapply checked_initial_stepsN_store_preservation; eauto.
Qed.

Theorem checked_counted_computation_store_value_shape :
  forall n gamma omega heap env rho expr phi heap' v,
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    CountedComputationEvaluation n heap env rho expr phi heap' v ->
    exists store ty_res,
      NStoreKeysBoundedByHeap heap' store /\
      NStoreResolvedHeapShape heap' store /\
      NStoreResolvedValShape store v ty_res.
Proof.
  intros n gamma omega heap env rho expr phi heap' v
    HRuntime HComp.
  destruct
    (checked_counted_computation_store_preservation
      n gamma omega heap env rho expr phi heap' v HRuntime HComp)
    as (store & ty_res & HState).
  destruct
    (NStoreResolvedStateShape_done_inv store heap' v ty_res HState)
    as (HBounded & HHeap & HVal).
  exists store, ty_res.
  split; [exact HBounded |].
  split; [exact HHeap |].
  exact HVal.
Qed.

Theorem checked_store_counted_computation_store_value_shape :
  forall n gamma omega heap env rho expr ty eff phi heap' v,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr ty eff ->
    CountedComputationEvaluation n heap env rho expr phi heap' v ->
    exists store ty_res,
      NStoreKeysBoundedByHeap heap' store /\
      NStoreResolvedHeapShape heap' store /\
      NStoreResolvedValShape store v ty_res.
Proof.
  intros n gamma omega heap env rho expr ty eff phi heap' v
    HContext HChecked HComp.
  destruct HContext as ((store & HRuntime) & HRho).
  pose proof
    (NCheckedTcExp_ty_wf gamma omega expr ty eff HChecked)
    as HTyWF.
  destruct
    (NResolveTy_exists 0 omega rho ty HRho HTyWF)
    as (ty_res & HResolve).
  assert
    (HInitial :
      NStoreResolvedStateShape store
        (NInitialState heap env rho expr)
        ty_res).
  {
    eapply NStoreResolvedStateShape_initial; eauto.
  }
  unfold CountedComputationEvaluation in HComp.
  destruct
    (NStepsN_store_resolved_state_preservation
      n
      (NInitialState heap env rho expr)
      phi
      (StDone heap' v)
      store
      ty_res
      HComp
      HInitial)
    as (store' & HFinal).
  destruct
    (NStoreResolvedStateShape_done_inv
      store' heap' v ty_res HFinal)
    as (HBounded & HHeap & HVal).
  exists store', ty_res.
  split; [exact HBounded |].
  split; [exact HHeap |].
  exact HVal.
Qed.

Theorem checked_store_counted_computation_store_value_shape_resolved :
  forall n gamma omega heap env rho expr ty eff phi heap' v,
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    NCheckedTcExp gamma omega expr ty eff ->
    CountedComputationEvaluation n heap env rho expr phi heap' v ->
    exists store ty_res,
      NResolveTy rho ty ty_res /\
      NStoreKeysBoundedByHeap heap' store /\
      NStoreResolvedHeapShape heap' store /\
      NStoreResolvedValShape store v ty_res.
Proof.
  intros n gamma omega heap env rho expr ty eff phi heap' v
    HContext HChecked HComp.
  destruct HContext as ((store & HRuntime) & HRho).
  pose proof
    (NCheckedTcExp_ty_wf gamma omega expr ty eff HChecked)
    as HTyWF.
  destruct
    (NResolveTy_exists 0 omega rho ty HRho HTyWF)
    as (ty_res & HResolve).
  assert
    (HInitial :
      NStoreResolvedStateShape store
        (NInitialState heap env rho expr)
        ty_res).
  {
    eapply NStoreResolvedStateShape_initial; eauto.
  }
  unfold CountedComputationEvaluation in HComp.
  destruct
    (NStepsN_store_resolved_state_preservation
      n
      (NInitialState heap env rho expr)
      phi
      (StDone heap' v)
      store
      ty_res
      HComp
      HInitial)
    as (store' & HFinal).
  destruct
    (NStoreResolvedStateShape_done_inv
      store' heap' v ty_res HFinal)
    as (HBounded & HHeap & HVal).
  exists store', ty_res.
  split; [exact HResolve |].
  split; [exact HBounded |].
  split; [exact HHeap |].
  exact HVal.
Qed.

Theorem checked_structured_summary_store_preservation :
  forall gamma omega heap env rho summary_expr
    view_summary heap_summary theta,
    CheckedInitialRuntimeTyping gamma omega heap env rho summary_expr ->
    StructuredSummaryEvaluation heap env rho summary_expr
      view_summary heap_summary theta ->
    exists store ty_res,
      NStoreResolvedStateShape store
        (StDone heap_summary (VSummary theta))
        ty_res.
Proof.
  intros gamma omega heap env rho summary_expr
    view_summary heap_summary theta HRuntime HSummary.
  unfold StructuredSummaryEvaluation in HSummary.
  eapply checked_initial_steps_view_store_preservation; eauto.
Qed.

Theorem checked_structured_summary_store_value_shape :
  forall gamma omega heap env rho summary_expr
    view_summary heap_summary theta,
    CheckedInitialRuntimeTyping gamma omega heap env rho summary_expr ->
    StructuredSummaryEvaluation heap env rho summary_expr
      view_summary heap_summary theta ->
    exists store,
      NStoreKeysBoundedByHeap heap_summary store /\
      NStoreResolvedHeapShape heap_summary store /\
      NStoreResolvedValShape store (VSummary theta) TyEffect.
Proof.
  intros gamma omega heap env rho summary_expr
    view_summary heap_summary theta HRuntime HSummary.
  destruct
    (checked_structured_summary_store_preservation
      gamma omega heap env rho summary_expr
      view_summary heap_summary theta HRuntime HSummary)
    as (store & ty_res & HState).
  destruct
    (NStoreResolvedStateShape_done_summary_inv
      store heap_summary theta ty_res HState)
    as (_ & HBounded & HHeap).
  exists store.
  split; [exact HBounded |].
  split; [exact HHeap |].
  exact (NSRVS_Summary store theta).
Qed.

Theorem checked_structured_computation_store_preservation :
  forall gamma omega heap env rho expr view heap' v,
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    StructuredComputationEvaluation heap env rho expr view heap' v ->
    exists store ty_res,
      NStoreResolvedStateShape store (StDone heap' v) ty_res.
Proof.
  intros gamma omega heap env rho expr view heap' v
    HRuntime HComp.
  unfold StructuredComputationEvaluation in HComp.
  eapply checked_initial_steps_view_store_preservation; eauto.
Qed.

Theorem checked_structured_computation_store_value_shape :
  forall gamma omega heap env rho expr view heap' v,
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    StructuredComputationEvaluation heap env rho expr view heap' v ->
    exists store ty_res,
      NStoreKeysBoundedByHeap heap' store /\
      NStoreResolvedHeapShape heap' store /\
      NStoreResolvedValShape store v ty_res.
Proof.
  intros gamma omega heap env rho expr view heap' v
    HRuntime HComp.
  destruct
    (checked_structured_computation_store_preservation
      gamma omega heap env rho expr view heap' v HRuntime HComp)
    as (store & ty_res & HState).
  destruct
    (NStoreResolvedStateShape_done_inv store heap' v ty_res HState)
    as (HBounded & HHeap & HVal).
  exists store, ty_res.
  split; [exact HBounded |].
  split; [exact HHeap |].
  exact HVal.
Qed.

Definition CheckedTerminalCorrectnessGoal : Prop :=
  forall gamma omega heap env rho expr summary_expr phi heap' v
    phi_summary heap_summary theta,
    NCheckedBackTriangle gamma omega expr summary_expr ->
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    CheckedInitialRuntimeTyping gamma omega heap env rho summary_expr ->
    ComputationEvaluation heap env rho expr phi heap' v ->
    SummaryEvaluation heap env rho summary_expr
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.

Definition CheckedStructuredTerminalCorrectnessGoal : Prop :=
  forall gamma omega heap env rho expr summary_expr view heap' v
    view_summary heap_summary theta,
    NCheckedBackTriangle gamma omega expr summary_expr ->
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    CheckedInitialRuntimeTyping gamma omega heap env rho summary_expr ->
    StructuredComputationEvaluation heap env rho expr view heap' v ->
    StructuredSummaryEvaluation heap env rho summary_expr
      view_summary heap_summary theta ->
    TraceViewCoveredBySummary view theta.

Definition CheckedSmallStepCorrectnessBelow (n : nat) : Prop :=
  forall n_child gamma omega heap env rho expr summary_expr phi heap' v
    phi_summary heap_summary theta,
    n_child < n ->
    NCheckedBackTriangle gamma omega expr summary_expr ->
    CheckedInitialRuntimeTyping gamma omega heap env rho expr ->
    CheckedInitialRuntimeTyping gamma omega heap env rho summary_expr ->
    CountedComputationEvaluation n_child heap env rho expr phi heap' v ->
    SummaryEvaluation heap env rho summary_expr
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.

Definition CheckedContextTerminalCorrectnessGoal : Prop :=
  forall gamma omega heap env rho expr summary_expr phi heap' v
    phi_summary heap_summary theta,
    NCheckedBackTriangle gamma omega expr summary_expr ->
    CheckedRuntimeContext gamma omega heap env rho ->
    ComputationEvaluation heap env rho expr phi heap' v ->
    SummaryEvaluation heap env rho summary_expr
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.

Definition CheckedContextStructuredTerminalCorrectnessGoal : Prop :=
  forall gamma omega heap env rho expr summary_expr view heap' v
    view_summary heap_summary theta,
    NCheckedBackTriangle gamma omega expr summary_expr ->
    CheckedRuntimeContext gamma omega heap env rho ->
    StructuredComputationEvaluation heap env rho expr view heap' v ->
    StructuredSummaryEvaluation heap env rho summary_expr
      view_summary heap_summary theta ->
    TraceViewCoveredBySummary view theta.

Definition CheckedContextSmallStepCorrectnessBelow (n : nat) : Prop :=
  forall n_child gamma omega heap env rho expr summary_expr phi heap' v
    phi_summary heap_summary theta,
    n_child < n ->
    NCheckedBackTriangle gamma omega expr summary_expr ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CountedComputationEvaluation n_child heap env rho expr phi heap' v ->
    SummaryEvaluation heap env rho summary_expr
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.

Definition CheckedStoreContextSmallStepCorrectnessBelow (n : nat) : Prop :=
  forall n_child gamma omega heap env rho expr summary_expr phi heap' v
    phi_summary heap_summary theta,
    n_child < n ->
    NCheckedBackTriangle gamma omega expr summary_expr ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CountedComputationEvaluation n_child heap env rho expr phi heap' v ->
    SummaryEvaluation heap env rho summary_expr
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.

Definition CheckedContextSummarySmallStepCorrectnessBelow (n : nat) : Prop :=
  forall n_child gamma omega heap env rho expr summary_expr phi heap' v
    phi_summary heap_summary theta,
    n_child < n ->
    NCheckedBackTriangle gamma omega expr summary_expr ->
    CheckedRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n_child heap env rho expr phi heap' v ->
    SummaryEvaluation heap env rho summary_expr
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.

Definition CheckedStoreSummarySmallStepCorrectnessBelow (n : nat) : Prop :=
  forall n_child gamma omega heap env rho expr summary_expr phi heap' v
    phi_summary heap_summary theta,
    n_child < n ->
    NCheckedBackTriangle gamma omega expr summary_expr ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CheckedSummaryTraceSoundnessFor gamma omega heap env rho ->
    CountedComputationEvaluation n_child heap env rho expr phi heap' v ->
    SummaryEvaluation heap env rho summary_expr
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.

Definition CheckedStoreSummaryValueSoundnessBelow (n : nat) : Prop :=
  forall n_child gamma omega heap env rho expr summary_expr eff
    phi heap_summary theta,
    n_child < n ->
    NCheckedBackTriangle gamma omega expr summary_expr ->
    NCheckedTcExp gamma omega summary_expr TyEffect eff ->
    CheckedStoreRuntimeContext gamma omega heap env rho ->
    CountedComputationEvaluation n_child heap env rho
      summary_expr phi heap_summary (VSummary theta) ->
    TraceCoveredBySummary phi theta.

Lemma CheckedContextSmallStepCorrectnessBelow_from_summary :
  forall n,
    CheckedContextSummarySmallStepCorrectnessBelow n ->
    CheckedSummaryTraceSoundnessGoal ->
    CheckedContextSmallStepCorrectnessBelow n.
Proof.
  unfold CheckedContextSummarySmallStepCorrectnessBelow,
    CheckedContextSmallStepCorrectnessBelow.
  intros n HBelow HSummaryTraceGoal n_child gamma omega heap env rho
    expr summary_expr phi heap' v phi_summary heap_summary theta
    HLt HBack HContext HComp HSummary.
  eapply HBelow; eauto.
Qed.

Lemma CheckedContextSummarySmallStepCorrectnessBelow_from_store_summary :
  forall n,
    CheckedStoreSummarySmallStepCorrectnessBelow n ->
    CheckedContextSummarySmallStepCorrectnessBelow n.
Proof.
  unfold CheckedStoreSummarySmallStepCorrectnessBelow,
    CheckedContextSummarySmallStepCorrectnessBelow.
  intros n HBelow n_child gamma omega heap env rho expr summary_expr
    phi heap' v phi_summary heap_summary theta HLt HBack HContext
    HSummaryTraceSound HComp HSummary.
  eapply HBelow; eauto using CheckedRuntimeContext_to_store_context.
Qed.

Lemma CheckedStoreSummarySmallStepCorrectnessBelow_forget_summary :
  forall n,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    CheckedStoreSummarySmallStepCorrectnessBelow n.
Proof.
  unfold CheckedStoreContextSmallStepCorrectnessBelow,
    CheckedStoreSummarySmallStepCorrectnessBelow.
  intros n HBelow n_child gamma omega heap env rho expr summary_expr
    phi heap' v phi_summary heap_summary theta HLt HBack HContext
    _HSummaryTraceSound HComp HSummary.
  eapply HBelow; eauto.
Qed.

Definition TerminalCorrectnessWithTop : Prop :=
  forall phi,
    TraceCoveredBySummary phi SummaryTop.

Theorem terminal_correctness_with_top :
  TerminalCorrectnessWithTop.
Proof.
  unfold TerminalCorrectnessWithTop.
  apply trace_covered_top.
Qed.

Theorem checked_terminal_correctness_from_below :
  (forall n, CheckedSmallStepCorrectnessBelow n) ->
  CheckedTerminalCorrectnessGoal.
Proof.
  unfold CheckedTerminalCorrectnessGoal.
  intros HBelow gamma omega heap env rho expr summary_expr phi heap' v
    phi_summary heap_summary theta HBack HRuntimeExpr HRuntimeSummary
    HComp HSummary.
  destruct
    (NSteps_to_NStepsN
      (NInitialState heap env rho expr)
      phi
      (StDone heap' v)
      HComp)
    as (n & HCompN).
  eapply (HBelow (S n) n); eauto; lia.
Qed.

Theorem checked_structured_terminal_correctness_from_terminal :
  CheckedTerminalCorrectnessGoal ->
  CheckedStructuredTerminalCorrectnessGoal.
Proof.
  unfold CheckedTerminalCorrectnessGoal,
    CheckedStructuredTerminalCorrectnessGoal.
  intros HTerminal gamma omega heap env rho expr summary_expr view heap' v
    view_summary heap_summary theta HBack HRuntimeExpr HRuntimeSummary
    HComp HSummary.
  unfold StructuredComputationEvaluation in HComp.
  unfold StructuredSummaryEvaluation in HSummary.
  unfold TraceViewCoveredBySummary.
  eapply HTerminal; eauto;
    eapply NStepsView_to_NSteps; eauto.
Qed.

Theorem checked_structured_terminal_correctness_from_below :
  (forall n, CheckedSmallStepCorrectnessBelow n) ->
  CheckedStructuredTerminalCorrectnessGoal.
Proof.
  intros HBelow.
  apply checked_structured_terminal_correctness_from_terminal.
  apply checked_terminal_correctness_from_below.
  exact HBelow.
Qed.

Theorem checked_context_terminal_correctness_from_checked :
  CheckedTerminalCorrectnessGoal ->
  CheckedContextTerminalCorrectnessGoal.
Proof.
  unfold CheckedTerminalCorrectnessGoal,
    CheckedContextTerminalCorrectnessGoal.
  intros HChecked gamma omega heap env rho expr summary_expr
    phi heap' v phi_summary heap_summary theta HBack HContext
    HComp HSummary.
  destruct
    (CheckedRuntimeContext_backtriangle_initials
      gamma omega heap env rho expr summary_expr HContext HBack)
    as (HRuntimeExpr & HRuntimeSummary).
  eapply HChecked; eauto.
Qed.

Theorem checked_context_structured_terminal_correctness_from_checked :
  CheckedStructuredTerminalCorrectnessGoal ->
  CheckedContextStructuredTerminalCorrectnessGoal.
Proof.
  unfold CheckedStructuredTerminalCorrectnessGoal,
    CheckedContextStructuredTerminalCorrectnessGoal.
  intros HChecked gamma omega heap env rho expr summary_expr
    view heap' v view_summary heap_summary theta HBack HContext
    HComp HSummary.
  destruct
    (CheckedRuntimeContext_backtriangle_initials
      gamma omega heap env rho expr summary_expr HContext HBack)
    as (HRuntimeExpr & HRuntimeSummary).
  eapply HChecked; eauto.
Qed.

Lemma CheckedContextSmallStepCorrectnessBelow_from_checked :
  forall n,
    CheckedSmallStepCorrectnessBelow n ->
    CheckedContextSmallStepCorrectnessBelow n.
Proof.
  unfold CheckedSmallStepCorrectnessBelow,
    CheckedContextSmallStepCorrectnessBelow.
  intros n HBelow n_child gamma omega heap env rho expr summary_expr
    phi heap' v phi_summary heap_summary theta HLt HBack HContext
    HComp HSummary.
  destruct
    (CheckedRuntimeContext_backtriangle_initials
      gamma omega heap env rho expr summary_expr HContext HBack)
    as (HRuntimeExpr & HRuntimeSummary).
  eapply HBelow; eauto.
Qed.

Lemma CheckedContextSmallStepCorrectnessBelow_from_store :
  forall n,
    CheckedStoreContextSmallStepCorrectnessBelow n ->
    CheckedContextSmallStepCorrectnessBelow n.
Proof.
  unfold CheckedStoreContextSmallStepCorrectnessBelow,
    CheckedContextSmallStepCorrectnessBelow.
  intros n HBelow n_child gamma omega heap env rho expr summary_expr
    phi heap' v phi_summary heap_summary theta HLt HBack HContext
    HComp HSummary.
  eapply HBelow; eauto using CheckedRuntimeContext_to_store_context.
Qed.

Theorem checked_context_terminal_correctness_from_below :
  (forall n, CheckedContextSmallStepCorrectnessBelow n) ->
  CheckedContextTerminalCorrectnessGoal.
Proof.
  unfold CheckedContextTerminalCorrectnessGoal.
  intros HBelow gamma omega heap env rho expr summary_expr phi heap' v
    phi_summary heap_summary theta HBack HContext HComp HSummary.
  destruct
    (NSteps_to_NStepsN
      (NInitialState heap env rho expr)
      phi
      (StDone heap' v)
      HComp)
    as (n & HCompN).
  eapply (HBelow (S n) n); eauto; lia.
Qed.

Theorem checked_context_terminal_correctness_from_store_below :
  (forall n, CheckedStoreContextSmallStepCorrectnessBelow n) ->
  CheckedContextTerminalCorrectnessGoal.
Proof.
  unfold CheckedContextTerminalCorrectnessGoal.
  intros HBelow gamma omega heap env rho expr summary_expr phi heap' v
    phi_summary heap_summary theta HBack HContext HComp HSummary.
  destruct
    (NSteps_to_NStepsN
      (NInitialState heap env rho expr)
      phi
      (StDone heap' v)
      HComp)
    as (n & HCompN).
  eapply (HBelow (S n) n); eauto using
    CheckedRuntimeContext_to_store_context; lia.
Qed.

Theorem checked_context_terminal_correctness_from_store_summary_below :
  (forall n, CheckedStoreSummarySmallStepCorrectnessBelow n) ->
  CheckedSummaryTraceSoundnessGoal ->
  CheckedContextTerminalCorrectnessGoal.
Proof.
  intros HBelow HSummaryTraceGoal.
  apply checked_context_terminal_correctness_from_below.
  intro n.
  eapply CheckedContextSmallStepCorrectnessBelow_from_summary.
  - eapply CheckedContextSummarySmallStepCorrectnessBelow_from_store_summary;
      eauto.
  - exact HSummaryTraceGoal.
Qed.

Theorem checked_context_terminal_correctness_from_checked_below :
  (forall n, CheckedSmallStepCorrectnessBelow n) ->
  CheckedContextTerminalCorrectnessGoal.
Proof.
  intros HBelow.
  apply checked_context_terminal_correctness_from_below.
  intro n.
  eapply CheckedContextSmallStepCorrectnessBelow_from_checked; eauto.
Qed.

Theorem checked_context_structured_terminal_correctness_from_terminal :
  CheckedContextTerminalCorrectnessGoal ->
  CheckedContextStructuredTerminalCorrectnessGoal.
Proof.
  unfold CheckedContextTerminalCorrectnessGoal,
    CheckedContextStructuredTerminalCorrectnessGoal.
  intros HTerminal gamma omega heap env rho expr summary_expr view heap' v
    view_summary heap_summary theta HBack HContext HComp HSummary.
  unfold StructuredComputationEvaluation in HComp.
  unfold StructuredSummaryEvaluation in HSummary.
  unfold TraceViewCoveredBySummary.
  eapply HTerminal; eauto;
    eapply NStepsView_to_NSteps; eauto.
Qed.

Theorem checked_context_structured_terminal_correctness_from_below :
  (forall n, CheckedContextSmallStepCorrectnessBelow n) ->
  CheckedContextStructuredTerminalCorrectnessGoal.
Proof.
  intros HBelow.
  apply checked_context_structured_terminal_correctness_from_terminal.
  apply checked_context_terminal_correctness_from_below.
  exact HBelow.
Qed.

Theorem checked_context_structured_terminal_correctness_from_store_below :
  (forall n, CheckedStoreContextSmallStepCorrectnessBelow n) ->
  CheckedContextStructuredTerminalCorrectnessGoal.
Proof.
  intros HBelow.
  apply checked_context_structured_terminal_correctness_from_terminal.
  apply checked_context_terminal_correctness_from_store_below.
  exact HBelow.
Qed.

Theorem checked_context_structured_terminal_correctness_from_checked_below :
  (forall n, CheckedSmallStepCorrectnessBelow n) ->
  CheckedContextStructuredTerminalCorrectnessGoal.
Proof.
  intros HBelow.
  apply checked_context_structured_terminal_correctness_from_below.
  intro n.
  eapply CheckedContextSmallStepCorrectnessBelow_from_checked; eauto.
Qed.
