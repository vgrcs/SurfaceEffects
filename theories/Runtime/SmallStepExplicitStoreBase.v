From stdpp Require Import gmap.
From Stdlib Require Import Program.Equality.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
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
Require Import theories.Meta.TypeFacts.
Require Import theories.Meta.TypingWeakeningFacts.

Inductive WTStateRuntimeHeapShapeAt : State -> Tau -> Sigma -> Prop :=
| WTSRHSA_Eval :
    forall heap env rho e k stty ctxt rgns t eff tout,
      TcHeap (heap, stty) ->
      RuntimeHeapShape heap stty ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e, t, eff) ->
      WTKontRuntime stty (subst_rho rho t) tout k ->
      WTStateRuntimeHeapShapeAt (StEval heap env rho e k) tout stty
| WTSRHSA_Return :
    forall heap v k stty t tout,
      TcHeap (heap, stty) ->
      RuntimeHeapShape heap stty ->
      TcVal (stty, v, t) ->
      WTKontRuntime stty t tout k ->
      RuntimeValShape stty t v ->
      WTStateRuntimeHeapShapeAt (StReturn heap v k) tout stty
| WTSRHSA_Done :
    forall heap v stty t,
      TcHeap (heap, stty) ->
      RuntimeHeapShape heap stty ->
      TcVal (stty, v, t) ->
      RuntimeValShape stty t v ->
      WTStateRuntimeHeapShapeAt (StDone heap v) t stty.

Lemma WTStateRuntimeHeapShapeAt_forget :
  forall state tout stty,
    WTStateRuntimeHeapShapeAt state tout stty ->
    WTStateRuntimeHeapShape state tout.
Proof.
  intros state tout stty HWT.
  inversion HWT; subst; econstructor; eauto.
Qed.


Lemma WTStateRuntimeHeapShapeAt_reheap_store_ext :
  forall state tout stty heap' stty',
    WTStateRuntimeHeapShapeAt state tout stty ->
    TcHeap (heap', stty') ->
    RuntimeHeapShape heap' stty' ->
    StoreExtends stty stty' ->
    WTStateRuntimeHeapShapeAt (with_state_heap heap' state) tout stty'.
Proof.
  intros state tout stty heap' stty' HWT HTcHeap' HHeapShape' HExt.
  inversion HWT; subst; simpl.
  - eapply WTSRHSA_Eval with (ctxt := ctxt) (rgns := rgns) (t := t)
      (eff := eff); eauto.
    + eapply ext_stores__env; eauto.
    + eapply RuntimeEnvShape_store_ext; eauto.
    + eapply WTKontRuntime_store_ext; eauto.
  - eapply WTSRHSA_Return; eauto.
    + eapply ext_stores__val; eauto.
    + eapply WTKontRuntime_store_ext; eauto.
    + eapply RuntimeValShape_store_ext; eauto.
  - eapply WTSRHSA_Done; eauto.
    + eapply ext_stores__val; eauto.
    + eapply RuntimeValShape_store_ext; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_reheap_same_store :
  forall state tout stty heap',
    WTStateRuntimeHeapShapeAt state tout stty ->
    TcHeap (heap', stty) ->
    RuntimeHeapShape heap' stty ->
    WTStateRuntimeHeapShapeAt (with_state_heap heap' state) tout stty.
Proof.
  intros state tout stty heap' HWT HTcHeap HHeapShape.
  eapply WTStateRuntimeHeapShapeAt_reheap_store_ext; eauto.
  intros k t HFind. exact HFind.
Qed.
