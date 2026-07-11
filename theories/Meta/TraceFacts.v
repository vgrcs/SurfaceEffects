From stdpp Require Import gmap.
Require Import Coq.Program.Equality.
Require Import theories.Core.Values.
Require Import theories.Runtime.Heap.
Require Import theories.Runtime.TraceSemantics.
Require Import theories.Runtime.Semantics.
Require Import theories.Core.DynamicActions.

Import Expressions.
Import ComputedActions.

Lemma EmptyTracePreservesHeap_1: 
  forall h r env e same_h v' acts,
    (h, r, env, e) ⇓ (same_h, v', acts) ->
    acts = Phi_Nil ->
    h ≡@{Heap} same_h.
Proof.
  intros h r env e same_h v' acts H Hnil.
  dependent induction H; auto; inversion Hnil.  
  - eapply IHBigStep. reflexivity. auto. reflexivity.
  - eapply IHBigStep; [reflexivity | auto | reflexivity]. 
Qed.

Lemma EmptyTracePreservesHeap_2 : 
  forall h r env e same_h v acts,
    (h, r, env, e) ⇓ (h, v, acts) ->
    h ≡@{Heap} same_h ->
    (same_h, r, env, e) ⇓ (same_h, v, acts).
Proof.
  intros h r env e same_h v' acts Dyn H.
  unfold equiv, heap_equiv in H. now subst.
Qed.

Lemma EmptyTracePreservesHeap_3 : 
  forall h r env e same_h v acts,
    (same_h, r, env, e) ⇓ (same_h, v, acts) ->
    (h, r, env, e) ⇓ (same_h, v, acts) ->
    acts = Phi_Nil ->
    (h, r, env, e) ⇓ (h, v, acts).
Proof.
  intros h r env e same_h v' acts Dyn Hheap Hnil.
  apply EmptyTracePreservesHeap_1 in Hheap; unfold equiv, heap_equiv in Hheap;
  now subst.
Qed.

Lemma EmptyTracePreservesHeap_4 : 
  forall h r env e same_h v,
    (h, r, env, e) ⇓ (same_h, v, Phi_Nil) ->
    h ≡@{Heap} same_h.
Proof.
   intros h r env e same_h v' Dyn1.
   dependent induction Dyn1; auto;  unfold equiv, heap_equiv.
   eapply IHDyn1.
   - reflexivity.
   - econstructor.
   - eapply IHDyn1.
     + reflexivity.
     + econstructor. 
Qed.

Lemma EmptyTracePreservesHeap_5 : 
  forall h r env e  v,
    (h, r, env, e) ⇓ (h, v, Phi_Nil) ->
    exists same_h,  (same_h, r, env, e) ⇓ (h, v, Phi_Nil).
Proof.
  intros h r env e v H.
  dependent induction H; exists h; econstructor; auto. 
Qed.

Lemma ReadOnlyPhi_Heap_Step_preserves_readonly:
  forall phi phi' heap heap',
    ReadOnlyPhi phi ->
    (phi, heap) ===> (phi', heap') ->
    ReadOnlyPhi phi'.
Proof.
  intros phi phi' heap heap' HRO HStep.
  dependent induction HStep; inversion HRO; subst; constructor; eauto.
Qed.

Lemma ReadOnlyPhi_Heap_Step_preserves_heap:
  forall phi phi' heap heap',
    ReadOnlyPhi phi ->
    (phi, heap) ===> (phi', heap') ->
    heap ≡@{Heap} heap'.
Proof.
  intros phi phi' heap heap' HRO HStep.
  dependent induction HStep; inversion HRO; subst; try reflexivity; eauto.
Qed.

Lemma ReadOnlyPhi_Heap_StepsAux_preserves_readonly:
  forall phi heap phi' heap' n,
    (phi, heap) =a=>* (phi', heap', n) ->
    ReadOnlyPhi phi ->
    ReadOnlyPhi phi'.
Proof.
  intros phi heap phi' heap' n HSteps.
  dependent induction HSteps; intros HRO.
  - exact HRO.
  - eapply ReadOnlyPhi_Heap_Step_preserves_readonly; eauto.
  - eapply IHHSteps2; try reflexivity.
    eapply IHHSteps1; try reflexivity; assumption.
Qed.

Lemma ReadOnlyPhi_Heap_StepsAux_preserves_heap:
  forall phi heap phi' heap' n,
    (phi, heap) =a=>* (phi', heap', n) ->
    ReadOnlyPhi phi ->
    heap ≡@{Heap} heap'.
Proof.
  intros phi heap phi' heap' n HSteps.
  dependent induction HSteps; intros HRO.
  - reflexivity.
  - eapply ReadOnlyPhi_Heap_Step_preserves_heap; eauto.
  - assert (Hheap1 : heap ≡@{Heap} heap'0)
      by (eapply IHHSteps1; try reflexivity; exact HRO).
    assert (HRO' : ReadOnlyPhi phi'0)
      by (eapply ReadOnlyPhi_Heap_StepsAux_preserves_readonly; eauto).
    assert (Hheap2 : heap'0 ≡@{Heap} heap')
      by (eapply IHHSteps2; try reflexivity; exact HRO').
    unfold equiv, heap_equiv in *; subst; reflexivity.
Qed.

Lemma ReadOnlyPhi_Heap_Steps_preserves_heap:
  forall phi heap phi' heap',
    (phi, heap) ==>* (phi', heap') ->
    ReadOnlyPhi phi ->
    heap ≡@{Heap} heap'.
Proof.
  intros phi heap phi' heap' [n HSteps] HRO.
  eapply ReadOnlyPhi_Heap_StepsAux_preserves_heap; eauto.
Qed.

Lemma ReadOnlyEvalPreservesHeap:
  forall h env rho e h' v phi,
    (h, env, rho, e) ⇓ (h', v, phi) ->
    ReadOnlyPhi phi ->
    h ≡@{Heap} h'.
Proof.
  intros h env rho e h' v phi H.
  dependent induction H; intros HRO; subst; try reflexivity.
  - inversion HRO; subst.
    repeat match goal with
    | HSeq : ReadOnlyPhi (Phi_Seq _ _) |- _ =>
        inversion HSeq; subst; clear HSeq
    end.
    assert (Hhf : h ≡@{Heap} fheap) by (eapply IHBigStep1; try reflexivity; eauto).
    assert (Hfa : fheap ≡@{Heap} aheap) by (eapply IHBigStep2; try reflexivity; eauto).
    assert (Hab : aheap ≡@{Heap} h') by (eapply IHBigStep3; try reflexivity; eauto).
    unfold equiv, heap_equiv in *; subst; reflexivity.
  - inversion HRO; subst.
    assert (Hhf : h ≡@{Heap} fheap) by (eapply IHBigStep1; try reflexivity; eauto).
    assert (Hfb : fheap ≡@{Heap} h') by (eapply IHBigStep2; try reflexivity; eauto).
    unfold equiv, heap_equiv in *; subst; reflexivity.
  - inversion HRO; subst.
    eapply ReadOnlyPhi_Heap_Steps_preserves_heap; eauto.
  - inversion HRO; subst.
    assert (Hhc : h ≡@{Heap} cheap) by (eapply IHBigStep1; try reflexivity; eauto).
    assert (Hct : cheap ≡@{Heap} h') by (eapply IHBigStep2; try reflexivity; eauto).
    unfold equiv, heap_equiv in *; subst; reflexivity.
  - inversion HRO; subst.
    assert (Hhc : h ≡@{Heap} cheap) by (eapply IHBigStep1; try reflexivity; eauto).
    assert (Hcf : cheap ≡@{Heap} h') by (eapply IHBigStep2; try reflexivity; eauto).
    unfold equiv, heap_equiv in *; subst; reflexivity.
  - inversion HRO; subst.
    match goal with
    | HAlloc : ReadOnlyPhi (Phi_Elem (DA_Alloc _ _ _)) |- _ =>
        inversion HAlloc
    end.
  - inversion HRO; subst.
    assert (Hha : h ≡@{Heap} h') by (eapply IHBigStep; try reflexivity; eauto).
    unfold equiv, heap_equiv in *; subst; reflexivity.
  - inversion HRO; subst.
    match goal with
    | HWrite : ReadOnlyPhi (Phi_Elem (DA_Write _ _ _)) |- _ =>
        inversion HWrite
    end.
  - inversion HRO; subst.
    assert (Hhl : h ≡@{Heap} lheap) by (eapply IHBigStep1; try reflexivity; eauto).
    assert (Hlr : lheap ≡@{Heap} h') by (eapply IHBigStep2; try reflexivity; eauto).
    unfold equiv, heap_equiv in *; subst; reflexivity.
  - inversion HRO; subst.
    assert (Hhl : h ≡@{Heap} lheap) by (eapply IHBigStep1; try reflexivity; eauto).
    assert (Hlr : lheap ≡@{Heap} h') by (eapply IHBigStep2; try reflexivity; eauto).
    unfold equiv, heap_equiv in *; subst; reflexivity.
  - inversion HRO; subst.
    assert (Hhl : h ≡@{Heap} lheap) by (eapply IHBigStep1; try reflexivity; eauto).
    assert (Hlr : lheap ≡@{Heap} h') by (eapply IHBigStep2; try reflexivity; eauto).
    unfold equiv, heap_equiv in *; subst; reflexivity.
  - inversion HRO; subst.
    assert (Hhl : h ≡@{Heap} lheap) by (eapply IHBigStep1; try reflexivity; eauto).
    assert (Hlr : lheap ≡@{Heap} h') by (eapply IHBigStep2; try reflexivity; eauto).
    unfold equiv, heap_equiv in *; subst; reflexivity.
  - subst. eapply IHBigStep; try reflexivity; constructor.
  - subst. eapply IHBigStep; try reflexivity; constructor.
Qed.

Lemma Phi_Heap_Steps_trans :
  forall phi1 heap1 phi2 heap2 phi3 heap3,
    (phi1, heap1) ==>* (phi2, heap2) ->
    (phi2, heap2) ==>* (phi3, heap3) ->
    (phi1, heap1) ==>* (phi3, heap3).
Proof.
  intros phi1 heap1 phi2 heap2 phi3 heap3 [n1 H1] [n2 H2].
  exists (1 + n1 + n2)%nat.
  eapply PHT_Trans; eauto.
Qed.

Lemma Phi_Seq_lift_left :
  forall phi1 heap phi1' heap' phi2,
    (phi1, heap) ==>* (phi1', heap') ->
    (Phi_Seq phi1 phi2, heap) ==>* (Phi_Seq phi1' phi2, heap').
Proof.
  intros phi1 heap phi1' heap' phi2 [n HSteps].
  dependent induction HSteps.
  - exists 0. constructor.
  - exists 1. constructor. now constructor.
  - eapply Phi_Heap_Steps_trans; eauto.
Qed.

Lemma Phi_Seq_lift_right :
  forall phi2 heap phi2' heap',
    (phi2, heap) ==>* (phi2', heap') ->
    (Phi_Seq Phi_Nil phi2, heap) ==>* (Phi_Seq Phi_Nil phi2', heap').
Proof.
  intros phi2 heap phi2' heap' [n HSteps].
  dependent induction HSteps.
  - exists 0. constructor.
  - exists 1. constructor. now constructor.
  - eapply Phi_Heap_Steps_trans; eauto.
Qed.

Lemma Phi_Seq_steps :
  forall phi1 heap heap' phi2 heap'',
    (phi1, heap) ==>* (Phi_Nil, heap') ->
    (phi2, heap') ==>* (Phi_Nil, heap'') ->
    (Phi_Seq phi1 phi2, heap) ==>* (Phi_Nil, heap'').
Proof.
  intros phi1 heap heap' phi2 heap'' H1 H2.
  eapply Phi_Heap_Steps_trans.
  - eapply Phi_Seq_lift_left; eauto.
  - eapply Phi_Heap_Steps_trans.
    + eapply Phi_Seq_lift_right; eauto.
    + exists 1. constructor. constructor.
Qed.

Lemma Phi_Par_lift_left :
  forall phi1 heap phi1' heap' phi2,
    (phi1, heap) ==>* (phi1', heap') ->
    (Phi_Par phi1 phi2, heap) ==>* (Phi_Par phi1' phi2, heap').
Proof.
  intros phi1 heap phi1' heap' phi2 [n HSteps].
  dependent induction HSteps.
  - exists 0. constructor.
  - exists 1. constructor. now constructor.
  - eapply Phi_Heap_Steps_trans; eauto.
Qed.

Lemma Phi_Par_lift_right :
  forall phi1 phi2 heap phi2' heap',
    (phi2, heap) ==>* (phi2', heap') ->
    (Phi_Par phi1 phi2, heap) ==>* (Phi_Par phi1 phi2', heap').
Proof.
  intros phi1 phi2 heap phi2' heap' [n HSteps].
  dependent induction HSteps.
  - exists 0. constructor.
  - exists 1. constructor. now constructor.
  - eapply Phi_Heap_Steps_trans; eauto.
Qed.

Lemma Phi_Par_steps :
  forall phi1 heap heap' phi2 heap'',
    (phi1, heap) ==>* (Phi_Nil, heap') ->
    (phi2, heap') ==>* (Phi_Nil, heap'') ->
    (Phi_Par phi1 phi2, heap) ==>* (Phi_Nil, heap'').
Proof.
  intros phi1 heap heap' phi2 heap'' H1 H2.
  eapply Phi_Heap_Steps_trans.
  - eapply Phi_Par_lift_left; eauto.
  - eapply Phi_Heap_Steps_trans.
    + eapply Phi_Par_lift_right; eauto.
    + exists 1. constructor. constructor.
Qed.

Lemma BigStep_replays_trace :
  forall heap env rho e heap' v phi,
    (heap, env, rho, e) ⇓ (heap', v, phi) ->
    (phi, heap) ==>* (Phi_Nil, heap').
Proof.
  intros heap env rho e heap' v phi HBig.
  dependent induction HBig; subst; try (exists 0; constructor).
  - match goal with
    | HEqual : ?h ≡@{Heap} ?h' |- _ =>
        unfold equiv, heap_equiv in HEqual; subst h'
    end.
    eapply Phi_Seq_steps.
    + eapply Phi_Seq_steps; eauto.
    + eauto.
  - eapply Phi_Seq_steps; eauto.
  - eapply Phi_Seq_steps.
    + eapply Phi_Seq_steps; eauto.
    + eauto.
  - match goal with
    | HEqual : ?h ≡@{Heap} ?h1 /\ ?h ≡@{Heap} ?h2 |- _ =>
        destruct HEqual as [HEq1 HEq2]
    end.
    unfold equiv, heap_equiv in HEq1, HEq2; subst.
    match goal with
    | HStep : (?h, ?env, ?rho, Eff_App ef1 ea1) ⇓ (?h, Eff theta1, acts_eff1) |- _ =>
        assert (HEff1Steps : (acts_eff1, h) ==>* (Phi_Nil, h))
          by (eapply IHHBig1; reflexivity)
    end.
    match goal with
    | HStep : (?h, ?env, ?rho, Eff_App ef2 ea2) ⇓ (?h, Eff theta2, acts_eff2) |- _ =>
        assert (HEff2Steps : (acts_eff2, h) ==>* (Phi_Nil, h))
          by (eapply IHHBig2; reflexivity)
    end.
    eapply Phi_Seq_steps.
    + eapply Phi_Par_steps; eauto.
    + eassumption.
  - match goal with
    | HEqual : ?h ≡@{Heap} ?h' |- _ =>
        unfold equiv, heap_equiv in HEqual; subst h'
    end.
    eapply Phi_Seq_steps; eauto.
  - match goal with
    | HEqual : ?h ≡@{Heap} ?h' |- _ =>
        unfold equiv, heap_equiv in HEqual; subst h'
    end.
    eapply Phi_Seq_steps; eauto.
  - eapply Phi_Seq_steps; eauto.
    exists 1. constructor. constructor.
  - eapply Phi_Seq_steps; eauto.
    exists 1. constructor. now constructor.
  - eapply Phi_Seq_steps.
    + eapply Phi_Seq_steps; eauto.
    + exists 1. constructor. constructor. assumption.
  - eapply Phi_Seq_steps; eauto.
  - eapply Phi_Seq_steps; eauto.
  - eapply Phi_Seq_steps; eauto.
  - eapply Phi_Seq_steps; eauto.
  - assert (HEq : heap ≡@{Heap} heap')
      by (eapply EmptyTracePreservesHeap_1; eauto).
    unfold equiv, heap_equiv in HEq; subst.
    exists 0. constructor.
  - assert (HEq : heap ≡@{Heap} heap')
      by (eapply EmptyTracePreservesHeap_1; eauto).
    unfold equiv, heap_equiv in HEq; subst.
    exists 0. constructor.
  - eapply Phi_Seq_steps; eauto.
Qed.

Lemma H_monotonic_updates:
  forall phi phi' (heap heap' : gmap HeapKey HeapVal),
     (phi, heap) ===> (phi', heap') ->
     forall r l,
       find_H (r, l) heap ≠ None ->
       find_H (r, l) heap' ≠ None.
Proof.
  intros phi phi' heap heap' H.  
  dependent induction H; intros; unfold find_H, update_H in *; simpl in *.
  - intro. apply H.
    apply lookup_insert_None in H0. destruct H0.
    assumption.
  - intro. apply H0. assumption.
  - intro. apply H0.
    apply lookup_insert_None in H1. destruct H1.
    assumption.
  - apply IHPhi_Heap_Step with (phi:=phi1) (heap:=heap) (phi':=phi1').
    + reflexivity.
    + reflexivity.
    + assumption.
  - apply IHPhi_Heap_Step with (phi:=phi2) (heap:=heap) (phi':=phi2'). 
    + reflexivity.
    + reflexivity.
    + assumption.
  - assumption.
  - apply IHPhi_Heap_Step with (phi:=phi1) (heap:=heap) (phi':=phi1').
    + reflexivity.
    + reflexivity.
    + assumption.
  - apply IHPhi_Heap_Step with (phi:=phi2) (heap:=heap) (phi':=phi2'). 
    + reflexivity.
    + reflexivity.
    + assumption.
 - assumption.
Qed.
