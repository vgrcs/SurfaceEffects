From stdpp Require Import gmap.
From stdpp Require Import fin_maps.
From Stdlib Require Import List.
From Stdlib Require Import Program.Equality.

Require Import theories.Core.DynamicActions.
Require Import theories.Core.Values.
Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.TraceSemantics.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.TypingWeakeningFacts.
Require Import theories.Meta.HeapFacts.
Require Import theories.Meta.StoreFacts.

Inductive Phi_Updates : SigmaKey -> Val -> Phi -> Prop :=
| PU_Alloc : forall r l v,
    Phi_Updates (r, l) v (Phi_Elem (DA_Alloc r l v))
| PU_Write : forall r l v,
    Phi_Updates (r, l) v (Phi_Elem (DA_Write r l v))
| PU_Seq_L : forall k v phi1 phi2,
    Phi_Updates k v phi1 ->
    Phi_Updates k v (Phi_Seq phi1 phi2)
| PU_Seq_R : forall k v phi1 phi2,
    Phi_Updates k v phi2 ->
    Phi_Updates k v (Phi_Seq phi1 phi2)
| PU_Par_L : forall k v phi1 phi2,
    Phi_Updates k v phi1 ->
    Phi_Updates k v (Phi_Par phi1 phi2)
| PU_Par_R : forall k v phi1 phi2,
    Phi_Updates k v phi2 ->
    Phi_Updates k v (Phi_Par phi1 phi2).

Inductive Phi_Allocates : SigmaKey -> Phi -> Prop :=
| PA_Alloc : forall r l v,
    Phi_Allocates (r, l) (Phi_Elem (DA_Alloc r l v))
| PA_Seq_L : forall k phi1 phi2,
    Phi_Allocates k phi1 ->
    Phi_Allocates k (Phi_Seq phi1 phi2)
| PA_Seq_R : forall k phi1 phi2,
    Phi_Allocates k phi2 ->
    Phi_Allocates k (Phi_Seq phi1 phi2)
| PA_Par_L : forall k phi1 phi2,
    Phi_Allocates k phi1 ->
    Phi_Allocates k (Phi_Par phi1 phi2)
| PA_Par_R : forall k phi1 phi2,
    Phi_Allocates k phi2 ->
    Phi_Allocates k (Phi_Par phi1 phi2).

Definition TcPhi (stty : Sigma) (phi : Phi) : Prop :=
  forall k v,
    Phi_Updates k v phi ->
    exists t, find_ST k stty = Some t /\ TcVal (stty, v, t).

Lemma Phi_Updates_nil_false :
  forall k v, ~ Phi_Updates k v Phi_Nil.
Proof.
  intros k v H. inversion H.
Qed.

Lemma Phi_Allocates_nil_false :
  forall k, ~ Phi_Allocates k Phi_Nil.
Proof.
  intros k H. inversion H.
Qed.

Lemma TcPhi_nil :
  forall stty, TcPhi stty Phi_Nil.
Proof.
  unfold TcPhi. intros stty k v H. inversion H.
Qed.

Lemma TcPhi_weaken :
  forall stty stty' phi,
    (forall k t, find_ST k stty = Some t -> find_ST k stty' = Some t) ->
    TcPhi stty phi ->
    TcPhi stty' phi.
Proof.
  unfold TcPhi.
  intros stty stty' phi Hweak HTcPhi k v HUpdate.
  destruct (HTcPhi k v HUpdate) as [t [Hfind HTcVal]].
  exists t. split; [now apply Hweak |].
  eapply ext_stores__val; eauto.
Qed.

Lemma TcPhi_seq :
  forall stty phi1 phi2,
    TcPhi stty phi1 ->
    TcPhi stty phi2 ->
    TcPhi stty (Phi_Seq phi1 phi2).
Proof.
  unfold TcPhi.
  intros stty phi1 phi2 H1 H2 k v HUpdate.
  inversion HUpdate; subst; eauto.
Qed.

Lemma TcPhi_par :
  forall stty phi1 phi2,
    TcPhi stty phi1 ->
    TcPhi stty phi2 ->
    TcPhi stty (Phi_Par phi1 phi2).
Proof.
  unfold TcPhi.
  intros stty phi1 phi2 H1 H2 k v HUpdate.
  inversion HUpdate; subst; eauto.
Qed.

Fixpoint trace_as_phi (trace : Trace) : Phi :=
  match trace with
  | nil => Phi_Nil
  | da :: trace' => Phi_Seq (Phi_Elem da) (trace_as_phi trace')
  end.

Lemma phi_as_list_trace_as_phi :
  forall trace,
    phi_as_list (trace_as_phi trace) = trace.
Proof.
  induction trace as [| da trace IH]; simpl; auto.
  now rewrite IH.
Qed.

Lemma Phi_Updates_trace_as_phi_app_l :
  forall trace1 trace2 k v,
    Phi_Updates k v (trace_as_phi trace1) ->
    Phi_Updates k v (trace_as_phi (trace1 ++ trace2)).
Proof.
  induction trace1 as [| da trace1 IH]; intros trace2 k v HUpdate.
  - inversion HUpdate.
  - simpl in *.
    inversion HUpdate; subst.
    + apply PU_Seq_L. assumption.
    + apply PU_Seq_R. eapply IH; eauto.
Qed.

Lemma Phi_Updates_trace_as_phi_app_r :
  forall trace1 trace2 k v,
    Phi_Updates k v (trace_as_phi trace2) ->
    Phi_Updates k v (trace_as_phi (trace1 ++ trace2)).
Proof.
  induction trace1 as [| da trace1 IH]; intros trace2 k v HUpdate.
  - simpl. assumption.
  - simpl. apply PU_Seq_R. eapply IH; eauto.
Qed.

Lemma Phi_Updates_trace_as_phi_phi_as_list :
  forall phi k v,
    Phi_Updates k v phi ->
    Phi_Updates k v (trace_as_phi (phi_as_list phi)).
Proof.
  intros phi k v HUpdate.
  induction HUpdate; simpl.
  - apply PU_Seq_L. constructor.
  - apply PU_Seq_L. constructor.
  - eapply Phi_Updates_trace_as_phi_app_l. exact IHHUpdate.
  - eapply Phi_Updates_trace_as_phi_app_r. exact IHHUpdate.
  - eapply Phi_Updates_trace_as_phi_app_l. exact IHHUpdate.
  - eapply Phi_Updates_trace_as_phi_app_r. exact IHHUpdate.
Qed.

Lemma TcPhi_of_trace_as_phi_phi_as_list :
  forall stty phi,
    TcPhi stty (trace_as_phi (phi_as_list phi)) ->
    TcPhi stty phi.
Proof.
  unfold TcPhi.
  intros stty phi HTcTrace k v HUpdate.
  apply HTcTrace.
  now apply Phi_Updates_trace_as_phi_phi_as_list.
Qed.

Lemma TcPhi_seq_inv_l :
  forall stty phi1 phi2,
    TcPhi stty (Phi_Seq phi1 phi2) ->
    TcPhi stty phi1.
Proof.
  unfold TcPhi.
  intros stty phi1 phi2 HTcPhi k v HUpdate.
  apply (HTcPhi k v).
  now apply PU_Seq_L.
Qed.

Lemma TcPhi_seq_inv_r :
  forall stty phi1 phi2,
    TcPhi stty (Phi_Seq phi1 phi2) ->
    TcPhi stty phi2.
Proof.
  unfold TcPhi.
  intros stty phi1 phi2 HTcPhi k v HUpdate.
  apply (HTcPhi k v).
  now apply PU_Seq_R.
Qed.

Lemma TcPhi_trace_as_phi_app :
  forall stty trace1 trace2,
    TcPhi stty (trace_as_phi trace1) ->
    TcPhi stty (trace_as_phi trace2) ->
    TcPhi stty (trace_as_phi (trace1 ++ trace2)).
Proof.
  intros stty trace1.
  induction trace1 as [| da trace1 IH]; intros trace2 HTcTrace1 HTcTrace2.
  - exact HTcTrace2.
  - simpl in *.
    apply TcPhi_seq.
    + eapply TcPhi_seq_inv_l; eauto.
    + apply IH.
      * eapply TcPhi_seq_inv_r; eauto.
      * exact HTcTrace2.
Qed.

Lemma TcPhi_trace_as_phi_single :
  forall stty da,
    TcPhi stty (Phi_Elem da) ->
    TcPhi stty (trace_as_phi (da :: nil)).
Proof.
  intros stty da HTcPhi.
  simpl.
  apply TcPhi_seq; [exact HTcPhi | apply TcPhi_nil].
Qed.

Lemma TcPhi_elem_read :
  forall stty r l v,
    TcPhi stty (Phi_Elem (DA_Read r l v)).
Proof.
  unfold TcPhi.
  intros stty r l v k value HUpdate.
  inversion HUpdate.
Qed.

Lemma TcPhi_elem_alloc_from_heap :
  forall stty heap r l v,
    TcHeap (heap, stty) ->
    find_H (r, l) heap = Some v ->
    TcPhi stty (Phi_Elem (DA_Alloc r l v)).
Proof.
  unfold TcPhi.
  intros stty heap r l v HTcHeap HFind k value HUpdate.
  inversion HUpdate; subst.
  inversion HTcHeap as [? ? HHeapStore _ HHeapVal]; subst.
  destruct (HHeapStore (r, l) v HFind) as (t & HFindST).
  exists t.
  split; [exact HFindST |].
  eapply HHeapVal; eauto.
Qed.

Lemma TcPhi_elem_write_from_heap :
  forall stty heap r l v,
    TcHeap (heap, stty) ->
    find_H (r, l) heap = Some v ->
    TcPhi stty (Phi_Elem (DA_Write r l v)).
Proof.
  unfold TcPhi.
  intros stty heap r l v HTcHeap HFind k value HUpdate.
  inversion HUpdate; subst.
  inversion HTcHeap as [? ? HHeapStore _ HHeapVal]; subst.
  destruct (HHeapStore (r, l) v HFind) as (t & HFindST).
  exists t.
  split; [exact HFindST |].
  eapply HHeapVal; eauto.
Qed.

Lemma Phi_Heap_Step_preserves_updates :
  forall phi phi' heap heap' k v,
    (phi, heap) ===> (phi', heap') ->
    Phi_Updates k v phi' ->
    Phi_Updates k v phi.
Proof.
  intros phi phi' heap heap' k v HStep.
  dependent induction HStep; intros HUpdate; inversion HUpdate; subst; eauto using Phi_Updates.
Qed.

Lemma Phi_Heap_StepsAux_preserves_updates :
  forall phi heap phi' heap' n k v,
    (phi, heap) =a=>* (phi', heap', n) ->
    Phi_Updates k v phi' ->
    Phi_Updates k v phi.
Proof.
  intros phi heap phi' heap' n k v HSteps.
  dependent induction HSteps; intros HUpdate.
  - assumption.
  - eapply Phi_Heap_Step_preserves_updates; eauto.
  - eapply IHHSteps1; try reflexivity.
    eapply IHHSteps2; try reflexivity; eauto.
Qed.

Lemma Phi_Heap_Step_preserves_allocates :
  forall phi phi' heap heap' k,
    (phi, heap) ===> (phi', heap') ->
    Phi_Allocates k phi' ->
    Phi_Allocates k phi.
Proof.
  intros phi phi' heap heap' k HStep.
  dependent induction HStep; intros HAlloc; inversion HAlloc; subst; eauto using Phi_Allocates.
Qed.

Lemma Phi_Heap_StepsAux_preserves_allocates :
  forall phi heap phi' heap' n k,
    (phi, heap) =a=>* (phi', heap', n) ->
    Phi_Allocates k phi' ->
    Phi_Allocates k phi.
Proof.
  intros phi heap phi' heap' n k HSteps.
  dependent induction HSteps; intros HAlloc.
  - assumption.
  - eapply Phi_Heap_Step_preserves_allocates; eauto.
  - eapply IHHSteps1; try reflexivity.
    eapply IHHSteps2; try reflexivity; eauto.
Qed.

Lemma Phi_Heap_Step_lookup_source :
  forall phi phi' heap heap' k v,
    (phi, heap) ===> (phi', heap') ->
    find_H k heap' = Some v ->
    find_H k heap = Some v \/ Phi_Updates k v phi.
Proof.
  intros phi phi' heap heap' k v HStep.
  dependent induction HStep; intros Hfind; simpl in *.
  - destruct (decide (k = (r, l))) as [Heq | Hneq].
    + subst.
      assert (Hsame : find_H (r, l) (update_H ((r, l), v0) heap) = Some v0).
      { unfold find_H, update_H. simpl. apply H_same_key_1. }
      rewrite Hsame in Hfind. inversion Hfind; subst.
      right. constructor.
    + left. unfold find_H, update_H in Hfind. simpl in Hfind.
      unfold find_H. eapply H_diff_keys_1; eauto.
  - left. assumption.
  - destruct (decide (k = (r, l))) as [Heq | Hneq].
    + subst.
      assert (Hsame : find_H (r, l) (update_H ((r, l), v0) heap) = Some v0).
      { unfold find_H, update_H. simpl. apply H_same_key_1. }
      rewrite Hsame in Hfind. inversion Hfind; subst.
      right. constructor.
    + left. unfold find_H, update_H in Hfind. simpl in Hfind.
      unfold find_H. eapply H_diff_keys_1; eauto.
  - destruct (IHHStep _ _ _ _ eq_refl eq_refl Hfind) as [HOld | HUpdate].
    + left. assumption.
    + right. now apply PU_Seq_L.
  - destruct (IHHStep _ _ _ _ eq_refl eq_refl Hfind) as [HOld | HUpdate].
    + left. assumption.
    + right. now apply PU_Seq_R.
  - left. assumption.
  - destruct (IHHStep _ _ _ _ eq_refl eq_refl Hfind) as [HOld | HUpdate].
    + left. assumption.
    + right. now apply PU_Par_L.
  - destruct (IHHStep _ _ _ _ eq_refl eq_refl Hfind) as [HOld | HUpdate].
    + left. assumption.
    + right. now apply PU_Par_R.
  - left. assumption.
Qed.

Lemma Phi_Heap_StepsAux_lookup_source :
  forall phi heap phi' heap' n k v,
    (phi, heap) =a=>* (phi', heap', n) ->
    find_H k heap' = Some v ->
    find_H k heap = Some v \/ Phi_Updates k v phi.
Proof.
  intros phi heap phi' heap' n k v HSteps.
  generalize dependent v.
  generalize dependent k.
  dependent induction HSteps; intros k v Hfind.
  - left. assumption.
  - eapply Phi_Heap_Step_lookup_source; eauto.
  - destruct (IHHSteps2 _ _ _ _ _ eq_refl eq_refl k v Hfind) as [Hmid | HUpdateMid].
    + destruct (IHHSteps1 _ _ _ _ _ eq_refl eq_refl k v Hmid) as [Hstart | HUpdateStart].
      * left. assumption.
      * right. assumption.
    + right.
      eapply Phi_Heap_StepsAux_preserves_updates; eauto.
Qed.

Lemma Phi_Heap_Steps_lookup_source :
  forall phi heap phi' heap' k v,
    (phi, heap) ==>* (phi', heap') ->
    find_H k heap' = Some v ->
    find_H k heap = Some v \/ Phi_Updates k v phi.
Proof.
  intros phi heap phi' heap' k v [n HSteps] Hfind.
  eapply Phi_Heap_StepsAux_lookup_source; eauto.
Qed.

Lemma Phi_Heap_Step_preserves_domain :
  forall phi phi' heap heap' k v,
    (phi, heap) ===> (phi', heap') ->
    find_H k heap = Some v ->
    exists v', find_H k heap' = Some v'.
Proof.
  intros phi phi' heap heap' k v HStep.
  dependent induction HStep; intros Hfind; simpl in *.
  - destruct (decide (k = (r, l))).
    + subst. exists v0. unfold find_H, update_H. simpl. apply H_same_key_1.
    + exists v. unfold find_H in Hfind. unfold find_H, update_H. simpl.
      eapply H_diff_keys_2; eauto.
  - exists v. assumption.
  - destruct (decide (k = (r, l))).
    + subst. exists v0. unfold find_H, update_H. simpl. apply H_same_key_1.
    + exists v. unfold find_H in Hfind. unfold find_H, update_H. simpl.
      eapply H_diff_keys_2; eauto.
  - eapply IHHStep; try reflexivity; eauto.
  - eapply IHHStep; try reflexivity; eauto.
  - exists v. assumption.
  - eapply IHHStep; try reflexivity; eauto.
  - eapply IHHStep; try reflexivity; eauto.
  - exists v. assumption.
Qed.

Lemma Phi_Heap_StepsAux_preserves_domain :
  forall phi heap phi' heap' n k v,
    (phi, heap) =a=>* (phi', heap', n) ->
    find_H k heap = Some v ->
    exists v', find_H k heap' = Some v'.
Proof.
  intros phi heap phi' heap' n k v HSteps.
  generalize dependent v.
  generalize dependent k.
  dependent induction HSteps; intros k v Hfind.
  - exists v. assumption.
  - eapply Phi_Heap_Step_preserves_domain; eauto.
  - destruct (IHHSteps1 _ _ _ _ _ eq_refl eq_refl k v Hfind) as [vmid Hmid].
    destruct (IHHSteps2 _ _ _ _ _ eq_refl eq_refl k vmid Hmid) as [vfinal Hfinal].
    exists vfinal. assumption.
Qed.

Lemma Phi_Heap_Steps_preserves_domain :
  forall phi heap phi' heap' k v,
    (phi, heap) ==>* (phi', heap') ->
    find_H k heap = Some v ->
    exists v', find_H k heap' = Some v'.
Proof.
  intros phi heap phi' heap' k v [n HSteps] Hfind.
  eapply Phi_Heap_StepsAux_preserves_domain; eauto.
Qed.

Lemma Phi_Heap_Step_alloc_source :
  forall phi phi' heap heap' k v,
    (phi, heap) ===> (phi', heap') ->
    find_H k heap' = Some v ->
    find_H k heap = None ->
    Phi_Allocates k phi.
Proof.
  intros phi phi' heap heap' k v HStep.
  dependent induction HStep; intros Hfind Hnone; simpl in *.
  - destruct (decide (k = (r, l))) as [Heq | Hneq].
    + subst. constructor.
    + unfold find_H, update_H in Hfind. simpl in Hfind.
      assert (Hold : find_H k heap = Some v).
      { unfold find_H. eapply H_diff_keys_1; eauto. }
      rewrite Hnone in Hold. discriminate.
  - rewrite Hnone in Hfind. discriminate.
  - destruct (decide (k = (r, l))) as [Heq | Hneq].
    + subst. rewrite Hnone in H. contradiction.
    + unfold find_H, update_H in Hfind. simpl in Hfind.
      assert (Hold : find_H k heap = Some v).
      { unfold find_H. eapply H_diff_keys_1; eauto. }
      rewrite Hnone in Hold. discriminate.
  - eauto using Phi_Allocates.
  - eauto using Phi_Allocates.
  - rewrite Hnone in Hfind. discriminate.
  - eauto using Phi_Allocates.
  - eauto using Phi_Allocates.
  - rewrite Hnone in Hfind. discriminate.
Qed.

Lemma Phi_Heap_StepsAux_alloc_source :
  forall phi heap phi' heap' n k v,
    (phi, heap) =a=>* (phi', heap', n) ->
    find_H k heap' = Some v ->
    find_H k heap = None ->
    Phi_Allocates k phi.
Proof.
  intros phi heap phi' heap' n k v HSteps.
  generalize dependent v.
  generalize dependent k.
  dependent induction HSteps; intros k v Hfind Hnone.
  - rewrite Hnone in Hfind. discriminate.
  - eapply Phi_Heap_Step_alloc_source; eauto.
  - destruct (find_H k heap'0) eqn:Hmid.
    + eapply IHHSteps1; try reflexivity; eauto.
    + assert (Halloc_mid : Phi_Allocates k phi'0).
      { eapply IHHSteps2; try reflexivity; eauto. }
      eapply Phi_Heap_StepsAux_preserves_allocates; eauto.
Qed.

Lemma Phi_Heap_Steps_alloc_source :
  forall phi heap phi' heap' k v,
    (phi, heap) ==>* (phi', heap') ->
    find_H k heap' = Some v ->
    find_H k heap = None ->
    Phi_Allocates k phi.
Proof.
  intros phi heap phi' heap' k v [n HSteps] Hfind Hnone.
  eapply Phi_Heap_StepsAux_alloc_source; eauto.
Qed.

Lemma Phi_Heap_Step_alloc_done :
  forall phi phi' heap heap' k,
    (phi, heap) ===> (phi', heap') ->
    Phi_Allocates k phi \/ (exists v, find_H k heap = Some v) ->
    Phi_Allocates k phi' \/ (exists v, find_H k heap' = Some v).
Proof.
  intros phi phi' heap heap' k HStep.
  dependent induction HStep; intros HPending.
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc; subst.
      right. exists v. unfold find_H, update_H. simpl. apply H_same_key_1.
    + right. eapply Phi_Heap_Step_preserves_domain with (v:=w);
        [constructor; eauto | exact Hfind].
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc.
    + right. exists w. assumption.
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc.
    + right. eapply Phi_Heap_Step_preserves_domain with (v:=w);
        [constructor; eauto | exact Hfind].
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc; subst.
      * destruct (IHHStep _ _ _ _ eq_refl eq_refl (or_introl H1)) as [HAlloc' | HDone].
        -- left. now apply PA_Seq_L.
        -- right. assumption.
      * left. now apply PA_Seq_R.
    + right. eapply Phi_Heap_Step_preserves_domain with (v:=w);
        [constructor; eauto | exact Hfind].
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc; subst.
      * inversion H1.
      * destruct (IHHStep _ _ _ _ eq_refl eq_refl (or_introl H1)) as [HAlloc' | HDone].
        -- left. now apply PA_Seq_R.
        -- right. assumption.
    + right. eapply Phi_Heap_Step_preserves_domain with (v:=w);
        [constructor; eauto | exact Hfind].
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc; subst; inversion H1.
    + right. exists w. assumption.
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc; subst.
      * destruct (IHHStep _ _ _ _ eq_refl eq_refl (or_introl H1)) as [HAlloc' | HDone].
        -- left. now apply PA_Par_L.
        -- right. assumption.
      * left. now apply PA_Par_R.
    + right. eapply Phi_Heap_Step_preserves_domain with (v:=w);
        [constructor; eauto | exact Hfind].
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc; subst.
      * left. now apply PA_Par_L.
      * destruct (IHHStep _ _ _ _ eq_refl eq_refl (or_introl H1)) as [HAlloc' | HDone].
        -- left. now apply PA_Par_R.
        -- right. assumption.
    + right. eapply Phi_Heap_Step_preserves_domain with (v:=w);
        [constructor; eauto | exact Hfind].
  - destruct HPending as [HAlloc | [w Hfind]].
    + inversion HAlloc; subst; inversion H1.
    + right. exists w. assumption.
  Unshelve. all: eauto.
Qed.

Lemma Phi_Heap_StepsAux_alloc_done :
  forall phi heap phi' heap' n k,
    (phi, heap) =a=>* (phi', heap', n) ->
    Phi_Allocates k phi \/ (exists v, find_H k heap = Some v) ->
    Phi_Allocates k phi' \/ (exists v, find_H k heap' = Some v).
Proof.
  intros phi heap phi' heap' n k HSteps.
  dependent induction HSteps; intros HAlloc.
  - assumption.
  - eapply Phi_Heap_Step_alloc_done; eauto.
  - eapply IHHSteps2; try reflexivity.
    eapply IHHSteps1; try reflexivity; eauto.
Qed.

Lemma Phi_Heap_Steps_alloc_done :
  forall phi heap heap' k,
    (phi, heap) ==>* (Phi_Nil, heap') ->
    Phi_Allocates k phi ->
    exists v, find_H k heap' = Some v.
Proof.
  intros phi heap heap' k [n HSteps] HAlloc.
  destruct (Phi_Heap_StepsAux_alloc_done phi heap Phi_Nil heap' n k HSteps
              (or_introl HAlloc)) as [HNilAlloc | HDone].
  - exfalso. eapply Phi_Allocates_nil_false; eauto.
  - assumption.
Qed.

Lemma Phi_Allocates_in_phi_as_list :
  forall k phi,
    Phi_Allocates k phi ->
    exists v,
      In (DA_Alloc (fst k) (snd k) v) (phi_as_list phi).
Proof.
  intros k phi HAlloc.
  induction HAlloc; simpl.
  - exists v. left. reflexivity.
  - destruct IHHAlloc as [v HIn].
    exists v. apply in_or_app. now left.
  - destruct IHHAlloc as [v HIn].
    exists v. apply in_or_app. now right.
  - destruct IHHAlloc as [v HIn].
    exists v. apply in_or_app. now left.
  - destruct IHHAlloc as [v HIn].
    exists v. apply in_or_app. now right.
Qed.

Lemma Disjoint_Traces_no_common_alloc :
  forall phi1 phi2 k,
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    Phi_Allocates k phi1 ->
    Phi_Allocates k phi2 ->
    False.
Proof.
  intros phi1 phi2 k HDisjoint HAlloc1 HAlloc2.
  destruct k as [r l].
  destruct (Phi_Allocates_in_phi_as_list (r, l) phi1 HAlloc1)
    as [v1 HIn1].
  destruct (Phi_Allocates_in_phi_as_list (r, l) phi2 HAlloc2)
    as [v2 HIn2].
  simpl in *.
  inversion HDisjoint as [? ? HDisjointActions]; subst.
  pose proof
    (HDisjointActions
      (DA_Alloc r l v1) (DA_Alloc r l v2) HIn1 HIn2)
    as HDynamicDisjoint.
  inversion HDynamicDisjoint; subst.
  match goal with
  | Hneq : (r, l) <> (r, l) |- _ => apply Hneq; reflexivity
  end.
Qed.

Lemma Phi_Heap_Steps_disjoint_deltas :
  forall phi1 phi2 heap heap1 heap2,
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    (phi1, heap) ==>* (Phi_Nil, heap1) ->
    (phi2, heap) ==>* (Phi_Nil, heap2) ->
    heap1 ∖ heap ##ₘ heap2 ∖ heap.
Proof.
  intros phi1 phi2 heap heap1 heap2 HDisjoint HSteps1 HSteps2.
  apply map_disjoint_spec.
  intros k v1 v2 HFind1 HFind2.
  apply lookup_difference_Some in HFind1.
  apply lookup_difference_Some in HFind2.
  destruct HFind1 as [HFindHeap1 HBaseNone1].
  destruct HFind2 as [HFindHeap2 HBaseNone2].
  assert (HAlloc1 : Phi_Allocates k phi1).
  { eapply Phi_Heap_Steps_alloc_source; eauto. }
  assert (HAlloc2 : Phi_Allocates k phi2).
  { eapply Phi_Heap_Steps_alloc_source; eauto. }
  eapply Disjoint_Traces_no_common_alloc; eauto.
Qed.

Lemma TcHeap_Extended_PhiPar :
  forall heap phi1 phi2 heap1 heap2 stty stty1 stty2 hp',
    heap1 ∖ heap ##ₘ heap2 ∖ heap ->
    (phi1, heap) ==>* (Phi_Nil, heap1) ->
    (phi2, heap) ==>* (Phi_Nil, heap2) ->
    (Phi_Par phi1 phi2, heap) ==>* (Phi_Nil, hp') ->
    TcPhi stty1 phi1 ->
    TcPhi stty2 phi2 ->
    TcHeap (heap, stty) ->
    StoreExtends stty stty1 ->
    StoreExtends stty stty2 ->
    TcHeap (heap1, stty1) ->
    TcHeap (heap2, stty2) ->
    TcHeap (hp', stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty)).
Proof.
  intros heap phi1 phi2 heap1 heap2 stty stty1 stty2 hp'
    HheapDisj Hsteps1 Hsteps2 Hpar HTcPhi1 HTcPhi2
    HTcHeap Hext1 Hext2 HTcHeap1 HTcHeap2.
  assert (HsttyDisj : stty1 ∖ stty ##ₘ stty2 ∖ stty)
    by (eapply djt_heap_implies_djt_stty; eauto).
  constructor.
  - intros k v HfindHp.
    destruct (Phi_Heap_Steps_lookup_source
                (Phi_Par phi1 phi2) heap Phi_Nil hp' k v Hpar HfindHp)
      as [HfindBase | Hupdate].
    + inversion HTcHeap as [? ? HHeapStore _ _]; subst.
      destruct (HHeapStore k v HfindBase) as [t HfindStty].
      exists t. eapply StoreTyping_Extended_Base; eauto.
    + inversion Hupdate; subst.
      * match goal with
        | H : Phi_Updates k v phi1 |- _ =>
            destruct (HTcPhi1 k v H) as [t [HfindStty1 _]]
        end.
        exists t. eapply StoreTyping_Extended_Left; eauto.
      * match goal with
        | H : Phi_Updates k v phi2 |- _ =>
            destruct (HTcPhi2 k v H) as [t [HfindStty2 _]]
        end.
        exists t. eapply StoreTyping_Extended_Right; eauto.
  - intros k t HfindStore.
    unfold find_ST in HfindStore.
    apply lookup_union_Some_raw in HfindStore.
    destruct HfindStore as [HfindBaseStore | [HbaseNone HfindDiffs]].
    + inversion HTcHeap as [? ? _ HStoreHeap _]; subst.
      destruct (HStoreHeap k t HfindBaseStore) as [v HfindHeap].
      eapply Phi_Heap_Steps_preserves_domain; eauto.
    + apply lookup_union_Some_raw in HfindDiffs.
      destruct HfindDiffs as [HfindDiff1 | [_ HfindDiff2]].
      * apply lookup_difference_Some in HfindDiff1.
        destruct HfindDiff1 as [HfindStty1 HfindBaseNone].
        inversion HTcHeap1 as [? ? _ HStoreHeap1 _]; subst.
        destruct (HStoreHeap1 k t HfindStty1) as [v HfindHeap1].
        assert (HfindHeapNone : find_H k heap = None).
        { eapply TcHeap_none_implies_none; eauto. }
        assert (Halloc : Phi_Allocates k phi1).
        { eapply Phi_Heap_Steps_alloc_source; eauto. }
        eapply Phi_Heap_Steps_alloc_done; eauto.
        now apply PA_Par_L.
      * apply lookup_difference_Some in HfindDiff2.
        destruct HfindDiff2 as [HfindStty2 HfindBaseNone].
        inversion HTcHeap2 as [? ? _ HStoreHeap2 _]; subst.
        destruct (HStoreHeap2 k t HfindStty2) as [v HfindHeap2].
        assert (HfindHeapNone : find_H k heap = None).
        { eapply TcHeap_none_implies_none; eauto. }
        assert (Halloc : Phi_Allocates k phi2).
        { eapply Phi_Heap_Steps_alloc_source; eauto. }
        eapply Phi_Heap_Steps_alloc_done; eauto.
        now apply PA_Par_R.
  - intros k v t HfindHp HfindStore.
    destruct (Phi_Heap_Steps_lookup_source
                (Phi_Par phi1 phi2) heap Phi_Nil hp' k v Hpar HfindHp)
      as [HfindBase | Hupdate].
    + inversion HTcHeap as [? ? HHeapStore _ HHeapVals]; subst.
      destruct (HHeapStore k v HfindBase) as [t0 HfindStty].
      assert (HfindStore0 :
                find_ST k (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty)) = Some t0)
        by (eapply StoreTyping_Extended_Base; eauto).
      assert (t = t0)
        by (eapply PairType_unique_type; eauto).
      subst.
      eapply ext_stores__val with (stty:=stty); eauto.
      intros l t' Hfind. eapply StoreTyping_Extended_Base; eauto.
    + inversion Hupdate; subst.
      * match goal with
        | H : Phi_Updates k v phi1 |- _ =>
            destruct (HTcPhi1 k v H) as [t1 [HfindStty1 HTcVal1]]
        end.
        assert (HfindStore1 :
                  find_ST k (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty)) = Some t1)
          by (eapply StoreTyping_Extended_Left; eauto).
        assert (t = t1)
          by (eapply PairType_unique_type; eauto).
        subst.
        eapply ext_stores__val with (stty:=stty1); eauto.
        intros l t' Hfind. eapply StoreTyping_Extended_Left; eauto.
      * match goal with
        | H : Phi_Updates k v phi2 |- _ =>
            destruct (HTcPhi2 k v H) as [t2 [HfindStty2 HTcVal2]]
        end.
        assert (HfindStore2 :
                  find_ST k (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty)) = Some t2)
          by (eapply StoreTyping_Extended_Right; eauto).
        assert (t = t2)
          by (eapply PairType_unique_type; eauto).
        subst.
        eapply ext_stores__val with (stty:=stty2); eauto.
        intros l t' Hfind. eapply StoreTyping_Extended_Right; eauto.
Qed.
