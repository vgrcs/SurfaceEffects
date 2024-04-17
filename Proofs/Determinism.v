From stdpp Require Import gmap.
From stdpp Require Import strings.
Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Ascii String.
Require Import Coq.Lists.List.

Require Import Definitions.GHeap.
Require Import Definitions.Semantics.
Require Import Definitions.Axioms.
Require Import Definitions.DynamicActions.
Require Import Definitions.ComputedActions.
Require Import Proofs.EffectFacts.
Require Import Proofs.HeapFacts.

Lemma Seq_Left_Pres :
  forall phi1 phi1' heap1 heap1' n1 phi2,
    (phi1, heap1) =a=>* (phi1', heap1', n1) ->
    (Phi_Seq phi1 phi2, heap1) =a=>* (Phi_Seq phi1' phi2, heap1', n1).
Proof.
  intros phi1 phi1' heap1 heap1' n1 phi2 HSteps.
  dependent induction HSteps.
  - econstructor.
  - econstructor. econstructor. assumption.
  - econstructor.
    + eapply IHHSteps1.
      * reflexivity.
      * reflexivity. 
    + eapply IHHSteps2.
      * reflexivity.
      * reflexivity.    
Qed.

Lemma Seq_Right_Pres :
  forall phi2 phi2' heap2 heap2' n2,
    (phi2, heap2) =a=>* (phi2', heap2', n2) ->
    (Phi_Seq Phi_Nil phi2, heap2) =a=>* (Phi_Seq Phi_Nil phi2', heap2', n2).
Proof.
  intros phi2 phi2' heap2 heap2' n2 HSteps.
  dependent induction HSteps.
  - econstructor.
  - econstructor. econstructor. assumption.
  - econstructor.
    + eapply IHHSteps1.
      * reflexivity.
      * reflexivity. 
    + eapply IHHSteps2.
      * reflexivity.
      * reflexivity.    
Qed.

Lemma Par_Left_Pres :
  forall phi1 phi1' heap1 heap1' n1 phi2,
    (phi1, heap1) =a=>* (phi1', heap1', n1) ->
    (Phi_Par phi1 phi2, heap1) =a=>* (Phi_Par phi1' phi2, heap1', n1).
Proof.
  intros phi1 phi1' heap1 heap1' n1 phi2 HSteps.
  dependent induction HSteps.
  - econstructor.
  - econstructor. econstructor. assumption.
  - econstructor.
    + eapply IHHSteps1.
      * reflexivity.
      * reflexivity. 
    + eapply IHHSteps2.
      * reflexivity.
      * reflexivity.    
Qed.

Lemma Par_Right_Pres :
  forall phi2 phi2' heap2 heap2' n2 phi1 ,
    (phi2, heap2) =a=>* (phi2', heap2', n2) ->
    (Phi_Par phi1 phi2, heap2) =a=>* (Phi_Par phi1 phi2', heap2', n2).
Proof.
  intros phi2 phi2' heap2 heap2' n2 phi1 HSteps.
  dependent induction HSteps.
  - econstructor.
  - econstructor. econstructor. assumption.
  - econstructor.
    + eapply IHHSteps1.
      * reflexivity.
      * reflexivity. 
    + eapply IHHSteps2.
      * reflexivity.
      * reflexivity.    
Qed.


Lemma Read_Preserved :
  forall r1 l1 v1 phi2 phi2' heap0 heap2',
    heap0 !! (r1, l1) = Some v1 ->
    Disjoint_Traces (phi_as_list (Phi_Elem (DA_Read r1 l1 v1))) (phi_as_list phi2) ->
    (phi2, heap0) ===> (phi2', heap2') ->
     heap2' !! (r1, l1) = Some v1.
Proof.
  intros r1 l1 v1 phi2 phi2' heap0 heap2' HFind HDisj HStep.
  dependent induction HStep.
  - assert (Disjoint_Dynamic (DA_Read r1 l1 v1) (DA_Alloc r l v))
      by (inversion HDisj; apply H; simpl; intuition).
    inversion H; subst.
    apply H_diff_keys_2; auto.
  - assumption.
  - assert (Disjoint_Dynamic (DA_Read r1 l1 v1) (DA_Write r l v))
      by (inversion HDisj; apply H0; simpl; intuition).
    inversion H0; subst.
    apply H_diff_keys_2; auto.
  - eapply IHHStep; try reflexivity.
    + eassumption.
    + replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0) in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj; intuition.
  - eapply IHHStep; try reflexivity.
    + eassumption.
    + replace (phi_as_list (Phi_Seq Phi_Nil phi0)) with (phi_as_list Phi_Nil ++ phi_as_list phi0) in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj; intuition.
  - assumption.
  - eapply IHHStep; try reflexivity.
    + eassumption.
    + replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0) in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj; intuition.
  - eapply IHHStep; try reflexivity.
    + eassumption.
    + replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0) in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj; intuition.
  - assumption.
Qed.

Lemma Disjointness_Preserves_Update_Alloc:
  forall phi1 phi1' heap heap' r l v, 
  (phi1, heap) ===> (phi1', heap') ->
  Disjoint_Traces (DA_Alloc r l v :: nil) (phi_as_list phi1) ->
  exists heapA,
    heapA ≡@{Heap} (update_H (r, l, v) heap') /\
    (phi1, update_H (r, l, v) heap) ===> (phi1', heapA).
Proof.
  intros phi1 phi1' heap heap' r l v H1 H2.
  generalize dependent r.
  generalize dependent l.
  generalize dependent v. 
  dependent induction H1; intros; inversion H2; subst; simpl in H.
  - assert (Disjoint_Dynamic (DA_Alloc r0 l0 v0) (DA_Alloc r l v)) by (apply H; intuition).
    inversion H0; subst. 
    exists (update_H (r, l, v) (update_H (r0, l0, v0) heap)). split.
    + unfold update_H; unfold equiv, heap_equiv; simpl. 
      apply insert_commute. auto.
    + constructor.
  - assert (Disjoint_Dynamic (DA_Alloc r0 l0 v0) (DA_Read r l v)) by (apply H0; apply in_eq).
    inversion H1; subst. exists ( update_H (r0, l0, v0) heap'). split.
    + reflexivity.
    + constructor.
      apply  H_diff_keys_2; [ simpl | ]; assumption.
  - assert (Disjoint_Dynamic (DA_Alloc r0 l0 v0) (DA_Write r l v)) by (apply H0; apply in_eq).
    inversion H1; subst. unfold update_H; simpl.
    exists ( <[(r, l):=v]> ( <[ (r0, l0):= v0 ]> heap)). split.
    + unfold update_H; unfold equiv, heap_equiv; simpl. 
      apply insert_commute. auto.
    + constructor.
      unfold find_H in *. intro. apply lookup_insert_None in H3.
      apply H. destruct H3. assumption.
  - simpl in H2. replace (DA_Alloc r l v :: nil)
      with (phi_as_list (Phi_Elem (DA_Alloc r l v))) in H2
      by (simpl; reflexivity).
    apply Disjointness_app_app_and_l in H2. destruct H2.
    edestruct IHPhi_Heap_Step; eauto. exists x. constructor.
    + inversion H3. assumption.
    + inversion H3. constructor. assumption.
  - edestruct IHPhi_Heap_Step; eauto. exists x. constructor.
    + inversion H0. assumption.
    + inversion H0. constructor. assumption.
  - exists (update_H (r, l, v) heap'). split; [reflexivity |  constructor].
  - simpl in H2. replace (DA_Alloc r l v :: nil)
      with (phi_as_list (Phi_Elem (DA_Alloc r l v))) in H2
      by (simpl; reflexivity).
    apply Disjointness_app_app_and_l in H2. destruct H2.
    edestruct IHPhi_Heap_Step; eauto. exists x. constructor.
    + inversion H3. assumption.
    + inversion H3. constructor. assumption.
  -  simpl in H2. replace (DA_Alloc r l v :: nil) with (phi_as_list (Phi_Elem (DA_Alloc r l v))) in H2
      by (simpl; reflexivity).
    apply Disjointness_app_app_and_l in H2. destruct H2.
    edestruct IHPhi_Heap_Step; eauto. exists x. constructor.
    + inversion H3. assumption.
    + inversion H3. constructor. assumption.
  - exists (update_H (r, l, v) heap'). split;  [reflexivity |  constructor].
Qed.

Lemma Disjointness_Preserves_Update_Write:
  forall phi1 phi1' heap heap' r l v, 
  (phi1, heap) ===> (phi1', heap') ->
  Disjoint_Traces (DA_Write r l v :: nil) (phi_as_list phi1) ->
  exists heapA,
    heapA  ≡@{Heap} (update_H (r, l, v) heap') /\
    (phi1, update_H (r, l, v) heap) ===> (phi1', heapA).
Proof.
  intros phi1 phi1' heap heap' r l v H1 H2.
  generalize dependent r.
  generalize dependent l.
  generalize dependent v.
  dependent induction H1; intros; inversion H2; subst; simpl in H.
  - assert (Disjoint_Dynamic (DA_Write r0 l0 v0) (DA_Alloc r l v)) by (apply H; intuition).
    inversion H0; subst. 
    exists (update_H (r, l, v) (update_H (r0, l0, v0) heap)). split.
    + unfold update_H; unfold equiv, heap_equiv; simpl. 
      apply insert_commute. auto.
    + constructor.
  - assert (Disjoint_Dynamic (DA_Write r0 l0 v0) (DA_Read r l v)) by (apply H0; apply in_eq).
    inversion H1; subst. exists ( update_H (r0, l0, v0) heap'). split.
    + reflexivity.
    + constructor.
      apply  H_diff_keys_2; [ intuition | assumption ]. 
  - assert (Disjoint_Dynamic (DA_Write r0 l0 v0) (DA_Write r l v)) by (apply H0; apply in_eq).
    inversion H1; subst. unfold update_H; simpl. 
    exists (<[(r, l):=v]> (<[(r0, l0):=v0]> heap)). split.
    + unfold update_H; unfold equiv, heap_equiv; simpl. 
      apply insert_commute. auto.
    + constructor. intro. apply H.
      unfold find_H in *. apply lookup_insert_None in H3. now destruct H3.      
  - simpl in H2. replace (DA_Write r l v :: nil)
      with (phi_as_list (Phi_Elem (DA_Write r l v))) in H2
      by (simpl; reflexivity).
    apply Disjointness_app_app_and_l in H2. destruct H2.
    edestruct IHPhi_Heap_Step; eauto. exists x. constructor.
    + inversion H3. assumption.
    + inversion H3. constructor. assumption.
  - edestruct IHPhi_Heap_Step; eauto. exists x. constructor.
    + inversion H0. assumption.
    + inversion H0. constructor. assumption.
  - exists (update_H (r, l, v) heap'). split; [reflexivity | constructor ].
  - simpl in H2. replace (DA_Write r l v :: nil) with (phi_as_list (Phi_Elem (DA_Write r l v))) in H2
      by (simpl; reflexivity).
    apply Disjointness_app_app_and_l in H2. destruct H2.
    edestruct IHPhi_Heap_Step; eauto. exists x. constructor.
    + inversion H3. assumption.
    + inversion H3. constructor. assumption.
  -  simpl in H2. replace (DA_Write r l v :: nil) with (phi_as_list (Phi_Elem (DA_Write r l v))) in H2
      by (simpl; reflexivity).
    apply Disjointness_app_app_and_l in H2. destruct H2.
    edestruct IHPhi_Heap_Step; eauto. exists x. constructor.
    + inversion H3. assumption.
    + inversion H3. constructor. assumption.
  - exists (update_H (r, l, v) heap'). split; [apply reflexivity | constructor ].
Qed.

Lemma Aux_Aux_Step_Ext_Heap :
forall phi heapA heapB phi' heapA',
   (phi, heapA) ===> (phi', heapA') ->
   heapA ≡@{Heap} heapB ->
   exists heapB',
     heapA' ≡@{Heap} heapB' /\
     (phi, heapB) ===> (phi', heapB').
Proof.
  intros phi heapA heapB phi' heapA' HStep.
  generalize dependent heapB.
  dependent induction HStep; intros heapB HEqual.
  - { exists (update_H (r, l, v) heapB). split.
      - unfold equiv, heap_equiv in *; unfold update_H in *; simpl in *.
        subst. reflexivity.
      - constructor. }
  - { exists heapB. split.
      - assumption.
      - constructor.
        unfold find_H in *. unfold equiv, heap_equiv in HEqual. now subst. }
  - { exists (update_H (r, l, v) heapB). split.
      - unfold update_H in *; simpl in *.
        unfold equiv, heap_equiv in *; now subst.
      - constructor.
        unfold equiv, heap_equiv in *; now subst. }
 - edestruct IHHStep; eauto. exists x; split; [ intuition | ]. 
    constructor. intuition.
  - edestruct IHHStep; eauto. exists x; split; [ intuition | ].
    constructor. intuition.
  - exists heapB. split; [assumption | constructor; auto].
  - edestruct IHHStep; eauto. exists x; split; [ intuition | ]. 
    constructor. intuition.
  - edestruct IHHStep; eauto. exists x; split; [ intuition | ]. 
    constructor. intuition.
  - exists heapB; split; [assumption | constructor].
Qed.

Lemma Aux_Step_Ext_Heap :
forall phi heapA heapB phi' heapA' n',
   (phi, heapA) =a=>* (phi', heapA', n') ->
   heapA  ≡@{Heap} heapB ->
   exists heapB',
     heapA' ≡@{Heap} heapB' /\
     (phi, heapB) =a=>* (phi', heapB', n').
Proof.
  intros  phi heapA heapB phi' heapA' n' H1 H2 .  
  generalize dependent heapB. 
  dependent induction H1; intros.
  - { exists heapB. intuition. constructor. }
  - edestruct Aux_Aux_Step_Ext_Heap.
    + eauto.
    + eassumption.
    + exists x; split.
      * intuition.
      * constructor. intuition.
  - edestruct (IHPhi_Heap_StepsAux1); eauto.
    edestruct (IHPhi_Heap_StepsAux2); eauto.
    exists x0. intuition.
    replace (S (n'0 + n'')) with (1 + n'0 + n'') by (simpl; reflexivity).
    econstructor. eassumption.
    unfold equiv, heap_equiv in H1. now subst.
Qed.

Lemma Par_Step_Alloc_Alloc :
  forall phi1 r1 l1 v1 phi2 r2 l2 v2 phi1' phi2' heapa heapb heap1' heap2',
    phi1 = Phi_Elem (DA_Alloc r1 l1 v1) ->
    phi2 = Phi_Elem (DA_Alloc r2 l2 v2) ->
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    heapa ≡@{Heap} heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA, exists heapB,
      heapA ≡@{Heap} heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros  phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2'
          H1 H2 Det1 HDet2 HDisj HConf HEqual HStep1 HStep2; subst.
  inversion HStep1; inversion HStep2; subst.
  exists (update_H (r0, l0, v0) (update_H (r, l, v) heapa)).
  exists (update_H (r, l, v) (update_H (r0, l0, v0) heapb)). repeat split. 
  - inversion HDisj; subst. simpl in H. 
    assert (Disjoint_Dynamic (DA_Alloc r l v) (DA_Alloc r0 l0 v0))
      by (apply H; left; reflexivity).
    inversion H0; subst. unfold update_H in *. simpl in *.
    inversion H0; subst. unfold update_H in *. simpl in *. 
    destruct (keys_eq_dec (r, l) (r0, l0)).
    + unfold keys_eq, fst, snd, NPeano.Nat.eq in *.
      destruct k; subst.
      contradiction.
    + clear n.
      unfold equiv, heap_equiv in HEqual. rewrite HEqual.
      apply insert_commute. symmetry. assumption.
  - do 2 constructor.    
  - econstructor. inversion HDisj; subst.
    assert (Disjoint_Dynamic (DA_Alloc r l v) (DA_Alloc r0 l0 v0))
      by (apply H; simpl; auto). 
    constructor.
Qed.

Lemma Par_Step_Write_Write :
  forall phi1 r1 l1 v1 phi2 r2 l2 v2 phi1' phi2' heapa heapb heap1' heap2',
    phi1 = Phi_Elem (DA_Write r1 l1 v1) ->
    phi2 = Phi_Elem (DA_Write r2 l2 v2) ->
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    heapa ≡@{Heap} heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA, exists heapB,
      heapA ≡@{Heap} heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros  phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2'
          H1 H2 Det1 HDet2 HDisj HConf HEqual HStep1 HStep2; subst.
  inversion HStep1; inversion HStep2; subst.
  exists (update_H (r0, l0, v0) (update_H (r, l, v) heapa)).
  exists (update_H (r, l, v) (update_H (r0, l0, v0) heapb)). repeat split. 
  -  inversion HDisj; subst. simpl in H. 
     assert (Disjoint_Dynamic (DA_Write r l v) (DA_Write r0 l0 v0))
       by (apply H; left; reflexivity).
    inversion H1; subst. unfold update_H in *. simpl in *.
    inversion H1; subst. unfold update_H in *. simpl in *. 
    destruct (keys_eq_dec (r, l) (r0, l0)).
    + unfold keys_eq, fst, snd, NPeano.Nat.eq in *; subst.
      inversion H1; subst. contradict H5. intuition.
    + clear n.
      unfold equiv, heap_equiv in HEqual. rewrite HEqual.
      apply insert_commute. assumption.
  - do 2 constructor.
    inversion HDisj; subst. simpl in H. 
    assert (Disjoint_Dynamic (DA_Write r l v) (DA_Write r0 l0 v0))
      by (apply H; left; reflexivity).
    inversion H1; subst. intro. apply H7.
    unfold find_H, update_H in H7, H2. unfold find_H. simpl in *.
    apply lookup_insert_None in H2. destruct H2.
    unfold equiv, heap_equiv in HEqual. now subst.
  - do 2 constructor.
    inversion HDisj; subst. simpl in H. 
    assert (Disjoint_Dynamic (DA_Write r l v) (DA_Write r0 l0 v0))
      by (apply H; left; reflexivity).
     inversion H1; subst. intro. apply H7.
    unfold find_H, update_H in H7, H2. unfold find_H. simpl in *.
    apply lookup_insert_None in H2. destruct H2.
    unfold equiv, heap_equiv in HEqual. now subst.
Qed.

Lemma Par_Step_Alloc_Read :
  forall phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2',
    phi1 = Phi_Elem (DA_Alloc r l v) ->
    phi2 = Phi_Elem (DA_Read r0 l0 v0) -> 
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    heapa ≡@{Heap} heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA heapB,
      heapA ≡@{Heap} heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros  phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2'
          H1 H2 Det1 HDet2 HDisj HConf HEqual HStep1 HStep2; subst.
  inversion HStep1; inversion HStep2; subst.
  edestruct Aux_Aux_Step_Ext_Heap with (heapA:=heapa); eauto.
  exists (update_H (r, l, v) heapa); exists x; repeat split.
  - intuition.
  - do 2 constructor.
    inversion HDisj; subst. simpl in H. 
    assert (Disjoint_Dynamic (DA_Alloc r l v) (DA_Read r0 l0 v0))
      by (apply H0; left; reflexivity).
    inversion H1; subst. eapply H_diff_keys_2; eauto.
    unfold equiv, heap_equiv in HEqual. now subst.
  - constructor. intuition.
Qed.

Lemma Par_Step_Write_Read :
  forall phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2',
    phi1 = Phi_Elem (DA_Write r l v) ->
    phi2 = Phi_Elem (DA_Read r0 l0 v0) -> 
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    heapa ≡@{Heap} heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA heapB,
      heapA ≡@{Heap} heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros  phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2'
          H1 H2 Det1 HDet2 HDisj HConf HEqual HStep1 HStep2; subst.
  inversion HStep1; inversion HStep2; subst.
  edestruct Aux_Aux_Step_Ext_Heap  with (heapA:=heapa); eauto.
  exists (update_H (r, l, v) heapa). exists x; repeat split.
  - intuition.
  - do 2 constructor. 
    inversion HDisj; subst. simpl in H. 
    assert (Disjoint_Dynamic (DA_Write r l v) (DA_Read r0 l0 v0))
      by (apply H1; left; reflexivity).
    inversion H2; subst. eapply H_diff_keys_2; eauto.
    unfold equiv, heap_equiv in HEqual. now subst.
  - constructor. intuition.
Qed.

Lemma Par_Step_Read_Alloc :
  forall phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2',
    phi1 = Phi_Elem (DA_Read r l v) ->
    phi2 = Phi_Elem (DA_Alloc r0 l0 v0) -> 
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    heapa ≡@{Heap} heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA heapB,
      heapA ≡@{Heap} heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros  phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2'
          H1 H2 Det1 HDet2 HDisj HConf HEqual HStep1 HStep2; subst.
  inversion HStep1; inversion HStep2; subst. 
  edestruct Aux_Aux_Step_Ext_Heap with (heapA:=heap1'); eauto.
  unfold equiv, heap_equiv in HEqual.
  exists (update_H (r0, l0, v0) heap1');
    exists (update_H (r0, l0, v0) heapb); repeat split.
  - unfold find_H, update_H in H0. unfold update_H. simpl in *.
    unfold equiv, heap_equiv in HEqual. now subst.
  - inversion HDisj; subst. simpl in H1. 
    assert (Disjoint_Dynamic (DA_Read r l v) (DA_Alloc r0 l0 v0))
      by (apply H1; left; reflexivity).
    inversion H2; subst. constructor. constructor.
  - do 2 constructor. inversion HStep2; subst.
    inversion HDisj; subst. simpl in H. 
    assert (Disjoint_Dynamic (DA_Read r l v) (DA_Alloc r0 l0 v0))
      by (apply H1; left; reflexivity).
    inversion H2; subst.
    eapply H_diff_keys_2; auto.
Qed.

Lemma Par_Step_Read_Write :
  forall phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2',
    phi1 = Phi_Elem (DA_Read r l v) ->
    phi2 = Phi_Elem (DA_Write r0 l0 v0) -> 
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    heapa ≡@{Heap} heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA heapB,
      heapA  ≡@{Heap} heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros  phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2'
          H1 H2 Det1 HDet2 HDisj HConf HEqual HStep1 HStep2; subst.
  inversion HStep1; inversion HStep2; subst.
  edestruct Aux_Aux_Step_Ext_Heap with (heapA:=heap1'); eauto.
  exists (update_H (r0, l0, v0) heap1');
    exists (update_H (r0, l0, v0) heapb); repeat split.
  - unfold find_H, update_H in H0. unfold update_H. simpl in *.
    unfold equiv, heap_equiv in HEqual. now subst.
  - inversion HDisj; subst. simpl in H1. 
    assert (Disjoint_Dynamic (DA_Read r l v) (DA_Write r0 l0 v0))
      by (apply H1; left; reflexivity).
    inversion H; subst. constructor.  constructor.
    intro. apply H7.
    unfold equiv, heap_equiv in HEqual. now subst.    
  - do 2 constructor. inversion HStep2; subst.
    inversion HDisj; subst. simpl in H1. 
    assert (Disjoint_Dynamic (DA_Read r l v) (DA_Write r0 l0 v0))
      by (apply H1; left; reflexivity).
    inversion H3; subst.
    eapply H_diff_keys_2; auto.
    unfold equiv, heap_equiv in HEqual. now subst.    
Qed.

Lemma Par_Step_Alloc_Write :
  forall phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2',
    phi1 = Phi_Elem (DA_Alloc r l v) ->
    phi2 = Phi_Elem (DA_Write r0 l0 v0) -> 
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    heapa ≡@{Heap} heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA heapB,
      heapA ≡@{Heap} heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros  phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2'
          H1 H2 Det1 HDet2 HDisj HConf HEqual HStep1 HStep2; subst.
  inversion HStep1; inversion HStep2; subst. 
  exists (update_H (r0, l0, v0) (update_H (r, l, v) heapa)).
  exists (update_H (r, l, v) (update_H (r0, l0, v0) heapb)). repeat split.
  - inversion HDisj; subst. 
    assert (Disjoint_Dynamic (DA_Alloc r l v) (DA_Write r0 l0 v0))
      by (apply H; left; reflexivity).
    inversion H0; subst. unfold update_H in *. simpl in *. 
    destruct (keys_eq_dec (r, l) (r0, l0)).
    + unfold keys_eq, fst, snd, NPeano.Nat.eq in *; subst.
      contradict H2. intuition.
    + clear n.
      unfold equiv, heap_equiv in HEqual. rewrite HEqual.
      apply insert_commute. symmetry. assumption.
  - inversion HDisj; subst.
    assert (Disjoint_Dynamic (DA_Alloc r l v) (DA_Write r0 l0 v0))
      by (apply H; left; reflexivity).
    inversion H0; subst. unfold update_H in *. simpl in *. 
    constructor. constructor.
    unfold find_H in H6. unfold find_H. simpl in *.
    intro. apply H6.
    apply lookup_insert_None in H1. destruct H1.
    unfold equiv, heap_equiv in HEqual. now subst.    
  - inversion HDisj; subst. simpl in H. constructor. constructor.
Qed.    

Lemma Par_Step_Write_Alloc :
  forall phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2',
    phi1 = Phi_Elem (DA_Write r l v) ->
    phi2 = Phi_Elem (DA_Alloc r0 l0 v0) -> 
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    heapa ≡@{Heap} heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA heapB,
      heapA ≡@{Heap} heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros  phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2'
          H1 H2 Det1 HDet2 HDisj HConf HEqual HStep1 HStep2; subst.
  inversion HStep1; inversion HStep2; subst. 
  exists (update_H (r0, l0, v0) (update_H (r, l, v) heapa)).
  exists (update_H (r, l, v) (update_H (r0, l0, v0) heapb)). repeat split.
  - inversion HDisj; subst. 
    assert (Disjoint_Dynamic (DA_Write r l v) (DA_Alloc r0 l0 v0))
      by (apply H; left; reflexivity).
    inversion H1; subst. unfold update_H in *. simpl in *. 
    destruct (keys_eq_dec (r, l) (r0, l0)).
    + unfold keys_eq, NPeano.Nat.eq in k; simpl in k; destruct k.
      contradict H3. subst. reflexivity.
    + clear n.
      unfold equiv, heap_equiv in HEqual. rewrite HEqual.
      apply insert_commute. assumption.
  - inversion HDisj; subst. 
    assert (Disjoint_Dynamic (DA_Write r l v)  (DA_Alloc r0 l0 v0))
      by (apply H; left; reflexivity).
    inversion H1; subst. unfold update_H in *. simpl in *.
    constructor. constructor.
  - constructor. constructor.
    inversion HDisj; subst. 
    assert (Disjoint_Dynamic (DA_Write r l v)  (DA_Alloc r0 l0 v0))
      by (apply H; left; reflexivity).
    inversion H1; subst. unfold update_H in *. simpl in *.
    unfold find_H in H0. unfold find_H. simpl in *.
    intro. apply H0.
    apply lookup_insert_None in H2. destruct H2.
    unfold equiv, heap_equiv in HEqual. now subst.    
Qed.    
    
Lemma Phi_Heap_Step_Progress :
  forall phi heap heap',
    (phi, heap) ===> (phi, heap') ->
    False.
Proof.
  induction phi; intros heap heap' HStep.
  + inversion HStep.
  + inversion HStep.
  + inversion HStep; subst.
    - eapply IHphi1; eassumption.
    - eapply IHphi2; eassumption.
  + inversion HStep; subst.
    - eapply IHphi1; eassumption.
    - eapply IHphi2; eassumption.
Qed.


Lemma Par_Step_Equal :
   forall phi1 phi2 phi1' phi2' heap0 heap1' heap2',
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    (phi1, heap0) ===> (phi1', heap1') ->
    (phi2, heap0) ===> (phi2', heap2') ->
    exists heapA, exists heapB,
      heapA ≡@{Heap} heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros phi1 phi2 phi1' phi2' heap0 heap1' heap2' HDet1 HDet2 HDisj HConf HStep1 HStep2.
  generalize dependent phi2.
  dependent induction HStep1; intros. 
  - dependent destruction HStep2. 
    + eapply Par_Step_Alloc_Alloc; eauto || econstructor.
    + eapply Par_Step_Alloc_Read; eauto  || econstructor; assumption.
    + eapply Par_Step_Alloc_Write; eauto || econstructor; assumption.
    + replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Alloc in HStep2; eauto.
      destruct HStep2 as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - assumption.
        - do 2 constructor; assumption.
        - do 2 constructor. }
    + replace (phi_as_list (Phi_Seq Phi_Nil phi0)) with (phi_as_list Phi_Nil ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Alloc in HStep2; eauto.
      destruct HStep2 as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - assumption.
        - do 2 constructor; assumption.
        - do 2 constructor. }
    + { exists (update_H (r, l, v) heap2'). exists (update_H (r, l, v) heap2'); repeat split; do 2  constructor. }
    + replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Alloc in HStep2; eauto.
      destruct HStep2 as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - assumption.
        - do 2 constructor; assumption.
        - do 2 constructor.   }
    + replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Alloc in HStep2; eauto.
      destruct HStep2 as [? [? ?]].
      { exists x. exists  (update_H (r, l, v) heap2'); repeat split.
        - assumption.
        - do 2 constructor; assumption.
        - do 2 constructor.  }            
    + { exists (update_H (r, l, v) heap2'). exists (update_H (r, l, v) heap2'); repeat split; do 2  constructor. }
  - dependent destruction HStep2. 
    + eapply Par_Step_Read_Alloc; eauto || econstructor; assumption.
    + { exists heap2'. exists heap2'; repeat split; do 2 constructor; assumption. }
    + eapply Par_Step_Read_Write; eauto || econstructor; assumption.
    + { exists heap2'. exists heap2'. repeat split.
        - do 2 constructor; assumption.
        - do 2 constructor.
          replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
            in HDisj by (simpl; reflexivity).
          apply Disjointness_app_app_and_l in HDisj. destruct HDisj as [HD1 ?].
          replace (phi_as_list (Phi_Elem (DA_Read r l v))) with (DA_Read r l v :: nil)
            in HD1 by (simpl; reflexivity).
          eapply Read_Preserved.
          eapply H.
          eapply HD1.
          eapply HStep2. }
    + { exists heap2'. exists heap2'. repeat split.
        - do 2 constructor; assumption.
        - do 2 constructor.
          replace (phi_as_list (Phi_Seq Phi_Nil phi0)) with (phi_as_list Phi_Nil ++ phi_as_list phi0)
            in HDisj by (simpl; reflexivity).
          apply Disjointness_app_app_and_l in HDisj. destruct HDisj as [? HD1].
          replace (phi_as_list (Phi_Elem (DA_Read r l v))) with (DA_Read r l v :: nil)
            in HD1 by (simpl; reflexivity).
          eapply Read_Preserved.
          eapply H.
          eapply HD1.
          eapply HStep2. }
    + exists heap2'. exists heap2'. repeat split; do 2 constructor. assumption.
    + { exists heap2'. exists heap2'. repeat split.
        - do 2 constructor; assumption.
        - do 2 constructor.
          replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
            in HDisj by (simpl; reflexivity).
          apply Disjointness_app_app_and_l in HDisj. destruct HDisj as [HD1 ?].
          replace (phi_as_list (Phi_Elem (DA_Read r l v))) with (DA_Read r l v :: nil)
            in HD1 by (simpl; reflexivity).
          eapply Read_Preserved.
          eapply H.
          eapply HD1.
          eapply HStep2. }
    + { exists heap2'. exists heap2'. repeat split.
        - do 2 constructor; assumption.
        - do 2 constructor.
          replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
            in HDisj by (simpl; reflexivity).
          apply Disjointness_app_app_and_l in HDisj. destruct HDisj as [? HD1].
          replace (phi_as_list (Phi_Elem (DA_Read r l v))) with (DA_Read r l v :: nil)
            in HD1 by (simpl; reflexivity).
          eapply Read_Preserved.
          eapply H.
          eapply HD1.
          eapply HStep2. }
    + { exists heap2'. exists heap2'. repeat split; do 2 constructor. assumption. }
  - dependent destruction HStep2.  
    + eapply Par_Step_Write_Alloc; eauto || econstructor; assumption.
    + eapply Par_Step_Write_Read; eauto || econstructor; assumption.
    + eapply Par_Step_Write_Write; eauto || econstructor; assumption.
    + eapply H_monotonic_updates in H; eauto.
      replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Write in HStep2; eauto.
      destruct HStep2 as [? [? ?]].   
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - assumption.
        - do 2 constructor. assumption.
        - constructor. constructor. assumption.
      }
    + eapply H_monotonic_updates in H; eauto.
      replace (phi_as_list (Phi_Seq Phi_Nil phi0)) with (phi_as_list Phi_Nil ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Write in HStep2; eauto.
      destruct HStep2 as [? [? ?]].
      { exists x.  exists (update_H (r, l, v) heap2'); repeat split.
        - assumption.
        - do 2 constructor; assumption.
        - constructor. constructor. assumption. }
    + { exists (update_H (r, l, v) heap2'). exists (update_H (r, l, v) heap2'); repeat split; do 2  constructor; assumption. }
    + eapply H_monotonic_updates in H; eauto.
      replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Write in HStep2; eauto.
      destruct HStep2 as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - assumption.
        - do 2 constructor; assumption.
        - constructor. constructor. assumption. }
    + eapply H_monotonic_updates in H; eauto.
      replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Write in HStep2; eauto.
      destruct HStep2 as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - assumption.
        - do 2 constructor; assumption.
        - constructor. constructor. assumption.  }            
    + { exists (update_H (r, l, v) heap2'). exists (update_H (r, l, v) heap2'); repeat split; do 2  constructor; assumption. }
  -  inversion HDet1; subst.
     edestruct IHHStep1 with (phi1:=phi0) (phi1':=phi1'0) (phi2:=phi1) as [heapA [heapB [? [? ?]]]]; auto.
     + simpl in HDisj. apply Disjointness_app_app_and_r in HDisj. destruct HDisj. assumption.
     + simpl in HConf. inversion HDet1.
       apply Conflictness_app_and_r in HConf; [ destruct HConf  | | | ]; assumption.
     + exists heapA. exists heapB. repeat split.
       * assumption.
       * inversion H0; subst.
         { apply Phi_Heap_Step_Progress in HStep2. contradiction. }
         { constructor. assumption. }
       * inversion H3; subst.
         { constructor. constructor. assumption. }
         { apply Phi_Heap_Step_Progress in H3. contradiction. }    
  - inversion HDet1; subst.
    inversion HDisj; subst. simpl in H.
    assert ( exists heapA heapB : Heap,
        heapA ≡@{Heap} heapB /\
        (Phi_Par phi2'0 phi0, heap1') ===> (Phi_Par phi2'0 phi2', heapA) /\
          (Phi_Par phi2 phi2', heap2') ===> (Phi_Par phi2'0 phi2', heapB)) by ( eapply IHHStep1; auto).
    destruct H0  as [HA [ HB [HEq [Ht1 Ht2]]]].
    exists HA, HB. repeat split; [assumption | | ].
    + rewrite Phi_Seq_Nil_L. assumption.
    + do 2 rewrite Phi_Seq_Nil_L. assumption.
  - exists heap2', heap2'. split.
    + reflexivity.
    + split.
      * constructor. assumption.
      * constructor. constructor.
  -  inversion HDet1; subst.
     edestruct IHHStep1 with (phi1:=phi0) (phi1':=phi1'0) (phi2:=phi1) as [heapA [heapB [? [? ?]]]]; auto.   
     + simpl in HDisj. apply Disjointness_app_app_and_r in HDisj. destruct HDisj. assumption.
     + simpl in HConf. inversion HDet1.
       apply Conflictness_app_and_r in HConf; [ destruct HConf  | | | ]; assumption.
     + exists heapA. exists heapB. repeat split.
       * assumption.
       * inversion H0; subst.
         { apply Phi_Heap_Step_Progress in HStep2. contradiction. }
         { constructor. assumption. }
       * inversion H4; subst.
         { constructor. constructor. assumption. }
         { apply Phi_Heap_Step_Progress in H4. contradiction. }    
  -  inversion HDet1; subst.
     edestruct IHHStep1 with (phi1:=phi2) (phi1':=phi2'0) (phi2:=phi1) as [heapA [heapB [? [? ?]]]]; auto.   
     + simpl in HDisj. apply Disjointness_app_app_and_r in HDisj. destruct HDisj. assumption.
     + simpl in HConf. inversion HDet1.
       apply Conflictness_app_and_r in HConf; [ destruct HConf  | | | ]; assumption.
     + exists heapA. exists heapB. repeat split.
       * assumption.
       * inversion H0; subst.
         { apply Phi_Heap_Step_Progress in HStep2. contradiction. }
         { constructor. assumption. }
       * inversion H4; subst.
         { constructor. constructor. assumption. }
         { apply Phi_Heap_Step_Progress in H4. contradiction. }   
  - inversion HDisj; subst. simpl in H.
    exists heap2', heap2'. split.
    + reflexivity.
    + split.
      * constructor. assumption.
      * constructor. constructor.       
Qed.


Lemma Par_Step_Equal_new :
   forall phi1 phi2 phi1' phi2' heapa heapb heap1' heap2',
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    heapa ≡@{Heap} heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA, exists heapB,
      heapA ≡@{Heap} heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros phi1 phi2 phi1' phi2' heapa heapb heap1' heap2' HDet1 HDet2 HDisj HConf HEqual HStep1 HStep2.
  generalize dependent phi2.
  dependent induction HStep1; intros.
  - dependent destruction HStep2.  
    + eapply Par_Step_Alloc_Alloc; eauto || econstructor.
    + eapply Par_Step_Alloc_Read; eauto  || econstructor; assumption.
    + eapply Par_Step_Alloc_Write; eauto || econstructor; assumption.
    + apply symmetry in HEqual. 
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
       as [heap2'' [HEqual' HStep2']]. clear HStep2.
      replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Alloc in HStep2'; eauto.  
      destruct HStep2' as [heapa' [? ?]]. 
      { exists heapa'. exists (update_H (r, l, v) heap2'); repeat split. 
        - unfold equiv, heap_equiv in *; unfold update_H in *; simpl in *.
          rewrite HEqual'. assumption.          
        - do 2 constructor. assumption.
        - do 2 constructor. }
    + apply symmetry in HEqual.
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
       as [heap2'' [HEqual' HStep2']]. clear HStep2.
      replace (phi_as_list (Phi_Seq Phi_Nil phi0)) with (phi_as_list Phi_Nil ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Alloc in HStep2'; eauto.
      destruct HStep2' as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - unfold equiv, heap_equiv in *; unfold update_H in *; simpl in *.
          rewrite HEqual'. assumption.
        - do 2 constructor; assumption.
        - do 2 constructor. }
    + { exists (update_H (r, l, v) heapa). exists (update_H (r, l, v) heap2'); repeat split.
        - unfold equiv, heap_equiv in *; unfold update_H in *; simpl in *.
          rewrite HEqual.
          reflexivity.
        - do 2  constructor.
        - do 2 constructor. }
    + apply symmetry in HEqual.
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
        as [heap2'' [HEqual' HStep2']]. clear HStep2.
      replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Alloc in HStep2'; eauto.
      destruct HStep2' as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - unfold equiv, heap_equiv in *; unfold update_H in *; simpl in *.
          rewrite HEqual'. assumption.          
        - do 2 constructor; assumption.
        - do 2 constructor.   }
    + apply symmetry in HEqual.
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
        as [heap2'' [HEqual' HStep2']]. clear HStep2.
      replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Alloc in HStep2'; eauto.
      destruct HStep2' as [? [? ?]].
      { exists x. exists  (update_H (r, l, v) heap2'); repeat split.
        - unfold equiv, heap_equiv in *; unfold update_H in *; simpl in *.
          rewrite HEqual'. assumption.
        - do 2 constructor; assumption.
        - do 2 constructor.  }            
    + { exists (update_H (r, l, v) heapa). exists (update_H (r, l, v) heap2'); repeat split; try (do 2  constructor). 
        unfold equiv, heap_equiv in *; unfold update_H in *; simpl in *.
        rewrite HEqual. reflexivity. }
  - dependent destruction HStep2. 
    + eapply Par_Step_Read_Alloc; eauto || econstructor; assumption.
    + { exists heap1'; exists heap2'; repeat split.
        - assumption.
        - constructor. constructor. unfold equiv, heap_equiv in HEqual.
          rewrite HEqual. assumption.
        - constructor. constructor. unfold equiv, heap_equiv in HEqual.
          rewrite <- HEqual. assumption.
      }
    + eapply Par_Step_Read_Write; eauto || econstructor; assumption.
    + { apply symmetry in HEqual.
        edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
        as [heap2'' [HEqual' HStep2']].
        exists heap2''. exists heap2'. repeat split.
        - apply symmetry. assumption.
        - do 2 constructor. assumption.
        - do 2 constructor. 
          replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
            in HDisj by (simpl; reflexivity).
          apply Disjointness_app_app_and_l in HDisj. destruct HDisj as [HD1 ?].
          replace (phi_as_list (Phi_Elem (DA_Read r l v))) with (DA_Read r l v :: nil)
            in HD1 by (simpl; reflexivity).
          unfold equiv, heap_equiv in HEqual'. rewrite HEqual'.
          eapply Read_Preserved.
          eapply H.
          eapply HD1.
          eapply HStep2'. }
    + { apply symmetry in HEqual.
        edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
          as [heap2'' [HEqual' HStep2']]. clear HStep2.
        exists heap2''. exists heap2'. repeat split.
        - apply symmetry. assumption.
        - do 2 constructor; assumption.
        - do 2 constructor.
          replace (phi_as_list (Phi_Seq Phi_Nil phi0)) with (phi_as_list Phi_Nil ++ phi_as_list phi0)
            in HDisj by (simpl; reflexivity).
          apply Disjointness_app_app_and_l in HDisj. destruct HDisj as [? HD1].
          replace (phi_as_list (Phi_Elem (DA_Read r l v))) with (DA_Read r l v :: nil)
            in HD1 by (simpl; reflexivity).
          unfold equiv, heap_equiv in HEqual'. rewrite HEqual'. eapply Read_Preserved.
          eapply H.
          eapply HD1.
          eapply HStep2'. }
    + { exists heap1'. exists heap2'. repeat split; auto.
        - do 2 constructor.
        - do 2 constructor.
          rewrite <- H. unfold equiv, heap_equiv in HEqual.
          symmetry. now subst.
      }
    + { apply symmetry in HEqual.
        edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
           as [heap2'' [HEqual' HStep2']]. clear HStep2.
        exists heap2''. exists heap2'. repeat split.
        - apply symmetry. assumption.
        - do 2 constructor; assumption.
        - do 2 constructor.
          replace (phi_as_list (Phi_Seq phi1 phi0))
            with (phi_as_list phi1 ++ phi_as_list phi0)
            in HDisj by (simpl; reflexivity).
          apply Disjointness_app_app_and_l in HDisj. destruct HDisj as [HD1 ?].
          replace (phi_as_list (Phi_Elem (DA_Read r l v))) with (DA_Read r l v :: nil)
            in HD1 by (simpl; reflexivity).
          unfold equiv, heap_equiv in HEqual'. rewrite HEqual'.  eapply Read_Preserved.
          eapply H.
          eapply HD1.
          eapply HStep2' . }
    + { apply symmetry in HEqual.
        edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
          as [heap2'' [HEqual' HStep2']]. clear HStep2.
        exists heap2''. exists heap2'. repeat split.
        - apply symmetry. assumption.
        - do 2 constructor; assumption.
        - do 2 constructor.
          replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
            in HDisj by (simpl; reflexivity).
          apply Disjointness_app_app_and_l in HDisj. destruct HDisj as [? HD1].
          replace (phi_as_list (Phi_Elem (DA_Read r l v))) with (DA_Read r l v :: nil)
            in HD1 by (simpl; reflexivity).
          unfold equiv, heap_equiv in HEqual'. rewrite HEqual'. eapply Read_Preserved.
          eapply H.
          eapply HD1.
          eapply HStep2'. }
    + { exists heap1'. exists heap2'. repeat split; auto.
        - do 2 constructor.
        - do 2 constructor.
          rewrite <- H. unfold equiv, heap_equiv in HEqual.
          symmetry. now subst.
      }
  - dependent destruction HStep2. 
    + eapply Par_Step_Write_Alloc; eauto || econstructor; assumption.
    + eapply Par_Step_Write_Read; eauto || econstructor; assumption.
    + eapply Par_Step_Write_Write; eauto || econstructor; assumption.
    + apply symmetry in HEqual.
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
        as [heap2'' [HEqual' HStep2']]. clear HStep2.
      eapply H_monotonic_updates in H; eauto.
      replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Write in HStep2'; eauto.
      destruct HStep2' as [? [? ?]].   
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        -  unfold equiv, heap_equiv in *; unfold update_H in *; simpl in *.
           rewrite HEqual'. assumption. 
        - do 2 constructor. assumption.
        - constructor. constructor.
          intro. apply H. rewrite <- HEqual'. assumption.
      }
    + apply symmetry in HEqual.
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
         as [heap2'' [HEqual' HStep2']]. clear HStep2.
      eapply H_monotonic_updates in H; eauto.
      replace (phi_as_list (Phi_Seq Phi_Nil phi0))
        with (phi_as_list Phi_Nil ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Write in HStep2'; eauto.
      destruct HStep2' as [? [? ?]].
      { exists x.  exists (update_H (r, l, v) heap2'); repeat split.
        -  unfold equiv, heap_equiv in *; unfold update_H in *; simpl in *.
           subst. reflexivity.
        - do 2 constructor; assumption.
        - constructor. constructor.
          intro. apply H. rewrite <- HEqual'. assumption. }
    + { exists (update_H (r, l, v) heapa). exists (update_H (r, l, v) heap2'); repeat split.
        -  unfold equiv, heap_equiv in *; unfold update_H in *; simpl in *.
           subst. reflexivity. 
        - constructor. constructor.
        - do 2 constructor.
          intro. apply H. unfold equiv, heap_equiv in HEqual.
          rewrite HEqual. assumption. }
    + apply symmetry in HEqual.
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
        as [heap2'' [HEqual' HStep2']]. clear HStep2.
      eapply H_monotonic_updates in H; eauto.
      replace (phi_as_list (Phi_Seq phi1 phi0))
        with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Write in HStep2'; eauto.
      destruct HStep2' as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        -  unfold equiv, heap_equiv in *; unfold update_H in *; simpl in *.
           subst. reflexivity.
        - do 2 constructor; assumption.
        - constructor. constructor.
           intro. apply H. rewrite <- HEqual'. assumption. }
    +  apply symmetry in HEqual.
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
         as [heap2'' [HEqual' HStep2']]. clear HStep2.
      eapply H_monotonic_updates in H; eauto.
      replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Write in HStep2'; eauto.
      destruct HStep2' as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - unfold equiv, heap_equiv in *; unfold update_H in *; simpl in *.
          subst. reflexivity.
        - do 2 constructor; assumption.
        - constructor. constructor.
          intro. apply H. rewrite <- HEqual'. assumption. }
    +  { exists (update_H (r, l, v) heapa). exists (update_H (r, l, v) heap2'); repeat split.
         -  unfold equiv, heap_equiv in *; unfold update_H in *; simpl in *.
            subst. reflexivity.
        - constructor. constructor.
        - do 2 constructor.
          intro. apply H. unfold equiv, heap_equiv in HEqual.
          subst. assumption. }
  - inversion HDet1; subst. clear H2.
    edestruct IHHStep1 with (phi2:=phi1)  as [heapA [heapB [? [? ?]]]]; eauto.
    + simpl in HDisj. apply Disjointness_app_app_and_r in HDisj. destruct HDisj. assumption.
    + simpl in HConf. inversion HDet1.
      apply Conflictness_app_and_r in HConf; [ destruct HConf  | | | ]; assumption.
    + exists heapA. exists heapB. repeat split.
      * assumption.
      * inversion H0; subst.
        { apply Phi_Heap_Step_Progress in HStep2. contradiction. }
        { constructor. assumption. }
      * inversion H2; subst.
        { constructor. constructor. assumption. }
        { apply Phi_Heap_Step_Progress in H2. contradiction. }
  - inversion HDet1; subst. clear H1.
    edestruct IHHStep1 with (phi2:=phi0) as [heapA [heapB [? [? ?]]]]; eauto.
    + exists heapA. exists heapB. repeat split.
      * assumption.
      * inversion H0; subst.
        { apply Phi_Heap_Step_Progress in HStep2. contradiction. }
        { constructor. assumption. }
      * inversion H1; subst.
        { constructor. constructor. assumption. }
        { apply Phi_Heap_Step_Progress in H1. contradiction. }
  -  apply symmetry in HEqual.
     edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
       as [heap2'' [HEqual' HStep2']]. clear HStep2.
     exists heap2''. exists heap2'. repeat split.
     * apply symmetry. assumption.
     * constructor; assumption.
     * constructor; constructor.
  - inversion HDet1; subst. clear H2.
    edestruct IHHStep1 with (phi2:=phi1) as [heapA [heapB [? [? ?]]]]; eauto.
    + simpl in HDisj. apply Disjointness_app_app_and_r in HDisj. destruct HDisj. assumption.
    + simpl in HConf. inversion HDet1.
      apply Conflictness_app_and_r in HConf; [ destruct HConf  | | | ]; assumption.
    + exists heapA. exists heapB. repeat split.
      * assumption.
      * inversion H0; subst.
        { apply Phi_Heap_Step_Progress in HStep2. contradiction. }
        { constructor. assumption. }
      * inversion H2; subst.
        { constructor. constructor. assumption. }
        { apply Phi_Heap_Step_Progress in H2. contradiction. }
  - inversion HDet1; subst. 
    edestruct IHHStep1 with (phi2:=phi1) as [heapA [heapB [? [? ?]]]]; eauto.
    + simpl in HDisj. apply Disjointness_app_app_and_r in HDisj. destruct HDisj. assumption.
    + simpl in HConf. inversion HDet1.
      apply Conflictness_app_and_r in HConf; [ destruct HConf  | | | ]; assumption.
    + exists heapA. exists heapB. repeat split.
      * assumption.
      * inversion H0; subst.
        { apply Phi_Heap_Step_Progress in HStep2. contradiction. }
        { constructor. assumption. }
      * inversion H4; subst.
        { constructor. constructor. assumption. }
        { apply Phi_Heap_Step_Progress in H4. contradiction. }
   -  apply symmetry in HEqual.
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
        as [heap2'' [HEqual' HStep2']]. clear HStep2.
      exists heap2''. exists heap2'. repeat split.
     * apply symmetry. assumption. 
     * constructor; assumption.
     * constructor; constructor.
Qed.



Lemma Diamond_Step :
  forall phi0 phi1 phi2 heap0 heap1 heap2,
    Det_Trace phi0 ->
    (phi0, heap0) ===> (phi1, heap1) ->
    (phi0, heap0) ===> (phi2, heap2) ->
    exists phi3, exists heap3, exists heap4, exists n13, exists n23,
      heap3 ≡@{Heap} heap4 /\                                                     
      (phi1, heap1) =a=>* (phi3, heap3, n13) /\
      (phi2, heap2) =a=>* (phi3, heap4, n23) /\
      (n13 <= 1) /\ (n23 <= 1).
Proof.
  induction phi0; intros phi1 phi2 heap0 heap1 heap2 HDet H0_1 H0_2.
  + inversion H0_1.
  + destruct d; inversion H0_1; subst; inversion H0_2; subst;
    repeat eexists; repeat econstructor.
  + inversion H0_1; subst; inversion H0_2; subst.
  - inversion HDet; subst.
      edestruct (IHphi0_1 phi1' phi1'0) as [phi3 [heap3 [heap4 [n13 [n23 [? [? [? ?]]]]]]]]; try eassumption.
      exists (Phi_Par phi3 phi0_2). exists heap3. exists heap4.  exists n13. exists n23; repeat split;
         try (solve [assumption | destruct H7; eassumption | eapply Par_Left_Pres; assumption]) .
    - inversion HDet; subst. destruct H5.
      edestruct (Par_Step_Equal phi0_1 phi0_2) as [heap3 [heap4 [? [? ?]]]]; try eassumption.
      exists (Phi_Par phi1' phi2'). exists heap3. exists heap4.
      repeat eexists; try (eapply PHT_Step; eassumption); repeat constructor. assumption.
    - inversion H0.
    - inversion HDet; subst. destruct H5.
      edestruct (Par_Step_Equal phi0_1 phi0_2 phi1' phi2') as [heap3 [heap4 [? [? ?]]]]; try eassumption.
      exists (Phi_Par phi1' phi2'). exists heap4. exists heap3. 
      repeat eexists; try (eapply PHT_Step; eassumption); repeat constructor.
      symmetry; assumption.
    - inversion HDet; subst.
      edestruct (IHphi0_2 phi2' phi2'0) as [phi3 [heap3 [heap4 [n13 [n23 [? [? [? ?]]]]]]]]; try eassumption.
      exists (Phi_Par phi0_1 phi3). exists heap3. exists heap4. exists n13. exists n23; repeat split;
        try (solve [assumption | destruct H7; eassumption | eapply Par_Right_Pres; assumption]) .
    - inversion H0.
    - inversion H0.
    - inversion H0.
    - exists Phi_Nil. exists heap2. repeat eexists; repeat econstructor.
  + inversion H0_1; subst; inversion H0_2; subst.
    - inversion HDet; subst.
      edestruct (IHphi0_1 phi1' phi1'0) as [phi3 [heap3 [heap4 [n13 [n23 [? [? [? ?]]]]]]]]; try eassumption.
      exists (Phi_Seq phi3 phi0_2). exists heap3. exists heap4. exists n13. exists n23. repeat split;
        try (solve [assumption | destruct H6; eassumption | eapply Seq_Left_Pres; assumption]) .
    - inversion H0.
    - inversion H0.
    - inversion H1.
    - inversion HDet; subst.
      edestruct (IHphi0_2 phi2' phi2'0) as [phi3 [heap3 [heap4 [n13 [n23 [? [? [? ?]]]]]]]]; try eassumption.
      exists (Phi_Seq Phi_Nil phi3). exists heap3. exists heap4. exists n13. exists n23; repeat split;
        try (solve [assumption | destruct H6; eassumption | eapply Seq_Right_Pres; assumption]) .
    - inversion H0.
    - inversion H0.
    - inversion H0.
    - exists Phi_Nil. exists heap2. repeat eexists; repeat econstructor.
Qed.

Lemma Diamond_Step_new :
  forall phi0 phi1 phi2 heapa heapb heap1 heap2,
    Det_Trace phi0 ->
    heapa ≡@{Heap} heapb ->
    (phi0, heapa) ===> (phi1, heap1) ->
    (phi0, heapb) ===> (phi2, heap2) ->
    exists phi3, exists heap3, exists heap4, exists n13, exists n23,
      heap3 ≡@{Heap} heap4 /\                                                     
      (phi1, heap1) =a=>* (phi3, heap3, n13) /\
      (phi2, heap2) =a=>* (phi3, heap4, n23) /\
      (n13 <= 1) /\ (n23 <= 1).
Proof.
  induction phi0; intros phi1 phi2 heapa heapb heap1 heap2 HDet HEqual H0_1 H0_2.
  + inversion H0_1.
  + destruct d; inversion H0_1; subst; inversion H0_2; subst; exists Phi_Nil.
    - exists (update_H (r, n, v) heapa); exists (update_H (r, n, v) heapb).
      repeat eexists; repeat econstructor.
      unfold equiv, heap_equiv in *; unfold update_H in *; simpl in *.
      subst. reflexivity.
    - exists heap1; exists heap2; repeat eexists; repeat econstructor.
      assumption.
    - exists (update_H (r, n, v) heapa); exists (update_H (r, n, v) heapb).
      repeat eexists; repeat econstructor.
      unfold equiv, heap_equiv in *; unfold update_H in *; simpl in *.
      subst. reflexivity.
  + inversion H0_1; subst; inversion H0_2; subst.
  - inversion HDet; subst.
      edestruct (IHphi0_1 phi1' phi1'0) as [phi3 [heap3 [heap4 [n13 [n23 [? [? [? ?]]]]]]]]; try eassumption.
      exists (Phi_Par phi3 phi0_2). exists heap3. exists heap4.  exists n13. exists n23; repeat split;
         try (solve [assumption | destruct H7; eassumption | eapply Par_Left_Pres; assumption]) .
    - inversion HDet; subst. destruct H5.
      edestruct (Par_Step_Equal_new phi0_1 phi0_2) as [heap3 [heap4 [? [? ?]]]]; try eassumption.
      exists (Phi_Par phi1' phi2'). exists heap3. exists heap4.
      repeat eexists; try (eapply PHT_Step; eassumption); repeat constructor. assumption.
    - inversion H0.
    - inversion HDet; subst. destruct H5.
      assert (HEqual': heapb ≡@{Heap} heapa) by (eauto using symmetry).
      edestruct (Par_Step_Equal_new phi0_1 phi0_2 phi1' phi2') as [heap3 [heap4 [? [? ?]]]]; try eassumption.
      exists (Phi_Par phi1' phi2'). exists heap4. exists heap3. 
      repeat eexists; try (eapply PHT_Step; eassumption); repeat constructor.
      symmetry; assumption.
    - inversion HDet; subst.
      edestruct (IHphi0_2 phi2' phi2'0) as [phi3 [heap3 [heap4 [n13 [n23 [? [? [? ?]]]]]]]]; try eassumption.
      exists (Phi_Par phi0_1 phi3). exists heap3. exists heap4. exists n13. exists n23; repeat split;
        try (solve [assumption | destruct H7; eassumption | eapply Par_Right_Pres; assumption]) .
    - inversion H0.
    - inversion H0.
    - inversion H0.
    - exists Phi_Nil. exists heap1. exists heap2. repeat eexists; repeat econstructor; assumption.
  + inversion H0_1; subst; inversion H0_2; subst.
    - inversion HDet; subst.
      edestruct (IHphi0_1 phi1' phi1'0) as [phi3 [heap3 [heap4 [n13 [n23 [? [? [? ?]]]]]]]]; try eassumption.
      exists (Phi_Seq phi3 phi0_2). exists heap3. exists heap4. exists n13. exists n23. repeat split;
        try (solve [assumption | destruct H6; eassumption | eapply Seq_Left_Pres; assumption]) .
    - inversion H0.
    - inversion H0.
    - inversion H1.
    - inversion HDet; subst.
      edestruct (IHphi0_2 phi2' phi2'0) as [phi3 [heap3 [heap4 [n13 [n23 [? [? [? ?]]]]]]]]; try eassumption.
      exists (Phi_Seq Phi_Nil phi3). exists heap3. exists heap4. exists n13. exists n23; repeat split;
        try (solve [assumption | destruct H6; eassumption | eapply Seq_Right_Pres; assumption]) .
    - inversion H0.
    - inversion H0.
    - inversion H0.
    - exists Phi_Nil. exists heap1. exists heap2. repeat eexists; repeat econstructor; assumption.
Qed.

Theorem Phi_Heap_Step__Preserves_DAs :
  forall phi phi' heap heap',
    (phi, heap) ===> (phi', heap') ->
    (forall da,
       In da (phi_as_list phi') ->
       In da (phi_as_list phi)).
Proof.
  intros phi phi' heap heap' HStep.
  dependent induction HStep; intros da HIn; simpl phi_as_list in *.
  - inversion HIn.
  - inversion HIn.
  - inversion HIn.
  - apply in_or_app.
    apply in_app_or in HIn; destruct HIn.
    + left. eapply IHHStep; auto.
    + right; assumption.
  - eapply IHHStep; auto.
  - assumption.
  - apply in_or_app.
    apply in_app_or in HIn; destruct HIn.
    + left; eapply IHHStep; auto.
    + right; assumption.
  - apply in_or_app.
    apply in_app_or in HIn; destruct HIn.
    + left; assumption.
    + right; eapply IHHStep; auto.
  - assumption.
Qed.

Lemma Det_Pres_Par_Conf_1:
  forall phi1 phi1' phi2 heap heap',
    (phi1, heap) ===> (phi1', heap') ->
    Det_Trace (Phi_Par phi1 phi2) ->
    ~ Conflict_Traces (phi_as_list phi1') (phi_as_list phi2).
Proof.
  intros. inversion H0; subst. destruct H5.
  intro. inversion H5; subst. apply H1.
  econstructor; eauto using Phi_Heap_Step__Preserves_DAs.
Qed.

Lemma Det_Pres_Par_Conf_1_aux:
  forall phi1 phi1' phi2 heap heap',
    (phi1, heap) ===> (phi1', heap') ->
    Det_Trace phi1' ->
    Det_Trace (Phi_Par phi1 phi2) ->
    ~ Conflict_Traces (phi_as_list phi1') (phi_as_list phi2).
Proof.
  intros phi1 phi1' phi2 heap heap' H1 H2 H3.
  inversion_clear H3; subst. destruct H4. clear H4.
  generalize dependent phi2.  
  dependent induction H1; intros; subst; simpl in *.
  - intro. inversion H1. trivial.
  - intro. inversion H4. trivial.
  - intro. inversion H4. trivial.
  - inversion H2; inversion H; subst.  
    apply Conflictness_app_and_r in H3; auto. destruct H3.
    apply Conflictness_and_app_r. split; [ | assumption].
    eapply IHPhi_Heap_Step; auto.    
  - eapply IHPhi_Heap_Step; auto; inversion H2; inversion H; assumption.
  - apply H3.
  - inversion H2; inversion H; subst.
    apply Conflictness_app_and_r in H3; auto. destruct H3.
    apply Conflictness_and_app_r. split; [ | assumption].
    eapply IHPhi_Heap_Step; auto.    
  - inversion H2; inversion H; subst.
    destruct H8. destruct H13.
    apply Conflictness_app_and_r in H3; auto. destruct H3.
    apply Conflictness_and_app_r.  split.
    + assumption.
    + eapply IHPhi_Heap_Step; auto.    
  - intro; now apply H3.
Qed.

Lemma Det_Pres_Par_Conf_2:
  forall phi1 phi1' phi2 heap heap',
    (phi1, heap) ===> (phi1', heap') ->
    Det_Trace (Phi_Par phi1 phi2) ->
    ~ Conflict_Traces (phi_as_list phi1') (phi_as_list phi2).
Proof.
  intros. inversion H0; subst. destruct H5.
  intro. inversion H5; subst. apply H1. 
  econstructor; eauto using Phi_Heap_Step__Preserves_DAs.
Qed.

Lemma Det_Pres_Par_Conf_2_aux:
  forall phi1 phi2 phi2' heap heap',
    (phi2, heap) ===> (phi2', heap') ->
    Det_Trace phi2' ->
    Det_Trace (Phi_Par phi1 phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2').
Proof.
  intros phi1 phi2 phi2' heap heap' H1 H2 H3.
   inversion_clear H3; subst. destruct H4. clear H4.  
   generalize dependent phi1. 
   dependent induction H1; intros; inversion H0; subst; simpl in *.
   - intro. inversion H1; trivial.
   - intro. inversion H4; trivial.
   - intro. inversion H4; trivial.
   - inversion H2; inversion H0; subst.
     eapply Conflictness_app_and_l in H3; auto.  destruct H3. 
     apply Conflictness_and_app_l; split; [ | assumption].
     eapply IHPhi_Heap_Step; auto.    
   - eapply IHPhi_Heap_Step; auto. inversion H2; inversion H0; assumption.
   - apply H3.
   - inversion H2; inversion H0; subst.
     destruct H8.
     apply Conflictness_app_and_l in H3; auto. destruct H3.
     apply Conflictness_and_app_l; split; [ | assumption].
    eapply IHPhi_Heap_Step; auto.    
   - inversion H2; inversion H0; subst.
     destruct H8. 
     apply Conflictness_app_and_l in H3; auto. destruct H3.
     apply Conflictness_and_app_l.
     split ; [ assumption | eapply IHPhi_Heap_Step; auto]. 
   - intro. inversion H1; trivial.
Qed.


Lemma Det_Pres_Par_Disj_1:
  forall phi1 phi1' phi2 heap heap',
    (phi1, heap) ===> (phi1', heap') ->
    Det_Trace phi1' ->
    Det_Trace (Phi_Par phi1 phi2) ->
    Disjoint_Traces (phi_as_list phi1') (phi_as_list phi2).
Proof.
  intros phi1 phi1' phi2 heap heap' H1 H2 H3.
  inversion H3; subst; simpl. destruct H6.
  inversion H0; subst. econstructor; intros. apply H6; auto.
  eapply Phi_Heap_Step__Preserves_DAs; eauto.
Qed.    
 
Lemma Det_Pres_Par_Disj_1_aux:
  forall phi1 phi1' phi2 heap heap',
    (phi1, heap) ===> (phi1', heap') ->
    Det_Trace phi1' ->
    Det_Trace (Phi_Par phi1 phi2) ->
    Disjoint_Traces (phi_as_list phi1') (phi_as_list phi2).
Proof.
  intros phi1 phi1' phi2 heap heap' H1 H2 H3.
  inversion_clear H3; subst. destruct H4. clear H3.
  generalize dependent phi2.     
  dependent induction H1; intros; simpl; try (solve [constructor]).
  inversion H4; subst;
  simpl in *; try (solve [econstructor ]).
  - econstructor; intros. apply H1; [inversion H3 | assumption].
  - econstructor; intros. inversion H3.
  - econstructor; intros. inversion H3.
  - inversion H2; inversion H; subst.
    apply Disjointness_and_app_r. simpl in H4.
    apply Disjointness_app_app_and_r in H4. destruct H4.
    split; [eapply IHPhi_Heap_Step; eauto | assumption].
  - inversion H2; inversion H. simpl in H4.
    eapply IHPhi_Heap_Step; eauto.
  - econstructor; intros. inversion H1. 
  - inversion H2; inversion H; subst.
    apply Disjointness_and_app_r. simpl in H4.
    apply Disjointness_app_app_and_r in H4. destruct H4.
    split; [ eapply IHPhi_Heap_Step; eauto | assumption].
  - inversion H2; inversion H; subst.
    apply Disjointness_and_app_r. simpl in H4.
    apply Disjointness_app_app_and_r in H4. destruct H4.
    split; [ assumption | eapply IHPhi_Heap_Step; eauto].
  -  econstructor; intros. inversion H1.    
Qed.

Lemma Det_Pres_Par_Disj_2:
  forall phi2 phi2' phi1 heap heap',
    (phi2, heap) ===> (phi2', heap') ->
    Det_Trace phi2' ->
    Det_Trace (Phi_Par phi1 phi2) ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2').
Proof.
  intros phi2 phi2' phi1 heap heap' H1 H2 H3.
   inversion H3; subst; simpl. destruct H6.
  inversion H0; subst. econstructor; intros. apply H6; auto.
  eapply Phi_Heap_Step__Preserves_DAs; eauto.
Qed.   

Lemma Det_Pres_Par_Disj_2_aux:
  forall phi2 phi2' phi1 heap heap',
    (phi2, heap) ===> (phi2', heap') ->
    Det_Trace phi2' ->
    Det_Trace (Phi_Par phi1 phi2) ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2').
Proof.
  intros phi2 phi2' phi1 heap heap' H1 H2 H3.
  inversion_clear H3; subst. destruct H4. clear H3.
  generalize dependent phi1.     
  dependent induction H1; intros; simpl in *;
  try (solve [constructor |
              econstructor; intros; inversion H5 |
              econstructor; intros; inversion H3
             ]).
  - inversion H2; inversion H0; subst.
    apply Disjointness_and_app_l. simpl in H4.
    apply Disjointness_app_app_and_l in H4. destruct H4.
    split; [eapply IHPhi_Heap_Step; eauto | assumption].
  - inversion H2; inversion H0. 
    eapply IHPhi_Heap_Step; eauto.
  - inversion H2; inversion H0; subst.
    apply Disjointness_and_app_l. simpl in H4.
    apply Disjointness_app_app_and_l in H4. destruct H4.
    split; [eapply IHPhi_Heap_Step; eauto | assumption].
  -  inversion H2; inversion H0; subst.
    apply Disjointness_and_app_l. simpl in H4.
    apply Disjointness_app_app_and_l in H4. destruct H4.
    split; [assumption | eapply IHPhi_Heap_Step; eauto].
Qed.

Theorem Det_Pres_Aux :
   forall phi phi' heap heap',
     (phi, heap) ===> (phi', heap') ->
     Det_Trace phi ->
     Det_Trace phi'.
Proof.
  intros phi phi' heap heap' H1 H2.
  dependent induction H1; intros; try (solve [constructor]).
  - inversion H2; subst. econstructor.
    + eapply IHPhi_Heap_Step; auto.
    + assumption.
  - inversion H2; subst. econstructor.
    + constructor.
    + eapply IHPhi_Heap_Step; auto.
  - inversion H2; subst. econstructor.
    + eapply IHPhi_Heap_Step; auto.
    + inversion H2; subst. assumption.
    + destruct H5. split.
      * intro; inversion H5; subst.
        apply H; econstructor; eauto using Phi_Heap_Step__Preserves_DAs.
      * constructor; intros.
        inversion H0; subst.
        apply H7; eauto using Phi_Heap_Step__Preserves_DAs.
  - inversion H2; subst; econstructor.
    + assumption.
    + eapply IHPhi_Heap_Step; auto.
    + destruct H5. split.
      * intro; inversion H5; subst.
        apply H; econstructor; eauto using Phi_Heap_Step__Preserves_DAs.
      * constructor; intros.
        inversion H0; subst.
        apply H7; eauto using Phi_Heap_Step__Preserves_DAs.
Qed.    

Theorem Det_Pres :
   forall phi phi' heap heap' n',
     (phi, heap) =a=>* (phi', heap', n') ->
     Det_Trace phi ->
     Det_Trace phi'.
Proof.
   intros phi phi' heap heap' n' HSteps.
   dependent induction HSteps; intro HDet.
   - assumption.
   - eapply Det_Pres_Aux; eassumption.
   - eapply IHHSteps2; auto. eapply IHHSteps1; auto.
Qed.


Require Import Lia.
    
Theorem Diamond_Walk_Aux : 
  forall n n1 n2,
    n = n1 + n2 ->
    forall phi0 phi1 phi2 heap0 heap1 heap2,
    forall (H0_1: (phi0, heap0) =a=>* (phi1, heap1, n1)),
    forall (H0_2: (phi0, heap0) =a=>* (phi2, heap2, n2)),
      Det_Trace phi0 ->
      exists phi3, exists heap3, exists heap4, exists n13, exists n23,
        heap3 ≡@{Heap} heap4 /\                                                             
        (phi1, heap1) =a=>* (phi3, heap3, n13) /\
        (phi2, heap2) =a=>* (phi3, heap4, n23) /\
        (n13 <= n2) /\ (n23 <= n1).
Proof.
  induction n using Wf_nat.lt_wf_ind.
  intros n1 n2 HSum.
  intros phi0 phi1 phi2 heap0 heap1 heap2 H0_1 H0_2 HDet. 
  dependent destruction H0_1.
  - exists phi2; exists heap2; exists heap2; exists n2; exists 0.
   repeat split; try (solve [lia]).
   + assumption.  (* phi1 walks into phi1 in n2 steps *)
   + apply PHT_Refl.  (* phi2 takes 0 steps *)
  -  rename H0 into H0_1.  
    dependent destruction H0_2.
    + exists phi1. exists heap1. exists heap1. exists 0. exists 1.
      repeat split; try (solve [lia]).
      * apply PHT_Refl. (* phi1 takes 0 steps *)
      * apply PHT_Step; assumption. (* phi2 walks into phi1 in 1 step *)
    + rename H0 into H0_2.
      destruct (Diamond_Step phi0 phi1 phi2 heap0 heap1 heap2 HDet H0_1 H0_2)
        as [phi3 [heap3 [heap4 [n13 [n23 [Heq [H1_3 [H2_3 [? ?]]]]]]]]].
      exists phi3. exists heap3. exists heap4. exists n13. exists n23. (* n13 and n23 are the remaining steps *)
      repeat split;  try (solve [lia]). 
      * assumption. (* context provided by Diamond_Step *)
      * assumption. (* context provided by Diamond_Step *)
      * assumption.
    + rename phi' into phi2'. rename heap' into heap2'. 
      rename H0_2_1 into H0_2'. rename H0_2_2 into H2'_2. 
      edestruct (H (1 + n')) as [phi3 [heap3 [heap4 [n1_3 [n2'_3 [Heq [H1_3 [H2'_3 [? ?]]]]]]]]]. (* transitivity on phi2 *)
      * lia. (* phi2 took n' intermediate steps *)
      * reflexivity.
      * eapply PHT_Step; eassumption.  (* phi1 steps 1 *)
      * eassumption. (* by induction *)
      * eassumption. (* by induction *)  
      * { edestruct (H (n2'_3 + n'')) as [phi4 [heap5 [heap6 [n3_4 [n2_4 [Heq' [H3_4 [H2_4 [? ?]]]]]]]]].
          - lia.  (* phi2 took n'' intermediate steps *)
          - reflexivity.
          - eassumption. (* by induction *)
          - eassumption. (* by induction *)
          - eapply Det_Pres; eassumption.
          - apply Aux_Step_Ext_Heap with (heapB:=heap3) in H3_4; [ | apply symmetry; assumption].
            destruct H3_4 as [heap5' [? ?]].
            exists phi4. exists heap5'. exists heap6. exists (1 + n1_3 + n3_4). exists n2_4.
            repeat split; try (solve [lia]).
            + eapply eq_trans in Heq'; eauto. 
            + eapply PHT_Trans. eassumption. assumption.
            + assumption. }
  - rename phi' into phi1'. rename heap' into heap1'.
    rename H0_1_1 into H0_1'. rename H0_1_2 into H1'_1.
    edestruct (H (n' + n2)) as [phi3 [heap3 [heap4 [n1'_3 [n2_3 [Heq [H1'_3 [H2_3 [? ?]]]]]]]]].
    + lia.  (* phi1 took n' intermediate steps *)
    + reflexivity.
    + eassumption.
    + eassumption.
    + assumption.
    + edestruct (H (n'' + n1'_3)) as [phi4 [heap5 [heap6 [n1_4 [n3_4 [Heq' [H1_4 [H3_4 [? ?]]]]]]]]].
      * lia. (* phi1 took the remaining n'' intermediate steps *)
      * reflexivity. 
      * eassumption.
      * eassumption.
      * eapply Det_Pres; eassumption.
      * apply Aux_Step_Ext_Heap with (heapB:=heap4) in H3_4; [ |assumption].
        destruct H3_4 as [heap6' [? ?]]. 
        exists phi4. exists heap5. exists heap6'. exists n1_4. exists (1 + n2_3 + n3_4).
        repeat split;  try (solve [lia]).
        { eapply eq_trans in H4; eauto. }
        { assumption. }
        { eapply PHT_Trans. eassumption. assumption. }
Qed.

Theorem Diamond_Walk_Aux_new : 
  forall n n1 n2,
    n = n1 + n2 ->
    forall phi0 phi1 phi2 heapa heapb heap1 heap2,
    heapa ≡@{Heap} heapb ->
    forall (H0_1: (phi0, heapa) =a=>* (phi1, heap1, n1)),
    forall (H0_2: (phi0, heapb) =a=>* (phi2, heap2, n2)),
      Det_Trace phi0 ->
      exists phi3, exists heap3, exists heap4, exists n13, exists n23,
        heap3 ≡@{Heap} heap4 /\
        (phi1, heap1) =a=>* (phi3, heap3, n13) /\
        (phi2, heap2) =a=>* (phi3, heap4, n23) /\
        (n13 <= n2) /\ (n23 <= n1).
Proof.
  induction n using Wf_nat.lt_wf_ind.
  intros n1 n2 HSum.
  intros phi0 phi1 phi2 heapa heapb heap1 heap2 HEqual H0_1 H0_2 HDet. 
  dependent destruction H0_1.
  - assert (HEqual' : heapb ≡@{Heap} heap1) by (eauto using symmetry).
    edestruct (Aux_Step_Ext_Heap _ _ _ _ _ _ H0_2 HEqual')
     as [heap2' [HEqual'' ?]].
    exists phi2; exists heap2'; exists heap2; exists n2; exists 0.
    repeat split; try (solve [lia]).
    + eauto using symmetry.  
    + assumption. (* phi1 walks into phi2 in n2 steps *)
    + apply PHT_Refl.  (* phi2 takes 0 steps *)
  - rename H0 into H0_1.  
    dependent destruction H0_2.
    + edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ H0_1 HEqual)
       as [heap1' [HEqual' H0_1']].
      exists phi1. exists heap1. exists heap1'. exists 0. exists 1.
      repeat split; try (solve [lia]).
      * assumption.
      * apply PHT_Refl. (* phi1 takes 0 steps *)
      * apply PHT_Step; assumption. (* phi2 walks into phi1 in 1 step *)
    + rename H0 into H0_2.
      destruct (Diamond_Step_new phi0 phi1 phi2 heapa heapb heap1 heap2 HDet HEqual H0_1 H0_2)
        as [phi3 [heap3 [heap4 [n13 [n23 [Heq [H1_3 [H2_3 [? ?]]]]]]]]].
      exists phi3. exists heap3. exists heap4. exists n13. exists n23. (* n13 and n23 are the remaining steps *)
      repeat split;  try (solve [lia]). 
      * assumption.
      * assumption. (* context provided by Diamond_Step *)
      * assumption. (* context provided by Diamond_Step *)
    + rename phi' into phi2'. rename heap' into heap2'. 
      rename H0_2_1 into H0_2'. rename H0_2_2 into H2'_2. 
      edestruct (H (1 + n')) as [phi3 [heap3 [heap4 [n1_3 [n2'_3 [Heq [H1_3 [H2'_3 [? ?]]]]]]]]]. (* transitivity on phi2 *)
      * lia. (* phi2 took n' intermediate steps *)
      * reflexivity.
      * eassumption.
      * eapply PHT_Step; eassumption.  (* phi1 steps 1 *)
      * eassumption. (* by induction *)
      * eassumption. (* by induction *)  
      * { edestruct (H (n2'_3 + n'')) as [phi4 [heap5 [heap6 [n3_4 [n2_4 [Heq' [H3_4 [H2_4 [? ?]]]]]]]]].
          - lia.  (* phi2 took n'' intermediate steps *)
          - reflexivity.
          - reflexivity.
          - eassumption. (* by induction *)
          - eassumption. (* by induction *)
          - eapply Det_Pres; eassumption.
          - apply Aux_Step_Ext_Heap with (heapB:=heap3) in H3_4; [ | apply symmetry; assumption].
            destruct H3_4 as [heap5' [? ?]].
            exists phi4. exists heap5'. exists heap6. exists (1 + n1_3 + n3_4). exists n2_4.
            repeat split; try (solve [lia]).
            + eapply eq_trans in Heq'; eauto. 
            + eapply PHT_Trans. eassumption. assumption.
            + assumption. }
  - rename phi' into phi1'. rename heap' into heap1'.
    rename H0_1_1 into H0_1'. rename H0_1_2 into H1'_1.
    edestruct (H (n' + n2)) as [phi3 [heap3 [heap4 [n1'_3 [n2_3 [Heq [H1'_3 [H2_3 [? ?]]]]]]]]].
    + lia.  (* phi1 took n' intermediate steps *)
    + reflexivity.
    + eassumption.
    + eassumption.
    + eassumption.
    + assumption.
    + edestruct (H (n'' + n1'_3)) as [phi4 [heap5 [heap6 [n1_4 [n3_4 [Heq' [H1_4 [H3_4 [? ?]]]]]]]]].
      * lia. (* phi1 took the remaining n'' intermediate steps *)
      * reflexivity. 
      * reflexivity.
      * eassumption.
      * eassumption.
      * eapply Det_Pres; eassumption.
      * apply Aux_Step_Ext_Heap with (heapB:=heap4) in H3_4; [ |assumption].
        destruct H3_4 as [heap6' [? ?]]. 
        exists phi4. exists heap5. exists heap6'. exists n1_4. exists (1 + n2_3 + n3_4).
        repeat split;  try (solve [lia]).
        { eapply eq_trans in H4; eauto. }
        { assumption. }
        { eapply PHT_Trans. eassumption. assumption. }
Qed.

Theorem Diamond_Walk : 
  forall phi0 phi1 phi2 heap0 heap1 heap2,
    (phi0, heap0) ==>* (phi1, heap1) ->
    (phi0, heap0) ==>* (phi2, heap2) ->
    Det_Trace phi0 ->
    exists phi3, exists heap3, exists heap4,
      heap3 ≡@{Heap} heap4 /\                           
      (phi1, heap1) ==>* (phi3, heap3) /\
      (phi2, heap2) ==>* (phi3, heap4).
Proof.
  intros phi0 phi1 phi2 heap0 heap1 heap2 H0_1 H0_2 HDet.
  unfold Phi_Heap_Steps in *.
  destruct H0_1 as [n0_1 H0_1].
  destruct H0_2 as [n0_2 H0_2].
  edestruct (Diamond_Walk_Aux (n0_1 + n0_2) n0_1 n0_2) as [phi3 [heap3 [heap4 [n1_3 [n2_3 [Heq [H1_3 [H2_3 [? ?]]]]]]]]]; eauto.
  exists phi3. exists heap3. exists heap4. repeat split;[ assumption | |]; eexists; eassumption.
Qed.

Theorem Diamond_Walk_new : 
  forall phi0 phi1 phi2 heapa heapb heap1 heap2,
     heapa ≡@{Heap} heapb ->
    (phi0, heapa) ==>* (phi1, heap1) ->
    (phi0, heapb) ==>* (phi2, heap2) ->
    Det_Trace phi0 ->
    exists phi3, exists heap3, exists heap4,
      heap3 ≡@{Heap} heap4 /\                           
      (phi1, heap1) ==>* (phi3, heap3) /\
      (phi2, heap2) ==>* (phi3, heap4).
Proof.
  intros phi0 phi1 phi2 heapa heapb heap1 heap2 HEqual H0_1 H0_2 HDet.
  unfold Phi_Heap_Steps in *.
  destruct H0_1 as [n0_1 H0_1].
  destruct H0_2 as [n0_2 H0_2].
  edestruct (Diamond_Walk_Aux_new (n0_1 + n0_2) n0_1 n0_2) as [phi3 [heap3 [heap4 [n1_3 [n2_3 [Heq [H1_3 [H2_3 [? ?]]]]]]]]]; eauto.
  exists phi3. exists heap3. exists heap4. repeat split;[ assumption | |]; eexists; eassumption.
Qed.

Lemma Term_Walk_Idemp :
  forall heap phi' heap' n,
    (Phi_Nil, heap) =a=>* (phi', heap', n) ->
    phi' = Phi_Nil /\ heap = heap'.
Proof.
  intros heap phi' heap' n HStep.
  dependent induction HStep.
  - split; reflexivity.
  - inversion H.
  - edestruct IHHStep1; subst; auto.
    eapply (IHHStep2 _ _ heap' _); auto.
    subst. reflexivity.
Qed.


        
Theorem Diamond_Term_Walk : 
  forall phi0 heap0 heap1 heap2,
    (phi0, heap0) ==>* (Phi_Nil, heap1) ->
    (phi0, heap0) ==>* (Phi_Nil, heap2) ->
    Det_Trace phi0 ->
    heap1 ≡@{Heap} heap2.
Proof.
  intros phi0 heap0 heap1 heap2 HDet HStep1 HStep2.
  edestruct (Diamond_Walk phi0 Phi_Nil Phi_Nil heap0 heap1 heap2) as [phi3 [heap3 [heap4 [Heq [H1 H2]]]]]; try eassumption.
  destruct H1 as [n1 H1]. destruct H2 as [n2 H2].
  edestruct (Term_Walk_Idemp heap1 phi3 heap3 n1) as [? ?]; try eassumption.
  edestruct (Term_Walk_Idemp heap2 phi3 heap4 n2) as [? ?]; try eassumption.
  subst. assumption.
Qed.


Theorem Diamond_Term_Walk_new : 
  forall phi0 heapa heapb heap1 heap2,
    heapa ≡@{Heap} heapb ->
    (phi0, heapa) ==>* (Phi_Nil, heap1) ->
    (phi0, heapb) ==>* (Phi_Nil, heap2) ->
    Det_Trace phi0 ->
    heap1 ≡@{Heap} heap2.
Proof.
  intros phi0 heapa heapb heap1 heap2 HEqual HStep1 HStep2 HDet.
  edestruct (Diamond_Walk_new phi0 Phi_Nil Phi_Nil heapa heapb heap1 heap2) as [phi3 [heap3 [heap4 [Heq [H1 H2]]]]]; try eassumption.
  destruct H1 as [n1 H1]. destruct H2 as [n2 H2].
  edestruct (Term_Walk_Idemp heap1 phi3 heap3 n1) as [? ?]; try eassumption.
  edestruct (Term_Walk_Idemp heap2 phi3 heap4 n2) as [? ?]; try eassumption.
  subst. assumption.
Qed.

Lemma Ext_disjoint_sets :
  forall e1 acts a,
    Disjoint_Sets_Computed_Actions e1 (set_union acts a) ->
    Disjoint_Sets_Computed_Actions e1 acts /\ Disjoint_Sets_Computed_Actions e1 a.
Proof.
  intros e1 acts a H. 
  split; inversion H; subst.
  - econstructor; intros. apply H0; auto. unfold set_elem, set_union. apply Union_introl. assumption.
  - econstructor. intros. apply H0; auto. unfold set_elem, set_union. apply Union_intror. assumption.
Qed.

Lemma Ext_disjoint_sets_2 :
  forall e1 acts a,
    Disjoint_Sets_Computed_Actions (set_union acts a) e1 ->
    Disjoint_Sets_Computed_Actions acts e1 /\ Disjoint_Sets_Computed_Actions a e1.
Proof.
  intros e1 acts a H. 
  split; inversion H; subst.
  - econstructor; intros. apply H0; auto. unfold set_elem, set_union. apply Union_introl. assumption.
  - econstructor. intros. apply H0; auto. unfold set_elem, set_union. apply Union_intror. assumption.
Qed.

Lemma Disjoint_da_in_theta :
  forall e1 e2 p1 p2,
    Disjoint_Sets_Computed_Actions e1 e2 ->
    DA_in_Theta p1 (Some e1) ->
    DA_in_Theta p2 (Some e2) ->
    Disjoint_Dynamic p1 p2.
Proof.
  intros e1 e2 p1 p2 H1 H2 H3.
  generalize dependent p2. 
  dependent induction H2; intros.
  - generalize dependent e1. 
    dependent induction H3; intros; inversion H1; subst.  
    + assert (HD : Disjoint_Computed_Actions (CA_AllocAbs s) (CA_AllocAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5. inversion H5. reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_AllocAbs s) (CA_ReadAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_AllocAbs s) (CA_ReadConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor; contradict H5; inversion H5; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_AllocAbs s) (CA_WriteAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5. inversion H5. reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_AllocAbs s) (CA_WriteConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5. inversion H5. reflexivity.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.
  - generalize dependent e1.  
    dependent induction H3; intros; inversion H1; subst.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadAbs s) (CA_AllocAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadAbs s) (CA_ReadAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. 
    + assert (HD : Disjoint_Computed_Actions (CA_ReadAbs s) (CA_ReadConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadAbs s) (CA_WriteAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadAbs s) (CA_WriteConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption. 
  - generalize dependent e1.  
    dependent induction H3; intros; inversion H1; subst.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadConc s l) (CA_AllocAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H4; inversion H4; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadConc s l) (CA_ReadAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadConc s l) (CA_ReadConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadConc s l) (CA_WriteAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H4; inversion H4; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadConc s l) (CA_WriteConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H6; inversion H6; reflexivity.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.  
  - generalize dependent e1.  
    dependent induction H3; intros; inversion H1; subst.
    + assert (HD : Disjoint_Computed_Actions (CA_WriteAbs s) (CA_AllocAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_WriteAbs s) (CA_ReadAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_WriteAbs s) (CA_ReadConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_WriteAbs s) (CA_WriteAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_WriteAbs s) (CA_WriteConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.
  - generalize dependent e1.  
    dependent induction H3; intros; inversion H1; subst.
    + assert (HD : Disjoint_Computed_Actions (CA_WriteConc s l) (CA_AllocAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H4; inversion H4; reflexivity.
    +  assert (HD : Disjoint_Computed_Actions (CA_WriteConc s l) (CA_ReadAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H4; inversion H4; reflexivity. 
    + assert (HD : Disjoint_Computed_Actions (CA_WriteConc s l) (CA_ReadConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H6. inversion H6. reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_WriteConc s l) (CA_WriteAbs s0)) by (apply H2; auto).
      inversion HD; subst.
    + assert (HD : Disjoint_Computed_Actions (CA_WriteConc s l) (CA_WriteConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H6. inversion H6. reflexivity.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.
  -  apply Ext_disjoint_sets_2 in H1; destruct H1.
     eapply IHDA_in_Theta with (e1:=acts); eauto.
  -  apply Ext_disjoint_sets_2 in H1; destruct H1.
     eapply IHDA_in_Theta with (e1:=acts); eauto.  
Qed.
    
Lemma Disjoint_computed_disjoint_dynamic_action:
  forall e1 e2 phi1 phi2 p1 p2,
    phi1 ⋞ Some e1 ->
    phi2 ⋞ Some e2 ->
    Disjoint_Sets_Computed_Actions e1 e2 -> 
    In p1 (phi_as_list phi1) ->
    In p2 (phi_as_list phi2) -> 
    Disjoint_Dynamic p1 p2.
Proof.
  intros e1 e2 phi1 phi2 p1 p2 H1 H2 H3 H4 H5.
  generalize dependent phi2.
  dependent induction H1; intros; simpl in *.
  - contradiction.
  - destruct H4; subst.
    + dependent induction H2; simpl in H5.
      * contradiction.
      * destruct H5; [subst | contradiction ].
        eapply Disjoint_da_in_theta; eauto.
      * apply in_app_or in H5. destruct H5.
        { eapply  IHPhi_Theta_Soundness1; eauto. }
        { eapply  IHPhi_Theta_Soundness2; eauto. }
      * apply in_app_or in H5. destruct H5.
        { eapply  IHPhi_Theta_Soundness1; eauto. }
        { eapply  IHPhi_Theta_Soundness2; eauto. }
    + contradiction.
  - apply in_app_or in H4. destruct H4.
    + eapply  IHPhi_Theta_Soundness1; eauto.
    + eapply  IHPhi_Theta_Soundness2; eauto.
  - apply in_app_or in H4. destruct H4.
    + eapply  IHPhi_Theta_Soundness1; eauto.
    + eapply  IHPhi_Theta_Soundness2; eauto.
Qed.


Lemma Ext_Conflict_sets_1 :
  forall e acts a,
    Conflict_Sets_Computed_Actions e acts \/ Conflict_Sets_Computed_Actions e a ->
    Conflict_Sets_Computed_Actions e (set_union acts a).
Proof.
  intros e acts a H. destruct H.
  - inversion H; subst.
    econstructor; eauto. apply Union_introl. assumption.
  - inversion H; subst.
    econstructor; eauto. apply Union_intror. assumption. 
Qed.

Lemma Ext_Conflict_sets_2 :
  forall e acts a,
    Conflict_Sets_Computed_Actions acts e \/ Conflict_Sets_Computed_Actions a e ->
    Conflict_Sets_Computed_Actions (set_union acts a) e.
Proof.
  intros e acts a H. destruct H.
  - inversion H; subst.
    econstructor; eauto. apply Union_introl. assumption.
  - inversion H; subst.
    econstructor; eauto. apply Union_intror. assumption. 
Qed.

Lemma Conflict_da_in_theta_read :
  forall r l v e0 e,
    DA_in_Theta (DA_Write r l v) (Some e0) ->
    DA_in_Theta (DA_Read r l v) (Some e) ->
    Conflict_Sets_Computed_Actions e e0. 
Proof.
  intros.
  generalize dependent e0.
  dependent induction H0; intros.
  - dependent induction H0; intros.
    + econstructor; eauto. constructor.
    + econstructor; eauto. constructor. 
    + apply Ext_Conflict_sets_1. left. eapply IHDA_in_Theta; eauto.
    + apply Ext_Conflict_sets_1. right. eapply IHDA_in_Theta; eauto.
  - dependent induction H0; intros.
    + econstructor; eauto. constructor.
    + econstructor; eauto. constructor. 
    + apply Ext_Conflict_sets_1. left. eapply IHDA_in_Theta; eauto.
    + apply Ext_Conflict_sets_1. right. eapply IHDA_in_Theta; eauto.
  - apply Ext_Conflict_sets_2.  left. eapply IHDA_in_Theta; eauto.
  - apply Ext_Conflict_sets_2.  right. eapply IHDA_in_Theta; eauto.
Qed.

Lemma Conflict_da_in_theta_write :
  forall r l v e0 e,
    DA_in_Theta (DA_Write r l v) (Some e0) ->
    DA_in_Theta (DA_Write r l v) (Some e) ->
    Conflict_Sets_Computed_Actions e e0. 
Proof.
  intros.
  generalize dependent e0.
  dependent induction H0; intros.
  - dependent induction H0; intros.
    + econstructor; eauto. constructor.
    + econstructor; eauto. constructor. 
    + apply Ext_Conflict_sets_1. left. eapply IHDA_in_Theta; eauto.
    + apply Ext_Conflict_sets_1. right. eapply IHDA_in_Theta; eauto.
  - dependent induction H0; intros.
    + econstructor; eauto. constructor.
    + econstructor; eauto. constructor. 
    + apply Ext_Conflict_sets_1. left. eapply IHDA_in_Theta; eauto.
    + apply Ext_Conflict_sets_1. right. eapply IHDA_in_Theta; eauto.
  - apply Ext_Conflict_sets_2.  left. eapply IHDA_in_Theta; eauto.
  - apply Ext_Conflict_sets_2.  right. eapply IHDA_in_Theta; eauto.
Qed.

Lemma Conflict_computed_conflict_dynamic_action_write:
  forall phi1 phi2 e e0 r l v,
  phi1 ⋞ Some e ->
  phi2 ⋞ Some e0 ->
  In (DA_Write r l v) (phi_as_list phi1) ->
  In (DA_Write r l v) (phi_as_list phi2) ->
  Conflict_Sets_Computed_Actions e e0.
Proof.
  intros. generalize dependent phi2.
  dependent induction phi1; simpl in *.
  - contradiction.
  - intuition; subst.
    dependent induction H1; simpl in *.
    + contradiction.
    + intuition; subst. inversion H0; subst; eapply Conflict_da_in_theta_write; eauto; inversion H; subst; assumption.
    + apply in_app_or in H2. destruct H2; [eapply IHPhi_Theta_Soundness1 | eapply IHPhi_Theta_Soundness2] ; eauto.
    + apply in_app_or in H2. destruct H2; [eapply IHPhi_Theta_Soundness1 | eapply IHPhi_Theta_Soundness2] ; eauto.   
  - inversion H; apply in_app_or in H1. destruct H1; [eapply IHphi1_1 | eapply IHphi1_2] ; eauto.
  - inversion H; apply in_app_or in H1. destruct H1; [eapply IHphi1_1 | eapply IHphi1_2] ; eauto.
Qed.

Lemma Conflict_computed_conflict_dynamic_action_read:
  forall phi1 phi2 e e0 r l v,
  phi1 ⋞ Some e ->
  phi2 ⋞ Some e0 ->
  In (DA_Write r l v) (phi_as_list phi2) ->
  In (DA_Read r l v) (phi_as_list phi1) ->
  Conflict_Sets_Computed_Actions e e0.
Proof.
  intros. generalize dependent phi2.
  dependent induction phi1; simpl in *.
  - contradiction.
  - intuition; subst.
    dependent induction H1; simpl in *.
    + contradiction.
    + intuition; subst. inversion H0; subst; eapply Conflict_da_in_theta_read; eauto; inversion H; subst; assumption.
    + apply in_app_or in H2. destruct H2; [eapply IHPhi_Theta_Soundness1 | eapply IHPhi_Theta_Soundness2] ; eauto.
    + apply in_app_or in H2. destruct H2; [eapply IHPhi_Theta_Soundness1 | eapply IHPhi_Theta_Soundness2] ; eauto.   
  - inversion H; apply in_app_or in H2. destruct H2; [eapply IHphi1_1 | eapply IHphi1_2] ; eauto.
  - inversion H; apply in_app_or in H2. destruct H2; [eapply IHphi1_1 | eapply IHphi1_2] ; eauto.
Qed.

Lemma Det_trace_from_readonly :
  forall phi,
    ReadOnlyPhi phi ->
    Det_Trace phi.
Proof.
  intros phi H.
  dependent induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - constructor; auto. split. 
    + generalize dependent phi2.
      dependent induction IHReadOnlyPhi1; intros.
      * intro. inversion H1. inversion H2.
      * { dependent induction IHReadOnlyPhi2.
          - intro. inversion H1. inversion H3.
          - inversion H; inversion H0; subst.
            intro. simpl in H1. inversion H1; subst.
            inversion H2; subst; [ | inversion H5].  inversion H3; subst; [ | inversion H5].
            inversion H4.
          - simpl in *. replace (da :: nil) with (phi_as_list (Phi_Elem da))  by (simpl; reflexivity).
            inversion H0; subst.
            apply Conflictness_and_app_l. split; [apply IHIHReadOnlyPhi2_1 | apply IHIHReadOnlyPhi2_2]; assumption.
          - simpl in *. replace (da :: nil) with (phi_as_list (Phi_Elem da))  by (simpl; reflexivity).
            inversion H0; subst.
            apply Conflictness_and_app_l. split; [apply IHIHReadOnlyPhi2_1 | apply IHIHReadOnlyPhi2_2]; assumption. }
      * inversion H; subst.
        apply Conflictness_and_app_r. split; [apply IHIHReadOnlyPhi1_1 | apply IHIHReadOnlyPhi1_2]; assumption.
      * inversion H; subst.
        apply Conflictness_and_app_r. split; [apply IHIHReadOnlyPhi1_1 | apply IHIHReadOnlyPhi1_2]; assumption.
    + generalize dependent phi2.
      dependent induction IHReadOnlyPhi1; intros.
      * constructor. intros. inversion H1.
      * { dependent induction IHReadOnlyPhi2.
          - constructor. intros. inversion H2.
          - inversion H; inversion H0; subst.
            constructor. intros. simpl in *. intuition; subst.
            constructor.
          - simpl.  replace (da :: nil) with (phi_as_list (Phi_Elem da))  by (simpl; reflexivity).
            inversion H0; subst.
            apply Disjointness_and_app_l.  split; [apply IHIHReadOnlyPhi2_1 | apply IHIHReadOnlyPhi2_2]; assumption.
          - simpl.  replace (da :: nil) with (phi_as_list (Phi_Elem da))  by (simpl; reflexivity).
            inversion H0; subst.
            apply Disjointness_and_app_l.  split; [apply IHIHReadOnlyPhi2_1 | apply IHIHReadOnlyPhi2_2]; assumption. }
      * inversion H; subst.
        apply Disjointness_and_app_r. split; [apply IHIHReadOnlyPhi1_1 | apply IHIHReadOnlyPhi1_2]; assumption.
      * inversion H; subst.
        apply Disjointness_and_app_r. split; [apply IHIHReadOnlyPhi1_1 | apply IHIHReadOnlyPhi1_2]; assumption.  
Qed.

Lemma Read_only_no_conflicts:
  forall phi1 phi2,
    ReadOnlyPhi phi1 ->
    ReadOnlyPhi phi2 ->
   ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2).
Proof.
  intros phi1 phi2 H1 H2.
  generalize dependent phi2.
  dependent induction phi1; intros.
  - intro. dependent destruction H. inversion H.
  - generalize dependent d.
    dependent induction H2; intros.
    + intro. inversion H. inversion H2.
    + intro. inversion H1; subst. simpl in H.
      inversion H; subst.
      inversion H0; subst; [ | inversion H4].
      inversion H2; subst; [ | inversion H4].
      inversion H3.
    + simpl. replace (d :: nil) with (phi_as_list (Phi_Elem d)) by (simpl; reflexivity).
      apply Conflictness_and_app_l. split; [apply IHReadOnlyPhi1 | apply IHReadOnlyPhi2]; assumption.
    + simpl. replace (d :: nil) with (phi_as_list (Phi_Elem d)) by (simpl; reflexivity).
      apply Conflictness_and_app_l. split; [apply IHReadOnlyPhi1 | apply IHReadOnlyPhi2]; assumption.
  - simpl. apply Conflictness_and_app_r.
    inversion H1; subst.
    split; [apply IHphi1_1 | apply IHphi1_2]; assumption.  
  - simpl. apply Conflictness_and_app_r.
    inversion H1; subst.
    split; [apply IHphi1_1 | apply IHphi1_2]; assumption.
Qed.

Lemma Read_only_disjointness:
  forall phi1 phi2,
    ReadOnlyPhi phi1 ->
    ReadOnlyPhi phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2).
Proof.
  intros phi1 phi2 H. generalize phi2.
  dependent induction H; intros.
  - constructor. intros. inversion H0.
  - constructor. dependent induction H; intros; simpl in *.
    + inversion H0.
    + intuition; subst. constructor.
    + intuition; subst. apply in_app_or in H2. destruct H2; [apply IHReadOnlyPhi1 | apply IHReadOnlyPhi2]; intuition.
    + intuition; subst. apply in_app_or in H2. destruct H2; [apply IHReadOnlyPhi1 | apply IHReadOnlyPhi2]; intuition.
  - simpl. apply Disjointness_and_app_r. split; auto.
  - simpl. apply Disjointness_and_app_r. split; auto.
Qed.    
  
Lemma Det_par_trace_from_readonly :
  forall phi1 phi2,
    ReadOnlyPhi phi1 ->
    ReadOnlyPhi phi2 ->
    Det_Trace (Phi_Par phi1 phi2).
Proof.
  intros phi1 phi2 H1 H2.
  generalize dependent phi2.
  dependent induction H1; intros; constructor.
  - constructor.
  - dependent induction phi2.
    + constructor.
    + constructor; assumption.
    + inversion H2; constructor; [apply IHphi2_1 | apply IHphi2_2 |]; try assumption.
      split; [apply Read_only_no_conflicts | apply Read_only_disjointness]; assumption.
    + inversion H2; constructor; [apply IHphi2_1 | apply IHphi2_2 ]; assumption.
  - split; simpl.
    + intro. inversion H; subst. inversion H0.
    + econstructor; intros. inversion H.
  - constructor.
  - dependent induction H2; try (solve [constructor; auto]).
    constructor; auto.
    split; [apply Read_only_no_conflicts | apply Read_only_disjointness]; assumption.
  - split; simpl.
    + dependent induction H2.
      * intro. inversion H. inversion H1.
      * intro. simpl in H. inversion H; subst.
        { inversion H2; subst.
          - inversion H1; inversion H3.
          - inversion H1; inversion H3. }
      * simpl. replace (DA_Read r a v :: nil) with (phi_as_list (Phi_Elem (DA_Read r a v))) by (simpl; reflexivity).
        apply Conflictness_and_app_l. split; auto.
      * simpl. replace (DA_Read r a v :: nil) with (phi_as_list (Phi_Elem (DA_Read r a v))) by (simpl; reflexivity).
        apply Conflictness_and_app_l. split; auto.
    + dependent induction H2; simpl.
      * constructor; intros. inversion H0.
      * econstructor; intros.
        inversion H; subst; [| inversion H1]. inversion H0; subst; [| inversion H1]. constructor.
      * simpl. replace (DA_Read r a v :: nil) with (phi_as_list (Phi_Elem (DA_Read r a v))) by (simpl; reflexivity).
        apply Disjointness_and_app_l.  split; auto.
      * simpl. replace (DA_Read r a v :: nil) with (phi_as_list (Phi_Elem (DA_Read r a v))) by (simpl; reflexivity).
        apply Disjointness_and_app_l.  split; auto.
  - constructor; apply Det_trace_from_readonly; auto.
  - apply Det_trace_from_readonly; auto.
  - split; simpl.
    + dependent induction H2.
      * intro. inversion H. inversion H1.
      * intro. simpl in H. inversion H; subst.
        { inversion H2; subst.
          - inversion H1; inversion H3.
          - inversion H1; inversion H3. }
      * replace (phi_as_list phi1 ++ phi_as_list phi2) with (phi_as_list (Phi_Seq phi1 phi2)) by (simpl; reflexivity).
        apply Conflictness_and_app_l. split; auto.
      * replace (phi_as_list phi1 ++ phi_as_list phi2) with (phi_as_list (Phi_Seq phi1 phi2)) by (simpl; reflexivity).
        apply Conflictness_and_app_l. split; auto.
    + dependent induction H2; simpl.
      * constructor; intros. inversion H0.
      * replace (DA_Read r a v :: nil) with (phi_as_list (Phi_Elem (DA_Read r a v))) by (simpl; reflexivity). 
        assert (ReadOnlyPhi (Phi_Elem (DA_Read r a v))) by constructor.
        apply IHReadOnlyPhi1 in H. inversion H; subst.
        destruct H4; apply  Disjointness_and_app_r. split; [ auto | ].
        assert (ReadOnlyPhi (Phi_Elem (DA_Read r a v))) by constructor.
        apply IHReadOnlyPhi2 in H4. inversion H4; subst.
        destruct H9. auto.
      * replace (phi_as_list phi1 ++ phi_as_list phi2) with (phi_as_list (Phi_Seq phi1 phi2)) by (simpl; reflexivity).
        apply Disjointness_and_app_l.  split; auto.
      * replace (phi_as_list phi1 ++ phi_as_list phi2) with (phi_as_list (Phi_Seq phi1 phi2)) by (simpl; reflexivity).
        apply Disjointness_and_app_l.  split; auto.
  - apply IHReadOnlyPhi1 in H1_0. assumption.
  - apply Det_trace_from_readonly; auto.
  - split; simpl. 
    + dependent induction H2.
      * intro. inversion H. inversion H1.
      * intro. simpl in H. inversion H; subst.
        { inversion H2; subst.
          - inversion H1; inversion H3.
          - inversion H1; inversion H3. }
      * replace (phi_as_list phi1 ++ phi_as_list phi2) with (phi_as_list (Phi_Par phi1 phi2)) by (simpl; reflexivity).
        apply Conflictness_and_app_l. split; auto.
      * replace (phi_as_list phi1 ++ phi_as_list phi2) with (phi_as_list (Phi_Par phi1 phi2)) by (simpl; reflexivity).
        apply Conflictness_and_app_l. split; auto.
     + dependent induction H2; simpl.
      * constructor; intros. inversion H0.
      * replace (DA_Read r a v :: nil) with (phi_as_list (Phi_Elem (DA_Read r a v))) by (simpl; reflexivity).
        assert (ReadOnlyPhi (Phi_Elem (DA_Read r a v))) by constructor.
        apply IHReadOnlyPhi1 in H. inversion H; subst. destruct H4.
        apply Disjointness_and_app_r. split; [auto |].
        assert (ReadOnlyPhi (Phi_Elem (DA_Read r a v))) by constructor.
        apply IHReadOnlyPhi2 in H4. inversion H4; subst. destruct H9.
        assumption.        
      * replace (phi_as_list phi1 ++ phi_as_list phi2) with (phi_as_list (Phi_Par phi1 phi2)) by (simpl; reflexivity).
        apply Disjointness_and_app_l.  split; auto.
      * replace (phi_as_list phi1 ++ phi_as_list phi2) with (phi_as_list (Phi_Par phi1 phi2)) by (simpl; reflexivity).
        apply Disjointness_and_app_l.  split; auto.
Qed.
     

Lemma Det_trace_from_theta :
  forall theta1 theta2 phi1 phi2,
    phi1 ⋞ theta1 ->
    phi2 ⋞ theta2 ->
    Disjointness theta1 theta2 /\ not (Conflictness theta1 theta2) -> 
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Det_Trace (Phi_Par phi1 phi2).
Proof.
  intros theta1 theta2 phi1 phi2 H1 H2 [HDisj HConf] HDet1 HDet2.
  constructor; [assumption | assumption | split].
  - intro. dependent induction H. inversion H3; subst. apply HConf.
    + destruct theta1; destruct theta2; constructor.
      eapply Conflict_computed_conflict_dynamic_action_read; eauto. 
    + destruct theta1 ; [ | apply HConf; constructor ].
      destruct theta2 ; [ | apply HConf; constructor ].    
      apply HConf. constructor. eapply Conflict_computed_conflict_dynamic_action_write; eauto.
  - destruct theta1; [ | dependent destruction HDisj].
    destruct theta2; [ | dependent destruction HDisj]. 
    dependent destruction HDisj. constructor; intros.
    eapply Disjoint_computed_disjoint_dynamic_action with (e1:=e) (e2:=e0); eauto.
Qed.

Lemma unique_heap :
  forall (heap heap1 heap2: Heap) (acts_mu1 acts_mu2: Phi) (theta1 theta2 : Theta),
    acts_mu1 ⋞ theta1 ->
    acts_mu2 ⋞ theta2 ->
    Disjointness theta1 theta2 /\ not (Conflictness theta1 theta2) ->
    Det_Trace acts_mu1 ->
    Det_Trace acts_mu2 ->
    (Phi_Par acts_mu1 acts_mu2, heap) ==>* (Phi_Nil, heap2) ->
    (Phi_Par acts_mu1 acts_mu2, heap) ==>* (Phi_Nil, heap1) ->
    heap1 ≡@{Heap} heap2.
Proof.
  intros.
  eapply Diamond_Term_Walk; eauto.
  eapply Det_trace_from_theta; eauto.
Qed.

Lemma unique_heap_new :
  forall (heapa heapb heap1 heap2: Heap) (acts_mu1 acts_mu2: Phi) (theta1 theta2 : Theta),
    acts_mu1 ⋞ theta1 ->
    acts_mu2 ⋞ theta2 ->
    Disjointness theta1 theta2 /\ not (Conflictness theta1 theta2) ->
    Det_Trace acts_mu1 ->
    Det_Trace acts_mu2 ->
    heapa ≡@{Heap} heapb ->
    (Phi_Par acts_mu1 acts_mu2, heapa) ==>* (Phi_Nil, heap1) ->
    (Phi_Par acts_mu1 acts_mu2, heapb) ==>* (Phi_Nil, heap2) ->
    heap1 ≡@{Heap} heap2.
Proof.
  intros.
  eapply Diamond_Term_Walk_new; eauto.
  eapply Det_trace_from_theta; eauto.
Qed.
