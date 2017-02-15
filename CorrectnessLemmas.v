Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.

Add LoadPath "." as Top0.
Require Import Top0.Definitions.
Require Import Top0.Heap.
Require Import Top0.Axioms.

Lemma UnionEmptyWithEffIsEff:
  forall eff,
    Union_Theta (Some empty_set) eff = eff.
Proof.
  intro.
  induction eff; simpl; [| reflexivity]. 
  apply f_equal.
  assert (set_union empty_set a = a).
  - apply Extensionality_Ensembles.
    unfold Same_set, Included; split; intros x H_; unfold In in *.
    * destruct H_; [inversion H | assumption ].
    * apply Union_intror. assumption.
  - assumption.    
Qed.


Lemma PhiInThetaTop:
  forall phi, phi ⊑ Theta_Top.
Proof.  
  induction phi; intros; econstructor; try assumption; apply DAT_Top.
Qed.

Lemma EmptyUnionisEmptySet :
  forall acts a,
    acts = Empty_set ComputedAction ->
    a = Empty_set ComputedAction ->
    Union ComputedAction acts a =  Empty_set ComputedAction.
Proof.
  intros acts a H1 H2.
  apply Extensionality_Ensembles.
  unfold Same_set, Included.
  split.
  - intros x Hx. rewrite H1 in Hx. 
    replace (Union ComputedAction (Empty_set ComputedAction) a) 
    with a in Hx 
    by (apply Extensionality_Ensembles;
        unfold Same_set, Included; split; intros y Hy; 
        unfold In in *;
          [apply Union_intror; assumption | destruct Hy; [inversion H | assumption]]).
    rewrite H2 in Hx. inversion Hx.
  - intros x Hx. inversion Hx.
Qed. 

Lemma EmptyUnionisEmptySet_2 :
  forall acts a,
    Union ComputedAction acts a =  Empty_set ComputedAction -> 
    acts = Empty_set ComputedAction /\ a = Empty_set ComputedAction.
Proof.
  intros. split.
  + rewrite <- H.
    apply Extensionality_Ensembles.
    unfold Same_set, Included.
    split; intros. 
    * apply Union_introl; assumption.
    * rewrite H in H0. inversion H0.
 + rewrite <- H.
   apply Extensionality_Ensembles.
   unfold Same_set, Included.
   split; intros. 
   * apply Union_intror; assumption.
   * rewrite H in H0. inversion H0.
Qed.

Lemma EmptyIsNil:
  forall phi, phi ⊑ Theta_Empty -> phi = Phi_Nil.
Proof.
  induction phi; intros.
  - reflexivity. 
  - unfold Theta_Empty, empty_set in H. 
    dependent induction H; inversion H; subst; try (solve [inversion H2]).
    + clear H2. clear H0. clear a. clear acts. 
      dependent induction H; try (solve [inversion H]); intros.
      * eapply IHDA_in_Theta; eauto. apply EmptyUnionisEmptySet_2 in x.
        destruct x; subst. intuition.
      * eapply IHDA_in_Theta; eauto. apply EmptyUnionisEmptySet_2 in x.
         destruct x; subst. intuition.
    + dependent induction H; try (solve [inversion H]).
      * eapply IHDA_in_Theta; eauto.  apply EmptyUnionisEmptySet_2 in x.
        destruct x; subst. intuition.
      * eapply IHDA_in_Theta; eauto.  apply EmptyUnionisEmptySet_2 in x.
        destruct x; subst. intuition.
  - inversion H; subst. 
    assert ( H_ : phi1 = Phi_Nil ) by (apply IHphi1; inversion H; assumption); rewrite H_.
    assert ( H__ : phi2 = Phi_Nil ) by (apply IHphi2; inversion H; assumption); rewrite H__.
    rewrite Phi_Par_Nil_R. reflexivity.
  - assert ( H_ : phi1 = Phi_Nil ) by (apply IHphi1; inversion H; assumption); rewrite H_.
    assert ( H__ : phi2 = Phi_Nil ) by (apply IHphi2; inversion H; assumption); rewrite H__.
    rewrite Phi_Seq_Nil_R. reflexivity.
Qed.

Lemma EmptyInAnyTheta:
  forall phi theta, phi ⊑ Theta_Empty -> phi ⊑ theta .
Proof.  
  induction phi; intros; try (solve [econstructor]).
  - econstructor. unfold Theta_Empty, empty_set in H.
    dependent induction H; dependent induction H; try (solve [inversion H]). 
    * eapply IHDA_in_Theta; eauto. apply EmptyUnionisEmptySet_2 in x.
        destruct x; subst. intuition.
    * eapply IHDA_in_Theta; eauto. apply EmptyUnionisEmptySet_2 in x.
        destruct x; subst. intuition.
  - inversion H; subst. apply EmptyIsNil in H2. apply EmptyIsNil in H4. subst.
    apply PTS_Par. apply IHphi1. apply PTS_Nil.  apply IHphi1. apply PTS_Nil.
  - inversion H; subst. apply EmptyIsNil in H2. apply EmptyIsNil in H4. subst.
    apply PTS_Seq. apply IHphi1. apply PTS_Nil.  apply IHphi1. apply PTS_Nil. 
Qed.

Lemma EnsembleUnionSym:
  forall (phi : Phi) (theta theta' : Theta),
    phi ⊑ theta -> phi ⊑ (Union_Theta theta theta') /\ phi ⊑ (Union_Theta theta' theta).
Proof.
  intros phi theta theta' H.
  generalize dependent theta'.
  induction H; intros theta'.
  - split; [apply PTS_Nil | apply PTS_Nil]. 
  - destruct theta as [acts|]; destruct theta' as [acts'|]; 
    intuition; simpl; try (solve [apply PTS_Elem; apply DAT_Top]). 
    + apply PTS_Elem. apply DAT_intror. assumption.
    + apply PTS_Elem. apply DAT_introl. assumption.    
  - destruct theta as [acts|]; destruct theta' as [acts'|]; intuition;
    (apply PTS_Seq; [apply IHPhi_Theta_Soundness1 | apply IHPhi_Theta_Soundness2]).
  - split; destruct theta as [acts|]; destruct theta' as [acts'|]; intuition;
    (apply PTS_Par; [apply IHPhi_Theta_Soundness1 | apply IHPhi_Theta_Soundness2]).  
Qed.

Lemma EmptyUnionIsIdentity : 
  forall p eff, p ⊑ (Union_Theta (Some empty_set) eff) -> p ⊑ eff. 
Proof.
  intros p eff H; inversion H; subst; try apply PTS_Nil.  
  induction eff; apply PTS_Elem;
  try assert ( HUnionEmpty : (Union_Theta (Some empty_set)  (Some a)) = Some a) 
    by (unfold Union_Theta, set_union, empty_set; f_equal;
         apply Extensionality_Ensembles; red; split; unfold Included;
         intros x Hx; [ inversion Hx; subst; [contradiction | assumption] | apply Union_intror]; auto).
  - rewrite HUnionEmpty in H0; assumption.
  - apply DAT_Top. 
  - induction eff. assert ( HUnionEmpty : (Union_Theta (Some empty_set)  (Some a)) = Some a) 
     by (unfold Union_Theta, set_union, empty_set; f_equal;
         apply Extensionality_Ensembles; red; split; unfold Included;
         intros x Hx; [ inversion Hx; subst; [contradiction | assumption] | apply Union_intror]; auto).
    rewrite <- HUnionEmpty. auto. now simpl in H.
  - induction eff. assert ( HUnionEmpty : (Union_Theta (Some empty_set)  (Some a)) = Some a) 
     by (unfold Union_Theta, set_union, empty_set; f_equal;
         apply Extensionality_Ensembles; red; split; unfold Included;
         intros x Hx; [ inversion Hx; subst; [contradiction | assumption] | apply Union_intror]; auto).
    rewrite <- HUnionEmpty. auto. now simpl in H. 
Qed.

Lemma EnsembleUnionComp :
  forall (phi1 phi2 : Phi) (theta1 theta2 : Theta),
    phi1 ⊑ theta1 -> phi2 ⊑ theta2 -> Phi_Seq phi1  phi2 ⊑ (Union_Theta theta1 theta2).
Proof. 
  intros phi1 phi2 theta1 theta2 H1 H2.
  econstructor.
  - apply EnsembleUnionSym with (theta' := theta2) in H1. intuition. 
  - apply EnsembleUnionSym with (theta' := theta1) in H2. intuition.
Qed.


Lemma Theta_introl: 
  forall phi theta1 theta2, phi ⊑ theta1 -> phi ⊑ Union_Theta theta1 theta2.
Proof.
  induction phi; intros; try (solve [econstructor]).
  - inversion H; subst; inversion H1; subst; simpl;
    try (solve [assumption |
                induction theta2; [econstructor; constructor; now apply Union_introl | econstructor; constructor] |
                induction theta2; [econstructor; now apply DAT_intror | econstructor; constructor ]] ).
  - apply PTS_Par. apply IHphi1. now inversion H. apply IHphi2. now inversion H.
  - apply PTS_Seq. apply IHphi1. now inversion H. apply IHphi2. now inversion H.
Qed.    

Lemma Theta_intror:
  forall phi theta1 theta2, phi ⊑ theta1 -> phi ⊑ Union_Theta theta2 theta1.
Proof.
  induction phi; intros; try (solve [econstructor]).
  - inversion H; subst; inversion H1; subst; simpl;
    try (solve [assumption |
                induction theta2; [econstructor; constructor; now apply Union_intror | econstructor; constructor] |
                induction theta2; [econstructor; now apply DAT_introl | econstructor; constructor ]] ).
  - apply PTS_Par. apply IHphi1. now inversion H. apply IHphi2. now inversion H.
  - apply PTS_Seq. apply IHphi1. now inversion H. apply IHphi2. now inversion H.
Qed.


Lemma Disjointness_app_or_r :
  forall phi1 phi2 phi3,
    Disjoint_Traces (phi_as_list phi1 ++ phi_as_list phi2) (phi_as_list phi3) ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi3) \/
    Disjoint_Traces (phi_as_list phi2) (phi_as_list phi3).
Proof.
  intros phi1 phi2 phi3 H. 
  dependent induction H.
  left; econstructor; intros.
  apply H;  [ apply in_or_app; left | ]; assumption.
Qed.

Lemma Disjointness_app_or_l :
  forall phi1 phi2 phi3,
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2 ++ phi_as_list phi3) ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) \/
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi3).
Proof.
  intros phi1 phi2 phi3 H. 
  dependent induction H.
  left; econstructor; intros.
  apply H;  [ | apply in_or_app; left]; assumption.
Qed.

Lemma Disjointness_app_app_and_r :
  forall phi1 phi2 phi3,
    Disjoint_Traces (phi_as_list phi1 ++ phi_as_list phi2) (phi_as_list phi3) ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi3) /\
    Disjoint_Traces (phi_as_list phi2) (phi_as_list phi3).
Proof.
  intros phi1 phi2 phi3 H.  
  dependent induction H; split.
  - econstructor; intros. apply H;  [ apply in_or_app; left | ]; assumption.
  - econstructor; intros. apply H;  [ apply in_or_app; right | ]; assumption.
Qed.

Lemma Disjointness_app_app_and_l :
  forall phi1 phi2 phi3,
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2 ++ phi_as_list phi3) ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) /\
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi3).
Proof.
  intros phi1 phi2 phi3 H.  
  dependent induction H; split.
  - econstructor; intros. apply H; [ |  apply in_or_app; left ]; assumption.
  - econstructor; intros. apply H;  [ | apply in_or_app; right ]; assumption.
Qed.

Lemma Disjointness_and_app_r :
  forall phi1 phi2 phi3,
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi3) /\
    Disjoint_Traces (phi_as_list phi2) (phi_as_list phi3) ->
    Disjoint_Traces (phi_as_list phi1 ++ phi_as_list phi2) (phi_as_list phi3).
Proof.
  intros phi1 phi2 phi3 H. destruct H. 
  generalize dependent phi2.
  dependent induction H; intros.
  econstructor; intros.
  rename H into H1_3. inversion H0 as [? ? H2_3]; subst.
  apply in_app_or in H1; destruct H1; [apply H1_3 | apply H2_3]; auto.
Qed.

Lemma Disjointness_and_app_l :
  forall phi1 phi2 phi3,
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) /\
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi3) ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2 ++ phi_as_list phi3).
Proof.
  intros phi1 phi2 phi3 H. destruct H. 
  generalize dependent phi2.
  dependent induction H0; intros.
  econstructor; intros. 
  rename H into H1_3. inversion H0 as [? ? H1_2]; subst.
  apply in_app_or in H2; destruct H2; [apply H1_2 | apply H1_3]; auto.
Qed.

Lemma Conflictness_app_or_l :
  forall phi1 phi2 phi3,
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Det_Trace phi3 ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2 ++ phi_as_list phi3) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) \/
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi3). 
Proof.
  intros phi1 phi2 phi3 HDet1 HDet2 HDet3 H. unfold not in *.
  left. intro. apply H. clear H.  
  dependent induction H0;
    inversion HDet1; inversion HDet2; inversion HDet3; subst; simpl in *;
    try (solve [contradiction |
                intuition; subst; econstructor; eauto; apply in_eq |
                intuition; subst; inversion HDet3; subst; econstructor; eauto; apply in_eq |
                intuition; subst; rewrite app_nil_r; econstructor; eauto; apply in_eq |
                intuition; subst; econstructor; eauto; [apply in_eq | apply in_or_app; left; assumption] |
                 econstructor; eauto;  apply in_or_app; left; assumption
               ]).
Qed.

Lemma Conflictness_app_or_r :
  forall phi1 phi2 phi3,
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Det_Trace phi3 ->
    ~ Conflict_Traces (phi_as_list phi1 ++ phi_as_list phi2) (phi_as_list phi3) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi3) \/
    ~ Conflict_Traces (phi_as_list phi2) (phi_as_list phi3). 
Proof.
  intros phi1 phi2 phi3 HDet1 HDet2 HDet3 H. unfold not in *.
  left. intro. apply H. clear H.  
  dependent induction H0;
    inversion HDet1; inversion HDet2; inversion HDet3; subst; simpl in *;
    try (solve [contradiction |
                intuition; subst; econstructor; [ apply in_eq | apply in_eq | eassumption] |
                intuition; subst; econstructor; [ apply in_eq | eassumption | assumption] |
                intuition; subst; econstructor; [rewrite app_nil_r; eassumption |  apply in_eq | assumption ] |
                intuition; subst; econstructor; [rewrite app_nil_r; eassumption | eassumption | assumption ] |
                intuition; subst; econstructor; [apply in_or_app; left; eassumption |  apply in_eq | assumption ] |
                intuition; subst; econstructor; [ apply in_or_app; left; eassumption | eassumption | assumption ]
               ]).
Qed.

Lemma Conflictness_app_and_l :
  forall phi1 phi2 phi3,
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Det_Trace phi3 ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2 ++ phi_as_list phi3) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) /\
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi3). 
Proof.
  intros phi1 phi2 phi3 HDet1 HDet2 HDet3 H. unfold not in *.
  split.
  - intro. apply H. clear H.
    dependent induction H0;
      inversion HDet1; inversion HDet2; inversion HDet3; subst; simpl in *;
      try (solve [contradiction |
                intuition; subst; econstructor; eauto; apply in_eq |
                intuition; subst; inversion HDet3; subst; econstructor; eauto; apply in_eq |
                intuition; subst; rewrite app_nil_r; econstructor; eauto; apply in_eq |
                intuition; subst; econstructor; eauto; [apply in_eq | apply in_or_app; left; assumption] |
                 econstructor; eauto;  apply in_or_app; left; assumption
                 ]).
  -  intro. apply H. clear H.
    dependent induction H0;
      inversion HDet1; inversion HDet2; inversion HDet3; subst; simpl in *;
      try (solve [contradiction |
                  econstructor; eauto;  apply in_or_app; right; assumption |
                  intuition; subst; econstructor; eauto; [ apply in_eq | apply in_cons; apply in_eq] |
                  intuition; subst; econstructor; eauto; [ apply in_eq | apply in_cons; assumption] |
                  intuition; subst; econstructor; eauto; apply in_cons; apply in_eq |
                  intuition; subst; econstructor; eauto; apply in_cons;assumption
                 ]).
Qed.


Lemma Conflictness_app_and_r :
  forall phi1 phi2 phi3,
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Det_Trace phi3 ->
    ~ Conflict_Traces (phi_as_list phi1 ++ phi_as_list phi2) (phi_as_list phi3) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi3) /\
    ~ Conflict_Traces (phi_as_list phi2) (phi_as_list phi3). 
Proof.
  intros phi1 phi2 phi3 HDet1 HDet2 HDet3 H. unfold not in *.
  split.
  - intro. apply H. clear H.
    dependent induction H0;
      inversion HDet1; inversion HDet2; inversion HDet3; subst; simpl in *;
      try (solve [contradiction |
                intuition; subst; econstructor; eauto; apply in_eq |
                intuition; subst; inversion HDet3; subst; econstructor; eauto; apply in_eq |
                intuition; subst; rewrite app_nil_r; econstructor; eauto; apply in_eq |
                intuition; subst; econstructor; eauto; [apply in_eq | apply in_or_app; left; assumption] |
                 econstructor; eauto;  apply in_or_app; left; assumption
                 ]).
  -  intro. apply H. clear H.
    dependent induction H0;
      inversion HDet1; inversion HDet2; inversion HDet3; subst; simpl in *;
      try (solve [contradiction |
                  econstructor; eauto;  apply in_or_app; right; assumption |
                  intuition; subst; econstructor; eauto; [ apply in_eq | apply in_cons; apply in_eq] |
                  intuition; subst; econstructor; eauto; apply in_cons; apply in_eq |
                  intuition; subst; econstructor; eauto; apply in_cons;assumption |
                  intuition; subst; econstructor; eauto; [apply in_cons; apply in_eq | apply in_eq] |
                  intuition; subst; econstructor; eauto; [apply in_cons; assumption | apply in_eq]
                 ]).
Qed.

Lemma Conflictness_or_app_l :
  forall phi1 phi2 phi3,
    Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) \/
    Conflict_Traces (phi_as_list phi1) (phi_as_list phi3) ->
    Conflict_Traces (phi_as_list phi1) (phi_as_list phi2 ++ phi_as_list phi3).
Proof.
  intros phi1 phi2 phi3 H.
  destruct H. 
  - dependent induction H. econstructor; eauto. apply in_or_app. left; assumption.
  - dependent induction H. econstructor; eauto. apply in_or_app. right; assumption.
Qed.

Lemma Conflictness_or_app_r :
  forall phi1 phi2 phi3,
    Conflict_Traces (phi_as_list phi1) (phi_as_list phi3) \/
    Conflict_Traces (phi_as_list phi2) (phi_as_list phi3) ->
    Conflict_Traces (phi_as_list phi1 ++ phi_as_list phi2) (phi_as_list phi3).
Proof.
  intros phi1 phi2 phi3 H.
  destruct H. 
  - dependent induction H. econstructor; eauto. apply in_or_app. left; assumption.
  - dependent induction H. econstructor; eauto. apply in_or_app. right; assumption.
Qed.
 
Lemma Conflictness_and_app_l :
  forall phi1 phi2 phi3,
    ~ Conflict_Traces (phi_as_list phi1 ) (phi_as_list phi2 ) /\
    ~ Conflict_Traces (phi_as_list phi1 ) (phi_as_list phi3 ) ->
    ~ Conflict_Traces (phi_as_list phi1 ) (phi_as_list phi2  ++ phi_as_list phi3 ).
Proof.
  intros phi1 phi2 phi3 H. unfold not in *. destruct H. 
  intro. dependent induction H1.  apply in_app_or in H3. intuition.
  + apply H. econstructor; eauto.
  + apply H0. econstructor; eauto. 
Qed.


Lemma Conflictness_and_app_r :
  forall phi1 phi2 phi3,
    ~ Conflict_Traces (phi_as_list phi1 ) (phi_as_list phi3 ) /\
    ~ Conflict_Traces (phi_as_list phi2 ) (phi_as_list phi3 ) ->
    ~ Conflict_Traces (phi_as_list phi1 ++ phi_as_list phi2)  (phi_as_list phi3 ).
Proof.
  intros phi1 phi2 phi3 H. unfold not in *. destruct H. 
  intro. dependent induction H1.  apply in_app_or in H3. intuition.
  + apply H. econstructor; eauto.
  + apply H0. econstructor; eauto. 
Qed.

Lemma EmptyTracePreservesHeap_1 : 
  forall h r env e same_h v' acts, (h, r, env, e) ⇓ (same_h, v', acts) -> acts = Phi_Nil -> h = same_h.
Proof.
  intros h r env e same_h v' acts H Hnil.  (*destruct H as [H Hnil]. *)
  dependent induction H; auto; inversion Hnil.
  - eapply IHBigStep; [reflexivity | auto].
  - eapply IHBigStep; [reflexivity | auto]. 
Qed.


Lemma EMPTYTRACEPRESERVESHEAP_1 : 
  forall h r env e same_h v' acts, (h, r, env, e) ⇓ (same_h, v', acts) -> acts = Phi_Nil -> h = same_h.
Proof.
  intros h r env e same_h v' acts H Hnil.  (*destruct H as [H Hnil]. *)
  dependent induction H; auto; inversion Hnil.
  - eapply IHBigStep; [reflexivity | auto].
  - eapply IHBigStep; [reflexivity | auto]. 
Qed.
       
Lemma ReadOnlyTracePreservesHeap_1 : 
  forall h env rho e same_h v' acts, (h, env, rho, e) ⇓ (same_h, v', acts) -> 
                                   ReadOnlyPhi acts -> h = same_h.
Proof.
  intros h env rho e same_h v' acts H.
  dependent induction H; intros;
  try (solve [reflexivity]).
  - inversion H2; inversion H5; subst;
    assert (h=fheap) by (eapply  IHBigStep1; [reflexivity | assumption]); subst;
    assert (aheap=fheap) by (symmetry; eapply IHBigStep2; assumption); subst;
    (eapply IHBigStep3; [reflexivity | reflexivity | assumption]).
  - inversion H2; subst;
    assert (h=fheap) by (eapply  IHBigStep1; [reflexivity | assumption]); subst;
    (eapply IHBigStep2; [reflexivity | reflexivity | assumption]). 
  - inversion H5; subst. inversion H9; subst. 
    assert (h = heap_mu1) by (eapply IHBigStep3; eauto).
    assert (h = heap_mu2) by (eapply IHBigStep4; eauto). 
    rewrite <- H6 in H2. rewrite <- H7 in H3.
    assert (h = same_h) by (eapply ReadOnlyWalkSameHeap; eauto).
    assumption.
  - inversion H1; subst;
    assert (h=cheap) by (eapply  IHBigStep1; [reflexivity | assumption]); subst;
    (eapply IHBigStep2; assumption).
  - inversion H1; subst;
    assert (h=cheap) by (eapply  IHBigStep1; [reflexivity | assumption]); subst;
    (eapply IHBigStep2; assumption).
  - inversion H2; inversion H6.
  - inversion H2; subst; (eapply IHBigStep; [reflexivity | assumption]).
  - inversion H2; inversion H6.
  - inversion H1; subst;
    assert (h=lheap) by (eapply IHBigStep1; [reflexivity | assumption]); subst;
    (eapply IHBigStep2; [reflexivity | assumption]).
  - inversion H1; subst;
    assert (h=lheap) by (eapply IHBigStep1; [reflexivity | assumption]); subst;
    (eapply IHBigStep2; [reflexivity | assumption]).
  - inversion H1; subst;
    assert (h=lheap) by (eapply IHBigStep1; [reflexivity | assumption]); subst;
    (eapply IHBigStep2; [reflexivity | assumption]).
  - inversion H1; subst;
    assert (h=lheap) by (eapply IHBigStep1; [reflexivity | assumption]); subst;
    (eapply IHBigStep2; [reflexivity | assumption]).
  - eapply EmptyTracePreservesHeap_1; eauto.
  - eapply EmptyTracePreservesHeap_1. eauto. reflexivity. 
Qed.   

Inductive SA_DA_Soundness : StaticAction -> DynamicAction -> Prop :=
| SA_DA_Read : forall r l v, SA_DA_Soundness (SA_Read (Rgn2_Const true true r)) (DA_Read r l v)
| SA_DA_Write : forall r l v, SA_DA_Soundness (SA_Write (Rgn2_Const true true r)) (DA_Write r l v)
| SA_DA_Alloc : forall r l v, SA_DA_Soundness (SA_Alloc (Rgn2_Const true true r)) (DA_Alloc r l v).

Inductive Epsilon_Phi_Soundness :  (Epsilon * Phi) -> Prop := 
  | EPS : forall st dy, (forall da, DA_in_Phi da dy -> exists sa, Ensembles.In StaticAction st sa /\ SA_DA_Soundness sa da) -> Epsilon_Phi_Soundness (st, dy).

Lemma ReadOnlyStaticImpliesReadOnlySubstStatic : 
  forall eps rho,
    ReadOnlyStatic eps ->
    ReadOnlyStatic (fold_subst_eps rho eps).
Proof.
  intros eps rho ROS.
  induction ROS.
  - replace (fold_subst_eps rho Empty_Static_Action) with (Empty_Static_Action).
    constructor.
    apply Extensionality_Ensembles;
    unfold Same_set, Included; split; intros x H; unfold Ensembles.In in *.
    inversion H. inversion H. destruct H0. inversion H0.
  - replace (fold_subst_eps rho (Singleton_Static_Action (SA_Read r))) with (Singleton_Static_Action (SA_Read (fold_subst_rgn rho r))).
    constructor.
    apply Extensionality_Ensembles;
    unfold Same_set, Included; split; intros x H; unfold Ensembles.In in *.
    inversion H.
    unfold fold_subst_eps. exists (SA_Read r). intuition.
    inversion H. inversion H0. inversion H1. subst. unfold fold_subst_sa; simpl. apply Ensembles.In_singleton.
  - replace (fold_subst_eps rho (Union_Static_Action eps1 eps2)) with (Union_Static_Action (fold_subst_eps rho eps1) (fold_subst_eps rho eps2)).
    constructor; assumption.
    apply Extensionality_Ensembles;
    unfold Same_set, Included; split; intros x H; unfold Ensembles.In in *.
    inversion H; subst; inversion H0; unfold fold_subst_eps; exists x0; split;
    [apply Ensembles.Union_introl | | apply Ensembles.Union_intror | ]; intuition.
    inversion H. inversion H0. inversion H1; subst;
    [apply Ensembles.Union_introl | apply Ensembles.Union_intror]; unfold Ensembles.In; unfold fold_subst_eps; exists x0; intuition.
Qed.

Lemma ReadOnlyStaticImpliesReadOnlyPhi :
  forall eps phi,
    ReadOnlyStatic eps ->
    Epsilon_Phi_Soundness (eps, phi) ->
    ReadOnlyPhi phi.
Proof.
  intros eps phi. induction phi; intros ROS H.
  - constructor.
  - induction d.
    + exfalso; induction ROS.
      * inversion H; subst. 
        edestruct H1; [econstructor | destruct H0 ; inversion H0].
      * inversion H; subst.
        edestruct H1; [econstructor | destruct H0 ; inversion H0; subst; inversion H2 ].
      * inversion H; subst. destruct (H1 (DA_Alloc r n v)) as [ ? [ ? ? ]]; [ constructor | ].
        inversion H0; subst.
        apply IHROS1; constructor; intros; inversion H4; subst; exists x; intuition.
        apply IHROS2; constructor; intros; inversion H4; subst; exists x; intuition.
    + econstructor.
    + exfalso; induction ROS.
      * inversion H; subst. 
        edestruct H1; [econstructor | destruct H0 ; inversion H0].
      * inversion H; subst.
        edestruct H1; [econstructor | destruct H0 ; inversion H0; subst; inversion H2 ].
      * inversion H; subst. destruct (H1 (DA_Write r n v)) as [ ? [ ? ? ]]; [ constructor | ].
        inversion H0; subst.
        apply IHROS1; constructor; intros; inversion H4; subst; exists x; intuition.
        apply IHROS2; constructor; intros; inversion H4; subst; exists x; intuition.
  - assert (Epsilon_Phi_Soundness (eps, phi1)).
    constructor; intros da daIn; inversion H; subst; apply (H1 da); apply DAP_Par; auto.
    assert (Epsilon_Phi_Soundness (eps, phi2)).
    constructor; intros da daIn; inversion H; subst; apply (H2 da); apply DAP_Par; auto.
    constructor; auto.
  - assert (Epsilon_Phi_Soundness (eps, phi1)).
    constructor; intros da daIn; inversion H; subst; apply (H1 da); apply DAP_Seq; auto.
    assert (Epsilon_Phi_Soundness (eps, phi2)).
    constructor; intros da daIn; inversion H; subst; apply (H2 da); apply DAP_Seq; auto.
    constructor; auto.
Qed.

Lemma EmptyTracePreservesHeap_2 : 
  forall h r env e same_h v acts,
    (h, r, env, e) ⇓ (h, v, acts) -> h = same_h -> (same_h, r, env, e) ⇓ (same_h, v, acts).
Proof.
  intros h r env e same_h v' acts Dyn H. now subst.
Qed.

Lemma EmptyTracePreservesHeap_3 : 
  forall h r env e same_h v acts,
    (same_h, r, env, e) ⇓ (same_h, v, acts) -> (h, r, env, e) ⇓ (same_h, v, acts) -> acts = Phi_Nil -> (h, r, env, e) ⇓ (h, v, acts).
Proof.
  intros h r env e same_h v' acts H Dyn1 Hnil.
  apply EmptyTracePreservesHeap_1 in Dyn1. now subst. exact Hnil.
Qed.

Lemma EmptyTracePreservesHeap_4 : 
  forall h r env e same_h v,
    (h, r, env, e) ⇓ (same_h, v, Phi_Nil) -> h = same_h.
Proof.
   intros h r env e same_h v' Dyn1.
   dependent induction Dyn1; auto.
   eapply IHDyn1. reflexivity. eapply IHDyn1. reflexivity.
Qed.


Lemma EmptyTracePreservesHeap_5 : 
  forall h r env e  v,
    (h, r, env, e) ⇓ (h, v, Phi_Nil) ->
    exists same_h,  (same_h, r, env, e) ⇓ (h, v, Phi_Nil).
Proof.
  intros h r env e v H.
  dependent induction H; exists h; econstructor; auto.
  assumption. assumption.
Qed.
