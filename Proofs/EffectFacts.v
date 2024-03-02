Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.

Require Import Definitions.Axioms.
Require Import Definitions.GHeap.
Require Import Definitions.Keys.
Require Import Definitions.ComputedActions.
Require Import Definitions.DynamicActions.
Require Import Definitions.StaticActions.
Require Import Definitions.Regions.
Require Import Definitions.Types.


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
  forall phi, phi ⋞ Theta_Top.
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
  forall phi, phi ⋞ Theta_Empty -> phi = Phi_Nil.
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
  forall phi theta, phi ⋞ Theta_Empty -> phi ⋞ theta .
Proof.  
  induction phi; intros; try (solve [econstructor]).
  - econstructor. unfold Theta_Empty, empty_set in H.
    dependent induction H; dependent induction H; try (solve [inversion H]). 
    * eapply IHDA_in_Theta; eauto. apply EmptyUnionisEmptySet_2 in x.
        destruct x; subst. intuition.
    * eapply IHDA_in_Theta; eauto. apply EmptyUnionisEmptySet_2 in x.
        destruct x; subst. intuition.
  - inversion H; subst.
    apply PTS_Par; [ apply IHphi1; assumption | apply IHphi2; assumption]. 
  - inversion H; subst.
    apply PTS_Seq; [ apply IHphi1; assumption | apply IHphi2; assumption]. 
Qed.

Lemma EnsembleUnionSym:
  forall (phi : Phi) (theta theta' : Theta),
    phi ⋞ theta -> phi ⋞ (Union_Theta theta theta') /\ phi ⋞ (Union_Theta theta' theta).
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
  forall p eff, p ⋞ (Union_Theta (Some empty_set) eff) -> p ⋞ eff. 
Proof.
  intros p eff H; inversion H; subst; try apply PTS_Nil.  
  induction eff; apply PTS_Elem;
  try assert ( HUnionEmpty : (Union_Theta (Some empty_set)  (Some a)) = Some a) 
    by (unfold Union_Theta, set_union, empty_set; f_equal;
         apply Extensionality_Ensembles; red; split; unfold Included;
         intros x Hx; [ inversion Hx; subst; [contradiction | assumption] | apply Union_intror]; auto).
  -  rewrite HUnionEmpty in H0; assumption.
  -   apply DAT_Top. 
  - induction eff. assert ( HUnionEmpty : (Union_Theta (Some empty_set)  (Some a)) = Some a) 
     by (unfold Union_Theta, set_union, empty_set; f_equal;
         apply Extensionality_Ensembles; red; split; unfold Included;
         intros x Hx; [ inversion Hx; subst; [contradiction | assumption] | apply Union_intror]; auto).
    rewrite <- HUnionEmpty.  auto. now simpl in H.
  -  induction eff. assert ( HUnionEmpty : (Union_Theta (Some empty_set)  (Some a)) = Some a) 
     by (unfold Union_Theta, set_union, empty_set; f_equal;
         apply Extensionality_Ensembles; red; split; unfold Included;
         intros x Hx; [ inversion Hx; subst; [contradiction | assumption] | apply Union_intror]; auto).
    rewrite <- HUnionEmpty. auto. now simpl in H. 
Qed.

Lemma EmptyUnionIsIdentity_2 : 
  forall p eff,  p ⋞ eff -> p ⋞ (Union_Theta (Some empty_set) eff). 
Proof.
  intros p eff H; inversion H; subst; try apply PTS_Nil.  
  induction eff; apply PTS_Elem;
  try assert ( HUnionEmpty : (Union_Theta (Some empty_set)  (Some a)) = Some a) 
      by (unfold Union_Theta, set_union, empty_set; f_equal;
         apply Extensionality_Ensembles; red; split; unfold Included;
         intros x Hx; [ inversion Hx; subst; [contradiction | assumption] | apply Union_intror]; auto).
  - rewrite HUnionEmpty. assumption.
  - apply DAT_Top.
  - induction eff. 
    assert ( HUnionEmpty : (Union_Theta (Some empty_set)  (Some a)) = Some a) 
     by (unfold Union_Theta, set_union, empty_set; f_equal;
         apply Extensionality_Ensembles; red; split; unfold Included;
         intros x Hx; [ inversion Hx; subst; [contradiction | assumption] | apply Union_intror]; auto).
    + rewrite HUnionEmpty. assumption.
    + simpl. assumption.
  - induction eff. 
    assert ( HUnionEmpty : (Union_Theta (Some empty_set)  (Some a)) = Some a) 
     by (unfold Union_Theta, set_union, empty_set; f_equal;
         apply Extensionality_Ensembles; red; split; unfold Included;
         intros x Hx; [ inversion Hx; subst; [contradiction | assumption] | apply Union_intror]; auto).
    + rewrite HUnionEmpty. assumption.
    + simpl. assumption.  
Qed.

Lemma EnsembleUnionComp :
  forall (phi1 phi2 : Phi) (theta1 theta2 : Theta),
    phi1 ⋞ theta1 -> phi2 ⋞ theta2 -> Phi_Seq phi1  phi2 ⋞ (Union_Theta theta1 theta2).
Proof. 
  intros phi1 phi2 theta1 theta2 H1 H2.
  econstructor.
  - apply EnsembleUnionSym with (theta' := theta2) in H1. intuition. 
  - apply EnsembleUnionSym with (theta' := theta1) in H2. intuition.
Qed.


Lemma Theta_introl: 
  forall phi theta1 theta2, phi ⋞ theta1 -> phi ⋞ Union_Theta theta1 theta2.
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
  forall phi theta1 theta2, phi ⋞ theta1 -> phi ⋞ Union_Theta theta2 theta1.
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
    unfold fold_subst_eps. exists (SA_Read r).
    + split; [constructor | subst; simpl; reflexivity].
    + inversion H. inversion H0. inversion H1. subst. unfold fold_subst_sa; simpl. apply Ensembles.In_singleton.
  - replace (fold_subst_eps rho (Union_Static_Action eps1 eps2)) with (Union_Static_Action (fold_subst_eps rho eps1) (fold_subst_eps rho eps2)).
    constructor; assumption.
    apply Extensionality_Ensembles;
    unfold Same_set, Included; split; intros x H; unfold Ensembles.In in *.
    + inversion H; subst; inversion H0; unfold fold_subst_eps; exists x0; split.
      * apply Ensembles.Union_introl. destruct H1; subst. assumption.
      * destruct H1; subst. reflexivity. 
      * apply Ensembles.Union_intror. destruct H1; subst. assumption.
      * destruct H1; subst. reflexivity.   
   + inversion H. inversion H0. inversion H1; subst;
       [apply Ensembles.Union_introl | apply Ensembles.Union_intror];
       unfold Ensembles.In; unfold fold_subst_eps; exists x0.
     * split; [assumption | reflexivity].
     * split; [assumption | reflexivity].
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


Lemma EmptyUnionisEmptySet_Name_Left :
  forall acts,
    Union VarId (Empty_set VarId) acts = acts.
Proof.
  intros acts;
  apply Extensionality_Ensembles;
  unfold Same_set, Included;
  split.
  - intros x Hx. unfold In in *. destruct Hx; auto. inversion H.
  - intros x Hx. apply Union_intror. assumption.
Qed. 

Lemma EmptyUnionisEmptySet_Name_Right :
  forall acts,
    Union VarId acts (Empty_set VarId) = acts.
Proof.
  intros acts;
  apply Extensionality_Ensembles;
  unfold Same_set, Included;
  split.
  - intros x Hx. unfold In in *. destruct Hx; auto. inversion H.
  - intros x Hx. apply Union_introl. assumption.
Qed. 

Lemma IncludedRemoveSingleton:
  forall n x rgns,
    n <> x ->
    included (singleton_set n) (Union VarId rgns (singleton_set x)) ->
    included (singleton_set n) rgns.
Proof.
  intros n x rgns H1 H2.
  unfold included, Included, In in *. 
  intro. intro.  destruct (H2 x0); auto.  
  inversion H; subst. 
  contradict H0. intro. inversion H0. 
  apply H1. symmetry. assumption.
Qed.

Lemma IncludedUnion_Name_1:
  forall (a b : Ensemble VarId) rgns,
    included (set_union a b) rgns ->
    included a rgns /\
    included b rgns.
Proof.
  intros.
  split.
  - intro. intro. apply H.
    apply Union_introl. assumption.
  - intro. intro. apply H.
    + apply Union_intror. assumption.
Qed.

Lemma IncludedUnion_Name_5:
  forall (a b c : Ensemble VarId) rgns,
    included (set_union a b)
             (set_union rgns c) ->
    included a (set_union rgns c) /\
    included b (set_union rgns c).
Proof.
  intros.
  split.
  - intro. intro. apply H.
    apply Union_introl. assumption.
  - intro. intro. apply H.
    apply Union_intror. assumption.    
Qed.

Lemma IncludedUnion_Name_4:
  forall (a b c : Ensemble VarId) rgns,
    included (set_union a b) rgns /\
    included (set_union a c) rgns ->
    included (set_union a (set_union c b)) rgns.
Proof.
  intros. 
  intro. intro. unfold In, set_union in *.
  destruct H.
  apply IncludedUnion_Name_1 in H. destruct H.
  apply IncludedUnion_Name_1 in H1. destruct H1.
  repeat destruct H0; [apply H1 | apply H3 | apply H2]; assumption. 
Qed.

Lemma IncludedUnion_Static_Action_4:
  forall (a b : Ensemble StaticAction) (rgns : Ensemble VarId) (x : VarId),
    (free_rgn_vars_in_eps a x -> rgns x) ->
    (free_rgn_vars_in_eps b x -> rgns x) ->                        
    (free_rgn_vars_in_eps (Union_Static_Action a b) x -> rgns x).
Proof.
  intros a b rgns x H1 H2 H3.
  unfold free_rgn_vars_in_eps in *.
  destruct H3 as [sa [H4 H5]].
  destruct H4; [apply H1 | apply H2]; exists x0; auto.
Qed.

Lemma IncludedUnion_Name_6:
  forall (a b: Ensemble VarId) rgns,
    included a rgns /\
    included b rgns ->
    included (set_union a b) rgns.
Proof.
  intros. 
  intro. intro. unfold In, set_union in *.
  destruct H0; destruct H; [apply H | apply H1]; assumption. 
Qed.

Lemma RegionAbsFrv_2:
  forall  x r rgns n,
    included (free_rgn_vars_in_rgn r) (set_union rgns (singleton_set x)) ->
    included (free_rgn_vars_in_rgn (closing_rgn_in_rgn n x r)) rgns.
Proof.
  intros. unfold Region_in_Type in r. 
  dependent induction r; simpl in *; do 2 intro.
  - inversion H0.
  - destruct (RMapProp.F.eq_dec v x); subst.
    + simpl in *. inversion H0.
    + apply IncludedRemoveSingleton in H; auto.
  - inversion H0.
Qed. 



Lemma NoFreeVarsAfterClosingRgn:
  forall n x r,
    ~ free_rgn_vars_in_rgn (closing_rgn_in_rgn n x r) x.
Proof.
  intros n x r.
  unfold Region_in_Type in r. dependent induction r; intro;
  unfold free_rgn_vars_in_rgn, closing_rgn_in_rgn in H.
  - inversion H.
  - destruct (RMapProp.F.eq_dec v x); subst.
    + inversion H.
    + inversion H. apply n0. assumption.
  - inversion H.
Qed.

Lemma NoFreeVarsAfterClosingSa:
 forall n sa x,
   ~ free_rgn_vars_in_sa (closing_rgn_in_sa n x sa) x.
Proof.
  intros n sa x. intro.
  induction sa;
  unfold free_rgn_vars_in_sa, closing_rgn_in_sa in H; 
  eapply NoFreeVarsAfterClosingRgn; eauto.
Qed.




Lemma RegionAbsFrv_1:
   forall effr rgns (x : VarId) n, 
     included (free_rgn_vars_in_eps effr) (set_union rgns (singleton_set x)) ->
     included (free_rgn_vars_in_eps (closing_rgn_in_eps n x effr)) rgns.
Proof.
  intros effr rgns x n H.
  unfold free_rgn_vars_in_eps in *.
  do 2 intro. unfold In in *.
  destruct H0 as [sa [H1 H2]].
  unfold closing_rgn_in_eps in H1.
  destruct H1 as [sa' [H3 H4]].
  rewrite <- H4 in H2. 
  unfold included, Included, In in H.
  destruct (H x0); auto.
  - exists sa'. intuition.
    destruct (RMapProp.F.eq_dec x x0); subst.
    + contradict H2. apply NoFreeVarsAfterClosingSa.
    + induction sa'; unfold Region_in_Type in r; dependent induction r; 
      simpl in *; unfold free_rgn_vars_in_rgn in *;
      try (solve [inversion H2 | destruct  (RMapProp.F.eq_dec v x); subst; [inversion H2 | assumption]]).
  - destruct (RMapProp.F.eq_dec x x0); subst.
    + contradict H2. apply NoFreeVarsAfterClosingSa.
    + exfalso. contradict n0. inversion H0. auto.
Qed.

Lemma RegionAbsFrv_3:
   forall tyr rgns (x : VarId), 
     included (frv tyr) (set_union rgns (singleton_set x)) ->
     included (frv (close_var x tyr)) rgns. 
Proof.
  intros tyr rgns x H.
  unfold close_var.
  generalize 0.
  dependent induction tyr; simpl in *; intro;
  try (solve [intro; intro; inversion H0]).
  - unfold included, Included, In in *. 
    intro. intro.  
    destruct H0.
    + eapply IHtyr1; auto. 
      intro. intro. apply H.
      apply Union_introl. assumption. eassumption.
    + eapply IHtyr2; auto.
      intro. intro. apply H.
      apply Union_intror. assumption. eassumption.
  - apply IncludedUnion_Name_6.
    split.
    + apply IncludedUnion_Name_1 in H. destruct H. clear H0. 
      apply RegionAbsFrv_2; eauto.
    + eapply IHtyr.
      do 2 intro. apply H.
       apply Union_intror. assumption.
  - repeat (apply IncludedUnion_Name_4; split); 
    apply IncludedUnion_Name_6; split;
    try (solve [apply IHtyr1; do 2 intro; apply H; apply Union_introl; assumption]).
    + apply IHtyr3. intro. intro.
      apply H.
      apply Union_intror. apply Union_intror. apply Union_intror. assumption. 
    + apply IHtyr2. intro. intro.
      apply H.
      apply Union_intror. apply Union_intror. apply Union_introl. assumption. 
    + apply IncludedUnion_Name_5 in H; destruct H as [H1  H]. clear H1.
      apply IncludedUnion_Name_5 in H; destruct H as [H  H1]. clear H1.
      apply IncludedUnion_Name_5 in H; destruct H as [H1  H]. clear H1.
      eapply RegionAbsFrv_1; eauto.
    + apply IncludedUnion_Name_5 in H; destruct H as [H1  H]. clear H1.
      apply IncludedUnion_Name_5 in H; destruct H as [H  H1]. clear H1.
      apply IncludedUnion_Name_5 in H; destruct H as [H  H1]. clear H1.
      eapply RegionAbsFrv_1; eauto.
  - apply IncludedUnion_Name_6.
    split.
    + apply IncludedUnion_Name_1 in H. destruct H. clear H0.
      eapply RegionAbsFrv_1; eauto.
    + apply IHtyr.
      do 2 intro.
      apply H. apply Union_intror. assumption. 
Qed.  

Lemma RegionAppFrv_2:
  forall region r x n,
    lc_type_rgn r ->
    free_rgn_vars_in_rgn (opening_rgn_in_rgn n region r) x ->
    free_rgn_vars_in_rgn r x.
Proof.
  intros.
  unfold Region_in_Type in r.
  dependent induction r; simpl in *.
  - inversion H0.
  - assumption.
  - inversion H.
Qed.

Lemma RegionAppFrv_3:
  forall region e x n,
    lc_type_eps e ->
    free_rgn_vars_in_eps (opening_rgn_in_eps n region e) x ->
    free_rgn_vars_in_eps e x.
Proof.
  intros region e x n H1 H2.
  inversion H1; subst.
  unfold free_rgn_vars_in_eps in *.
  destruct H2 as [sa [H3 H4]].
  destruct (H sa).
  exists sa. auto.
Qed.

Lemma RegionAppFrv_1:
  forall tyr rgns w,
    lc_type tyr ->
    included (frv tyr) rgns ->
    included (frv (open (mk_rgn_type w) tyr)) rgns.
Proof.
  intros tyr rgns w Hlc H.
  unfold open.
  generalize 0.
  unfold Region_in_Expr in w; intro.
  dependent induction w; simpl.
  - dependent induction tyr; simpl in *;
    inversion Hlc; subst;
    try (solve [do 2 intro; inversion H | do 2 intro; inversion H0]).
    + apply IncludedUnion_Name_6.
      split; [apply IHtyr1 |  apply IHtyr2]; auto.
      * do 2 intro. apply H; simpl.
        apply Union_introl. assumption.
      * do 2 intro. apply H; simpl.
        apply Union_intror. assumption. 
    + apply IncludedUnion_Name_6.
      split.
      * do 2 intro. apply H; simpl.
        apply Union_introl. unfold In in *. 
        eapply RegionAppFrv_2; eauto.
      * apply IHtyr; auto. do 2 intro. 
        apply H; simpl.
        apply Union_intror. assumption. 
    + apply IncludedUnion_Name_6. 
      split; [apply IHtyr1; auto; do 2 intro; apply H; simpl; apply Union_introl; assumption |].
      apply IncludedUnion_Name_6.
      split; [apply IncludedUnion_Name_6; split | apply IncludedUnion_Name_6; split].
      * do 2 intro. apply H; simpl. 
        apply Union_intror. apply Union_introl. apply Union_introl.
        unfold In in *.
        eapply RegionAppFrv_3; eauto.
      * do 2 intro. apply H; simpl. 
        apply Union_intror. apply Union_introl. apply Union_intror.
        unfold In in *.
        eapply RegionAppFrv_3; eauto.
      * apply IHtyr2; auto; do 2 intro; apply H; simpl. 
        apply Union_intror; apply Union_intror. apply Union_introl. assumption.
      * apply IHtyr3; auto; do 2 intro; apply H; simpl. 
        apply Union_intror; apply Union_intror. apply Union_intror. assumption.
    + apply IncludedUnion_Name_6. 
      split; [| apply IHtyr; auto; do 2 intro; apply H; simpl; apply Union_intror; assumption].
      do 2 intro. apply H; simpl in *.
      apply Union_introl.  unfold In in *.
      eapply RegionAppFrv_3; eauto.
  - dependent induction tyr; simpl;
    inversion Hlc; subst;
    try (solve [do 2 intro; inversion H0]).
    + apply IncludedUnion_Name_6.
      split; [apply IHtyr1 |  apply IHtyr2]; auto.
      * do 2 intro. apply H; simpl.
        apply Union_introl. assumption.
      * do 2 intro. apply H; simpl.
        apply Union_intror. assumption. 
    + apply IncludedUnion_Name_6.
      split.
      * do 2 intro. apply H; simpl.
        apply Union_introl. unfold In in *. 
        eapply RegionAppFrv_2; eauto.
      * apply IHtyr; auto. do 2 intro. 
        apply H; simpl.
        apply Union_intror. assumption. 
    + apply IncludedUnion_Name_6. 
      split; [apply IHtyr1; auto; do 2 intro; apply H; simpl; apply Union_introl; assumption |].
      apply IncludedUnion_Name_6.
      split; [apply IncludedUnion_Name_6; split | apply IncludedUnion_Name_6; split].
      * do 2 intro. apply H; simpl. 
        apply Union_intror. apply Union_introl. apply Union_introl.
        unfold In in *.
        eapply RegionAppFrv_3; eauto.
      * do 2 intro. apply H; simpl. 
        apply Union_intror. apply Union_introl. apply Union_intror.
        unfold In in *.
        eapply RegionAppFrv_3; eauto.
      * apply IHtyr2; auto; do 2 intro; apply H; simpl. 
        apply Union_intror; apply Union_intror. apply Union_introl. assumption.
      * apply IHtyr3; auto; do 2 intro; apply H; simpl. 
        apply Union_intror; apply Union_intror. apply Union_intror. assumption.
    + apply IncludedUnion_Name_6. 
      split; [| apply IHtyr; auto; do 2 intro; apply H; simpl; apply Union_intror; assumption].
      do 2 intro. apply H; simpl in *.
      apply Union_introl.  unfold In in *.
      eapply RegionAppFrv_3; eauto.
Qed.
