From stdpp Require Import strings.
Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.

Require Import theories.Core.ComputedActions.
Require Import theories.Core.DynamicActions.
Require Import theories.Core.StaticActions.
Require Import theories.Core.Regions.
Require Import theories.Typing.TypeSyntax.
Require Export theories.Meta.EffectFreeVarsFacts.
Require Import theories.Meta.RegionSubstitutionFacts.


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

Definition theta_of_dynamic_action (da : DynamicAction) : Theta :=
  match da with
  | DA_Alloc r _ _ => Some (singleton_set (CA_AllocAbs r))
  | DA_Read r l _ => Some (singleton_set (CA_ReadConc r l))
  | DA_Write r l _ => Some (singleton_set (CA_WriteConc r l))
  end.

Fixpoint theta_of_phi (phi : Phi) : Theta :=
  match phi with
  | Phi_Nil => Theta_Empty
  | Phi_Elem da => theta_of_dynamic_action da
  | Phi_Par phi1 phi2 => Union_Theta (theta_of_phi phi1) (theta_of_phi phi2)
  | Phi_Seq phi1 phi2 => Union_Theta (theta_of_phi phi1) (theta_of_phi phi2)
  end.

Definition theta_with_phi_prefixes
    (phi1 phi2 : Phi) (theta : Theta) : Theta :=
  Union_Theta (theta_of_phi phi1) (Union_Theta (theta_of_phi phi2) theta).

Lemma theta_of_dynamic_action_sound :
  forall da,
    Phi_Elem da ⋞ theta_of_dynamic_action da.
Proof.
  intros da.
  destruct da as [r l v | r l v | r l v]; simpl;
    apply PTS_Elem.
  - apply DAT_Alloc_Abs.
    constructor.
  - apply DAT_Read_Conc.
    constructor.
  - apply DAT_Write_Conc.
    constructor.
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

Lemma EmptyTraceIsNil:
  forall phi, phi ⋞ Theta_Empty -> phi_as_list phi = nil.
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
  - inversion H; subst; simpl.
    assert (H_ : phi_as_list phi1 = nil) by (apply IHphi1; assumption).
    assert (H__ : phi_as_list phi2 = nil) by (apply IHphi2; assumption).
    rewrite H_, H__. reflexivity.
  - inversion H; subst; simpl.
    assert (H_ : phi_as_list phi1 = nil) by (apply IHphi1; assumption).
    assert (H__ : phi_as_list phi2 = nil) by (apply IHphi2; assumption).
    rewrite H_, H__. reflexivity.
Qed.

Lemma ReadOnlyPhi_Seq_inv:
  forall phi1 phi2,
    ReadOnlyPhi (Phi_Seq phi1 phi2) ->
    ReadOnlyPhi phi1 /\ ReadOnlyPhi phi2.
Proof.
  intros phi1 phi2 H.
  inversion H; subst; split; assumption.
Qed.

Lemma ReadOnlyPhi_Par_inv:
  forall phi1 phi2,
    ReadOnlyPhi (Phi_Par phi1 phi2) ->
    ReadOnlyPhi phi1 /\ ReadOnlyPhi phi2.
Proof.
  intros phi1 phi2 H.
  inversion H; subst; split; assumption.
Qed.

Lemma EmptySoundReadOnlyPhi:
  forall phi,
    phi ⋞ Theta_Empty ->
    ReadOnlyPhi phi.
Proof.
  induction phi; intros HSound.
  - constructor.
  - exfalso.
    apply EmptyTraceIsNil in HSound.
    simpl in HSound. discriminate.
  - inversion HSound; subst.
    constructor; [apply IHphi1 | apply IHphi2]; assumption.
  - inversion HSound; subst.
    constructor; [apply IHphi1 | apply IHphi2]; assumption.
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

Lemma theta_of_phi_sound :
  forall phi,
    phi ⋞ theta_of_phi phi.
Proof.
  induction phi; simpl.
  - apply PTS_Nil.
  - apply theta_of_dynamic_action_sound.
  - apply PTS_Par.
    + apply Theta_introl.
      exact IHphi1.
    + apply Theta_intror.
      exact IHphi2.
  - apply EnsembleUnionComp; assumption.
Qed.

Lemma theta_with_phi_prefixes_left_sound :
  forall phi1 phi2 theta,
    phi1 ⋞ theta_with_phi_prefixes phi1 phi2 theta.
Proof.
  intros phi1 phi2 theta.
  unfold theta_with_phi_prefixes.
  apply Theta_introl.
  apply theta_of_phi_sound.
Qed.

Lemma theta_with_phi_prefixes_middle_sound :
  forall phi1 phi2 theta,
    phi2 ⋞ theta_with_phi_prefixes phi1 phi2 theta.
Proof.
  intros phi1 phi2 theta.
  unfold theta_with_phi_prefixes.
  apply Theta_intror.
  apply Theta_introl.
  apply theta_of_phi_sound.
Qed.

Lemma theta_with_phi_prefixes_right_sound :
  forall phi1 phi2 phi theta,
    phi ⋞ theta ->
    phi ⋞ theta_with_phi_prefixes phi1 phi2 theta.
Proof.
  intros phi1 phi2 phi theta HSound.
  unfold theta_with_phi_prefixes.
  apply Theta_intror.
  apply Theta_intror.
  exact HSound.
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
| SA_DA_Read :
  forall r l v,
    SA_DA_Soundness (SA_Read (Rgn_Const true true r)) (DA_Read r l v)

| SA_DA_Write :
  forall r l v,
    SA_DA_Soundness (SA_Write (Rgn_Const true true r)) (DA_Write r l v)

| SA_DA_Alloc
  : forall r l v,
    SA_DA_Soundness (SA_Alloc (Rgn_Const true true r)) (DA_Alloc r l v).


Inductive Epsilon_Phi_Soundness :  (Epsilon * Phi) -> Prop :=
| EPS :
  forall st dy,
    (forall da, DA_in_Phi da dy ->
                exists sa, Ensembles.In StaticAction st sa
                           /\ SA_DA_Soundness sa da) ->
    Epsilon_Phi_Soundness (st, dy).

Definition DynamicAction_StaticAction (da : DynamicAction) : StaticAction :=
  match da with
  | DA_Alloc r _ _ => SA_Alloc (Rgn_Const true true r)
  | DA_Read r _ _ => SA_Read (Rgn_Const true true r)
  | DA_Write r _ _ => SA_Write (Rgn_Const true true r)
  end.

Definition DynamicAction_Epsilon (da : DynamicAction) : Epsilon :=
  Singleton_Static_Action (DynamicAction_StaticAction da).

Fixpoint Phi_Static_Effect (phi : Phi) : Epsilon :=
  match phi with
  | Phi_Nil => Empty_Static_Action
  | Phi_Elem da => DynamicAction_Epsilon da
  | Phi_Par phi1 phi2 =>
      Union_Static_Action (Phi_Static_Effect phi1) (Phi_Static_Effect phi2)
  | Phi_Seq phi1 phi2 =>
      Union_Static_Action (Phi_Static_Effect phi1) (Phi_Static_Effect phi2)
  end.

Lemma DynamicAction_StaticAction_sound :
  forall da,
    SA_DA_Soundness (DynamicAction_StaticAction da) da.
Proof.
  intros da.
  destruct da; constructor.
Qed.

Lemma Epsilon_Phi_Soundness_nil :
  forall eps,
    Epsilon_Phi_Soundness (eps, Phi_Nil).
Proof.
  intros eps.
  constructor.
  intros da HIn.
  inversion HIn.
Qed.

Lemma Epsilon_Phi_Soundness_elem :
  forall da,
    Epsilon_Phi_Soundness (DynamicAction_Epsilon da, Phi_Elem da).
Proof.
  intros da.
  constructor.
  intros da' HIn.
  inversion HIn; subst.
  exists (DynamicAction_StaticAction da).
  split.
  - apply Ensembles.In_singleton.
  - apply DynamicAction_StaticAction_sound.
Qed.

Lemma Epsilon_Phi_Soundness_seq :
  forall eps1 eps2 phi1 phi2,
    Epsilon_Phi_Soundness (eps1, phi1) ->
    Epsilon_Phi_Soundness (eps2, phi2) ->
    Epsilon_Phi_Soundness
      (Union_Static_Action eps1 eps2, Phi_Seq phi1 phi2).
Proof.
  intros eps1 eps2 phi1 phi2 H1 H2.
  inversion H1 as [? ? HEps1]; inversion H2 as [? ? HEps2]; subst.
  constructor.
  intros da HIn.
  inversion HIn; subst.
  destruct H3 as [HIn1 | HIn2].
  - destruct (HEps1 da HIn1) as [sa [HInSa HSound]].
    exists sa.
    split; [apply Ensembles.Union_introl; assumption | assumption].
  - destruct (HEps2 da HIn2) as [sa [HInSa HSound]].
    exists sa.
    split; [apply Ensembles.Union_intror; assumption | assumption].
Qed.

Lemma Epsilon_Phi_Soundness_par :
  forall eps1 eps2 phi1 phi2,
    Epsilon_Phi_Soundness (eps1, phi1) ->
    Epsilon_Phi_Soundness (eps2, phi2) ->
    Epsilon_Phi_Soundness
      (Union_Static_Action eps1 eps2, Phi_Par phi1 phi2).
Proof.
  intros eps1 eps2 phi1 phi2 H1 H2.
  inversion H1 as [? ? HEps1]; inversion H2 as [? ? HEps2]; subst.
  constructor.
  intros da HIn.
  inversion HIn; subst.
  destruct H3 as [HIn1 | HIn2].
  - destruct (HEps1 da HIn1) as [sa [HInSa HSound]].
    exists sa.
    split; [apply Ensembles.Union_introl; assumption | assumption].
  - destruct (HEps2 da HIn2) as [sa [HInSa HSound]].
    exists sa.
    split; [apply Ensembles.Union_intror; assumption | assumption].
Qed.

Theorem Phi_Static_Effect_sound :
  forall phi,
    Epsilon_Phi_Soundness (Phi_Static_Effect phi, phi).
Proof.
  induction phi.
  - apply Epsilon_Phi_Soundness_nil.
  - apply Epsilon_Phi_Soundness_elem.
  - simpl. apply Epsilon_Phi_Soundness_par; assumption.
  - simpl. apply Epsilon_Phi_Soundness_seq; assumption.
Qed.

Lemma Epsilon_Phi_Soundness_weaken :
  forall eps1 eps2 phi,
    Included StaticAction eps1 eps2 ->
    Epsilon_Phi_Soundness (eps1, phi) ->
    Epsilon_Phi_Soundness (eps2, phi).
Proof.
  intros eps1 eps2 phi HIncluded HSound.
  inversion HSound as [? ? HEps]; subst.
  constructor.
  intros da HIn.
  destruct (HEps da HIn) as [sa [HInSa HSoundSa]].
  exists sa.
  split; [apply HIncluded; assumption | assumption].
Qed.

Lemma SA_DA_Soundness_static_unique :
  forall sa da,
    SA_DA_Soundness sa da ->
    sa = DynamicAction_StaticAction da.
Proof.
  intros sa da HSound.
  inversion HSound; reflexivity.
Qed.

Theorem Phi_Static_Effect_least :
  forall phi eps,
    Epsilon_Phi_Soundness (eps, phi) ->
    Included StaticAction (Phi_Static_Effect phi) eps.
Proof.
  induction phi; intros eps HSound; simpl; unfold Included; intros sa HIn.
  - inversion HIn.
  - unfold DynamicAction_Epsilon, Singleton_Static_Action in HIn.
    inversion HIn; subst.
    inversion HSound as [? ? HEps]; subst.
    destruct (HEps d (DAP_Trace d)) as [sa' [HInSa HSoundSa]].
    pose proof (SA_DA_Soundness_static_unique sa' d HSoundSa) as HUnique.
    subst sa'.
    exact HInSa.
  - inversion HSound as [? ? HEps]; subst.
    destruct HIn as [sa HInLeft | sa HInRight].
    + eapply IHphi1; [| exact HInLeft].
      constructor.
      intros da HDA.
      apply HEps.
      apply DAP_Par.
      left. exact HDA.
    + eapply IHphi2; [| exact HInRight].
      constructor.
      intros da HDA.
      apply HEps.
      apply DAP_Par.
      right. exact HDA.
  - inversion HSound as [? ? HEps]; subst.
    destruct HIn as [sa HInLeft | sa HInRight].
    + eapply IHphi1; [| exact HInLeft].
      constructor.
      intros da HDA.
      apply HEps.
      apply DAP_Seq.
      left. exact HDA.
    + eapply IHphi2; [| exact HInRight].
      constructor.
      intros da HDA.
      apply HEps.
      apply DAP_Seq.
      right. exact HDA.
Qed.

Theorem Epsilon_Phi_Soundness_of_phi_static_included :
  forall eps phi,
    Included StaticAction (Phi_Static_Effect phi) eps ->
    Epsilon_Phi_Soundness (eps, phi).
Proof.
  intros eps phi HIncluded.
  eapply Epsilon_Phi_Soundness_weaken.
  - exact HIncluded.
  - apply Phi_Static_Effect_sound.
Qed.

Theorem Epsilon_Phi_Soundness_iff_phi_static_included :
  forall eps phi,
    Epsilon_Phi_Soundness (eps, phi) <->
    Included StaticAction (Phi_Static_Effect phi) eps.
Proof.
  intros eps phi.
  split.
  - intros HSound.
    apply Phi_Static_Effect_least.
    exact HSound.
  - intros HIncluded.
    apply Epsilon_Phi_Soundness_of_phi_static_included.
    exact HIncluded.
Qed.

Lemma fold_dist_union :
  forall rho (eff1 eff2 : Epsilon),
    fold_subst_eps rho (Union_Static_Action eff1 eff2) =
    Union_Static_Action (fold_subst_eps rho eff1) (fold_subst_eps rho eff2).
Proof.
  intros rho eff1 eff2.
  unfold fold_subst_eps.
  apply Extensionality_Ensembles.
  unfold Same_set, Included.
  split; intros sa HIn; unfold Ensembles.In in *.
  - destruct HIn as [sa' [HIn HSubst]].
    subst.
    destruct HIn as [sa' HInLeft | sa' HInRight].
    + apply Union_introl.
      exists sa'. split; [assumption | reflexivity].
    + apply Union_intror.
      exists sa'. split; [assumption | reflexivity].
  - destruct HIn as [sa HInLeft | sa HInRight].
    + destruct HInLeft as [sa' [HInLeft HSubst]].
      subst.
      exists sa'. split; [apply Union_introl; assumption | reflexivity].
    + destruct HInRight as [sa' [HInRight HSubst]].
      subst.
      exists sa'. split; [apply Union_intror; assumption | reflexivity].
Qed.

Lemma fold_subst_rgn_mk_rgn_type_find_R :
  forall rho w r,
    find_R w rho = Some r ->
    fold_subst_rgn rho (mk_rgn_type w) = Rgn_Const true true r.
Proof.
  intros rho w r HFind.
  unfold find_R in HFind.
  unfold mk_rgn_type.
  destruct w; simpl in HFind.
  - inversion HFind; subst.
    simpl.
    apply subst_rho_rgn_const.
  - simpl.
    eapply subst_rho_fvar_2; eauto.
  - discriminate.
Qed.

Lemma fold_subst_eps_singleton_alloc_find_R :
  forall rho w r,
    find_R w rho = Some r ->
    Ensembles.In StaticAction
      (fold_subst_eps rho
        (Singleton_Static_Action (SA_Alloc (mk_rgn_type w))))
      (SA_Alloc (Rgn_Const true true r)).
Proof.
  intros rho w r HFind.
  unfold fold_subst_eps.
  exists (SA_Alloc (mk_rgn_type w)).
  split.
  - apply Ensembles.In_singleton.
  - unfold fold_subst_sa.
    f_equal.
    eapply fold_subst_rgn_mk_rgn_type_find_R; eauto.
Qed.

Lemma fold_subst_eps_singleton_read_find_R :
  forall rho w r,
    find_R w rho = Some r ->
    Ensembles.In StaticAction
      (fold_subst_eps rho
        (Singleton_Static_Action (SA_Read (mk_rgn_type w))))
      (SA_Read (Rgn_Const true true r)).
Proof.
  intros rho w r HFind.
  unfold fold_subst_eps.
  exists (SA_Read (mk_rgn_type w)).
  split.
  - apply Ensembles.In_singleton.
  - unfold fold_subst_sa.
    f_equal.
    eapply fold_subst_rgn_mk_rgn_type_find_R; eauto.
Qed.

Lemma fold_subst_eps_singleton_write_find_R :
  forall rho w r,
    find_R w rho = Some r ->
    Ensembles.In StaticAction
      (fold_subst_eps rho
        (Singleton_Static_Action (SA_Write (mk_rgn_type w))))
      (SA_Write (Rgn_Const true true r)).
Proof.
  intros rho w r HFind.
  unfold fold_subst_eps.
  exists (SA_Write (mk_rgn_type w)).
  split.
  - apply Ensembles.In_singleton.
  - unfold fold_subst_sa.
    f_equal.
    eapply fold_subst_rgn_mk_rgn_type_find_R; eauto.
Qed.

Lemma Epsilon_Phi_Soundness_alloc_find_R :
  forall rho w r l v,
    find_R w rho = Some r ->
    Epsilon_Phi_Soundness
      (fold_subst_eps rho
        (Singleton_Static_Action (SA_Alloc (mk_rgn_type w))),
       Phi_Elem (DA_Alloc r l v)).
Proof.
  intros rho w r l v HFind.
  constructor.
  intros da HIn.
  inversion HIn; subst.
  exists (SA_Alloc (Rgn_Const true true r)).
  split.
  - eapply fold_subst_eps_singleton_alloc_find_R; eauto.
  - constructor.
Qed.

Lemma Epsilon_Phi_Soundness_read_find_R :
  forall rho w r l v,
    find_R w rho = Some r ->
    Epsilon_Phi_Soundness
      (fold_subst_eps rho
        (Singleton_Static_Action (SA_Read (mk_rgn_type w))),
       Phi_Elem (DA_Read r l v)).
Proof.
  intros rho w r l v HFind.
  constructor.
  intros da HIn.
  inversion HIn; subst.
  exists (SA_Read (Rgn_Const true true r)).
  split.
  - eapply fold_subst_eps_singleton_read_find_R; eauto.
  - constructor.
Qed.

Lemma Epsilon_Phi_Soundness_write_find_R :
  forall rho w r l v,
    find_R w rho = Some r ->
    Epsilon_Phi_Soundness
      (fold_subst_eps rho
        (Singleton_Static_Action (SA_Write (mk_rgn_type w))),
       Phi_Elem (DA_Write r l v)).
Proof.
  intros rho w r l v HFind.
  constructor.
  intros da HIn.
  inversion HIn; subst.
  exists (SA_Write (Rgn_Const true true r)).
  split.
  - eapply fold_subst_eps_singleton_write_find_R; eauto.
  - constructor.
Qed.


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
