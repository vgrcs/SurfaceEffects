From stdpp Require Import strings.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Ascii.

Require Import theories.BigStep.Core.ComputedActions.
Require Import theories.BigStep.Core.StaticActions.
Require Import theories.BigStep.Core.Regions.
Require Import theories.BigStep.Typing.TypeSyntax.

Lemma EmptyUnionisEmptySet_Name_Left :
  forall acts,
    Union RgnName (Empty_set RgnName) acts = acts.
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
    Union RgnName acts (Empty_set RgnName) = acts.
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
    included (singleton_set n) (Union RgnName rgns (singleton_set x)) ->
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
  forall (a b : Ensemble RgnName) rgns,
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
  forall (a b c : Ensemble RgnName) rgns,
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
  forall (a b c : Ensemble RgnName) rgns,
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
  forall (a b : Ensemble StaticAction) (rgns : Ensemble RgnName) (x : RgnName),
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
  forall (a b: Ensemble RgnName) rgns,
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
  - destruct (Ascii.ascii_dec r x); subst.
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
  - destruct (Ascii.ascii_dec r x); subst.
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
   forall effr rgns (x : RgnName) n, 
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
    destruct (Ascii.ascii_dec x x0); subst.
    + contradict H2. subst.
      apply NoFreeVarsAfterClosingSa.
    + induction sa'; unfold Region_in_Type in r; dependent induction r; 
        simpl in *; unfold free_rgn_vars_in_rgn in *;
        try (solve [inversion H2 | destruct  (Ascii.ascii_dec r x);
                                   subst; [inversion H2 | assumption]]).
  - destruct (Ascii.ascii_dec x x0); subst.
    + contradict H2.
      apply NoFreeVarsAfterClosingSa.
    + exfalso.
      contradict n0. inversion H0. auto.
Qed.

Lemma RegionAbsFrv_3:
   forall tyr rgns (x : RgnName), 
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
