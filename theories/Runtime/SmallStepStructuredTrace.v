From stdpp Require Import gmap.
From stdpp Require Import fin_maps.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Sets.Ensembles.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.TraceSemantics.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepParallelStepPreservation.
Require Import theories.Runtime.SmallStepParallelTraceTyping.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepPreservationTheorems.
Require Import theories.Runtime.SmallStepExplicitStoreBase.
Require Import theories.Runtime.SmallStepExplicitStoreTheorems.
Require Import theories.Runtime.SmallStepTraceSafety.
Require Import theories.Runtime.SmallStepParallelProgress.
Require Import theories.Runtime.SmallStepParallelSafety.
Require Import theories.Runtime.SmallStepSequentialSoundness.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.DynamicActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.EffectFacts.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.TraceFacts.
Require Import theories.Meta.TraceTypingFacts.

Definition label_phi (lbl : Label) : Phi :=
  match lbl with
  | Silent => Phi_Nil
  | Act da => Phi_Elem da
  end.

Definition label_static_effect (lbl : Label) : Epsilon :=
  Phi_Static_Effect (label_phi lbl).

Lemma phi_as_list_label_phi :
  forall label,
    phi_as_list (label_phi label) = label_trace label.
Proof.
  intros [| da]; reflexivity.
Qed.

Lemma label_phi_static_sound :
  forall label,
    Epsilon_Phi_Soundness (label_static_effect label, label_phi label).
Proof.
  intros label.
  unfold label_static_effect.
  apply Phi_Static_Effect_sound.
Qed.

Inductive StepsPhi : State -> Phi -> State -> Prop :=
| StepsPhi_Refl :
    forall state,
      StepsPhi state Phi_Nil state
| StepsPhi_Step :
    forall state label state' phi state'',
      Step state label state' ->
      StepsPhi state' phi state'' ->
      StepsPhi state (Phi_Seq (label_phi label) phi) state''.

Theorem StepsPhi_trace_static_sound :
  forall state phi state',
    StepsPhi state phi state' ->
    Epsilon_Phi_Soundness (Phi_Static_Effect phi, phi).
Proof.
  intros.
  apply Phi_Static_Effect_sound.
Qed.

Lemma StepsPhi_as_steps :
  forall state phi state',
    StepsPhi state phi state' ->
    Steps state (phi_as_list phi) state'.
Proof.
  intros state phi state' HSteps.
  induction HSteps.
  - simpl. constructor.
  - simpl. rewrite phi_as_list_label_phi.
    econstructor; eauto.
Qed.

Lemma steps_as_StepsPhi :
  forall state trace state',
    Steps state trace state' ->
    exists phi,
      StepsPhi state phi state' /\
      phi_as_list phi = trace.
Proof.
  intros state trace state' HSteps.
  induction HSteps as [state | state label state1 trace state2 HStep _ IH].
  - exists Phi_Nil. split; [constructor | reflexivity].
  - destruct IH as (phi & HStepsPhi & HTrace).
    exists (Phi_Seq (label_phi label) phi).
    split.
    + econstructor; eauto.
    + simpl. rewrite phi_as_list_label_phi. now rewrite HTrace.
Qed.

Lemma StepsPhi_trans_exists :
  forall state phi1 state' phi2 state'',
    StepsPhi state phi1 state' ->
    StepsPhi state' phi2 state'' ->
    exists phi,
      StepsPhi state phi state'' /\
      phi_as_list phi = phi_as_list phi1 ++ phi_as_list phi2.
Proof.
  intros state phi1 state' phi2 state'' HSteps1 HSteps2.
  pose proof (StepsPhi_as_steps state phi1 state' HSteps1) as HListSteps1.
  pose proof (StepsPhi_as_steps state' phi2 state'' HSteps2) as HListSteps2.
  destruct
    (steps_as_StepsPhi
      state (phi_as_list phi1 ++ phi_as_list phi2) state'')
    as (phi & HSteps & HTrace).
  - eapply steps_trans; eauto.
  - exists phi. split; assumption.
Qed.

Fixpoint kont_append (k tail : Kont) : Kont :=
  match k with
  | KDone => tail
  | KMuAppFun ea env rho k' =>
      KMuAppFun ea env rho (kont_append k' tail)
  | KMuAppArg env rho f x ec ee k' =>
      KMuAppArg env rho f x ec ee (kont_append k' tail)
  | KRgnApp w rho k' =>
      KRgnApp w rho (kont_append k' tail)
  | KEffAppFun ea env rho k' =>
      KEffAppFun ea env rho (kont_append k' tail)
  | KEffAppArg env rho f x ec ee k' =>
      KEffAppArg env rho f x ec ee (kont_append k' tail)
  | KPairParEff1 ef1 ea1 ef2 ea2 env rho k' =>
      KPairParEff1 ef1 ea1 ef2 ea2 env rho (kont_append k' tail)
  | KPairParEff2 ef1 ea1 ef2 ea2 env rho theta k' =>
      KPairParEff2 ef1 ea1 ef2 ea2 env rho theta (kont_append k' tail)
  | KPairParMu1 ef2 ea2 env rho k' =>
      KPairParMu1 ef2 ea2 env rho (kont_append k' tail)
  | KPairParMu2 v k' =>
      KPairParMu2 v (kont_append k' tail)
  | KCond et ef env rho k' =>
      KCond et ef env rho (kont_append k' tail)
  | KRef w rho k' =>
      KRef w rho (kont_append k' tail)
  | KDeRef w rho k' =>
      KDeRef w rho (kont_append k' tail)
  | KAssignLoc w ev env rho k' =>
      KAssignLoc w ev env rho (kont_append k' tail)
  | KAssignVal w l rho k' =>
      KAssignVal w l rho (kont_append k' tail)
  | KPlusL e2 env rho k' =>
      KPlusL e2 env rho (kont_append k' tail)
  | KPlusR n k' =>
      KPlusR n (kont_append k' tail)
  | KMinusL e2 env rho k' =>
      KMinusL e2 env rho (kont_append k' tail)
  | KMinusR n k' =>
      KMinusR n (kont_append k' tail)
  | KTimesL e2 env rho k' =>
      KTimesL e2 env rho (kont_append k' tail)
  | KTimesR n k' =>
      KTimesR n (kont_append k' tail)
  | KEqL e2 env rho k' =>
      KEqL e2 env rho (kont_append k' tail)
  | KEqR n k' =>
      KEqR n (kont_append k' tail)
  | KReadConc k' =>
      KReadConc (kont_append k' tail)
  | KWriteConc k' =>
      KWriteConc (kont_append k' tail)
  | KConcatL e2 env rho k' =>
      KConcatL e2 env rho (kont_append k' tail)
  | KConcatR theta k' =>
      KConcatR theta (kont_append k' tail)
  end.

Definition state_append_kont (state : State) (tail : Kont) : State :=
  match state with
  | StEval heap env rho e k =>
      StEval heap env rho e (kont_append k tail)
  | StReturn heap v k =>
      StReturn heap v (kont_append k tail)
  | StDone heap v =>
      StReturn heap v tail
  end.

Fixpoint kont_size (k : Kont) : nat :=
  match k with
  | KDone => 0
  | KMuAppFun _ _ _ k' => S (kont_size k')
  | KMuAppArg _ _ _ _ _ _ k' => S (kont_size k')
  | KRgnApp _ _ k' => S (kont_size k')
  | KEffAppFun _ _ _ k' => S (kont_size k')
  | KEffAppArg _ _ _ _ _ _ k' => S (kont_size k')
  | KPairParEff1 _ _ _ _ _ _ k' => S (kont_size k')
  | KPairParEff2 _ _ _ _ _ _ _ k' => S (kont_size k')
  | KPairParMu1 _ _ _ _ k' => S (kont_size k')
  | KPairParMu2 _ k' => S (kont_size k')
  | KCond _ _ _ _ k' => S (kont_size k')
  | KRef _ _ k' => S (kont_size k')
  | KDeRef _ _ k' => S (kont_size k')
  | KAssignLoc _ _ _ _ k' => S (kont_size k')
  | KAssignVal _ _ _ k' => S (kont_size k')
  | KPlusL _ _ _ k' => S (kont_size k')
  | KPlusR _ k' => S (kont_size k')
  | KMinusL _ _ _ k' => S (kont_size k')
  | KMinusR _ k' => S (kont_size k')
  | KTimesL _ _ _ k' => S (kont_size k')
  | KTimesR _ k' => S (kont_size k')
  | KEqL _ _ _ k' => S (kont_size k')
  | KEqR _ k' => S (kont_size k')
  | KReadConc k' => S (kont_size k')
  | KWriteConc k' => S (kont_size k')
  | KConcatL _ _ _ k' => S (kont_size k')
  | KConcatR _ k' => S (kont_size k')
  end.

Lemma StepsPhi_from_done_inv :
  forall heap v phi state',
    StepsPhi (StDone heap v) phi state' ->
    phi = Phi_Nil /\ state' = StDone heap v.
Proof.
  intros heap v phi state' HSteps.
  inversion HSteps; subst.
  - split; reflexivity.
  - exfalso.
    eapply done_no_step; eauto.
Qed.

Lemma Step_to_done_inv :
  forall state label heap v,
    Step state label (StDone heap v) ->
    state = StReturn heap v KDone /\ label = Silent.
Proof.
  intros state label heap v HStep.
  inversion HStep; subst; split; reflexivity.
Qed.

Lemma Step_return_kont_decreases :
  forall heap v k label heap' v' k',
    Step (StReturn heap v k) label (StReturn heap' v' k') ->
    kont_size k' < kont_size k.
Proof.
  intros heap v k label heap' v' k' HStep.
  inversion HStep; subst; simpl; lia.
Qed.

Lemma Step_return_self_absurd :
  forall heap v k label,
    ~ Step (StReturn heap v k) label (StReturn heap v k).
Proof.
  intros heap v k label HStep.
  pose proof
    (Step_return_kont_decreases heap v k label heap v k HStep)
    as HDecrease.
  lia.
Qed.

Lemma Step_append_kont_or_done :
  forall state label state' tail,
    Step state label state' ->
    (exists heap v,
      state = StReturn heap v KDone /\
      label = Silent /\
      state' = StDone heap v) \/
    Step
      (state_append_kont state tail)
      label
      (state_append_kont state' tail).
Proof.
  intros state label state' tail HStep.
  inversion HStep; subst; simpl;
    try (right; econstructor; eauto; fail).
  left.
  exists heap, v.
  repeat split; reflexivity.
Qed.

Theorem StepsPhi_append_kont_terminal_continue :
  forall state phi heap' v tail state_next,
    StepsPhi state phi (StDone heap' v) ->
    Step (StReturn heap' v tail) Silent state_next ->
    ~ Terminal state ->
    StepsPhi (state_append_kont state tail) phi state_next.
Proof.
  intros state phi heap' v tail state_next HSteps HFinal HNotTerminal.
  dependent induction HSteps.
  - exfalso.
    apply HNotTerminal.
    constructor.
  - destruct (Step_append_kont_or_done state label state' tail H)
      as [(heap_done & v_done & HState & HLabel & HState') | HStepAppend].
    + subst.
      destruct (StepsPhi_from_done_inv _ _ _ _ HSteps) as (-> & HDone).
      inversion HDone; subst.
      simpl.
      change (Phi_Seq Phi_Nil Phi_Nil)
        with (Phi_Seq (label_phi Silent) Phi_Nil).
      eapply StepsPhi_Step.
      * exact HFinal.
      * constructor.
    + eapply StepsPhi_Step.
      * exact HStepAppend.
      * eapply (IHHSteps heap' v).
        -- reflexivity.
        -- exact HFinal.
        -- intros HTerminal.
           inversion HTerminal; subst.
           destruct (Step_to_done_inv state label heap v0 H)
             as (HState & HLabel).
           subst.
           simpl in HStepAppend.
           eapply Step_return_self_absurd; eauto.
Qed.

Theorem StepsPhi_initial_terminal_continue :
  forall heap env rho e phi heap' v tail state_next,
    StepsPhi (initial_state heap env rho e) phi (StDone heap' v) ->
    Step (StReturn heap' v tail) Silent state_next ->
    StepsPhi (StEval heap env rho e tail) phi state_next.
Proof.
  intros heap env rho e phi heap' v tail state_next HSteps HFinal.
  unfold initial_state in HSteps.
  change (StEval heap env rho e tail)
    with (state_append_kont (StEval heap env rho e KDone) tail).
  eapply StepsPhi_append_kont_terminal_continue; eauto.
  intros HTerminal.
  inversion HTerminal.
Qed.

Lemma structured_phi_heap_steps_trans :
  forall phi1 heap1 phi2 heap2 phi3 heap3,
    (phi1, heap1) ==>* (phi2, heap2) ->
    (phi2, heap2) ==>* (phi3, heap3) ->
    (phi1, heap1) ==>* (phi3, heap3).
Proof.
  intros phi1 heap1 phi2 heap2 phi3 heap3 [n1 H1] [n2 H2].
  exists (1 + n1 + n2)%nat.
  eapply PHT_Trans; eauto.
Qed.

Lemma structured_phi_seq_lift_left :
  forall phi1 heap phi1' heap' phi2,
    (phi1, heap) ==>* (phi1', heap') ->
    (Phi_Seq phi1 phi2, heap) ==>* (Phi_Seq phi1' phi2, heap').
Proof.
  intros phi1 heap phi1' heap' phi2 [n HSteps].
  dependent induction HSteps.
  - exists 0. constructor.
  - exists 1. constructor. now constructor.
  - eapply structured_phi_heap_steps_trans; eauto.
Qed.

Lemma structured_phi_seq_lift_right :
  forall phi2 heap phi2' heap',
    (phi2, heap) ==>* (phi2', heap') ->
    (Phi_Seq Phi_Nil phi2, heap) ==>* (Phi_Seq Phi_Nil phi2', heap').
Proof.
  intros phi2 heap phi2' heap' [n HSteps].
  dependent induction HSteps.
  - exists 0. constructor.
  - exists 1. constructor. now constructor.
  - eapply structured_phi_heap_steps_trans; eauto.
Qed.

Lemma structured_phi_seq_steps :
  forall phi1 heap heap' phi2 heap'',
    (phi1, heap) ==>* (Phi_Nil, heap') ->
    (phi2, heap') ==>* (Phi_Nil, heap'') ->
    (Phi_Seq phi1 phi2, heap) ==>* (Phi_Nil, heap'').
Proof.
  intros phi1 heap heap' phi2 heap'' H1 H2.
  eapply structured_phi_heap_steps_trans.
  - eapply structured_phi_seq_lift_left; eauto.
  - eapply structured_phi_heap_steps_trans.
    + eapply structured_phi_seq_lift_right; eauto.
    + exists 1. constructor. constructor.
Qed.

Lemma structured_phi_par_lift_left :
  forall phi1 heap phi1' heap' phi2,
    (phi1, heap) ==>* (phi1', heap') ->
    (Phi_Par phi1 phi2, heap) ==>* (Phi_Par phi1' phi2, heap').
Proof.
  intros phi1 heap phi1' heap' phi2 [n HSteps].
  dependent induction HSteps.
  - exists 0. constructor.
  - exists 1. constructor. now constructor.
  - eapply structured_phi_heap_steps_trans; eauto.
Qed.

Lemma structured_phi_par_lift_right :
  forall phi1 phi2 heap phi2' heap',
    (phi2, heap) ==>* (phi2', heap') ->
    (Phi_Par phi1 phi2, heap) ==>* (Phi_Par phi1 phi2', heap').
Proof.
  intros phi1 phi2 heap phi2' heap' [n HSteps].
  dependent induction HSteps.
  - exists 0. constructor.
  - exists 1. constructor. now constructor.
  - eapply structured_phi_heap_steps_trans; eauto.
Qed.

Lemma structured_phi_par_steps :
  forall phi1 heap heap' phi2 heap'',
    (phi1, heap) ==>* (Phi_Nil, heap') ->
    (phi2, heap') ==>* (Phi_Nil, heap'') ->
    (Phi_Par phi1 phi2, heap) ==>* (Phi_Nil, heap'').
Proof.
  intros phi1 heap heap' phi2 heap'' H1 H2.
  eapply structured_phi_heap_steps_trans.
  - eapply structured_phi_par_lift_left; eauto.
  - eapply structured_phi_heap_steps_trans.
    + eapply structured_phi_par_lift_right; eauto.
    + exists 1. constructor. constructor.
Qed.

Inductive ParSeqNilLeftRel : Phi -> Phi -> Prop :=
| ParSeqNilLeftRel_Par :
    forall phi_left phi_right,
      ParSeqNilLeftRel
        (Phi_Par phi_left phi_right)
        (Phi_Par (Phi_Seq Phi_Nil phi_left) phi_right)
| ParSeqNilLeftRel_Nil :
      ParSeqNilLeftRel Phi_Nil Phi_Nil.

Lemma ParSeqNilLeftRel_step :
  forall phi phi_aug heap phi' heap',
    ParSeqNilLeftRel phi phi_aug ->
    (phi, heap) ===> (phi', heap') ->
    exists phi_aug',
      (phi_aug, heap) ==>* (phi_aug', heap') /\
      ParSeqNilLeftRel phi' phi_aug'.
Proof.
  intros phi phi_aug heap phi' heap' HRel HStep.
  inversion HRel; subst.
  - inversion HStep; subst.
    + exists (Phi_Par (Phi_Seq Phi_Nil phi1') phi_right).
      split.
      * exists 1. constructor.
        apply PHS_Par_1.
        now apply PHS_Seq_2.
      * constructor.
    + exists (Phi_Par (Phi_Seq Phi_Nil phi_left) phi2').
      split.
      * exists 1. constructor.
        now apply PHS_Par_2.
      * constructor.
    + exists Phi_Nil.
      split.
      * eapply structured_phi_heap_steps_trans with
          (phi2 := Phi_Par Phi_Nil Phi_Nil).
        { exists 1. constructor.
          apply PHS_Par_1.
          apply PHS_Seq_3. }
        { exists 1. constructor.
          apply PHS_Par_3. }
      * constructor.
  - inversion HStep.
Qed.

Lemma ParSeqNilLeftRel_steps :
  forall phi phi_aug heap phi' heap',
    ParSeqNilLeftRel phi phi_aug ->
    (phi, heap) ==>* (phi', heap') ->
    exists phi_aug',
      (phi_aug, heap) ==>* (phi_aug', heap') /\
      ParSeqNilLeftRel phi' phi_aug'.
Proof.
  intros phi phi_aug heap phi' heap' HRel [n HSteps].
  revert phi_aug HRel.
  dependent induction HSteps; intros phi_aug HRel.
  - exists phi_aug. split; [exists 0; constructor | exact HRel].
  - eapply ParSeqNilLeftRel_step; eauto.
  - destruct
      (IHHSteps1 phi heap phi'0 heap'0 n' eq_refl eq_refl
        phi_aug HRel)
      as (phi_mid_aug & HAug1 & HRelMid).
    destruct
      (IHHSteps2 phi'0 heap'0 phi' heap' n'' eq_refl eq_refl
        phi_mid_aug HRelMid)
      as (phi_final_aug & HAug2 & HRelFinal).
    exists phi_final_aug. split; [| exact HRelFinal].
    eapply structured_phi_heap_steps_trans; eauto.
Qed.

Lemma structured_phi_par_seq_nil_left :
  forall phi_left phi_right heap heap',
    (Phi_Par phi_left phi_right, heap) ==>* (Phi_Nil, heap') ->
    (Phi_Par (Phi_Seq Phi_Nil phi_left) phi_right, heap)
      ==>* (Phi_Nil, heap').
Proof.
  intros phi_left phi_right heap heap' HSteps.
  destruct
    (ParSeqNilLeftRel_steps
      (Phi_Par phi_left phi_right)
      (Phi_Par (Phi_Seq Phi_Nil phi_left) phi_right)
      heap Phi_Nil heap')
    as (phi_aug' & HAug & HRelAug);
    [constructor | exact HSteps |].
  inversion HRelAug; subst.
  exact HAug.
Qed.

Inductive ParSeqNilRightRel : Phi -> Phi -> Prop :=
| ParSeqNilRightRel_Par :
    forall phi_left phi_right,
      ParSeqNilRightRel
        (Phi_Par phi_left phi_right)
        (Phi_Par phi_left (Phi_Seq Phi_Nil phi_right))
| ParSeqNilRightRel_Nil :
      ParSeqNilRightRel Phi_Nil Phi_Nil.

Lemma ParSeqNilRightRel_step :
  forall phi phi_aug heap phi' heap',
    ParSeqNilRightRel phi phi_aug ->
    (phi, heap) ===> (phi', heap') ->
    exists phi_aug',
      (phi_aug, heap) ==>* (phi_aug', heap') /\
      ParSeqNilRightRel phi' phi_aug'.
Proof.
  intros phi phi_aug heap phi' heap' HRel HStep.
  inversion HRel; subst.
  - inversion HStep; subst.
    + exists (Phi_Par phi1' (Phi_Seq Phi_Nil phi_right)).
      split.
      * exists 1. constructor.
        now apply PHS_Par_1.
      * constructor.
    + exists (Phi_Par phi_left (Phi_Seq Phi_Nil phi2')).
      split.
      * exists 1. constructor.
        apply PHS_Par_2.
        now apply PHS_Seq_2.
      * constructor.
    + exists Phi_Nil.
      split.
      * eapply structured_phi_heap_steps_trans with
          (phi2 := Phi_Par Phi_Nil Phi_Nil).
        { exists 1. constructor.
          apply PHS_Par_2.
          apply PHS_Seq_3. }
        { exists 1. constructor.
          apply PHS_Par_3. }
      * constructor.
  - inversion HStep.
Qed.

Lemma ParSeqNilRightRel_steps :
  forall phi phi_aug heap phi' heap',
    ParSeqNilRightRel phi phi_aug ->
    (phi, heap) ==>* (phi', heap') ->
    exists phi_aug',
      (phi_aug, heap) ==>* (phi_aug', heap') /\
      ParSeqNilRightRel phi' phi_aug'.
Proof.
  intros phi phi_aug heap phi' heap' HRel [n HSteps].
  revert phi_aug HRel.
  dependent induction HSteps; intros phi_aug HRel.
  - exists phi_aug. split; [exists 0; constructor | exact HRel].
  - eapply ParSeqNilRightRel_step; eauto.
  - destruct
      (IHHSteps1 phi heap phi'0 heap'0 n' eq_refl eq_refl
        phi_aug HRel)
      as (phi_mid_aug & HAug1 & HRelMid).
    destruct
      (IHHSteps2 phi'0 heap'0 phi' heap' n'' eq_refl eq_refl
        phi_mid_aug HRelMid)
      as (phi_final_aug & HAug2 & HRelFinal).
    exists phi_final_aug. split; [| exact HRelFinal].
    eapply structured_phi_heap_steps_trans; eauto.
Qed.

Lemma structured_phi_par_seq_nil_right :
  forall phi_left phi_right heap heap',
    (Phi_Par phi_left phi_right, heap) ==>* (Phi_Nil, heap') ->
    (Phi_Par phi_left (Phi_Seq Phi_Nil phi_right), heap)
      ==>* (Phi_Nil, heap').
Proof.
  intros phi_left phi_right heap heap' HSteps.
  destruct
    (ParSeqNilRightRel_steps
      (Phi_Par phi_left phi_right)
      (Phi_Par phi_left (Phi_Seq Phi_Nil phi_right))
      heap Phi_Nil heap')
    as (phi_aug' & HAug & HRelAug);
    [constructor | exact HSteps |].
  inversion HRelAug; subst.
  exact HAug.
Qed.

Lemma structured_phi_par_prefix_left :
  forall prefix phi_left phi_right heap heap' heap'',
    (prefix, heap) ==>* (Phi_Nil, heap') ->
    (Phi_Par phi_left phi_right, heap') ==>* (Phi_Nil, heap'') ->
    (Phi_Par (Phi_Seq prefix phi_left) phi_right, heap)
      ==>* (Phi_Nil, heap'').
Proof.
  intros prefix phi_left phi_right heap heap' heap'' HPrefix HRest.
  eapply structured_phi_heap_steps_trans.
  - eapply structured_phi_par_lift_left.
    eapply structured_phi_seq_lift_left; eauto.
  - now apply structured_phi_par_seq_nil_left.
Qed.

Lemma structured_phi_par_prefix_right :
  forall phi_left prefix phi_right heap heap' heap'',
    (prefix, heap) ==>* (Phi_Nil, heap') ->
    (Phi_Par phi_left phi_right, heap') ==>* (Phi_Nil, heap'') ->
    (Phi_Par phi_left (Phi_Seq prefix phi_right), heap)
      ==>* (Phi_Nil, heap'').
Proof.
  intros phi_left prefix phi_right heap heap' heap'' HPrefix HRest.
  eapply structured_phi_heap_steps_trans.
  - eapply structured_phi_par_lift_right.
    eapply structured_phi_seq_lift_left; eauto.
  - now apply structured_phi_par_seq_nil_right.
Qed.

Lemma step_label_phi_replays_heap :
  forall state label state',
    Step state label state' ->
    (label_phi label, state_heap state) ==>* (Phi_Nil, state_heap state').
Proof.
  intros state label state' HStep.
  inversion HStep; subst; simpl; try (exists 0; constructor).
  - exists 1. constructor. constructor.
  - exists 1. constructor. now constructor.
  - exists 1. constructor. now constructor.
Qed.

Theorem StepsPhi_replays_heap :
  forall state phi state',
    StepsPhi state phi state' ->
    (phi, state_heap state) ==>* (Phi_Nil, state_heap state').
Proof.
  intros state phi state' HSteps.
  induction HSteps.
  - exists 0. constructor.
  - eapply structured_phi_seq_steps.
    + eapply step_label_phi_replays_heap; eauto.
    + exact IHHSteps.
Qed.

Theorem StepsPhi_readonly_preserves_heap :
  forall state phi state',
    StepsPhi state phi state' ->
    ReadOnlyPhi phi ->
    state_heap state = state_heap state'.
Proof.
  intros state phi state' HSteps HReadOnly.
  pose proof (StepsPhi_replays_heap _ _ _ HSteps) as HReplay.
  pose proof
    (ReadOnlyPhi_Heap_Steps_preserves_heap
      phi (state_heap state) Phi_Nil (state_heap state')
      HReplay HReadOnly)
    as HHeap.
  unfold equiv, heap_equiv in HHeap.
  exact HHeap.
Qed.

Theorem StepsPhi_readonly_static_effect_preserves_heap :
  forall state phi state',
    StepsPhi state phi state' ->
    ReadOnlyStatic (Phi_Static_Effect phi) ->
    state_heap state = state_heap state'.
Proof.
  intros state phi state' HSteps HReadOnlyStatic.
  eapply StepsPhi_readonly_preserves_heap; eauto.
  eapply ReadOnlyStaticImpliesReadOnlyPhi.
  - exact HReadOnlyStatic.
  - eapply StepsPhi_trace_static_sound; eauto.
Qed.

Lemma WTStateRuntimeHeapShapeAt_step_label_phi_typed :
  forall state tin stty label state' tout stty',
    WTStateRuntimeHeapShapeAt state tin stty ->
    Step state label state' ->
    WTStateRuntimeHeapShapeAt state' tout stty' ->
    TcPhi stty' (label_phi label).
Proof.
  intros state tin stty label state' tout stty' HWT HStep HWT'.
  destruct label as [| da].
  - apply TcPhi_nil.
  - pose proof
      (WTStateRuntimeHeapShapeAt_step_label_typed
        state tin stty (Act da) state' tout stty' HWT HStep HWT')
      as HTcLabel.
    simpl in HTcLabel.
    eapply TcPhi_seq_inv_l; eauto.
Qed.

Theorem WTStateRuntimeHeapShapeAt_steps_phi_trace_typed :
  forall state tout stty phi state',
    WTStateRuntimeHeapShapeAt state tout stty ->
    StepsPhi state phi state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      StoreExtends stty stty' /\
      TcPhi stty' phi.
Proof.
  intros state tout stty phi state' HWT HSteps.
  revert tout stty HWT.
  induction HSteps as [state | state label state1 phi state2 HStep HSteps IH];
    intros tout stty HWT.
  - exists stty.
    split; [exact HWT |].
    split; [apply StoreExtends_refl | apply TcPhi_nil].
  - destruct
      (WTStateRuntimeHeapShapeAt_step_preservation
        state tout stty label state1 HWT HStep)
      as (stty1 & HWT1 & _ & _ & HExt1).
    destruct (IH tout stty1 HWT1) as (stty2 & HWT2 & HExt2 & HTcPhi).
    pose proof
      (WTStateRuntimeHeapShapeAt_step_label_phi_typed
        state tout stty label state1 tout stty1 HWT HStep HWT1)
      as HTcLabel1.
    pose proof
      (TcPhi_weaken stty1 stty2 (label_phi label) HExt2 HTcLabel1)
      as HTcLabel2.
    exists stty2.
    split; [exact HWT2 |].
    split; [eapply StoreExtends_trans; eauto |].
    apply TcPhi_seq; assumption.
Qed.

Theorem WTStateRuntimeHeapShapeAt_steps_phi_safety_with_trace :
  PairParCheckDecidable ->
  forall state tout stty phi state',
    WTStateRuntimeHeapShapeAt state tout stty ->
    StepsPhi state phi state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      StoreExtends stty stty' /\
      NotStuck state' /\
      TcPhi stty' phi.
Proof.
  intros HDec state tout stty phi state' HWT HSteps.
  destruct
    (WTStateRuntimeHeapShapeAt_steps_phi_trace_typed
      state tout stty phi state' HWT HSteps)
    as (stty' & HWT' & HExt & HTcPhi).
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
  split; [exact HNotStuck' | exact HTcPhi].
Qed.

Definition StatePhiTraceSafeAt (state : State) (tout : Tau) (stty : Sigma) : Prop :=
  forall phi state',
    StepsPhi state phi state' ->
    exists stty',
      WTStateRuntimeHeapShapeAt state' tout stty' /\
      StoreExtends stty stty' /\
      NotStuck state' /\
      TcPhi stty' phi.

Theorem WTStateRuntimeHeapShapeAt_phi_trace_safe_typed :
  PairParCheckDecidable ->
  forall state tout stty,
    WTStateRuntimeHeapShapeAt state tout stty ->
    StatePhiTraceSafeAt state tout stty.
Proof.
  intros HDec state tout stty HWT phi state' HSteps.
  eapply WTStateRuntimeHeapShapeAt_steps_phi_safety_with_trace; eauto.
Qed.

Inductive PairParStepsPhi :
  PairParState -> Phi -> Phi -> Phi -> PairParState -> Prop :=
| PairParStepsPhi_Refl :
    forall state,
      PairParStepsPhi state Phi_Nil Phi_Nil Phi_Nil state
| PairParStepsPhi_State :
    forall state label state' phi_state phi_left phi_right state'',
      Step state label state' ->
      PairParStepsPhi
        (PPS_State state') phi_state phi_left phi_right state'' ->
      PairParStepsPhi
        (PPS_State state)
        (Phi_Seq (label_phi label) phi_state)
        phi_left
        phi_right
        state''
| PairParStepsPhi_Left :
    forall left right k label left' phi_state phi_left phi_right state'',
      Step left label left' ->
      PairParStepsPhi
        (PPS_Run left' (with_state_heap (state_heap left') right) k)
        phi_state
        phi_left
        phi_right
        state'' ->
      PairParStepsPhi
        (PPS_Run left right k)
        phi_state
        (Phi_Seq (label_phi label) phi_left)
        phi_right
        state''
| PairParStepsPhi_Right :
    forall left right k label right' phi_state phi_left phi_right state'',
      Step right label right' ->
      PairParStepsPhi
        (PPS_Run (with_state_heap (state_heap right') left) right' k)
        phi_state
        phi_left
        phi_right
        state'' ->
      PairParStepsPhi
        (PPS_Run left right k)
        phi_state
        phi_left
        (Phi_Seq (label_phi label) phi_right)
        state''
| PairParStepsPhi_Done :
    forall heap v1 v2 k phi_state phi_left phi_right state'',
      PairParStepsPhi
        (PPS_State (StReturn heap (Pair (v1, v2)) k))
        phi_state
        phi_left
        phi_right
        state'' ->
      PairParStepsPhi
        (PPS_Run (StDone heap v1) (StDone heap v2) k)
        phi_state
        phi_left
        phi_right
        state''.

Definition pairpar_state_heap (state : PairParState) : Heap :=
  match state with
  | PPS_State state => state_heap state
  | PPS_Run left_state _ _ => state_heap left_state
  end.

Definition pairpar_runtime_phi
    (state : PairParState) (phi_state phi_left phi_right : Phi) : Phi :=
  match state with
  | PPS_State _ => phi_state
  | PPS_Run _ _ _ => Phi_Seq (Phi_Par phi_left phi_right) phi_state
  end.

Lemma PairParStepsPhi_state_branches_nil :
  forall state phi_state phi_left phi_right state',
    PairParStepsPhi
      (PPS_State state) phi_state phi_left phi_right state' ->
    phi_left = Phi_Nil /\ phi_right = Phi_Nil.
Proof.
  intros state phi_state phi_left phi_right state' HSteps.
  dependent induction HSteps.
  - split; reflexivity.
  - exact (IHHSteps state' eq_refl).
Qed.

Lemma PairParStepsPhi_state_replays_heap :
  forall state phi_state phi_left phi_right state',
    PairParStepsPhi
      (PPS_State state) phi_state phi_left phi_right state' ->
    (phi_state, state_heap state) ==>* (Phi_Nil, pairpar_state_heap state').
Proof.
  intros state phi_state phi_left phi_right state' HSteps.
  dependent induction HSteps.
  - simpl. exists 0. constructor.
  - simpl.
    eapply structured_phi_seq_steps.
    + eapply step_label_phi_replays_heap; eauto.
    + exact (IHHSteps state' eq_refl).
Qed.

Theorem PairParStepsPhi_run_split_replays_heap :
  forall left_state right_state k phi_state phi_left phi_right state',
    state_heap left_state = state_heap right_state ->
    PairParStepsPhi
      (PPS_Run left_state right_state k)
      phi_state phi_left phi_right state' ->
    exists heap_mid,
      (Phi_Par phi_left phi_right, state_heap left_state)
        ==>* (Phi_Nil, heap_mid) /\
      (phi_state, heap_mid)
        ==>* (Phi_Nil, pairpar_state_heap state').
Proof.
  intros left_state right_state k phi_state phi_left phi_right state'
    HAgree HSteps.
  remember (PPS_Run left_state right_state k) as run_state eqn:HRun.
  revert left_state right_state k HAgree HRun.
  induction HSteps;
    intros left_state0 right_state0 k0 HAgree HRun;
    inversion HRun; subst.
  - simpl.
    exists (state_heap left_state0). split.
    + eapply structured_phi_par_steps.
      * exists 0. constructor.
      * exists 0. constructor.
    + exists 0. constructor.
  - destruct
      (IHHSteps left' (with_state_heap (state_heap left') right_state0) k0)
      as (heap_mid & HParRest & HStateRest).
    + rewrite state_heap_with_state_heap. reflexivity.
    + reflexivity.
    + exists heap_mid. split.
      * eapply structured_phi_par_prefix_left.
        -- eapply step_label_phi_replays_heap; eauto.
        -- exact HParRest.
      * exact HStateRest.
  - destruct
      (IHHSteps (with_state_heap (state_heap right') left_state0) right' k0)
      as (heap_mid & HParRest & HStateRest).
    + rewrite state_heap_with_state_heap. reflexivity.
    + reflexivity.
    + exists heap_mid. split.
      * eapply structured_phi_par_prefix_right.
        -- rewrite HAgree.
           eapply step_label_phi_replays_heap; eauto.
        -- rewrite state_heap_with_state_heap in HParRest.
           exact HParRest.
      * exact HStateRest.
  - destruct
      (PairParStepsPhi_state_branches_nil
        (StReturn heap (Pair (v1, v2)) k0)
        phi_state phi_left phi_right state'' HSteps)
      as (HLeftNil & HRightNil).
    subst.
    exists heap. split.
    + simpl.
      eapply structured_phi_par_steps.
      * exists 0. constructor.
      * exists 0. constructor.
    + exact
        (PairParStepsPhi_state_replays_heap
          (StReturn heap (Pair (v1, v2)) k0)
          phi_state Phi_Nil Phi_Nil state'' HSteps).
Qed.

Theorem PairParStepsPhi_run_replays_heap :
  forall left_state right_state k phi_state phi_left phi_right state',
    state_heap left_state = state_heap right_state ->
    PairParStepsPhi
      (PPS_Run left_state right_state k)
      phi_state phi_left phi_right state' ->
    (Phi_Seq (Phi_Par phi_left phi_right) phi_state, state_heap left_state)
      ==>* (Phi_Nil, pairpar_state_heap state').
Proof.
  intros left_state right_state k phi_state phi_left phi_right state'
    HAgree HSteps.
  destruct
    (PairParStepsPhi_run_split_replays_heap
      left_state right_state k phi_state phi_left phi_right state'
      HAgree HSteps)
    as (heap_mid & HPar & HState).
  eapply structured_phi_seq_steps; eauto.
Qed.

Theorem PairParStepsPhi_checked_replays_heap :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_state phi_left phi_right state',
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi_state phi_left phi_right state' ->
    (Phi_Seq (Phi_Par phi_left phi_right) phi_state, heap)
      ==>* (Phi_Nil, pairpar_state_heap state').
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_state phi_left phi_right state' HSteps.
  unfold pairpar_checked_start, pairpar_checked_initial in HSteps.
  pose proof
    (PairParStepsPhi_run_replays_heap
      (initial_state heap env rho (Mu_App ef1 ea1))
      (initial_state heap env rho (Mu_App ef2 ea2))
      k phi_state phi_left phi_right state'
      eq_refl HSteps)
    as HReplay.
  simpl in HReplay.
  exact HReplay.
Qed.

Definition PairParBranchReplayWitness
    (heap : Heap) (phi_left phi_right : Phi)
    (heap_left heap_right heap_join : Heap) : Prop :=
  heap_left ∖ heap ##ₘ heap_right ∖ heap /\
  (phi_left, heap) ==>* (Phi_Nil, heap_left) /\
  (phi_right, heap) ==>* (Phi_Nil, heap_right) /\
  (Phi_Par phi_left phi_right, heap) ==>* (Phi_Nil, heap_join).

Theorem PairParBranchReplayWitness_tc_heap_join :
  forall heap phi_left phi_right heap_left heap_right heap_join
    stty stty_left stty_right,
    PairParBranchReplayWitness
      heap phi_left phi_right heap_left heap_right heap_join ->
    TcPhi stty_left phi_left ->
    TcPhi stty_right phi_right ->
    TcHeap (heap, stty) ->
    StoreExtends stty stty_left ->
    StoreExtends stty stty_right ->
    TcHeap (heap_left, stty_left) ->
    TcHeap (heap_right, stty_right) ->
    TcHeap
      (heap_join, stty ∪ (stty_left ∖ stty ∪ stty_right ∖ stty)).
Proof.
  intros heap phi_left phi_right heap_left heap_right heap_join
    stty stty_left stty_right
    (HDisj & HLeftReplay & HRightReplay & HParReplay)
    HTcLeft HTcRight HTcHeap HExtLeft HExtRight HTcHeapLeft HTcHeapRight.
  eapply
    (TcHeap_Extended_PhiPar
      heap phi_left phi_right heap_left heap_right
      stty stty_left stty_right heap_join);
    eauto.
Qed.

Theorem PairParBranchReplayWitness_from_trace_disjointness :
  forall heap phi_left phi_right heap_left heap_right heap_join,
    Disjoint_Traces (phi_as_list phi_left) (phi_as_list phi_right) ->
    (phi_left, heap) ==>* (Phi_Nil, heap_left) ->
    (phi_right, heap) ==>* (Phi_Nil, heap_right) ->
    (Phi_Par phi_left phi_right, heap) ==>* (Phi_Nil, heap_join) ->
    PairParBranchReplayWitness
      heap phi_left phi_right heap_left heap_right heap_join.
Proof.
  intros heap phi_left phi_right heap_left heap_right heap_join
    HDisjointTraces HLeftReplay HRightReplay HParReplay.
  repeat split; eauto.
  eapply Phi_Heap_Steps_disjoint_deltas; eauto.
Qed.

Theorem PairParStepsPhi_checked_branch_replay_join :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_state phi_left phi_right state'
    heap_left heap_right stty stty_left stty_right,
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi_state phi_left phi_right state' ->
    heap_left ∖ heap ##ₘ heap_right ∖ heap ->
    (phi_left, heap) ==>* (Phi_Nil, heap_left) ->
    (phi_right, heap) ==>* (Phi_Nil, heap_right) ->
    TcPhi stty_left phi_left ->
    TcPhi stty_right phi_right ->
    TcHeap (heap, stty) ->
    StoreExtends stty stty_left ->
    StoreExtends stty stty_right ->
    TcHeap (heap_left, stty_left) ->
    TcHeap (heap_right, stty_right) ->
    exists heap_join,
      PairParBranchReplayWitness
        heap phi_left phi_right heap_left heap_right heap_join /\
      (phi_state, heap_join) ==>* (Phi_Nil, pairpar_state_heap state') /\
      TcHeap
        (heap_join, stty ∪ (stty_left ∖ stty ∪ stty_right ∖ stty)).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_state phi_left phi_right state'
    heap_left heap_right stty stty_left stty_right
    HSteps HDisj HLeftReplay HRightReplay HTcLeft HTcRight
    HTcHeap HExtLeft HExtRight HTcHeapLeft HTcHeapRight.
  unfold pairpar_checked_start, pairpar_checked_initial in HSteps.
  destruct
    (PairParStepsPhi_run_split_replays_heap
      (initial_state heap env rho (Mu_App ef1 ea1))
      (initial_state heap env rho (Mu_App ef2 ea2))
      k phi_state phi_left phi_right state'
      eq_refl HSteps)
    as (heap_join & HParReplay & HStateReplay).
  simpl in HParReplay, HStateReplay.
  exists heap_join.
  split.
  - repeat split; assumption.
  - split; [exact HStateReplay |].
    eapply PairParBranchReplayWitness_tc_heap_join; eauto.
    repeat split; assumption.
Qed.

Theorem PairParStepsPhi_checked_trace_disjoint_branch_replay_join :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_state phi_left phi_right state'
    heap_left heap_right stty stty_left stty_right,
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      phi_state phi_left phi_right state' ->
    Disjoint_Traces (phi_as_list phi_left) (phi_as_list phi_right) ->
    (phi_left, heap) ==>* (Phi_Nil, heap_left) ->
    (phi_right, heap) ==>* (Phi_Nil, heap_right) ->
    TcPhi stty_left phi_left ->
    TcPhi stty_right phi_right ->
    TcHeap (heap, stty) ->
    StoreExtends stty stty_left ->
    StoreExtends stty stty_right ->
    TcHeap (heap_left, stty_left) ->
    TcHeap (heap_right, stty_right) ->
    exists heap_join,
      PairParBranchReplayWitness
        heap phi_left phi_right heap_left heap_right heap_join /\
      (phi_state, heap_join) ==>* (Phi_Nil, pairpar_state_heap state') /\
      TcHeap
        (heap_join, stty ∪ (stty_left ∖ stty ∪ stty_right ∖ stty)).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_state phi_left phi_right state'
    heap_left heap_right stty stty_left stty_right
    HSteps HTraceDisjoint HLeftReplay HRightReplay HTcLeft HTcRight
    HTcHeap HExtLeft HExtRight HTcHeapLeft HTcHeapRight.
  assert (HHeapDisjoint : heap_left ∖ heap ##ₘ heap_right ∖ heap).
  {
    eapply Phi_Heap_Steps_disjoint_deltas; eauto.
  }
  eapply PairParStepsPhi_checked_branch_replay_join; eauto.
Qed.

Lemma WTPairParStateRuntimeHeapShapeAtStrong_step_label_phi_typed :
  forall state tout stty label state' stty',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParStep state label state' ->
    WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' ->
    TcPhi stty' (label_phi label).
Proof.
  intros state tout stty label state' stty' HWT HStep HWT'.
  destruct label as [| da].
  - apply TcPhi_nil.
  - pose proof
      (WTPairParStateRuntimeHeapShapeAtStrong_step_label_typed
        state tout stty (Act da) state' stty' HWT HStep HWT')
      as HTcLabel.
    simpl in HTcLabel.
    eapply TcPhi_seq_inv_l; eauto.
Qed.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_steps_phi_trace_typed :
  forall state tout stty phi_state phi_left phi_right state',
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParStepsPhi state phi_state phi_left phi_right state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' /\
      StoreExtends stty stty' /\
      TcPhi stty' phi_state /\
      TcPhi stty' phi_left /\
      TcPhi stty' phi_right.
Proof.
  intros state tout stty phi_state phi_left phi_right state' HWT HSteps.
  revert tout stty HWT.
  induction HSteps;
    intros tout stty HWT.
  - exists stty.
    split; [exact HWT |].
    split; [apply StoreExtends_refl |].
    repeat split; apply TcPhi_nil.
  - assert
      (HPairStep :
        PairParStep (PPS_State state) label (PPS_State state'))
      by (constructor; exact H).
    destruct
      (WTPairParStateRuntimeHeapShapeAtStrong_step_preservation
        (PPS_State state) tout stty label (PPS_State state') HWT HPairStep)
      as (stty1 & HWT1 & HExt1).
    destruct (IHHSteps tout stty1 HWT1)
      as (stty2 & HWT2 & HExt2 & HTcState & HTcLeft & HTcRight).
    pose proof
      (WTPairParStateRuntimeHeapShapeAtStrong_step_label_phi_typed
        (PPS_State state) tout stty label (PPS_State state') stty1
        HWT HPairStep HWT1)
      as HTcLabel1.
    pose proof
      (TcPhi_weaken stty1 stty2 (label_phi label) HExt2 HTcLabel1)
      as HTcLabel2.
    exists stty2.
    split; [exact HWT2 |].
    split; [eapply StoreExtends_trans; eauto |].
    split; [apply TcPhi_seq; assumption |].
    split; assumption.
  - assert
      (HPairStep :
        PairParStep
          (PPS_Run left right k)
          label
          (PPS_Run left' (with_state_heap (state_heap left') right) k))
      by (constructor; exact H).
    destruct
      (WTPairParStateRuntimeHeapShapeAtStrong_step_preservation
        (PPS_Run left right k) tout stty label
        (PPS_Run left' (with_state_heap (state_heap left') right) k)
        HWT HPairStep)
      as (stty1 & HWT1 & HExt1).
    destruct (IHHSteps tout stty1 HWT1)
      as (stty2 & HWT2 & HExt2 & HTcState & HTcLeft & HTcRight).
    pose proof
      (WTPairParStateRuntimeHeapShapeAtStrong_step_label_phi_typed
        (PPS_Run left right k) tout stty label
        (PPS_Run left' (with_state_heap (state_heap left') right) k)
        stty1 HWT HPairStep HWT1)
      as HTcLabel1.
    pose proof
      (TcPhi_weaken stty1 stty2 (label_phi label) HExt2 HTcLabel1)
      as HTcLabel2.
    exists stty2.
    split; [exact HWT2 |].
    split; [eapply StoreExtends_trans; eauto |].
    split; [exact HTcState |].
    split; [apply TcPhi_seq; assumption | exact HTcRight].
  - assert
      (HPairStep :
        PairParStep
          (PPS_Run left right k)
          label
          (PPS_Run (with_state_heap (state_heap right') left) right' k))
      by (constructor; exact H).
    destruct
      (WTPairParStateRuntimeHeapShapeAtStrong_step_preservation
        (PPS_Run left right k) tout stty label
        (PPS_Run (with_state_heap (state_heap right') left) right' k)
        HWT HPairStep)
      as (stty1 & HWT1 & HExt1).
    destruct (IHHSteps tout stty1 HWT1)
      as (stty2 & HWT2 & HExt2 & HTcState & HTcLeft & HTcRight).
    pose proof
      (WTPairParStateRuntimeHeapShapeAtStrong_step_label_phi_typed
        (PPS_Run left right k) tout stty label
        (PPS_Run (with_state_heap (state_heap right') left) right' k)
        stty1 HWT HPairStep HWT1)
      as HTcLabel1.
    pose proof
      (TcPhi_weaken stty1 stty2 (label_phi label) HExt2 HTcLabel1)
      as HTcLabel2.
    exists stty2.
    split; [exact HWT2 |].
    split; [eapply StoreExtends_trans; eauto |].
    split; [exact HTcState |].
    split; [exact HTcLeft | apply TcPhi_seq; assumption].
  - assert
      (HPairStep :
        PairParStep
          (PPS_Run (StDone heap v1) (StDone heap v2) k)
          Silent
          (PPS_State (StReturn heap (Pair (v1, v2)) k)))
      by constructor.
    destruct
      (WTPairParStateRuntimeHeapShapeAtStrong_step_preservation
        (PPS_Run (StDone heap v1) (StDone heap v2) k)
        tout stty Silent
        (PPS_State (StReturn heap (Pair (v1, v2)) k))
        HWT HPairStep)
      as (stty1 & HWT1 & HExt1).
    destruct (IHHSteps tout stty1 HWT1)
      as (stty2 & HWT2 & HExt2 & HTcState & HTcLeft & HTcRight).
    exists stty2.
    split; [exact HWT2 |].
    split; [eapply StoreExtends_trans; eauto |].
    repeat split; assumption.
Qed.

Lemma PairParStepsPhi_as_pairpar_steps_exists :
  forall state phi_state phi_left phi_right state',
    PairParStepsPhi state phi_state phi_left phi_right state' ->
    exists trace, PairParSteps state trace state'.
Proof.
  intros state phi_state phi_left phi_right state' HSteps.
  induction HSteps as
    [state
    | state label state1 phi_state phi_left phi_right state2
        HStep _ IH
    | left right k label left1 phi_state phi_left phi_right state2
        HStep _ IH
    | left right k label right1 phi_state phi_left phi_right state2
        HStep _ IH
    | heap v1 v2 k phi_state phi_left phi_right state2
        _ IH].
  - exists nil. constructor.
  - destruct IH as (trace & HPairSteps).
    exists (label_trace label ++ trace).
    econstructor; [apply PPStep_State; exact HStep | exact HPairSteps].
  - destruct IH as (trace & HPairSteps).
    exists (label_trace label ++ trace).
    econstructor; [apply PPStep_Left; exact HStep | exact HPairSteps].
  - destruct IH as (trace & HPairSteps).
    exists (label_trace label ++ trace).
    econstructor; [apply PPStep_Right; exact HStep | exact HPairSteps].
  - destruct IH as (trace & HPairSteps).
    exists (label_trace Silent ++ trace).
    econstructor; [apply PPStep_Done | exact HPairSteps].
Qed.

Lemma pairpar_steps_phi_preserve_heap_agreement :
  forall state phi_state phi_left phi_right state',
    PairParRunHeapsAgree state ->
    PairParStepsPhi state phi_state phi_left phi_right state' ->
    PairParRunHeapsAgree state'.
Proof.
  intros state phi_state phi_left phi_right state' HAgree HSteps.
  destruct (PairParStepsPhi_as_pairpar_steps_exists _ _ _ _ _ HSteps)
    as (trace & HPairSteps).
  eapply pairpar_steps_preserve_heap_agreement; eauto.
Qed.

Definition PairParPhiTraceSafeAt
    (state : PairParState) (tout : Tau) (stty : Sigma) : Prop :=
  forall phi_state phi_left phi_right state',
    PairParStepsPhi state phi_state phi_left phi_right state' ->
    exists stty',
      WTPairParStateRuntimeHeapShapeAtStrong state' tout stty' /\
      StoreExtends stty stty' /\
      PairParRunHeapsAgree state' /\
      PairParNotStuck state' /\
      TcPhi stty' phi_state /\
      TcPhi stty' phi_left /\
      TcPhi stty' phi_right.

Theorem WTPairParStateRuntimeHeapShapeAtStrong_phi_trace_safe_typed :
  PairParCheckDecidable ->
  forall state tout stty,
    WTPairParStateRuntimeHeapShapeAtStrong state tout stty ->
    PairParRunHeapsAgree state ->
    PairParPhiTraceSafeAt state tout stty.
Proof.
  intros HDec state tout stty HWT HAgree
    phi_state phi_left phi_right state' HSteps.
  destruct
    (WTPairParStateRuntimeHeapShapeAtStrong_steps_phi_trace_typed
      state tout stty phi_state phi_left phi_right state' HWT HSteps)
    as (stty' & HWT' & HExt & HTcState & HTcLeft & HTcRight).
  assert (HAgree' : PairParRunHeapsAgree state').
  {
    eapply pairpar_steps_phi_preserve_heap_agreement; eauto.
  }
  destruct (PairParStepsPhi_as_pairpar_steps_exists _ _ _ _ _ HSteps)
    as (trace & HPairSteps).
  pose proof
    (WTPairParStateRuntimeHeapShapeAtStrong_never_stuck_typed
      HDec state tout stty HWT HAgree)
    as HNeverStuck.
  exists stty'. split; [exact HWT' |].
  split; [exact HExt |].
  split; [exact HAgree' |].
  split; [exact (HNeverStuck trace state' HPairSteps) |].
  repeat split; assumption.
Qed.

Theorem StatePhiTraceSafeAt_terminal_value :
  forall state tout stty phi heap' v,
    StatePhiTraceSafeAt state tout stty ->
    StepsPhi state phi (StDone heap' v) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, tout) /\
      RuntimeValShape stty' tout v /\
      TcPhi stty' phi.
Proof.
  intros state tout stty phi heap' v HSafe HSteps.
  destruct (HSafe phi (StDone heap' v) HSteps)
    as (stty' & HWT' & HExt & _ & HTcPhi).
  destruct
    (WTStateRuntimeHeapShapeAt_done_value heap' v tout stty' HWT')
    as (HTcHeap' & HHeapShape' & HTcVal' & HValShape').
  exists stty'. split; [exact HExt |].
  split; [exact HTcHeap' |].
  split; [exact HHeapShape' |].
  split; [exact HTcVal' |].
  split; [exact HValShape' | exact HTcPhi].
Qed.

Theorem PairParPhiTraceSafeAt_terminal_value :
  forall state tout stty phi_state phi_left phi_right heap' v,
    PairParPhiTraceSafeAt state tout stty ->
    PairParStepsPhi state phi_state phi_left phi_right
      (PPS_State (StDone heap' v)) ->
    exists stty',
      StoreExtends stty stty' /\
      TcHeap (heap', stty') /\
      RuntimeHeapShape heap' stty' /\
      TcVal (stty', v, tout) /\
      RuntimeValShape stty' tout v /\
      TcPhi stty' phi_state /\
      TcPhi stty' phi_left /\
      TcPhi stty' phi_right.
Proof.
  intros state tout stty phi_state phi_left phi_right heap' v HSafe HSteps.
  destruct (HSafe phi_state phi_left phi_right
    (PPS_State (StDone heap' v)) HSteps)
    as (stty' & HWT' & HExt & _ & _ & HTcState & HTcLeft & HTcRight).
  destruct
    (WTPairParStateRuntimeHeapShapeAtStrong_done_value
      heap' v tout stty' HWT')
    as (HTcHeap' & HHeapShape' & HTcVal' & HValShape').
  exists stty'. split; [exact HExt |].
  split; [exact HTcHeap' |].
  split; [exact HHeapShape' |].
  split; [exact HTcVal' |].
  split; [exact HValShape' |].
  repeat split; assumption.
Qed.

Theorem pairpar_check_pass_checked_phi_trace_safe :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout theta1 theta2,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    PairParCheckPass theta1 theta2 ->
    PairParPhiTraceSafeAt
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      tout stty.
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout theta1 theta2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont _.
  unfold pairpar_checked_start.
  eapply WTPairParStateRuntimeHeapShapeAtStrong_phi_trace_safe_typed; eauto.
  - eapply WTPairParStateRuntimeHeapShapeAtStrong_checked_initial; eauto.
  - apply pairpar_checked_initial_heaps_agree.
Qed.

Theorem pairpar_check_fail_sequential_phi_trace_safe :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout theta1 theta2,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    PairParCheckFail theta1 theta2 ->
    exists stty',
      StoreExtends stty stty' /\
      StatePhiTraceSafeAt
        (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k)
        tout stty'.
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout theta1 theta2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont HFail.
  destruct
    (pairpar_check_fail_sequential_preservation
      heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k tout stty)
    as (stty' & HWT' & HExt).
  - eapply pairpar_check_state_typed; eauto.
  - exact HFail.
  - exists stty'. split; [exact HExt |].
    eapply WTStateRuntimeHeapShapeAt_phi_trace_safe_typed; eauto.
Qed.

Theorem pairpar_check_decidable_phi_trace_safe :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout theta1 theta2,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    (PairParCheckPass theta1 theta2 /\
      PairParPhiTraceSafeAt
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
        tout stty) \/
    (PairParCheckFail theta1 theta2 /\
      exists stty',
        StoreExtends stty stty' /\
        StatePhiTraceSafeAt
          (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k)
          tout stty').
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout theta1 theta2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont.
  destruct (HDec theta1 theta2) as [HPass | HFail].
  - left. split; [exact HPass |].
    eapply pairpar_check_pass_checked_phi_trace_safe; eauto.
  - right. split; [exact HFail |].
    eapply pairpar_check_fail_sequential_phi_trace_safe; eauto.
Qed.

Theorem pairpar_check_decidable_phi_terminal_value :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout theta1 theta2,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    (PairParCheckPass theta1 theta2 /\
      forall phi_state phi_left phi_right heap' v,
        PairParStepsPhi
          (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
          phi_state phi_left phi_right
          (PPS_State (StDone heap' v)) ->
        exists stty',
          StoreExtends stty stty' /\
          TcHeap (heap', stty') /\
          RuntimeHeapShape heap' stty' /\
          TcVal (stty', v, tout) /\
          RuntimeValShape stty' tout v /\
          TcPhi stty' phi_state /\
          TcPhi stty' phi_left /\
          TcPhi stty' phi_right) \/
    (PairParCheckFail theta1 theta2 /\
      forall phi heap' v,
        StepsPhi
          (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k)
          phi (StDone heap' v) ->
        exists stty',
          StoreExtends stty stty' /\
          TcHeap (heap', stty') /\
          RuntimeHeapShape heap' stty' /\
          TcVal (stty', v, tout) /\
          RuntimeValShape stty' tout v /\
          TcPhi stty' phi).
Proof.
  intros HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 tout theta1 theta2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcExp1 HTcExp2 HKont.
  destruct
    (pairpar_check_decidable_phi_trace_safe
      HDec heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
      ty1 ty2 eff1 eff2 tout theta1 theta2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcExp1 HTcExp2 HKont)
    as [(HPass & HSafe) | (HFail & stty_seq & HExtSeq & HSafe)].
  - left.
    split; [exact HPass |].
    intros phi_state phi_left phi_right heap' v HSteps.
    eapply PairParPhiTraceSafeAt_terminal_value; eauto.
  - right.
    split; [exact HFail |].
    intros phi heap' v HSteps.
    destruct
      (StatePhiTraceSafeAt_terminal_value
        (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k)
        tout stty_seq phi heap' v HSafe HSteps)
      as (stty' & HExtFinal & HTcHeap' & HHeapShape' & HTcVal' &
          HValShape' & HTcPhi).
    exists stty'. split.
    + eapply StoreExtends_trans; eauto.
    + split; [exact HTcHeap' |].
      split; [exact HHeapShape' |].
      split; [exact HTcVal' |].
      split; [exact HValShape' | exact HTcPhi].
Qed.

Definition pairpar_effect_summary_state
    (heap : Heap) (env : Env) (rho : Rho) (ef ea : Expr) : State :=
  initial_state heap env rho (Eff_App ef ea).

Inductive PairParEffectSummaryStepsPhi
    (heap : Heap) (env : Env) (rho : Rho)
    (ef1 ea1 ef2 ea2 : Expr) :
    Phi -> Phi -> Heap -> Theta -> Heap -> Theta -> Prop :=
| PairParEffectSummaryStepsPhi_intro :
    forall phi_eff1 phi_eff2 heap_eff1 heap_eff2 theta1 theta2,
      StepsPhi
        (pairpar_effect_summary_state heap env rho ef1 ea1)
        phi_eff1
        (StDone heap_eff1 (Eff theta1)) ->
      StepsPhi
        (pairpar_effect_summary_state heap env rho ef2 ea2)
        phi_eff2
        (StDone heap_eff2 (Eff theta2)) ->
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2.

Inductive PairParSequentialEffectSummaryStepsPhi
    (heap : Heap) (env : Env) (rho : Rho)
    (ef1 ea1 ef2 ea2 : Expr) :
    Phi -> Phi -> Heap -> Theta -> Heap -> Theta -> Prop :=
| PairParSequentialEffectSummaryStepsPhi_intro :
    forall phi_eff1 phi_eff2 heap_eff1 heap_eff2 theta1 theta2,
      StepsPhi
        (pairpar_effect_summary_state heap env rho ef1 ea1)
        phi_eff1
        (StDone heap_eff1 (Eff theta1)) ->
      StepsPhi
        (pairpar_effect_summary_state heap_eff1 env rho ef2 ea2)
        phi_eff2
        (StDone heap_eff2 (Eff theta2)) ->
      PairParSequentialEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2.

Theorem PairParEffectSummaryStepsPhi_sequential_when_first_heap_unchanged :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    heap_eff1 = heap ->
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    HSummary HHeapUnchanged.
  inversion HSummary; subst.
  subst.
  constructor; assumption.
Qed.

Theorem PairParSequentialEffectSummaryStepsPhi_independent_when_first_heap_unchanged :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    heap_eff1 = heap ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    HSummary HHeapUnchanged.
  inversion HSummary; subst.
  subst.
  constructor; assumption.
Qed.

Theorem pairpar_effect_summary_steps_phi_heap_neutral :
  forall heap env rho ef ea phi heap_eff theta,
    StepsPhi
      (pairpar_effect_summary_state heap env rho ef ea)
      phi
      (StDone heap_eff (Eff theta)) ->
    ReadOnlyPhi phi ->
    heap_eff = heap.
Proof.
  intros heap env rho ef ea phi heap_eff theta HSteps HReadOnly.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (pairpar_effect_summary_state heap env rho ef ea)
      phi
      (StDone heap_eff (Eff theta))
      HSteps HReadOnly)
    as HHeap.
  simpl in HHeap.
  now symmetry.
Qed.

Theorem effect_summary_trace_readonly_from_static_soundness :
  forall rho static_eff phi,
    ReadOnlyStatic (fold_subst_eps rho static_eff) ->
    Epsilon_Phi_Soundness (fold_subst_eps rho static_eff, phi) ->
    ReadOnlyPhi phi.
Proof.
  intros rho static_eff phi HReadOnlyStatic HSound.
  eapply ReadOnlyStaticImpliesReadOnlyPhi; eauto.
Qed.

Theorem pairpar_effect_summary_steps_phi_readonly_from_static_soundness :
  forall heap env rho ef ea phi heap_eff theta static_eff,
    StepsPhi
      (pairpar_effect_summary_state heap env rho ef ea)
      phi
      (StDone heap_eff (Eff theta)) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff) ->
    Epsilon_Phi_Soundness (fold_subst_eps rho static_eff, phi) ->
    ReadOnlyPhi phi.
Proof.
  intros heap env rho ef ea phi heap_eff theta static_eff
    _ HReadOnlyStatic HSound.
  eapply effect_summary_trace_readonly_from_static_soundness; eauto.
Qed.

Theorem PairParEffectSummaryStepsPhi_first_readonly_heap_neutral :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyPhi phi_eff1 ->
    heap_eff1 = heap.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    HSummary HReadOnly.
  inversion HSummary; subst.
  eapply pairpar_effect_summary_steps_phi_heap_neutral; eauto.
Qed.

Theorem PairParSequentialEffectSummaryStepsPhi_first_readonly_heap_neutral :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyPhi phi_eff1 ->
    heap_eff1 = heap.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    HSummary HReadOnly.
  inversion HSummary; subst.
  eapply pairpar_effect_summary_steps_phi_heap_neutral; eauto.
Qed.

Theorem PairParEffectSummaryStepsPhi_sequential_when_first_readonly :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyPhi phi_eff1 ->
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    HSummary HReadOnly.
  eapply PairParEffectSummaryStepsPhi_sequential_when_first_heap_unchanged.
  - exact HSummary.
  - eapply PairParEffectSummaryStepsPhi_first_readonly_heap_neutral; eauto.
Qed.

Theorem PairParSequentialEffectSummaryStepsPhi_independent_when_first_readonly :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyPhi phi_eff1 ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    HSummary HReadOnly.
  eapply PairParSequentialEffectSummaryStepsPhi_independent_when_first_heap_unchanged.
  - exact HSummary.
  - eapply PairParSequentialEffectSummaryStepsPhi_first_readonly_heap_neutral;
      eauto.
Qed.

Theorem pairpar_effect_summary_steps_phi_continue :
  forall heap env rho ef ea phi heap_eff theta tail state_next,
    StepsPhi
      (pairpar_effect_summary_state heap env rho ef ea)
      phi
      (StDone heap_eff (Eff theta)) ->
    Step (StReturn heap_eff (Eff theta) tail) Silent state_next ->
    StepsPhi
      (StEval heap env rho (Eff_App ef ea) tail)
      phi
      state_next.
Proof.
  intros heap env rho ef ea phi heap_eff theta tail state_next
    HSteps HFinal.
  unfold pairpar_effect_summary_state in HSteps.
  eapply StepsPhi_initial_terminal_continue; eauto.
Qed.

Theorem PairParSequentialEffectSummaryStepsPhi_source_pass_prefix :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
    exists phi_source,
      StepsPhi
        (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
        phi_source
        (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k) /\
      phi_as_list phi_source =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    HSummary HPass.
  inversion HSummary; subst.
  assert
    (HStepEff2 :
      Step
        (StReturn heap_eff1 (Eff theta1)
          (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
        Silent
        (StEval heap_eff1 env rho (Eff_App ef2 ea2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))).
  {
    constructor.
  }
  pose proof
    (pairpar_effect_summary_steps_phi_continue
      heap env rho ef1 ea1 phi_eff1 heap_eff1 theta1
      (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)
      (StEval heap_eff1 env rho (Eff_App ef2 ea2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      H HStepEff2)
    as HRunEff1.
  assert
    (HStepMu1 :
      Step
        (StReturn heap_eff2 (Eff theta2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
        Silent
        (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k)).
  {
    eapply pairpar_check_passes_to_sequential_start; eauto.
  }
  pose proof
    (pairpar_effect_summary_steps_phi_continue
      heap_eff1 env rho ef2 ea2 phi_eff2 heap_eff2 theta2
      (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)
      (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k)
      H0 HStepMu1)
    as HRunEff2.
  destruct
    (StepsPhi_trans_exists
      (StEval heap env rho (Eff_App ef1 ea1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      phi_eff1
      (StEval heap_eff1 env rho (Eff_App ef2 ea2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      phi_eff2
      (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k)
      HRunEff1 HRunEff2)
    as (phi_eff & HRunEff & HTraceEff).
  exists (Phi_Seq (label_phi Silent) phi_eff).
  split.
  - eapply StepsPhi_Step.
    + constructor.
    + exact HRunEff.
  - simpl.
    exact HTraceEff.
Qed.

Theorem PairParSequentialEffectSummaryStepsPhi_source_fail_prefix :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckFail theta1 theta2 ->
    exists phi_source,
      StepsPhi
        (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
        phi_source
        (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k) /\
      phi_as_list phi_source =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    HSummary HFail.
  inversion HSummary; subst.
  assert
    (HStepEff2 :
      Step
        (StReturn heap_eff1 (Eff theta1)
          (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
        Silent
        (StEval heap_eff1 env rho (Eff_App ef2 ea2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))).
  {
    constructor.
  }
  pose proof
    (pairpar_effect_summary_steps_phi_continue
      heap env rho ef1 ea1 phi_eff1 heap_eff1 theta1
      (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)
      (StEval heap_eff1 env rho (Eff_App ef2 ea2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      H HStepEff2)
    as HRunEff1.
  assert
    (HStepMu1 :
      Step
        (StReturn heap_eff2 (Eff theta2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
        Silent
        (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k)).
  {
    eapply pairpar_check_fails_to_sequential_start; eauto.
  }
  pose proof
    (pairpar_effect_summary_steps_phi_continue
      heap_eff1 env rho ef2 ea2 phi_eff2 heap_eff2 theta2
      (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)
      (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k)
      H0 HStepMu1)
    as HRunEff2.
  destruct
    (StepsPhi_trans_exists
      (StEval heap env rho (Eff_App ef1 ea1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      phi_eff1
      (StEval heap_eff1 env rho (Eff_App ef2 ea2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      phi_eff2
      (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k)
      HRunEff1 HRunEff2)
    as (phi_eff & HRunEff & HTraceEff).
  exists (Phi_Seq (label_phi Silent) phi_eff).
  split.
  - eapply StepsPhi_Step.
    + constructor.
    + exact HRunEff.
  - simpl.
    exact HTraceEff.
Qed.

Theorem PairParSequentialEffectSummaryStepsPhi_source_pass_independent_prefix :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyPhi phi_eff1 ->
    PairParCheckPass theta1 theta2 ->
    exists phi_source,
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      StepsPhi
        (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
        phi_source
        (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k) /\
      phi_as_list phi_source =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    HSummary HReadOnly HPass.
  destruct
    (PairParSequentialEffectSummaryStepsPhi_source_pass_prefix
      heap env rho ef1 ea1 ef2 ea2 k
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
      HSummary HPass)
    as (phi_source & HPrefix & HTrace).
  exists phi_source.
  split.
  - eapply PairParSequentialEffectSummaryStepsPhi_independent_when_first_readonly;
      eauto.
  - split; assumption.
Qed.

Theorem PairParSequentialEffectSummaryStepsPhi_source_fail_independent_prefix :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyPhi phi_eff1 ->
    PairParCheckFail theta1 theta2 ->
    exists phi_source,
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      StepsPhi
        (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
        phi_source
        (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k) /\
      phi_as_list phi_source =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    HSummary HReadOnly HFail.
  destruct
    (PairParSequentialEffectSummaryStepsPhi_source_fail_prefix
      heap env rho ef1 ea1 ef2 ea2 k
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
      HSummary HFail)
    as (phi_source & HPrefix & HTrace).
  exists phi_source.
  split.
  - eapply PairParSequentialEffectSummaryStepsPhi_independent_when_first_readonly;
      eauto.
  - split; assumption.
Qed.

Theorem PairParSequentialEffectSummaryStepsPhi_source_pass_static_sound_prefix :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1,
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    Epsilon_Phi_Soundness
      (fold_subst_eps rho static_eff1, phi_eff1) ->
    PairParCheckPass theta1 theta2 ->
    exists phi_source,
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      StepsPhi
        (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
        phi_source
        (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k) /\
      phi_as_list phi_source =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1
    HSummary HReadOnlyStatic HSound HPass.
  eapply PairParSequentialEffectSummaryStepsPhi_source_pass_independent_prefix;
    eauto.
  eapply effect_summary_trace_readonly_from_static_soundness; eauto.
Qed.

Theorem PairParSequentialEffectSummaryStepsPhi_source_fail_static_sound_prefix :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1,
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    Epsilon_Phi_Soundness
      (fold_subst_eps rho static_eff1, phi_eff1) ->
    PairParCheckFail theta1 theta2 ->
    exists phi_source,
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      StepsPhi
        (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
        phi_source
        (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k) /\
      phi_as_list phi_source =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1
    HSummary HReadOnlyStatic HSound HFail.
  eapply PairParSequentialEffectSummaryStepsPhi_source_fail_independent_prefix;
    eauto.
  eapply effect_summary_trace_readonly_from_static_soundness; eauto.
Qed.

Theorem PairParSequentialEffectSummaryStepsPhi_source_pass_static_included_prefix :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1,
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    Included StaticAction
      (Phi_Static_Effect phi_eff1)
      (fold_subst_eps rho static_eff1) ->
    PairParCheckPass theta1 theta2 ->
    exists phi_source,
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      StepsPhi
        (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
        phi_source
        (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k) /\
      phi_as_list phi_source =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1
    HSummary HReadOnlyStatic HIncluded HPass.
  eapply PairParSequentialEffectSummaryStepsPhi_source_pass_static_sound_prefix;
    eauto.
  eapply Epsilon_Phi_Soundness_of_phi_static_included; eauto.
Qed.

Theorem PairParSequentialEffectSummaryStepsPhi_source_fail_static_included_prefix :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1,
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    Included StaticAction
      (Phi_Static_Effect phi_eff1)
      (fold_subst_eps rho static_eff1) ->
    PairParCheckFail theta1 theta2 ->
    exists phi_source,
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      StepsPhi
        (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
        phi_source
        (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k) /\
      phi_as_list phi_source =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1
    HSummary HReadOnlyStatic HIncluded HFail.
  eapply PairParSequentialEffectSummaryStepsPhi_source_fail_static_sound_prefix;
    eauto.
  eapply Epsilon_Phi_Soundness_of_phi_static_included; eauto.
Qed.

Theorem PairParSequentialEffectSummaryStepsPhi_source_pass_trace_static_prefix :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (Phi_Static_Effect phi_eff1) ->
    PairParCheckPass theta1 theta2 ->
    exists phi_source,
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      StepsPhi
        (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
        phi_source
        (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k) /\
      phi_as_list phi_source =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    HSummary HReadOnlyStatic HPass.
  eapply PairParSequentialEffectSummaryStepsPhi_source_pass_independent_prefix;
    eauto.
  eapply ReadOnlyStaticImpliesReadOnlyPhi.
  - exact HReadOnlyStatic.
  - apply Phi_Static_Effect_sound.
Qed.

Theorem PairParSequentialEffectSummaryStepsPhi_source_fail_trace_static_prefix :
  forall heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (Phi_Static_Effect phi_eff1) ->
    PairParCheckFail theta1 theta2 ->
    exists phi_source,
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      StepsPhi
        (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
        phi_source
        (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k) /\
      phi_as_list phi_source =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    HSummary HReadOnlyStatic HFail.
  eapply PairParSequentialEffectSummaryStepsPhi_source_fail_independent_prefix;
    eauto.
  eapply ReadOnlyStaticImpliesReadOnlyPhi.
  - exact HReadOnlyStatic.
  - apply Phi_Static_Effect_sound.
Qed.

Theorem pairpar_effect_summary_steps_phi_replay :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    (phi_eff1, heap) ==>* (Phi_Nil, heap_eff1) /\
    (phi_eff2, heap) ==>* (Phi_Nil, heap_eff2).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 HSummary.
  inversion HSummary; subst.
  split.
  - pose proof (StepsPhi_replays_heap _ _ _ H) as HReplay.
    simpl in HReplay. exact HReplay.
  - pose proof (StepsPhi_replays_heap _ _ _ H0) as HReplay.
    simpl in HReplay. exact HReplay.
Qed.

Theorem pairpar_effect_summary_steps_phi_trace_typed :
  forall heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns eff3 eff4
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, eff3) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, Ty_Effect, eff4) ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    exists stty_eff1 stty_eff2,
      WTStateRuntimeHeapShapeAt
        (StDone heap_eff1 (Eff theta1))
        (subst_rho rho Ty_Effect)
        stty_eff1 /\
      StoreExtends stty stty_eff1 /\
      TcPhi stty_eff1 phi_eff1 /\
      WTStateRuntimeHeapShapeAt
        (StDone heap_eff2 (Eff theta2))
        (subst_rho rho Ty_Effect)
        stty_eff2 /\
      StoreExtends stty stty_eff2 /\
      TcPhi stty_eff2 phi_eff2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns eff3 eff4
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEff1 HTcEff2 HSummary.
  inversion HSummary; subst.
  destruct
    (WTStateRuntimeHeapShapeAt_steps_phi_trace_typed
      (pairpar_effect_summary_state heap env rho ef1 ea1)
      (subst_rho rho Ty_Effect) stty
      phi_eff1 (StDone heap_eff1 (Eff theta1)))
    as (stty_eff1 & HWT1 & HExt1 & HTcPhi1).
  - eapply WTStateRuntimeHeapShapeAt_initial; eauto.
  - exact H.
  - destruct
      (WTStateRuntimeHeapShapeAt_steps_phi_trace_typed
        (pairpar_effect_summary_state heap env rho ef2 ea2)
        (subst_rho rho Ty_Effect) stty
        phi_eff2 (StDone heap_eff2 (Eff theta2)))
      as (stty_eff2 & HWT2 & HExt2 & HTcPhi2).
    + eapply WTStateRuntimeHeapShapeAt_initial; eauto.
    + exact H0.
    + exists stty_eff1, stty_eff2.
      split; [exact HWT1 |].
      split; [exact HExt1 |].
      split; [exact HTcPhi1 |].
      split; [exact HWT2 |].
      split; [exact HExt2 | exact HTcPhi2].
Qed.

Definition pairpar_checked_structured_trace
    (phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2 : Phi) : Phi :=
  Phi_Seq
    (Phi_Par phi_eff1 phi_eff2)
    (Phi_Seq (Phi_Par phi_mu1 phi_mu2) phi_mu_state).

Definition pairpar_fallback_structured_trace
    (phi_eff1 phi_eff2 phi_seq : Phi) : Phi :=
  Phi_Seq (Phi_Par phi_eff1 phi_eff2) phi_seq.

Inductive PairParCheckedStructuredStepsPhi
    (heap : Heap) (env : Env) (rho : Rho)
    (ef1 ea1 ef2 ea2 : Expr) (k : Kont) :
    Phi -> PairParState -> Prop :=
| PairParCheckedStructuredStepsPhi_intro :
    forall phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
      heap_eff1 heap_eff2 theta1 theta2 state',
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
      PairParCheckPass theta1 theta2 ->
      PairParStepsPhi
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
        phi_mu_state
        phi_mu1
        phi_mu2
        state' ->
      PairParCheckedStructuredStepsPhi
        heap env rho ef1 ea1 ef2 ea2 k
        (pairpar_checked_structured_trace
          phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2)
        state'.

Inductive PairParFallbackStructuredStepsPhi
    (heap : Heap) (env : Env) (rho : Rho)
    (ef1 ea1 ef2 ea2 : Expr) (k : Kont) :
    Phi -> State -> Prop :=
| PairParFallbackStructuredStepsPhi_intro :
    forall phi_eff1 phi_eff2 phi_seq
      heap_eff1 heap_eff2 theta1 theta2 state',
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
      PairParCheckFail theta1 theta2 ->
      StepsPhi
        (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k)
        phi_seq
        state' ->
      PairParFallbackStructuredStepsPhi
        heap env rho ef1 ea1 ef2 ea2 k
        (pairpar_fallback_structured_trace phi_eff1 phi_eff2 phi_seq)
        state'.

Theorem pairpar_check_pass_steps_phi_to_sequential :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k phi state',
    PairParCheckPass theta1 theta2 ->
    StepsPhi
      (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k)
      phi
      state' ->
    StepsPhi
      (pairpar_check_state
        heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
      (Phi_Seq Phi_Nil phi)
      state'.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k phi state'
    HPass HSteps.
  change (Phi_Seq Phi_Nil phi) with (Phi_Seq (label_phi Silent) phi).
  eapply StepsPhi_Step.
  - eapply pairpar_check_passes_to_sequential_start; eauto.
  - exact HSteps.
Qed.

Theorem pairpar_check_fail_steps_phi_to_fallback :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k phi state',
    PairParCheckFail theta1 theta2 ->
    StepsPhi
      (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k)
      phi
      state' ->
    StepsPhi
      (pairpar_check_state
        heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
      (Phi_Seq Phi_Nil phi)
      state'.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k phi state'
    HFail HSteps.
  change (Phi_Seq Phi_Nil phi) with (Phi_Seq (label_phi Silent) phi).
  eapply StepsPhi_Step.
  - eapply pairpar_check_fails_to_sequential_start; eauto.
  - exact HSteps.
Qed.

Theorem PairParCheckedStructuredStepsPhi_source_check_dispatch :
  forall heap env rho ef1 ea1 ef2 ea2 k phi state',
    PairParCheckedStructuredStepsPhi
      heap env rho ef1 ea1 ef2 ea2 k
      phi
      state' ->
    exists phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
      heap_eff1 heap_eff2 theta1 theta2,
      phi =
        pairpar_checked_structured_trace
          phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2 /\
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      PairParCheckPass theta1 theta2 /\
      Step
        (pairpar_check_state
          heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
        Silent
        (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k) /\
      PairParStepsPhi
        (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
        phi_mu_state
        phi_mu1
        phi_mu2
        state'.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k phi state' HStructured.
  inversion HStructured; subst.
  exists phi_eff1, phi_eff2, phi_mu_state, phi_mu1, phi_mu2.
  exists heap_eff1, heap_eff2, theta1, theta2.
  split; [reflexivity |].
  split; [exact H |].
  split; [exact H0 |].
  split.
  - now apply pairpar_check_passes_to_sequential_start.
  - exact H1.
Qed.

Theorem PairParFallbackStructuredStepsPhi_erases_from_check_state :
  forall heap env rho ef1 ea1 ef2 ea2 k phi state',
    PairParFallbackStructuredStepsPhi
      heap env rho ef1 ea1 ef2 ea2 k
      phi
      state' ->
    exists phi_eff1 phi_eff2 phi_seq
      heap_eff1 heap_eff2 theta1 theta2,
      phi = pairpar_fallback_structured_trace phi_eff1 phi_eff2 phi_seq /\
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      PairParCheckFail theta1 theta2 /\
      StepsPhi
        (pairpar_check_state
          heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
        (Phi_Seq Phi_Nil phi_seq)
        state'.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k phi state' HStructured.
  inversion HStructured; subst.
  exists phi_eff1, phi_eff2, phi_seq.
  exists heap_eff1, heap_eff2, theta1, theta2.
  split; [reflexivity |].
  split; [exact H |].
  split; [exact H0 |].
  eapply pairpar_check_fail_steps_phi_to_fallback; eauto.
Qed.

Lemma TcPhi_pairpar_checked_structured_trace :
  forall stty phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2,
    TcPhi stty phi_eff1 ->
    TcPhi stty phi_eff2 ->
    TcPhi stty phi_mu_state ->
    TcPhi stty phi_mu1 ->
    TcPhi stty phi_mu2 ->
    TcPhi stty
      (pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2).
Proof.
  intros stty phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    HTcEff1 HTcEff2 HTcMuState HTcMu1 HTcMu2.
  unfold pairpar_checked_structured_trace.
  apply TcPhi_seq.
  - now apply TcPhi_par.
  - apply TcPhi_seq.
    + now apply TcPhi_par.
    + exact HTcMuState.
Qed.

Lemma TcPhi_pairpar_fallback_structured_trace :
  forall stty phi_eff1 phi_eff2 phi_seq,
    TcPhi stty phi_eff1 ->
    TcPhi stty phi_eff2 ->
    TcPhi stty phi_seq ->
    TcPhi stty
      (pairpar_fallback_structured_trace phi_eff1 phi_eff2 phi_seq).
Proof.
  intros stty phi_eff1 phi_eff2 phi_seq HTcEff1 HTcEff2 HTcSeq.
  unfold pairpar_fallback_structured_trace.
  apply TcPhi_seq.
  - now apply TcPhi_par.
  - exact HTcSeq.
Qed.

Theorem PairParCheckedStructuredStepsPhi_terminal_components_typed :
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 eff3 eff4 tout phi heap' v,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, eff3) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, Ty_Effect, eff4) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    PairParCheckedStructuredStepsPhi
      heap env rho ef1 ea1 ef2 ea2 k
      phi (PPS_State (StDone heap' v)) ->
    exists phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
      stty_eff1 stty_eff2 stty_mu,
      phi =
        pairpar_checked_structured_trace
          phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2 /\
      StoreExtends stty stty_eff1 /\
      TcPhi stty_eff1 phi_eff1 /\
      StoreExtends stty stty_eff2 /\
      TcPhi stty_eff2 phi_eff2 /\
      StoreExtends stty stty_mu /\
      TcHeap (heap', stty_mu) /\
      RuntimeHeapShape heap' stty_mu /\
      TcVal (stty_mu, v, tout) /\
      RuntimeValShape stty_mu tout v /\
      TcPhi stty_mu phi_mu_state /\
      TcPhi stty_mu phi_mu1 /\
      TcPhi stty_mu phi_mu2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 eff3 eff4 tout phi heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcMu1 HTcMu2 HTcEff1 HTcEff2 HKont HStructured.
  inversion HStructured; subst.
  destruct
    (pairpar_effect_summary_steps_phi_trace_typed
      heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns eff3 eff4
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2)
    as (stty_eff1 & stty_eff2 & _ & HExtEff1 & HTcPhiEff1 &
        _ & HExtEff2 & HTcPhiEff2);
    eauto.
  destruct
    (WTPairParStateRuntimeHeapShapeAtStrong_steps_phi_trace_typed
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 k)
      tout stty phi_mu_state phi_mu1 phi_mu2
      (PPS_State (StDone heap' v)))
    as (stty_mu & HWTMu & HExtMu & HTcPhiMuState & HTcPhiMu1 & HTcPhiMu2).
  - unfold pairpar_checked_start.
    eapply WTPairParStateRuntimeHeapShapeAtStrong_checked_initial; eauto.
  - exact H1.
  - destruct
      (WTPairParStateRuntimeHeapShapeAtStrong_done_value
        heap' v tout stty_mu HWTMu)
      as (HTcHeap' & HHeapShape' & HTcVal' & HValShape').
    exists phi_eff1, phi_eff2, phi_mu_state, phi_mu1, phi_mu2.
    exists stty_eff1, stty_eff2, stty_mu.
    split; [reflexivity |].
    split; [exact HExtEff1 |].
    split; [exact HTcPhiEff1 |].
    split; [exact HExtEff2 |].
    split; [exact HTcPhiEff2 |].
    split; [exact HExtMu |].
    split; [exact HTcHeap' |].
    split; [exact HHeapShape' |].
    split; [exact HTcVal' |].
    split; [exact HValShape' |].
    split; [exact HTcPhiMuState |].
    split; [exact HTcPhiMu1 | exact HTcPhiMu2].
Qed.

Theorem PairParFallbackStructuredStepsPhi_terminal_components_typed :
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 eff3 eff4 tout phi heap' v,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, eff3) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, Ty_Effect, eff4) ->
    WTKontRuntime stty (subst_rho rho (Ty_Pair ty1 ty2)) tout k ->
    PairParFallbackStructuredStepsPhi
      heap env rho ef1 ea1 ef2 ea2 k
      phi (StDone heap' v) ->
    exists phi_eff1 phi_eff2 phi_seq stty_eff1 stty_eff2 stty_seq,
      phi = pairpar_fallback_structured_trace phi_eff1 phi_eff2 phi_seq /\
      StoreExtends stty stty_eff1 /\
      TcPhi stty_eff1 phi_eff1 /\
      StoreExtends stty stty_eff2 /\
      TcPhi stty_eff2 phi_eff2 /\
      StoreExtends stty stty_seq /\
      TcHeap (heap', stty_seq) /\
      RuntimeHeapShape heap' stty_seq /\
      TcVal (stty_seq, v, tout) /\
      RuntimeValShape stty_seq tout v /\
      TcPhi stty_seq phi_seq.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    ty1 ty2 eff1 eff2 eff3 eff4 tout phi heap' v
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcMu1 HTcMu2 HTcEff1 HTcEff2 HKont HStructured.
  inversion HStructured; subst.
  destruct
    (pairpar_effect_summary_steps_phi_trace_typed
      heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns eff3 eff4
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2)
    as (stty_eff1 & stty_eff2 & _ & HExtEff1 & HTcPhiEff1 &
        _ & HExtEff2 & HTcPhiEff2);
    eauto.
  destruct
    (pairpar_check_fail_sequential_preservation
      heap env rho ef1 ea1 ef2 ea2 theta1 theta2 k tout stty)
    as (stty_start & HWTStart & HExtStart).
  - eapply pairpar_check_state_typed; eauto.
  - exact H0.
  - destruct
      (WTStateRuntimeHeapShapeAt_steps_phi_trace_typed
        (pairpar_sequential_start heap env rho ef1 ea1 ef2 ea2 k)
        tout stty_start phi_seq (StDone heap' v)
        HWTStart H1)
      as (stty_seq & HWTSeq & HExtSeq & HTcPhiSeq).
    destruct
      (WTStateRuntimeHeapShapeAt_done_value
        heap' v tout stty_seq HWTSeq)
      as (HTcHeap' & HHeapShape' & HTcVal' & HValShape').
    exists phi_eff1, phi_eff2, phi_seq, stty_eff1, stty_eff2, stty_seq.
    split; [reflexivity |].
    split; [exact HExtEff1 |].
    split; [exact HTcPhiEff1 |].
    split; [exact HExtEff2 |].
    split; [exact HTcPhiEff2 |].
    split; [eapply StoreExtends_trans; eauto |].
    split; [exact HTcHeap' |].
    split; [exact HHeapShape' |].
    split; [exact HTcVal' |].
    split; [exact HValShape' | exact HTcPhiSeq].
Qed.
