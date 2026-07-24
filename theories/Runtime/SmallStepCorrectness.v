From Stdlib Require Import List.
From Stdlib Require Import Sets.Ensembles.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepPairParDispatch.
Require Import theories.Runtime.TraceSemantics.
Require Import theories.Runtime.SmallStepStructuredTrace.
Require Import theories.Runtime.SmallStepEffectSoundness.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.DynamicActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.EffectFacts.
Require Import theories.Meta.TraceTypingFacts.

Lemma DA_in_Phi_in_phi_as_list :
  forall da phi,
    DA_in_Phi da phi ->
    List.In da (phi_as_list phi).
Proof.
  intros da phi HIn.
  induction phi as [| da' | phi1 IHphi1 phi2 IHphi2
                   | phi1 IHphi1 phi2 IHphi2]; simpl in *.
  - inversion HIn.
  - inversion HIn; subst.
    left. reflexivity.
  - inversion HIn; subst.
    match goal with
    | H : DA_in_Phi da phi1 \/ DA_in_Phi da phi2 |- _ =>
        destruct H as [HLeft | HRight]
    end.
    + apply in_or_app. left. now apply IHphi1.
    + apply in_or_app. right. now apply IHphi2.
  - inversion HIn; subst.
    match goal with
    | H : DA_in_Phi da phi1 \/ DA_in_Phi da phi2 |- _ =>
        destruct H as [HLeft | HRight]
    end.
    + apply in_or_app. left. now apply IHphi1.
    + apply in_or_app. right. now apply IHphi2.
Qed.

Lemma In_trace_as_phi_DA_in :
  forall da trace,
    List.In da trace ->
    DA_in_Phi da (trace_as_phi trace).
Proof.
  intros da trace.
  induction trace as [| da' trace IH]; intros HIn.
  - inversion HIn.
  - simpl in *.
    destruct HIn as [HEq | HIn].
    + subst. apply DAP_Seq. left. apply DAP_Trace.
    + apply DAP_Seq. right. now apply IH.
Qed.

Lemma DA_in_Phi_trace_as_phi_phi_as_list :
  forall da phi,
    DA_in_Phi da phi ->
    DA_in_Phi da (trace_as_phi (phi_as_list phi)).
Proof.
  intros da phi HIn.
  apply In_trace_as_phi_DA_in.
  now apply DA_in_Phi_in_phi_as_list.
Qed.

Lemma In_phi_as_list_DA_in :
  forall da phi,
    List.In da (phi_as_list phi) ->
    DA_in_Phi da phi.
Proof.
  intros da phi.
  induction phi as [| da' | phi1 IHphi1 phi2 IHphi2
                   | phi1 IHphi1 phi2 IHphi2]; simpl; intros HIn.
  - inversion HIn.
  - destruct HIn as [HEq | HIn].
    + subst. constructor.
    + inversion HIn.
  - apply in_app_or in HIn.
    destruct HIn as [HIn | HIn].
    + apply DAP_Par. left. now apply IHphi1.
    + apply DAP_Par. right. now apply IHphi2.
  - apply in_app_or in HIn.
    destruct HIn as [HIn | HIn].
    + apply DAP_Seq. left. now apply IHphi1.
    + apply DAP_Seq. right. now apply IHphi2.
Qed.

Lemma ReadOnlyPhi_da_in_read :
  forall phi da,
    ReadOnlyPhi phi ->
    DA_in_Phi da phi ->
    exists r l v, da = DA_Read r l v.
Proof.
  induction phi as [| da' | phi1 IHphi1 phi2 IHphi2
                   | phi1 IHphi1 phi2 IHphi2];
    intros da HReadOnly HIn.
  - inversion HIn.
  - destruct da' as [r l v | r l v | r l v].
    + inversion HReadOnly.
    + inversion HIn; subst. exists r, l, v. reflexivity.
    + inversion HReadOnly.
  - inversion HReadOnly; subst.
    inversion HIn; subst.
    match goal with
    | H : DA_in_Phi da phi1 \/ DA_in_Phi da phi2 |- _ =>
        destruct H as [HLeft | HRight]
    end.
    + eapply IHphi1; eauto.
    + eapply IHphi2; eauto.
  - inversion HReadOnly; subst.
    inversion HIn; subst.
    match goal with
    | H : DA_in_Phi da phi1 \/ DA_in_Phi da phi2 |- _ =>
        destruct H as [HLeft | HRight]
    end.
    + eapply IHphi1; eauto.
    + eapply IHphi2; eauto.
Qed.

Lemma ReadOnlyPhi_of_da_in_read :
  forall phi,
    (forall da, DA_in_Phi da phi -> exists r l v, da = DA_Read r l v) ->
    ReadOnlyPhi phi.
Proof.
  induction phi as [| da | phi1 IHphi1 phi2 IHphi2
                   | phi1 IHphi1 phi2 IHphi2]; intros HAll.
  - constructor.
  - destruct (HAll da (DAP_Trace da)) as (r & l & v & HEq).
    subst. constructor.
  - constructor.
    + apply IHphi1. intros da HIn.
      apply HAll. apply DAP_Par. left. exact HIn.
    + apply IHphi2. intros da HIn.
      apply HAll. apply DAP_Par. right. exact HIn.
  - constructor.
    + apply IHphi1. intros da HIn.
      apply HAll. apply DAP_Seq. left. exact HIn.
    + apply IHphi2. intros da HIn.
      apply HAll. apply DAP_Seq. right. exact HIn.
Qed.

Theorem ReadOnlyPhi_trace_as_phi_phi_as_list :
  forall phi,
    ReadOnlyPhi phi ->
    ReadOnlyPhi (trace_as_phi (phi_as_list phi)).
Proof.
  intros phi HReadOnly.
  apply ReadOnlyPhi_of_da_in_read.
  intros da HIn.
  eapply ReadOnlyPhi_da_in_read; eauto.
  apply In_phi_as_list_DA_in.
  pose proof
    (DA_in_Phi_in_phi_as_list
      da (trace_as_phi (phi_as_list phi)) HIn)
    as HList.
  now rewrite phi_as_list_trace_as_phi in HList.
Qed.

Lemma Epsilon_Phi_Soundness_trace_as_phi_phi_as_list :
  forall phi,
    Epsilon_Phi_Soundness
      (Phi_Static_Effect (trace_as_phi (phi_as_list phi)), phi).
Proof.
  intros phi.
  pose proof
    (Phi_Static_Effect_sound (trace_as_phi (phi_as_list phi))) as HNormSound.
  inversion HNormSound as [? ? HSound]; subst.
  constructor.
  intros da HIn.
  apply HSound.
  now apply DA_in_Phi_trace_as_phi_phi_as_list.
Qed.

Lemma Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list :
  forall eps phi,
    Epsilon_Phi_Soundness
      (eps, trace_as_phi (phi_as_list phi)) ->
    Epsilon_Phi_Soundness (eps, phi).
Proof.
  intros eps phi HSound.
  eapply Epsilon_Phi_Soundness_weaken.
  - eapply Phi_Static_Effect_least; eauto.
  - apply Epsilon_Phi_Soundness_trace_as_phi_phi_as_list.
Qed.

Lemma Phi_Theta_Soundness_da_in :
  forall phi theta da,
    phi ⋞ theta ->
    DA_in_Phi da phi ->
    DA_in_Theta da theta.
Proof.
  induction phi as [| da' | phi1 IHphi1 phi2 IHphi2
                   | phi1 IHphi1 phi2 IHphi2];
    intros theta da HSound HIn;
    inversion HSound; subst; inversion HIn; subst; eauto.
  - match goal with
    | H : DA_in_Phi da phi1 \/ DA_in_Phi da phi2 |- _ =>
        destruct H as [HLeft | HRight]
    end.
    + eapply IHphi1; eauto.
    + eapply IHphi2; eauto.
  - match goal with
    | H : DA_in_Phi da phi1 \/ DA_in_Phi da phi2 |- _ =>
        destruct H as [HLeft | HRight]
    end.
    + eapply IHphi1; eauto.
    + eapply IHphi2; eauto.
Qed.

Lemma Phi_Theta_Soundness_of_da_in :
  forall phi theta,
    (forall da, DA_in_Phi da phi -> DA_in_Theta da theta) ->
    phi ⋞ theta.
Proof.
  induction phi as [| da | phi1 IHphi1 phi2 IHphi2
                   | phi1 IHphi1 phi2 IHphi2];
    intros theta HAll.
  - constructor.
  - constructor. apply HAll. constructor.
  - apply PTS_Par.
    + apply IHphi1. intros da HIn.
      apply HAll. apply DAP_Par. left. exact HIn.
    + apply IHphi2. intros da HIn.
      apply HAll. apply DAP_Par. right. exact HIn.
  - apply PTS_Seq.
    + apply IHphi1. intros da HIn.
      apply HAll. apply DAP_Seq. left. exact HIn.
    + apply IHphi2. intros da HIn.
      apply HAll. apply DAP_Seq. right. exact HIn.
Qed.

Theorem Phi_Theta_Soundness_of_trace_as_phi_phi_as_list :
  forall phi theta,
    trace_as_phi (phi_as_list phi) ⋞ theta ->
    phi ⋞ theta.
Proof.
  intros phi theta HSound.
  apply Phi_Theta_Soundness_of_da_in.
  intros da HIn.
  eapply Phi_Theta_Soundness_da_in.
  - exact HSound.
  - now apply DA_in_Phi_trace_as_phi_phi_as_list.
Qed.

Lemma Phi_Theta_Soundness_of_phi_as_list_nil :
  forall phi theta,
    phi_as_list phi = nil ->
    phi ⋞ theta.
Proof.
  induction phi as [| da | phi1 IHphi1 phi2 IHphi2
                   | phi1 IHphi1 phi2 IHphi2];
    intros theta HNil; simpl in HNil.
  - constructor.
  - discriminate.
  - apply app_eq_nil in HNil as [HNil1 HNil2].
    apply PTS_Par.
    + now apply IHphi1.
    + now apply IHphi2.
  - apply app_eq_nil in HNil as [HNil1 HNil2].
    apply PTS_Seq.
    + now apply IHphi1.
    + now apply IHphi2.
Qed.

Lemma Phi_Theta_Soundness_of_phi_as_list_eq :
  forall phi1 phi2 theta,
    phi_as_list phi1 = phi_as_list phi2 ->
    phi2 ⋞ theta ->
    phi1 ⋞ theta.
Proof.
  intros phi1 phi2 theta HListEq HSound.
  apply Phi_Theta_Soundness_of_da_in.
  intros da HIn.
  eapply Phi_Theta_Soundness_da_in; eauto.
  apply In_phi_as_list_DA_in.
  pose proof (DA_in_Phi_in_phi_as_list da phi1 HIn) as HListIn.
  now rewrite HListEq in HListIn.
Qed.

Lemma Phi_Theta_Soundness_of_phi_as_list_app :
  forall phi phi1 phi2 theta,
    phi_as_list phi = phi_as_list phi1 ++ phi_as_list phi2 ->
    phi1 ⋞ theta ->
    phi2 ⋞ theta ->
    phi ⋞ theta.
Proof.
  intros phi phi1 phi2 theta HListEq HSound1 HSound2.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with (phi2 := Phi_Seq phi1 phi2).
  - simpl. exact HListEq.
  - apply PTS_Seq; assumption.
Qed.

Theorem PairParSourceOrderedEffectSummaryStepsPhi_first_small_step_sound :
  forall heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, static_eff1) ->
    PairParSourceOrderedEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    Epsilon_Phi_Soundness
      (fold_subst_eps rho static_eff1, phi_eff1).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff1 HSummary.
  apply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
  inversion HSummary; subst.
  eapply small_step_effect_summary_eff_sound; eauto.
  eapply StepsPhi_as_steps; eauto.
Qed.

Theorem StepsPhi_effect_summary_readonly_from_small_step_sound :
  forall heap env rho e stty ctxt rgns static_eff phi heap' theta,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, Ty_Effect, static_eff) ->
    StepsPhi
      (initial_state heap env rho e)
      phi
      (StDone heap' (Eff theta)) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff) ->
    ReadOnlyPhi phi.
Proof.
  intros heap env rho e stty ctxt rgns static_eff phi heap' theta
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff
    HSteps HReadOnlyStatic.
  eapply effect_summary_trace_readonly_from_static_soundness; eauto.
  apply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
  eapply small_step_effect_summary_eff_sound; eauto.
  eapply StepsPhi_as_steps; eauto.
Qed.

Theorem StepsPhi_effect_summary_heap_neutral_from_small_step_sound :
  forall heap env rho e stty ctxt rgns static_eff phi heap' theta,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, Ty_Effect, static_eff) ->
    StepsPhi
      (initial_state heap env rho e)
      phi
      (StDone heap' (Eff theta)) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff) ->
    heap' = heap.
Proof.
  intros heap env rho e stty ctxt rgns static_eff phi heap' theta
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff
    HSteps HReadOnlyStatic.
  pose proof
    (StepsPhi_effect_summary_readonly_from_small_step_sound
      heap env rho e stty ctxt rgns static_eff phi heap' theta
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff
      HSteps HReadOnlyStatic)
    as HReadOnly.
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho e)
      phi
      (StDone heap' (Eff theta))
      HSteps HReadOnly)
    as HHeap.
  simpl in HHeap.
  now symmetry.
Qed.

Theorem PairParSourceOrderedEffectSummaryStepsPhi_first_heap_neutral_from_small_step_sound :
  forall heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, static_eff1) ->
    PairParSourceOrderedEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    heap_eff1 = heap.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff1
    HSummary HReadOnlyStatic.
  inversion HSummary; subst.
  eapply StepsPhi_effect_summary_heap_neutral_from_small_step_sound; eauto.
Qed.

Theorem PairParSourceOrderedEffectSummaryStepsPhi_readonly_from_small_step_sound :
  forall heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    static_eff1 static_eff2,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, Ty_Effect, static_eff2) ->
    PairParSourceOrderedEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    ReadOnlyPhi phi_eff1 /\ ReadOnlyPhi phi_eff2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    static_eff1 static_eff2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEff1 HTcEff2 HSummary HReadOnlyStatic1 HReadOnlyStatic2.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HSteps1 HSteps2]; subst.
  pose proof
    (StepsPhi_effect_summary_readonly_from_small_step_sound
      heap env rho (Eff_App ef1 ea1) stty ctxt rgns static_eff1
      phi_eff1 heap_eff1 theta1
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff1
      HSteps1 HReadOnlyStatic1) as HReadOnly1.
  pose proof
    (pairpar_effect_summary_steps_phi_heap_neutral
      heap env rho ef1 ea1 phi_eff1 heap_eff1 theta1
      HSteps1 HReadOnly1) as HHeap1.
  subst heap_eff1.
  pose proof
    (StepsPhi_effect_summary_readonly_from_small_step_sound
      heap env rho (Eff_App ef2 ea2) stty ctxt rgns static_eff2
      phi_eff2 heap_eff2 theta2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff2
      HSteps2 HReadOnlyStatic2) as HReadOnly2.
  split; assumption.
Qed.

Theorem PairParSourceOrderedEffectSummaryStepsPhi_readonly_heap_neutral_from_small_step_sound :
  forall heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    static_eff1 static_eff2,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, Ty_Effect, static_eff2) ->
    PairParSourceOrderedEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    heap_eff1 = heap /\ heap_eff2 = heap.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    static_eff1 static_eff2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEff1 HTcEff2 HSummary HReadOnlyStatic1 HReadOnlyStatic2.
  destruct
    (PairParSourceOrderedEffectSummaryStepsPhi_readonly_from_small_step_sound
      heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
      static_eff1 static_eff2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEff1 HTcEff2 HSummary HReadOnlyStatic1 HReadOnlyStatic2)
    as [HReadOnly1 HReadOnly2].
  eapply PairParSourceOrderedEffectSummaryStepsPhi_readonly_heap_neutral;
    eauto.
Qed.

Theorem PairParEffectSummaryStepsPhi_readonly_from_small_step_sound :
  forall heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    static_eff1 static_eff2,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, Ty_Effect, static_eff2) ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    ReadOnlyPhi phi_eff1 /\ ReadOnlyPhi phi_eff2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    static_eff1 static_eff2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEff1 HTcEff2 HSummary HReadOnlyStatic1 HReadOnlyStatic2.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HSteps1 HSteps2]; subst.
  split.
  - eapply
      (StepsPhi_effect_summary_readonly_from_small_step_sound
        heap env rho (Eff_App ef1 ea1) stty ctxt rgns static_eff1
        phi_eff1 heap_eff1 theta1); eauto.
  - eapply
      (StepsPhi_effect_summary_readonly_from_small_step_sound
        heap env rho (Eff_App ef2 ea2) stty ctxt rgns static_eff2
        phi_eff2 heap_eff2 theta2); eauto.
Qed.

Lemma TcExp_mu_app_summary_readonly :
  forall ctxt rgns rho ef ea ty static,
    TcExp (ctxt, rgns, Mu_App ef ea, ty, static) ->
    exists static_eff,
      TcExp (ctxt, rgns, Eff_App ef ea, Ty_Effect, static_eff) /\
      ReadOnlyStatic (fold_subst_eps rho static_eff).
Proof.
  intros ctxt rgns rho ef ea ty static HTcMu.
  inversion HTcMu; subst.
  match goal with
  | HBackAll : forall rho0,
      BackTriangle (ctxt, rgns, rho0, Mu_App ef ea, Eff_App ef ea) |- _ =>
      pose proof (HBackAll rho) as HBack
  end.
  inversion HBack; subst; try solve [discriminate].
  exists static_ee.
  split.
  - inversion H11; subst. exact H11.
  - exact H12.
Qed.

Lemma PairParEffectSummaryStepsPhi_readonly_from_pairpar_typed :
  forall heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns ty static
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty, static) ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyPhi phi_eff1 /\ ReadOnlyPhi phi_eff2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns ty static
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcPair HSummary.
  inversion HTcPair; subst.
  match goal with
  | HMu1 : TcExp (ctxt, rgns, Mu_App ef1 ea1, _, _),
    HMu2 : TcExp (ctxt, rgns, Mu_App ef2 ea2, _, _) |- _ =>
      destruct (TcExp_mu_app_summary_readonly
        ctxt rgns rho ef1 ea1 _ _ HMu1)
        as (static_eff1 & HTcEff1 & HReadOnly1);
      destruct (TcExp_mu_app_summary_readonly
        ctxt rgns rho ef2 ea2 _ _ HMu2)
        as (static_eff2 & HTcEff2 & HReadOnly2);
      exact
        (PairParEffectSummaryStepsPhi_readonly_from_small_step_sound
          heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
          phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
          static_eff1 static_eff2
          HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
          HTcEff1 HTcEff2 HSummary HReadOnly1 HReadOnly2)
  end.
Qed.

Theorem PairParEffectSummaryStepsPhi_static_trace_soundness :
  forall heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    static_eff1 static_eff2,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, Ty_Effect, static_eff2) ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    Epsilon_Phi_Soundness (fold_subst_eps rho static_eff1, phi_eff1) /\
    Epsilon_Phi_Soundness (fold_subst_eps rho static_eff2, phi_eff2).
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    static_eff1 static_eff2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEff1 HTcEff2 HSummary.
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HSteps1 HSteps2]; subst.
  split.
  - apply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_effect_summary_eff_sound; eauto.
    eapply StepsPhi_as_steps; eauto.
  - apply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_effect_summary_eff_sound; eauto.
    eapply StepsPhi_as_steps; eauto.
Qed.

Theorem PairParEffectSummaryStepsPhi_readonly_heap_neutral_from_small_step_sound :
  forall heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    static_eff1 static_eff2,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, Ty_Effect, static_eff2) ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    heap_eff1 = heap /\ heap_eff2 = heap.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
    static_eff1 static_eff2
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HTcEff1 HTcEff2 HSummary HReadOnlyStatic1 HReadOnlyStatic2.
  destruct
    (PairParEffectSummaryStepsPhi_readonly_from_small_step_sound
      heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
      static_eff1 static_eff2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEff1 HTcEff2 HSummary HReadOnlyStatic1 HReadOnlyStatic2)
    as [HReadOnly1 HReadOnly2].
  inversion HSummary as
    [phi_eff1' phi_eff2' heap_eff1' heap_eff2' theta1' theta2'
      HSteps1 HSteps2]; subst.
  split.
  - eapply pairpar_effect_summary_steps_phi_heap_neutral; eauto.
  - eapply pairpar_effect_summary_steps_phi_heap_neutral; eauto.
Qed.

Theorem PairParSourceOrderedEffectSummaryStepsPhi_source_pass_small_step_sound_prefix :
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, static_eff1) ->
    PairParSourceOrderedEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    PairParCheckPass theta1 theta2 ->
    exists phi_source,
      PairParEffectSummaryStepsPhi
        heap env rho ef1 ea1 ef2 ea2
        phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
      StepsPhi
        (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k)
        phi_source
        (pairpar_checked_run_start heap_eff2 env rho ef1 ea1 ef2 ea2 k) /\
      phi_as_list phi_source =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff1
    HSummary HReadOnlyStatic HPass.
  eapply PairParSourceOrderedEffectSummaryStepsPhi_source_pass_static_sound_prefix;
    eauto.
  eapply PairParSourceOrderedEffectSummaryStepsPhi_first_small_step_sound; eauto.
Qed.

Theorem PairParSourceOrderedEffectSummaryStepsPhi_source_fail_small_step_sound_prefix :
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, static_eff1) ->
    PairParSourceOrderedEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    PairParCheckFail theta1 theta2 ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 /\
    PairParCheckState
      (pairpar_check_state heap_eff2 env rho ef1 ea1 ef2 ea2 theta1 theta2 k) /\
    forall label state',
      ~ Step
        (pairpar_check_state heap_eff2 env rho ef1 ea1 ef2 ea2 theta1 theta2 k)
        label state'.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff1
    HSummary HReadOnlyStatic HFail.
  eapply PairParSourceOrderedEffectSummaryStepsPhi_source_fail_static_sound_prefix;
    eauto.
  eapply PairParSourceOrderedEffectSummaryStepsPhi_first_small_step_sound; eauto.
Qed.

Lemma PairParStepsPhi_state_done_trace_nil :
  forall heap v phi_state phi_left phi_right state',
    PairParStepsPhi
      (PPS_State (StDone heap v))
      phi_state phi_left phi_right state' ->
    phi_as_list phi_state = nil.
Proof.
  intros heap v phi_state phi_left phi_right state' HSteps.
  remember (PPS_State (StDone heap v)) as state eqn:HState.
  induction HSteps; inversion HState; subst.
  - reflexivity.
  - exfalso.
    eapply done_no_step; eauto.
Qed.

Lemma PairParStepsPhi_state_return_done_trace_nil :
  forall heap v phi_state phi_left phi_right state',
    PairParStepsPhi
      (PPS_State (StReturn heap v KDone))
      phi_state phi_left phi_right state' ->
    phi_as_list phi_state = nil.
Proof.
  intros heap v phi_state phi_left phi_right state' HSteps.
  inversion HSteps; subst; try discriminate.
  - reflexivity.
  - match goal with
    | HStep : Step _ _ _ |- _ =>
        inversion HStep; subst; simpl;
        eapply PairParStepsPhi_state_done_trace_nil; eauto
    end.
Qed.

Lemma PairParStepsPhi_run_kdone_terminal_state_trace_nil :
  forall left_state right_state
    phi_state phi_left phi_right heap' v,
    PairParStepsPhi
      (PPS_Run left_state right_state KDone)
      phi_state phi_left phi_right
      (PPS_State (StDone heap' v)) ->
    phi_as_list phi_state = nil.
Proof.
  intros left_state right_state
    phi_state phi_left phi_right heap' v HSteps.
  remember (PPS_Run left_state right_state KDone) as run_state eqn:HRun.
  revert left_state right_state HRun.
  induction HSteps; intros left_state0 right_state0 HRun;
    inversion HRun; subst.
  - reflexivity.
  - match goal with
    | IH : forall left_state right_state,
        PPS_Run _ _ KDone = PPS_Run left_state right_state KDone ->
        phi_as_list _ = nil |- _ =>
        eapply IH; reflexivity
    end.
  - match goal with
    | IH : forall left_state right_state,
        PPS_Run _ _ KDone = PPS_Run left_state right_state KDone ->
        phi_as_list _ = nil |- _ =>
        eapply IH; reflexivity
    end.
  - eapply PairParStepsPhi_state_return_done_trace_nil; eauto.
Qed.

Lemma PairParStepsPhi_top_terminal_state_trace_nil :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_state phi_left phi_right heap' v,
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_state phi_left phi_right
      (PPS_State (StDone heap' v)) ->
    phi_as_list phi_state = nil.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_state phi_left phi_right heap' v HSteps.
  unfold pairpar_checked_start, pairpar_checked_initial in HSteps.
  eapply PairParStepsPhi_run_kdone_terminal_state_trace_nil
    with
      (left_state :=
      (initial_state heap env rho (Mu_App ef1 ea1))
      )
      (right_state :=
      (initial_state heap env rho (Mu_App ef2 ea2))
      );
    eauto.
Qed.

Theorem PairParCheckedStructuredStepsPhi_top_sound_with_branch_summaries :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v,
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
	    phi_mu1 ⋞ theta1 ->
	    phi_mu2 ⋞ theta2 ->
	    pairpar_checked_structured_trace
	      phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
	      ⋞ Theta_Top.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    _ _ _ _ _.
  apply PhiInThetaTop.
Qed.

Theorem PairParCheckedStructuredStepsPhi_top_sound :
  forall heap env rho ef1 ea1 ef2 ea2
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v,
    phi =
      pairpar_checked_structured_trace
        phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2 ->
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
    PairParStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
	    phi_mu1 ⋞ theta1 ->
	    phi_mu2 ⋞ theta2 ->
	    phi ⋞ Theta_Top.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi phi_eff1 phi_eff2 phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    HTrace HSummary HPass HSteps HSoundMu1 HSoundMu2.
  subst.
  eapply PairParCheckedStructuredStepsPhi_top_sound_with_branch_summaries;
    eauto.
Qed.

Lemma PairParLoosePackedStepsPhi_sched_sound :
  forall state phi_sched phi_state phi_left phi_right state'
    theta_state theta_left theta_right,
    PairParLoosePackedStepsPhi
      state phi_sched phi_state phi_left phi_right state' ->
    phi_state ⋞ theta_state ->
    phi_left ⋞ theta_left ->
    phi_right ⋞ theta_right ->
    phi_sched ⋞ Union_Theta theta_state
      (Union_Theta theta_left theta_right).
Proof.
  intros state phi_sched phi_state phi_left phi_right state'
    theta_state theta_left theta_right HSteps.
  induction HSteps; intros HStateSound HLeftSound HRightSound.
  - apply PTS_Nil.
  - inversion HStateSound; subst.
    apply PTS_Seq.
    + apply Theta_introl. assumption.
    + eauto.
  - inversion HLeftSound; subst.
    apply PTS_Seq.
    + apply Theta_intror.
      apply Theta_introl.
      assumption.
    + eauto.
  - inversion HRightSound; subst.
    apply PTS_Seq.
    + apply Theta_intror.
      apply Theta_intror.
      assumption.
    + eauto.
  - apply PTS_Seq.
    + apply PTS_Nil.
    + eauto.
Qed.

Lemma PairParLoosePackedStepsPhi_state_done_trace_nil :
  forall heap v phi_sched phi_state phi_left phi_right state',
    PairParLoosePackedStepsPhi
      (PPS_State (StDone heap v))
      phi_sched
      phi_state
      phi_left
      phi_right
      state' ->
    phi_as_list phi_state = nil.
Proof.
  intros heap v phi_sched phi_state phi_left phi_right state' HSteps.
  remember (PPS_State (StDone heap v)) as state eqn:HState.
  induction HSteps; inversion HState; subst.
  - reflexivity.
  - exfalso.
    eapply done_no_step; eauto.
Qed.

Lemma PairParLoosePackedStepsPhi_state_return_done_trace_nil :
  forall heap v phi_sched phi_state phi_left phi_right state',
    PairParLoosePackedStepsPhi
      (PPS_State (StReturn heap v KDone))
      phi_sched
      phi_state
      phi_left
      phi_right
      state' ->
    phi_as_list phi_state = nil.
Proof.
  intros heap v phi_sched phi_state phi_left phi_right state' HSteps.
  inversion HSteps; subst; try discriminate.
  - reflexivity.
  - match goal with
    | HStep : Step _ _ _ |- _ =>
        inversion HStep; subst; simpl;
        eapply PairParLoosePackedStepsPhi_state_done_trace_nil; eauto
    end.
Qed.

Lemma PairParLoosePackedStepsPhi_state_done_branches_nil :
  forall heap v phi_sched phi_state phi_left phi_right state',
    PairParLoosePackedStepsPhi
      (PPS_State (StDone heap v))
      phi_sched
      phi_state
      phi_left
      phi_right
      state' ->
    phi_left = Phi_Nil /\ phi_right = Phi_Nil.
Proof.
  intros heap v phi_sched phi_state phi_left phi_right state' HSteps.
  remember (PPS_State (StDone heap v)) as state eqn:HState.
  induction HSteps; inversion HState; subst.
  - split; reflexivity.
  - exfalso.
    eapply done_no_step; eauto.
Qed.

Lemma PairParLoosePackedStepsPhi_state_return_kdone_branches_nil :
  forall heap v phi_sched phi_state phi_left phi_right state',
    PairParLoosePackedStepsPhi
      (PPS_State (StReturn heap v KDone))
      phi_sched
      phi_state
      phi_left
      phi_right
      state' ->
    phi_left = Phi_Nil /\ phi_right = Phi_Nil.
Proof.
  intros heap v phi_sched phi_state phi_left phi_right state' HSteps.
  inversion HSteps; subst; try discriminate.
  - split; reflexivity.
  - match goal with
    | HStep : Step _ _ _ |- _ =>
        inversion HStep; subst;
        eapply PairParLoosePackedStepsPhi_state_done_branches_nil; eauto
    end.
Qed.

Lemma PairParLoosePackedStepsPhi_state_done_replays_heap :
  forall heap v phi_sched phi_state phi_left phi_right state',
    PairParLoosePackedStepsPhi
      (PPS_State (StDone heap v))
      phi_sched
      phi_state
      phi_left
      phi_right
      state' ->
    (phi_state, heap) ==>* (Phi_Nil, pairpar_state_heap state').
Proof.
  intros heap v phi_sched phi_state phi_left phi_right state' HSteps.
  remember (PPS_State (StDone heap v)) as state eqn:HState.
  induction HSteps; inversion HState; subst.
  - exists 0. constructor.
  - exfalso.
    eapply done_no_step; eauto.
Qed.

Lemma PairParLoosePackedStepsPhi_state_return_kdone_replays_heap :
  forall heap v phi_sched phi_state phi_left phi_right state',
    PairParLoosePackedStepsPhi
      (PPS_State (StReturn heap v KDone))
      phi_sched
      phi_state
      phi_left
      phi_right
      state' ->
    (phi_state, heap) ==>* (Phi_Nil, pairpar_state_heap state').
Proof.
  intros heap v phi_sched phi_state phi_left phi_right state' HSteps.
  inversion HSteps; subst; try discriminate.
  - exists 0. constructor.
  - match goal with
    | HStep : Step _ _ _ |- _ =>
        inversion HStep; subst; simpl
    end.
    eapply structured_phi_seq_steps.
    + exists 0. constructor.
    + eapply PairParLoosePackedStepsPhi_state_done_replays_heap; eauto.
Qed.

Lemma PairParLoosePackedStepsPhi_run_kdone_terminal_state_trace_nil :
  forall left_state right_state phi_sched phi_state phi_left phi_right heap' v,
    PairParLoosePackedStepsPhi
      (PPS_Run left_state right_state KDone)
      phi_sched
      phi_state
      phi_left
      phi_right
      (PPS_State (StDone heap' v)) ->
    phi_as_list phi_state = nil.
Proof.
  intros left_state right_state
    phi_sched phi_state phi_left phi_right heap' v HSteps.
  remember (PPS_Run left_state right_state KDone) as run_state eqn:HRun.
  revert left_state right_state HRun.
  induction HSteps; intros left_state0 right_state0 HRun;
    inversion HRun; subst.
  - reflexivity.
  - match goal with
    | IH : forall left_state right_state,
        PPS_Run _ _ KDone = PPS_Run left_state right_state KDone ->
        phi_as_list _ = nil |- _ =>
        eapply IH; reflexivity
    end.
  - match goal with
    | IH : forall left_state right_state,
        PPS_Run _ _ KDone = PPS_Run left_state right_state KDone ->
        phi_as_list _ = nil |- _ =>
        eapply IH; reflexivity
    end.
  - eapply PairParLoosePackedStepsPhi_state_return_done_trace_nil; eauto.
Qed.

Theorem PairParLoosePackedStepsPhi_run_kdone_split_replays_heap :
  forall left_state right_state phi_sched phi_state phi_left phi_right heap' v,
    state_heap left_state = state_heap right_state ->
    PairParLoosePackedStepsPhi
      (PPS_Run left_state right_state KDone)
      phi_sched
      phi_state
      phi_left
      phi_right
      (PPS_State (StDone heap' v)) ->
    exists heap_mid,
      (Phi_Par phi_left phi_right, state_heap left_state)
        ==>* (Phi_Nil, heap_mid) /\
      (phi_state, heap_mid) ==>* (Phi_Nil, heap').
Proof.
  intros left_state right_state phi_sched phi_state phi_left phi_right
    heap' v HAgree HSteps.
  remember (PPS_Run left_state right_state KDone) as run_state eqn:HRun.
  remember (PPS_State (StDone heap' v)) as final_state eqn:HFinal.
  revert left_state right_state heap' v HAgree HRun HFinal.
  induction HSteps;
    intros left_state0 right_state0 heap_final v_final
      HAgree HRun HFinal;
    inversion HRun; subst; try discriminate.
  - destruct
      (IHHSteps left' (with_state_heap (state_heap left') right_state0)
        heap_final v_final)
      as (heap_mid & HParRest & HStateRest).
    + rewrite state_heap_with_state_heap. reflexivity.
    + reflexivity.
    + reflexivity.
    + exists heap_mid. split.
      * eapply structured_phi_par_prefix_left.
        -- eapply step_label_phi_replays_heap; eauto.
        -- exact HParRest.
      * exact HStateRest.
  - destruct
      (IHHSteps (with_state_heap (state_heap right') left_state0) right'
        heap_final v_final)
      as (heap_mid & HParRest & HStateRest).
    + rewrite state_heap_with_state_heap. reflexivity.
    + reflexivity.
    + reflexivity.
    + exists heap_mid. split.
      * eapply structured_phi_par_prefix_right.
        -- rewrite HAgree.
           eapply step_label_phi_replays_heap; eauto.
        -- rewrite state_heap_with_state_heap in HParRest.
           exact HParRest.
      * exact HStateRest.
  - destruct
      (PairParLoosePackedStepsPhi_state_return_kdone_branches_nil
        heap (Pair (v1, v2)) phi_sched phi_state phi_left phi_right
        (PPS_State (StDone heap_final v_final)) HSteps)
      as (HLeftNil & HRightNil).
    subst.
    exists heap. split.
    + simpl.
      eapply structured_phi_par_steps.
      * exists 0. constructor.
      * exists 0. constructor.
    + exact
        (PairParLoosePackedStepsPhi_state_return_kdone_replays_heap
          heap (Pair (v1, v2)) phi_sched phi_state Phi_Nil Phi_Nil
          (PPS_State (StDone heap_final v_final)) HSteps).
Qed.

Lemma PairParLoosePackedStepsPhi_state_done_terminal_value :
  forall heap v phi_sched phi_state phi_left phi_right heap' v',
    PairParLoosePackedStepsPhi
      (PPS_State (StDone heap v))
      phi_sched
      phi_state
      phi_left
      phi_right
      (PPS_State (StDone heap' v')) ->
    v' = v.
Proof.
  intros heap v phi_sched phi_state phi_left phi_right heap' v' HSteps.
  inversion HSteps; subst; try discriminate.
  - reflexivity.
  - exfalso.
    eapply done_no_step; eauto.
Qed.

Lemma PairParLoosePackedStepsPhi_state_return_kdone_terminal_value :
  forall heap v phi_sched phi_state phi_left phi_right heap' v',
    PairParLoosePackedStepsPhi
      (PPS_State (StReturn heap v KDone))
      phi_sched
      phi_state
      phi_left
      phi_right
      (PPS_State (StDone heap' v')) ->
    v' = v.
Proof.
  intros heap v phi_sched phi_state phi_left phi_right heap' v' HSteps.
  inversion HSteps; subst; try discriminate.
  match goal with
  | HStep : Step _ _ _ |- _ =>
      inversion HStep; subst
  end.
  eapply PairParLoosePackedStepsPhi_state_done_terminal_value; eauto.
Qed.

Lemma PairParLoosePackedStepsPhi_run_kdone_terminal_pair_value :
  forall left_state right_state phi_sched phi_state phi_left phi_right heap' v,
    PairParLoosePackedStepsPhi
      (PPS_Run left_state right_state KDone)
      phi_sched
      phi_state
      phi_left
      phi_right
      (PPS_State (StDone heap' v)) ->
    exists v1 v2, v = Pair (v1, v2).
Proof.
  intros left_state right_state phi_sched phi_state phi_left phi_right
    heap' v HSteps.
  remember (PPS_Run left_state right_state KDone) as run_state eqn:HRun.
  remember (PPS_State (StDone heap' v)) as final_state eqn:HFinal.
  revert left_state right_state heap' v HRun HFinal.
  induction HSteps;
    intros left_state0 right_state0 heap_final v_final HRun HFinal;
    inversion HRun; subst; try discriminate.
  - eapply IHHSteps; reflexivity.
  - eapply IHHSteps; reflexivity.
  - pose proof
      (PairParLoosePackedStepsPhi_state_return_kdone_terminal_value
        heap (Pair (v1, v2)) phi_sched phi_state phi_left phi_right
        heap_final v_final HSteps)
      as HVal.
    subst.
    exists v1, v2. reflexivity.
Qed.

Theorem PairParLoosePackedStepsPhi_checked_kdone_split_replays_heap :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_sched phi_state phi_left phi_right heap' v,
    PairParLoosePackedStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_sched
      phi_state
      phi_left
      phi_right
      (PPS_State (StDone heap' v)) ->
    exists heap_mid,
      (Phi_Par phi_left phi_right, heap) ==>* (Phi_Nil, heap_mid) /\
      (phi_state, heap_mid) ==>* (Phi_Nil, heap').
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_sched phi_state phi_left phi_right heap' v HSteps.
  unfold pairpar_checked_start, pairpar_checked_initial in HSteps.
  change heap with
    (state_heap (initial_state heap env rho (Mu_App ef1 ea1))).
  eapply
    (PairParLoosePackedStepsPhi_run_kdone_split_replays_heap
      (initial_state heap env rho (Mu_App ef1 ea1))
      (initial_state heap env rho (Mu_App ef2 ea2))
      phi_sched phi_state phi_left phi_right heap' v).
  - reflexivity.
  - exact HSteps.
Qed.

Lemma PairParLoosePackedStepsPhi_top_terminal_state_trace_nil :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_sched phi_state phi_left phi_right heap' v,
    PairParLoosePackedStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_sched
      phi_state
      phi_left
      phi_right
      (PPS_State (StDone heap' v)) ->
    phi_as_list phi_state = nil.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_sched phi_state phi_left phi_right heap' v HSteps.
  unfold pairpar_checked_start, pairpar_checked_initial in HSteps.
  eapply PairParLoosePackedStepsPhi_run_kdone_terminal_state_trace_nil
    with
      (left_state :=
      (initial_state heap env rho (Mu_App ef1 ea1))
      )
      (right_state :=
      (initial_state heap env rho (Mu_App ef2 ea2))
      );
    eauto.
Qed.

Theorem PairParLoosePackedStepsPhi_top_sound_with_branch_summaries :
  forall heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 phi_mu phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v,
    PairParEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    PairParCheckPass theta1 theta2 ->
    PairParLoosePackedStepsPhi
      (pairpar_checked_start heap env rho ef1 ea1 ef2 ea2 KDone)
      phi_mu
      phi_mu_state
      phi_mu1
      phi_mu2
      (PPS_State (StDone heap' v)) ->
	    phi_mu1 ⋞ theta1 ->
	    phi_mu2 ⋞ theta2 ->
	    pairpar_checked_packed_structured_trace
	      phi_eff1 phi_eff2 phi_mu
	      ⋞ Theta_Top.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2
    phi_eff1 phi_eff2 phi_mu phi_mu_state phi_mu1 phi_mu2
    heap_eff1 theta1 heap_eff2 theta2 heap' v
    _ _ _ _ _.
  apply PhiInThetaTop.
Qed.
