From Stdlib Require Import List.
From Stdlib Require Import Sets.Ensembles.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepSequentialSoundness.
Require Import theories.Runtime.SmallStepStructuredTrace.
Require Import theories.Runtime.SmallStepEffectSoundness.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
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

Theorem PairParSequentialEffectSummaryStepsPhi_first_small_step_sound :
  forall heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, static_eff1) ->
    PairParSequentialEffectSummaryStepsPhi
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

Theorem PairParSequentialEffectSummaryStepsPhi_first_heap_neutral_from_small_step_sound :
  forall heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, static_eff1) ->
    PairParSequentialEffectSummaryStepsPhi
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

Theorem PairParSequentialEffectSummaryStepsPhi_readonly_from_small_step_sound :
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
    PairParSequentialEffectSummaryStepsPhi
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

Theorem PairParSequentialEffectSummaryStepsPhi_readonly_heap_neutral_from_small_step_sound :
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
    PairParSequentialEffectSummaryStepsPhi
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
    (PairParSequentialEffectSummaryStepsPhi_readonly_from_small_step_sound
      heap env rho ef1 ea1 ef2 ea2 stty ctxt rgns
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2
      static_eff1 static_eff2
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HTcEff1 HTcEff2 HSummary HReadOnlyStatic1 HReadOnlyStatic2)
    as [HReadOnly1 HReadOnly2].
  eapply PairParSequentialEffectSummaryStepsPhi_readonly_heap_neutral;
    eauto.
Qed.

Theorem PairParSequentialEffectSummaryStepsPhi_source_pass_small_step_sound_prefix :
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, static_eff1) ->
    PairParSequentialEffectSummaryStepsPhi
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
        (pairpar_sequential_start heap_eff2 env rho ef1 ea1 ef2 ea2 k) /\
      phi_as_list phi_source =
        phi_as_list phi_eff1 ++ phi_as_list phi_eff2.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff1
    HSummary HReadOnlyStatic HPass.
  eapply PairParSequentialEffectSummaryStepsPhi_source_pass_static_sound_prefix;
    eauto.
  eapply PairParSequentialEffectSummaryStepsPhi_first_small_step_sound; eauto.
Qed.

Theorem PairParSequentialEffectSummaryStepsPhi_source_fail_small_step_sound_prefix :
  forall heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1,
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, Ty_Effect, static_eff1) ->
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
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
  intros heap env rho ef1 ea1 ef2 ea2 k stty ctxt rgns
    phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 static_eff1
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEff1
    HSummary HReadOnlyStatic HFail.
  eapply PairParSequentialEffectSummaryStepsPhi_source_fail_static_sound_prefix;
    eauto.
  eapply PairParSequentialEffectSummaryStepsPhi_first_small_step_sound; eauto.
Qed.
