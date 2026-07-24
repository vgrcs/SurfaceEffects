From Stdlib Require Import List.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.Typing.
Require Import theories.NewSmallStep.Typing.Types.

Import ListNotations.

Definition NProgressState (state : NState) : Prop :=
  NTerminal state \/ exists label state', NStep state label state'.

Theorem NStep_progress :
  forall gamma omega state,
    NWTState gamma omega state ->
    NProgressState state.
Proof.
  intros gamma omega state HWT.
  unfold NProgressState.
  inversion HWT as
    [gamma0 omega0 heap env rho e k ty eff
      HHeap HEnv HRho HTc HK
    | gamma0 omega0 heap rho v k ty
      HHeap HRho HV HK
    | gamma0 omega0 heap v rho ty
      HHeap HRho HV];
    subst; clear HWT.
  - right.
    inversion HTc; subst;
      try solve [
        eexists; eexists; constructor
      ].
    + destruct
        (NEnvHasType_lookup rho heap env gamma x ty HEnv H)
        as (v_lookup & HLookup & _).
      exists LSilent, (StReturn heap v_lookup k).
      eapply StepVar. exact HLookup.
    + destruct
        (NRhoModels_eval_region omega rho r HRho H)
        as (r_val & HRgn).
      exists LSilent, (StEval heap env rho e0 (KRef r_val k)).
      eapply StepRef. exact HRgn.
    + destruct
        (NRhoModels_eval_region omega rho r HRho H)
        as (r_val & HRgn).
      exists LSilent, (StReturn heap (VSummary (SummarySet [CAllocAbs r_val])) k).
      eapply StepAllocAbs. exact HRgn.
    + destruct
        (NRhoModels_eval_region omega rho r HRho H)
        as (r_val & HRgn).
      exists LSilent, (StReturn heap (VSummary (SummarySet [CReadAbs r_val])) k).
      eapply StepReadAbs. exact HRgn.
    + destruct
        (NRhoModels_eval_region omega rho r HRho H)
        as (r_val & HRgn).
      exists LSilent, (StReturn heap (VSummary (SummarySet [CWriteAbs r_val])) k).
      eapply StepWriteAbs. exact HRgn.
  - right.
    inversion HK; subst.
    + exists LSilent, (StDone heap v). constructor.
    + inversion HV; subst.
      eexists; eexists.
      constructor.
    + eexists; eexists.
      constructor.
    + inversion HV; subst.
      eexists; eexists.
      constructor.
    + eexists; eexists.
      constructor.
    + inversion HV; subst.
      destruct
        (NRhoModels_eval_region omega rho r HRho H)
        as (r_val & HRgn).
      eexists; eexists.
      eapply StepRgnAppReturn. exact HRgn.
    + inversion HV; subst.
      destruct b.
      * eexists; eexists. constructor.
      * eexists; eexists. constructor.
    + destruct (heap_alloc r_val v heap) as (l & heap') eqn:HAlloc.
      eexists; eexists.
      eapply StepRefReturn. exact HAlloc.
    + inversion HV; subst.
      eexists; eexists.
      eapply StepDerefReturn. eassumption.
    + inversion HV; subst.
      eexists; eexists.
      constructor.
    + match goal with
      | HLoc : NValHasType _ _ _ (TyRef _ _) |- _ =>
          inversion HLoc; subst
      end.
      eexists; eexists.
      constructor.
    + inversion HV; subst.
      eexists; eexists.
      constructor.
    + inversion HV; subst.
      eexists; eexists.
      constructor.
    + inversion HV; subst.
      eexists; eexists.
      constructor.
    + inversion HV; subst.
      eexists; eexists.
      constructor.
    + inversion HV; subst.
      eexists; eexists.
      constructor.
    + inversion HV; subst.
      eexists; eexists.
      constructor.
    + inversion HV; subst.
      eexists; eexists.
      constructor.
    + inversion HV; subst.
      eexists; eexists.
      constructor.
    + inversion HV; subst.
      eexists; eexists.
      constructor.
    + inversion HV; subst.
      eexists; eexists.
      constructor.
    + inversion HV; subst.
      eexists; eexists.
      constructor.
    + inversion HV; subst.
      eexists; eexists.
      constructor.
  - left. constructor.
Qed.
