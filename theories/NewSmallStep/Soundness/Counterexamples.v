From Stdlib Require Import List.
From Stdlib Require Import Ascii.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.Trace.
Require Import theories.NewSmallStep.Soundness.Correctness.
Require Import theories.NewSmallStep.Typing.Judgments.
Require Import theories.NewSmallStep.Typing.Regularity.
Require Import theories.NewSmallStep.Typing.Resolve.
Require Import theories.NewSmallStep.Typing.Types.

Import ListNotations.
Open Scope list_scope.
Open Scope char_scope.

Definition counter_x : VarId := "x"%char.

Definition counter_gamma : NCtx :=
  [(counter_x, TyRef (region_const_type 0) TyNat)].

Definition counter_env : NEnv :=
  EnvCons counter_x (VLoc 1 0) EnvNil.

Definition counter_heap : Heap :=
  [(1, 0, VNat 7)].

Definition counter_expr : NExpr :=
  EDeref (region_const_expr 0) (EVar counter_x).

Definition counter_summary : NExpr :=
  EConcat EEmpty (EReadAbs (region_const_expr 0)).

Definition counter_ty : NTy :=
  TyRef (region_const_type 0) TyNat.

Lemma counter_var_typed :
  NTcExp counter_gamma [] (EVar counter_x)
    counter_ty [].
Proof.
  apply NT_Var.
  reflexivity.
Qed.

Lemma counter_ty_wf :
  NTyWF [] counter_ty.
Proof.
  unfold counter_ty, NTyWF.
  eapply NTyWF_Ref.
  - constructor.
  - constructor.
Qed.

Lemma counter_gamma_wf :
  NCtxWF [] counter_gamma.
Proof.
  unfold counter_gamma, counter_ty, NCtxWF.
  constructor.
  - exact counter_ty_wf.
  - constructor.
Qed.

Lemma counter_var_checked :
  NCheckedTcExp counter_gamma [] (EVar counter_x)
    counter_ty [].
Proof.
  eapply NCheckedTcExp_intro.
  - exact counter_var_typed.
  - unfold NRgnCtxWF. constructor.
  - exact counter_gamma_wf.
  - exact counter_ty_wf.
  - unfold NStaticEffectWF, NStaticEffectWFAt. constructor.
  - apply NCTS_Var. reflexivity.
Qed.

Lemma counter_expr_typed :
  NTcExp counter_gamma [] counter_expr TyNat
    [SRead (region_const_type 0)].
Proof.
  unfold counter_expr.
  apply NT_Deref.
  - apply REWF_Const.
  - exact counter_var_typed.
Qed.

Lemma counter_expr_checked :
  NCheckedTcExp counter_gamma [] counter_expr TyNat
    [SRead (region_const_type 0)].
Proof.
  eapply NCheckedTcExp_intro.
  - exact counter_expr_typed.
  - unfold NRgnCtxWF. constructor.
  - exact counter_gamma_wf.
  - unfold NTyWF. constructor.
  - unfold NStaticEffectWF, NStaticEffectWFAt.
    constructor.
    + constructor. constructor.
    + constructor.
  - unfold counter_expr.
    apply NCTS_Deref.
    + apply REWF_Const.
    + exact counter_var_checked.
Qed.

Lemma counter_backtriangle :
  NCheckedBackTriangle counter_gamma [] counter_expr counter_summary.
Proof.
  unfold counter_expr, counter_summary.
  eapply NCBT_Deref with
    (ty := counter_ty)
    (static := [])
    (ty_deref := TyNat)
    (eff_deref := [SRead (region_const_type 0)]).
  - exact counter_var_checked.
  - exact counter_expr_checked.
  - refine (NCBT_Var counter_gamma [] counter_x counter_ty _).
    exact counter_var_checked.
Qed.

Lemma counter_computation :
  ComputationEvaluation
    counter_heap counter_env empty_rho counter_expr
    [DRead 1 0] counter_heap (VNat 7).
Proof.
  unfold ComputationEvaluation, counter_expr, counter_heap, counter_env,
    counter_x.
  change [DRead 1 0] with (label_trace LSilent ++ [DRead 1 0]).
  eapply StepsStep.
  - apply StepDeref.
  - change [DRead 1 0] with (label_trace LSilent ++ [DRead 1 0]).
    eapply StepsStep.
    + apply StepVar.
      reflexivity.
    + change [DRead 1 0] with
        (label_trace (LAction (DRead 1 0)) ++ []).
      eapply StepsStep.
      * apply StepDerefReturn.
        reflexivity.
      * change (@nil DynamicAction) with
          (label_trace LSilent ++ @nil DynamicAction).
        eapply StepsStep.
        -- apply StepReturnDone.
        -- constructor.
Qed.

Lemma counter_summary_evaluation :
  SummaryEvaluation
    counter_heap counter_env empty_rho counter_summary
    [] counter_heap (SummarySet [CReadAbs 0]).
Proof.
  unfold SummaryEvaluation, counter_summary, counter_heap, counter_env,
    counter_x.
  replace (@nil DynamicAction) with
    (label_trace LSilent ++ @nil DynamicAction) by reflexivity.
  eapply StepsStep.
  - apply StepConcat.
  - replace (@nil DynamicAction) with
      (label_trace LSilent ++ @nil DynamicAction) by reflexivity.
    eapply StepsStep.
    + apply StepEmpty.
    + replace (@nil DynamicAction) with
        (label_trace LSilent ++ @nil DynamicAction) by reflexivity.
      eapply StepsStep.
      * apply StepConcatL.
      * replace (@nil DynamicAction) with
          (label_trace LSilent ++ @nil DynamicAction) by reflexivity.
        eapply StepsStep.
        -- apply StepReadAbs.
           reflexivity.
        -- replace (@nil DynamicAction) with
            (label_trace LSilent ++ @nil DynamicAction) by reflexivity.
           eapply StepsStep.
           ++ apply StepConcatR.
           ++ replace (@nil DynamicAction) with
               (label_trace LSilent ++ @nil DynamicAction) by reflexivity.
              eapply StepsStep.
              ** apply StepReturnDone.
              ** constructor.
Qed.

Lemma counter_not_covered :
  ~ TraceCoveredBySummary [DRead 1 0] (SummarySet [CReadAbs 0]).
Proof.
  intros HCovered.
  simpl in HCovered.
  destruct (HCovered (DRead 1 0) (or_introl eq_refl))
    as (ca & HIn & HCover).
  simpl in HIn.
  destruct HIn as [HCa | []].
  subst ca.
  inversion HCover; subst.
Qed.

Definition UntypedTerminalCorrectnessGoal : Prop :=
  forall gamma omega heap env rho expr summary_expr phi heap' v
    phi_summary heap_summary theta,
    NCheckedBackTriangle gamma omega expr summary_expr ->
    ComputationEvaluation heap env rho expr phi heap' v ->
    SummaryEvaluation heap env rho summary_expr
      phi_summary heap_summary theta ->
    TraceCoveredBySummary phi theta.

Theorem untyped_terminal_correctness_goal_false :
  UntypedTerminalCorrectnessGoal -> False.
Proof.
  intros HGoal.
  apply counter_not_covered.
  eapply HGoal.
  - exact counter_backtriangle.
  - exact counter_computation.
  - exact counter_summary_evaluation.
Qed.
