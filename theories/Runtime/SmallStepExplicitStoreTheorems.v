Require Import theories.Runtime.SmallStepExplicitStoreBase.
Require Import theories.Runtime.SmallStepExplicitStoreHeap.
Require Import theories.Runtime.SmallStepExplicitStoreCases.

Theorem WTStateRuntimeHeapShapeAt_step_preservation :
  WTStateRuntimeHeapShapeAtStepPreservation.
Proof.
  unfold WTStateRuntimeHeapShapeAtStepPreservation.
  intros state tout stty lbl state' HState HStep.
  inversion HStep; subst; eauto
    using
      WTStateRuntimeHeapShapeAt_const_step_preservation,
      WTStateRuntimeHeapShapeAt_bool_step_preservation,
      WTStateRuntimeHeapShapeAt_var_step_preservation,
      WTStateRuntimeHeapShapeAt_mu_step_preservation,
      WTStateRuntimeHeapShapeAt_lambda_step_preservation,
      WTStateRuntimeHeapShapeAt_mu_app_eval_fun_step_preservation,
      WTStateRuntimeHeapShapeAt_mu_app_eval_arg_step_preservation,
      WTStateRuntimeHeapShapeAt_mu_app_body_step_preservation,
      WTStateRuntimeHeapShapeAt_rgn_app_eval_fun_step_preservation,
      WTStateRuntimeHeapShapeAt_rgn_app_body_step_preservation,
      WTStateRuntimeHeapShapeAt_eff_app_eval_fun_step_preservation,
      WTStateRuntimeHeapShapeAt_eff_app_eval_arg_step_preservation,
      WTStateRuntimeHeapShapeAt_eff_app_body_step_preservation,
      WTStateRuntimeHeapShapeAt_pairpar_eval_eff1_step_preservation,
      WTStateRuntimeHeapShapeAt_pairpar_eval_eff2_step_preservation,
      WTStateRuntimeHeapShapeAt_pairpar_eval_mu1_step_preservation,
      WTStateRuntimeHeapShapeAt_pairpar_eval_mu2_step_preservation,
      WTStateRuntimeHeapShapeAt_pairpar_done_step_preservation,
      WTStateRuntimeHeapShapeAt_cond_eval_guard_step_preservation,
      WTStateRuntimeHeapShapeAt_cond_true_step_preservation,
      WTStateRuntimeHeapShapeAt_cond_false_step_preservation,
      WTStateRuntimeHeapShapeAt_ref_eval_arg_step_preservation,
      WTStateRuntimeHeapShapeAt_ref_done_step_preservation,
      WTStateRuntimeHeapShapeAt_deref_eval_arg_step_preservation,
      WTStateRuntimeHeapShapeAt_deref_done_step_preservation,
      WTStateRuntimeHeapShapeAt_assign_eval_loc_step_preservation,
      WTStateRuntimeHeapShapeAt_assign_eval_val_step_preservation,
      WTStateRuntimeHeapShapeAt_assign_done_step_preservation,
      WTStateRuntimeHeapShapeAt_plus_eval_left_step_preservation,
      WTStateRuntimeHeapShapeAt_plus_eval_right_step_preservation,
      WTStateRuntimeHeapShapeAt_plus_done_step_preservation,
      WTStateRuntimeHeapShapeAt_minus_eval_left_step_preservation,
      WTStateRuntimeHeapShapeAt_minus_eval_right_step_preservation,
      WTStateRuntimeHeapShapeAt_minus_done_step_preservation,
      WTStateRuntimeHeapShapeAt_times_eval_left_step_preservation,
      WTStateRuntimeHeapShapeAt_times_eval_right_step_preservation,
      WTStateRuntimeHeapShapeAt_times_done_step_preservation,
      WTStateRuntimeHeapShapeAt_eq_eval_left_step_preservation,
      WTStateRuntimeHeapShapeAt_eq_eval_right_step_preservation,
      WTStateRuntimeHeapShapeAt_eq_done_step_preservation,
      WTStateRuntimeHeapShapeAt_alloc_abs_step_preservation,
      WTStateRuntimeHeapShapeAt_read_abs_step_preservation,
      WTStateRuntimeHeapShapeAt_write_abs_step_preservation,
      WTStateRuntimeHeapShapeAt_read_conc_eval_arg_step_preservation,
      WTStateRuntimeHeapShapeAt_read_conc_done_step_preservation,
      WTStateRuntimeHeapShapeAt_write_conc_eval_arg_step_preservation,
      WTStateRuntimeHeapShapeAt_write_conc_done_step_preservation,
      WTStateRuntimeHeapShapeAt_concat_eval_left_step_preservation,
      WTStateRuntimeHeapShapeAt_concat_eval_right_step_preservation,
      WTStateRuntimeHeapShapeAt_concat_done_step_preservation,
      WTStateRuntimeHeapShapeAt_top_step_preservation,
      WTStateRuntimeHeapShapeAt_empty_step_preservation,
      WTStateRuntimeHeapShapeAt_done_step_preservation.
Qed.
