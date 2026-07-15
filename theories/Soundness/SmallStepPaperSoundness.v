From Stdlib Require Import List.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepPreservationTheorems.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepStructuredTrace.
Require Import theories.Runtime.SmallStepSequentialSoundness.
Require Import theories.Runtime.SmallStepCorrectness.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.DynamicActions.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.EffectFacts.
Require Import theories.Soundness.SmallStepCorrectnessDirect.

Theorem PaperSmallStepRefAbsBTSummaryCorrectness :
  forall heap env rho w e eff
    phi_arg heap_arg v r l
    phi_eff heap_eff theta_eff
    phi_summary heap_summary theta_summary
    phi_ref heap_ref v_ref,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg v) ->
    StepsPhi (initial_state heap env rho eff) phi_eff
      (StDone heap_eff (Eff theta_eff)) ->
    find_R w rho = Some r ->
    allocate_H heap_arg r = l ->
    StepsPhi (initial_state heap env rho (Concat eff (AllocAbs w)))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Ref w e)) phi_ref
      (StDone heap_ref v_ref) ->
    phi_arg ⋞ theta_eff ->
    phi_ref ⋞ theta_summary.
Proof.
  exact Correctness_soundness_ext_small_step_ref_abs_bt_summary_terminal_case.
Qed.

Theorem PaperSmallStepDerefAbsBTSummaryCorrectness :
  forall heap env rho w e eff
    phi_arg heap_arg r l v
    phi_eff heap_eff theta_eff
    phi_summary heap_summary theta_summary
    phi_deref heap_deref v_deref,
    StepsPhi (initial_state heap env rho e) phi_arg
      (StDone heap_arg (Loc w l)) ->
    StepsPhi (initial_state heap env rho eff) phi_eff
      (StDone heap_eff (Eff theta_eff)) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_arg = Some v ->
    StepsPhi (initial_state heap env rho (Concat eff (ReadAbs w)))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (DeRef w e)) phi_deref
      (StDone heap_deref v_deref) ->
    phi_arg ⋞ theta_eff ->
    phi_deref ⋞ theta_summary.
Proof.
  exact Correctness_soundness_ext_small_step_deref_abs_bt_summary_terminal_case.
Qed.

Theorem PaperSmallStepAssignAbsBTSummaryCorrectness :
  forall heap env rho w ea ev eff1 eff2
    phi_loc heap_loc l phi_val heap_val v r
    phi_eff1 heap_eff1 theta_loc
    phi_eff2 heap_eff2 theta_val
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign,
    StepsPhi (initial_state heap env rho ea) phi_loc
      (StDone heap_loc (Loc w l)) ->
    StepsPhi (initial_state heap_loc env rho ev) phi_val
      (StDone heap_val v) ->
    StepsPhi (initial_state heap env rho eff1) phi_eff1
      (StDone heap_eff1 (Eff theta_loc)) ->
    StepsPhi (initial_state heap_eff1 env rho eff2) phi_eff2
      (StDone heap_eff2 (Eff theta_val)) ->
    find_R w rho = Some r ->
    find_H (r, l) heap_val <> None ->
    StepsPhi
      (initial_state heap env rho (Concat eff1 (Concat eff2 (WriteAbs w))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Assign w ea ev)) phi_assign
      (StDone heap_assign v_assign) ->
    phi_loc ⋞ theta_loc ->
    phi_val ⋞ theta_val ->
    phi_assign ⋞ theta_summary.
Proof.
  exact Correctness_soundness_ext_small_step_assign_abs_bt_summary_terminal_case.
Qed.

Theorem PaperSmallStepAssignAbsBTSummaryHeterogeneousRecursiveCorrectness :
  forall heap heap_summary_start env rho w ea ev eff1 eff2
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val,
    StepsPhi
      (initial_state heap_summary_start env rho
        (Concat eff1 (Concat eff2 (WriteAbs w))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Assign w ea ev)) phi_assign
      (StDone heap_assign v_assign) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty_loc, static_loc) ->
    TcExp (ctxt, rgns, ev, ty_val, static_val) ->
    ReadOnlyStatic (fold_subst_eps rho static_loc) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ea, eff1) ->
    BackTriangle (ctxt, rgns, rho, ev, eff2) ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi_assign ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_assign_abs_bt_summary_terminal_heterogeneous_recursive_case.
Qed.

Theorem PaperSmallStepAssignConcBTSummaryReadonlyCorrectness :
  forall heap env rho ea ev eff1 eff2
    phi_loc heap_loc r l phi_val heap_val v
    phi_eff1 heap_eff1 theta_loc
    phi_eff2 heap_eff2 theta_val
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign,
    StepsPhi (initial_state heap env rho ea) phi_loc
      (StDone heap_loc (Loc (Rgn_Const true false r) l)) ->
    StepsPhi (initial_state heap_loc env rho ev) phi_val
      (StDone heap_val v) ->
    StepsPhi (initial_state heap env rho eff1) phi_eff1
      (StDone heap_eff1 (Eff theta_loc)) ->
    StepsPhi (initial_state heap_eff1 env rho eff2) phi_eff2
      (StDone heap_eff2 (Eff theta_val)) ->
    ReadOnlyPhi phi_eff1 ->
    ReadOnlyPhi phi_eff2 ->
    find_H (r, l) heap_val <> None ->
    StepsPhi
      (initial_state heap env rho (Concat eff1 (Concat eff2 (WriteConc ea))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi
      (initial_state heap env rho (Assign (Rgn_Const true false r) ea ev))
      phi_assign (StDone heap_assign v_assign) ->
    phi_loc ⋞ theta_loc ->
    phi_val ⋞ theta_val ->
    phi_assign ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_assign_conc_bt_summary_readonly_terminal_case.
Qed.

Theorem PaperSmallStepAssignConcBTSummaryAddressAgreementCorrectness :
  forall heap heap_summary_start env rho ea ev eff1 eff2
    phi_loc heap_loc r l phi_val heap_val v
    phi_eff1 heap_eff1 theta_loc
    phi_eff2 heap_eff2 theta_val
    phi_loc_summary heap_loc_summary
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign,
    StepsPhi (initial_state heap env rho ea) phi_loc
      (StDone heap_loc (Loc (Rgn_Const true false r) l)) ->
    StepsPhi (initial_state heap_loc env rho ev) phi_val
      (StDone heap_val v) ->
    StepsPhi (initial_state heap_summary_start env rho eff1) phi_eff1
      (StDone heap_eff1 (Eff theta_loc)) ->
    StepsPhi (initial_state heap_eff1 env rho eff2) phi_eff2
      (StDone heap_eff2 (Eff theta_val)) ->
    StepsPhi (initial_state heap_eff2 env rho ea) phi_loc_summary
      (StDone heap_loc_summary (Loc (Rgn_Const true false r) l)) ->
    find_H (r, l) heap_val <> None ->
    StepsPhi
      (initial_state heap_summary_start env rho
        (Concat eff1 (Concat eff2 (WriteConc ea))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi
      (initial_state heap env rho (Assign (Rgn_Const true false r) ea ev))
      phi_assign (StDone heap_assign v_assign) ->
    phi_loc ⋞ theta_loc ->
    phi_val ⋞ theta_val ->
    phi_assign ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_address_agreement_case.
Qed.

Theorem PaperSmallStepAssignConcBTSummaryHeterogeneousHeapCorrectness :
  forall heap heap_summary_start env rho ea ev eff1 eff2 r
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val,
    StepsPhi
      (initial_state heap_summary_start env rho
        (Concat eff1 (Concat eff2 (WriteConc ea))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi
      (initial_state heap env rho (Assign (Rgn_Const true false r) ea ev))
      phi_assign (StDone heap_assign v_assign) ->
    HeterogeneousHeapForExpr env rho ea heap heap_summary_start ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty_loc, static_loc) ->
    TcExp (ctxt, rgns, ev, ty_val, static_val) ->
    ReadOnlyStatic (fold_subst_eps rho static_loc) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ea, eff1) ->
    BackTriangle (ctxt, rgns, rho, ev, eff2) ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi_assign ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_heterogeneous_recursive_case.
Qed.

Theorem PaperSmallStepAssignConcBTSummaryHeapCompatibleCorrectness :
  forall heap heap_summary_start env rho ea ev eff1 eff2 r
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val,
    StepsPhi
      (initial_state heap_summary_start env rho
        (Concat eff1 (Concat eff2 (WriteConc ea))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi
      (initial_state heap env rho (Assign (Rgn_Const true false r) ea ev))
      phi_assign (StDone heap_assign v_assign) ->
    HeterogeneousHeapForExpr env rho ea heap heap_summary_start ->
    HeterogeneousHeapForExpr env rho ev heap heap_summary_start ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty_loc, static_loc) ->
    TcExp (ctxt, rgns, ev, ty_val, static_val) ->
    ReadOnlyStatic (fold_subst_eps rho static_loc) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ea, eff1) ->
    BackTriangle (ctxt, rgns, rho, ev, eff2) ->
    SmallStepCorrectnessHeapCompatibleRecursivePremise ->
    phi_assign ⋞ theta_summary.
Proof.
	  exact
	    Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_heap_compatible_recursive_case.
Qed.

Theorem PaperSmallStepAssignConcBTSummaryHeapEquivalentCorrectness :
  forall heap heap_summary_start env rho ea ev eff1 eff2 r
    phi_summary heap_summary theta_summary
    phi_assign heap_assign v_assign
    stty ctxt rgns ty_loc static_loc ty_val static_val,
    StepsPhi
      (initial_state heap_summary_start env rho
        (Concat eff1 (Concat eff2 (WriteConc ea))))
      phi_summary (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi
      (initial_state heap env rho (Assign (Rgn_Const true false r) ea ev))
      phi_assign (StDone heap_assign v_assign) ->
    HeapEquivalentForExpr env rho ea heap heap_summary_start ->
    HeapEquivalentForExpr env rho ev heap heap_summary_start ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty_loc, static_loc) ->
    TcExp (ctxt, rgns, ev, ty_val, static_val) ->
    ReadOnlyStatic (fold_subst_eps rho static_loc) ->
    ReadOnlyPhi phi_summary ->
    BackTriangle (ctxt, rgns, rho, ea, eff1) ->
    BackTriangle (ctxt, rgns, rho, ev, eff2) ->
    SmallStepCorrectnessHeapEquivalentRecursivePremise ->
    phi_assign ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_assign_conc_bt_summary_terminal_heap_compatible_recursive_case.
Qed.

Theorem PaperSmallStepMuAppSummaryDirectCorrectness :
  forall heap env rho ef ea
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty_ef static_ef ty_ea static_ea,
    StepsPhi (initial_state heap env rho (Mu_App ef ea)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho (Eff_App ef ea)) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ef, ty_ef, static_ef) ->
    TcExp (ctxt, rgns, ea, ty_ea, static_ea) ->
    ReadOnlyStatic (fold_subst_eps rho static_ef) ->
    ReadOnlyStatic (fold_subst_eps rho static_ea) ->
    ReadOnlyPhi phi_summary ->
    (forall phi_fun heap_fun env_fun rho_fun f x ec ee,
      StepsPhi (initial_state heap env rho ef) phi_fun
        (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) ->
      phi_fun ⋞ theta_summary) ->
    (forall phi_arg heap_arg v_arg,
      StepsPhi (initial_state heap env rho ea) phi_arg
        (StDone heap_arg v_arg) ->
      phi_arg ⋞ theta_summary) ->
    (forall env_fun rho_fun f x ec ee v_arg
            phi_body heap_body v_body
            phi_summary_body heap_summary_body theta_body,
      StepsPhi
        (initial_state heap
          (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
            (x, v_arg) env_fun)
          rho_fun ec) phi_body
        (StDone heap_body v_body) ->
      StepsPhi
        (initial_state heap
          (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
            (x, v_arg) env_fun)
          rho_fun ee) phi_summary_body
        (StDone heap_summary_body (Eff theta_body)) ->
      ReadOnlyPhi phi_summary_body ->
      phi_body ⋞ theta_body) ->
    phi_app ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_mu_app_summary_terminal_direct_case.
Qed.

Theorem PaperSmallStepRgnAppEmptySummaryDirectCorrectness :
  forall heap env rho er w
    phi_app heap_app v_app
    phi_summary heap_summary theta_summary,
    StepsPhi (initial_state heap env rho (Rgn_App er w)) phi_app
      (StDone heap_app v_app) ->
    StepsPhi (initial_state heap env rho Empty) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    (forall phi_fun heap_fun env_fun rho_fun x eb,
      StepsPhi (initial_state heap env rho er) phi_fun
        (StDone heap_fun (Cls (env_fun, rho_fun, Lambda x eb))) ->
      phi_fun ⋞ Theta_Empty) ->
    (forall env_fun rho_fun x eb r phi_body heap_start heap_body v_body,
      find_R w rho = Some r ->
      StepsPhi
        (initial_state heap_start env_fun (update_R (x, r) rho_fun) eb)
        phi_body
        (StDone heap_body v_body) ->
      phi_body ⋞ Theta_Empty) ->
    phi_app ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_rgn_app_empty_summary_terminal_direct_case.
Qed.

Theorem PaperSmallStepPairParBTSummaryCorrectness :
  PairParCheckDecidable ->
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_eff1 heap_eff1 theta1
    phi_eff2 heap_eff2 theta2
    phi_mu1 heap_mu1 v1 theta3
    phi_mu2 heap_mu2 v2 theta4
    phi_sum1 heap_sum1
    phi_sum2 heap_sum2
    phi_sum3 heap_sum3
    phi_sum4 heap_sum4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair,
    PairParSequentialEffectSummaryStepsPhi
      heap env rho ef1 ea1 ef2 ea2
      phi_eff1 phi_eff2 heap_eff1 theta1 heap_eff2 theta2 ->
    StepsPhi (initial_state heap env rho eff1) phi_sum1
      (StDone heap_sum1 (Eff theta1)) ->
    StepsPhi (initial_state heap_sum1 env rho eff2) phi_sum2
      (StDone heap_sum2 (Eff theta2)) ->
    StepsPhi (initial_state heap_sum2 env rho eff3) phi_sum3
      (StDone heap_sum3 (Eff theta3)) ->
    StepsPhi (initial_state heap_sum3 env rho eff4) phi_sum4
      (StDone heap_sum4 (Eff theta4)) ->
    StepsPhi
      (initial_state heap env rho
        (Concat (Concat eff1 eff2) (Concat eff3 eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
      (StDone heap_mu1 v1) ->
    StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
      (StDone heap_mu2 v2) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    phi_eff1 ⋞ theta1 ->
    phi_eff2 ⋞ theta2 ->
    phi_mu1 ⋞ theta3 ->
    phi_mu2 ⋞ theta4 ->
    phi_pair ⋞ theta_summary.
Proof.
  exact Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_case.
Qed.

Theorem PaperSmallStepPairParBTSummaryDirectCorrectness :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair,
    StepsPhi
      (initial_state heap env rho
        (Concat (Concat eff1 eff2) (Concat eff3 eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    (forall phi_eff1 heap_eff1 theta_eff1
            phi_sum1 heap_sum1 theta1,
      StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
        (StDone heap_eff1 (Eff theta_eff1)) ->
      StepsPhi (initial_state heap env rho eff1) phi_sum1
        (StDone heap_sum1 (Eff theta1)) ->
      phi_eff1 ⋞ theta1) ->
    (forall heap_eff1 phi_eff2 heap_eff2 theta_eff2
            heap_sum1 phi_sum2 heap_sum2 theta2,
      StepsPhi (initial_state heap_eff1 env rho (Eff_App ef2 ea2))
        phi_eff2
        (StDone heap_eff2 (Eff theta_eff2)) ->
      StepsPhi (initial_state heap_sum1 env rho eff2) phi_sum2
        (StDone heap_sum2 (Eff theta2)) ->
      phi_eff2 ⋞ theta2) ->
    (forall heap_eff2 phi_mu1 heap_mu1 v1
            heap_sum2 phi_sum3 heap_sum3 theta3,
      StepsPhi (initial_state heap_eff2 env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) ->
      StepsPhi (initial_state heap_sum2 env rho eff3) phi_sum3
        (StDone heap_sum3 (Eff theta3)) ->
      phi_mu1 ⋞ theta3) ->
    (forall heap_mu1 phi_mu2 heap_mu2 v2
            heap_sum3 phi_sum4 heap_sum4 theta4,
      StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
        (StDone heap_mu2 v2) ->
      StepsPhi (initial_state heap_sum3 env rho eff4) phi_sum4
        (StDone heap_sum4 (Eff theta4)) ->
      phi_mu2 ⋞ theta4) ->
    phi_pair ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_direct_case.
Qed.

Theorem PaperSmallStepPairParCheckPassBranchTraceDisjoint :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2,
    PairParCheckPass theta1 theta2 ->
    (forall phi_mu1 heap_mu1 v1,
      StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) ->
      phi_mu1 ⋞ theta1) ->
    (forall heap_mu1 phi_mu2 heap_mu2 v2,
      StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
        (StDone heap_mu2 v2) ->
      ReadOnlyPhi phi_mu2 ->
      phi_mu2 ⋞ theta2) ->
    PairParBranchTraceDisjoint heap env rho ef1 ea1 ef2 ea2.
Proof.
  exact PairParBranchTraceDisjoint_from_check_soundness.
Qed.

Theorem PaperSmallStepPairParCheckPassDependentBranchTraceDisjoint :
  forall heap env rho ef1 ea1 ef2 ea2 theta1 theta2,
    PairParCheckPass theta1 theta2 ->
    (forall phi_mu1 heap_mu1 v1,
      StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) ->
      phi_mu1 ⋞ theta1) ->
    (forall phi_mu1 heap_mu1 v1 phi_mu2 heap_mu2 v2,
      StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) ->
      StepsPhi (initial_state heap_mu1 env rho (Mu_App ef2 ea2)) phi_mu2
        (StDone heap_mu2 v2) ->
      ReadOnlyPhi phi_mu2 ->
      phi_mu2 ⋞ theta2) ->
    PairParBranchTraceDisjoint heap env rho ef1 ea1 ef2 ea2.
Proof.
  exact PairParBranchTraceDisjoint_from_check_dependent_soundness.
Qed.

Theorem PaperSmallStepPairParCheckPassBranchSummaryTraceDisjoint :
  forall heap env rho ef1 ea1 summary2 theta1 theta2,
    PairParCheckPass theta1 theta2 ->
    (forall phi_mu1 heap_mu1 v1,
      StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) ->
      phi_mu1 ⋞ theta1) ->
    (forall phi_summary heap_summary v_summary,
      StepsPhi (initial_state heap env rho summary2) phi_summary
        (StDone heap_summary v_summary) ->
      ReadOnlyPhi phi_summary ->
      phi_summary ⋞ theta2) ->
    PairParBranchSummaryTraceDisjoint heap env rho ef1 ea1 summary2.
Proof.
  exact PairParBranchSummaryTraceDisjoint_from_check_soundness.
Qed.

Theorem PaperSmallStepPairParCheckPassBranchSummaryReplayCompatible :
  forall heap env rho ef1 ea1 summary2 theta1 theta2,
    PairParCheckPass theta1 theta2 ->
    (forall phi_mu1 heap_mu1 v1,
      StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) ->
      phi_mu1 ⋞ theta1) ->
    (forall phi_summary heap_summary v_summary,
      StepsPhi (initial_state heap env rho summary2) phi_summary
        (StDone heap_summary v_summary) ->
      ReadOnlyPhi phi_summary ->
      phi_summary ⋞ theta2) ->
    PairParBranchSummaryReplayCompatible heap env rho ef1 ea1 summary2.
Proof.
  exact PairParBranchSummaryReplayCompatible_from_check_soundness.
Qed.

Theorem PaperSmallStepPairParCheckPassBranchSummaryReplayCompatibleFromWitness :
  forall heap env rho ef1 ea1 summary2 theta1 theta2
    phi_summary2 heap_summary2 v_summary2,
    PairParCheckPass theta1 theta2 ->
    StepsPhi (initial_state heap env rho summary2) phi_summary2
      (StDone heap_summary2 v_summary2) ->
    phi_summary2 ⋞ theta2 ->
    (forall phi_mu1 heap_mu1 v1,
      StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) ->
      phi_mu1 ⋞ theta1) ->
    PairParBranchSummaryReplayCompatible heap env rho ef1 ea1 summary2.
Proof.
  exact PairParBranchSummaryReplayCompatible_from_check_summary_witness.
Qed.

Theorem PaperSmallStepPairParEffAppSummaryPassCorrectness :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2
    phi_eff1 phi_eff2 theta1 theta2
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2,
    StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
      (StDone heap (Eff theta1)) ->
    StepsPhi (initial_state heap env rho (Eff_App ef2 ea2)) phi_eff2
      (StDone heap (Eff theta2)) ->
    PairParCheckPass theta1 theta2 ->
    StepsPhi
      (initial_state heap env rho
        (Concat (Concat eff1 eff2)
          (Concat (Eff_App ef1 ea1) (Eff_App ef2 ea2))))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, static_mu1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, static_mu2) ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_eff1, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_eff2, static_eff2) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_pair_par_eff_app_bt_summary_terminal_pass_heterogeneous_recursive_case.
Qed.

Theorem PaperSmallStepPairParEffAppSummaryCheckedOrFallback :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty1 ty2 static_mu1 static_mu2
    ty_eff1 ty_eff2 static_eff1 static_eff2,
    StepsPhi
      (initial_state heap env rho
        (Concat (Concat eff1 eff2)
          (Concat (Eff_App ef1 ea1) (Eff_App ef2 ea2))))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, static_mu1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, static_mu2) ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_eff1, static_eff1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_eff2, static_eff2) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff1) ->
    ReadOnlyStatic (fold_subst_eps rho static_eff2) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    (exists phi_eff1 theta1 phi_eff2 theta2,
      StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
        (StDone heap (Eff theta1)) /\
      StepsPhi (initial_state heap env rho (Eff_App ef2 ea2)) phi_eff2
        (StDone heap (Eff theta2)) /\
      PairParCheckFail theta1 theta2) \/
    phi_pair ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_pair_par_eff_app_bt_summary_terminal_checked_or_fallback_heterogeneous_recursive_case.
Qed.

Theorem PaperSmallStepPairParEffAppBackTriangleCheckedOrFallback :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (Eff_App ef1 ea1 ⊕ Eff_App ef2 ea2)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (Eff_App ef1 ea1 ⊕ Eff_App ef2 ea2)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    (exists phi_eff1 theta1 phi_eff2 theta2,
      StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
        (StDone heap (Eff theta1)) /\
      StepsPhi (initial_state heap env rho (Eff_App ef2 ea2)) phi_eff2
        (StDone heap (Eff theta2)) /\
      PairParCheckFail theta1 theta2) \/
    phi_pair ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_pair_par_eff_app_backtriangle_checked_or_fallback_heterogeneous_recursive_case.
Qed.

Theorem PaperSmallStepPairParCanonicalEffAppCheckedOrFallback :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (Eff_App ef1 ea1 ⊕ Eff_App ef2 ea2)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    (exists phi_eff1 theta1 phi_eff2 theta2,
      StepsPhi (initial_state heap env rho (Eff_App ef1 ea1)) phi_eff1
        (StDone heap (Eff theta1)) /\
      StepsPhi (initial_state heap env rho (Eff_App ef2 ea2)) phi_eff2
        (StDone heap (Eff theta2)) /\
      PairParCheckFail theta1 theta2) \/
    phi_pair ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_pair_par_canonical_eff_app_backtriangle_checked_or_fallback_heterogeneous_recursive_case.
Qed.

Theorem PaperSmallStepPairParCanonicalEffAppCorrectness :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (Eff_App ef1 ea1 ⊕ Eff_App ef2 ea2)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_pair_par_canonical_eff_app_backtriangle_heterogeneous_recursive_case.
Qed.

Theorem PaperSmallStepRuntimeBackTriangleCheckedOrFallbackCorrectness :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    RuntimeBackTriangleSummary ctxt rgns rho ea ee ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    PairParCanonicalFallback heap env rho ea \/ phi ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_runtime_backtriangle_terminal_checked_or_fallback_heterogeneous_recursive_case.
Qed.

Theorem PaperSmallStepRuntimeBackTriangleTerminalCorrectness :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    RuntimeBackTriangleSummary ctxt rgns rho ea ee ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_runtime_backtriangle_terminal_heterogeneous_recursive_case.
Qed.

Theorem PaperSmallStepPairParBackTriangleHeterogeneousRecursiveCorrectness :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_pair_par_backtriangle_heterogeneous_recursive_case.
Qed.

Theorem PaperSmallStepPairParBackTriangleHeapCompatibleCorrectness :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    PairParBranchHeapCompatible heap env rho ef1 ea1 ef2 ea2 ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeapCompatibleRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_pair_par_backtriangle_heap_compatible_recursive_case.
Qed.

Theorem PaperSmallStepPairParBackTriangleSummaryReplayCorrectness :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    PairParBranchSummaryReplayCompatible heap env rho ef1 ea1 eff4 ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessSummaryReplayRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair
    HBack HSummary HPair HBranchSummary HTcHeap HHeapShape HTcRho HTcInc
    HTcEnv HEnvShape HTcPair HReadOnlySummary HRecursive.
  inversion HBack; subst; try discriminate.
  inversion HTcPair; subst.
  match goal with
  | HTcMu1 : TcExp
      (ctxt, rgns, Mu_App ef1 ea1, ?ty_mu1, ?static_mu1),
    HTcMu2 : TcExp
      (ctxt, rgns, Mu_App ef2 ea2, ?ty_mu2, ?static_mu2),
    HTcEff1 : TcExp
      (ctxt, rgns, Eff_App ef1 ea1, ?ty_eff1, ?static_eff1),
    HTcEff2 : TcExp
      (ctxt, rgns, Eff_App ef2 ea2, ?ty_eff2, ?static_eff2),
    HReadOnly1 : ReadOnlyStatic (fold_subst_eps rho ?static_eff1),
    HReadOnly2 : ReadOnlyStatic (fold_subst_eps rho ?static_eff2) |- _ =>
      eapply
        (Correctness_soundness_ext_small_step_pair_par_bt_summary_terminal_summary_replay_recursive_case
          heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
          phi_summary heap_summary theta_summary
          phi_pair heap_pair v_pair
          stty ctxt rgns ty_mu1 ty_mu2 static_mu1 static_mu2
          ty_eff1 ty_eff2 static_eff1 static_eff2);
      eauto
  end.
Qed.

Theorem PaperSmallStepPairParBackTriangleSummaryReplayBelowCorrectness :
  forall n heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhiN n (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    PairParBranchSummaryReplayCompatible heap env rho ef1 ea1 eff4 ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessSummaryReplayRecursivePremiseBelow n ->
    phi_pair ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_pair_par_backtriangle_summary_replay_below_case.
Qed.

Theorem PaperSmallStepPairParBackTriangleTraceDisjointCorrectness :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    PairParBranchTraceDisjoint heap env rho ef1 ea1 ef2 ea2 ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessHeapCompatibleRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_pair_par_backtriangle_trace_disjoint_recursive_case.
Qed.

Theorem PaperSmallStepPairParBackTriangleCheckedSummaryReplayCorrectness :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    theta_left theta_summary_branch
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    PairParCheckPass theta_left theta_summary_branch ->
    (forall phi_mu1 heap_mu1 v1,
      StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) ->
      phi_mu1 ⋞ theta_left) ->
    (forall phi_summary4 heap_summary4 v_summary4,
      StepsPhi (initial_state heap env rho eff4) phi_summary4
        (StDone heap_summary4 v_summary4) ->
      ReadOnlyPhi phi_summary4 ->
      phi_summary4 ⋞ theta_summary_branch) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessSummaryReplayRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    theta_left theta_summary_branch
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair
    HBack HSummary HPair HPass HLeftSound HSummarySound
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcPair
    HReadOnlySummary HRecursive.
  eapply PaperSmallStepPairParBackTriangleSummaryReplayCorrectness;
    eauto.
  eapply PairParBranchSummaryReplayCompatible_from_check_soundness;
    eauto.
Qed.

Theorem PaperSmallStepPairParBackTriangleCheckedSummaryReplayWitnessCorrectness :
  forall heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    theta_left theta_summary_branch
    phi_summary4 heap_summary4 v_summary4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair,
    BackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,
       (eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)) ->
    StepsPhi
      (initial_state heap env rho
        ((eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4)))
      phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    StepsPhi (initial_state heap env rho (Pair_Par ef1 ea1 ef2 ea2))
      phi_pair (StDone heap_pair v_pair) ->
    PairParCheckPass theta_left theta_summary_branch ->
    StepsPhi (initial_state heap env rho eff4) phi_summary4
      (StDone heap_summary4 v_summary4) ->
    phi_summary4 ⋞ theta_summary_branch ->
    (forall phi_mu1 heap_mu1 v1,
      StepsPhi (initial_state heap env rho (Mu_App ef1 ea1)) phi_mu1
        (StDone heap_mu1 v1) ->
      phi_mu1 ⋞ theta_left) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, ty_pair, static_pair) ->
    ReadOnlyPhi phi_summary ->
    SmallStepCorrectnessSummaryReplayRecursivePremise ->
    phi_pair ⋞ theta_summary.
Proof.
  intros heap env rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4
    theta_left theta_summary_branch
    phi_summary4 heap_summary4 v_summary4
    phi_summary heap_summary theta_summary
    phi_pair heap_pair v_pair
    stty ctxt rgns ty_pair static_pair
    HBack HSummary HPair HPass HSummary4 HSummary4Sound HLeftSound
    HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcPair
    HReadOnlySummary HRecursive.
  eapply PaperSmallStepPairParBackTriangleSummaryReplayCorrectness;
    eauto.
  eapply PairParBranchSummaryReplayCompatible_from_check_summary_witness;
    eauto.
Qed.

Theorem PaperSmallStepTopSummaryTerminalCorrectness :
  forall heap env rho e phi heap' v
         phi_summary heap_summary theta_summary,
    StepsPhi (initial_state heap env rho e) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho Top) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    phi ⋞ theta_summary.
Proof.
  intros heap env rho e phi heap' v
    phi_summary heap_summary theta_summary HSteps HSummary.
  eapply Correctness_soundness_ext_small_step_top_summary_case; eauto.
Qed.

Theorem PaperSmallStepBackTriangleTerminalHeterogeneousRecursiveCorrectness :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    SmallStepCorrectnessHeterogeneousRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_backtriangle_terminal_heterogeneous_recursive_case.
Qed.

Theorem PaperSmallStepBackTriangleSequentialHeadLookupEquivalentCorrectness :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    SequentialHead ea ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    SmallStepCorrectnessLookupEquivalentRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_backtriangle_sequential_head_lookup_equivalent_recursive_case.
Qed.

Theorem PaperSmallStepBackTriangleTerminalHeapCompatibleCorrectness :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    PairParBranchHeapCompatibleRecursivePremise ->
    SmallStepCorrectnessHeapCompatibleRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
	  exact
	    Correctness_soundness_ext_small_step_backtriangle_terminal_heap_compatible_recursive_case.
Qed.

Theorem PaperSmallStepBackTriangleTerminalHeapEquivalentCorrectness :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    PairParBranchHeapEquivalentRecursivePremise ->
    SmallStepCorrectnessHeapEquivalentRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_backtriangle_terminal_heap_equivalent_recursive_case.
Qed.

Theorem PaperSmallStepBackTriangleTerminalSummaryReplayCorrectness :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    PairParBranchSummaryReplayCompatibleRecursivePremise ->
    SmallStepCorrectnessSummaryReplayRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_backtriangle_terminal_summary_replay_recursive_case.
Qed.

Theorem PaperSmallStepBackTriangleTerminalSummaryReplayClosedCorrectness :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    PairParBranchSummaryReplayCompatibleRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_backtriangle_terminal_summary_replay_case.
Qed.

Theorem PaperSmallStepBackTriangleTerminalTraceDisjointCorrectness :
  forall heap env rho ea ee phi heap' v
         phi_summary heap_summary theta_summary
         stty ctxt rgns ty static,
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhi (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    ReadOnlyPhi phi_summary ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    PairParBranchTraceDisjointRecursivePremise ->
    SmallStepCorrectnessHeapCompatibleRecursivePremise ->
    phi ⋞ theta_summary.
Proof.
  exact
    Correctness_soundness_ext_small_step_backtriangle_terminal_trace_disjoint_recursive_case.
Qed.
