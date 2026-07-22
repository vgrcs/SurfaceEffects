From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Wf_nat.

(* Application and effect-application correctness lemmas. *)

Require Export theories.Runtime.SmallStepPaperTheorems.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepParallel.
Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepRuntimeSubstShape.
Require Import theories.Runtime.SmallStepRuntimeStateShape.
Require Import theories.Runtime.SmallStepPairParDispatch.
Require Import theories.Runtime.SmallStepTraceSafety.
Require Import theories.Runtime.SmallStepStructuredTrace.
Require Import theories.Runtime.SmallStepCorrectness.
Require Import theories.Runtime.SmallStepEffectSoundness.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.DynamicActions.
Require Import theories.Core.Expressions.
Require Import theories.Core.StaticActions.
Require Import theories.Core.Values.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.EffectFacts.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.TraceTypingFacts.
Require Import theories.Meta.TypingWeakeningFacts.
Require Import theories.Meta.TypeFacts.
Require Import theories.Soundness.SmallStepBackTriangle.


Require Export theories.Soundness.SmallStepCorrectnessBase.

Theorem MuAppTerminalDecompose :
  forall heap env rho ef ea phi heap_final v_final,
    StepsPhi
      (initial_state heap env rho (Mu_App ef ea))
      phi
      (StDone heap_final v_final) ->
    exists phi_fun phi_arg phi_body
      heap_fun heap_arg env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun
        (StDone heap_fun
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap_fun env rho ea)
        phi_arg
        (StDone heap_arg v_arg) /\
      StepsPhi
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body
        (StDone heap_final v_final) /\
      phi_as_list phi =
        phi_as_list phi_fun ++
        phi_as_list phi_arg ++
        phi_as_list phi_body.
Proof.
  intros heap env rho ef ea phi heap_final v_final HSteps.
  pose proof
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Mu_App ef ea))
      Silent
      (StEval heap env rho ef (KMuAppFun ea env rho KDone))
      phi heap_final v_final)
    as HFirst.
	  specialize
	    (HFirst I (Step_MuApp_EvalFun heap env rho KDone ef ea) HSteps).
  destruct HFirst as (phi_after_fun & HAfterFun & HTraceStart).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho ef (KMuAppFun ea env rho KDone)
      phi_after_fun heap_final v_final HAfterFun)
    as (heap_fun & v_fun & phi_fun & phi_after_kfun &
        HFun & HAfterKFun & HTraceFun).
  destruct
    (StepsPhi_nonterminal_terminal_inv_step
      (StReturn heap_fun v_fun (KMuAppFun ea env rho KDone))
      phi_after_kfun heap_final v_final)
    as (label_arg & state_arg & phi_after_arg &
        HStepArg & HAfterArg & HTraceArgStep).
  - intros HTerminal. inversion HTerminal.
  - exact HAfterKFun.
  - inversion HStepArg; subst.
    destruct
      (StepsPhi_initial_with_kont_terminal_decompose
        heap_fun env rho ea (KMuAppArg env' rho' f x ec ee KDone)
        phi_after_arg heap_final v_final HAfterArg)
      as (heap_arg & v_arg & phi_arg & phi_after_karg &
          HArg & HAfterKArg & HTraceArg).
    destruct
      (StepsPhi_nonterminal_terminal_inv_step
        (StReturn heap_arg v_arg
          (KMuAppArg env' rho' f x ec ee KDone))
        phi_after_karg heap_final v_final)
      as (label_body & state_body & phi_body &
          HStepBody & HBody & HTraceBodyStep).
    + intros HTerminal. inversion HTerminal.
    + exact HAfterKArg.
    + inversion HStepBody; subst.
      exists phi_fun, phi_arg, phi_body,
        heap_fun, heap_arg, env', rho', f, x, ec, ee, v_arg.
      split; [exact HFun |].
      split; [exact HArg |].
      split; [exact HBody |].
      rewrite HTraceStart, HTraceFun, HTraceArgStep,
        HTraceArg, HTraceBodyStep.
      simpl.
      repeat rewrite app_nil_l.
      repeat rewrite app_nil_r.
      rewrite app_assoc.
      reflexivity.
Qed.

Theorem EffAppTerminalDecompose :
  forall heap env rho ef ea phi heap_final v_final,
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi
      (StDone heap_final v_final) ->
    exists phi_fun phi_arg phi_body
      heap_fun heap_arg env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun
        (StDone heap_fun
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap_fun env rho ea)
        phi_arg
        (StDone heap_arg v_arg) /\
      StepsPhi
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body
        (StDone heap_final v_final) /\
      phi_as_list phi =
        phi_as_list phi_fun ++
        phi_as_list phi_arg ++
        phi_as_list phi_body.
Proof.
  intros heap env rho ef ea phi heap_final v_final HSteps.
  pose proof
    (StepsPhi_terminal_inv_step
      (initial_state heap env rho (Eff_App ef ea))
      Silent
      (StEval heap env rho ef (KEffAppFun ea env rho KDone))
      phi heap_final v_final)
    as HFirst.
	  specialize
	    (HFirst I (Step_EffApp_EvalFun heap env rho KDone ef ea) HSteps).
  destruct HFirst as (phi_after_fun & HAfterFun & HTraceStart).
  destruct
    (StepsPhi_initial_with_kont_terminal_decompose
      heap env rho ef (KEffAppFun ea env rho KDone)
      phi_after_fun heap_final v_final HAfterFun)
    as (heap_fun & v_fun & phi_fun & phi_after_kfun &
        HFun & HAfterKFun & HTraceFun).
  destruct
    (StepsPhi_nonterminal_terminal_inv_step
      (StReturn heap_fun v_fun (KEffAppFun ea env rho KDone))
      phi_after_kfun heap_final v_final)
    as (label_arg & state_arg & phi_after_arg &
        HStepArg & HAfterArg & HTraceArgStep).
  - intros HTerminal. inversion HTerminal.
  - exact HAfterKFun.
  - inversion HStepArg; subst.
    destruct
      (StepsPhi_initial_with_kont_terminal_decompose
        heap_fun env rho ea (KEffAppArg env' rho' f x ec ee KDone)
        phi_after_arg heap_final v_final HAfterArg)
      as (heap_arg & v_arg & phi_arg & phi_after_karg &
          HArg & HAfterKArg & HTraceArg).
    destruct
      (StepsPhi_nonterminal_terminal_inv_step
        (StReturn heap_arg v_arg
          (KEffAppArg env' rho' f x ec ee KDone))
        phi_after_karg heap_final v_final)
      as (label_body & state_body & phi_body &
          HStepBody & HBody & HTraceBodyStep).
    + intros HTerminal. inversion HTerminal.
    + exact HAfterKArg.
    + inversion HStepBody; subst.
      exists phi_fun, phi_arg, phi_body,
        heap_fun, heap_arg, env', rho', f, x, ec, ee, v_arg.
      split; [exact HFun |].
      split; [exact HArg |].
      split; [exact HBody |].
      rewrite HTraceStart, HTraceFun, HTraceArgStep,
        HTraceArg, HTraceBodyStep.
      simpl.
      repeat rewrite app_nil_l.
      repeat rewrite app_nil_r.
      rewrite app_assoc.
      reflexivity.
Qed.

Lemma StepsPhiN_mu_app_terminal_decompose_counts :
  forall n heap env rho ef ea phi heap_final v_final,
    StepsPhiN n (initial_state heap env rho (Mu_App ef ea)) phi
      (StDone heap_final v_final) ->
    exists env_fun rho_fun f x ec ee
      n_fun phi_fun heap_fun
      n_arg phi_arg heap_arg v_arg
      n_body phi_body,
      n_fun < n /\
      n_arg < n /\
      n_body < n /\
      StepsPhiN n_fun (initial_state heap env rho ef) phi_fun
        (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) /\
      StepsPhiN n_arg (initial_state heap_fun env rho ea) phi_arg
        (StDone heap_arg v_arg) /\
      StepsPhiN n_body
        (initial_state heap_arg
          (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
            (x, v_arg) env_fun)
          rho_fun ec) phi_body
        (StDone heap_final v_final) /\
      phi_as_list phi =
        phi_as_list phi_fun ++ phi_as_list phi_arg ++ phi_as_list phi_body.
Proof.
  intros n heap env rho ef ea phi heap_final v_final HApp.
  assert
    (HFirst :
      Step (initial_state heap env rho (Mu_App ef ea)) Silent
        (StEval heap env rho ef (KMuAppFun ea env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhiN_terminal_inv_step
      n
	      (initial_state heap env rho (Mu_App ef ea))
	      Silent
	      (StEval heap env rho ef (KMuAppFun ea env rho KDone))
	      phi heap_final v_final I HFirst HApp)
    as (n_after_fun & phi_after_fun & HNAfterFun &
        HAfterFun & HTraceStart).
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_fun heap env rho ef (KMuAppFun ea env rho KDone)
      phi_after_fun heap_final v_final HAfterFun)
    as (n_fun & n_after_arg & heap_fun & v_fun &
        phi_fun & phi_after_arg &
        HLeFun & HLeAfterArg & HFun & HAfterArg & HTraceFun).
  inversion HAfterArg as
    [| n_after_arg_tail state_arg label_arg state_after_arg
       phi_after_arg_tail final_arg HStepArg HAfterArgTail];
    subst; try discriminate.
  inversion HStepArg; subst.
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_arg_tail heap_fun env rho ea
      (KMuAppArg env' rho' f x ec ee KDone)
      phi_after_arg_tail heap_final v_final HAfterArgTail)
    as (n_arg & n_after_body & heap_arg & v_arg &
        phi_arg & phi_after_body &
        HLeArg & HLeAfterBody & HArg & HAfterBody & HTraceArg).
  inversion HAfterBody as
    [| n_body state_body label_body state_after_body
       phi_body final_body HStepBody HBody];
    subst; try discriminate.
  inversion HStepBody; subst.
  exists env', rho', f, x, ec, ee,
    n_fun, phi_fun, heap_fun,
    n_arg, phi_arg, heap_arg, v_arg,
    n_body, phi_body.
  repeat split; try lia; try assumption.
  rewrite HTraceStart.
  simpl.
  rewrite HTraceFun.
  simpl.
  rewrite HTraceArg.
  simpl.
  repeat rewrite app_assoc.
  reflexivity.
Qed.

Lemma StepsPhiN_eff_app_terminal_decompose_counts :
  forall n heap env rho ef ea phi heap_final v_final,
    StepsPhiN n (initial_state heap env rho (Eff_App ef ea)) phi
      (StDone heap_final v_final) ->
    exists env_fun rho_fun f x ec ee
      n_fun phi_fun heap_fun
      n_arg phi_arg heap_arg v_arg
      n_body phi_body,
      n_fun < n /\
      n_arg < n /\
      n_body < n /\
      StepsPhiN n_fun (initial_state heap env rho ef) phi_fun
        (StDone heap_fun (Cls (env_fun, rho_fun, Mu f x ec ee))) /\
      StepsPhiN n_arg (initial_state heap_fun env rho ea) phi_arg
        (StDone heap_arg v_arg) /\
      StepsPhiN n_body
        (initial_state heap_arg
          (update_rec_E (f, Cls (env_fun, rho_fun, Mu f x ec ee))
            (x, v_arg) env_fun)
          rho_fun ee) phi_body
        (StDone heap_final v_final) /\
      phi_as_list phi =
        phi_as_list phi_fun ++ phi_as_list phi_arg ++ phi_as_list phi_body.
Proof.
  intros n heap env rho ef ea phi heap_final v_final HApp.
  assert
    (HFirst :
      Step (initial_state heap env rho (Eff_App ef ea)) Silent
        (StEval heap env rho ef (KEffAppFun ea env rho KDone))).
  {
    constructor.
  }
  destruct
    (StepsPhiN_terminal_inv_step
      n
	      (initial_state heap env rho (Eff_App ef ea))
	      Silent
	      (StEval heap env rho ef (KEffAppFun ea env rho KDone))
	      phi heap_final v_final I HFirst HApp)
    as (n_after_fun & phi_after_fun & HNAfterFun &
        HAfterFun & HTraceStart).
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_fun heap env rho ef (KEffAppFun ea env rho KDone)
      phi_after_fun heap_final v_final HAfterFun)
    as (n_fun & n_after_arg & heap_fun & v_fun &
        phi_fun & phi_after_arg &
        HLeFun & HLeAfterArg & HFun & HAfterArg & HTraceFun).
  inversion HAfterArg as
    [| n_after_arg_tail state_arg label_arg state_after_arg
       phi_after_arg_tail final_arg HStepArg HAfterArgTail];
    subst; try discriminate.
  inversion HStepArg; subst.
  destruct
    (StepsPhiN_initial_with_kont_terminal_decompose
      n_after_arg_tail heap_fun env rho ea
      (KEffAppArg env' rho' f x ec ee KDone)
      phi_after_arg_tail heap_final v_final HAfterArgTail)
    as (n_arg & n_after_body & heap_arg & v_arg &
        phi_arg & phi_after_body &
        HLeArg & HLeAfterBody & HArg & HAfterBody & HTraceArg).
  inversion HAfterBody as
    [| n_body state_body label_body state_after_body
       phi_body final_body HStepBody HBody];
    subst; try discriminate.
  inversion HStepBody; subst.
  exists env', rho', f, x, ec, ee,
    n_fun, phi_fun, heap_fun,
    n_arg, phi_arg, heap_arg, v_arg,
    n_body, phi_body.
  repeat split; try lia; try assumption.
  rewrite HTraceStart.
  simpl.
  rewrite HTraceFun.
  simpl.
  rewrite HTraceArg.
  simpl.
  repeat rewrite app_assoc.
  reflexivity.
Qed.

Definition SmallStepCorrectnessBelow (n : nat) : Prop :=
  forall n_child heap env rho ea ee phi heap' v
    phi_summary heap_summary theta_summary
    stty ctxt rgns ty static,
    n_child < n ->
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    StepsPhiN n_child (initial_state heap env rho ea) phi
      (StDone heap' v) ->
    StepsPhi (initial_state heap env rho ee) phi_summary
      (StDone heap_summary (Eff theta_summary)) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, ea, ty, static) ->
    phi ⋞ theta_summary.

Theorem MuEffAppTerminalAlignedBodyDecompose :
  forall heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta,
    StepsPhi
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      (StDone heap_mu v_mu) ->
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      (StDone heap_eff (Eff theta)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea)) ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      heap_fun heap_arg env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_mu
        (StDone heap_fun
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_eff
        (StDone heap_fun
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap_fun env rho ea)
        phi_arg_mu
        (StDone heap_arg v_arg) /\
      StepsPhi
        (initial_state heap_fun env rho ea)
        phi_arg_eff
        (StDone heap_arg v_arg) /\
      StepsPhi
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu v_mu) /\
      StepsPhi
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff (Eff theta)) /\
      phi_as_list phi_mu =
        phi_as_list phi_fun_mu ++
        phi_as_list phi_arg_mu ++
        phi_as_list phi_body_mu /\
      phi_as_list phi_eff =
        phi_as_list phi_fun_eff ++
        phi_as_list phi_arg_eff ++
        phi_as_list phi_body_eff /\
      phi_as_list phi_fun_mu = phi_as_list phi_fun_eff /\
      phi_as_list phi_arg_mu = phi_as_list phi_arg_eff.
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    HMu HEff HStayFun HStayArg.
  destruct
    (MuAppTerminalDecompose
      heap env rho ef ea phi_mu heap_mu v_mu HMu)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        heap_fun_mu & heap_arg_mu & env_mu & rho_mu &
        f_mu & x_mu & ec_mu & ee_mu & v_arg_mu &
        HFunMu & HArgMu & HBodyMu & HTraceMu).
  destruct
    (EffAppTerminalDecompose
      heap env rho ef ea phi_eff heap_eff (Eff theta) HEff)
    as (phi_fun_eff & phi_arg_eff & phi_body_eff &
        heap_fun_eff & heap_arg_eff & env_eff & rho_eff &
        f_eff & x_eff & ec_eff & ee_eff & v_arg_eff &
        HFunEff & HArgEff & HBodyEff & HTraceEff).
  destruct
    (StepsPhi_terminal_deterministic
      (initial_state heap env rho ef)
      phi_fun_mu heap_fun_mu
      (Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu))
		      phi_fun_eff heap_fun_eff
		      (Cls (env_eff, rho_eff, Mu f_eff x_eff ec_eff ee_eff))
		      HStayFun
		      HFunMu HFunEff)
    as (HFunTrace & HHeapFun & HClosureEq).
  subst heap_fun_eff.
  symmetry in HClosureEq.
  inversion HClosureEq; subst.
  destruct
    (StepsPhi_terminal_deterministic
		      (initial_state heap_fun_mu env rho ea)
		      phi_arg_mu heap_arg_mu v_arg_mu
		      phi_arg_eff heap_arg_eff v_arg_eff
		      (HStayArg heap_fun_mu)
		      HArgMu HArgEff)
    as (HArgTrace & HHeapArg & HArgVal).
  subst heap_arg_eff.
  subst v_arg_eff.
  exists phi_fun_mu, phi_arg_mu, phi_body_mu,
    phi_fun_eff, phi_arg_eff, phi_body_eff,
    heap_fun_mu, heap_arg_mu, env_mu, rho_mu,
    f_mu, x_mu, ec_mu, ee_mu, v_arg_mu.
  repeat split; try assumption.
Qed.

Lemma BackTriangle_mu_app_eff_app_inv :
  forall ctxt rgns rho ef ea,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    exists ty_mu ty_eff ty_ef ty_ea
      static_ef static_ea static_mu static_ee,
      TcExp (ctxt, rgns, Mu_App ef ea, ty_mu, static_mu) /\
      TcExp (ctxt, rgns, Eff_App ef ea, ty_eff, static_ee) /\
      ReadOnlyStatic (fold_subst_eps rho static_ee) /\
      TcExp (ctxt, rgns, ef, ty_ef, static_ef) /\
      TcExp (ctxt, rgns, ea, ty_ea, static_ea) /\
      BackTriangle (ctxt, rgns, rho, ef, Eff_App ef ea) /\
      BackTriangle (ctxt, rgns, rho, ea, Eff_App ef ea) /\
      ReadOnlyStatic (fold_subst_eps rho static_ef) /\
      ReadOnlyStatic (fold_subst_eps rho static_ea).
Proof.
  intros ctxt rgns rho ef ea HBack.
  inversion HBack; subst; try discriminate.
  repeat eexists; eauto.
Qed.

Lemma TcExp_mu_app_inv :
  forall ctxt rgns ef ea ty static,
    TcExp (ctxt, rgns, Mu_App ef ea, ty, static) ->
    exists tya effc tyc effe efff effa,
      TcExp (ctxt, rgns, ef,
        Ty_Arrow tya effc tyc effe Ty_Effect, efff) /\
      TcExp (ctxt, rgns, ea, tya, effa).
Proof.
  intros ctxt rgns ef ea ty static HTc.
  inversion HTc; subst; repeat eexists; eauto.
Qed.

Lemma MuAppFunctionPrefix_body_backtriangle :
  forall heap env rho ef ea
    phi_fun env_closure rho_closure f x ec ee
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    StepsPhi
      (initial_state heap env rho ef)
      phi_fun
      (StDone heap
        (Cls (env_closure, rho_closure, Mu f x ec ee))) ->
    exists stty_cl ctxt_cl rgns_cl tyx effc tyc effe,
      StoreExtends stty stty_cl /\
      TcHeap (heap, stty_cl) /\
      RuntimeHeapShape heap stty_cl /\
      TcRho (rho_closure, rgns_cl) /\
      TcInc (ctxt_cl, rgns_cl) /\
      TcEnv (stty_cl, rho_closure, env_closure, ctxt_cl) /\
      RuntimeEnvShape stty_cl rho_closure env_closure ctxt_cl /\
      TcExp
        (ctxt_cl, rgns_cl, Mu f x ec ee,
          Ty_Arrow tyx effc tyc effe Ty_Effect,
          Empty_Static_Action) /\
      BackTriangle
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_cl,
         rgns_cl, rho_closure, ec, ee) /\
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_cl,
         rgns_cl, ec, tyc, effc) /\
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_cl,
         rgns_cl, ee, Ty_Effect, effe).
Proof.
  intros heap env rho ef ea
    phi_fun env_closure rho_closure f x ec ee
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HFun.
  destruct
    (BackTriangle_mu_app_eff_app_inv ctxt rgns rho ef ea HBack)
    as (_ty_mu & _ty_eff & ty_ef & _ty_ea &
        static_ef & _static_ea & _static_mu & _static_ee &
        _HTcMu & _HTcEff & _HReadOnlyEff &
        HTcEf & _HTcEa & _HBackEf & _HBackEa &
        _HReadOnlyEf & _HReadOnlyEa).
  destruct
    (initial_state_terminal_value_with_trace
      heap env rho ef stty ctxt rgns ty_ef static_ef
      (phi_as_list phi_fun) heap
      (Cls (env_closure, rho_closure, Mu f x ec ee))
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEf)
    as (stty_cl & HExt & HTcHeapCl & HHeapShapeCl &
        _HTcValCl & HValShapeCl & _HTcPhiFun).
  {
    eapply StepsPhi_as_steps; eauto.
  }
  destruct
    (RuntimeValShape_mu_closure_inv
      stty_cl (subst_rho rho ty_ef)
      env_closure rho_closure f x ec ee HValShapeCl)
    as (rgns_cl & ctxt_cl & tyx & effc & tyc & effe &
        _HClosureTy & HTcRhoCl & HTcIncCl & HTcEnvCl &
        HEnvShapeCl & HTcAbsCl).
  inversion HTcAbsCl; subst.
  match goal with
  | HBodyBackAll : forall rho0,
      BackTriangle
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_cl,
         rgns_cl, rho0, ec, ee) |- _ =>
      pose proof (HBodyBackAll rho_closure) as HBodyBack
  end.
  match goal with
  | HTcBodyMu : TcExp
      (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
        (x, tyx) ctxt_cl,
       rgns_cl, ec, tyc, effc),
    HTcBodyEff : TcExp
      (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
        (x, tyx) ctxt_cl,
       rgns_cl, ee, Ty_Effect, effe) |- _ =>
      pose proof HTcBodyMu as HBodyMuTc;
      pose proof HTcBodyEff as HBodyEffTc
  end.
  exists stty_cl, ctxt_cl, rgns_cl, tyx, effc, tyc, effe.
  split; [exact HExt |].
  split; [exact HTcHeapCl |].
  split; [exact HHeapShapeCl |].
  split; [exact HTcRhoCl |].
  split; [exact HTcIncCl |].
  split; [exact HTcEnvCl |].
  split; [exact HEnvShapeCl |].
  split; [exact HTcAbsCl |].
  split; [exact HBodyBack |].
  split; [exact HBodyMuTc | exact HBodyEffTc].
Qed.

Lemma MuAppBodyRuntimeTyping_from_prefixes :
  forall heap env rho ef ea
    phi_fun phi_arg env_closure rho_closure f x ec ee v_arg
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    StepsPhi
      (initial_state heap env rho ef)
      phi_fun
      (StDone heap
        (Cls (env_closure, rho_closure, Mu f x ec ee))) ->
    StepsPhi
      (initial_state heap env rho ea)
      phi_arg
      (StDone heap v_arg) ->
    exists stty_body ctxt_body rgns_body tyx effc tyc effe,
      TcHeap (heap, stty_body) /\
      RuntimeHeapShape heap stty_body /\
      TcRho (rho_closure, rgns_body) /\
      TcInc
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body) /\
      TcEnv
        (stty_body, rho_closure,
         update_rec_E
           (f, Cls (env_closure, rho_closure, Mu f x ec ee))
           (x, v_arg) env_closure,
         update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
           (x, tyx) ctxt_body) /\
      RuntimeEnvShape stty_body rho_closure
        (update_rec_E
          (f, Cls (env_closure, rho_closure, Mu f x ec ee))
          (x, v_arg) env_closure)
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body) /\
      BackTriangle
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, rho_closure, ec, ee) /\
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, ec, tyc, effc) /\
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, ee, Ty_Effect, effe).
Proof.
  intros heap env rho ef ea
    phi_fun phi_arg env_closure rho_closure f x ec ee v_arg
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HFun HArg.
  destruct
    (BackTriangle_mu_app_eff_app_inv ctxt rgns rho ef ea HBack)
    as (_ty_mu & _ty_eff & _ty_ef & _ty_ea &
        _static_ef & _static_ea & _static_mu & _static_ee &
        HTcMu & _HTcEff & _HReadOnlyEff &
        _HTcEf & _HTcEa & _HBackEf & _HBackEa &
        _HReadOnlyEf & _HReadOnlyEa).
  destruct (TcExp_mu_app_inv ctxt rgns ef ea _ _ HTcMu)
    as (tya & effc_top & tyc_top & effe_top & efff & effa &
        HTcFun & HTcArg).
  destruct
    (initial_state_terminal_value_with_trace
      heap env rho ef stty ctxt rgns
      (Ty_Arrow tya effc_top tyc_top effe_top Ty_Effect)
      efff
      (phi_as_list phi_fun) heap
      (Cls (env_closure, rho_closure, Mu f x ec ee))
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcFun)
    as (stty_fun & HExtFun & HTcHeapFun & HHeapShapeFun &
        _HTcFunVal & HFunShape & _HTcPhiFun).
  {
    eapply StepsPhi_as_steps; eauto.
  }
  destruct
    (RuntimeValShape_mu_closure_inv
      stty_fun
      (subst_rho rho
        (Ty_Arrow tya effc_top tyc_top effe_top Ty_Effect))
      env_closure rho_closure f x ec ee HFunShape)
    as (rgns_body & ctxt_body & tyx & effc & tyc & effe &
        HClosureTy & HTcRhoBody & HTcIncClosure &
        HTcEnvClosure & HEnvShapeClosure & HTcClosure).
  destruct
    (initial_state_terminal_value_with_trace
      heap env rho ea stty_fun ctxt rgns tya effa
      (phi_as_list phi_arg) heap v_arg
      HTcHeapFun HHeapShapeFun HTcRho HTcInc
      (ext_stores__env stty stty_fun HExtFun rho env ctxt HTcEnv)
      (RuntimeEnvShape_store_ext
        stty rho env ctxt HEnvShape stty_fun HExtFun)
      HTcArg)
    as (stty_arg & HExtArg & HTcHeapArg & HHeapShapeArg &
        HArgVal & HArgShape & _HTcPhiArg).
  {
    eapply StepsPhi_as_steps; eauto.
  }
  inversion HTcClosure; subst.
  match goal with
  | HBodyBackAll : forall rho0,
      BackTriangle
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, rho0, ec, ee) |- _ =>
      pose proof (HBodyBackAll rho_closure) as HBodyBack
  end.
  match goal with
  | HFindX : find_T x ctxt_body = Some tyx,
    HFindF : find_T f ctxt_body =
      Some (Ty_Arrow tyx effc tyc effe Ty_Effect) |- _ =>
      assert
        (HTcIncBody :
          TcInc
            (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
              (x, tyx) ctxt_body,
             rgns_body))
      by
        (eapply ExtendedTcInv_2; eauto;
         inversion HTcIncClosure as [? ? HFrv]; subst;
         eapply HFrv; eauto)
  end.
  assert
    (HArgTyEq :
      subst_rho rho tya = subst_rho rho_closure tyx).
  {
    eapply subst_rho_arrow_arg_eq.
    exact HClosureTy.
  }
  assert
    (HClosureValArg :
      TcVal
        (stty_arg, Cls (env_closure, rho_closure, Mu f x ec ee),
         subst_rho rho_closure
           (Ty_Arrow tyx effc tyc effe Ty_Effect))).
  {
    eapply TC_Cls with (rgns := rgns_body) (ctxt := ctxt_body); eauto.
    eapply ext_stores__env; eauto.
  }
  assert
    (HClosureShapeArg :
      RuntimeValShape stty_arg
        (subst_rho rho_closure
          (Ty_Arrow tyx effc tyc effe Ty_Effect))
        (Cls (env_closure, rho_closure, Mu f x ec ee))).
  {
    eapply RVS_Arrow with (rgns := rgns_body) (ctxt := ctxt_body); eauto.
    - eapply ext_stores__env; eauto.
    - intros y vy tty HFindE HFindT.
      eapply RuntimeEnvShape_store_ext; eauto.
  }
  assert
    (HArgValBody :
      TcVal (stty_arg, v_arg, subst_rho rho_closure tyx)).
  {
    rewrite <- HArgTyEq.
    exact HArgVal.
  }
  assert
    (HArgShapeBody :
      RuntimeValShape stty_arg (subst_rho rho_closure tyx) v_arg).
  {
    rewrite <- HArgTyEq.
    exact HArgShape.
  }
  exists stty_arg, ctxt_body, rgns_body, tyx, effc, tyc, effe.
  split; [exact HTcHeapArg |].
  split; [exact HHeapShapeArg |].
  split; [exact HTcRhoBody |].
  split; [exact HTcIncBody |].
  split.
  - eapply TcEnv_update_rec; eauto.
    eapply ext_stores__env; eauto.
  - split.
    + eapply RuntimeEnvShape_update_rec; eauto.
      eapply RuntimeEnvShape_store_ext; eauto.
    + split; [exact HBodyBack |].
      split; assumption.
Qed.

Theorem MuEffAppAlignedPrefixes_readonly_heap_neutral :
  forall heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      (StDone heap_mu v_mu) ->
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      (StDone heap_eff (Eff theta)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea)) ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_mu
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_eff
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_mu
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_eff
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu v_mu) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff (Eff theta)) /\
      phi_as_list phi_mu =
        phi_as_list phi_fun_mu ++
        phi_as_list phi_arg_mu ++
        phi_as_list phi_body_mu /\
      phi_as_list phi_eff =
        phi_as_list phi_fun_eff ++
        phi_as_list phi_arg_eff ++
        phi_as_list phi_body_eff /\
      phi_as_list phi_fun_mu = phi_as_list phi_fun_eff /\
      phi_as_list phi_arg_mu = phi_as_list phi_arg_eff /\
      ReadOnlyPhi phi_fun_mu /\
      ReadOnlyPhi phi_arg_mu.
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HStayFun HStayArg.
  destruct
    (BackTriangle_mu_app_eff_app_inv ctxt rgns rho ef ea HBack)
    as (ty_mu & ty_eff & ty_ef & ty_ea &
        static_ef & static_ea & static_mu & static_ee &
        _HTcMu & _HTcEff & _HReadOnlyEff &
        HTcEf & HTcEa & _HBackEf & _HBackEa &
        HReadOnlyEf & HReadOnlyEa).
  destruct
    (MuEffAppTerminalAlignedBodyDecompose
      heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      HMu HEff HStayFun HStayArg)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        phi_fun_eff & phi_arg_eff & phi_body_eff &
        heap_fun & heap_arg & env_closure & rho_closure &
        f & x & ec & ee & v_arg &
        HFunMu & HFunEff & HArgMu & HArgEff & HBodyMu & HBodyEff &
        HTraceMu & HTraceEff & HFunTrace & HArgTrace).
  assert (HFunStaticSound :
    Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, phi_fun_mu)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_eff_sound with
      (t := ty_ef) (eff := static_ef)
      (heap' := heap_fun)
      (v := Cls (env_closure, rho_closure, Mu f x ec ee));
      eauto.
    eapply StepsPhi_as_steps; eauto.
  }
  assert (HFunRO : ReadOnlyPhi phi_fun_mu).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ef)
        phi_fun_mu
        HReadOnlyEf
        HFunStaticSound).
  }
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho ef)
      phi_fun_mu
      (StDone heap_fun
        (Cls (env_closure, rho_closure, Mu f x ec ee)))
      HFunMu HFunRO)
    as HHeapFun.
  simpl in HHeapFun.
  symmetry in HHeapFun.
  subst heap_fun.
  assert (HArgStaticSound :
    Epsilon_Phi_Soundness (fold_subst_eps rho static_ea, phi_arg_mu)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_eff_sound with
      (t := ty_ea) (eff := static_ea)
      (heap' := heap_arg) (v := v_arg);
      eauto.
    eapply StepsPhi_as_steps; eauto.
  }
  assert (HArgRO : ReadOnlyPhi phi_arg_mu).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ea)
        phi_arg_mu
        HReadOnlyEa
        HArgStaticSound).
  }
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho ea)
      phi_arg_mu
      (StDone heap_arg v_arg)
      HArgMu HArgRO)
    as HHeapArg.
  simpl in HHeapArg.
  symmetry in HHeapArg.
  subst heap_arg.
  exists phi_fun_mu, phi_arg_mu, phi_body_mu,
    phi_fun_eff, phi_arg_eff, phi_body_eff,
    env_closure, rho_closure, f, x, ec, ee, v_arg.
  repeat split; try assumption.
Qed.

Theorem MuAppEffAppTerminalSound_with_readonly_prefixes_from_body_soundness :
  forall heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      (StDone heap_mu v_mu) ->
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      (StDone heap_eff (Eff theta)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea)) ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_mu
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_eff
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_mu
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_eff
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu v_mu) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff (Eff theta)) /\
      phi_as_list phi_fun_mu = phi_as_list phi_fun_eff /\
      phi_as_list phi_arg_mu = phi_as_list phi_arg_eff /\
      ReadOnlyPhi phi_fun_mu /\
      ReadOnlyPhi phi_arg_mu /\
      (phi_body_mu ⋞ theta ->
       phi_mu ⋞ theta_with_phi_prefixes phi_fun_mu phi_arg_mu theta).
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HStayFun HStayArg.
  destruct
    (MuEffAppAlignedPrefixes_readonly_heap_neutral
      heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu HEff HStayFun HStayArg)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        phi_fun_eff & phi_arg_eff & phi_body_eff &
        env_closure & rho_closure & f & x & ec & ee & v_arg &
        HFunMu & HFunEff & HArgMu & HArgEff &
        HBodyMu & HBodyEff & HTraceMu & _HTraceEff &
        HFunTrace & HArgTrace & HFunRO & HArgRO).
  exists phi_fun_mu, phi_arg_mu, phi_body_mu.
  exists phi_fun_eff, phi_arg_eff, phi_body_eff.
  exists env_closure, rho_closure, f, x, ec, ee, v_arg.
  repeat split; try assumption.
  intros HBodySound.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with
      (phi2 := Phi_Seq phi_fun_mu (Phi_Seq phi_arg_mu phi_body_mu)).
  - simpl. exact HTraceMu.
  - apply PTS_Seq.
    + apply theta_with_phi_prefixes_left_sound.
    + apply PTS_Seq.
      * apply theta_with_phi_prefixes_middle_sound.
      * apply theta_with_phi_prefixes_right_sound.
	        exact HBodySound.
Qed.

Theorem MuEffAppAlignedPrefixes_readonly_heap_neutral_counted :
  forall n heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    StepsPhiN n
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      (StDone heap_mu v_mu) ->
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      (StDone heap_eff (Eff theta)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea)) ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      env_closure rho_closure f x ec ee v_arg n_body,
      n_body < n /\
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_mu
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_eff
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_mu
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_eff
        (StDone heap v_arg) /\
      StepsPhiN n_body
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu v_mu) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff (Eff theta)) /\
      phi_as_list phi_mu =
        phi_as_list phi_fun_mu ++
        phi_as_list phi_arg_mu ++
        phi_as_list phi_body_mu /\
      phi_as_list phi_eff =
        phi_as_list phi_fun_eff ++
        phi_as_list phi_arg_eff ++
        phi_as_list phi_body_eff /\
      phi_as_list phi_fun_mu = phi_as_list phi_fun_eff /\
      phi_as_list phi_arg_mu = phi_as_list phi_arg_eff /\
      ReadOnlyPhi phi_fun_mu /\
      ReadOnlyPhi phi_arg_mu.
Proof.
  intros n heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HStayFun HStayArg.
  destruct
    (BackTriangle_mu_app_eff_app_inv ctxt rgns rho ef ea HBack)
    as (ty_mu & ty_eff & ty_ef & ty_ea &
        static_ef & static_ea & static_mu & static_ee &
        _HTcMu & _HTcEff & _HReadOnlyEff &
        HTcEf & HTcEa & _HBackEf & _HBackEa &
        HReadOnlyEf & HReadOnlyEa).
  destruct
    (StepsPhiN_mu_app_terminal_decompose_counts
      n heap env rho ef ea phi_mu heap_mu v_mu HMu)
    as (env_mu & rho_mu & f_mu & x_mu & ec_mu & ee_mu &
        n_fun_mu & phi_fun_mu & heap_fun_mu &
        n_arg_mu & phi_arg_mu & heap_arg_mu & v_arg_mu &
        n_body_mu & phi_body_mu &
        HNFun & HNArg & HNBody &
        HFunMuN & HArgMuN & HBodyMuN & HTraceMu).
  pose proof (StepsPhiN_to_StepsPhi _ _ _ _ HFunMuN) as HFunMu.
  pose proof (StepsPhiN_to_StepsPhi _ _ _ _ HArgMuN) as HArgMu.
  pose proof (StepsPhiN_to_StepsPhi _ _ _ _ HBodyMuN) as HBodyMu.
  destruct
    (EffAppTerminalDecompose
      heap env rho ef ea phi_eff heap_eff (Eff theta) HEff)
    as (phi_fun_eff & phi_arg_eff & phi_body_eff &
        heap_fun_eff & heap_arg_eff & env_eff & rho_eff &
        f_eff & x_eff & ec_eff & ee_eff & v_arg_eff &
        HFunEff & HArgEff & HBodyEff & HTraceEff).
  destruct
    (StepsPhi_terminal_deterministic
      (initial_state heap env rho ef)
      phi_fun_mu heap_fun_mu
      (Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu))
		      phi_fun_eff heap_fun_eff
		      (Cls (env_eff, rho_eff, Mu f_eff x_eff ec_eff ee_eff))
		      HStayFun
		      HFunMu HFunEff)
    as (HFunTrace & HHeapFunEq & HClosureEq).
  subst heap_fun_eff.
  symmetry in HClosureEq.
  inversion HClosureEq; subst.
  destruct
    (StepsPhi_terminal_deterministic
		      (initial_state heap_fun_mu env rho ea)
		      phi_arg_mu heap_arg_mu v_arg_mu
		      phi_arg_eff heap_arg_eff v_arg_eff
		      (HStayArg heap_fun_mu)
		      HArgMu HArgEff)
    as (HArgTrace & HHeapArgEq & HArgValEq).
  subst heap_arg_eff.
  subst v_arg_eff.
  assert (HFunStaticSound :
    Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, phi_fun_mu)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_eff_sound with
      (t := ty_ef) (eff := static_ef)
      (heap' := heap_fun_mu)
      (v := Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu));
      eauto.
    eapply StepsPhi_as_steps; eauto.
  }
  assert (HFunRO : ReadOnlyPhi phi_fun_mu).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ef)
        phi_fun_mu
        HReadOnlyEf
        HFunStaticSound).
  }
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho ef)
      phi_fun_mu
      (StDone heap_fun_mu
        (Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu)))
      HFunMu HFunRO)
    as HHeapFun.
  simpl in HHeapFun.
  symmetry in HHeapFun.
  subst heap_fun_mu.
  assert (HArgStaticSound :
    Epsilon_Phi_Soundness (fold_subst_eps rho static_ea, phi_arg_mu)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_eff_sound with
      (t := ty_ea) (eff := static_ea)
      (heap' := heap_arg_mu) (v := v_arg_mu);
      eauto.
    eapply StepsPhi_as_steps; eauto.
  }
  assert (HArgRO : ReadOnlyPhi phi_arg_mu).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ea)
        phi_arg_mu
        HReadOnlyEa
        HArgStaticSound).
  }
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho ea)
      phi_arg_mu
      (StDone heap_arg_mu v_arg_mu)
      HArgMu HArgRO)
    as HHeapArg.
  simpl in HHeapArg.
  symmetry in HHeapArg.
  subst heap_arg_mu.
  exists phi_fun_mu, phi_arg_mu, phi_body_mu.
  exists phi_fun_eff, phi_arg_eff, phi_body_eff.
  exists env_mu, rho_mu, f_mu, x_mu, ec_mu, ee_mu, v_arg_mu, n_body_mu.
  repeat split; try assumption.
Qed.

Theorem MuAppEffAppTerminalSound_with_readonly_prefixes_from_below :
  forall n heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    StepsPhiN n
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      (StDone heap_mu v_mu) ->
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      (StDone heap_eff (Eff theta)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea)) ->
    SmallStepCorrectnessBelow n ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_mu
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_eff
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_mu
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_eff
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu v_mu) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff (Eff theta)) /\
      ReadOnlyPhi phi_fun_mu /\
      ReadOnlyPhi phi_arg_mu /\
      phi_mu ⋞ theta_with_phi_prefixes phi_fun_mu phi_arg_mu theta.
Proof.
  intros n heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HStayFun HStayArg HBelow.
  destruct
    (MuEffAppAlignedPrefixes_readonly_heap_neutral_counted
      n heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu HEff HStayFun HStayArg)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        phi_fun_eff & phi_arg_eff & phi_body_eff &
        env_closure & rho_closure & f & x & ec & ee & v_arg &
        n_body & HNBody & HFunMu & HFunEff & HArgMu & HArgEff &
        HBodyMuN & HBodyEff & HTraceMu & _HTraceEff &
        _HFunTrace & _HArgTrace & HFunRO & HArgRO).
  destruct
    (MuAppBodyRuntimeTyping_from_prefixes
      heap env rho ef ea
      phi_fun_mu phi_arg_mu
      env_closure rho_closure f x ec ee v_arg
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HFunMu HArgMu)
    as (stty_body & ctxt_body & rgns_body & tyx & effc & tyc & effe &
        HTcHeapBody & HHeapShapeBody & HTcRhoBody & HTcIncBody &
        HTcEnvBody & HEnvShapeBody & HBackBody &
        HTcBodyMu & HTcBodyEff).
  pose proof
    (HBelow
      n_body heap
      (update_rec_E
        (f, Cls (env_closure, rho_closure, Mu f x ec ee))
        (x, v_arg) env_closure)
      rho_closure ec ee
      phi_body_mu heap_mu v_mu
      phi_body_eff heap_eff theta
      stty_body
      (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
        (x, tyx) ctxt_body)
      rgns_body tyc effc
      HNBody HBackBody HBodyMuN HBodyEff
      HTcHeapBody HHeapShapeBody HTcRhoBody HTcIncBody
      HTcEnvBody HEnvShapeBody HTcBodyMu)
    as HBodySound.
  exists phi_fun_mu, phi_arg_mu, phi_body_mu.
  exists phi_fun_eff, phi_arg_eff, phi_body_eff.
  exists env_closure, rho_closure, f, x, ec, ee, v_arg.
  repeat split; try assumption.
  - exact (StepsPhiN_to_StepsPhi _ _ _ _ HBodyMuN).
  - eapply Phi_Theta_Soundness_of_phi_as_list_eq
      with
        (phi2 := Phi_Seq phi_fun_mu (Phi_Seq phi_arg_mu phi_body_mu)).
    + simpl. exact HTraceMu.
    + apply PTS_Seq.
      * apply theta_with_phi_prefixes_left_sound.
      * apply PTS_Seq.
        -- apply theta_with_phi_prefixes_middle_sound.
        -- apply theta_with_phi_prefixes_right_sound.
           exact HBodySound.
Qed.

Theorem MuAppEffAppTerminalSound_raw_from_below :
  forall n heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    StepsPhiN n
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      (StDone heap_mu v_mu) ->
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      (StDone heap_eff (Eff theta)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea)) ->
    SmallStepCorrectnessBelow n ->
    phi_mu ⋞ theta.
Proof.
  intros n heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HStayFun HStayArg HBelow.
  destruct
    (BackTriangle_mu_app_eff_app_inv ctxt rgns rho ef ea HBack)
    as (_ty_mu & _ty_eff & ty_ef & ty_ea &
        static_ef & static_ea & _static_mu & _static_ee &
        _HTcMu & _HTcEff & _HReadOnlyEff &
        HTcEf & HTcEa & HBackEf & HBackEa &
        HReadOnlyEf & HReadOnlyEa).
  destruct
    (StepsPhiN_mu_app_terminal_decompose_counts
      n heap env rho ef ea phi_mu heap_mu v_mu HMu)
    as (env_mu & rho_mu & f_mu & x_mu & ec_mu & ee_mu &
        n_fun_mu & phi_fun_mu & heap_fun_mu &
        n_arg_mu & phi_arg_mu & heap_arg_mu & v_arg_mu &
        n_body_mu & phi_body_mu &
        HNFun & HNArg & HNBody &
        HFunMuN & HArgMuN & HBodyMuN & HTraceMu).
  pose proof (StepsPhiN_to_StepsPhi _ _ _ _ HFunMuN) as HFunMu.
  pose proof (StepsPhiN_to_StepsPhi _ _ _ _ HArgMuN) as HArgMu.
  destruct
    (EffAppTerminalDecompose
      heap env rho ef ea phi_eff heap_eff (Eff theta) HEff)
    as (phi_fun_eff & phi_arg_eff & phi_body_eff &
        heap_fun_eff & heap_arg_eff & env_eff & rho_eff &
        f_eff & x_eff & ec_eff & ee_eff & v_arg_eff &
        HFunEff & HArgEff & HBodyEff & _HTraceEff).
  destruct
    (StepsPhi_terminal_deterministic
      (initial_state heap env rho ef)
      phi_fun_mu heap_fun_mu
      (Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu))
		      phi_fun_eff heap_fun_eff
		      (Cls (env_eff, rho_eff, Mu f_eff x_eff ec_eff ee_eff))
		      HStayFun
		      HFunMu HFunEff)
    as (_HFunTrace & HHeapFunEq & HClosureEq).
  subst heap_fun_eff.
  symmetry in HClosureEq.
  inversion HClosureEq; subst.
  assert (HFunStaticSound :
    Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, phi_fun_mu)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_eff_sound with
      (t := ty_ef) (eff := static_ef)
      (heap' := heap_fun_mu)
      (v := Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu));
      eauto.
    eapply StepsPhi_as_steps; eauto.
  }
  assert (HFunRO : ReadOnlyPhi phi_fun_mu).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ef)
        phi_fun_mu
        HReadOnlyEf
        HFunStaticSound).
  }
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho ef)
      phi_fun_mu
      (StDone heap_fun_mu
        (Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu)))
      HFunMu HFunRO)
    as HHeapFun.
  simpl in HHeapFun.
  symmetry in HHeapFun.
  subst heap_fun_mu.
  destruct
    (StepsPhi_terminal_deterministic
		      (initial_state heap env rho ea)
		      phi_arg_mu heap_arg_mu v_arg_mu
		      phi_arg_eff heap_arg_eff v_arg_eff
		      (HStayArg heap)
		      HArgMu HArgEff)
    as (_HArgTrace & HHeapArgEq & HArgValEq).
  subst heap_arg_eff.
  subst v_arg_eff.
  assert (HArgStaticSound :
    Epsilon_Phi_Soundness (fold_subst_eps rho static_ea, phi_arg_mu)).
  {
    eapply Epsilon_Phi_Soundness_of_trace_as_phi_phi_as_list.
    eapply small_step_eff_sound with
      (t := ty_ea) (eff := static_ea)
      (heap' := heap_arg_mu) (v := v_arg_mu);
      eauto.
    eapply StepsPhi_as_steps; eauto.
  }
  assert (HArgRO : ReadOnlyPhi phi_arg_mu).
  {
    exact
      (ReadOnlyStaticImpliesReadOnlyPhi
        (fold_subst_eps rho static_ea)
        phi_arg_mu
        HReadOnlyEa
        HArgStaticSound).
  }
  pose proof
    (StepsPhi_readonly_preserves_heap
      (initial_state heap env rho ea)
      phi_arg_mu
      (StDone heap_arg_mu v_arg_mu)
      HArgMu HArgRO)
    as HHeapArg.
  simpl in HHeapArg.
  symmetry in HHeapArg.
  subst heap_arg_mu.
  destruct
    (MuAppBodyRuntimeTyping_from_prefixes
      heap env rho ef ea
      phi_fun_mu phi_arg_mu
      env_mu rho_mu f_mu x_mu ec_mu ee_mu v_arg_mu
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HFunMu HArgMu)
    as (stty_body & ctxt_body & rgns_body & tyx & effc & tyc & effe &
        HTcHeapBody & HHeapShapeBody & HTcRhoBody & HTcIncBody &
        HTcEnvBody & HEnvShapeBody & HBackBody &
        HTcBodyMu & _HTcBodyEff).
  pose proof
    (HBelow n_fun_mu heap env rho ef (Eff_App ef ea)
      phi_fun_mu heap
      (Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu))
      phi_eff heap_eff theta
      stty ctxt rgns ty_ef static_ef
      HNFun HBackEf HFunMuN HEff
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEf)
    as HFunSound.
  pose proof
    (HBelow n_arg_mu heap env rho ea (Eff_App ef ea)
      phi_arg_mu heap v_arg_mu
      phi_eff heap_eff theta
      stty ctxt rgns ty_ea static_ea
      HNArg HBackEa HArgMuN HEff
      HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HTcEa)
    as HArgSound.
  pose proof
    (HBelow n_body_mu heap
      (update_rec_E
        (f_mu, Cls (env_mu, rho_mu, Mu f_mu x_mu ec_mu ee_mu))
        (x_mu, v_arg_mu) env_mu)
      rho_mu ec_mu ee_mu
      phi_body_mu heap_mu v_mu
      phi_body_eff heap_eff theta
      stty_body
      (update_rec_T (f_mu, Ty_Arrow tyx effc tyc effe Ty_Effect)
        (x_mu, tyx) ctxt_body)
      rgns_body tyc effc
      HNBody HBackBody HBodyMuN HBodyEff
      HTcHeapBody HHeapShapeBody HTcRhoBody HTcIncBody
      HTcEnvBody HEnvShapeBody HTcBodyMu)
    as HBodySound.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with (phi2 := Phi_Seq phi_fun_mu (Phi_Seq phi_arg_mu phi_body_mu)).
  - simpl. exact HTraceMu.
  - apply PTS_Seq.
    + exact HFunSound.
    + apply PTS_Seq; assumption.
Qed.

Theorem MuAppEffAppTerminalSound_with_readonly_prefixes_with_body_reasoning :
  forall heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      (StDone heap_mu v_mu) ->
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      (StDone heap_eff (Eff theta)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea)) ->
    (forall stty_body ctxt_body rgns_body tyx effc tyc effe
       env_closure rho_closure f x ec ee v_arg
       phi_body_mu phi_body_eff,
      StoreExtends stty stty_body ->
      TcHeap (heap, stty_body) ->
      RuntimeHeapShape heap stty_body ->
      TcRho (rho_closure, rgns_body) ->
      TcInc (ctxt_body, rgns_body) ->
      TcEnv (stty_body, rho_closure, env_closure, ctxt_body) ->
      RuntimeEnvShape stty_body rho_closure env_closure ctxt_body ->
      TcExp
        (ctxt_body, rgns_body, Mu f x ec ee,
          Ty_Arrow tyx effc tyc effe Ty_Effect,
          Empty_Static_Action) ->
      BackTriangle
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, rho_closure, ec, ee) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, ec, tyc, effc) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect)
          (x, tyx) ctxt_body,
         rgns_body, ee, Ty_Effect, effe) ->
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu v_mu) ->
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff (Eff theta)) ->
      phi_body_mu ⋞ theta) ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_mu
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_eff
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_mu
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_eff
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu v_mu) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff (Eff theta)) /\
      ReadOnlyPhi phi_fun_mu /\
      ReadOnlyPhi phi_arg_mu /\
      phi_mu ⋞ theta_with_phi_prefixes phi_fun_mu phi_arg_mu theta.
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HStayFun HStayArg HBodyReasoning.
  destruct
    (MuAppEffAppTerminalSound_with_readonly_prefixes_from_body_soundness
      heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu HEff HStayFun HStayArg)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        phi_fun_eff & phi_arg_eff & phi_body_eff &
        env_closure & rho_closure & f & x & ec & ee & v_arg &
        HFunMu & HFunEff & HArgMu & HArgEff &
        HBodyMu & HBodyEff & _HFunTrace & _HArgTrace &
        HFunRO & HArgRO & HAssemble).
  destruct
    (MuAppFunctionPrefix_body_backtriangle
      heap env rho ef ea
      phi_fun_mu env_closure rho_closure f x ec ee
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape HFunMu)
    as (stty_body & ctxt_body & rgns_body &
        tyx & effc & tyc & effe &
        HExt & HTcHeapBody & HHeapShapeBody &
        HTcRhoBody & HTcIncBody & HTcEnvBody & HEnvShapeBody &
        HTcClosureBody & HBackBody & HTcBodyMu & HTcBodyEff).
  pose proof
    (HBodyReasoning
      stty_body ctxt_body rgns_body tyx effc tyc effe
      env_closure rho_closure f x ec ee v_arg
      phi_body_mu phi_body_eff
      HExt HTcHeapBody HHeapShapeBody HTcRhoBody HTcIncBody
      HTcEnvBody HEnvShapeBody HTcClosureBody HBackBody
      HTcBodyMu HTcBodyEff HBodyMu HBodyEff)
    as HBodySound.
  exists phi_fun_mu, phi_arg_mu, phi_body_mu.
  exists phi_fun_eff, phi_arg_eff, phi_body_eff.
  exists env_closure, rho_closure, f, x, ec, ee, v_arg.
  repeat split; try assumption.
  exact (HAssemble HBodySound).
Qed.

Theorem MuAppEffAppTerminalSound_with_readonly_prefixes_actual_body :
  forall heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns,
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea) ->
    TcHeap (heap, stty) ->
    RuntimeHeapShape heap stty ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    StepsPhi
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      (StDone heap_mu v_mu) ->
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      (StDone heap_eff (Eff theta)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea)) ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_mu
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_eff
        (StDone heap
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_mu
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap env rho ea)
        phi_arg_eff
        (StDone heap v_arg) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu v_mu) /\
      StepsPhi
        (initial_state heap
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff (Eff theta)) /\
      ReadOnlyPhi phi_fun_mu /\
      ReadOnlyPhi phi_arg_mu /\
      phi_mu ⋞
        theta_with_phi_prefixes
          phi_fun_mu phi_arg_mu (theta_of_phi phi_body_mu).
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    stty ctxt rgns
    HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
    HMu HEff HStayFun HStayArg.
  destruct
    (MuEffAppAlignedPrefixes_readonly_heap_neutral
      heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      stty ctxt rgns
      HBack HTcHeap HHeapShape HTcRho HTcInc HTcEnv HEnvShape
      HMu HEff HStayFun HStayArg)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        phi_fun_eff & phi_arg_eff & phi_body_eff &
        env_closure & rho_closure & f & x & ec & ee & v_arg &
        HFunMu & HFunEff & HArgMu & HArgEff &
        HBodyMu & HBodyEff & HTraceMu & _HTraceEff &
        _HFunTrace & _HArgTrace & _HFunRO & _HArgRO).
  exists phi_fun_mu, phi_arg_mu, phi_body_mu.
  exists phi_fun_eff, phi_arg_eff, phi_body_eff.
  exists env_closure, rho_closure, f, x, ec, ee, v_arg.
  repeat split; try assumption.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with
      (phi2 := Phi_Seq phi_fun_mu (Phi_Seq phi_arg_mu phi_body_mu)).
  - simpl. exact HTraceMu.
  - apply PTS_Seq.
    + apply theta_with_phi_prefixes_left_sound.
    + apply PTS_Seq.
      * apply theta_with_phi_prefixes_middle_sound.
      * apply theta_with_phi_prefixes_right_sound.
        apply theta_of_phi_sound.
Qed.

Theorem MuAppEffAppTerminalSound_reduces_to_component_soundness :
  forall heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta,
    StepsPhi
      (initial_state heap env rho (Mu_App ef ea))
      phi_mu
      (StDone heap_mu v_mu) ->
    StepsPhi
      (initial_state heap env rho (Eff_App ef ea))
      phi_eff
      (StDone heap_eff (Eff theta)) ->
    StepsStayNonPairParRun (initial_state heap env rho ef) ->
    (forall heap_fun,
      StepsStayNonPairParRun (initial_state heap_fun env rho ea)) ->
    exists phi_fun_mu phi_arg_mu phi_body_mu
      phi_fun_eff phi_arg_eff phi_body_eff
      heap_fun heap_arg env_closure rho_closure f x ec ee v_arg,
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_mu
        (StDone heap_fun
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap env rho ef)
        phi_fun_eff
        (StDone heap_fun
          (Cls (env_closure, rho_closure, Mu f x ec ee))) /\
      StepsPhi
        (initial_state heap_fun env rho ea)
        phi_arg_mu
        (StDone heap_arg v_arg) /\
      StepsPhi
        (initial_state heap_fun env rho ea)
        phi_arg_eff
        (StDone heap_arg v_arg) /\
      StepsPhi
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ec)
        phi_body_mu
        (StDone heap_mu v_mu) /\
      StepsPhi
        (initial_state heap_arg
          (update_rec_E
            (f, Cls (env_closure, rho_closure, Mu f x ec ee))
            (x, v_arg) env_closure)
          rho_closure ee)
        phi_body_eff
        (StDone heap_eff (Eff theta)) /\
      phi_as_list phi_fun_mu = phi_as_list phi_fun_eff /\
      phi_as_list phi_arg_mu = phi_as_list phi_arg_eff /\
      (phi_fun_mu ⋞ theta ->
       phi_arg_mu ⋞ theta ->
       phi_body_mu ⋞ theta ->
       phi_mu ⋞ theta).
Proof.
  intros heap env rho ef ea
    phi_mu heap_mu v_mu phi_eff heap_eff theta
    HMu HEff HStayFun HStayArg.
  destruct
    (MuEffAppTerminalAlignedBodyDecompose
      heap env rho ef ea
      phi_mu heap_mu v_mu phi_eff heap_eff theta
      HMu HEff HStayFun HStayArg)
    as (phi_fun_mu & phi_arg_mu & phi_body_mu &
        phi_fun_eff & phi_arg_eff & phi_body_eff &
        heap_fun & heap_arg & env_closure & rho_closure &
        f & x & ec & ee & v_arg &
        HFunMu & HFunEff & HArgMu & HArgEff & HBodyMu & HBodyEff &
        HTraceMu & _ & HFunTrace & HArgTrace).
  exists phi_fun_mu, phi_arg_mu, phi_body_mu,
    phi_fun_eff, phi_arg_eff, phi_body_eff,
    heap_fun, heap_arg, env_closure, rho_closure,
    f, x, ec, ee, v_arg.
  repeat split; try assumption.
  intros HFunSound HArgSound HBodySound.
  eapply Phi_Theta_Soundness_of_phi_as_list_eq
    with
      (phi2 := Phi_Seq phi_fun_mu (Phi_Seq phi_arg_mu phi_body_mu)).
  - simpl. exact HTraceMu.
  - apply PTS_Seq.
    + exact HFunSound.
    + apply PTS_Seq; assumption.
Qed.
