From Stdlib Require Import List.
From Stdlib Require Import Ascii.
From Stdlib Require Import Program.Equality.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Core.Values.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Runtime.Typing.
Require Import theories.SmallStep.Typing.Judgments.
Require Import theories.SmallStep.Typing.Resolve.
Require Import theories.SmallStep.Typing.Types.

Import ListNotations.

Inductive NResolvedValShape : Heap -> NVal -> NTy -> Prop :=
| NRVS_Nat :
    forall heap n,
      NResolvedValShape heap (VNat n) TyNat
| NRVS_Bool :
    forall heap b,
      NResolvedValShape heap (VBool b) TyBool
| NRVS_Unit :
    forall heap,
      NResolvedValShape heap VUnit TyUnit
| NRVS_Summary :
    forall heap theta,
      NResolvedValShape heap (VSummary theta) TyEffect
| NRVS_Pair :
    forall heap v1 v2 ty1 ty2,
      NResolvedValShape heap v1 ty1 ->
      NResolvedValShape heap v2 ty2 ->
      NResolvedValShape heap (VPair v1 v2) (TyPair ty1 ty2)
| NRVS_Loc :
    forall heap r l cell ty,
      heap_lookup r l heap = Some cell ->
      NResolvedValShape heap cell ty ->
      NResolvedValShape heap (VLoc r l) (TyRef (region_const_type r) ty)
| NRVS_Closure :
    forall heap closure_env closure_rho f x ec ee
      gamma omega ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res,
      NResolvedEnvShape closure_rho heap closure_env gamma ->
      NRhoModels omega closure_rho ->
      NResolveTy closure_rho ty_arg ty_arg_res ->
      NResolveStaticEffect closure_rho eff_body eff_body_res ->
      NResolveTy closure_rho ty_body ty_body_res ->
      NResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      NTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      NTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      NResolvedValShape heap
        (VClosure closure_env closure_rho f x ec ee)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
| NRVS_RegionClosure :
    forall heap closure_env closure_rho x e gamma omega ty ty_res eff eff_res,
      NResolvedEnvShape closure_rho heap closure_env gamma ->
      NRhoModels omega closure_rho ->
      NResolveStaticEffect closure_rho (close_static_effect x eff) eff_res ->
      NResolveTy closure_rho (close_ty x ty) ty_res ->
      NTcExp gamma (x :: omega) e ty eff ->
      NResolvedValShape heap
        (VRegionClosure closure_env closure_rho x e)
        (TyForallRgn eff_res ty_res)
with NResolvedEnvShape : Rho -> Heap -> NEnv -> NCtx -> Prop :=
| NRES_EnvNil :
    forall rho heap,
      NResolvedEnvShape rho heap EnvNil []
| NRES_EnvCons :
    forall rho heap x v env ty ty_res gamma,
      NResolveTy rho ty ty_res ->
      NResolvedValShape heap v ty_res ->
      NResolvedEnvShape rho heap env gamma ->
      NResolvedEnvShape rho heap (EnvCons x v env) ((x, ty) :: gamma).

Scheme NResolvedValShape_ind' :=
  Induction for NResolvedValShape Sort Prop
with NResolvedEnvShape_ind' :=
  Induction for NResolvedEnvShape Sort Prop.

Combined Scheme NResolvedValShape_NResolvedEnvShape_ind
  from NResolvedValShape_ind', NResolvedEnvShape_ind'.

Lemma NResolvedEnvShape_lookup :
  forall rho heap env gamma x ty ty_res,
    NResolvedEnvShape rho heap env gamma ->
    ctx_binds x ty gamma ->
    NResolveTy rho ty ty_res ->
    exists v,
      env_lookup x env = Some v /\
      NResolvedValShape heap v ty_res.
Proof.
  intros rho heap env gamma x ty ty_res HEnv.
  induction HEnv as
    [rho heap
    | rho heap y v env ty_y ty_y_res gamma
      HResolveY HV HEnv IH];
    intros HBind HResolve.
  - inversion HBind.
  - unfold ctx_binds in HBind.
    simpl in HBind.
    simpl.
    destruct (ascii_dec x y) as [HEq | HNe].
    + inversion HBind; subst.
      match goal with
      | HStored : NResolveTy rho ?ty ?ty_stored,
        HGoal : NResolveTy rho ?ty ?ty_goal,
        HVStored : NResolvedValShape heap v ?ty_stored |- _ =>
          pose proof
            (NResolveTy_deterministic
              rho ty ty_stored ty_goal HStored HGoal)
            as HResolvedEq;
          subst ty_goal;
          exists v; split; [reflexivity | exact HVStored]
      end.
    + apply IH; assumption.
Qed.

Lemma NResolvedEnvShape_extend_fresh :
  forall rho heap env gamma omega x r_val,
    ~ In x omega ->
    NCtxWF omega gamma ->
    NResolvedEnvShape rho heap env gamma ->
    NResolvedEnvShape (rho_extend x r_val rho) heap env gamma.
Proof.
  intros rho heap env gamma omega x r_val HFresh HCtxWF HEnv.
  induction HEnv as
    [rho heap
    | rho heap y v env ty ty_res gamma HResolve HV HEnv IH].
  - constructor.
  - inversion HCtxWF as [| binding gamma_tail HBindingWF HCtxTailWF];
      subst; simpl in HBindingWF.
    econstructor; eauto.
    eapply NResolveTy_extend_fresh; eauto.
Qed.

Definition NResolvedHeapShape (heap : Heap) : Prop :=
  forall r l v,
    heap_lookup r l heap = Some v ->
    exists ty,
      NResolvedValShape heap v ty.

Inductive NResolvedKontShape : Heap -> NKont -> NTy -> NTy -> Prop :=
| NRKS_Done :
    forall heap ty,
      NResolvedKontShape heap KDone ty ty
| NRKS_MuAppFun :
    forall heap ea env rho k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res eff_arg ty_out,
      NResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty_arg ty_arg_res ->
      NResolveStaticEffect rho eff_body eff_body_res ->
      NResolveTy rho ty_body ty_body_res ->
      NResolveStaticEffect rho eff_summary eff_summary_res ->
      NTcExp gamma omega ea ty_arg eff_arg ->
      NResolvedKontShape heap k ty_body_res ty_out ->
      NResolvedKontShape heap
        (KMuAppFun ea env rho k)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
        ty_out
| NRKS_MuAppArg :
    forall heap closure_env closure_rho f x ec ee k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res ty_out,
      NResolvedEnvShape closure_rho heap closure_env gamma ->
      NRhoModels omega closure_rho ->
      NResolveTy closure_rho ty_arg ty_arg_res ->
      NResolveStaticEffect closure_rho eff_body eff_body_res ->
      NResolveTy closure_rho ty_body ty_body_res ->
      NResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      NTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      NTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      NResolvedKontShape heap k ty_body_res ty_out ->
      NResolvedKontShape heap
        (KMuAppArg closure_env closure_rho f x ec ee k)
        ty_arg_res
        ty_out
| NRKS_EffAppFun :
    forall heap ea env rho k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res eff_arg ty_out,
      NResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty_arg ty_arg_res ->
      NResolveStaticEffect rho eff_body eff_body_res ->
      NResolveTy rho ty_body ty_body_res ->
      NResolveStaticEffect rho eff_summary eff_summary_res ->
      NTcExp gamma omega ea ty_arg eff_arg ->
      NResolvedKontShape heap k TyEffect ty_out ->
      NResolvedKontShape heap
        (KEffAppFun ea env rho k)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
        ty_out
| NRKS_EffAppArg :
    forall heap closure_env closure_rho f x ec ee k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res ty_out,
      NResolvedEnvShape closure_rho heap closure_env gamma ->
      NRhoModels omega closure_rho ->
      NResolveTy closure_rho ty_arg ty_arg_res ->
      NResolveStaticEffect closure_rho eff_body eff_body_res ->
      NResolveTy closure_rho ty_body ty_body_res ->
      NResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      NTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      NTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      NResolvedKontShape heap k TyEffect ty_out ->
      NResolvedKontShape heap
        (KEffAppArg closure_env closure_rho f x ec ee k)
        ty_arg_res
        ty_out
| NRKS_PairParEff1 :
    forall heap ef1 ea1 ef2 ea2 env rho k gamma omega
      ty1 ty1_res ty2 ty2_res eff1 eff2 eff_summary2 ty_out,
      NResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty1 ty1_res ->
      NResolveTy rho ty2 ty2_res ->
      NTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 ->
      NTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
      NTcExp gamma omega (EEffApp ef2 ea2) TyEffect eff_summary2 ->
      NResolvedKontShape heap k (TyPair ty1_res ty2_res) ty_out ->
      NResolvedKontShape heap
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)
        TyEffect
        ty_out
| NRKS_PairParEff2 :
    forall heap ef1 ea1 ef2 ea2 env rho theta1 k gamma omega
      ty1 ty1_res ty2 ty2_res eff1 eff2 ty_out,
      NResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty1 ty1_res ->
      NResolveTy rho ty2 ty2_res ->
      NTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 ->
      NTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
      NResolvedKontShape heap k (TyPair ty1_res ty2_res) ty_out ->
      NResolvedKontShape heap
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)
        TyEffect
        ty_out
| NRKS_RgnApp :
    forall heap r arg_rho r_val k eff ty ty_out,
      eval_region arg_rho r = Some r_val ->
      NResolvedKontShape heap k
        (open_ty_type (region_const_type r_val) ty)
        ty_out ->
      NResolvedKontShape heap
        (KRgnApp r arg_rho k)
        (TyForallRgn eff ty)
        ty_out
| NRKS_Cond :
    forall heap et ef env rho k gamma omega ty ty_res eff_t eff_f ty_out,
      NResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty ty_res ->
      NTcExp gamma omega et ty eff_t ->
      NTcExp gamma omega ef ty eff_f ->
      NResolvedKontShape heap k ty_res ty_out ->
      NResolvedKontShape heap
        (KCond et ef env rho k)
        TyBool
        ty_out
| NRKS_Ref :
    forall heap r ty k ty_out,
      NResolvedKontShape heap k (TyRef (region_const_type r) ty) ty_out ->
      NResolvedKontShape heap (KRef r k) ty ty_out
| NRKS_Deref :
    forall heap rgn r ty k ty_out,
      NResolvedKontShape heap k ty ty_out ->
      NResolvedKontShape heap (KDeref rgn k)
        (TyRef (region_const_type r) ty) ty_out
| NRKS_AssignLoc :
    forall heap rgn ev env rho k gamma omega r ty ty_res eff_v ty_out,
      NResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      eval_region rho rgn = Some r ->
      NResolveTy rho ty ty_res ->
      NTcExp gamma omega ev ty eff_v ->
      NResolvedKontShape heap k TyUnit ty_out ->
      NResolvedKontShape heap
        (KAssignLoc rgn ev env rho k)
        (TyRef (region_const_type r) ty_res)
        ty_out
| NRKS_AssignVal :
    forall heap rgn r ty loc k ty_out,
      NResolvedValShape heap loc (TyRef (region_const_type r) ty) ->
      NResolvedKontShape heap k TyUnit ty_out ->
      NResolvedKontShape heap
        (KAssignVal rgn loc k)
        ty
        ty_out
| NRKS_PlusL :
    forall heap e2 env rho k gamma omega eff ty_out,
      NResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NTcExp gamma omega e2 TyNat eff ->
      NResolvedKontShape heap k TyNat ty_out ->
      NResolvedKontShape heap
        (KPlusL e2 env rho k)
        TyNat
        ty_out
| NRKS_PlusR :
    forall heap n k ty_out,
      NResolvedKontShape heap k TyNat ty_out ->
      NResolvedKontShape heap (KPlusR n k) TyNat ty_out
| NRKS_MinusL :
    forall heap e2 env rho k gamma omega eff ty_out,
      NResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NTcExp gamma omega e2 TyNat eff ->
      NResolvedKontShape heap k TyNat ty_out ->
      NResolvedKontShape heap
        (KMinusL e2 env rho k)
        TyNat
        ty_out
| NRKS_MinusR :
    forall heap n k ty_out,
      NResolvedKontShape heap k TyNat ty_out ->
      NResolvedKontShape heap (KMinusR n k) TyNat ty_out
| NRKS_TimesL :
    forall heap e2 env rho k gamma omega eff ty_out,
      NResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NTcExp gamma omega e2 TyNat eff ->
      NResolvedKontShape heap k TyNat ty_out ->
      NResolvedKontShape heap
        (KTimesL e2 env rho k)
        TyNat
        ty_out
| NRKS_TimesR :
    forall heap n k ty_out,
      NResolvedKontShape heap k TyNat ty_out ->
      NResolvedKontShape heap (KTimesR n k) TyNat ty_out
| NRKS_EqL :
    forall heap e2 env rho k gamma omega eff ty_out,
      NResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NTcExp gamma omega e2 TyNat eff ->
      NResolvedKontShape heap k TyBool ty_out ->
      NResolvedKontShape heap
        (KEqL e2 env rho k)
        TyNat
        ty_out
| NRKS_EqR :
    forall heap n k ty_out,
      NResolvedKontShape heap k TyBool ty_out ->
      NResolvedKontShape heap (KEqR n k) TyNat ty_out
| NRKS_ReadConc :
    forall heap k r ty ty_out,
      NResolvedKontShape heap k TyEffect ty_out ->
      NResolvedKontShape heap
        (KReadConc k)
        (TyRef (region_const_type r) ty)
        ty_out
| NRKS_WriteConc :
    forall heap k r ty ty_out,
      NResolvedKontShape heap k TyEffect ty_out ->
      NResolvedKontShape heap
        (KWriteConc k)
        (TyRef (region_const_type r) ty)
        ty_out
| NRKS_ConcatL :
    forall heap e2 env rho k gamma omega eff ty_out,
      NResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NTcExp gamma omega e2 TyEffect eff ->
      NResolvedKontShape heap k TyEffect ty_out ->
      NResolvedKontShape heap
        (KConcatL e2 env rho k)
        TyEffect
        ty_out
| NRKS_ConcatR :
    forall heap theta k ty_out,
      NResolvedKontShape heap k TyEffect ty_out ->
      NResolvedKontShape heap
        (KConcatR theta k)
        TyEffect
        ty_out.

Inductive NResolvedStateShape : NState -> NTy -> Prop :=
| NRSS_Eval :
    forall heap env rho e k gamma omega ty ty_res eff ty_out,
      NResolvedHeapShape heap ->
      NResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty ty_res ->
      NTcExp gamma omega e ty eff ->
      NResolvedKontShape heap k ty_res ty_out ->
      NResolvedStateShape (StEval heap env rho e k) ty_out
| NRSS_Return :
    forall heap v k ty ty_out,
      NResolvedHeapShape heap ->
      NResolvedValShape heap v ty ->
      NResolvedKontShape heap k ty ty_out ->
      NResolvedStateShape (StReturn heap v k) ty_out
| NRSS_Done :
    forall heap v ty,
      NResolvedHeapShape heap ->
      NResolvedValShape heap v ty ->
      NResolvedStateShape (StDone heap v) ty
| NRSS_Error :
    forall heap ty,
      NResolvedHeapShape heap ->
      NResolvedStateShape (StError heap) ty
| NRSS_PairParRun :
    forall left_state right_state phi_left phi_right k
      heap ty1 ty2 ty_out,
      state_heap left_state = heap ->
      state_heap right_state = heap ->
      NResolvedStateShape left_state ty1 ->
      NResolvedStateShape right_state ty2 ->
      NResolvedKontShape heap k (TyPair ty1 ty2) ty_out ->
      NResolvedStateShape
        (StPairParRun left_state right_state phi_left phi_right k)
        ty_out.

Lemma NResolvedStateShape_done_inv :
  forall heap v ty,
    NResolvedStateShape (StDone heap v) ty ->
    NResolvedHeapShape heap /\ NResolvedValShape heap v ty.
Proof.
  intros heap v ty HState.
  inversion HState as [| | heap0 v0 ty0 HHeap HVal | |];
    subst; clear HState.
  split; assumption.
Qed.

Lemma NResolvedStateShape_done_summary_inv :
  forall heap theta ty,
    NResolvedStateShape (StDone heap (VSummary theta)) ty ->
    ty = TyEffect.
Proof.
  intros heap theta ty HState.
  destruct (NResolvedStateShape_done_inv heap (VSummary theta) ty HState)
    as (_ & HVal).
  inversion HVal; reflexivity.
Qed.

Lemma NResolvedValShape_closure_inv :
  forall heap closure_env closure_rho f x ec ee ty,
    NResolvedValShape heap
      (VClosure closure_env closure_rho f x ec ee)
      ty ->
    exists gamma omega ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res,
      ty =
        TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res /\
      NResolvedEnvShape closure_rho heap closure_env gamma /\
      NRhoModels omega closure_rho /\
      NResolveTy closure_rho ty_arg ty_arg_res /\
      NResolveStaticEffect closure_rho eff_body eff_body_res /\
      NResolveTy closure_rho ty_body ty_body_res /\
      NResolveStaticEffect closure_rho eff_summary eff_summary_res /\
      NTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body /\
      NTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary.
Proof.
  intros heap closure_env closure_rho f x ec ee ty HVal.
  dependent destruction HVal.
  exists gamma, omega, ty_arg, ty_arg_res, ty_body, ty_body_res.
  exists eff_body, eff_body_res, eff_summary, eff_summary_res.
  repeat split; assumption || reflexivity.
Qed.

Lemma NResolvedStateShape_done_closure_inv :
  forall heap closure_env closure_rho f x ec ee ty,
    NResolvedStateShape
      (StDone heap (VClosure closure_env closure_rho f x ec ee))
      ty ->
    exists gamma omega ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res,
      NResolvedHeapShape heap /\
      ty =
        TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res /\
      NResolvedEnvShape closure_rho heap closure_env gamma /\
      NRhoModels omega closure_rho /\
      NResolveTy closure_rho ty_arg ty_arg_res /\
      NResolveStaticEffect closure_rho eff_body eff_body_res /\
      NResolveTy closure_rho ty_body ty_body_res /\
      NResolveStaticEffect closure_rho eff_summary eff_summary_res /\
      NTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body /\
      NTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary.
Proof.
  intros heap closure_env closure_rho f x ec ee ty HState.
  destruct
    (NResolvedStateShape_done_inv
      heap
      (VClosure closure_env closure_rho f x ec ee)
      ty
      HState)
    as (HHeap & HVal).
  destruct
    (NResolvedValShape_closure_inv
      heap closure_env closure_rho f x ec ee ty HVal)
    as
      (gamma & omega & ty_arg & ty_arg_res & ty_body & ty_body_res &
        eff_body & eff_body_res & eff_summary & eff_summary_res &
        HTy & HEnv & HRho & HArgResolve & HBodyResolve &
        HBodyTyResolve & HSummaryResolve & HBodyTc & HSummaryTc).
  exists gamma, omega, ty_arg, ty_arg_res, ty_body, ty_body_res.
  exists eff_body, eff_body_res, eff_summary, eff_summary_res.
  repeat split; assumption || reflexivity.
Qed.

Lemma NResolvedStateShape_done_closure_summary_static_heap_neutral :
  forall heap closure_env closure_rho f x ec ee
    ty_arg_res eff_body_res ty_body_res eff_summary_res
    rho eff_summary,
    NResolvedStateShape
      (StDone heap (VClosure closure_env closure_rho f x ec ee))
      (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res) ->
    NResolveStaticEffect rho eff_summary eff_summary_res ->
    static_heap_neutral eff_summary ->
    exists gamma omega ty_arg ty_body eff_body eff_summary_closure,
      NResolvedHeapShape heap /\
      NResolvedEnvShape closure_rho heap closure_env gamma /\
      NRhoModels omega closure_rho /\
      NTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary_closure) ::
          gamma)
        omega ee TyEffect eff_summary_closure /\
      static_heap_neutral eff_summary_closure.
Proof.
  intros heap closure_env closure_rho f x ec ee
    ty_arg_res eff_body_res ty_body_res eff_summary_res
    rho eff_summary HState HResolveOriginal HNeutralOriginal.
  destruct
    (NResolvedStateShape_done_closure_inv
      heap closure_env closure_rho f x ec ee
      (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
      HState)
    as
      (gamma & omega & ty_arg & ty_arg_res_closure &
        ty_body & ty_body_res_closure & eff_body &
        eff_body_res_closure & eff_summary_closure &
        eff_summary_res_closure &
        HHeap & HTy & HEnv & HRho & HArgResolve &
        HBodyResolve & HBodyTyResolve & HSummaryResolve &
        _ & HSummaryTc).
  inversion HTy; subst.
  exists gamma, omega, ty_arg, ty_body, eff_body, eff_summary_closure.
  split; [exact HHeap |].
  split; [exact HEnv |].
  split; [exact HRho |].
  split; [exact HSummaryTc |].
  eapply
    (NResolveStaticEffect_static_heap_neutral_transfer_any
      rho closure_rho eff_summary eff_summary_closure
      eff_summary_res_closure);
    eauto.
Qed.

Lemma NResolvedStateShape_initial :
  forall heap env rho e gamma omega ty ty_res eff,
    NResolvedHeapShape heap ->
    NResolvedEnvShape rho heap env gamma ->
    NRhoModels omega rho ->
    NResolveTy rho ty ty_res ->
    NTcExp gamma omega e ty eff ->
    NResolvedStateShape (NInitialState heap env rho e) ty_res.
Proof.
  intros heap env rho e gamma omega ty ty_res eff
    HHeap HEnv HRho HResolve HTyped.
  unfold NInitialState.
  eapply NRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty) (eff := eff);
    eauto.
  constructor.
Qed.

Corollary NResolvedStateShape_initial_effect :
  forall heap env rho e gamma omega eff,
    NResolvedHeapShape heap ->
    NResolvedEnvShape rho heap env gamma ->
    NRhoModels omega rho ->
    NTcExp gamma omega e TyEffect eff ->
    NResolvedStateShape (NInitialState heap env rho e) TyEffect.
Proof.
  intros heap env rho e gamma omega eff HHeap HEnv HRho HTyped.
  eapply NResolvedStateShape_initial; eauto using NResolve_Effect.
Qed.
