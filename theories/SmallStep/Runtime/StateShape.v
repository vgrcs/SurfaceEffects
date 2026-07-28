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

Inductive ResolvedValShape : Heap -> Val -> Ty -> Prop :=
| RVS_Nat :
    forall heap n,
      ResolvedValShape heap (VNat n) TyNat
| RVS_Bool :
    forall heap b,
      ResolvedValShape heap (VBool b) TyBool
| RVS_Unit :
    forall heap,
      ResolvedValShape heap VUnit TyUnit
| RVS_Summary :
    forall heap theta,
      ResolvedValShape heap (VSummary theta) TyEffect
| RVS_Pair :
    forall heap v1 v2 ty1 ty2,
      ResolvedValShape heap v1 ty1 ->
      ResolvedValShape heap v2 ty2 ->
      ResolvedValShape heap (VPair v1 v2) (TyPair ty1 ty2)
| RVS_Loc :
    forall heap r l cell ty,
      heap_lookup r l heap = Some cell ->
      ResolvedValShape heap cell ty ->
      ResolvedValShape heap (VLoc r l) (TyRef (region_const_type r) ty)
| RVS_Closure :
    forall heap closure_env closure_rho f x ec ee
      gamma omega ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res,
      ResolvedEnvShape closure_rho heap closure_env gamma ->
      RhoModels omega closure_rho ->
      ResolveTy closure_rho ty_arg ty_arg_res ->
      ResolveStaticEffect closure_rho eff_body eff_body_res ->
      ResolveTy closure_rho ty_body ty_body_res ->
      ResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      TcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      TcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      ResolvedValShape heap
        (VClosure closure_env closure_rho f x ec ee)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
| RVS_RegionClosure :
    forall heap closure_env closure_rho x e gamma omega ty ty_res eff eff_res,
      ResolvedEnvShape closure_rho heap closure_env gamma ->
      RhoModels omega closure_rho ->
      ResolveStaticEffect closure_rho (close_static_effect x eff) eff_res ->
      ResolveTy closure_rho (close_ty x ty) ty_res ->
      TcExp gamma (x :: omega) e ty eff ->
      ResolvedValShape heap
        (VRegionClosure closure_env closure_rho x e)
        (TyForallRgn eff_res ty_res)
with ResolvedEnvShape : Rho -> Heap -> Env -> Ctx -> Prop :=
| RES_EnvNil :
    forall rho heap,
      ResolvedEnvShape rho heap EnvNil []
| RES_EnvCons :
    forall rho heap x v env ty ty_res gamma,
      ResolveTy rho ty ty_res ->
      ResolvedValShape heap v ty_res ->
      ResolvedEnvShape rho heap env gamma ->
      ResolvedEnvShape rho heap (EnvCons x v env) ((x, ty) :: gamma).

Scheme ResolvedValShape_ind' :=
  Induction for ResolvedValShape Sort Prop
with ResolvedEnvShape_ind' :=
  Induction for ResolvedEnvShape Sort Prop.

Combined Scheme ResolvedValShape_ResolvedEnvShape_ind
  from ResolvedValShape_ind', ResolvedEnvShape_ind'.

Lemma ResolvedEnvShape_lookup :
  forall rho heap env gamma x ty ty_res,
    ResolvedEnvShape rho heap env gamma ->
    ctx_binds x ty gamma ->
    ResolveTy rho ty ty_res ->
    exists v,
      env_lookup x env = Some v /\
      ResolvedValShape heap v ty_res.
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
      | HStored : ResolveTy rho ?ty ?ty_stored,
        HGoal : ResolveTy rho ?ty ?ty_goal,
        HVStored : ResolvedValShape heap v ?ty_stored |- _ =>
          pose proof
            (ResolveTy_deterministic
              rho ty ty_stored ty_goal HStored HGoal)
            as HResolvedEq;
          subst ty_goal;
          exists v; split; [reflexivity | exact HVStored]
      end.
    + apply IH; assumption.
Qed.

Lemma ResolvedEnvShape_extend_fresh :
  forall rho heap env gamma omega x r_val,
    ~ In x omega ->
    CtxWF omega gamma ->
    ResolvedEnvShape rho heap env gamma ->
    ResolvedEnvShape (rho_extend x r_val rho) heap env gamma.
Proof.
  intros rho heap env gamma omega x r_val HFresh HCtxWF HEnv.
  induction HEnv as
    [rho heap
    | rho heap y v env ty ty_res gamma HResolve HV HEnv IH].
  - constructor.
  - inversion HCtxWF as [| binding gamma_tail HBindingWF HCtxTailWF];
      subst; simpl in HBindingWF.
    econstructor; eauto.
    eapply ResolveTy_extend_fresh; eauto.
Qed.

Definition ResolvedHeapShape (heap : Heap) : Prop :=
  forall r l v,
    heap_lookup r l heap = Some v ->
    exists ty,
      ResolvedValShape heap v ty.

Inductive ResolvedKontShape : Heap -> Kont -> Ty -> Ty -> Prop :=
| RKS_Done :
    forall heap ty,
      ResolvedKontShape heap KDone ty ty
| RKS_MuAppFun :
    forall heap ea env rho k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res eff_arg ty_out,
      ResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty_arg ty_arg_res ->
      ResolveStaticEffect rho eff_body eff_body_res ->
      ResolveTy rho ty_body ty_body_res ->
      ResolveStaticEffect rho eff_summary eff_summary_res ->
      TcExp gamma omega ea ty_arg eff_arg ->
      ResolvedKontShape heap k ty_body_res ty_out ->
      ResolvedKontShape heap
        (KMuAppFun ea env rho k)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
        ty_out
| RKS_MuAppArg :
    forall heap closure_env closure_rho f x ec ee k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res ty_out,
      ResolvedEnvShape closure_rho heap closure_env gamma ->
      RhoModels omega closure_rho ->
      ResolveTy closure_rho ty_arg ty_arg_res ->
      ResolveStaticEffect closure_rho eff_body eff_body_res ->
      ResolveTy closure_rho ty_body ty_body_res ->
      ResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      TcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      TcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      ResolvedKontShape heap k ty_body_res ty_out ->
      ResolvedKontShape heap
        (KMuAppArg closure_env closure_rho f x ec ee k)
        ty_arg_res
        ty_out
| RKS_EffAppFun :
    forall heap ea env rho k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res eff_arg ty_out,
      ResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty_arg ty_arg_res ->
      ResolveStaticEffect rho eff_body eff_body_res ->
      ResolveTy rho ty_body ty_body_res ->
      ResolveStaticEffect rho eff_summary eff_summary_res ->
      TcExp gamma omega ea ty_arg eff_arg ->
      ResolvedKontShape heap k TyEffect ty_out ->
      ResolvedKontShape heap
        (KEffAppFun ea env rho k)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
        ty_out
| RKS_EffAppArg :
    forall heap closure_env closure_rho f x ec ee k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res ty_out,
      ResolvedEnvShape closure_rho heap closure_env gamma ->
      RhoModels omega closure_rho ->
      ResolveTy closure_rho ty_arg ty_arg_res ->
      ResolveStaticEffect closure_rho eff_body eff_body_res ->
      ResolveTy closure_rho ty_body ty_body_res ->
      ResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      TcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      TcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      ResolvedKontShape heap k TyEffect ty_out ->
      ResolvedKontShape heap
        (KEffAppArg closure_env closure_rho f x ec ee k)
        ty_arg_res
        ty_out
| RKS_PairParEff1 :
    forall heap ef1 ea1 ef2 ea2 env rho k gamma omega
      ty1 ty1_res ty2 ty2_res eff1 eff2 eff_summary2 ty_out,
      ResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty1 ty1_res ->
      ResolveTy rho ty2 ty2_res ->
      TcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 ->
      TcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
      TcExp gamma omega (EEffApp ef2 ea2) TyEffect eff_summary2 ->
      ResolvedKontShape heap k (TyPair ty1_res ty2_res) ty_out ->
      ResolvedKontShape heap
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)
        TyEffect
        ty_out
| RKS_PairParEff2 :
    forall heap ef1 ea1 ef2 ea2 env rho theta1 k gamma omega
      ty1 ty1_res ty2 ty2_res eff1 eff2 ty_out,
      ResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty1 ty1_res ->
      ResolveTy rho ty2 ty2_res ->
      TcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 ->
      TcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
      ResolvedKontShape heap k (TyPair ty1_res ty2_res) ty_out ->
      ResolvedKontShape heap
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)
        TyEffect
        ty_out
| RKS_RgnApp :
    forall heap r arg_rho r_val k eff ty ty_out,
      eval_region arg_rho r = Some r_val ->
      ResolvedKontShape heap k
        (open_ty_type (region_const_type r_val) ty)
        ty_out ->
      ResolvedKontShape heap
        (KRgnApp r arg_rho k)
        (TyForallRgn eff ty)
        ty_out
| RKS_Cond :
    forall heap et ef env rho k gamma omega ty ty_res eff_t eff_f ty_out,
      ResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty ty_res ->
      TcExp gamma omega et ty eff_t ->
      TcExp gamma omega ef ty eff_f ->
      ResolvedKontShape heap k ty_res ty_out ->
      ResolvedKontShape heap
        (KCond et ef env rho k)
        TyBool
        ty_out
| RKS_Ref :
    forall heap r ty k ty_out,
      ResolvedKontShape heap k (TyRef (region_const_type r) ty) ty_out ->
      ResolvedKontShape heap (KRef r k) ty ty_out
| RKS_Deref :
    forall heap rgn r ty k ty_out,
      ResolvedKontShape heap k ty ty_out ->
      ResolvedKontShape heap (KDeref rgn k)
        (TyRef (region_const_type r) ty) ty_out
| RKS_AssignLoc :
    forall heap rgn ev env rho k gamma omega r ty ty_res eff_v ty_out,
      ResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      eval_region rho rgn = Some r ->
      ResolveTy rho ty ty_res ->
      TcExp gamma omega ev ty eff_v ->
      ResolvedKontShape heap k TyUnit ty_out ->
      ResolvedKontShape heap
        (KAssignLoc rgn ev env rho k)
        (TyRef (region_const_type r) ty_res)
        ty_out
| RKS_AssignVal :
    forall heap rgn r ty loc k ty_out,
      ResolvedValShape heap loc (TyRef (region_const_type r) ty) ->
      ResolvedKontShape heap k TyUnit ty_out ->
      ResolvedKontShape heap
        (KAssignVal rgn loc k)
        ty
        ty_out
| RKS_PlusL :
    forall heap e2 env rho k gamma omega eff ty_out,
      ResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      TcExp gamma omega e2 TyNat eff ->
      ResolvedKontShape heap k TyNat ty_out ->
      ResolvedKontShape heap
        (KPlusL e2 env rho k)
        TyNat
        ty_out
| RKS_PlusR :
    forall heap n k ty_out,
      ResolvedKontShape heap k TyNat ty_out ->
      ResolvedKontShape heap (KPlusR n k) TyNat ty_out
| RKS_MinusL :
    forall heap e2 env rho k gamma omega eff ty_out,
      ResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      TcExp gamma omega e2 TyNat eff ->
      ResolvedKontShape heap k TyNat ty_out ->
      ResolvedKontShape heap
        (KMinusL e2 env rho k)
        TyNat
        ty_out
| RKS_MinusR :
    forall heap n k ty_out,
      ResolvedKontShape heap k TyNat ty_out ->
      ResolvedKontShape heap (KMinusR n k) TyNat ty_out
| RKS_TimesL :
    forall heap e2 env rho k gamma omega eff ty_out,
      ResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      TcExp gamma omega e2 TyNat eff ->
      ResolvedKontShape heap k TyNat ty_out ->
      ResolvedKontShape heap
        (KTimesL e2 env rho k)
        TyNat
        ty_out
| RKS_TimesR :
    forall heap n k ty_out,
      ResolvedKontShape heap k TyNat ty_out ->
      ResolvedKontShape heap (KTimesR n k) TyNat ty_out
| RKS_EqL :
    forall heap e2 env rho k gamma omega eff ty_out,
      ResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      TcExp gamma omega e2 TyNat eff ->
      ResolvedKontShape heap k TyBool ty_out ->
      ResolvedKontShape heap
        (KEqL e2 env rho k)
        TyNat
        ty_out
| RKS_EqR :
    forall heap n k ty_out,
      ResolvedKontShape heap k TyBool ty_out ->
      ResolvedKontShape heap (KEqR n k) TyNat ty_out
| RKS_ReadConc :
    forall heap k r ty ty_out,
      ResolvedKontShape heap k TyEffect ty_out ->
      ResolvedKontShape heap
        (KReadConc k)
        (TyRef (region_const_type r) ty)
        ty_out
| RKS_WriteConc :
    forall heap k r ty ty_out,
      ResolvedKontShape heap k TyEffect ty_out ->
      ResolvedKontShape heap
        (KWriteConc k)
        (TyRef (region_const_type r) ty)
        ty_out
| RKS_ConcatL :
    forall heap e2 env rho k gamma omega eff ty_out,
      ResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      TcExp gamma omega e2 TyEffect eff ->
      ResolvedKontShape heap k TyEffect ty_out ->
      ResolvedKontShape heap
        (KConcatL e2 env rho k)
        TyEffect
        ty_out
| RKS_ConcatR :
    forall heap theta k ty_out,
      ResolvedKontShape heap k TyEffect ty_out ->
      ResolvedKontShape heap
        (KConcatR theta k)
        TyEffect
        ty_out.

Inductive ResolvedStateShape : State -> Ty -> Prop :=
| RSS_Eval :
    forall heap env rho e k gamma omega ty ty_res eff ty_out,
      ResolvedHeapShape heap ->
      ResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty ty_res ->
      TcExp gamma omega e ty eff ->
      ResolvedKontShape heap k ty_res ty_out ->
      ResolvedStateShape (StEval heap env rho e k) ty_out
| RSS_Return :
    forall heap v k ty ty_out,
      ResolvedHeapShape heap ->
      ResolvedValShape heap v ty ->
      ResolvedKontShape heap k ty ty_out ->
      ResolvedStateShape (StReturn heap v k) ty_out
| RSS_Done :
    forall heap v ty,
      ResolvedHeapShape heap ->
      ResolvedValShape heap v ty ->
      ResolvedStateShape (StDone heap v) ty
| RSS_Error :
    forall heap ty,
      ResolvedHeapShape heap ->
      ResolvedStateShape (StError heap) ty
| RSS_PairParRun :
    forall left_state right_state phi_left phi_right k
      heap ty1 ty2 ty_out,
      state_heap left_state = heap ->
      state_heap right_state = heap ->
      ResolvedStateShape left_state ty1 ->
      ResolvedStateShape right_state ty2 ->
      ResolvedKontShape heap k (TyPair ty1 ty2) ty_out ->
      ResolvedStateShape
        (StPairParRun left_state right_state phi_left phi_right k)
        ty_out.

Lemma ResolvedStateShape_done_inv :
  forall heap v ty,
    ResolvedStateShape (StDone heap v) ty ->
    ResolvedHeapShape heap /\ ResolvedValShape heap v ty.
Proof.
  intros heap v ty HState.
  inversion HState as [| | heap0 v0 ty0 HHeap HVal | |];
    subst; clear HState.
  split; assumption.
Qed.

Lemma ResolvedStateShape_done_summary_inv :
  forall heap theta ty,
    ResolvedStateShape (StDone heap (VSummary theta)) ty ->
    ty = TyEffect.
Proof.
  intros heap theta ty HState.
  destruct (ResolvedStateShape_done_inv heap (VSummary theta) ty HState)
    as (_ & HVal).
  inversion HVal; reflexivity.
Qed.

Lemma ResolvedValShape_closure_inv :
  forall heap closure_env closure_rho f x ec ee ty,
    ResolvedValShape heap
      (VClosure closure_env closure_rho f x ec ee)
      ty ->
    exists gamma omega ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res,
      ty =
        TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res /\
      ResolvedEnvShape closure_rho heap closure_env gamma /\
      RhoModels omega closure_rho /\
      ResolveTy closure_rho ty_arg ty_arg_res /\
      ResolveStaticEffect closure_rho eff_body eff_body_res /\
      ResolveTy closure_rho ty_body ty_body_res /\
      ResolveStaticEffect closure_rho eff_summary eff_summary_res /\
      TcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body /\
      TcExp
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

Lemma ResolvedStateShape_done_closure_inv :
  forall heap closure_env closure_rho f x ec ee ty,
    ResolvedStateShape
      (StDone heap (VClosure closure_env closure_rho f x ec ee))
      ty ->
    exists gamma omega ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res,
      ResolvedHeapShape heap /\
      ty =
        TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res /\
      ResolvedEnvShape closure_rho heap closure_env gamma /\
      RhoModels omega closure_rho /\
      ResolveTy closure_rho ty_arg ty_arg_res /\
      ResolveStaticEffect closure_rho eff_body eff_body_res /\
      ResolveTy closure_rho ty_body ty_body_res /\
      ResolveStaticEffect closure_rho eff_summary eff_summary_res /\
      TcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body /\
      TcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary.
Proof.
  intros heap closure_env closure_rho f x ec ee ty HState.
  destruct
    (ResolvedStateShape_done_inv
      heap
      (VClosure closure_env closure_rho f x ec ee)
      ty
      HState)
    as (HHeap & HVal).
  destruct
    (ResolvedValShape_closure_inv
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

Lemma ResolvedStateShape_done_closure_summary_static_heap_neutral :
  forall heap closure_env closure_rho f x ec ee
    ty_arg_res eff_body_res ty_body_res eff_summary_res
    rho eff_summary,
    ResolvedStateShape
      (StDone heap (VClosure closure_env closure_rho f x ec ee))
      (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res) ->
    ResolveStaticEffect rho eff_summary eff_summary_res ->
    static_heap_neutral eff_summary ->
    exists gamma omega ty_arg ty_body eff_body eff_summary_closure,
      ResolvedHeapShape heap /\
      ResolvedEnvShape closure_rho heap closure_env gamma /\
      RhoModels omega closure_rho /\
      TcExp
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
    (ResolvedStateShape_done_closure_inv
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
    (ResolveStaticEffect_static_heap_neutral_transfer_any
      rho closure_rho eff_summary eff_summary_closure
      eff_summary_res_closure);
    eauto.
Qed.

Lemma ResolvedStateShape_initial :
  forall heap env rho e gamma omega ty ty_res eff,
    ResolvedHeapShape heap ->
    ResolvedEnvShape rho heap env gamma ->
    RhoModels omega rho ->
    ResolveTy rho ty ty_res ->
    TcExp gamma omega e ty eff ->
    ResolvedStateShape (InitialState heap env rho e) ty_res.
Proof.
  intros heap env rho e gamma omega ty ty_res eff
    HHeap HEnv HRho HResolve HTyped.
  unfold InitialState.
  eapply RSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty) (eff := eff);
    eauto.
  constructor.
Qed.

Corollary ResolvedStateShape_initial_effect :
  forall heap env rho e gamma omega eff,
    ResolvedHeapShape heap ->
    ResolvedEnvShape rho heap env gamma ->
    RhoModels omega rho ->
    TcExp gamma omega e TyEffect eff ->
    ResolvedStateShape (InitialState heap env rho e) TyEffect.
Proof.
  intros heap env rho e gamma omega eff HHeap HEnv HRho HTyped.
  eapply ResolvedStateShape_initial; eauto using Resolve_Effect.
Qed.
