From Stdlib Require Import List.
From Stdlib Require Import Ascii.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.Typing.
Require Import theories.NewSmallStep.Typing.Judgments.
Require Import theories.NewSmallStep.Typing.Resolve.
Require Import theories.NewSmallStep.Typing.Types.

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
      NResolvedStateShape (StDone heap v) ty.
